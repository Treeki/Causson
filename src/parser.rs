use symbol::Symbol;
use crate::ast::*;
use crate::data::*;
use crate::stdlib;
use std::collections::HashMap;
use std::rc::Rc;
use std::cell::RefCell;

lazy_static! {
	static ref ASSIGN_OP: Symbol = id!("=");
}

#[derive(Debug, PartialEq)]
pub enum ParserError {
	SymTab(SymTabError),
	TypeIsMissing(QualID),
	TypeIsIncomplete,
	TypeExpected,
	TypeDependencyCycle,
	FunctionIsMissing(Symbol),
	NoMatchingOverload(Symbol),
	TypeMismatch(TypeRef, TypeRef),
	InvalidAssignTarget,
	InvalidCall,
	LocalCannotBeVoid,
	BadIfConditionType,
	BadWhileConditionType,
	BadMatchConditionType,
	BadMatchArmChoiceName(Symbol),
	BadMatchArmArguments,
	NonExhaustiveMatchArms,
	DuplicateMatchArms,
	VariableNotFound(Symbol),
	ConstantNotFound,
	MissingNamespace,
	UnexpectedSpecialisation,
}
pub type Result<T> = std::result::Result<T, ParserError>;

impl From<SymTabError> for ParserError {
	fn from(e: SymTabError) -> ParserError { ParserError::SymTab(e) }
}

impl Type {
	fn ensure_complete(&self) -> Result<()> {
		if let TypeBody::Incomplete = *self.borrow() {
			Err(ParserError::TypeIsIncomplete)
		} else {
			Ok(())
		}
	}
}

impl TypeRef {
	fn err_if_equal(a: &TypeRef, b: &TypeRef, err: ParserError) -> Result<()> {
		if a == b {
			Err(err)
		} else {
			Ok(())
		}
	}
	fn err_if_not_equal(a: &TypeRef, b: &TypeRef, err: ParserError) -> Result<()> {
		if a == b {
			Ok(())
		} else {
			Err(err)
		}
	}

	fn ensure_equal(a: &TypeRef, b: &TypeRef) -> Result<()> {
		TypeRef::err_if_not_equal(&a, &b, ParserError::TypeMismatch(a.clone(), b.clone()))
	}
}

struct ParseContext {
	symtab_rc: Rc<RefCell<SymbolTable>>
}

impl ParseContext {
	fn new() -> ParseContext {
		ParseContext { symtab_rc: SymbolTable::new_counted() }
	}

	fn preprocess_components(&self, program: &Program) -> Result<Program> {
		let mut extra_defs = vec![];
		for def in program {
			if let GlobalDef::Component(comp_id, subdefs) = def {
				// Extract the sub-definition tree as a flat list of
				// instances, and a flat list of component-global subdefs
				fn grab_bits<'a>(
					instances: &mut Vec<&'a HLCompInstance>,
					comp_global_subdefs: &mut Vec<&'a HLCompSubDef>,
					subdef: &'a HLCompSubDef) {
						match &subdef {
							HLCompSubDef::Instance(instance) => {
								instances.push(instance);
								for c in &instance.children {
									grab_bits(instances, comp_global_subdefs, c)
								}
							}
							HLCompSubDef::EventConnection(_, _) => (),
							HLCompSubDef::PropertySet(_, _) => (),
							HLCompSubDef::TransientAdd(_) => (),
							HLCompSubDef::Dynamic(_, _, _) | HLCompSubDef::Method(_, _, _, _) => {
								comp_global_subdefs.push(subdef);
							}
						}
				}

				let mut instances = vec![];
				let mut comp_global_subdefs = vec![];
				for subdef in subdefs {
					grab_bits(&mut instances, &mut comp_global_subdefs, &subdef);
				}

				// Pull out methods now, for dependency analysis of properties
				let mut methods: HashMap<Symbol, &HLExpr> = HashMap::new();
				for subdef in &comp_global_subdefs {
					if let HLCompSubDef::Method(method_name, args, ret_type, code_expr) = subdef {
						extra_defs.push(GlobalDef::Func(
							qid_combine!(comp_id, *method_name),
							FuncType::Method,
							args.clone(),
							ret_type.clone(),
							code_expr.clone()
						));
						methods.insert(*method_name, code_expr);
					}
				}

				// Create all the stuff we need
				let mut instance_ids: Vec<Symbol> = vec![];
				let mut notifier_ids: Vec<Symbol> = vec![];
				let mut record_fields = vec![];
				let mut new_frag = vec![];
				let mut prop_update_methods: Vec<Symbol> = vec![];
				let mut prop_updates: Vec<(Symbol, HLExpr, Symbol)> = vec![];

				let mut field_init_info = vec![];

				// Create fields for every instance
				for (index, instance) in instances.iter().enumerate() {
					let (instance_id, notifier_id) = match instance.name {
						Some(field_name) => (field_name, id!(format!("_n_{}", field_name))),
						None => (id!(format!("_f_{}", index)), id!(format!("_n_{}", index)))
					};
					instance_ids.push(instance_id);
					notifier_ids.push(notifier_id);

					// Add a new field to the record
					record_fields.push((instance.what.clone(), instance_id));
					field_init_info.push((id!(new), instance.new_args.clone()));
					record_fields.push((HLTypeRef(qid!(Notifier), vec![]), notifier_id));
					field_init_info.push((id!(new), vec![]));
				}

				// Create fields for every dynamic property
				for subdef in &comp_global_subdefs {
					if let HLCompSubDef::Dynamic(name, typ, _expr) = subdef {
						let notifier_id = id!(format!("_n_{}", name));
						notifier_ids.push(notifier_id);

						record_fields.push((typ.clone(), *name));
						field_init_info.push((id!(default), vec![]));
						record_fields.push((HLTypeRef(qid!(Notifier), vec![]), notifier_id));
						field_init_info.push((id!(new), vec![]));
					}
				}

				// Creation boilerplate
				for (a, b) in record_fields.iter().zip(field_init_info) {
					let (typ, field_id) = a;
					let (new_id, new_args) = b;
					let type_expr = typ.to_hl_expr();
					let new_expr = HLExpr::NamespaceAccess(Box::new(type_expr), new_id);
					let field_expr = HLExpr::Call(Box::new(new_expr), new_args);
					new_frag.push(HLExpr::Let(*field_id, Box::new(field_expr)));
				}


				// Assemble the hierarchy
				// This requires care, to keep the IDs in sync
				fn get_instance_weight(instance: &HLCompInstance) -> usize {
					let mut total = 1;
					for subdef in &instance.children {
						if let HLCompSubDef::Instance(sub_instance) = subdef {
							total += get_instance_weight(sub_instance);
						}
					}
					total
				}

				fn scan_dependencies(expr: &HLExpr, methods: &HashMap<Symbol, &HLExpr>) -> Result<Vec<(HLExpr, Symbol)>> {
					fn _is_self(expr: &HLExpr) -> bool {
						match expr {
							HLExpr::ID(sym) => *sym == "self",
							_ => false
						}
					}
					fn _directly_involves_self(expr: &HLExpr) -> bool {
						use HLExpr::*;
						match expr {
							ID(sym) => *sym == "self",
							PropAccess(subexpr, _) => _directly_involves_self(&subexpr),
							_ => false
						}
					}

					fn _recursive_scan(output: &mut Vec<(HLExpr, Symbol)>, expr: &HLExpr, is_call_target: bool, methods: &HashMap<Symbol, &HLExpr>, method_stack: &mut Vec<Symbol>) -> Result<()> {
						use HLExpr::*;
						match expr {
							ID(_) => (),
							Specialise(_, _) => (),
							NamespaceAccess(_, _) => (),
							Binary(l, _, r) => {
								_recursive_scan(output, &l, false, methods, method_stack)?;
								_recursive_scan(output, &r, false, methods, method_stack)?;
							}
							PropAccess(subexpr, sym) => {
								if is_call_target {
									if _is_self(&subexpr) {
										if !method_stack.contains(sym) {
											method_stack.push(*sym);
											if let Some(method_expr) = methods.get(sym) {
												_recursive_scan(output, method_expr, false, methods, method_stack)?;
											}
											method_stack.pop();
										}
									} else {
										_recursive_scan(output, &subexpr, false, methods, method_stack)?;
									}
								} else {
									if _directly_involves_self(&subexpr) {
										let result = (*subexpr.clone(), *sym);
										if !output.contains(&result) {
											output.push(result);
										}
									}
								}
							}
							Call(target, args) => {
								_recursive_scan(output, &target, true, methods, method_stack)?;
								for arg in args {
									_recursive_scan(output, &arg, false, methods, method_stack)?;
								}
							}
							If(cond, t, f) => {
								_recursive_scan(output, &cond, false, methods, method_stack)?;
								_recursive_scan(output, &t, false, methods, method_stack)?;
								if let Some(f) = f {
									_recursive_scan(output, &f, false, methods, method_stack)?;
								}
							}
							While(cond, subexpr) => {
								_recursive_scan(output, &cond, false, methods, method_stack)?;
								_recursive_scan(output, &subexpr, false, methods, method_stack)?;
							}
							Match(cond, arms) => {
								_recursive_scan(output, &cond, false, methods, method_stack)?;
								for (_, _, body) in arms {
									_recursive_scan(output, &body, false, methods, method_stack)?;
								}
							}
							Let(_, subexpr) => _recursive_scan(output, &subexpr, false, methods, method_stack)?,
							CodeBlock(subexprs) => {
								for subexpr in subexprs {
									_recursive_scan(output, &subexpr, false, methods, method_stack)?;
								}
							}
							Int(_) => (),
							Real(_) => (),
							Bool(_) => (),
							Str(_) => ()
						}
						Ok(())
					}

					let mut result = vec![];
					let mut method_stack = vec![];
					_recursive_scan(&mut result, expr, false, methods, &mut method_stack)?;
					Ok(result)
				}

				let mut next_callback_id = 0;
				let generate_updater = |callback_id: usize,
										prop_expr: HLExpr,
										value_expr: HLExpr,
										deps: Vec<(HLExpr, Symbol)>,
										extra_defs: &mut Vec<GlobalDef>,
										prop_updates: &mut Vec<(Symbol, HLExpr, Symbol)>,
										prop_update_methods: &mut Vec<Symbol>| {
					let updater_id = id!(format!("_upd_{}", callback_id));

					let set_expr = HLExpr::Binary(Box::new(prop_expr), id!("="), Box::new(value_expr.clone()));

					let mut updater_qid = comp_id.clone();
					updater_qid.push(updater_id);
					extra_defs.push(GlobalDef::Func(
						updater_qid,
						FuncType::Method,
						vec![],
						HLTypeRef(qid!(void), vec![]),
						set_expr
					));

					prop_update_methods.push(updater_id);
					for (dep_obj, dep_prop) in deps {
						prop_updates.push((updater_id, dep_obj, dep_prop));
					}
				};

				for (index, instance) in instances.iter().enumerate() {
					let mut sub_index = index + 1;
					for subdef in &instance.children {
						match subdef {
							HLCompSubDef::Instance(_sub_instance) => {
								let parent_expr = HLExpr::ID(instance_ids[index]);
								let child_expr = HLExpr::ID(instance_ids[sub_index]);
								let child_root_expr = HLExpr::PropAccess(Box::new(child_expr), id!(root));
								let add_expr = HLExpr::PropAccess(Box::new(parent_expr), id!(add_child));
								new_frag.push(HLExpr::Call(Box::new(add_expr), vec![child_root_expr]));
								sub_index += get_instance_weight(_sub_instance);
							},
							HLCompSubDef::TransientAdd(sub_expr) => {
								let parent_expr = HLExpr::ID(instance_ids[index]);
								let add_expr = HLExpr::PropAccess(Box::new(parent_expr), id!(add_child));
								new_frag.push(HLExpr::Call(Box::new(add_expr), vec![sub_expr.clone()]));
							},
							HLCompSubDef::EventConnection(event_id, value_expr) => {
								// Make a method
								let method_id = id!(format!("_cb_{}", next_callback_id));
								next_callback_id += 1;

								let mut method_qid = comp_id.clone();
								method_qid.push(method_id);
								extra_defs.push(GlobalDef::Func(
									method_qid,
									FuncType::Method,
									vec![],
									HLTypeRef(qid!(void), vec![]),
									value_expr.clone()
								));

								// Rely on the existing Notifier logic
								let this_expr = HLExpr::ID(instance_ids[index]);
								prop_updates.push((method_id, this_expr, *event_id));
							},
							HLCompSubDef::PropertySet(prop_id, value_expr) => {
								let deps = scan_dependencies(value_expr, &methods)?;
								if deps.is_empty() {
									// Static property, assign on construction
									let parent_expr = HLExpr::ID(instance_ids[index]);
									let prop_expr = HLExpr::PropAccess(Box::new(parent_expr), *prop_id);
									let set_expr = HLExpr::Binary(Box::new(prop_expr), id!("="), Box::new(value_expr.clone()));
									new_frag.push(set_expr);
								} else {
									// Make a method
									let self_expr = HLExpr::ID(id!(self));
									let parent_expr = HLExpr::PropAccess(Box::new(self_expr), instance_ids[index]);
									let prop_expr = HLExpr::PropAccess(Box::new(parent_expr), *prop_id);
									generate_updater(next_callback_id, prop_expr, value_expr.clone(), deps, &mut extra_defs, &mut prop_updates, &mut prop_update_methods);
									next_callback_id += 1;
								}
							}
							HLCompSubDef::Dynamic(_, _, _) => {}
							HLCompSubDef::Method(_, _, _, _) => {}
						}
					}
				}

				// Build update machinery for dynamic properties
				for subdef in &comp_global_subdefs {
					if let HLCompSubDef::Dynamic(name, _typ, expr) = subdef {
						let deps = scan_dependencies(expr, &methods)?;
						let self_expr = HLExpr::ID(id!(self));
						let prop_expr = HLExpr::PropAccess(Box::new(self_expr), *name);
						generate_updater(next_callback_id, prop_expr, expr.clone(), deps, &mut extra_defs, &mut prop_updates, &mut prop_update_methods);
						next_callback_id += 1;
					}
				}

				let result_id = id!(self);

				// self = Type:build(...)
				let comp_type_expr = HLTypeRef(comp_id.clone(), vec![]).to_hl_expr();
				let comp_build_expr = HLExpr::NamespaceAccess(Box::new(comp_type_expr), id!(build));
				let field_id_exprs = record_fields.iter().map(|(_, i)| HLExpr::ID(*i)).collect();
				new_frag.push(HLExpr::Let(result_id, Box::new(HLExpr::Call(Box::new(comp_build_expr), field_id_exprs))));

				// Update all dynamic properties
				for upd in prop_update_methods {
					let self_expr = HLExpr::ID(result_id);
					let upd_expr = HLExpr::PropAccess(Box::new(self_expr), upd);
					new_frag.push(HLExpr::Call(Box::new(upd_expr), vec![]));
				}

				// Connect all notifiers
				for (upd, dep_obj, dep_prop) in prop_updates {
					let notifier_id = id!(format!("_n_{}", dep_prop));
					let notifier_expr = HLExpr::PropAccess(Box::new(dep_obj), notifier_id);
					let connect_expr = HLExpr::PropAccess(Box::new(notifier_expr), id!(connect));
					let self_expr = HLExpr::ID(result_id);
					let upd_expr = HLExpr::Str(upd.to_string());
					new_frag.push(HLExpr::Call(Box::new(connect_expr), vec![self_expr, upd_expr]));
				}

				// Finally, return self
				new_frag.push(HLExpr::ID(result_id));

				extra_defs.push(GlobalDef::Type(
					comp_id.clone(),
					HLTypeDef::Record { fields: record_fields, rename_setters: true }
				));
				extra_defs.push(GlobalDef::Func(
					qid_combine!(comp_id, id!(new)),
					FuncType::Function,
					vec![],
					HLTypeRef(comp_id.clone(), vec![]),
					HLExpr::CodeBlock(new_frag)
				));

				// Last but not least, generate custom setters that call our notifiers
				let mut generate_setter = |field_id: Symbol,
										   notifier_id: Symbol,
										   typ: HLTypeRef| {
					let mut code = vec![];

					// Write it using the renamed default setter
					let self_expr = HLExpr::ID(id!(self));
					let defsetter_id = id!(format!("_set_{}", field_id));
					let defsetter_expr = HLExpr::PropAccess(Box::new(self_expr), defsetter_id);
					let v_expr = HLExpr::ID(id!(v));
					code.push(HLExpr::Call(Box::new(defsetter_expr), vec![v_expr]));

					// Call the notifier
					let self_expr = HLExpr::ID(id!(self));
					let notifier_expr = HLExpr::PropAccess(Box::new(self_expr), notifier_id);
					let notify_expr = HLExpr::PropAccess(Box::new(notifier_expr), id!(notify));
					code.push(HLExpr::Call(Box::new(notify_expr), vec![]));

					let mut setter_qid = comp_id.clone();
					setter_qid.push(id!(format!("{}=", field_id)));
					extra_defs.push(GlobalDef::Func(
						setter_qid,
						FuncType::Method,
						vec![(typ, id!(v))],
						HLTypeRef(qid!(void), vec![]),
						HLExpr::CodeBlock(code)
					));
				};

				for ((instance, instance_id), notifier_id) in instances.iter().zip(instance_ids).zip(notifier_ids) {
					generate_setter(instance_id, notifier_id, instance.what.clone());
				}
				for subdef in &comp_global_subdefs {
					if let HLCompSubDef::Dynamic(name, typ, _) = subdef {
						generate_setter(*name, id!(format!("_n_{}", name)), typ.clone());
					}
				}
			}
		}

		crate::pretty_print::print_program(&mut std::io::stdout(), &extra_defs).unwrap();

		Ok(extra_defs)
	}

	fn resolve_typeref(symtab: &mut SymbolTable, r: &HLTypeRef) -> Result<TypeRef> {
		let typ = symtab.root.resolve(&r.0).ok_or_else(|| ParserError::TypeIsMissing(r.0.clone()))?;
		let typ = typ.get_type().ok_or_else(|| ParserError::TypeIsMissing(r.0.clone()))?;
		typ.ensure_complete()?;
		let refs = r.1.iter().map(|sr| ParseContext::resolve_typeref(symtab, &sr)).collect::<Result<Vec<TypeRef>>>()?;
		Ok(TypeRef(typ, refs))
	}

	fn replace_incomplete_type(&mut self, name: &[Symbol], typedef: &HLTypeDef) -> Result<()> {
		let mut symtab = self.symtab_rc.borrow_mut();
		let node = symtab.root.resolve_mut(name).expect("incomplete type should exist!");
		let mut typ = node.get_type().expect("incomplete type should be a type");

		match typedef {
			HLTypeDef::Wrap(target_ref) => {
				let target_typeref = ParseContext::resolve_typeref(&mut symtab, target_ref)?;
				*typ.borrow_mut() = TypeBody::Wrapper(target_typeref.clone());

				stdlib::inject_wrap_type(&mut symtab, typ, target_typeref.0)?;
				Ok(())
			}
			HLTypeDef::Enum(values) => {
				let mut res_values = vec![];
				for (val_id, fields) in values {
					let fields = fields.iter().map(
						|(tref, field_id)|
						ParseContext::resolve_typeref(&mut symtab, &tref).map(|t| (t.to_spectype(), *field_id))
					).collect::<Result<Vec<(SpecType, Symbol)>>>()?;
					res_values.push((val_id.clone(), fields));
				}

				for (i, (val_id, fields)) in res_values.iter().enumerate() {
					if fields.is_empty() {
						// we have to re-select 'node' because the borrow checker is silly
						let node = symtab.root.resolve_mut(name).unwrap();
						let c = Value::Enum(i, vec![]);
						node.get_children_mut().unwrap().insert(*val_id, SymTabNode::new_constant(SpecType::Type(typ.clone(), vec![]), c));
					} else {
						symtab.add_builtin_generic_method(
							false, &typ, *val_id, &SpecType::Type(typ.clone(), vec![]), &fields,
							move |_, _, args| { Value::Enum(i, args.to_vec()) }
						)?;
					}
				}
				let have_fields = res_values.iter().any(|v| !v.1.is_empty());
				*typ.borrow_mut() = TypeBody::Enum(res_values);
				stdlib::inject_enum_type(&mut symtab, typ, have_fields)?;
				Ok(())
			}
			HLTypeDef::Record { fields, rename_setters } => {
				let fields = fields.iter().map(
					|(tref, field_id)|
					ParseContext::resolve_typeref(&mut symtab, &tref).map(|t| (t, *field_id))
				).collect::<Result<Vec<(TypeRef, Symbol)>>>()?;
				stdlib::inject_record_type(&mut symtab, typ.clone(), &fields, *rename_setters)?;
				*typ.borrow_mut() = TypeBody::Record(fields);
				Ok(())
			}
		}
	}

	fn collect_types(&mut self, prog: &Program, extra_defs: &Program) -> Result<()> {
		let mut typedefs: Vec<&GlobalDef> = vec![];
		let mut symtab = self.symtab_rc.borrow_mut();

		for p in [prog, extra_defs].iter() {
			for def in p.iter() {
				if let GlobalDef::Type(name, _) = def {
					symtab.add_type(Type::from_body(name.clone(), TypeBody::Incomplete))?;
					typedefs.push(&def);
				}
			}
		}

		drop(symtab); // satisfy the borrow checker

		// This may require multiple passes, and cycles may occur,
		// so we must detect those and return an error
		while !typedefs.is_empty() {
			let mut leftovers: Vec<&GlobalDef> = vec![];
			let mut processed = 0;

			for def in &typedefs {
				let result = match def {
					GlobalDef::Type(name, def) => self.replace_incomplete_type(&name, &def),
					_ => unreachable!()
				};

				match result {
					Ok(()) => processed += 1,
					Err(ParserError::TypeIsIncomplete) => leftovers.push(def),
					_ => return result
				}
			}

			if processed == 0 {
				// we have reached a cycle
				return Err(ParserError::TypeDependencyCycle);
			} else {
				typedefs = leftovers;
			}
		}

		Ok(())
	}


	fn collect_function_specs(&mut self, prog: &Program) -> Result<()> {
		let mut symtab = self.symtab_rc.borrow_mut();

		for (i, def) in prog.iter().enumerate() {
			if let GlobalDef::Func(name, func_type, args, return_type, _) = def {
				let args = args.iter().map(
					|(tref, arg_id)|
					ParseContext::resolve_typeref(&mut symtab, &tref).map(|t| (t.to_spectype(), *arg_id))
				).collect::<Result<Vec<(SpecType, Symbol)>>>()?;

				let return_type = ParseContext::resolve_typeref(&mut symtab, &return_type)?.to_spectype();

				let is_method = match func_type {
					FuncType::Function => false,
					FuncType::Method   => true
				};
				symtab.add_function(Function::new_incomplete(
					name.clone(), is_method, return_type, args, i
				))?;
			}
		}

		Ok(())
	}

	fn collect_function_bodies(&mut self, prog: &Program) -> Result<()> {
		// this is kind of horrid, but satisfies the borrow checker
		let symtab_rc_clone = Rc::clone(&self.symtab_rc);
		let symtab = symtab_rc_clone.borrow();

		for (i, def) in prog.iter().enumerate() {
			if let GlobalDef::Func(name, _, _, _, hlexpr) = def {
				let func = symtab.root.resolve(name).unwrap();
				let variants = func.get_function_variants().unwrap();
				let mut func = variants.iter().find(|f| f.is_incomplete(i)).unwrap().clone();

				let expr = desugar_expr(hlexpr)?;
				let expr = self.check_function(&func, &expr)?;
				*func.borrow_mut() = FunctionBody::Expr(expr);
			}
		}

		Ok(())
	}


	fn check_function(&mut self, func: &FunctionData, expr: &UncheckedExpr) -> Result<Expr> {
		let mut ctx = CodeParseContext::new(self, func);
		let result_expr = ctx.typecheck_expr(expr)?;

		// any final result is ok if the function returns void
		match &func.return_type {
			SpecType::Placeholder(_) => unreachable!("cannot define custom generic functions (yet?)"),
			SpecType::Type(t, _params) => {
				if t != &self.symtab_rc.borrow().void_type {
					// calling fill_gap here is ugly, but works for now
					TypeRef::ensure_equal(&result_expr.typ, &func.return_type.fill_gap(&[]))?;
				}
			}
		}
		Ok(result_expr)
	}
}

fn desugar_qual_id(expr: &HLExpr, failure: ParserError) -> Result<QualID> {
	let mut qid = vec![];
	let mut expr = expr;

	loop {
		expr = match expr {
			HLExpr::ID(id) => {
				qid.push(*id);
				qid.reverse();
				return Ok(qid)
			}
			HLExpr::NamespaceAccess(subexpr, id) => {
				qid.push(*id);
				&*subexpr
			}
			_ => return Err(failure)
		};
	}
}

fn desugar_type_ref(expr: &HLExpr) -> Result<HLTypeRef> {
	match expr {
		HLExpr::ID(_) | HLExpr::NamespaceAccess(_, _) => {
			Ok(HLTypeRef(desugar_qual_id(expr, ParserError::TypeExpected)?, vec![]))
		}
		HLExpr::Specialise(subexpr, refs) => {
			Ok(HLTypeRef(desugar_qual_id(subexpr, ParserError::TypeExpected)?, refs.clone()))
		}
		_ => Err(ParserError::TypeExpected)
	}
}

fn desugar_expr(expr: &HLExpr) -> Result<UncheckedExpr> {
	match expr {
		HLExpr::ID(var) => {
			Ok(UncheckedExpr(ExprKind::LocalGet(*var)))
		}
		HLExpr::Binary(lhs, op, rhs) if *op == *ASSIGN_OP => {
			match lhs {
				box HLExpr::ID(var) => {
					// Assign to local
					let value = Box::new(desugar_expr(&*rhs)?);
					Ok(UncheckedExpr(ExprKind::LocalSet(*var, value)))
				}
				box HLExpr::PropAccess(obj, sym) => {
					// Set property
					let obj   = Box::new(desugar_expr(&*obj)?);
					let sym   = id!(sym.as_str().to_string() + "=");
					let value = desugar_expr(&*rhs)?;
					Ok(UncheckedExpr(ExprKind::MethodCall(obj, sym, vec![value])))
				}
				_ => Err(ParserError::InvalidAssignTarget)
			}
		}
		HLExpr::Binary(lhs, op, rhs) => {
			// Binary op becomes a method call
			let lhs = Box::new(desugar_expr(&*lhs)?);
			let sym = id!("op#".to_string() + op);
			let rhs = desugar_expr(&*rhs)?;
			Ok(UncheckedExpr(ExprKind::MethodCall(lhs, sym, vec![rhs])))
		}
		HLExpr::PropAccess(obj, sym) => {
			// Naked PropAccess maps to an argument-less method call
			let obj = Box::new(desugar_expr(&*obj)?);
			Ok(UncheckedExpr(ExprKind::MethodCall(obj, *sym, vec![])))
		}
		HLExpr::NamespaceAccess(obj, sym) => {
			// Standalone, this is only valid for accessing a global constant
			// For now, just don't let these work on specialised types...
			let type_ref = desugar_type_ref(&*obj)?;
			Ok(UncheckedExpr(ExprKind::GlobalGet(type_ref, *sym)))
		}
		HLExpr::Specialise(_, _) => Err(ParserError::UnexpectedSpecialisation),
		HLExpr::Call(box HLExpr::PropAccess(obj, sym), args) => {
			// Call on a property becomes a method call
			let obj  = Box::new(desugar_expr(&*obj)?);
			let args = args.iter().map(desugar_expr).collect::<Result<Vec<UncheckedExpr>>>()?;
			Ok(UncheckedExpr(ExprKind::MethodCall(obj, *sym, args)))
		}
		HLExpr::Call(box HLExpr::NamespaceAccess(ns, sym), args) => {
			// Call on a namespace access becomes a static method call
			let typeref = desugar_type_ref(&*ns)?;
			let args = args.iter().map(desugar_expr).collect::<Result<Vec<UncheckedExpr>>>()?;
			Ok(UncheckedExpr(ExprKind::FunctionCall(typeref, *sym, args)))
		}
		HLExpr::Call(box HLExpr::ID(sym), args) => {
			// Call on a naked ID becomes a plain function call
			let args = args.iter().map(desugar_expr).collect::<Result<Vec<UncheckedExpr>>>()?;
			Ok(UncheckedExpr(ExprKind::FunctionCall(HLTypeRef(vec![], vec![]), *sym, args)))
		}
		HLExpr::Call(_, _) => Err(ParserError::InvalidCall),
		HLExpr::If(cond, if_true, if_false) => {
			let cond     = Box::new(desugar_expr(&*cond)?);
			let if_true  = Box::new(desugar_expr(&*if_true)?);
			let if_false = match if_false {
				None        => None,
				Some(box e) => Some(Box::new(desugar_expr(e)?))
			};
			Ok(UncheckedExpr(ExprKind::If(cond, if_true, if_false)))
		}
		HLExpr::While(cond, subexpr) => {
			let cond    = Box::new(desugar_expr(&*cond)?);
			let subexpr = Box::new(desugar_expr(&*subexpr)?);
			Ok(UncheckedExpr(ExprKind::While(cond, subexpr)))
		}
		HLExpr::Let(sym, value) => {
			let value = Box::new(desugar_expr(&*value)?);
			Ok(UncheckedExpr(ExprKind::Let(sym.clone(), value)))
		}
		HLExpr::Match(cond, arms) => {
			let cond = Box::new(desugar_expr(&*cond)?);
			let arms = arms.iter().map(|(c, args, subexpr)| {
				let subexpr = desugar_expr(&subexpr)?;
				Ok((*c, args.clone(), subexpr))
			}).collect::<Result<Vec<(Symbol, Vec<Symbol>, UncheckedExpr)>>>()?;
			Ok(UncheckedExpr(ExprKind::Match(cond, arms)))
		}
		HLExpr::CodeBlock(exprs) => {
			let exprs = exprs.iter().map(desugar_expr).collect::<Result<Vec<UncheckedExpr>>>()?;
			Ok(UncheckedExpr(ExprKind::CodeBlock(exprs)))
		}
		HLExpr::Int(result)  => Ok(UncheckedExpr(ExprKind::Int(result.clone()))),
		HLExpr::Real(result) => Ok(UncheckedExpr(ExprKind::Real(result.clone()))),
		HLExpr::Bool(value)  => Ok(UncheckedExpr(ExprKind::Bool(*value))),
		HLExpr::Str(string)  => Ok(UncheckedExpr(ExprKind::Str(string.clone())))
	}
}


struct CodeParseContext<'a> {
	parent: &'a ParseContext,
	locals: Vec<(TypeRef, Symbol)>
}

impl<'a> CodeParseContext<'a> {
	fn new(parent_ctx: &'a ParseContext, func: &FunctionData) -> CodeParseContext<'a> {
		let mut locals = vec![];
		if func.is_method {
			let symtab = parent_ctx.symtab_rc.borrow();
			let owner_name = func.name.split_last().unwrap().1;
			let owner_node = symtab.root.resolve(owner_name).unwrap();
			let owner_type = owner_node.get_type().unwrap();
			locals.push((TypeRef(owner_type, vec![]), id!(self)));
		}
		for (styp, sym) in &func.arguments {
			match styp {
				// calling fill_gap here is ugly but works for now
				SpecType::Type(_, _) => locals.push((styp.fill_gap(&[]), *sym)),
				SpecType::Placeholder(_) => panic!("unimplemented custom generic functions")
			}
		}
		CodeParseContext {
			parent: parent_ctx,
			locals
		}
	}

	fn resolve_typeref(&mut self, symtab: &SymbolTable, r: &HLTypeRef) -> Result<TypeRef> {
		let typ = symtab.root.resolve(&r.0).ok_or_else(|| ParserError::TypeIsMissing(r.0.clone()))?;
		let typ = typ.get_type().ok_or_else(|| ParserError::TypeIsMissing(r.0.clone()))?;
		typ.ensure_complete()?;
		let refs = r.1.iter().map(|sr| self.resolve_typeref(symtab, &sr)).collect::<Result<Vec<TypeRef>>>()?;
		Ok(TypeRef(typ, refs))
	}

	fn resolve_local_var(&mut self, sym: &Symbol) -> Result<(usize, TypeRef)> {
		for (i, (var_type, var_name)) in self.locals.iter().enumerate().rev() {
			if sym == var_name {
				return Ok((i, var_type.clone()));
			}
		}
		Err(ParserError::VariableNotFound(*sym))
	}

	fn scoped_typecheck_expr(&mut self, expr: &UncheckedExpr) -> Result<Expr> {
		let locals_depth = self.locals.len();
		let result = self.typecheck_expr(expr);
		self.locals.truncate(locals_depth);
		result
	}

	fn typecheck_expr(&mut self, expr: &UncheckedExpr) -> Result<Expr> {
		let symtab = self.parent.symtab_rc.borrow();

		use ExprKind::*;
		match &expr.0 {
			LocalGet(sym) => {
				let (id, typ) = self.resolve_local_var(sym)?;
				Ok(Expr { expr: LocalGetResolved(id), typ })
			}
			LocalSet(sym, value) => {
				let (id, var_type) = self.resolve_local_var(sym)?;
				let value_expr = self.typecheck_expr(value)?;
				TypeRef::ensure_equal(&var_type, &value_expr.typ)?;
				let typ = value_expr.typ.clone();
				Ok(Expr { expr: LocalSetResolved(id, Box::new(value_expr)), typ })
			}
			LocalGetResolved(_) => unreachable!(),
			LocalSetResolved(_, _) => unreachable!(),
			GlobalGet(typeref, sym) => {
				// right now this is JUST for enum constants
				let parent_node = symtab.root.resolve(&typeref.0).ok_or(ParserError::MissingNamespace)?;
				let parent_typ = parent_node.get_type().ok_or_else(|| ParserError::TypeIsMissing(typeref.0.clone()))?;
				let specials = typeref.1.iter().map(|tr| self.resolve_typeref(&symtab, &tr)).collect::<Result<Vec<TypeRef>>>()?;
				let const_node = parent_node.resolve(&[*sym]).ok_or(ParserError::ConstantNotFound)?;
				let (typ, _) = const_node.get_constant().ok_or(ParserError::ConstantNotFound)?;
				let typ = typ.fill_gap(&specials);

				Ok(Expr { expr: GlobalGetResolved(TypeRef(parent_typ, specials), *sym), typ })
			}
			GlobalGetResolved(_, _) => unreachable!(),
			FunctionCall(typeref, sym, args) => {
				let arg_exprs = args.iter().map(|e| self.scoped_typecheck_expr(e)).collect::<Result<Vec<Expr>>>()?;
				let arg_types = arg_exprs.iter().map(|e| e.typ.clone()).collect::<Vec<TypeRef>>();
				let parent_typ = symtab.root.resolve(&typeref.0).ok_or_else(|| ParserError::TypeIsMissing(typeref.0.clone()))?;
				let specials = typeref.1.iter().map(|tr| self.resolve_typeref(&symtab, &tr)).collect::<Result<Vec<TypeRef>>>()?;
				let func = parent_typ.resolve(&[*sym]).ok_or(ParserError::FunctionIsMissing(*sym))?;
				let variants = func.get_function_variants().ok_or(ParserError::FunctionIsMissing(*sym))?;
				let func = variants.iter().find(|f| f.matches_types(&specials, &arg_types)).ok_or(ParserError::NoMatchingOverload(*sym))?;
				let return_type = func.return_type.fill_gap(&specials);
				Ok(Expr { expr: FunctionCallResolved(func.clone(), arg_types, arg_exprs), typ: return_type })
			}
			FunctionCallResolved(_, _, _) => unreachable!(),
			MethodCall(obj, sym, args) => {
				let obj_expr = self.typecheck_expr(obj)?;
				let arg_exprs = args.iter().map(|e| self.scoped_typecheck_expr(e)).collect::<Result<Vec<Expr>>>()?;
				let arg_types = arg_exprs.iter().map(|e| e.typ.clone()).collect::<Vec<TypeRef>>();
				let type_node = symtab.root.resolve(&obj_expr.typ.0.name).expect("type missing");
				let method = type_node.resolve(&[*sym]).ok_or(ParserError::FunctionIsMissing(*sym))?;
				let variants = method.get_function_variants().ok_or(ParserError::FunctionIsMissing(*sym))?;
				let method = variants.iter().find(|f| f.matches_types(&obj_expr.typ.1, &arg_types)).ok_or(ParserError::NoMatchingOverload(*sym))?;
				let return_type = method.return_type.fill_gap(&obj_expr.typ.1);
				Ok(Expr { expr: MethodCallResolved(Box::new(obj_expr), *sym, arg_types, arg_exprs), typ: return_type })
			}
			MethodCallResolved(_, _, _, _) => unreachable!(),
			If(cond, if_true, if_false) => {
				// don't use scoped_typecheck_expr here so the locals carry on into branches
				let orig_local_depth = self.locals.len();
				let cond_expr = self.typecheck_expr(cond)?;
				TypeRef::err_if_not_equal(&cond_expr.typ, &TypeRef(symtab.bool_type.clone(), vec![]), ParserError::BadIfConditionType)?;
				let if_true_expr = self.scoped_typecheck_expr(if_true)?;
				let if_false_expr = if_false.as_ref().map(|e| self.scoped_typecheck_expr(&e)).transpose()?;
				let typ = match &if_false_expr {
					Some(e) if e.typ == if_true_expr.typ => e.typ.clone(),
					_                                    => TypeRef(symtab.void_type.clone(), vec![])
				};
				self.locals.truncate(orig_local_depth);
				Ok(Expr { expr: If(Box::new(cond_expr), Box::new(if_true_expr), if_false_expr.map(Box::new)), typ })
			}
			While(cond, sub) => {
				let cond_expr = self.scoped_typecheck_expr(cond)?;
				let sub_expr = self.scoped_typecheck_expr(sub)?;
				TypeRef::err_if_not_equal(&cond_expr.typ, &TypeRef(symtab.bool_type.clone(), vec![]), ParserError::BadWhileConditionType)?;
				let typ = TypeRef(symtab.void_type.clone(), vec![]);
				Ok(Expr { expr: While(Box::new(cond_expr), Box::new(sub_expr)), typ })
			}
			Match(cond, arms) => {
				let cond_expr = self.scoped_typecheck_expr(cond)?;
				let cond_typebody = cond_expr.typ.0.borrow();
				let choices = match &*cond_typebody {
					TypeBody::Enum(choices) => choices,
					_ => return Err(ParserError::BadMatchConditionType)
				};
				let mut arm_exprs: Vec<Option<Expr>> = Vec::new();
				let mut default_arm: Option<Box<Expr>> = None;
				arm_exprs.resize(choices.len(), None);

				for (arm_name, arm_args, arm_expr) in arms {
					let orig_local_depth = self.locals.len();
					let index = if arm_name == &"_" {
						// default arm
						if default_arm.is_some() {
							return Err(ParserError::DuplicateMatchArms);
						}
						None
					} else {
						// need to find the associated choice
						let i = choices.iter().position(|c| c.0 == *arm_name);
						let i = i.ok_or(ParserError::BadMatchArmChoiceName(*arm_name))?;
						if choices[i].1.len() != arm_args.len() {
							return Err(ParserError::BadMatchArmArguments);
						}
						if arm_exprs[i].is_some() {
							return Err(ParserError::DuplicateMatchArms);
						}
						for (arg_name, (arg_typespec, _)) in arm_args.iter().zip(&choices[i].1) {
							self.locals.push((arg_typespec.fill_gap(&cond_expr.typ.1), *arg_name));
						}
						Some(i)
					};

					let arm_expr = self.typecheck_expr(arm_expr)?;
					self.locals.truncate(orig_local_depth);

					// now, place it
					match index {
						None    => default_arm = Some(Box::new(arm_expr)),
						Some(i) => arm_exprs[i] = Some(arm_expr)
					};
				}

				let typ = match &default_arm {
					None => {
						// there can be no empty arms in this case
						if arm_exprs.iter().any(Option::is_none) {
							return Err(ParserError::NonExhaustiveMatchArms)
						} else if arm_exprs.iter().all(|e| e.as_ref().unwrap().typ == arm_exprs[0].as_ref().unwrap().typ) {
							arm_exprs[0].as_ref().unwrap().typ.clone()
						} else {
							TypeRef(symtab.void_type.clone(), vec![])
						}
					}
					Some(default_arm) => {
						// we only return a non-void type if every arm returns that type
						if arm_exprs.iter().all(|e| e.is_none() || e.as_ref().unwrap().typ == default_arm.typ) {
							default_arm.typ.clone()
						} else {
							TypeRef(symtab.void_type.clone(), vec![])
						}
					}
				};

				drop(cond_typebody); // ah, gotta love the borrow checker,
				Ok(Expr { expr: MatchResolved(Box::new(cond_expr), arm_exprs, default_arm), typ })
			}
			MatchResolved(_, _, _) => unreachable!(),
			Let(sym, value) => {
				let value_expr = self.typecheck_expr(value)?;
				TypeRef::err_if_equal(&value_expr.typ, &TypeRef(symtab.void_type.clone(), vec![]), ParserError::LocalCannotBeVoid)?;
				self.locals.push((value_expr.typ.clone(), *sym));
				let typ = value_expr.typ.clone();
				Ok(Expr { expr: Let(*sym, Box::new(value_expr)), typ })
			}
			CodeBlock(exprs) => {
				let orig_local_depth = self.locals.len();
				let exprs = exprs.iter().map(|e| self.typecheck_expr(e)).collect::<Result<Vec<Expr>>>()?;
				self.locals.truncate(orig_local_depth);
				let final_type = match exprs.last() {
					Some(e) => e.typ.clone(),
					None    => TypeRef(symtab.void_type.clone(), vec![])
				};
				Ok(Expr { expr: CodeBlock(exprs), typ: final_type })
			}
			Int(v)  => Ok(Expr { expr: Int(v.clone()),  typ: TypeRef(symtab.int_type.clone(), vec![]) }),
			Real(v) => Ok(Expr { expr: Real(v.clone()), typ: TypeRef(symtab.real_type.clone(), vec![]) }),
			Bool(v) => Ok(Expr { expr: Bool(v.clone()), typ: TypeRef(symtab.bool_type.clone(), vec![]) }),
			Str(s)  => Ok(Expr { expr: Str(s.clone()),  typ: TypeRef(symtab.str_type.clone(), vec![]) }),
		}
	}
}


pub fn make_symtab_from_program(prog: &Program) -> Result<Rc<RefCell<SymbolTable>>> {
	let mut ctx = ParseContext::new();
	let new_defs = ctx.preprocess_components(prog)?;
	ctx.collect_types(prog, &new_defs)?;
	ctx.collect_function_specs(prog)?;
	ctx.collect_function_specs(&new_defs)?;
	ctx.collect_function_bodies(prog)?;
	ctx.collect_function_bodies(&new_defs)?;
	Ok(ctx.symtab_rc)
}


#[cfg(test)]
mod tests {
	use super::*;
	use HLExpr as HL;
	use ExprKind::*;

	fn expr(e: ExprKind<UncheckedExpr>) -> UncheckedExpr {
		UncheckedExpr(e)
	}
	fn box_expr(e: ExprKind<UncheckedExpr>) -> Box<UncheckedExpr> {
		Box::new(expr(e))
	}

	fn exprs_equal(a: &ExprKind<UncheckedExpr>, b: &ExprKind<UncheckedExpr>) -> bool {
		fn vec_equal(a: &Vec<UncheckedExpr>, b: &Vec<UncheckedExpr>) -> bool {
			(a.len() == b.len()) && (a.iter().zip(b).all(|(a,b)| exprs_equal(&a.0, &b.0)))
		}

		if std::mem::discriminant(&a) != std::mem::discriminant(&b) {
			return false;
		}

		match (a, b) {
			(LocalGet(a), LocalGet(b)) => a == b,
			(LocalSet(a0, a1), LocalSet(b0, b1)) => (a0 == b0) && exprs_equal(&a1.0, &b1.0),
			(GlobalGet(a0, a1), GlobalGet(b0, b1)) => (a0 == b0) && (a1 == b1),
			(FunctionCall(a0, a1, a2), FunctionCall(b0, b1, b2)) => {
				(a0 == b0) && (a1 == b1) && vec_equal(a2, b2)
			}
			(MethodCall(a0, a1, a2), MethodCall(b0, b1, b2)) => {
				exprs_equal(&a0.0, &b0.0) && (a1 == b1) && vec_equal(a2, b2)
			}
			(If(a0, a1, a2), If(b0, b1, b2)) => {
				exprs_equal(&a0.0, &b0.0) && exprs_equal(&a1.0, &b1.0) && match (a2, b2) {
					(None, None)       => true,
					(Some(a), Some(b)) => exprs_equal(&a.0, &b.0),
					_                  => false
				}
			}
			(While(a0, a1), While(b0, b1)) => {
				exprs_equal(&a0.0, &b0.0) && exprs_equal(&a1.0, &b1.0)
			}
			(Match(a0, a1), Match(b0, b1)) => {
				exprs_equal(&a0.0, &b0.0) && (a1.len() == b1.len()) && (a1.iter().zip(b1).all(|(i,j)|
					(i.0 == j.0) && (i.1 == j.1) && exprs_equal(&(i.2).0, &(j.2).0)
				))
			}
			(Let(a0, a1), Let(b0, b1)) => (a0 == b0) && exprs_equal(&a1.0, &b1.0),
			(CodeBlock(a), CodeBlock(b)) => vec_equal(&a, &b),
			(Int(a), Int(b)) => a == b,
			(Real(a), Real(b)) => a == b,
			(Bool(a), Bool(b)) => a == b,
			_ => unreachable!()
		}
	}

	fn check_desugar_ok(hl: HLExpr, res: ExprKind<UncheckedExpr>) {
		let expr = desugar_expr(&hl).unwrap();
		assert!(exprs_equal(&expr.0, &res));
	}
	fn check_desugar_err(hl: HLExpr, err: ParserError) {
		let expr = desugar_expr(&hl);
		assert!(expr.is_err() && expr.unwrap_err() == err);
	}

	#[test]
	fn test_desugar_get() {
		check_desugar_ok(
			HL::ID(id!(foo)),
			LocalGet(id!(foo))
		);

		check_desugar_ok(
			HL::NamespaceAccess(Box::new(HL::ID(id!(foo))), id!(bar)),
			GlobalGet(HLTypeRef(qid!(foo), vec![]), id!(bar))
		);
	}

	#[test]
	fn test_desugar_assign_ok() {
		let hl_int1 = Box::new(HL::Int(Ok(1)));
		let int1 = box_expr(Int(Ok(1)));
		let hl_foo = Box::new(HL::ID(id!(foo)));

		check_desugar_ok(
			HL::Binary(hl_foo.clone(), id!("="), hl_int1.clone()),
			LocalSet(id!(foo), int1.clone())
		);
		check_desugar_ok(
			HL::Binary(Box::new(HL::PropAccess(hl_foo.clone(), id!(bar))), id!("="), hl_int1.clone()),
			MethodCall(box_expr(LocalGet(id!(foo))), id!("bar="), vec![expr(Int(Ok(1)))])
		);
	}

	#[test]
	fn test_desugar_assign_err() {
		fn check(target: HLExpr) {
			check_desugar_err(
				HL::Binary(Box::new(target), id!("="), Box::new(HL::Int(Ok(1)))),
				ParserError::InvalidAssignTarget
			);
		}

		check(HL::NamespaceAccess(Box::new(HL::ID(id!(a))), id!(b)));
		check(HL::Int(Ok(1)));
		check(HL::Real(Ok(1.)));
		check(HL::Bool(true));
		check(HL::Binary(Box::new(HL::Int(Ok(1))), id!("+"), Box::new(HL::Int(Ok(2)))));
	}

	#[test]
	fn test_desugar_calls() {
		check_desugar_ok(
			HL::Call(Box::new(HL::ID(id!(a))), vec![]),
			FunctionCall(HLTypeRef(vec![], vec![]), id!(a), vec![])
		);
		check_desugar_ok(
			HL::Call(Box::new(HL::NamespaceAccess(Box::new(HL::ID(id!(a))), id!(b))), vec![]),
			FunctionCall(HLTypeRef(qid!(a), vec![]), id!(b), vec![])
		);
		check_desugar_ok(
			HL::Call(Box::new(HL::PropAccess(Box::new(HL::ID(id!(a))), id!(b))), vec![]),
			MethodCall(box_expr(LocalGet(id!(a))), id!(b), vec![])
		);
		check_desugar_err(
			HL::Call(Box::new(HL::Int(Ok(1))), vec![]),
			ParserError::InvalidCall
		);
	}

	#[test]
	fn test_desugar_if() {
		check_desugar_ok(
			HL::If(
				Box::new(HL::Bool(true)),
				Box::new(HL::Int(Ok(1))),
				Some(Box::new(HL::Int(Ok(2))))
			),
			If(
				box_expr(Bool(true)),
				box_expr(Int(Ok(1))),
				Some(box_expr(Int(Ok(2))))
			)
		);
	}

	#[test]
	fn test_desugar_while() {
		check_desugar_ok(
			HL::While(
				Box::new(HL::Bool(true)),
				Box::new(HL::Int(Ok(1)))
			),
			While(
				box_expr(Bool(true)),
				box_expr(Int(Ok(1)))
			)
		);
	}

	#[test]
	fn test_desugar_match() {
		check_desugar_ok(
			HL::Match(
				Box::new(HL::Int(Ok(1))),
				vec![
					(id!(a), vec![], HL::Bool(true)),
					(id!(b), vec![id!(z)], HL::Bool(false))
				]
			),
			Match(
				box_expr(Int(Ok(1))),
				vec![
					(id!(a), vec![], expr(Bool(true))),
					(id!(b), vec![id!(z)], expr(Bool(false)))
				]
			)
		);
	}

	#[test]
	fn test_desugar_binary_ops() {
		check_desugar_ok(
			HL::Binary(Box::new(HL::Int(Ok(1))), id!("+"), Box::new(HL::Int(Ok(2)))),
			MethodCall(box_expr(Int(Ok(1))), id!("op#+"), vec![expr(Int(Ok(2)))])
		);
	}



	#[test]
	fn test_typed_constants() {
		let pc = ParseContext::new();
		let symtab = pc.symtab_rc.borrow();

		let func = Function::new_incomplete(qid!(test), false, SpecType::Type(symtab.void_type.clone(), vec![]), vec![], 0);
		let mut cpc = CodeParseContext::new(&pc, &func);

		assert_eq!(cpc.typecheck_expr(&expr(Bool(true))).unwrap().typ, TypeRef(symtab.bool_type.clone(), vec![]));
		assert_eq!(cpc.typecheck_expr(&expr(Int(Ok(5)))).unwrap().typ, TypeRef(symtab.int_type.clone(), vec![]));
		assert_eq!(cpc.typecheck_expr(&expr(Real(Ok(5.)))).unwrap().typ, TypeRef(symtab.real_type.clone(), vec![]));
	}

	#[test]
	fn test_typed_variables() {
		let pc = ParseContext::new();
		let symtab = pc.symtab_rc.borrow();

		let args = vec![(SpecType::Type(symtab.int_type.clone(), vec![]), id!(var))];
		let func = Function::new_incomplete(qid!(test), false, SpecType::Type(symtab.void_type.clone(), vec![]), args, 0);
		let mut cpc = CodeParseContext::new(&pc, &func);

		// Get
		let e = cpc.typecheck_expr(&expr(LocalGet(id!(var))));
		assert_eq!(e.unwrap().typ, TypeRef(symtab.int_type.clone(), vec![]));
		let e = cpc.typecheck_expr(&expr(LocalGet(id!(nevar))));
		assert!(e.is_err() && e.unwrap_err() == ParserError::VariableNotFound(id!(nevar)));

		// Set
		let e = cpc.typecheck_expr(&expr(LocalSet(id!(var), box_expr(Int(Ok(5))))));
		assert_eq!(e.unwrap().typ, TypeRef(symtab.int_type.clone(), vec![]));
		let e = cpc.typecheck_expr(&expr(LocalSet(id!(var), box_expr(Bool(false)))));
		match e {
			Err(ParserError::TypeMismatch(_, _)) => {/*ok*/}
			_ => panic!("expected TypeMismatch")
		}
	}

	#[test]
	fn test_generic_func() {
		let pc = ParseContext::new();
		let symtab = pc.symtab_rc.borrow();

		let func = Function::new_incomplete(qid!(test), false, SpecType::Type(symtab.void_type.clone(), vec![]), vec![], 0);
		let mut cpc = CodeParseContext::new(&pc, &func);

		let maybe_typ = symtab.root.resolve(qid_slice!(Maybe)).unwrap().get_type().unwrap();

		let maybe_str_e = HLTypeRef(qid!(Maybe), vec![HLTypeRef(qid!(str), vec![])]);

		let maybe_str_none = expr(GlobalGet(maybe_str_e.clone(), id!(None)));
		assert_eq!(cpc.typecheck_expr(&maybe_str_none).unwrap().typ, TypeRef(maybe_typ.clone(), vec![TypeRef(symtab.str_type.clone(), vec![])]));

		let maybe_str_just = expr(FunctionCall(maybe_str_e, id!(Just), vec![expr(Str("hello".to_string()))]));
		assert_eq!(cpc.typecheck_expr(&maybe_str_just).unwrap().typ, TypeRef(maybe_typ.clone(), vec![TypeRef(symtab.str_type.clone(), vec![])]));
	}
}
