use crate::ast::*;
use crate::data::*;
use symbol::Symbol;
use std::rc::Rc;
use std::cell::RefCell;

pub fn call_func(symtab_rc: &Rc<RefCell<SymbolTable>>, parent_qid: &[Symbol], specials: &[TypeRef], id: Symbol, args: &[Value], arg_types: &[TypeRef], is_method: bool) -> Option<Value> {
	let expected_arg_count = arg_types.len() + if is_method { 1 } else { 0 };
	assert!(args.len() == expected_arg_count);
	let context = EvalContext { symtab_rc: Rc::clone(symtab_rc), locals: vec![] };
	let symtab = symtab_rc.borrow();
	let node = symtab.root.resolve(parent_qid)?;
	let node = node.resolve(&[id])?;
	let variants = node.get_function_variants()?;
	let func = variants.iter().find(|f| f.matches_types(specials, arg_types) && f.is_method == is_method)?;
	Some(context.eval_func(func, arg_types, args.to_vec()))
}

pub struct EvalContext {
	symtab_rc: Rc<RefCell<SymbolTable>>,
	locals: Vec<Value>
}

impl EvalContext {
	pub fn eval_func(&self, func: &Function, arg_types: &[TypeRef], args: Vec<Value>) -> Value {
		match &*func.borrow() {
			FunctionBody::Incomplete(_) => unreachable!("executing incomplete function"),
			FunctionBody::Expr(sub_expr) => {
				let mut sub_ctx = EvalContext { symtab_rc: Rc::clone(&self.symtab_rc), locals: args };
				sub_ctx.eval(&sub_expr)
			}
			FunctionBody::BuiltIn(f) => f(&self.symtab_rc, arg_types, &args)
		}
	}

	pub fn eval(&mut self, expr: &Expr) -> Value {
		use ExprKind::*;

		match &expr.expr {
			LocalGet(_) => unreachable!(),
			LocalSet(_, _) => unreachable!(),
			LocalGetResolved(index) => {
				self.locals[*index].clone()
			}
			LocalSetResolved(index, sub_expr) => {
				let value = self.eval(&sub_expr);
				self.locals[*index] = value.clone();
				value
			}
			GlobalGet(_, _) => unreachable!(),
			GlobalGetResolved(typeref, sym) => {
				let symtab = self.symtab_rc.borrow();
				let node = symtab.root.resolve(&typeref.0.name).unwrap();
				let node = node.resolve(&[*sym]).unwrap();
				let (_, value) = node.get_constant().unwrap();
				value
			}
			FunctionCall(_, _, _) => unreachable!(),
			FunctionCallResolved(func, arg_types, arg_exprs) => {
				let args = arg_exprs.iter().map(|e| self.eval(&e)).collect::<Vec<Value>>();
				self.eval_func(func, &arg_types, args)
			}
			MethodCall(_, _, _) => unreachable!(),
			MethodCallResolved(obj_expr, sym, arg_types, arg_exprs) => {
				// dynamic dispatch will go here eventually
				// low-hanging optimisation fruit here...
				let obj = self.eval(&obj_expr);
				let symtab_rc = Rc::clone(&self.symtab_rc);
				let symtab = symtab_rc.borrow();
				let type_node = symtab.root.resolve(&obj_expr.typ.0.name).unwrap();
				// TODO validate the length of the specials array
				let method_node = type_node.resolve(&[*sym]).unwrap();
				let variants = method_node.get_function_variants().unwrap();
				let func = variants.iter().find(|f| f.matches_types(&obj_expr.typ.1, &arg_types)).unwrap();
				let mut args = arg_exprs.iter().map(|e| self.eval(&e)).collect::<Vec<Value>>();
				args.insert(0, obj);
				self.eval_func(func, &arg_types, args)
			}
			If(cond_expr, if_true_expr, if_false_expr) => {
				let orig_local_depth = self.locals.len();
				let cond = self.eval(&cond_expr);
				if let Value::Bool(cond) = cond {
					if cond {
						let value = self.eval(&if_true_expr);
						self.locals.truncate(orig_local_depth);
						let symtab = self.symtab_rc.borrow();
						if expr.typ.0 == symtab.void_type { Value::Void } else { value }
					} else if if_false_expr.is_some() {
						let value = self.eval(&if_false_expr.as_ref().unwrap());
						self.locals.truncate(orig_local_depth);
						let symtab = self.symtab_rc.borrow();
						if expr.typ.0 == symtab.void_type { Value::Void } else { value }
					} else {
						self.locals.truncate(orig_local_depth);
						Value::Void
					}
				} else {
					unreachable!("if condition is expected to be a boolean")
				}
			}
			While(cond_expr, sub_expr) => {
				loop {
					let orig_local_depth = self.locals.len();
					let cond = self.eval(&cond_expr);
					self.locals.truncate(orig_local_depth);

					if let Value::Bool(cond) = cond {
						if !cond {
							break
						}
					} else {
						unreachable!("while condition is expected to be a boolean")
					}

					let orig_local_depth = self.locals.len();
					self.eval(&sub_expr);
					self.locals.truncate(orig_local_depth);
				}
				Value::Void
			}
			Let(_sym, sub_expr) => {
				let value = self.eval(&sub_expr);
				self.locals.push(value.clone());
				value
			}
			CodeBlock(sub_exprs) => {
				let orig_local_depth = self.locals.len();
				let mut value = Value::Void;
				for sub_expr in sub_exprs {
					value = self.eval(&sub_expr);
				}
				self.locals.truncate(orig_local_depth);
				value
			}
			Int(r)  => Value::Int(*r.as_ref().expect("int constant must be valid")),
			Real(r) => Value::Real(*r.as_ref().expect("real constant must be valid")),
			Bool(v) => Value::Bool(*v),
			Str(s)  => Obj::Str(s.clone()).to_heap(),
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use ExprKind::*;

	fn expr(k: ExprKind<Expr>, typ: &Type) -> Expr {
		Expr { expr: k, typ: TypeRef(typ.clone(), vec![]) }
	}
	fn box_expr(k: ExprKind<Expr>, typ: &Type) -> Box<Expr> {
		Box::new(expr(k, typ))
	}

	fn type_ref(typ: &Type) -> TypeRef {
		TypeRef(typ.clone(), vec![])
	}
	fn spec_type(typ: &Type) -> SpecType {
		SpecType::Type(typ.clone(), vec![])
	}

	#[test]
	fn test_locals() {
		let symtab_rc = SymbolTable::new_counted();
		let symtab = symtab_rc.borrow();
		let mut ctx = EvalContext { symtab_rc: Rc::clone(&symtab_rc), locals: vec![Value::Int(5)] };

		assert_eq!(
			ctx.eval(&expr(LocalGetResolved(0), &symtab.int_type)),
			Value::Int(5));
		ctx.eval(&expr(LocalSetResolved(0, box_expr(Int(Ok(10)), &symtab.int_type)), &symtab.int_type));
		assert_eq!(
			ctx.eval(&expr(LocalGetResolved(0), &symtab.int_type)),
			Value::Int(10));

		ctx.eval(&expr(Let(id!(test), box_expr(Int(Ok(20)), &symtab.int_type)), &symtab.int_type));
		assert_eq!(
			ctx.eval(&expr(LocalGetResolved(1), &symtab.int_type)),
			Value::Int(20));
	}

	#[test]
	fn test_constants() {
		let symtab_rc = SymbolTable::new_counted();
		let symtab = symtab_rc.borrow();
		let mut ctx = EvalContext { symtab_rc: Rc::clone(&symtab_rc), locals: vec![] };

		assert_eq!(ctx.eval(&expr(Int(Ok(5)), &symtab.int_type)), Value::Int(5));
		assert_eq!(ctx.eval(&expr(Real(Ok(0.5)), &symtab.real_type)), Value::Real(0.5));
		assert_eq!(ctx.eval(&expr(Bool(false), &symtab.bool_type)), Value::Bool(false));
	}

	#[test]
	fn test_block() {
		let symtab_rc = SymbolTable::new_counted();
		let symtab = symtab_rc.borrow();
		let mut ctx = EvalContext { symtab_rc: Rc::clone(&symtab_rc), locals: vec![] };

		let result = ctx.eval(&expr(CodeBlock(vec![
			expr(Let(id!(test), box_expr(Int(Ok(5)), &symtab.int_type)), &symtab.int_type),
			expr(Let(id!(test2), box_expr(Int(Ok(10)), &symtab.int_type)), &symtab.int_type),
			expr(LocalGetResolved(1), &symtab.int_type)
		]), &symtab.int_type));
		assert_eq!(result, Value::Int(10));

		assert_eq!(ctx.locals.len(), 0);
	}

	#[test]
	fn test_if() {
		let symtab_rc = SymbolTable::new_counted();
		let symtab = symtab_rc.borrow();
		let locals = vec![Value::Bool(true), Value::Int(0), Value::Real(0.0)];
		let mut ctx = EvalContext { symtab_rc: Rc::clone(&symtab_rc), locals };

		// test return of the if block
		let if_same_type = expr(If(
			box_expr(LocalGetResolved(0), &symtab.bool_type),
			box_expr(Int(Ok(1)), &symtab.int_type),
			Some(box_expr(Int(Ok(0)), &symtab.int_type))
		), &symtab.int_type);
		ctx.locals[0] = Value::Bool(true);
		assert_eq!(ctx.eval(&if_same_type), Value::Int(1));
		ctx.locals[0] = Value::Bool(false);
		assert_eq!(ctx.eval(&if_same_type), Value::Int(0));

		// test actions and return when both sides are different types
		let if_diff_type = expr(If(
			box_expr(LocalGetResolved(0), &symtab.bool_type),
			box_expr(LocalSetResolved(1, box_expr(Int(Ok(1)), &symtab.int_type)), &symtab.int_type),
			Some(box_expr(LocalSetResolved(2, box_expr(Real(Ok(1.0)), &symtab.real_type)), &symtab.real_type))
		), &symtab.void_type);

		ctx.locals[0] = Value::Bool(true);
		assert_eq!(ctx.locals[1], Value::Int(0));
		assert_eq!(ctx.locals[2], Value::Real(0.0));
		assert_eq!(ctx.eval(&if_diff_type), Value::Void);
		assert_eq!(ctx.locals[1], Value::Int(1));
		assert_eq!(ctx.locals[2], Value::Real(0.0));

		ctx.locals[0] = Value::Bool(false);
		ctx.locals[1] = Value::Int(0);
		assert_eq!(ctx.locals[1], Value::Int(0));
		assert_eq!(ctx.locals[2], Value::Real(0.0));
		assert_eq!(ctx.eval(&if_diff_type), Value::Void);
		assert_eq!(ctx.locals[1], Value::Int(0));
		assert_eq!(ctx.locals[2], Value::Real(1.0));
	}

	#[test]
	fn test_function_calls() {
		let symtab_rc = SymbolTable::new_counted();
		let symtab = symtab_rc.borrow();

		// test function:
		// if arg { 1 } else { 2 }
		let test_func = Function::new_expr(
			qid!(test),
			false,
			spec_type(&symtab.int_type),
			vec![(spec_type(&symtab.bool_type), id!(arg))],
			expr(If(
				box_expr(LocalGetResolved(0), &symtab.bool_type),
				box_expr(Int(Ok(1)), &symtab.int_type),
				Some(box_expr(Int(Ok(2)), &symtab.int_type))
			), &symtab.int_type)
		);
		let mut test_func_node = SymTabNode::new_function();
		test_func_node.get_function_variants_mut().unwrap().push(test_func.clone());

		// satisfy the borrow checker
		drop(symtab);
		let mut symtab_mut = symtab_rc.borrow_mut();
		symtab_mut.root.get_children_mut().unwrap().insert(id!(test), test_func_node);
		drop(symtab_mut);
		let symtab = symtab_rc.borrow();

		let mut ctx = EvalContext { symtab_rc: Rc::clone(&symtab_rc), locals: vec![Value::Bool(true)] };
		let call_expr = expr(
			FunctionCallResolved(test_func, vec![type_ref(&symtab.bool_type)], vec![expr(LocalGetResolved(0), &symtab.bool_type)]),
			&symtab.int_type
		);
		assert_eq!(ctx.eval(&call_expr), Value::Int(1));
		ctx.locals[0] = Value::Bool(false);
		assert_eq!(ctx.eval(&call_expr), Value::Int(2));
	}
}
