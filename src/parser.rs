use std::collections::HashMap;
use std::rc::Rc;
use std::cell::{Ref, RefMut, RefCell};
use symbol::Symbol;
use crate::ast::*;

lazy_static! {
	static ref ASSIGN_OP: Symbol = "=".into();
}

#[derive(Debug, PartialEq)]
pub enum ParserError {
	NameAlreadyUsed,
	TypeIsMissing,
	TypeIsIncomplete,
	TypeDependencyCycle,
	FunctionIsMissing,
	NoMatchingOverload,
	DuplicateOverload,
	TypeMismatch,
	InvalidAssignTarget,
	InvalidCall,
	LocalCannotBeVoid,
	BadIfConditionType,
	VariableNotFound,
	MissingNamespace
}
pub type Result<T> = std::result::Result<T, ParserError>;

#[derive(Debug, PartialEq, Eq)]
pub enum PrimitiveType {
	Void, Bool, Int, Real
}

#[derive(Debug, Clone)]
pub struct TypePtr(Rc<RefCell<TypeData>>);

impl PartialEq for TypePtr {
	fn eq(&self, other: &TypePtr) -> bool {
		std::rc::Rc::ptr_eq(&self.0, &other.0)
	}
}
impl TypePtr {
	fn borrow(&self) -> Ref<TypeData> { self.0.borrow() }
	fn borrow_mut(&mut self) -> RefMut<TypeData> { self.0.borrow_mut() }
}

#[derive(Debug)]
pub enum TypeBody {
	Incomplete,
	Enum,
	Primitive(PrimitiveType),
	Wrapper(TypePtr)
}
#[derive(Debug)]
pub struct TypeData {
	name: QualID,
	body: TypeBody
}

impl TypeData {
	fn ensure_complete(&self) -> Result<()> {
		if let TypeBody::Incomplete = self.body {
			Err(ParserError::TypeIsIncomplete)
		} else {
			Ok(())
		}
	}

	fn err_if_equal(a: &TypePtr, b: &TypePtr, err: ParserError) -> Result<()> {
		if a == b {
			Err(err)
		} else {
			Ok(())
		}
	}
	fn err_if_not_equal(a: &TypePtr, b: &TypePtr, err: ParserError) -> Result<()> {
		if a == b {
			Ok(())
		} else {
			Err(err)
		}
	}
	fn ensure_equal(a: &TypePtr, b: &TypePtr) -> Result<()> {
		println!("comparing {:?} and {:?}", a.0.borrow().name, b.0.borrow().name);
		TypeData::err_if_not_equal(a, b, ParserError::TypeMismatch)
	}
}

pub type FunctionPtr = Rc<RefCell<Function>>;
pub enum FunctionBody {
	Incomplete(usize),
	BuiltIn,
	Expr(Expr)
}
pub struct Function {
	name: QualID,
	is_method: bool,
	arguments: Vec<(TypePtr, Symbol)>,
	return_type: TypePtr,
	body: FunctionBody
}

impl Function {
	fn matches_types(&self, types: &[TypePtr]) -> bool {
		(self.arguments.len() == types.len()) &&
		types.iter().zip(self.arguments.iter()).all(|(check, (arg, _))| check == arg)
	}

	fn matches_arguments(&self, args: &[(TypePtr, Symbol)]) -> bool {
		(self.arguments.len() == args.len()) &&
		args.iter().zip(self.arguments.iter()).all(|((check, _), (arg, _))| check == arg)
	}
}

enum NodeData {
	Nothing,
	Function(Vec<FunctionPtr>),
	Type(TypePtr),
	SymbolConstant(Symbol)
}

struct Node {
	children: HashMap<Symbol, Node>,
	what: NodeData
}

impl Node {
	fn new(what: NodeData) -> Node {
		Node { children: HashMap::new(), what }
	}
	fn from_type(typ: TypePtr) -> Node {
		Node::new(NodeData::Type(typ))
	}
	fn from_function(func: FunctionPtr) -> Node {
		Node::new(NodeData::Function(vec![func]))
	}
	fn from_symbol_constant(symbol: &Symbol) -> Node {
		Node::new(NodeData::SymbolConstant(symbol.clone()))
	}

	fn get_function_group(&self) -> Option<&[FunctionPtr]> {
		if let NodeData::Function(p) = &self.what { Some(p) } else { None }
	}

	fn get_function_group_mut(&mut self) -> Option<&mut Vec<FunctionPtr>> {
		if let NodeData::Function(p) = &mut self.what { Some(p) } else { None }
	}

	fn get_type(&self) -> Option<TypePtr> {
		if let NodeData::Type(t) = &self.what { Some(t.clone()) } else { None }
	}

	fn resolve(&self, name: &[Symbol]) -> Option<&Node> {
		match name.len() {
			0 => Some(self),
			1 => self.children.get(name.first().unwrap()),
			_ => {
				let (name, next) = name.split_first().unwrap();
				self.children.get(name)?.resolve(next)
			}
		}
	}

	fn resolve_mut(&mut self, name: &[Symbol]) -> Option<&mut Node> {
		match name.len() {
			0 => Some(self),
			1 => self.children.get_mut(name.first().unwrap()),
			_ => {
				let (name, next) = name.split_first().unwrap();
				self.children.get_mut(name)?.resolve_mut(next)
			}
		}
	}

	fn resolve_type(&self, name: &[Symbol]) -> Option<TypePtr> {
		self.resolve(name)?.get_type()
	}

	fn require_type(&self, name: &[Symbol]) -> Result<TypePtr> {
		self.resolve_type(name).ok_or(ParserError::TypeIsMissing)
	}

	fn resolve_function_group(&self, name: &[Symbol]) -> Option<&[FunctionPtr]> {
		self.resolve(name)?.get_function_group()
	}

	fn resolve_incomplete_function(&self, name: &[Symbol], index: usize) -> Option<FunctionPtr> {
		let group = self.resolve_function_group(name)?;
		for func in group {
			if let FunctionBody::Incomplete(i) = func.borrow().body {
				if i == index {
					return Some(func.clone());
				}
			}
		}
		None
	}

	fn require_compatible_function(&self, name: &[Symbol], args: &[TypePtr]) -> Result<FunctionPtr> {
		let group = self.resolve_function_group(name);
		let group = group.ok_or(ParserError::FunctionIsMissing)?;
		for func in group {
			if func.borrow().matches_types(args) {
				return Ok(func.clone());
			}
		}
		Err(ParserError::NoMatchingOverload)
	}
}

struct ParseContext {
	void_type: TypePtr,
	bool_type: TypePtr,
	int_type: TypePtr,
	real_type: TypePtr,
	root: Node
}

impl TypeData {
	fn from_primitive(name: &str, ptyp: PrimitiveType) -> TypePtr {
		TypeData::from_body(vec![name.into()], TypeBody::Primitive(ptyp))
	}

	fn from_body(name: QualID, body: TypeBody) -> TypePtr {
		TypePtr(Rc::new(RefCell::new(TypeData { name, body })))
	}
}

impl ParseContext {
	fn new() -> ParseContext {
		use PrimitiveType::*;
		let mut ctx = ParseContext {
			void_type: TypeData::from_primitive("void", Void),
			bool_type: TypeData::from_primitive("bool", Bool),
			int_type: TypeData::from_primitive("int", Int),
			real_type: TypeData::from_primitive("real", Real),
			root: Node::new(NodeData::Nothing)
		};
		ctx.add_default_types();
		ctx
	}

	fn add_default_types(&mut self) {
		self.add_type(self.void_type.clone()).unwrap();
		self.add_type(self.bool_type.clone()).unwrap();
		self.add_type(self.int_type.clone()).unwrap();
		self.add_type(self.real_type.clone()).unwrap();
	}

	fn add_type(&mut self, typ: TypePtr) -> Result<()> {
		let node = Node::from_type(typ.clone());
		let typ = typ.borrow();
		let (name, container) = typ.name.split_last().unwrap();
		let container = self.root.resolve_mut(container).ok_or(ParserError::MissingNamespace)?;
		if container.children.contains_key(&name) {
			Err(ParserError::NameAlreadyUsed)
		} else {
			container.children.insert(*name, node);
			Ok(())
		}
	}

	fn replace_incomplete_type(&mut self, name: &[Symbol], typedef: &TypeDef) -> Result<()> {
		let node = self.root.resolve_mut(name).expect("incomplete type should exist!");
		let mut typ = node.get_type().expect("incomplete type should be a type");

		match typedef {
			TypeDef::Wrap(target_ref) => {
				let target_type = self.root.require_type(target_ref)?;
				target_type.borrow().ensure_complete()?;
				typ.borrow_mut().body = TypeBody::Wrapper(target_type.clone());

				self.add_builtin_function(&typ, &"wrap".into(), &typ, &[(target_type.clone(), "v".into())])?;
				self.add_builtin_method(&typ, &"unwrap".into(), &target_type, &[])?;

				Ok(())
			}
			TypeDef::Enum(ids) => {
				typ.borrow_mut().body = TypeBody::Enum;
				for id in ids {
					node.children.insert(*id, Node::from_symbol_constant(id));
				}
				Ok(())
			}
		}
	}

	fn collect_types(&mut self, prog: &Program) -> Result<()> {
		let mut typedefs: Vec<&GlobalDef> = vec![];

		for def in prog {
			if let GlobalDef::Type(name, _) = def {
				self.add_type(TypeData::from_body(name.clone(), TypeBody::Incomplete))?;
				typedefs.push(&def);
			}
		}

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

	fn add_builtin_function(&mut self, typ: &TypePtr, name: &Symbol, return_type: &TypePtr, args: &[(TypePtr, Symbol)]) -> Result<()> {
		self.add_builtin_fn(typ, false, name, return_type, args)
	}
	fn add_builtin_method(&mut self, typ: &TypePtr, name: &Symbol, return_type: &TypePtr, args: &[(TypePtr, Symbol)]) -> Result<()> {
		self.add_builtin_fn(typ, true, name, return_type, args)
	}
	fn add_builtin_fn(&mut self, typ: &TypePtr, is_method: bool, name: &Symbol, return_type: &TypePtr, args: &[(TypePtr, Symbol)]) -> Result<()> {
		let mut full_name = typ.borrow().name.clone();
		full_name.push(*name);
		let func = Function {
			name: full_name,
			is_method,
			arguments: args.to_vec(),
			return_type: return_type.clone(),
			body: FunctionBody::BuiltIn
		};
		self.add_function(Rc::new(RefCell::new(func)))
	}

	fn add_function(&mut self, func: FunctionPtr) -> Result<()> {
		let func_copy = func.clone();
		let func = func.borrow();
		let (name, container) = func.name.split_last().unwrap();
		let container = self.root.resolve_mut(container).ok_or(ParserError::MissingNamespace)?;
		if let Some(existing) = container.children.get_mut(&name) {
			// add to the existing function?
			let group = existing.get_function_group().ok_or(ParserError::NameAlreadyUsed)?;
			if group.iter().any(|c| c.borrow().matches_arguments(&func.arguments)) {
				Err(ParserError::DuplicateOverload)
			} else {
				existing.get_function_group_mut().unwrap().push(func_copy);
				Ok(())
			}
		} else {
			container.children.insert(*name, Node::from_function(func_copy));
			Ok(())
		}
	}

	fn collect_function_specs(&mut self, prog: &Program) -> Result<()> {
		for (i, def) in prog.iter().enumerate() {
			if let GlobalDef::Func(name, func_type, args, return_type, _) = def {
				let processed_args: Result<Vec<(TypePtr, Symbol)>> = args.iter().map(
					|(tref, arg_id)|
					self.root.require_type(tref).map(|t| (t, arg_id.clone()))
				).collect();

				let func = Function {
					name: name.clone(),
					is_method: match func_type {
						FuncType::Function => false,
						FuncType::Method   => true
					},
					arguments: processed_args?,
					return_type: self.root.require_type(return_type)?,
					body: FunctionBody::Incomplete(i)
				};
				self.add_function(Rc::new(RefCell::new(func)))?;
			}
		}

		Ok(())
	}

	fn collect_function_bodies(&mut self, prog: &Program) -> Result<()> {
		for (i, def) in prog.iter().enumerate() {
			if let GlobalDef::Func(name, _, _, _, hlexpr) = def {
				let func = self.root.resolve_incomplete_function(name, i).expect("filling body for non-existent function");

				println!("SUGARED EXPRESSION: {:?}", hlexpr);
				let expr = desugar_expr(hlexpr)?;
				println!("DESUGARED EXPRESSION: {:?}", expr);
				self.check_function(&func.borrow(), &expr)?;
				func.borrow_mut().body = FunctionBody::Expr(expr);
			}
		}

		Ok(())
	}


	fn check_function(&mut self, func: &Function, expr: &Expr) -> Result<()> {
		let mut ctx = CodeParseContext::new(self, func);
		let result_type = ctx.typecheck_expr(expr)?;

		// any final result is ok if the function returns void
		if func.return_type != self.void_type {
			TypeData::ensure_equal(&result_type, &func.return_type)?;
		}
		Ok(())
	}
}


fn desugar_expr(expr: &HLExpr) -> Result<Expr> {
	match expr {
		HLExpr::ID(qid) => {
			if qid.len() == 1 {
				let var = qid.first().unwrap().clone();
				Ok(Expr::LocalGet(var))
			} else {
				Ok(Expr::GlobalGet(qid.clone()))
			}
		}
		HLExpr::Binary(lhs, op, rhs) if *op == *ASSIGN_OP => {
			match lhs {
				box HLExpr::ID(syms) if syms.len() == 1 => {
					// Assign to local
					let var   = syms.first().unwrap().clone();
					let value = Box::new(desugar_expr(&*rhs)?);
					Ok(Expr::LocalSet(var, value))
				}
				box HLExpr::PropAccess(obj, sym) => {
					// Set property
					let obj   = Box::new(desugar_expr(&*obj)?);
					let sym   = (sym.as_str().to_string() + "=").into();
					let value = desugar_expr(&*rhs)?;
					Ok(Expr::MethodCall(obj, sym, vec![value]))
				}
				_ => Err(ParserError::InvalidAssignTarget)
			}
		}
		HLExpr::Binary(lhs, op, rhs) => {
			// Binary op becomes a method call
			let lhs = Box::new(desugar_expr(&*lhs)?);
			let sym = ("op#".to_string() + op).into();
			let rhs = desugar_expr(&*rhs)?;
			Ok(Expr::MethodCall(lhs, sym, vec![rhs]))
		}
		HLExpr::PropAccess(obj, sym) => {
			// Naked PropAccess maps to an argument-less method call
			let obj = Box::new(desugar_expr(&*obj)?);
			Ok(Expr::MethodCall(obj, *sym, vec![]))
		}
		HLExpr::Call(box HLExpr::PropAccess(obj, sym), args) => {
			// Call on a property becomes a method call
			let obj  = Box::new(desugar_expr(&*obj)?);
			let args = args.iter().map(desugar_expr).collect::<Result<Vec<Expr>>>()?;
			Ok(Expr::MethodCall(obj, *sym, args))
		}
		HLExpr::Call(box HLExpr::ID(qid), args) => {
			// Call on a qualified ID becomes a function call
			let args = args.iter().map(desugar_expr).collect::<Result<Vec<Expr>>>()?;
			Ok(Expr::FunctionCall(qid.clone(), args))
		}
		HLExpr::Call(_, _) => Err(ParserError::InvalidCall),
		HLExpr::If(cond, if_true, if_false) => {
			let cond     = Box::new(desugar_expr(&*cond)?);
			let if_true  = Box::new(desugar_expr(&*if_true)?);
			let if_false = match if_false {
				None        => None,
				Some(box e) => Some(Box::new(desugar_expr(e)?))
			};
			Ok(Expr::If(cond, if_true, if_false))
		}
		HLExpr::Let(sym, value) => {
			let value = Box::new(desugar_expr(&*value)?);
			Ok(Expr::Let(sym.clone(), value))
		}
		HLExpr::CodeBlock(exprs) => {
			let exprs = exprs.iter().map(desugar_expr).collect::<Result<Vec<Expr>>>()?;
			Ok(Expr::CodeBlock(exprs))
		}
		HLExpr::Int(result)  => Ok(Expr::Int(result.clone())),
		HLExpr::Real(result) => Ok(Expr::Real(result.clone())),
		HLExpr::Bool(value)  => Ok(Expr::Bool(*value))
	}
}


struct CodeParseContext<'a> {
	parent: &'a ParseContext,
	locals: Vec<(TypePtr, Symbol)>
}

impl<'a> CodeParseContext<'a> {
	fn new(parent_ctx: &'a ParseContext, func: &Function) -> CodeParseContext<'a> {
		let mut locals = vec![];
		if func.is_method {
			let owner_name = func.name.split_last().unwrap().1;
			let owner = parent_ctx.root.resolve_type(owner_name).unwrap();
			locals.push((owner, "self".into()));
		}
		locals.extend(func.arguments.iter().cloned());
		CodeParseContext {
			parent: parent_ctx,
			locals
		}
	}

	fn resolve_local_var(&mut self, sym: &Symbol) -> Result<(usize, TypePtr)> {
		for (i, (var_type, var_name)) in self.locals.iter().enumerate().rev() {
			if sym == var_name {
				return Ok((i, var_type.clone()));
			}
		}
		Err(ParserError::VariableNotFound)
	}

	fn typecheck_expr(&mut self, expr: &Expr) -> Result<TypePtr> {
		use Expr::*;
		match expr {
			LocalGet(sym) => Ok(self.resolve_local_var(sym)?.1),
			LocalSet(sym, value) => {
				let (_, var_type) = self.resolve_local_var(sym)?;
				let value_type = self.typecheck_expr(value)?;
				Type::ensure_equal(&var_type, &value_type)?;
				Ok(value_type)
			}
			GlobalGet(qid) => {
				// right now this is JUST for enum constants
				let (sym, node_name) = qid.split_last().unwrap();
				let node = self.parent.root.resolve(node_name);
				let node = node.ok_or(ParserError::MissingNamespace)?;
				if let Some(Node { what: NodeData::SymbolConstant(_), .. }) = node.children.get(sym) {
					// this is a valid enum constant
					Ok(self.parent.root.resolve_type(node_name).unwrap())
				} else {
					Err(ParserError::VariableNotFound)
				}
			}
			FunctionCall(qid, args) => {
				let arg_types = args.iter().map(|e| self.typecheck_expr(e)).collect::<Result<Vec<TypePtr>>>()?;
				let func = self.parent.root.require_compatible_function(qid, &arg_types)?;
				let return_type = func.borrow().return_type.clone();
				Ok(return_type)
			}
			MethodCall(obj, sym, args) => {
				let obj_type = self.typecheck_expr(obj)?;
				let arg_types = args.iter().map(|e| self.typecheck_expr(e)).collect::<Result<Vec<TypePtr>>>()?;
				let type_node = self.parent.root.resolve(&obj_type.borrow().name).expect("type missing");
				let method = type_node.require_compatible_function(&[*sym], &arg_types)?;
				let return_type = method.borrow().return_type.clone();
				Ok(return_type)
			}
			If(cond, if_true, if_false) => {
				let cond_type = self.typecheck_expr(cond)?;
				TypeData::err_if_not_equal(&cond_type, &self.parent.bool_type, ParserError::BadIfConditionType)?;
				let if_true_type = self.typecheck_expr(if_true)?;
				match if_false {
					None => {
						// Without a False, this always returns void
						Ok(self.parent.void_type.clone())
					}
					Some(e) => {
						let if_false_type = self.typecheck_expr(e)?;
						if if_true_type == if_false_type {
							Ok(if_true_type)
						} else {
							// If both branches have differing return types, return void
							Ok(self.parent.void_type.clone())
						}
					}
				}
			}
			Let(sym, value) => {
				let value_type = self.typecheck_expr(value)?;
				TypeData::err_if_equal(&value_type, &self.parent.void_type, ParserError::LocalCannotBeVoid)?;
				self.locals.push((value_type.clone(), *sym));
				Ok(value_type)
			}
			CodeBlock(exprs) => {
				let mut result_type = self.parent.void_type.clone();
				for sub_expr in exprs {
					result_type = self.typecheck_expr(sub_expr)?.clone();
				}
				Ok(result_type)
			}
			Int(_) => Ok(self.parent.int_type.clone()),
			Real(_) => Ok(self.parent.real_type.clone()),
			Bool(_) => Ok(self.parent.bool_type.clone())
		}
	}
}


pub fn magic(prog: &Program) {
	let mut ctx = ParseContext::new();
	ctx.collect_types(prog).expect("Yep");
	ctx.collect_function_specs(prog).expect("Yep");
	ctx.collect_function_bodies(prog).expect("Yep");
}


#[cfg(test)]
mod tests {
	use super::*;
	use HLExpr as HL;
	use Expr::*;

	fn check_desugar_ok(hl: HLExpr, res: Expr) {
		assert_eq!(desugar_expr(&hl), Ok(res));
	}
	fn check_desugar_err(hl: HLExpr, err: ParserError) {
		assert_eq!(desugar_expr(&hl), Err(err));
	}

	#[test]
	fn test_desugar_get() {
		check_desugar_ok(
			HL::ID(vec!["foo".into()]),
			LocalGet("foo".into())
		);

		check_desugar_ok(
			HL::ID(vec!["foo".into(), "bar".into()]),
			GlobalGet(vec!["foo".into(), "bar".into()])
		);
	}

	#[test]
	fn test_desugar_assign_ok() {
		let hl_int1 = Box::new(HL::Int(Ok(1)));
		let int1 = Box::new(Int(Ok(1)));
		let hl_foo = Box::new(HL::ID(vec!["foo".into()]));

		check_desugar_ok(
			HL::Binary(hl_foo.clone(), "=".into(), hl_int1.clone()),
			LocalSet("foo".into(), int1.clone())
		);
		check_desugar_ok(
			HL::Binary(Box::new(HL::PropAccess(hl_foo.clone(), "bar".into())), "=".into(), hl_int1.clone()),
			MethodCall(Box::new(LocalGet("foo".into())), "bar=".into(), vec![Int(Ok(1))])
		);
	}

	#[test]
	fn test_desugar_assign_err() {
		fn check(target: HLExpr) {
			check_desugar_err(
				HL::Binary(Box::new(target), "=".into(), Box::new(HL::Int(Ok(1)))),
				ParserError::InvalidAssignTarget
			);
		}

		check(HL::ID(vec!["a".into(), "b".into()]));
		check(HL::Int(Ok(1)));
		check(HL::Real(Ok(1.)));
		check(HL::Bool(true));
		check(HL::Binary(Box::new(HL::Int(Ok(1))), "+".into(), Box::new(HL::Int(Ok(2)))));
	}

	#[test]
	fn test_desugar_calls() {
		check_desugar_ok(
			HL::Call(Box::new(HL::ID(vec!["a".into()])), vec![]),
			FunctionCall(vec!["a".into()], vec![])
		);
		check_desugar_ok(
			HL::Call(Box::new(HL::PropAccess(Box::new(HL::ID(vec!["a".into()])), "b".into())), vec![]),
			MethodCall(Box::new(LocalGet("a".into())), "b".into(), vec![])
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
				Box::new(Bool(true)),
				Box::new(Int(Ok(1))),
				Some(Box::new(Int(Ok(2))))
			)
		);
	}

	#[test]
	fn test_desugar_binary_ops() {
		check_desugar_ok(
			HL::Binary(Box::new(HL::Int(Ok(1))), "+".into(), Box::new(HL::Int(Ok(2)))),
			MethodCall(Box::new(Int(Ok(1))), "op#+".into(), vec![Int(Ok(2))])
		);
	}



	#[test]
	fn test_typed_constants() {
		let pc = ParseContext::new();
		let func = Function {
			name: vec!["test".into()],
			is_method: false,
			arguments: vec![],
			return_type: pc.void_type.clone(),
			body: FunctionBody::Incomplete(0)
		};
		let mut cpc = CodeParseContext::new(&pc, &func);

		assert_eq!(cpc.typecheck_expr(&Bool(true)), Ok(pc.bool_type.clone()));
		assert_eq!(cpc.typecheck_expr(&Int(Ok(5))), Ok(pc.int_type.clone()));
		assert_eq!(cpc.typecheck_expr(&Real(Ok(5.))), Ok(pc.real_type.clone()));
	}

	#[test]
	fn test_typed_variables() {
		let pc = ParseContext::new();
		let func = Function {
			name: vec!["test".into()],
			is_method: false,
			arguments: vec![(pc.int_type.clone(), "var".into())],
			return_type: pc.void_type.clone(),
			body: FunctionBody::Incomplete(0)
		};
		let mut cpc = CodeParseContext::new(&pc, &func);

		// Get
		assert_eq!(
			cpc.typecheck_expr(&LocalGet("var".into())),
			Ok(pc.int_type.clone()));
		assert_eq!(
			cpc.typecheck_expr(&LocalGet("nevar".into())),
			Err(ParserError::VariableNotFound));

		// Set
		assert_eq!(
			cpc.typecheck_expr(&LocalSet("var".into(), Box::new(Int(Ok(5))))),
			Ok(pc.int_type.clone()));
		assert_eq!(
			cpc.typecheck_expr(&LocalSet("var".into(), Box::new(Bool(false)))),
			Err(ParserError::TypeMismatch));
	}
}
