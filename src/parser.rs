use std::collections::HashMap;
use std::rc::Rc;
use std::ops::Deref;
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

impl Type {
	fn ensure_complete(&self) -> Result<()> {
		if let TypeBody::Incomplete = *self.borrow() {
			Err(ParserError::TypeIsIncomplete)
		} else {
			Ok(())
		}
	}

	fn err_if_equal(a: &Type, b: &Type, err: ParserError) -> Result<()> {
		if a == b {
			Err(err)
		} else {
			Ok(())
		}
	}
	fn err_if_not_equal(a: &Type, b: &Type, err: ParserError) -> Result<()> {
		if a == b {
			Ok(())
		} else {
			Err(err)
		}
	}
	fn ensure_equal(a: &Type, b: &Type) -> Result<()> {
		println!("comparing {:?} and {:?}", a.name, b.name);
		Type::err_if_not_equal(a, b, ParserError::TypeMismatch)
	}
}

#[derive(Debug, Clone)]
pub struct Function(Rc<FunctionData>);
#[derive(Debug)]
pub enum FunctionBody {
	Incomplete(usize),
	BuiltIn,
	Expr(Expr)
}
#[derive(Debug)]
pub struct FunctionData {
	name: QualID,
	is_method: bool,
	arguments: Vec<(Type, Symbol)>,
	return_type: Type,
	body: RefCell<FunctionBody>
}

impl Deref for Function {
	type Target = FunctionData;
	fn deref(&self) -> &Self::Target { &self.0 }
}

impl Function {
	fn borrow(&self) -> Ref<FunctionBody> { self.0.body.borrow() }
	fn borrow_mut(&mut self) -> RefMut<FunctionBody> { self.0.body.borrow_mut() }

	fn matches_types(&self, types: &[Type]) -> bool {
		(self.0.arguments.len() == types.len()) &&
		types.iter().zip(self.0.arguments.iter()).all(|(check, (arg, _))| check == arg)
	}

	fn matches_arguments(&self, args: &[(Type, Symbol)]) -> bool {
		(self.0.arguments.len() == args.len()) &&
		args.iter().zip(self.0.arguments.iter()).all(|((check, _), (arg, _))| check == arg)
	}
}

enum NodeData {
	Nothing,
	Function(Vec<Function>),
	Type(Type),
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
	fn from_type(typ: Type) -> Node {
		Node::new(NodeData::Type(typ))
	}
	fn from_function(func: Function) -> Node {
		Node::new(NodeData::Function(vec![func]))
	}
	fn from_symbol_constant(symbol: &Symbol) -> Node {
		Node::new(NodeData::SymbolConstant(symbol.clone()))
	}

	fn get_function_group(&self) -> Option<&[Function]> {
		if let NodeData::Function(p) = &self.what { Some(p) } else { None }
	}

	fn get_function_group_mut(&mut self) -> Option<&mut Vec<Function>> {
		if let NodeData::Function(p) = &mut self.what { Some(p) } else { None }
	}

	fn get_type(&self) -> Option<Type> {
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

	fn resolve_type(&self, name: &[Symbol]) -> Option<Type> {
		self.resolve(name)?.get_type()
	}

	fn require_type(&self, name: &[Symbol]) -> Result<Type> {
		self.resolve_type(name).ok_or(ParserError::TypeIsMissing)
	}

	fn resolve_function_group(&self, name: &[Symbol]) -> Option<&[Function]> {
		self.resolve(name)?.get_function_group()
	}

	fn resolve_incomplete_function(&self, name: &[Symbol], index: usize) -> Option<Function> {
		let group = self.resolve_function_group(name)?;
		for func in group {
			if let FunctionBody::Incomplete(i) = *func.borrow() {
				if i == index {
					return Some(func.clone());
				}
			}
		}
		None
	}

	fn require_compatible_function(&self, name: &[Symbol], args: &[Type]) -> Result<Function> {
		let group = self.resolve_function_group(name);
		let group = group.ok_or(ParserError::FunctionIsMissing)?;
		for func in group {
			if func.matches_types(args) {
				return Ok(func.clone());
			}
		}
		Err(ParserError::NoMatchingOverload)
	}
}

struct ParseContext {
	void_type: Type,
	bool_type: Type,
	int_type: Type,
	real_type: Type,
	root: Node
}

impl ParseContext {
	fn new() -> ParseContext {
		use PrimitiveType::*;
		let mut ctx = ParseContext {
			void_type: Type::from_primitive("void", Void),
			bool_type: Type::from_primitive("bool", Bool),
			int_type: Type::from_primitive("int", Int),
			real_type: Type::from_primitive("real", Real),
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

	fn add_type(&mut self, typ: Type) -> Result<()> {
		let node = Node::from_type(typ.clone());
		let (name, container) = typ.name.split_last().unwrap();
		let container = self.root.resolve_mut(container).ok_or(ParserError::MissingNamespace)?;
		if container.children.contains_key(&name) {
			Err(ParserError::NameAlreadyUsed)
		} else {
			container.children.insert(*name, node);
			Ok(())
		}
	}

	fn replace_incomplete_type(&mut self, name: &[Symbol], typedef: &HLTypeDef) -> Result<()> {
		let node = self.root.resolve_mut(name).expect("incomplete type should exist!");
		let mut typ = node.get_type().expect("incomplete type should be a type");

		match typedef {
			HLTypeDef::Wrap(target_ref) => {
				let target_type = self.root.require_type(target_ref)?;
				target_type.ensure_complete()?;
				*typ.borrow_mut() = TypeBody::Wrapper(target_type.clone());

				self.add_builtin_function(&typ, &"wrap".into(), &typ, &[(target_type.clone(), "v".into())])?;
				self.add_builtin_method(&typ, &"unwrap".into(), &target_type, &[])?;

				Ok(())
			}
			HLTypeDef::Enum(ids) => {
				*typ.borrow_mut() = TypeBody::Enum;
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
				self.add_type(Type::from_body(name.clone(), TypeBody::Incomplete))?;
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

	fn add_builtin_function(&mut self, typ: &Type, name: &Symbol, return_type: &Type, args: &[(Type, Symbol)]) -> Result<()> {
		self.add_builtin_fn(typ, false, name, return_type, args)
	}
	fn add_builtin_method(&mut self, typ: &Type, name: &Symbol, return_type: &Type, args: &[(Type, Symbol)]) -> Result<()> {
		self.add_builtin_fn(typ, true, name, return_type, args)
	}
	fn add_builtin_fn(&mut self, typ: &Type, is_method: bool, name: &Symbol, return_type: &Type, args: &[(Type, Symbol)]) -> Result<()> {
		let mut full_name = typ.name.clone();
		full_name.push(*name);
		let func = FunctionData {
			name: full_name,
			is_method,
			arguments: args.to_vec(),
			return_type: return_type.clone(),
			body: RefCell::new(FunctionBody::BuiltIn)
		};
		self.add_function(Function(Rc::new(func)))
	}

	fn add_function(&mut self, func: Function) -> Result<()> {
		let func_copy = func.clone();
		let (name, container) = func.name.split_last().unwrap();
		let container = self.root.resolve_mut(container).ok_or(ParserError::MissingNamespace)?;
		if let Some(existing) = container.children.get_mut(&name) {
			// add to the existing function?
			let group = existing.get_function_group().ok_or(ParserError::NameAlreadyUsed)?;
			if group.iter().any(|c| c.matches_arguments(&func.arguments)) {
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
				let processed_args: Result<Vec<(Type, Symbol)>> = args.iter().map(
					|(tref, arg_id)|
					self.root.require_type(tref).map(|t| (t, arg_id.clone()))
				).collect();

				let func = FunctionData {
					name: name.clone(),
					is_method: match func_type {
						FuncType::Function => false,
						FuncType::Method   => true
					},
					arguments: processed_args?,
					return_type: self.root.require_type(return_type)?,
					body: RefCell::new(FunctionBody::Incomplete(i))
				};
				self.add_function(Function(Rc::new(func)))?;
			}
		}

		Ok(())
	}

	fn collect_function_bodies(&mut self, prog: &Program) -> Result<()> {
		for (i, def) in prog.iter().enumerate() {
			if let GlobalDef::Func(name, _, _, _, hlexpr) = def {
				let mut func = self.root.resolve_incomplete_function(name, i).expect("filling body for non-existent function");

				println!("SUGARED EXPRESSION: {:?}", hlexpr);
				let expr = desugar_expr(hlexpr)?;
				println!("DESUGARED EXPRESSION: {:?}", expr);
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
		if func.return_type != self.void_type {
			Type::ensure_equal(&result_expr.typ, &func.return_type)?;
		}
		Ok(result_expr)
	}
}


fn desugar_expr(expr: &HLExpr) -> Result<UncheckedExpr> {
	match expr {
		HLExpr::ID(qid) => {
			if qid.len() == 1 {
				let var = qid.first().unwrap().clone();
				Ok(UncheckedExpr(ExprKind::LocalGet(var)))
			} else {
				Ok(UncheckedExpr(ExprKind::GlobalGet(qid.clone())))
			}
		}
		HLExpr::Binary(lhs, op, rhs) if *op == *ASSIGN_OP => {
			match lhs {
				box HLExpr::ID(syms) if syms.len() == 1 => {
					// Assign to local
					let var   = syms.first().unwrap().clone();
					let value = Box::new(desugar_expr(&*rhs)?);
					Ok(UncheckedExpr(ExprKind::LocalSet(var, value)))
				}
				box HLExpr::PropAccess(obj, sym) => {
					// Set property
					let obj   = Box::new(desugar_expr(&*obj)?);
					let sym   = (sym.as_str().to_string() + "=").into();
					let value = desugar_expr(&*rhs)?;
					Ok(UncheckedExpr(ExprKind::MethodCall(obj, sym, vec![value])))
				}
				_ => Err(ParserError::InvalidAssignTarget)
			}
		}
		HLExpr::Binary(lhs, op, rhs) => {
			// Binary op becomes a method call
			let lhs = Box::new(desugar_expr(&*lhs)?);
			let sym = ("op#".to_string() + op).into();
			let rhs = desugar_expr(&*rhs)?;
			Ok(UncheckedExpr(ExprKind::MethodCall(lhs, sym, vec![rhs])))
		}
		HLExpr::PropAccess(obj, sym) => {
			// Naked PropAccess maps to an argument-less method call
			let obj = Box::new(desugar_expr(&*obj)?);
			Ok(UncheckedExpr(ExprKind::MethodCall(obj, *sym, vec![])))
		}
		HLExpr::Call(box HLExpr::PropAccess(obj, sym), args) => {
			// Call on a property becomes a method call
			let obj  = Box::new(desugar_expr(&*obj)?);
			let args = args.iter().map(desugar_expr).collect::<Result<Vec<UncheckedExpr>>>()?;
			Ok(UncheckedExpr(ExprKind::MethodCall(obj, *sym, args)))
		}
		HLExpr::Call(box HLExpr::ID(qid), args) => {
			// Call on a qualified ID becomes a function call
			let args = args.iter().map(desugar_expr).collect::<Result<Vec<UncheckedExpr>>>()?;
			Ok(UncheckedExpr(ExprKind::FunctionCall(qid.clone(), args)))
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
		HLExpr::Let(sym, value) => {
			let value = Box::new(desugar_expr(&*value)?);
			Ok(UncheckedExpr(ExprKind::Let(sym.clone(), value)))
		}
		HLExpr::CodeBlock(exprs) => {
			let exprs = exprs.iter().map(desugar_expr).collect::<Result<Vec<UncheckedExpr>>>()?;
			Ok(UncheckedExpr(ExprKind::CodeBlock(exprs)))
		}
		HLExpr::Int(result)  => Ok(UncheckedExpr(ExprKind::Int(result.clone()))),
		HLExpr::Real(result) => Ok(UncheckedExpr(ExprKind::Real(result.clone()))),
		HLExpr::Bool(value)  => Ok(UncheckedExpr(ExprKind::Bool(*value)))
	}
}


struct CodeParseContext<'a> {
	parent: &'a ParseContext,
	locals: Vec<(Type, Symbol)>
}

impl<'a> CodeParseContext<'a> {
	fn new(parent_ctx: &'a ParseContext, func: &FunctionData) -> CodeParseContext<'a> {
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

	fn resolve_local_var(&mut self, sym: &Symbol) -> Result<(usize, Type)> {
		for (i, (var_type, var_name)) in self.locals.iter().enumerate().rev() {
			if sym == var_name {
				return Ok((i, var_type.clone()));
			}
		}
		Err(ParserError::VariableNotFound)
	}

	fn typecheck_expr(&mut self, expr: &UncheckedExpr) -> Result<Expr> {
		use ExprKind::*;
		match &expr.0 {
			LocalGet(sym) => Ok(Expr { expr: LocalGet(*sym), typ: self.resolve_local_var(sym)?.1 }),
			LocalSet(sym, value) => {
				let (_, var_type) = self.resolve_local_var(sym)?;
				let value_expr = self.typecheck_expr(value)?;
				Type::ensure_equal(&var_type, &value_expr.typ)?;
				let typ = value_expr.typ.clone();
				Ok(Expr { expr: LocalSet(*sym, Box::new(value_expr)), typ })
			}
			GlobalGet(qid) => {
				// right now this is JUST for enum constants
				let (sym, node_name) = qid.split_last().unwrap();
				let node = self.parent.root.resolve(node_name);
				let node = node.ok_or(ParserError::MissingNamespace)?;
				if let Some(Node { what: NodeData::SymbolConstant(_), .. }) = node.children.get(sym) {
					// this is a valid enum constant
					let typ = self.parent.root.resolve_type(node_name).unwrap();
					Ok(Expr { expr: GlobalGet(qid.clone()), typ })
				} else {
					Err(ParserError::VariableNotFound)
				}
			}
			FunctionCall(qid, args) => {
				let arg_exprs = args.iter().map(|e| self.typecheck_expr(e)).collect::<Result<Vec<Expr>>>()?;
				let arg_types = arg_exprs.iter().map(|e| e.typ.clone()).collect::<Vec<Type>>();
				let func = self.parent.root.require_compatible_function(qid, &arg_types)?;
				let return_type = func.return_type.clone();
				Ok(Expr { expr: FunctionCall(qid.clone(), arg_exprs), typ: return_type })
			}
			MethodCall(obj, sym, args) => {
				let obj_expr = self.typecheck_expr(obj)?;
				let arg_exprs = args.iter().map(|e| self.typecheck_expr(e)).collect::<Result<Vec<Expr>>>()?;
				let arg_types = arg_exprs.iter().map(|e| e.typ.clone()).collect::<Vec<Type>>();
				let type_node = self.parent.root.resolve(&obj_expr.typ.name).expect("type missing");
				let method = type_node.require_compatible_function(&[*sym], &arg_types)?;
				let return_type = method.return_type.clone();
				Ok(Expr { expr: MethodCall(Box::new(obj_expr), *sym, arg_exprs), typ: return_type })
			}
			If(cond, if_true, if_false) => {
				let cond_expr = self.typecheck_expr(cond)?;
				Type::err_if_not_equal(&cond_expr.typ, &self.parent.bool_type, ParserError::BadIfConditionType)?;
				let if_true_expr = self.typecheck_expr(if_true)?;
				let if_false_expr = if_false.as_ref().map(|e| self.typecheck_expr(&e)).transpose()?;
				let typ = match &if_false_expr {
					Some(e) if e.typ == if_true_expr.typ => e.typ.clone(),
					_                                    => self.parent.void_type.clone()
				};
				Ok(Expr { expr: If(Box::new(cond_expr), Box::new(if_true_expr), if_false_expr.map(Box::new)), typ })
			}
			Let(sym, value) => {
				let value_expr = self.typecheck_expr(value)?;
				Type::err_if_equal(&value_expr.typ, &self.parent.void_type, ParserError::LocalCannotBeVoid)?;
				self.locals.push((value_expr.typ.clone(), *sym));
				let typ = value_expr.typ.clone();
				Ok(Expr { expr: Let(*sym, Box::new(value_expr)), typ })
			}
			CodeBlock(exprs) => {
				let exprs = exprs.iter().map(|e| self.typecheck_expr(e)).collect::<Result<Vec<Expr>>>()?;
				let final_type = match exprs.last() {
					Some(e) => e.typ.clone(),
					None    => self.parent.void_type.clone()
				};
				Ok(Expr { expr: CodeBlock(exprs), typ: final_type })
			}
			Int(v)  => Ok(Expr { expr: Int(v.clone()),  typ: self.parent.int_type.clone() }),
			Real(v) => Ok(Expr { expr: Real(v.clone()), typ: self.parent.real_type.clone() }),
			Bool(v) => Ok(Expr { expr: Bool(v.clone()), typ: self.parent.bool_type.clone() })
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
			(GlobalGet(a), GlobalGet(b)) => a == b,
			(FunctionCall(a0, a1), FunctionCall(b0, b1)) => {
				(a0 == b0) && vec_equal(a1, b1)
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
		let int1 = box_expr(Int(Ok(1)));
		let hl_foo = Box::new(HL::ID(vec!["foo".into()]));

		check_desugar_ok(
			HL::Binary(hl_foo.clone(), "=".into(), hl_int1.clone()),
			LocalSet("foo".into(), int1.clone())
		);
		check_desugar_ok(
			HL::Binary(Box::new(HL::PropAccess(hl_foo.clone(), "bar".into())), "=".into(), hl_int1.clone()),
			MethodCall(box_expr(LocalGet("foo".into())), "bar=".into(), vec![expr(Int(Ok(1)))])
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
			MethodCall(box_expr(LocalGet("a".into())), "b".into(), vec![])
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
	fn test_desugar_binary_ops() {
		check_desugar_ok(
			HL::Binary(Box::new(HL::Int(Ok(1))), "+".into(), Box::new(HL::Int(Ok(2)))),
			MethodCall(box_expr(Int(Ok(1))), "op#+".into(), vec![expr(Int(Ok(2)))])
		);
	}



	#[test]
	fn test_typed_constants() {
		let pc = ParseContext::new();
		let func = FunctionData {
			name: vec!["test".into()],
			is_method: false,
			arguments: vec![],
			return_type: pc.void_type.clone(),
			body: RefCell::new(FunctionBody::Incomplete(0))
		};
		let mut cpc = CodeParseContext::new(&pc, &func);

		assert_eq!(cpc.typecheck_expr(&expr(Bool(true))).unwrap().typ, pc.bool_type.clone());
		assert_eq!(cpc.typecheck_expr(&expr(Int(Ok(5)))).unwrap().typ, pc.int_type.clone());
		assert_eq!(cpc.typecheck_expr(&expr(Real(Ok(5.)))).unwrap().typ, pc.real_type.clone());
	}

	#[test]
	fn test_typed_variables() {
		let pc = ParseContext::new();
		let func = FunctionData {
			name: vec!["test".into()],
			is_method: false,
			arguments: vec![(pc.int_type.clone(), "var".into())],
			return_type: pc.void_type.clone(),
			body: RefCell::new(FunctionBody::Incomplete(0))
		};
		let mut cpc = CodeParseContext::new(&pc, &func);

		// Get
		let e = cpc.typecheck_expr(&expr(LocalGet("var".into())));
		assert_eq!(e.unwrap().typ, pc.int_type.clone());
		let e = cpc.typecheck_expr(&expr(LocalGet("nevar".into())));
		assert!(e.is_err() && e.unwrap_err() == ParserError::VariableNotFound);

		// Set
		let e = cpc.typecheck_expr(&expr(LocalSet("var".into(), box_expr(Int(Ok(5))))));
		assert_eq!(e.unwrap().typ, pc.int_type.clone());
		let e = cpc.typecheck_expr(&expr(LocalSet("var".into(), box_expr(Bool(false)))));
		assert!(e.is_err() && e.unwrap_err() == ParserError::TypeMismatch);
	}
}
