use crate::ast::*;
use crate::data::*;
use symbol::Symbol;

pub fn call_func(symtab: &SymbolTable, qid: &[Symbol], args: &[Value], arg_types: &[Type]) -> Option<Value> {
	assert!(args.len() == arg_types.len());
	let node = symtab.root.resolve(qid)?;
	let variants = node.get_function_variants()?;
	let func = variants.iter().find(|f| f.matches_types(arg_types))?;
	let context = EvalContext { symtab, locals: vec![] };
	Some(context.eval_func(func, args.to_vec()))
}

pub struct EvalContext<'a> {
	symtab: &'a SymbolTable,
	locals: Vec<Value>
}

impl EvalContext<'_> {
	pub fn eval_func(&self, func: &Function, args: Vec<Value>) -> Value {
		match &*func.borrow() {
			FunctionBody::Incomplete(_) => unreachable!("executing incomplete function"),
			FunctionBody::Expr(sub_expr) => {
				let mut sub_ctx = EvalContext { symtab: self.symtab, locals: args };
				sub_ctx.eval(&sub_expr)
			}
			FunctionBody::BuiltIn(f) => f(self.symtab, &args)
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
			GlobalGet(qid) => {
				let node = self.symtab.root.resolve(&qid).unwrap();
				let (_, value) = node.get_constant().unwrap();
				value
			}
			FunctionCall(_, _) => unreachable!(),
			FunctionCallResolved(func, arg_exprs) => {
				let args = arg_exprs.iter().map(|e| self.eval(&e)).collect::<Vec<Value>>();
				self.eval_func(func, args)
			}
			MethodCall(obj_expr, sym, arg_exprs) => {
				// dynamic dispatch will go here eventually
				// low-hanging optimisation fruit here...
				let obj = self.eval(&obj_expr);
				let arg_types = arg_exprs.iter().map(|e| e.typ.clone()).collect::<Vec<Type>>();
				let type_node = self.symtab.root.resolve(&obj_expr.typ.name).unwrap();
				let method_node = type_node.resolve(&[*sym]).unwrap();
				let variants = method_node.get_function_variants().unwrap();
				let func = variants.iter().find(|f| f.matches_types(&arg_types)).unwrap();
				let mut args = arg_exprs.iter().map(|e| self.eval(&e)).collect::<Vec<Value>>();
				args.insert(0, obj);
				self.eval_func(func, args)
			}
			If(cond_expr, if_true_expr, if_false_expr) => {
				let orig_local_depth = self.locals.len();
				let cond = self.eval(&cond_expr);
				if let Value::Bool(cond) = cond {
					if cond {
						let value = self.eval(&if_true_expr);
						self.locals.truncate(orig_local_depth);
						if expr.typ == self.symtab.void_type { Value::Void } else { value }
					} else if if_false_expr.is_some() {
						let value = self.eval(&if_false_expr.as_ref().unwrap());
						self.locals.truncate(orig_local_depth);
						if expr.typ == self.symtab.void_type { Value::Void } else { value }
					} else {
						self.locals.truncate(orig_local_depth);
						Value::Void
					}
				} else {
					unreachable!("if condition is expected to be a boolean")
				}
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
		Expr { expr: k, typ: typ.clone() }
	}
	fn box_expr(k: ExprKind<Expr>, typ: &Type) -> Box<Expr> {
		Box::new(expr(k, typ))
	}

	#[test]
	fn test_locals() {
		let symtab = SymbolTable::new();
		let mut ctx = EvalContext { symtab: &symtab, locals: vec![Value::Int(5)] };

		assert_eq!(
			ctx.eval(&expr(LocalGetResolved(0), &symtab.int_type)),
			Value::Int(5));
		ctx.eval(&expr(LocalSetResolved(0, box_expr(Int(Ok(10)), &symtab.int_type)), &symtab.int_type));
		assert_eq!(
			ctx.eval(&expr(LocalGetResolved(0), &symtab.int_type)),
			Value::Int(10));

		ctx.eval(&expr(Let("test".into(), box_expr(Int(Ok(20)), &symtab.int_type)), &symtab.int_type));
		assert_eq!(
			ctx.eval(&expr(LocalGetResolved(1), &symtab.int_type)),
			Value::Int(20));
	}

	#[test]
	fn test_constants() {
		let symtab = SymbolTable::new();
		let mut ctx = EvalContext { symtab: &symtab, locals: vec![] };

		assert_eq!(ctx.eval(&expr(Int(Ok(5)), &symtab.int_type)), Value::Int(5));
		assert_eq!(ctx.eval(&expr(Real(Ok(0.5)), &symtab.real_type)), Value::Real(0.5));
		assert_eq!(ctx.eval(&expr(Bool(false), &symtab.bool_type)), Value::Bool(false));
	}

	#[test]
	fn test_block() {
		let symtab = SymbolTable::new();
		let mut ctx = EvalContext { symtab: &symtab, locals: vec![] };

		let result = ctx.eval(&expr(CodeBlock(vec![
			expr(Let("test".into(), box_expr(Int(Ok(5)), &symtab.int_type)), &symtab.int_type),
			expr(Let("test2".into(), box_expr(Int(Ok(10)), &symtab.int_type)), &symtab.int_type),
			expr(LocalGetResolved(1), &symtab.int_type)
		]), &symtab.int_type));
		assert_eq!(result, Value::Int(10));

		assert_eq!(ctx.locals.len(), 0);
	}

	#[test]
	fn test_if() {
		let symtab = SymbolTable::new();
		let locals = vec![Value::Bool(true), Value::Int(0), Value::Real(0.0)];
		let mut ctx = EvalContext { symtab: &symtab, locals };

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
		let mut symtab = SymbolTable::new();

		// test function:
		// if arg { 1 } else { 2 }
		let test_func = Function::new_expr(
			vec!["test".into()],
			false,
			symtab.int_type.clone(),
			vec![(symtab.bool_type.clone(), "arg".into())],
			expr(If(
				box_expr(LocalGetResolved(0), &symtab.bool_type),
				box_expr(Int(Ok(1)), &symtab.int_type),
				Some(box_expr(Int(Ok(2)), &symtab.int_type))
			), &symtab.int_type)
		);
		let mut test_func_node = SymTabNode::new_function();
		test_func_node.get_function_variants_mut().unwrap().push(test_func.clone());
		symtab.root.get_children_mut().unwrap().insert("test".into(), test_func_node);

		let mut ctx = EvalContext { symtab: &symtab, locals: vec![Value::Bool(true)] };
		let call_expr = expr(
			FunctionCallResolved(test_func, vec![expr(LocalGetResolved(0), &symtab.bool_type)]),
			&symtab.int_type
		);
		assert_eq!(ctx.eval(&call_expr), Value::Int(1));
		ctx.locals[0] = Value::Bool(false);
		assert_eq!(ctx.eval(&call_expr), Value::Int(2));
	}
}
