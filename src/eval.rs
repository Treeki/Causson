use crate::ast::*;
use symbol::Symbol;

#[derive(Debug, PartialEq, Clone)]
pub enum Value {
	Void,
	Bool(bool),
	Int(i64),
	Real(f64),
	Enum(Symbol)
}

pub struct EvalContext<'a> {
	symtab: &'a SymbolTable,
	locals: Vec<Value>
}

impl EvalContext<'_> {
	pub fn eval(&mut self, expr: &Expr) -> Value {
		use ExprKind::*;

		match &expr.expr {
			LocalGet(_) => unreachable!(),
			LocalSet(_, _) => unreachable!(),
			LocalGetResolved(index) => {
				// self.locals.get(index).expect("invalid local index in eval").clone()
				self.locals[*index].clone()
			}
			LocalSetResolved(index, sub_expr) => {
				let value = self.eval(&sub_expr);
				self.locals[*index] = value.clone();
				value
			}
			GlobalGet(qid) => {
				unreachable!()
			}
			FunctionCall(qid, arg_exprs) => {
				unreachable!()
			}
			MethodCall(obj_expr, sym, arg_exprs) => {
				unreachable!()
			}
			If(cond_expr, if_true_expr, if_false_expr) => {
				unreachable!()
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
}
