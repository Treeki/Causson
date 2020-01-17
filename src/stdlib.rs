use crate::ast::*;

impl SymbolTable {
	fn add_binary<F: Fn(&[Value]) -> Value + 'static>(&mut self, typ: Type, name: &str, f: F) -> Result<(), SymTabError> {
		self.add_builtin_method(
			&typ, name,
			&typ, &[(typ.clone(), "v".into())],
			f
		)
	}
	fn add_binary_bool<F: Fn(&[Value]) -> Value + 'static>(&mut self, typ: Type, name: &str, f: F) -> Result<(), SymTabError> {
		self.add_builtin_method(
			&typ, name,
			&self.bool_type.clone(), &[(typ.clone(), "v".into())],
			f
		)
	}
}

pub fn inject(symtab: &mut SymbolTable) -> Result<(), SymTabError> {
	let void_ = symtab.void_type.clone();
	let void_ = || { void_.clone() };
	let int_ = symtab.int_type.clone();
	let int_ = || { int_.clone() };
	let real_ = symtab.real_type.clone();
	let real_ = || { real_.clone() };
	let bool_ = symtab.bool_type.clone();
	let bool_ = || { bool_.clone() };

	symtab.add_binary_bool(bool_(), "op#==", move |args| Value::Bool(args[0].unchecked_bool() == args[1].unchecked_bool()))?;
	symtab.add_binary_bool(bool_(), "op#!=", move |args| Value::Bool(args[0].unchecked_bool() != args[1].unchecked_bool()))?;

	symtab.add_binary(int_(), "op#+", move |args| Value::Int(args[0].unchecked_int() + args[1].unchecked_int()))?;
	symtab.add_binary(int_(), "op#-", move |args| Value::Int(args[0].unchecked_int() - args[1].unchecked_int()))?;
	symtab.add_binary(int_(), "op#*", move |args| Value::Int(args[0].unchecked_int() * args[1].unchecked_int()))?;
	symtab.add_binary(int_(), "op#/", move |args| Value::Int(args[0].unchecked_int() / args[1].unchecked_int()))?;
	symtab.add_binary_bool(int_(), "op#==", move |args| Value::Bool(args[0].unchecked_int() == args[1].unchecked_int()))?;
	symtab.add_binary_bool(int_(), "op#!=", move |args| Value::Bool(args[0].unchecked_int() != args[1].unchecked_int()))?;
	symtab.add_binary_bool(int_(), "op#<", move |args| Value::Bool(args[0].unchecked_int() < args[1].unchecked_int()))?;
	symtab.add_binary_bool(int_(), "op#<=", move |args| Value::Bool(args[0].unchecked_int() <= args[1].unchecked_int()))?;
	symtab.add_binary_bool(int_(), "op#>", move |args| Value::Bool(args[0].unchecked_int() > args[1].unchecked_int()))?;
	symtab.add_binary_bool(int_(), "op#>=", move |args| Value::Bool(args[0].unchecked_int() >= args[1].unchecked_int()))?;

	symtab.add_binary(real_(), "op#+", move |args| Value::Real(args[0].unchecked_real() + args[1].unchecked_real()))?;
	symtab.add_binary(real_(), "op#-", move |args| Value::Real(args[0].unchecked_real() - args[1].unchecked_real()))?;
	symtab.add_binary(real_(), "op#*", move |args| Value::Real(args[0].unchecked_real() * args[1].unchecked_real()))?;
	symtab.add_binary(real_(), "op#/", move |args| Value::Real(args[0].unchecked_real() / args[1].unchecked_real()))?;
	symtab.add_binary_bool(real_(), "op#==", move |args| Value::Bool(args[0].unchecked_real() == args[1].unchecked_real()))?;
	symtab.add_binary_bool(real_(), "op#!=", move |args| Value::Bool(args[0].unchecked_real() != args[1].unchecked_real()))?;
	symtab.add_binary_bool(real_(), "op#<", move |args| Value::Bool(args[0].unchecked_real() < args[1].unchecked_real()))?;
	symtab.add_binary_bool(real_(), "op#<=", move |args| Value::Bool(args[0].unchecked_real() <= args[1].unchecked_real()))?;
	symtab.add_binary_bool(real_(), "op#>", move |args| Value::Bool(args[0].unchecked_real() > args[1].unchecked_real()))?;
	symtab.add_binary_bool(real_(), "op#>=", move |args| Value::Bool(args[0].unchecked_real() >= args[1].unchecked_real()))?;

	symtab.add_builtin_function(
		vec!["test_builtin_function".into()], &int_(), &[],
		move |_| Value::Int(100)
	)?;

	symtab.add_builtin_function(
		vec!["print".into()], &void_(), &[],
		move |_| { print!("\n"); Value::Void }
	)?;
	symtab.add_builtin_function(
		vec!["print".into()], &void_(), &[(real_(), "v".into())],
		move |args| { print!("{}", args[0].unchecked_real()); Value::Void }
	)?;

	Ok(())
}

pub fn inject_wrap_type(symtab: &mut SymbolTable, wrap_type: Type, target_type: Type) -> Result<(), SymTabError> {
	let mut n = wrap_type.name.clone();
	n.push("wrap".into());
	symtab.add_builtin_function(
		n, &wrap_type, &[(target_type.clone(), "v".into())],
		move |args| args[0].clone()
	)?;
	symtab.add_builtin_method(
		&wrap_type, "unwrap", &target_type, &[],
		move |args| args[0].clone()
	)?;
	Ok(())
}

pub fn inject_enum_type(symtab: &mut SymbolTable, typ: Type) -> Result<(), SymTabError> {
	symtab.add_binary_bool(typ.clone(), "op#==", move |args| Value::Bool(args[0].unchecked_enum_symbol() == args[1].unchecked_enum_symbol()))?;
	symtab.add_binary_bool(typ.clone(), "op#!=", move |args| Value::Bool(args[0].unchecked_enum_symbol() != args[1].unchecked_enum_symbol()))?;
	Ok(())
}