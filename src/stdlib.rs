use crate::ast::*;
use crate::data::*;
use crate::eval::*;
use symbol::Symbol;
use std::convert::TryInto;
use gtk::prelude::*;

impl SymbolTable {
	fn add_binary<F: Fn(&SymbolTable, &[Value]) -> Value + 'static>(&mut self, typ: Type, name: &str, f: F) -> Result<(), SymTabError> {
		self.add_builtin_method(
			&typ, name,
			&typ, &[(typ.clone(), "v".into())],
			f
		)
	}
	fn add_binary_bool<F: Fn(&SymbolTable, &[Value]) -> Value + 'static>(&mut self, typ: Type, name: &str, f: F) -> Result<(), SymTabError> {
		self.add_builtin_method(
			&typ, name,
			&self.bool_type.clone(), &[(typ.clone(), "v".into())],
			f
		)
	}
	fn add_default<F: Fn(&SymbolTable) -> Value + 'static>(&mut self, typ: Type, f: F) -> Result<(), SymTabError> {
		self.add_builtin_static_method(&typ, "default", &typ, &[], move |s, _| f(s))
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
	let str_ = symtab.str_type.clone();
	let str_ = || { str_.clone() };

	symtab.add_binary_bool(bool_(), "op#==", move |_, args| Value::Bool(args[0].unchecked_bool() == args[1].unchecked_bool()))?;
	symtab.add_binary_bool(bool_(), "op#!=", move |_, args| Value::Bool(args[0].unchecked_bool() != args[1].unchecked_bool()))?;

	symtab.add_binary(int_(), "op#+", move |_, args| Value::Int(args[0].unchecked_int() + args[1].unchecked_int()))?;
	symtab.add_binary(int_(), "op#-", move |_, args| Value::Int(args[0].unchecked_int() - args[1].unchecked_int()))?;
	symtab.add_binary(int_(), "op#*", move |_, args| Value::Int(args[0].unchecked_int() * args[1].unchecked_int()))?;
	symtab.add_binary(int_(), "op#/", move |_, args| Value::Int(args[0].unchecked_int() / args[1].unchecked_int()))?;
	symtab.add_binary_bool(int_(), "op#==", move |_, args| Value::Bool(args[0].unchecked_int() == args[1].unchecked_int()))?;
	symtab.add_binary_bool(int_(), "op#!=", move |_, args| Value::Bool(args[0].unchecked_int() != args[1].unchecked_int()))?;
	symtab.add_binary_bool(int_(), "op#<", move |_, args| Value::Bool(args[0].unchecked_int() < args[1].unchecked_int()))?;
	symtab.add_binary_bool(int_(), "op#<=", move |_, args| Value::Bool(args[0].unchecked_int() <= args[1].unchecked_int()))?;
	symtab.add_binary_bool(int_(), "op#>", move |_, args| Value::Bool(args[0].unchecked_int() > args[1].unchecked_int()))?;
	symtab.add_binary_bool(int_(), "op#>=", move |_, args| Value::Bool(args[0].unchecked_int() >= args[1].unchecked_int()))?;
	symtab.add_default(int_(), move |_| Value::Int(0))?;

	symtab.add_binary(real_(), "op#+", move |_, args| Value::Real(args[0].unchecked_real() + args[1].unchecked_real()))?;
	symtab.add_binary(real_(), "op#-", move |_, args| Value::Real(args[0].unchecked_real() - args[1].unchecked_real()))?;
	symtab.add_binary(real_(), "op#*", move |_, args| Value::Real(args[0].unchecked_real() * args[1].unchecked_real()))?;
	symtab.add_binary(real_(), "op#/", move |_, args| Value::Real(args[0].unchecked_real() / args[1].unchecked_real()))?;
	symtab.add_binary_bool(real_(), "op#==", move |_, args| Value::Bool(args[0].unchecked_real() == args[1].unchecked_real()))?;
	symtab.add_binary_bool(real_(), "op#!=", move |_, args| Value::Bool(args[0].unchecked_real() != args[1].unchecked_real()))?;
	symtab.add_binary_bool(real_(), "op#<", move |_, args| Value::Bool(args[0].unchecked_real() < args[1].unchecked_real()))?;
	symtab.add_binary_bool(real_(), "op#<=", move |_, args| Value::Bool(args[0].unchecked_real() <= args[1].unchecked_real()))?;
	symtab.add_binary_bool(real_(), "op#>", move |_, args| Value::Bool(args[0].unchecked_real() > args[1].unchecked_real()))?;
	symtab.add_binary_bool(real_(), "op#>=", move |_, args| Value::Bool(args[0].unchecked_real() >= args[1].unchecked_real()))?;
	symtab.add_default(real_(), move |_| Value::Real(0.))?;

	symtab.add_binary(str_(), "op#+", move |_, args| {
		let a = args[0].borrow_obj().unwrap();
		let b = args[1].borrow_obj().unwrap();
		let mut s = String::with_capacity(a.unchecked_str().len() + b.unchecked_str().len());
		s.push_str(a.unchecked_str());
		s.push_str(b.unchecked_str());
		Obj::Str(s).to_heap()
	})?;

	symtab.add_builtin_function(
		vec!["str".into(), "from".into()], &str_(), &[(bool_(), "v".into())],
		move |_, args| Obj::Str(args[0].unchecked_bool().to_string()).to_heap()
	)?;
	symtab.add_builtin_function(
		vec!["str".into(), "from".into()], &str_(), &[(int_(), "v".into())],
		move |_, args| Obj::Str(args[0].unchecked_int().to_string()).to_heap()
	)?;
	symtab.add_builtin_function(
		vec!["str".into(), "from".into()], &str_(), &[(real_(), "v".into())],
		move |_, args| Obj::Str(args[0].unchecked_real().to_string()).to_heap()
	)?;
	symtab.add_default(str_(), move |_| Obj::Str("".to_string()).to_heap())?;

	symtab.add_builtin_function(
		vec!["print".into()], &void_(), &[],
		move |_, _| { print!("\n"); Value::Void }
	)?;
	symtab.add_builtin_function(
		vec!["print".into()], &void_(), &[(int_(), "v".into())],
		move |_, args| { print!("{}", args[0].unchecked_int()); Value::Void }
	)?;
	symtab.add_builtin_function(
		vec!["print".into()], &void_(), &[(real_(), "v".into())],
		move |_, args| { print!("{}", args[0].unchecked_real()); Value::Void }
	)?;
	symtab.add_builtin_function(
		vec!["print".into()], &void_(), &[(str_(), "v".into())],
		move |_, args| { print!("{}", args[0].borrow_obj().unwrap().unchecked_str()); Value::Void }
	)?;

	// TODO checkme, there should be a better way to do namespacing
	symtab.add_type(Type::from_body(vec!["gui".into()], TypeBody::Incomplete))?;
	symtab.add_builtin_function(
		vec!["gui".into(), "init".into()], &void_(), &[],
		move |_, _args| { gtk::init().expect("GTK init failed"); Value::Void }
	)?;
	symtab.add_builtin_function(
		vec!["gui".into(), "run".into()], &void_(), &[],
		move |_, _args| { gtk::main(); Value::Void }
	)?;

	let window = Type::from_body(vec!["gui".into(), "Window".into()], TypeBody::Primitive(PrimitiveType::GuiWindow));
	symtab.add_type(window.clone())?;
	symtab.add_builtin_function(
		vec!["gui".into(), "Window".into(), "new".into()], &window, &[],
		move |_, _args| { Obj::GuiWindow(gtk::Window::new(gtk::WindowType::Toplevel)).to_heap() }
	)?;
	symtab.add_builtin_method(
		&window, "show", &void_(), &[],
		move |_, args| { args[0].borrow_obj().unwrap().unchecked_gui_window().show(); Value::Void }
	)?;

	Ok(())
}

pub fn inject_wrap_type(symtab: &mut SymbolTable, wrap_type: Type, target_type: Type) -> Result<(), SymTabError> {
	symtab.add_builtin_static_method(
		&wrap_type, "wrap", &wrap_type, &[(target_type.clone(), "v".into())],
		move |_, args| args[0].clone()
	)?;
	symtab.add_builtin_method(
		&wrap_type, "unwrap", &target_type, &[],
		move |_, args| args[0].clone()
	)?;
	Ok(())
}

pub fn inject_enum_type(symtab: &mut SymbolTable, typ: Type, has_fields: bool) -> Result<(), SymTabError> {
	symtab.add_builtin_method(
		&typ, "discriminant", &symtab.int_type.clone(), &[],
		move |_, args| { Value::Int(args[0].unchecked_enum_index().try_into().unwrap()) }
	)?;
	if !has_fields {
		symtab.add_binary_bool(typ.clone(), "op#==", move |_, args| Value::Bool(args[0].unchecked_enum_index() == args[1].unchecked_enum_index()))?;
		symtab.add_binary_bool(typ.clone(), "op#!=", move |_, args| Value::Bool(args[0].unchecked_enum_index() != args[1].unchecked_enum_index()))?;
	}
	Ok(())
}

pub fn inject_record_type(symtab: &mut SymbolTable, typ: Type, fields: &[(Type, Symbol)]) -> Result<(), SymTabError> {
	for (idx, (ftyp, fid)) in fields.iter().enumerate() {
		symtab.add_builtin_method(
			&typ, fid, ftyp, &[],
			move |_, args| args[0].borrow_obj().unwrap().unchecked_record()[idx].clone()
		)?;
		symtab.add_builtin_method(
			&typ, &(fid.to_string() + "="), &symtab.void_type.clone(), &[(ftyp.clone(), "v".into())],
			move |_, args| { args[0].borrow_obj_mut().unwrap().unchecked_record_mut()[idx] = args[1].clone(); Value::Void }
		)?;
	}

	// TODO: only create 'default' for records that are all default types?
	//   (although, this might cause issues as default methods can be defined later...)
	let typ_ = typ.clone();
	symtab.add_builtin_static_method(
		&typ, "default", &typ, &[],
		move |symtab, _args| {
			let tbody = typ_.borrow();
			let fields = tbody.unchecked_record_fields();
			let mut values = Vec::with_capacity(fields.len());
			for (ftyp, _) in fields {
				let mut ftyp_name = ftyp.name.clone();
				ftyp_name.push("default".into());
				values.push(call_func(symtab, &ftyp_name, &[], &[]).unwrap());
			}

			Obj::Record(values).to_heap()
		}
	)?;

	symtab.add_builtin_static_method(
		&typ, "build", &typ, &fields,
		move |_, args| Obj::Record(args.to_vec()).to_heap()
	)?;

	Ok(())
}
