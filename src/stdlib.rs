use crate::ast::*;
use crate::data::*;
use crate::eval::*;
use symbol::Symbol;
use std::convert::TryInto;
use gtk::prelude::*;
use std::rc::Rc;
use std::cell::RefCell;

impl SymbolTable {
	fn add_binary<F: Fn(&Rc<RefCell<SymbolTable>>, &[Type], &[Value]) -> Value + 'static>(&mut self, typ: Type, name: &str, f: F) -> Result<(), SymTabError> {
		self.add_builtin_method(
			&typ, name,
			&typ, &[(typ.clone(), "v".into())],
			f
		)
	}
	fn add_binary_bool<F: Fn(&Rc<RefCell<SymbolTable>>, &[Type], &[Value]) -> Value + 'static>(&mut self, typ: Type, name: &str, f: F) -> Result<(), SymTabError> {
		self.add_builtin_method(
			&typ, name,
			&self.bool_type.clone(), &[(typ.clone(), "v".into())],
			f
		)
	}
	fn add_default<F: Fn(&Rc<RefCell<SymbolTable>>) -> Value + 'static>(&mut self, typ: Type, f: F) -> Result<(), SymTabError> {
		self.add_builtin_static_method(&typ, "default", &typ, &[], move |s, _, _| f(s))
	}
}

pub fn inject(symtab_rc: &Rc<RefCell<SymbolTable>>) -> Result<(), SymTabError> {
	let mut symtab = symtab_rc.borrow_mut();
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
	let any_ = symtab.any_type.clone();
	let any_ = || { any_.clone() };

	symtab.add_binary_bool(bool_(), "op#==", move |_, _, args| Value::Bool(args[0].unchecked_bool() == args[1].unchecked_bool()))?;
	symtab.add_binary_bool(bool_(), "op#!=", move |_, _, args| Value::Bool(args[0].unchecked_bool() != args[1].unchecked_bool()))?;

	symtab.add_binary(int_(), "op#+", move |_, _, args| Value::Int(args[0].unchecked_int() + args[1].unchecked_int()))?;
	symtab.add_binary(int_(), "op#-", move |_, _, args| Value::Int(args[0].unchecked_int() - args[1].unchecked_int()))?;
	symtab.add_binary(int_(), "op#*", move |_, _, args| Value::Int(args[0].unchecked_int() * args[1].unchecked_int()))?;
	symtab.add_binary(int_(), "op#/", move |_, _, args| Value::Int(args[0].unchecked_int() / args[1].unchecked_int()))?;
	symtab.add_binary_bool(int_(), "op#==", move |_, _, args| Value::Bool(args[0].unchecked_int() == args[1].unchecked_int()))?;
	symtab.add_binary_bool(int_(), "op#!=", move |_, _, args| Value::Bool(args[0].unchecked_int() != args[1].unchecked_int()))?;
	symtab.add_binary_bool(int_(), "op#<", move |_, _, args| Value::Bool(args[0].unchecked_int() < args[1].unchecked_int()))?;
	symtab.add_binary_bool(int_(), "op#<=", move |_, _, args| Value::Bool(args[0].unchecked_int() <= args[1].unchecked_int()))?;
	symtab.add_binary_bool(int_(), "op#>", move |_, _, args| Value::Bool(args[0].unchecked_int() > args[1].unchecked_int()))?;
	symtab.add_binary_bool(int_(), "op#>=", move |_, _, args| Value::Bool(args[0].unchecked_int() >= args[1].unchecked_int()))?;
	symtab.add_default(int_(), move |_| Value::Int(0))?;

	symtab.add_binary(real_(), "op#+", move |_, _, args| Value::Real(args[0].unchecked_real() + args[1].unchecked_real()))?;
	symtab.add_binary(real_(), "op#-", move |_, _, args| Value::Real(args[0].unchecked_real() - args[1].unchecked_real()))?;
	symtab.add_binary(real_(), "op#*", move |_, _, args| Value::Real(args[0].unchecked_real() * args[1].unchecked_real()))?;
	symtab.add_binary(real_(), "op#/", move |_, _, args| Value::Real(args[0].unchecked_real() / args[1].unchecked_real()))?;
	symtab.add_binary_bool(real_(), "op#==", move |_, _, args| Value::Bool(args[0].unchecked_real() == args[1].unchecked_real()))?;
	symtab.add_binary_bool(real_(), "op#!=", move |_, _, args| Value::Bool(args[0].unchecked_real() != args[1].unchecked_real()))?;
	symtab.add_binary_bool(real_(), "op#<", move |_, _, args| Value::Bool(args[0].unchecked_real() < args[1].unchecked_real()))?;
	symtab.add_binary_bool(real_(), "op#<=", move |_, _, args| Value::Bool(args[0].unchecked_real() <= args[1].unchecked_real()))?;
	symtab.add_binary_bool(real_(), "op#>", move |_, _, args| Value::Bool(args[0].unchecked_real() > args[1].unchecked_real()))?;
	symtab.add_binary_bool(real_(), "op#>=", move |_, _, args| Value::Bool(args[0].unchecked_real() >= args[1].unchecked_real()))?;
	symtab.add_default(real_(), move |_| Value::Real(0.))?;

	symtab.add_binary(str_(), "op#+", move |_, _, args| {
		let a = args[0].borrow_obj().unwrap();
		let b = args[1].borrow_obj().unwrap();
		let mut s = String::with_capacity(a.unchecked_str().len() + b.unchecked_str().len());
		s.push_str(a.unchecked_str());
		s.push_str(b.unchecked_str());
		Obj::Str(s).to_heap()
	})?;

	symtab.add_builtin_function(
		vec!["str".into(), "from".into()], &str_(), &[(bool_(), "v".into())],
		move |_, _, args| Obj::Str(args[0].unchecked_bool().to_string()).to_heap()
	)?;
	symtab.add_builtin_function(
		vec!["str".into(), "from".into()], &str_(), &[(int_(), "v".into())],
		move |_, _, args| Obj::Str(args[0].unchecked_int().to_string()).to_heap()
	)?;
	symtab.add_builtin_function(
		vec!["str".into(), "from".into()], &str_(), &[(real_(), "v".into())],
		move |_, _, args| Obj::Str(args[0].unchecked_real().to_string()).to_heap()
	)?;
	symtab.add_default(str_(), move |_| Obj::Str("".to_string()).to_heap())?;

	symtab.add_builtin_function(
		vec!["print".into()], &void_(), &[],
		move |_, _, _| { print!("\n"); Value::Void }
	)?;
	symtab.add_builtin_function(
		vec!["print".into()], &void_(), &[(int_(), "v".into())],
		move |_, _, args| { print!("{}", args[0].unchecked_int()); Value::Void }
	)?;
	symtab.add_builtin_function(
		vec!["print".into()], &void_(), &[(real_(), "v".into())],
		move |_, _, args| { print!("{}", args[0].unchecked_real()); Value::Void }
	)?;
	symtab.add_builtin_function(
		vec!["print".into()], &void_(), &[(str_(), "v".into())],
		move |_, _, args| { print!("{}", args[0].borrow_obj().unwrap().unchecked_str()); Value::Void }
	)?;

	// TODO checkme, there should be a better way to do namespacing
	symtab.add_type(Type::from_body(vec!["gui".into()], TypeBody::Incomplete))?;
	symtab.add_builtin_function(
		vec!["gui".into(), "init".into()], &void_(), &[],
		move |_, _, _args| { gtk::init().expect("GTK init failed"); Value::Void }
	)?;
	symtab.add_builtin_function(
		vec!["gui".into(), "run".into()], &void_(), &[],
		move |_, _, _args| { gtk::main(); Value::Void }
	)?;

	// TODO make it easier to build enums from here...
	let orientation = Type::from_body(
		vec!["gui".into(), "Orientation".into()],
		TypeBody::Enum(vec![
			("Horizontal".into(), vec![]),
			("Vertical".into(), vec![]),
		])
	);
	symtab.add_type(orientation.clone())?;
	let orientation_c = symtab.root.resolve_mut(&orientation.name).unwrap().get_children_mut().unwrap();
	orientation_c.insert("Horizontal".into(), SymTabNode::new_constant(orientation.clone(), Value::Enum(0, vec![])));
	orientation_c.insert("Vertical".into(), SymTabNode::new_constant(orientation.clone(), Value::Enum(1, vec![])));
	inject_enum_type(&mut symtab, orientation.clone(), false)?;

	let button = Type::from_body(vec!["gui".into(), "Button".into()], TypeBody::Primitive(PrimitiveType::GuiButton));
	symtab.add_type(button.clone())?;
	symtab.add_builtin_static_method(
		&button, "new", &button, &[],
		move |_, _, _args| Obj::GuiButton(gtk::Button::new()).to_heap()
	)?;
	symtab.add_builtin_method(
		&button, "label=", &void_(), &[(str_(), "s".into())],
		move |_, _, args| { args[0].borrow_obj().unwrap().unchecked_gtk_button().set_label(args[1].borrow_obj().unwrap().unchecked_str()); Value::Void }
	)?;
	let symtab_rc_clone = Rc::clone(&symtab_rc);
	symtab.add_builtin_method(
		&button, "connect_clicked", &void_(), &[(any_(), "target".into()), (str_(), "funcname".into())],
		move |_, arg_types, args| {
			let obj = args[0].borrow_obj().unwrap();
			let obj = obj.unchecked_gtk_button();
			let target_type = arg_types[0].clone();
			let target = args[1].clone();
			let funcname: Symbol = args[2].borrow_obj().unwrap().unchecked_str().into();
			let symtab_rc_clone = Rc::clone(&symtab_rc_clone);
			obj.connect_clicked(move |_butt| {
				let mut qid = target_type.name.clone();
				qid.push(funcname);
				call_func(&symtab_rc_clone, &qid, &[target.clone()], &[], true);
			});
			Value::Void
		}
	)?;

	let window = Type::from_body(vec!["gui".into(), "Window".into()], TypeBody::Primitive(PrimitiveType::GuiWindow));
	symtab.add_type(window.clone())?;
	symtab.add_builtin_static_method(
		&window, "new", &window, &[],
		move |_, _, _args| Obj::GuiWindow(gtk::Window::new(gtk::WindowType::Toplevel)).to_heap()
	)?;
	symtab.add_builtin_method(
		&window, "show", &void_(), &[],
		move |_, _, args| { args[0].borrow_obj().unwrap().unchecked_gtk_window().show_all(); Value::Void }
	)?;

	let boxt = Type::from_body(vec!["gui".into(), "Box".into()], TypeBody::Primitive(PrimitiveType::GuiBox));
	symtab.add_type(boxt.clone())?;
	symtab.add_builtin_static_method(
		&boxt, "new", &boxt, &[(orientation.clone(), "orientation".into())],
		move |_, _, args| {
			let orient = match args[0].unchecked_enum_index() {
				0 => gtk::Orientation::Horizontal,
				1 => gtk::Orientation::Vertical,
				_ => panic!("unknown Orientation")
			};
			Obj::GuiBox(gtk::Box::new(orient, 0)).to_heap()
		}
	)?;
	symtab.add_builtin_method(
		&boxt, "spacing=", &int_(), &[],
		move |_, _, args| Value::Int(args[0].borrow_obj().unwrap().unchecked_gtk_box().get_spacing().into())
	)?;
	symtab.add_builtin_method(
		&boxt, "spacing=", &void_(), &[(int_(), "spacing".into())],
		move |_, _, args| { args[0].borrow_obj().unwrap().unchecked_gtk_box().set_spacing(args[1].unchecked_int().try_into().unwrap()); Value::Void }
	)?;

	let container_parents = vec![window.clone(), boxt.clone()];
	let container_children = vec![boxt.clone(), button.clone()];
	for parent in &container_parents {
		for child in &container_children {
			symtab.add_builtin_method(
				&parent, "add_child", &void_(), &[(child.clone(), "child".into())],
				move |_, _, args| {
					let parent_obj = args[0].borrow_obj().unwrap();
					let child_obj = args[1].borrow_obj().unwrap();
					parent_obj.unchecked_gtk_container().add(child_obj.unchecked_gtk_widget());
					Value::Void
				}
			)?;
		}
	}

	let notifier = Type::from_body(vec!["Notifier".into()], TypeBody::Primitive(PrimitiveType::Notifier));
	symtab.add_type(notifier.clone())?;
	symtab.add_builtin_static_method(
		&notifier, "new", &notifier, &[],
		move |_, _, _| Obj::Notifier(vec![]).to_heap()
	)?;
	symtab.add_builtin_method(
		&notifier, "connect", &void_(), &[(any_(), "target".into()), (str_(), "funcname".into())],
		move |_, arg_types, args| {
			let mut notifier = args[0].borrow_obj_mut().unwrap();
			let target_type = arg_types[0].clone();
			let target = args[1].clone();
			let funcname: Symbol = args[2].borrow_obj().unwrap().unchecked_str().into();
			let mut qid = target_type.name.clone();
			qid.push(funcname);
			notifier.unchecked_notifier_mut().push((target, qid));
			Value::Void
		}
	)?;
	symtab.add_builtin_method(
		&notifier, "notify", &void_(), &[],
		move |symtab, _, args| {
			let notifier = args[0].borrow_obj().unwrap();
			for (target, func_qid) in notifier.unchecked_notifier() {
				call_func(symtab, func_qid, &[target.clone()], &[], true);
			}
			Value::Void
		}
	)?;

	Ok(())
}

pub fn inject_wrap_type(symtab: &mut SymbolTable, wrap_type: Type, target_type: Type) -> Result<(), SymTabError> {
	symtab.add_builtin_static_method(
		&wrap_type, "wrap", &wrap_type, &[(target_type.clone(), "v".into())],
		move |_, _, args| args[0].clone()
	)?;
	symtab.add_builtin_method(
		&wrap_type, "unwrap", &target_type, &[],
		move |_, _, args| args[0].clone()
	)?;
	Ok(())
}

pub fn inject_enum_type(symtab: &mut SymbolTable, typ: Type, has_fields: bool) -> Result<(), SymTabError> {
	symtab.add_builtin_method(
		&typ, "discriminant", &symtab.int_type.clone(), &[],
		move |_, _, args| { Value::Int(args[0].unchecked_enum_index().try_into().unwrap()) }
	)?;
	if !has_fields {
		symtab.add_binary_bool(typ.clone(), "op#==", move |_, _, args| Value::Bool(args[0].unchecked_enum_index() == args[1].unchecked_enum_index()))?;
		symtab.add_binary_bool(typ.clone(), "op#!=", move |_, _, args| Value::Bool(args[0].unchecked_enum_index() != args[1].unchecked_enum_index()))?;
	}
	Ok(())
}

pub fn inject_record_type(symtab: &mut SymbolTable, typ: Type, fields: &[(Type, Symbol)]) -> Result<(), SymTabError> {
	for (idx, (ftyp, fid)) in fields.iter().enumerate() {
		symtab.add_builtin_method(
			&typ, fid, ftyp, &[],
			move |_, _, args| args[0].borrow_obj().unwrap().unchecked_record()[idx].clone()
		)?;
		symtab.add_builtin_method(
			&typ, &(fid.to_string() + "="), &symtab.void_type.clone(), &[(ftyp.clone(), "v".into())],
			move |_, _, args| { args[0].borrow_obj_mut().unwrap().unchecked_record_mut()[idx] = args[1].clone(); Value::Void }
		)?;
	}

	// TODO: only create 'default' for records that are all default types?
	//   (although, this might cause issues as default methods can be defined later...)
	let typ_ = typ.clone();
	symtab.add_builtin_static_method(
		&typ, "default", &typ, &[],
		move |symtab, _, _args| {
			let tbody = typ_.borrow();
			let fields = tbody.unchecked_record_fields();
			let mut values = Vec::with_capacity(fields.len());
			for (ftyp, _) in fields {
				let mut ftyp_name = ftyp.name.clone();
				ftyp_name.push("default".into());
				values.push(call_func(symtab, &ftyp_name, &[], &[], false).unwrap());
			}

			Obj::Record(values).to_heap()
		}
	)?;

	symtab.add_builtin_static_method(
		&typ, "build", &typ, &fields,
		move |_, _, args| Obj::Record(args.to_vec()).to_heap()
	)?;

	Ok(())
}
