use crate::ast::*;
use crate::data::*;
use crate::eval::*;
use symbol::Symbol;
use std::convert::TryInto;
use gtk::prelude::*;
use std::rc::Rc;
use std::cell::RefCell;

macro_rules! id {
	($id:ident) => { stringify!($id).into() };
	($id:expr) => { $id.into() };
}

macro_rules! qid {
	($($id:tt):*) => {
		vec![ $( id!($id) ),* ]
	};
}

macro_rules! qid_slice {
	($($id:tt):*) => {
		&[ $( id!($id) ),* ]
	};
}

macro_rules! qid_combine {
	($qid:expr, $id:expr) => {
		{
			let mut new_qid = $qid.clone();
			new_qid.push($id);
			new_qid
		}
	};
}

impl SymbolTable {
	fn add_binary_bool<F: Fn(&Rc<RefCell<SymbolTable>>, &[Type], &[Value]) -> Value + 'static>(&mut self, typ: Type, name: &str, f: F) -> Result<(), SymTabError> {
		self.add_builtin_method(
			&typ, name,
			&self.bool_type.clone(), &[(typ.clone(), id!("v"))],
			f
		)
	}
	fn add_simple_new<F: Fn(&Rc<RefCell<SymbolTable>>, Value) -> Value + 'static>(&mut self, typ: Type, f: F) -> Result<(), SymTabError> {
		self.add_builtin_static_method(
			&typ, "new",
			&typ, &[(typ.clone(), id!("v"))],
			move |s, _, args| f(s, args[0].clone())
		)
	}
	fn add_default<F: Fn(&Rc<RefCell<SymbolTable>>) -> Value + 'static>(&mut self, typ: Type, f: F) -> Result<(), SymTabError> {
		self.add_builtin_static_method(&typ, "default", &typ, &[], move |s, _, _| f(s))
	}
}

pub fn inject(symtab_rc: &Rc<RefCell<SymbolTable>>) -> Result<(), SymTabError> {
	let mut symtab = symtab_rc.borrow_mut();

	// Obtain all types
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

	// TODO checkme, there should be a better way to do namespacing
	symtab.add_type(Type::from_body(qid![gui], TypeBody::Incomplete))?;

	let notifier = Type::from_body(qid!(Notifier), TypeBody::Primitive(PrimitiveType::Notifier));

	// TODO make it easier to build enums from here...
	let orientation = Type::from_body(
		qid!(gui:Orientation),
		TypeBody::Enum(vec![
			(id!("Horizontal"), vec![]),
			(id!("Vertical"), vec![]),
		])
	);

	let button = Type::from_body(qid!(gui:Button), TypeBody::Primitive(PrimitiveType::GuiButton));
	let entry = Type::from_body(qid!(gui:Entry), TypeBody::Primitive(PrimitiveType::GuiEntry));
	let window = Type::from_body(qid!(gui:Window), TypeBody::Primitive(PrimitiveType::GuiWindow));
	let boxt = Type::from_body(qid!(gui:Box), TypeBody::Primitive(PrimitiveType::GuiBox));

	symtab.add_type(notifier.clone())?;
	symtab.add_type(orientation.clone())?;
	symtab.add_type(button.clone())?;
	symtab.add_type(entry.clone())?;
	symtab.add_type(window.clone())?;
	symtab.add_type(boxt.clone())?;

	macro_rules! resolve_type {
		(IntI32) => { int_() };
		(Int) => { int_() };
		(Real) => { real_() };
		(Bool) => { bool_() };
		(Str) => { str_() };
	}
	macro_rules! unpack_type {
		($out:ident, IntI32, $e:expr) => { let $out: i32 = $e.unchecked_int().try_into().unwrap(); };
		($out:ident, Int, $e:expr) => { let $out = $e.unchecked_int(); };
		($out:ident, Real, $e:expr) => { let $out = $e.unchecked_real(); };
		($out:ident, Bool, $e:expr) => { let $out = $e.unchecked_bool(); };
		($out:ident, Str, $e:expr) => { let $out = $e.borrow_obj().unwrap(); let $out = $out.unchecked_str(); };
	}
	macro_rules! pack_type {
		(IntI32, $e:expr) => { Value::Int($e) };
		(Int, $e:expr) => { Value::Int($e) };
		(Real, $e:expr) => { Value::Real($e) };
		(Bool, $e:expr) => { Value::Bool($e) };
		(Str, $e:expr) => { Obj::Str($e).to_heap() };
	}

	macro_rules! export_notifier {
		($typ:expr, $enum_id:ident, $rust_name:ident, $getter_id:expr) => {
			symtab.add_builtin_method(
				&$typ, $getter_id, &notifier, &[],
				move |_, _, args| {
					match &*args[0].borrow_obj().unwrap() {
						Obj::$enum_id { $rust_name, .. } => $rust_name.clone(),
						_ => unreachable!()
					}
				}
			)?;
		};
	}

	macro_rules! export_obj_getter {
		($obj_typ:expr, $value_typ:ident, $field_id:expr, |$arg:ident| $code:expr) => {
			symtab.add_builtin_method(
				&$obj_typ, $field_id, &resolve_type!($value_typ), &[],
				move |_, _, args| {
					let $arg = args[0].borrow_obj().unwrap();
					let result = $code;
					pack_type!($value_typ, result)
				}
			)?;
		};
	}

	macro_rules! export_obj_setter {
		($obj_typ:expr, $value_typ:ident, $field_id:expr, |$obj:ident, $value:ident| $code:expr) => {
			symtab.add_builtin_method(
				&$obj_typ, &($field_id.to_owned() + "="), &void_(), &[(resolve_type!($value_typ), id!(value))],
				move |_, _, args| {
					let $obj = args[0].borrow_obj().unwrap();
					unpack_type!($value, $value_typ, args[1]);
					$code;
					Value::Void
				}
			)?;
		};
	}

	macro_rules! export_binary {
		($ret_typ: ident, $typ:ident, $method_id:expr, |$a:ident, $b:ident| $code:expr) => {
			symtab.add_builtin_method(
				&resolve_type!($typ), $method_id,
				&resolve_type!($ret_typ),
				&[(resolve_type!($typ), id!(other))],
				move |_, _, args| {
					unpack_type!($a, $typ, args[0]);
					unpack_type!($b, $typ, args[1]);
					let result = $code;
					pack_type!($ret_typ, result)
				}
			)?;
		};
	}

	export_binary!(Bool, Bool, id!("op#=="), |a, b| a == b);
	export_binary!(Bool, Bool, id!("op#!="), |a, b| a != b);
	symtab.add_simple_new(bool_(), move |_, v| Value::Bool(v.unchecked_bool()))?;
	symtab.add_default(bool_(), move |_| Value::Bool(false))?;

	export_binary!(Int, Int, id!("op#+"), |a, b| a + b);
	export_binary!(Int, Int, id!("op#-"), |a, b| a - b);
	export_binary!(Int, Int, id!("op#*"), |a, b| a * b);
	export_binary!(Int, Int, id!("op#/"), |a, b| a / b);
	export_binary!(Bool, Int, id!("op#=="), |a, b| a == b);
	export_binary!(Bool, Int, id!("op#!="), |a, b| a != b);
	export_binary!(Bool, Int, id!("op#<"), |a, b| a < b);
	export_binary!(Bool, Int, id!("op#<="), |a, b| a <= b);
	export_binary!(Bool, Int, id!("op#>"), |a, b| a > b);
	export_binary!(Bool, Int, id!("op#>="), |a, b| a >= b);
	symtab.add_simple_new(int_(), move |_, v| Value::Int(v.unchecked_int()))?;
	symtab.add_default(int_(), move |_| Value::Int(0))?;

	export_binary!(Real, Real, id!("op#+"), |a, b| a + b);
	export_binary!(Real, Real, id!("op#-"), |a, b| a - b);
	export_binary!(Real, Real, id!("op#*"), |a, b| a * b);
	export_binary!(Real, Real, id!("op#/"), |a, b| a / b);
	export_binary!(Bool, Real, id!("op#=="), |a, b| a == b);
	export_binary!(Bool, Real, id!("op#!="), |a, b| a != b);
	export_binary!(Bool, Real, id!("op#<"), |a, b| a < b);
	export_binary!(Bool, Real, id!("op#<="), |a, b| a <= b);
	export_binary!(Bool, Real, id!("op#>"), |a, b| a > b);
	export_binary!(Bool, Real, id!("op#>="), |a, b| a >= b);
	symtab.add_simple_new(real_(), move |_, v| Value::Real(v.unchecked_real()))?;
	symtab.add_default(real_(), move |_| Value::Real(0.))?;

	export_binary!(Str, Str, id!("op#+"), |a, b| {
		let mut s = String::with_capacity(a.len() + b.len());
		s.push_str(a);
		s.push_str(b);
		s
	});

	symtab.add_builtin_function(
		qid!(str:from), &str_(), &[(bool_(), id!(v))],
		move |_, _, args| Obj::Str(args[0].unchecked_bool().to_string()).to_heap()
	)?;
	symtab.add_builtin_function(
		qid!(str:from), &str_(), &[(int_(), id!(v))],
		move |_, _, args| Obj::Str(args[0].unchecked_int().to_string()).to_heap()
	)?;
	symtab.add_builtin_function(
		qid!(str:from), &str_(), &[(real_(), id!(v))],
		move |_, _, args| Obj::Str(args[0].unchecked_real().to_string()).to_heap()
	)?;
	symtab.add_simple_new(str_(), move |_, s| Obj::Str(s.borrow_obj().unwrap().unchecked_str().clone()).to_heap())?;
	symtab.add_default(str_(), move |_| Obj::Str("".to_string()).to_heap())?;

	symtab.add_builtin_function(
		qid!(print), &void_(), &[],
		move |_, _, _| { print!("\n"); Value::Void }
	)?;
	symtab.add_builtin_function(
		qid!(print), &void_(), &[(int_(), id!(v))],
		move |_, _, args| { print!("{}", args[0].unchecked_int()); Value::Void }
	)?;
	symtab.add_builtin_function(
		qid!(print), &void_(), &[(real_(), id!(v))],
		move |_, _, args| { print!("{}", args[0].unchecked_real()); Value::Void }
	)?;
	symtab.add_builtin_function(
		qid!(print), &void_(), &[(str_(), id!(v))],
		move |_, _, args| { print!("{}", args[0].borrow_obj().unwrap().unchecked_str()); Value::Void }
	)?;

	symtab.add_builtin_static_method(
		&notifier, "new", &notifier, &[],
		move |_, _, _| Obj::Notifier(vec![]).to_heap()
	)?;
	symtab.add_builtin_method(
		&notifier, "connect", &void_(), &[(any_(), id!(target)), (str_(), id!(funcname))],
		move |_, arg_types, args| {
			let mut notifier = args[0].borrow_obj_mut().unwrap();
			let target_type = arg_types[0].clone();
			let target = args[1].clone();
			let funcname = id!(args[2].borrow_obj().unwrap().unchecked_str());
			let qid = qid_combine!(target_type.name, funcname);
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


	symtab.add_builtin_function(
		qid!(gui:init), &void_(), &[],
		move |_, _, _args| { gtk::init().expect("GTK init failed"); Value::Void }
	)?;
	symtab.add_builtin_function(
		qid!(gui:run), &void_(), &[],
		move |_, _, _args| { gtk::main(); Value::Void }
	)?;

	let orientation_c = symtab.root.resolve_mut(&orientation.name).unwrap().get_children_mut().unwrap();
	orientation_c.insert(id!(Horizontal), SymTabNode::new_constant(orientation.clone(), Value::Enum(0, vec![])));
	orientation_c.insert(id!(Vertical), SymTabNode::new_constant(orientation.clone(), Value::Enum(1, vec![])));
	inject_enum_type(&mut symtab, orientation.clone(), false)?;

	symtab.add_builtin_static_method(
		&button, "new", &button, &[],
		move |symtab_rc, _, _args| {
			let button = gtk::Button::new();
			let clicked_notifier = Obj::Notifier(vec![]).to_heap();
			let val = Obj::GuiButton { button: button.clone(), clicked_notifier }.to_heap();
			let symtab_rc = Rc::clone(&symtab_rc);

			let val_ = val.clone();
			button.connect_clicked(move |_| {
				match &*val_.borrow_obj().unwrap() {
					Obj::GuiButton { clicked_notifier, .. } => {
						call_func(&symtab_rc, qid_slice!(Notifier:notify), &[clicked_notifier.clone()], &[], true);
					},
					_ => unreachable!()
				}
			});

			val
		}
	)?;
	export_notifier!(button, GuiButton, clicked_notifier, "_n_clicked");
	symtab.add_builtin_method(
		&button, "label=", &void_(), &[(str_(), "s".into())],
		move |_, _, args| { args[0].borrow_obj().unwrap().unchecked_gtk_button().set_label(args[1].borrow_obj().unwrap().unchecked_str()); Value::Void }
	)?;


	symtab.add_builtin_static_method(
		&entry, "new", &entry, &[],
		move |symtab_rc, _, _args| {
			let entry = gtk::Entry::new();
			let changed_notifier = Obj::Notifier(vec![]).to_heap();
			let val = Obj::GuiEntry { entry: entry.clone(), changed_notifier }.to_heap();
			let symtab_rc = Rc::clone(&symtab_rc);

			let val_ = val.clone();
			entry.connect_changed(move |_| {
				match &*val_.borrow_obj().unwrap() {
					Obj::GuiEntry { changed_notifier, .. } => {
						call_func(&symtab_rc, qid_slice!(Notifier:notify), &[changed_notifier.clone()], &[], true);
					},
					_ => unreachable!()
				}
			});

			val
		}
	)?;
	export_notifier!(entry, GuiEntry, changed_notifier, "_n_text");
	export_obj_getter!(entry, Str, "text", |o| o.unchecked_gtk_entry().get_text().unwrap().to_string());
	export_obj_setter!(entry, Str, "text", |o,s| o.unchecked_gtk_entry().set_text(s));

	symtab.add_builtin_static_method(
		&window, "new", &window, &[],
		move |_, _, _args| Obj::GuiWindow(gtk::Window::new(gtk::WindowType::Toplevel)).to_heap()
	)?;
	symtab.add_builtin_method(
		&window, "show", &void_(), &[],
		move |_, _, args| { args[0].borrow_obj().unwrap().unchecked_gtk_window().show_all(); Value::Void }
	)?;

	symtab.add_builtin_static_method(
		&boxt, "new", &boxt, &[(orientation.clone(), id!(orientation))],
		move |_, _, args| {
			let orient = match args[0].unchecked_enum_index() {
				0 => gtk::Orientation::Horizontal,
				1 => gtk::Orientation::Vertical,
				_ => panic!("unknown Orientation")
			};
			Obj::GuiBox(gtk::Box::new(orient, 0)).to_heap()
		}
	)?;
	export_obj_setter!(boxt, IntI32, "spacing", |o,s| o.unchecked_gtk_box().set_spacing(s));
	symtab.add_builtin_method(
		&boxt, "spacing=", &int_(), &[],
		move |_, _, args| Value::Int(args[0].borrow_obj().unwrap().unchecked_gtk_box().get_spacing().into())
	)?;

	let container_parents = vec![window.clone(), boxt.clone()];
	let container_children = vec![boxt.clone(), button.clone(), entry.clone()];
	for parent in &container_parents {
		for child in &container_children {
			symtab.add_builtin_method(
				&parent, "add_child", &void_(), &[(child.clone(), id!(child))],
				move |_, _, args| {
					let parent_obj = args[0].borrow_obj().unwrap();
					let child_obj = args[1].borrow_obj().unwrap();
					parent_obj.unchecked_gtk_container().add(child_obj.unchecked_gtk_widget());
					Value::Void
				}
			)?;
		}
	}

	Ok(())
}

pub fn inject_wrap_type(symtab: &mut SymbolTable, wrap_type: Type, target_type: Type) -> Result<(), SymTabError> {
	symtab.add_builtin_static_method(
		&wrap_type, "wrap", &wrap_type, &[(target_type.clone(), id!(v))],
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

pub fn inject_record_type(symtab: &mut SymbolTable, typ: Type, fields: &[(Type, Symbol)], rename_setters: bool) -> Result<(), SymTabError> {
	for (idx, (ftyp, fid)) in fields.iter().enumerate() {
		symtab.add_builtin_method(
			&typ, fid, ftyp, &[],
			move |_, _, args| args[0].borrow_obj().unwrap().unchecked_record()[idx].clone()
		)?;
		let setter_name = match rename_setters {
			true =>  format!("_set_{}", fid.to_string()),
			false => fid.to_string() + "="
		};
		symtab.add_builtin_method(
			&typ, &setter_name, &symtab.void_type.clone(), &[(ftyp.clone(), id!(v))],
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
				ftyp_name.push(id!(default));
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
