use crate::ast::*;
use crate::data::*;
use crate::eval::*;
use symbol::Symbol;
use std::convert::TryInto;
use gtk::prelude::*;
use std::rc::Rc;
use std::cell::RefCell;

impl SymbolTable {
	fn add_binary_bool<F: Fn(&Rc<RefCell<SymbolTable>>, &[TypeRef], &[Value]) -> Value + 'static>(&mut self, typ: Type, name: Symbol, f: F) -> Result<(), SymTabError> {
		self.add_builtin_method(
			true, &typ, name,
			&self.bool_type.clone(), &[(typ.clone(), id!("v"))],
			f
		)
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

	let mut maybe = Type::from_body(qid!(Maybe), TypeBody::Incomplete);
	*maybe.borrow_mut() = TypeBody::Enum(vec![
		(id!(None), vec![]),
		(id!(Just), vec![(SpecType::Type(maybe.clone(), vec![SpecType::Placeholder(0)]), id!(field))])
	]);

	// TODO checkme, there should be a better way to do namespacing
	symtab.add_type(Type::from_body(qid![gui], TypeBody::Incomplete))?;

	let notifier = Type::from_body(qid!(Notifier), TypeBody::Primitive(PrimitiveType::Notifier));

	// TODO make it easier to build enums from here...
	let orientation = Type::from_body(
		qid!(gui:Orientation),
		TypeBody::Enum(vec![
			(id!(Horizontal), vec![]),
			(id!(Vertical), vec![]),
		])
	);

	let boxt = Type::from_body(qid!(gui:Box), TypeBody::Primitive(PrimitiveType::GuiBox));
	let button = Type::from_body(qid!(gui:Button), TypeBody::Primitive(PrimitiveType::GuiButton));
	let checkbutton = Type::from_body(qid!(gui:CheckButton), TypeBody::Primitive(PrimitiveType::GuiCheckButton));
	let entry = Type::from_body(qid!(gui:Entry), TypeBody::Primitive(PrimitiveType::GuiEntry));
	let label = Type::from_body(qid!(gui:Label), TypeBody::Primitive(PrimitiveType::GuiLabel));
	let togglebutton = Type::from_body(qid!(gui:ToggleButton), TypeBody::Primitive(PrimitiveType::GuiToggleButton));
	let window = Type::from_body(qid!(gui:Window), TypeBody::Primitive(PrimitiveType::GuiWindow));

	symtab.add_type(maybe.clone())?;
	symtab.add_type(notifier.clone())?;
	symtab.add_type(orientation.clone())?;
	symtab.add_type(boxt.clone())?;
	symtab.add_type(button.clone())?;
	symtab.add_type(checkbutton.clone())?;
	symtab.add_type(entry.clone())?;
	symtab.add_type(label.clone())?;
	symtab.add_type(togglebutton.clone())?;
	symtab.add_type(window.clone())?;

	macro_rules! resolve_type {
		(IntI32) => { int_() };
		(IntU32) => { int_() };
		(IntUsize) => { int_() };
		(Int) => { int_() };
		(Real) => { real_() };
		(Bool) => { bool_() };
		(Str) => { str_() };
		(Void) => { void_() };
		(Notifier) => { notifier.clone() };
		(GuiBox) => { boxt };
		(GuiButton) => { button.clone() };
		(GuiCheckButton) => { checkbutton.clone() };
		(GuiEntry) => { entry.clone() };
		(GuiLabel) => { label.clone() };
		(GuiToggleButton) => { togglebutton.clone() };
		(GuiWindow) => { window.clone() };
	}
	macro_rules! resolve_spec_type {
		(MaybeStr) => { SpecType::Type(maybe.clone(), vec![SpecType::Type(str_(), vec![])]) };
		($i:ident) => { SpecType::Type(resolve_type!($i), vec![]) };
	}
	macro_rules! unpack_type {
		($out:ident, IntI32, $e:expr) => { let $out: i32 = $e.unchecked_int().try_into().unwrap(); };
		($out:ident, IntU32, $e:expr) => { let $out: u32 = $e.unchecked_int().try_into().unwrap(); };
		($out:ident, IntUsize, $e:expr) => { let $out: usize = $e.unchecked_int().try_into().unwrap(); };
		($out:ident, Int, $e:expr) => { let $out = $e.unchecked_int(); };
		($out:ident, Real, $e:expr) => { let $out = $e.unchecked_real(); };
		($out:ident, Bool, $e:expr) => { let $out = $e.unchecked_bool(); };
		($out:ident, Str, $e:expr) => { let $out = $e.borrow_obj().unwrap(); let $out = $out.unchecked_str(); };
		($out:ident, MaybeStr, $e:expr) => {
			let $out = $e;
			let ind = $out.unchecked_enum_index();
			let $out = match ind {
				0 => None,
				1 => Some($out.unchecked_enum_args()[0].borrow_obj().unwrap().unchecked_str().clone()),
				_ => unreachable!("bad MaybeStr")
			};
		};
		($out:ident, Notifier, $e:expr) => { let $out = $e.borrow_obj().unwrap(); let $out = $out.unchecked_notifier(); };
		($out:ident, GuiBox, $e:expr) => { let $out = $e.borrow_obj().unwrap(); let $out = $out.unchecked_gtk_box(); };
		($out:ident, GuiButton, $e:expr) => { let $out = $e.borrow_obj().unwrap(); let $out = $out.unchecked_gtk_button(); };
		($out:ident, GuiCheckButton, $e:expr) => { let $out = $e.borrow_obj().unwrap(); let $out = $out.unchecked_gtk_checkbutton(); };
		($out:ident, GuiEntry, $e:expr) => { let $out = $e.borrow_obj().unwrap(); let $out = $out.unchecked_gtk_entry(); };
		($out:ident, GuiLabel, $e:expr) => { let $out = $e.borrow_obj().unwrap(); let $out = $out.unchecked_gtk_label(); };
		($out:ident, GuiToggleButton, $e:expr) => { let $out = $e.borrow_obj().unwrap(); let $out = $out.unchecked_gtk_togglebutton(); };
		($out:ident, GuiWindow, $e:expr) => { let $out = $e.borrow_obj().unwrap(); let $out = $out.unchecked_gtk_window(); };
	}
	macro_rules! convert_arg {
		(SymbolTable, $arg:ident) => { (SpecType::Type(void_(), vec![]), id!(_DUMMY)) };
		($arg_typ:ident, $arg:ident) => { (resolve_spec_type!($arg_typ), id!($arg)) };
	}
	macro_rules! load_arg {
		($out:ident, SymbolTable, $_arg_iter:expr, $symtab:expr) => { let $out = $symtab; };
		($out:ident, $ty:ident, $arg_iter:expr, $_symtab:expr) => { unpack_type!($out, $ty, $arg_iter.next().unwrap()); };
	}
	macro_rules! pack_type {
		(IntI32, $e:expr) => { Value::Int($e.into()) };
		(IntU32, $e:expr) => { Value::Int($e.into()) };
		(IntUsize, $e:expr) => { Value::Int($e.try_into().unwrap()) };
		(Int, $e:expr) => { Value::Int($e) };
		(Real, $e:expr) => { Value::Real($e) };
		(Bool, $e:expr) => { Value::Bool($e) };
		(Str, $e:expr) => { Obj::Str($e).to_heap() };
		(MaybeStr, $e:expr) => {
			match $e {
				None => Value::Enum(0, vec![]),
				Some(s) => Value::Enum(1, vec![Obj::Str(s.to_string()).to_heap()])
			}
		};
		(Void, $_:tt) => { Value::Void };
		(Notifier, $e:expr) => { $e.to_heap() };
		(GuiBox, $e:expr) => { $e };
		(GuiButton, $e:expr) => { $e };
		(GuiCheckButton, $e:expr) => { $e };
		(GuiEntry, $e:expr) => { $e };
		(GuiLabel, $e:expr) => { $e };
		(GuiToggleButton, $e:expr) => { $e };
		(GuiWindow, $e:expr) => { $e };
	}

	macro_rules! export {
		// Function without parameters
		($ret_typ:ident, $qid:expr, || $code:expr) => {
			symtab.add_builtin_function(
				$qid, &resolve_type!($ret_typ),
				&[],
				move |_, _, _| {
					#[allow(unused_variables)]
					let result = $code;
					pack_type!($ret_typ, result)
				}
			)?;
		};
		// Function with parameters
		($ret_typ:ident, $qid:expr, |$($arg:ident : $arg_typ:ident),*| $code:expr) => {
			symtab.add_builtin_function(
				$qid, &resolve_type!($ret_typ),
				&[ $( (resolve_type!($arg_typ), id!($arg)) ),* ],
				move |_, _, args| {
					let mut arg_iter = args.iter();
					$( unpack_type!($arg, $arg_typ, arg_iter.next().unwrap());)*
					#[allow(unused_variables)]
					let result = $code;
					pack_type!($ret_typ, result)
				}
			)?;
		};
		// Static method without parameters
		($ret_typ:ident, $typ:ident, $name:tt, || $code:expr) => {
			symtab.add_builtin_generic_method(
				false,
				&resolve_type!($typ), id!($name), &resolve_spec_type!($ret_typ),
				&[],
				move |_, _, _| {
					#[allow(unused_variables)]
					let result = $code;
					pack_type!($ret_typ, result)
				}
			)?;
		};
		// Static method with parameters
		($ret_typ:ident, $typ:ident, $name:tt, |$($arg:ident : $arg_typ:ident),*| $code:expr) => {
			symtab.add_builtin_generic_method(
				false,
				&resolve_type!($typ), id!($name), &resolve_spec_type!($ret_typ),
				&[ $( convert_arg!($arg_typ, $arg) ),* ],
				#[allow(unused_variables)]
				move |symtab, _, args| {
					#[allow(unused_mut)]
					let mut arg_iter = args.iter();
					$( load_arg!($arg, $arg_typ, arg_iter, symtab);)*
					let result = $code;
					pack_type!($ret_typ, result)
				}
			)?;
		};
		// Method without parameters
		($ret_typ:ident, $typ:ident, $name:tt, |$this: ident| $code:expr) => {
			symtab.add_builtin_generic_method(
				true,
				&resolve_type!($typ), id!($name), &resolve_spec_type!($ret_typ),
				&[],
				move |_, _, args| {
					unpack_type!($this, $typ, args[0]);
					#[allow(unused_variables)]
					let result = $code;
					pack_type!($ret_typ, result)
				}
			)?;
		};
		// Method with parameters
		($ret_typ:ident, $typ:ident, $name:tt, |$this: ident, $($arg:ident : $arg_typ:ident),*| $code:expr) => {
			symtab.add_builtin_generic_method(
				true,
				&resolve_type!($typ), id!($name), &resolve_spec_type!($ret_typ),
				&[ $( convert_arg!($arg_typ, $arg) ),* ],
				#[allow(unused_variables)]
				move |symtab, _, args| {
					#[allow(unused_mut)]
					let mut arg_iter = args.iter();
					unpack_type!($this, $typ, arg_iter.next().unwrap());
					$( load_arg!($arg, $arg_typ, arg_iter, symtab);)*
					let result = $code;
					pack_type!($ret_typ, result)
				}
			)?;
		};
	}

	macro_rules! extract_notifier {
		($enum_id:ident, $notifier_id:ident, $val:expr) => {
			match &*$val.borrow_obj().unwrap() {
				Obj::$enum_id { $notifier_id, .. } => $notifier_id.clone(),
				_ => unreachable!()
			}
		};
	}
	macro_rules! export_notifier {
		($typ:ident, $field_name:ident, $getter_id:ident) => {
			symtab.add_builtin_method(
				true,
				&resolve_type!($typ), id!($getter_id), &notifier, &[],
				move |_, _, args| extract_notifier!($typ, $field_name, args[0])
			)?;
		};
	}
	macro_rules! connect_gtk_signal {
		($gtk_obj:expr, $gtk_method:ident, $enum_id:ident, $notifier_id:ident, $val:expr, $symtab_rc:expr) => {
			let symtab_rc = Rc::clone(&$symtab_rc);
			let val = $val.clone();
			$gtk_obj.$gtk_method(move |_| {
				let not = extract_notifier!($enum_id, $notifier_id, val);
				call_func(&symtab_rc, qid_slice!(Notifier), &[], id!(notify), &[not.clone()], &[], true);
			});
		};
	}

	macro_rules! export_getter {
		($obj_typ:ident, $id:ident : $typ:ident, |$this: ident| $code:expr) => {
			export!($typ, $obj_typ, $id, |$this| $code);
		};
	}
	macro_rules! export_setter {
		($obj_typ:ident, |$this: ident, $id:ident : $typ:ident| $code:expr) => {
			let id: Symbol = id!($id);
			export!(Void, $obj_typ, (id.to_string() + "="), |$this, $id : $typ| $code);
		};
	}
	macro_rules! connect_gtk_property {
		($obj_typ:ident, $id:ident: Str, $get_id:ident, $set_id:ident) => {
			export_getter!($obj_typ, $id: Str, |this| this.$get_id().unwrap().to_string());
			export_setter!($obj_typ, |this, $id: Str| this.$set_id($id));
		};
		($obj_typ:ident, $id:ident: MaybeStr, $get_id:ident, $set_id:ident) => {
			export_getter!($obj_typ, $id: MaybeStr, |this| this.$get_id().map(|x| x.to_string()));
			export_setter!($obj_typ, |this, $id: MaybeStr| this.$set_id($id.as_deref()));
		};
		($obj_typ:ident, $id:ident : $prop_typ:ident, $get_id:ident, $set_id:ident) => {
			export_getter!($obj_typ, $id: $prop_typ, |this| this.$get_id());
			export_setter!($obj_typ, |this, $id: $prop_typ| this.$set_id($id));
		};
	}

	macro_rules! connect_gtk_container {
		($as_container_typ:ident) => {
			connect_gtk_property!($as_container_typ, border_width: IntU32, get_border_width, set_border_width);
		};
	}

	macro_rules! connect_gtk_widget {
		($as_widget_typ:ident) => {
			connect_gtk_property!($as_widget_typ, sensitive: Bool, get_sensitive, set_sensitive);
			connect_gtk_property!($as_widget_typ, visible: Bool, get_visible, set_visible);
		};
	}

	macro_rules! connect_gtk_button {
		($typ:ident) => {
			export_notifier!($typ, clicked_notifier, _n_clicked);
			connect_gtk_property!($typ, label: Str, get_label, set_label);
		};
	}

	macro_rules! connect_gtk_togglebutton {
		($typ:ident) => {
			export_notifier!($typ, toggled_notifier, _n_active);
			connect_gtk_property!($typ, active: Bool, get_active, set_active);
		};
	}

	macro_rules! export_binary {
		($ret_typ: ident, $typ:ident, $method_id:expr, |$a:ident, $b:ident| $code:expr) => {
			export!($ret_typ, $typ, $method_id, |$a, $b : $typ| $code);
		};
	}

	export_binary!(Bool, Bool, "op#==", |a, b| a == b);
	export_binary!(Bool, Bool, "op#!=", |a, b| a != b);
	export_binary!(Bool, Bool, "op#&&", |a, b| a && b);
	export_binary!(Bool, Bool, "op#||", |a, b| a || b);
	export!(Bool, Bool, new, |b: Bool| b);
	export!(Bool, Bool, default, || false);

	export_binary!(Int, Int, "op#+", |a, b| a + b);
	export_binary!(Int, Int, "op#-", |a, b| a - b);
	export_binary!(Int, Int, "op#*", |a, b| a * b);
	export_binary!(Int, Int, "op#/", |a, b| a / b);
	export_binary!(Bool, Int, "op#==", |a, b| a == b);
	export_binary!(Bool, Int, "op#!=", |a, b| a != b);
	export_binary!(Bool, Int, "op#<", |a, b| a < b);
	export_binary!(Bool, Int, "op#<=", |a, b| a <= b);
	export_binary!(Bool, Int, "op#>", |a, b| a > b);
	export_binary!(Bool, Int, "op#>=", |a, b| a >= b);
	export!(Int, Int, new, |i: Int| i);
	export!(Int, Int, default, || 0);

	export_binary!(Real, Real, "op#+", |a, b| a + b);
	export_binary!(Real, Real, "op#-", |a, b| a - b);
	export_binary!(Real, Real, "op#*", |a, b| a * b);
	export_binary!(Real, Real, "op#/", |a, b| a / b);
	export_binary!(Bool, Real, "op#==", |a, b| a == b);
	export_binary!(Bool, Real, "op#!=", |a, b| a != b);
	export_binary!(Bool, Real, "op#<", |a, b| a < b);
	export_binary!(Bool, Real, "op#<=", |a, b| a <= b);
	export_binary!(Bool, Real, "op#>", |a, b| a > b);
	export_binary!(Bool, Real, "op#>=", |a, b| a >= b);
	export!(Real, Real, new, |r: Real| r);
	export!(Real, Real, default, || 0.);

	export_binary!(Bool, Str, "op#==", |a, b| a == b);
	export_binary!(Bool, Str, "op#!=", |a, b| a != b);
	export_binary!(Str, Str, "op#+", |a, b| {
		let mut s = String::with_capacity(a.len() + b.len());
		s.push_str(a);
		s.push_str(b);
		s
	});
	export!(IntUsize, Str, length, |this| this.len());

	export!(Str, Str, from, |v: Bool| v.to_string());
	export!(Str, Str, from, |v: Int| v.to_string());
	export!(Str, Str, from, |v: Real| v.to_string());
	export!(Str, Str, new, |s: Str| s.to_string());
	export!(Str, Str, default, || "".to_string());

	let maybe_c = symtab.root.resolve_mut(&maybe.name).unwrap().get_children_mut().unwrap();
	maybe_c.insert(id!(None), SymTabNode::new_constant(SpecType::Type(maybe.clone(), vec![SpecType::Placeholder(0)]), Value::Enum(0, vec![])));
	symtab.add_builtin_generic_method(
		false, &maybe, id!(Just),
		&SpecType::Type(maybe.clone(), vec![SpecType::Placeholder(0)]),
		&[(SpecType::Placeholder(0), id!(value))],
		move |_, _, args| Value::Enum(1, vec![args[0].clone()])
	)?;

	export!(Void, qid!(print), || print!("\n"));
	export!(Void, qid!(print), |i: Int| print!("{}", i));
	export!(Void, qid!(print), |r: Real| print!("{}", r));
	export!(Void, qid!(print), |s: Str| print!("{}", s));

	// These need special access that the macros don't provide
	export!(Notifier, Notifier, new, || Obj::Notifier(vec![]));
	symtab.add_builtin_method(
		true, &notifier, id!(connect), &void_(), &[(any_(), id!(target)), (str_(), id!(funcname))],
		move |_, arg_types, args| {
			let mut notifier = args[0].borrow_obj_mut().unwrap();
			let target_type = arg_types[0].clone();
			let target = args[1].clone();
			let funcname = id!(args[2].borrow_obj().unwrap().unchecked_str());
			notifier.unchecked_notifier_mut().push((target, target_type, funcname));
			Value::Void
		}
	)?;
	export!(Void, Notifier, notify, |this, symtab: SymbolTable| {
		for (target, target_typeref, funcname) in this {
			call_func(symtab, &target_typeref.0.name, &target_typeref.1, *funcname, &[target.clone()], &[], true);
		}
	});


	export!(Void, qid!(gui:init), || gtk::init().expect("GTK init failed"));
	export!(Void, qid!(gui:run), || gtk::main());
	export!(Void, qid!(gui:quit), || gtk::main_quit());

	let orientation_c = symtab.root.resolve_mut(&orientation.name).unwrap().get_children_mut().unwrap();
	orientation_c.insert(id!(Horizontal), SymTabNode::new_constant(SpecType::Type(orientation.clone(), vec![]), Value::Enum(0, vec![])));
	orientation_c.insert(id!(Vertical), SymTabNode::new_constant(SpecType::Type(orientation.clone(), vec![]), Value::Enum(1, vec![])));
	inject_enum_type(&mut symtab, orientation.clone(), false)?;

	// ****************************************
	// GuiButton
	export!(GuiButton, GuiButton, new, |symtab: SymbolTable| {
		let button = gtk::Button::new();
		let clicked_notifier = Obj::Notifier(vec![]).to_heap();
		let val = Obj::GuiButton { w: button.clone(), clicked_notifier }.to_heap();
		connect_gtk_signal!(button, connect_clicked, GuiButton, clicked_notifier, val, symtab);
		val
	});
	connect_gtk_button!(GuiButton);
	connect_gtk_widget!(GuiButton);

	// ****************************************
	// GuiBox
	symtab.add_builtin_method(
		false, &boxt, id!(new), &boxt, &[(orientation.clone(), id!(orientation))],
		move |_, _, args| {
			let orient = match args[0].unchecked_enum_index() {
				0 => gtk::Orientation::Horizontal,
				1 => gtk::Orientation::Vertical,
				_ => panic!("unknown Orientation")
			};
			Obj::GuiBox { w: gtk::Box::new(orient, 0) }.to_heap()
		}
	)?;
	connect_gtk_property!(GuiBox, spacing: IntI32, get_spacing, set_spacing);
	connect_gtk_container!(GuiBox);
	connect_gtk_widget!(GuiBox);

	// ****************************************
	// GuiCheckButton
	export!(GuiCheckButton, GuiCheckButton, new, |symtab: SymbolTable| {
		let btn = gtk::CheckButton::new();
		let clicked_notifier = Obj::Notifier(vec![]).to_heap();
		let toggled_notifier = Obj::Notifier(vec![]).to_heap();
		let val = Obj::GuiCheckButton { w: btn.clone(), clicked_notifier, toggled_notifier }.to_heap();
		connect_gtk_signal!(btn, connect_clicked, GuiCheckButton, clicked_notifier, val, symtab);
		connect_gtk_signal!(btn, connect_toggled, GuiCheckButton, toggled_notifier, val, symtab);
		val
	});
	connect_gtk_togglebutton!(GuiCheckButton);
	connect_gtk_button!(GuiCheckButton);
	connect_gtk_widget!(GuiCheckButton);

	// ****************************************
	// GuiEntry
	export!(GuiEntry, GuiEntry, new, |symtab: SymbolTable| {
		let entry = gtk::Entry::new();
		let changed_notifier = Obj::Notifier(vec![]).to_heap();
		let val = Obj::GuiEntry { w: entry.clone(), changed_notifier }.to_heap();
		connect_gtk_signal!(entry, connect_changed, GuiEntry, changed_notifier, val, symtab);
		val
	});
	export_notifier!(GuiEntry, changed_notifier, _n_text);
	connect_gtk_property!(GuiEntry, text: Str, get_text, set_text);
	connect_gtk_property!(GuiEntry, placeholder_text: MaybeStr, get_placeholder_text, set_placeholder_text);
	connect_gtk_property!(GuiEntry, visibility: Bool, get_visibility, set_visibility);
	connect_gtk_widget!(GuiEntry);

	// ****************************************
	// GuiLabel
	export!(GuiLabel, GuiLabel, new, |symtab: SymbolTable| {
		Obj::GuiLabel { w: gtk::Label::new(None) }.to_heap()
	});
	connect_gtk_property!(GuiLabel, text: Str, get_text, set_text);
	connect_gtk_widget!(GuiLabel);

	// ****************************************
	// GuiToggleButton
	export!(GuiToggleButton, GuiToggleButton, new, |symtab: SymbolTable| {
		let btn = gtk::ToggleButton::new();
		let clicked_notifier = Obj::Notifier(vec![]).to_heap();
		let toggled_notifier = Obj::Notifier(vec![]).to_heap();
		let val = Obj::GuiToggleButton { w: btn.clone(), clicked_notifier, toggled_notifier }.to_heap();
		connect_gtk_signal!(btn, connect_clicked, GuiToggleButton, clicked_notifier, val, symtab);
		connect_gtk_signal!(btn, connect_toggled, GuiToggleButton, toggled_notifier, val, symtab);
		val
	});
	connect_gtk_togglebutton!(GuiToggleButton);
	connect_gtk_button!(GuiToggleButton);
	connect_gtk_widget!(GuiToggleButton);

	// ****************************************
	// GuiWindow
	export!(GuiWindow, GuiWindow, new, |symtab: SymbolTable| {
		let window = gtk::Window::new(gtk::WindowType::Toplevel);
		let destroy_notifier = Obj::Notifier(vec![]).to_heap();
		let val = Obj::GuiWindow { w: window.clone(), destroy_notifier }.to_heap();
		connect_gtk_signal!(window, connect_destroy, GuiWindow, destroy_notifier, val, symtab);
		val
	});
	export_notifier!(GuiWindow, destroy_notifier, _n_destroy);
	export!(Void, GuiWindow, show, |this| this.show_all() );
	export!(Void, GuiWindow, destroy, |this| this.destroy() );
	connect_gtk_property!(GuiWindow, title: Str, get_title, set_title);
	connect_gtk_container!(GuiWindow);
	connect_gtk_widget!(GuiWindow);


	// Repetitive container-adding methods
	let container_parents = vec![window.clone(), boxt.clone()];
	let container_children = vec![
		boxt.clone(), button.clone(), checkbutton.clone(), entry.clone(),
		label.clone(), togglebutton.clone()
	];
	for parent in &container_parents {
		for child in &container_children {
			symtab.add_builtin_method(
				true, &parent, id!(add_child), &void_(), &[(child.clone(), id!(child))],
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
	symtab.add_builtin_method(
		false, &wrap_type, id!(wrap), &wrap_type, &[(target_type.clone(), id!(v))],
		move |_, _, args| args[0].clone()
	)?;
	symtab.add_builtin_method(
		true, &wrap_type, id!(unwrap), &target_type, &[],
		move |_, _, args| args[0].clone()
	)?;
	Ok(())
}

pub fn inject_enum_type(symtab: &mut SymbolTable, typ: Type, has_fields: bool) -> Result<(), SymTabError> {
	symtab.add_builtin_method(
		true, &typ, id!(discriminant), &symtab.int_type.clone(), &[],
		move |_, _, args| { Value::Int(args[0].unchecked_enum_index().try_into().unwrap()) }
	)?;
	if !has_fields {
		symtab.add_binary_bool(typ.clone(), id!("op#=="), move |_, _, args| Value::Bool(args[0].unchecked_enum_index() == args[1].unchecked_enum_index()))?;
		symtab.add_binary_bool(typ.clone(), id!("op#!="), move |_, _, args| Value::Bool(args[0].unchecked_enum_index() != args[1].unchecked_enum_index()))?;
	}
	Ok(())
}

pub fn inject_record_type(symtab: &mut SymbolTable, typ: Type, fields: &[(TypeRef, Symbol)], rename_setters: bool) -> Result<(), SymTabError> {
	for (idx, (ftyp, fid)) in fields.iter().enumerate() {
		symtab.add_builtin_generic_method(
			true, &typ, *fid, &ftyp.to_spectype(), &[],
			move |_, _, args| args[0].borrow_obj().unwrap().unchecked_record()[idx].clone()
		)?;
		let setter_name = id!(match rename_setters {
			true =>  format!("_set_{}", fid.to_string()),
			false => fid.to_string() + "="
		});
		symtab.add_builtin_generic_method(
			true, &typ, setter_name, &SpecType::Type(symtab.void_type.clone(), vec![]), &[(ftyp.to_spectype(), id!(v))],
			move |_, _, args| { args[0].borrow_obj_mut().unwrap().unchecked_record_mut()[idx] = args[1].clone(); Value::Void }
		)?;
	}

	// TODO: only create 'default' for records that are all default types?
	//   (although, this might cause issues as default methods can be defined later...)
	let typ_ = typ.clone();
	symtab.add_builtin_method(
		false, &typ, id!(default), &typ, &[],
		move |symtab, _, _args| {
			let tbody = typ_.borrow();
			let fields = tbody.unchecked_record_fields();
			let mut values = Vec::with_capacity(fields.len());
			for (ftyp, _) in fields {
				values.push(call_func(symtab, &ftyp.0.name, &ftyp.1, id!(default), &[], &[], false).unwrap());
			}

			Obj::Record(values).to_heap()
		}
	)?;

	let spec_fields: Vec<(SpecType, Symbol)> = fields.iter().map(|(tr, s)| (tr.to_spectype(), *s)).collect();
	symtab.add_builtin_generic_method(
		false, &typ, id!(build), &SpecType::Type(typ.clone(), vec![]), &spec_fields,
		move |_, _, args| Obj::Record(args.to_vec()).to_heap()
	)?;

	Ok(())
}
