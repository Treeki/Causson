use crate::ast::*;
use crate::data::*;
use crate::eval::*;
use symbol::Symbol;
use std::convert::TryInto;
use std::fs::OpenOptions;
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

	symtab.add_namespace(qid![io])?;
	symtab.add_namespace(qid![gui])?;

	macro_rules! map_primitive {
		(io : $name:ident) => {
			paste::expr! {
				{
					let t = Type::from_body(qid!(io:$name), TypeBody::Primitive(PrimitiveType::[<Io $name>]));
					symtab.add_type(t.clone())?;
					t
				}
			}
		};
		(gui : $name:ident) => {
			paste::expr! {
				{
					let t = Type::from_body(qid!(gui:$name), TypeBody::Primitive(PrimitiveType::[<Gui $name>]));
					symtab.add_type(t.clone())?;
					t
				}
			}
		};
		($name:ident) => {
			paste::expr! {
				{
					let t = Type::from_body(qid!($name), TypeBody::Primitive(PrimitiveType::$name));
					symtab.add_type(t.clone())?;
					t
				}
			}
		};
	}

	let list_t = map_primitive!(List);
	let notifier_t = map_primitive!(Notifier);

	let box_t = map_primitive!(gui:Box);
	let button_t = map_primitive!(gui:Button);
	let check_button_t = map_primitive!(gui:CheckButton);
	let combo_box_text_t = map_primitive!(gui:ComboBoxText);
	let container_t = map_primitive!(gui:Container);
	let entry_t = map_primitive!(gui:Entry);
	let label_t = map_primitive!(gui:Label);
	let notebook_t = map_primitive!(gui:Notebook);
	let toggle_button_t = map_primitive!(gui:ToggleButton);
	let widget_t = map_primitive!(gui:Widget);
	let window_t = map_primitive!(gui:Window);

	let file_t = map_primitive!(io:File);

	// It would have been nice to use resolve_spec_type! here, but
	// we can't use it while building types...
	macro_rules! build_enum_choice {
		($choice_id:expr, $node:ident, $my_type:ident, $my_spec:ident, $key:ident, []) => {
			$node.insert(id!($key), SymTabNode::new_constant($my_spec.clone(), Value::Enum($choice_id, vec![])));
		};
		($choice_id:expr, $node:ident, $my_type:ident, $my_spec:ident, $key:ident, [$( $f_id:ident : $f_ty:expr ),+]) => {
			let n = $choice_id;
			symtab.add_builtin_generic_method(
				false, &$my_type, id!($key), &$my_spec,
				&[$( ($f_ty, id!($f_id)) ),*],
				move |_, _, args| {
					Value::Enum(n, args.to_vec())
				}
			)?;
		};
	}
	macro_rules! build_enum_typespec {
		(0, $t:expr) => { SpecType::Type($t, vec![]) };
		(1, $t:expr) => { SpecType::Type($t, vec![SpecType::Placeholder(0)]) };
		(2, $t:expr) => { SpecType::Type($t, vec![SpecType::Placeholder(0), SpecType::Placeholder(1)]) };
	}
	macro_rules! build_enum {
		($( $id:ident ):*, $placeholder_count:tt, $( $key:ident($( $f_id:ident : $f_ty:expr ),*) ),+) => {
			{
				let mut n = Type::from_body(qid!($($id):*), TypeBody::Incomplete);
				*n.borrow_mut() = TypeBody::Enum(vec![
					$( (id!($key), vec![$( ($f_ty, id!($f_id)) ),*]) ),*
				]);
				symtab.add_type(n.clone())?;
				let my_spec = build_enum_typespec!($placeholder_count, n.clone());
				let node = symtab.root.resolve_mut(&n.name).unwrap().get_children_mut().unwrap();
				let mut choice_id: usize = 0;
				$(
					build_enum_choice!(choice_id, node, n, my_spec, $key, [$( $f_id : $f_ty ),*]);
					#[allow(unused_assignments)] { choice_id += 1; }
				)*
				n
			}
		};
	}

	let orientation_t = build_enum!(gui:Orientation, 0, Horizontal(), Vertical());
	let maybe_t = build_enum!(Maybe, 1, None(), Just(t: SpecType::Placeholder(0)));

	macro_rules! resolve_type {
		(IntI32) => { int_() };
		(IntU32) => { int_() };
		(IntUsize) => { int_() };
		(Int) => { int_() };
		(Real) => { real_() };
		(Bool) => { bool_() };
		(Str) => { str_() };
		(Void) => { void_() };
		(Notifier) => { notifier_t.clone() };
		(List) => { list_t.clone() };
		(ListMut) => { list_t.clone() };
		(GuiBox) => { box_t.clone() };
		(GuiButton) => { button_t.clone() };
		(GuiCheckButton) => { check_button_t.clone() };
		(GuiComboBoxText) => { combo_box_text_t.clone() };
		(GuiContainer) => { container_t.clone() };
		(GuiEntry) => { entry_t.clone() };
		(GuiLabel) => { label_t.clone() };
		(GuiNotebook) => { notebook_t.clone() };
		(GuiNotebookRaw) => { notebook_t.clone() };
		(GuiToggleButton) => { toggle_button_t.clone() };
		(GuiWidget) => { widget_t.clone() };
		(GuiWindow) => { window_t.clone() };
		(IoFile) => { file_t.clone() };
		(IoFileMut) => { file_t.clone() };
	}
	macro_rules! resolve_spec_type {
		(MaybeStr) => { SpecType::Type(maybe_t.clone(), vec![SpecType::Type(str_(), vec![])]) };
		(MaybeIntU32) => { SpecType::Type(maybe_t.clone(), vec![SpecType::Type(int_(), vec![])]) };
		(MaybeIoFile) => { SpecType::Type(maybe_t.clone(), vec![SpecType::Type(file_t.clone(), vec![])]) };
		(Maybe) => { SpecType::Type(maybe_t.clone(), vec![SpecType::Placeholder(0)]) };
		(List) => { SpecType::Type(list_t.clone(), vec![SpecType::Placeholder(0)]) };
		(ListMut) => { SpecType::Type(list_t.clone(), vec![SpecType::Placeholder(0)]) };
		(Placeholder0) => { SpecType::Placeholder(0) };
		(Placeholder1) => { SpecType::Placeholder(1) };
		($i:ident) => { SpecType::Type(resolve_type!($i), vec![]) };
	}

	macro_rules! unpack_maybe {
		($e:expr, $out:ident : $out_type:ty, |$arg:ident| $code:expr) => {
			let $out = $e;
			let ind = $out.unchecked_enum_index();
			let $out: Option<$out_type> = match ind {
				0 => None,
				1 => {
					let $arg = &$out.unchecked_enum_args()[0];
					Some($code)
				},
				_ => unreachable!("bad Maybe")
			};
		};
	}
	macro_rules! unpack_type {
		($out:ident, IntI32, $e:expr) => { let $out: i32 = $e.unchecked_int().try_into().unwrap(); };
		($out:ident, IntU32, $e:expr) => { let $out: u32 = $e.unchecked_int().try_into().unwrap(); };
		($out:ident, IntUsize, $e:expr) => { let $out: usize = $e.unchecked_int().try_into().unwrap(); };
		($out:ident, Int, $e:expr) => { let $out = $e.unchecked_int(); };
		($out:ident, Real, $e:expr) => { let $out = $e.unchecked_real(); };
		($out:ident, Bool, $e:expr) => { let $out = $e.unchecked_bool(); };
		($out:ident, Str, $e:expr) => { let $out = $e.borrow_obj().unwrap(); let $out = $out.unchecked_str(); };
		($out:ident, MaybeIntU32, $e:expr) => { unpack_maybe!($e, $out: u32, |a| a.unchecked_int().try_into().unwrap()); };
		($out:ident, MaybeStr, $e:expr) => { unpack_maybe!($e, $out: String, |a| a.borrow_obj().unwrap().unchecked_str().clone()); };
		($out:ident, List, $e:expr) => { let $out = $e.borrow_obj().unwrap(); let $out = $out.unchecked_list(); };
		($out:ident, ListMut, $e:expr) => { let mut $out = $e.borrow_obj_mut().unwrap(); let $out = $out.unchecked_list_mut(); };
		($out:ident, Notifier, $e:expr) => { let $out = $e.borrow_obj().unwrap(); let $out = $out.unchecked_notifier(); };
		($out:ident, GuiBox, $e:expr) => { let $out = $e.borrow_obj().unwrap(); let $out = $out.unchecked_gui_box(); };
		($out:ident, GuiButton, $e:expr) => { let $out = $e.borrow_obj().unwrap(); let $out = $out.unchecked_gui_button(); };
		($out:ident, GuiCheckButton, $e:expr) => { let $out = $e.borrow_obj().unwrap(); let $out = $out.unchecked_gui_check_button(); };
		($out:ident, GuiComboBoxText, $e:expr) => { let $out = $e.borrow_obj().unwrap(); let $out = $out.unchecked_gui_combo_box_text(); };
		($out:ident, GuiContainer, $e:expr) => { let $out = $e.borrow_obj().unwrap(); let $out = $out.unchecked_gui_container(); };
		($out:ident, GuiEntry, $e:expr) => { let $out = $e.borrow_obj().unwrap(); let $out = $out.unchecked_gui_entry(); };
		($out:ident, GuiLabel, $e:expr) => { let $out = $e.borrow_obj().unwrap(); let $out = $out.unchecked_gui_label(); };
		($out:ident, GuiNotebook, $e:expr) => { let $out = $e.borrow_obj().unwrap(); let $out = $out.unchecked_gui_notebook(); };
		($out:ident, GuiNotebookRaw, $e:expr) => { let $out = $e; };
		($out:ident, GuiToggleButton, $e:expr) => { let $out = $e.borrow_obj().unwrap(); let $out = $out.unchecked_gui_toggle_button(); };
		($out:ident, GuiWidget, $e:expr) => { let $out = $e.borrow_obj().unwrap(); let $out = $out.unchecked_gui_widget(); };
		($out:ident, GuiWindow, $e:expr) => { let $out = $e.borrow_obj().unwrap(); let $out = $out.unchecked_gui_window(); };
		($out:ident, Placeholder0, $e:expr) => { let $out = $e; };
		($out:ident, Placeholder1, $e:expr) => { let $out = $e; };
		($out:ident, IoFile, $e:expr) => { let $out = $e.borrow_obj().unwrap(); let $out = $out.unchecked_io_file(); };
		($out:ident, IoFileMut, $e:expr) => { let mut $out = $e.borrow_obj_mut().unwrap(); let $out = $out.unchecked_io_file_mut(); };
	}
	macro_rules! convert_arg {
		(SymbolTable, $arg:ident) => { (SpecType::Type(void_(), vec![]), id!(_DUMMY)) };
		($arg_typ:ident, $arg:ident) => { (resolve_spec_type!($arg_typ), id!($arg)) };
	}
	macro_rules! load_arg {
		($out:ident, SymbolTable, $_arg_iter:expr, $symtab:expr) => { let $out = $symtab; };
		($out:ident, $ty:ident, $arg_iter:expr, $_symtab:expr) => { unpack_type!($out, $ty, $arg_iter.next().unwrap()); };
	}
	macro_rules! pack_maybe {
		($e:expr, |$v:ident| $code:expr) => {
			match $e {
				None => Value::Enum(0, vec![]),
				Some($v) => Value::Enum(1, vec![$code])
			}
		};
	}
	macro_rules! pack_type {
		(IntI32, $e:expr) => { Value::Int($e.into()) };
		(IntU32, $e:expr) => { Value::Int($e.into()) };
		(IntUsize, $e:expr) => { Value::Int($e.try_into().unwrap()) };
		(Int, $e:expr) => { Value::Int($e) };
		(Real, $e:expr) => { Value::Real($e) };
		(Bool, $e:expr) => { Value::Bool($e) };
		(Str, $e:expr) => { Obj::Str($e).to_heap() };
		(MaybeIntU32, $e:expr) => { pack_maybe!($e, |s| Value::Int(s.into())) };
		(MaybeStr, $e:expr) => { pack_maybe!($e, |s| Obj::Str(s.to_string()).to_heap()) };
		(MaybeIoFile, $e:expr) => { pack_maybe!($e, |s| Obj::IoFile(Some(s)).to_heap()) };
		(List, $e:expr) => { Obj::List($e).to_heap() };
		(Void, $_:tt) => { Value::Void };
		(Notifier, $e:expr) => { $e.to_heap() };
		(GuiBox, $e:expr) => { $e };
		(GuiButton, $e:expr) => { $e };
		(GuiCheckButton, $e:expr) => { $e };
		(GuiComboBoxText, $e:expr) => { $e };
		(GuiEntry, $e:expr) => { $e };
		(GuiLabel, $e:expr) => { $e };
		(GuiNotebook, $e:expr) => { $e };
		(GuiToggleButton, $e:expr) => { $e };
		(GuiWindow, $e:expr) => { $e };
		(IoFile, $e:expr) => { Obj::IoFile($e).to_heap() };
		(Placeholder0, $e:expr) => { $e };
		(Placeholder1, $e:expr) => { $e };
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
				&resolve_type!($typ), id!($getter_id), &notifier_t, &[],
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
			export!(Void, $as_container_typ, add_child, |this, child: GuiWidget| {
				this.add(child);
			});
			connect_gtk_property!($as_container_typ, border_width: IntU32, get_border_width, set_border_width);
		};
	}

	macro_rules! connect_gtk_widget {
		($as_widget_typ:ident) => {
			connect_gtk_property!($as_widget_typ, sensitive: Bool, get_sensitive, set_sensitive);
			connect_gtk_property!($as_widget_typ, visible: Bool, get_visible, set_visible);
			// We cannot use export!() here as we don't want to unpack the object
			symtab.add_builtin_method(
				true, &resolve_type!($as_widget_typ), id!(root),
				&resolve_type!(GuiWidget), &[],
				move |_, _, args| args[0].clone()
			)?;
		};
	}

	macro_rules! connect_gtk_button {
		($typ:ident) => {
			export_notifier!($typ, clicked_notifier, _n_clicked);
			connect_gtk_property!($typ, label: Str, get_label, set_label);
		};
	}

	macro_rules! connect_gtk_toggle_button {
		($typ:ident) => {
			export_notifier!($typ, toggled_notifier, _n_active);
			connect_gtk_property!($typ, active: Bool, get_active, set_active);
		};
	}

	macro_rules! connect_gtk_base_class {
		($sub_typ:ident, $($base_typ:ident),+) => {
			paste::expr! { $(
				// We cannot use export!() here as we don't want to unpack the object
				symtab.add_builtin_method(
					false, &resolve_type!($base_typ), id!(from),
					&resolve_type!($base_typ),
					&[(resolve_type!($sub_typ), id!(obj))],
					move |_, _, args| args[0].clone()
				)?;
				symtab.add_builtin_generic_method(
					false, &resolve_type!($sub_typ), id!(try_from),
					&SpecType::Type(maybe_t.clone(), vec![SpecType::Type(resolve_type!($sub_typ), vec![])]),
					&[(SpecType::Type(resolve_type!($base_typ), vec![]), id!(obj))],
					move |_, _, args| {
						// We can safely go from base_typ to sub_typ if
						// the value is a sub_typ, or a subclass of that
						let obj = args[0].borrow_obj().unwrap();
						match obj.[<is_ $sub_typ:snake>]() {
							true  => Value::Enum(1, vec![args[0].clone()]), // Just(x)
							false => Value::Enum(0, vec![])                 // None
						}
					}
				)?;
			)* }
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

	export!(Void, qid!(print), || print!("\n"));
	export!(Void, qid!(print), |i: Int| print!("{}", i));
	export!(Void, qid!(print), |r: Real| print!("{}", r));
	export!(Void, qid!(print), |s: Str| print!("{}", s));

	// ****************************************
	// List
	export!(List, List, new, || vec![]);
	export_getter!(List, len: IntUsize, |this| this.len());
	export!(Void, ListMut, push, |this, v: Placeholder0| this.push(v.clone()));
	export!(Placeholder0, ListMut, pop, |this, i: IntUsize| this.remove(i));
	export!(Placeholder0, List, get, |this, i: IntUsize| this[i].clone());

	// ****************************************
	// Notifier
	// These need special access that the macros don't provide
	export!(Notifier, Notifier, new, || Obj::Notifier(vec![]));
	symtab.add_builtin_method(
		true, &notifier_t, id!(connect), &void_(), &[(any_(), id!(target)), (str_(), id!(funcname))],
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


	// ****************************************
	// Core GUI functions
	export!(Void, qid!(gui:init), || gtk::init().expect("GTK init failed"));
	export!(Void, qid!(gui:run), || gtk::main());
	export!(Void, qid!(gui:quit), || gtk::main_quit());

	// ****************************************
	// GuiBox
	symtab.add_builtin_method(
		false, &box_t, id!(new), &box_t, &[(orientation_t.clone(), id!(orientation))],
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
	connect_gtk_base_class!(GuiBox, GuiContainer, GuiWidget);

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
	connect_gtk_base_class!(GuiButton, GuiWidget);

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
	connect_gtk_toggle_button!(GuiCheckButton);
	connect_gtk_button!(GuiCheckButton);
	connect_gtk_widget!(GuiCheckButton);
	connect_gtk_base_class!(GuiCheckButton, GuiButton, GuiWidget);

	// ****************************************
	// GuiComboBoxText
	export!(GuiComboBoxText, GuiComboBoxText, new, |symtab: SymbolTable| {
		let cb = gtk::ComboBoxText::new();
		let changed_notifier = Obj::Notifier(vec![]).to_heap();
		let val = Obj::GuiComboBoxText { w: cb.clone(), changed_notifier }.to_heap();
		connect_gtk_signal!(cb, connect_changed, GuiComboBoxText, changed_notifier, val, symtab);
		val
	});
	export_notifier!(GuiComboBoxText, changed_notifier, _n_selected_index);
	export!(Void, GuiComboBoxText, add_child, |this, s: Str| this.append_text(&s) );
	export!(Void, GuiComboBoxText, insert_child, |this, pos: IntI32, s: Str| this.insert_text(pos, s) );
	export!(Void, GuiComboBoxText, remove_child, |this, i: IntI32| gtk::ComboBoxTextExt::remove(this, i) );
	export!(Void, GuiComboBoxText, remove_all, |this| this.remove_all() );
	connect_gtk_property!(GuiComboBoxText, selected_index: MaybeIntU32, get_active, set_active);
	connect_gtk_widget!(GuiComboBoxText);
	connect_gtk_base_class!(GuiComboBoxText, GuiWidget);

	// ****************************************
	// GuiContainer
	connect_gtk_container!(GuiContainer);
	connect_gtk_widget!(GuiContainer);
	connect_gtk_base_class!(GuiContainer, GuiWidget);

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
	connect_gtk_base_class!(GuiEntry, GuiWidget);

	// ****************************************
	// GuiLabel
	export!(GuiLabel, GuiLabel, new, |symtab: SymbolTable| {
		Obj::GuiLabel { w: gtk::Label::new(None) }.to_heap()
	});
	connect_gtk_property!(GuiLabel, text: Str, get_text, set_text);
	connect_gtk_widget!(GuiLabel);
	connect_gtk_base_class!(GuiLabel, GuiWidget);

	// ****************************************
	// GuiNotebook
	export!(GuiNotebook, GuiNotebook, new, |symtab: SymbolTable| {
		Obj::GuiNotebook { w: gtk::Notebook::new(), pending_labels: vec![] }.to_heap()
	});
	export!(Void, GuiNotebookRaw, add_child, |this, s: Str| {
		this.borrow_obj_mut().unwrap().unchecked_gui_notebook_pending_labels_mut().push(s.to_string());
	});
	export!(Void, GuiNotebookRaw, add_child, |this, w: GuiWidget| {
		let have_name = !this.borrow_obj().unwrap().unchecked_gui_notebook_pending_labels().is_empty();
		let name = if have_name { this.borrow_obj_mut().unwrap().unchecked_gui_notebook_pending_labels_mut().remove(0) } else { "Tab".to_string() };
		let nb = this.borrow_obj().unwrap();
		let nb = nb.unchecked_gui_notebook();
		nb.add(w);
		nb.set_tab_label_text(w, &name);
	});
	connect_gtk_widget!(GuiNotebook);
	connect_gtk_base_class!(GuiNotebook, GuiWidget);

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
	connect_gtk_toggle_button!(GuiToggleButton);
	connect_gtk_button!(GuiToggleButton);
	connect_gtk_widget!(GuiToggleButton);
	connect_gtk_base_class!(GuiToggleButton, GuiButton, GuiWidget);

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
	connect_gtk_base_class!(GuiWindow, GuiContainer, GuiWidget);



	// ****************************************
	// IoFile
	export!(MaybeIoFile, IoFile, open_read, |path: Str| {
		OpenOptions::new().read(true).open(&path).ok()
	});
	export!(MaybeIoFile, IoFile, open_write, |path: Str| {
		OpenOptions::new().write(true).create(true).open(&path).ok()
	});
	export!(MaybeIoFile, IoFile, open_append, |path: Str| {
		OpenOptions::new().append(true).create(true).open(&path).ok()
	});

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


#[cfg(test)]
mod tests {
	use super::*;
	use crate::ast_builder;
	use crate::parser;
	use crate::eval;

	fn eval_program(code: &str) -> Value {
		let parsed = ast_builder::parse_causson_code(code).expect("test code should make a high-level AST");
		let symtab_rc = parser::make_symtab_from_program(&parsed).expect("test code should make a symbol table");
		eval::call_func(&symtab_rc, &[], &[], id!(test), &[], &[], false).unwrap()
	}

	fn eval_expr(typ: &str, body: &str) -> Value {
		let code = format!("def test() -> {} {{ {} }}", typ, body);
		eval_program(&code)
	}

	#[test]
	fn test_maybe() {
		let v = eval_expr("Maybe<str>", "Maybe<str>:Just(\"hello\")");
		assert_eq!(v.unchecked_enum_index(), 1);
		let v = &v.unchecked_enum_args()[0];
		let v = v.borrow_obj().unwrap();
		assert_eq!(v.unchecked_str(), "hello");

		let v = eval_expr("Maybe<int>", "Maybe<int>:None");
		assert_eq!(v.unchecked_enum_index(), 0);
	}
}
