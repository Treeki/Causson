use std::cell::{Ref, RefMut};
use std::ptr::NonNull;
use crate::ast::TypeRef;
use crate::gc::*;
use crate::gtk::prelude::Cast;
use symbol::Symbol;


thread_local!(pub static MAIN_GC: GC<Obj> = GC::new());


#[derive(Debug)]
pub enum Obj {
	Str(String),
	Record(Vec<Value>),
	List(Vec<Value>),
	GuiBox { w : gtk::Box },
	GuiButton { w: gtk::Button, clicked_notifier: Value },
	GuiCheckButton { w: gtk::CheckButton, clicked_notifier: Value, toggled_notifier: Value },
	GuiComboBoxText { w: gtk::ComboBoxText, changed_notifier: Value },
	GuiContainer { w: gtk::Container },
	GuiEntry { w: gtk::Entry, changed_notifier: Value },
	GuiFrame { w: gtk::Frame },
	GuiImage { w: gtk::Image },
	GuiLabel { w: gtk::Label },
	GuiNotebook { w: gtk::Notebook, pending_labels: Vec<String> },
	GuiToggleButton { w: gtk::ToggleButton, clicked_notifier: Value, toggled_notifier: Value },
	GuiWidget { w: gtk::Widget },
	GuiWindow { w: gtk::Window, destroy_notifier: Value },
	Notifier(Vec<(Value, TypeRef, Symbol)>),
	IoFile(Option<std::fs::File>)
}

macro_rules! obj_type {
	($name:ident, $rust_ty:ty) => {
		paste::item! {
			pub fn [<unchecked_ $name:snake>](&self) -> &$rust_ty {
				match self {
					Obj::$name(o) => o,
					_ => panic!(concat!(stringify!($name), " heapobj expected"))
				}
			}
		}
	};
}
macro_rules! obj_type_mut {
	($name:ident, $rust_ty:ty) => {
		paste::item! {
			pub fn [<unchecked_ $name:snake>](&self) -> &$rust_ty {
				match self {
					Obj::$name(o) => o,
					_ => panic!(concat!(stringify!($name), " heapobj expected"))
				}
			}
			pub fn [<unchecked_ $name:snake _mut>](&mut self) -> &mut $rust_ty {
				match self {
					Obj::$name(o) => o,
					_ => panic!(concat!(stringify!($name), " heapobj expected"))
				}
			}
		}
	};
}
macro_rules! obj_type_gtk {
	($name:ident, [$($sub_name:ident),*]) => {
		paste::item! {
			pub fn [<unchecked_gui_ $name:snake>](&self) -> &gtk::$name {
				match self {
					Obj::[<Gui $name>] { w, .. } => w,
					$( Obj::[<Gui $sub_name>] { w, .. } => w.upcast_ref(), )*
					_ => panic!(concat!("Gui", stringify!($name), " heapobj expected"))
				}
			}
			pub fn [<is_gui_ $name:snake>](&self) -> bool {
				match self {
					Obj::[<Gui $name>] { .. } => true,
					$( Obj::[<Gui $sub_name>] { .. } => true, )*
					_ => false
				}
			}
		}
	};
}
macro_rules! obj_type_mut_field {
	($name:ident, $field:ident, $rust_ty:ty) => {
		paste::item! {
			pub fn [<unchecked_ $name:snake _ $field>](&self) -> &$rust_ty {
				match self {
					Obj::$name { $field, .. } => $field,
					_ => panic!(concat!(stringify!($name), " heapobj expected"))
				}
			}
			pub fn [<unchecked_ $name:snake _ $field _mut>](&mut self) -> &mut $rust_ty {
				match self {
					Obj::$name { $field, .. } => $field,
					_ => panic!(concat!(stringify!($name), " heapobj expected"))
				}
			}
		}
	};
}

impl Obj {
	pub fn to_heap(self) -> Value {
		MAIN_GC.with(|gc| {
			Value::Obj(gc.take_obj(self))
		})
	}

	obj_type!(Str, String);
	obj_type_mut!(Record, Vec<Value>);
	obj_type_mut!(List, Vec<Value>);
	obj_type_mut!(Notifier, Vec<(Value, TypeRef, Symbol)>);
	obj_type_mut!(IoFile, Option<std::fs::File>);

	obj_type_gtk!(Box, []);
	obj_type_gtk!(Button, [CheckButton, ToggleButton]);
	obj_type_gtk!(CheckButton, []);
	obj_type_gtk!(ComboBoxText, []);
	obj_type_gtk!(Container, [Box, Frame, Window]);
	obj_type_gtk!(Entry, []);
	obj_type_gtk!(Frame, []);
	obj_type_gtk!(Image, []);
	obj_type_gtk!(Label, []);
	obj_type_gtk!(Notebook, []);
	obj_type_mut_field!(GuiNotebook, pending_labels, Vec<String>);
	obj_type_gtk!(ToggleButton, [CheckButton]);
	obj_type_gtk!(Widget, [Box, Button, CheckButton, ComboBoxText, Container, Entry, Frame, Image, Label, Notebook, ToggleButton, Window]);
	obj_type_gtk!(Window, []);
}


#[derive(Debug, PartialEq, Clone)]
pub enum Value {
	Void,
	Bool(bool),
	Int(i64),
	Real(f64),
	Enum(usize, Vec<Value>),
	Obj(NonNull<GCNode<Obj>>)
}

impl Value {
	pub fn unchecked_bool(&self) -> bool {
		match self {
			Value::Bool(v) => *v,
			_ => panic!("Bool value expected")
		}
	}
	pub fn unchecked_int(&self) -> i64 {
		match self {
			Value::Int(v) => *v,
			_ => panic!("Int value expected")
		}
	}
	pub fn unchecked_real(&self) -> f64 {
		match self {
			Value::Real(v) => *v,
			_ => panic!("Real value expected")
		}
	}
	pub fn unchecked_enum_index(&self) -> usize {
		match self {
			Value::Enum(idx, _) => *idx,
			_ => panic!("Enum value expected")
		}
	}
	pub fn unchecked_enum_args(&self) -> &Vec<Value> {
		match self {
			Value::Enum(_, args) => args,
			_ => panic!("Enum value expected")
		}
	}

	pub fn borrow_obj(&self) -> Option<Ref<Obj>> {
		match self {
			Value::Obj(hmd) => {
				unsafe {
					let r = &*hmd.as_ptr();
					Some(r.borrow())
				}
			}
			_ => None
		}
	}

	#[allow(dead_code)]
	pub fn borrow_obj_mut(&self) -> Option<RefMut<Obj>> {
		match self {
			Value::Obj(hmd) => {
				unsafe {
					let r = &*hmd.as_ptr();
					Some(r.borrow_mut())
				}
			}
			_ => None
		}
	}
}

