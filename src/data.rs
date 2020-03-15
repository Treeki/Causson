use std::cell::{Ref, RefMut};
use std::ptr::NonNull;
use crate::gc::*;
use crate::gtk::prelude::Cast;
use symbol::Symbol;


thread_local!(pub static MAIN_GC: GC<Obj> = GC::new());


#[derive(Debug)]
pub enum Obj {
	Str(String),
	Record(Vec<Value>),
	GuiBox(gtk::Box),
	GuiButton { button: gtk::Button, clicked_notifier: Value },
	GuiEntry { entry: gtk::Entry, changed_notifier: Value },
	GuiWindow(gtk::Window),
	Notifier(Vec<(Value, Vec<Symbol>)>)
}

impl Obj {
	pub fn to_heap(self) -> Value {
		MAIN_GC.with(|gc| {
			Value::Obj(gc.take_obj(self))
		})
	}

	pub fn unchecked_str(&self) -> &String {
		match self {
			Obj::Str(s) => s,
			_ => panic!("Str heapobj expected")
		}
	}
	pub fn unchecked_record(&self) -> &Vec<Value> {
		match self {
			Obj::Record(v) => v,
			_ => panic!("Record heapobj expected")
		}
	}
	pub fn unchecked_record_mut(&mut self) -> &mut Vec<Value> {
		match self {
			Obj::Record(v) => v,
			_ => panic!("Record heapobj expected")
		}
	}
	pub fn unchecked_gtk_button(&self) -> &gtk::Button {
		match self {
			Obj::GuiButton { button, .. } => button,
			_ => panic!("GuiButton heapobj expected")
		}
	}
	pub fn unchecked_gtk_entry(&self) -> &gtk::Entry {
		match self {
			Obj::GuiEntry { entry, .. } => entry,
			_ => panic!("GuiEntry heapobj expected")
		}
	}
	pub fn unchecked_gtk_window(&self) -> &gtk::Window {
		match self {
			Obj::GuiWindow(w) => w,
			_ => panic!("GuiWindow heapobj expected")
		}
	}

	pub fn unchecked_gtk_container(&self) -> &gtk::Container {
		match self {
			Obj::GuiBox(b) => b.upcast_ref(),
			Obj::GuiWindow(w) => w.upcast_ref(),
			_ => panic!("gtk::Container heapobj expected")
		}
	}

	pub fn unchecked_gtk_box(&self) -> &gtk::Box {
		match self {
			Obj::GuiBox(b) => b,
			_ => panic!("gtk::Box heapobj expected")
		}
	}

	pub fn unchecked_gtk_widget(&self) -> &gtk::Widget {
		match self {
			Obj::GuiBox(b) => b.upcast_ref(),
			Obj::GuiButton { button, .. } => button.upcast_ref(),
			Obj::GuiEntry { entry, .. } => entry.upcast_ref(),
			Obj::GuiWindow(w) => w.upcast_ref(),
			_ => panic!("gtk::Widget heapobj expected")
		}
	}

	pub fn unchecked_notifier(&self) -> &Vec<(Value, Vec<Symbol>)> {
		match self {
			Obj::Notifier(v) => v,
			_ => panic!("Notifier heapobj expected")
		}
	}

	pub fn unchecked_notifier_mut(&mut self) -> &mut Vec<(Value, Vec<Symbol>)> {
		match self {
			Obj::Notifier(v) => v,
			_ => panic!("Notifier heapobj expected")
		}
	}
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

