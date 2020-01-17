use std::cell::{Ref, RefMut};
use std::ptr::NonNull;
use symbol::Symbol;
use crate::gc::*;


thread_local!(pub static MAIN_GC: GC<Obj> = GC::new());


#[derive(Debug)]
pub enum Obj {
	Str(String)
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
}


#[derive(Debug, PartialEq, Clone)]
pub enum Value {
	Void,
	Bool(bool),
	Int(i64),
	Real(f64),
	Enum(Symbol),
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
	pub fn unchecked_enum_symbol(&self) -> Symbol {
		match self {
			Value::Enum(sym) => *sym,
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

