use std::cell::{Cell, RefCell, Ref, RefMut};
use std::fmt;
use std::ptr::NonNull;

pub struct GC<T> {
	head: Cell<Option<NonNull<GCNode<T>>>>
}

impl<T> GC<T> where T: fmt::Debug {
	pub fn new() -> GC<T> {
		GC { head: Cell::new(None) }
	}

	pub fn take_obj(&self, obj: T) -> NonNull<GCNode<T>> {
		unsafe {
			let node = GCNode {
				obj: RefCell::new(obj),
				marked: Cell::new(false),
				next: Cell::new(self.head.get())
			};
			let node_ptr = NonNull::new_unchecked(Box::into_raw(Box::new(node)));
			self.head.set(Some(node_ptr));
			node_ptr
		}
	}

	#[allow(dead_code)]
	pub fn sweep(&self) {
		unsafe {
			let mut node_ref = &self.head;
			while node_ref.get().is_some() {
				let node_ptr = node_ref.get().unwrap().as_ptr();
				let node = &*node_ptr;
				if node.marked.get() {
					// move onto next node
					node.marked.set(false);
					node_ref = &node.next;
				} else {
					// unlink this node
					node_ref.set(node.next.take());
					Box::from_raw(node_ptr);
				}
			}
		}
	}

	#[allow(dead_code)]
	pub fn each_node<F>(&self, mut f: F)
		where F: FnMut(&GCNode<T>)
	{
		unsafe {
			let mut iter = self.head.get();
			while iter.is_some() {
				let node = &*iter.unwrap().as_ptr();
				f(node);
				iter = node.next.get();
			}
		}
	}

	#[allow(dead_code)]
	pub fn node_count(&self) -> usize {
		let mut count = 0;
		self.each_node(|_| count += 1);
		count
	}
}

impl<T> GC<T> where T: fmt::Debug {
	#[allow(dead_code)]
	pub fn dump(&self) {
		let mut index = 0;
		self.each_node(|node| {
			println!("obj{}: {:?}", index, node);
			index += 1;
		});
	}
}



#[allow(dead_code)]
pub struct GCNode<T> {
	obj: RefCell<T>,
	marked: Cell<bool>,
	next: Cell<Option<NonNull<GCNode<T>>>>
}
impl<T> fmt::Debug for GCNode<T> where T: fmt::Debug {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "{:?}", self.obj.borrow())
	}
}
impl<T> GCNode<T> {
	pub fn borrow(&self) -> Ref<T> {
		self.obj.borrow()
	}
	pub fn borrow_mut(&self) -> RefMut<T> {
		self.obj.borrow_mut()
	}
}
