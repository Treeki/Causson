use std::str::FromStr;
use std::rc::Rc;
use std::ops::Deref;
use std::cell::{Ref, RefMut, RefCell};
use std::collections::HashMap;
use std::fmt;
use symbol::Symbol;
pub type ParseResult<T> = Result<T, <T as FromStr>::Err>;

pub type QualID = Vec<Symbol>;

// High Level Expressions:
// This maps closely to the Causson source code
#[derive(Debug, Clone, PartialEq)]
pub enum HLExpr {
	ID(QualID),
	Binary(Box<HLExpr>, Symbol, Box<HLExpr>),
	PropAccess(Box<HLExpr>, Symbol),
	Call(Box<HLExpr>, Vec<HLExpr>),
	If(Box<HLExpr>, Box<HLExpr>, Option<Box<HLExpr>>),
	Let(Symbol, Box<HLExpr>),
	CodeBlock(Vec<HLExpr>),
	Int(ParseResult<i64>),
	Real(ParseResult<f64>),
	Bool(bool)
}

// A definition for a new type
#[derive(Debug, PartialEq)]
pub enum HLTypeDef {
	Enum(Vec<Symbol>),
	Wrap(QualID)
}

pub type FuncArg = (QualID, Symbol);

#[derive(Debug, PartialEq)]
pub enum FuncType {
	Function,
	Method
}

#[derive(Debug, PartialEq)]
pub enum GlobalDef {
	Type(QualID, HLTypeDef),
	Func(QualID, FuncType, Vec<FuncArg>, QualID, HLExpr)
}

pub type Program = Vec<GlobalDef>;



// Typing
// TODO: Move this elsewhere?
#[derive(Debug, PartialEq, Eq)]
pub enum PrimitiveType {
	Void, Bool, Int, Real
}


#[derive(Debug, Clone)]
pub struct Type(Rc<TypeData>);

impl Deref for Type {
	type Target = TypeData;
	fn deref(&self) -> &Self::Target { &self.0 }
}
impl PartialEq for Type {
	fn eq(&self, other: &Type) -> bool {
		std::rc::Rc::ptr_eq(&self.0, &other.0)
	}
}
impl Type {
	pub fn borrow(&self) -> Ref<TypeBody> { self.0.body.borrow() }
	pub fn borrow_mut(&mut self) -> RefMut<TypeBody> { self.0.body.borrow_mut() }

	pub fn from_primitive(name: &str, ptyp: PrimitiveType) -> Type {
		Type::from_body(vec![name.into()], TypeBody::Primitive(ptyp))
	}

	pub fn from_body(name: QualID, body: TypeBody) -> Type {
		Type(Rc::new(TypeData { name, body: RefCell::new(body) }))
	}
}

#[derive(Debug)]
pub enum TypeBody {
	Incomplete,
	Enum,
	Primitive(PrimitiveType),
	Wrapper(Type)
}
#[derive(Debug)]
pub struct TypeData {
	pub name: QualID,
	body: RefCell<TypeBody>
}


// Functions
#[derive(Debug, Clone)]
pub struct Function(Rc<FunctionData>);

pub enum FunctionBody {
	Incomplete(usize),
	BuiltIn(Box<dyn Fn(&[Value]) -> Value>),
	Expr(Expr)
}
impl fmt::Debug for FunctionBody {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			FunctionBody::Incomplete(id) => write!(f, "Incomplete({:})", id),
			FunctionBody::BuiltIn(_) => write!(f, "BuiltIn(...)"),
			FunctionBody::Expr(expr) => write!(f, "Expr({:?})", expr)
		}
	}
}

#[derive(Debug)]
pub struct FunctionData {
	pub name: QualID,
	pub is_method: bool,
	pub arguments: Vec<(Type, Symbol)>,
	pub return_type: Type,
	body: RefCell<FunctionBody>
}

impl Deref for Function {
	type Target = FunctionData;
	fn deref(&self) -> &Self::Target { &self.0 }
}

impl Function {
	pub fn borrow(&self) -> Ref<FunctionBody> { self.0.body.borrow() }
	pub fn borrow_mut(&mut self) -> RefMut<FunctionBody> { self.0.body.borrow_mut() }

	pub fn new_builtin<F>(name: QualID, is_method: bool, return_type: Type, arguments: Vec<(Type, Symbol)>, func: F) -> Function
		where F: Fn(&[Value]) -> Value + 'static
	{
		Function(Rc::new(FunctionData {
			name, is_method, arguments, return_type,
			body: RefCell::new(FunctionBody::BuiltIn(Box::new(func)))
		}))
	}

	pub fn new_incomplete(name: QualID, is_method: bool, return_type: Type, arguments: Vec<(Type, Symbol)>, id: usize) -> Function {
		Function(Rc::new(FunctionData {
			name, is_method, arguments, return_type,
			body: RefCell::new(FunctionBody::Incomplete(id))
		}))
	}

	pub fn new_expr(name: QualID, is_method: bool, return_type: Type, arguments: Vec<(Type, Symbol)>, expr: Expr) -> Function {
		Function(Rc::new(FunctionData {
			name, is_method, arguments, return_type,
			body: RefCell::new(FunctionBody::Expr(expr))
		}))
	}

	pub fn matches_types(&self, types: &[Type]) -> bool {
		(self.0.arguments.len() == types.len()) &&
		types.iter().zip(self.0.arguments.iter()).all(|(check, (arg, _))| check == arg)
	}

	pub fn matches_arguments(&self, args: &[(Type, Symbol)]) -> bool {
		(self.0.arguments.len() == args.len()) &&
		args.iter().zip(self.0.arguments.iter()).all(|((check, _), (arg, _))| check == arg)
	}

	pub fn is_incomplete(&self, id: usize) -> bool {
		if let FunctionBody::Incomplete(i) = *self.body.borrow() {
			if i == id {
				return true;
			}
		}
		false
	}
}



// Low Level Expressions:
// These are generated when desugaring and type-checking the high-level
// expressions
#[derive(Debug, Clone)]
pub enum ExprKind<P: Clone> {
	LocalGet(Symbol),
	LocalSet(Symbol, Box<P>),
	LocalGetResolved(usize),
	LocalSetResolved(usize, Box<P>),
	GlobalGet(QualID),
	FunctionCall(QualID, Vec<P>),
	FunctionCallResolved(Function, Vec<P>),
	MethodCall(Box<P>, Symbol, Vec<P>),
	If(Box<P>, Box<P>, Option<Box<P>>),
	Let(Symbol, Box<P>),
	CodeBlock(Vec<P>),
	Int(ParseResult<i64>),
	Real(ParseResult<f64>),
	Bool(bool)
}

#[derive(Debug, Clone)]
pub struct UncheckedExpr(pub ExprKind<UncheckedExpr>);

#[derive(Debug, Clone)]
pub struct Expr {
	pub expr: ExprKind<Expr>,
	pub typ: Type
}



// Symbol Tables
pub enum SymTabNode {
	Namespace { children: HashMap<Symbol, SymTabNode> },
	Type { typ: Type, children: HashMap<Symbol, SymTabNode> },
	Function { variants: Vec<Function> },
	SymbolConstant(Symbol)
}

impl SymTabNode {
	pub fn new_namespace() -> SymTabNode {
		SymTabNode::Namespace { children: HashMap::new() }
	}
	pub fn new_type(typ: Type) -> SymTabNode {
		SymTabNode::Type { typ, children: HashMap::new() }
	}
	pub fn new_function() -> SymTabNode {
		SymTabNode::Function { variants: vec![] }
	}
	pub fn new_symbol_constant(sym: Symbol) -> SymTabNode {
		SymTabNode::SymbolConstant(sym)
	}

	// pub fn has_children(&self) -> bool {
	// 	match self {
	// 		SymTabNode::Namespace { .. }  => true,
	// 		SymTabNode::Type      { .. }  => true,
	// 		SymTabNode::Function  { .. }  => false,
	// 		SymTabNode::SymbolConstant(_) => false
	// 	}
	// }

	pub fn get_children(&self) -> Option<&HashMap<Symbol, SymTabNode>> {
		match self {
			SymTabNode::Namespace { children, .. }  => Some(children),
			SymTabNode::Type      { children, .. }  => Some(children),
			_ => None
		}
	}

	pub fn get_children_mut(&mut self) -> Option<&mut HashMap<Symbol, SymTabNode>> {
		match self {
			SymTabNode::Namespace { children, .. }  => Some(children),
			SymTabNode::Type      { children, .. }  => Some(children),
			_ => None
		}
	}

	pub fn get_type(&self) -> Option<Type> {
		match self {
			SymTabNode::Type { typ, .. } => Some(typ.clone()),
			_ => None
		}
	}

	pub fn get_symbol_constant(&self) -> Option<Symbol> {
		match self {
			SymTabNode::SymbolConstant(sym) => Some(*sym),
			_ => None
		}
	}

	pub fn get_function_variants(&self) -> Option<&Vec<Function>> {
		match self {
			SymTabNode::Function { variants, .. } => Some(variants),
			_ => None
		}
	}

	pub fn get_function_variants_mut(&mut self) -> Option<&mut Vec<Function>> {
		match self {
			SymTabNode::Function { variants, .. } => Some(variants),
			_ => None
		}
	}

	pub fn resolve(&self, name: &[Symbol]) -> Option<&SymTabNode> {
		match (name.split_first(), self.get_children()) {
			(None, _)                     => Some(self),
			(Some(_),            None)    => None,
			(Some((name, &[])),  Some(c)) => c.get(name),
			(Some((name, next)), Some(c)) => c.get(name)?.resolve(next),
		}
	}

	pub fn resolve_mut(&mut self, name: &[Symbol]) -> Option<&mut SymTabNode> {
		if name.is_empty() {
			// this would be in the first match arm, but then the borrow
			// checker gets upset as we're mutably borrowing self twice
			return Some(self);
		}
		match (name.split_first(), self.get_children_mut()) {
			(None, _)                     => unreachable!(),
			(Some(_),            None)    => None,
			(Some((name, &[])),  Some(c)) => c.get_mut(name),
			(Some((name, next)), Some(c)) => c.get_mut(name)?.resolve_mut(next),
		}
	}
}

pub struct SymbolTable {
	pub void_type: Type,
	pub bool_type: Type,
	pub int_type: Type,
	pub real_type: Type,
	pub root: SymTabNode
}

#[derive(Debug, PartialEq)]
pub enum SymTabError {
	MissingNamespace,
	NamespaceOrTypeExpected,
	DuplicateName,
	DuplicateOverload
}

impl SymbolTable {
	pub fn new() -> SymbolTable {
		use PrimitiveType::*;
		let mut symtab = SymbolTable {
			void_type: Type::from_primitive("void", Void),
			bool_type: Type::from_primitive("bool", Bool),
			int_type: Type::from_primitive("int", Int),
			real_type: Type::from_primitive("real", Real),
			root: SymTabNode::new_namespace()
		};

		symtab.add_type(symtab.void_type.clone()).unwrap();
		symtab.add_type(symtab.bool_type.clone()).unwrap();
		symtab.add_type(symtab.int_type.clone()).unwrap();
		symtab.add_type(symtab.real_type.clone()).unwrap();

		symtab.add_builtin_method(
			vec!["real".into(), "op#+".into()], &symtab.real_type.clone(), &[(symtab.real_type.clone(), "v".into())],
			move |args| Value::Real(args[0].unchecked_real() + args[1].unchecked_real())
		).unwrap();

		symtab.add_builtin_function(
			vec!["test_builtin_function".into()], &symtab.int_type.clone(), &[],
			move |_| Value::Int(100)
		).unwrap();

		symtab
	}

	pub fn add_type(&mut self, typ: Type) -> Result<(), SymTabError> {
		let node = SymTabNode::new_type(typ.clone());
		let (name, container) = typ.name.split_last().unwrap();
		let container = self.root.resolve_mut(container).ok_or(SymTabError::MissingNamespace)?;
		let hashmap = container.get_children_mut().ok_or(SymTabError::NamespaceOrTypeExpected)?;
		if hashmap.contains_key(&name) {
			Err(SymTabError::DuplicateName)
		} else {
			hashmap.insert(*name, node);
			Ok(())
		}
	}

	pub fn add_builtin_function<F>(&mut self, qid: QualID, return_type: &Type, args: &[(Type, Symbol)], func: F) -> Result<(), SymTabError>
		where F: Fn(&[Value]) -> Value + 'static
	{
		self.add_builtin_fn(false, qid, return_type, args, func)
	}
	pub fn add_builtin_method<F>(&mut self, qid: QualID, return_type: &Type, args: &[(Type, Symbol)], func: F) -> Result<(), SymTabError>
		where F: Fn(&[Value]) -> Value + 'static
	{
		self.add_builtin_fn(true, qid, return_type, args, func)
	}
	fn add_builtin_fn<F>(&mut self, is_method: bool, qid: QualID, return_type: &Type, args: &[(Type, Symbol)], func: F) -> Result<(), SymTabError>
		where F: Fn(&[Value]) -> Value + 'static
	{
		self.add_function(Function::new_builtin(qid, is_method, return_type.clone(), args.to_vec(), func))
	}

	pub fn add_function(&mut self, func: Function) -> Result<(), SymTabError> {
		let func_copy = func.clone();
		let (name, container) = func.name.split_last().unwrap();
		let container = self.root.resolve_mut(container).ok_or(SymTabError::MissingNamespace)?;
		let hashmap = container.get_children_mut().ok_or(SymTabError::NamespaceOrTypeExpected)?;
		if let Some(existing) = hashmap.get_mut(&name) {
			// add to the existing function?
			let group = existing.get_function_variants().ok_or(SymTabError::DuplicateName)?;
			if group.iter().any(|c| c.matches_arguments(&func.arguments)) {
				Err(SymTabError::DuplicateOverload)
			} else {
				existing.get_function_variants_mut().unwrap().push(func_copy);
				Ok(())
			}
		} else {
			let mut node = SymTabNode::new_function();
			node.get_function_variants_mut().unwrap().push(func_copy);
			hashmap.insert(*name, node);
			Ok(())
		}
	}
}



// Execution Data
#[derive(Debug, PartialEq, Clone)]
pub enum Value {
	Void,
	Bool(bool),
	Int(i64),
	Real(f64),
	Enum(Symbol)
}

impl Value {
	pub fn unchecked_real(&self) -> f64 {
		match self {
			Value::Real(v) => *v,
			_ => panic!("Real value expected")
		}
	}
}

