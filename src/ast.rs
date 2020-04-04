use std::str::FromStr;
use std::rc::Rc;
use std::ops::Deref;
use std::cell::{Ref, RefMut, RefCell};
use std::collections::HashMap;
use std::fmt;
use symbol::Symbol;
use crate::data::Value;
pub type ParseResult<T> = Result<T, <T as FromStr>::Err>;

#[macro_export]
macro_rules! id {
	($id:ident) => { stringify!($id).into() };
	($id:expr) => { $id.into() };
}

#[macro_export]
macro_rules! qid {
	($($id:tt):*) => {
		vec![ $( id!($id) ),* ]
	};
}

#[macro_export]
macro_rules! qid_slice {
	($($id:tt):*) => {
		&[ $( id!($id) ),* ]
	};
}

#[macro_export]
macro_rules! qid_combine {
	($qid:expr, $id:expr) => {
		{
			let qid: &QualID = $qid;
			let mut new_qid: QualID = Vec::with_capacity(qid.len() + 1);
			for n in qid { new_qid.push(*n) }
			new_qid.push($id);
			new_qid
		}
	};
}

pub type QualID = Vec<Symbol>;

lazy_static! {
	pub static ref DUMMY_ARG: Symbol = id!("_DUMMY");
}

// High Level Expressions:
// This maps closely to the Causson source code
#[derive(Debug, Clone, PartialEq)]
pub enum HLExpr {
	ID(Symbol),
	Specialise(Box<HLExpr>, Vec<HLTypeRef>),
	NamespaceAccess(Box<HLExpr>, Symbol),
	Binary(Box<HLExpr>, Symbol, Box<HLExpr>),
	PropAccess(Box<HLExpr>, Symbol),
	Call(Box<HLExpr>, Vec<HLExpr>),
	If(Box<HLExpr>, Box<HLExpr>, Option<Box<HLExpr>>),
	While(Box<HLExpr>, Box<HLExpr>),
	Match(Box<HLExpr>, Vec<(Symbol, Vec<Symbol>, HLExpr)>),
	Let(Symbol, Box<HLExpr>),
	CodeBlock(Vec<HLExpr>),
	Int(ParseResult<i64>),
	Real(ParseResult<f64>),
	Bool(bool),
	Str(String)
} 

#[derive(Debug, PartialEq, Clone)]
pub struct HLTypeRef(pub QualID, pub Vec<HLTypeRef>);

impl HLTypeRef {
	pub fn to_hl_expr(&self) -> HLExpr {
		let qid: &QualID = &self.0;
		let mut e = HLExpr::ID(qid[0]);
		for sym in &qid[1..] {
			e = HLExpr::NamespaceAccess(Box::new(e), *sym);
		}

		match self.1.is_empty() {
			true  => e,
			false => HLExpr::Specialise(Box::new(e), self.1.clone())
		}
	}
}

// A definition for a new type
#[derive(Debug, PartialEq)]
pub enum HLTypeDef {
	Enum(Vec<(Symbol, Vec<(HLTypeRef, Symbol)>)>),
	Wrap(HLTypeRef),
	Record { fields: Vec<(HLTypeRef, Symbol)>, rename_setters: bool }
}

pub type HLFuncArg = (HLTypeRef, Symbol);

#[derive(Debug, PartialEq)]
pub enum FuncType {
	Function,
	Method
}

#[derive(Debug, PartialEq)]
pub struct HLCompInstance {
	pub name: Option<Symbol>,
	pub what: HLTypeRef,
	pub new_args: Vec<HLExpr>,
	pub children: Vec<HLCompSubDef>
}

#[derive(Debug, PartialEq)]
pub enum HLCompSubDef {
	Instance(HLCompInstance),
	PropertySet(Symbol, HLExpr),
	EventConnection(Symbol, HLExpr),
	TransientAdd(HLExpr),
	Method(Symbol, Vec<HLFuncArg>, HLTypeRef, HLExpr)
}

#[derive(Debug, PartialEq)]
pub enum GlobalDef {
	Type(QualID, HLTypeDef),
	Func(QualID, FuncType, Vec<HLFuncArg>, HLTypeRef, HLExpr),
	Component(QualID, Vec<HLCompSubDef>)
}

pub type Program = Vec<GlobalDef>;



// Typing
// TODO: Move this elsewhere?
// TODO: Rename to BuiltinType or even remove?
#[derive(Debug, PartialEq, Eq)]
pub enum PrimitiveType {
	Any, Void, Bool, Int, Real, Str, List,
	GuiBox, GuiButton, GuiCheckButton, GuiComboBoxText, GuiContainer, GuiEntry,
	GuiLabel, GuiNotebook, GuiToggleButton, GuiWidget, GuiWindow,
	IoFile,
	Notifier
}


#[derive(Debug, Clone)]
pub struct Type(Rc<TypeData>);

impl Deref for Type {
	type Target = TypeData;
	fn deref(&self) -> &Self::Target { &self.0 }
}
impl PartialEq for Type {
	fn eq(&self, other: &Type) -> bool {
		match (self.is_any(), other.is_any()) {
			(true, _) => true,
			(_, true) => true,
			(_, _)    => std::rc::Rc::ptr_eq(&self.0, &other.0)
		}
	}
}
impl Type {
	pub fn borrow(&self) -> Ref<TypeBody> { self.0.body.borrow() }
	pub fn borrow_mut(&mut self) -> RefMut<TypeBody> { self.0.body.borrow_mut() }

	pub fn from_primitive(name: QualID, ptyp: PrimitiveType) -> Type {
		Type::from_body(name, TypeBody::Primitive(ptyp))
	}

	pub fn from_body(name: QualID, body: TypeBody) -> Type {
		Type(Rc::new(TypeData { name, body: RefCell::new(body) }))
	}

	pub fn is_any(&self) -> bool {
		match *self.borrow() {
			TypeBody::Primitive(PrimitiveType::Any) => true,
			_ => false
		}
	}
}

#[derive(Debug)]
pub enum TypeBody {
	Incomplete,
	Enum(Vec<(Symbol, Vec<(SpecType, Symbol)>)>),
	Primitive(PrimitiveType),
	Wrapper(TypeRef),
	Record(Vec<(TypeRef, Symbol)>)
}
#[derive(Debug)]
pub struct TypeData {
	pub name: QualID,
	body: RefCell<TypeBody>
}
impl TypeBody {
	pub fn unchecked_record_fields(&self) -> &Vec<(TypeRef, Symbol)> {
		match self {
			TypeBody::Record(fields) => fields,
			_ => panic!("Record TypeBody expected")
		}
	}
}


// Functions
#[derive(Debug, Clone)]
pub struct Function(Rc<FunctionData>);

pub enum FunctionBody {
	Incomplete(usize),
	BuiltIn(Box<dyn Fn(&Rc<RefCell<SymbolTable>>, &[TypeRef], &[Value]) -> Value>),
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
	pub arguments: Vec<(SpecType, Symbol)>,
	pub return_type: SpecType,
	body: RefCell<FunctionBody>
}

impl Deref for Function {
	type Target = FunctionData;
	fn deref(&self) -> &Self::Target { &self.0 }
}

impl Function {
	pub fn borrow(&self) -> Ref<FunctionBody> { self.0.body.borrow() }
	pub fn borrow_mut(&mut self) -> RefMut<FunctionBody> { self.0.body.borrow_mut() }

	pub fn new_builtin<F>(name: QualID, is_method: bool, return_type: SpecType, arguments: Vec<(SpecType, Symbol)>, func: F) -> Function
		where F: Fn(&Rc<RefCell<SymbolTable>>, &[TypeRef], &[Value]) -> Value + 'static
	{
		Function(Rc::new(FunctionData {
			name, is_method, arguments, return_type,
			body: RefCell::new(FunctionBody::BuiltIn(Box::new(func)))
		}))
	}

	pub fn new_incomplete(name: QualID, is_method: bool, return_type: SpecType, arguments: Vec<(SpecType, Symbol)>, id: usize) -> Function {
		Function(Rc::new(FunctionData {
			name, is_method, arguments, return_type,
			body: RefCell::new(FunctionBody::Incomplete(id))
		}))
	}

	#[allow(dead_code)]
	pub fn new_expr(name: QualID, is_method: bool, return_type: SpecType, arguments: Vec<(SpecType, Symbol)>, expr: Expr) -> Function {
		Function(Rc::new(FunctionData {
			name, is_method, arguments, return_type,
			body: RefCell::new(FunctionBody::Expr(expr))
		}))
	}

	pub fn matches_types(&self, specials: &[TypeRef], types: &[TypeRef]) -> bool {
		(self.0.arguments.len() == types.len()) &&
		types.iter().zip(self.0.arguments.iter()).all(
			|(check, (arg, _))| arg.matches(check, specials)
		)
	}

	pub fn matches_arg_types(&self, args: &[(SpecType, Symbol)]) -> bool {
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
	GlobalGet(HLTypeRef, Symbol),
	GlobalGetResolved(TypeRef, Symbol),
	FunctionCall(HLTypeRef, Symbol, Vec<P>),
	FunctionCallResolved(Function, Vec<TypeRef>, Vec<P>),
	MethodCall(Box<P>, Symbol, Vec<P>),
	MethodCallResolved(Box<P>, Symbol, Vec<TypeRef>, Vec<P>),
	If(Box<P>, Box<P>, Option<Box<P>>),
	While(Box<P>, Box<P>),
	Match(Box<P>, Vec<(Symbol, Vec<Symbol>, P)>),
	MatchResolved(Box<P>, Vec<Option<P>>, Option<Box<P>>),
	Let(Symbol, Box<P>),
	CodeBlock(Vec<P>),
	Int(ParseResult<i64>),
	Real(ParseResult<f64>),
	Bool(bool),
	Str(String)
}

#[derive(Debug, Clone)]
pub struct UncheckedExpr(pub ExprKind<UncheckedExpr>);

#[derive(Debug, Clone)]
pub struct Expr {
	pub expr: ExprKind<Expr>,
	pub typ: TypeRef
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeRef(pub Type, pub Vec<TypeRef>);

impl TypeRef {
	pub fn to_spectype(&self) -> SpecType {
		SpecType::Type(self.0.clone(), self.1.iter().map(TypeRef::to_spectype).collect::<Vec<SpecType>>())
	}
}

#[derive(Debug, Clone, PartialEq)]
pub enum SpecType {
	Type(Type, Vec<SpecType>),
	Placeholder(usize)
}

impl SpecType {
	pub fn fill_gap(&self, specials: &[TypeRef]) -> TypeRef {
		match self {
			SpecType::Type(t, params) => {
				let params = params.iter().map(|p| p.fill_gap(specials)).collect::<Vec<TypeRef>>();
				TypeRef(t.clone(), params)
			}
			SpecType::Placeholder(i) => specials[*i].clone()
		}
	}

	pub fn matches(&self, typ: &TypeRef, specials: &[TypeRef]) -> bool {
		match self {
			SpecType::Type(t, params) => {
				(t == &typ.0) && (params.len() == typ.1.len()) &&
				params.iter().zip(&typ.1).all(|(spec, field)| spec.matches(field, specials))
			}
			SpecType::Placeholder(i) => &specials[*i] == typ
		}
	}
}



// Symbol Tables
pub enum SymTabNode {
	Namespace { children: HashMap<Symbol, SymTabNode> },
	Type { typ: Type, children: HashMap<Symbol, SymTabNode> },
	Function { variants: Vec<Function> },
	Constant { typ: SpecType, value: Value }
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
	pub fn new_constant(typ: SpecType, value: Value) -> SymTabNode {
		SymTabNode::Constant { typ, value }
	}

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

	pub fn get_constant(&self) -> Option<(SpecType, Value)> {
		match self {
			SymTabNode::Constant { typ, value, .. } => Some((typ.clone(), value.clone())),
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
	pub str_type: Type,
	pub any_type: Type,
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
	pub fn new_counted() -> Rc<RefCell<SymbolTable>> {
		use PrimitiveType::*;
		let mut symtab = SymbolTable {
			void_type: Type::from_primitive(qid!(void), Void),
			bool_type: Type::from_primitive(qid!(bool), Bool),
			int_type: Type::from_primitive(qid!(int), Int),
			real_type: Type::from_primitive(qid!(real), Real),
			str_type: Type::from_primitive(qid!(str), Str),
			any_type: Type::from_primitive(qid!(any), Any),
			root: SymTabNode::new_namespace()
		};

		symtab.add_type(symtab.void_type.clone()).unwrap();
		symtab.add_type(symtab.bool_type.clone()).unwrap();
		symtab.add_type(symtab.int_type.clone()).unwrap();
		symtab.add_type(symtab.real_type.clone()).unwrap();
		symtab.add_type(symtab.str_type.clone()).unwrap();
		// do not list the "any" type in the program!

		let symtab_rc = Rc::new(RefCell::new(symtab));
		crate::stdlib::inject(&symtab_rc).expect("standard library injection failed");

		symtab_rc
	}

	pub fn add_namespace(&mut self, qid: QualID) -> Result<(), SymTabError> {
		let node = SymTabNode::new_namespace();
		let (name, container) = qid.split_last().unwrap();
		let container = self.root.resolve_mut(container).ok_or(SymTabError::MissingNamespace)?;
		let hashmap = container.get_children_mut().ok_or(SymTabError::NamespaceOrTypeExpected)?;
		if hashmap.contains_key(&name) {
			Err(SymTabError::DuplicateName)
		} else {
			hashmap.insert(*name, node);
			Ok(())
		}
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
		where F: Fn(&Rc<RefCell<SymbolTable>>, &[TypeRef], &[Value]) -> Value + 'static
	{
		self.add_builtin_fn(false, qid, return_type, args, func)
	}
	pub fn add_builtin_method<F>(&mut self, has_self: bool, typ: &Type, name: Symbol, return_type: &Type, args: &[(Type, Symbol)], func: F) -> Result<(), SymTabError>
		where F: Fn(&Rc<RefCell<SymbolTable>>, &[TypeRef], &[Value]) -> Value + 'static
	{
		self.add_builtin_fn(has_self, qid_combine!(&typ.name, name), return_type, args, func)
	}
	fn add_builtin_fn<F>(&mut self, is_method: bool, qid: QualID, return_type: &Type, args: &[(Type, Symbol)], func: F) -> Result<(), SymTabError>
		where F: Fn(&Rc<RefCell<SymbolTable>>, &[TypeRef], &[Value]) -> Value + 'static
	{
		let dummy: Symbol = *DUMMY_ARG; // rustc is bad sometimes
		let cleaned_args: Vec<(SpecType, Symbol)> = args.iter().cloned().filter(|(_, s)| dummy != *s).map(|(t, s)| (SpecType::Type(t, vec![]), s)).collect();
		self.add_function(Function::new_builtin(qid, is_method, SpecType::Type(return_type.clone(), vec![]), cleaned_args, func))
	}

	#[allow(dead_code)]
	pub fn add_builtin_generic_function<F>(&mut self, qid: QualID, return_type: &SpecType, args: &[(SpecType, Symbol)], func: F) -> Result<(), SymTabError>
		where F: Fn(&Rc<RefCell<SymbolTable>>, &[TypeRef], &[Value]) -> Value + 'static
	{
		self.add_builtin_generic_fn(false, qid, return_type, args, func)
	}
	pub fn add_builtin_generic_method<F>(&mut self, has_self: bool, typ: &Type, name: Symbol, return_type: &SpecType, args: &[(SpecType, Symbol)], func: F) -> Result<(), SymTabError>
		where F: Fn(&Rc<RefCell<SymbolTable>>, &[TypeRef], &[Value]) -> Value + 'static
	{
		self.add_builtin_generic_fn(has_self, qid_combine!(&typ.name, name), return_type, args, func)
	}
	fn add_builtin_generic_fn<F>(&mut self, is_method: bool, qid: QualID, return_type: &SpecType, args: &[(SpecType, Symbol)], func: F) -> Result<(), SymTabError>
		where F: Fn(&Rc<RefCell<SymbolTable>>, &[TypeRef], &[Value]) -> Value + 'static
	{
		let dummy: Symbol = *DUMMY_ARG; // rustc is bad sometimes
		let cleaned_args: Vec<(SpecType, Symbol)> = args.iter().cloned().filter(|(_, s)| dummy != *s).collect();
		self.add_function(Function::new_builtin(qid, is_method, return_type.clone(), cleaned_args, func))
	}

	pub fn add_function(&mut self, func: Function) -> Result<(), SymTabError> {
		let func_copy = func.clone();
		let (name, container) = func.name.split_last().unwrap();
		let container = self.root.resolve_mut(container).ok_or(SymTabError::MissingNamespace)?;
		let hashmap = container.get_children_mut().ok_or(SymTabError::NamespaceOrTypeExpected)?;
		if let Some(existing) = hashmap.get_mut(&name) {
			// add to the existing function?
			let group = existing.get_function_variants().ok_or(SymTabError::DuplicateName)?;
			if group.iter().any(|c| c.matches_arg_types(&func.arguments)) {
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


