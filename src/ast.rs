use std::str::FromStr;
use std::rc::Rc;
use std::ops::Deref;
use std::cell::{Ref, RefMut, RefCell};
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


// Low Level Expressions:
// These are generated when desugaring and type-checking the high-level
// expressions
#[derive(Debug, Clone)]
pub enum ExprKind<P: Clone> {
	LocalGet(Symbol),
	LocalSet(Symbol, Box<P>),
	GlobalGet(QualID),
	FunctionCall(QualID, Vec<P>),
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
