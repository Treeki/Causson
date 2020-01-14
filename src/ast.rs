use std::str::FromStr;
use symbol::Symbol;
pub type ParseResult<T> = Result<T, <T as FromStr>::Err>;

pub type QualID = Vec<Symbol>;

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

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
	LocalGet(Symbol),
	LocalSet(Symbol, Box<Expr>),
	GlobalGet(QualID),
	FunctionCall(QualID, Vec<Expr>),
	MethodCall(Box<Expr>, Symbol, Vec<Expr>),
	If(Box<Expr>, Box<Expr>, Option<Box<Expr>>),
	Let(Symbol, Box<Expr>),
	CodeBlock(Vec<Expr>),
	Int(ParseResult<i64>),
	Real(ParseResult<f64>),
	Bool(bool)
}

// A definition for a new type
#[derive(Debug, PartialEq)]
pub enum TypeDef {
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
	Type(QualID, TypeDef),
	Func(QualID, FuncType, Vec<FuncArg>, QualID, HLExpr)
}

pub type Program = Vec<GlobalDef>;
