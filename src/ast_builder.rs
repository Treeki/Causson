use pest::Parser;
use pest::prec_climber::*;
use pest::error::Error;
use symbol::Symbol;
use crate::ast::*;

#[derive(Parser)]
#[grammar = "causson.pest"]
struct CaussonParser;
type Pair<'a> = pest::iterators::Pair<'a, Rule>;

fn parse_id(pair: Pair) -> Symbol {
	assert_eq!(pair.as_rule(), Rule::id);
	pair.as_str().into()
}

fn parse_qualified_id(pair: Pair) -> QualID {
	assert_eq!(pair.as_rule(), Rule::qualifiedID);
	pair.into_inner().map(parse_id).collect()
}

// Expressions
lazy_static! {
	static ref PREC_CLIMBER: PrecClimber<Rule> = {
		use Rule::*;
		use Assoc::*;

		PrecClimber::new(vec![
			Operator::new(assign, Right),
			Operator::new(eq, Left) | Operator::new(ne, Left),
			Operator::new(lt, Left) | Operator::new(le, Left) | Operator::new(gt, Left) | Operator::new(ge, Left),
			Operator::new(add, Left) | Operator::new(subtract, Left),
			Operator::new(multiply, Left) | Operator::new(divide, Left)
		])
	};
}

fn parse_hlexpr(pair: Pair) -> HLExpr {
	assert_eq!(pair.as_rule(), Rule::expr);
	PREC_CLIMBER.climb(
		pair.into_inner(),
		parse_term,
		|lhs: HLExpr, op: Pair, rhs: HLExpr| {
			HLExpr::Binary(Box::new(lhs), op.as_str().into(), Box::new(rhs))
		}
	)
}

fn parse_term(pair: Pair) -> HLExpr {
	assert_eq!(pair.as_rule(), Rule::term);
	let mut pairs = pair.into_inner();
	let mut expr = parse_term_piece(pairs.next().unwrap());

	// handle the suffixes
	for suffix in pairs {
		expr = match suffix.as_rule() {
			Rule::termPropAccess => {
				let id = parse_id(suffix.into_inner().next().unwrap());
				HLExpr::PropAccess(Box::new(expr), id)
			}
			Rule::termCall => {
				let args = suffix.into_inner().map(parse_hlexpr).collect();
				HLExpr::Call(Box::new(expr), args)
			}
			_ => unreachable!()
		}
	}

	expr
}

fn parse_if_piece<'i, P>(pairs: &mut std::iter::Peekable<P>) -> HLExpr where P: std::iter::Iterator<Item = Pair<'i>> {
	match pairs.peek().unwrap().as_rule() {
		Rule::expr => {
			// this is a condition, so we are building an 'if'
			let cond = Box::new(parse_hlexpr(pairs.next().unwrap()));
			let if_true = Box::new(parse_code_block(pairs.next().unwrap()));
			let if_false = if pairs.peek().is_some() {
				Some(Box::new(parse_if_piece(pairs)))
			} else {
				None
			};
			HLExpr::If(cond, if_true, if_false)
		}
		Rule::codeBlock => {
			// this is simply a plain old 'false'
			parse_code_block(pairs.next().unwrap())
		}
		_ => unreachable!()
	}
}

fn parse_term_piece(pair: Pair) -> HLExpr {
	match pair.as_rule() {
		Rule::qualifiedID => HLExpr::ID(parse_qualified_id(pair)),
		Rule::bTrue => HLExpr::Bool(true),
		Rule::bFalse => HLExpr::Bool(false),
		Rule::real => HLExpr::Real(pair.as_str().parse()),
		Rule::int => HLExpr::Int(pair.as_str().parse()),
		Rule::ifTerm => parse_if_piece(&mut pair.into_inner().peekable()),
		Rule::letTerm => {
			let mut pairs = pair.into_inner();
			let name = parse_id(pairs.next().unwrap());
			let value = Box::new(parse_hlexpr(pairs.next().unwrap()));
			HLExpr::Let(name, value)
		}
		Rule::expr => parse_hlexpr(pair),
		_ => unreachable!()
	}
}


fn parse_code_block(pair: Pair) -> HLExpr {
	assert_eq!(pair.as_rule(), Rule::codeBlock);
	let mut vec: Vec<HLExpr> = pair.into_inner().map(parse_hlexpr).collect();
	if vec.len() == 1 { vec.remove(0) } else { HLExpr::CodeBlock(vec) }
}


// Global Definitions
fn parse_type_def(pair: Pair) -> TypeDef {
	match pair.as_rule() {
		Rule::wrapDef => TypeDef::Wrap(parse_qualified_id(pair.into_inner().next().unwrap())),
		Rule::enumDef => {
			TypeDef::Enum(pair.into_inner().map(parse_id).collect())
		},
		_ => unreachable!()
	}
}

fn parse_func_spec(pair: Pair) -> (QualID, FuncType, Vec<FuncArg>) {
	assert_eq!(pair.as_rule(), Rule::funcSpec);
	let mut pairs = pair.into_inner();
	let func_name = parse_qualified_id(pairs.next().unwrap());

	let mut func_type = FuncType::Function;
	if let Some(p) = pairs.peek() {
		if p.as_rule() == Rule::funcSelfArg {
			func_type = FuncType::Method;
			pairs.next();
		}
	}
	let func_args = pairs.map(parse_func_arg).collect();
	(func_name, func_type, func_args)
}

fn parse_func_arg(pair: Pair) -> FuncArg {
	assert_eq!(pair.as_rule(), Rule::funcArg);
	let mut pairs = pair.into_inner();
	let typeref = pairs.next().unwrap();
	let id = pairs.next().unwrap();
	(parse_qualified_id(typeref), parse_id(id))
}

fn parse_global_def(pair: Pair) -> GlobalDef {
	match pair.as_rule() {
		Rule::gTypeDef => {
			let mut pairs = pair.into_inner();
			let id = pairs.next().unwrap();
			let typ = pairs.next().unwrap();
			GlobalDef::Type(parse_qualified_id(id), parse_type_def(typ))
		},
		Rule::gFuncDef => {
			let mut pairs = pair.into_inner();
			let spec = pairs.next().unwrap();
			let ret_type = pairs.next().unwrap();
			let code = pairs.next().unwrap();
			let (func_name, func_type, args) = parse_func_spec(spec);
			GlobalDef::Func(func_name, func_type, args, parse_qualified_id(ret_type), parse_code_block(code))
		},
		_ => panic!("unknown global def type {:?}", pair)
	}
}

pub fn parse_causson_code(code: &str) -> Result<Program, Error<Rule>> {
	let pairs = CaussonParser::parse(Rule::program, code)?;
	let mut output = vec![];

	for pair in pairs {
		match pair.as_rule() {
			Rule::globalDef => {
				output.push(parse_global_def(pair.into_inner().next().unwrap()))
			}
			Rule::EOI => (),
			_ => panic!("unknown global rule {:?}", pair)
		}
	}

	Ok(output)
}
