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



#[cfg(test)]
mod tests {
	use super::*;
	use super::parse_causson_code as pcc;

	#[test]
	fn test_whitespace() {
		pcc("def x() -> void { }").expect("singleline function must work");
		pcc("\n\ndef x() -> void { }").expect("newlines at start must be allowed");
		pcc("def x() -> void { }\n\n").expect("newlines at end must be allowed");
		pcc("def x() -> void {\nlet x = 1 +\\\n3\n}").expect("newlines within expressions must be allowed");
		pcc("def x() -> void\\\n{ let x = 1 +\\\n3 }").expect("newlines within function definitions must be allowed");
	}

	#[test]
	fn test_comments() {
		let c = pcc("--xxx
			type a = wrap a
			--type b = wrap a
			def a() -> void {
				x = 1 + 3 -- * y
			}").unwrap();
		assert_eq!(c, vec![
			GlobalDef::Type(vec!["a".into()], TypeDef::Wrap(vec!["a".into()])),
			GlobalDef::Func(
				vec!["a".into()], FuncType::Function, vec![], vec!["void".into()],
				HLExpr::Binary(
					Box::new(HLExpr::ID(vec!["x".into()])),
					"=".into(),
					Box::new(HLExpr::Binary(Box::new(HLExpr::Int(Ok(1))), "+".into(), Box::new(HLExpr::Int(Ok(3)))))
				)
			)
		]);
	}

	#[test]
	fn test_wrap_type() {
		let x_qid = vec!["x".into()];
		let y_qid = vec!["y".into()];
		let a_b_qid = vec!["a".into(), "b".into()];

		let c = pcc("type x = wrap y").unwrap();
		assert_eq!(c, vec![GlobalDef::Type(x_qid.clone(), TypeDef::Wrap(y_qid.clone()))]);
		let c = pcc("type y = wrap a:b").unwrap();
		assert_eq!(c, vec![GlobalDef::Type(y_qid.clone(), TypeDef::Wrap(a_b_qid.clone()))]);
		let c = pcc("type a:b = wrap y").unwrap();
		assert_eq!(c, vec![GlobalDef::Type(a_b_qid.clone(), TypeDef::Wrap(y_qid.clone()))]);
	}

	#[test]
	fn test_enum_type() {
		let x_qid = vec!["x".into()];
		let a_b_c_syms = vec!["a".into(), "b".into(), "c".into()];
		let c = pcc("type x = enum(a,b,c)").unwrap();
		assert_eq!(c, vec![GlobalDef::Type(x_qid, TypeDef::Enum(a_b_c_syms))]);
	}

	#[test]
	#[should_panic]
	fn test_empty_enum_type() {
		pcc("type x = enum()").unwrap();
	}

	#[test]
	fn test_func_spec() {
		let x_qid = vec!["x".into()];
		let x_y_z_qid = vec!["x".into(), "y".into(), "z".into()];
		let void_qid = vec!["void".into()];
		let int_qid = vec!["int".into()];
		let real_qid = vec!["real".into()];
		let foo_bar_qid = vec!["foo".into(), "bar".into()];

		let c = pcc("def x() -> void { }").unwrap();
		let args = vec![];
		assert_eq!(c, vec![GlobalDef::Func(x_qid.clone(), FuncType::Function, args, void_qid.clone(), HLExpr::CodeBlock(vec![]))]);

		let c = pcc("def x:y:z(real r) -> int { }").unwrap();
		let args = vec![(real_qid.clone(), "r".into())];
		assert_eq!(c, vec![GlobalDef::Func(x_y_z_qid.clone(), FuncType::Function, args, int_qid.clone(), HLExpr::CodeBlock(vec![]))]);

		let c = pcc("def x:y:z(real r, foo:bar fb, int i) -> foo:bar { }").unwrap();
		let args = vec![(real_qid.clone(), "r".into()), (foo_bar_qid.clone(), "fb".into()), (int_qid.clone(), "i".into())];
		assert_eq!(c, vec![GlobalDef::Func(x_y_z_qid.clone(), FuncType::Function, args, foo_bar_qid.clone(), HLExpr::CodeBlock(vec![]))]);
	}

	#[test]
	fn test_method_spec() {
		let x_y_z_qid = vec!["x".into(), "y".into(), "z".into()];
		let void_qid = vec!["void".into()];
		let int_qid = vec!["int".into()];
		let real_qid = vec!["real".into()];

		let c = pcc("def x:y:z(self) -> void { }").unwrap();
		let args = vec![];
		assert_eq!(c, vec![GlobalDef::Func(x_y_z_qid.clone(), FuncType::Method, args, void_qid.clone(), HLExpr::CodeBlock(vec![]))]);

		let c = pcc("def x:y:z(self, real r) -> int { }").unwrap();
		let args = vec![(real_qid.clone(), "r".into())];
		assert_eq!(c, vec![GlobalDef::Func(x_y_z_qid.clone(), FuncType::Method, args, int_qid.clone(), HLExpr::CodeBlock(vec![]))]);
	}

	fn assert_expr(ecode: &str, expected: HLExpr) {
		let ecode = String::from("def x() -> void {") + ecode + "}";
		let c = pcc(&ecode).expect(&ecode);
		assert_eq!(c, vec![GlobalDef::Func(vec!["x".into()], FuncType::Function, vec![], vec!["void".into()], expected)]);
	}

	fn box_qid(i: &str) -> Box<HLExpr> { Box::new(HLExpr::ID(vec![i.into()])) }
	fn box_bool(v: bool) -> Box<HLExpr> { Box::new(HLExpr::Bool(v)) }
	fn box_int(v: i64) -> Box<HLExpr> { Box::new(HLExpr::Int(Ok(v))) }

	#[test]
	fn test_binary_ops() {
		use HLExpr::*;
		assert_expr("1 + 2", Binary(box_int(1), "+".into(), box_int(2)));
		assert_expr("1 - 2", Binary(box_int(1), "-".into(), box_int(2)));
		assert_expr("1 * 2", Binary(box_int(1), "*".into(), box_int(2)));
		assert_expr("1 / 2", Binary(box_int(1), "/".into(), box_int(2)));
		assert_expr("1 = 2", Binary(box_int(1), "=".into(), box_int(2)));
		assert_expr("1 < 2", Binary(box_int(1), "<".into(), box_int(2)));
		assert_expr("1 > 2", Binary(box_int(1), ">".into(), box_int(2)));
		assert_expr("1 <= 2", Binary(box_int(1), "<=".into(), box_int(2)));
		assert_expr("1 >= 2", Binary(box_int(1), ">=".into(), box_int(2)));
		assert_expr("1 == 2", Binary(box_int(1), "==".into(), box_int(2)));
		assert_expr("1 != 2", Binary(box_int(1), "!=".into(), box_int(2)));
	}

	#[test]
	fn test_binary_op_precedence() {
		use HLExpr::*;
		assert_expr("1 * 2 + 3", Binary(Box::new(Binary(box_int(1), "*".into(), box_int(2))), "+".into(), box_int(3)));
		assert_expr("1 * (2 + 3)", Binary(box_int(1), "*".into(), Box::new(Binary(box_int(2), "+".into(), box_int(3)))));

		assert_expr(
			"1 * 2 + 3 / 4 - 5 * 6",
			Binary(
				Box::new(Binary(
					Box::new(Binary(box_int(1), "*".into(), box_int(2))),
					"+".into(),
					Box::new(Binary(box_int(3), "/".into(), box_int(4)))
				)),
				"-".into(),
				Box::new(Binary(box_int(5), "*".into(), box_int(6)))
			)
		);

		assert_expr(
			"a = 5 < x + 3",
			Binary(
				Box::new(ID(vec!["a".into()])),
				"=".into(),
				Box::new(Binary(
					box_int(5),
					"<".into(),
					Box::new(Binary(
						Box::new(ID(vec!["x".into()])),
						"+".into(),
						box_int(3)
					))
				))
			)
		);
	}

	#[test]
	fn test_constants() {
		use HLExpr::*;
		assert_expr("true", Bool(true));
		assert_expr("false", Bool(false));
		assert_expr("34", Int(Ok(34)));
		assert_expr("34.1", Real(Ok(34.1))); // this is probably dodgy...

		// this should error on overflow, TODO figure out a better way to detect that
		assert_expr("18446744073709551615", Int("18446744073709551615".parse::<i64>()));
	}

	#[test]
	fn test_if() {
		use HLExpr::*;
		assert_expr(
			"if true { 1 }",
			If(box_bool(true), box_int(1), None)
		);
		assert_expr(
			"if true { 1 } else { 2 }",
			If(box_bool(true), box_int(1), Some(box_int(2)))
		);
		assert_expr(
			"if true { 1 } elif foo { 2 } else { 3 }",
			If(box_bool(true), box_int(1), Some(
				Box::new(If(box_qid("foo"), box_int(2), Some(box_int(3))))
			))
		);
		assert_expr(
			"if true {
				1
				2
			} else {
				3
			}",
			If(box_bool(true), Box::new(CodeBlock(vec![Int(Ok(1)), Int(Ok(2))])), Some(box_int(3)))
		);
	}

	#[test]
	fn test_let() {
		use HLExpr::*;
		assert_expr(
			"let x = 5",
			Let("x".into(), box_int(5))
		);
		assert_expr(
			"let x = 1 + 2 + 3",
			Let(
				"x".into(),
				Box::new(Binary(
					Box::new(Binary(box_int(1), "+".into(), box_int(2))),
					"+".into(),
					box_int(3)
				))
			)
		);
	}

	#[test]
	fn test_term_suffixes() {
		use HLExpr::*;
		assert_expr("a:b.c", PropAccess(Box::new(ID(vec!["a".into(), "b".into()])), "c".into()));
		assert_expr("a.b", PropAccess(box_qid("a"), "b".into()));
		assert_expr("a()", Call(box_qid("a"), vec![]));
		assert_expr("a(1)", Call(box_qid("a"), vec![Int(Ok(1))]));
		assert_expr("a(1, 2)", Call(box_qid("a"), vec![Int(Ok(1)), Int(Ok(2))]));
		assert_expr("a.b(1, 2)", Call(Box::new(PropAccess(box_qid("a"), "b".into())), vec![Int(Ok(1)), Int(Ok(2))]));
		assert_expr("a().b", PropAccess(Box::new(Call(box_qid("a"), vec![])), "b".into()));
	}
}

