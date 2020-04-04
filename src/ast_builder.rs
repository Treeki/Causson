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
	id!(pair.as_str())
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
			Operator::new(logOr, Left),
			Operator::new(logAnd, Left),
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
			HLExpr::Binary(Box::new(lhs), id!(op.as_str()), Box::new(rhs))
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
			Rule::termNamespaceAccess => {
				let id = parse_id(suffix.into_inner().next().unwrap());
				HLExpr::NamespaceAccess(Box::new(expr), id)
			}
			Rule::termSpecialise => {
				let refs = suffix.into_inner().map(parse_type_ref).collect();
				HLExpr::Specialise(Box::new(expr), refs)
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

fn parse_match_arm_spec(pair: Pair) -> (Symbol, Vec<Symbol>) {
	let mut pairs = pair.into_inner();
	let choice = parse_id(pairs.next().unwrap());
	let args = pairs.map(parse_id).collect();
	(choice, args)
}

fn parse_match_arm(pair: Pair) -> (Symbol, Vec<Symbol>, HLExpr) {
	let mut pairs = pair.into_inner();
	let (choice, args) = parse_match_arm_spec(pairs.next().unwrap());
	let code_pair = pairs.next().unwrap();
	let code_expr = match code_pair.as_rule() {
		Rule::expr => parse_hlexpr(code_pair),
		Rule::codeBlock => parse_code_block(code_pair),
		_ => unreachable!()
	};
	(choice, args, code_expr)
}

fn parse_term_piece(pair: Pair) -> HLExpr {
	match pair.as_rule() {
		Rule::id => HLExpr::ID(parse_id(pair)),
		Rule::bTrue => HLExpr::Bool(true),
		Rule::bFalse => HLExpr::Bool(false),
		Rule::real => HLExpr::Real(pair.as_str().parse()),
		Rule::int => HLExpr::Int(pair.as_str().parse()),
		Rule::string => HLExpr::Str(pair.into_inner().next().unwrap().as_str().to_string()),
		Rule::ifTerm => parse_if_piece(&mut pair.into_inner().peekable()),
		Rule::whileTerm => {
			let mut pairs = pair.into_inner();
			let cond = Box::new(parse_hlexpr(pairs.next().unwrap()));
			let expr = Box::new(parse_code_block(pairs.next().unwrap()));
			HLExpr::While(cond, expr)
		}
		Rule::letTerm => {
			let mut pairs = pair.into_inner();
			let name = parse_id(pairs.next().unwrap());
			let value = Box::new(parse_hlexpr(pairs.next().unwrap()));
			HLExpr::Let(name, value)
		}
		Rule::matchTerm => {
			let mut pairs = pair.into_inner();
			let cond = Box::new(parse_hlexpr(pairs.next().unwrap()));
			let arms = pairs.map(parse_match_arm).collect();
			HLExpr::Match(cond, arms)
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
fn parse_type_def(pair: Pair) -> HLTypeDef {
	match pair.as_rule() {
		Rule::wrapDef => HLTypeDef::Wrap(parse_type_ref(pair.into_inner().next().unwrap())),
		Rule::enumDef => {
			HLTypeDef::Enum(pair.into_inner().map(parse_enum_value).collect())
		},
		Rule::recordDef => {
			let fields = pair.into_inner().map(parse_typed_id).collect();
			HLTypeDef::Record { fields, rename_setters: false }
		},
		_ => unreachable!()
	}
}

fn parse_enum_value(pair: Pair) -> (Symbol, Vec<(HLTypeRef, Symbol)>) {
	assert_eq!(pair.as_rule(), Rule::enumValue);
	let mut pairs = pair.into_inner();
	let val_id = parse_id(pairs.next().unwrap());
	let vec: Vec<(HLTypeRef, Symbol)> = pairs.map(parse_typed_id).collect();
	(val_id, vec)
}

fn parse_func_spec(pair: Pair) -> (QualID, FuncType, Vec<HLFuncArg>) {
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
	let func_args = pairs.map(parse_typed_id).collect();
	(func_name, func_type, func_args)
}

fn parse_type_ref(pair: Pair) -> HLTypeRef {
	assert_eq!(pair.as_rule(), Rule::typeRef);
	let mut pairs = pair.into_inner();
	let qid = parse_qualified_id(pairs.next().unwrap());
	let subrefs: Vec<HLTypeRef> = pairs.map(parse_type_ref).collect();
	HLTypeRef(qid, subrefs)
}

fn parse_typed_id(pair: Pair) -> (HLTypeRef, Symbol) {
	assert_eq!(pair.as_rule(), Rule::typedID);
	let mut pairs = pair.into_inner();
	let typeref = pairs.next().unwrap();
	let id = pairs.next().unwrap();
	(parse_type_ref(typeref), parse_id(id))
}

fn parse_comp_subdef(pair: Pair) -> HLCompSubDef {
	match pair.as_rule() {
		Rule::compInstance => {
			let mut pairs = pair.into_inner();
			let name = match pairs.peek().unwrap().as_rule() {
				Rule::id => Some(parse_id(pairs.next().unwrap())),
				_ => None
			};
			let what = parse_type_ref(pairs.next().unwrap());
			let new_args = match pairs.peek() {
				Some(r) if r.as_rule() == Rule::compInstanceArgs => {
					pairs.next().unwrap().into_inner().map(parse_hlexpr).collect()
				}
				_ => vec![]
			};
			let children = pairs.map(parse_comp_subdef).collect();
			HLCompSubDef::Instance(HLCompInstance { name, what, new_args, children })
		},
		Rule::compEventConnection => {
			let mut pairs = pair.into_inner();
			let id = parse_id(pairs.next().unwrap());
			let expr = match pairs.peek().unwrap().as_rule() {
				Rule::expr => parse_hlexpr(pairs.next().unwrap()),
				Rule::codeBlock => parse_code_block(pairs.next().unwrap()),
				_ => unreachable!()
			};
			HLCompSubDef::EventConnection(id, expr)
		},
		Rule::compTransientAdd => {
			let mut pairs = pair.into_inner();
			let expr = parse_hlexpr(pairs.next().unwrap());
			HLCompSubDef::TransientAdd(expr)
		},
		Rule::compPropSet => {
			let mut pairs = pair.into_inner();
			let id = parse_id(pairs.next().unwrap());
			let expr = parse_hlexpr(pairs.next().unwrap());
			HLCompSubDef::PropertySet(id, expr)
		},
		Rule::compMethod => {
			let mut pairs = pair.into_inner();
			let spec = pairs.next().unwrap();
			let ret_type = pairs.next().unwrap();
			let code = pairs.next().unwrap();
			let (method_name, args) = parse_comp_method_spec(spec);
			HLCompSubDef::Method(method_name, args, parse_type_ref(ret_type), parse_code_block(code))
		}
		_ => panic!("unknown component subdef type {:?}", pair)
	}
}

fn parse_comp_method_spec(pair: Pair) -> (Symbol, Vec<HLFuncArg>) {
	assert_eq!(pair.as_rule(), Rule::compMethodSpec);
	let mut pairs = pair.into_inner();
	let method_name = parse_id(pairs.next().unwrap());
	let args = pairs.map(parse_typed_id).collect();
	(method_name, args)
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
			GlobalDef::Func(func_name, func_type, args, parse_type_ref(ret_type), parse_code_block(code))
		},
		Rule::gComponentDef => {
			let mut pairs = pair.into_inner();
			let qual_id = pairs.next().unwrap();
			let subdefs = pairs.map(parse_comp_subdef).collect();
			GlobalDef::Component(parse_qualified_id(qual_id), subdefs)
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

	fn typeref(qid: QualID) -> HLTypeRef {
		HLTypeRef(qid, vec![])
	}

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
			GlobalDef::Type(qid!(a), HLTypeDef::Wrap(typeref(qid!(a)))),
			GlobalDef::Func(
				qid!(a), FuncType::Function, vec![], typeref(qid!(void)),
				HLExpr::Binary(
					Box::new(HLExpr::ID(id!(x))),
					id!("="),
					Box::new(HLExpr::Binary(Box::new(HLExpr::Int(Ok(1))), id!("+"), Box::new(HLExpr::Int(Ok(3)))))
				)
			)
		]);
	}

	#[test]
	fn test_wrap_type() {
		let c = pcc("type x = wrap y").unwrap();
		assert_eq!(c, vec![GlobalDef::Type(qid!(x), HLTypeDef::Wrap(typeref(qid!(y))))]);
		let c = pcc("type y = wrap a:b").unwrap();
		assert_eq!(c, vec![GlobalDef::Type(qid!(y), HLTypeDef::Wrap(typeref(qid!(a:b))))]);
		let c = pcc("type a:b = wrap y").unwrap();
		assert_eq!(c, vec![GlobalDef::Type(qid!(a:b), HLTypeDef::Wrap(typeref(qid!(y))))]);
	}

	#[test]
	fn test_enum_type() {
		let a_b_c_syms = vec![
			(id!(a), vec![]),
			(id!(b), vec![(typeref(qid!(int)), id!(z))]),
			(id!(c), vec![])
		];
		let c = pcc("type x = enum(a,b(int z),c)").unwrap();
		assert_eq!(c, vec![GlobalDef::Type(qid!(x), HLTypeDef::Enum(a_b_c_syms))]);
	}

	#[test]
	#[should_panic]
	fn test_empty_enum_type() {
		pcc("type x = enum()").unwrap();
	}

	#[test]
	fn test_record_type() {
		fn build_rec(fields: Vec<(HLTypeRef, Symbol)>) -> HLTypeDef {
			HLTypeDef::Record { fields, rename_setters: false }
		}

		let int_a = (typeref(qid!(int)), id!(a));
		let real_b = (typeref(qid!(real)), id!(b));
		let xyz_c = (typeref(qid!(xyz)), id!(c));

		let c = pcc("type x = record { int a, real b }").unwrap();
		assert_eq!(c, vec![GlobalDef::Type(qid!(x), build_rec(vec![int_a.clone(), real_b.clone()]))]);
		let c = pcc("type x = record { real b }").unwrap();
		assert_eq!(c, vec![GlobalDef::Type(qid!(x), build_rec(vec![real_b.clone()]))]);
		let c = pcc("type x = record {\nreal b\n}").unwrap();
		assert_eq!(c, vec![GlobalDef::Type(qid!(x), build_rec(vec![real_b.clone()]))]);
		let c = pcc("type x = record {real b,}").unwrap();
		assert_eq!(c, vec![GlobalDef::Type(qid!(x), build_rec(vec![real_b.clone()]))]);
		let c = pcc("type x = record { int a\nreal b, xyz c\n }").unwrap();
		assert_eq!(c, vec![GlobalDef::Type(qid!(x), build_rec(vec![int_a.clone(), real_b.clone(), xyz_c.clone()]))]);
	}

	#[test]
	fn test_func_spec() {
		let c = pcc("def x() -> void { }").unwrap();
		let args = vec![];
		assert_eq!(c, vec![GlobalDef::Func(qid!(x), FuncType::Function, args, typeref(qid!(void)), HLExpr::CodeBlock(vec![]))]);

		let c = pcc("def x:y:z(real r) -> int { }").unwrap();
		let args = vec![(typeref(qid!(real)), id!(r))];
		assert_eq!(c, vec![GlobalDef::Func(qid!(x:y:z), FuncType::Function, args, typeref(qid!(int)), HLExpr::CodeBlock(vec![]))]);

		let c = pcc("def x:y:z(real r, foo:bar fb, int i) -> foo:bar { }").unwrap();
		let args = vec![
			(typeref(qid!(real)), id!(r)),
			(typeref(qid!(foo:bar)), id!(fb)),
			(typeref(qid!(int)), id!(i))
		];
		assert_eq!(c, vec![GlobalDef::Func(qid!(x:y:z), FuncType::Function, args, typeref(qid!(foo:bar)), HLExpr::CodeBlock(vec![]))]);
	}

	#[test]
	fn test_method_spec() {
		let c = pcc("def x:y:z(self) -> void { }").unwrap();
		let args = vec![];
		assert_eq!(c, vec![GlobalDef::Func(qid!(x:y:z), FuncType::Method, args, typeref(qid!(void)), HLExpr::CodeBlock(vec![]))]);

		let c = pcc("def x:y:z(self, real r) -> int { }").unwrap();
		let args = vec![(typeref(qid!(real)), id!(r))];
		assert_eq!(c, vec![GlobalDef::Func(qid!(x:y:z), FuncType::Method, args, typeref(qid!(int)), HLExpr::CodeBlock(vec![]))]);
	}

	fn assert_expr(ecode: &str, expected: HLExpr) {
		let ecode = String::from("def x() -> void {") + ecode + "}";
		let c = pcc(&ecode).expect(&ecode);
		assert_eq!(c, vec![GlobalDef::Func(qid!(x), FuncType::Function, vec![], typeref(qid!(void)), expected)]);
	}

	fn box_id(id: Symbol) -> Box<HLExpr> { Box::new(HLExpr::ID(id)) }
	fn box_bool(v: bool) -> Box<HLExpr> { Box::new(HLExpr::Bool(v)) }
	fn box_int(v: i64) -> Box<HLExpr> { Box::new(HLExpr::Int(Ok(v))) }

	#[test]
	fn test_binary_ops() {
		use HLExpr::*;
		assert_expr("1 + 2", Binary(box_int(1), id!("+"), box_int(2)));
		assert_expr("1 - 2", Binary(box_int(1), id!("-"), box_int(2)));
		assert_expr("1 * 2", Binary(box_int(1), id!("*"), box_int(2)));
		assert_expr("1 / 2", Binary(box_int(1), id!("/"), box_int(2)));
		assert_expr("1 = 2", Binary(box_int(1), id!("="), box_int(2)));
		assert_expr("1 < 2", Binary(box_int(1), id!("<"), box_int(2)));
		assert_expr("1 > 2", Binary(box_int(1), id!(">"), box_int(2)));
		assert_expr("1 <= 2", Binary(box_int(1), id!("<="), box_int(2)));
		assert_expr("1 >= 2", Binary(box_int(1), id!(">="), box_int(2)));
		assert_expr("1 == 2", Binary(box_int(1), id!("=="), box_int(2)));
		assert_expr("1 != 2", Binary(box_int(1), id!("!="), box_int(2)));
		assert_expr("1 && 2", Binary(box_int(1), id!("&&"), box_int(2)));
		assert_expr("1 || 2", Binary(box_int(1), id!("||"), box_int(2)));
	}

	#[test]
	fn test_binary_op_precedence() {
		use HLExpr::*;
		assert_expr("1 * 2 + 3", Binary(Box::new(Binary(box_int(1), id!("*"), box_int(2))), id!("+"), box_int(3)));
		assert_expr("1 * (2 + 3)", Binary(box_int(1), id!("*"), Box::new(Binary(box_int(2), id!("+"), box_int(3)))));

		assert_expr(
			"1 * 2 + 3 / 4 - 5 * 6",
			Binary(
				Box::new(Binary(
					Box::new(Binary(box_int(1), id!("*"), box_int(2))),
					id!("+"),
					Box::new(Binary(box_int(3), id!("/"), box_int(4)))
				)),
				id!("-"),
				Box::new(Binary(box_int(5), id!("*"), box_int(6)))
			)
		);

		assert_expr(
			"a = 5 < x + 3",
			Binary(
				Box::new(ID(id!(a))),
				id!("="),
				Box::new(Binary(
					box_int(5),
					id!("<"),
					Box::new(Binary(
						Box::new(ID(id!(x))),
						id!("+"),
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
				Box::new(If(box_id(id!(foo)), box_int(2), Some(box_int(3))))
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
	fn test_while() {
		use HLExpr::*;
		assert_expr(
			"while 1 < 2 { 5 }",
			While(
				Box::new(Binary(box_int(1), id!("<"), box_int(2))),
				box_int(5)
			)
		);
	}

	#[test]
	fn test_match() {
		use HLExpr::*;
		assert_expr(
			"match x(5) { a => 1, b(z) => 3 }",
			Match(
				Box::new(Call(box_id(id!(x)), vec![Int(Ok(5))])),
				vec![
					(id!(a), vec![], Int(Ok(1))),
					(id!(b), vec![id!(z)], Int(Ok(3)))
				]
			)
		);
		assert_expr(
			"match a {\na => {1}\nb => 2, c => 3\nd => 4\n}",
			Match(
				box_id(id!(a)),
				vec![
					(id!(a), vec![], Int(Ok(1))),
					(id!(b), vec![], Int(Ok(2))),
					(id!(c), vec![], Int(Ok(3))),
					(id!(d), vec![], Int(Ok(4)))
				]
			)
		);
	}

	#[test]
	fn test_let() {
		use HLExpr::*;
		assert_expr(
			"let x = 5",
			Let(id!(x), box_int(5))
		);
		assert_expr(
			"let x = 1 + 2 + 3",
			Let(
				id!(x),
				Box::new(Binary(
					Box::new(Binary(box_int(1), id!("+"), box_int(2))),
					id!("+"),
					box_int(3)
				))
			)
		);
	}

	#[test]
	fn test_term_suffixes() {
		use HLExpr::*;

		let a = box_id(id!(a));
		let a_b = Box::new(NamespaceAccess(a, id!(b)));
		assert_expr("a:b.c", PropAccess(a_b, id!(c)));
		assert_expr("a.b", PropAccess(box_id(id!(a)), id!(b)));
		assert_expr("a()", Call(box_id(id!(a)), vec![]));
		assert_expr("a(1)", Call(box_id(id!(a)), vec![Int(Ok(1))]));
		assert_expr("a(1, 2)", Call(box_id(id!(a)), vec![Int(Ok(1)), Int(Ok(2))]));
		assert_expr("a.b(1, 2)", Call(Box::new(PropAccess(box_id(id!(a)), id!(b))), vec![Int(Ok(1)), Int(Ok(2))]));
		assert_expr("a().b", PropAccess(Box::new(Call(box_id(id!(a)), vec![])), id!(b)));
	}

	#[test]
	fn test_component() {
		let c = pcc("component xyz {}").unwrap();
		assert_eq!(c, vec![GlobalDef::Component(qid!(xyz), vec![])]);

		let c = pcc("component xyz {x = Gui:Window}").unwrap();
		assert_eq!(c, vec![GlobalDef::Component(qid!(xyz), vec![
			HLCompSubDef::Instance(HLCompInstance {
				name: Some(id!(x)),
				what: typeref(qid!(Gui:Window)),
				new_args: vec![],
				children: vec![]
			})
		])]);

		let c = pcc("component xyz {Gui:Window(5) { y = Gui:Button \n Gui:Dummy }}").unwrap();
		assert_eq!(c, vec![GlobalDef::Component(qid!(xyz), vec![
			HLCompSubDef::Instance(HLCompInstance {
				name: None,
				what: typeref(qid!(Gui:Window)),
				new_args: vec![HLExpr::Int(Ok(5))],
				children: vec![
					HLCompSubDef::Instance(HLCompInstance {
						name: Some(id!("y")),
						what: typeref(qid!(Gui:Button)),
						new_args: vec![],
						children: vec![]
					}),
					HLCompSubDef::Instance(HLCompInstance {
						name: None,
						what: typeref(qid!(Gui:Dummy)),
						new_args: vec![],
						children: vec![]
					})
				]
			})
		])]);

		let c = pcc("component xyz {x = Gui:Window { .title = \"beep\" \n .test -> {\n1\n} }}").unwrap();
		assert_eq!(c, vec![GlobalDef::Component(qid!(xyz), vec![
			HLCompSubDef::Instance(HLCompInstance {
				name: Some(id!(x)),
				what: typeref(qid!(Gui:Window)),
				new_args: vec![],
				children: vec![
					HLCompSubDef::PropertySet(id!(title), HLExpr::Str("beep".to_string())),
					HLCompSubDef::EventConnection(id!(test), HLExpr::Int(Ok(1)))
				]
			})
		])]);
	}
}

