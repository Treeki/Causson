use crate::ast::*;
use std::fmt;
use std::io;

impl fmt::Display for HLTypeRef {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		fmt_qid(f, &self.0)?;
		if !self.1.is_empty() {
			for (index, tref) in self.1.iter().enumerate() {
				if index == 0 {
					write!(f, "<{}", tref)?;
				} else {
					write!(f, ", {}", tref)?;
				}
			}
			write!(f, ">")?;
		}
		Ok(())
	}
}

fn do_indent(output: &mut dyn io::Write, amount: usize) -> io::Result<()> {
	for _ in 0..amount {
		write!(output, "  ")?;
	}
	Ok(())
}

impl HLExpr {
	pub fn pretty_print_block(&self, output: &mut dyn io::Write, indent: usize) -> io::Result<()> {
		use HLExpr::*;
		match self {
			CodeBlock(subexprs) => {
				for subexpr in subexprs {
					do_indent(output, indent)?;
					subexpr.pretty_print(output, indent)?;
					writeln!(output)?;
				}
			}
			_ => {
				do_indent(output, indent)?;
				self.pretty_print(output, indent)?;
				writeln!(output)?;
			}
		}
		Ok(())
	}

	pub fn pretty_print(&self, output: &mut dyn io::Write, indent: usize) -> io::Result<()> {
		use HLExpr::*;
		match self {
			ID(sym) => write!(output, "{}", sym)?,
			Specialise(subexpr, typerefs) => {
				subexpr.pretty_print(output, indent)?;
				for (index, typeref) in typerefs.iter().enumerate() {
					if index == 0 {
						write!(output, "<{}", *typeref)?;
					} else {
						write!(output, ", {}", *typeref)?;
					}
				}
				write!(output, ">")?;
			}
			NamespaceAccess(subexpr, sym) => {
				subexpr.pretty_print(output, indent)?;
				write!(output, ":{}", sym)?;
			}
			Binary(left, op, right) => {
				left.pretty_print(output, indent)?;
				write!(output, " {} ", op)?;
				right.pretty_print(output, indent)?;
			}
			PropAccess(subexpr, sym) => {
				subexpr.pretty_print(output, indent)?;
				write!(output, ".{}", sym)?;
			}
			Call(target, args) => {
				target.pretty_print(output, indent)?;
				write!(output, "(")?;
				for (index, arg) in args.iter().enumerate() {
					if index > 0 {
						write!(output, ", ")?;
					}
					arg.pretty_print(output, indent)?;
				}
				write!(output, ")")?;
			}
			If(cond, true_expr, false_expr) => {
				write!(output, "if ")?;
				cond.pretty_print(output, indent)?;
				writeln!(output, " {{")?;
				true_expr.pretty_print_block(output, indent + 1)?;
				do_indent(output, indent)?;
				match false_expr {
					None => write!(output, "}}")?,
					Some(box If(_, _, _)) => {
						write!(output, "}} el")?;
						false_expr.as_ref().unwrap().pretty_print(output, indent)?;
					}
					Some(false_expr) => {
						writeln!(output, "}} else {{")?;
						false_expr.pretty_print_block(output, indent + 1)?;
						do_indent(output, indent)?;
						write!(output, "}}")?;
					}
				}
			}
			While(cond, body) => {
				write!(output, "while ")?;
				cond.pretty_print(output, indent)?;
				writeln!(output, " {{")?;
				body.pretty_print_block(output, indent + 1)?;
				do_indent(output, indent)?;
				write!(output, "}}")?;
			}
			Match(cond, arms) => {
				write!(output, "match ")?;
				cond.pretty_print(output, indent)?;
				writeln!(output, " {{")?;
				for (arm_index, (choice_id, args, body)) in arms.iter().enumerate() {
					if arm_index > 0 {
						writeln!(output, ",")?;
					}
					do_indent(output, indent + 1)?;
					write!(output, "{}", choice_id)?;
					if !args.is_empty() {
						write!(output, "(")?;
						for (arg_index, arg) in args.iter().enumerate() {
							if arg_index > 0 {
								write!(output, ", ")?;
							}
							write!(output, "{}", arg)?;
						}
						write!(output, ")")?;
					}
					writeln!(output, " => {{")?;
					body.pretty_print_block(output, indent + 2)?;
					do_indent(output, indent + 1)?;
					write!(output, "}}")?;
				}
				writeln!(output)?;
				do_indent(output, indent)?;
				write!(output, "}}")?;
			}
			Let(sym, subexpr) => {
				write!(output, "let {} = ", sym)?;
				subexpr.pretty_print(output, indent)?;
			}
			CodeBlock(_) => panic!("unexpected block"),
			Int(Ok(i)) => write!(output, "{}", i)?,
			Int(_) => write!(output, "???")?,
			Real(Ok(i)) => write!(output, "{:#?}", i)?,
			Real(_) => write!(output, "???")?,
			Bool(true) => write!(output, "true")?,
			Bool(false) => write!(output, "false")?,
			Str(s) => write!(output, "\"{}\"", s)?
		}

		Ok(())
	}
}

pub fn print_program(output: &mut dyn io::Write, defs: &[GlobalDef]) -> io::Result<()> {
	for def in defs {
		match def {
			GlobalDef::Component(qid, _) => {
				write!(output, "-- component ")?;
				write_qid(output, qid)?;
				writeln!(output)?;
			}
			GlobalDef::Type(qid, typ) => {
				write!(output, "type ")?;
				write_qid(output, qid)?;
				write!(output, " = ")?;

				match typ {
					HLTypeDef::Wrap(wraptyp) => writeln!(output, "wrap {}", wraptyp)?,
					HLTypeDef::Enum(variants) => {
						write!(output, "enum(")?;
						for (index, (sym, args)) in variants.iter().enumerate() {
							if index == 0 {
								write!(output, "{}", *sym)?;
							} else {
								write!(output, ", {}", *sym)?;
							}
							if !args.is_empty() {
								for (arg_index, (arg_typeref, arg_name)) in args.iter().enumerate() {
									if arg_index == 0 {
										write!(output, "({} {}", arg_typeref, *arg_name)?;
									} else {
										write!(output, ", {} {}", arg_typeref, *arg_name)?;
									}
								}
								write!(output, ")")?;
							}
						}
						writeln!(output, ")")?;
					}
					HLTypeDef::Record { fields, .. } => {
						writeln!(output, "record {{")?;
						for (typeref, sym) in fields {
							writeln!(output, "  {} {}", typeref, sym)?;
						}
						writeln!(output, "}}")?;
					}
				}
			}
			GlobalDef::Func(qid, func_type, func_args, ret_typeref, expr) => {
				write!(output, "def ")?;
				write_qid(output, qid)?;

				let mut add_comma = false;
				match func_type {
					FuncType::Function => write!(output, "(")?,
					FuncType::Method   => { write!(output, "(self")?; add_comma = true; }
				};

				for (arg_type, arg_name) in func_args {
					if add_comma {
						write!(output, ", ")?;
					}
					add_comma = true;

					write!(output, "{} {}", arg_type, arg_name)?;
				}

				writeln!(output, ") -> {} {{", ret_typeref)?;
				expr.pretty_print_block(output, 1)?;
				writeln!(output, "}}")?;
			}
		}
	}
	Ok(())
}
