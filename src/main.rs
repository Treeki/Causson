#![feature(box_patterns)]
#![feature(trace_macros)]

extern crate pest;
#[macro_use]
extern crate pest_derive;
#[macro_use]
extern crate lazy_static;
extern crate paste;
extern crate symbol;
extern crate gtk;
extern crate gio;

#[macro_use]
mod ast;
mod ast_builder;
mod data;
mod eval;
mod gc;
mod parser;
mod pretty_print;
mod stdlib;

fn main() {
    let args = std::env::args().collect::<Vec<String>>();
    if args.len() < 2 {
        println!("Please specify a source code file: {} something.causson", args[0]);
        return
    }
    let code = match std::fs::read_to_string(&args[1]) {
        Ok(c) => c,
        Err(e) => {
            println!("Unable to read file {}:", args[1]);
            println!("{}", e);
            return
        }
    };
    let parsed = match ast_builder::parse_causson_code(&code) {
        Ok(c) => c,
        Err(e) => {
            println!("Error parsing code:");
            println!("{}", e);
            return
        }
    };
    let symtab_rc = match parser::make_symtab_from_program(&parsed) {
        Ok(c) => c,
        Err(e) => {
            println!("Error checking code:");
            println!("{}", e);
            return
        }
    };
    let result = eval::call_func(&symtab_rc, &[], &[], id!(main), &[], &[], false).unwrap();
    println!("Program Result: {:?}", result);
}
