#![feature(box_patterns)]

extern crate pest;
#[macro_use]
extern crate pest_derive;
#[macro_use]
extern crate lazy_static;
extern crate symbol;

mod ast;
mod ast_builder;
mod parser;

fn main() {
    let code = std::fs::read_to_string("sample/temperature.causson").unwrap();
    match ast_builder::parse_causson_code(&code) {
        Ok(result) => {
            parser::magic(&result);
            println!("{:?}", result);
        }
        Err(err) => println!("{}", err)
    }
}
