#![feature(box_patterns)]

extern crate pest;
#[macro_use]
extern crate pest_derive;
#[macro_use]
extern crate lazy_static;
extern crate symbol;

mod ast;
mod ast_builder;
mod data;
mod eval;
mod gc;
mod parser;
mod stdlib;

fn main() {
    let code = std::fs::read_to_string("sample/temperature.causson").unwrap();
    let parsed = ast_builder::parse_causson_code(&code).unwrap();
    let symtab = parser::make_symtab_from_program(&parsed).unwrap();
    let result = eval::call_func(&symtab, &["main".into()], &[], &[]).unwrap();
    println!("Program Result: {:?}", result);
    data::MAIN_GC.with(|gc| {
        println!("GC Nodes: {}", gc.node_count());
        gc.dump();
        gc.sweep();
        println!("After sweep: GC Nodes: {}", gc.node_count());
        gc.dump();
    });
}
