use pest_derive::Parser;

mod function_context;
mod module_context;


#[derive(Parser)]
#[grammar = "parser/base_rules.pest"]
#[grammar = "parser/function_context.pest"]
#[grammar = "parser/module_context.pest"]
pub struct PestParser;