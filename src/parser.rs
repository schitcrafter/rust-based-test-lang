use pest_derive::Parser;

use crate::ast;

pub mod function_context;
pub mod module_context;
pub mod nodeid_visitor;

#[derive(Parser)]
#[grammar = "parser/base_rules.pest"]
#[grammar = "parser/function_context.pest"]
#[grammar = "parser/module_context.pest"]
pub struct PestParser;

pub struct Parser<'input> {
    input: &'input str,
    root_module: Option<Vec<ast::OuterExpression<'input>>>
}

impl<'input> Parser<'input> {
    pub fn new(input: &'input str) -> Parser {
        Parser {
            input,
            root_module: None,
        }
    }

    pub fn parse_module(&mut self) {
        use pest::Parser as _;
        let pairs = PestParser::parse(Rule::module_context, self.input)
            .expect("Couldn't parse module context");

        self.root_module = self.parse_module_context(pairs).into();
    }

}
