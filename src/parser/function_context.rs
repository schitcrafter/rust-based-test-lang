//! Parses anything inside a function, i.e.
//! Arithmetic, variable bindings, function calls, etc.

use std::sync::LazyLock;

use pest::{iterators::Pairs, pratt_parser::PrattParser, Parser};
use pest_derive::Parser;

use ast::*;

pub mod ast {

    #[derive(Debug, PartialEq)]
    pub enum Statement<'input> {
        LetExpression {
            variable_binding: &'input str,
            type_hint: Option<&'input str>,
            rhs: Expression<'input>
        },
        Expression(Expression<'input>),
    }

    #[derive(Debug, PartialEq)]
    pub enum Expression<'input> {
        Integer(i64),
        Float(f64),
        StringLiteral(String),
        Boolean(bool),
        Character(char),
        Identifier(&'input str),
        BinOp {
            lhs: Box<Expression<'input>>,
            op: BiOperator,
            rhs: Box<Expression<'input>>,
        },
        UnaryOperator(UnaryOperator, Box<Expression<'input>>),
        FunctionCall {
            fn_expr: Box<Expression<'input>>,
            arguments: Vec<Expression<'input>>,
        }
    }

    #[derive(Debug, PartialEq)]
    pub enum BiOperator {
        Add,
        Subtract,
        Multiply,
        Divide,
    }

    #[derive(Debug, PartialEq)]
    pub enum UnaryOperator {
        Minus,
    }
}

#[derive(Parser)]
#[grammar = "parser/function_context.pest"]
#[grammar = "parser/base_rules.pest"]
pub struct FunctionContextParser;

const OPERATOR_PARSER: LazyLock<PrattParser<Rule>> = LazyLock::new(|| {
    use pest::pratt_parser::{Assoc::*, Op};
    use Rule::*;

    // Precedence is defined lowest to highest
    PrattParser::new()
        .op(Op::infix(add, Left) | Op::infix(subtract, Left))
        .op(Op::infix(multiply, Left) | Op::infix(divide, Left))
        .op(Op::prefix(unary_minus))
        .op(Op::postfix(function_call))
});

pub fn parse_function_context<'input>(source: &'input str) -> Vec<Statement> {
    let pairs = FunctionContextParser::parse(Rule::function_context, source)
            .expect("Parsing failed");

    // let pairs = dbg!(pairs);

    let mut statements = vec![];

    for pair in pairs {
        let rule = pair.as_rule();
        let mut inner = pair.into_inner();
        
        let statement = match rule {
            Rule::let_statement => {
                let variable_binding = inner.next().expect("First inner rule of let_statement didn't exist");
                let variable_binding = match variable_binding.as_rule() {
                    Rule::identifier => variable_binding.as_str(),
                    rule => unreachable!("Found rule {rule:?} while looking for identifier in a let statement")
                };

                let mut possible_rhs = inner.next().expect("Second inner rule of let statement didn't exist");

                let type_hint = if possible_rhs.as_rule() == Rule::type_hint {
                    let typename = possible_rhs.into_inner().next().expect("No inner rule inside type_hint in let binding");
                    if typename.as_rule() != Rule::identifier {
                        panic!("Rule inside type hint was not an identifier but a {:?}", typename.as_rule());
                    }
                    
                    // If the second inner rule was a type hint, the third will now be the right-hand side
                    possible_rhs = inner.next().expect("Third inner rule of let statement with type hint didn't exist");
                    
                    Some(typename.as_str())
                } else {
                    None
                };

                Statement::LetExpression {
                    variable_binding,
                    type_hint,
                    rhs: parse_expression(possible_rhs.into_inner())
                }
            },
            Rule::expression => Statement::Expression(parse_expression(inner)),
            Rule::EOI => continue,
            rule => unreachable!("Expected let statement or expression, found {rule:?}")
        };

        statements.push(statement);
    }

    statements
}

pub fn parse_expression<'input>(pairs: Pairs<'input, Rule>) -> Expression<'input> {
    OPERATOR_PARSER
        .map_primary(|primary| match primary.as_rule() {
            Rule::identifier => Expression::Identifier(primary.as_str()),
            Rule::integer => Expression::Integer(primary.as_str().parse().unwrap()),
            Rule::float => Expression::Float(primary.as_str().parse().unwrap()),
            Rule::char_literal => { // TODO: unescape characters
                let inner = primary.into_inner().next()
                    .expect("Char literal didn't have an inner rule");
                Expression::Character(unescape_char(inner.as_str()))
            },
            Rule::string_literal => { // TODO: unescape characters
                let inner = primary.into_inner().next()
                    .expect("String literal didn't have an inner rule");
                Expression::StringLiteral(unescape_string(inner.as_str()))
            },
            Rule::bool_true => Expression::Boolean(true),
            Rule::bool_false => Expression::Boolean(false),
            rule => unreachable!("Expr::parse expected atom, found {rule:?}")
        })
        .map_infix(|lhs, op, rhs| {
            let op = match op.as_rule() {
                Rule::add => BiOperator::Add,
                Rule::subtract => BiOperator::Subtract,
                Rule::multiply => BiOperator::Multiply,
                Rule::divide => BiOperator::Divide,
                rule => unreachable!("Expr::parse expected infix expression, found {rule:?}")
            };

            Expression::BinOp { lhs: Box::new(lhs), op, rhs: Box::new(rhs) }
        })
        .map_prefix(|op, rhs| {
            let op = match op.as_rule() {
                Rule::unary_minus => UnaryOperator::Minus,
                rule => unreachable!("Expr::parse expected unary operator, found {rule:?}"),
            };
            Expression::UnaryOperator(op, Box::new(rhs))
        })
        .map_postfix(|lhs, op| match op.as_rule() {
            Rule::function_call => Expression::FunctionCall {
                fn_expr: Box::new(lhs),
                arguments: op.into_inner().map(|arg| parse_expression(arg.into_inner())).collect()
            },
            rule => unreachable!("Expr::parse expected function call, found {rule:?}")
        })
        .parse(pairs)
}

fn unescape_char(input_str: &str) -> char {
    let input: Vec<char> = input_str.chars().collect();

    match &input[..] {
        [one_char] => *one_char,
        ['\\', escaped_char] => match escaped_char {
            '\'' => '\'',
            '\\' => '\\',
            'n' => '\n',
            'r' => '\r',
            't' => '\t',
            escaped_char => panic!("Invalid escaped char {escaped_char}")
        },
        ['\\', 'u', hex_chars @ ..] if hex_chars.len() == 4 => {
            let unicode_char = u32::from_str_radix(&input_str[2..], 16)
                .expect("Char does not use hex digits");
            char::from_u32(unicode_char).expect("Char is not valid unicode")
        },
        _ => unreachable!("Found invalid char literal {input_str:?}")
    }
}

fn unescape_string(input: &str) -> String {
    let mut unescaped_string = String::new();

    let mut input_chars = input.chars();

    while let Some(char) = input_chars.next() {
        let unescaped = match char {
            '\\' => {
                // escaped character
                let next_char = input_chars.next()
                    .expect("Missing character after backslash in string literal");
                match next_char {
                    '"' => '"',
                    '\\' => '\\',
                    'n' => '\n',
                    'r' => '\r',
                    't' => '\t',
                    // '\n' => '',
                    'u' => {
                        if input_chars.next() != Some('{') {
                            panic!("Expected '{{' after 'u' in string literal");
                        }
                        let mut unicode_value = 0u32;
                        for _ in 0..4 {
                            let hex_char = input_chars.next().unwrap();
                            if !hex_char.is_ascii_hexdigit() {
                                panic!("Expected ASCII hex digit, found {hex_char:?}");
                            }

                            unicode_value <<= 4;
                            unicode_value += hex_char.to_digit(16).unwrap();
                        }

                        if input_chars.next() != Some('}') {
                            panic!("Expected '}}' after unicode escape sequence");
                        }

                        char::from_u32(unicode_value)
                            .expect(&format!("Not a valid unicode char: '{unicode_value}'"))
                    },
                    next_char => panic!("Unknown escape character '{next_char}'")
                }
            },
            other_char => other_char,
        };

        unescaped_string.push(unescaped);
    }

    unescaped_string
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_function_context() {
        let source = "let smth = 3;";

        let statements = parse_function_context(source);

        assert_eq!(statements, vec![
            Statement::LetExpression {
                variable_binding: "smth",
                type_hint: None,
                rhs: Expression::Integer(3)
            }
        ]);
    }

    #[test]
    fn expression_complex_arithmetic() {
        let source = "(3+4) * 17 / -3";

        
        let pairs = FunctionContextParser::parse(Rule::expression, source)
            .expect("Parsing failed");

        println!("{pairs:#?}");
    }

    #[test]
    fn expression_with_comment() {
        let source = r"
        /// doc comment?!
        // comment before
        let /* comment */ smth = 3; // some comment
        // comment after
        // another comment after
        ";
        
        let statements = parse_function_context(source);

        assert_eq!(statements, vec![
            Statement::LetExpression {
                variable_binding: "smth",
                type_hint: None,
                rhs: Expression::Integer(3)
            }
        ]);
    }

    #[test]
    fn expression_function_call() {
        let source = r"
            my_function();
            my_function(2, 3, 4);
            my_function(2, 4, )(); // my_function could return a lambda
            //";

        let statements = parse_function_context(source);

        let second_args = vec![2, 3, 4].into_iter()
            .map(Expression::Integer)
            .collect();

        let third_args = vec![2, 4].into_iter()
            .map(Expression::Integer)
            .collect();

        assert_eq!(statements, vec![
            Statement::Expression(Expression::FunctionCall {
                fn_expr: Box::new(Expression::Identifier("my_function")),
                arguments: vec![] }
            ),
            Statement::Expression(Expression::FunctionCall {
                fn_expr: Box::new(Expression::Identifier("my_function")), arguments: second_args }),
            Statement::Expression(Expression::FunctionCall {
                fn_expr: Box::new(Expression::FunctionCall {
                    fn_expr: Box::new(Expression::Identifier("my_function")),
                    arguments: third_args
                }),
                arguments: vec![]
            })
        ]);
    }

    #[test]
    fn let_with_type_hint() {
        let source = r"let something: String = test;";

        let statements = parse_function_context(source);

        assert_eq!(statements,
            vec![
                Statement::LetExpression {
                    variable_binding: "something",
                    type_hint: Some("String"),
                    rhs: Expression::Identifier("test")
                }
            ]
        )
    }

    #[test]
    fn non_float_literals() {
        let source = r#"
            let a = true;
            let b = false;
            let c = 'a';
            let d = '\'';
            let e = '\\';
            let f = "something \" \t \r\n \u{26A7}";
            let g = 0;
            let h = 3;
        "#;

        let statements = dbg!(parse_function_context(source));

        assert_eq!(statements.len(), 8);
    }

    #[test]
    fn float_literals() {
        let source = r"
            let a = 1.3;
            let b = 0.3;
            let c = 1e3;
            let d = 10.2E-16;
        ";

        
        let statements = dbg!(parse_function_context(source));

        assert_eq!(statements.len(), 4);
    }
}