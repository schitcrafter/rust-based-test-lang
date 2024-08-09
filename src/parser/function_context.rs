//! Parses anything inside a function, i.e.
//! Arithmetic, variable bindings, function calls, etc.

use std::sync::LazyLock;

use pest::{iterators::{Pair, Pairs}, pratt_parser::PrattParser, Parser};

use ast::*;

use super::{PestParser, Rule};

pub mod ast {

    #[derive(Debug, PartialEq)]
    pub struct CodeBlock<'input>(pub Vec<Statement<'input>>);

    #[derive(Debug, PartialEq)]
    pub enum Statement<'input> {
        LetExpression {
            variable_binding: &'input str,
            type_hint: Option<&'input str>,
            rhs: Expression<'input>
        },
        Expression(Expression<'input>),
        IfElseBlock {
            if_condition: Expression<'input>,
            if_block: CodeBlock<'input>,
            // condition, block
            else_if_chain: Vec<(Expression<'input>, CodeBlock<'input>)>,
            else_block: Option<CodeBlock<'input>>,
        },
        WhileBlock {
            condition: Expression<'input>,
            block: CodeBlock<'input>,
        },
        /// `for a in b` { ... }``
        ForEachLoop {
            iterator_var_ident: &'input str,
            iterator_expression: Expression<'input>,
            block: CodeBlock<'input>,
        }
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
        },
        Assignment {
            variable: &'input str,
            rhs: Box<Expression<'input>>,
        },
    }

    #[derive(Debug, PartialEq)]
    pub enum BiOperator {
        Add,
        Subtract,
        Multiply,
        Divide,
        Remainder,
        And,
        Or,
        LessThan,
        LessThanEq,
        GreaterThan,
        GreaterThanEq,
        Eq,
        NotEq,
    }

    #[derive(Debug, PartialEq)]
    pub enum UnaryOperator {
        Minus,
        Not,
    }
}

const OPERATOR_PARSER: LazyLock<PrattParser<Rule>> = LazyLock::new(|| {
    use pest::pratt_parser::{Assoc::*, Op};
    use Rule::*;

    // Precedence is defined lowest to highest
    PrattParser::new()
        .op(Op::infix(and, Left) | Op::infix(or, Left))
        .op(Op::infix(add, Left) | Op::infix(subtract, Left))
        .op(Op::infix(multiply, Left) | Op::infix(divide, Left) | Op::infix(remainder, Left))
        .op(Op::infix(less_than, Left) | Op::infix(less_than_equals, Left)
            | Op::infix(greater_than, Left) | Op::infix(greater_than_equals, Left)
            | Op::infix(equals, Left) | Op::infix(not_equals, Left))        
        .op(Op::prefix(unary_minus) | Op::prefix(not))
        .op(Op::postfix(function_call))
});

pub fn parse_function_str<'input>(source: &'input str) -> Vec<Statement> {
    let pairs = PestParser::parse(Rule::function_context, source)
            .expect("Parsing failed");

    // let pairs = dbg!(pairs);

    parse_function_context(pairs)
}

pub fn parse_function_context(pairs: Pairs<Rule>) -> Vec<Statement> {
    let mut statements = vec![];

    for pair in pairs {
        let rule = pair.as_rule();
        let mut inner = pair.into_inner();
    
        let statement = match rule {
            Rule::if_else_block => {
                let if_condition = inner.next().unwrap();
                let if_condition = parse_expression(if_condition.into_inner());
                let if_block = inner.next().unwrap();
                let if_block = parse_function_context(if_block.into_inner());

                let mut else_if_chains = vec![];

                while inner.peek().map(|pair| pair.as_rule()) == Some(Rule::else_if_chain) {
                    // Found another else if chain
                    let mut chain = inner.next().unwrap().into_inner();
                    let chain_cond = parse_expression(chain.next().unwrap().into_inner());
                    let chain_block = parse_function_context(chain.next().unwrap().into_inner());

                    else_if_chains.push((chain_cond, CodeBlock(chain_block)))
                }

                let else_block = if inner.peek().map(|pair| pair.as_rule()) == Some(Rule::else_block) {
                    let mut else_rule_inner = inner.next().unwrap().into_inner();
                    let else_code_block_rule = else_rule_inner.next().unwrap();
                    let else_statements = parse_function_context(else_code_block_rule.into_inner());
                    Some(CodeBlock(else_statements))
                } else {
                    None
                };

                Statement::IfElseBlock {
                    if_condition,
                    if_block: CodeBlock(if_block),
                    else_if_chain: else_if_chains,
                    else_block
                }
            }
            Rule::while_block => {
                let condition = inner.next().unwrap();
                let condition = parse_expression(condition.into_inner());
                let block = inner.next().unwrap();
                let block = parse_function_context(block.into_inner());

                Statement::WhileBlock { condition, block: CodeBlock(block) }
            }
            Rule::for_each_loop => {
                let iterator_var_ident = inner.next().unwrap().as_str();

                let iterator_expression = inner.next().unwrap();
                let iterator_expression = parse_expression(iterator_expression.into_inner());

                let block = inner.next().unwrap();
                let block = parse_function_context(block.into_inner());

                Statement::ForEachLoop {
                    iterator_var_ident,
                    iterator_expression,
                    block: CodeBlock(block)
                }
            }
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
            }
            Rule::expression => Statement::Expression(parse_expression(inner)),
            Rule::EOI => continue,
            rule => unreachable!("Expected let/if-else/while/... statement, expression, found {rule:?}")
        };

        statements.push(statement);
    }

    statements
}

pub fn parse_expression<'input>(mut pairs: Pairs<'input, Rule>) -> Expression<'input> {
    let inner_expr = pairs.next().unwrap();
    match inner_expr.as_rule() {
        Rule::operator_expression => OPERATOR_PARSER
            .map_primary(parse_primary_expression)
            .map_infix(parse_binop_expression)
            .map_prefix(|op, rhs| {
                let op = match op.as_rule() {
                    Rule::unary_minus => UnaryOperator::Minus,
                    Rule::not => UnaryOperator::Not,
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
            .parse(inner_expr.into_inner()),
        Rule::assignment => {
            let mut inner = inner_expr.into_inner(); 
            let variable = inner.next().unwrap().as_str();
            let rhs = inner.next().unwrap().into_inner();
            let rhs = parse_expression(rhs);
            Expression::Assignment { variable, rhs: Box::new(rhs) }
        }
        rule => unreachable!("Expected inner expression, found '{rule:?}'")
    }
}

fn parse_primary_expression<'input>(primary: Pair<'input, Rule>) -> Expression<'input> {
    match primary.as_rule() {
        Rule::identifier => Expression::Identifier(primary.as_str()),
        Rule::integer => Expression::Integer(primary.as_str().parse().unwrap()),
        Rule::float => Expression::Float(primary.as_str().parse().unwrap()),
        Rule::char_literal => {
            let inner = primary.into_inner().next()
                .expect("Char literal didn't have an inner rule");
            Expression::Character(unescape_char(inner.as_str()))
        },
        Rule::string_literal => {
            let inner = primary.into_inner().next()
                .expect("String literal didn't have an inner rule");
            Expression::StringLiteral(unescape_string(inner.as_str()))
        },
        Rule::bool_true => Expression::Boolean(true),
        Rule::bool_false => Expression::Boolean(false),
        Rule::expression => parse_expression(primary.into_inner()),
        rule => unreachable!("Expr::parse expected atom, found {rule:?}")
    }
}

fn parse_binop_expression<'input>(lhs: Expression<'input>, op: Pair<'input, Rule>, rhs: Expression<'input>) -> Expression<'input> {
    use BiOperator::*;
    let op = match op.as_rule() {
        Rule::add => Add,
        Rule::subtract => Subtract,
        Rule::multiply => Multiply,
        Rule::divide => Divide,
        Rule::remainder => Remainder,
        Rule::and => And,
        Rule::or => Or,
        Rule::less_than => LessThan,
        Rule::less_than_equals => LessThanEq,
        Rule::greater_than => GreaterThan,
        Rule::greater_than_equals => GreaterThanEq,
        Rule::equals => Eq,
        Rule::not_equals => NotEq,
        rule => unreachable!("Expr::parse expected infix expression, found {rule:?}")
    };

    Expression::BinOp { lhs: Box::new(lhs), op, rhs: Box::new(rhs) }
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
        let source = "
            let smth = 3;
            smth = 5;
        ";

        let statements = parse_function_str(source);

        assert_eq!(statements, vec![
            Statement::LetExpression {
                variable_binding: "smth",
                type_hint: None,
                rhs: Expression::Integer(3)
            },
            Statement::Expression(Expression::Assignment {
                variable: "smth",
                rhs: Box::new(Expression::Integer(5))
            })
        ]);
    }

    #[test]
    fn expression_complex_arithmetic() {
        let source = "(3+4) * 17 / -3";

        
        let pairs = PestParser::parse(Rule::expression, source)
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
        
        let statements = parse_function_str(source);

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

        let second_args = vec![2, 3, 4].into_iter()
            .map(Expression::Integer)
            .collect();

        let third_args = vec![2, 4].into_iter()
            .map(Expression::Integer)
            .collect();

        let expected = vec![
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
        ];

        let statements = parse_function_str(source);

        assert_eq!(statements, expected);
    }

    #[test]
    fn let_with_type_hint() {
        let source = r"let something: String = test;";

        let statements = parse_function_str(source);

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

        let statements = dbg!(parse_function_str(source));

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

        
        let statements = dbg!(parse_function_str(source));

        assert_eq!(statements.len(), 4);
    }

    #[test]
    fn boolean_expressions() {
        let source = r"
            true || false;
            a || b || c;
            !((a + b) && false);
        ";

        use Expression::*;
        use BiOperator::*;
        use super::ast::UnaryOperator::*;

        let expected = vec![
            BinOp {
                lhs: Box::new(Boolean(true)),
                op: BiOperator::Or,
                rhs: Box::new(Boolean(false))
            },
            BinOp {
                lhs: Box::new(BinOp {
                    lhs: Box::new(Identifier("a")),
                    op: Or,
                    rhs: Box::new(Identifier("b"))
                }),
                op: Or,
                rhs: Box::new(Identifier("c"))
            },
            UnaryOperator(
                Not,
                Box::new(BinOp {
                    lhs: Box::new(BinOp {
                        lhs: Box::new(Identifier("a")),
                        op: BiOperator::Add,
                        rhs: Box::new(Identifier("b"))
                    }),
                    op: BiOperator::And,
                    rhs: Box::new(Boolean(false))
                })
            )
        ];
        let expected: Vec<_> = expected.into_iter().map(Statement::Expression).collect();
        
        let statements = dbg!(parse_function_str(source));

        assert_eq!(statements, expected);
    }

    #[test]
    fn comparisons() {
        let source = r#"
            1 <= 2;
            "one" != "two";
            1 <= 2 <= 3;
            (3 < 4) == true;
        "#;

        use Expression::*;
        use BiOperator::*;

        let expected = vec![
            BinOp {
                lhs: Box::new(Integer(1)),
                op: LessThanEq,
                rhs: Box::new(Integer(2))
            },
            BinOp {
                lhs: Box::new(StringLiteral("one".to_string())),
                op: NotEq,
                rhs: Box::new(StringLiteral("two".to_string()))
            },
            BinOp {
                lhs: Box::new(BinOp {
                        lhs: Box::new(Integer(1)),
                        op: LessThanEq,
                        rhs: Box::new(Integer(2))
                    },),
                op: LessThanEq,
                rhs: Box::new(Integer(3))
            },
            BinOp {
                lhs: Box::new(BinOp {
                    lhs: Box::new(Integer(3)),
                    op: LessThan,
                    rhs: Box::new(Integer(4))
                }),
                op: Eq,
                rhs: Box::new(Boolean(true))
            },
        ];
        let expected: Vec<_> = expected.into_iter().map(Statement::Expression).collect();
        
        let statements = dbg!(parse_function_str(source));

        assert_eq!(statements, expected);
    }

    #[test]
    fn if_blocks() {
        let source = r#"
        if true { }
        if a == 3 { } else { "c"; }
        if a { } else if c { }
        if a { } else if c { } else { }
        "#;

        use Statement::*;
        use super::ast::Expression::*;
        use BiOperator::*;

        let expected = vec![
            IfElseBlock {
                if_condition: Boolean(true),
                if_block: CodeBlock(vec![]),
                else_if_chain: vec![],
                else_block: None
            },
            IfElseBlock {
                if_condition: BinOp { lhs: Box::new(Identifier("a")), op: Eq, rhs: Box::new(Integer(3)) },
                if_block: CodeBlock(vec![]),
                else_if_chain: vec![],
                else_block: Some(CodeBlock(vec![Expression(StringLiteral("c".to_string()))]))
            },
            IfElseBlock {
                if_condition: Identifier("a"),
                if_block: CodeBlock(vec![]),
                else_if_chain: vec![
                    (Identifier("c"), CodeBlock(vec![]))
                ],
                else_block: None
            },
            IfElseBlock {
                if_condition: Identifier("a"),
                if_block: CodeBlock(vec![]),
                else_if_chain: vec![
                    (Identifier("c"), CodeBlock(vec![]))
                ],
                else_block: Some(CodeBlock(vec![]))
            }
        ];
        
        let statements = dbg!(parse_function_str(source));

        assert_eq!(statements, expected);
    }

    
    #[test]
    fn while_blocks() {
        let source = r#"
            while a == true {
                set_a();
            }
        "#;

        use Statement::*;
        use super::ast::Expression::*;
        use BiOperator::*;

        let expected = vec![
            WhileBlock {
                condition: BinOp { lhs: Box::new(Identifier("a")), op: Eq, rhs: Box::new(Boolean(true)) },
                block: CodeBlock(vec![
                    Statement::Expression(FunctionCall { fn_expr: Box::new(Identifier("set_a")), arguments: vec![] })
                ])
            }
        ];
        
        let statements = dbg!(parse_function_str(source));

        assert_eq!(statements, expected);
    }

    #[test]
    fn for_each_loops() {
        let source = r#"
            for a in some_list {
                println(a);
            }
        "#;

        use Statement::*;
        use super::ast::Expression::*;

        let expected = vec![
            ForEachLoop {
                iterator_var_ident: "a", 
                iterator_expression: Identifier("some_list"),
                block: CodeBlock(vec![
                    Statement::Expression(FunctionCall {
                        fn_expr: Box::new(Identifier("println")),
                        arguments: vec![Identifier("a")]
                    })
                ])
            }
        ];
        
        let statements = dbg!(parse_function_str(source));

        assert_eq!(statements, expected);
    }
}