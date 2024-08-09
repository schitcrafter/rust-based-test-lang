//! parses anything at a module context,
//! i.e. functions, structs, enums,
//! traits, other modules etc.

use pest::{iterators::Pair, Parser};

use ast::*;

use super::{function_context::{ast::CodeBlock, parse_function_context}, PestParser, Rule};

pub mod ast {
    use crate::parser::function_context::ast::CodeBlock;

    #[derive(Debug, PartialEq)]
    pub enum ModuleElement<'input> {
        Struct {
            ident: &'input str,
            fields: Fields<'input>,
        },
        Enum {
            ident: &'input str,
            variants: Vec<(&'input str, Fields<'input>)>,
        },
        Function {
            ident: &'input str,
            arguments: Vec<(&'input str, &'input str)>,
            return_type: Option<&'input str>,
            inner: CodeBlock<'input>,
        },
        ModuleDefinition {
            ident: &'input str,
            inner: Vec<ModuleElement<'input>>,
        },
        // TODO:
        StaticElement,
        ConstElement,
        Trait,
        ImplBlock,
    }

    #[derive(Debug, PartialEq)]
    /// used anytime we either have nothing, or tuple-like values, or fields
    pub enum Fields<'input> {
        Empty,
        TupleLike(Vec<&'input str>),
        StructLike(Vec<(&'input str, &'input str)>),
    }
}

pub fn parse_module_context<'input>(source: &'input str) -> Vec<ModuleElement<'input>> {
    let rules = PestParser::parse(Rule::module_context, source)
        .expect("Couldn't parse module context");

    let mut module_elements = vec![];

    for pair in rules {
        let rule = pair.as_rule();
        let mut inner = pair.into_inner();

        let module_element = match rule {
            Rule::r#struct => {
                let ident = inner.next().unwrap().as_str();

                let maybe_fields = inner.next();
                let fields = parse_all_fields(maybe_fields);
                ModuleElement::Struct { ident, fields }
            }
            Rule::r#enum => {
                let ident = inner.next().unwrap().as_str();
                
                let variants = inner.map(parse_enum_variant).collect();

                ModuleElement::Enum { ident, variants }
            }
            Rule::function => {
                let ident = inner.next().unwrap().as_str();
                
                let arguments_pairs = inner.next().unwrap().into_inner();

                let mut arguments = vec![];

                for pair in arguments_pairs {
                    let mut arg_inner = pair.into_inner();
                    let arg_ident = arg_inner.next().unwrap().as_str();
                    let arg_type = arg_inner.next().unwrap();
                    let arg_type = arg_type.into_inner().next().unwrap().as_str();

                    arguments.push((arg_ident, arg_type));
                }

                let return_type = if inner.peek().map(|pair| pair.as_rule()) == Some(Rule::function_return_type) {
                    let return_type_rule = inner.next().unwrap();
                    Some(return_type_rule.into_inner().next().unwrap().as_str())
                } else {
                    None
                };

                let code_block = inner.next().unwrap();
                let code_block = parse_function_context(code_block.into_inner());

                ModuleElement::Function {
                    ident,
                    arguments,
                    return_type,
                    inner: CodeBlock(code_block)
                }
            }
            rule => unreachable!("Encountered unexpected rule {rule:?} in module context")
        };
        module_elements.push(module_element);
    }

    module_elements
}

/// Parses missing fields (None), tuple-like fields, and struct-like fields
fn parse_all_fields(maybe_fields: Option<Pair<Rule>>) -> Fields {
    match maybe_fields.as_ref().map(|pair| pair.as_rule()) {
        None => Fields::Empty,
        Some(Rule::struct_fields_tuple) => parse_tuple_like_fields(maybe_fields.unwrap()),
        Some(Rule::struct_fields_normal) => parse_struct_like_fields(maybe_fields.unwrap()),
        rule => unreachable!("Unexpected rule inside struct: {rule:?}")
    }
}

fn parse_tuple_like_fields<'input>(tuple_like: Pair<'input, Rule>) -> Fields<'input> {
    let types = tuple_like.into_inner()
        .map(|pair| pair.as_str())
        .collect();

    Fields::TupleLike(types)
}

fn parse_struct_like_fields<'input>(struct_like: Pair<'input, Rule>) -> Fields<'input> {
    let fields = struct_like.into_inner()
        .map(|pair| {
            // pair here is a typed_field
            let mut inner = pair.into_inner();
            let ident = inner.next().unwrap().as_str();
            let type_hint = inner.next().unwrap();
            let type_ident = type_hint.into_inner().next().unwrap();

            (ident, type_ident.as_str())
        })
        .collect();

    Fields::StructLike(fields)
}

fn parse_enum_variant<'input>(variant: Pair<'input, Rule>) -> (&str, Fields) {
    let mut inner = variant.into_inner();
    let ident = inner.next().unwrap().as_str();
    let maybe_fields = inner.next();

    (ident, parse_all_fields(maybe_fields))
}

#[cfg(test)]
mod tests {
    use crate::parser::function_context::ast::CodeBlock;

    use super::*;

    #[test]
    fn struct_definition() {
        let source = r"
            struct SomeStruct;
            struct SomeOtherStruct(u64);
            struct SomeThirdStruct {
                field: u64,
            }
        ";

        let expected = vec![
            ModuleElement::Struct { ident: "SomeStruct", fields: Fields::Empty },
            ModuleElement::Struct { ident: "SomeOtherStruct", fields: Fields::TupleLike(vec!["u64"]) },
            ModuleElement::Struct { ident: "SomeThirdStruct", fields: Fields::StructLike(vec![("field", "u64")]) }
        ];

        let output = dbg!(parse_module_context(source));
        assert_eq!(output, expected);
    }

    #[test]
    fn enum_definition() {
        let source = r"
            enum SomeEnum {}
            enum SomeOtherEnum {
                EmptyVariant,
                TupleLikeVariant(u64, u32, f32,),
                StructLikeVariant {
                    field: u64,
                    other: String,
                }
            }
        ";
        
        let expected = vec![
            ModuleElement::Enum { ident: "SomeEnum", variants: vec![] },
            ModuleElement::Enum { ident: "SomeOtherEnum", variants:
                vec![
                    ("EmptyVariant", Fields::Empty),
                    ("TupleLikeVariant", Fields::TupleLike(vec!["u64", "u32", "f32"])),
                    ("StructLikeVariant", Fields::StructLike(
                        vec![("field", "u64"), ("other", "String")]
                    ))
                ]
            }
        ];

        let output = dbg!(parse_module_context(source));
        assert_eq!(output, expected);
    }

    #[test]
    fn function_definition() {
        let source = r"
        fn my_func() { }
        fn other_func(a: f64, b: f64) -> f64 { }
        ";

        use ModuleElement::*;
        
        let expected = vec![
            Function {
                ident: "my_func",
                arguments: vec![],
                return_type: None,
                inner: CodeBlock(vec![])
            },
            Function {
                ident: "other_func",
                arguments: vec![("a", "f64"), ("b", "f64")],
                return_type: Some("f64"),
                inner: CodeBlock(vec![])
            }
        ];

        let output = dbg!(parse_module_context(source));
        assert_eq!(output, expected);
    }
}
