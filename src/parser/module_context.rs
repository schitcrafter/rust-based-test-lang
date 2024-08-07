//! parses anything at a module context,
//! i.e. functions, structs, enums,
//! traits, other modules etc.

use pest::{iterators::{Pair, Pairs}, Parser};
use pest_derive::Parser;

use ast::*;

pub mod ast {
    use crate::parser::function_context;

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
            inner: Vec<function_context::ast::Statement<'input>>
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

#[derive(Parser)]
#[grammar = "parser/base_rules.pest"]
#[grammar = "parser/function_context.pest"]
#[grammar = "parser/module_context.pest"]
pub struct ModuleContextParser;

pub fn parse_module_context<'input>(source: &'input str) -> Vec<ModuleElement<'input>> {
    let rules = ModuleContextParser::parse(Rule::module_context, source)
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
}
