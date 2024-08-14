//! parses anything at a module context,
//! i.e. functions, structs, enums,
//! traits, other modules etc.

use pest::{iterators::{Pair, Pairs}, Parser as _};
use super::Parser;

use crate::ast::*;

use super::{PestParser, Rule};

/// Helper function to parse a module context from a string
pub fn parse_module_context_str(source: &str) -> Vec<OuterExpression> {
    let parser = Parser::new(source);
    let rules = PestParser::parse(Rule::module_context, source)
        .expect("Couldn't parse module context");

    parser.parse_module_context(rules)
}

impl<'input> Parser<'input> {
    pub fn parse_module_context(&self, pairs: Pairs<'input, Rule>) -> Vec<OuterExpression<'input>> {
        let mut module_elements = vec![];

        for pair in pairs {
            let rule = pair.as_rule();
            let mut inner = pair.into_inner();

            let module_element: OuterExpression<'input> = match rule {
                Rule::r#struct => {
                    let ident = inner.next().unwrap().as_str().into();

                    let maybe_fields = inner.next();
                    let fields = self.parse_all_fields(maybe_fields);
                    OuterExpression::Struct { ident, fields, node_id: NodeId::NOT_YET_ASSIGNED }
                }
                Rule::r#enum => {
                    let ident = inner.next().unwrap().as_str().into();
                    
                    let variants = inner.map(|arg| self.parse_enum_variant(arg)).collect();

                    OuterExpression::Enum { ident, variants, node_id: NodeId::NOT_YET_ASSIGNED }
                }
                Rule::function => {
                    let ident = Ident::new(inner.next().unwrap().as_str());
                    
                    let arguments_pairs = inner.next().unwrap().into_inner();
                    
                    let mut arguments = vec![];

                    for pair in arguments_pairs {
                        let mut arg_inner = pair.into_inner();
                        let arg_ident = arg_inner.next().unwrap().as_str();
                        let arg_type = arg_inner.next().unwrap();
                        let arg_type = arg_type.into_inner().next().unwrap().as_str();

                        arguments.push(FnArg {
                            ident: arg_ident.into(),
                            ty: arg_type.into(),
                            node_id: Default::default()
                        });
                    }

                    let return_type = if inner.peek().map(|pair| pair.as_rule()) == Some(Rule::function_return_type) {
                        let return_type_rule = inner.next().unwrap();
                        let return_type_str = return_type_rule.into_inner().next().unwrap().as_str();
                        Some(Path::new(return_type_str))
                    } else {
                        None
                    };

                    let code_block = inner.next().unwrap();
                    let code_block = self.parse_function_context(code_block.into_inner());

                    OuterExpression::Function {
                        ident,
                        arguments,
                        return_type,
                        inner: CodeBlock(code_block),
                        node_id: NodeId::NOT_YET_ASSIGNED
                    }
                }
                Rule::module_definition => {
                    let ident = Ident::new(inner.next().unwrap().as_str());

                    let mod_inner = match inner.peek().map(|pair| pair.as_rule()) {
                        None => None,
                        Some(Rule::module_definition_inner) => {
                            let mod_inner = inner.next().unwrap();
                            Some(self.parse_module_context(mod_inner.into_inner()))
                        }
                        Some(rule) => unreachable!("Found unexpected rule '{rule:?}' inside a mod definition")
                    };

                    OuterExpression::ModuleDefinition { ident, inner: mod_inner, node_id: NodeId::NOT_YET_ASSIGNED }
                }
                rule => unreachable!("Encountered unexpected rule {rule:?} in module context")
            };
            module_elements.push(module_element);
        }

        module_elements
    }

    /// Parses missing fields (None), tuple-like fields, and struct-like fields
    fn parse_all_fields(&self, maybe_fields: Option<Pair<'input, Rule>>) -> Fields<'input> {
        match maybe_fields.as_ref().map(|pair| pair.as_rule()) {
            None => Fields::Empty,
            Some(Rule::struct_fields_tuple) => self.parse_tuple_like_fields(maybe_fields.unwrap()),
            Some(Rule::struct_fields_normal) => self.parse_struct_like_fields(maybe_fields.unwrap()),
            rule => unreachable!("Unexpected rule inside struct: {rule:?}")
        }
    }

    fn parse_tuple_like_fields(&self, tuple_like: Pair<'input, Rule>) -> Fields<'input> {
        let types = tuple_like.into_inner()
            .map(|pair| pair.as_str().into())
            .collect();

        Fields::TupleLike(types)
    }

    fn parse_struct_like_fields(&self, struct_like: Pair<'input, Rule>) -> Fields<'input> {
        let fields = struct_like.into_inner()
            .map(|pair| {
                // pair here is a typed_field
                let mut inner = pair.into_inner();
                let ident = Ident::new(inner.next().unwrap().as_str());
                let type_hint = inner.next().unwrap();
                let type_ident = type_hint.into_inner().next().unwrap();
                
                (ident, Path::new(type_ident.as_str()))
            })
            .collect();

        Fields::StructLike(fields)
    }

    fn parse_enum_variant(&self, variant: Pair<'input, Rule>) -> (Ty<'input>, Fields<'input>) {
        let mut inner = variant.into_inner();
        let ident = inner.next().unwrap().as_str();
        let maybe_fields = inner.next();

        (ident.into(), self.parse_all_fields(maybe_fields))
    }
}

#[cfg(test)]
mod tests {
    use similar_asserts::assert_eq;

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
            OuterExpression::Struct { ident: "SomeStruct".into(), fields: Fields::Empty, node_id: NodeId::NOT_YET_ASSIGNED, },
            OuterExpression::Struct { ident: "SomeOtherStruct".into(), fields: Fields::TupleLike(vec!["u64".into()]), node_id: NodeId::NOT_YET_ASSIGNED, },
            OuterExpression::Struct { ident: "SomeThirdStruct".into(), fields: Fields::StructLike(vec![("field".into(), "u64".into())]), node_id: NodeId::NOT_YET_ASSIGNED, }
        ];

        let output = dbg!(parse_module_context_str(source));
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
            OuterExpression::Enum { ident: "SomeEnum".into(), variants: vec![], node_id: NodeId::NOT_YET_ASSIGNED },
            OuterExpression::Enum { ident: "SomeOtherEnum".into(), node_id: NodeId::NOT_YET_ASSIGNED, variants:
                vec![
                    ("EmptyVariant".into(), Fields::Empty),
                    ("TupleLikeVariant".into(), Fields::TupleLike(
                        vec!["u64", "u32", "f32"].into_iter().map(Path::new).collect()
                    )),
                    ("StructLikeVariant".into(), Fields::StructLike(
                        vec![("field", "u64"), ("other", "String")]
                            .into_iter().map(|(ident, ty)| (ident.into(), ty.into())).collect()
                    ))
                ]
            }
        ];

        let output = dbg!(parse_module_context_str(source));
        assert_eq!(output, expected);
    }

    #[test]
    fn function_definition() {
        let source = r"
        fn my_func() { }
        fn other_func(a: f64, b: f64) -> f64 { }
        ";

        use OuterExpression::*;
        
        let expected = vec![
            Function {
                ident: "my_func".into(),
                arguments: vec![],
                return_type: None,
                inner: CodeBlock(vec![]),
                node_id: NodeId::NOT_YET_ASSIGNED
            },
            Function {
                ident: "other_func".into(),
                arguments: vec![
                    FnArg {
                        ident: "a".into(),
                        ty: "f64".into(),
                        node_id: Default::default()
                    },
                    FnArg {
                        ident: "b".into(),
                        ty: "f64".into(),
                        node_id: Default::default()
                    }],
                return_type: Some("f64".into()),
                inner: CodeBlock(vec![]),
                node_id: NodeId::NOT_YET_ASSIGNED
            }
        ];

        let output = dbg!(parse_module_context_str(source));
        assert_eq!(output, expected);
    }

    #[test]
    fn module_definition_with_fns() {
        let source = r"
            mod my_cool_mod {
                fn my_func() { }
                fn other_func(a: f64, b: f64) -> f64 { }
            }
            mod my_inner_mod;
            mod my_third_mod { }
        ";

        use OuterExpression::*;
        
        let fns = vec![
            Function {
                ident: "my_func".into(),
                arguments: vec![],
                return_type: None,
                inner: CodeBlock(vec![]),
                node_id: NodeId::NOT_YET_ASSIGNED
            },
            Function {
                ident: "other_func".into(),
                arguments: vec![
                    FnArg {
                        ident: "a".into(),
                        ty: "f64".into(),
                        node_id: Default::default()
                    },
                    FnArg {
                        ident: "b".into(),
                        ty: "f64".into(),
                        node_id: Default::default()
                    }],
                return_type: Some("f64".into()),
                inner: CodeBlock(vec![]),
                node_id: NodeId::NOT_YET_ASSIGNED
            }
        ];

        let expected = vec![
            ModuleDefinition {
                ident: "my_cool_mod".into(),
                inner: Some(fns),
                node_id: NodeId::NOT_YET_ASSIGNED
            },
            ModuleDefinition { ident: "my_inner_mod".into(), inner: None, node_id: NodeId::NOT_YET_ASSIGNED },
            ModuleDefinition { ident: "my_third_mod".into(), inner: Some(vec![]), node_id: NodeId::NOT_YET_ASSIGNED }
        ];

        let output = dbg!(parse_module_context_str(source));
        assert_eq!(output, expected);
    }
}
