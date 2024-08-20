use crate::ast::*;

pub fn initialise_nodeids(ast: &mut Vec<OuterExpression>) {
    let mut visitor = NodeIdVisitor::new();
    visitor.start_visiting(ast);
}

#[derive(Debug, PartialEq)]
pub struct NodeIdVisitor {
    current_node_id: NodeId,
}

impl NodeIdVisitor {
    pub fn new() -> NodeIdVisitor {
        NodeIdVisitor {
            current_node_id: NodeId::FIRST_NODEID
        }
    }
}

impl Default for NodeIdVisitor {
    fn default() -> Self {
        Self::new()
    }
}

impl<'input> MutAstVisitor<'input> for NodeIdVisitor {
    fn visit_nodeid(&mut self, node_id: &mut NodeId) {
        *node_id = self.current_node_id;
        self.current_node_id = self.current_node_id.next();
    }

    // Do not visit ident or type paths; the nodeid's in them
    // point to other nodeid's, which will be resolved in
    // name resolution
    fn visit_ident_path(&mut self, _ident: &mut Path<'input>) { }
    fn visit_type_path(&mut self, _type_path: &mut Path<'input>) { }
}

#[cfg(test)]
mod tests {
    use similar_asserts::assert_eq;
    use crate::parser::module_context::parse_module_context_str;

    use super::*;

    #[test]
    fn nodeid_visitor() {
        let source = r#"
            struct Struct;
            fn function(arg: u64) {
                let smth = 3;
                let other = smth;
            }
        "#;

        let mut outer_exprs = parse_module_context_str(source);


        let mut visitor = NodeIdVisitor::new();
        visitor.start_visiting(&mut outer_exprs);

        let expected = vec![
            OuterExpression::Struct {
                node_id: 1.into(),
                ident: "Struct".into(),
                fields: Fields::Empty
            },
            OuterExpression::Function {
                node_id: 2.into(),
                ident: "function".into(),
                arguments: vec![FnArg {
                    ident: "arg".into(),
                    ty: "u64".into(),
                    node_id: 3.into()
                }],
                return_type: None,
                inner: CodeBlock(vec![
                    Statement::LetExpression {
                        node_id: 4.into(),
                        variable_binding: "smth".into(),
                        type_hint: None,
                        rhs: Expression::Integer(3)
                    },
                    Statement::LetExpression {
                        node_id: 5.into(),
                        variable_binding: "other".into(),
                        type_hint: None,
                        rhs: Expression::Identifier("smth".into())
                    }
                ])
            }
        ];

        assert_eq!(expected, outer_exprs);
    }
}
