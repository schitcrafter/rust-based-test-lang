use std::{collections::HashMap, hash::Hash, iter};

use crate::ast::*;

pub fn resolve_names(ast: &mut Vec<OuterExpression>) {
    let mut resolver = NameResolutionVisitor::new();
    resolver.start_visiting(ast);
}

#[derive(Debug)]
pub struct Rib<T> {
    pub node_ref_map: FxHashMap<T, Ref>,
    pub rib_type: RibType,
}

impl<T: Eq + Hash> Rib<T> {
    pub fn new_with_single_entry(rib_type: RibType, key: T, node_id: Ref) -> Rib<T> {
        Rib {
            rib_type,
            node_ref_map: iter::once((key, node_id)).collect()
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RibType {
    Module,
    Function,
    Local,
    Block,
    /// Struct or enum
    Container,
}

///TODO: Use string intering - that way we don't need to copy and compare
/// the strings here, but just compare the interned indexes.
#[derive(Debug)]
pub struct NameResolutionVisitor {
    type_rib_stack: Vec<Rib<String>>,
    ident_rib_stack: Vec<Rib<String>>,
}

impl Default for NameResolutionVisitor {
    fn default() -> Self {
        Self::new()
    }
}

impl NameResolutionVisitor {
    pub fn new() -> Self {
        Self {
            type_rib_stack: vec![Rib { rib_type: RibType::Module, node_ref_map: Default::default() }],
            ident_rib_stack: vec![Rib { rib_type: RibType::Module, node_ref_map: Default::default() }]
        }
    }

    /// Collects all names defined in the outer expressions, and pushes ribs accordingly.
    /// Always pushes type and ident ribs.
    /// For functions: Only pushes the function name, not the arguments.
    fn push_ribs_from_module(&mut self, exprs: &[OuterExpression]) {
        let mut type_rib_map = HashMap::new();
        let mut ident_rib_map = HashMap::new();

        use OuterExpression::*;
        for expr in exprs {
            let node_ref = expr.to_node_ref();
            if node_ref.is_none() {
                continue;
            }
            let node_ref = node_ref.unwrap();
            
            // Add to ident map
            if let Function { ident, .. } = expr {
                ident_rib_map.insert(
                    ident.inner().to_string(),
                    node_ref
                );
            }

            // Add to type map
            match expr {
                Struct { ident, .. } | Enum { ident, .. } => {
                    type_rib_map.insert(
                        ident.inner().to_string(),
                        node_ref
                    );
                },
                _ => {},
            };
        }

        let type_rib = Rib {
            node_ref_map: type_rib_map,
            rib_type: RibType::Module,
        };
        let ident_rib = Rib {
            node_ref_map: ident_rib_map,
            rib_type: RibType::Module,
        };

        self.type_rib_stack.push(type_rib);
        self.ident_rib_stack.push(ident_rib);
    }

    /// pushes a single ident rib
    fn push_ident_rib_from_fn_args(&mut self, args: &[FnArg]) {
        let mut ident_rib_map = HashMap::new();

        for FnArg { node_id, ident, ty: _ } in args {
            if ident_rib_map.contains_key(ident.inner()) {
                panic!("Argument names must be exclusive, found {:?} twice", ident.inner());
            } else {
                ident_rib_map.insert(ident.inner().to_string(), Ref::Local(*node_id));
            }
        }

        self.ident_rib_stack.push(Rib {
            node_ref_map: ident_rib_map,
            rib_type: RibType::Function
        });
    }
}

impl<'input> MutAstVisitor<'input> for NameResolutionVisitor {
    fn start_visiting(&mut self, ast: &mut Vec<OuterExpression<'input>>) {
        self.push_ribs_from_module(ast);

        for expr in ast {
            self.visit_outer_expression(expr);
        }
        
        self.type_rib_stack.pop();
        self.ident_rib_stack.pop();
    }

    fn visit_module(&mut self, node_id: &mut NodeId, ident: &mut Ident<'input>, inner: &mut Option<Vec<OuterExpression<'input>>>) {
        self.visit_nodeid(node_id);
        self.visit_ident(ident);

        if let Some(inner) = inner {
            self.push_ribs_from_module(inner);
            
            for expr in inner {
                self.visit_outer_expression(expr);
            }
            
            self.type_rib_stack.pop();
            self.ident_rib_stack.pop();
        }
    }

    /// Pushes an ident rib containing all the arguments for the inner codeblock.
    /// The function name itself was pushed 
    fn visit_function(
            &mut self,
            node_id: &mut NodeId,
            ident: &mut Ident<'input>,
            arguments: &mut Vec<FnArg<'input>>,
            return_type: &mut Option<Path<'input>>,
            inner: &mut CodeBlock<'input>
        ) {
        self.visit_nodeid(node_id);
        self.visit_ident(ident);
        
        // Collect function arguments and push a new ident rib for them
        
        for arg in arguments.iter_mut() {
            self.visit_fn_arg(arg);
        }

        if let Some(ty) = return_type {
            self.visit_type_path(ty);
        }
        
        self.push_ident_rib_from_fn_args(arguments);
        self.visit_codeblock(inner);

        debug_assert_eq!(self.ident_rib_stack.last().map(|rib| rib.rib_type), Some(RibType::Function));

        // Pop function rib
        self.ident_rib_stack.pop();
    }

    fn visit_statement(&mut self, stmt: &mut Statement<'input>) {
        use Statement::*;
        match stmt {
            LetExpression { node_id, variable_binding, type_hint, rhs } => {
                self.visit_nodeid(node_id);
                self.visit_ident(variable_binding);
                if let Some(ty) = type_hint {
                    self.visit_type_path(ty);
                }

                self.ident_rib_stack.push(
                    Rib::new_with_single_entry(RibType::Local, variable_binding.inner().to_string(), Ref::Local(*node_id))
                );

                self.visit_expression(rhs);
            }
            Expression(expr) => self.visit_expression(expr),
            WhileBlock { condition, block } => {
                self.visit_expression(condition);
                self.visit_codeblock(block);
            }
            ForEachLoop { node_id, iterator_var_ident, iterator_expression, block } => {
                self.visit_ident(iterator_var_ident);
                self.visit_expression(iterator_expression);

                self.ident_rib_stack.push(
                    Rib::new_with_single_entry(RibType::Local, iterator_var_ident.inner().to_string(), Ref::Local(*node_id))
                );

                self.visit_codeblock(block);

                debug_assert_eq!(self.ident_rib_stack.last().map(|rib| rib.rib_type), Some(RibType::Local));
                self.ident_rib_stack.pop();
            }
        }
    }

    fn visit_expression(&mut self, expr: &mut Expression<'input>) {
        use Expression::*;
        match expr {
            Identifier(ident) => self.visit_ident_path(ident),
            BinOp { lhs, op: _, rhs } => {
                self.visit_expression(lhs);
                self.visit_expression(rhs);
            }
            UnaryOperator(_, inner_expr) => self.visit_expression(inner_expr),
            FunctionCall { fn_expr, arguments } => {
                self.visit_expression(fn_expr);
                for arg_expr in arguments {
                    self.visit_expression(arg_expr);
                }
            }
            Assignment { variable, rhs } => {
                self.visit_ident_path(variable);
                self.visit_expression(rhs);
            }
            IfElseBlock { if_condition, if_block, else_if_chain, else_block } => {
                self.visit_expression(if_condition);
                self.visit_codeblock(if_block);

                for (expr, block) in else_if_chain {
                    self.visit_expression(expr);
                    self.visit_codeblock(block);
                }

                if let Some(block) = else_block {
                    self.visit_codeblock(block);
                }
            }
            FieldAccess { lhs, rhs: _ } => {
                self.visit_expression(lhs);
                // NOTE: don't visit the right-hand side, as it's a field of a struct.
            }
            StructConstructor { struct_name, fields } => {
                self.visit_type_path(struct_name);
                for (struct_field, local) in fields {
                    self.visit_ident_path(struct_field);
                    self.visit_ident_path(local);
                }
            }
            Integer(..) | Float(..) | StringLiteral(..) | Boolean(..)
            | Character(..) => { }
        }
    }

    fn visit_codeblock(&mut self, codeblock: &mut CodeBlock<'input>) {
        self.ident_rib_stack.push(Rib {
            rib_type: RibType::Block,
            node_ref_map: HashMap::new()
        });

        for stmt in &mut codeblock.0 {
            self.visit_statement(stmt);
        }

        // Pop all ident ribs that were pushed as a result of let assignments.
        while let Some(last_rib) = self.ident_rib_stack.last() {
            if last_rib.rib_type == RibType::Local {
                self.ident_rib_stack.pop();
            } else {
                debug_assert_eq!(last_rib.rib_type, RibType::Block);
                break;
            }
        }

        // Pop block rib
        self.ident_rib_stack.pop();
    }

    /// Resolves this ident path, setting its NodeId reference
    fn visit_ident_path(&mut self, ident_path: &mut Path<'input>) {
        let Path { ident, node_ref } = ident_path;

        if let Ok(primitive) = ident.parse() {
            *node_ref = Some(Ref::PrimitiveType(primitive));
        } else {
            for rib in self.ident_rib_stack.iter().rev() {
                if let Some(resolved_node_id) = rib.node_ref_map.get(*ident) {
                    *node_ref = Some(*resolved_node_id);
                    break;
                }
            }
        }

        if node_ref.is_none() {
            eprintln!("Couldn't find identifier {ident:?}");
        }
    }
    
    fn visit_type_path(&mut self, type_path: &mut Path<'input>) {
        let Path { ident, node_ref } = type_path;

        if let Ok(primitive) = ident.parse() {
            *node_ref = Some(Ref::PrimitiveType(primitive));
        } else {
            for rib in self.type_rib_stack.iter().rev() {
                if let Some(resolved_node_id) = rib.node_ref_map.get(*ident) {
                    *node_ref = Some(*resolved_node_id);
                    break;
                }
            }
        }

        if node_ref.is_none() {
            eprintln!("Couldn't find type {ident:?}");
        }
    }
}

#[cfg(test)]
mod tests {
    use similar_asserts::assert_eq;
    use crate::parser::{module_context::parse_module_context_str, nodeid_visitor::initialise_nodeids};
    use super::*;

    #[test]
    fn locals() {
        let source = r#"
            fn function(arg: u64) {
                let smth = 3;
                let other = smth;
                let third = arg;
            }
        "#;

        let mut outer_exprs = parse_module_context_str(source);

        let expected = vec![
            OuterExpression::Function {
                node_id: 1.into(),
                ident: "function".into(),
                arguments: vec![FnArg {
                    ident: Ident::new("arg"),
                    ty: Path::new_prim("u64"),
                    node_id: 2.into()
                }],
                return_type: None,
                inner: CodeBlock(vec![
                    Statement::LetExpression {
                        node_id: 3.into(),
                        variable_binding: "smth".into(),
                        type_hint: None,
                        rhs: Expression::Integer(3)
                    },
                    Statement::LetExpression {
                        node_id: 4.into(),
                        variable_binding: "other".into(),
                        type_hint: None,
                        rhs: Expression::Identifier(Path::new_with_ref("smth", Ref::Local(3.into())))
                    },
                    Statement::LetExpression {
                        node_id: 5.into(),
                        variable_binding: "third".into(),
                        type_hint: None,
                        rhs: Expression::Identifier(Path::new_with_ref("arg", Ref::Local(2.into())))
                    }
                ])
            }
        ];

        initialise_nodeids(&mut outer_exprs);

        resolve_names(&mut outer_exprs);

        assert_eq!(expected, outer_exprs);
    }

    #[test]
    fn recursion() {
        let source = r#"
            fn function(arg: u64) {
                function(arg + 1);
            }
        "#;

        let mut outer_exprs = parse_module_context_str(source);

        let expected = vec![
            OuterExpression::Function {
                node_id: 1.into(),
                ident: "function".into(),
                arguments: vec![FnArg {
                    ident: Ident::new("arg"),
                    ty: Path::new_prim("u64"),
                    node_id: 2.into()
                }],
                return_type: None,
                inner: CodeBlock(vec![
                    Statement::Expression(
                        Expression::FunctionCall {
                            fn_expr: Box::new(Expression::Identifier(Path::new_with_ref("function", Ref::Function(1.into())))),
                            arguments: vec![
                                Expression::BinOp {
                                    lhs: Box::new(Expression::Identifier(Path::new_with_ref("arg", Ref::Local(2.into())))),
                                    op: BiOperator::Add,
                                    rhs: Box::new(Expression::Integer(1))
                                }
                            ]
                        }
                    )
                ])
            }
        ];

        initialise_nodeids(&mut outer_exprs);

        resolve_names(&mut outer_exprs);

        assert_eq!(expected, outer_exprs);
    }

    
    #[test]
    fn blocks() {
        let source = r#"
            fn function() {
                let a = 1;
                if true {
                    let a = 2;
                    a;
                }
                a;
            }
        "#;

        let mut outer_exprs = parse_module_context_str(source);

        let expected = vec![
            OuterExpression::Function {
                node_id: 1.into(),
                ident: "function".into(),
                arguments: vec![],
                return_type: None,
                inner: CodeBlock(vec![
                    Statement::LetExpression {
                        node_id: 2.into(),
                        variable_binding: "a".into(),
                        type_hint: None,
                        rhs: Expression::Integer(1),
                    },
                    Statement::Expression(Expression::IfElseBlock {
                        if_condition: Box::new(Expression::Boolean(true)),
                        if_block: CodeBlock(vec![
                                Statement::LetExpression {
                                    node_id: 3.into(),
                                    variable_binding: "a".into(),
                                    type_hint: None,
                                    rhs: Expression::Integer(2),
                                },
                                Statement::Expression(Expression::Identifier(Path::new_with_ref("a", Ref::Local(3.into())))),
                            ]),
                        else_if_chain: vec![],
                        else_block: None,
                    }),
                    Statement::Expression(Expression::Identifier(
                        Path::new_with_ref("a", Ref::Local(2.into()))
                    ))
                ])
            }
        ];

        initialise_nodeids(&mut outer_exprs);

        resolve_names(&mut outer_exprs);

        assert_eq!(expected, outer_exprs);
    }

    #[test]
    fn for_each_loop() {
        let source = r#"
            fn function() {
                for a in some_list {
                    print(a);
                }
                print(a);
            }
        "#;

        let mut outer_exprs = parse_module_context_str(source);

        let expected = vec![
            OuterExpression::Function {
                node_id: 1.into(),
                ident: "function".into(),
                arguments: vec![],
                return_type: None,
                inner: CodeBlock(vec![
                    Statement::ForEachLoop {
                        node_id: 2.into(),
                        iterator_var_ident: "a".into(),
                        iterator_expression: Expression::Identifier(Path::new("some_list")),
                        block: CodeBlock(vec![
                            Statement::Expression(
                                Expression::FunctionCall {
                                    fn_expr: Box::new(Expression::Identifier(
                                        Path::new("print")
                                    )),
                                    arguments: vec![
                                        Expression::Identifier(Path::new_with_ref("a", Ref::Local(2.into())))
                                    ]
                                }
                            )
                        ])
                    },
                    Statement::Expression(
                        Expression::FunctionCall {
                            fn_expr: Box::new(Expression::Identifier(
                                Path::new("print")
                            )),
                            arguments: vec![
                                Expression::Identifier(Path::new("a"))
                            ]
                        }
                    )
                ])
            }
        ];

        initialise_nodeids(&mut outer_exprs);

        resolve_names(&mut outer_exprs);

        assert_eq!(expected, outer_exprs);
    }
}