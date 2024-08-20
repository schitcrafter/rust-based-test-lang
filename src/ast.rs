use std::{collections::HashMap, fmt::Debug};
use derive_more::{From, Into};

/// ID used to refer to individual nodes.
/// A node is everything that can be used
/// as an identifier/type/whatever in the code
#[derive(PartialEq, Hash, Clone, Copy, From)]
pub struct NodeId(u64);

impl NodeId {
    pub const NOT_YET_ASSIGNED: NodeId = NodeId(u64::MAX);
    pub const NAME_NOT_FOUND: NodeId = NodeId(0);
    pub const FIRST_NODEID: NodeId = NodeId(1);

    pub fn next(&self) -> NodeId {
        NodeId(self.0 + 1)
    }
}

impl Default for NodeId {
    fn default() -> Self {
        NodeId::NOT_YET_ASSIGNED
    }
}

impl Debug for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self == &NodeId::NOT_YET_ASSIGNED {
            f.write_str("NodeId::NOT_YET_ASSIGNED")
        } else if self == &NodeId::NAME_NOT_FOUND {
            f.write_str("NodeId::NAME_NOT_FOUND")
        } else {
            f.debug_tuple("NodeId")
                .field(&self.0)
                .finish()
        }
    }
}

// FIXME: Better hash here (FxHash)
pub type FxHashMap<K, V> = HashMap<K, V>;

/// Map of NodeId -> V
pub type NodeMap<V> = FxHashMap<NodeId, V>;

/// Only used when defining a new type, use
/// Path when referring
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Ty<'input> {
    ty: &'input str,
}

impl<'input> Ty<'input> {
    pub fn new(ident: &'input str) -> Ty<'input> {
        ident.into()
    }

    pub fn inner(&self) -> &'input str {
        self.ty
    }
}

impl<'input> From<&'input str> for Ty<'input> {
    fn from(ty: &'input str) -> Self {
        Self {
            ty,
        }
    }
}

/// An identifier to be used only when it's newly defined.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Ident<'input> {
    ident: &'input str,
}

impl<'input> Ident<'input> {
    pub fn new(ident: &'input str) -> Ident<'input> {
        ident.into()
    }

    pub fn inner(&self) -> &'input str {
        self.ident
    }
}

impl<'input> From<&'input str> for Ident<'input> {
    fn from(ident: &'input str) -> Self {
        Self {
            ident,
        }
    }
}

/// Provides information on what a reference points
/// to, as well as (if applicable) a NodeId.
/// Cannot point to a module, as it doesn't
/// make sense to refer to a module in code.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Ref {
    Struct(NodeId),
    Enum(NodeId),
    Local(NodeId),
    Function(NodeId),
    PrimitiveType, // TODO:
}

/// Used when we want to refer to another object,
/// like a struct or a local variable or whatever.
/// TODO: Replace node_id here with a Ref type,
/// which marks what exactly was referenced.
/// Reason for this is that primitive types
/// have no NodeId, and therefore can't
/// be referenced like this
#[derive(Debug, PartialEq)]
pub struct Path<'input> {
    pub ident: &'input str,
    /// The node this path is referring to
    pub node_ref: Option<Ref>,
}

impl<'input> Path<'input> {
    pub fn new(ident: &'input str) -> Path<'input> {
        ident.into()
    }

    pub fn new_with_ref(ident: &'input str, node_ref: Ref) -> Path<'input> {
        Path {
            ident,
            node_ref: Some(node_ref)
        }
    }
}

impl<'input> From<&'input str> for Path<'input> {
    fn from(ident: &'input str) -> Self {
        Self {
            ident,
            node_ref: Default::default()
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum OuterExpression<'input> {
    Struct {
        node_id: NodeId,
        ident: Ty<'input>,
        fields: Fields<'input>,
    },
    Enum {
        node_id: NodeId,
        ident: Ty<'input>,
        variants: Vec<(Ty<'input>, Fields<'input>)>,
    },
    Function {
        node_id: NodeId,
        ident: Ident<'input>,
        arguments: Vec<FnArg<'input>>,
        return_type: Option<Path<'input>>,
        inner: CodeBlock<'input>,
    },
    /// If inner is `None`, it was a module defined with a
    /// semicolon (`mod my_mod;`), if it is `Some` it
    /// was defined with curly brackets.
    ModuleDefinition {
        node_id: NodeId,
        ident: Ident<'input>,
        inner: Option<Vec<OuterExpression<'input>>>,
    },
    // TODO:
    StaticElement,
    ConstElement,
    Trait,
    ImplBlock,
}

impl<'input> OuterExpression<'input> {
    pub fn to_node_ref(&self) -> Option<Ref> {
        use OuterExpression::*;
        match self {
            Struct { node_id, .. } => Some(Ref::Struct(*node_id)),
            Enum { node_id, .. } => Some(Ref::Enum(*node_id)),
            Function { node_id, .. } => Some(Ref::Function(*node_id)),
            ModuleDefinition { .. } => None,
            StaticElement | ConstElement | Trait | ImplBlock => todo!()
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct FnArg<'input> {
    pub node_id: NodeId,
    pub ident: Ident<'input>,
    pub ty: Path<'input>
}

#[derive(Debug, PartialEq)]
/// used anytime we either have nothing, or tuple-like values, or fields
pub enum Fields<'input> {
    Empty,
    TupleLike(Vec<Path<'input>>),
    StructLike(Vec<(Ident<'input>, Path<'input>)>),
}

#[derive(Debug, PartialEq, From, Into)]
pub struct CodeBlock<'input>(pub Vec<Statement<'input>>);

#[derive(Debug, PartialEq)]
pub enum Statement<'input> {
    LetExpression {
        node_id: NodeId,
        variable_binding: Ident<'input>,
        type_hint: Option<Path<'input>>,
        rhs: Expression<'input>
    },
    Expression(Expression<'input>),
    WhileBlock {
        condition: Expression<'input>,
        block: CodeBlock<'input>,
    },
    /// `for a in b` { ... }``
    ForEachLoop {
        node_id: NodeId,
        iterator_var_ident: Ident<'input>,
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
    Identifier(Path<'input>),
    BinOp {
        lhs: Box<Expression<'input>>,
        op: BiOperator,
        rhs: Box<Expression<'input>>,
    },
    FieldAccess {
        lhs: Box<Expression<'input>>,
        rhs: Path<'input>,
    },
    UnaryOperator(UnaryOperator, Box<Expression<'input>>),
    FunctionCall {
        fn_expr: Box<Expression<'input>>,
        arguments: Vec<Expression<'input>>,
    },
    Assignment {
        variable: Path<'input>,
        rhs: Box<Expression<'input>>,
    },
    IfElseBlock {
        if_condition: Box<Expression<'input>>,
        if_block: CodeBlock<'input>,
        // condition, block
        else_if_chain: Vec<(Expression<'input>, CodeBlock<'input>)>,
        else_block: Option<CodeBlock<'input>>,
    },
    StructConstructor {
        struct_name: Path<'input>,
        /// (struct field name, local var name)
        fields: Vec<(Path<'input>, Path<'input>)>
    }
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

pub trait MutAstVisitor<'i> {
    fn start_visiting(&mut self, ast: &mut Vec<OuterExpression<'i>>) {
        for expr in ast {
            self.visit_outer_expression(expr);
        }
    }

    fn visit_outer_expression(&mut self, expr: &mut OuterExpression<'i>) {
        use OuterExpression::*;
        match expr {
            // TODO: Push container rib when the expression is a struct or an enum
            Struct { node_id, ident, fields }
                => self.visit_struct(node_id, ident, fields),
            Enum { node_id, ident, variants }
                => self.visit_enum(node_id, ident, variants),
            Function { node_id, ident, arguments, return_type, inner }
                => self.visit_function(node_id, ident, arguments, return_type, inner),
            ModuleDefinition { node_id, ident, inner }
                => self.visit_module(node_id, ident, inner),
            StaticElement | ConstElement | Trait | ImplBlock => todo!()
        }
    }

    fn visit_struct(&mut self, node_id: &mut NodeId, ty: &mut Ty<'i>, fields: &mut Fields<'i>) {
        self.visit_nodeid(node_id);
        self.visit_type(ty);
        self.visit_fields(fields);
    }
    
    fn visit_enum(&mut self, node_id: &mut NodeId, ty: &mut Ty<'i>, variants: &mut Vec<(Ty<'i>, Fields<'i>)>) {
        self.visit_nodeid(node_id);
        self.visit_type(ty);
        
        for (ty, fields) in variants {
            self.visit_type(ty);
            self.visit_fields(fields);
        }
    }

    fn visit_function(
        &mut self,
        node_id: &mut NodeId,
        ident: &mut Ident<'i>,
        arguments: &mut Vec<FnArg<'i>>,
        return_type: &mut Option<Path<'i>>,
        inner: &mut CodeBlock<'i>
    ) {
        self.visit_nodeid(node_id);
        self.visit_ident(ident);
        
        for arg in arguments {
            self.visit_fn_arg(arg);
        }

        if let Some(ty) = return_type {
            self.visit_type_path(ty);
        }

        self.visit_codeblock(inner);
    }

    fn visit_module(&mut self, node_id: &mut NodeId, ident: &mut Ident<'i>, inner: &mut Option<Vec<OuterExpression<'i>>>) {
        self.visit_nodeid(node_id);
        self.visit_ident(ident);
        for outer_expr in inner.iter_mut().flatten() {
            self.visit_outer_expression(outer_expr);
        }
    }

    fn visit_codeblock(&mut self, codeblock: &mut CodeBlock<'i>) {
        for stmt in &mut codeblock.0 {
            self.visit_statement(stmt);
        }
    }

    fn visit_fields(&mut self, fields: &mut Fields<'i>) {
        use Fields::*;
        match fields {
            Empty => { }
            TupleLike(types) => types.iter_mut().for_each(|ty| self.visit_type_path(ty)),
            StructLike(fields) => fields.iter_mut()
                .for_each(|(ident, ty)| {
                    self.visit_ident(ident);
                    self.visit_type_path(ty);
                })
        }
    }

    fn visit_fn_arg(&mut self, fn_arg: &mut FnArg<'i>) {
        self.visit_nodeid(&mut fn_arg.node_id);
        self.visit_ident(&mut fn_arg.ident);
        self.visit_type_path(&mut fn_arg.ty);
    }

    fn visit_statement(&mut self, stmt: &mut Statement<'i>) {
        use Statement::*;
        match stmt {
            LetExpression { node_id, variable_binding, type_hint, rhs } => {
                self.visit_nodeid(node_id);
                self.visit_ident(variable_binding);
                if let Some(ty) = type_hint {
                    self.visit_type_path(ty);
                }
                self.visit_expression(rhs);
            }
            Expression(expr) => self.visit_expression(expr),
            WhileBlock { condition, block } => {
                self.visit_expression(condition);
                self.visit_codeblock(block);
            }
            ForEachLoop { node_id, iterator_var_ident, iterator_expression, block } => {
                self.visit_nodeid(node_id);
                self.visit_ident(iterator_var_ident);
                self.visit_expression(iterator_expression);
                self.visit_codeblock(block);
            }
        }
    }

    fn visit_expression(&mut self, expr: &mut Expression<'i>) {
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
            FieldAccess { lhs, rhs } => {
                self.visit_expression(lhs);
                self.visit_ident_path(rhs);
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

    fn visit_nodeid(&mut self, _node_id: &mut NodeId) { }
    fn visit_ref(&mut self, _node_ref: &mut Option<Ref>) { }
    fn visit_ident(&mut self, _ident: &mut Ident<'i>) { }
    fn visit_type(&mut self, _ty: &mut Ty<'i>) { }

    fn visit_ident_path(&mut self, ident_path: &mut Path<'i>) {
        self.visit_ref(&mut ident_path.node_ref);
    }

    fn visit_type_path(&mut self, type_path: &mut Path<'i>) {
        self.visit_ref(&mut type_path.node_ref);
    }
}
