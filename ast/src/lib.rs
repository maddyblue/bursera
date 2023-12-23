use mz_sql_parser::ast as mz_ast;
use parser::parse;
use parser::Parse;
use syntax::SyntaxKind::*;
use syntax::SyntaxNode;

macro_rules! ast_node {
    ($ast:ident, $kind:ident) => {
        #[derive(Debug, PartialEq, Eq, Hash)]
        #[repr(transparent)]
        struct $ast(SyntaxNode);
        impl $ast {
            #[allow(unused)]
            fn cast(node: SyntaxNode) -> Option<Self> {
                if node.kind() == $kind {
                    Some(Self(node))
                } else {
                    None
                }
            }
        }
    };
}

ast_node!(Root, ROOT);
ast_node!(DropObjects, DROP_OBJECTS);
ast_node!(ObjectType, OBJECT_TYPE);

impl Root {
    fn statements(&self) -> impl Iterator<Item = Statement> + '_ {
        self.0.children().filter_map(Statement::cast)
    }
}

impl From<Parse> for Root {
    fn from(value: Parse) -> Self {
        Root::cast(value.syntax()).unwrap()
    }
}

impl DropObjects {
    fn typ(&self) -> Option<mz_ast::ObjectType> {
        self.0
            .children()
            .find_map(ObjectType::cast)
            .and_then(|t| t.typ())
    }
}

impl ObjectType {
    fn typ(&self) -> Option<mz_ast::ObjectType> {
        self.0
            .green()
            .children()
            .find(|t| t.kind() == KEYWORD.into())
            .and_then(|t| match t {
                rowan::NodeOrToken::Node(_) => None,
                rowan::NodeOrToken::Token(t) => match t.text() {
                    "TABLE" => Some(mz_ast::ObjectType::Table),
                    _ => None,
                },
            })
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
#[repr(transparent)]
struct Statement(SyntaxNode);

#[derive(Debug)]
enum StatementKind {
    DropObjects(DropObjects),
}

impl Statement {
    fn cast(node: SyntaxNode) -> Option<Self> {
        if DropObjects::cast(node.clone()).is_some() {
            Some(Statement(node))
        } else {
            None
        }
    }

    fn kind(&self) -> StatementKind {
        DropObjects::cast(self.0.clone())
            .map(StatementKind::DropObjects)
            .unwrap()
    }
}

#[test]
fn test_ast() {
    let text = "drop table blah
    -- drop dependents
    CASCADE;";
    let root = Root::from(parse(text));
    let statements = root.statements();
    for s in statements {
        match s.kind() {
            StatementKind::DropObjects(s) => {
                dbg!(s.typ());
            }
        }
    }
}
