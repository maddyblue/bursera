use mz_sql_parser::ast as mz_ast;
use parser::parse;
use parser::Parse;
use rowan::TextRange;
use syntax::SyntaxKind::*;
use syntax::SyntaxNode;

#[derive(Debug)]
struct Error {
    message: String,
    pos: usize,
}

impl Error {
    fn new(message: impl Into<String>, pos: TextRange) -> Self {
        Self {
            message: message.into(),
            pos: pos.start().into(),
        }
    }
}

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
    fn typ(&self) -> Result<ObjectType, Error> {
        self.0
            .children()
            .find_map(ObjectType::cast)
            .ok_or_else(|| Error::new("no object type specified", self.0.text_range()))
    }
}

impl ObjectType {
    fn typ(&self) -> Result<mz_ast::ObjectType, Error> {
        match self.0.children_with_tokens().find(|t| t.kind() == KEYWORD) {
            Some(rowan::NodeOrToken::Token(tok)) => match tok.text() {
                "TABLE" => Ok(mz_ast::ObjectType::Table),
                t => Err(Error::new(
                    format!("unknown object type: {t}"),
                    tok.text_range(),
                )),
            },
            _ => Err(Error::new("no object type", self.0.text_range())),
        }
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
    let text = "drop VIEW blah
    -- drop dependents
    CASCADE;";
    let root = Root::from(parse(text));
    let statements = root.statements();
    for s in statements {
        dbg!(&s);
        match s.kind() {
            StatementKind::DropObjects(s) => {
                s.0.children_with_tokens().for_each(|t| {
                    dbg!(&t, t.index());
                });
                let typ = s.typ();
                dbg!(typ.and_then(|t| t.typ()));
            }
        }
    }
}
