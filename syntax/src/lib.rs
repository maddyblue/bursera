#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[allow(non_camel_case_types)]
#[repr(u16)]
pub enum SyntaxKind {
    // Lexer tokens.
    KEYWORD,
    IDENT,
    STRING,
    HEXSTRING,
    NUMBER,
    PARAMETER,
    OP,
    STAR,
    EQ,
    LPAREN,
    RPAREN,
    LBRACKET,
    RBRACKET,
    DOT,
    COMMA,
    COLON,
    DOUBLECOLON,
    SEMICOLON,
    WHITESPACE,
    LINECOMMENT,
    MULTILINECOMMENT,

    // Statement nodes.
    DROP_OBJECTS,

    // Inner composite nodes.
    OBJECT_TYPE,
    CASCADE_OR_RESTRICT,

    // Must be last.
    ERR,
    ROOT,
}
use lexer::Token;
use SyntaxKind::*;

impl From<SyntaxKind> for rowan::SyntaxKind {
    fn from(kind: SyntaxKind) -> Self {
        Self(kind as u16)
    }
}

impl From<&Token> for SyntaxKind {
    fn from(value: &Token) -> Self {
        match value {
            Token::Keyword(_) => KEYWORD,
            Token::Ident(_) => IDENT,
            Token::String(_) => STRING,
            Token::HexString(_) => HEXSTRING,
            Token::Number(_) => NUMBER,
            Token::Parameter(_, _) => PARAMETER,
            Token::Op(_) => OP,
            Token::Star => STAR,
            Token::Eq => EQ,
            Token::LParen => LPAREN,
            Token::RParen => RPAREN,
            Token::LBracket => LBRACKET,
            Token::RBracket => RBRACKET,
            Token::Dot => DOT,
            Token::Comma => COMMA,
            Token::Colon => COLON,
            Token::DoubleColon => DOUBLECOLON,
            Token::Semicolon => SEMICOLON,
            Token::Whitespace(_) => WHITESPACE,
            Token::LineComment(_) => LINECOMMENT,
            Token::MultilineComment(_) => MULTILINECOMMENT,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Lang {}
impl rowan::Language for Lang {
    type Kind = SyntaxKind;
    fn kind_from_raw(raw: rowan::SyntaxKind) -> Self::Kind {
        assert!(raw.0 <= ROOT as u16);
        unsafe { std::mem::transmute::<u16, SyntaxKind>(raw.0) }
    }
    fn kind_to_raw(kind: Self::Kind) -> rowan::SyntaxKind {
        kind.into()
    }
}

pub type SyntaxNode = rowan::SyntaxNode<Lang>;
pub type SyntaxToken = rowan::SyntaxToken<Lang>;
pub type SyntaxElement = rowan::NodeOrToken<SyntaxNode, SyntaxToken>;
