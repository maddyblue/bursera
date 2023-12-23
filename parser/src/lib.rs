use lexer::{lex, Token};
use mz_sql_lexer::keywords::*;
use rowan::{GreenNode, GreenNodeBuilder};
use syntax::SyntaxKind::{self, *};
use syntax::SyntaxNode;

/// The parse results are stored as a "green tree".
/// We'll discuss working with the results later
pub struct Parse {
    green_node: GreenNode,
    #[allow(unused)]
    errors: Vec<String>,
}

/// Now, let's write a parser.
/// Note that `parse` does not return a `Result`:
/// by design, syntax tree can be built even for
/// completely invalid source code.
pub fn parse(text: &str) -> Parse {
    struct Parser {
        /// input tokens, including whitespace,
        /// in *reverse* order.
        tokens: Vec<Token>,
        /// the in-progress tree.
        builder: GreenNodeBuilder<'static>,
        /// the list of syntax errors we've accumulated
        /// so far.
        errors: Vec<String>,
    }

    /// The outcome of parsing a single S-expression
    #[derive(Debug)]
    enum StatementRes {
        /// A statement was successfully parsed.
        Ok,
        /// Nothing was parsed, as no significant tokens remained.
        Eof,
        /// A parse error occurred.
        Error(String),
    }

    impl Parser {
        fn parse(mut self) -> Parse {
            // Make sure that the root node covers all source
            self.builder.start_node(ROOT.into());
            // Parse zero or more statements
            loop {
                match self.statement() {
                    StatementRes::Eof => break,
                    StatementRes::Error(err) => {
                        self.builder.start_node(ERR.into());
                        self.errors.push(err);
                        // be sure to chug along in case of error
                        self.bump();
                        while matches!(self.current(), Some(Token::Semicolon)) {
                            self.bump();
                        }
                        self.builder.finish_node();
                    }
                    StatementRes::Ok => (),
                }
            }
            // Don't forget to eat *trailing* whitespace
            self.skip_ws();
            // Close the root node.
            self.builder.finish_node();

            // Turn the builder into a GreenNode
            Parse {
                green_node: self.builder.finish(),
                errors: self.errors,
            }
        }
        fn drop(&mut self) -> Result<(), String> {
            self.builder.start_node(DROP_OBJECTS.into());
            self.bump();
            self.finish_after(|slf| {
                slf.parse_object_type()?;
                slf.parse_ident()?;
                slf.parse_cascade();
                Ok(())
            })
        }
        fn parse_object_type(&mut self) -> Result<(), String> {
            self.builder.start_node(OBJECT_TYPE.into());
            self.finish_after(|slf| slf.expect_one_of(&[TABLE, VIEW]))
        }
        fn parse_cascade(&mut self) {
            self.builder.start_node(CASCADE_OR_RESTRICT.into());
            self.consume_one_of(&[RESTRICT, CASCADE]);
            self.builder.finish_node();
        }
        fn finish_after<F>(&mut self, f: F) -> Result<(), String>
        where
            F: Fn(&mut Self) -> Result<(), String>,
        {
            let res = f(self);
            self.builder.finish_node();
            res
        }
        fn statement(&mut self) -> StatementRes {
            self.skip_ws();
            let kw = match self.current() {
                None => return StatementRes::Eof,
                Some(Token::Semicolon) => {
                    self.bump();
                    return StatementRes::Ok;
                }
                Some(Token::Keyword(kw)) => kw,
                // todo: add position
                Some(tok) => {
                    return StatementRes::Error(format!("unexpected token {}", tok.as_str()))
                }
            };
            let res = match *kw {
                DROP => self.drop(),
                _ => return StatementRes::Error(format!("unexpected keyword {}", kw)),
            };
            match res {
                Ok(()) => StatementRes::Ok,
                Err(err) => StatementRes::Error(err),
            }
        }
        fn parse_ident(&mut self) -> Result<(), String> {
            self.skip_ws();
            match self.current() {
                Some(Token::Ident(_)) => {
                    self.bump();
                    Ok(())
                }
                tok => Err(format!("expected ident, found {tok:?}")),
            }
        }
        fn expect_keyword(&mut self, kw: Keyword) -> Result<(), String> {
            self.expect_one_of(&[kw])
        }
        fn expect_one_of(&mut self, kws: &[Keyword]) -> Result<(), String> {
            self.skip_ws();
            match self.current() {
                Some(Token::Keyword(k)) if kws.contains(k) => {
                    self.bump();
                    Ok(())
                }
                tok => Err(format!("expected {kws:?}, found {tok:?}")),
            }
        }
        // Consume one of the keywords if present.
        fn consume_one_of(&mut self, kws: &[Keyword]) {
            self.skip_ws();
            if let Some(Token::Keyword(kw)) = self.current() {
                if kws.contains(kw) {
                    self.bump();
                }
            }
        }
        /// Advance one token, adding it to the current branch of the tree builder.
        fn bump(&mut self) {
            let token = self.tokens.pop().unwrap();
            let kind: SyntaxKind = (&token).into();
            self.builder.token(kind.into(), token.as_str());
        }
        /// Peek at the first unprocessed token
        fn current(&self) -> Option<&Token> {
            self.tokens.last()
        }
        fn skip_ws(&mut self) {
            while matches!(
                self.current(),
                Some(Token::Whitespace(_) | Token::LineComment(_) | Token::MultilineComment(_))
            ) {
                self.bump()
            }
        }
    }

    let mut tokens = lex(text).unwrap();
    tokens.reverse();
    // todo: assert that parsed tokens are identical to original text.
    Parser {
        tokens,
        builder: GreenNodeBuilder::new(),
        errors: Vec::new(),
    }
    .parse()
}

impl Parse {
    pub fn syntax(&self) -> SyntaxNode {
        SyntaxNode::new_root(self.green_node.clone())
    }
}

#[test]
fn test_parser() {
    let text = "/* comment test */drop /*more*/table /*oaeu*/blah
    -- drop dependents
    CASCADE;";
    let parsed = parse(text);
    let node = parsed.syntax();
    dbg!(node);
    let p = parsed.pretty(&crate::prettier::Prettier { tab_width: 4 });
    dbg!(&p);
    println!("PRETTY:\n\n{}", p.pretty(80));
}

mod prettier {
    use pretty::RcDoc;
    use syntax::SyntaxKind::*;
    use syntax::SyntaxNode;

    use crate::Parse;

    impl Parse {
        pub fn pretty<'p>(&'p self, prettier: &'p Prettier) -> RcDoc<()> {
            let node = self.syntax();
            let statements = node.children_with_tokens().map(|c| match c {
                rowan::NodeOrToken::Node(n) => prettier.node(n),
                rowan::NodeOrToken::Token(t) => {
                    match t.kind() {
                        LINECOMMENT | MULTILINECOMMENT => {
                            RcDoc::concat([RcDoc::text(t.text().to_string()), RcDoc::hardline()])
                        }
                        WHITESPACE => {
                            let t = t.text();
                            let lines = t.lines().map(|_| RcDoc::hardline()).collect::<Vec<_>>();
                            if lines.len() == 1 {
                                RcDoc::text(t.to_string())
                            } else {
                                RcDoc::concat(lines)
                            }
                        }
                        // Pass other random stuff through unchanged.
                        _ => RcDoc::text(t.text().to_string()),
                    }
                }
            });
            // todo: if there are multiple statements, make sure they end with semicolons
            // todo: preserve comments inbetween statements
            RcDoc::concat(statements)
        }
    }

    pub struct Prettier {
        pub tab_width: isize,
    }

    impl Prettier {
        fn node(&self, node: SyntaxNode) -> RcDoc {
            // Record initial comments so we only tab the first non-comment node (well, the nodes
            // after it).
            let mut top_comments = Vec::new();
            let mut docs = Vec::new();
            let mut seen_non_comment = false;
            for c in node.children_with_tokens() {
                if c.kind() == WHITESPACE {
                    continue;
                }
                if !seen_non_comment && !c.kind().is_comment() {
                    seen_non_comment = true;
                }
                let doc = match c {
                    rowan::NodeOrToken::Node(n) => self.node(n),
                    rowan::NodeOrToken::Token(t) => {
                        let doc = RcDoc::text(t.text().to_string());
                        let line = if t.kind().is_comment() {
                            // Comments can never be grouped.
                            RcDoc::hardline()
                        } else {
                            RcDoc::line()
                        };
                        RcDoc::concat([doc, line])
                    }
                };
                if !seen_non_comment {
                    top_comments.push(doc);
                } else {
                    docs.push(doc);
                }
            }
            let doc = RcDoc::concat(docs).nest(self.tab_width).group();
            RcDoc::concat([RcDoc::concat(top_comments), doc])
        }
    }
}
