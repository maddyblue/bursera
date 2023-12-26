use lexer::{lex, Token};
use mz_sql_lexer::keywords as kw;
use mz_sql_lexer::keywords::Keyword;
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
        fn parse_drop(&mut self) -> Result<(), String> {
            self.finish_after(DROP_OBJECTS, |slf| {
                slf.bump();
                slf.parse_object_type()?;
                slf.parse_ident()?;
                slf.parse_cascade();
                Ok(())
            })
        }
        fn parse_select_statement(&mut self) -> Result<(), String> {
            self.finish_after(SELECT_STATEMENT, |slf| {
                slf.parse_query()?;
                Ok(())
            })
        }
        fn parse_query(&mut self) -> Result<(), String> {
            self.finish_after(QUERY, |slf| {
                slf.parse_query_body(SetPrecedence::Zero)?;
                slf.parse_query_tail()?;
                Ok(())
            })
        }
        fn parse_query_body(&mut self, precedence: SetPrecedence) -> Result<(), String> {
            if self.parse_keyword(kw::SELECT) {
                self.parse_select()?;
            } else {
                return Err(format!("SELECT, VALUES, or a subquery in the query body",));
            };
            Ok(())
        }
        fn parse_select(&mut self) -> Result<(), String> {
            self.finish_after(SELECT, |slf| {
                slf.parse_keyword(kw::ALL);
                let distinct = slf.parse_keyword(kw::DISTINCT);
                if distinct && slf.parse_keyword(kw::ON) {
                    slf.expect_token(&Token::LParen)?;
                    let exprs = slf.parse_comma_separated(Parser::parse_expr)?;
                    slf.expect_token(&Token::RParen)?;
                }

                let projection = match slf.peek(0) {
                    // An empty target list is permissible to match PostgreSQL, which
                    // permits these for symmetry with zero column tables.
                    Some(Token::Keyword(kw)) if kw.is_reserved() => vec![],
                    Some(Token::Semicolon) | Some(Token::RParen) | None => vec![],
                    _ => {
                        let mut projection = vec![];
                        loop {
                            projection.push(slf.parse_select_item()?);
                            if !slf.consume_token(&Token::Comma) {
                                break;
                            }
                            if slf.peek_keyword(kw::FROM) {
                                return Err(format!("invalid trailing comma in SELECT list",));
                            }
                        }
                        projection
                    }
                };

                // Note that for keywords to be properly handled here, they need to be
                // added to `RESERVED_FOR_COLUMN_ALIAS` / `RESERVED_FOR_TABLE_ALIAS`,
                // otherwise they may be parsed as an alias as part of the `projection`
                // or `from`.

                slf.if_peek_keyword(kw::FROM, FROM, |slf| {
                    slf.parse_comma_separated(Parser::parse_table_and_joins)
                })?;
                slf.if_peek_keyword(kw::WHERE, WHERE, Self::parse_expr)?;
                slf.if_peek_keywords(&[kw::GROUP, kw::BY], GROUP_BY, |slf| {
                    slf.parse_comma_separated(Parser::parse_expr)
                })?;
                slf.if_peek_keyword(kw::HAVING, HAVING, Self::parse_expr)?;
                Ok(())
            })
        }
        fn parse_table_and_joins(&mut self) -> Result<(), String> {
            let relation = self.parse_table_factor()?;

            // Note that for keywords to be properly handled here, they need to be
            // added to `RESERVED_FOR_TABLE_ALIAS`, otherwise they may be parsed as
            // a table alias.
            let mut joins = vec![];
            loop {
                let join = if self.parse_keyword(kw::CROSS) {
                    self.expect_keyword(kw::JOIN)?;
                    Join {
                        relation: self.parse_table_factor()?,
                        join_operator: JoinOperator::CrossJoin,
                    }
                } else {
                    let natural = self.parse_keyword(kw::NATURAL);
                    let peek_keyword = if let Some(Token::Keyword(kw)) = self.peek_token() {
                        Some(kw)
                    } else {
                        None
                    };

                    let join_operator_type = match peek_keyword {
                        Some(INNER) | Some(JOIN) => {
                            let _ = self.parse_keyword(kw::INNER);
                            self.expect_keyword(kw::JOIN)?;
                            JoinOperator::Inner
                        }
                        Some(kw @ LEFT) | Some(kw @ RIGHT) | Some(kw @ FULL) => {
                            let _ = self.next_token();
                            let _ = self.parse_keyword(kw::OUTER);
                            self.expect_keyword(kw::JOIN)?;
                            match kw {
                                LEFT => JoinOperator::LeftOuter,
                                RIGHT => JoinOperator::RightOuter,
                                FULL => JoinOperator::FullOuter,
                                _ => unreachable!(),
                            }
                        }
                        Some(OUTER) => {
                            return self.expected(
                                self.peek_pos(),
                                "LEFT, RIGHT, or FULL",
                                self.peek_token(),
                            )
                        }
                        None if natural => {
                            return self.expected(
                                self.peek_pos(),
                                "a join type after NATURAL",
                                self.peek_token(),
                            );
                        }
                        _ => break,
                    };
                    let relation = self.parse_table_factor()?;
                    let join_constraint = self.parse_join_constraint(natural)?;
                    Join {
                        relation,
                        join_operator: join_operator_type(join_constraint),
                    }
                };
                joins.push(join);
            }
            Ok(TableWithJoins { relation, joins })
        }
        fn parse_table_factor(&mut self) -> Result<(), String> {
            if self.parse_keyword(kw::LATERAL) {
                // LATERAL must always be followed by a subquery or table function.
                if self.consume_token(&Token::LParen) {
                    return self.parse_derived_table_factor(Lateral);
                } else if self.parse_keywords(&[ROWS, FROM]) {
                    return self.parse_rows_from();
                } else {
                    let name = self.parse_raw_name()?;
                    self.expect_token(&Token::LParen)?;
                    let args = self.parse_optional_args(false)?;
                    let alias = self.parse_optional_table_alias()?;
                    let with_ordinality = self.parse_keywords(&[kw::WITH, kw::ORDINALITY]);
                    return Ok(TableFactor::Function {
                        function: Function {
                            name,
                            args,
                            filter: None,
                            over: None,
                            distinct: false,
                        },
                        alias,
                        with_ordinality,
                    });
                }
            }

            if self.consume_token(&Token::LParen) {
                // A left paren introduces either a derived table (i.e., a subquery)
                // or a nested join. It's nearly impossible to determine ahead of
                // time which it is... so we just try to parse both.
                //
                // Here's an example that demonstrates the complexity:
                //                     /-------------------------------------------------------\
                //                     | /-----------------------------------\                 |
                //     SELECT * FROM ( ( ( (SELECT 1) UNION (SELECT 2) ) AS t1 NATURAL JOIN t2 ) )
                //                   ^ ^ ^ ^
                //                   | | | |
                //                   | | | |
                //                   | | | (4) belongs to a SetExpr::Query inside the subquery
                //                   | | (3) starts a derived table (subquery)
                //                   | (2) starts a nested join
                //                   (1) an additional set of parens around a nested join
                //

                // Check if the recently consumed '(' started a derived table, in
                // which case we've parsed the subquery, followed by the closing
                // ')', and the alias of the derived table. In the example above
                // this is case (3), and the next token would be `NATURAL`.
                maybe!(self.maybe_parse(|parser| parser.parse_derived_table_factor(NotLateral)));

                // The '(' we've recently consumed does not start a derived table.
                // For valid input this can happen either when the token following
                // the paren can't start a query (e.g. `foo` in `FROM (foo NATURAL
                // JOIN bar)`, or when the '(' we've consumed is followed by another
                // '(' that starts a derived table, like (3), or another nested join
                // (2).
                //
                // Ignore the error and back up to where we were before. Either
                // we'll be able to parse a valid nested join, or we won't, and
                // we'll return that error instead.
                let table_and_joins = self.parse_table_and_joins()?;
                match table_and_joins.relation {
                    TableFactor::NestedJoin { .. } => (),
                    _ => {
                        if table_and_joins.joins.is_empty() {
                            // The SQL spec prohibits derived tables and bare
                            // tables from appearing alone in parentheses.
                            self.expected(self.peek_pos(), "joined table", self.peek_token())?
                        }
                    }
                }
                self.expect_token(&Token::RParen)?;
                Ok(TableFactor::NestedJoin {
                    join: Box::new(table_and_joins),
                    alias: self.parse_optional_table_alias()?,
                })
            } else if self.parse_keywords(&[ROWS, FROM]) {
                Ok(self.parse_rows_from()?)
            } else {
                let name = self.parse_raw_name()?;
                if self.consume_token(&Token::LParen) {
                    let args = self.parse_optional_args(false)?;
                    let alias = self.parse_optional_table_alias()?;
                    let with_ordinality = self.parse_keywords(&[WITH, ORDINALITY]);
                    Ok(TableFactor::Function {
                        function: Function {
                            name,
                            args,
                            filter: None,
                            over: None,
                            distinct: false,
                        },
                        alias,
                        with_ordinality,
                    })
                } else {
                    Ok(TableFactor::Table {
                        name,
                        alias: self.parse_optional_table_alias()?,
                    })
                }
            }
        }

        fn parse_query_tail(&mut self) -> Result<(), String> {
            // todo: care about the various inner_ things.
            self.finish_after(QUERY, |slf| {
                let checkpoint = slf.builder.checkpoint();
                if slf.parse_keywords(&[kw::ORDER, kw::BY]) {
                    slf.builder.start_node_at(checkpoint, ORDER_BY.into());
                    slf.parse_comma_separated(Self::parse_order_by_expr)?;
                }
                Ok(())
            })
        }
        fn parse_expr(&mut self) -> Result<(), String> {
            self.finish_after(EXPR, |slf| Err("todo parse expr".into()))
        }
        fn parse_order_by_expr(&mut self) -> Result<(), String> {
            self.finish_after(ORDER_BY_EXPR, |slf| {
                slf.parse_expr()?;
                slf.consume_one_of(ORDER_BY_DIRECTION, &[kw::ASC, kw::DESC]);
                Ok(())
            })
        }
        fn parse_object_type(&mut self) -> Result<(), String> {
            self.finish_after(OBJECT_TYPE, |slf| slf.expect_one_of(&[kw::TABLE, kw::VIEW]))
        }
        fn parse_cascade(&mut self) {
            self.consume_one_of(CASCADE_OR_RESTRICT, &[kw::RESTRICT, kw::CASCADE]);
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
                kw::DROP => self.parse_drop(),
                kw::SELECT | kw::WITH | kw::VALUES | kw::TABLE => self.parse_select_statement(),
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
        /// Parse a comma-separated list of 1+ items accepted by `F`
        fn parse_comma_separated<T, F>(&mut self, mut f: F) -> Result<(), String>
        where
            F: FnMut(&mut Self) -> Result<T, String>,
        {
            loop {
                f(self)?;
                if !matches!(self.peek(0), Some(&Token::Comma)) {
                    break;
                }
            }
            Ok(())
        }
        fn if_peek_keyword<F>(
            &mut self,
            kw: Keyword,
            kind: impl Into<rowan::SyntaxKind>,
            f: F,
        ) -> Result<(), String>
        where
            F: Fn(&mut Self) -> Result<(), String>,
        {
            self.if_peek_keywords(&[kw], kind, f)
        }
        fn if_peek_keywords<F>(
            &mut self,
            kws: &[Keyword],
            kind: impl Into<rowan::SyntaxKind>,
            f: F,
        ) -> Result<(), String>
        where
            F: Fn(&mut Self) -> Result<(), String>,
        {
            let checkpoint = self.builder.checkpoint();
            if !self.parse_keywords(kws) {
                return Ok(());
            }
            self.builder.start_node_at(checkpoint, kind.into());
            let res = f(self);
            self.builder.finish_node();
            res
        }
        fn finish_after<F>(
            &mut self,
            kind: impl Into<rowan::SyntaxKind>,
            f: F,
        ) -> Result<(), String>
        where
            F: Fn(&mut Self) -> Result<(), String>,
        {
            self.builder.start_node(kind.into());
            let res = f(self);
            self.builder.finish_node();
            res
        }
        /// Whether the next token is the keyword, and consumes it if so.
        fn parse_keyword(&mut self, kw: Keyword) -> bool {
            self.parse_keywords(&[kw])
        }
        /// Look for an expected sequence of keywords and consume them if they exist.
        fn parse_keywords(&mut self, kws: &[Keyword]) -> bool {
            for (offset, kw) in kws.iter().enumerate() {
                match self.peek(offset) {
                    Some(Token::Keyword(k)) if kw == k => {}
                    _ => return false,
                }
            }
            for _ in kws {
                self.skip_ws();
                self.bump();
            }
            true
        }
        fn consume_token(&mut self, tok: &Token) -> bool {
            if self.peek_token(tok) {
                self.skip_ws();
                self.bump();
            }
            Ok(())
        }
        fn expect_token(&mut self, tok: &Token) -> Result<(), String> {
            self.skip_ws();
            if matches!(self.current(), tok) {
                return Err(format!("expected {tok:?}, found {:?}", self.current()));
            }
            Ok(())
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
        // Consume one of the keywords if present and adds a kind node if so.
        fn consume_one_of(&mut self, kind: impl Into<rowan::SyntaxKind>, kws: &[Keyword]) {
            self.skip_ws();
            if let Some(Token::Keyword(kw)) = self.current() {
                if kws.contains(kw) {
                    self.builder.start_node(kind.into());
                    self.bump();
                    self.builder.finish_node();
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
        /// Peeks at the offset'th token that is not whitespace or a comment.
        fn peek(&self, offset: usize) -> Option<&Token> {
            self.tokens
                .iter()
                .rev()
                .filter(|t| {
                    !matches!(
                        t,
                        Token::Whitespace(_) | Token::LineComment(_) | Token::MultilineComment(_)
                    )
                })
                .nth(offset)
        }
        fn peek_keyword(&self, kw: Keyword) -> bool {
            self.peek_token(&Token::Keyword(kw))
        }
        fn peek_token(&self, tok: &Token) -> bool {
            matches!(self.peek(0), Some(tok))
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

enum SetPrecedence {
    Zero,
    UnionExcept,
    Intersect,
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
