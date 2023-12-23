use mz_ore::lex::LexBuf;
use mz_ore::str::{MaxLenString, StrExt};
use mz_sql_lexer::keywords::Keyword;
use std::error::Error;
use std::{char, fmt};

/// Maximum allowed identifier length in bytes.
pub const MAX_IDENTIFIER_LENGTH: usize = 255;

/// Newtype that limits the length of identifiers.
pub type IdentString = MaxLenString<MAX_IDENTIFIER_LENGTH>;

#[derive(Debug, Clone, PartialEq)]
pub struct LexerError {
    /// The error message.
    pub message: String,
    /// The byte position with which the error is associated.
    pub pos: usize,
}

impl fmt::Display for LexerError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl Error for LexerError {}

impl LexerError {
    /// Constructs an error with the provided message at the provided position.
    pub(crate) fn new<S>(pos: usize, message: S) -> LexerError
    where
        S: Into<String>,
    {
        LexerError {
            pos,
            message: message.into(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    Keyword(Keyword),
    Ident(IdentString),
    String(String),
    HexString(String),
    Number(String),
    Parameter(String, usize),
    Op(String),
    Star,
    Eq,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Dot,
    Comma,
    Colon,
    DoubleColon,
    Semicolon,
    Whitespace(String),
    LineComment(String),
    MultilineComment(String),
}

impl Token {
    pub fn as_str(&self) -> &str {
        match self {
            Token::Keyword(s) => s.as_str(),
            Token::Ident(s) => s,
            Token::String(s) => s,
            Token::HexString(s) => s,
            Token::Number(s) => s,
            Token::Parameter(s, _) => s,
            Token::Op(s) => s,
            Token::Star => "*",
            Token::Eq => "=",
            Token::LParen => "(",
            Token::RParen => ")",
            Token::LBracket => "[",
            Token::RBracket => "]",
            Token::Dot => ".",
            Token::Comma => ",",
            Token::Colon => ":",
            Token::DoubleColon => "::",
            Token::Semicolon => ";",
            Token::Whitespace(s) => s,
            Token::LineComment(s) => s,
            Token::MultilineComment(s) => s,
        }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Token::Keyword(kw) => f.write_str(kw.as_str()),
            Token::Ident(id) => write!(f, "identifier {}", id.quoted()),
            Token::String(s) => write!(f, "string literal {}", s.quoted()),
            Token::HexString(s) => write!(f, "hex string literal {}", s.quoted()),
            Token::Number(n) => write!(f, "number \"{}\"", n),
            Token::Parameter(s, _) => write!(f, "parameter \"{}\"", s),
            Token::Op(op) => write!(f, "operator {}", op.quoted()),
            Token::Star => f.write_str("star"),
            Token::Eq => f.write_str("equals sign"),
            Token::LParen => f.write_str("left parenthesis"),
            Token::RParen => f.write_str("right parenthesis"),
            Token::LBracket => f.write_str("left square bracket"),
            Token::RBracket => f.write_str("right square bracket"),
            Token::Dot => f.write_str("dot"),
            Token::Comma => f.write_str("comma"),
            Token::Colon => f.write_str("colon"),
            Token::DoubleColon => f.write_str("double colon"),
            Token::Semicolon => f.write_str("semicolon"),
            Token::Whitespace(_) => f.write_str("whitespace"),
            Token::LineComment(_) => f.write_str("linecomment"),
            Token::MultilineComment(_) => f.write_str("multilinecomment"),
        }
    }
}

macro_rules! bail {
    ($pos:expr, $($fmt:expr),*) => {
        return Err(LexerError::new($pos, format!($($fmt),*)))
    }
}

/// Lexes a SQL query.
///
/// Returns a list of tokens alongside their corresponding byte offset in the
/// input string. Returns an error if the SQL query is lexically invalid.
///
/// See the module documentation for more information about the lexical
/// structure of SQL.
pub fn lex(query: &str) -> Result<Vec<Token>, LexerError> {
    let buf = &mut LexBuf::new(query);
    let mut tokens = vec![];
    while let Some(ch) = buf.next() {
        let token = match ch {
            _ if ch.is_ascii_whitespace() => lex_whitespace(buf),
            '-' if buf.consume('-') => lex_line_comment(buf),
            '/' if buf.consume('*') => lex_multiline_comment(buf)?,
            '\'' => Token::String(lex_string(buf)?),
            'x' | 'X' if buf.consume('\'') => Token::HexString(lex_string(buf)?),
            'e' | 'E' if buf.consume('\'') => lex_extended_string(buf)?,
            'A'..='Z' | 'a'..='z' | '_' | '\u{80}'..=char::MAX => lex_ident(buf)?,
            '"' => lex_quoted_ident(buf)?,
            '0'..='9' => lex_number(buf)?,
            '.' if matches!(buf.peek(), Some('0'..='9')) => lex_number(buf)?,
            '$' if matches!(buf.peek(), Some('0'..='9')) => lex_parameter(buf)?,
            '$' => lex_dollar_string(buf)?,
            '(' => Token::LParen,
            ')' => Token::RParen,
            ',' => Token::Comma,
            '.' => Token::Dot,
            ':' if buf.consume(':') => Token::DoubleColon,
            ':' => Token::Colon,
            ';' => Token::Semicolon,
            '[' => Token::LBracket,
            ']' => Token::RBracket,
            #[rustfmt::skip]
            '+'|'-'|'*'|'/'|'<'|'>'|'='|'~'|'!'|'@'|'#'|'%'|'^'|'&'|'|'|'`'|'?' => lex_op(buf),
            _ => bail!(buf.pos(), "unexpected character in input: {}", ch),
        };
        tokens.push(token)
    }

    #[cfg(debug_assertions)]
    {
        let mut s = String::new();
        for token in &tokens {
            s.push_str(token.as_str());
        }
        assert_eq!(s.to_lowercase(), query.to_lowercase());
    }

    Ok(tokens)
}

fn lex_whitespace(buf: &mut LexBuf) -> Token {
    buf.prev();
    Token::Whitespace(buf.take_while(|ch| ch.is_ascii_whitespace()).into())
}

fn lex_line_comment(buf: &mut LexBuf) -> Token {
    buf.prev();
    buf.prev();
    Token::LineComment(buf.take_while(|ch| ch != '\n').into())
}

fn lex_multiline_comment(buf: &mut LexBuf) -> Result<Token, LexerError> {
    let pos = buf.pos() - 2;
    let mut nesting = 0;
    while let Some(ch) = buf.next() {
        match ch {
            '*' if buf.consume('/') => {
                if nesting == 0 {
                    return Ok(Token::MultilineComment(buf.inner()[pos..buf.pos()].into()));
                } else {
                    nesting -= 1;
                }
            }
            '/' if buf.consume('*') => nesting += 1,
            _ => (),
        }
    }
    bail!(pos, "unterminated multiline comment")
}

fn lex_ident(buf: &mut LexBuf) -> Result<Token, LexerError> {
    buf.prev();
    let pos: usize = buf.pos();
    let word = buf.take_while(
        |ch| matches!(ch, 'A'..='Z' | 'a'..='z' | '0'..='9' | '$' | '_' | '\u{80}'..=char::MAX),
    );
    match word.parse() {
        Ok(kw) => Ok(Token::Keyword(kw)),
        Err(_) => {
            let Ok(small) = IdentString::new(word.to_lowercase()) else {
                bail!(
                    pos,
                    "identifier length exceeds {MAX_IDENTIFIER_LENGTH} bytes"
                )
            };
            Ok(Token::Ident(small))
        }
    }
}

fn lex_quoted_ident(buf: &mut LexBuf) -> Result<Token, LexerError> {
    let mut s = String::new();
    let pos = buf.pos() - 1;
    loop {
        match buf.next() {
            Some('"') if buf.consume('"') => s.push('"'),
            Some('"') => break,
            Some('\0') => bail!(pos, "null character in quoted identifier"),
            Some(c) => s.push(c),
            None => bail!(pos, "unterminated quoted identifier"),
        }
    }
    let Ok(small) = IdentString::new(s) else {
        bail!(
            pos,
            "identifier length exceeds {MAX_IDENTIFIER_LENGTH} bytes"
        )
    };
    Ok(Token::Ident(small))
}

fn lex_string(buf: &mut LexBuf) -> Result<String, LexerError> {
    let mut s = String::new();
    loop {
        let pos = buf.pos() - 1;
        loop {
            match buf.next() {
                Some('\'') if buf.consume('\'') => s.push('\''),
                Some('\'') => break,
                Some(c) => s.push(c),
                None => bail!(pos, "unterminated quoted string"),
            }
        }
        if !lex_to_adjacent_string(buf) {
            return Ok(s);
        }
    }
}

fn lex_extended_string(buf: &mut LexBuf) -> Result<Token, LexerError> {
    fn lex_unicode_escape(buf: &mut LexBuf, n: usize) -> Result<char, LexerError> {
        let pos = buf.pos() - 2;
        buf.next_n(n)
            .and_then(|s| u32::from_str_radix(s, 16).ok())
            .and_then(|codepoint| char::try_from(codepoint).ok())
            .ok_or_else(|| LexerError::new(pos, "invalid unicode escape"))
    }

    // We do not support octal (\o) or hexadecimal (\x) escapes, since it is
    // possible to construct invalid UTF-8 with these escapes. We could check
    // for and reject invalid UTF-8, of course, but it is too annoying to be
    // worth doing right now. We still lex the escapes to produce nice error
    // messages.

    fn lex_octal_escape(buf: &mut LexBuf) -> LexerError {
        let pos = buf.pos() - 2;
        buf.take_while(|ch| matches!(ch, '0'..='7'));
        LexerError::new(pos, "octal escapes are not supported")
    }

    fn lex_hexadecimal_escape(buf: &mut LexBuf) -> LexerError {
        let pos = buf.pos() - 2;
        buf.take_while(|ch| matches!(ch, '0'..='9' | 'A'..='F' | 'a'..='f'));
        LexerError::new(pos, "hexadecimal escapes are not supported")
    }

    let mut s = String::new();
    loop {
        let pos = buf.pos() - 1;
        loop {
            match buf.next() {
                Some('\'') if buf.consume('\'') => s.push('\''),
                Some('\'') => break,
                Some('\\') => match buf.next() {
                    Some('b') => s.push('\x08'),
                    Some('f') => s.push('\x0c'),
                    Some('n') => s.push('\n'),
                    Some('r') => s.push('\r'),
                    Some('t') => s.push('\t'),
                    Some('u') => s.push(lex_unicode_escape(buf, 4)?),
                    Some('U') => s.push(lex_unicode_escape(buf, 8)?),
                    Some('0'..='7') => return Err(lex_octal_escape(buf)),
                    Some('x') => return Err(lex_hexadecimal_escape(buf)),
                    Some(c) => s.push(c),
                    None => bail!(pos, "unterminated quoted string"),
                },
                Some(c) => s.push(c),
                None => bail!(pos, "unterminated quoted string"),
            }
        }
        if !lex_to_adjacent_string(buf) {
            return Ok(Token::String(s));
        }
    }
}

fn lex_to_adjacent_string(buf: &mut LexBuf) -> bool {
    // Adjacent string literals that are separated by whitespace are
    // concatenated if and only if that whitespace contains at least one newline
    // character. This bizarre rule matches PostgreSQL and the SQL standard.
    let whitespace = buf.take_while(|ch| ch.is_ascii_whitespace());
    whitespace.contains(&['\n', '\r'][..]) && buf.consume('\'')
}

fn lex_dollar_string(buf: &mut LexBuf) -> Result<Token, LexerError> {
    let pos = buf.pos() - 1;
    let tag = format!("${}$", buf.take_while(|ch| ch != '$'));
    let _ = buf.next();
    if let Some(s) = buf.take_to_delimiter(&tag) {
        Ok(Token::String(s.into()))
    } else {
        Err(LexerError::new(pos, "unterminated dollar-quoted string"))
    }
}

fn lex_parameter(buf: &mut LexBuf) -> Result<Token, LexerError> {
    let pos = buf.pos() - 1;
    let s = buf.take_while(|ch| matches!(ch, '0'..='9'));
    let n = s
        .parse()
        .map_err(|_| LexerError::new(pos, "invalid parameter number"))?;
    Ok(Token::Parameter(s.into(), n))
}

fn lex_number(buf: &mut LexBuf) -> Result<Token, LexerError> {
    buf.prev();
    let mut s = buf.take_while(|ch| matches!(ch, '0'..='9')).to_owned();

    // Optional decimal component.
    if buf.consume('.') {
        s.push('.');
        s.push_str(buf.take_while(|ch| matches!(ch, '0'..='9')));
    }

    // Optional exponent.
    if buf.consume('e') || buf.consume('E') {
        s.push('E');
        let require_exp = if buf.consume('-') {
            s.push('-');
            true
        } else {
            buf.consume('+')
        };
        let exp = buf.take_while(|ch| matches!(ch, '0'..='9'));
        if require_exp && exp.is_empty() {
            return Err(LexerError::new(buf.pos() - 1, "missing required exponent"));
        } else if exp.is_empty() {
            // Put back consumed E.
            buf.prev();
            s.pop();
        } else {
            s.push_str(exp);
        }
    }

    Ok(Token::Number(s))
}

fn lex_op(buf: &mut LexBuf) -> Token {
    buf.prev();
    let mut s = String::new();

    // In PostgreSQL, operators might be composed of any of the characters in
    // the set below...
    while let Some(ch) = buf.next() {
        match ch {
            // ...except the sequences `--` and `/*` start comments, even within
            // what would otherwise be an operator...
            '-' if buf.peek() == Some('-') => {
                buf.prev();
                break;
            }
            '/' if buf.peek() == Some('*') => {
                buf.prev();
                break;
            }
            #[rustfmt::skip]
            '+'|'-'|'*'|'/'|'<'|'>'|'='|'~'|'!'|'@'|'#'|'%'|'^'|'&'|'|'|'`'|'?' => s.push(ch),
            _ => {
                buf.prev();
                break;
            }
        }
    }

    // ...and a multi-character operator that ends with `-` or `+` must also
    // contain at least one nonstandard operator character. This is so that e.g.
    // `1+-2` is lexed as `1 + (-2)` as required by the SQL standard, but `1@+2`
    // is lexed as `1 @+ 2`, as `@+` is meant to be a user-definable operator.
    if s.len() > 1
        && s.ends_with(&['-', '+'][..])
        && !s.contains(&['~', '!', '@', '#', '%', '^', '&', '|', '`', '?'][..])
    {
        while s.len() > 1 && s.ends_with(&['-', '+'][..]) {
            buf.prev();
            s.pop();
        }
    }

    match s.as_str() {
        // `*` and `=` are not just expression operators in SQL, so give them
        // dedicated tokens to simplify the parser.
        "*" => Token::Star,
        "=" => Token::Eq,
        // Normalize the two forms of the not-equals operator.
        "!=" => Token::Op("<>".into()),
        // Emit all other operators as is.
        _ => Token::Op(s),
    }
}
