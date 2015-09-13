/* Copyright 2015 Jordan Miner
 *
 * Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
 * http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
 * <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
 * option. This file may not be copied, modified, or distributed
 * except according to those terms.
 */

extern crate regex;

use std::borrow::Cow;
use std::ops::Range;
use std::rc::Rc;
use self::regex::Regex;
use super::{
    Protocol,
    Schema,
    Field,
    RecordSchema,
    EnumSymbol,
    EnumSchema,
    FixedSchema,
};

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct TokenRange<Idx> {
    start: Idx,
    end: Idx,
}

impl<T> Into<Range<T>> for TokenRange<T> {
    fn into(self) -> Range<T> {
        Range { start: self.start, end: self.end }
    }
}

impl<T> From<Range<T>> for TokenRange<T> {
    fn from(range: Range<T>) -> TokenRange<T> {
        TokenRange { start: range.start, end: range.end }
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct Token<'a> {
    ty: TokenType,
    text: &'a str,
    range: TokenRange<usize>,
}

impl<'a> Token<'a> {
    fn comment_contents(&self) -> Cow<'a, str> {
        fn range_comment_contents(s: &str) -> Cow<str> {
            let mut contents = String::new();
            let first_regex = Regex::new(r"^\s*(\*+(\s+))?").unwrap();
            let rest_regex = Regex::new(r"^\s*(\*+)?").unwrap();
            let mut indent = None;

            for line in s.lines() {
                // Skip blank lines at the beginning.
                if indent.is_none() && line.trim().is_empty() {
                    continue;
                }
                let mut trimmed_line = line;
                if let Some(indent) = indent {
                    if let Some(captures) = rest_regex.captures(line) {
                        // Trim up to and including the star.
                        let (_, matched_end) = captures.pos(0).unwrap();
                        trimmed_line = &line[matched_end..line.len()];

                        // Trim whitespace after the star.
                        let index = trimmed_line.as_bytes().iter().enumerate().position(|(i, &b)|
                            !is_ascii_whitespace(b) || i >= indent
                        ).unwrap_or(trimmed_line.len());
                        trimmed_line = &trimmed_line[index..trimmed_line.len()];
                    }
                } else {
                    // Trim star and all whitespace on the first line of the commnent.
                    // Use it to determine how much whitespace to remove after the star on
                    // subsequent lines.
                    if let Some(captures) = first_regex.captures(line) {
                        let (_, matched_end) = captures.pos(0).unwrap();
                        trimmed_line = &line[matched_end..line.len()];

                        match captures.pos(2) {
                            Some((start, end)) => indent = Some(end - start),
                            _ => indent = Some(0),
                        }
                    }
                }
                trimmed_line = trimmed_line.trim_right();

                contents.push_str(trimmed_line);
                contents.push('\n');
            }
            let trailing_whitespace = contents.as_bytes().iter()
                .rev().take_while(|&&b| is_ascii_whitespace(b)).count();
            let len = contents.len(); // borrow checker workaround
            contents.truncate(len - trailing_whitespace);
            Cow::Owned(contents)
        }

        match self.ty {
            TokenType::LineComment => Cow::Borrowed(&self.text[2..self.text.len()]),
            TokenType::RangeComment => range_comment_contents(&self.text[2..self.text.len()-2]),
            TokenType::DocComment => range_comment_contents(&self.text[3..self.text.len()-2]),
            _ => panic!(),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum TokenType {
    Ident,
    Integer,

    Protocol,
    Import,
    Idl,
    Schema,
    Null,
    Boolean,
    Int,
    Long,
    Float,
    Double,
    Bytes,
    String,
    Array,
    Map,
    Union,
    Record,
    Error,
    Enum,
    Fixed,

    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Colon,
    Semi,
    Comma,
    At,
    Equals,
    Dot,
    Hyphen,
    LAngle,
    RAngle,
    Backquote,

    RangeComment,
    DocComment,
    LineComment,
    Whitespace,
}

impl TokenType {
    fn alphanumeric_token_from_str(s: &str) -> TokenType {
        match s {
            "protocol" => TokenType::Protocol,
            "import" => TokenType::Import,
            "idl" => TokenType::Idl,
            "schema" => TokenType::Schema,
            "null" => TokenType::Null,
            "boolean" => TokenType::Boolean,
            "int" => TokenType::Int,
            "long" => TokenType::Long,
            "float" => TokenType::Float,
            "double" => TokenType::Double,
            "bytes" => TokenType::Bytes,
            "string" => TokenType::String,
            "array" => TokenType::Array,
            "map" => TokenType::Map,
            "union" => TokenType::Union,
            "record" => TokenType::Record,
            "error" => TokenType::Error,
            "enum" => TokenType::Enum,
            "fixed" => TokenType::Fixed,

            _ => TokenType::Ident,
        }
    }
}

fn is_ascii_whitespace(c: u8) -> bool {
    match c {
        b' ' | b'\t' | b'\r' | b'\n' => true,
        _ => false
    }
}

fn is_ascii_alphanumeric(c: u8) -> bool {
    match c {
        b'A' ... b'Z' | b'a' ... b'z' | b'0' ... b'9' | b'_' => true,
        _ => false
    }
}

fn is_ascii_digit(c: u8) -> bool {
    match c {
        b'0' ... b'9' => true,
        _ => false
    }
}

fn is_crlf(c: u8) -> bool {
    c == b'\r' || c == b'\n'
}

#[derive(Debug, Copy, Clone)]
pub struct Lexer<'a> {
    src: &'a str,
    skip_whitespace: bool,
    skip_comments: bool,
    index: usize,

    line: usize,
    column: usize,
    last_doc_comment: Option<Token<'a>>,
}

impl<'a> Lexer<'a> {
    pub fn new(src: &'a str) -> Lexer {
        Lexer {
            src: src,
            skip_whitespace: false,
            skip_comments: false,
            index: 0,
            line: 1,
            column: 1,
            last_doc_comment: None
        }
    }

    pub fn skip_whitespace(&self) -> bool {
        self.skip_whitespace
    }

    pub fn set_skip_whitespace(&mut self, skip: bool) {
        self.skip_whitespace = skip;
    }

    pub fn skip_comments(&self) -> bool {
        self.skip_comments
    }

    pub fn set_skip_comments(&mut self, skip: bool) {
        self.skip_comments = skip;
    }

    pub fn index(&self) -> usize {
        self.index
    }

    pub fn line(&self) -> usize {
        self.line
    }

    pub fn column(&self) -> usize {
        self.column
    }

    pub fn last_doc_comment(&self) -> Option<Token<'a>> {
        self.last_doc_comment
    }

    pub fn clear_last_doc_comment(&mut self) {
        self.last_doc_comment = None;
    }

    pub fn expect_and_consume(&mut self, ty: TokenType) -> Result<Token<'a>, IdlError> {
        match self.next() {
            Some(Ok(token)) => {
                if token.ty == ty {
                    Ok(token)
                } else {
                    Err(IdlError { kind: IdlErrorKind::UnexpectedToken })
                }
            },
            Some(err @ Err(_)) => err,
            None => Err(IdlError { kind: IdlErrorKind::UnexpectedEnd }),
        }
    }

    pub fn try_consume(&mut self, ty: TokenType) -> bool {
        let mut copy = *self;
        match copy.next() {
            Some(Ok(token)) if token.ty == ty => {
                self.next();
                true
            },
            _ => false,
        }
    }

    pub fn expect_next(&mut self) -> Result<Token<'a>, IdlError> {
        match self.next() {
            Some(token @ Ok(_)) => token,
            Some(err @ Err(_)) => err,
            None => Err(IdlError { kind: IdlErrorKind::UnexpectedEnd }),
        }
    }

    // I knew how to implement a lexer, but I did skim this example presented as a fast lexer:
    // http://www.cs.dartmouth.edu/~mckeeman/cs48/mxcom/doc/lexInCpp.html
    // linked from the bottom of http://www.cs.dartmouth.edu/~mckeeman/cs48/mxcom/doc/Lexing.html
    // https://github.com/apache/avro/blob/eb31746cd5efd5e2c9c57780a651afaccd5cfe06/lang/java/compiler/src/main/javacc/org/apache/avro/compiler/idl/idl.jj
    fn lex(&mut self) -> Option<Result<Token<'a>, IdlError>> {
        let bytes = self.src.as_bytes();
        let start = self.index;

        let c = if self.index < bytes.len() {
            bytes[self.index] // could use get_unchecked() for speed
        } else {
            return None;
        };
        self.index += 1;

        let token = |ty, this: &mut Lexer<'a>| Some(Ok(Token {
            ty: ty, text: &this.src[start..this.index], range: (start..this.index).into()
        }));

        match c {
            b'(' => return token(TokenType::LParen, self),
            b')' => return token(TokenType::RParen, self),
            b'{' => return token(TokenType::LBrace, self),
            b'}' => return token(TokenType::RBrace, self),
            b'[' => return token(TokenType::LBracket, self),
            b']' => return token(TokenType::RBracket, self),
            b':' => return token(TokenType::Colon, self),
            b';' => return token(TokenType::Semi, self),
            b',' => return token(TokenType::Comma, self),
            b'@' => return token(TokenType::At, self),
            b'=' => return token(TokenType::Equals, self),
            b'.' => return token(TokenType::Dot, self),
            b'-' => return token(TokenType::Hyphen, self),
            b'<' => return token(TokenType::LAngle, self),
            b'>' => return token(TokenType::RAngle, self),
            b'`' => return token(TokenType::Backquote, self),

            b' ' | b'\t' | b'\r' | b'\n' => {
                while self.index < bytes.len() && is_ascii_whitespace(bytes[self.index]) {
                    self.index += 1;
                }
                return token(TokenType::Whitespace, self);
            },

            b'A' ... b'Z' | b'a' ... b'z' | b'_' => {
                while self.index < bytes.len() && is_ascii_alphanumeric(bytes[self.index]) {
                    self.index += 1;
                }
                let token_text = &self.src[start..self.index];
                let token_ty = TokenType::alphanumeric_token_from_str(token_text);
                return Some(Ok(Token {
                    ty: token_ty,
                    text: token_text,
                    range: (start..self.index).into()
                }));
            },

            b'0' ... b'9' => {
                while self.index < bytes.len() && is_ascii_digit(bytes[self.index]) {
                    self.index += 1;
                }
                return token(TokenType::Integer, self);
            },

            // TODO: escaped identifiers
            //b'`' => {
            //},

            b'/' if self.index < bytes.len() => {
                match bytes[self.index] {
                    b'*' => {
                        self.index += 1;
                        let doc = self.index < bytes.len() && bytes[self.index] == b'*';
                        loop {
                            self.index += 1;
                            if bytes.len() - self.index < 2 {
                                return Some(Err(IdlError {
                                        kind: IdlErrorKind::UnterminatedComment
                                }));
                            }
                            if bytes[self.index + 1] == b'/' && bytes[self.index] == b'*' {
                                self.index += 2;
                                break;
                            }
                        }
                        return token(if doc {
                            TokenType::DocComment
                        } else {
                            TokenType::RangeComment
                        }, self);
                    },
                    b'/' => {
                        while self.index < bytes.len() && !is_crlf(bytes[self.index]) {
                            self.index += 1;
                        }
                        return token(TokenType::LineComment, self);
                    },
                    _ => return Some(Err(IdlError { kind: IdlErrorKind::UnexpectedCharacter }))
                };
            },

            _ => Some(Err(IdlError { kind: IdlErrorKind::UnexpectedCharacter }))
        }
    }
}

#[derive(Debug)]
pub enum IdlErrorKind {
    UnexpectedCharacter,
    UnterminatedComment,
    UnexpectedEnd,
    UnexpectedToken,
}

#[derive(Debug)]
pub struct IdlError {
    pub kind: IdlErrorKind,
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<Token<'a>, IdlError>;

    fn next(&mut self) -> Option<Result<Token<'a>, IdlError>> {
        let mut res;
        loop {
            res = self.lex();
            if let Some(Ok(token @ Token { .. })) = res {
                if token.ty == TokenType::DocComment {
                    self.last_doc_comment = Some(token);
                }
                if self.skip_whitespace && token.ty == TokenType::Whitespace {
                    continue;
                }
                if self.skip_comments {
                    match token.ty {
                        TokenType::RangeComment |
                        TokenType::LineComment |
                        TokenType::DocComment => continue,
                        _ => {}
                    }
                }
            }
            break;
        }
        res
    }
}

#[test]
fn test_enum() {
    let lexer = Lexer::new(
"enum Suit {
  SPADES, DIAMONDS
}");
    let tokens = lexer.map(|r| {
        let t = r.unwrap();
        (t.ty, t.text)
    }).collect::<Vec<_>>();
    assert_eq!(&tokens[..], &[
        (TokenType::Enum, "enum"),
        (TokenType::Whitespace, " "),
        (TokenType::Ident, "Suit"),
        (TokenType::Whitespace, " "),
        (TokenType::LBrace, "{"),
        (TokenType::Whitespace, "\n  "),
        (TokenType::Ident, "SPADES"),
        (TokenType::Comma, ","),
        (TokenType::Whitespace, " "),
        (TokenType::Ident, "DIAMONDS"),
        (TokenType::Whitespace, "\n"),
        (TokenType::RBrace, "}")
    ]);
}

#[test]
fn test_comment() {
    let lexer = Lexer::new(
"/** a doc comment */
enum/*range comment*/Suit2 { // a line comment
}");
    let tokens = lexer.map(|r| {
        let t = r.unwrap();
        (t.ty, t.text)
    }).collect::<Vec<_>>();
    assert_eq!(&tokens[..], &[
        (TokenType::DocComment, "/** a doc comment */"),
        (TokenType::Whitespace, "\n"),
        (TokenType::Enum, "enum"),
        (TokenType::RangeComment, "/*range comment*/"),
        (TokenType::Ident, "Suit2"),
        (TokenType::Whitespace, " "),
        (TokenType::LBrace, "{"),
        (TokenType::Whitespace, " "),
        (TokenType::LineComment, "// a line comment"),
        (TokenType::Whitespace, "\n"),
        (TokenType::RBrace, "}")
    ]);
}

//fn parse_annotation(lexer: &mut Lexer) {
//}

fn parse_type<'a>(lexer: &mut Lexer) -> Result<Schema<'a>, IdlError> {
    match lexer.expect_next() {
        Ok(Token { ty: TokenType::Array, .. }) => {
            try!(lexer.expect_and_consume(TokenType::LAngle));
            let ty = try!(parse_type(lexer));
            try!(lexer.expect_and_consume(TokenType::RAngle));
            Ok(Schema::Array { items: Box::new(ty) })
        },
        Ok(Token { ty: TokenType::Map, .. }) => {
            try!(lexer.expect_and_consume(TokenType::LAngle));
            let ty = try!(parse_type(lexer));
            try!(lexer.expect_and_consume(TokenType::RAngle));
            Ok(Schema::Map { values: Box::new(ty) })
        },
        Ok(Token { ty: TokenType::Union, .. }) => {
            try!(lexer.expect_and_consume(TokenType::LBrace));
            let mut tys = vec![];
            let mut first = true;
            loop {
                match lexer.clone().expect_next() {
                    Ok(Token { ty: TokenType::RBrace, .. }) => break,
                    Ok(_) => {
                        if !first {
                            try!(lexer.expect_and_consume(TokenType::Comma));
                        }
                        tys.push(try!(parse_type(lexer)));
                    },
                    Err(err) => return Err(err),
                };
                first = false;
            }
            try!(lexer.expect_and_consume(TokenType::RBrace));
            Ok(Schema::Union { tys: tys })
        },
        Ok(Token { ty: TokenType::Boolean, .. }) => Ok(Schema::Boolean),
        Ok(Token { ty: TokenType::Bytes, .. }) => Ok(Schema::Bytes),
        Ok(Token { ty: TokenType::Int, .. }) => Ok(Schema::Int),
        Ok(Token { ty: TokenType::String, .. }) => Ok(Schema::String),
        Ok(Token { ty: TokenType::Float, .. }) => Ok(Schema::Float),
        Ok(Token { ty: TokenType::Double, .. }) => Ok(Schema::Double),
        Ok(Token { ty: TokenType::Long, .. }) => Ok(Schema::Long),
        Ok(Token { ty: TokenType::Null, .. }) => Ok(Schema::Null),
        // TODO: need to handle reference types
        Ok(Token { ty: TokenType::Ident, .. }) => Err(IdlError {
                kind: IdlErrorKind::UnexpectedToken
        }),
        Err(err) => Err(err),
        _ => Err(IdlError { kind: IdlErrorKind::UnexpectedToken }),
    }
}

fn parse_field<'a>(lexer: &mut Lexer<'a>) -> Result<Field<'a>, IdlError> {
    lexer.clear_last_doc_comment();
    let ty = try!(parse_type(lexer));
    let doc = lexer.last_doc_comment().map(|t| t.comment_contents());
    let name = try!(lexer.expect_and_consume(TokenType::Ident));
    // TODO: parse variable names and defaults
    try!(lexer.expect_and_consume(TokenType::Semi));

    Ok(Field {
        name: Cow::Borrowed(name.text),
        doc: doc,
        ty: ty,
    })
}

fn parse_record<'a>(lexer: &mut Lexer<'a>) -> Result<Schema<'a>, IdlError> {
    lexer.clear_last_doc_comment();
    let error = match lexer.expect_next() {
        Ok(Token { ty: TokenType::Record, .. }) => false,
        Ok(Token { ty: TokenType::Error, .. }) => true,
        Err(err) => return Err(err),
        _ => return Err(IdlError { kind: IdlErrorKind::UnexpectedToken }),
    };
    let doc = lexer.last_doc_comment().map(|t| t.comment_contents());
    let name_token = try!(lexer.expect_and_consume(TokenType::Ident));
    try!(lexer.expect_and_consume(TokenType::LBrace));

    let mut fields = vec![];
    loop {
        match lexer.clone().expect_next() {
            Ok(Token { ty: TokenType::RBrace, .. }) => break,
            Ok(_) => fields.push(try!(parse_field(lexer))),
            Err(err) => return Err(err),
        };
    }

    try!(lexer.expect_and_consume(TokenType::RBrace));

    let data = Rc::new(RecordSchema::new(Cow::Borrowed(name_token.text), doc, fields));
    Ok(if error { Schema::Error(data) } else { Schema::Record(data) })
}

fn parse_enum<'a>(lexer: &mut Lexer<'a>) -> Result<Schema<'a>, IdlError> {
    lexer.clear_last_doc_comment();
    try!(lexer.expect_and_consume(TokenType::Enum));
    let doc = lexer.last_doc_comment().map(|t| t.comment_contents());
    let name_token = try!(lexer.expect_and_consume(TokenType::Ident));
    try!(lexer.expect_and_consume(TokenType::LBrace));

    let mut symbols = vec![];
    let mut first = true;
    loop {
        match lexer.clone().expect_next() {
            Ok(Token { ty: TokenType::RBrace, .. }) => break,
            Ok(_) => {
                if !first {
                    try!(lexer.expect_and_consume(TokenType::Comma));
                }
                lexer.clear_last_doc_comment();
                let sym_name = try!(lexer.expect_and_consume(TokenType::Ident)).text;
                let doc = lexer.last_doc_comment().map(|t| t.comment_contents());
                symbols.push(EnumSymbol { name: Cow::Borrowed(sym_name), doc: doc });
            },
            Err(err) => return Err(err),
        };
        first = false;
    }

    try!(lexer.expect_and_consume(TokenType::RBrace));

    Ok(Schema::Enum(Rc::new(EnumSchema {
        name: Cow::Borrowed(name_token.text),
        doc: doc,
        symbols: symbols,
    })))
}

fn parse_fixed<'a>(lexer: &mut Lexer<'a>) -> Result<Schema<'a>, IdlError> {
    lexer.clear_last_doc_comment();
    try!(lexer.expect_and_consume(TokenType::Fixed));
    let doc = lexer.last_doc_comment().map(|t| t.comment_contents());
    let name_token = try!(lexer.expect_and_consume(TokenType::Ident));
    try!(lexer.expect_and_consume(TokenType::LParen));

    let size = try!(lexer.expect_and_consume(TokenType::Integer)).text.parse().unwrap();

    try!(lexer.expect_and_consume(TokenType::RParen));
    try!(lexer.expect_and_consume(TokenType::Semi));

    Ok(Schema::Fixed(Rc::new(FixedSchema {
        name: name_token.text.into(),
        doc: doc,
        size: size,
    })))
}

pub fn parse_idl(src: &str) -> Result<Protocol, IdlError> {
    let mut lexer = Lexer::new(src);
    lexer.set_skip_whitespace(true);
    lexer.set_skip_comments(true);

    // TODO: annotations

    try!(lexer.expect_and_consume(TokenType::Protocol));
    let doc = lexer.last_doc_comment().map(|t| t.comment_contents());
    let name_token = try!(lexer.expect_and_consume(TokenType::Ident));
    try!(lexer.expect_and_consume(TokenType::LBrace));

    let mut tys = vec![];
    loop {
        match lexer.clone().expect_next() {
            Ok(Token { ty: TokenType::RBrace, .. }) => break,
            Ok(Token { ty: TokenType::Record, .. }) |
            Ok(Token { ty: TokenType::Error, .. }) => tys.push(try!(parse_record(&mut lexer))),
            Ok(Token { ty: TokenType::Enum, .. }) => tys.push(try!(parse_enum(&mut lexer))),
            Ok(Token { ty: TokenType::Fixed, .. }) => tys.push(try!(parse_fixed(&mut lexer))),
            Err(err) => return Err(err),
            _ => return Err(IdlError { kind: IdlErrorKind::UnexpectedToken }),
        };
    }

    try!(lexer.expect_and_consume(TokenType::RBrace));

    Ok(Protocol {
        name: Cow::Borrowed(name_token.text),
        doc: doc,
        tys: tys,
        messages: vec![]
    })
}

#[test]
fn test_parse_protocol() {
    let res = parse_idl("
/** a test IDL file */
protocol Test1 {
}");
    let protocol = res.unwrap();
    assert_eq!(protocol.name, "Test1");
    assert_eq!(protocol.doc, Some(Cow::Borrowed("a test IDL file")));
}

#[test]
fn test_parse_doc_comment() {
    let res = parse_idl(r#"
/**
 * Here's some example code:
 *
 *   print("something")
 */
protocol Test1 {
}"#);
    let protocol = res.unwrap();
    assert_eq!(protocol.name, "Test1");
    assert_eq!(protocol.doc, Some(Cow::Borrowed(
        "Here's some example code:\n\n  print(\"something\")"
    )));
}

#[test]
fn test_parse_record() {
    let res = parse_idl(r#"
/** Comment one. */
protocol Test1 {
    record First {
        int i;
        /** banana */
        string foo;
    }
    /** Comment two. */
    record Second {
        array<long> nums;
    }
    error Third {
        map<boolean> enabledFeatures;
        union { int, boolean, string } bar;
    }
}"#);
    let protocol = res.unwrap();
    assert_eq!(protocol.name, "Test1");
    assert_eq!(protocol.doc, Some(Cow::Borrowed("Comment one.")));
    assert_eq!(protocol.tys.len(), 3);

    let first = &protocol.tys[0];
    if let &Schema::Record(ref r) = first {
        assert_eq!(r.name, Cow::Borrowed("First"));
        assert_eq!(r.doc, None);
        assert_eq!(r.fields[0].name, Cow::Borrowed("i"));
        assert_eq!(r.fields[0].doc, None);
        assert_eq!(r.fields[0].ty, Schema::Int);
        assert_eq!(r.fields[1].name, Cow::Borrowed("foo"));
        assert_eq!(r.fields[1].doc, Some(Cow::Borrowed("banana")));
        assert_eq!(r.fields[1].ty, Schema::String);
    } else {
        panic!("wrong type");
    }

    let second = &protocol.tys[1];
    if let &Schema::Record(ref r) = second {
        assert_eq!(r.name, Cow::Borrowed("Second"));
        assert_eq!(r.doc, Some(Cow::Borrowed("Comment two.")));
        assert_eq!(r.fields[0].name, Cow::Borrowed("nums"));
        assert_eq!(r.fields[0].doc, None);
        if let Schema::Array { ref items } = r.fields[0].ty {
            assert_eq!(**items, Schema::Long);
        } else {
            panic!("wrong type");
        }
    } else {
        panic!("wrong type");
    }

    let third = &protocol.tys[2];
    if let &Schema::Error(ref r) = third {
        assert_eq!(r.name, Cow::Borrowed("Third"));
        assert_eq!(r.doc, None);
        assert_eq!(r.fields[0].name, Cow::Borrowed("enabledFeatures"));
        assert_eq!(r.fields[0].doc, None);
        if let Schema::Map { ref values } = r.fields[0].ty {
            assert_eq!(**values, Schema::Boolean);
        } else {
            panic!("wrong type");
        }
        assert_eq!(r.fields[1].name, Cow::Borrowed("bar"));
        assert_eq!(r.fields[1].doc, None);
        if let Schema::Union { ref tys } = r.fields[1].ty {
            assert_eq!(tys, &[Schema::Int, Schema::Boolean, Schema::String]);
        } else {
            panic!("wrong type");
        }
    } else {
        panic!("wrong type");
    }
}

#[test]
fn test_parse_enum() {
    let res = parse_idl(r#"
protocol TestEnum {
    /** Only two values */
    enum TimePeriods {
        AM, PM
    }
    enum Seasons {
        SPRING,
        // This is ignored.
        SUMMER,
        FALL,
        /**
         * Winter is coming.
         */
        WINTER
    }
}"#);
    let protocol = res.unwrap();
    assert_eq!(protocol.name, "TestEnum");
    assert_eq!(protocol.tys.len(), 2);

    let first = &protocol.tys[0];
    if let &Schema::Enum(ref e) = first {
        assert_eq!(e.name, Cow::Borrowed("TimePeriods"));
        assert_eq!(e.doc, Some(Cow::Borrowed("Only two values")));
        assert_eq!(&e.symbols, &[
            EnumSymbol { name: Cow::Borrowed("AM"), doc: None },
            EnumSymbol { name: Cow::Borrowed("PM"), doc: None },
        ]);
    } else {
        panic!("wrong type");
    }

    let second = &protocol.tys[1];
    if let &Schema::Enum(ref e) = second {
        assert_eq!(e.name, Cow::Borrowed("Seasons"));
        assert_eq!(e.doc, None);
        assert_eq!(&e.symbols, &[
            EnumSymbol { name: Cow::Borrowed("SPRING"), doc: None },
            EnumSymbol { name: Cow::Borrowed("SUMMER"), doc: None },
            EnumSymbol { name: Cow::Borrowed("FALL"), doc: None },
            EnumSymbol {
                name: Cow::Borrowed("WINTER"),
                doc: Some(Cow::Borrowed("Winter is coming."))
            },
        ]);
    } else {
        panic!("wrong type");
    }

}

#[test]
fn test_parse_fixed() {
    let res = parse_idl(r#"
protocol TestFixed {
    /** An identifier */
    fixed Guid(16);

    fixed IPv4(4);
}"#);
    let protocol = res.unwrap();
    assert_eq!(protocol.name, "TestFixed");
    assert_eq!(protocol.tys.len(), 2);

    let first = &protocol.tys[0];
    if let &Schema::Fixed(ref f) = first {
        assert_eq!(f.name, Cow::Borrowed("Guid"));
        assert_eq!(f.doc, Some(Cow::Borrowed("An identifier")));
        assert_eq!(f.size, 16);
    } else {
        panic!("wrong type");
    }

    let second = &protocol.tys[1];
    if let &Schema::Fixed(ref f) = second {
        assert_eq!(f.name, Cow::Borrowed("IPv4"));
        assert_eq!(f.doc, None);
        assert_eq!(f.size, 4);
    } else {
        panic!("wrong type");
    }

}
