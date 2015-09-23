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
use std::cell::RefCell;
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

// different from Range in that this struct is Copy
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct SpanRange {
    start: usize,
    end: usize,
}

impl Into<Range<usize>> for SpanRange {
    fn into(self) -> Range<usize> {
        Range { start: self.start, end: self.end }
    }
}

impl From<Range<usize>> for SpanRange {
    fn from(range: Range<usize>) -> SpanRange {
        SpanRange { start: range.start, end: range.end }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Span {
    // format: 0b0LLL_LLLL_SSSS_SSSS_SSSS_SSSS_SSSS_SSSS
    // format: 0b1DDD_DDDD_DDDD_DDDD_DDDD_DDDD_DDDD_DDDD
    // D = ID, L = length, S = start index
    // The highest bit is a flag bit:
    // - If set, data is an ID number used to look up the start and end
    // - If not set, data is 24 bits of index and 7 bits length
    data: u32,
}

#[derive(Debug)]
pub struct SourceManager<'a> {
    src: &'a str,
    line_indexes: RefCell<Option<Vec<usize>>>, // index 0 is line 1's start index (which is 0)
    span_ranges: RefCell<Vec<SpanRange>>,
}

impl<'a> SourceManager<'a> {
    fn new(src: &str) -> SourceManager {
        SourceManager {
            src: src,
            line_indexes: RefCell::new(None),
            span_ranges: RefCell::new(vec![]),
        }
    }

    pub fn src_slice(&self, range: SpanRange) -> &'a str {
        let range: Range<usize> = range.into();
        &self.src[range]
    }

    fn build_line_index(&self) {
        let mut self_line_indexes = self.line_indexes.borrow_mut();
        if self_line_indexes.is_some() {
            return;
        }
        let bytes = self.src.as_bytes();
        // average line length is at least this much, right?
        let mut line_indexes = Vec::with_capacity(bytes.len() / 25);
        line_indexes.push(0);
        line_indexes.extend(bytes.iter().enumerate()
                            .filter_map(|(i, b)| if *b == b'\n' { Some(i + 1) } else { None }));
        *self_line_indexes = Some(line_indexes);
    }

    fn get_line(&self, index: usize) -> usize {
        self.build_line_index();
        let line_indexes_ref = self.line_indexes.borrow();
        let line_indexes = line_indexes_ref.as_ref().unwrap();

        (match line_indexes.binary_search(&index) {
            Ok(i) => i,
            Err(i) => i - 1,
        } + 1) // index 0 = line 1
    }

    fn get_column(&self, index: usize) -> usize {
        let bytes = self.src.as_bytes();
        bytes[..index].iter().rev().take_while(|b| **b != b'\n').count() + 1 // index 0 = col 1
    }

    //fn get_span(&self, range: SpanRange) -> Span {
    //    let len = range.end - range.start;
    //    // Test `len` first because it will usually be the one too large.
    //    if len > 0x7F || range.start > 0xFF_FFFF {
    //        let mut span_ranges = self.span_ranges.borrow_mut();
    //        let id = span_ranges.len();
    //        span_ranges.push(SpanRange { start: range.start, end: range.end });
    //        Span { data: (0x8000_0000 | id) as u32 }
    //    } else {
    //        Span { data: (range.start | len << 24) as u32 }
    //    }
    //}
    //
    //fn get_span_range(&self, span: &Span) -> SpanRange {
    //    if span.data & 0x8000_0000 > 0 {
    //        let span_ranges = self.span_ranges.borrow_mut();
    //        let span_range = span_ranges[(span.data & 0x7FFF_FFFF) as usize];
    //        SpanRange { start: span_range.start, end: span_range.end }
    //    } else {
    //        let start = span.data & 0xFF_FFFF;
    //        SpanRange { start: start as usize, end: (start + (span.data >> 24)) as usize }
    //    }
    //}
}

#[test]
fn test_line_index() {
    let src = "hi\nthere\n\nmore";
    let sm = SourceManager::new(src);
    sm.build_line_index();
    assert_eq!(sm.line_indexes.borrow().as_ref().unwrap(), &[0, 3, 9, 10]);

    let src = "\nhowdy\n\n";
    let sm = SourceManager::new(src);
    sm.build_line_index();
    assert_eq!(sm.line_indexes.borrow().as_ref().unwrap(), &[0, 1, 7, 8]);
}

#[test]
fn test_get_line() {
    let src = "hi\nthere\n\nmore";
    let sm = SourceManager::new(src);
    assert_eq!(sm.get_line(0), 1);
    assert_eq!(sm.get_line(1), 1);
    assert_eq!(sm.get_line(2), 1);
    assert_eq!(sm.get_line(3), 2);
    assert_eq!(sm.get_line(4), 2);
    assert_eq!(sm.get_line(7), 2);
    assert_eq!(sm.get_line(8), 2);
    assert_eq!(sm.get_line(9), 3);
    assert_eq!(sm.get_line(10), 4);
    assert_eq!(sm.get_line(11), 4);
    assert_eq!(sm.get_line(13), 4);

    let src = "\nhowdy\n\n";
    let sm = SourceManager::new(src);
    assert_eq!(sm.get_line(0), 1);
    assert_eq!(sm.get_line(1), 2);
    assert_eq!(sm.get_line(2), 2);
    assert_eq!(sm.get_line(6), 2);
    assert_eq!(sm.get_line(7), 3);
}

#[test]
fn test_get_column() {
    let src = "hi\nthere\n\nmore";
    let sm = SourceManager::new(src);
    assert_eq!(sm.get_column(0), 1);
    assert_eq!(sm.get_column(1), 2);
    assert_eq!(sm.get_column(2), 3);
    assert_eq!(sm.get_column(3), 1);
    assert_eq!(sm.get_column(4), 2);
    assert_eq!(sm.get_column(7), 5);
    assert_eq!(sm.get_column(8), 6);
    assert_eq!(sm.get_column(9), 1);
    assert_eq!(sm.get_column(10), 1);
    assert_eq!(sm.get_column(11), 2);
    assert_eq!(sm.get_column(13), 4);

    let src = "\nhowdy\n\n";
    let sm = SourceManager::new(src);
    assert_eq!(sm.get_column(0), 1);
    assert_eq!(sm.get_column(1), 1);
    assert_eq!(sm.get_column(2), 2);
    assert_eq!(sm.get_column(6), 6);
    assert_eq!(sm.get_column(7), 1);
    assert_eq!(sm.get_column(8), 1);
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct Token {
    ty: TokenType,
    range: SpanRange,
}

impl Token {
    fn comment_contents<'a>(&self, src: &'a str) -> Cow<'a, str> {
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
            TokenType::LineComment => Cow::Borrowed(&src[2..src.len()]),
            TokenType::RangeComment => range_comment_contents(&src[2..src.len()-2]),
            TokenType::DocComment => range_comment_contents(&src[3..src.len()-2]),
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

#[derive(Debug, Clone)]
pub struct Lexer<'a, 'b: 'a> {
    source_manager: &'a SourceManager<'b>,
    skip_whitespace: bool,
    skip_comments: bool,

    index: usize,
    saved_indexes: Vec<usize>,
    token: Option<Result<Token, Box<IdlError>>>,
    last_doc_comment: Option<Token>,
}

impl<'a, 'b> Lexer<'a, 'b> {
    pub fn new(source_manager: &'a SourceManager<'b>) -> Lexer<'a, 'b> {
        Lexer {
            source_manager: source_manager,
            skip_whitespace: false,
            skip_comments: false,
            index: 0,
            saved_indexes: Vec::with_capacity(4),
            token: None,
            last_doc_comment: None,
        }
    }

    pub fn src(&self) -> &'b str {
        self.source_manager.src
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

    pub fn last_doc_comment(&self) -> Option<Token> {
        self.last_doc_comment
    }

    pub fn clear_last_doc_comment(&mut self) {
        self.last_doc_comment = None;
    }

    pub fn save(&mut self) {
        self.saved_indexes.push(self.index);
    }

    pub fn restore(&mut self) {
        self.index = self.saved_indexes.pop().unwrap();
    }

    pub fn expect_next_ty(&mut self, ty: TokenType) -> Result<Token, Box<IdlError>> {
        match self.next() {
            Some(Ok(token)) => {
                if token.ty == ty {
                    Ok(token)
                } else {
                    Err(Box::new(IdlError::new(
                        IdlErrorKind::UnexpectedToken,
                        self.source_manager.get_line(token.range.start),
                        self.source_manager.get_column(token.range.start)
                    )))
                }
            },
            Some(err @ Err(_)) => err,
            None => Err(Box::new(IdlError::new(
                IdlErrorKind::UnexpectedEnd,
                self.source_manager.get_line(self.index),
                self.source_manager.get_column(self.index)
            ))),
        }
    }

    pub fn try_consume(&mut self, ty: TokenType) -> bool {
        self.save();
        let next = self.next();
        self.restore();
        match next {
            Some(Ok(token)) if token.ty == ty => {
                self.next();
                true
            },
            _ => false,
        }
    }

    pub fn expect_next(&mut self) -> Result<Token, Box<IdlError>> {
        match self.next() {
            Some(token @ Ok(_)) => token,
            Some(err @ Err(_)) => err,
            None => Err(Box::new(IdlError::new(
                IdlErrorKind::UnexpectedEnd,
                self.source_manager.get_line(self.index),
                self.source_manager.get_column(self.index)
            ))),
        }
    }

    // I knew how to implement a lexer, but I did skim this example presented as a fast lexer:
    // http://www.cs.dartmouth.edu/~mckeeman/cs48/mxcom/doc/lexInCpp.html
    // linked from the bottom of http://www.cs.dartmouth.edu/~mckeeman/cs48/mxcom/doc/Lexing.html
    // https://github.com/apache/avro/blob/eb31746cd5efd5e2c9c57780a651afaccd5cfe06/lang/java/compiler/src/main/javacc/org/apache/avro/compiler/idl/idl.jj
    // The error is boxed so that it can't enlarge the return value. It definitely
    // isn't the common case.
    fn lex(&mut self) -> Option<Result<Token, Box<IdlError>>> {
        let bytes = self.source_manager.src.as_bytes();

        let start = self.index;

        let c = if self.index < bytes.len() {
            bytes[self.index] // could use get_unchecked() for speed
        } else {
            return None;
        };
        self.index += 1;

        let token = |ty, this: &mut Lexer<'a, 'b>| Some(Ok(Token {
            ty: ty, range: (start..this.index).into()
        }));

        match c {
            b'(' => token(TokenType::LParen, self),
            b')' => token(TokenType::RParen, self),
            b'{' => token(TokenType::LBrace, self),
            b'}' => token(TokenType::RBrace, self),
            b'[' => token(TokenType::LBracket, self),
            b']' => token(TokenType::RBracket, self),
            b':' => token(TokenType::Colon, self),
            b';' => token(TokenType::Semi, self),
            b',' => token(TokenType::Comma, self),
            b'@' => token(TokenType::At, self),
            b'=' => token(TokenType::Equals, self),
            b'.' => token(TokenType::Dot, self),
            b'-' => token(TokenType::Hyphen, self),
            b'<' => token(TokenType::LAngle, self),
            b'>' => token(TokenType::RAngle, self),
            b'`' => token(TokenType::Backquote, self),

            b' ' | b'\t' | b'\r' | b'\n' => {
                while self.index < bytes.len() && is_ascii_whitespace(bytes[self.index]) {
                    self.index += 1;
                }
                token(TokenType::Whitespace, self)
            },

            b'A' ... b'Z' | b'a' ... b'z' | b'_' => {
                while self.index < bytes.len() && is_ascii_alphanumeric(bytes[self.index]) {
                    self.index += 1;
                }
                let token_text = &self.source_manager.src[start..self.index];
                let token_ty = TokenType::alphanumeric_token_from_str(token_text);
                token(token_ty, self)
            },

            b'0' ... b'9' => {
                while self.index < bytes.len() && is_ascii_digit(bytes[self.index]) {
                    self.index += 1;
                }
                token(TokenType::Integer, self)
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
                                return Some(Err(Box::new(IdlError::new(
                                    IdlErrorKind::UnterminatedComment,
                                    // It is most helpful to show where the comment starts.
                                    self.source_manager.get_line(start),
                                    self.source_manager.get_column(start)
                                ))));
                            }
                            if bytes[self.index + 1] == b'/' && bytes[self.index] == b'*' {
                                self.index += 2;
                                break;
                            }
                        }
                        token(if doc {
                            TokenType::DocComment
                        } else {
                            TokenType::RangeComment
                        }, self)
                    },
                    b'/' => {
                        while self.index < bytes.len() && !is_crlf(bytes[self.index]) {
                            self.index += 1;
                        }
                        token(TokenType::LineComment, self)
                    },
                    _ => Some(Err(Box::new(IdlError::new(
                        IdlErrorKind::UnexpectedCharacter,
                        self.source_manager.get_line(self.index),
                        self.source_manager.get_column(self.index)
                    )))),
                }
            },

            _ => Some(Err(Box::new(IdlError::new(
                IdlErrorKind::UnexpectedCharacter,
                self.source_manager.get_line(self.index),
                self.source_manager.get_column(self.index)
            )))),
        }
    }
}

#[derive(Debug, Clone)]
pub enum IdlErrorKind {
    UnexpectedCharacter,
    UnterminatedComment,
    UnexpectedEnd,
    UnexpectedToken,
}

#[derive(Debug, Clone)]
pub struct IdlError {
    pub kind: IdlErrorKind,
    pub line: usize,
    pub column: usize,
}

impl IdlError {
    pub fn new(kind: IdlErrorKind, line: usize, column: usize) -> IdlError {
        IdlError {
            kind: kind,
            line: line,
            column: column,
        }
    }
}

impl<'a, 'b> Iterator for Lexer<'a, 'b> {
    type Item = Result<Token, Box<IdlError>>;

    fn next(&mut self) -> Option<Result<Token, Box<IdlError>>> {
        if let Some(Err(_)) = self.token {
            return None;
        }
        loop {
            self.token = self.lex();
            if let Some(Ok(token @ Token { .. })) = self.token {
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
        self.token.clone()
    }
}

#[test]
fn test_enum() {
    let sm = SourceManager::new(
"enum Suit {
  SPADES, DIAMONDS
}");
    let lexer = Lexer::new(&sm);
    let tokens = lexer.map(|r| {
        let t = r.unwrap();
        (t.ty, sm.src_slice(t.range))
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
    let sm = SourceManager::new(
"/** a doc comment */
enum/*range comment*/Suit2 { // a line comment
}");
    let lexer = Lexer::new(&sm);
    let tokens = lexer.map(|r| {
        let t = r.unwrap();
        (t.ty, sm.src_slice(t.range))
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

fn parse_type<'a>(lexer: &mut Lexer) -> Result<Schema<'a>, Box<IdlError>> {
    match lexer.expect_next() {
        Ok(Token { ty: TokenType::Array, .. }) => {
            try!(lexer.expect_next_ty(TokenType::LAngle));
            let ty = try!(parse_type(lexer));
            try!(lexer.expect_next_ty(TokenType::RAngle));
            Ok(Schema::Array { items: Box::new(ty) })
        },
        Ok(Token { ty: TokenType::Map, .. }) => {
            try!(lexer.expect_next_ty(TokenType::LAngle));
            let ty = try!(parse_type(lexer));
            try!(lexer.expect_next_ty(TokenType::RAngle));
            Ok(Schema::Map { values: Box::new(ty) })
        },
        Ok(Token { ty: TokenType::Union, .. }) => {
            try!(lexer.expect_next_ty(TokenType::LBrace));
            let mut tys = vec![];
            let mut first = true;
            loop {
                lexer.save();
                let next = lexer.expect_next();
                lexer.restore();
                match next {
                    Ok(Token { ty: TokenType::RBrace, .. }) => break,
                    Ok(_) => {
                        if !first {
                            try!(lexer.expect_next_ty(TokenType::Comma));
                        }
                        tys.push(try!(parse_type(lexer)));
                    },
                    Err(err) => return Err(err),
                };
                first = false;
            }
            try!(lexer.expect_next_ty(TokenType::RBrace));
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
        Ok(Token { ty: TokenType::Ident, range: SpanRange { start, .. }, .. }) =>
            Err(Box::new(IdlError::new(
                IdlErrorKind::UnexpectedToken,
                lexer.source_manager.get_line(start),
                lexer.source_manager.get_column(start)
            ))),
        Err(err) => Err(err),
        Ok(Token { range: SpanRange { start, .. }, .. }) =>
            Err(Box::new(IdlError::new(
                IdlErrorKind::UnexpectedToken,
                lexer.source_manager.get_line(start),
                lexer.source_manager.get_column(start)
            ))),
    }
}

fn parse_field<'a, 'b>(lexer: &mut Lexer<'a, 'b>) -> Result<Field<'b>, Box<IdlError>> {
    lexer.clear_last_doc_comment();
    let ty = try!(parse_type(lexer));
    let doc = lexer.last_doc_comment().map(|t|
        t.comment_contents(lexer.source_manager.src_slice(t.range))
    );
    let name_token = try!(lexer.expect_next_ty(TokenType::Ident));
    let name = lexer.source_manager.src_slice(name_token.range);
    // TODO: parse variable names and defaults
    try!(lexer.expect_next_ty(TokenType::Semi));

    Ok(Field {
        name: Cow::Borrowed(name),
        doc: doc,
        ty: ty,
    })
}

fn parse_record<'a, 'b>(lexer: &mut Lexer<'a, 'b>) -> Result<Schema<'b>, Box<IdlError>> {
    lexer.clear_last_doc_comment();
    let error = match lexer.expect_next() {
        Ok(Token { ty: TokenType::Record, .. }) => false,
        Ok(Token { ty: TokenType::Error, .. }) => true,
        Err(err) => return Err(err),
        Ok(Token { range: SpanRange { start, .. }, .. }) => return Err(Box::new(IdlError {
            kind: IdlErrorKind::UnexpectedToken,
            line: lexer.source_manager.get_line(start),
            column: lexer.source_manager.get_column(start),
        })),
    };
    let doc = lexer.last_doc_comment().map(|t|
        t.comment_contents(lexer.source_manager.src_slice(t.range))
    );
    let name_token = try!(lexer.expect_next_ty(TokenType::Ident));
    try!(lexer.expect_next_ty(TokenType::LBrace));

    let mut fields = vec![];
    loop {
        lexer.save();
        let next = lexer.expect_next();
        lexer.restore();
        match next {
            Ok(Token { ty: TokenType::RBrace, .. }) => break,
            Ok(_) => fields.push(try!(parse_field(lexer))),
            Err(err) => return Err(err),
        };
    }

    try!(lexer.expect_next_ty(TokenType::RBrace));

    let name = lexer.source_manager.src_slice(name_token.range);
    let data = Rc::new(RecordSchema::new(Cow::Borrowed(name), doc, fields));
    Ok(if error { Schema::Error(data) } else { Schema::Record(data) })
}

fn parse_enum<'a, 'b>(lexer: &mut Lexer<'a, 'b>) -> Result<Schema<'b>, Box<IdlError>> {
    lexer.clear_last_doc_comment();
    try!(lexer.expect_next_ty(TokenType::Enum));
    let doc = lexer.last_doc_comment().map(|t|
        t.comment_contents(lexer.source_manager.src_slice(t.range))
    );
    let name_token = try!(lexer.expect_next_ty(TokenType::Ident));
    try!(lexer.expect_next_ty(TokenType::LBrace));

    let mut symbols = vec![];
    let mut first = true;
    loop {
        lexer.save();
        let next = lexer.expect_next();
        lexer.restore();
        match next {
            Ok(Token { ty: TokenType::RBrace, .. }) => break,
            Ok(_) => {
                if !first {
                    try!(lexer.expect_next_ty(TokenType::Comma));
                }
                lexer.clear_last_doc_comment();
                let sym_token = try!(lexer.expect_next_ty(TokenType::Ident));
                let sym_name = lexer.source_manager.src_slice(sym_token.range);
                let doc = lexer.last_doc_comment().map(|t|
                    t.comment_contents(lexer.source_manager.src_slice(t.range))
                );
                symbols.push(EnumSymbol { name: Cow::Borrowed(sym_name), doc: doc });
            },
            Err(err) => return Err(err),
        };
        first = false;
    }

    try!(lexer.expect_next_ty(TokenType::RBrace));

    Ok(Schema::Enum(Rc::new(EnumSchema {
        name: Cow::Borrowed(lexer.source_manager.src_slice(name_token.range)),
        doc: doc,
        symbols: symbols,
    })))
}

fn parse_fixed<'a, 'b>(lexer: &mut Lexer<'a, 'b>) -> Result<Schema<'b>, Box<IdlError>> {
    lexer.clear_last_doc_comment();
    try!(lexer.expect_next_ty(TokenType::Fixed));
    let doc = lexer.last_doc_comment().map(|t|
        t.comment_contents(lexer.source_manager.src_slice(t.range))
    );
    let name_token = try!(lexer.expect_next_ty(TokenType::Ident));
    try!(lexer.expect_next_ty(TokenType::LParen));

    let size_token = try!(lexer.expect_next_ty(TokenType::Integer));
    let size = lexer.source_manager.src_slice(size_token.range).parse().unwrap();

    try!(lexer.expect_next_ty(TokenType::RParen));
    try!(lexer.expect_next_ty(TokenType::Semi));

    Ok(Schema::Fixed(Rc::new(FixedSchema {
        name: Cow::Borrowed(lexer.source_manager.src_slice(name_token.range)),
        doc: doc,
        size: size,
    })))
}

pub fn parse_idl(src: &str) -> Result<Protocol, Box<IdlError>> {
    let manager = SourceManager::new(src);
    let mut lexer = Lexer::new(&manager);
    lexer.set_skip_whitespace(true);
    lexer.set_skip_comments(true);

    // TODO: annotations

    try!(lexer.expect_next_ty(TokenType::Protocol));
    let doc = lexer.last_doc_comment().map(|t|
        t.comment_contents(lexer.source_manager.src_slice(t.range))
    );
    let name_token = try!(lexer.expect_next_ty(TokenType::Ident));
    try!(lexer.expect_next_ty(TokenType::LBrace));

    let mut tys = vec![];
    loop {
        lexer.save();
        let next = lexer.expect_next();
        lexer.restore();
        match next {
            Ok(Token { ty: TokenType::RBrace, .. }) => break,
            Ok(Token { ty: TokenType::Record, .. }) |
            Ok(Token { ty: TokenType::Error, .. }) => tys.push(try!(parse_record(&mut lexer))),
            Ok(Token { ty: TokenType::Enum, .. }) => tys.push(try!(parse_enum(&mut lexer))),
            Ok(Token { ty: TokenType::Fixed, .. }) => tys.push(try!(parse_fixed(&mut lexer))),
            Err(err) => return Err(err),
            Ok(Token { range: SpanRange { start, .. }, .. }) => return Err(Box::new(IdlError {
                kind: IdlErrorKind::UnexpectedToken,
                line: lexer.source_manager.get_line(start),
                column: lexer.source_manager.get_column(start),
            })),
        };
    }

    try!(lexer.expect_next_ty(TokenType::RBrace));

    Ok(Protocol {
        name: Cow::Borrowed(lexer.source_manager.src_slice(name_token.range)),
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
