
use std::borrow::Cow;
use std::ops::Range;

#[derive(Debug)]
struct Token<'a> {
    ty: TokenType,
    text: &'a str,
    range: Range<usize>,
}

#[derive(Debug, Copy, Clone, PartialEq)]
enum TokenType {
    Ident,

    Protocol,
    Null,
    Boolean,
    Int,
    Long,
    Float,
    Double,
    Bytes,
    String,
    Array,
    Record,
    Error,
    Enum,
    Fixed,

    LBrace,
    RBrace,
    Comma,
    Semi,

    RangeComment,
    DocComment,
    LineComment,
    Whitespace,
}

impl TokenType {
    fn alphanumeric_token_from_str(s: &str) -> TokenType {
        match s {
            "protocol" => TokenType::Protocol,
            "null" => TokenType::Null,
            "boolean" => TokenType::Boolean,
            "int" => TokenType::Int,
            "long" => TokenType::Long,
            "float" => TokenType::Float,
            "double" => TokenType::Double,
            "bytes" => TokenType::Bytes,
            "string" => TokenType::String,
            "array" => TokenType::Array,
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

fn is_crlf(c: u8) -> bool {
    c == b'\r' || c == b'\n'
}

#[derive(Debug, Copy, Clone)]
struct Lexer<'a> {
    src: &'a str,
    index: usize,
    line: usize,
    column: usize,
}

impl<'a> Lexer<'a> {
    pub fn new(src: &'a str) -> Lexer {
        Lexer { src: src, index: 0, line: 1, column: 1 }
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
}

#[derive(Debug)]
enum ErrorKind {
    UnexpectedCharacter,
    UnterminatedComment,
}

#[derive(Debug)]
struct Error {
    kind: ErrorKind
}

// I knew how to implement a lexer, but I did skim this example presented as a fast lexer:
// http://www.cs.dartmouth.edu/~mckeeman/cs48/mxcom/doc/lexInCpp.html
// linked from the bottom of http://www.cs.dartmouth.edu/~mckeeman/cs48/mxcom/doc/Lexing.html
impl<'a> Iterator for Lexer<'a> {
    type Item = Result<Token<'a>, Error>;

    fn next(&mut self) -> Option<Result<Token<'a>, Error>> {
        let bytes = self.src.as_bytes();
        let start = self.index;

        let c = if self.index < bytes.len() {
            bytes[self.index] // could use get_unchecked() for speed
        } else {
            return None;
        };
        self.index += 1;

        let token = |ty, this: &mut Lexer<'a>| Some(Ok(Token {
            ty: ty, text: &this.src[start..this.index], range: start..this.index
        }));

        match c {
            b'{' => return token(TokenType::LBrace, self),
            b'}' => return token(TokenType::RBrace, self),
            b',' => return token(TokenType::Comma, self),
            b';' => return token(TokenType::Semi, self),

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
                return Some(Ok(Token { ty: token_ty, text: token_text, range: start..self.index }));
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
                                return Some(Err(Error { kind: ErrorKind::UnterminatedComment }));
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
                    _ => return Some(Err(Error { kind: ErrorKind::UnexpectedCharacter }))
                };
            },

            _ => Some(Err(Error { kind: ErrorKind::UnexpectedCharacter }))
        }
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

