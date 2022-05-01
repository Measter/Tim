use std::{
    iter::Peekable,
    ops::{Not, Range},
    str::CharIndices,
};

use ariadne::{Color, Label};
use lasso::{Rodeo, Spur};

use crate::{
    diagnostics,
    source_file::{FileId, SourceLocation, SourceStorage},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
    NopO,
    Ld,
    Add,
    Sub,
    One,
    Nand,
    Or,
    Xor,
    Sto,
    StoC,
    Ien,
    Oen,
    Ioc,
    Rtn,
    Skz,
    NopF,
    Equals,
    Def,
    Repeat,
    In,
    Do,
    End,
    DotDot,
    Ident(Spur),
    Number(u64),
}

#[derive(Debug, Clone, Copy)]
pub struct Token {
    pub kind: TokenKind,
    pub lexeme: Spur,
    pub location: SourceLocation,
}

fn new_token_char(c: char) -> bool {
    c.is_whitespace() || matches!(c, ';' | '=' | '.')
}

struct Scanner<'a> {
    chars: Peekable<CharIndices<'a>>,
    cur_token_start: usize,
    next_token_start: usize,
    file_id: FileId,
    string_buf: String,
}

impl Scanner<'_> {
    fn advance(&mut self) -> char {
        let (idx, ch) = self.chars.next().expect("unexpected end of input");
        self.next_token_start = idx + ch.len_utf8();
        ch
    }

    fn peek(&mut self) -> Option<char> {
        self.chars.peek().map(|(_, c)| *c)
    }

    fn is_at_end(&mut self) -> bool {
        self.peek().is_none()
    }

    fn lexeme<'a>(&self, input: &'a str) -> &'a str {
        &input[self.cur_token_start..self.next_token_start]
    }

    fn lexeme_range(&self) -> Range<usize> {
        self.cur_token_start..self.next_token_start
    }

    fn scan_token(
        &mut self,
        input: &str,
        interner: &mut Rodeo,
        sources: &SourceStorage,
    ) -> Result<Option<Token>, ()> {
        let ch = self.advance();
        let next_ch = self.peek().unwrap_or_default();

        let res = match (ch, next_ch) {
            _ if ch.is_whitespace() => None,
            (';', _) => {
                while !matches!(self.peek(), Some('\n')) && !self.is_at_end() {
                    self.advance();
                }

                None
            }

            ('0', 'x' | 'X' | 'o' | 'O' | 'b' | 'B') => {
                // Consume the base indicator
                self.advance();

                let (base, base_name, valid_digits): (_, _, fn(char) -> bool) = match next_ch {
                    'b' | 'B' => (2, "binary", |c| c == '0' || c == '1'),
                    'o' | 'O' => (8, "octal", |c| matches!(c, '0'..='7')),
                    'x' | 'X' => (16, "hex", |c| c.is_ascii_hexdigit()),

                    _ => unreachable!(),
                };

                self.string_buf.clear();
                let mut is_all_digits = true;
                while !matches!(self.peek(), Some(c) if new_token_char(c)) && !self.is_at_end() {
                    let c = self.advance();
                    is_all_digits &= valid_digits(c) || c == '_';
                    if c.is_ascii_hexdigit() {
                        self.string_buf.push(c);
                    }
                }

                let lexeme = self.lexeme(input);
                let source_location = SourceLocation::new(self.file_id, self.lexeme_range());

                if next_ch == 'O' {
                    diagnostics::emit_error(
                        source_location,
                        "octal numbers must use a lower-case 'o'",
                        [Label::new(source_location).with_color(Color::Red)],
                        None,
                        sources,
                    );
                    return Err(());
                }

                if !is_all_digits {
                    diagnostics::emit_error(
                        source_location,
                        format!("invalid {} number", base_name),
                        [Label::new(source_location).with_color(Color::Red)],
                        None,
                        sources,
                    );
                    return Err(());
                } else {
                    let number = match u64::from_str_radix(&lexeme[2..], base) {
                        Ok(number) => number,
                        Err(_) => {
                            diagnostics::emit_error(
                                source_location,
                                "number literal too large",
                                [Label::new(source_location).with_color(Color::Red)],
                                None,
                                sources,
                            );
                            return Err(());
                        }
                    };

                    let lexeme = interner.get_or_intern(lexeme);
                    Some(Token {
                        kind: TokenKind::Number(number),
                        lexeme,
                        location: source_location,
                    })
                }
            }

            ('0'..='9', _) => {
                self.string_buf.clear();
                let mut is_all_digits = true;
                while !matches!(self.peek(), Some(c) if new_token_char(c)) && !self.is_at_end() {
                    let c = self.advance();
                    is_all_digits &= c.is_ascii_digit() || c == '_';
                    if c.is_ascii_digit() {
                        self.string_buf.push(c);
                    }
                }

                let lexeme = self.lexeme(input);
                let source_location = SourceLocation::new(self.file_id, self.lexeme_range());

                if !is_all_digits {
                    diagnostics::emit_error(
                        source_location,
                        "invalid number",
                        [Label::new(source_location).with_color(Color::Red)],
                        None,
                        sources,
                    );
                    return Err(());
                } else {
                    let number = match lexeme.parse::<u64>() {
                        Ok(number) => number,
                        Err(_) => {
                            diagnostics::emit_error(
                                source_location,
                                "number literal too large",
                                [Label::new(source_location).with_color(Color::Red)],
                                None,
                                sources,
                            );
                            return Err(());
                        }
                    };

                    let lexeme = interner.get_or_intern(lexeme);
                    Some(Token {
                        kind: TokenKind::Number(number),
                        lexeme,
                        location: source_location,
                    })
                }
            }

            ('=', _) => Some(Token {
                kind: TokenKind::Equals,
                lexeme: interner.get_or_intern(self.lexeme(input)),
                location: SourceLocation::new(self.file_id, self.lexeme_range()),
            }),

            ('.', '.') => {
                self.advance(); // Consume second '.'
                Some(Token {
                    kind: TokenKind::DotDot,
                    lexeme: interner.get_or_intern(self.lexeme(input)),
                    location: SourceLocation::new(self.file_id, self.lexeme_range()),
                })
            }

            _ => {
                self.string_buf.clear();
                self.string_buf.extend(ch.to_lowercase());
                while !matches!(self.peek(), Some(c) if new_token_char(c)) && !self.is_at_end() {
                    let c = self.advance();
                    self.string_buf.extend(c.to_lowercase());
                }

                let source_location = SourceLocation::new(self.file_id, self.lexeme_range());
                let kind = match &*self.string_buf {
                    "nopo" => TokenKind::NopO,
                    "ld" => TokenKind::Ld,
                    "add" => TokenKind::Add,
                    "sub" => TokenKind::Sub,
                    "one" => TokenKind::One,
                    "nand" => TokenKind::Nand,
                    "or" => TokenKind::Or,
                    "xor" => TokenKind::Xor,
                    "sto" => TokenKind::Sto,
                    "stoc" => TokenKind::StoC,
                    "ien" => TokenKind::Ien,
                    "oen" => TokenKind::Oen,
                    "ioc" => TokenKind::Ioc,
                    "rtn" => TokenKind::Rtn,
                    "skz" => TokenKind::Skz,
                    "nopf" => TokenKind::NopF,
                    "#def" => TokenKind::Def,
                    "#rep" => TokenKind::Repeat,
                    "do" => TokenKind::Do,
                    "end" => TokenKind::End,
                    "in" => TokenKind::In,
                    _ => {
                        let ident_spur = interner.get_or_intern(self.lexeme(input));
                        TokenKind::Ident(ident_spur)
                    }
                };

                Some(Token {
                    kind,
                    lexeme: interner.get_or_intern(self.lexeme(input)),
                    location: source_location,
                })
            }
        };

        Ok(res)
    }
}

pub fn lex_file(
    contents: &str,
    file_id: FileId,
    interner: &mut Rodeo,
    sources: &SourceStorage,
) -> Result<Vec<Token>, ()> {
    let mut scanner = Scanner {
        chars: contents.char_indices().peekable(),
        cur_token_start: 0,
        next_token_start: 0,
        file_id,
        string_buf: String::new(),
    };

    let mut tokens = Vec::new();

    let mut had_error = false;

    while !scanner.is_at_end() {
        scanner.cur_token_start = scanner.next_token_start;

        match scanner.scan_token(contents, interner, sources) {
            Ok(Some(token)) => tokens.push(token),
            Ok(None) => continue,
            Err(()) => {
                had_error |= true;
                continue;
            }
        };
    }

    had_error.not().then(|| tokens).ok_or(())
}
