use std::{
    collections::{hash_map::Entry, HashMap},
    iter::Peekable,
    ops::Not,
};

use ariadne::{Color, Label};
use lasso::{Rodeo, Spur};

use crate::{
    diagnostics,
    scanner::{Token, TokenKind},
    source_file::{SourceLocation, SourceStorage},
};

#[derive(Debug, Copy, Clone)]
pub enum Instruction {
    NopO,
    Load(u8),
    Add(u8),
    Sub(u8),
    One,
    Nand(u8),
    Or(u8),
    Xor(u8),
    Store(u8),
    StoreComplement(u8),
    InputEnable(u8),
    OutputEnable(u8),
    IoControl(u8),
    Return,
    SkipIfZero,
    NopF,
}

impl Instruction {
    pub fn encode(self) -> u16 {
        match self {
            Instruction::NopO => 0b0000 << 8,
            Instruction::Load(addr) => 0b0001 << 8 | (addr as u16),
            Instruction::Add(addr) => 0b0010 << 8 | (addr as u16),
            Instruction::Sub(addr) => 0b0011 << 8 | (addr as u16),
            Instruction::One => 0b0100 << 8,
            Instruction::Nand(addr) => 0b0101 << 8 | (addr as u16),
            Instruction::Or(addr) => 0b0110 << 8 | (addr as u16),
            Instruction::Xor(addr) => 0b0111 << 8 | (addr as u16),
            Instruction::Store(addr) => 0b1000 << 8 | (addr as u16),
            Instruction::StoreComplement(addr) => 0b1001 << 8 | (addr as u16),
            Instruction::InputEnable(addr) => 0b1010 << 8 | (addr as u16),
            Instruction::OutputEnable(addr) => 0b1011 << 8 | (addr as u16),
            Instruction::IoControl(addr) => 0b1100 << 8 | (addr as u16),
            Instruction::Return => 0b1101 << 8,
            Instruction::SkipIfZero => 0b1110,
            Instruction::NopF => 0b1111,
        }
    }
}

#[derive(Debug)]
struct Define {
    value: u64,
    location: SourceLocation,
}

fn expect<'a>(
    tokens: &mut impl Iterator<Item = &'a Token>,
    kind_str: &str,
    expected: fn(TokenKind) -> bool,
    prev: Token,
    interner: &Rodeo,
    sources: &SourceStorage,
) -> Result<Token, ()> {
    match tokens.next() {
        Some(token) if expected(token.kind) => Ok(*token),
        Some(token) => {
            diagnostics::emit_error(
                token.location,
                format!(
                    "expected `{}`, found `{}`",
                    kind_str,
                    interner.resolve(&token.lexeme)
                ),
                [Label::new(token.location).with_color(Color::Red)],
                None,
                sources,
            );
            Err(())
        }
        None => {
            diagnostics::emit_error(
                prev.location,
                "unexpected end of tokens",
                [Label::new(prev.location).with_color(Color::Red)],
                None,
                sources,
            );
            Err(())
        }
    }
}

fn parse_define<'a>(
    tokens: &mut Peekable<impl Iterator<Item = &'a Token>>,
    keyword: Token,
    defines: &mut HashMap<Spur, Define>,
    interner: &Rodeo,
    sources: &SourceStorage,
) -> Result<(), ()> {
    let name_token = expect(
        tokens,
        "ident",
        |k| matches!(k, TokenKind::Ident(_)),
        keyword,
        interner,
        sources,
    )?;

    let equals = expect(
        tokens,
        "=",
        |k| k == TokenKind::Equals,
        name_token,
        interner,
        sources,
    )?;

    let addr_token = expect(
        tokens,
        "number",
        |k| matches!(k, TokenKind::Number(_)),
        equals,
        interner,
        sources,
    )?;

    let addr = if let TokenKind::Number(addr) = addr_token.kind {
        addr
    } else {
        unreachable!()
    };

    if addr > 0xFF {
        diagnostics::emit_error(
            addr_token.location,
            "address out of range",
            [Label::new(addr_token.location)
                .with_color(Color::Red)
                .with_message("address must be in range 0x00-0xFF")],
            None,
            sources,
        );
    }

    let id = if let TokenKind::Ident(id) = name_token.kind {
        id
    } else {
        unreachable!()
    };

    match defines.entry(id) {
        Entry::Occupied(en) => {
            let value: &Define = en.get();
            diagnostics::emit_error(
                name_token.location,
                "symbol defined multiple times",
                [
                    Label::new(name_token.location)
                        .with_color(Color::Red)
                        .with_message("defined here"),
                    Label::new(value.location)
                        .with_color(Color::Cyan)
                        .with_message("previously defined here"),
                ],
                None,
                sources,
            );
            return Err(());
        }
        Entry::Vacant(new) => {
            new.insert(Define {
                value: addr,
                location: name_token.location,
            });
        }
    }

    Ok(())
}

fn parse_addressable_instr<'a>(
    tokens: &mut Peekable<impl Iterator<Item = &'a Token>>,
    keyword: Token,
    defines: &HashMap<Spur, Define>,
    interner: &Rodeo,
    sources: &SourceStorage,
) -> Result<Instruction, ()> {
    let addr_or_ident = expect(
        tokens,
        "address",
        |k| matches!(k, TokenKind::Number(_) | TokenKind::Ident(_)),
        keyword,
        interner,
        sources,
    )?;

    let addr = match addr_or_ident.kind {
        TokenKind::Ident(id) => match defines.get(&id) {
            Some(def) => def.value,
            None => {
                diagnostics::emit_error(
                    addr_or_ident.location,
                    "unknown ident",
                    [Label::new(addr_or_ident.location).with_color(Color::Red)],
                    None,
                    sources,
                );
                return Err(());
            }
        },
        TokenKind::Number(addr @ 0x00..=0xFF) => addr,
        TokenKind::Number(_) => {
            diagnostics::emit_error(
                addr_or_ident.location,
                "address out of range",
                [Label::new(addr_or_ident.location)
                    .with_color(Color::Red)
                    .with_message("address must be in range 0x00-0xFF")],
                None,
                sources,
            );
            return Err(());
        }
        _ => unreachable!(),
    };

    let addr = addr as u8;

    let instr = match keyword.kind {
        TokenKind::Ld => Instruction::Load(addr),
        TokenKind::Add => Instruction::Add(addr),
        TokenKind::Sub => Instruction::Sub(addr),
        TokenKind::Nand => Instruction::Nand(addr),
        TokenKind::Or => Instruction::Or(addr),
        TokenKind::Xor => Instruction::Xor(addr),
        TokenKind::Sto => Instruction::Store(addr),
        TokenKind::StoC => Instruction::StoreComplement(addr),
        TokenKind::Ien => Instruction::InputEnable(addr),
        TokenKind::Oen => Instruction::OutputEnable(addr),
        TokenKind::Ioc => Instruction::IoControl(addr),
        _ => unreachable!(),
    };

    Ok(instr)
}

pub fn parse_tokens(
    tokens: &[Token],
    interner: &Rodeo,
    sources: &SourceStorage,
) -> Result<Vec<Instruction>, ()> {
    let mut instructions = Vec::new();
    let mut had_error = false;

    let mut token_iter = tokens.iter().peekable();
    let mut defines = HashMap::new();

    while let Some(token) = token_iter.next() {
        let instr = match token.kind {
            TokenKind::Def => {
                if parse_define(&mut token_iter, *token, &mut defines, interner, sources).is_err() {
                    had_error = true;
                }

                continue;
            }

            TokenKind::NopO => Instruction::NopO,
            TokenKind::One => Instruction::One,
            TokenKind::Rtn => Instruction::Return,
            TokenKind::Skz => Instruction::SkipIfZero,
            TokenKind::NopF => Instruction::NopF,

            TokenKind::Ld
            | TokenKind::Add
            | TokenKind::Sub
            | TokenKind::Nand
            | TokenKind::Or
            | TokenKind::Xor
            | TokenKind::Sto
            | TokenKind::StoC
            | TokenKind::Ien
            | TokenKind::Oen
            | TokenKind::Ioc => {
                match parse_addressable_instr(&mut token_iter, *token, &defines, interner, sources)
                {
                    Ok(i) => i,
                    Err(_) => {
                        had_error = true;
                        continue;
                    }
                }
            }

            TokenKind::Number(_) => {
                diagnostics::emit_error(
                    token.location,
                    "expected mnemonic, found address",
                    [Label::new(token.location).with_color(Color::Red)],
                    None,
                    sources,
                );
                had_error = true;
                continue;
            }
            TokenKind::Equals => {
                diagnostics::emit_error(
                    token.location,
                    "expected mnemonic, found `=`",
                    [Label::new(token.location).with_color(Color::Red)],
                    None,
                    sources,
                );
                had_error = true;
                continue;
            }
            TokenKind::Ident(_) => {
                diagnostics::emit_error(
                    token.location,
                    "expected mnemonic, found `ident`",
                    [Label::new(token.location).with_color(Color::Red)],
                    None,
                    sources,
                );
                had_error = true;
                continue;
            }
        };

        instructions.push(instr);
    }

    had_error.not().then(|| instructions).ok_or(())
}
