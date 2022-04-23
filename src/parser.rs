use std::ops::Not;

use ariadne::{Color, Label};

use crate::{
    diagnostics,
    scanner::{Token, TokenKind},
    source_file::SourceStorage,
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

pub fn parse_tokens(tokens: &[Token], sources: &SourceStorage) -> Result<Vec<Instruction>, ()> {
    let mut instructions = Vec::new();
    let mut had_error = false;

    let mut token_iter = tokens.iter().peekable();

    while let Some(token) = token_iter.next() {
        let next_kind = token_iter.peek().map(|t| t.kind);
        let instr = match (token.kind, next_kind) {
            (TokenKind::NopO, _) => Instruction::NopO,
            (TokenKind::One, _) => Instruction::One,
            (TokenKind::Rtn, _) => Instruction::Return,
            (TokenKind::Skz, _) => Instruction::SkipIfZero,
            (TokenKind::NopF, _) => Instruction::NopF,
            (TokenKind::Number(_), _) => {
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

            (TokenKind::Ld, Some(TokenKind::Number(addr @ 0x00..=0xFF))) => {
                token_iter.next(); // Consume address.
                Instruction::Load(addr as u8)
            }
            (TokenKind::Add, Some(TokenKind::Number(addr @ 0x00..=0xFF))) => {
                token_iter.next(); // Consume address.
                Instruction::Add(addr as u8)
            }
            (TokenKind::Sub, Some(TokenKind::Number(addr @ 0x00..=0xFF))) => {
                token_iter.next(); // Consume address.
                Instruction::Sub(addr as u8)
            }
            (TokenKind::Nand, Some(TokenKind::Number(addr @ 0x00..=0xFF))) => {
                token_iter.next(); // Consume address.
                Instruction::Nand(addr as u8)
            }
            (TokenKind::Or, Some(TokenKind::Number(addr @ 0x00..=0xFF))) => {
                token_iter.next(); // Consume address.
                Instruction::Or(addr as u8)
            }
            (TokenKind::Xor, Some(TokenKind::Number(addr @ 0x00..=0xFF))) => {
                token_iter.next(); // Consume address.
                Instruction::Xor(addr as u8)
            }
            (TokenKind::Sto, Some(TokenKind::Number(addr @ 0x00..=0xFF))) => {
                token_iter.next(); // Consume address.
                Instruction::Store(addr as u8)
            }
            (TokenKind::StoC, Some(TokenKind::Number(addr @ 0x00..=0xFF))) => {
                token_iter.next(); // Consume address.
                Instruction::StoreComplement(addr as u8)
            }
            (TokenKind::Ien, Some(TokenKind::Number(addr @ 0x00..=0xFF))) => {
                token_iter.next(); // Consume address.
                Instruction::InputEnable(addr as u8)
            }
            (TokenKind::Oen, Some(TokenKind::Number(addr @ 0x00..=0xFF))) => {
                token_iter.next(); // Consume address.
                Instruction::OutputEnable(addr as u8)
            }
            (TokenKind::Ioc, Some(TokenKind::Number(addr @ 0x00..=0xFF))) => {
                token_iter.next(); // Consume address.
                Instruction::IoControl(addr as u8)
            }

            (_, Some(TokenKind::Number(_))) => {
                let next_token = token_iter.next().unwrap();
                diagnostics::emit_error(
                    next_token.location,
                    "address out of range",
                    [Label::new(next_token.location)
                        .with_color(Color::Red)
                        .with_message("address must be in range 0x00-0xFF")],
                    None,
                    sources,
                );

                had_error = true;
                continue;
            }

            (_, Some(_)) => {
                let next_token = token_iter.next().unwrap();
                diagnostics::emit_error(
                    next_token.location,
                    "expected address, found mnemonic",
                    [Label::new(next_token.location).with_color(Color::Red)],
                    None,
                    sources,
                );

                had_error = true;
                continue;
            }

            (_, None) => {
                diagnostics::emit_error(
                    token.location,
                    "unexpected end of file",
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
