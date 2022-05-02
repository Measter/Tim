use std::{
    collections::{hash_map::Entry, HashMap},
    iter::Peekable,
    ops::{Add, Div, Mul, Not, Range, Sub},
};

use ariadne::{Color, Label};
use lasso::{Rodeo, Spur};

use crate::{
    diagnostics,
    scanner::{Token, TokenKind},
    source_file::{SourceLocation, SourceStorage},
};

#[derive(Debug, Clone)]
pub enum Expression {
    Literal(u64),
    Expression(Vec<Token>),
}

impl Expression {
    pub fn value(&self) -> u64 {
        match self {
            Expression::Literal(val) => *val,
            Expression::Expression(_) => panic!("Expected Literal, fonud Expression"),
        }
    }
}

#[derive(Debug, Clone)]
pub enum InstructionKind {
    Add(Expression),
    Define(Token, Expression),
    InputEnable(Expression),
    IoControl(Expression),
    Load(Expression),
    Nand(Expression),
    NopF,
    NopO,
    One,
    Or(Expression),
    OutputEnable(Expression),
    Repeat {
        range: Range<u64>,
        variable: Token,
        instructions: Vec<Instruction>,
    },
    Return,
    SkipIfZero,
    Store(Expression),
    StoreComplement(Expression),
    Sub(Expression),
    Undefine(Token),
    Xor(Expression),
}

impl InstructionKind {
    pub fn opcode(&self) -> u8 {
        match self {
            InstructionKind::NopO => 0b0000,
            InstructionKind::Load(_) => 0b0001,
            InstructionKind::Add(_) => 0b0010,
            InstructionKind::Sub(_) => 0b0011,
            InstructionKind::One => 0b0100,
            InstructionKind::Nand(_) => 0b0101,
            InstructionKind::Or(_) => 0b0110,
            InstructionKind::Xor(_) => 0b0111,
            InstructionKind::Store(_) => 0b1000,
            InstructionKind::StoreComplement(_) => 0b1001,
            InstructionKind::InputEnable(_) => 0b1010,
            InstructionKind::OutputEnable(_) => 0b1011,
            InstructionKind::IoControl(_) => 0b1100,
            InstructionKind::Return => 0b1101,
            InstructionKind::SkipIfZero => 0b1110,
            InstructionKind::NopF => 0b1111,
            InstructionKind::Define(..) => panic!("Shouldn't encounter Define."),
            InstructionKind::Undefine(..) => panic!("Shouldn't encounter Undefine."),
            InstructionKind::Repeat { .. } => panic!("Shouldn't encounter Repeat."),
        }
    }

    fn with_expression(&self, new_expr: Expression) -> Self {
        match self {
            InstructionKind::Load(_) => InstructionKind::Load(new_expr),
            InstructionKind::Add(_) => InstructionKind::Add(new_expr),
            InstructionKind::Sub(_) => InstructionKind::Sub(new_expr),
            InstructionKind::Nand(_) => InstructionKind::Nand(new_expr),
            InstructionKind::Or(_) => InstructionKind::Or(new_expr),
            InstructionKind::Xor(_) => InstructionKind::Xor(new_expr),
            InstructionKind::Store(_) => InstructionKind::Store(new_expr),
            InstructionKind::StoreComplement(_) => InstructionKind::StoreComplement(new_expr),
            InstructionKind::InputEnable(_) => InstructionKind::InputEnable(new_expr),
            InstructionKind::OutputEnable(_) => InstructionKind::OutputEnable(new_expr),
            InstructionKind::IoControl(_) => InstructionKind::IoControl(new_expr),

            InstructionKind::One
            | InstructionKind::NopO
            | InstructionKind::Return
            | InstructionKind::SkipIfZero
            | InstructionKind::NopF
            | InstructionKind::Define(_, _)
            | InstructionKind::Undefine(_)
            | InstructionKind::Repeat { .. } => {
                panic!("Instruction doesn't take expression: {:?}", &self)
            }
        }
    }

    pub fn value(&self) -> u64 {
        match self {
            InstructionKind::Load(expr)
            | InstructionKind::Add(expr)
            | InstructionKind::Sub(expr)
            | InstructionKind::Nand(expr)
            | InstructionKind::Or(expr)
            | InstructionKind::Xor(expr)
            | InstructionKind::Store(expr)
            | InstructionKind::StoreComplement(expr)
            | InstructionKind::InputEnable(expr)
            | InstructionKind::OutputEnable(expr)
            | InstructionKind::IoControl(expr) => expr.value(),

            InstructionKind::One
            | InstructionKind::NopO
            | InstructionKind::Return
            | InstructionKind::SkipIfZero
            | InstructionKind::NopF => 0,

            InstructionKind::Define(_, _) => panic!("Encountered Define"),
            InstructionKind::Undefine(_) => panic!("Encountered Undefine"),
            InstructionKind::Repeat { .. } => panic!("Encountered Repeat"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Instruction {
    pub kind: InstructionKind,
    pub location: SourceLocation,
}

impl Instruction {
    fn with_expression(&self, new_expr: Expression) -> Self {
        Self {
            location: self.location,
            kind: self.kind.with_expression(new_expr),
        }
    }
}

#[derive(Debug)]
struct Define {
    value: u64,
    location: SourceLocation,
}

fn expect<'a>(
    tokens: &mut impl Iterator<Item = (usize, &'a Token)>,
    kind_str: &str,
    expected: fn(TokenKind) -> bool,
    prev: Token,
    interner: &Rodeo,
    sources: &SourceStorage,
) -> Result<Token, ()> {
    match tokens.next() {
        Some((_, token)) if expected(token.kind) => Ok(*token),
        Some((_, token)) => {
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

fn parse_expression<'a>(
    tokens_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    tokens: &[Token],
    keyword: Token,
    interner: &Rodeo,
    sources: &SourceStorage,
) -> Result<Expression, ()> {
    let start_idx = match tokens_iter.next() {
        Some((idx, token)) if token.kind.is_expression_token() => idx,
        Some((_, token)) => {
            diagnostics::emit_error(
                token.location,
                format!(
                    "expected maths expression, found `{}`",
                    interner.resolve(&token.lexeme)
                ),
                [Label::new(token.location).with_color(Color::Red)],
                None,
                sources,
            );
            return Err(());
        }
        None => {
            diagnostics::end_of_file(keyword.location, sources);
            return Err(());
        }
    };

    let mut last_token_idx = start_idx;
    while let Some(&(idx, token)) = tokens_iter.peek() {
        if !token.kind.is_expression_token() {
            break;
        }

        tokens_iter.next();
        last_token_idx = idx;
    }

    let expression = &tokens[start_idx..=last_token_idx];

    Ok(Expression::Expression(expression.to_owned()))
}

fn parse_define<'a>(
    tokens_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    tokens: &[Token],
    keyword: Token,
    interner: &Rodeo,
    sources: &SourceStorage,
) -> Result<Instruction, ()> {
    let name_token = expect(
        tokens_iter,
        "ident",
        |k| matches!(k, TokenKind::Ident(_)),
        keyword,
        interner,
        sources,
    )?;

    let equals = expect(
        tokens_iter,
        "=",
        |k| k == TokenKind::Equals,
        name_token,
        interner,
        sources,
    )?;

    let expr = parse_expression(tokens_iter, tokens, equals, interner, sources)?;

    Ok(Instruction {
        kind: InstructionKind::Define(name_token, expr),
        location: keyword.location,
    })
}

fn parse_repetition<'a>(
    tokens_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    tokens: &[Token],
    keyword: Token,
    interner: &Rodeo,
    sources: &SourceStorage,
) -> Result<Instruction, ()> {
    let variable_token = expect(
        tokens_iter,
        "ident",
        |k| matches!(k, TokenKind::Ident(_)),
        keyword,
        interner,
        sources,
    )?;

    let in_token = expect(
        tokens_iter,
        "in",
        |k| k == TokenKind::In,
        variable_token,
        interner,
        sources,
    )?;

    let range_start = expect(
        tokens_iter,
        "number",
        |k| matches!(k, TokenKind::Number(_)),
        in_token,
        interner,
        sources,
    )?;

    let dot_dot_token = expect(
        tokens_iter,
        "..",
        |k| k == TokenKind::DotDot,
        range_start,
        interner,
        sources,
    )?;

    let range_end = expect(
        tokens_iter,
        "number",
        |k| matches!(k, TokenKind::Number(_)),
        dot_dot_token,
        interner,
        sources,
    )?;

    let do_token = expect(
        tokens_iter,
        "do",
        |k| k == TokenKind::Do,
        range_end,
        interner,
        sources,
    )?;

    let body_start_idx = match tokens_iter.peek() {
        Some((idx, _)) => *idx,
        None => {
            diagnostics::end_of_file(do_token.location, sources);
            return Err(());
        }
    };

    // We need to keep track of block depth so we know which 'end' token is ending the current
    // repetition. We've already consumed the opening 'do'.
    let mut block_depth = 1;
    let mut body_end_idx = body_start_idx;
    let mut end_token = do_token;

    for (idx, token) in tokens_iter {
        if token.kind == TokenKind::Repeat {
            block_depth += 1;
        } else if token.kind == TokenKind::End {
            block_depth -= 1;
        }

        body_end_idx = idx;
        end_token = *token;

        if block_depth == 0 {
            break;
        }
    }

    if end_token.kind != TokenKind::End {
        diagnostics::end_of_file(end_token.location, sources);
        return Err(());
    }

    if body_start_idx == body_end_idx {
        diagnostics::emit_warning(
            keyword.location,
            "empty repetition",
            [Label::new(do_token.location.merge(end_token.location)).with_color(Color::Red)],
            None,
            sources,
        );
    }

    let body_tokens = &tokens[body_start_idx..body_end_idx];

    let body = parse_tokens(body_tokens, interner, sources)?;
    let start = match range_start.kind {
        TokenKind::Number(start) => start,
        _ => unreachable!(),
    };
    let end = match range_end.kind {
        TokenKind::Number(end) => end,
        _ => unreachable!(),
    };

    if start > 0xFF || end > 0xFF || end <= start {
        let loc = range_start.location.merge(range_end.location);
        diagnostics::emit_error(
            loc,
            "invalid range",
            [Label::new(loc).with_color(Color::Red)],
            None,
            sources,
        );
        return Err(());
    }

    Ok(Instruction {
        kind: InstructionKind::Repeat {
            range: start..end,
            variable: variable_token,
            instructions: body,
        },
        location: keyword.location.merge(end_token.location),
    })
}

fn parse_addressable_instr<'a>(
    tokens_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    tokens: &[Token],
    keyword: Token,
    interner: &Rodeo,
    sources: &SourceStorage,
) -> Result<Instruction, ()> {
    let expr = parse_expression(tokens_iter, tokens, keyword, interner, sources)?;

    let instr = match keyword.kind {
        TokenKind::Ld => InstructionKind::Load(expr),
        TokenKind::Add => InstructionKind::Add(expr),
        TokenKind::Sub => InstructionKind::Sub(expr),
        TokenKind::Nand => InstructionKind::Nand(expr),
        TokenKind::Or => InstructionKind::Or(expr),
        TokenKind::Xor => InstructionKind::Xor(expr),
        TokenKind::Sto => InstructionKind::Store(expr),
        TokenKind::StoC => InstructionKind::StoreComplement(expr),
        TokenKind::Ien => InstructionKind::InputEnable(expr),
        TokenKind::Oen => InstructionKind::OutputEnable(expr),
        TokenKind::Ioc => InstructionKind::IoControl(expr),
        _ => unreachable!(),
    };

    Ok(Instruction {
        kind: instr,
        location: keyword.location,
    })
}

pub fn parse_tokens(
    tokens: &[Token],
    interner: &Rodeo,
    sources: &SourceStorage,
) -> Result<Vec<Instruction>, ()> {
    let mut instructions = Vec::new();
    let mut had_error = false;

    let mut token_iter = tokens.iter().enumerate().peekable();

    while let Some((_, token)) = token_iter.next() {
        let instr = match token.kind {
            TokenKind::Def => {
                match parse_define(&mut token_iter, tokens, *token, interner, sources) {
                    Ok(i) => i,
                    Err(_) => {
                        had_error = true;
                        continue;
                    }
                }
            }

            TokenKind::Repeat => {
                match parse_repetition(&mut token_iter, tokens, *token, interner, sources) {
                    Ok(i) => i,
                    Err(_) => {
                        had_error = true;
                        continue;
                    }
                }
            }

            TokenKind::NopO => Instruction {
                kind: InstructionKind::NopO,
                location: token.location,
            },
            TokenKind::One => Instruction {
                kind: InstructionKind::One,
                location: token.location,
            },
            TokenKind::Rtn => Instruction {
                kind: InstructionKind::Return,
                location: token.location,
            },
            TokenKind::Skz => Instruction {
                kind: InstructionKind::SkipIfZero,
                location: token.location,
            },
            TokenKind::NopF => Instruction {
                kind: InstructionKind::NopF,
                location: token.location,
            },

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
                match parse_addressable_instr(&mut token_iter, tokens, *token, interner, sources) {
                    Ok(i) => i,
                    Err(_) => {
                        had_error = true;
                        continue;
                    }
                }
            }

            _ => {
                let msg = match token.kind {
                    TokenKind::Number(_) => "number",
                    TokenKind::Ident(_) => "ident",
                    _ => interner.resolve(&token.lexeme),
                };

                diagnostics::emit_error(
                    token.location,
                    format!("expected mnemonic, found `{}`", msg),
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

pub fn expand_repetitions(mut instructions: Vec<Instruction>) -> Vec<Instruction> {
    let mut dest = Vec::with_capacity(instructions.len());

    loop {
        dest.clear();
        let mut did_expansion = false;
        for instr in instructions.drain(..) {
            match &instr.kind {
                InstructionKind::Repeat {
                    range,
                    variable,
                    instructions,
                } => {
                    did_expansion = true;

                    for i in range.clone() {
                        dest.push(Instruction {
                            kind: InstructionKind::Define(*variable, Expression::Literal(i as u64)),
                            location: instr.location,
                        });
                        dest.extend_from_slice(instructions);
                        dest.push(Instruction {
                            kind: InstructionKind::Undefine(*variable),
                            location: instr.location,
                        });
                    }
                }
                _ => dest.push(instr),
            }
        }

        std::mem::swap(&mut dest, &mut instructions);
        if !did_expansion {
            break;
        }
    }

    instructions
}

fn operator_prec(kind: TokenKind) -> u8 {
    match kind {
        TokenKind::Minus | TokenKind::Plus => 1,
        TokenKind::Slash | TokenKind::Star => 2,
        _ => unreachable!(),
    }
}

#[derive(Debug)]
enum RpnOp {
    Number(u64),
    Function(Token),
}

impl From<u64> for RpnOp {
    fn from(v: u64) -> Self {
        RpnOp::Number(v)
    }
}

impl From<Token> for RpnOp {
    fn from(t: Token) -> Self {
        RpnOp::Function(t)
    }
}

fn evaluate_expression(
    defines: &HashMap<Spur, Define>,
    value: &Expression,
    interner: &Rodeo,
    sources: &SourceStorage,
) -> Result<u64, ()> {
    match value {
        Expression::Literal(val) => Ok(*val),
        Expression::Expression(expr) => {
            let mut output: Vec<RpnOp> = Vec::new();
            let mut op_stack: Vec<Token> = Vec::new();
            let mut parens_balance: u8 = 0;

            for token in expr {
                match token.kind {
                    TokenKind::Number(num) => output.push(num.into()),
                    TokenKind::Ident(id) => {
                        let num = match defines.get(&id) {
                            Some(def) => def.value,
                            None => {
                                diagnostics::emit_error(
                                    token.location,
                                    format!(
                                        "symbol `{}` not defined",
                                        interner.resolve(&token.lexeme)
                                    ),
                                    [Label::new(token.location).with_color(Color::Red)],
                                    None,
                                    sources,
                                );
                                return Err(());
                            }
                        };

                        output.push(num.into());
                    }
                    TokenKind::ParenOpen => {
                        op_stack.push(*token);
                        parens_balance += 1;
                    }
                    TokenKind::ParenClose => {
                        parens_balance = match parens_balance.checked_sub(1) {
                            Some(v) => v,
                            None => {
                                diagnostics::emit_error(
                                    token.location,
                                    "unbalanced parenthesis",
                                    [Label::new(token.location).with_color(Color::Red)],
                                    None,
                                    sources,
                                );
                                return Err(());
                            }
                        };

                        while let Some(op) = op_stack.pop() {
                            if op.kind == TokenKind::ParenOpen {
                                break;
                            }
                            output.push(op.into());
                        }
                    }
                    TokenKind::Minus | TokenKind::Plus | TokenKind::Star | TokenKind::Slash => {
                        if matches!(op_stack.last(), Some(op) if op.kind != TokenKind::ParenOpen && operator_prec(token.kind) <= operator_prec(op.kind))
                        {
                            let prev_token = op_stack.pop().unwrap();
                            output.push(prev_token.into());
                        }

                        op_stack.push(*token);
                    }
                    _ => unreachable!(),
                }
            }

            if parens_balance != 0 {
                let start_loc = expr[0].location;
                let end_loc = expr.last().unwrap().location;
                let span = start_loc.merge(end_loc);
                diagnostics::emit_error(
                    span,
                    "unbalanced parethesis",
                    [Label::new(span).with_color(Color::Red)],
                    None,
                    sources,
                );
                return Err(());
            }

            for op in op_stack.drain(..).rev() {
                output.push(op.into());
            }

            let mut evaluation_stack: Vec<u64> = Vec::new();
            for rpn_op in output {
                match rpn_op {
                    RpnOp::Number(num) => evaluation_stack.push(num),
                    RpnOp::Function(token) => {
                        let b = match evaluation_stack.pop() {
                            Some(a) => a,
                            None => {
                                diagnostics::emit_error(
                                    token.location,
                                    "missing operand",
                                    [Label::new(token.location).with_color(Color::Red)],
                                    None,
                                    sources,
                                );
                                return Err(());
                            }
                        };
                        let a = match evaluation_stack.pop() {
                            Some(a) => a,
                            None => {
                                diagnostics::emit_error(
                                    token.location,
                                    "missing operand",
                                    [Label::new(token.location).with_color(Color::Red)],
                                    None,
                                    sources,
                                );
                                return Err(());
                            }
                        };

                        let func = match token.kind {
                            TokenKind::Plus => u64::add,
                            TokenKind::Minus => u64::sub,
                            TokenKind::Slash => u64::div,
                            TokenKind::Star => u64::mul,
                            _ => unreachable!(),
                        };

                        evaluation_stack.push(func(a, b));
                    }
                }
            }

            if evaluation_stack.len() != 1 {
                let start_loc = expr[0].location;
                let end_loc = expr.last().unwrap().location;
                let span = start_loc.merge(end_loc);
                diagnostics::emit_error(
                    span,
                    "invalid expression",
                    [Label::new(span).with_color(Color::Red)],
                    None,
                    sources,
                );
                return Err(());
            }

            Ok(evaluation_stack[0])
        }
    }
}

pub fn evaluate_expressions(
    instructions: &[Instruction],
    interner: &Rodeo,
    sources: &SourceStorage,
) -> Result<Vec<Instruction>, ()> {
    let mut evaluated = Vec::with_capacity(instructions.len());
    let mut defines = HashMap::new();
    let mut had_error = false;

    for instr in instructions {
        let expr = match &instr.kind {
            InstructionKind::Define(id, value) => {
                let value = match evaluate_expression(&defines, value, interner, sources) {
                    Ok(val) => val,
                    Err(_) => {
                        had_error = true;
                        continue;
                    }
                };

                match defines.entry(id.lexeme) {
                    Entry::Occupied(en) => {
                        let value = en.get();
                        diagnostics::emit_error(
                            id.location,
                            "symbol defined multiple times",
                            [
                                Label::new(id.location)
                                    .with_color(Color::Red)
                                    .with_message("defined here"),
                                Label::new(value.location)
                                    .with_color(Color::Cyan)
                                    .with_message("previously defined here"),
                            ],
                            None,
                            sources,
                        );
                        had_error = true;
                    }
                    Entry::Vacant(slot) => {
                        slot.insert(Define {
                            value,
                            location: id.location,
                        });
                    }
                }
                continue;
            }
            InstructionKind::Undefine(id) => {
                if defines.remove(&id.lexeme).is_none() {
                    had_error = true;
                    diagnostics::emit_error(
                        id.location,
                        format!("unknown define `{}`", interner.resolve(&id.lexeme)),
                        [Label::new(id.location).with_color(Color::Red)],
                        None,
                        sources,
                    );
                }
                continue;
            }

            InstructionKind::Load(expr)
            | InstructionKind::Add(expr)
            | InstructionKind::Sub(expr)
            | InstructionKind::Nand(expr)
            | InstructionKind::Or(expr)
            | InstructionKind::Xor(expr)
            | InstructionKind::Store(expr)
            | InstructionKind::StoreComplement(expr)
            | InstructionKind::InputEnable(expr)
            | InstructionKind::OutputEnable(expr)
            | InstructionKind::IoControl(expr) => expr,

            InstructionKind::One
            | InstructionKind::Return
            | InstructionKind::SkipIfZero
            | InstructionKind::NopO
            | InstructionKind::NopF => {
                evaluated.push(instr.clone());
                continue;
            }
            InstructionKind::Repeat { .. } => panic!("Repeat encountered."),
        };

        let value = match evaluate_expression(&defines, expr, interner, sources) {
            Ok(value) => value,
            Err(_) => {
                had_error = true;
                continue;
            }
        };

        let new_instr = instr.with_expression(Expression::Literal(value));
        evaluated.push(new_instr);
    }

    had_error.not().then(|| evaluated).ok_or(())
}
