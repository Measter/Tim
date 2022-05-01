use std::{
    fs::File,
    io::BufWriter,
    path::{Path, PathBuf},
};

use ariadne::{Color, Label};
use byteorder::WriteBytesExt;
use clap::Parser;
use color_eyre::{eyre::eyre, eyre::Context, Result};
use lasso::Rodeo;
use source_file::SourceStorage;

mod diagnostics;
mod parser;
mod scanner;
mod source_file;

#[derive(Debug, Parser)]
struct Args {
    file: String,
    #[clap(short, long)]
    output: Option<String>,
}

fn main() -> Result<()> {
    color_eyre::install()?;
    let args = Args::parse();

    let output: PathBuf = if let Some(path) = args.output {
        path.into()
    } else {
        Path::new(&*args.file).with_extension("bin")
    };

    let mut interner = Rodeo::default();
    let mut sources = SourceStorage::new();

    let contents = std::fs::read_to_string(&args.file)
        .with_context(|| eyre!("Couldn't open file `{}`", Path::new(&args.file).display()))?;

    let file_id = sources.add(&args.file, &contents);
    let tokens = scanner::lex_file(&contents, file_id, &mut interner, &sources)
        .map_err(|_| eyre!("Error lexing file: {}", &args.file))?;

    let instructions = parser::parse_tokens(&tokens, &interner, &sources)
        .map_err(|_| eyre!("Error parsing file: {}", &args.file))?;

    let expanded = parser::expand_repetitions(instructions);
    let evaluated = parser::evaluate_expressions(&expanded, &interner, &sources)
        .map_err(|_| eyre!("Error evaluating expressions"))?;

    let output_file = File::create(&output)
        .with_context(|| eyre!("Failed to create file: {}", output.display()))?;
    let mut writer = BufWriter::new(output_file);

    for instr in evaluated {
        let opcode = instr.kind.opcode();
        writer
            .write_u8(opcode)
            .with_context(|| eyre!("Failed to write to file: {}", output.display()))?;

        let value = match instr.kind.value() {
            value @ 0..=255 => value as u8,
            value => {
                diagnostics::emit_error(
                    instr.location,
                    format!("value `{}` is out of bounds", value),
                    [Label::new(instr.location).with_color(Color::Red)],
                    None,
                    &sources,
                );
                continue;
            }
        };

        writer
            .write_u8(value)
            .with_context(|| eyre!("Failed to write to file: {}", output.display()))?;
    }

    Ok(())
}
