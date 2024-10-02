use std::{fs::read_to_string, io, path::PathBuf};

use clap::Parser;
use lang_tools_cli::print::{pretty_print, StandardOutputStyle};
use mimalloc::MiMalloc;
use slate_dtt::DTTMetaModel;
use slate_lang_def::{
    parser::{
        layer1_tokenizer::TokenizerConfig, layer2_parenthesis_matcher::ParenthesisMatcherConfig,
        layer3_parameter_identifier::ParameterIdentifierConfig,
    },
    SlateLang,
};
use termcolor::{BufferedStandardStream, Color, ColorChoice, ColorSpec};

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Cli {
    file: PathBuf,
}

fn main() -> io::Result<()> {
    let cli = Cli::parse();

    let mut style = StandardOutputStyle::standard();
    style.fn_names = style.value_names.clone();
    let mut global_spec = ColorSpec::new();
    global_spec.set_fg(Some(Color::Magenta));
    style.scope_overrides.global = Some(global_spec);
    let mut var_spec = ColorSpec::new();
    var_spec.set_italic(true);
    style.scope_overrides.local = Some(var_spec.clone());
    style.scope_overrides.param = Some(var_spec.clone());
    var_spec.set_fg(Some(Color::Ansi256(7)));
    style.scope_overrides.field = Some(var_spec);

    let mut stdout = BufferedStandardStream::stdout(ColorChoice::Auto);

    let input = read_to_string(&cli.file)?;
    let config = (
        (TokenizerConfig, ParenthesisMatcherConfig),
        ParameterIdentifierConfig::new(&DTTMetaModel),
    );

    pretty_print::<SlateLang, _>(&input, config, &style, &mut stdout)
}
