#![warn(rust_2018_idioms)]

use language_reporting::termcolor::{ColorChoice, StandardStream};
use mltt_core::validate;
use mltt_parse::lexer::Lexer;
use mltt_parse::parser;
use mltt_span::Files;
use std::fs;
use std::path::Path;

pub fn run(_test_name: &str, test_path: impl AsRef<Path>) {
    let _ = pretty_env_logger::try_init();

    let test_path = test_path.as_ref();
    let src = fs::read_to_string(&test_path)
        .unwrap_or_else(|err| panic!("error reading `{}`: {}", test_path.display(), err));

    let mut files = Files::new();
    let file_id = files.add("test", src);

    let lexer = Lexer::new(&files[file_id]);
    let module = match parser::parse_module(lexer) {
        Ok(module) => module,
        Err(diagnostic) => {
            let writer = StandardStream::stdout(ColorChoice::Always);
            language_reporting::emit(
                &mut writer.lock(),
                &files,
                &diagnostic,
                &language_reporting::DefaultConfig,
            )
            .unwrap();
            panic!("error encountered");
        },
    };

    let core_module = mltt_elaborate::check_module(&module).unwrap();
    match validate::check_module(&core_module) {
        Ok(()) => {},
        Err(error) => panic!("failed validation: {}\n\n{:#?}", error, error),
    }
}
