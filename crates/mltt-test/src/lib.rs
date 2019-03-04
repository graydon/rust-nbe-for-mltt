//! Integration tests for the MLTT language

macro_rules! run_test {
    ($name:ident, $path:literal) => {
        #[test]
        fn $name() {
            use language_reporting::termcolor::{ColorChoice, StandardStream};
            use mltt_core::validate;
            use mltt_parse::lexer::Lexer;
            use mltt_parse::parser;
            use mltt_span::Files;

            let _ = pretty_env_logger::try_init();

            let mut files = Files::new();
            let writer = StandardStream::stdout(ColorChoice::Always);
            let reporting_config = language_reporting::DefaultConfig;

            let src = include_str!(concat!("../../../", $path));
            let file_id = files.add($path, src);

            let lexer = Lexer::new(&files[file_id]);
            let concrete_module = parser::parse_module(lexer).unwrap_or_else(|diagnostic| {
                let writer = &mut writer.lock();
                language_reporting::emit(writer, &files, &diagnostic, &reporting_config).unwrap();
                panic!("error encountered");
            });
            // FIXME: check lexer for errors

            let core_module = mltt_elaborate::check_module(&concrete_module).unwrap();
            validate::check_module(&core_module).unwrap_or_else(|error| {
                panic!("failed validation: {}\n\n{:#?}", error, error);
            });
        }
    };
}

run_test!(records, "tests/records.mltt");
run_test!(combinators, "tests/combinators.mltt");
run_test!(empty, "tests/empty.mltt");
run_test!(connectives, "tests/connectives.mltt");
run_test!(cumulativity, "tests/cumulativity.mltt");
run_test!(categories, "tests/categories.mltt");
