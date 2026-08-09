mod ast;
mod lex;
mod sax;

use logos::Logos;
use std::fs;

pub fn parse_string(input: String) -> ast::Env {
    let lex_stream = lex::Token::lexer_with_extras(&input, 0)
        .spanned()
        .map(|(t, y)| (y.start, t.expect("Couldn't lex token"), y.end));

    let parser = sax::ProgParser::new();
    parser.parse(lex_stream).expect("Parse error")
}

pub fn parse_from_file(file_name: String) -> ast::Env {
    let str_file = fs::read_to_string(file_name.trim()).expect("File read error");
    parse_string(str_file)
}
