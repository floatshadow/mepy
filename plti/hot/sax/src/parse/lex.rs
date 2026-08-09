#![allow(clippy::upper_case_acronyms)]
use logos::{Lexer, Logos, Skip};
use std::fmt;

impl<'a> fmt::Display for Token<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:#?}", self)
    }
}

#[allow(dead_code)]
fn indentation_callback<'a>(lex: &mut Lexer<'a, Token<'a>>) -> usize {
    let last_line = lex.slice().lines().last().unwrap();
    last_line.len()
}

fn nested_comment<'a>(lex: &mut Lexer<'a, Token<'a>>) -> Skip {
    let mut depth = 0;
    loop {
        let slice = lex.slice();
        if slice.ends_with("/*") {
            depth += 1;
        } else if slice.ends_with("*/") {
            depth -= 1;
            if depth == 0 {
                break;
            }
        }
        if lex.remainder().is_empty() {
            break;
        }
        lex.bump(1);
    }
    Skip
}

#[allow(non_camel_case_types)]
#[derive(Clone, Logos, Debug, PartialEq)]
#[logos(error = String, extras = usize)]
pub enum Token<'a> {
    #[regex(r"[A-Za-z_][A-Za-z0-9_$]*")]
    Ident(&'a str),
    #[regex("'[A-Za-z0-9_$]+")]
    Tag(&'a str),

    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token(",")]
    Comma,
    #[token(":")]
    Colon,
    #[token("=")]
    Equal,
    #[token("|")]
    Pipe,
    // haha, ha
    #[token("1")]
    One,
    #[token("+")]
    Plus,
    #[token("*")]
    Ast,
    #[token("=>")]
    Arrow,

    #[token("read")]
    Read,
    #[token("proc")]
    Proc,
    #[token("type")]
    Type,
    #[token("fail")]
    Fail,
    #[token("write")]
    Write,
    #[token("cut")]
    Cut,
    #[token("id")]
    Id,
    #[token("call")]
    Call,
    #[regex(r"//[^\n]*", logos::skip)]
    #[regex(r"/*", nested_comment)]
    #[regex(r"[ \n\t\v\r\f]", logos::skip)]
    Ignore,
}
