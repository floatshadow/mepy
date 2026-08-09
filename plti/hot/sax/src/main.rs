mod parse;

use parse::parse_from_file;
use std::env;

fn main() {
    if let Some(fname) = env::args().nth(1) {
        for dfn in parse_from_file(fname) {
            println!("{:?}", dfn);
        }
    } else {
        println!("usage:");
        println!("./sax <filename.sax>");
    }
}
