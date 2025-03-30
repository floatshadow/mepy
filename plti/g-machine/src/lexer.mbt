typealias HashMap[K, V] = @immut/hashmap.T[K, V]

pub struct Lexer {
  buffer: String
  mut index : Int
  mut colstart: Int
  mut line :Int
} derive(Show)

pub struct Loc {
  line: Int
  column : Int
  index : Int
} derive(Show, Eq, Hash)


pub enum Keyword {
  Defn
} derive(Show, Eq, Hash)

pub enum Paired {
  Bracket
  Parenthesis
} derive (Show, Eq, Hash)

pub enum TokenTag {
  Eof
  Newline
  Identifier
  Kw(Keyword)
  IntLiteral(Int)
  PairedOpen(Paired)
  PairedClose(Paired)
  Err(String)
} derive(Show, Eq, Hash)

pub struct Token {
  tag : TokenTag
  loc : Loc
  span : String
} derive(Show, Eq, Hash)

fn Token::new(tag: TokenTag, loc: Loc, span: String) -> Token {
  Token:: { tag, loc, span }
}

let keywords: HashMap[String, Keyword] = @immut/hashmap.from_array([
  ("defn", Keyword::Defn)
])

pub fn Lexer::new(s: String) -> Lexer {
  let buffer = StringBuilder::new(size_hint=s.length() + 1)
  buffer.write_string(s)
  buffer.write_char(Char::from_int(0))
  Lexer:: {
    buffer: buffer.to_string(),
    index: 0,
    colstart: 0,
    line: 1
  }
}

fn Lexer::move_to_newline(self : Lexer) -> Unit {
  self.colstart = self.index
  self.line += 1
}

fn Lexer::get_loc(self : Lexer) -> Loc {
  { line: self.line, column: self.index - self.colstart + 1, index: self.index }
}

fn Lexer::make_span(self : Lexer, start : Int) -> String {
  self.buffer.substring(start~, end=self.index)
}

fn Lexer::make_token(self : Lexer, tag : TokenTag, loc : Loc) -> Token {
  Token::new(tag, loc, self.make_span(loc.index))
}

fn Lexer::make_error(self : Lexer, loc : Loc, msg : String) -> Token {
  Token::new(TokenTag::Err(msg), loc, self.make_span(loc.index))
}

fn Lexer::eof(self : Lexer) -> Token {
  Token::new(TokenTag::Eof, self.get_loc(), "<empty>")
}

fn Lexer::is_keyword(s : String) -> Keyword? {
  keywords.find(s)
}

fn Lexer::ch(self : Lexer) -> Char {
  self.buffer[self.index]
}

fn Lexer::ch_at(self : Lexer, i : Int) -> Char {
  self.buffer[self.index + i]
}

fn Lexer::ident(self : Lexer, loc : Loc) -> Token {
  while true {
    let cond = (self.ch() >= 'a' && self.ch() <= 'z') ||
      (self.ch() >= 'A' && self.ch() <= 'Z') ||
      self.ch() == '_' ||
      (self.ch() >= '0' && self.ch() <= '9')
    if not(cond) {
      break
    }
    self.index += 1
  }
  let tok = self.make_token(TokenTag::Identifier, loc)
  Lexer::is_keyword(tok.span).map_or(
    tok,
    fn(kw) { Token::new(TokenTag::Kw(kw), loc, tok.span) },
  )
}

fn Lexer::numeric_literal(self : Lexer, loc : Loc) -> Token {
  let start = self.index
  self.index += 1
  while true {
    let n = self.ch()
    if n < '0' || n > '9' {
      break
    }
    self.index += 1
  }

  try {
    let value = @strconv.parse_int!(
      self.buffer.substring(start~, end=self.index),
    )
    self.make_token(TokenTag::IntLiteral(value), loc)
  } catch {
    StrConvError(msg) => self.make_error(loc, msg)
  }
}

fn Lexer::skip_comment(self : Lexer) -> Unit {
  self.index += 2
  while true {
    if self.ch() == '\x00' {
      break
    } else if self.ch() == '\n' {
      self.index += 1
      self.move_to_newline()
      break
    }
    self.index += 1
  }
}


pub fn Lexer::next_err(self : Lexer) -> Token!Failure {
  let tok = self.next()
  match tok.tag {
    TokenTag::Err(msg) => fail!(msg)
    _ => tok
  }
}

fn Lexer::next(self : Lexer) -> Token {
  while true {
    let c = self.ch()
    let loc = self.get_loc()
    match c {
      '\x00' => return self.eof()
      ' ' | '\t' | '\r' => {
        self.index += 1
        while (match self.ch() {
                ' ' | '\t' | '\r' => true
                _ => false
              }) {
          self.index += 1
        }
        continue
      }
      '\n' => {
        self.index += 1
        self.move_to_newline()
        return self.make_token(TokenTag::Newline, loc)
      }
      '(' => {
        self.index += 1
        return self.make_token(TokenTag::PairedOpen(Paired::Parenthesis), loc)
      }
      ')' => {
        self.index += 1
        return self.make_token(TokenTag::PairedClose(Paired::Parenthesis), loc)
      }
      '[' => {
        self.index += 1
        return self.make_token(TokenTag::PairedOpen(Paired::Bracket), loc)
      }
      ']' => {
        self.index += 1
        return self.make_token(TokenTag::PairedClose(Paired::Bracket), loc)
      }
      '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' =>
        return self.numeric_literal(loc)
      _ =>
        if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_' {
          return self.ident(loc)
        } else {
          return self.make_error(loc, "invalid character: \{c}")
        }
    }
  } else {
    return self.make_error(self.get_loc(), "unreachable")
  }
}