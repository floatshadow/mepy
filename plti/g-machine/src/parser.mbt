pub struct Parser {
  tokenizer: Lexer
  mut token: Token?
}

pub struct PResult[T] {
  inner: T
  ntokens: Int
}

type PToken = PResult[Token]

type PRawExpr = PResult[RawExpr[String]]

type PScDefs = PResult[ScDefs]

pub fn Parser::new(s: String) -> Parser {
  Parser:: { tokenizer: Lexer::new(s), token: None }
}
fn Parser::skip_token(self : Parser) -> Unit raise Failure {
  // if it's eof, don't skip
  match self.token {
    Some({ tag: TokenTag::Eof, .. }) => fail("trying to skip eof")
    _ => self.token = None
  }
}

fn Parser::peek_token(self : Parser) -> PToken raise Failure {
  let token = match self.token {
    Some(tok) => { inner: tok, ntokens: 1 }
    None => {
      let mut tok = self.tokenizer.next_err()
      while tok.tag == TokenTag::Newline {
        tok = self.tokenizer.next_err()
      }
      self.token = Some(tok)
      { inner: tok, ntokens: 1 }
    }
  }
  token
}

pub fn Parser::next_token(self : Parser) -> PToken raise Failure {
  match self.token {
    Some(tok) => {
      self.token = None
      { inner: tok, ntokens: 1 }
    }
    None => {
      let mut tok = self.tokenizer.next_err()
      while tok.tag == TokenTag::Newline {
        tok = self.tokenizer.next_err()
      }
      { inner: tok, ntokens: 1 }
    }
  }
}

fn Parser::reach_eof(self : Parser) -> Bool {
  try {
    match self.peek_token() {
      { inner: { tag: TokenTag::Eof, .. }, .. } => true
      _ => false
    }
  } catch {
    _ => false
  }
}

fn Parser::expect_paired_open(self : Parser, po : Paired) -> PToken raise Failure {
  match self.next_token() {
    { inner: { tag: TokenTag::PairedOpen(po2), .. }, .. } as r =>
      if po == po2 {
        r
      } else {
        fail("expected paired open \{po}, got \{r.inner}")
      }
    tok => fail("expected paired open \{po}, got \{tok.inner}")
  }
}

fn Parser::expect_paired_close(self : Parser, pc : Paired) -> PToken raise Failure {
  match self.next_token() {
    { inner: { tag: TokenTag::PairedClose(pc2), .. }, .. } as r =>
      if pc == pc2 {
        r
      } else {
        fail("expected paired close \{pc}, got \{r.inner}")
      }
    tok => fail("expected paired close \{pc}, got \{tok.inner}")
  }
}

fn Parser::expect_ident(self : Parser) -> PToken raise Failure {
  match self.next_token() {
    { inner: { tag: TokenTag::Identifier, .. }, .. } as r => r
    tok => fail("expected identifier, got \{tok.inner}")
  }
}

fn Parser::expect_int(self : Parser) -> PResult[Int] raise Failure {
  match self.next_token() {
    { inner: { tag: TokenTag::IntLiteral(n), .. }, .. } =>
      { inner: n, ntokens: 1 }
    tok => fail("expected int, got \{tok.inner}")
  }
}


fn Parser::peek_keyword(self : Parser, kw : Keyword) -> Bool {
  let token = try {
    self.peek_token()
  } catch {
    _ => return false
  }
  match token {
    { inner: { tag: TokenTag::Kw(kw2), .. }, .. } => kw == kw2
    _ => false
  }
}

fn Parser::parse_raw_expression(self: Parser) -> PRawExpr raise Failure {
  let mut ntokens = 0
  let lookahead = self.peek_token()
  let raw_expr = match lookahead.inner.tag {
    PairedOpen(Parenthesis) => {
      self.skip_token()
      let exprs = []
      let mut lookahead2 = self.peek_token()
      while lookahead2.inner.tag != PairedClose(Parenthesis) {
        let expr = self.parse_raw_expression()
        ntokens += expr.ntokens
        exprs.push(expr.inner)
        lookahead2 = self.peek_token()
      }
      let _ = self.expect_paired_close(Parenthesis)
      ntokens += 1
      if exprs.length() == 0 {
        fail("empty application")
      }
      if exprs.length() == 1 {
        exprs[0]
      } else {
        // currying
        let mut a0 = exprs[0]
        for i in 1..<exprs.length() {
          a0 = RawExpr::App(a0, exprs[i])
        }
        a0
      }
    }
    TokenTag::Identifier => {

      let ident = self.expect_ident()
      ntokens += ident.ntokens
      RawExpr::Var(ident.inner.span)
    }
    TokenTag::IntLiteral(_) => {
      let int = self.expect_int()
      ntokens += int.ntokens
      RawExpr::Num(int.inner)
    }
    _ => fail("unexpected token \{lookahead.inner}")
  }


  { inner: raw_expr, ntokens: ntokens }
}

pub fn Parser::parse(self: Parser) -> PScDefs raise Failure {
  let lookahead = self.peek_token()
  let mut ntokens = 0
  let scdefs = match lookahead.inner.tag {
    PairedOpen(Parenthesis) => {
      self.skip_token()
      ntokens += 1
      let kw = self.next_token()
      if kw.inner.tag != TokenTag::Kw(Keyword::Defn) {
        fail("expected defn on top level but get \{kw.inner}")
      }
      ntokens += kw.ntokens

      let ident = self.expect_ident()
      ntokens += ident.ntokens
      let name = ident.inner.span
      let args = []
      // parse parameter list
      let _ = self.expect_paired_open(Bracket)
      ntokens += 1
      let mut lookahead2 = self.peek_token()
      while lookahead2.inner.tag != PairedClose(Bracket) {
        let ident = self.expect_ident()
        ntokens += ident.ntokens
        args.push(ident.inner.span)
        lookahead2 = self.peek_token()
      }
      let _ = self.expect_paired_close(Bracket)
      ntokens += 1
      let body = self.parse_raw_expression()
      ntokens += body.ntokens
      // end super combinator definition
      let _ = self.expect_paired_close(Parenthesis)
      ntokens += 1
      let scdef = ScDef:: {name, args: @list.from_array(FixedArray::from_array(args)), body: body.inner}
      @list.cons(scdef, @list.empty())
    }
    Eof => @list.empty()
    _ => fail("unexpected token \{lookahead.inner}")
  }
  { inner: scdefs, ntokens: ntokens }
}