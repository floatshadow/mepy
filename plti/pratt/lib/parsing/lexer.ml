open Core

(* A cursor belongs to one scan. In particular, keywords are not lexer state:
   the complete token stream can be produced before executing any directive.
   Literal values are decoded, while integer/float spellings remain lossless. *)
let scan ?(file = "<input>") source =
  let length = String.length source in
  let position = ref Source.initial in
  let offset () = !position.offset in
  let peek n = String.get source (offset () + n) in
  let available n = offset () + n < length in
  let starts text = String.is_substring_at source ~pos:(offset ()) ~substring:text in
  let consume () =
    let ch = peek 0 in
    position := Source.advance !position ch;
    ch
  in
  let skip n =
    for _ = 1 to n do
      ignore (consume () : char)
    done
  in
  let span start = { Source.file; start; finish = !position } in
  let fail start message = Source.error (span start) message in
  let slice start = String.sub source ~pos:start ~len:(offset () - start) in
  let while_char f =
    while available 0 && f (peek 0) do
      skip 1
    done
  in
  let is_letter ch = Char.is_alpha ch || Char.equal ch '_' in
  let is_ident ch = is_letter ch || Char.is_digit ch || Char.equal ch '\'' in
  let quoted start quote =
    skip 1;
    let buffer = Buffer.create 16 in
    let rec loop () =
      if not (available 0) then fail start "unterminated literal";
      match consume () with
      | ch when Char.equal ch quote -> Buffer.contents buffer
      | '\\' ->
          if not (available 0) then fail start "unterminated escape";
          let escaped = consume () in
          (match escaped with
          | 'n' -> Buffer.add_char buffer '\n'
          | 'r' -> Buffer.add_char buffer '\r'
          | 't' -> Buffer.add_char buffer '\t'
          | 'b' -> Buffer.add_char buffer '\b'
          | '\\' | '\'' | '"' | '`' -> Buffer.add_char buffer escaped
          | '\n' -> while_char (fun ch -> Char.equal ch ' ' || Char.equal ch '\t')
          | '0' .. '9' ->
              if not (available 1 && Char.is_digit (peek 0) && Char.is_digit (peek 1)) then
                fail start "decimal escapes need exactly three digits";
              let second = consume () in
              let third = consume () in
              let value =
                ((Char.to_int escaped - 48) * 100)
                + ((Char.to_int second - 48) * 10)
                + Char.to_int third - 48
              in
              if value > 255 then fail start "escape is outside the byte range";
              Buffer.add_char buffer (Char.of_int_exn value)
          | _ -> fail start [%string "unknown escape \\%{escaped#Char}"]);
          loop ()
      | ('\n' | '\r') when not (Char.equal quote '"') -> fail start "newline in character literal"
      | ch ->
          Buffer.add_char buffer ch;
          loop ()
    in
    loop ()
  in
  let rec comment start depth =
    if not (available 0) then fail start "unterminated comment";
    if starts "(*" then (
      skip 2;
      comment start (depth + 1))
    else if starts "*)" then (
      skip 2;
      if depth > 1 then comment start (depth - 1))
    else if Char.equal (peek 0) '"' then (
      ignore (quoted start '"' : string);
      comment start depth)
    else (
      skip 1;
      comment start depth)
  in
  let number start =
    let begin_offset = offset () in
    let digit_run valid =
      let first = offset () in
      while_char (fun ch -> valid ch || Char.equal ch '_');
      if offset () = first then fail start "expected digits in number"
    in
    let based prefix valid =
      skip 2;
      digit_run valid;
      if available 0 && is_ident (peek 0) then fail start [%string "invalid base-%{prefix} integer"];
      Token.Literal (Token.Integer, slice begin_offset)
    in
    if starts "0x" || starts "0X" then based "16" Char.is_hex_digit
    else if starts "0o" || starts "0O" then based "8" (fun ch -> Char.between ch ~low:'0' ~high:'7')
    else if starts "0b" || starts "0B" then
      based "2" (fun ch -> Char.equal ch '0' || Char.equal ch '1')
    else (
      digit_run Char.is_digit;
      let floating = ref false in
      if available 0 && Char.equal (peek 0) '.' && not (available 1 && Char.equal (peek 1) '.') then (
        floating := true;
        skip 1;
        while_char (fun ch -> Char.is_digit ch || Char.equal ch '_'));
      if available 0 && (Char.equal (peek 0) 'e' || Char.equal (peek 0) 'E') then (
        floating := true;
        skip 1;
        if available 0 && (Char.equal (peek 0) '+' || Char.equal (peek 0) '-') then skip 1;
        digit_run Char.is_digit);
      if available 0 && is_letter (peek 0) then fail start "invalid numeric suffix";
      Token.Literal ((if !floating then Token.Decimal else Token.Integer), slice begin_offset))
  in
  let rec loop acc =
    if not (available 0) then (List.rev acc, Source.point file !position)
    else
      let start = !position in
      if Char.is_whitespace (peek 0) then (
        skip 1;
        loop acc)
      else if starts "(*" then (
        skip 2;
        comment start 1;
        loop acc)
      else
        let kind =
          if starts "[|" then (
            skip 2;
            Token.Open Token.Array)
          else if starts "|]" then (
            skip 2;
            Token.Close Token.Array)
          else
            match peek 0 with
            | '(' ->
                skip 1;
                Token.Open Token.Round
            | ')' ->
                skip 1;
                Token.Close Token.Round
            | '[' ->
                skip 1;
                Token.Open Token.Square
            | ']' ->
                skip 1;
                Token.Close Token.Square
            | '{' ->
                skip 1;
                Token.Open Token.Curly
            | '}' ->
                skip 1;
                Token.Close Token.Curly
            | '"' -> Token.Literal (Token.String, quoted start '"')
            | '`' ->
                let text = quoted start '`' in
                if String.length text <> 1 then
                  fail start "a character literal must contain one byte";
                Token.Literal (Token.Character, text)
            | '\'' when available 2 && (Char.equal (peek 2) '\'' || Char.equal (peek 1) '\\') ->
                let text = quoted start '\'' in
                if String.length text <> 1 then
                  fail start "a character literal must contain one byte";
                Token.Literal (Token.Character, text)
            | '\'' ->
                let begin_offset = offset () in
                skip 1;
                if not (available 0 && is_letter (peek 0)) then
                  fail start "expected a type variable after apostrophe";
                while_char is_ident;
                Token.Identifier (slice begin_offset)
            | '0' .. '9' -> number start
            | ch when is_letter ch -> (
                let begin_offset = offset () in
                while_char is_ident;
                match slice begin_offset with
                | "begin" -> Token.Open Token.BeginEnd
                | "end" -> Token.Close Token.BeginEnd
                | ("true" | "false") as value -> Token.Literal (Token.Boolean, value)
                | name -> Token.Identifier name)
            | ';' ->
                if starts ";;" then (
                  skip 2;
                  Token.Symbol ";;")
                else (
                  skip 1;
                  Token.Symbol ";")
            | '#' ->
                skip 1;
                Token.Symbol "#"
            | ch when Operator.is_operator_char ch ->
                let begin_offset = offset () in
                skip 1;
                while available 0 && Operator.is_operator_char (peek 0) && not (starts "|]") do
                  skip 1
                done;
                Token.Symbol (slice begin_offset)
            | ch -> fail start [%string "unrecognized character %{ch#Char}"]
        in
        loop ({ Token.kind; span = span start } :: acc)
  in
  loop []
