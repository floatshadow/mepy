open Core

type 'a attempt = Absent | Parsed of 'a

(* Paper §3.1 splits the original expr/exprCont pair into parseKind and
   parseRule. These three modes make that split visible in the type:
   Sequence consumes the fixed tail of a selected route, Prefix chooses a
   construct that can start a phrase, and Continuation extends a left tree. *)
type mode = Sequence | Prefix | Continuation [@@deriving equal]

module Cursor : sig
  type t
  val create : Token.t list -> Source.span -> t
  val peek : t -> Token.t option
  val take : t -> unit
  val index : t -> int
  val span : t -> Source.span
  val consumed_span : t -> Source.span -> Source.span
end = struct
  type t = { tokens : Token.t array; eof : Source.span; mutable index : int }
  let create tokens eof = { tokens = Array.of_list tokens; eof; index = 0 }
  let peek cursor =
    if cursor.index < Array.length cursor.tokens then Some cursor.tokens.(cursor.index) else None
  let take cursor = cursor.index <- cursor.index + 1
  let index cursor = cursor.index
  let span cursor = match peek cursor with Some token -> token.span | None -> cursor.eof
  let consumed_span cursor start =
    if cursor.index = 0 then start else Source.cover start cursor.tokens.(cursor.index - 1).span
end

type t = {
  grammar : Grammar.t;
  cursor : Cursor.t;
  trace : string -> unit;
  mutable active : (SyntaxKind.t * int) list;
}

let create ?(trace = fun _ -> ()) grammar tokens eof =
  { grammar; cursor = Cursor.create tokens eof; trace; active = [] }

let take parser =
  let token = Option.value_exn (Cursor.peek parser.cursor) in
  parser.trace
    [%string
      "consume #%{Cursor.index parser.cursor#Int}: %{Document.string_of_document (Token.pp_token \
       token)}"];
  Cursor.take parser.cursor

let fail parser message = Source.error (Cursor.span parser.cursor) message

let expected parser label =
  let found =
    match Cursor.peek parser.cursor with
    | None -> "end of input"
    | Some token -> Document.string_of_document (Token.pp_token token)
  in
  fail parser [%string "expected %{label}; found %{found}"]

let require parser label = function Parsed value -> value | Absent -> expected parser label
let name_at parser =
  Option.bind (Cursor.peek parser.cursor) ~f:(fun token -> Token.spelling token.kind)

let stopped parser stops =
  Option.exists (name_at parser) ~f:(fun name -> List.mem stops name ~equal:String.equal)

let terminal parser kind =
  match (kind, Cursor.peek parser.cursor) with
  | SyntaxKind.Identifier, Some { kind = Token.Identifier name; span }
    when not (Grammar.is_reserved parser.grammar name) ->
      take parser;
      Parsed (Tree.Reference (name, span))
  | FieldIdentifier, Some { kind = Token.Identifier name; span } ->
      (* A reserved word is still a field after `.`. Without this closed kind,
         §3.6's own `String.format` replacement stops parsing as soon as the
         preceding #keyword directive reserves `format`. *)
      take parser;
      Parsed (Tree.Reference (name, span))
  | TypeVariable, Some { kind = Token.Identifier name; span } when String.is_prefix name ~prefix:"'"
    ->
      take parser;
      Parsed (Tree.Reference (name, span))
  | Literal expected, Some { kind = Token.Literal (literal_kind, text); span } ->
      let accepts =
        match expected with None -> true | Some expected -> Poly.equal expected literal_kind
      in
      if accepts then (
        take parser;
        Parsed (Tree.Literal (literal_kind, text, span)))
      else Absent
  | _ -> Absent

(* The invariant of Absent is stronger than Tree.Empty in the snippets:
   the cursor is unchanged. Once a keyword/operator is consumed, every required
   suffix either succeeds or raises Source.Error. No speculative backtracking
   and no consumed error can disappear into an optional application. *)
let rec parse_kind parser stops kind bp =
  if stopped parser stops then Absent
  else if SyntaxKind.is_terminal kind then terminal parser kind
  else if SyntaxKind.equal kind Binding then parse_kind parser ("=" :: stops) Term bp
  else
    let position = Cursor.index parser.cursor in
    let start = Cursor.span parser.cursor in
    if
      List.exists parser.active ~f:(fun (name, index) ->
          SyntaxKind.equal name kind && index = position)
    then
      Source.invalid
        [%string "nonproductive recursion in %{SyntaxKind.name kind}; factor its leading reference"];
    let definition =
      match Grammar.kind parser.grammar kind with
      | Some definition -> definition
      | None -> Source.invalid [%string "unknown syntax kind %{SyntaxKind.name kind}"]
    in
    parser.active <- (kind, position) :: parser.active;
    Exn.protect
      ~finally:(fun () -> parser.active <- List.tl_exn parser.active)
      ~f:(fun () ->
        parser.trace [%string "enter %{SyntaxKind.name kind} bp=%{bp#Int} token=%{position#Int}"];
        let initial = ParseRule.without_self kind definition.rule in
        let mode =
          match definition.atoms with Grammar.No_atoms -> Sequence | Terms | Types -> Prefix
        in
        let head = parse_rule parser stops mode bp initial in
        let head =
          match head with
          | Parsed _ -> head
          | Absent -> parse_atom parser stops definition.atoms kind bp
        in
        match head with
        | Absent -> Absent
        | Parsed head ->
            let rec continue acc =
              (* Read the current rule, so an extension installed between program
               phrases is visible without recomputing cached afterRef values. *)
              let rule = (Map.find_exn parser.grammar.kinds (SyntaxKind.name kind)).rule in
              match ParseRule.after_ref kind rule with
              | None -> acc
              | Some rest -> (
                  let before = Cursor.index parser.cursor in
                  match parse_rule parser stops Continuation bp rest with
                  | Absent -> acc
                  | Parsed extend ->
                      if before = Cursor.index parser.cursor then
                        Source.invalid [%string "nullable continuation in %{SyntaxKind.name kind}"];
                      let result = extend acc in
                      parser.trace
                        [%string "continue %{SyntaxKind.name kind}: %{Tree.string_of_tree result}"];
                      continue result)
            in
            let result = continue head in
            (* A rule's process functions only receive semantic children, as in
             the paper, so they cannot see keyword spans. The kind boundary is
             the one generic place where we know the complete consumed range. *)
            Parsed (Tree.with_tag result (Cursor.consumed_span parser.cursor start)))

and parse_atom parser stops atoms kind _bp =
  match (atoms, Cursor.peek parser.cursor) with
  | Grammar.No_atoms, _ -> Absent
  | Terms, Some { kind = Token.Identifier "_"; span } when SyntaxKind.equal kind Pattern ->
      (* The archived Caml grammar gives [_] its own tree node. This matters to
         later binding analysis: a wildcard never introduces a variable. *)
      take parser;
      Parsed (Tree.Wildcard span)
  | (Terms | Types), Some { kind = Token.Identifier name; span }
    when not (Grammar.is_reserved parser.grammar name) ->
      take parser;
      Parsed (Tree.Reference (name, span))
  | Terms, Some { kind = Token.Literal (literal_kind, text); span } ->
      take parser;
      Parsed (Tree.Literal (literal_kind, text, span))
  | Terms, Some { kind = Token.Symbol name; span } -> (
      match Operator.prefix_binding_power name with
      | Some power ->
          take parser;
          let rhs = require parser "prefix operand" (parse_kind parser stops kind power) in
          Parsed
            (Tree.apply (Tree.Reference (name, span)) [ rhs ] (Source.cover span (Tree.tag rhs)))
      | None -> Absent)
  | (Terms | Types), (Some _ | None) -> Absent

and parse_rule : type a. t -> string list -> mode -> int -> a ParseRule.t -> a attempt =
 fun parser stops mode bp rule ->
  let before = Cursor.index parser.cursor in
  let fallback () =
    match ParseRule.end_choice rule with Some value -> Parsed value | None -> Absent
  in
  let keyword_branch =
    Option.bind (name_at parser) ~f:(fun name ->
        Option.bind (Grammar.keyword parser.grammar name) ~f:(fun keyword ->
            Option.map (ParseRule.keyword_choice rule name) ~f:(fun rest -> (keyword, rest))))
  in
  let can_enter (keyword : Grammar.keyword) =
    match mode with
    | Sequence -> true
    | Prefix | Continuation -> Option.exists keyword.lbp ~f:(fun lbp -> lbp > bp)
  in
  match keyword_branch with
  | Some (keyword, rest)
    when can_enter keyword && (equal_mode mode Sequence || not (stopped parser stops)) ->
      let start = Cursor.span parser.cursor in
      parser.trace [%string "choose keyword %{keyword.name} at bp=%{bp#Int}"];
      take parser;
      (* Explicit delimiters are consumed regardless of lbp. In a phrase tail
           they reset to base, as in the archived parseRule; entry and infix
           keywords instead use rbp, inheriting the outer threshold for None. *)
      let next_bp = if equal_mode mode Sequence then 0 else Option.value keyword.rbp ~default:bp in
      let stops = match keyword.name with "(" | "[" | "{" | "[|" | "begin" -> [] | _ -> stops in
      let value =
        require parser [%string "syntax after %{keyword.name}"]
          (parse_rule parser stops Sequence next_bp rest)
      in
      ignore (Cursor.consumed_span parser.cursor start : Source.span);
      Parsed value
  | _ when equal_mode mode Continuation && stopped parser stops -> Absent
  | Some _ when not (equal_mode mode Sequence) -> Absent
  | _ -> (
      let infix =
        List.find_map rule.choices ~f:(function
          | ParseRule.Infix _ as choice -> Some choice
          | _ -> None)
      in
      let operator_result =
        match (infix, Cursor.peek parser.cursor) with
        | ( Some (Infix { operator; rhs_kind; rest; process; _ }),
            Some { kind = Token.Symbol name; _ } )
          when not (Grammar.is_reserved parser.grammar name) -> (
            match operator name with
            | Some op when op.lbp > bp ->
                parser.trace
                  [%string
                    "operator %{name}: left=%{op.lbp#Int}, right=%{op.rbp#Int}, \
                     threshold=%{bp#Int}; continue"];
                take parser;
                let rhs =
                  require parser "operator right operand" (parse_kind parser stops rhs_kind op.rbp)
                in
                let tail =
                  require parser "operator suffix" (parse_rule parser stops Sequence op.lbp rest)
                in
                Some (Parsed (process name rhs tail))
            | Some op ->
                parser.trace
                  [%string "operator %{name}: left=%{op.lbp#Int}, threshold=%{bp#Int}; stop"];
                Some Absent
            | None -> None)
        | _ -> None
      in
      match operator_result with
      | Some result -> result
      | None ->
          let rec try_references = function
            | [] -> fallback ()
            | ParseRule.Ref { kind; label; bp = entry; rest; process; _ } :: remaining -> (
                if Option.value entry ~default:Int.max_value <= bp then try_references remaining
                else
                  let argument_bp =
                    match mode with
                    | Continuation -> Option.value entry ~default:bp
                    | Prefix | Sequence -> bp
                  in
                  match parse_kind parser stops kind argument_bp with
                  | Absent -> try_references remaining
                  | Parsed tree -> (
                      let tail = parse_rule parser stops Sequence argument_bp rest in
                      match tail with
                      | Parsed tail -> Parsed (process tree tail)
                      | Absent when Cursor.index parser.cursor = before -> try_references remaining
                      | Absent ->
                          expected parser (if String.is_empty label then "rule suffix" else label)))
            | _ :: remaining -> try_references remaining
          in
          try_references rule.choices)

let parse_kind_exn parser kind = require parser (SyntaxKind.name kind) (parse_kind parser [] kind 0)

let finish_exn parser =
  if Option.is_some (Cursor.peek parser.cursor) then expected parser "end of input"

let expression_exn ?(kind = SyntaxKind.Term) ?trace ?file grammar source =
  let tokens, eof = Lexer.scan ?file source in
  let parser = create ?trace grammar tokens eof in
  let tree = parse_kind_exn parser kind in
  finish_exn parser;
  tree

(* Caml Light's top level is the one deliberate ad-hoc seam. This is the
   bootstrapping issue discussed in §3.3 and implemented by the artifact's
   top-level loop: a leading keyword may introduce either a term or a
   declaration. We prefer the term rule first, then try a declaration.
   Directives take effect before the next phrase is parsed; [;;] is a separator. *)
let program_exn ?trace ?file grammar source =
  let tokens, eof = Lexer.scan ?file source in
  let parser = create ?trace grammar tokens eof in
  let starts_with_keyword rule =
    Option.exists (name_at parser) ~f:(fun name ->
        Option.is_some (ParseRule.keyword_choice rule name))
  in
  let rec loop trees =
    match Cursor.peek parser.cursor with
    | None -> List.rev trees
    | Some { kind = Token.Symbol ";;"; _ } ->
        take parser;
        loop trees
    | Some _ ->
        let before = Cursor.index parser.cursor in
        let term = Map.find_exn grammar.kinds (SyntaxKind.name Term) in
        let declaration = Map.find_exn grammar.kinds (SyntaxKind.name Declaration) in
        let tree =
          if starts_with_keyword term.rule then parse_kind_exn parser Term
          else if starts_with_keyword declaration.rule then parse_kind_exn parser Declaration
          else parse_kind_exn parser Term
        in
        if Cursor.index parser.cursor = before then
          Source.invalid "a top-level parser returned without consuming input";
        if Extension.apply grammar tree then loop trees else loop (tree :: trees)
  in
  loop []
