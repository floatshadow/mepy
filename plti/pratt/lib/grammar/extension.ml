open Core
open ParseRule

(* Section 3.6 makes syntax extension part of the language. A directive is
   parsed normally, then interpreted before the parser reads the following
   phrase. The lexer therefore stays language-agnostic: an Identifier token can
   become a keyword after it has already been produced.

   Keyword spellings and User kind names remain strings because source programs
   create them at run time. Built-in kind names pass through SyntaxKind.of_name
   immediately and become ordinary variant constructors. *)
type syntax_element = Keyword of string | Reference of SyntaxKind.t * string option

let fail tree message = Source.error (Tree.tag tree) message

let rec application tree args =
  match tree with
  | Tree.Application (callee, arguments, _) -> application callee (arguments @ args)
  | callee -> (callee, args)

let list_elements tree =
  match tree with
  | Tree.Bracketed (Token.Square, None, _) -> Some []
  | Bracketed (Square, Some (Tuple (elements, _) | Sequence (elements, _) | Items (elements, _)), _)
    ->
      Some elements
  | Bracketed (Square, Some element, _) -> Some [ element ]
  | _ -> None

let literal_string = function Tree.Literal (Token.String, text, _) -> Some text | _ -> None

let precedence tree =
  let integer text =
    match Option.try_with (fun () -> Int.of_string text) with
    | Some power -> power
    | None -> fail tree "binding power is outside OCaml's integer range"
  in
  match tree with
  | Tree.Reference ("None", _) -> None
  | Literal (Integer, text, _) -> Some (integer text)
  | tree -> (
      let callee, args = application tree [] in
      match (callee, args) with
      | Reference ("Some", _), [ Literal (Integer, text, _) ] -> Some (integer text)
      | _ -> fail tree "a binding power must be None, an integer, or Some integer")

let keyword_directive grammar body =
  let callee, args = application body [] in
  let args =
    match callee with
    | Tree.Literal (Token.String, _, _) as first -> first :: args
    | _ -> fail body "#keyword expects a string followed by two binding powers"
  in
  match args with
  | [ name; left; right ] ->
      let name =
        match literal_string name with
        | Some name -> name
        | None -> fail name "the first #keyword argument must be a string literal"
      in
      Grammar.register_keyword grammar ?lbp:(precedence left) ?rbp:(precedence right) name
  | _ -> fail body "#keyword expects exactly three arguments"

let syntax_element grammar target tree =
  let callee, args = application tree [] in
  match (callee, args, list_elements tree) with
  | Tree.Reference ("keyword", _), [ argument ], _ ->
      let name =
        match literal_string argument with
        | Some name -> name
        | None -> fail argument "keyword(...) expects a string literal"
      in
      if Option.is_none (Grammar.keyword grammar name) then
        fail argument [%string "keyword %{name} has not been declared"];
      Keyword name
  | _, _, Some [ kind ] ->
      let name =
        match literal_string kind with
        | Some name -> name
        | None -> fail kind "a syntax-kind name must be a string literal"
      in
      Reference (SyntaxKind.of_name name, None)
  | _, _, Some [ kind; label ] ->
      let kind =
        match literal_string kind with
        | Some name -> SyntaxKind.of_name name
        | None -> fail kind "a syntax-kind name must be a string literal"
      in
      let label =
        match literal_string label with
        | Some label -> label
        | None -> fail label "a capture label must be a string literal"
      in
      Reference (kind, Some label)
  | _ -> fail tree "expected keyword(\"...\"), [\"kind\"], or [\"kind\", \"label\"]"

let ensure_reference grammar target tree = function
  | Reference (kind, _) when SyntaxKind.equal kind target -> ()
  | Reference (kind, _) when SyntaxKind.is_terminal kind -> ()
  | Reference (kind, _) when Option.is_some (Grammar.kind grammar kind) -> ()
  | Reference (kind, _) -> fail tree [%string "unknown syntax kind %{SyntaxKind.name kind}"]
  | Keyword _ -> ()

let extension_directive grammar body =
  let target_tree, syntax_tree, replacement_tree =
    match list_elements body with
    | Some [ target; syntax; replacement ] -> (target, syntax, replacement)
    | _ -> fail body "#extend expects [target, syntax, replacement]"
  in
  let target =
    match literal_string target_tree with
    | Some name -> SyntaxKind.of_name name
    | None -> fail target_tree "the extension target must be a string literal"
  in
  if SyntaxKind.is_terminal target then
    fail target_tree [%string "closed syntax kind %{SyntaxKind.name target} cannot be extended"];
  let syntax_trees =
    match list_elements syntax_tree with
    | Some elements -> elements
    | None -> fail syntax_tree "the extension syntax must be a bracketed list"
  in
  if List.is_empty syntax_trees then fail syntax_tree "an extension route cannot be empty";
  let replacement =
    match list_elements replacement_tree with
    | Some [ tree ] -> tree
    | Some _ -> fail replacement_tree "the replacement brackets must contain one expression"
    | None -> fail replacement_tree "the replacement must be enclosed in square brackets"
  in
  let elements =
    List.map syntax_trees ~f:(fun tree ->
        let element = syntax_element grammar target tree in
        ensure_reference grammar target tree element;
        element)
  in
  (match elements with
  | [ Reference (kind, _) ] when SyntaxKind.equal kind target ->
      fail syntax_tree "a self-referential extension must consume a keyword or another kind"
  | _ -> ());
  let _labels =
    List.fold elements ~init:String.Set.empty ~f:(fun labels -> function
      | Reference (_, Some label) ->
          if Set.mem labels label then fail syntax_tree [%string "duplicate capture label %{label}"];
          Set.add labels label
      | Reference (_, None) | Keyword _ -> labels)
  in
  let rec compile = function
    | [] -> finish String.Map.empty
    | Keyword name :: rest -> rule [ keyword name (compile rest) ]
    | Reference (kind, label) :: rest ->
        rule
          [
            reference ?capture:label kind (compile rest) (fun tree env ->
                match label with None -> env | Some label -> Map.set env ~key:label ~data:tree);
          ]
  in
  let generated = map (compile elements) ~f:(fun env -> Tree.substitute replacement env) in
  Grammar.extend grammar target generated.choices

let apply grammar tree =
  match tree with
  | Tree.Directive (Reference ("keyword", _), body, _) ->
      keyword_directive grammar body;
      true
  | Directive (Reference ("extend", _), body, _) ->
      extension_directive grammar body;
      true
  | _ -> false
