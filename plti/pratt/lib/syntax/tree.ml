open Core
open PPrint

(* Paper, §2.2: "We employ the following abstract syntax tree to represent
   expressions." Its initial constructors are Literal, Reference, Application,
   Error and Empty. As §3 adds language constructs, we add constructors with
   their actual arities. For example, If has exactly a condition, a consequent
   and an optional alternative; a list of arbitrarily many children cannot
   accidentally be passed as an if-expression.

   MLscript's `data class` declarations play the same role as these OCaml
   variants (and Scala enum/case-class hierarchies). The trailing 'a is an
   annotation: here it is a source span, but later lessons can use type info.
   Items is an intermediate list returned by named grammar fragments, such as
   let-bindings. It is not a source-language expression. *)
type direction = Up | Down
type definition_kind = TypeDefinition | ExceptionDefinition

type 'a t =
  | Literal of Token.literal_kind * string * 'a
  | Reference of string * 'a
  | Wildcard of 'a
  | Application of 'a t * 'a t list * 'a
  | Tuple of 'a t list * 'a
  | Sequence of 'a t list * 'a
  | Items of 'a t list * 'a
  | Bracketed of Token.bracket_kind * 'a t option * 'a
  | Let of bool * 'a t list * 'a t option * 'a
  | Binding of 'a t * 'a t * 'a
  | Lambda of 'a t * 'a t * 'a
  | Case of 'a t * 'a t * 'a
  | Match of 'a t option * 'a t list * 'a
  | Try of 'a t * 'a t list * 'a
  | If of 'a t * 'a t * 'a t option * 'a
  | While of 'a t * 'a t * 'a
  | For of direction * 'a t * 'a t * 'a t * 'a t * 'a
  | Assignment of 'a t * 'a t * 'a
  | Ascription of 'a t * 'a t * 'a
  | Select of 'a t * 'a t * 'a
  | Index of 'a t * 'a t * 'a
  | Alternative of 'a t * 'a t * 'a
  | Alias of 'a t * 'a t * 'a
  | Product of 'a t list * 'a
  | TypeArguments of 'a t list * 'a
  | Constructor of 'a t * 'a t option * 'a
  | Mutable of 'a t * 'a
  | TypeHead of 'a t * 'a t list * 'a
  | TypeAlias of 'a t * 'a
  | RecordType of 'a t list * 'a
  | TypeBinding of 'a t * 'a t * 'a
  | Define of definition_kind * 'a t list * 'a
  | Directive of 'a t * 'a t * 'a
  | Empty of 'a
  | Error of 'a t option * Source.diagnostic * 'a

type located = Source.span t

let tag = function
  | Literal (_, _, tag)
  | Reference (_, tag)
  | Wildcard tag
  | Application (_, _, tag)
  | Tuple (_, tag)
  | Sequence (_, tag)
  | Items (_, tag)
  | Bracketed (_, _, tag)
  | Let (_, _, _, tag)
  | Binding (_, _, tag)
  | Lambda (_, _, tag)
  | Case (_, _, tag)
  | Match (_, _, tag)
  | Try (_, _, tag)
  | If (_, _, _, tag)
  | While (_, _, tag)
  | For (_, _, _, _, _, tag)
  | Assignment (_, _, tag)
  | Ascription (_, _, tag)
  | Select (_, _, tag)
  | Index (_, _, tag)
  | Alternative (_, _, tag)
  | Alias (_, _, tag)
  | Product (_, tag)
  | TypeArguments (_, tag)
  | Constructor (_, _, tag)
  | Mutable (_, tag)
  | TypeHead (_, _, tag)
  | TypeAlias (_, tag)
  | RecordType (_, tag)
  | TypeBinding (_, _, tag)
  | Define (_, _, tag)
  | Directive (_, _, tag)
  | Empty tag
  | Error (_, _, tag) ->
      tag

(* Rebuild one level. Keeping the child mapper separate from the tag mapper
   lets us reuse the exhaustive traversal for both annotations and macros.
   Adding a constructor forces us to update this match and the printer. *)
let map_node tree ~child:f ~annotation:g =
  let fs trees = List.map trees ~f in
  let fo tree = Option.map tree ~f in
  match tree with
  | Literal (kind, text, t) -> Literal (kind, text, g t)
  | Reference (name, t) -> Reference (name, g t)
  | Wildcard t -> Wildcard (g t)
  | Application (callee, args, t) -> Application (f callee, fs args, g t)
  | Tuple (xs, t) -> Tuple (fs xs, g t)
  | Sequence (xs, t) -> Sequence (fs xs, g t)
  | Items (xs, t) -> Items (fs xs, g t)
  | Bracketed (kind, x, t) -> Bracketed (kind, fo x, g t)
  | Let (recursive, bindings, body, t) -> Let (recursive, fs bindings, fo body, g t)
  | Binding (a, b, t) -> Binding (f a, f b, g t)
  | Lambda (a, b, t) -> Lambda (f a, f b, g t)
  | Case (a, b, t) -> Case (f a, f b, g t)
  | Match (x, arms, t) -> Match (fo x, fs arms, g t)
  | Try (x, arms, t) -> Try (f x, fs arms, g t)
  | If (a, b, c, t) -> If (f a, f b, fo c, g t)
  | While (a, b, t) -> While (f a, f b, g t)
  | For (direction, a, b, c, d, t) -> For (direction, f a, f b, f c, f d, g t)
  | Assignment (a, b, t) -> Assignment (f a, f b, g t)
  | Ascription (a, b, t) -> Ascription (f a, f b, g t)
  | Select (a, b, t) -> Select (f a, f b, g t)
  | Index (a, b, t) -> Index (f a, f b, g t)
  | Alternative (a, b, t) -> Alternative (f a, f b, g t)
  | Alias (a, b, t) -> Alias (f a, f b, g t)
  | Product (xs, t) -> Product (fs xs, g t)
  | TypeArguments (xs, t) -> TypeArguments (fs xs, g t)
  | Constructor (name, payload, t) -> Constructor (f name, fo payload, g t)
  | Mutable (x, t) -> Mutable (f x, g t)
  | TypeHead (name, params, t) -> TypeHead (f name, fs params, g t)
  | TypeAlias (x, t) -> TypeAlias (f x, g t)
  | RecordType (xs, t) -> RecordType (fs xs, g t)
  | TypeBinding (a, b, t) -> TypeBinding (f a, f b, g t)
  | Define (kind, xs, t) -> Define (kind, fs xs, g t)
  | Directive (a, b, t) -> Directive (f a, f b, g t)
  | Empty t -> Empty (g t)
  | Error (tree, diagnostic, t) -> Error (fo tree, diagnostic, g t)

let rec tag_map tree ~f = map_node tree ~child:(fun tree -> tag_map tree ~f) ~annotation:f
let with_tag tree tag = map_node tree ~child:Fn.id ~annotation:(fun _ -> tag)

let span_of_children fallback = function
  | [] -> fallback
  | first :: rest ->
      List.fold rest ~init:(tag first) ~f:(fun span tree -> Source.cover span (tag tree))

let apply callee args span = Application (callee, args, span)
let operator name lhs rhs =
  let span = Source.cover (tag lhs) (tag rhs) in
  Application (Reference (name, span), [ lhs; rhs ], span)

(* §3.6 substitutes captured syntax for references in a replacement tree.
   This is deliberately syntactic, not hygienic: a binder in the replacement
   can capture a name. Inserted trees retain use-site spans and are not visited
   again, so substituting x -> x does not recurse forever. *)
let rec substitute tree env =
  match tree with
  | Reference (name, _) -> Option.value (Map.find env name) ~default:tree
  | tree -> map_node tree ~child:(fun tree -> substitute tree env) ~annotation:Fn.id

let rec pp_tree tree =
  let node name xs = pp_list (string name :: List.map xs ~f:pp_tree) in
  match tree with
  | Literal (kind, text, _) -> Token.pp_kind (Token.Literal (kind, text))
  | Reference (name, _) -> string name
  | Wildcard _ -> string "_"
  | Application (callee, args, _) -> pp_list (pp_tree callee :: List.map args ~f:pp_tree)
  | Tuple (xs, _) -> node "tuple" xs
  | Sequence (xs, _) -> node "sequence" xs
  | Items (xs, _) -> node "items" xs
  | Bracketed (kind, inner, _) ->
      let name =
        match kind with
        | Token.Round -> "unit"
        | Square -> "list"
        | Curly -> "record"
        | Array -> "array"
        | BeginEnd -> "begin"
      in
      node name (Option.to_list inner)
  | Let (recursive, bindings, body, _) ->
      node (if recursive then "let-rec" else "let") (bindings @ Option.to_list body)
  | Binding (a, b, _) -> node "=" [ a; b ]
  | Lambda (a, b, _) -> node "fun" [ a; b ]
  | Case (a, b, _) -> node "case" [ a; b ]
  | Match (subject, arms, _) ->
      node (if Option.is_none subject then "function" else "match") (Option.to_list subject @ arms)
  | Try (body, arms, _) -> node "try" (body :: arms)
  | If (condition, consequent, alternative, _) ->
      node "if" ([ condition; consequent ] @ Option.to_list alternative)
  | While (a, b, _) -> node "while" [ a; b ]
  | For (direction, variable, start, stop, body, _) ->
      node
        (match direction with Up -> "for-to" | Down -> "for-downto")
        [ variable; start; stop; body ]
  | Assignment (a, b, _) -> node "<-" [ a; b ]
  | Ascription (a, b, _) -> node ":" [ a; b ]
  | Select (a, b, _) -> node "select" [ a; b ]
  | Index (a, b, _) -> node "index" [ a; b ]
  | Alternative (a, b, _) -> node "or-pattern" [ a; b ]
  | Alias (a, b, _) -> node "as" [ a; b ]
  | Product (xs, _) -> node "product" xs
  | TypeArguments (xs, _) -> node "type-arguments" xs
  | Constructor (name, None, _) -> pp_tree name
  | Constructor (name, Some payload, _) -> node "of" [ name; payload ]
  | Mutable (x, _) -> node "mutable" [ x ]
  | TypeHead (name, params, _) -> node "type-head" (name :: params)
  | TypeAlias (x, _) -> node "alias" [ x ]
  | RecordType (xs, _) -> node "record-type" xs
  | TypeBinding (a, b, _) -> node "type-binding" [ a; b ]
  | Define (kind, xs, _) ->
      node (match kind with TypeDefinition -> "type" | ExceptionDefinition -> "exception") xs
  | Directive (a, b, _) -> node "directive" [ a; b ]
  | Empty _ -> string "<empty>"
  | Error (tree, diagnostic, _) ->
      pp_list
        ([ string "error"; Document.quoted diagnostic.message ]
        @ Option.to_list (Option.map tree ~f:pp_tree))

and pp_list documents = group (lparen ^^ nest 2 (separate (break 1) documents) ^^ rparen)

let string_of_tree tree = Document.string_of_document (pp_tree tree)
