open Core

(* §3.1 calls these "syntax kinds": the role played by a nonterminal in a
   grammar. The paper uses names such as "term" in a mutable map because users
   can introduce new kinds. In OCaml we can make the built-in vocabulary closed
   and exhaustively checked, while leaving a single explicit User case open. *)
type t =
  | Term
  | Type
  | Pattern
  | Binding
  | Identifier
  | FieldIdentifier
  | TypeVariable
  | Literal of Token.literal_kind option
  | LetBindings
  | SimpleMatching
  | TypeArguments
  | ConstructorDecl
  | Variants
  | LabelName
  | LabelDecl
  | LabelDecls
  | TypeParamsTail
  | TypeParams
  | TypedefLhs
  | TypedefRhs
  | Typedefs
  | Declaration
  | User of string

let name = function
  | Term -> "term"
  | Type -> "type"
  | Pattern -> "pattern"
  | Binding -> "binding"
  | Identifier -> "ident"
  | FieldIdentifier -> "field-ident"
  | TypeVariable -> "typevar"
  | Literal None -> "literal"
  | Literal (Some Token.Integer) -> "integer-literal"
  | Literal (Some Token.Decimal) -> "decimal-literal"
  | Literal (Some Token.String) -> "string-literal"
  | Literal (Some Token.Character) -> "character-literal"
  | Literal (Some Token.Boolean) -> "boolean-literal"
  | LetBindings -> "let-bindings"
  | SimpleMatching -> "simple-matching"
  | TypeArguments -> "type-arguments"
  | ConstructorDecl -> "constr-decl"
  | Variants -> "variants"
  | LabelName -> "label-name"
  | LabelDecl -> "label-decl"
  | LabelDecls -> "label-decls"
  | TypeParamsTail -> "type-params-tail"
  | TypeParams -> "type-params"
  | TypedefLhs -> "typedef-lhs"
  | TypedefRhs -> "typedef-rhs"
  | Typedefs -> "typedefs"
  | Declaration -> "decl"
  | User name -> name

let builtins =
  [
    Term;
    Type;
    Pattern;
    Binding;
    Identifier;
    FieldIdentifier;
    TypeVariable;
    Literal None;
    Literal (Some Token.Integer);
    Literal (Some Token.Decimal);
    Literal (Some Token.String);
    Literal (Some Token.Character);
    Literal (Some Token.Boolean);
    LetBindings;
    SimpleMatching;
    TypeArguments;
    ConstructorDecl;
    Variants;
    LabelName;
    LabelDecl;
    LabelDecls;
    TypeParamsTail;
    TypeParams;
    TypedefLhs;
    TypedefRhs;
    Typedefs;
    Declaration;
  ]

(* String interpretation happens once, at the CLI/directive boundary. Parser
   control flow pattern-matches on t rather than repeatedly comparing names. *)
let of_name text =
  Option.value
    (List.find builtins ~f:(fun kind -> String.equal (name kind) text))
    ~default:(User text)

let equal lhs rhs = String.equal (name lhs) (name rhs)

let is_terminal = function
  | Identifier | FieldIdentifier | TypeVariable | Literal _ -> true
  | Term | Type | Pattern | Binding | LetBindings | SimpleMatching | TypeArguments | ConstructorDecl
  | Variants | LabelName | LabelDecl | LabelDecls | TypeParamsTail | TypeParams | TypedefLhs
  | TypedefRhs | Typedefs | Declaration | User _ ->
      false
