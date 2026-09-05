open Core
open PPrint

(** The paper's lexer prose calls [Decimal] a floating-point literal. The archived [Token.mls] names
    the constructor [Decimal] and also recognizes Boolean literals; using those names here keeps
    runtime kinds such as [decimal-literal] and [boolean-literal] compatible with [#extend]. *)
type literal_kind = Integer | Decimal | Character | String | Boolean

type bracket_kind = Round | Square | Curly | Array | BeginEnd

(* Keywords are deliberately absent: the parser consults its current registry
   at use time, so a directive can reserve an already-lexed identifier. *)
type kind =
  | Literal of literal_kind * string
  | Identifier of string
  | Symbol of string
  | Open of bracket_kind
  | Close of bracket_kind

type t = { kind : kind; span : Source.span }

let brackets = function
  | Round -> ("(", ")")
  | Square -> ("[", "]")
  | Curly -> ("{", "}")
  | Array -> ("[|", "|]")
  | BeginEnd -> ("begin", "end")

let spelling = function
  | Identifier name | Symbol name -> Some name
  | Open bracket -> Some (fst (brackets bracket))
  | Close bracket -> Some (snd (brackets bracket))
  | Literal _ -> None

let pp_kind = function
  | Literal (String, text) -> Document.quoted text
  | Literal (Character, text) -> squotes (string (String.escaped text))
  | Literal ((Integer | Decimal | Boolean), text) -> string text
  | Identifier name | Symbol name -> string name
  | Open bracket -> string (fst (brackets bracket))
  | Close bracket -> string (snd (brackets bracket))

let pp_token token = pp_kind token.kind
