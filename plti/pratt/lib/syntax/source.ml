open Core
open PPrint

(* Offsets and columns count bytes; lines and columns are one-based. The end
   position is exclusive, so even an EOF diagnostic has a well-defined span. *)
type position = { offset : int; line : int; column : int }
type span = { file : string; start : position; finish : position }
type diagnostic = { span : span; message : string }

exception Error of diagnostic
exception Invalid_grammar of string

let initial = { offset = 0; line = 1; column = 1 }
let point file position = { file; start = position; finish = position }

let advance position ch =
  if Char.equal ch '\n' then { offset = position.offset + 1; line = position.line + 1; column = 1 }
  else { position with offset = position.offset + 1; column = position.column + 1 }

let cover first last = { first with finish = last.finish }
let error span message = raise (Error { span; message })
let invalid message = raise (Invalid_grammar message)

let pp_span span =
  string span.file ^^ colon
  ^^ string (Int.to_string span.start.line)
  ^^ colon
  ^^ string (Int.to_string span.start.column)

let pp_diagnostic { span; message } =
  group (pp_span span ^^ string ": " ^^ flow (break 1) (words message))

let () =
  Stdlib.Printexc.register_printer (function
    | Error diagnostic -> Some (Document.string_of_document (pp_diagnostic diagnostic))
    | Invalid_grammar message -> Some ("invalid grammar: " ^ message)
    | _ -> None)
