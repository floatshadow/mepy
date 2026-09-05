open Core
open Pratty

(** The parser library returns [PPrint.document] values so callers can decide where and how to
    render them. The command line program makes that decision at its boundary: successful results go
    to stdout and structured parser diagnostics go to stderr. *)
let output channel document = Document.output channel PPrint.(document ^^ hardline)

let run action () =
  try output Out_channel.stdout (action ()) with
  | Source.Error diagnostic ->
      output Out_channel.stderr (Source.pp_diagnostic diagnostic);
      Command.exit 1
  | Source.Invalid_grammar message ->
      output Out_channel.stderr (PPrint.string message);
      Command.exit 2

let parse_command =
  Command.basic ~summary:"Parse a source file as a sequence of declarations and terms"
    (let%map_open.Command file = anon ("FILE" %: string) in
     run (fun () ->
         let grammar = Language.make () in
         let source = In_channel.read_all file in
         PPrint.separate PPrint.hardline
           (List.map (Parser.program_exn ~file grammar source) ~f:Tree.pp_tree)))

let expression_command =
  Command.basic ~summary:"Parse one expression"
    (let%map_open.Command source = anon ("SOURCE" %: string) in
     run (fun () -> Tree.pp_tree (Parser.expression_exn (Language.make ()) source)))

let trace_command =
  Command.basic ~summary:"Parse one expression and explain each Pratt-parser decision"
    (let%map_open.Command source = anon ("SOURCE" %: string) in
     run (fun () ->
         let trace message = output Out_channel.stderr (PPrint.string message) in
         Tree.pp_tree (Parser.expression_exn ~trace (Language.make ()) source)))

let type_command =
  Command.basic ~summary:"Parse one type expression"
    (let%map_open.Command source = anon ("SOURCE" %: string) in
     run (fun () ->
         Tree.pp_tree (Parser.expression_exn ~kind:SyntaxKind.Type (Language.make ()) source)))

let pattern_command =
  Command.basic ~summary:"Parse one pattern"
    (let%map_open.Command source = anon ("SOURCE" %: string) in
     run (fun () ->
         Tree.pp_tree (Parser.expression_exn ~kind:SyntaxKind.Pattern (Language.make ()) source)))

let grammar_command =
  Command.basic ~summary:"Print the active grammar as readable BNF"
    (Command.Param.return (run (fun () -> Diagram.pp_grammar (Language.make ()))))

let diagram_command =
  Command.basic ~summary:"Write a self-contained HTML railroad diagram for the active grammar"
    ~readme:(fun () ->
      "When FILE is present, Pratty parses its top-level directives first.  The output then \
       includes syntax added by #keyword and #extend directives in that file.")
    (let%map_open.Command file = anon (maybe ("FILE" %: string)) in
     run (fun () ->
         let grammar = Language.make () in
         Option.iter file ~f:(fun file ->
             ignore
               (Parser.program_exn ~file grammar (In_channel.read_all file) : Tree.located list));
         Diagram.pp_html grammar))

let command =
  Command.group ~summary:"Explore a generalized Pratt parser for a Caml-like language"
    [
      ("parse", parse_command);
      ("expr", expression_command);
      ("trace", trace_command);
      ("type", type_command);
      ("pattern", pattern_command);
      ("grammar", grammar_command);
      ("diagram", diagram_command);
    ]

let () = Command_unix.run command
