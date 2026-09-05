open Core

type t = { name : string; lbp : int; rbp : int; unary : bool }

(* §2.3: the first and last characters independently determine binding power.
   Start above the keywords so arithmetic binds inside keyword-led phrases.
   The complete groups after the clipped PDF line come from Keywords.mls.

   The two empty groups are real precedence slots: prefix and application sit
   between [~] and [.]. Keeping them in this table puts dot-led and dot-ended
   operators at the paper's highest character power. Unlike the artifact, [@]
   remains left associative here, following the paper's rightAssocChars =
   ":,/". See docs/audit.md. *)
let groups = [ ","; "@"; ":"; "|"; "&"; "="; "/\\"; "^"; "!"; "<>"; "+-"; "*%"; "~"; ""; ""; "." ]

let base = 20
let prefix_power = base + List.length groups - 3
let application_power = prefix_power + 1
let selection_power = application_power + 1
let bracket_power = selection_power + 1
let bang_prefix_power = selection_power + 1

let character_powers =
  List.concat_mapi groups ~f:(fun index chars ->
      List.map (String.to_list chars) ~f:(fun ch -> (ch, base + index)))
  |> Char.Map.of_alist_exn

let is_operator_char ch = Map.mem character_powers ch

(* The artifact gives [!] a deliberately stronger prefix power than field
   selection. Ordinary negation uses the shared prefix slot below application.
   Returning an option also prevents arbitrary infix symbols from being
   accepted accidentally at the beginning of a phrase. *)
let prefix_binding_power = function
  | "!" -> Some bang_prefix_power
  | "-" | "-." -> Some prefix_power
  | _ -> None

let is_unary name = Option.is_some (prefix_binding_power name)

let derive name =
  if String.is_empty name || not (String.for_all name ~f:is_operator_char) then None
  else if List.mem [ "!"; "~" ] name ~equal:String.equal then
    (* In the Caml artifact these single-character spellings are reserved for
       prefix syntax; the character table still determines their relative
       power when they occur inside a longer operator. *)
    None
  else if List.mem [ "+."; "-."; "*."; "/." ] name ~equal:String.equal then
    (* A literal first/last lookup would give these an unusually strong right
       power because they end in [.]. The archived implementation instead
       assigns both sides from the leading arithmetic character. *)
    Option.map
      (Map.find character_powers name.[0])
      ~f:(fun power -> { name; lbp = power; rbp = power; unary = String.equal name "-." })
  else
    let first = name.[0] in
    let last = name.[String.length name - 1] in
    match (Map.find character_powers first, Map.find character_powers last) with
    | Some lbp, Some right ->
        let rbp = if String.contains ":,/" last then right - 1 else right in
        Some { name; lbp; rbp; unary = is_unary name }
    | _ -> None

(* The exact §2.2 table remains available for comparison: ** is explicitly
   right associative there, but is left associative under the §2.3 heuristic. *)
let arithmetic name =
  let make lbp rbp unary = Some { name; lbp; rbp; unary } in
  match name with
  | "+" | "-" -> make 3 4 true
  | "*" | "/" -> make 5 6 false
  | "**" -> make 8 7 false
  | _ -> None
