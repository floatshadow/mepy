open Core

type keyword = { name : string; lbp : int option; rbp : int option }
type atoms = No_atoms | Terms | Types
type kind = { name : SyntaxKind.t; rule : Tree.located ParseRule.t; atoms : atoms }

(* An explicit instance replaces the artifact's global registries. Parsing one
   file never reserves keywords in a later, unrelated file. Rules are immutable:
   extending a kind replaces its entry, so there are no stale lookup caches. *)
type t = { mutable keywords : keyword String.Map.t; mutable kinds : kind String.Map.t }

let create () = { keywords = String.Map.empty; kinds = String.Map.empty }
let keyword grammar name = Map.find grammar.keywords name
let kind grammar name = Map.find grammar.kinds (SyntaxKind.name name)
let is_reserved grammar name = Map.mem grammar.keywords name

let register_keyword grammar ?lbp ?rbp name =
  if String.is_empty name then Source.invalid "a keyword cannot be empty";
  grammar.keywords <- Map.set grammar.keywords ~key:name ~data:{ name; lbp; rbp }

let define grammar ?(atoms = No_atoms) name rule =
  grammar.kinds <- Map.set grammar.kinds ~key:(SyntaxKind.name name) ~data:{ name; rule; atoms }

(* Validate dispatch determinism, not an arbitrary CFG. Duplicate keyword
   prefixes must be factored explicitly instead of silently shadowing. The
   paper's core selects the first Ref; we allow distinct prioritized Refs so a
   runtime extension can begin with a syntax kind without mutating an existing
   GADT node. Each attempt must obey Parser.Absent's no-consumption invariant.
   Direct self references are checked after their tails have been combined. *)
let rec validate_rule : type a. a ParseRule.t -> unit =
 fun rule ->
  let keywords = ref String.Set.empty in
  let infixes = ref 0 and ends = ref 0 in
  List.iter rule.choices ~f:(function
    | ParseRule.End _ -> incr ends
    | Keyword (name, rest) ->
        if Set.mem !keywords name then Source.invalid [%string "duplicate keyword branch %{name}"];
        keywords := Set.add !keywords name;
        validate_rule rest
    | Ref { rest; _ } -> validate_rule rest
    | Infix { rest; _ } ->
        incr infixes;
        validate_rule rest);
  if !infixes > 1 then Source.invalid "more than one infix family at a rule decision";
  if !ends > 1 then Source.invalid "more than one end at a rule decision"

let top_keywords rule =
  List.fold rule.ParseRule.choices ~init:String.Set.empty ~f:(fun names -> function
    | ParseRule.Keyword (name, _) -> Set.add names name
    | End _ | Ref _ | Infix _ -> names)

let top_reference_count rule =
  List.count rule.ParseRule.choices ~f:(function ParseRule.Ref _ -> true | _ -> false)

let validate_kind kind =
  validate_rule kind.rule;
  (* Direct self references are interpreted together as one continuation
     decision. Validate that combined rule as well: checking each tail alone
     would miss an extension that repeats an existing ':' or infix route. *)
  Option.iter (ParseRule.after_ref kind.name kind.rule) ~f:(fun continuation ->
      validate_rule continuation;
      (* The artifact exposes only its first Ref choice. Different referenced
         kinds can still recognize the same first token (term and type both
         accept identifiers), so their names are not enough to prove
         disjointness. Keep at most one Ref in the combined continuation. *)
      if top_reference_count continuation > 1 then
        Source.invalid "overlapping continuation reference branches";
      let initial = ParseRule.without_self kind.name kind.rule in
      let shared_keywords = Set.inter (top_keywords initial) (top_keywords continuation) in
      Option.iter (Set.min_elt shared_keywords) ~f:(fun name ->
          Source.invalid [%string "keyword %{name} overlaps prefix and continuation rules"]))

let validate grammar = Map.iter grammar.kinds ~f:validate_kind

let extend grammar name choices =
  let old =
    match kind grammar name with
    | Some kind -> kind
    | None -> { name; atoms = No_atoms; rule = ParseRule.rule [] }
  in
  let rule = ParseRule.rule (old.rule.choices @ choices) in
  let extended = { old with rule } in
  validate_kind extended;
  define grammar ~atoms:old.atoms name rule
