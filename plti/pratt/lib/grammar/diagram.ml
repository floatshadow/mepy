open Core
open PPrint

(* A textual view is useful while bootstrapping; the railroad renderer will
   consume these same reified choices, including their binding-power guards. *)
let rec pp_rule : type a. a ParseRule.t -> document =
 fun rule -> separate (string " | ") (List.map rule.choices ~f:pp_choice)

and pp_choice : type a. a ParseRule.choice -> document = function
  | End _ -> string "epsilon"
  | Keyword (name, rest) -> Document.quoted name ^^ space ^^ pp_tail rest
  | Ref { kind; capture; bp; rest; _ } ->
      (match capture with
        | None -> angles (string (SyntaxKind.name kind))
        | Some name -> angles (string name ^^ string ": " ^^ string (SyntaxKind.name kind)))
      ^^ (match bp with
        | None -> empty
        | Some bp -> string "[bp<" ^^ string (Int.to_string bp) ^^ string "]")
      ^^ space ^^ pp_tail rest
  | Infix { name; rhs_kind; rest; _ } ->
      angles (string name)
      ^^ space
      ^^ angles (string (SyntaxKind.name rhs_kind))
      ^^ space ^^ pp_tail rest

and pp_tail : type a. a ParseRule.t -> document =
 fun rule -> match rule.choices with [ End _ ] -> empty | _ -> parens (pp_rule rule)

let pp_atom_rule kind =
  match kind.Grammar.atoms with
  | No_atoms -> []
  | Terms ->
      [
        angles (string "ident");
        angles (string "literal");
        angles (string "prefix !|-|-.") ^^ space ^^ angles (string (SyntaxKind.name kind.name));
      ]
      @ if SyntaxKind.equal kind.name Pattern then [ Document.quoted "_" ] else []
  | Types -> [ angles (string "ident") ]

let pp_kind_rule kind = separate (string " | ") (pp_atom_rule kind @ [ pp_rule kind.rule ])

let pp_grammar grammar =
  separate hardline
    (List.map (Map.to_alist grammar.Grammar.kinds) ~f:(fun (name, kind) ->
         group (angles (string name) ^^ string " ::= " ^^ nest 2 (pp_kind_rule kind))))

type step = { label : string; terminal : bool; guard : string option }

(* A path is one complete route through the finite Choice tree. References are
   boxes; we never expand the referenced kind, so recursive rules stay finite.
   Nested alternatives become parallel routes in the generated SVG. *)
let rec rule_paths : type a. a ParseRule.t -> step list list =
 fun rule ->
  List.concat_map rule.choices ~f:(function
    | ParseRule.End _ -> [ [] ]
    | Keyword (name, rest) -> prepend { label = name; terminal = true; guard = None } rest
    | Ref { kind; capture; bp; rest; _ } ->
        prepend
          {
            label =
              (match capture with
              | None -> SyntaxKind.name kind
              | Some name -> [%string "%{name}: %{SyntaxKind.name kind}"]);
            terminal = false;
            guard = Option.map bp ~f:(fun bp -> [%string "bp < %{bp#Int}"]);
          }
          rest
    | Infix { name; rhs_kind; rest; _ } ->
        let operator = { label = name; terminal = true; guard = None } in
        let rhs = { label = SyntaxKind.name rhs_kind; terminal = false; guard = None } in
        List.map (rule_paths rest) ~f:(fun tail -> operator :: rhs :: tail))

and prepend : type a. step -> a ParseRule.t -> step list list =
 fun head rest -> List.map (rule_paths rest) ~f:(fun tail -> head :: tail)

let atom_paths kind =
  let nonterminal label = { label; terminal = false; guard = None } in
  let terminal label = { label; terminal = true; guard = None } in
  match kind.Grammar.atoms with
  | No_atoms -> []
  | Types -> [ [ nonterminal "ident" ] ]
  | Terms ->
      [
        [ nonterminal "ident" ];
        [ nonterminal "literal" ];
        [
          terminal "prefix ! | - | -.";
          {
            label = SyntaxKind.name kind.name;
            terminal = false;
            guard = Some "operator-specific operand bp";
          };
        ];
      ]
      @ if SyntaxKind.equal kind.name Pattern then [ [ terminal "_" ] ] else []

let escape_xml text =
  List.fold
    [ ("&", "&amp;"); ("<", "&lt;"); (">", "&gt;"); ("\"", "&quot;") ]
    ~init:text
    ~f:(fun text (pattern, with_) -> String.substr_replace_all text ~pattern ~with_)

let pp_svg_line x1 y1 x2 y2 =
  string
    [%string
      {|<path d="M %{x1#Int} %{y1#Int} H %{x2#Int}" fill="none" stroke="#566" stroke-width="2"/>|}]

let step_width step = Int.max 86 ((String.length step.label * 8) + 24)

let pp_step x y step =
  let width = step_width step in
  let top = y - 16 in
  let shape =
    if step.terminal then
      string
        [%string
          {|<rect class="terminal" x="%{x#Int}" y="%{top#Int}" width="%{width#Int}" height="32" rx="14" fill="#e5f4e8" stroke="#397249" stroke-width="2"/>|}]
    else
      string
        [%string
          {|<rect class="nonterminal" x="%{x#Int}" y="%{top#Int}" width="%{width#Int}" height="32" fill="#e7effa" stroke="#315b86" stroke-width="2"/>|}]
  in
  let label = escape_xml step.label in
  let text =
    string
      [%string
        {|<text x="%{x + (width / 2)#Int}" y="%{y + 5#Int}" text-anchor="middle" fill="#182026">%{label}</text>|}]
  in
  let guard =
    match step.guard with
    | None -> empty
    | Some guard ->
        string
          [%string
            {|<text class="guard" x="%{x + (width / 2)#Int}" y="%{top - 5#Int}" text-anchor="middle" fill="#7b4b19">%{escape_xml guard}</text>|}]
  in
  (shape ^^ hardline ^^ text ^^ hardline ^^ guard, x + width)

let path_width path = 60 + List.sum (module Int) path ~f:(fun step -> step_width step + 34)

let pp_path width center_y row path =
  let y = 31 + (row * 58) in
  let rec steps x = function
    | [] ->
        pp_svg_line x y (width - 32) y
        ^^ hardline
        ^^ string
             [%string
               {|<path d="M %{width - 32#Int} %{y#Int} C %{width - 23#Int} %{y#Int}, %{width - 23#Int} %{center_y#Int}, %{width - 16#Int} %{center_y#Int}" fill="none" stroke="#566" stroke-width="2"/>|}]
    | step :: rest ->
        let box_x = x + 17 in
        let box, next = pp_step box_x y step in
        pp_svg_line x y box_x y ^^ hardline ^^ box ^^ hardline ^^ steps next rest
  in
  string
    [%string
      {|<path d="M 15 %{center_y#Int} C 24 %{center_y#Int}, 24 %{y#Int}, 32 %{y#Int}" fill="none" stroke="#566" stroke-width="2"/>|}]
  ^^ hardline ^^ steps 32 path

let pp_diagram name kind =
  let routes = atom_paths kind @ rule_paths kind.Grammar.rule in
  let width = List.fold routes ~init:180 ~f:(fun width path -> Int.max width (path_width path)) in
  let height = 24 + (List.length routes * 58) in
  let center_y = 31 + ((List.length routes - 1) * 58 / 2) in
  string [%string {|<section><h2>&lt;%{escape_xml name}&gt;</h2>|}]
  ^^ hardline
  ^^ string
       [%string
         {|<svg role="img" aria-label="Syntax diagram for %{escape_xml name}" viewBox="0 0 %{width#Int} %{height#Int}">|}]
  ^^ hardline
  ^^ string [%string {|<circle class="start" cx="10" cy="%{center_y#Int}" r="5" fill="#566"/>|}]
  ^^ hardline
  ^^ separate hardline (List.mapi routes ~f:(pp_path width center_y))
  ^^ hardline
  ^^ string
       [%string
         {|<circle class="end" cx="%{width - 10#Int}" cy="%{center_y#Int}" r="6" fill="white" stroke="#566" stroke-width="3"/>|}]
  ^^ hardline ^^ string "</svg></section>"

let pp_left_power = function
  | None -> string "cannot lead"
  | Some power -> string (Int.to_string power)

let pp_right_power = function
  | None -> string "inherit"
  | Some power -> string (Int.to_string power)

let pp_precedence grammar =
  let rows =
    Map.to_alist grammar.Grammar.keywords
    |> List.sort ~compare:(fun (_, lhs) (_, rhs) ->
        [%compare: int option * int option * string] (lhs.lbp, lhs.rbp, lhs.name)
          (rhs.lbp, rhs.rbp, rhs.name))
  in
  string "<h3>Keyword spellings</h3>"
  ^^ hardline
  ^^ string "<table><thead><tr><th>keyword</th><th>left</th><th>right</th></tr></thead><tbody>"
  ^^ hardline
  ^^ separate hardline
       (List.map rows ~f:(fun (_, keyword) ->
            string "<tr><td><code>"
            ^^ string (escape_xml keyword.name)
            ^^ string "</code></td><td>" ^^ pp_left_power keyword.lbp ^^ string "</td><td>"
            ^^ pp_right_power keyword.rbp ^^ string "</td></tr>"))
  ^^ hardline ^^ string "</tbody></table>" ^^ hardline
  ^^ string "<h3>Operator character powers</h3>"
  ^^ hardline
  ^^ string
       "<p>Normally the first and last characters select left and right power. A final \
        <code>:</code>, <code>,</code>, or <code>/</code> subtracts one from the right power. Caml \
        decimal operators <code>+.</code>, <code>-.</code>, <code>*.</code>, and <code>/.</code> \
        instead use their first character for both powers.</p>"
  ^^ hardline
  ^^ string "<table><thead><tr><th>characters</th><th>power</th></tr></thead><tbody>"
  ^^ hardline
  ^^ separate hardline
       (List.filter_mapi Operator.groups ~f:(fun index group ->
            if String.is_empty group then None
            else
              Some
                (string "<tr><td><code>"
                ^^ string (escape_xml group)
                ^^ string "</code></td><td>"
                ^^ string (Int.to_string (Operator.base + index))
                ^^ string "</td></tr>")))
  ^^ hardline
  ^^ string [%string "<tr><td>prefix</td><td>%{Operator.prefix_power#Int}</td></tr>"]
  ^^ hardline
  ^^ string [%string "<tr><td>application</td><td>%{Operator.application_power#Int}</td></tr>"]
  ^^ hardline
  ^^ string [%string "<tr><td>bang prefix</td><td>%{Operator.bang_prefix_power#Int}</td></tr>"]
  ^^ hardline ^^ string "</tbody></table>"

let pp_html grammar =
  let diagrams =
    List.map (Map.to_alist grammar.Grammar.kinds) ~f:(fun (name, kind) -> pp_diagram name kind)
  in
  let style =
    {|<style>
body{font:16px system-ui,sans-serif;max-width:1100px;margin:2rem auto;padding:0 1rem;color:#182026}
h1,h2{font-weight:600}section{margin:2.5rem 0}svg{width:100%;height:auto;background:#fbfaf6;border:1px solid #ddd;border-radius:8px}
svg text{font:14px ui-monospace,monospace}.guard{font-size:11px}
table{border-collapse:collapse}tr{break-inside:avoid}th,td{border:1px solid #bbb;padding:.35rem .7rem;text-align:left}th{background:#eee}
</style>|}
  in
  string
    "<!doctype html><html lang=\"en\"><meta charset=\"utf-8\"><title>Pratty syntax diagrams</title>"
  ^^ hardline ^^ string style ^^ hardline
  ^^ string "<body><h1>Pratty syntax diagrams</h1>"
  ^^ hardline
  ^^ string
       "<p>Generated from the typed <code>ParseRule</code> values and atom policies interpreted by \
        the parser. Capture labels are shown as <code>name: kind</code>.</p>"
  ^^ hardline ^^ string "<h2>Precedence</h2>" ^^ hardline ^^ pp_precedence grammar ^^ hardline
  ^^ separate hardline diagrams ^^ hardline ^^ string "</body></html>"
