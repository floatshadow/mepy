open Core
open ParseRule

(* This file is the executable syntax specification. Helpers only assemble
   Choice trees; none of them reads a token. Consequently the diagram renderer
   and the parser see exactly the same alternatives and references. *)
let unknown = Source.point "<grammar>" Source.initial
let span children = Tree.span_of_children unknown children
let items children = Tree.Items (children, span children)
let children = function
  | Tree.Items (children, _) -> children
  | _ -> Source.invalid "a list-valued grammar fragment did not return Items"

let get ?bp kind f = reference ?bp kind (finish ()) (fun tree () -> f tree)
let kw name choices = Keyword (name, rule choices)
let keep kind rest = reference kind rest (fun tree () -> tree)
let one kind = capture kind

let optional_keyword name rest = rule (Keyword (name, rest) :: rest.choices)

let separated ~kind ~separator ~name =
  rule
    [
      reference kind
        (rule [ End []; kw separator [ get name children ] ])
        (fun head tail -> items (head :: tail));
    ]

let bracket opening closing kind wrap =
  kw opening
    [
      kw closing [ End (wrap []) ];
      reference ~label:[%string "closing %{closing}"] kind
        (rule [ kw closing [ End () ] ])
        (fun tree () -> wrap [ tree ]);
    ]

let infix_keyword name rhs_kind combine = kw name [ get rhs_kind (fun rhs lhs -> combine lhs rhs) ]

let tuple lhs rhs =
  let tail = match rhs with Tree.Tuple (trees, _) -> trees | _ -> [ rhs ] in
  Tree.Tuple (lhs :: tail, span [ lhs; rhs ])

let sequence lhs rhs =
  let tail = match rhs with Tree.Sequence (trees, _) -> trees | _ -> [ rhs ] in
  Tree.Sequence (lhs :: tail, span [ lhs; rhs ])

let product lhs rhs =
  let tail = match lhs with Tree.Product (trees, _) -> trees | _ -> [ lhs ] in
  Tree.Product (tail @ [ rhs ], span [ lhs; rhs ])

let wrap_bracket kind = function
  | [ tree ] when Poly.equal kind Token.Round -> tree
  | [] -> Tree.Bracketed (kind, None, unknown)
  | [ tree ] -> Tree.Bracketed (kind, Some tree, Tree.tag tree)
  | _ ->
      (* bracket parses exactly one optional inner expression. *)
      assert false

let make () =
  let grammar = Grammar.create () in
  let keyword ?lbp ?rbp name = Grammar.register_keyword grammar ?lbp ?rbp name in
  (* Keyword levels occupy the space below character operators (§3.3). A
     delimiter has no left power; rbp=None inherits its caller's threshold. *)
  List.iter
    [
      "then";
      "else";
      "in";
      "with";
      "do";
      "done";
      "to";
      "downto";
      "and";
      "rec";
      "of";
      "mutable";
      ";;";
      "#";
    ] ~f:(fun name -> keyword name);
  List.iter [ "let"; "if"; "match"; "function"; "try"; "while"; "for"; "fun"; "type"; "exception" ]
    ~f:(fun name -> keyword ~lbp:10 ~rbp:0 name);
  List.iter
    [
      (";", 1, 0);
      (",", 2, 1);
      ("|", 4, 4);
      ("as", 4, 4);
      ("->", 5, 4);
      (":", 4, 0);
      ("<-", 9, 9);
      ("=", 25, 25);
      ("==", 25, 25);
      ("*", 31, 31);
      (".", Operator.selection_power, Operator.selection_power);
    ]
    ~f:(fun (name, lbp, rbp) -> keyword ~lbp ~rbp name);
  List.iter [ "mod"; "lsl"; "lsr"; "asr" ] ~f:(keyword ~lbp:31 ~rbp:31);
  List.iter [ "land"; "lor"; "lxor" ] ~f:(keyword ~lbp:24 ~rbp:24);
  List.iter [ Token.Round; Square; Curly; Array; BeginEnd ] ~f:(fun bracket ->
      let opening, closing = Token.brackets bracket in
      keyword ~lbp:Operator.bracket_power ~rbp:0 opening;
      keyword closing);
  let define ?atoms name choices = Grammar.define grammar ?atoms name (rule choices) in
  let named name rule = Grammar.define grammar name rule in

  define SyntaxKind.LetBindings
    [
      reference SyntaxKind.Binding
        (rule
           [
             kw "="
               [
                 reference SyntaxKind.Term
                   (rule [ End []; kw "and" [ get SyntaxKind.LetBindings children ] ])
                   (fun rhs rest -> (rhs, rest));
               ];
           ])
        (fun lhs (rhs, rest) -> items (Tree.Binding (lhs, rhs, span [ lhs; rhs ]) :: rest));
    ];
  let let_tail recursive =
    rule
      [
        reference SyntaxKind.LetBindings
          (rule [ End None; kw "in" [ get SyntaxKind.Term Option.some ] ])
          (fun bindings body ->
            Tree.Let (recursive, children bindings, body, span (bindings :: Option.to_list body)));
      ]
  in
  let let_choice =
    Keyword ("let", rule (Keyword ("rec", let_tail true) :: (let_tail false).choices))
  in

  define SyntaxKind.SimpleMatching
    [
      reference ~label:"case arrow ->" SyntaxKind.Pattern
        (rule
           [
             kw "->"
               [
                 reference SyntaxKind.Term
                   (rule [ End []; kw "|" [ get SyntaxKind.SimpleMatching children ] ])
                   (fun body rest -> (body, rest));
               ];
           ])
        (fun pattern (body, rest) ->
          items (Tree.Case (pattern, body, span [ pattern; body ]) :: rest));
    ];
  let matching = optional_keyword "|" (one SyntaxKind.SimpleMatching) in
  let match_choice name build =
    kw name
      [
        reference ~label:[%string "with after %{name} subject"] SyntaxKind.Term
          (rule [ Keyword ("with", matching) ])
          (fun subject arms -> build subject (children arms) (span [ subject; arms ]));
      ]
  in
  let if_choice =
    kw "if"
      [
        reference ~label:"then after if condition" SyntaxKind.Term
          (rule
             [
               kw "then"
                 [
                   reference ~label:"if consequent" SyntaxKind.Term
                     (rule [ End None; kw "else" [ get SyntaxKind.Term Option.some ] ])
                     (fun consequent alternative -> (consequent, alternative));
                 ];
             ])
          (fun condition (consequent, alternative) ->
            Tree.If
              ( condition,
                consequent,
                alternative,
                span ([ condition; consequent ] @ Option.to_list alternative) ));
      ]
  in
  let while_choice =
    kw "while"
      [
        reference ~label:"do after while condition" SyntaxKind.Term
          (rule [ kw "do" [ keep SyntaxKind.Term (rule [ kw "done" [ End () ] ]) ] ])
          (fun condition body -> Tree.While (condition, body, span [ condition; body ]));
      ]
  in
  let for_tail direction =
    rule
      [
        reference SyntaxKind.Term
          (rule [ kw "do" [ keep SyntaxKind.Term (rule [ kw "done" [ End () ] ]) ] ])
          (fun bound body -> (direction, bound, body));
      ]
  in
  let for_choice =
    kw "for"
      [
        reference SyntaxKind.Binding
          (rule
             [
               kw "="
                 [
                   reference SyntaxKind.Term
                     (rule
                        [ Keyword ("to", for_tail Tree.Up); Keyword ("downto", for_tail Tree.Down) ])
                     (fun start tail -> (start, tail));
                 ];
             ])
          (fun variable (start, (direction, bound, body)) ->
            Tree.For (direction, variable, start, bound, body, span [ variable; start; bound; body ]));
      ]
  in
  let term_brackets =
    [
      bracket "(" ")" SyntaxKind.Term (wrap_bracket Token.Round);
      bracket "[" "]" SyntaxKind.Term (wrap_bracket Token.Square);
      bracket "[|" "|]" SyntaxKind.Term (wrap_bracket Token.Array);
      bracket "{" "}" SyntaxKind.Term (wrap_bracket Token.Curly);
      bracket "begin" "end" SyntaxKind.Term (wrap_bracket Token.BeginEnd);
    ]
  in
  let term_continuations =
    [
      infix_keyword "," SyntaxKind.Term tuple;
      infix_keyword ";" SyntaxKind.Term sequence;
      infix_keyword "<-" SyntaxKind.Term (fun lhs rhs ->
          Tree.Assignment (lhs, rhs, span [ lhs; rhs ]));
      infix_keyword "=" SyntaxKind.Term (Tree.operator "=");
      infix_keyword "==" SyntaxKind.Term (Tree.operator "==");
      infix_keyword "*" SyntaxKind.Term (Tree.operator "*");
      infix_keyword ":" SyntaxKind.Type (fun lhs rhs ->
          Tree.Ascription (lhs, rhs, span [ lhs; rhs ]));
      kw "."
        [
          kw "("
            [
              reference SyntaxKind.Term
                (rule [ kw ")" [ End () ] ])
                (fun index () lhs -> Tree.Index (lhs, index, span [ lhs; index ]));
            ];
          get SyntaxKind.FieldIdentifier (fun field lhs ->
              Tree.Select (lhs, field, span [ lhs; field ]));
        ];
      Infix
        {
          name = "first/last character operator";
          operator = Operator.derive;
          rhs_kind = SyntaxKind.Term;
          rest = finish ();
          process = (fun name rhs () lhs -> Tree.operator name lhs rhs);
        };
      get ~bp:Operator.application_power SyntaxKind.Term (fun arg callee ->
          Tree.apply callee [ arg ] (Source.cover (Tree.tag callee) (Tree.tag arg)));
    ]
    @ List.map [ "mod"; "land"; "lor"; "lxor"; "lsl"; "lsr"; "asr" ] ~f:(fun name ->
        infix_keyword name SyntaxKind.Term (Tree.operator name))
  in
  let term_choices =
    [
      let_choice;
      if_choice;
      while_choice;
      for_choice;
      kw "fun"
        [
          reference SyntaxKind.Pattern
            (rule [ kw "->" [ get SyntaxKind.Term Fn.id ] ])
            (fun params body -> Tree.Lambda (params, body, span [ params; body ]));
        ];
      match_choice "match" (fun subject arms tag -> Tree.Match (Some subject, arms, tag));
      match_choice "try" (fun subject arms tag -> Tree.Try (subject, arms, tag));
      Keyword
        ("function", map matching ~f:(fun arms -> Tree.Match (None, children arms, Tree.tag arms)));
    ]
    @ term_brackets
    @ [ reference SyntaxKind.Term (rule term_continuations) (fun lhs extend -> extend lhs) ]
  in
  define ~atoms:Grammar.Terms SyntaxKind.Term term_choices;

  (* Patterns reuse the same atom/continuation engine with the continuations in
     the artifact's Caml fragment: alternatives, tuples, aliases, list cons and
     constructor application. Case arrows remain delimiters. *)
  define ~atoms:Grammar.Terms SyntaxKind.Pattern
    [
      bracket "(" ")" SyntaxKind.Pattern (wrap_bracket Token.Round);
      bracket "[" "]" SyntaxKind.Pattern (wrap_bracket Token.Square);
      reference SyntaxKind.Pattern
        (rule
           [
             infix_keyword "," SyntaxKind.Pattern tuple;
             infix_keyword "|" SyntaxKind.Pattern (fun lhs rhs ->
                 Tree.Alternative (lhs, rhs, span [ lhs; rhs ]));
             infix_keyword "as" SyntaxKind.Identifier (fun lhs rhs ->
                 Tree.Alias (lhs, rhs, span [ lhs; rhs ]));
             Infix
               {
                 name = "list cons";
                 operator =
                   (fun name -> if String.equal name "::" then Operator.derive name else None);
                 rhs_kind = SyntaxKind.Pattern;
                 rest = finish ();
                 process = (fun name rhs () lhs -> Tree.operator name lhs rhs);
               };
             get ~bp:Operator.application_power SyntaxKind.Pattern (fun arg callee ->
                 Tree.apply callee [ arg ] (Source.cover (Tree.tag callee) (Tree.tag arg)));
           ])
        (fun lhs extend -> extend lhs);
    ];

  define SyntaxKind.TypeArguments
    [
      reference SyntaxKind.Type
        (rule [ End []; kw "," [ get SyntaxKind.TypeArguments children ] ])
        (fun head tail -> items (head :: tail));
    ];
  define ~atoms:Grammar.Types SyntaxKind.Type
    [
      kw "("
        [
          reference SyntaxKind.TypeArguments
            (rule [ kw ")" [ End () ] ])
            (fun args () ->
              match children args with
              | [ tree ] -> tree
              | args -> Tree.TypeArguments (args, span args));
        ];
      reference SyntaxKind.Type
        (rule
           [
             infix_keyword "->" SyntaxKind.Type (Tree.operator "->");
             infix_keyword "*" SyntaxKind.Type product;
             get ~bp:Operator.application_power SyntaxKind.Identifier (fun constructor argument ->
                 Tree.apply constructor [ argument ]
                   (Source.cover (Tree.tag argument) (Tree.tag constructor)));
           ])
        (fun lhs extend -> extend lhs);
    ];
  define SyntaxKind.ConstructorDecl
    [
      reference SyntaxKind.Identifier
        (rule [ End None; kw "of" [ get SyntaxKind.Type Option.some ] ])
        (fun name payload ->
          Tree.Constructor (name, payload, span (name :: Option.to_list payload)));
    ];
  named SyntaxKind.Variants
    (optional_keyword "|"
       (separated ~kind:SyntaxKind.ConstructorDecl ~separator:"|" ~name:SyntaxKind.Variants));
  define SyntaxKind.LabelName
    [
      get SyntaxKind.Identifier Fn.id;
      kw "mutable" [ get SyntaxKind.Identifier (fun name -> Tree.Mutable (name, Tree.tag name)) ];
    ];
  define SyntaxKind.LabelDecl
    [
      reference SyntaxKind.LabelName
        (rule [ kw ":" [ get SyntaxKind.Type Fn.id ] ])
        (fun label typ -> Tree.Ascription (label, typ, span [ label; typ ]));
    ];
  named SyntaxKind.LabelDecls
    (separated ~kind:SyntaxKind.LabelDecl ~separator:";" ~name:SyntaxKind.LabelDecls);
  define SyntaxKind.TypeParamsTail
    [
      End (items []);
      kw ","
        [
          reference SyntaxKind.TypeVariable (one SyntaxKind.TypeParamsTail) (fun first rest ->
              items (first :: children rest));
        ];
    ];
  define SyntaxKind.TypeParams
    [
      End (items []);
      get SyntaxKind.TypeVariable (fun tree -> items [ tree ]);
      kw "("
        [
          reference SyntaxKind.TypeVariable
            (rule
               [
                 reference SyntaxKind.TypeParamsTail
                   (rule [ kw ")" [ End () ] ])
                   (fun rest () -> rest);
               ])
            (fun first rest -> items (first :: children rest));
        ];
    ];
  define SyntaxKind.TypedefLhs
    [
      reference SyntaxKind.TypeParams (one SyntaxKind.Identifier) (fun params name ->
          if List.is_empty (children params) then name
          else Tree.TypeHead (name, children params, span [ params; name ]));
    ];
  define SyntaxKind.TypedefRhs
    [
      kw "==" [ get SyntaxKind.Type (fun typ -> Tree.TypeAlias (typ, Tree.tag typ)) ];
      kw "="
        [
          get SyntaxKind.Variants Fn.id;
          kw "{"
            [
              reference SyntaxKind.LabelDecls
                (rule [ kw "}" [ End () ] ])
                (fun labels () -> Tree.RecordType (children labels, Tree.tag labels));
            ];
        ];
    ];
  define SyntaxKind.Typedefs
    [
      reference SyntaxKind.TypedefLhs
        (rule
           [
             reference SyntaxKind.TypedefRhs
               (rule [ End []; kw "and" [ get SyntaxKind.Typedefs children ] ])
               (fun body rest -> (body, rest));
           ])
        (fun head (body, rest) ->
          items (Tree.TypeBinding (head, body, span [ head; body ]) :: rest));
    ];
  define SyntaxKind.Declaration
    [
      let_choice;
      kw "type"
        [
          get SyntaxKind.Typedefs (fun defs ->
              Tree.Define (Tree.TypeDefinition, children defs, Tree.tag defs));
        ];
      kw "exception"
        [
          get SyntaxKind.Variants (fun defs ->
              Tree.Define (Tree.ExceptionDefinition, children defs, Tree.tag defs));
        ];
      kw "#"
        [
          reference SyntaxKind.Identifier (one SyntaxKind.Term) (fun name body ->
              Tree.Directive (name, body, span [ name; body ]));
        ];
    ];
  Grammar.validate grammar;
  grammar
