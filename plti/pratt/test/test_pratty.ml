open Core
open Pratty

let check label expected actual =
  if not (String.equal expected actual) then
    failwith [%string "%{label}: expected %{expected}; got %{actual}"]

let parse ?(kind = SyntaxKind.Term) source =
  Parser.expression_exn ~kind (Language.make ()) source |> Tree.string_of_tree

let check_error ?(kind = SyntaxKind.Term) label source ~line ~column ~message =
  match Parser.expression_exn ~kind (Language.make ()) source with
  | _ -> failwith [%string "%{label}: expected an error"]
  | exception Source.Error diagnostic ->
      if
        diagnostic.span.start.line <> line
        || diagnostic.span.start.column <> column
        || not (String.is_substring diagnostic.message ~substring:message)
      then failwith [%string "%{label}: wrong diagnostic"]

let check_program_error label source ~message =
  match Parser.program_exn (Language.make ()) source with
  | _ -> failwith [%string "%{label}: expected an error"]
  | exception Source.Error diagnostic ->
      if not (String.is_substring diagnostic.message ~substring:message) then
        failwith [%string "%{label}: wrong diagnostic %{diagnostic.message}"]
  | exception Source.Invalid_grammar actual ->
      if not (String.is_substring actual ~substring:message) then
        failwith [%string "%{label}: wrong grammar error %{actual}"]

let test_binding_power () =
  check "precedence" "(+ a (* b c))" (parse "a + b * c");
  check "left associativity" "(+ (+ a b) c)" (parse "a + b + c");
  check "right associativity" "(:: a (:: b c))" (parse "a :: b :: c");
  check "application" "((f x) y)" (parse "f x y");
  check "decimal operator" "(+. 1.0 2.0)" (parse "1.0 +. 2.0");
  check "dot operator" "(.. a b)" (parse "a .. b");
  check "dot-led operator" "(.+ a (* b c))" (parse "a .+ b * c");
  check "dot-ended operator" "(* (^. a b) c)" (parse "a ^. b * c");
  check "forward pipe" "(|> (|> (+ a b) f) g)" (parse "a + b |> f |> g");
  check "reverse pipe" "(<| f (<| g (+ a b)))" (parse "f <| g <| a + b");
  check "derived stars" "(** (** a b) c)" (parse "a ** b ** c");
  let explicit = Option.value_exn (Operator.arithmetic "**") in
  let derived = Option.value_exn (Operator.derive "**") in
  assert (explicit.rbp < explicit.lbp);
  assert (derived.rbp = derived.lbp);
  check "left-associative assignment" "(<- (<- a b) c)" (parse "a <- b <- c");
  check "bang binds before selection" "(select (! a) b)" (parse "!a.b");
  check "negation binds after selection" "(- (select a b))" (parse "-a.b");
  check "bang after term is a prefix argument" "(a (! b))" (parse "a ! b");
  check_error "tilde is not infix" "a ~ b" ~line:1 ~column:3 ~message:"end of input"

let test_language_categories () =
  check "dangling else" "(if a (if b c d))" (parse "if a then if b then c else d");
  check "type arrows" "(-> 'a (-> 'b 'c))" (parse ~kind:SyntaxKind.Type "'a -> 'b -> 'c");
  check "type application" "(result (type-arguments 'a 'b))"
    (parse ~kind:SyntaxKind.Type "('a, 'b) result");
  check "pattern" "(:: (Cons x) xs)" (parse ~kind:SyntaxKind.Pattern "Cons x :: xs");
  (match Parser.expression_exn ~kind:SyntaxKind.Pattern (Language.make ()) "_" with
  | Tree.Wildcard _ -> ()
  | _ -> failwith "pattern wildcard should have its own ADT constructor");
  check_error ~kind:SyntaxKind.Pattern "pattern semicolon" "a ; b" ~line:1 ~column:3
    ~message:"end of input";
  check_error ~kind:SyntaxKind.Pattern "pattern equality" "a = b" ~line:1 ~column:3
    ~message:"end of input";
  check_error ~kind:SyntaxKind.Pattern "curly pattern" "{x}" ~line:1 ~column:1
    ~message:"expected pattern";
  check "boolean literal" "true" (parse "true");
  check_error ~kind:SyntaxKind.Type "boolean is not a type" "true" ~line:1 ~column:1
    ~message:"expected type"

let test_extension () =
  let source =
    {|#keyword "print" 10 10;;
#keyword "format" None None;;
#extend ["term",
  [keyword "print"; ["term", "x"]; keyword "format";
   ["string-literal", "f"]],
  [System.println (String.format f x)]];;
print answer format "value: %d";;|}
  in
  let trees = Parser.program_exn (Language.make ()) source in
  match trees with
  | [ tree ] ->
      check "extension"
        {|((select System println)
  (((select String format) "value: %d") answer))|}
        (Tree.string_of_tree tree)
  | _ -> failwith "extension directives should leave one program tree"

let test_left_recursive_extension () =
  let source =
    {|#keyword "where" 6 6;;
#extend ["term",
  [["term", "lhs"]; keyword "where"; ["term", "rhs"]],
  [Pair lhs rhs]];;
a where b where c;;|}
  in
  match Parser.program_exn (Language.make ()) source with
  | [ tree ] ->
      check "left-recursive extension" "((Pair ((Pair a) b)) c)" (Tree.string_of_tree tree)
  | _ -> failwith "left-recursive extension should leave one program tree"

let test_user_kind_extension () =
  let source =
    {|#keyword "unless" 10 0;;
#extend ["guard", [keyword "unless"; ["term", "body"]], [body]];;
#extend ["term", [["guard", "guard"]], [guard]];;
unless value;;|}
  in
  match Parser.program_exn (Language.make ()) source with
  | [ tree ] -> check "user syntax kind" "value" (Tree.string_of_tree tree)
  | _ -> failwith "user syntax kind should leave one program tree"

let test_literal_kind_extension () =
  let source =
    {|#keyword "given" 10 10;;
#extend ["term",
  [keyword "given"; ["boolean-literal", "b"]; ["decimal-literal", "n"]],
  [Pair b n]];;
given true 1.5;;|}
  in
  match Parser.program_exn (Language.make ()) source with
  | [ tree ] -> check "literal kinds in extension" "((Pair true) 1.5)" (Tree.string_of_tree tree)
  | _ -> failwith "literal-kind extension should leave one program tree"

let test_extension_guards () =
  check_program_error "empty route" {|#extend ["term", [], [x]];;|} ~message:"cannot be empty";
  check_program_error "duplicate capture"
    {|#keyword "p" 10 10;;
#extend ["term", [keyword "p"; ["term", "x"]; ["term", "x"]], [x]];;|}
    ~message:"duplicate capture";
  check_program_error "closed kind" {|#extend ["ident", [["term", "x"]], [x]];;|}
    ~message:"cannot be extended";
  check_program_error "overlapping continuation"
    {|#extend ["term",
  [["term", "lhs"]; keyword ":"; ["type", "rhs"]],
    [Pair lhs rhs]];;|}
    ~message:"duplicate keyword branch :";
  check_program_error "overlapping continuation reference"
    {|#extend ["term",
  [["term", "lhs"]; ["term", "rhs"]],
  [Pair lhs rhs]];;|}
    ~message:"overlapping continuation reference branches";
  check_program_error "overlapping continuation kinds"
    {|#extend ["term",
  [["term", "lhs"]; ["type", "rhs"]],
  [Pair lhs rhs]];;|}
    ~message:"overlapping continuation reference branches";
  check_program_error "prefix and continuation overlap"
    {|#keyword "ifx" 10 10;;
#extend ["term", [keyword "ifx"; ["term", "x"]], [x]];;
#extend ["term",
  [["term", "lhs"]; keyword "ifx"; ["term", "rhs"]],
  [Pair lhs rhs]];;|}
    ~message:"overlaps prefix and continuation";
  check_program_error "delimiter cannot start"
    {|#keyword "print" None 10;;
#extend ["term", [keyword "print"; ["term", "x"]], [x]];;
print value;;|}
    ~message:"expected term"

let test_source_spans () =
  let tree = Parser.expression_exn ~file:"lesson.pratty" (Language.make ()) "if a then b" in
  let span = Tree.tag tree in
  assert (String.equal span.file "lesson.pratty");
  assert (span.start.offset = 0);
  assert (span.finish.offset = 11);
  let unit = Parser.expression_exn (Language.make ()) "()" in
  let span = Tree.tag unit in
  assert (span.start.offset = 0 && span.finish.offset = 2)

let test_diagnostics () =
  check_error "missing operand" "a +\n)" ~line:2 ~column:1 ~message:"right operand";
  check_error "closing bracket" "(a" ~line:1 ~column:3 ~message:"closing )";
  check_error "if delimiter" "if a b" ~line:1 ~column:7 ~message:"then after if condition";
  check_error "invalid number" "1abc" ~line:1 ~column:1 ~message:"numeric suffix";
  check_error "unterminated comment" "(* never" ~line:1 ~column:1 ~message:"unterminated comment"

let test_generated_specification () =
  let grammar = Language.make () in
  let html = Document.string_of_document (Diagram.pp_html grammar) in
  assert (String.is_substring html ~substring:"<svg");
  assert (String.is_substring html ~substring:"Syntax diagram for term");
  assert (String.is_substring html ~substring:"prefix ! | - | -.");
  assert (String.is_substring html ~substring:"<code>.</code>");
  assert (String.is_substring html ~substring:"<td>cannot lead</td><td>inherit</td>");
  assert (String.is_substring html ~substring:"Operator character powers");
  assert (String.is_substring html ~substring:"<table>");
  let extension =
    {|#keyword "given" 10 10;;
#extend ["term",
  [keyword "given"; ["boolean-literal", "b"]; ["decimal-literal", "n"]],
  [Pair b n]];;|}
  in
  ignore (Parser.program_exn grammar extension : Tree.located list);
  let extended = Document.string_of_document (Diagram.pp_html grammar) in
  assert (String.is_substring extended ~substring:"b: boolean-literal");
  assert (String.is_substring extended ~substring:"n: decimal-literal")

let () =
  test_binding_power ();
  test_language_categories ();
  test_extension ();
  test_left_recursive_extension ();
  test_user_kind_extension ();
  test_literal_kind_extension ();
  test_extension_guards ();
  test_source_spans ();
  test_diagnostics ();
  test_generated_specification ()
