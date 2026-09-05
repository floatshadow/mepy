# Pratty: generalized Pratt parsing in OCaml

This repository is a teaching implementation of Cheng and Parreaux's
*A Simple Recipe for Writing Decent Recursive Descent Parsers* (ECOOP 2026,
article 30). The code implements its two stages:

1. ordinary Pratt parsing with independent left and right binding powers; and
2. the generalized parser, where typed `Rule`/`Choice` values describe terms,
   patterns, types, declarations, and runtime syntax extensions.

The port is written as idiomatic OCaml rather than transliterated MLscript.
MLscript `data class` declarations resemble Scala case classes; their direct
OCaml counterpart is usually a variant. The rule representation needs a GADT
because each `Ref` choice hides a different tail-result type.

## Build and run

```sh
make check
make examples

dune exec pratty expr 'a + b * c'
dune exec pratty type "'a -> 'b -> 'c"
dune exec pratty pattern 'Cons x :: xs'
dune exec pratty parse example/extension.pratty
dune exec pratty trace 'a + b * c'

# Generate HTML railroad diagrams and a precedence table.
make diagram
```

The first command prints `(+ a (* b c))`. The tree is deliberately printed as
an S-expression: grouping is visible without needing an evaluator.

## Reading order

The implementation is split by the ideas it teaches:

- `lib/syntax/`: positions, tokens, syntax-kind and tree ADTs, and printers;
- `lib/parsing/operator.ml`: Section 2's binding-power policy;
- `lib/grammar/parseRule.ml`: Section 3's typed `Rule` and `Choice` language;
- `lib/parsing/parser.ml`: the small interpreter for those rules;
- `lib/grammar/language.ml`: the executable Caml-style syntax specification;
- `lib/grammar/extension.ml`: `#keyword` and `#extend`;
- `lib/grammar/diagram.ml`: BNF and standalone HTML railroad diagrams.

## Examples

- `example/arithmetic.pratty` mirrors the paper's precedence examples.
- `example/caml.pratty` exercises bindings, matching, types, and declarations.
- `example/extension.pratty` defines and uses syntax while parsing the file.

This parser covers the language constructs used to teach the paper's method. It
does not claim byte-for-byte compatibility with the full historical Caml Light
grammar. The exact supported language is inspectable with `pratty grammar` or
the generated diagrams; both are derived from the rules the parser executes.
