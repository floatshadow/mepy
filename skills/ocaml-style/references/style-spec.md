# OCaml Style Report

This file records *conventions and the reasoning behind them*, illustrated with small code shapes.

---

## Strong conventions

These are the kind of conventions such a project applies consistently; treat a
confirmed one as house style.

### Formatting / ocamlformat
- Format with the formatter (`dune fmt`); do format only when the code is ready for commit, and don't make formatting-only edits to code you aren't otherwise touching.

### Naming
- Modules `CamelCase`; types, values, and record fields `snake_case`
  (`level_old`, `values_count`, `max_degree`).
- Variant constructors are `CamelCase` and, when a type has several related
  families, frequently take a **one-letter category prefix** so the families read
  at a glance — for example pattern nodes `P…` (`PVar`, `PTup`, `PCtorApp`), type
  nodes `T…` (`TArrow`, `TApp`, `TVar`), binding nodes `B…` (`BSeq`, `BOne`,
  `BRec`). Some core families (often expressions) stay unprefixed. Follow whatever
  prefix the type already uses.
- Function-name suffixes carry meaning and are used consistently:
  - `_exn` — partial/raising variant (`front_exn`, `find_exn`)
  - `_opt` / option-returning — expected absence (`find_opt`)
  - `_unsafe` — skips invariant checks for speed (`snoc_unsafe`)
  - `pp_…` — returns a pretty-printer *document*
  - `string_of_…` — renders a value to `string`
  - `show_…` — full value → string via the pretty-printer
  - `new_…`or `mk_…` — smart constructor that establishes invariants
    (`new_tvar`, `new_arrow`)
- Recursion helpers are conventionally `aux`, `go`, `inner`, or `recurse`
  (the last a partial-application alias for the common recursive call, e.g.
  `let recurse = resolve_expr env in …`).
- Contexts/environments are `ctx` / `env` with possible prefix such as `tenv` for type environment;
  string-keyed maps via `String.Map` (or a `String.Set`).

### AST / type / IR representation
- The surface AST is **polymorphic in its annotation type**: every constructor
  ends with a trailing `'a` "tag" field, e.g.

  ```ocaml
  type 'a expr =
    | Var of string * 'a
    | App of 'a expr * 'a expr list * 'a
    | Let of 'a binding * 'a expr * 'a
    | …
  ```

  The same declarations are reused with the tag instantiated to parse info, then
  to a typed-info record. Provide uniform `…_tag` accessors and `…_tag_map`
  transformers that read and rewrite annotations across the whole tree
  (`expr_tag`, `expr_tag_map`, `prog_tag_map`).
- Efficient Hindley–Milner type representations are classic: `TVar of tv ref`
  with `Link | Unbound`, plus a mutable `levels` record for generalization. Level
  bookkeeping is hidden behind a small generative module so the rest of the
  typechecker treats levels abstractly.

### Pattern matching
- Exhaustive matches, one constructor per arm, destructuring the trailing tag
  inline (`| App (fn, xs, tag) -> …`).
- Arms that share an outcome are merged with `|`, including long or-patterns and
  guarded groups:

  ```ocaml
  | (TArrow (_, _, ls) | TTup (_, ls) | TApp (_, _, ls)) when is_marker ls -> …
  ```

- `function` shorthand for single-argument matches (`let rec repr = function …`).
- Argument-position destructuring of single-constructor types
  (`let cases_tag (MatchPattern (_, tag)) = tag`).
- Impossible cases close with `failwith "…"` or `assert false`, never a silent
  catch-all that could swallow a real case.

### Function size & helper extraction
- Top-level functions may be large, but they are structured as **a cluster of
  named local helpers followed by a small driver**.
- Pure, reusable traversals (free-variable collection, tag maps, normalization)
  are promoted to standalone recursive top-level functions.

### Interfaces & abstraction boundaries
- Abstraction is expressed **inside `.ml` files**, not in separate `.mli`s:
  - inline sealed modules: `module M : sig … end = struct … end`
  - generative functors for fresh mutable state:
    `module Make () : sig … end = struct … end` (fresh-name and level counters)
  - `module type` for plugin points (a `Backend`, a `Hash`, a hashtable `S`)
  - first-class modules + `(val …)` to choose an implementation at runtime
    (e.g. selecting a backend from a CLI flag)
- The standard way to offer interchangeable implementations: a `module type`
  named for its role, several conforming modules, and optionally a `Make` functor
  over the interface.

### Error handling
- Default channel is **exceptions / `failwith`**, with messages built via string
  interpolation: `failwith [%string "type %{name} not defined"]`.
- Use named exceptions where callers, printers, or diagnostics need to
  distinguish failures; register custom exception printers with
  `Stdlib.Printexc.register_printer`.
- For compiler frontend, ppx, or source-span diagnostics, register
  exception-to-error conversion with `Location.register_error_of_exn`.
- Structured domain exceptions where handling matters, e.g. an elaboration error
  carrying a message (and sometimes a bounded re-raise depth), a lexer error
  carrying a position, a duplicate-key error from a builder.
- `option` for genuine absence (`find_opt`, list-uncons helpers, lookups).
- Core-style status returns from data-structure mutation when the caller
  must react: `add : … -> [ \`Ok | \`Duplicate ]`.
- `assert` guards internal invariants, often with an explanatory comment; some
  asserts are left commented-out as machine-readable invariant documentation on
  hot paths.
- Unfinished branches use a `todo` helper / `failwith "todo: …"`.
- Parser/lexer errors are caught at the driver and reported with the source
  position (line/column from the lexing position), then a clean failure.

### Source locations
- Locations typically ride along in the AST's polymorphic annotation rather than
  in a separate `Location.t` threaded by hand. Raw positions come from the
  lexing position record (`pos_lnum`, `pos_cnum`, `pos_bol`) and are consumed at
  the driver for diagnostics.

### Pretty-printing
- `PPrint` is universal; files that print open it at the top.
- Typical combinators: `string`, `^^`, `space`, `break 1`, `group`, `align`,
  `nest 2`, `separate_map`, `concat_map`, `parens`, `brackets`.
- Operator precedence is threaded with a boolean "parenthesize here?" parameter
  plus a local helper:

  ```ocaml
  let rec f c e =
    let pp inner = if c then parens inner else inner in
    match e with … | App (g, x) -> pp (f true g ^^ space ^^ f true x)
  ```

- Rendering uses one consistent ribbon/width pair across the project (commonly
  ribbon 0.8, width 80), with a small `string_of_document` wrapper.
- **Generated source is emitted as documents** through an IR/document DSL, not
  by string concatenation — this keeps indentation and parenthesization correct
  and is usually a stated rule.

### Tests
- Always prefer `ppx_expect` if the tests can be succintly rewriten in ppx_expect format.
- Plain `assert`-based unit tests: `let test_foo () = …` with a
  `let _ = test_foo (); …` runner at the bottom.
- Hand-rolled property checks over random inputs for algebraic laws
  (associativity, idempotency, round-tripping).
- Functor-parameterized test suites that run the same checks across several
  implementations of a `module type`.

### Comments & documentation
- Comment the **why**, not the what: invariants, special cases (e.g.
  `(* special case for ctor application, for compatibility *)`), and `NOTE:`
  markers.
- **Long design rationale lives in docs and source comments link to it by
  anchor** rather than inlining an essay. When you add a subtle data structure or
  algorithm, follow that split: a short why-comment at the code, the full story
  in the docs.

---

## Weak or inconsistent conventions

Be aware of these; don't "fix" them wholesale. Pick the locally dominant choice
for the file you are editing.

- **Standard-library dialect is Core.** Always use `Core` and the labelled API
  (`List.map ~f:`, `~init:`); don't introduce another standard-library dialect.
- **`open` at file scope is common** (often several per file) rather than local
  opens. Local opens (`let open M in`) appear but are rarer.
- **`[@@deriving …]` tends to be used sparingly** (`eq`, `show`, occasionally
  `compare`/`hash`/`sexp` on small key types), not pervasively. Don't assume a
  type derives anything.
- **Function length varies widely.** Small leaf modules are tight; frontend and
  backend modules contain very long functions. There is usually no enforced size
  limit — cohesion via local helpers is what matters, not line count.
- **`.mli` files are effectively absent** — default to no separate interface and
  use inline sealed signatures to hide internals.

---

## Representative examples

Rather than naming this project's files, here is the *kind* of module to read
before writing similar code, and what to extract from each:

- **The surface AST + its pretty-printer** — the polymorphic-tag tree, the
  `…_tag` / `…_tag_map` family, and precedence-threaded printers. The canonical
  reference for AST and pretty-printing style.
- **The semantic type module** — `ref`-based unification variables, a mutable
  `levels` record, `new_*` smart constructors, and a generative `Make ()` functor
  hiding level representation behind a sealed signature.
- **The typechecker / inference module** — a large `type_of` built from local
  helpers, structured domain errors, and interpolated error messages; also a
  good place to see the project's Core-labelled style.
- **The codegen IR + document DSL** — emitting target source as pretty-printer
  documents, with combinators named to avoid clashing with the constructs they
  generate (e.g. trailing-underscore `app_`, `lam_`, `match_int_`).
- **A `module type` + several conforming modules** (a `Backend`, a `Hash`, a
  hashtable `S`) — the template for interchangeable implementations, including
  any C-FFI `external` backends.
- **A runtime/state module** — mutually recursive runtime types and deliberate
  use of mutable record fields / dynamic arrays for performance.
- **A self-contained algorithm module** (Core-based) — clean `snake_case`, a
  local exception for control flow, thorough why-comments. A good model for a new
  leaf utility.
- **The CLI driver** — argument parsing, first-class-module backend selection via
  `(val …)`, and driver-level parse/lex error reporting.
- **The test runner** — assert-based, functor-parameterized tests.

---

## Rules for new code

1. Place the module under the subdirectory matching its role and add it to the
   module list in the relevant build file if that list is explicit.
2. Use the `Core` standard-library dialect and labelled APIs. Don't mix dialects
   within a file.
3. For a new tree/IR type, decide up front whether it needs a per-node
   annotation; if it carries info, follow the trailing-`'a`-tag pattern and
   provide `…_tag` / `…_tag_map` helpers.
4. Use category-prefixed constructors when a type has several related families,
   matching the project's prefix scheme.
5. Pretty-print with the project's document library; render at the project's
   standard ribbon/width; thread precedence with a boolean + local `pp`. Never
   build source/output strings by concatenation when a document DSL fits.
6. Errors: raise interpolated `failwith` for programmer/elaboration faults; use
   named exceptions when callers, printers, or diagnostics need to distinguish
   failures; register printers with `Stdlib.Printexc.register_printer`, or use
   `Location.register_error_of_exn` for compiler frontend, ppx, and source-span
   diagnostics; `option` for expected absence; `assert` for invariants (comment
   why).
7. Offer interchangeable implementations through a `module type` + conforming
   modules; hide per-instance mutable state behind `Make () : sig … end`.
8. Default to no `.mli`. If hiding internals, use an inline sealed `sig`.
9. Name by role: `pp_*`, `string_of_*`, `show_*`, `new_*`, and the
   `_exn` / `_opt` / `_unsafe` suffixes, used precisely.
10. Comment the why. Push long rationale into the docs and link back to it from
    the source.

## Rules for modifying existing code

1. Read the file's top-of-file `open`s and pick up its dialect, utility aliases,
   and helper conventions before writing a line.
2. Preserve the polymorphic-tag shape and exhaustive matches — when you add a
   constructor, update every `match`, `…_tag`, and `…_tag_map` over the type. If
   the project disables match-exhaustiveness errors, the compiler won't flag a
   missed arm; check by hand.
3. Keep large functions structured as local-helpers-plus-driver; add a named
   local helper rather than inlining one more nested `match`.
4. Keep functional-record-update sites working — don't drop placeholder fields
   that exist to enable `{ record with … }`.
5. Match the surrounding error-handling channel (don't thread `result` plumbing
   into an exception-based module).
6. Run the formatter; never hand-format. Keep edits inside the file's role.
7. Don't hand-edit build-generated directories. If you add/remove modules,
   update the module list in the build file.

## Open questions

These vary by project and are worth confirming rather than assuming:

- **Test framework**: whether a richer inline/expect-test framework is wanted, or
  whether assert-based tests plus microbenchmarks are the norm, is **unclear in
  the general case** — check the test directory.
- **Source-location policy**: whether locations should ever graduate out of the
  polymorphic tag into a named `Location.t` is **often unspecified**.
