(** * Classical.Formula: the language of CLL

    The [Intuitionistic/] files develop intuitionistic linear logic (ILL).
    The [Classical/] files develop _classical_ linear logic (CLL) in
    parallel, file by file, so the two can be read side by side. The
    resource reading of [Intuitionistic/Formula.v] carries over unchanged.
    Only the shape of a sequent changes.

    ** One conclusion versus many

    An ILL sequent [Γ ⊢ C] has exactly one conclusion. A CLL sequent
    [Γ ⊢ Δ] has a _list_ of conclusions. Read it as "consuming [Γ], we
    produce all of [Δ] together". Hypotheses and conclusions are now
    perfectly symmetric. Moving a formula across [⊢] is linear negation
    [A^⊥], and every connective gets a De Morgan dual:

<<
                      additive          multiplicative       exponential
      conjunction     A & B   "with"    A ⊗ B   "times"      !A  "of course"
      disjunction     A ⊕ B   "plus"    A ⅋ B   "par"        ? A "why not"
      truth           ⊤       "top"     𝟙       "one"
      falsity         𝟘       "zero"    ⊥       "bottom"

          (A ⊗ B)^⊥ = A^⊥ ⅋ B^⊥     (A & B)^⊥ = A^⊥ ⊕ B^⊥     (!A)^⊥ = ? A^⊥
          𝟙^⊥ = ⊥                   ⊤^⊥ = 𝟘                   A^⊥^⊥ = A
>>

    What each new connective needs:

    - [A ⅋ B] ("par"): its right rule turns [Γ ⊢ A, B, Δ] into
      [Γ ⊢ A ⅋ B, Δ], so it needs two conclusions at once. [A ⊸ B] is
      _defined_ as [A^⊥ ⅋ B].
    - [⊥]: its right rule weakens an arbitrary [Δ], [Γ ⊢ Δ ⟹ Γ ⊢ ⊥, Δ].
      In ILL, [⊥] is an unremarkable constant.
    - [? A] ("why not"): the dual of [!]. [?] may be weakened and
      contracted on the right, so it needs room for two [? A]'s there.
    - [A^⊥]: involutive, [A^⊥^⊥ ⊣⊢ A]. ILL's [∼A = A ⊸ ⊥] is not.

    [Comparison.v] shows that ILL embeds into CLL and that the inclusion is
    strict: [∼∼A ⊢ A] holds classically but not intuitionistically. *)

From stdpp Require Export prelude.

(** ** Syntax

    Constructor names start with [C] (for "classical"). The prefix keeps
    them apart from the intuitionistic [I…] constructors and from keywords
    such as [with]. Propositional variables are numbered by [nat] and
    written [$0], [$1], …. ([#0] would clash with stdpp's vector notation
    [[# …]].) *)
Inductive cformula : Type :=
| CAtom   (p : nat)          (* propositional variable                 *)
| CNeg    (A : cformula)     (* A^⊥  linear negation                   *)
| COne                       (* 𝟙    multiplicative truth (unit of ⊗)  *)
| CBot                       (* ⊥    multiplicative falsity (unit of ⅋) *)
| CTop                       (* ⊤    additive truth (unit of &)        *)
| CZero                      (* 𝟘    additive falsity (unit of ⊕)      *)
| CTensor (A B : cformula)   (* A ⊗ B  times                           *)
| CPar    (A B : cformula)   (* A ⅋ B  par                             *)
| CWith   (A B : cformula)   (* A & B  with                            *)
| CPlus   (A B : cformula)   (* A ⊕ B  plus                            *)
| CBang   (A : cformula)     (* !A     of course                       *)
| CWhy    (A : cformula).    (* ? A    why not                         *)

(** ** Notations

    The levels match [ill_scope]. Tightest first:

<<
        A^⊥     postfix
        !  ?    prefix
        ⊗  &    (left associative)
        ⅋  ⊕    (left associative)
        ⊸       (right associative)
>>

    Write [? A] _with a space_: Rocq reads [?A] as an existential
    variable. *)
Declare Scope cll_scope.
Delimit Scope cll_scope with cll.
Bind Scope cll_scope with cformula.

Notation "$ p" := (CAtom p) (at level 1, format "$ p") : cll_scope.
Notation "A ^⊥" := (CNeg A) (at level 20, format "A ^⊥") : cll_scope.
Notation "𝟙" := COne : cll_scope.
Notation "⊥" := CBot : cll_scope.
Notation "⊤" := CTop : cll_scope.
Notation "𝟘" := CZero : cll_scope.
Notation "! A" := (CBang A) (at level 30, right associativity, format "! A")
  : cll_scope.
Notation "? A" := (CWhy A) (at level 30, right associativity, format "?  A")
  : cll_scope.
Infix "⊗" := CTensor (at level 40, left associativity) : cll_scope.
Infix "&" := CWith (at level 40, left associativity) : cll_scope.
Infix "⅋" := CPar (at level 50, left associativity) : cll_scope.
Infix "⊕" := CPlus (at level 50, left associativity) : cll_scope.

(** Linear implication is _defined_: [A ⊸ B] is [A^⊥ ⅋ B]. "Consume an
    [A] and produce a [B]" is the same as "produce a demand for an [A]
    together with a [B]". Because [⊸] is a notation, Rocq prints every
    [A^⊥ ⅋ B] as [A ⊸ B]. Its left and right rules are derived in
    [Classical/Sequent.v]. *)
Notation "A ⊸ B" := (CPar (CNeg A) B) (at level 55, right associativity)
  : cll_scope.

(** [‼Γ] puts a [!] on every formula of [Γ], and [⁇Γ] puts a [?] on every
    formula. Promotion needs them. *)
Notation "‼ Γ" := (map CBang Γ) (at level 30, format "‼ Γ") : cll_scope.
Notation "⁇ Γ" := (map CWhy Γ) (at level 30, format "⁇ Γ") : cll_scope.

Open Scope cll_scope.

(** Sanity checks of the notations. *)
Check ($0 ⊸ $1 & $2).
Check (($0 ⊗ $1)^⊥ ⊸ $0^⊥ ⅋ $1^⊥).
Check (λ (A : cformula) Σ Π, ? A :: ‼Σ ++ ⁇Π).
