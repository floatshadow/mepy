(** * Intuitionistic.Formula: the language of ILL

    Start reading the tutorial here. The [Intuitionistic/] files develop
    _intuitionistic linear logic_ (ILL). The [Classical/] files develop
    classical linear logic (CLL) in parallel, and [Comparison.v] relates
    the two.

    ** Why linear logic?

    In ordinary logic a hypothesis is a _truth_. Once you know [A], you may
    use it as often as you like ([A → A ∧ A]) or ignore it ([A ∧ B → A]).
    Girard's linear logic (1987) reads hypotheses as _resources_ instead:
    a proof of [A ⊸ B] consumes exactly one [A] and produces exactly one
    [B]. Two structural rules are dropped:

<<
       Γ, A, A ⊢ C                       Γ ⊢ C
      ------------- contraction      ------------ weakening
        Γ, A ⊢ C                       Γ, A ⊢ C
>>

    Without them, conjunction splits into two connectives, and so does
    truth:

    - [A ⊗ B] ("times"): an [A] _and_ a [B], side by side. Both get used.
    - [A & B] ("with"): a _choice_ of [A] or [B]. The consumer picks one,
      and the other is never produced.
    - [𝟙] ("one") is the unit of [⊗], the empty resource. [⊤] ("top") is
      the unit of [&], a sink that accepts anything.

    Disjunction comes in one intuitionistic form:

    - [A ⊕ B] ("plus"): an [A] or a [B]. The producer chose which. Its
      unit is [𝟘] ("zero").

    The remaining connectives:

    - [A ⊸ B] ("lollipop") turns one [A] into one [B].
    - [!A] ("of course") is an unlimited supply of [A]. It brings
      contraction and weakening back in a controlled way.
    - [⊥] ("bottom"). In ILL it is a propositional constant with no rules
      of its own. It lets us define the (non-involutive) negation
      [∼A := A ⊸ ⊥].

    ** Why "intuitionistic"?

    Every ILL sequent [Γ ⊢ C] has exactly one conclusion. Classical
    linear logic (CLL, [Classical/Formula.v]) allows a list of
    conclusions [Γ ⊢ Δ]. That extra room is what CLL needs for its other
    connectives:

    - the multiplicative disjunction [A ⅋ B] ("par"), whose right rule
      needs two conclusions [Γ ⊢ A, B];
    - the exponential [? A] ("why not"), whose contraction rule needs two
      copies [? A, ? A] on the right;
    - an involutive negation [A^⊥], with [A^⊥^⊥ ⊣⊢ A].

    ILL has none of these, for the same reason intuitionistic logic lacks
    double-negation elimination. [Comparison.v] makes this precise: ILL
    embeds into CLL, but CLL proves [∼∼A ⊢ A] and ILL does not.

    ILL is also exactly the type language of the linear λ-calculus
    ([Types/LinearTypes.v]).

    The coffee example:

<<
        euro ⊸ coffee & tea          one euro buys your choice of drink
>>

    [euro ⊢ coffee ⊗ tea] is unprovable. [Intuitionistic/Phase.v] proves
    that. *)

From stdpp Require Export prelude.

(** ** Syntax

    Constructor names start with [I] (for "intuitionistic"). The prefix
    keeps them apart from the classical constructors ([C…]), from Gallina
    keywords ([with]), and from stdpp names ([top]). Propositional
    variables are numbered by [nat] and written [$0], [$1], …. ([#0] would
    clash with stdpp's vector notation [[# …]].) *)
Inductive iformula : Type :=
| IAtom   (p : nat)          (* propositional variable                 *)
| IOne                       (* 𝟙      unit of ⊗                       *)
| IBot                       (* ⊥      a constant: "the answer"        *)
| ITop                       (* ⊤      unit of &                       *)
| IZero                      (* 𝟘      unit of ⊕                       *)
| ITensor (A B : iformula)   (* A ⊗ B  times                           *)
| ILolli  (A B : iformula)   (* A ⊸ B  linear implication              *)
| IWith   (A B : iformula)   (* A & B  with                            *)
| IPlus   (A B : iformula)   (* A ⊕ B  plus                            *)
| IBang   (A : iformula).    (* !A     of course                       *)

(** ** Notations

    Binding strength, tightest first:

<<
        ∼  !    prefix
        ⊗  &    (left associative)
        ⊕       (left associative)
        ⊸       (right associative)
>>

    So [!A ⊗ B ⊸ C & D] reads as [((!A) ⊗ B) ⊸ (C & D)]. All
    connectives bind tighter than [::] and [++], so [A ⊸ B :: Γ] is a
    list whose head is [A ⊸ B]. The classical notations use the same
    levels.

    Inside [ill_scope], [⊤] and [&] mean [ITop] and [IWith]. This
    overrides stdpp's [⊤] and Stdlib's [{x : T & P}]. *)
Declare Scope ill_scope.
Delimit Scope ill_scope with ill.
Bind Scope ill_scope with iformula.

Notation "$ p" := (IAtom p) (at level 1, format "$ p") : ill_scope.
Notation "𝟙" := IOne : ill_scope.
Notation "⊥" := IBot : ill_scope.
Notation "⊤" := ITop : ill_scope.
Notation "𝟘" := IZero : ill_scope.
Notation "! A" := (IBang A) (at level 30, right associativity, format "! A")
  : ill_scope.
Infix "⊗" := ITensor (at level 40, left associativity) : ill_scope.
Infix "&" := IWith (at level 40, left associativity) : ill_scope.
Infix "⊕" := IPlus (at level 50, left associativity) : ill_scope.
Infix "⊸" := ILolli (at level 55, right associativity) : ill_scope.

(** Intuitionistic linear negation is _defined_ as [A ⊸ ⊥]. Unlike
    classical [A^⊥], it is not involutive: [A ⊢ ∼∼A] holds, but
    [∼∼A ⊢ A] does not. *)
Notation "∼ A" := (ILolli A IBot) (at level 30, right associativity,
  format "∼ A") : ill_scope.

(** [‼Γ] puts a [!] on every formula of the context [Γ]:
    [‼[A; B] = [!A; !B]]. *)
Notation "‼ Γ" := (map IBang Γ) (at level 30, format "‼ Γ") : ill_scope.

Open Scope ill_scope.

(** Sanity checks of the notations. *)
Check ($0 ⊸ $1 & $2).
Check (!$0 ⊗ $1 ⊸ ∼ $2).
Check (λ A B (Γ : list iformula), A ⊸ B :: ‼Γ).

(** The coffee example from the introduction. *)
Definition euro   := $0.
Definition coffee := $1.
Definition tea    := $2.
Check (euro ⊸ coffee & tea).
