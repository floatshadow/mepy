(** * Types.LinearTypes: a linear λ-calculus

    This file reads the formulas of ILL ([Intuitionistic/Formula.v]) as
    _types_ of a small functional language, and proves the language type
    safe: a well-typed closed program never gets stuck.

    ** Linear types

    In a linear type system every variable of the context must be used
    _exactly once_. A function of type [A ⊸ B] uses its argument exactly
    once. A pair of type [A ⊗ B] is consumed by taking both components
    apart with [let⊗]. A lazy pair of type [A & B] offers a choice: the
    consumer projects out one component with [π₁] or [π₂]. The type [!A]
    is a value that may be used any number of times.

    We follow the _dual-context_ presentation of Barber and Benton (DILL).
    A typing judgment has two contexts:

<<
        Γ ⨾ Δ ⊢ e ∶ A
        │   │
        │   └─ linear variables: each used exactly once
        └───── unrestricted variables: used any number of times
>>

    An unrestricted variable comes only from [let! e₁ in e₂]: once
    [e₁ : !A] has been opened, its content may be copied or dropped
    freely. Nothing else can be duplicated or thrown away.

    ** Variables and contexts

    Variables are de Bruijn indices, and the two sorts of variables live in
    two separate index spaces: [lv n] is the [n]-th linear variable, [uv n]
    the [n]-th unrestricted variable.

    - The unrestricted context [Γ : list iformula] is an ordinary list:
      [uv n] has type [A] when [Γ !! n = Some A].
    - The linear context [Δ : list (option iformula)] records, for each
      linear variable in scope, whether this subterm may use it ([Some A])
      or not ([None]). A context in which every entry is [None]
      ([lempty]) allows nothing to be used.

    Keeping every linear variable in [Δ], used or not, means that a
    variable has the same index in every subterm. Splitting a context
    between two subterms is then a pointwise operation:
    [Δ ≔ Δ₁ ⋈ Δ₂] gives each [Some A] in [Δ] to exactly one side.

    ** Why we do not use Autosubst

    Libraries such as Autosubst generate de Bruijn substitution for us:
    instantiation with parallel substitutions [σ : nat → tm], shifting,
    and their equational theory. Here they would buy little.

    - There are two sorts of variables, each with its own index space and
      its own binders. A binder shifts only the indices of its own sort.
    - The typing lemma for a parallel substitution needs a typing
      judgment for [σ] itself, and in a linear calculus that judgment
      must split the linear context among all the terms that [σ]
      substitutes. That is extra machinery the type safety proof does not
      need.
    - Evaluation substitutes only _closed_ terms (a value, or the body of
      a [!]-suspension), and only for one variable at a time. A closed
      term needs no shifting when it moves under a binder.

    So a direct substitution function suffices. Its variable case
    ([subst_var]) is three lines, and the rest is a structural traversal.
    Its typing lemma is a plain induction on the typing derivation.

    ** Contents

    - syntax, notations, and the typing rules;
    - values and a call-by-value, left-to-right small-step semantics;
    - context lemmas: insertion [ins] into a context, weakening by unused
      variables, and substitution;
    - progress, preservation, and type safety;
    - examples. *)

From LinearLogic.Intuitionistic Require Export Formula.

(** ** Terms

    Constructor names start with [E] (for "expression"). The binding
    structure, in de Bruijn style:

<<
     ELam e           ƛ e                 e sees the argument as lv 0
     ELetPair e1 e2   let⊗ e1 in e2       in e2: lv 0 = second component,
                                                 lv 1 = first component
     ECase e e1 e2    case e of e1 | e2   each branch sees the payload as lv 0
     ELetBang e1 e2   let! e1 in e2       e2 sees the content as uv 0
>>

    No other constructor binds a variable. The introduction and
    elimination forms for each type:

<<
     type     introduction           elimination
     A ⊸ B    ƛ e                    e1 · e2
     𝟙        ⟨⟩                     let𝟙 e1 in e2
     A ⊗ B    ⟪ e1 , e2 ⟫            let⊗ e1 in e2
     A & B    ⟨ e1 , e2 ⟩            π₁ e,  π₂ e
     A ⊕ B    ι₁ e,  ι₂ e            case e of e1 | e2
     ⊤        ⟨⊤⟩                    (none)
     𝟘        (none)                 abort e
     !A       ! e                    let! e1 in e2
>>

    [⊥] and the atoms [$p] have no term formers: they are opaque base
    types. *)
Inductive tm : Type :=
| ELVar    (n : nat)          (* linear variable                       *)
| EUVar    (n : nat)          (* unrestricted variable                 *)
| ELam     (e : tm)           (* ƛ e          ⊸ intro                  *)
| EApp     (e1 e2 : tm)       (* e1 · e2      ⊸ elim                   *)
| EUnit                       (* ⟨⟩           𝟙 intro                  *)
| ELetUnit (e1 e2 : tm)       (* let𝟙         𝟙 elim                   *)
| EPair    (e1 e2 : tm)       (* ⟪ e1, e2 ⟫   ⊗ intro                  *)
| ELetPair (e1 e2 : tm)       (* let⊗         ⊗ elim                   *)
| EWith    (e1 e2 : tm)       (* ⟨ e1, e2 ⟩   & intro (lazy)           *)
| EFst     (e : tm)           (* π₁ e         & elim                   *)
| ESnd     (e : tm)           (* π₂ e         & elim                   *)
| EInl     (e : tm)           (* ι₁ e         ⊕ intro                  *)
| EInr     (e : tm)           (* ι₂ e         ⊕ intro                  *)
| ECase    (e e1 e2 : tm)     (* case         ⊕ elim                   *)
| ETriv                       (* ⟨⊤⟩          ⊤ intro                  *)
| EAbort   (e : tm)           (* abort e      𝟘 elim                   *)
| EBang    (e : tm)           (* ! e          promotion (lazy)         *)
| ELetBang (e1 e2 : tm).      (* let!         ! elim                   *)

(** ** Notations for terms

    Binding strength, tightest first:

<<
        lv n   uv n                  variables (plain abbreviations)
        π₁ π₂ ι₁ ι₂ ! abort          prefix
        ·                            application (left associative)
        ƛ  let𝟙  let⊗  let!  case    extend as far to the right as possible
>>

    So [ƛ lv 0 · π₁ lv 1] reads as [ƛ ((lv 0) · (π₁ (lv 1)))].

    The term notations live in [tm_scope]. The term [! e] and the type
    [! A] share their notation (and its level); the scope decides which
    is meant. [tm_scope] is bound to the type [tm], so every argument of
    type [tm] (of [typed], [step], [value], …) is read as a term and every
    argument of type [iformula] as a type, whichever scopes are open.
    This file opens [tm_scope] only locally. A file that imports it keeps
    [!] as the type former by default; it can write [(…)%tm] for a
    standalone term. *)
Declare Scope tm_scope.
Delimit Scope tm_scope with tm.
Bind Scope tm_scope with tm.

Notation lv := ELVar.
Notation uv := EUVar.
Notation "'ƛ' e" := (ELam e) (at level 200, right associativity,
  format "ƛ  e") : tm_scope.
Notation "e1 · e2" := (EApp e1 e2) (at level 40, left associativity)
  : tm_scope.
Notation "⟨⟩" := EUnit : tm_scope.
Notation "'let𝟙' e1 'in' e2" := (ELetUnit e1 e2)
  (at level 200, e1 at level 200, right associativity) : tm_scope.
Notation "⟪ e1 , e2 ⟫" := (EPair e1 e2) : tm_scope.
Notation "'let⊗' e1 'in' e2" := (ELetPair e1 e2)
  (at level 200, e1 at level 200, right associativity) : tm_scope.
Notation "⟨ e1 , e2 ⟩" := (EWith e1 e2) : tm_scope.
Notation "'π₁' e" := (EFst e) (at level 30, right associativity) : tm_scope.
Notation "'π₂' e" := (ESnd e) (at level 30, right associativity) : tm_scope.
Notation "'ι₁' e" := (EInl e) (at level 30, right associativity) : tm_scope.
Notation "'ι₂' e" := (EInr e) (at level 30, right associativity) : tm_scope.
Notation "'case' e 'of' e1 '|' e2" := (ECase e e1 e2)
  (at level 200, e at level 200, e1 at level 200, right associativity)
  : tm_scope.
Notation "⟨⊤⟩" := ETriv : tm_scope.
Notation "'abort' e" := (EAbort e) (at level 30, right associativity)
  : tm_scope.
Notation "! e" := (EBang e) (at level 30, right associativity, format "! e")
  : tm_scope.
Notation "'let!' e1 'in' e2" := (ELetBang e1 e2)
  (at level 200, e1 at level 200, right associativity) : tm_scope.

Local Open Scope tm_scope.

(** Sanity checks of the notations: swap, duplicating a [!]-value, and a
    [case] whose branches use [let𝟙] and [abort]. *)
Check (ƛ let⊗ lv 0 in ⟪lv 0, lv 1⟫).
Check (ƛ let! lv 0 in ⟪!uv 0, !uv 0⟫).
Check (case ι₁ ⟨⟩ of let𝟙 lv 0 in ⟨⊤⟩ | abort lv 0).

(** ** Linear contexts *)

(** [lempty Δ]: no linear variable of [Δ] is available. It is an
    abbreviation, not a definition, so stdpp's [Forall] lemmas apply to
    it directly. *)
Notation lempty := (Forall (λ o : option iformula, o = None)).

(** [lone n A Δ]: exactly the linear variable [n] is available in [Δ],
    with type [A]. This is the context of the variable rule. *)
Inductive lone : nat -> iformula -> list (option iformula) -> Prop :=
| lone_here A Δ :
    lempty Δ ->
    lone 0 A (Some A :: Δ)
| lone_there n A Δ :
    lone n A Δ ->
    lone (S n) A (None :: Δ).

(** [mrg o1 o2 o]: one entry of a context split. An available variable
    goes to the left or to the right, never to both. *)
Inductive mrg : option iformula -> option iformula -> option iformula -> Prop :=
| mrg_none : mrg None None None
| mrg_left A : mrg (Some A) None (Some A)
| mrg_right A : mrg None (Some A) (Some A).

(** [Δ ≔ Δ1 ⋈ Δ2]: [Δ] is split into [Δ1] and [Δ2], pointwise. This is
    stdpp's [Forall3], so the three contexts have the same length. *)
Notation "Δ ≔ Δ1 ⋈ Δ2" := (Forall3 mrg Δ1 Δ2 Δ)
  (at level 70, Δ1 at level 69, Δ2 at level 69, no associativity).

(** ** Typing

    The rules follow the natural-deduction presentation of ILL. Two
    premises split the linear context ([⋈]) for multiplicative rules and
    share it for the additive rule [T_with] and for the two branches of
    [T_case]. Read [Γ ⨾ Δ ⊢ e ∶ A] as "with unrestricted [Γ] and linear
    [Δ], the term [e] has type [A]" (the colon is [∶], U+2236).

<<
     lone n A Δ             Γ !! n = Some A   lempty Δ       Γ ⨾ A,Δ ⊢ e ∶ B
   ------------------ var  ----------------------------- uvar ----------------- ⊸I
    Γ ⨾ Δ ⊢ lv n ∶ A           Γ ⨾ Δ ⊢ uv n ∶ A              Γ ⨾ Δ ⊢ ƛ e ∶ A ⊸ B

    Γ ⨾ Δ1 ⊢ e1 ∶ A ⊸ B   Γ ⨾ Δ2 ⊢ e2 ∶ A          lempty Δ
   ------------------------------------------ ⊸E  ---------------- 𝟙I
             Γ ⨾ Δ1⋈Δ2 ⊢ e1 · e2 ∶ B              Γ ⨾ Δ ⊢ ⟨⟩ ∶ 𝟙

    Γ ⨾ Δ1 ⊢ e1 ∶ A ⊗ B   Γ ⨾ B,A,Δ2 ⊢ e2 ∶ C      Γ ⨾ Δ ⊢ e1 ∶ A   Γ ⨾ Δ ⊢ e2 ∶ B
   ----------------------------------------- ⊗E  ---------------------------------- &I
          Γ ⨾ Δ1⋈Δ2 ⊢ let⊗ e1 in e2 ∶ C               Γ ⨾ Δ ⊢ ⟨e1, e2⟩ ∶ A & B

    Γ ⨾ Δ1 ⊢ e ∶ A ⊕ B   Γ ⨾ A,Δ2 ⊢ e1 ∶ C   Γ ⨾ B,Δ2 ⊢ e2 ∶ C
   ------------------------------------------------------------ ⊕E
                Γ ⨾ Δ1⋈Δ2 ⊢ case e of e1 | e2 ∶ C

    lempty Δ   Γ ⨾ Δ ⊢ e ∶ A        Γ ⨾ Δ1 ⊢ e1 ∶ !A   A :: Γ ⨾ Δ2 ⊢ e2 ∶ C
   -------------------------- !I  ------------------------------------------ !E
       Γ ⨾ Δ ⊢ !e ∶ !A                  Γ ⨾ Δ1⋈Δ2 ⊢ let! e1 in e2 ∶ C
>>

    In the table, [A,Δ] abbreviates [Some A :: Δ], and a conclusion
    context [Δ1⋈Δ2] stands for any [Δ] with [Δ ≔ Δ1 ⋈ Δ2]. The remaining
    rules ([T_letunit], [T_pair], [T_fst], [T_snd], [T_inl], [T_inr],
    [T_triv], [T_abort]) are as expected. Some points:

    - In [T_letpair], the second component is pushed last, so it is
      [lv 0] and the first component is [lv 1].
    - [T_triv] accepts any [Δ]: [⊤] is the sink that consumes anything,
      like the sequent rule [topR].
    - [T_abort] splits the context and discards [Δ2], like [zeroL].
    - [T_bang] (promotion) requires an empty linear context: a value
      that may be copied must not capture linear resources.
    - Every term former has exactly one rule: typing is syntax-directed.
      Hence [econstructor] always picks the right rule. *)
Reserved Notation "Γ ⨾ Δ ⊢ e ∶ A"
  (at level 80, Δ at level 79, e at level 200, no associativity).

Inductive typed : list iformula -> list (option iformula) -> tm -> iformula -> Prop :=
| T_lvar Γ Δ n A :
    lone n A Δ ->
    Γ ⨾ Δ ⊢ lv n ∶ A
| T_uvar Γ Δ n A :
    Γ !! n = Some A ->
    lempty Δ ->
    Γ ⨾ Δ ⊢ uv n ∶ A
| T_lam Γ Δ e A B :
    Γ ⨾ Some A :: Δ ⊢ e ∶ B ->
    Γ ⨾ Δ ⊢ ƛ e ∶ A ⊸ B
| T_app Γ Δ Δ1 Δ2 e1 e2 A B :
    Δ ≔ Δ1 ⋈ Δ2 ->
    Γ ⨾ Δ1 ⊢ e1 ∶ A ⊸ B ->
    Γ ⨾ Δ2 ⊢ e2 ∶ A ->
    Γ ⨾ Δ ⊢ e1 · e2 ∶ B
| T_unit Γ Δ :
    lempty Δ ->
    Γ ⨾ Δ ⊢ ⟨⟩ ∶ 𝟙
| T_letunit Γ Δ Δ1 Δ2 e1 e2 C :
    Δ ≔ Δ1 ⋈ Δ2 ->
    Γ ⨾ Δ1 ⊢ e1 ∶ 𝟙 ->
    Γ ⨾ Δ2 ⊢ e2 ∶ C ->
    Γ ⨾ Δ ⊢ let𝟙 e1 in e2 ∶ C
| T_pair Γ Δ Δ1 Δ2 e1 e2 A B :
    Δ ≔ Δ1 ⋈ Δ2 ->
    Γ ⨾ Δ1 ⊢ e1 ∶ A ->
    Γ ⨾ Δ2 ⊢ e2 ∶ B ->
    Γ ⨾ Δ ⊢ ⟪e1, e2⟫ ∶ A ⊗ B
| T_letpair Γ Δ Δ1 Δ2 e1 e2 A B C :
    Δ ≔ Δ1 ⋈ Δ2 ->
    Γ ⨾ Δ1 ⊢ e1 ∶ A ⊗ B ->
    Γ ⨾ Some B :: Some A :: Δ2 ⊢ e2 ∶ C ->
    Γ ⨾ Δ ⊢ let⊗ e1 in e2 ∶ C
| T_with Γ Δ e1 e2 A B :
    Γ ⨾ Δ ⊢ e1 ∶ A ->
    Γ ⨾ Δ ⊢ e2 ∶ B ->
    Γ ⨾ Δ ⊢ ⟨e1, e2⟩ ∶ A & B
| T_fst Γ Δ e A B :
    Γ ⨾ Δ ⊢ e ∶ A & B ->
    Γ ⨾ Δ ⊢ π₁ e ∶ A
| T_snd Γ Δ e A B :
    Γ ⨾ Δ ⊢ e ∶ A & B ->
    Γ ⨾ Δ ⊢ π₂ e ∶ B
| T_inl Γ Δ e A B :
    Γ ⨾ Δ ⊢ e ∶ A ->
    Γ ⨾ Δ ⊢ ι₁ e ∶ A ⊕ B
| T_inr Γ Δ e A B :
    Γ ⨾ Δ ⊢ e ∶ B ->
    Γ ⨾ Δ ⊢ ι₂ e ∶ A ⊕ B
| T_case Γ Δ Δ1 Δ2 e e1 e2 A B C :
    Δ ≔ Δ1 ⋈ Δ2 ->
    Γ ⨾ Δ1 ⊢ e ∶ A ⊕ B ->
    Γ ⨾ Some A :: Δ2 ⊢ e1 ∶ C ->
    Γ ⨾ Some B :: Δ2 ⊢ e2 ∶ C ->
    Γ ⨾ Δ ⊢ case e of e1 | e2 ∶ C
| T_triv Γ Δ :
    Γ ⨾ Δ ⊢ ⟨⊤⟩ ∶ ⊤
| T_abort Γ Δ Δ1 Δ2 e C :
    Δ ≔ Δ1 ⋈ Δ2 ->
    Γ ⨾ Δ1 ⊢ e ∶ 𝟘 ->
    Γ ⨾ Δ ⊢ abort e ∶ C
| T_bang Γ Δ e A :
    lempty Δ ->
    Γ ⨾ Δ ⊢ e ∶ A ->
    Γ ⨾ Δ ⊢ !e ∶ !A
| T_letbang Γ Δ Δ1 Δ2 e1 e2 A C :
    Δ ≔ Δ1 ⋈ Δ2 ->
    Γ ⨾ Δ1 ⊢ e1 ∶ !A ->
    A :: Γ ⨾ Δ2 ⊢ e2 ∶ C ->
    Γ ⨾ Δ ⊢ let! e1 in e2 ∶ C
where "Γ ⨾ Δ ⊢ e ∶ A" := (typed Γ Δ e A).

(** ** Values

    Values are the results of evaluation. The two lazy constructs, [&]
    and [!], are values whatever their contents: [⟨e1, e2⟩] waits for a
    projection to choose a component, and [!e] waits for a [let!] to
    copy it. The eager pairs and injections are values when their
    contents are. *)
Inductive value : tm -> Prop :=
| V_lam e : value (ƛ e)
| V_unit : value ⟨⟩
| V_pair v1 v2 : value v1 -> value v2 -> value ⟪v1, v2⟫
| V_with e1 e2 : value ⟨e1, e2⟩
| V_inl v : value v -> value (ι₁ v)
| V_inr v : value v -> value (ι₂ v)
| V_triv : value ⟨⊤⟩
| V_bang e : value (!e).

(** ** Substitution of a closed term

    [subst_var var k s n] is what the variable [n] becomes when the
    variable [k] is replaced by [s] and removed from the context:
    variables below [k] are unchanged, [k] itself becomes [s], and
    variables above [k] move down by one. The argument [var] is [ELVar]
    or [EUVar]. *)
Definition subst_var (var : nat -> tm) (k : nat) (s : tm) (n : nat) : tm :=
  match n ?= k with
  | Lt => var n
  | Eq => s
  | Gt => var (pred n)
  end.

(** [subst_l k s e] replaces the linear variable [k] of [e] by [s].
    Under a linear binder the target index grows by one (by two under
    [let⊗]). Under [let!] it is unchanged: [let!] binds an unrestricted
    variable. The term [s] is assumed closed, so it is never shifted. *)
Fixpoint subst_l (k : nat) (s : tm) (e : tm) : tm :=
  match e with
  | lv n => subst_var ELVar k s n
  | uv n => uv n
  | ƛ e => ƛ subst_l (S k) s e
  | e1 · e2 => subst_l k s e1 · subst_l k s e2
  | ⟨⟩ => ⟨⟩
  | let𝟙 e1 in e2 => let𝟙 subst_l k s e1 in subst_l k s e2
  | ⟪e1, e2⟫ => ⟪subst_l k s e1, subst_l k s e2⟫
  | let⊗ e1 in e2 => let⊗ subst_l k s e1 in subst_l (S (S k)) s e2
  | ⟨e1, e2⟩ => ⟨subst_l k s e1, subst_l k s e2⟩
  | π₁ e => π₁ subst_l k s e
  | π₂ e => π₂ subst_l k s e
  | ι₁ e => ι₁ subst_l k s e
  | ι₂ e => ι₂ subst_l k s e
  | case e of e1 | e2 =>
      case subst_l k s e of subst_l (S k) s e1 | subst_l (S k) s e2
  | ⟨⊤⟩ => ⟨⊤⟩
  | abort e => abort subst_l k s e
  | !e => !subst_l k s e
  | let! e1 in e2 => let! subst_l k s e1 in subst_l k s e2
  end.

(** [subst_u k s e] replaces the unrestricted variable [k] of [e] by [s].
    Only [let!] moves the target index. *)
Fixpoint subst_u (k : nat) (s : tm) (e : tm) : tm :=
  match e with
  | lv n => lv n
  | uv n => subst_var EUVar k s n
  | ƛ e => ƛ subst_u k s e
  | e1 · e2 => subst_u k s e1 · subst_u k s e2
  | ⟨⟩ => ⟨⟩
  | let𝟙 e1 in e2 => let𝟙 subst_u k s e1 in subst_u k s e2
  | ⟪e1, e2⟫ => ⟪subst_u k s e1, subst_u k s e2⟫
  | let⊗ e1 in e2 => let⊗ subst_u k s e1 in subst_u k s e2
  | ⟨e1, e2⟩ => ⟨subst_u k s e1, subst_u k s e2⟩
  | π₁ e => π₁ subst_u k s e
  | π₂ e => π₂ subst_u k s e
  | ι₁ e => ι₁ subst_u k s e
  | ι₂ e => ι₂ subst_u k s e
  | case e of e1 | e2 => case subst_u k s e of subst_u k s e1 | subst_u k s e2
  | ⟨⊤⟩ => ⟨⊤⟩
  | abort e => abort subst_u k s e
  | !e => !subst_u k s e
  | let! e1 in e2 => let! subst_u k s e1 in subst_u (S k) s e2
  end.

(** ** Operational semantics

    Call-by-value, left to right. The redexes:

<<
     (ƛ e) · v                  ⟶  e[v/0]
     let𝟙 ⟨⟩ in e               ⟶  e
     let⊗ ⟪v1, v2⟫ in e         ⟶  e[v2/0][v1/0]
     π₁ ⟨e1, e2⟩                ⟶  e1
     π₂ ⟨e1, e2⟩                ⟶  e2
     case ι₁ v of e1 | e2       ⟶  e1[v/0]
     case ι₂ v of e1 | e2       ⟶  e2[v/0]
     let! !e in e2              ⟶  e2[e/0]      (unrestricted variable)
>>

    In the [let⊗] rule, [v2] replaces [lv 0] first. Then the old [lv 1]
    has become [lv 0], and [v1] replaces it. In the [let!] rule, the
    suspended term [e] is substituted unevaluated; each use of the
    unrestricted variable runs its own copy. The other rules evaluate
    subterms in place, leftmost first. *)
Reserved Notation "e ⟶ e'" (at level 70, no associativity).

Inductive step : tm -> tm -> Prop :=
(* redexes *)
| S_beta e v :
    value v ->
    (ƛ e) · v ⟶ subst_l 0 v e
| S_letunit e :
    (let𝟙 ⟨⟩ in e) ⟶ e
| S_letpair v1 v2 e :
    value v1 ->
    value v2 ->
    (let⊗ ⟪v1, v2⟫ in e) ⟶ subst_l 0 v1 (subst_l 0 v2 e)
| S_fst e1 e2 :
    π₁ ⟨e1, e2⟩ ⟶ e1
| S_snd e1 e2 :
    π₂ ⟨e1, e2⟩ ⟶ e2
| S_caseInl v e1 e2 :
    value v ->
    (case ι₁ v of e1 | e2) ⟶ subst_l 0 v e1
| S_caseInr v e1 e2 :
    value v ->
    (case ι₂ v of e1 | e2) ⟶ subst_l 0 v e2
| S_letbang e e2 :
    (let! !e in e2) ⟶ subst_u 0 e e2
(* congruences *)
| S_app1 e1 e1' e2 :
    e1 ⟶ e1' ->
    e1 · e2 ⟶ e1' · e2
| S_app2 v e2 e2' :
    value v ->
    e2 ⟶ e2' ->
    v · e2 ⟶ v · e2'
| S_letunit1 e1 e1' e2 :
    e1 ⟶ e1' ->
    (let𝟙 e1 in e2) ⟶ (let𝟙 e1' in e2)
| S_pair1 e1 e1' e2 :
    e1 ⟶ e1' ->
    ⟪e1, e2⟫ ⟶ ⟪e1', e2⟫
| S_pair2 v e2 e2' :
    value v ->
    e2 ⟶ e2' ->
    ⟪v, e2⟫ ⟶ ⟪v, e2'⟫
| S_letpair1 e1 e1' e2 :
    e1 ⟶ e1' ->
    (let⊗ e1 in e2) ⟶ (let⊗ e1' in e2)
| S_fst1 e e' :
    e ⟶ e' ->
    π₁ e ⟶ π₁ e'
| S_snd1 e e' :
    e ⟶ e' ->
    π₂ e ⟶ π₂ e'
| S_inl1 e e' :
    e ⟶ e' ->
    ι₁ e ⟶ ι₁ e'
| S_inr1 e e' :
    e ⟶ e' ->
    ι₂ e ⟶ ι₂ e'
| S_case1 e e' e1 e2 :
    e ⟶ e' ->
    (case e of e1 | e2) ⟶ (case e' of e1 | e2)
| S_abort1 e e' :
    e ⟶ e' ->
    abort e ⟶ abort e'
| S_letbang1 e1 e1' e2 :
    e1 ⟶ e1' ->
    (let! e1 in e2) ⟶ (let! e1' in e2)
where "e ⟶ e'" := (step e e').

(** Multi-step evaluation is stdpp's reflexive-transitive closure. *)
Notation "e ⟶* e'" := (rtc step (e : tm)%tm (e' : tm)%tm)
  (at level 70, no associativity).

Local Hint Constructors value step : core.

(** Values do not step. *)
Lemma value_irreducible v e : value v -> ¬ v ⟶ e.
Proof.
  intros Hv. revert e. induction Hv; intros e' Hs; inversion Hs; naive_solver.
Qed.

(** ** Inserting into a context

    The substitution lemmas remove one variable from a context. We
    describe the context before removal as the context after removal
    with one entry inserted: [ins k x l' l] says that [l] is [l'] with [x]
    inserted at position [k]. The same relation serves both kinds of
    context. *)
Inductive ins {X : Type} : nat -> X -> list X -> list X -> Prop :=
| ins_here x l :
    ins 0 x l (x :: l)
| ins_there k x y l' l :
    ins k x l' l ->
    ins (S k) x (y :: l') (y :: l).

(** Looking up after an insertion: the three cases of [subst_var]. *)
Lemma lookup_ins {X} k (x : X) l' l n :
  ins k x l' l ->
  l !! n = match n ?= k with
           | Lt => l' !! n
           | Eq => Some x
           | Gt => l' !! pred n
           end.
Proof.
  intros Hi. revert n.
  induction Hi as [x l | k x y l' l Hi IH]; intros [| n]; simpl; auto.
  rewrite IH. destruct (n ?= k) eqn:E; auto.
  (* [Gt]: [n] is positive, since [n > k] *)
  destruct n; [destruct k; discriminate | done].
Qed.

(** An empty context stays empty when an entry is removed, and the
    removed entry was [None]. *)
Lemma lempty_ins k o Δ' Δ :
  lempty Δ -> ins k o Δ' Δ -> o = None ∧ lempty Δ'.
Proof. intros HΔ Hi. induction Hi; rewrite Forall_cons in *; naive_solver. Qed.

(** Removing an entry from the context of [lv n], in the three cases of
    [subst_var]. *)
Lemma lone_ins n A Δ k o Δ' :
  lone n A Δ -> ins k o Δ' Δ ->
  match n ?= k with
  | Lt => o = None ∧ lone n A Δ'
  | Eq => o = Some A ∧ lempty Δ'
  | Gt => o = None ∧ lone (pred n) A Δ'
  end.
Proof.
  intros Hl Hi. revert n Hl.
  induction Hi as [o Δ' | k o y Δ' Δ Hi IH]; intros n Hl.
  - inversion Hl; subst; simpl; auto.
  - inversion Hl as [? ? HΔ | m ? ? Hm]; subst; simpl.
    + destruct (lempty_ins _ _ _ _ HΔ Hi) as [-> ?]. split; [done | by constructor].
    + specialize (IH m Hm). destruct (m ?= k) eqn:E; destruct IH as [-> IH].
      * split; [done | by constructor].
      * split; [done | by constructor].
      * destruct m; [destruct k; discriminate |].
        split; [done | by constructor].
Qed.

(** Removing an entry from a split context splits the entry. *)
Lemma merge_ins Δ1 Δ2 Δ k o Δ' :
  Δ ≔ Δ1 ⋈ Δ2 -> ins k o Δ' Δ ->
  ∃ o1 o2 Δ1' Δ2',
    mrg o1 o2 o ∧ ins k o1 Δ1' Δ1 ∧ ins k o2 Δ2' Δ2 ∧ Δ' ≔ Δ1' ⋈ Δ2'.
Proof.
  intros Hm Hi. revert Δ1 Δ2 Hm.
  induction Hi as [o Δ' | k o y Δ' Δ Hi IH]; intros Δ1 Δ2 Hm;
    apply Forall3_cons_inv_r in Hm as (o1 & Δ1' & o2 & Δ2' & -> & -> & Ho & Hm).
  - eexists _, _, _, _. split_and!; eauto using ins.
  - destruct (IH _ _ Hm) as (p1 & p2 & Δ1'' & Δ2'' & ? & ? & ? & ?).
    eexists _, _, _, _. split_and!; eauto using ins, Forall3_cons.
Qed.

(** ** Weakening by unused variables

    Unrestricted variables, and unavailable linear variables, can be
    added at the end of the contexts. In particular a closed term can be
    used in any context whose linear part is empty. *)
Lemma lone_app n A Δ N : lone n A Δ -> lempty N -> lone n A (Δ ++ N).
Proof. induction 1; simpl; constructor; auto using Forall_app_2. Qed.

Lemma merge_lempty N : lempty N -> N ≔ N ⋈ N.
Proof. induction 1 as [| o N -> _ IH]; constructor; auto using mrg. Qed.

(** Weakening at the end of both contexts. The proof needs no index
    shifting: a binder adds its variable at the front, the new variables
    sit at the back. *)
Lemma typed_weaken Γ Γ' Δ N e A :
  lempty N ->
  Γ ⨾ Δ ⊢ e ∶ A ->
  Γ ++ Γ' ⨾ Δ ++ N ⊢ e ∶ A.
Proof.
  intros HN.
  induction 1; econstructor;
    eauto using lone_app, Forall_app_2, lookup_app_l_Some, Forall3_app,
      merge_lempty.
Qed.

(** A closed term is well typed in every context without linear
    resources. This is how a substituted value enters its new context. *)
Lemma closed_weaken Γ Δ v A :
  [] ⨾ [] ⊢ v ∶ A -> lempty Δ -> Γ ⨾ Δ ⊢ v ∶ A.
Proof. intros Hv HΔ. exact (typed_weaken [] Γ [] Δ v A HΔ Hv). Qed.

(** ** The substitution lemmas

    [fits v o]: the closed term [v] may replace a linear variable whose
    context entry is [o]. If [o = None] the variable is not available
    here, so it does not occur, and any [v] fits: the lemma then only
    removes an unused variable (strengthening). This case is needed for
    the subterm of a split that does not own the variable. *)
Definition fits (v : tm) (o : option iformula) : Prop :=
  ∀ A, o = Some A -> [] ⨾ [] ⊢ v ∶ A.

Lemma fits_None v : fits v None.
Proof. by intros A. Qed.

Lemma fits_Some v A : [] ⨾ [] ⊢ v ∶ A -> fits v (Some A).
Proof. by intros ? ? [= <-]. Qed.

Lemma fits_mrg_l v o1 o2 o : mrg o1 o2 o -> fits v o -> fits v o1.
Proof. intros Hm Hv A ->. inversion Hm; subst. by apply Hv. Qed.

Lemma fits_mrg_r v o1 o2 o : mrg o1 o2 o -> fits v o -> fits v o2.
Proof. intros Hm Hv A ->. inversion Hm; subst. by apply Hv. Qed.

(** In a rule that splits the context, removing an entry from the
    conclusion's context removes one from each premise's context. *)
Ltac split_ins :=
  match goal with
  | Hm : _ ≔ _ ⋈ _, Hi : ins _ _ _ _ |- _ =>
      destruct (merge_ins _ _ _ _ _ _ Hm Hi)
        as (?o1 & ?o2 & ?Δ1' & ?Δ2' & ?Ho & ?Hi1 & ?Hi2 & ?Hm')
  end.

(** Substituting a linear variable. The variable [k] has entry [o] in [Δ],
    and [Δ'] is [Δ] without it. *)
Lemma subst_l_typed Γ Δ e B :
  Γ ⨾ Δ ⊢ e ∶ B ->
  ∀ k o Δ' v, ins k o Δ' Δ -> fits v o -> Γ ⨾ Δ' ⊢ subst_l k v e ∶ B.
Proof.
  induction 1; intros k o Δ' v Hi Hv; simpl;
    (* in a rule with an empty linear context, the removed entry is [None] *)
    try match goal with
        | HΔ : lempty _ |- _ => destruct (lempty_ins _ _ _ _ HΔ Hi) as [-> ?]
        end;
    (* in a rule that splits the context, split the removed entry too *)
    try split_ins;
    (* rebuild the rule; under a binder, use [ins_there] *)
    try by (econstructor; eauto using ins, fits_None, fits_mrg_l, fits_mrg_r).
  (* the variable case: compare [n] with [k] *)
  match goal with
  | Hl : lone _ _ _ |- _ => pose proof (lone_ins _ _ _ _ _ _ Hl Hi) as Hn
  end.
  unfold subst_var. destruct (n ?= k); destruct Hn as [-> ?].
  - apply closed_weaken; [by apply Hv | done].
  - by apply T_lvar.
  - by apply T_lvar.
Qed.

(** Substituting an unrestricted variable [k : A]. The linear context does
    not change: the substituted term is closed and uses no resources. *)
Lemma subst_u_typed Γ Δ e B :
  Γ ⨾ Δ ⊢ e ∶ B ->
  ∀ k A Γ' s, ins k A Γ' Γ -> [] ⨾ [] ⊢ s ∶ A -> Γ' ⨾ Δ ⊢ subst_u k s e ∶ B.
Proof.
  induction 1; intros k A' Γ' s Hi Hs; simpl; try by (econstructor; eauto using ins).
  (* the variable case: compare [n] with [k] *)
  match goal with HΓ : Γ !! n = Some _ |- _ => rewrite (lookup_ins _ _ _ _ _ Hi) in HΓ end.
  unfold subst_var.
  destruct (n ?= k); simplify_eq.
  - by apply closed_weaken.
  - by apply T_uvar.
  - by apply T_uvar.
Qed.

(** ** Canonical forms

    A value of a given type has the expected shape. Each proof inspects
    the value, then the (syntax-directed) typing rule for it. *)
Section CanonicalForms.
  Context (Γ : list iformula) (Δ : list (option iformula)) (v : tm).

  Lemma canonical_lolli A B :
    Γ ⨾ Δ ⊢ v ∶ A ⊸ B -> value v -> ∃ e, v = ƛ e.
  Proof. intros Ht Hv. inversion Hv; subst; inversion Ht; eauto. Qed.

  Lemma canonical_one :
    Γ ⨾ Δ ⊢ v ∶ 𝟙 -> value v -> v = ⟨⟩.
  Proof. intros Ht Hv. inversion Hv; subst; inversion Ht; eauto. Qed.

  Lemma canonical_tensor A B :
    Γ ⨾ Δ ⊢ v ∶ A ⊗ B -> value v ->
    ∃ v1 v2, v = ⟪v1, v2⟫ ∧ value v1 ∧ value v2.
  Proof. intros Ht Hv. inversion Hv; subst; inversion Ht; eauto. Qed.

  Lemma canonical_with A B :
    Γ ⨾ Δ ⊢ v ∶ A & B -> value v -> ∃ e1 e2, v = ⟨e1, e2⟩.
  Proof. intros Ht Hv. inversion Hv; subst; inversion Ht; eauto. Qed.

  Lemma canonical_plus A B :
    Γ ⨾ Δ ⊢ v ∶ A ⊕ B -> value v ->
    (∃ v', v = ι₁ v' ∧ value v') ∨ (∃ v', v = ι₂ v' ∧ value v').
  Proof. intros Ht Hv. inversion Hv; subst; inversion Ht; eauto. Qed.

  Lemma canonical_zero :
    Γ ⨾ Δ ⊢ v ∶ 𝟘 -> value v -> False.
  Proof. intros Ht Hv. inversion Hv; subst; inversion Ht. Qed.

  Lemma canonical_bang A :
    Γ ⨾ Δ ⊢ v ∶ !A -> value v -> ∃ e, v = !e.
  Proof. intros Ht Hv. inversion Hv; subst; inversion Ht; eauto. Qed.
End CanonicalForms.

(** ** Type safety

    Two tactics for derivations in the empty context. [inv_merge_nil]
    uses that a split of the empty context is two empty contexts.
    [inv_intro] takes apart the typing of an introduction form. *)
Ltac inv_merge_nil :=
  repeat match goal with H : [] ≔ _ ⋈ _ |- _ => inversion H; clear H; subst end.

Ltac inv_intro :=
  repeat match goal with
  | H : _ ⨾ _ ⊢ ?e ∶ _ |- _ =>
      lazymatch e with
      | ƛ _ => idtac | ⟪_, _⟫ => idtac | ⟨_, _⟩ => idtac
      | ι₁ _ => idtac | ι₂ _ => idtac | !_ => idtac
      end;
      inversion H; clear H; subst
  end.

(** *** Progress

    A closed well-typed term is a value or can take a step. The proof is
    by induction on the typing derivation. In a closed term all the
    contexts in the derivation's premises are empty too, except under
    binders, which the evaluator never enters. *)
Theorem progress e A :
  [] ⨾ [] ⊢ e ∶ A -> value e ∨ ∃ e', e ⟶ e'.
Proof.
  intros Ht.
  remember (@nil iformula) as Γ. remember (@nil (option iformula)) as Δ.
  induction Ht; subst; inv_merge_nil;
    repeat match goal with
           | IH : [] = [] -> [] = [] -> _ |- _ => specialize (IH eq_refl eq_refl)
           end.
  (* there are no variables in the empty context *)
  all: try by match goal with H : lone _ _ [] |- _ => inversion H end.
  all: try by match goal with H : [] !! _ = Some _ |- _ => rewrite lookup_nil in H end.
  (* if an evaluated subterm can step, so can the term *)
  all: repeat match goal with
         | IH : value ?e ∨ ∃ _, ?e ⟶ _ |- _ => destruct IH as [? | [? ?]]; [| by eauto]
         end.
  (* the introduction forms are now values *)
  all: try by eauto.
  (* the elimination forms are redexes, by the canonical forms lemmas *)
  all: right.
  - apply canonical_lolli in Ht1 as [? ->]; eauto.
  - apply canonical_one in Ht1 as ->; eauto.
  - apply canonical_tensor in Ht1 as (? & ? & -> & ? & ?); eauto.
  - apply canonical_with in Ht as (? & ? & ->); eauto.
  - apply canonical_with in Ht as (? & ? & ->); eauto.
  - apply canonical_plus in Ht1 as [(? & -> & ?) | (? & -> & ?)]; eauto.
  - by apply canonical_zero in Ht.
  - apply canonical_bang in Ht1 as [? ->]; eauto.
Qed.

(** *** Preservation

    Evaluation preserves the type of a closed term. The redex cases are
    the substitution lemmas: the substituted value is closed, so it
    [fits] the variable it replaces. *)
Theorem preservation e e' A :
  [] ⨾ [] ⊢ e ∶ A -> e ⟶ e' -> [] ⨾ [] ⊢ e' ∶ A.
Proof.
  intros Ht Hs. revert A Ht.
  induction Hs; intros C Ht; inversion Ht; subst; inv_merge_nil.
  (* congruences: the induction hypothesis retypes the subterm that stepped *)
  all: try by (econstructor; eauto using Forall3_nil).
  (* redexes: take apart the introduction form, then substitute *)
  all: inv_intro; inv_merge_nil.
  all: eauto using subst_l_typed, subst_u_typed, ins, fits_Some.
Qed.

Corollary preservation_multi e e' A :
  [] ⨾ [] ⊢ e ∶ A -> e ⟶* e' -> [] ⨾ [] ⊢ e' ∶ A.
Proof. intros Ht Hs. revert Ht. induction Hs; eauto using preservation. Qed.

(** *** Type safety

    A closed well-typed program never gets stuck: whatever it evaluates
    to is a value or can step further. *)
Theorem type_safety e e' A :
  [] ⨾ [] ⊢ e ∶ A -> e ⟶* e' -> value e' ∨ ∃ e'', e' ⟶ e''.
Proof. eauto using progress, preservation_multi. Qed.

(** ** Examples

    Two programs: [swap] exchanges the components of a pair, and [dup]
    copies a [!]-value. *)
Definition swap : tm := ƛ let⊗ lv 0 in ⟪lv 0, lv 1⟫.
Definition dup : tm := ƛ let! lv 0 in ⟪!uv 0, !uv 0⟫.

(** [evaluate] runs a closed program to the end, one step at a time,
    computing each substitution. *)
Ltac evaluate :=
  repeat (eapply rtc_l;
          [by eauto | cbn [subst_l subst_u subst_var Nat.compare pred]]);
  apply rtc_refl.

Section Examples.
  Variables A B : iformula.

  (** The typing of [swap] makes the context splits explicit: the outer
      [lv 0] is consumed by [let⊗], and in the body [lv 0 : B] goes to
      the left component and [lv 1 : A] to the right. *)
  Example swap_typed : [] ⨾ [] ⊢ swap ∶ A ⊗ B ⊸ B ⊗ A.
  Proof.
    unfold swap. eapply T_lam, (T_letpair _ _ [Some (A ⊗ B)] [None]);
      [repeat constructor | repeat constructor |].
    apply (T_pair _ _ [Some B; None; None] [None; Some A; None]);
      repeat constructor.
  Qed.

  (** In [dup] the content of [!A] becomes the unrestricted [uv 0], which
      may be used twice. Promotion [!uv 0] is allowed because no linear
      variable is available. *)
  Example dup_typed : [] ⨾ [] ⊢ dup ∶ !A ⊸ !A ⊗ !A.
  Proof.
    unfold dup. eapply T_lam, (T_letbang _ _ [Some (!A)%ill] [None]);
      [repeat constructor | repeat constructor |].
    apply (T_pair _ _ [None] [None]); repeat constructor.
  Qed.

  (** A linear variable cannot be used twice in a pair. *)
  Example no_copy : ¬ ([] ⨾ [] ⊢ ƛ ⟪lv 0, lv 0⟫ ∶ A ⊸ A ⊗ A).
  Proof.
    intros Ht. inv_intro.
    (* each component needs [lv 0], so each half of the split has it *)
    repeat match goal with
      | H : _ ⨾ _ ⊢ lv _ ∶ _ |- _ => inversion H; clear H; subst
      | H : lone _ _ _ |- _ => inversion H; clear H; subst
      end.
    (* but [mrg] gives [lv 0] to one side only *)
    match goal with
    | H : _ ≔ _ ⋈ _ |- _ => inversion H as [| ? ? ? ? ? ? Hm]; inversion Hm
    end.
  Qed.

  (** Nor can it be dropped. *)
  Example no_drop : ¬ ([] ⨾ [] ⊢ ƛ ⟨⟩ ∶ A ⊸ 𝟙).
  Proof.
    intros Ht. inv_intro.
    (* [⟨⟩] needs an empty linear context, but [lv 0] is available *)
    match goal with H : _ ⨾ _ ⊢ ⟨⟩ ∶ _ |- _ => inversion H; subst end.
    match goal with HΔ : lempty _ |- _ => by apply Forall_cons in HΔ as [? _] end.
  Qed.

  (** The additive pair, by contrast, shares its context: each component
      may use [lv 0], since only one of them will ever run. *)
  Example with_share : [] ⨾ [] ⊢ ƛ ⟨lv 0, lv 0⟩ ∶ A ⊸ A & A.
  Proof. repeat constructor. Qed.

  (** A [!]-value may be dropped, and [⊤] absorbs anything. *)
  Example bang_drop : [] ⨾ [] ⊢ ƛ let! lv 0 in ⟨⟩ ∶ !A ⊸ 𝟙.
  Proof.
    eapply T_lam, (T_letbang _ _ [Some (!A)%ill] [None]); repeat constructor.
  Qed.

  Example top_drop : [] ⨾ [] ⊢ ƛ ⟨⊤⟩ ∶ A ⊸ ⊤.
  Proof. repeat constructor. Qed.
End Examples.

(** Running [swap] on a pair. *)
Example swap_eval : swap · ⟪⟨⟩, ⟨⊤⟩⟫ ⟶* ⟪⟨⊤⟩, ⟨⟩⟫.
Proof. unfold swap, dup. evaluate. Qed.

(** Running [dup] copies the suspended [π₁ ⟨⟨⟩, ⟨⊤⟩⟩] _unevaluated_:
    [!e] is a value whatever [e] is. *)
Example dup_eval :
  dup · !(π₁ ⟨⟨⟩, ⟨⊤⟩⟩) ⟶* ⟪!(π₁ ⟨⟨⟩, ⟨⊤⟩⟩), !(π₁ ⟨⟨⟩, ⟨⊤⟩⟩)⟫.
Proof. unfold swap, dup. evaluate. Qed.
