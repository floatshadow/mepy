(** * Intuitionistic.Phase: phase semantics and soundness for ILL

    Truth tables explain classical logic and Kripke models explain
    intuitionistic logic. _Phase semantics_ (Girard 1987) plays the same
    role for linear logic, and its intuition is short:

    - a _phase_ is an element of a commutative monoid [(M, ·, ε)]. Think of
      it as a bag of resources, with [·] putting two bags together;
    - a formula denotes a _set_ of phases: the bags of resources that are
      enough to produce it;
    - a sequent [A₁, …, Aₙ ⊢ C] is valid when combining one bag from each
      [Aᵢ] always gives a bag in [C].

    [·] need not be idempotent, so [m · m] can differ from [m]. That is how
    the semantics refuses to duplicate resources.

    The connectives [⊗], [⊕], [𝟙], [𝟘], [!] require sets to be _closed_
    under a closure operator [cl]. Closed sets are called _facts_. In the
    intuitionistic semantics, [cl] is any closure operator that is stable
    under [·], and [⊥] is just some fact. The classical semantics
    ([Classical/Phase.v]) is the special case [cl X = X^⊥⊥], in which
    [⊥] determines everything else.

    This file contains:
    - phase spaces, with sets taken from stdpp's [propset];
    - the interpretation of formulas and sequents;
    - soundness: [Γ ⊢[c] C → Γ ⊨ C];
    - countermodels: ILL has neither contraction nor weakening.

    [Intuitionistic/CutElim.v] proves the converse and uses it to
    eliminate cuts. *)

From stdpp Require Export propset.
From LinearLogic.Intuitionistic Require Export Sequent.

(** ** Phase spaces

    Before the record we define the pointwise product of two sets, for any
    monoid operation [op] and equivalence [eq]:
    [X ⊙ Y = { z | z ≡ x · y for some x ∈ X, y ∈ Y }]. The stability axiom
    of the record uses it. *)
Definition prod_with {M} (eq : relation M) (op : M -> M -> M) (X Y : propset M)
  : propset M := {[ z | ∃ a b, a ∈ X ∧ b ∈ Y ∧ eq z (op a b) ]}.

(**

    An intuitionistic phase space has four components:

    - a commutative monoid [(M, ·, ε)], commutative only up to an
      equivalence [≡]. The syntactic model of [CutElim.v] uses lists up
      to permutation, so equality would be too strict. We use stdpp's
      [Equiv] class and [Proper] instances, so [rewrite] works under [≡];
    - a closure operator [cl] on [propset M] that is _stable_:
      [cl X ⊙ cl Y ⊆ cl (X ⊙ Y)];
    - a set [J] of _reusable_ phases. [J] contains [ε] and is closed under
      [·], and each [j ∈ J] can be discarded ([j ∈ cl {ε}]) and duplicated
      ([j ∈ cl {j · j}]). [J] is the semantic shadow of [!];
    - a set [ph_bot]. Its closure interprets the constant [⊥]. *)
Record phase_space : Type := {
  carrier :> Type;
  ph_equiv : Equiv carrier;
  ph_op : carrier -> carrier -> carrier;
  ph_e  : carrier;
  ph_cl : propset carrier -> propset carrier;
  ph_J  : propset carrier;
  ph_bot : propset carrier;

  (* (M, ·, ε) is a commutative monoid up to ≡ *)
  ph_equivalence : Equivalence (@equiv _ ph_equiv);
  ph_op_proper : Proper (@equiv _ ph_equiv ==> @equiv _ ph_equiv ==> @equiv _ ph_equiv) ph_op;
  ph_assoc  : ∀ x y z, @equiv _ ph_equiv (ph_op x (ph_op y z)) (ph_op (ph_op x y) z);
  ph_comm   : ∀ x y, @equiv _ ph_equiv (ph_op x y) (ph_op y x);
  ph_unit_l : ∀ x, @equiv _ ph_equiv (ph_op ph_e x) x;

  (* cl is a closure operator: extensive, and monotone + idempotent
     (packed into ph_cl_least); it respects ≡ and is stable under · *)
  ph_cl_ext    : ∀ X, X ⊆ ph_cl X;
  ph_cl_least  : ∀ X Y, X ⊆ ph_cl Y -> ph_cl X ⊆ ph_cl Y;
  ph_cl_proper : ∀ X x y, @equiv _ ph_equiv x y -> x ∈ ph_cl X -> y ∈ ph_cl X;
  ph_cl_stable : ∀ X Y x y, x ∈ ph_cl X -> y ∈ ph_cl Y ->
      ph_op x y ∈ ph_cl (prod_with (@equiv _ ph_equiv) ph_op X Y);

  (* J: the reusable phases *)
  ph_J_proper : ∀ x y, @equiv _ ph_equiv x y -> x ∈ ph_J -> y ∈ ph_J;
  ph_J_unit   : ph_e ∈ ph_J;
  ph_J_op     : ∀ x y, x ∈ ph_J -> y ∈ ph_J -> ph_op x y ∈ ph_J;
  ph_J_weak   : ∀ x, x ∈ ph_J -> x ∈ ph_cl {[ z | @equiv _ ph_equiv z ph_e ]};
  ph_J_contr  : ∀ x, x ∈ ph_J -> x ∈ ph_cl {[ z | @equiv _ ph_equiv z (ph_op x x) ]};
}.

Arguments ph_op {_}. Arguments ph_e {_}. Arguments ph_cl {_}.
Arguments ph_J {_}. Arguments ph_bot {_}.
Arguments ph_assoc {_}. Arguments ph_comm {_}. Arguments ph_unit_l {_}.
Arguments ph_cl_ext {_}. Arguments ph_cl_least {_}. Arguments ph_cl_proper {_}.
Arguments ph_cl_stable {_}. Arguments ph_J_proper {_}. Arguments ph_J_unit {_}.
Arguments ph_J_op {_}. Arguments ph_J_weak {_}. Arguments ph_J_contr {_}.

#[export] Existing Instance ph_equiv.
#[export] Instance ph_equivalence' (P : phase_space) : Equivalence (≡@{P})
  := ph_equivalence P.
#[export] Instance ph_op_proper' (P : phase_space)
  : Proper ((≡) ==> (≡) ==> (≡)) (@ph_op P) := ph_op_proper P.

(** *** Notations *)
Declare Scope ill_phase_scope.
Open Scope ill_phase_scope.

Notation "x · y" := (ph_op x y) (at level 40, left associativity)
  : ill_phase_scope.
Notation ε := ph_e.
Notation cl := ph_cl.
Notation J := ph_J.

(** [{ε}] up to [≡], and the pointwise product
    [X ⊙ Y = { z | z ≡ x · y, x ∈ X, y ∈ Y }]. *)
Definition one_set {P : phase_space} : propset P := {[ z | z ≡ ε ]}.
Definition prod_set {P : phase_space} (X Y : propset P) : propset P :=
  prod_with (≡) ph_op X Y.
Infix "⊙" := prod_set (at level 40, left associativity) : ill_phase_scope.

(** stdpp keeps [propset] membership opaque. Each set former therefore
    comes with an [elem_of_…] lemma, and with a [SetUnfoldElemOf] instance
    so that stdpp's [set_unfold] and [set_solver] can see through it. *)
Section elem_of.
  Context {P : phase_space}.
  Implicit Types (X Y : propset P) (z : P).

  Lemma elem_of_one z : z ∈ one_set ↔ z ≡ ε.
  Proof. unfold one_set. by rewrite elem_of_PropSet. Qed.
  Lemma elem_of_prod X Y z : z ∈ X ⊙ Y ↔ ∃ a b, a ∈ X ∧ b ∈ Y ∧ z ≡ a · b.
  Proof. unfold prod_set, prod_with. by rewrite elem_of_PropSet. Qed.

  #[global] Instance set_unfold_one z : SetUnfoldElemOf z one_set (z ≡ ε).
  Proof. constructor. apply elem_of_one. Qed.
  #[global] Instance set_unfold_prod X Y z (Q R : P -> Prop) :
    (∀ a, SetUnfoldElemOf a X (Q a)) -> (∀ b, SetUnfoldElemOf b Y (R b)) ->
    SetUnfoldElemOf z (X ⊙ Y) (∃ a b, Q a ∧ R b ∧ z ≡ a · b).
  Proof.
    intros HX HY. constructor. rewrite elem_of_prod.
    setoid_rewrite (λ a, @set_unfold_elem_of _ _ _ a X (Q a) (HX a)).
    by setoid_rewrite (λ b, @set_unfold_elem_of _ _ _ b Y (R b) (HY b)).
  Qed.
End elem_of.

(** ** Facts and the algebra of sets of phases

    Most of the soundness proof is reasoning about inclusions [X ⊆ Y]
    between sets of phases, not about individual phases. This section
    collects the inclusions we need. [cl] and [⊙] are monotone, and we
    register this with stdpp's [Proper] machinery so that [⊆] works with
    [rewrite]: in a goal [L ⊆ R], [rewrite H] with [H : X ⊆ X'] replaces
    [X] by [X'] inside [L]. A proof of [L ⊆ R] then reads as a short
    calculation [L ⊆ L' ⊆ … ⊆ R]. *)
Section Facts.
  Context {P : phase_space}.
  Implicit Types (X Y Z G F : propset P) (x y z m g : P).

  Lemma cl_mono X Y : X ⊆ Y -> cl X ⊆ cl Y.
  Proof. intros H. apply ph_cl_least. intros x Hx. apply ph_cl_ext, H, Hx. Qed.

  #[global] Instance cl_subseteq_proper : Proper ((⊆) ==> (⊆)) (@ph_cl P).
  Proof. intros X Y. apply cl_mono. Qed.

  (** A _fact_ is a closed set: [cl F ⊆ F], so [cl F = F]. *)
  Definition fact F : Prop := cl F ⊆ F.

  Lemma fact_cl X : fact (cl X).
  Proof. apply ph_cl_least. done. Qed.

  (** Facts are closed under [≡]. *)
  Lemma fact_proper F x y : fact F -> x ≡ y -> x ∈ F -> y ∈ F.
  Proof.
    intros HF Hxy Hx. apply HF, (ph_cl_proper _ x); [done |]. by apply ph_cl_ext.
  Qed.

  (** [cl X] is the least fact containing [X]. *)
  Lemma cl_least_fact X F : fact F -> X ⊆ F -> cl X ⊆ F.
  Proof. intros HF H. by rewrite H. Qed.

  (** *** Products

      [⊙] is monotone, commutative, associative, and has [{ε}] as its
      unit, all up to [⊆]. [prod_assoc_l] and [prod_assoc_r] move the
      brackets to the left and to the right. The proofs unfold [⊙] and use
      the monoid laws of [·]. *)
  Lemma prod_mono X X' Y Y' : X ⊆ X' -> Y ⊆ Y' -> X ⊙ Y ⊆ X' ⊙ Y'.
  Proof. set_solver. Qed.

  #[global] Instance prod_subseteq_proper :
    Proper ((⊆) ==> (⊆) ==> (⊆)) (@prod_set P).
  Proof. intros X X' HX Y Y' HY. by apply prod_mono. Qed.

  Lemma prod_comm X Y : X ⊙ Y ⊆ Y ⊙ X.
  Proof.
    intros m (a & b & Ha & Hb & Hm)%elem_of_prod.
    apply elem_of_prod. exists b, a. by rewrite Hm, ph_comm.
  Qed.

  Lemma prod_assoc_l X Y Z : X ⊙ (Y ⊙ Z) ⊆ (X ⊙ Y) ⊙ Z.
  Proof.
    intros m (a & n & Ha & (b & c & Hb & Hc & Hn)%elem_of_prod & Hm)%elem_of_prod.
    apply elem_of_prod. exists (a · b), c. split_and!; [| done |].
    - apply elem_of_prod. by exists a, b.
    - by rewrite Hm, Hn, ph_assoc.
  Qed.

  Lemma prod_assoc_r X Y Z : (X ⊙ Y) ⊙ Z ⊆ X ⊙ (Y ⊙ Z).
  Proof.
    intros m (n & c & (a & b & Ha & Hb & Hn)%elem_of_prod & Hc & Hm)%elem_of_prod.
    apply elem_of_prod. exists a, (b · c). split_and!; [done | |].
    - apply elem_of_prod. by exists b, c.
    - by rewrite Hm, Hn, ph_assoc.
  Qed.

  Lemma prod_unit_l X : X ⊆ one_set ⊙ X.
  Proof.
    intros x Hx. apply elem_of_prod. exists ε, x. by rewrite elem_of_one, ph_unit_l.
  Qed.

  (** The converse of [prod_unit_l] needs [≡]-closure, so we state it for
      a fact [F] that contains [X]. *)
  Lemma prod_one_l X F : fact F -> X ⊆ F -> one_set ⊙ X ⊆ F.
  Proof.
    intros HF HX m (e & x & He%elem_of_one & Hx & Hm)%elem_of_prod.
    apply (fact_proper _ x); [done | | by apply HX].
    by rewrite Hm, He, ph_unit_l.
  Qed.

  (** The stability axiom of the record, stated for sets. *)
  Lemma cl_prod X Y : cl X ⊙ cl Y ⊆ cl (X ⊙ Y).
  Proof.
    intros m (x & y & Hx & Hy & Hm)%elem_of_prod.
    apply (ph_cl_proper _ (x · y)); [by symmetry |]. by apply ph_cl_stable.
  Qed.

  (** The workhorse of the soundness proof. To show that [cl X ⊙ G] lies
      in a fact [F], it is enough to check the generators [X] of the
      closure. This is where stability is used. *)
  Lemma prod_cl_l X G F : fact F -> X ⊙ G ⊆ F -> cl X ⊙ G ⊆ F.
  Proof. intros HF H. rewrite (ph_cl_ext G), cl_prod. by apply cl_least_fact. Qed.

  (** ** The phase connectives

      The phase-space counterpart of each connective:

<<
      𝟙      ↦  cl {ε}
      X ⊗ Y  ↦  cl (X ⊙ Y)
      X ⊸ Y  ↦  { m | ∀ a ∈ X, m · a ∈ Y }
      X & Y  ↦  X ∩ Y
      ⊤      ↦  M
      X ⊕ Y  ↦  cl (X ∪ Y)
      𝟘      ↦  cl ∅
      !X     ↦  cl (X ∩ J)
      ⊥      ↦  cl ph_bot            (part of the model)
>>

      [⊸] and [&] need no closure: when [X] and [Y] are facts, so are
      [X ⊸ Y] and [X ∩ Y]. *)
  Definition ph_one : propset P := cl one_set.
  Definition ph_tensor X Y : propset P := cl (X ⊙ Y).
  Definition ph_lolli X Y : propset P := {[ m | ∀ a, a ∈ X -> m · a ∈ Y ]}.
  Definition ph_top : propset P := {[ _ | True ]}.
  Definition ph_plus X Y : propset P := cl (X ∪ Y).
  Definition ph_zero : propset P := cl ∅.
  Definition ph_bang X : propset P := cl (X ∩ J).

  Lemma elem_of_lolli X Y m : m ∈ ph_lolli X Y ↔ ∀ a, a ∈ X -> m · a ∈ Y.
  Proof. unfold ph_lolli. by rewrite elem_of_PropSet. Qed.
  Lemma elem_of_top m : m ∈ ph_top.
  Proof. unfold ph_top. by rewrite elem_of_PropSet. Qed.

  #[global] Instance set_unfold_lolli X Y m :
    SetUnfoldElemOf m (ph_lolli X Y) (∀ a, a ∈ X -> m · a ∈ Y).
  Proof. constructor. apply elem_of_lolli. Qed.
  #[global] Instance set_unfold_top m : SetUnfoldElemOf m ph_top True.
  Proof. constructor. split; [done | intros; apply elem_of_top]. Qed.

  (** [X ⊸ Y] is the largest [G] with [G ⊙ X ⊆ Y]. The two directions
      are the semantic [⊸R] and [⊸L]. *)
  Lemma lolli_intro X Y G : G ⊙ X ⊆ Y -> G ⊆ ph_lolli X Y.
  Proof.
    intros H m Hm. apply elem_of_lolli. intros a Ha.
    apply H, elem_of_prod. by exists m, a.
  Qed.

  Lemma lolli_elim X Y : fact Y -> ph_lolli X Y ⊙ X ⊆ Y.
  Proof.
    intros HY m (f & a & Hf & Ha & Hm)%elem_of_prod.
    apply (fact_proper _ (f · a)); [done | by symmetry |].
    rewrite elem_of_lolli in Hf. by apply Hf.
  Qed.

  Lemma fact_lolli X Y : fact Y -> fact (ph_lolli X Y).
  Proof. intros HY. apply lolli_intro, prod_cl_l, lolli_elim; done. Qed.

  Lemma fact_inter X Y : fact X -> fact Y -> fact (X ∩ Y).
  Proof.
    intros HX HY m Hm. apply elem_of_intersection.
    split; [apply HX | apply HY]; revert m Hm; apply cl_mono; set_solver.
  Qed.

  Lemma fact_top : fact ph_top.
  Proof. intros m _. apply elem_of_top. Qed.

  (** Using a tensor [X ⊗ Y] next to [G] is the same as using [X], [Y]
      and [G] side by side: the semantic [⊗L]. *)
  Lemma tensor_l X Y G F : fact F -> X ⊙ (Y ⊙ G) ⊆ F -> ph_tensor X Y ⊙ G ⊆ F.
  Proof. intros HF H. apply prod_cl_l; [done |]. by rewrite prod_assoc_r. Qed.

  (** The axioms on [J] say that a phase of [!X] can be discarded (it
      lies in [𝟙]) and duplicated (it lies in [!X ⊗ !X]). These are the
      semantic [!W] and [!C]. *)
  Lemma bang_weak X : ph_bang X ⊆ ph_one.
  Proof.
    apply ph_cl_least. intros j [_ HJ]%elem_of_intersection. by apply ph_J_weak.
  Qed.

  Lemma bang_contr X : ph_bang X ⊆ ph_tensor (ph_bang X) (ph_bang X).
  Proof.
    apply ph_cl_least. intros j Hj.
    apply (cl_mono ((X ∩ J) ⊙ (X ∩ J))); [apply prod_mono; apply ph_cl_ext |].
    apply (cl_mono {[ z | z ≡ j · j ]}); [set_solver |].
    apply ph_J_contr. set_solver.
  Qed.
End Facts.

(** ** Interpreting formulas and sequents

    A _valuation_ [v] gives each propositional variable a set of phases.
    The variable [$p] denotes [cl (v p)], which makes it a fact. *)
Fixpoint interp {P : phase_space} (v : nat -> propset P) (A : iformula)
  : propset P :=
  match A with
  | IAtom p     => cl (v p)
  | IOne        => ph_one
  | IBot        => cl ph_bot
  | ITop        => ph_top
  | IZero       => ph_zero
  | ITensor A B => ph_tensor (interp v A) (interp v B)
  | ILolli A B  => ph_lolli (interp v A) (interp v B)
  | IWith A B   => interp v A ∩ interp v B
  | IPlus A B   => ph_plus (interp v A) (interp v B)
  | IBang A     => ph_bang (interp v A)
  end.

Notation "⟦ A ⟧ v" := (interp v A)
  (at level 1, A at level 200, v at level 1, format "⟦ A ⟧ v")
  : ill_phase_scope.

(** A context [[A₁; …; Aₙ]] denotes [⟦A₁⟧ ⊙ … ⊙ ⟦Aₙ⟧ ⊙ {ε}]: the bags
    obtained by taking one bag for each hypothesis and combining them. *)
Fixpoint interp_ctx {P : phase_space} (v : nat -> propset P)
    (Γ : list iformula) : propset P :=
  match Γ with
  | []     => one_set
  | A :: Γ => ⟦A⟧v ⊙ interp_ctx v Γ
  end.

Notation "⦅ Γ ⦆ v" := (interp_ctx v Γ)
  (at level 1, Γ at level 200, v at level 1, format "⦅ Γ ⦆ v")
  : ill_phase_scope.

(** A sequent is valid in a model when the bags for the hypotheses always
    give a bag for the conclusion. It is valid outright when that holds in
    every phase space under every valuation. *)
Definition valid_in {P : phase_space} (v : nat -> propset P) Γ A : Prop :=
  ⦅Γ⦆v ⊆ ⟦A⟧v.

Definition valid (Γ : list iformula) (A : iformula) : Prop :=
  ∀ (P : phase_space) (v : nat -> propset P), valid_in v Γ A.

Notation "Γ ⊨ A" := (valid Γ A) (at level 80, no associativity)
  : ill_phase_scope.

Section Interp.
  Context {P : phase_space} (v : nat -> propset P).

  (** Every formula denotes a fact. *)
  Lemma interp_fact A : fact (⟦A⟧v).
  Proof.
    induction A; cbn [interp];
      unfold ph_one, ph_zero, ph_tensor, ph_plus, ph_bang;
      auto using fact_cl, fact_lolli, fact_inter, fact_top.
  Qed.

  (** Split a bag for [Γ ++ Δ] into a bag for [Γ] and a bag for [Δ]. *)
  Lemma ctx_app Γ Δ : ⦅Γ ++ Δ⦆v ⊆ ⦅Γ⦆v ⊙ ⦅Δ⦆v.
  Proof.
    induction Γ as [| A Γ IH]; cbn [interp_ctx app].
    - apply prod_unit_l.
    - by rewrite IH, prod_assoc_l.
  Qed.

  (** [·] is commutative, so the order of hypotheses is irrelevant. This
      is the semantic content of the exchange rule. *)
  Lemma ctx_perm Γ Γ' : Γ ≡ₚ Γ' -> ⦅Γ⦆v ⊆ ⦅Γ'⦆v.
  Proof.
    induction 1 as [| A Γ Γ' _ IH | A B Γ | Γ Γ' Γ'' _ IH1 _ IH2];
      cbn [interp_ctx].
    - done.
    - by rewrite IH.
    - by rewrite prod_assoc_l, (prod_comm (⟦B⟧v)), prod_assoc_r.
    - by rewrite IH1, IH2.
  Qed.

  (** A bag for a banged context [‼Σ] lies in the closure of the bags that
      are both in [⦅‼Σ⦆] and reusable. Promotion uses this. *)
  Lemma ctx_bangs Σ : ⦅‼Σ⦆v ⊆ cl (⦅‼Σ⦆v ∩ J).
  Proof.
    induction Σ as [| A Σ IH]; cbn [interp_ctx map interp].
    - intros m Hm. apply ph_cl_ext, elem_of_intersection. split; [done |].
      apply elem_of_one in Hm.
      apply (ph_J_proper ε); [by symmetry | apply ph_J_unit].
    - (* cl (⟦A⟧ ∩ J) ⊙ cl (⦅‼Σ⦆ ∩ J) ⊆ cl ((⟦A⟧ ∩ J) ⊙ (⦅‼Σ⦆ ∩ J)) *)
      rewrite IH at 1. unfold ph_bang. rewrite cl_prod. apply cl_mono.
      intros m (a & g & [Ha HJa]%elem_of_intersection
                      & [Hg HJg]%elem_of_intersection & Hm)%elem_of_prod.
      apply elem_of_intersection. split.
      + apply elem_of_prod. exists a, g. split_and!; [by apply ph_cl_ext | done..].
      + apply (ph_J_proper (a · g)); [by symmetry | by apply ph_J_op].
  Qed.
End Interp.

(** ** Soundness

    Every derivable sequent is valid. The proof is by induction on the
    derivation. Each case is a short calculation with the inclusions
    above: a right rule builds the conclusion from the premises, and a
    left rule [A :: Γ ⊢ C] reduces [⟦A⟧ ⊙ ⦅Γ⦆] to the generators of
    [⟦A⟧] with [prod_cl_l]. [c] is arbitrary, so this covers the calculus
    with cut and the cut-free calculus alike. *)
Theorem soundness c Γ A : Γ ⊢[c] A -> Γ ⊨ A.
Proof.
  intros H P v.
  induction H; unfold valid_in in *; cbn [interp interp_ctx map] in *.
  - (* ax: ⟦A⟧ ⊙ {ε} ⊆ ⟦A⟧ *)
    rewrite prod_comm. apply prod_one_l; [apply interp_fact | done].
  - (* cut: feed the Γ-part into the A-hole of A :: Δ *)
    by rewrite ctx_app, IHill1.
  - (* ex *)
    rewrite <- IHill. apply ctx_perm. by symmetry.
  - (* 𝟙R *)
    apply ph_cl_ext.
  - (* 𝟙L *)
    apply prod_cl_l, prod_one_l; auto using interp_fact.
  - (* ⊗R *)
    rewrite ctx_app, IHill1, IHill2. apply ph_cl_ext.
  - (* ⊗L *)
    apply tensor_l; auto using interp_fact.
  - (* ⊸R *)
    apply lolli_intro. by rewrite prod_comm.
  - (* ⊸L: (A ⊸ B) ⊙ (Γ ⊙ Δ) ⊆ ((A ⊸ B) ⊙ A) ⊙ Δ ⊆ B ⊙ Δ *)
    by rewrite ctx_app, prod_assoc_l, IHill1, lolli_elim by apply interp_fact.
  - (* &R *)
    set_solver.
  - (* &L₁ *)
    by rewrite intersection_subseteq_l.
  - (* &L₂ *)
    by rewrite intersection_subseteq_r.
  - (* ⊤R *)
    intros m _. apply elem_of_top.
  - (* ⊕R₁ *)
    rewrite IHill. etrans; [| apply ph_cl_ext]. set_solver.
  - (* ⊕R₂ *)
    rewrite IHill. etrans; [| apply ph_cl_ext]. set_solver.
  - (* ⊕L: a generator of ⟦A ⊕ B⟧ is in ⟦A⟧ or in ⟦B⟧ *)
    apply prod_cl_l; [apply interp_fact | set_solver].
  - (* 𝟘L: ⟦𝟘⟧ has no generators *)
    apply prod_cl_l; [apply interp_fact | set_solver].
  - (* !R (promotion): the bag for ‼Σ is reusable *)
    rewrite ctx_bangs. apply cl_mono. set_solver.
  - (* !D (dereliction): generators of ⟦!A⟧ are in ⟦A⟧ *)
    apply prod_cl_l; [apply interp_fact |]. by rewrite intersection_subseteq_l.
  - (* !W (weakening) *)
    rewrite bang_weak. apply prod_cl_l, prod_one_l; auto using interp_fact.
  - (* !C (contraction) *)
    rewrite bang_contr. apply tensor_l; auto using interp_fact.
Qed.

(** ** Using the semantics: what ILL cannot prove

    Soundness gives a way to show that a sequent is _not_ derivable: find a
    phase space in which it fails. One small phase space is enough for
    every example below:

    - phases are natural numbers, counting how many resources a bag holds;
    - [·] is [+] and [ε] is [0];
    - [cl] is the identity, so every set is a fact;
    - the reusable phases are [J = {0}]: only the empty bag is free to
      copy or drop;
    - [⊥] denotes [∅].

    Each variable [$p] denotes [{1}], one unit of resource. *)
Definition counting_space : phase_space.
Proof.
  refine (Build_phase_space nat (=) Nat.add 0 (λ X, X) {[ n | n = 0 ]} ∅
            _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  (* the monoid laws are arithmetic; the closure laws are trivial since
     cl is the identity *)
  all: try apply _; intros; unfold equiv, prod_with in *; set_unfold;
    naive_solver lia.
Defined.

Definition one_each : nat -> propset counting_space := λ _, {[ n | n = 1 ]}.

(** In [counting_space], every set membership reduces to arithmetic.
    [count] unfolds the definitions and leaves the arithmetic behind.
    [set_unfold] can expose new redexes of [interp], so it runs a few
    rounds. *)
Ltac count_unfold :=
  cbn [interp interp_ctx counting_space carrier ph_cl ph_op ph_e
       ph_J ph_bot ph_equiv] in *;
  unfold ph_one, ph_tensor, ph_plus, ph_zero, ph_bang, one_each, equiv in *.
Ltac count := do 3 (count_unfold; set_unfold).

Lemma counting_sound {Γ A} : Γ ⊢ A -> ∀ m, m ∈ ⦅Γ⦆one_each -> m ∈ ⟦A⟧one_each.
Proof. intros H. exact (soundness _ _ _ H counting_space one_each). Qed.

(** Every refutation below has the same shape: name a bag [m] that is in
    [⦅Γ⦆] but not in [⟦A⟧]. After [count], both conditions are statements
    about natural numbers. *)
Lemma counting_refute m Γ A :
  m ∈ ⦅Γ⦆one_each -> m ∉ ⟦A⟧one_each -> ¬ (Γ ⊢ A).
Proof. intros Hm HA H. by apply HA, (counting_sound H). Qed.

(** No contraction: one [A] does not give two. The bag [1] is not [2]. *)
Theorem no_contraction : ¬ ([$0] ⊢ $0 ⊗ $0).
Proof. apply (counting_refute 1); count; naive_solver lia. Qed.

(** No weakening: a hypothesis cannot be ignored. The bag [2] is not
    [1]. *)
Theorem no_weakening : ¬ ([$0; $1] ⊢ $0).
Proof. apply (counting_refute 2); count; naive_solver lia. Qed.

(** No free lunch: one euro buys a coffee _or_ a tea, never both. *)
Theorem no_free_lunch : ¬ ([euro] ⊢ coffee ⊗ tea).
Proof.
  unfold euro, coffee, tea. apply (counting_refute 1); count; naive_solver lia.
Qed.

(** [&] is not [⊗]: a choice of [A] or [B] does not give both. *)
Theorem with_is_not_tensor : ¬ ([$0 & $1] ⊢ $0 ⊗ $1).
Proof. apply (counting_refute 1); count; naive_solver lia. Qed.

(** A single resource cannot be promoted to an unlimited supply. The bag
    [1] is not reusable. *)
Theorem no_promotion : ¬ ([$0] ⊢ !$0).
Proof. apply (counting_refute 1); count; naive_solver lia. Qed.

(** Consistency: [𝟘] cannot be proved from nothing. [⟦𝟘⟧ = ∅]. *)
Theorem consistency : ¬ ([] ⊢ 𝟘).
Proof. apply (counting_refute 0); count; naive_solver lia. Qed.

(** The same facts, stated as implications with no hypotheses. In
    [Types/CurryHoward.v] they become statements about which programs
    exist. The empty bag [0] does not turn [1] into [2], nor [2] into
    [1]. *)
Theorem no_duplicator : ¬ ([] ⊢ $0 ⊸ $0 ⊗ $0).
Proof. apply (counting_refute 0); count; naive_solver lia. Qed.

Theorem no_eraser : ¬ ([] ⊢ $0 ⊗ $1 ⊸ $0).
Proof.
  apply (counting_refute 0); count; [done |].
  intros H. enough (2 = 1) by lia. apply H. by exists 1, 1.
Qed.

(** Double-negation elimination fails in ILL. With [⊥ = ∅], the set
    [∼$0 = $0 ⊸ ⊥] is empty, so [∼∼$0] holds of every bag, including
    bags that are not [{1}], such as [5]. [Comparison.v] contrasts this
    with CLL, where [∼∼A ⊢ A] _is_ provable. *)
Theorem no_dne : ¬ ([∼∼$0] ⊢ $0).
Proof.
  apply (counting_refute 5); count; [| lia].
  exists 5, 0. split_and!; [| done..]. intros _ Hf. by apply (Hf 1).
Qed.
