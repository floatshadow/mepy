(** * Classical.Phase: phase semantics and soundness for CLL

    In the intuitionistic semantics ([Intuitionistic/Phase.v]), the
    closure operator [cl] is a free parameter of the model, and [⊥] is just
    one fact among others. Classical phase semantics fixes one set of
    phases instead, the _pole_ [⫫]. Think of it as the set of _balanced_
    situations, where everything produced was also consumed. Every other
    notion is defined from the pole by _orthogonality_:

<<
        X^⊥ = { y | ∀ x ∈ X, x · y ∈ ⫫ }      the "counter-bags" of X
>>

    The closure is then [cl X = X^⊥⊥], and a fact is a set with
    [X^⊥⊥ = X]. Linear negation is literally [^⊥] on sets. That is why
    [A^⊥^⊥ = A] holds classically, while in the intuitionistic semantics
    [∼∼A] can be strictly larger than [A].

    Validity of a two-sided sequent takes a symmetric form. Take a bag for
    each hypothesis and a _counter-bag_ (an element of [⟦B⟧^⊥]) for each
    conclusion. The sequent is valid when the combination of all of them
    always lies in the pole:

<<
        Γ ⊨ Δ   iff   ⟦A₁⟧ ⊙ … ⊙ ⟦Aₙ⟧ ⊙ ⟦B₁⟧^⊥ ⊙ … ⊙ ⟦Bₘ⟧^⊥  ⊆  ⫫
>>

    Moving a formula across [⊢] swaps [⟦B⟧] with [⟦B⟧^⊥]. This is the
    semantic counterpart of the negation rules.

    This file contains classical phase spaces, the interpretation,
    soundness, and countermodels based on resource _balance_. *)

From stdpp Require Export propset.
From LinearLogic.Classical Require Export Sequent.

(** ** Classical phase spaces

    A classical phase space has three components:

    - a commutative monoid [(M, ·, ε)] up to [≡], as in the intuitionistic
      case;
    - a pole [⫫ ⊆ M], closed under [≡];
    - a set [J] of reusable phases. It contains [ε], is closed under [·],
      and its elements can be discarded and duplicated _in front of the
      pole_: if [y ∈ ⫫] then [j · y ∈ ⫫], and if [(j · j) · y ∈ ⫫] then
      [j · y ∈ ⫫].

    The field names start with [cph_], to keep them apart from the
    intuitionistic [ph_] fields. *)
Record cphase_space : Type := {
  ccarrier :> Type;
  cph_equiv : Equiv ccarrier;
  cph_op : ccarrier -> ccarrier -> ccarrier;
  cph_e  : ccarrier;
  cph_pole : propset ccarrier;
  cph_J  : propset ccarrier;

  cph_equivalence : Equivalence (@equiv _ cph_equiv);
  cph_op_proper : Proper (@equiv _ cph_equiv ==> @equiv _ cph_equiv ==>
                          @equiv _ cph_equiv) cph_op;
  cph_assoc  : ∀ x y z, @equiv _ cph_equiv (cph_op x (cph_op y z))
                                           (cph_op (cph_op x y) z);
  cph_comm   : ∀ x y, @equiv _ cph_equiv (cph_op x y) (cph_op y x);
  cph_unit_l : ∀ x, @equiv _ cph_equiv (cph_op cph_e x) x;

  cph_pole_proper : ∀ x y, @equiv _ cph_equiv x y -> x ∈ cph_pole -> y ∈ cph_pole;

  cph_J_proper : ∀ x y, @equiv _ cph_equiv x y -> x ∈ cph_J -> y ∈ cph_J;
  cph_J_unit   : cph_e ∈ cph_J;
  cph_J_op     : ∀ x y, x ∈ cph_J -> y ∈ cph_J -> cph_op x y ∈ cph_J;
  cph_J_weak   : ∀ j y, j ∈ cph_J -> y ∈ cph_pole -> cph_op j y ∈ cph_pole;
  cph_J_contr  : ∀ j y, j ∈ cph_J ->
      cph_op (cph_op j j) y ∈ cph_pole -> cph_op j y ∈ cph_pole;
}.

Arguments cph_op {_}. Arguments cph_e {_}. Arguments cph_pole {_}.
Arguments cph_J {_}. Arguments cph_assoc {_}. Arguments cph_comm {_}.
Arguments cph_unit_l {_}. Arguments cph_pole_proper {_}.
Arguments cph_J_proper {_}. Arguments cph_J_unit {_}. Arguments cph_J_op {_}.
Arguments cph_J_weak {_}. Arguments cph_J_contr {_}.

#[export] Existing Instance cph_equiv.
#[export] Instance cph_equivalence' (P : cphase_space) : Equivalence (≡@{P})
  := cph_equivalence P.
#[export] Instance cph_op_proper' (P : cphase_space)
  : Proper ((≡) ==> (≡) ==> (≡)) (@cph_op P) := cph_op_proper P.

(** *** Notations and set formers *)
Declare Scope cll_phase_scope.
Open Scope cll_phase_scope.

Notation "x · y" := (cph_op x y) (at level 40, left associativity)
  : cll_phase_scope.
Notation "⫫" := cph_pole : cll_phase_scope.

Section SetFormers.
  Context {P : cphase_space}.
  Implicit Types (X Y : propset P) (x y z : P).

  (** [{ε}] up to [≡], the product [X ⊙ Y], and the orthogonal [X^⊥]. *)
  Definition one_set : propset P := {[ z | z ≡ cph_e ]}.
  Definition prod_set X Y : propset P := {[ z | ∃ a b, a ∈ X ∧ b ∈ Y ∧ z ≡ a · b ]}.
  Definition orth X : propset P := {[ y | ∀ x, x ∈ X -> x · y ∈ ⫫ ]}.
  Definition full_set : propset P := {[ _ | True ]}.

  Lemma elem_of_one z : z ∈ one_set ↔ z ≡ cph_e.
  Proof. unfold one_set. by rewrite elem_of_PropSet. Qed.
  Lemma elem_of_prod X Y z : z ∈ prod_set X Y ↔ ∃ a b, a ∈ X ∧ b ∈ Y ∧ z ≡ a · b.
  Proof. unfold prod_set. by rewrite elem_of_PropSet. Qed.
  Lemma elem_of_orth X y : y ∈ orth X ↔ ∀ x, x ∈ X -> x · y ∈ ⫫.
  Proof. unfold orth. by rewrite elem_of_PropSet. Qed.
  Lemma elem_of_full z : z ∈ full_set.
  Proof. unfold full_set. by rewrite elem_of_PropSet. Qed.
End SetFormers.

Infix "⊙" := prod_set (at level 40, left associativity) : cll_phase_scope.
Notation "X ^⊥" := (orth X) (at level 20, format "X ^⊥") : cll_phase_scope.

(** ** The algebra of orthogonality *)
Section Orth.
  Context {P : cphase_space}.
  Implicit Types (X Y Z F R : propset P) (x y z : P).

  Lemma cph_unit_r x : x · cph_e ≡ x.
  Proof. rewrite cph_comm. apply cph_unit_l. Qed.

  Lemma orth_proper X y y' : y ≡ y' -> y ∈ X^⊥ -> y' ∈ X^⊥.
  Proof.
    rewrite !elem_of_orth. intros Hy H x Hx.
    apply (cph_pole_proper (x · y)); [by rewrite Hy | auto].
  Qed.

  Lemma orth_anti X Y : X ⊆ Y -> Y^⊥ ⊆ X^⊥.
  Proof. intros H y. rewrite !elem_of_orth. naive_solver. Qed.

  (** [X ⊆ X^⊥⊥]: every bag is orthogonal to its counter-bags. *)
  Lemma biorth X : X ⊆ X^⊥^⊥.
  Proof.
    intros x Hx. apply elem_of_orth. intros y Hy. rewrite elem_of_orth in Hy.
    apply (cph_pole_proper (x · y)); [apply cph_comm | auto].
  Qed.

  Lemma triorth X : X^⊥^⊥^⊥ ⊆ X^⊥.
  Proof. apply orth_anti, biorth. Qed.

  Lemma biorth_mono X Y : X ⊆ Y -> X^⊥^⊥ ⊆ Y^⊥^⊥.
  Proof. intros H. by apply orth_anti, orth_anti. Qed.

  (** A _fact_ is a set equal to its biorthogonal. *)
  Definition fact F : Prop := F^⊥^⊥ ⊆ F.

  Lemma fact_orth X : fact (X^⊥).
  Proof. apply triorth. Qed.

  Lemma fact_inter X Y : fact X -> fact Y -> fact (X ∩ Y).
  Proof.
    intros HX HY z Hz. apply elem_of_intersection.
    split; [apply HX | apply HY]; revert z Hz; apply biorth_mono; set_solver.
  Qed.

  Lemma fact_full : fact full_set.
  Proof. intros z _. apply elem_of_full. Qed.

  Lemma fact_proper F x y : fact F -> x ≡ y -> x ∈ F -> y ∈ F.
  Proof. intros HF Hxy Hx. apply HF. apply (orth_proper _ x); [done | by apply biorth]. Qed.

  (** The key adjunction: [X ⊙ Y ⊆ ⫫] iff [Y ⊆ X^⊥]. *)
  Lemma prod_pole X Y : X ⊙ Y ⊆ ⫫ ↔ Y ⊆ X^⊥.
  Proof.
    split.
    - intros H y Hy. apply elem_of_orth. intros x Hx. apply H, elem_of_prod. by exists x, y.
    - intros H z (a & b & Ha & Hb & Hz)%elem_of_prod.
      apply (cph_pole_proper (a · b)); [by symmetry |].
      specialize (H b Hb). rewrite elem_of_orth in H. auto.
  Qed.

  Lemma prod_mono X X' Y Y' : X ⊆ X' -> Y ⊆ Y' -> X ⊙ Y ⊆ X' ⊙ Y'.
  Proof.
    intros HX HY z (a & b & Ha & Hb & Hz)%elem_of_prod.
    apply elem_of_prod. exists a, b. auto.
  Qed.

  Lemma prod_assoc_l X Y Z : X ⊙ (Y ⊙ Z) ⊆ (X ⊙ Y) ⊙ Z.
  Proof.
    intros z (a & w & Ha & (b & c & Hb & Hc & Hw)%elem_of_prod & Hz)%elem_of_prod.
    apply elem_of_prod. exists (a · b), c. rewrite elem_of_prod. split_and!; auto.
    - by exists a, b.
    - rewrite Hz, Hw. apply cph_assoc.
  Qed.

  Lemma prod_assoc_r X Y Z : (X ⊙ Y) ⊙ Z ⊆ X ⊙ (Y ⊙ Z).
  Proof.
    intros z (w & c & (a & b & Ha & Hb & Hw)%elem_of_prod & Hc & Hz)%elem_of_prod.
    apply elem_of_prod. exists a, (b · c). rewrite elem_of_prod. split_and!; auto.
    - by exists b, c.
    - rewrite Hz, Hw. symmetry. apply cph_assoc.
  Qed.

  Lemma prod_comm X Y : X ⊙ Y ⊆ Y ⊙ X.
  Proof.
    intros z (a & b & Ha & Hb & Hz)%elem_of_prod. apply elem_of_prod.
    exists b, a. split_and!; auto. by rewrite Hz, cph_comm.
  Qed.

  Lemma prod_one_r F : fact F -> F ⊙ one_set ⊆ F.
  Proof.
    intros HF z (a & b & Ha & Hb%elem_of_one & Hz)%elem_of_prod.
    apply (fact_proper _ a); [done | | done]. by rewrite Hz, Hb, cph_unit_r.
  Qed.

  Lemma prod_one_l X : X ⊆ one_set ⊙ X.
  Proof.
    intros x Hx. apply elem_of_prod. exists cph_e, x.
    rewrite elem_of_one, cph_unit_l. done.
  Qed.

  (** Stability: [X^⊥⊥ ⊙ Y^⊥⊥ ⊆ (X ⊙ Y)^⊥⊥]. In the intuitionistic
      semantics this was an axiom about [cl]. Here it follows from the
      definition of [^⊥]. *)
  Lemma stability X Y : X^⊥^⊥ ⊙ Y^⊥^⊥ ⊆ (X ⊙ Y)^⊥^⊥.
  Proof.
    intros z (a & b & Ha & Hb & Hz)%elem_of_prod. apply elem_of_orth.
    intros w Hw. rewrite elem_of_orth in Hw.
    (* first: for y ∈ Y, y · w is a counter-bag of X *)
    assert (H1 : ∀ y, y ∈ Y -> y · w ∈ X^⊥).
    { intros y Hy. apply elem_of_orth. intros x Hx.
      apply (cph_pole_proper ((x · y) · w)); [symmetry; apply cph_assoc |].
      apply Hw, elem_of_prod. by exists x, y. }
    (* then: w · a is a counter-bag of Y *)
    assert (H2 : w · a ∈ Y^⊥).
    { apply elem_of_orth. intros y Hy.
      rewrite elem_of_orth in Ha. specialize (Ha _ (H1 y Hy)).
      apply (cph_pole_proper ((y · w) · a)); [symmetry; apply cph_assoc | done]. }
    rewrite elem_of_orth in Hb. specialize (Hb _ H2).
    apply (cph_pole_proper ((w · a) · b)); [| done].
    rewrite Hz. symmetry. apply cph_assoc.
  Qed.

  Lemma orth_union X Y : X^⊥ ∩ Y^⊥ ⊆ (X ∪ Y)^⊥.
  Proof.
    intros z [HX HY]%elem_of_intersection. rewrite elem_of_orth in HX, HY.
    apply elem_of_orth. intros x [Hx | Hx]%elem_of_union; auto.
  Qed.

  Lemma pole_orth_one R : R ⊆ ⫫ -> R ⊆ one_set^⊥.
  Proof.
    intros H r Hr. apply elem_of_orth. intros x Hx%elem_of_one.
    apply (cph_pole_proper r); [by rewrite Hx, cph_unit_l | auto].
  Qed.

  Lemma cut_pole R1 R2 X : R1 ⊆ X -> R2 ⊆ X^⊥ -> R1 ⊙ R2 ⊆ ⫫.
  Proof.
    intros H1 H2. etransitivity; [by apply prod_mono |]. by apply prod_pole.
  Qed.

  (** *** Reusable phases *)

  (** Weakening: anything in the pole stays there after a reusable phase
      is added. *)
  Lemma weak_orth R X : R ⊆ ⫫ -> R ⊆ (X ∩ cph_J)^⊥.
  Proof.
    intros H r Hr. apply elem_of_orth. intros j [_ Hj]%elem_of_intersection.
    by apply cph_J_weak, H.
  Qed.

  (** Contraction: a reusable phase that may be used twice may be used
      once. *)
  Lemma contr_orth R X :
    R ⊆ ((X ∩ cph_J)^⊥^⊥ ⊙ (X ∩ cph_J)^⊥^⊥)^⊥ -> R ⊆ (X ∩ cph_J)^⊥.
  Proof.
    intros H r Hr. apply elem_of_orth. intros j Hj.
    pose proof Hj as [_ HJ]%elem_of_intersection.
    apply cph_J_contr; [done |].
    specialize (H r Hr). rewrite elem_of_orth in H. apply H, elem_of_prod.
    exists j, j. split_and!; [by apply biorth | by apply biorth | done].
  Qed.

  (** [X] is _[J]-generated_ when it is included in the biorthogonal of its
      reusable part. Promotion needs every formula in the context to be
      [J]-generated. *)
  Definition jgen X : Prop := X ⊆ (X ∩ cph_J)^⊥^⊥.

  Lemma jgen_biorth Y : jgen ((Y ∩ cph_J)^⊥^⊥).
  Proof.
    apply biorth_mono. intros x [Hx HJ]%elem_of_intersection.
    apply elem_of_intersection. split; [by apply biorth | done].
  Qed.
End Orth.

(** ** Big products

    [⨀ [X₁; …; Xₙ] = X₁ ⊙ … ⊙ Xₙ ⊙ {ε}]. *)
Fixpoint bigprod {P : cphase_space} (L : list (propset P)) : propset P :=
  match L with
  | [] => one_set
  | X :: L => X ⊙ bigprod L
  end.
Notation "⨀ L" := (bigprod L) (at level 30) : cll_phase_scope.

Section BigProd.
  Context {P : cphase_space}.
  Implicit Types (L : list (propset P)).

  Lemma bigprod_perm L L' : L ≡ₚ L' -> ⨀ L ⊆ ⨀ L'.
  Proof.
    induction 1 as [| X L L' _ IH | X Y L | L L' L'' _ IH1 _ IH2]; simpl.
    - done.
    - by apply prod_mono.
    - etransitivity; [apply prod_assoc_l |].
      etransitivity; [apply prod_mono; [apply prod_comm | done] |].
      apply prod_assoc_r.
    - by etransitivity.
  Qed.

  Lemma bigprod_app L1 L2 : ⨀ (L1 ++ L2) ⊆ ⨀ L1 ⊙ ⨀ L2.
  Proof.
    induction L1 as [| X L1 IH]; simpl.
    - apply prod_one_l.
    - etransitivity; [by apply prod_mono |]. apply prod_assoc_l.
  Qed.

  (** A big product of [J]-generated sets is [J]-generated. *)
  Lemma bigprod_jgen L : Forall jgen L -> jgen (⨀ L).
  Proof.
    induction 1 as [| X L HX _ IH]; simpl; unfold jgen in *.
    - intros z Hz. apply biorth, elem_of_intersection. split; [done |].
      apply elem_of_one in Hz. apply (cph_J_proper cph_e); [by symmetry | apply cph_J_unit].
    - etransitivity; [by apply prod_mono |].
      etransitivity; [apply stability |]. apply biorth_mono.
      intros z (a & b & [Ha HJa]%elem_of_intersection
                      & [Hb HJb]%elem_of_intersection & Hz)%elem_of_prod.
      apply elem_of_intersection. split.
      + apply elem_of_prod. by exists a, b.
      + apply (cph_J_proper (a · b)); [by symmetry | by apply cph_J_op].
  Qed.
End BigProd.

(** ** Interpreting formulas and sequents

    The classical interpretation, connective by connective. Compare it
    with the intuitionistic one. Each [cl] has become [^⊥⊥], and each
    dual pair is related by [^⊥]:

<<
      $p     ↦ (v p)^⊥⊥             A^⊥    ↦ ⟦A⟧^⊥
      𝟙      ↦ {ε}^⊥⊥               ⊥      ↦ {ε}^⊥
      A ⊗ B  ↦ (⟦A⟧ ⊙ ⟦B⟧)^⊥⊥       A ⅋ B  ↦ (⟦A⟧^⊥ ⊙ ⟦B⟧^⊥)^⊥
      A & B  ↦ ⟦A⟧ ∩ ⟦B⟧            A ⊕ B  ↦ (⟦A⟧ ∪ ⟦B⟧)^⊥⊥
      ⊤      ↦ M                    𝟘      ↦ ∅^⊥⊥
      !A     ↦ (⟦A⟧ ∩ J)^⊥⊥         ? A    ↦ (⟦A⟧^⊥ ∩ J)^⊥
>>
*)
Fixpoint interp {P : cphase_space} (v : nat -> propset P) (A : cformula)
  : propset P :=
  match A with
  | CAtom p     => (v p)^⊥^⊥
  | CNeg A      => (interp v A)^⊥
  | COne        => one_set^⊥^⊥
  | CBot        => one_set^⊥
  | CTop        => full_set
  | CZero       => (∅ : propset P)^⊥^⊥
  | CTensor A B => (interp v A ⊙ interp v B)^⊥^⊥
  | CPar A B    => ((interp v A)^⊥ ⊙ (interp v B)^⊥)^⊥
  | CWith A B   => interp v A ∩ interp v B
  | CPlus A B   => (interp v A ∪ interp v B)^⊥^⊥
  | CBang A     => (interp v A ∩ cph_J)^⊥^⊥
  | CWhy A      => ((interp v A)^⊥ ∩ cph_J)^⊥
  end.

Notation "⟦ A ⟧ v" := (interp v A)
  (at level 1, A at level 200, v at level 1, format "⟦ A ⟧ v")
  : cll_phase_scope.

(** A sequent becomes a list of sets: [⟦A⟧] for each hypothesis and
    [⟦B⟧^⊥] for each conclusion. *)
Definition sq {P : cphase_space} (v : nat -> propset P) (Γ Δ : list cformula)
  : list (propset P) :=
  map (interp v) Γ ++ map (λ B, (interp v B)^⊥) Δ.

Definition valid_in {P : cphase_space} (v : nat -> propset P) Γ Δ : Prop :=
  ⨀ (sq v Γ Δ) ⊆ ⫫.

Definition valid (Γ Δ : list cformula) : Prop :=
  ∀ (P : cphase_space) (v : nat -> propset P), valid_in v Γ Δ.

Notation "Γ ⊨ Δ" := (valid Γ Δ) (at level 80, no associativity)
  : cll_phase_scope.

Section Sequents.
  Context {P : cphase_space} (v : nat -> propset P).
  Implicit Types (R : propset P).

  Lemma interp_fact A : fact (⟦A⟧v).
  Proof. induction A; simpl; auto using fact_orth, fact_inter, fact_full. Qed.

  (** A hypothesis [A] at the head: its bag must be orthogonal to the
      rest. *)
  Lemma valid_l A Γ Δ : valid_in v (A :: Γ) Δ ↔ ⨀ (sq v Γ Δ) ⊆ (⟦A⟧v)^⊥.
  Proof. apply prod_pole. Qed.

  Lemma sq_cons_r B Γ Δ : sq v Γ (B :: Δ) ≡ₚ (⟦B⟧v)^⊥ :: sq v Γ Δ.
  Proof. unfold sq. simpl. by rewrite Permutation_middle. Qed.

  (** A conclusion [B] at the head: the rest must land in [⟦B⟧]. *)
  Lemma valid_r B Γ Δ : valid_in v Γ (B :: Δ) ↔ ⨀ (sq v Γ Δ) ⊆ ⟦B⟧v.
  Proof.
    unfold valid_in. split.
    - intros H. etransitivity; [| apply interp_fact].
      apply prod_pole. etransitivity; [| exact H].
      apply (bigprod_perm ((⟦B⟧v)^⊥ :: sq v Γ Δ)). by rewrite sq_cons_r.
    - intros H. etransitivity; [apply bigprod_perm, sq_cons_r |]. simpl.
      apply prod_pole. etransitivity; [exact H | apply biorth].
  Qed.

  Lemma valid_ll A B Γ Δ :
    valid_in v (A :: B :: Γ) Δ ↔ ⨀ (sq v Γ Δ) ⊆ (⟦A⟧v ⊙ ⟦B⟧v)^⊥.
  Proof.
    unfold valid_in. simpl. split; intros H.
    - apply prod_pole. etransitivity; [apply prod_assoc_r | exact H].
    - apply prod_pole in H. etransitivity; [apply prod_assoc_l | exact H].
  Qed.

  Lemma valid_rr A B Γ Δ :
    valid_in v Γ (A :: B :: Δ) ↔ ⨀ (sq v Γ Δ) ⊆ ((⟦A⟧v)^⊥ ⊙ (⟦B⟧v)^⊥)^⊥.
  Proof.
    assert (Hp : sq v Γ (A :: B :: Δ) ≡ₚ (⟦A⟧v)^⊥ :: (⟦B⟧v)^⊥ :: sq v Γ Δ).
    { unfold sq. simpl. solve_Permutation. }
    unfold valid_in. split; intros H.
    - apply prod_pole. etransitivity; [apply prod_assoc_r |].
      etransitivity; [apply (bigprod_perm _ _ (symmetry Hp)) | exact H].
    - apply prod_pole in H. etransitivity; [apply (bigprod_perm _ _ Hp) |]. simpl.
      etransitivity; [apply prod_assoc_l | exact H].
  Qed.

  Lemma valid_split Γ₁ Γ₂ Δ₁ Δ₂ :
    ⨀ (sq v (Γ₁ ++ Γ₂) (Δ₁ ++ Δ₂)) ⊆ ⨀ (sq v Γ₁ Δ₁) ⊙ ⨀ (sq v Γ₂ Δ₂).
  Proof.
    etransitivity; [| apply bigprod_app]. apply bigprod_perm.
    unfold sq. rewrite !map_app. solve_Permutation.
  Qed.

  Lemma valid_perm Γ Γ' Δ Δ' :
    Γ ≡ₚ Γ' -> Δ ≡ₚ Δ' -> valid_in v Γ Δ -> valid_in v Γ' Δ'.
  Proof.
    intros HΓ HΔ H. unfold valid_in. etransitivity; [| exact H].
    apply bigprod_perm. unfold sq. by rewrite HΓ, HΔ.
  Qed.

  (** The context of a promotion is [J]-generated. *)
  Lemma promo Σ Π : ⨀ (sq v (‼Σ) (⁇Π)) ⊆ (⨀ (sq v (‼Σ) (⁇Π)) ∩ cph_J)^⊥^⊥.
  Proof.
    apply bigprod_jgen. unfold sq. rewrite !map_map.
    apply Forall_app; split; apply Forall_forall;
      intros X (B & <- & _)%list_elem_of_In%in_map_iff; simpl; apply jgen_biorth.
  Qed.
End Sequents.

(** ** Soundness

    Each case unfolds the sequent with [valid_l] / [valid_r] and then
    reasons about orthogonals. The negation rules are almost trivial,
    which is the point of the classical semantics. *)
Theorem soundness c Γ Δ : Γ ⊢[c] Δ -> Γ ⊨ Δ.
Proof.
  intros H P v.
  induction H.
  - (* ax *)
    apply valid_l. unfold sq. simpl. apply prod_one_r, fact_orth.
  - (* cut *)
    apply valid_r in IHcll1. apply valid_l in IHcll2.
    unfold valid_in. etransitivity; [apply valid_split | by eapply cut_pole].
  - (* ex *)
    by eapply valid_perm.
  - (* negL *)
    apply valid_l. apply valid_r in IHcll. simpl.
    etransitivity; [exact IHcll | apply biorth].
  - (* negR *)
    apply valid_r. by apply valid_l in IHcll.
  - (* 𝟙L *)
    apply valid_l. simpl. etransitivity; [by apply pole_orth_one | apply biorth].
  - (* 𝟙R *)
    apply valid_r. unfold sq. simpl. apply biorth.
  - (* ⊥L *)
    apply valid_l. unfold sq. simpl. apply biorth.
  - (* ⊥R *)
    apply valid_r. simpl. by apply pole_orth_one.
  - (* ⊗L *)
    apply valid_l. apply valid_ll in IHcll. simpl.
    etransitivity; [exact IHcll | apply biorth].
  - (* ⊗R *)
    apply valid_r in IHcll1, IHcll2. apply valid_r. simpl.
    etransitivity; [apply valid_split |].
    etransitivity; [by apply prod_mono | apply biorth].
  - (* ⅋L *)
    apply valid_l in IHcll1, IHcll2. apply valid_l. simpl.
    etransitivity; [apply valid_split |].
    etransitivity; [by apply prod_mono | apply biorth].
  - (* ⅋R *)
    apply valid_r. by apply valid_rr in IHcll.
  - (* &L₁ *)
    apply valid_l. apply valid_l in IHcll. simpl.
    etransitivity; [exact IHcll | apply orth_anti; set_solver].
  - (* &L₂ *)
    apply valid_l. apply valid_l in IHcll. simpl.
    etransitivity; [exact IHcll | apply orth_anti; set_solver].
  - (* &R *)
    apply valid_r in IHcll1, IHcll2. apply valid_r. simpl. set_solver.
  - (* ⊤R *)
    apply valid_r. intros z _. apply elem_of_full.
  - (* ⊕L *)
    apply valid_l in IHcll1, IHcll2. apply valid_l. simpl.
    etransitivity; [| apply biorth].
    intros z Hz. apply orth_union, elem_of_intersection. auto.
  - (* ⊕R₁ *)
    apply valid_r in IHcll. apply valid_r. simpl.
    etransitivity; [| apply biorth]. set_solver.
  - (* ⊕R₂ *)
    apply valid_r in IHcll. apply valid_r. simpl.
    etransitivity; [| apply biorth]. set_solver.
  - (* 𝟘L: ∅^⊥ is everything *)
    apply valid_l. simpl. etransitivity; [| apply biorth].
    intros z _. apply elem_of_orth. set_solver.
  - (* !D *)
    apply valid_l. apply valid_l in IHcll. simpl.
    etransitivity; [exact IHcll |].
    etransitivity; [apply (orth_anti (⟦A⟧v ∩ cph_J)); set_solver | apply biorth].
  - (* !W *)
    apply valid_l. simpl. etransitivity; [by apply weak_orth | apply biorth].
  - (* !C *)
    apply valid_l. apply valid_ll in IHcll. simpl in *.
    etransitivity; [by apply contr_orth | apply biorth].
  - (* !R *)
    apply valid_r in IHcll. apply valid_r. simpl.
    etransitivity; [apply promo |]. apply biorth_mono. set_solver.
  - (* ?D *)
    apply valid_r in IHcll. apply valid_r. simpl.
    etransitivity; [exact IHcll |].
    etransitivity; [apply biorth | apply orth_anti; set_solver].
  - (* ?W *)
    apply valid_r. simpl. by apply weak_orth.
  - (* ?C *)
    apply valid_r. apply valid_rr in IHcll. simpl in *. by apply contr_orth.
  - (* ?L *)
    apply valid_l in IHcll. apply valid_l. simpl.
    etransitivity; [apply promo |]. apply biorth_mono. set_solver.
Qed.

(** ** Using the semantics: balance

    One family of models covers all the counterexamples. Phases are
    integers, [·] is [+], and [J = {0}]. The pole is a parameter.

    With the pole [{0}], an atom denotes [{1}], one unit of supply, and
    its negation denotes [{-1}], one unit of demand. A sequent is valid
    only if _the books balance_: total supply on the left equals total
    supply on the right. *)
Definition int_space (pole : propset Z) : cphase_space.
Proof.
  refine (Build_cphase_space Z (=) Z.add 0%Z pole {[ z | z = 0%Z ]}
            _ _ _ _ _ _ _ _ _ _ _).
  all: try apply _; intros; unfold equiv in *; set_unfold;
    repeat match goal with H : _ ∧ _ |- _ => destruct H end; subst;
    rewrite ?Z.add_0_l, ?Z.add_0_r in *; try done; lia.
Defined.

Definition one_each {pole} : nat -> propset (int_space pole) :=
  λ _, {[ z | z = 1%Z ]}.

(** The balance model: the pole is [{0}]. *)
Definition balance_space : cphase_space := int_space {[ z | z = 0%Z ]}.

(** Every variable denotes [{1}]: one unit of supply. *)
Definition bval : nat -> propset balance_space := λ _, {[ z | z = 1%Z ]}.

(** [denotes A n]: in the balance model, [A] denotes exactly [{n}]. *)
Definition denotes (A : cformula) (n : Z) : Prop :=
  ∀ z : balance_space, z ∈ ⟦A⟧bval ↔ z = n.

Section Balance.
  Notation M := balance_space.
  Implicit Types (X Y : propset M) (z : M).

  Lemma single_orth X (n : Z) : (∀ z, z ∈ X ↔ z = n) -> ∀ z, z ∈ X^⊥ ↔ z = (- n)%Z.
  Proof.
    intros HX z. rewrite elem_of_orth. split.
    - intros H. specialize (H n (proj2 (HX n) eq_refl)).
      cbn in H. set_unfold. lia.
    - intros -> x Hx%HX. cbn. set_unfold. lia.
  Qed.

  Lemma single_prod X Y (n m : Z) :
    (∀ z, z ∈ X ↔ z = n) -> (∀ z, z ∈ Y ↔ z = m) -> ∀ z, z ∈ X ⊙ Y ↔ z = (n + m)%Z.
  Proof.
    intros HX HY z. rewrite elem_of_prod. split.
    - intros (a & b & ->%HX & ->%HY & Hz). exact Hz.
    - intros ->. exists n, m. rewrite HX, HY. done.
  Qed.

  Lemma denotes_atom p : denotes ($p) 1.
  Proof.
    assert (H : ∀ z, z ∈ bval p ↔ z = 1%Z).
    { intros z. unfold bval. by rewrite elem_of_PropSet. }
    intros z. cbn [interp]. rewrite (single_orth _ _ (single_orth _ _ H)). lia.
  Qed.

  Lemma denotes_neg A n : denotes A n -> denotes (A^⊥) (- n).
  Proof. intros H z. exact (single_orth _ _ H z). Qed.

  Lemma denotes_tensor A B n m :
    denotes A n -> denotes B m -> denotes (A ⊗ B) (n + m).
  Proof.
    intros HA HB z. cbn [interp].
    rewrite (single_orth _ _ (single_orth _ _ (single_prod _ _ _ _ HA HB))). lia.
  Qed.

  Lemma denotes_par A B n m :
    denotes A n -> denotes B m -> denotes (A ⅋ B) (n + m).
  Proof.
    intros HA HB z. cbn [interp].
    rewrite (single_orth _ _ (single_prod _ _ _ _ (single_orth _ _ HA)
                                                   (single_orth _ _ HB))). lia.
  Qed.

  Lemma denotes_with A B n : denotes A n -> denotes B n -> denotes (A & B) n.
  Proof. intros HA HB z. cbn [interp]. rewrite elem_of_intersection, (HA z), (HB z). naive_solver. Qed.

  (** A list of singletons multiplies to the singleton of the sum. *)
  Lemma bigprod_sum (L : list (propset M)) (ns : list Z) :
    Forall2 (λ X n, ∀ z, z ∈ X ↔ z = n) L ns -> (foldr Z.add 0%Z ns : M) ∈ ⨀ L.
  Proof.
    induction 1 as [| X n L ns HX _ IH]; cbn [foldr bigprod].
    - by apply elem_of_one.
    - apply elem_of_prod. exists n, (foldr Z.add 0%Z ns : M). by rewrite HX.
  Qed.

  Lemma sum_init k (l : list Z) : foldr Z.add k l = (k + foldr Z.add 0 l)%Z.
  Proof. induction l; simpl; lia. Qed.

  Lemma sum_opp (l : list Z) : foldr Z.add 0%Z (map Z.opp l) = (- foldr Z.add 0 l)%Z.
  Proof. induction l; simpl; lia. Qed.

  (** The balance theorem: in a provable sequent whose formulas all have
      weights, the supply on the left equals the supply on the right. *)
  Theorem balance Γ Δ (ns ms : list Z) :
    Γ ⊢ Δ -> Forall2 denotes Γ ns -> Forall2 denotes Δ ms ->
    foldr Z.add 0%Z ns = foldr Z.add 0%Z ms.
  Proof.
    intros H HΓ HΔ.
    pose proof (soundness _ _ _ H M bval) as S. unfold valid_in in S.
    enough (Hsum : (foldr Z.add 0%Z (ns ++ map Z.opp ms) : M) ∈ ⨀ (sq bval Γ Δ)).
    { apply S in Hsum. cbn [cph_pole balance_space int_space] in Hsum.
      set_unfold in Hsum.
      rewrite foldr_app, sum_init, sum_opp in Hsum. lia. }
    apply bigprod_sum. unfold sq. apply Forall2_app.
    - apply Forall2_fmap_l. exact HΓ.
    - apply Forall2_fmap. eapply Forall2_impl; [exact HΔ |].
      intros B m HB. by apply single_orth.
  Qed.
End Balance.

(** [weigh] proves the [Forall2 denotes] side conditions of [balance],
    computing each weight as it goes. It dispatches on the shape of the
    formula, so it never asks Rocq to unify two different connectives
    (which would unfold [denotes] and [interp] and take forever). *)
Ltac weigh :=
  repeat match goal with
  | |- Forall2 _ _ _ => constructor
  | |- denotes ($ _) _ => apply denotes_atom
  | |- denotes (_^⊥) _ => apply denotes_neg
  | |- denotes (_ ⊗ _) _ => apply denotes_tensor
  | |- denotes (_ ⅋ _) _ => apply denotes_par
  | |- denotes (_ & _) _ => apply denotes_with
  end.

(** [refute_by_balance] applies [balance] with weights left to [weigh],
    then checks that the two sums differ. *)
Ltac refute_by_balance :=
  intros H; eapply balance in H; [| weigh | weigh]; simpl in H; lia.

(** No contraction: supply 1 ≠ demand 2. *)
Theorem no_contraction : ¬ ([$0] ⊢ [$0 ⊗ $0]).
Proof. refute_by_balance. Qed.

(** No weakening: supply 2 ≠ demand 1. *)
Theorem no_weakening : ¬ ([$0; $1] ⊢ [$0]).
Proof. refute_by_balance. Qed.

(** [&] is not [⊗]: [$0 & $1] weighs 1 (both components are offered,
    only one is used), [$0 ⊗ $1] weighs 2. *)
Theorem with_is_not_tensor : ¬ ([$0 & $1] ⊢ [$0 ⊗ $1]).
Proof. refute_by_balance. Qed.

(** No duplicator: [$0 ⊸ $0 ⊗ $0], i.e. [$0^⊥ ⅋ ($0 ⊗ $0)], has weight
    [-1 + 2 = 1], but the empty left side supplies nothing. *)
Theorem no_duplicator : ¬ ([] ⊢ [$0 ⊸ $0 ⊗ $0]).
Proof. refute_by_balance. Qed.

(** No eraser: [$0 ⊗ $1 ⊸ $0] has weight [-2 + 1 = -1]. *)
Theorem no_eraser : ¬ ([] ⊢ [$0 ⊗ $1 ⊸ $0]).
Proof. refute_by_balance. Qed.

(** Balance is necessary but not sufficient. [[$0 ⅋ $1] ⊢ [$0 ⊗ $1]]
    balances, since both sides weigh 2, yet it is not provable without
    the extra MIX rule ([Γ₁ ⊢ Δ₁] and [Γ₂ ⊢ Δ₂] give [Γ₁,Γ₂ ⊢ Δ₁,Δ₂]).
    The balance model cannot tell the two formulas apart: *)
Example par_tensor_balance :
  denotes ($0 ⅋ $1) (1 + 1) ∧ denotes ($0 ⊗ $1) (1 + 1).
Proof. split; weigh. Qed.

(** ** Consistency

    The pole [∅] gives a different model, in which nothing is balanced.
    The empty sequent [⊢] is the classical "contradiction", and in this
    model it is invalid: the empty product [{0}] is not inside [∅]. *)
Theorem consistency : ¬ ([] ⊢ []).
Proof.
  intros H. apply (not_elem_of_empty (C := propset Z) 0%Z).
  apply (soundness _ _ _ H (int_space ∅) one_each). by apply elem_of_one.
Qed.

(** As a consequence, neither [⊥] nor [𝟘] is provable: cut either one
    against its left rule to get [⊢]. *)
Corollary bot_unprovable : ¬ ([] ⊢ [⊥]).
Proof. intros H. apply consistency, (cut _ [] [] [] [] ⊥); [done | exact H | apply botL]. Qed.

Corollary zero_unprovable : ¬ ([] ⊢ [𝟘]).
Proof. intros H. apply consistency, (cut _ [] [] [] [] 𝟘); [done | exact H | apply zeroL]. Qed.
