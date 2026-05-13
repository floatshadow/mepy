From Stdlib Require Import Logic.Classical_Prop.
From Stdlib Require Import Lists.List.

Import ListNotations.

Set Implicit Arguments.
Set Universe Polymorphism.

Declare Scope modal_scope.
Delimit Scope modal_scope with modal.

(*
  System T is the normal modal logic K plus the reflexivity axiom:

      □ φ ⟶ φ

  This file is meant to be read beside ModalK.v and ModalD.v.

  The comparison with System K is the main point:

  - Syntax: exactly the same formulas as K.
  - Rules: exactly the same rules as K, plus one axiom schema ax_T.
  - Semantics: K quantifies over arbitrary Kripke frames; T quantifies only
    over reflexive Kripke frames, where every world can see itself.
  - Soundness: every K soundness case is reused unchanged. The only new case
    is ax_T_sound, and the only new semantic fact it needs is reflexivity.

  We keep the syntax small: atoms, falsity, implication, and box.
  Negation, diamond, and other connectives can be defined from these.
*)
Inductive formula (Atom : Type) : Type :=
| atom : Atom -> formula Atom
| falsum : formula Atom
| imply : formula Atom -> formula Atom -> formula Atom
| box : formula Atom -> formula Atom.

Arguments atom {Atom} _.
Arguments falsum {Atom}.
Arguments imply {Atom} _ _.
Arguments box {Atom} _.

Notation "⊥" := falsum : modal_scope.
Notation "# p" := (atom p) (at level 1, format "# p") : modal_scope.
Infix "⟶" := imply (at level 90, right associativity) : modal_scope.
Notation "¬ φ" := (imply φ falsum) (at level 75, right associativity) : modal_scope.
Notation "□ φ" := (box φ) (at level 75, right associativity) : modal_scope.
Notation "◇ φ" := (imply (box (imply φ falsum)) falsum)
  (at level 75, right associativity) : modal_scope.
Notation "xs ∋ x" := (In x xs) (at level 70, no associativity) : modal_scope.

(*
  The diamond notation is an abbreviation, not a new constructor:

      ◇ φ  means  ¬ □ ¬ φ

  This keeps the language identical to Systems K and D. System T is stronger
  because of its additional axiom and frame condition, not because it has more
  syntax.
*)

Open Scope modal_scope.

Section ProofSystem.
  Context {Atom : Type}.

  Reserved Notation "Γ ⊢ φ" (at level 99, φ at next level).

(*
  Hilbert-style derivability for T.

  Γ ⊢ φ means that φ is derivable from assumptions Γ.
  The three ax_prop rules form a classical implicational basis.

  Up through ax_K, this is the same proof system as System K. The K axiom says
  that box distributes over implication:

      □ (φ ⟶ ψ) ⟶ □ φ ⟶ □ ψ

  What T adds is ax_T:

      □ φ ⟶ φ

  Intuitively, if φ is necessary, then φ is actually true. This is not valid
  on arbitrary K frames: a world might fail to access itself, so □ φ can speak
  only about other worlds and say nothing about the current one. System T rules
  out exactly that situation by requiring reflexivity in the semantics.

  The inference rules are modus ponens and necessitation. Necessitation is
  restricted to theorems: to derive □ φ under any Γ, φ must first be
  derivable from the empty context.
*)
  Inductive proves : list (formula Atom) -> formula Atom -> Prop :=
  | by_hyp Γ φ :
      Γ ∋ φ ->
      Γ ⊢ φ
  | ax_prop₁ Γ φ ψ :
      Γ ⊢ φ ⟶ ψ ⟶ φ
  | ax_prop₂ Γ φ ψ χ :
      Γ ⊢ (φ ⟶ ψ ⟶ χ) ⟶ (φ ⟶ ψ) ⟶ φ ⟶ χ
  | ax_prop₃ Γ φ ψ :
      Γ ⊢ (¬ ψ ⟶ ¬ φ) ⟶ φ ⟶ ψ
  | ax_K Γ φ ψ :
      Γ ⊢ □ (φ ⟶ ψ) ⟶ □ φ ⟶ □ ψ
  | ax_T Γ φ :
      Γ ⊢ □ φ ⟶ φ
  | mp Γ φ ψ :
      Γ ⊢ φ ⟶ ψ ->
      Γ ⊢ φ ->
      Γ ⊢ ψ
  | nec Γ φ :
      [] ⊢ φ ->
      Γ ⊢ □ φ
  where "Γ ⊢ φ" := (proves Γ φ) : modal_scope.
End ProofSystem.

Notation "Γ ⊢ φ" := (proves Γ φ)
  (at level 99, φ at next level) : modal_scope.
Notation "⊢ φ" := ([] ⊢ φ)
  (at level 99, φ at next level) : modal_scope.

Section KripkeSemantics.
  Context {Atom : Type}.

(*
  Kripke models for T use reflexive frames.

  World     : the type of possible worlds
  access    : accessibility relation between worlds
  reflexive : every world is accessible from itself
  val       : valuation of atoms at worlds

  This is the semantic difference from System K. A K model has World, access,
  and val, with no condition on access. A T model adds:

      reflexive : forall w, access w w

  So every T model is K-like, but not every K model is a T model. The excluded
  K models are precisely those where some world cannot see itself. Those are
  exactly the frames where the T axiom can fail.
*)
  Record model : Type := {
    World : Type;
    access : World -> World -> Prop;
    reflexive : forall w : World, access w w;
    val : World -> Atom -> Prop;
  }.

  Notation "w ↝[ M ] v" := (access M w v)
    (at level 70, M at next level, v at next level) : modal_scope.

(*
  Forcing, written M, w ⊩ φ, is truth of φ at world w in model M.

  The key modal clause is:

      M, w ⊩ □ φ

  exactly when φ holds at every world v accessible from w.
*)
  Fixpoint forces (M : model) (w : World M) (φ : formula Atom) : Prop :=
    match φ with
    | # p => val M w p
    | ⊥ => False
    | φ ⟶ ψ => forces M w φ -> forces M w ψ
    | □ φ => forall v : World M, w ↝[M] v -> forces M v φ
    end.

  Notation "M , w ⊩ φ" := (forces M w φ)
    (at level 80, w at next level, φ at next level) : modal_scope.

(*
  A context Γ is satisfied at w when every formula in Γ is true at w.
  Semantic entailment Γ ⊨ φ quantifies over all reflexive models and worlds.

  Compare this with System K: the definition of entailment has the same shape,
  but the type of M is now the T model type above. Therefore every semantic
  statement in this section is automatically restricted to reflexive frames.
*)
  Definition satisfies (M : model) (w : World M) (Γ : list (formula Atom)) : Prop :=
    forall φ, Γ ∋ φ -> M, w ⊩ φ.

  Notation "M , w ⊩* Γ" := (satisfies M w Γ)
    (at level 80, w at next level, Γ at next level) : modal_scope.

  Definition entails (Γ : list (formula Atom)) (φ : formula Atom) : Prop :=
    forall M w, M, w ⊩* Γ -> M, w ⊩ φ.

  Definition valid (φ : formula Atom) : Prop := entails [] φ.

  Notation "Γ ⊨ φ" := (entails Γ φ)
    (at level 99, φ at next level) : modal_scope.
  Notation "⊨ φ" := (valid φ)
    (at level 99, φ at next level) : modal_scope.

  Lemma satisfies_nil M w :
    M, w ⊩* [].
  Proof.
    intros φ Hφ. inversion Hφ.
  Qed.

(*
  Each axiom schema is valid in every reflexive Kripke model.
  The first two propositional axioms are intuitionistically valid;
  the third one uses classical reasoning through NNPP.

  The K axiom is valid on every frame, so its proof is identical to System K.
  The T axiom is the only axiom whose soundness proof actually uses the extra
  reflexive field of the model.
*)
  Lemma ax_prop₁_sound Γ φ ψ :
    Γ ⊨ φ ⟶ ψ ⟶ φ.
  Proof.
    intros M w _. simpl. intros Hφ _. exact Hφ.
  Qed.

  Lemma ax_prop₂_sound Γ φ ψ χ :
    Γ ⊨ (φ ⟶ ψ ⟶ χ) ⟶ (φ ⟶ ψ) ⟶ φ ⟶ χ.
  Proof.
    intros M w _. simpl.
    intros Hφψχ Hφψ Hφ.
    exact (Hφψχ Hφ (Hφψ Hφ)).
  Qed.

  Lemma ax_prop₃_sound Γ φ ψ :
    Γ ⊨ (¬ ψ ⟶ ¬ φ) ⟶ φ ⟶ ψ.
  Proof.
    intros M w _. simpl.
    intros Hcontra Hφ.
    apply NNPP.
    intros Hnotψ.
    exact (Hcontra Hnotψ Hφ).
  Qed.

  Lemma ax_K_sound Γ φ ψ :
    Γ ⊨ □ (φ ⟶ ψ) ⟶ □ φ ⟶ □ ψ.
  Proof.
    intros M w _. simpl.
    intros Hboxφψ Hboxφ v Hwv.
    exact (Hboxφψ v Hwv (Hboxφ v Hwv)).
  Qed.

  Lemma ax_T_sound Γ φ :
    Γ ⊨ □ φ ⟶ φ.
  Proof.
    intros M w _. simpl.
    intros Hboxφ.
(*
    This is the whole K-versus-T step.

    After unfolding □ φ, we know that φ holds at every world accessible from
    w. From that alone, K cannot conclude φ at w: w might not be accessible
    from itself. T gives reflexivity, so w is one of the worlds quantified over
    by □ φ.
*)
    exact (Hboxφ w (reflexive M w)).
  Qed.

(*
  Soundness of the inference rules:

  - modus ponens preserves semantic consequence by function application;
  - necessitation is sound because a theorem is true at every world,
    so it is true at every accessible world.
*)
  Lemma mp_sound Γ φ ψ :
    Γ ⊨ φ ⟶ ψ ->
    Γ ⊨ φ ->
    Γ ⊨ ψ.
  Proof.
    intros Himp Hφ M w Hctx.
    exact (Himp M w Hctx (Hφ M w Hctx)).
  Qed.

  Lemma nec_sound Γ φ :
    ⊨ φ ->
    Γ ⊨ □ φ.
  Proof.
    intros Hvalid M w _ v _.
    exact (Hvalid M v (satisfies_nil M v)).
  Qed.

(*
  Main theorem.

  The proof is by induction on the derivation Γ ⊢ φ.
  Every syntactic constructor is matched with the corresponding
  semantic fact above.

  Compared with the System K soundness theorem, the induction has one extra
  branch for ax_T. That branch is discharged by ax_T_sound, whose proof is the
  only place where reflexivity is used.
*)
  Theorem soundness Γ φ :
    Γ ⊢ φ ->
    Γ ⊨ φ.
  Proof.
    intros Hderiv.
    induction Hderiv.
    - intros M w Hctx. exact (Hctx φ H).
    - apply ax_prop₁_sound.
    - apply ax_prop₂_sound.
    - apply ax_prop₃_sound.
    - apply ax_K_sound.
    - apply ax_T_sound.
    - eapply mp_sound; eassumption.
    - apply nec_sound. exact IHHderiv.
  Qed.

  Corollary theorem_soundness φ :
    ⊢ φ ->
    ⊨ φ.
  Proof.
    apply soundness.
  Qed.
End KripkeSemantics.

Notation "M , w ⊩ φ" := (forces M w φ)
  (at level 80, w at next level, φ at next level) : modal_scope.
Notation "M , w ⊩* Γ" := (satisfies M w Γ)
  (at level 80, w at next level, Γ at next level) : modal_scope.
Notation "Γ ⊨ φ" := (entails Γ φ)
  (at level 99, φ at next level) : modal_scope.
Notation "⊨ φ" := (valid φ)
  (at level 99, φ at next level) : modal_scope.
