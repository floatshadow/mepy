From Stdlib Require Import Logic.Classical_Prop.
From Stdlib Require Import Lists.List.

Import ListNotations.

Set Implicit Arguments.
Set Universe Polymorphism.

Declare Scope modal_scope.
Delimit Scope modal_scope with modal.

(*
  System K is the minimal normal modal logic.

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

Open Scope modal_scope.

Section ProofSystem.
  Context {Atom : Type}.

  Reserved Notation "Γ ⊢ φ" (at level 99, φ at next level).

(*
  Hilbert-style derivability for K.

  Γ ⊢ φ means that φ is derivable from assumptions Γ.
  The three ax_prop rules form a classical implicational basis.
  ax_K is the modal distribution axiom:

      □ (φ ⟶ ψ) ⟶ □ φ ⟶ □ ψ

  The necessitation rule is restricted to theorems: to derive □ φ
  under any Γ, φ must first be derivable from the empty context.
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
  Kripke models for plain K use arbitrary frames.

  World  : the type of possible worlds
  access : accessibility relation between worlds
  val    : valuation of atoms at worlds

  Because K imposes no frame condition, access is not required to be
  reflexive, transitive, symmetric, serial, etc.
*)
  Record model : Type := {
    World : Type;
    access : World -> World -> Prop;
    val : World -> Atom -> Prop;
  }.

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
    | □ φ => forall v : World M, access M w v -> forces M v φ
    end.

  Notation "M , w ⊩ φ" := (forces M w φ)
    (at level 80, w at next level, φ at next level) : modal_scope.

(*
  A context Γ is satisfied at w when every formula in Γ is true at w.
  Semantic entailment Γ ⊨ φ quantifies over all models and worlds.
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
  Each axiom schema is valid in every Kripke model.
  The first two propositional axioms are intuitionistically valid;
  the third one uses classical reasoning through NNPP.
*)
  Lemma ax_prop₁_sound Γ φ ψ :
    Γ ⊨ φ ⟶ ψ ⟶ φ.
  Proof.
    intros M w _. simpl. intros Hphi _. exact Hphi.
  Qed.

  Lemma ax_prop₂_sound Γ φ ψ χ :
    Γ ⊨ (φ ⟶ ψ ⟶ χ) ⟶ (φ ⟶ ψ) ⟶ φ ⟶ χ.
  Proof.
    intros M w _. simpl.
    intros Hphi_psi_chi Hphi_psi Hphi.
    exact (Hphi_psi_chi Hphi (Hphi_psi Hphi)).
  Qed.

  Lemma ax_prop₃_sound Γ φ ψ :
    Γ ⊨ (¬ ψ ⟶ ¬ φ) ⟶ φ ⟶ ψ.
  Proof.
    intros M w _. simpl.
    intros Hcontra Hphi.
    apply NNPP.
    intros Hnot_psi.
    exact (Hcontra Hnot_psi Hphi).
  Qed.

  Lemma ax_K_sound Γ φ ψ :
    Γ ⊨ □ (φ ⟶ ψ) ⟶ □ φ ⟶ □ ψ.
  Proof.
    intros M w _. simpl.
    intros Hbox_imp Hbox_phi v Hwv.
    exact (Hbox_imp v Hwv (Hbox_phi v Hwv)).
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
    intros Himp Hphi M w Hctx.
    exact (Himp M w Hctx (Hphi M w Hctx)).
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
