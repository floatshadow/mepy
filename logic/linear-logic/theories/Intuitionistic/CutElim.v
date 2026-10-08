(** * Intuitionistic.CutElim: completeness and cut elimination for ILL

    [Phase.v] proved soundness: whatever is provable, with or without
    cuts, is valid in every phase space. This file proves the converse:
    whatever is valid has a _cut-free_ proof. Chaining the two gives
    cut elimination:

<<
         Γ ⊢ A   ──soundness──▶   Γ ⊨ A   ──completeness──▶   Γ ⊢cf A
>>

    This is Okada's _semantic_ proof of cut elimination (1996, 1999).
    Gentzen's syntactic proof rewrites a derivation step by step, pushing
    each cut upwards. It needs a delicate termination argument, and the
    [!] rules make that worse (they call for a "multicut"). The semantic
    proof sidesteps all of it. We build one phase space out of cut-free
    provability, and soundness does the rest.

    ** The syntactic phase space

    - a phase is a context [Γ : list iformula], taken up to permutation;
    - [·] is [++] and [ε] is [[]];
    - the closure of a set [X] of contexts is

<<
          cl X = { Γ | for every "test" (Δ, C):
                         if  x ++ Δ ⊢cf C  for all x ∈ X,
                         then Γ ++ Δ ⊢cf C }
>>

      [Γ] lies in [cl X] when it passes every test that all members of [X]
      pass;
    - the reusable phases are the banged contexts [‼Σ];
    - [⊥] denotes the contexts that prove [⊥] without cut.

    ** Okada's lemma

    In this model, every formula [A] satisfies

<<
        [A] ∈ ⟦A⟧ ⊆ { Γ | Γ ⊢cf A }
>>

    Given that, take a provable [Γ ⊢ C]. Soundness gives
    [⦅Γ⦆ ⊆ ⟦C⟧], and [Γ ∈ ⦅Γ⦆] holds by the left half of the lemma.
    So [Γ ∈ ⟦C⟧], and the right half gives [Γ ⊢cf C]. *)

From LinearLogic.Intuitionistic Require Export Phase.

(** ** The closure operator on contexts *)
Definition syn_cl (X : propset (list iformula)) : propset (list iformula) :=
  {[ Γ | ∀ Δ C, (∀ x, x ∈ X -> x ++ Δ ⊢cf C) -> Γ ++ Δ ⊢cf C ]}.

Lemma elem_of_syn_cl X Γ :
  Γ ∈ syn_cl X ↔ ∀ Δ C, (∀ x, x ∈ X -> x ++ Δ ⊢cf C) -> Γ ++ Δ ⊢cf C.
Proof. unfold syn_cl. by rewrite elem_of_PropSet. Qed.

(** stdpp's [set_unfold] can see through [syn_cl] and, below, [down]. *)
#[global] Instance set_unfold_syn_cl X Γ :
  SetUnfoldElemOf Γ (syn_cl X)
    (∀ Δ C, (∀ x, x ∈ X -> x ++ Δ ⊢cf C) -> Γ ++ Δ ⊢cf C).
Proof. constructor. apply elem_of_syn_cl. Qed.

(** ** The syntactic phase space

    After [set_unfold], every axiom is a statement about tests, and most
    are one-liners. The two interesting ones are stability (a test of a
    product is split into a test of each factor) and the axioms for [J],
    which are exactly the derived rules [weaken_bangs] and
    [contract_bangs] of [Sequent.v]. *)
Definition syntactic : phase_space.
Proof.
  refine (Build_phase_space (list iformula) (@Permutation iformula) app []
            syn_cl {[ Γ | ∃ Σ, Γ = ‼Σ ]} {[ Γ | Γ ⊢cf ⊥ ]}
            _ _ _ _ _ _ _ _ _ _ _ _ _ _);
    try apply _; unfold prod_with; set_unfold.
  - (* assoc *) intros. by rewrite (assoc_L (++)).
  - (* comm *) intros. apply Permutation_app_comm.
  - (* unit *) done.
  - (* cl_ext: members of X pass every test that X passes *)
    intros X Γ HΓ Δ C H. by apply H.
  - (* cl_least: a test passed by Y is passed by X ⊆ cl Y, hence by cl X *)
    intros X Y HXY Γ HΓ Δ C H. apply HΓ. intros x Hx. by apply HXY.
  - (* cl respects ≡ₚ: by exchange *)
    intros X Γ Γ' HΓ H Δ C HX. apply (ex' (H Δ C HX)). by rewrite HΓ.
  - (* stability: test Γ with Γ' ++ Δ, then test Γ' with x ++ Δ *)
    intros X Y Γ Γ' HΓ HΓ' Δ C H. rewrite <- (assoc_L (++)).
    apply HΓ. intros x Hx. ex_to (Γ' ++ x ++ Δ).
    apply HΓ'. intros y Hy. ex_to ((x ++ y) ++ Δ).
    apply H. by exists x, y.
  - (* J respects ≡ₚ: a permutation of ‼Σ is ‼Σ' for some Σ' *)
    intros Γ Γ' HΓ [Σ ->].
    destruct (Permutation_map_inv _ _ (symmetry HΓ)) as (Σ' & -> & _).
    by exists Σ'.
  - (* ε ∈ J *) by exists [].
  - (* J is closed under · *)
    intros Γ Γ' [Σ ->] [Σ' ->]. exists (Σ ++ Σ'). by rewrite map_app.
  - (* reusable contexts can be discarded: weakening *)
    intros Γ [Σ ->] Δ C H.
    apply weaken_bangs, (H []). by apply elem_of_PropSet.
  - (* reusable contexts can be duplicated: contraction *)
    intros Γ [Σ ->] Δ C H.
    apply contract_bangs. rewrite (assoc_L (++)). apply H.
    by apply elem_of_PropSet.
Defined.

(** Reduce the projections of [syntactic], leaving [∈] alone. *)
Ltac syn_simpl :=
  cbn [ph_cl ph_J ph_bot ph_equiv ph_op ph_e syntactic carrier] in *.

(** Each variable [$p] denotes the contexts that prove [$p] without cut. *)
Definition down (A : iformula) : propset syntactic := {[ Γ | Γ ⊢cf A ]}.
Definition syn_val : nat -> propset syntactic := λ p, down ($p).

Lemma elem_of_down A Γ : Γ ∈ down A ↔ Γ ⊢cf A.
Proof. unfold down. by rewrite elem_of_PropSet. Qed.

#[global] Instance set_unfold_down A Γ : SetUnfoldElemOf Γ (down A) (Γ ⊢cf A).
Proof. constructor. apply elem_of_down. Qed.

(** [elem_of_syn_cl], stated over the carrier of [syntactic]. Then the
    lemmas of [Phase.v] can infer the phase space. *)
Lemma elem_of_cl_syn (X : propset syntactic) (Γ : syntactic) :
  Γ ∈ cl X ↔ ∀ Δ C, (∀ x : syntactic, x ∈ X -> x ++ Δ ⊢cf C) -> Γ ++ Δ ⊢cf C.
Proof. apply elem_of_syn_cl. Qed.

(** ** Facts of the syntactic model

    Okada's lemma has two halves, and each half has one tool.

    _Left rules put a formula into a fact._ To show [Γ ∈ cl X], pick one
    member [Γ'] of [X] and check that every test passed by [Γ'] is also
    passed by [Γ]. That check is usually a single left rule. For
    example, [[A ⊗ B]] passes every test that [[A; B]] passes, by
    [tensorL]:

<<
         Γ' ++ Δ ⊢cf C
        ───────────────  (a left rule)          Γ' ∈ X
         Γ  ++ Δ ⊢cf C
        ───────────────────────────────────────────────  cl_left
                          Γ ∈ cl X
>>
*)
Lemma cl_left (X : propset syntactic) (Γ Γ' : syntactic) :
  Γ' ∈ X -> (∀ Δ C, Γ' ++ Δ ⊢cf C -> Γ ++ Δ ⊢cf C) -> Γ ∈ cl X.
Proof.
  intros HΓ' Hrule. apply elem_of_cl_syn. intros Δ C H. by apply Hrule, H.
Qed.

(** The same for a fact [F], which is its own closure. *)
Lemma fact_left (F : propset syntactic) (Γ Γ' : syntactic) :
  fact F -> Γ' ∈ F -> (∀ Δ C, Γ' ++ Δ ⊢cf C -> Γ ++ Δ ⊢cf C) -> Γ ∈ F.
Proof. intros HF HΓ' Hrule. by apply HF, (cl_left _ _ Γ'). Qed.

(** _Right rules bound a fact from above._ The closure of a set of proofs
    of [C] contains only proofs of [C]: use the trivial test ([[]], [C]). *)
Lemma cl_down (X : propset syntactic) C : X ⊆ down C -> cl X ⊆ down C.
Proof.
  intros HX Γ HΓ. rewrite elem_of_cl_syn in HΓ.
  rewrite elem_of_down, <- (right_id_L [] (++) Γ). apply HΓ.
  intros x Hx. rewrite (right_id_L [] (++)). by apply elem_of_down, HX.
Qed.

(** ** Okada's lemma

    By induction on [A]. In each case the first half uses the left rule
    of the connective (through [cl_left] / [fact_left]), and the second
    half uses its right rule (through [cl_down]). *)
Lemma okada A : [A] ∈ ⟦A⟧syn_val ∧ ⟦A⟧syn_val ⊆ down A.
Proof.
  induction A as [p | | | | | A [HA1 HA2] B [HB1 HB2] | A [HA1 HA2] B [HB1 HB2]
                 | A [HA1 HA2] B [HB1 HB2] | A [HA1 HA2] B [HB1 HB2]
                 | A [HA1 HA2]]; cbn [interp].
  - (* $p *)
    split; [| by apply cl_down].
    apply ph_cl_ext, elem_of_down, ax.
  - (* 𝟙 *)
    split.
    + apply (cl_left _ _ []); [by apply elem_of_one | intros; by apply oneL].
    + apply cl_down. intros x Hx%elem_of_one. apply elem_of_down.
      syn_simpl. apply Permutation_nil_r in Hx as ->. apply oneR.
  - (* ⊥ *)
    split; [| by apply cl_down].
    apply ph_cl_ext. set_unfold. apply ax.
  - (* ⊤ *)
    split; [apply elem_of_top |]. intros x _. apply elem_of_down, topR.
  - (* 𝟘: the empty set passes every test *)
    split; [| apply cl_down; set_solver].
    apply elem_of_cl_syn. intros Δ C _. apply zeroL.
  - (* A ⊗ B *)
    split.
    + apply (cl_left _ _ [A; B]); [| intros; by apply tensorL].
      apply elem_of_prod. by exists [A], [B].
    + apply cl_down. intros x (a & b & Ha%HA2 & Hb%HB2 & Hx)%elem_of_prod.
      apply elem_of_down. apply (ex' (Γ := a ++ b)); [| by symmetry].
      apply tensorR; by apply elem_of_down.
  - (* A ⊸ B *)
    split.
    + apply elem_of_lolli. intros a Ha%HA2%elem_of_down.
      apply (fact_left _ _ [B]); [apply interp_fact | done |].
      intros Δ C H. by apply lolliL.
    + intros f Hf. rewrite elem_of_lolli in Hf. apply elem_of_down.
      apply lolliR. ex_to (f ++ [A]). by apply elem_of_down, HB2, Hf.
  - (* A & B *)
    split.
    + apply elem_of_intersection. split.
      * apply (fact_left _ _ [A]); [apply interp_fact | done |].
        intros; by apply withL1.
      * apply (fact_left _ _ [B]); [apply interp_fact | done |].
        intros; by apply withL2.
    + intros x [Ha%HA2 Hb%HB2]%elem_of_intersection.
      apply elem_of_down, withR; by apply elem_of_down.
  - (* A ⊕ B: two witnesses, one per premise of plusL *)
    split.
    + apply elem_of_cl_syn. intros Δ C H.
      apply plusL; [apply (H [A]) | apply (H [B])]; set_solver.
    + apply cl_down. intros x [Hx%HA2 | Hx%HB2]%elem_of_union;
        apply elem_of_down; [apply plusR1 | apply plusR2]; by apply elem_of_down.
  - (* !A *)
    split.
    + apply ph_cl_ext, elem_of_intersection. split.
      * apply (fact_left _ _ [A]); [apply interp_fact | done |].
        intros; by apply bangD.
      * syn_simpl. set_unfold. by exists [A].
    + apply cl_down. intros x [Hx%HA2 HJ]%elem_of_intersection.
      syn_simpl. set_unfold in HJ. destruct HJ as [Σ ->].
      apply elem_of_down, bangR, elem_of_down, Hx.
Qed.

(** In the syntactic model, every context [Γ] is a bag for itself. *)
Lemma ctx_self Γ : Γ ∈ ⦅Γ⦆syn_val.
Proof.
  induction Γ as [| A Γ IH]; cbn [interp_ctx].
  - by apply elem_of_one.
  - apply elem_of_prod. exists [A], Γ. split_and!; [apply okada | done | done].
Qed.

(** ** The main theorems *)

(** Completeness: a valid sequent has a cut-free proof. *)
Theorem completeness Γ A : Γ ⊨ A -> Γ ⊢cf A.
Proof.
  intros H. apply elem_of_down, (proj2 (okada A)), (H syntactic syn_val), ctx_self.
Qed.

(** Cut elimination: every proof can be replaced by a cut-free one. *)
Theorem cut_elimination Γ A : Γ ⊢ A -> Γ ⊢cf A.
Proof. intros H. by apply completeness, (soundness true). Qed.

(** As a consequence, [cut] is _admissible_ in the cut-free calculus:
    adding it as a rule proves nothing new. *)
Corollary cut_admissible Γ Δ A C : Γ ⊢cf A -> A :: Δ ⊢cf C -> Γ ++ Δ ⊢cf C.
Proof.
  intros H1 H2. apply cut_elimination, (cut _ _ _ A); [done | |];
    by apply cf_to_full.
Qed.

(** All three notions coincide. *)
Theorem provable_valid_cutfree Γ A :
  (Γ ⊢ A ↔ Γ ⊨ A) ∧ (Γ ⊨ A ↔ Γ ⊢cf A).
Proof.
  split; split.
  - apply soundness.
  - intros H. by apply cf_to_full, completeness.
  - apply completeness.
  - apply soundness.
Qed.
