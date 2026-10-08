(** * Classical.CutElim: completeness and cut elimination for CLL

    [Classical/Phase.v] proved soundness: every provable two-sided
    sequent, with or without cuts, is valid in every classical phase
    space. This file proves the converse, and in a strong form: every
    valid sequent has a _cut-free_ proof. Chaining the two gives cut
    elimination, exactly as in [Intuitionistic/CutElim.v]:

<<
         Γ ⊢ Δ   ──soundness──▶   Γ ⊨ Δ   ──completeness──▶   Γ ⊢cf Δ
>>

    ** The syntactic phase space

    The phases are two-sided contexts, and the pole is cut-free
    provability:

    - a phase is a pair [(Γ, Δ)] of lists of formulas, taken up to
      permutation on each side. Read it as the sequent fragment
      "[Γ] on the left, [Δ] on the right";
    - [·] concatenates both sides, and [ε] is [([], [])];
    - the pole is [{ (Γ, Δ) | Γ ⊢cf Δ }];
    - the reusable phases are the pairs [(‼Σ, ⁇Π)]. They are exactly the
      contexts allowed around a promotion, and the structural rules for
      [!] and [?] let them be discarded and duplicated.

    ** What changes compared with ILL

    In the intuitionistic proof, the closure operator had to be _chosen_:
    a context lies in [cl X] when it passes every "test" [(Δ, C)] that the
    members of [X] pass. Here nothing is chosen besides the pole. The
    closure is [X^⊥⊥], and unfolding it gives the same idea with two-sided
    tests:

<<
        y ∈ X^⊥    iff  for every x ∈ X,  x.1 ++ y.1 ⊢cf x.2 ++ y.2
        z ∈ X^⊥⊥   iff  z passes every test y that all members of X pass
>>

    So the tests of the intuitionistic proof reappear as the counter-bags
    [X^⊥]. And because the right-hand side may hold any number of
    formulas, a test is just another context, with no distinguished
    conclusion [C].

    ** Okada's lemma

    Write [hyp A] for the phase [([A], [])] (one copy of [A] on the left)
    and [concl A] for [([], [A])] (one copy on the right). The heart of the
    proof is

<<
        hyp A ∈ ⟦A⟧      and      concl A ∈ ⟦A⟧^⊥
>>

    In words: [A] used as a hypothesis is a bag of [A], and [A] used as a
    conclusion is a counter-bag of [A]. Their product, [([A], [A])], is in
    the pole: that is the axiom. Given the lemma, a sequent [Γ ⊢ Δ] gives
    the phase [(Γ, Δ)], which lies in the big product [⨀ (sq Γ Δ)]. If the
    sequent is valid, that product lies in the pole, so [Γ ⊢cf Δ].

    This is simpler than the intuitionistic case in one respect. There,
    the right half of the lemma, [⟦A⟧ ⊆ { Γ | Γ ⊢cf A }], had to be
    applied at the end. Here the pole _is_ cut-free provability, so the
    last step is free. *)

From LinearLogic.Classical Require Export Phase.

(** ** The syntactic phase space *)

(** A two-sided context: hypotheses and conclusions. *)
Definition ctx : Type := list cformula * list cformula.

(** Two contexts are equivalent when both sides are permutations. We
    give this relation explicitly. stdpp also has generic [Equiv]
    instances for pairs and lists, but they are not the ones we want, so
    every lemma below types its phases as elements of [syntactic]. *)
Definition ctx_equiv : Equiv ctx := λ x y, x.1 ≡ₚ y.1 ∧ x.2 ≡ₚ y.2.

(** Concatenation on both sides. *)
Definition ctx_app (x y : ctx) : ctx := (x.1 ++ y.1, x.2 ++ y.2).

Lemma ctx_equivalence : Equivalence ctx_equiv.
Proof.
  unfold ctx_equiv. split.
  - done.
  - intros x y []. split; by symmetry.
  - intros x y z [] []. split; by etrans.
Qed.

Lemma ctx_app_proper : Proper (ctx_equiv ==> ctx_equiv ==> ctx_equiv) ctx_app.
Proof.
  intros x x' [Hx1 Hx2] y y' [Hy1 Hy2]. split; cbn [ctx_app fst snd]; by f_equiv.
Qed.

(** The model. The obligations are the monoid laws, closure of the pole
    under [≡] (by [ex]), closure of [J] under [≡] (a permutation of [‼Σ]
    is again of the form [‼Σ']), and the two structural laws for [J]
    (by [weaken_bangs]/[weaken_whys] and [contract_bangs]/[contract_whys]). *)
Definition syntactic : cphase_space.
Proof.
  refine (Build_cphase_space ctx ctx_equiv ctx_app ([], [])
            {[ x | x.1 ⊢cf x.2 ]} {[ x | ∃ Σ Π, x.1 = ‼Σ ∧ x.2 = ⁇Π ]}
            ctx_equivalence ctx_app_proper _ _ _ _ _ _ _ _ _);
    unfold equiv, ctx_equiv, ctx_app; cbn [fst snd]; set_unfold.
  - (* assoc *) intros. by rewrite !(assoc_L (++)).
  - (* comm *) intros. split; apply Permutation_app_comm.
  - (* unit *) done.
  - (* the pole respects ≡ *) intros x y [H1 H2]. by apply ex.
  - (* J respects ≡ *)
    intros x y [H1 H2] (Σ & Π & E1 & E2). rewrite E1 in H1. rewrite E2 in H2.
    destruct (Permutation_map_inv _ _ (symmetry H1)) as (Σ' & ? & _).
    destruct (Permutation_map_inv _ _ (symmetry H2)) as (Π' & ? & _).
    by exists Σ', Π'.
  - (* ε ∈ J *) by exists [], [].
  - (* J is closed under · *)
    intros x y (Σ & Π & -> & ->) (Σ' & Π' & -> & ->).
    exists (Σ ++ Σ'), (Π ++ Π'). by rewrite !map_app.
  - (* reusable contexts can be discarded *)
    intros j y (Σ & Π & -> & ->) H. by apply weaken_bangs, weaken_whys.
  - (* reusable contexts can be duplicated *)
    intros j y (Σ & Π & -> & ->) H.
    apply contract_bangs, contract_whys. by rewrite !(assoc_L (++)).
Defined.

(** *** Membership in the syntactic model

    These lemmas restate the set formers of [Phase.v] in terms of
    sequents. They never unfold [∈] itself. *)
Lemma elem_of_pole_syn (x : syntactic) : x ∈ ⫫ ↔ x.1 ⊢cf x.2.
Proof. exact (elem_of_PropSet (λ x : ctx, x.1 ⊢cf x.2) x). Qed.

Lemma elem_of_J_syn (x : syntactic) : x ∈ cph_J ↔ ∃ Σ Π, x = (‼Σ, ⁇Π).
Proof.
  rewrite (elem_of_PropSet (λ x : ctx, ∃ Σ Π, x.1 = ‼Σ ∧ x.2 = ⁇Π) x).
  destruct x as [Γ Δ]. cbn [fst snd]. naive_solver.
Qed.

Lemma elem_of_one_syn (x : syntactic) : x ∈ one_set ↔ x = ([], []).
Proof.
  rewrite elem_of_one. destruct x as [Γ Δ]. split.
  - intros [H1%Permutation_nil_r H2%Permutation_nil_r]. by simplify_eq/=.
  - by intros [= -> ->].
Qed.

(** [y] is a counter-bag of [X] when it completes every member of [X] to
    a cut-free provable sequent. *)
Lemma elem_of_orth_syn (X : propset syntactic) (y : syntactic) :
  y ∈ X^⊥ ↔ ∀ x : syntactic, x ∈ X → x.1 ++ y.1 ⊢cf x.2 ++ y.2.
Proof. rewrite elem_of_orth. by setoid_rewrite elem_of_pole_syn. Qed.

Lemma elem_of_prod_syn (X Y : propset syntactic) (x : syntactic) :
  x ∈ X ⊙ Y ↔
  ∃ a b : syntactic, a ∈ X ∧ b ∈ Y ∧ x.1 ≡ₚ a.1 ++ b.1 ∧ x.2 ≡ₚ a.2 ++ b.2.
Proof. by rewrite elem_of_prod. Qed.

(** The counter-bags of [{ε}] are the provable contexts. *)
Lemma orth_one_syn (y : syntactic) : y ∈ one_set^⊥ → y.1 ⊢cf y.2.
Proof.
  rewrite elem_of_orth_syn. intros H. apply (H ([], [])), elem_of_one_syn. done.
Qed.

(** ** A formula on one side *)

(** [hyp A] holds one [A] as a hypothesis, [concl A] one [A] as a conclusion. *)
Definition hyp (A : cformula) : syntactic := ([A], []).
Definition concl (A : cformula) : syntactic := ([], [A]).

(** Four small lemmas do all the bookkeeping for Okada's lemma. The first
    two _prove_ that [hyp A] or [concl A] is a counter-bag: check that it
    completes each member of [X], adding [A] on the left or the right. *)
Lemma L_orth (X : propset syntactic) A :
  (∀ x : syntactic, x ∈ X → A :: x.1 ⊢cf x.2) → hyp A ∈ X^⊥.
Proof.
  intros H. apply elem_of_orth_syn. intros x Hx. cbn [hyp fst snd].
  ex_to (A :: x.1) x.2. auto.
Qed.

Lemma R_orth (X : propset syntactic) A :
  (∀ x : syntactic, x ∈ X → x.1 ⊢cf A :: x.2) → concl A ∈ X^⊥.
Proof.
  intros H. apply elem_of_orth_syn. intros x Hx. cbn [concl fst snd].
  ex_to x.1 (A :: x.2). auto.
Qed.

(** The other two _use_ such facts: they turn membership into a cut-free
    proof with [A] on the left or on the right. *)
Lemma L_use (X : propset syntactic) A (y : syntactic) :
  hyp A ∈ X → y ∈ X^⊥ → A :: y.1 ⊢cf y.2.
Proof. intros HA Hy. rewrite elem_of_orth_syn in Hy. exact (Hy _ HA). Qed.

Lemma R_use (X : propset syntactic) A (x : syntactic) :
  concl A ∈ X^⊥ → x ∈ X → x.1 ⊢cf A :: x.2.
Proof.
  intros HA Hx. rewrite elem_of_orth_syn in HA.
  ex_to (x.1 ++ []) (x.2 ++ [A]). auto.
Qed.

(** A counter-bag of [X ⊙ Y] completes every product [a · b]. *)
Lemma orth_prod_use (X Y : propset syntactic) (a b y : syntactic) :
  a ∈ X → b ∈ Y → y ∈ (X ⊙ Y)^⊥ → (a.1 ++ b.1) ++ y.1 ⊢cf (a.2 ++ b.2) ++ y.2.
Proof.
  intros Ha Hb Hy. rewrite elem_of_orth_syn in Hy. apply (Hy (a · b)).
  apply elem_of_prod. by exists a, b.
Qed.

(** Each variable [$p] denotes the single phase [hyp ($p)]. *)
Definition syn_val : nat → propset syntactic := λ p, {[ x | x = hyp ($p) ]}.

Lemma elem_of_syn_val p (x : syntactic) : x ∈ syn_val p ↔ x = hyp ($p).
Proof. unfold syn_val. by rewrite elem_of_PropSet. Qed.

(** ** Okada's lemma

    Each case applies the left or right rule of the connective, and
    [L_use]/[R_use] supply its premises from the induction hypotheses.
    When the target set is a biorthogonal [Y^⊥⊥], it is enough to land in
    [Y] ([biorth]). When the target is a fact [⟦A⟧], it is enough to land
    in [⟦A⟧^⊥⊥] ([interp_fact]), that is, to be a counter-bag of
    [⟦A⟧^⊥]. *)
Lemma okada A : hyp A ∈ ⟦A⟧syn_val ∧ concl A ∈ (⟦A⟧syn_val)^⊥.
Proof.
  induction A as [p | A [HA1 HA2] | | | | | A [HA1 HA2] B [HB1 HB2]
                 | A [HA1 HA2] B [HB1 HB2] | A [HA1 HA2] B [HB1 HB2]
                 | A [HA1 HA2] B [HB1 HB2] | A [HA1 HA2] | A [HA1 HA2]];
    cbn [interp]; split.
  - (* $p, left: hyp $p ∈ v p *)
    apply L_orth. intros y Hy.
    apply (L_use (syn_val p)); [by apply elem_of_syn_val | done].
  - (* $p, right: the axiom *)
    apply biorth, R_orth. intros x ->%elem_of_syn_val. apply ax.
  - (* A^⊥, left: ^⊥L *)
    apply L_orth. intros x Hx. apply negL. by apply (R_use (⟦A⟧syn_val)).
  - (* A^⊥, right: ^⊥R *)
    apply R_orth. intros y Hy. apply negR. by apply (L_use (⟦A⟧syn_val)).
  - (* 𝟙, left: 𝟙L *)
    apply L_orth. intros y Hy. by apply oneL, orth_one_syn.
  - (* 𝟙, right: 𝟙R *)
    apply biorth, R_orth. intros x ->%elem_of_one_syn. apply oneR.
  - (* ⊥, left: ⊥L *)
    apply L_orth. intros x ->%elem_of_one_syn. apply botL.
  - (* ⊥, right: ⊥R *)
    apply R_orth. intros y Hy. by apply botR, orth_one_syn.
  - (* ⊤, left: anything *)
    apply elem_of_full.
  - (* ⊤, right: ⊤R *)
    apply R_orth. intros x _. apply topR.
  - (* 𝟘, left: 𝟘L *)
    apply L_orth. intros y _. apply zeroL.
  - (* 𝟘, right: vacuous *)
    apply biorth, R_orth. set_solver.
  - (* A ⊗ B, left: ⊗L, using hyp A · hyp B ∈ ⟦A⟧ ⊙ ⟦B⟧ *)
    apply L_orth. intros y Hy. apply tensorL.
    exact (orth_prod_use _ _ (hyp A) (hyp B) y HA1 HB1 Hy).
  - (* A ⊗ B, right: ⊗R *)
    apply biorth, R_orth. intros x (a & b & Ha & Hb & H1 & H2)%elem_of_prod_syn.
    apply (ex' (tensorR _ _ _ _ _ A B (R_use _ _ _ HA2 Ha) (R_use _ _ _ HB2 Hb)));
      by rewrite ?H1, ?H2.
  - (* A ⅋ B, left: ⅋L *)
    apply L_orth. intros x (a & b & Ha & Hb & H1 & H2)%elem_of_prod_syn.
    apply (ex' (parL _ _ _ _ _ A B (L_use _ _ _ HA1 Ha) (L_use _ _ _ HB1 Hb)));
      by rewrite ?H1, ?H2.
  - (* A ⅋ B, right: ⅋R, using concl A · concl B ∈ ⟦A⟧^⊥ ⊙ ⟦B⟧^⊥ *)
    apply R_orth. intros y Hy. apply parR.
    exact (orth_prod_use _ _ (concl A) (concl B) y HA2 HB2 Hy).
  - (* A & B, left: &L₁ and &L₂ *)
    apply elem_of_intersection. split; apply interp_fact, L_orth; intros y Hy.
    + apply withL1. by apply (L_use (⟦A⟧syn_val)).
    + apply withL2. by apply (L_use (⟦B⟧syn_val)).
  - (* A & B, right: &R *)
    apply R_orth. intros x [Ha Hb]%elem_of_intersection.
    apply withR; [by apply (R_use (⟦A⟧syn_val)) | by apply (R_use (⟦B⟧syn_val))].
  - (* A ⊕ B, left: ⊕L *)
    apply L_orth. intros y Hy.
    apply plusL; apply (L_use (⟦A⟧syn_val ∪ ⟦B⟧syn_val)); set_solver.
  - (* A ⊕ B, right: ⊕R₁ and ⊕R₂ *)
    apply biorth, R_orth. intros x [Hx | Hx]%elem_of_union.
    + apply plusR1. by apply (R_use (⟦A⟧syn_val)).
    + apply plusR2. by apply (R_use (⟦B⟧syn_val)).
  - (* !A, left: hyp (!A) ∈ ⟦A⟧ ∩ J, by !D *)
    apply biorth, elem_of_intersection. split.
    + apply interp_fact, L_orth. intros y Hy.
      apply bangD. by apply (L_use (⟦A⟧syn_val)).
    + apply elem_of_J_syn. by exists [A], [].
  - (* !A, right: !R, on a reusable context (‼Σ, ⁇Π) *)
    apply biorth, R_orth.
    intros x [Hx (Σ & Π & ->)%elem_of_J_syn]%elem_of_intersection.
    apply bangR. exact (R_use _ _ _ HA2 Hx).
  - (* ? A, left: ?L, on a reusable context (‼Σ, ⁇Π) *)
    apply L_orth. intros x [Hx (Σ & Π & ->)%elem_of_J_syn]%elem_of_intersection.
    apply whyL. exact (L_use _ _ _ HA1 Hx).
  - (* ? A, right: concl (? A) ∈ ⟦A⟧^⊥ ∩ J, by ?D *)
    apply biorth, elem_of_intersection. split.
    + apply fact_orth, R_orth. intros y Hy.
      apply whyD. apply (R_use (⟦A⟧syn_val)); [done | by apply interp_fact].
    + apply elem_of_J_syn. by exists [], [A].
Qed.

(** Two direct consequences: in the syntactic model, every bag of [A]
    proves [A], and every counter-bag of [A] refutes [A]. *)
Corollary okada_bag A (x : syntactic) : x ∈ ⟦A⟧syn_val → x.1 ⊢cf A :: x.2.
Proof. apply R_use, okada. Qed.

Corollary okada_counter A (y : syntactic) :
  y ∈ (⟦A⟧syn_val)^⊥ → A :: y.1 ⊢cf y.2.
Proof. apply L_use, okada. Qed.

(** Every two-sided context is a phase of its own sequent: [(Γ, Δ)] is
    the product of the [hyp A] for [A ∈ Γ] and the [concl B] for [B ∈ Δ]. *)
Lemma ctx_self Γ Δ : ((Γ, Δ) : syntactic) ∈ ⨀ (sq syn_val Γ Δ).
Proof.
  induction Γ as [| A Γ IH]; [induction Δ as [| B Δ IH] |];
    cbn [sq map app bigprod].
  - by apply elem_of_one_syn.
  - apply elem_of_prod. exists (concl B), ([], Δ).
    split_and!; [apply okada | exact IH | done].
  - apply elem_of_prod. exists (hyp A), (Γ, Δ).
    split_and!; [apply okada | exact IH | done].
Qed.

(** ** The main theorems *)

(** Completeness: a valid sequent has a cut-free proof. Validity in the
    syntactic model puts [(Γ, Δ)] in the pole, and the pole is cut-free
    provability. *)
Theorem completeness Γ Δ : Γ ⊨ Δ → Γ ⊢cf Δ.
Proof.
  intros H. apply (elem_of_pole_syn (Γ, Δ)), (H syntactic syn_val (Γ, Δ)), ctx_self.
Qed.

(** Cut elimination: every proof can be replaced by a cut-free one. *)
Theorem cut_elimination Γ Δ : Γ ⊢ Δ → Γ ⊢cf Δ.
Proof. intros H. by apply completeness, (soundness true). Qed.

(** As a consequence, [cut] is _admissible_ in the cut-free calculus. *)
Corollary cut_admissible Γ₁ Γ₂ Δ₁ Δ₂ A :
  Γ₁ ⊢cf A :: Δ₁ → A :: Γ₂ ⊢cf Δ₂ → Γ₁ ++ Γ₂ ⊢cf Δ₁ ++ Δ₂.
Proof.
  intros H1 H2. apply cut_elimination, (cut _ _ _ _ _ A); [done | |];
    by apply cf_to_full.
Qed.

(** All three notions coincide. *)
Theorem provable_valid_cutfree Γ Δ :
  (Γ ⊢ Δ ↔ Γ ⊨ Δ) ∧ (Γ ⊨ Δ ↔ Γ ⊢cf Δ).
Proof.
  split; split.
  - apply soundness.
  - intros H. by apply cf_to_full, completeness.
  - apply completeness.
  - apply soundness.
Qed.
