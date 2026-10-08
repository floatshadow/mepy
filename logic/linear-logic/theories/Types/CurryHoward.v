(** * Types.CurryHoward: programs are proofs

    [Types/LinearTypes.v] used the formulas of ILL as the types of a
    linear λ-calculus. This file shows that the match is more than a
    choice of names. Every typing derivation is, read differently, an
    ILL proof:

<<
        Γ ⨾ Δ ⊢ e ∶ A      ──translation──▶      ‼Γ ++ somes Δ ⊢ A
>>

    This is the _Curry–Howard correspondence_ for linear logic:

    - types are formulas: [A ⊸ B], [A ⊗ B], [!A], … are read the same way
      on both sides;
    - programs are proofs: a term [e] of type [A] records a derivation of
      [A], one rule per term former;
    - evaluation is cut elimination: a redex such as [(ƛ e) · v] is an
      introduction rule immediately consumed by the matching elimination,
      which in the sequent calculus is a [cut] between a right rule and a
      left rule. Contracting the redex ([⟶]) corresponds to the step of
      Gentzen's cut elimination that removes that cut. This file does not
      formalize the step-by-step match. What it does use is the end
      result: by [Intuitionistic/CutElim.v] every proof has a cut-free
      form. On the program side, [LinearTypes.preservation] says that
      each step keeps the type, so each step gives a proof of the same
      sequent;
    - linearity is the absence of contraction and weakening: a linear
      variable used twice would need contraction, and one never used
      would need weakening. Only [!]-types, whose variables live in the
      unrestricted context [Γ], may be copied and dropped, exactly as
      [bangC] and [bangW] allow only [!]-formulas to be.

    ** Reading the contexts

    The unrestricted context [Γ] becomes the banged context [‼Γ]: an
    unrestricted variable of type [A] is a hypothesis [!A], which may be
    used any number of times. The linear context [Δ] holds an entry for
    every linear variable in scope, available or not; only the available
    ones ([Some A]) are hypotheses. [somes Δ] collects them.

    ** The translation, rule by rule

    Natural deduction has introduction and elimination rules; the
    sequent calculus has right and left rules. Introductions become
    right rules directly. An elimination becomes a [cut] against the
    left rule of the same connective:

<<
     typing rule     sequent proof
     ƛ e             ⊸R
     e1 · e2         cut e1 against ⊸L (with e2 and ax)
     ⟨⟩              𝟙R, after dropping ‼Γ
     let𝟙 e1 in e2   cut e1 against 𝟙L
     ⟪e1, e2⟫        ⊗R, after duplicating ‼Γ
     let⊗ e1 in e2   cut e1 against ⊗L
     ⟨e1, e2⟩        &R
     π₁ e, π₂ e      cut e against &L₁, &L₂ (with ax)
     ι₁ e, ι₂ e      ⊕R₁, ⊕R₂
     case            cut e against ⊕L
     ⟨⊤⟩             ⊤R
     abort e         cut e against 𝟘L
     !e              !R (the linear context is empty)
     let! e1 in e2   cut e1 against e2, which uses !A as a hypothesis
     lv n            ax, after dropping ‼Γ
     uv n            !D and ax, after dropping the rest of ‼Γ
>>

    Every rule with two premises splits the linear context but shares
    [Γ]. On the sequent side this means both premises get a copy of
    [‼Γ]; [contract_bangs] merges the two copies back into one.

    ** Consequences

    Combined with cut elimination and the countermodels of
    [Intuitionistic/Phase.v], the translation gives facts about
    _programs_ that would be awkward to prove directly: no closed program
    duplicates or discards an argument of atomic type, and no closed
    program has type [𝟘]. *)

From LinearLogic.Types Require Import LinearTypes.
From LinearLogic.Intuitionistic Require Import CutElim.

(** ** Available linear variables

    [somes Δ] keeps the available entries of a linear context. It is
    stdpp's [omap id]: [somes [Some A; None; Some B] = [A; B]]. *)
Definition somes (Δ : list (option iformula)) : list iformula := omap id Δ.

Lemma somes_Some A Δ : somes (Some A :: Δ) = A :: somes Δ.
Proof. done. Qed.

Lemma somes_None Δ : somes (None :: Δ) = somes Δ.
Proof. done. Qed.

(** An empty linear context has no hypotheses. *)
Lemma somes_lempty Δ : lempty Δ -> somes Δ = [].
Proof. induction 1 as [| o Δ -> _ IH]; [done | by rewrite somes_None]. Qed.

(** The context of a linear variable is a single hypothesis. *)
Lemma somes_lone n A Δ : lone n A Δ -> somes Δ = [A].
Proof.
  induction 1 as [A Δ HΔ | n A Δ _ IH].
  - by rewrite somes_Some, somes_lempty.
  - by rewrite somes_None.
Qed.

(** A split of the linear context is a split of the hypotheses, up to
    order. *)
Lemma somes_merge Δ Δ1 Δ2 :
  Δ ≔ Δ1 ⋈ Δ2 -> somes Δ ≡ₚ somes Δ1 ++ somes Δ2.
Proof.
  induction 1 as [| o1 o2 o Δ1 Δ2 Δ Ho _ IH]; [done |].
  inversion Ho; subst; rewrite ?somes_Some, ?somes_None, IH; solve_Permutation.
Qed.

(** ** Structural lemmas for the translated contexts *)

(** A context split, on the sequent side: both premises receive [‼Γ],
    and [contract_bangs] merges the two copies. *)
Lemma join Γ Δ Δ1 Δ2 C :
  Δ ≔ Δ1 ⋈ Δ2 ->
  (‼Γ ++ somes Δ1) ++ (‼Γ ++ somes Δ2) ⊢ C ->
  ‼Γ ++ somes Δ ⊢ C.
Proof.
  intros Hm H. apply contract_bangs. apply (ex' H).
  rewrite (somes_merge _ _ _ Hm). solve_Permutation.
Qed.

(** The shape of every elimination: cut the eliminated term [A] against
    a proof that uses [A] as a hypothesis. *)
Lemma cut_join Γ Δ Δ1 Δ2 A C :
  Δ ≔ Δ1 ⋈ Δ2 ->
  ‼Γ ++ somes Δ1 ⊢ A ->
  A :: ‼Γ ++ somes Δ2 ⊢ C ->
  ‼Γ ++ somes Δ ⊢ C.
Proof. intros Hm H1 H2. apply (join _ _ _ _ _ Hm), (cut _ _ _ A); done. Qed.

(** A cut whose second premise uses nothing but the cut formula. *)
Lemma cut_r Γ A C : Γ ⊢ A -> [A] ⊢ C -> Γ ⊢ C.
Proof.
  intros H1 H2. rewrite <- (app_nil_r Γ). by apply (cut _ _ _ A).
Qed.

(** An unrestricted variable: take its [!A] out of [‼Γ], drop the rest
    with [bangW], and open it with [bangD]. *)
Lemma uvar_proof Γ n A : Γ !! n = Some A -> ‼Γ ⊢ A.
Proof.
  intros Hn. apply list_elem_of_lookup_2, list_elem_of_split in Hn
    as (Γ1 & Γ2 & ->).
  rewrite map_app. cbn [map].
  ex_to ((‼Γ1 ++ ‼Γ2) ++ [!A]). rewrite <- map_app.
  apply weaken_bangs, bangD, ax.
Qed.

(** ** The translation *)
Theorem curry_howard Γ Δ e A :
  Γ ⨾ Δ ⊢ e ∶ A -> ‼Γ ++ somes Δ ⊢ A.
Proof.
  induction 1.
  - (* lv n *)
    erewrite somes_lone by done. apply weaken_bangs, ax.
  - (* uv n *)
    rewrite somes_lempty, app_nil_r by done. by eapply uvar_proof.
  - (* ƛ e *)
    apply lolliR. ex_to (‼Γ ++ A :: somes Δ). done.
  - (* e1 · e2 *)
    eapply cut_join; [done | done |].
    ex_to (A ⊸ B :: (‼Γ ++ somes Δ2) ++ []). apply lolliL; [done | apply ax].
  - (* ⟨⟩ *)
    rewrite somes_lempty by done. apply weaken_bangs, oneR.
  - (* let𝟙 *)
    eapply cut_join; [done | done |]. by apply oneL.
  - (* ⟪e1, e2⟫ *)
    eapply join; [done |]. by apply tensorR.
  - (* let⊗ *)
    eapply cut_join; [done | done |]. apply tensorL.
    ex_to (‼Γ ++ B :: A :: somes Δ2). done.
  - (* ⟨e1, e2⟩ *)
    by apply withR.
  - (* π₁ e *)
    eapply cut_r; [done |]. apply withL1, ax.
  - (* π₂ e *)
    eapply cut_r; [done |]. apply withL2, ax.
  - (* ι₁ e *)
    by apply plusR1.
  - (* ι₂ e *)
    by apply plusR2.
  - (* case *)
    eapply cut_join; [done | done |]. apply plusL.
    + ex_to (‼Γ ++ A :: somes Δ2). done.
    + ex_to (‼Γ ++ B :: somes Δ2). done.
  - (* ⟨⊤⟩ *)
    apply topR.
  - (* abort e *)
    eapply cut_join; [done | done |]. apply zeroL.
  - (* !e *)
    rewrite somes_lempty, app_nil_r in * by done. by apply bangR.
  - (* let! *)
    eapply cut_join; done.
Qed.

(** ** Consequences for closed programs

    A closed program [[] ⨾ [] ⊢ e ∶ A] translates to a proof of [[] ⊢ A]
    with no hypotheses. *)
Corollary closed_proof e A : [] ⨾ [] ⊢ e ∶ A -> [] ⊢ A.
Proof. apply curry_howard. Qed.

(** By cut elimination ([Intuitionistic/CutElim.v]) that proof can be
    taken cut-free. A cut-free proof of a sequent with no hypotheses
    ends, up to exchange, in a right rule, just as a closed value is an
    introduction form. *)
Corollary closed_proof_cf e A : [] ⨾ [] ⊢ e ∶ A -> [] ⊢cf A.
Proof. intros He. by apply cut_elimination, (closed_proof e). Qed.

(** For instance [swap] yields a cut-free proof that [⊗] commutes. *)
Example swap_proof : [] ⊢cf $0 ⊗ $1 ⊸ $1 ⊗ $0.
Proof. apply (closed_proof_cf swap), swap_typed. Qed.

(** Read contrapositively, the translation turns unprovability into the
    nonexistence of programs. [Intuitionistic/Phase.v] refutes the
    following sequents in a phase model, so no program has these types.

    No closed program duplicates its argument. [LinearTypes.no_copy]
    rules out one particular term, [ƛ ⟪lv 0, lv 0⟫]; this rules out all
    of them. *)
Corollary no_duplicating_program e : ¬ ([] ⨾ [] ⊢ e ∶ $0 ⊸ $0 ⊗ $0).
Proof. intros He. by apply no_duplicator, (closed_proof e). Qed.

(** No closed program discards part of its argument. *)
Corollary no_erasing_program e : ¬ ([] ⨾ [] ⊢ e ∶ $0 ⊗ $1 ⊸ $0).
Proof. intros He. by apply no_eraser, (closed_proof e). Qed.

(** No closed program has the empty type: the language is consistent as
    a logic. *)
Corollary no_zero_program e : ¬ ([] ⨾ [] ⊢ e ∶ 𝟘).
Proof. intros He. by apply consistency, (closed_proof e). Qed.

(** Under [!], duplication is allowed: [LinearTypes.dup] has the type
    that [no_duplicating_program] rules out for an atom. The phase model
    agrees: [!$0 ⊸ !$0 ⊗ !$0] is provable, by [bangC]. *)
Example bang_duplicating_program : ∃ e, [] ⨾ [] ⊢ e ∶ !$0 ⊸ !$0 ⊗ !$0.
Proof. exists dup. apply dup_typed. Qed.
