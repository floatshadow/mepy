(** * Comparison: ILL inside CLL

    The [Intuitionistic/] and [Classical/] files develop the two logics in
    parallel. This chapter puts them side by side. It proves that every
    ILL proof is also a CLL proof, and that the converse fails.

    ** Sequents

    An ILL sequent [Γ ⊢ C] has exactly one conclusion. A CLL sequent
    [Γ ⊢ Δ] has a list of them. Every ILL rule fits the classical format
    with [Δ] a singleton, which is why the translation below goes through
    rule by rule. Several CLL rules need room for more than one
    conclusion and have no ILL counterpart:

<<
     Γ ⊢ A,B,Δ           Γ ⊢ ?A,?A,Δ          Γ ⊢ A,Δ            A,Γ ⊢ Δ
    ------------ ⅋R     ------------- ?C    ----------- ^⊥L    ----------- ^⊥R
     Γ ⊢ A⅋B,Δ            Γ ⊢ ?A,Δ           A^⊥,Γ ⊢ Δ          Γ ⊢ A^⊥,Δ
>>

    [⅋R] and [?C] have two conclusions in their premise. The negation
    rules move a formula across [⊢]. Applied to a sequent with one
    conclusion, [^⊥L] leaves none and [^⊥R] makes two.

    ** Connectives

    ILL has [𝟙 ⊗ ⊸ ⊤ & 𝟘 ⊕ !] and a constant [⊥]. CLL adds [⅋], [?] and
    an involutive negation [A^⊥], and defines [A ⊸ B] as [A^⊥ ⅋ B].
    In ILL, [⊥] has no rules at all. It is an atom that every model must
    interpret. In CLL, [⊥] is the unit of [⅋], with rules [⊥L] and [⊥R].
    [⊥R] weakens the right-hand side: [Γ ⊢ Δ] gives [Γ ⊢ ⊥, Δ].

    ** Negation

    ILL _defines_ [∼A := A ⊸ ⊥]. One direction of double negation holds,
    [A ⊢ ∼∼A] ([Intuitionistic.Sequent.dni]). The other, [∼∼A ⊢ A], does
    not ([Intuitionistic.Phase.no_dne]). CLL has a primitive negation
    [A^⊥] with [A^⊥^⊥ ⊣⊢ A]. In CLL the defined [A ⊸ ⊥] and the primitive
    [A^⊥] are interderivable ([neg_to_perp], [perp_to_neg] below), so
    [∼∼A ⊢ A] becomes provable once ILL is read classically.

    ** Semantics

    In an intuitionistic phase space ([Intuitionistic/Phase.v]) the
    closure [cl] is a free parameter of the model, and [⊥] may be any
    fact. A classical phase space ([Classical/Phase.v]) fixes a pole [⫫]
    instead. The closure is forced to be [X ↦ X^⊥⊥], and [⊥] denotes
    [{ε}^⊥], which is the pole itself. The intuitionistic countermodel to [∼∼$0 ⊢ $0] takes
    [⊥ = ∅]. Then [∼∼$0] contains every bag, so it is strictly bigger
    than [$0]. A classical model cannot do this, because there [∼∼X] is
    [X^⊥⊥ = X] for every fact [X].

    ** Handling two calculi in one file

    The two [Sequent] files use the same names ([ax], [cut], [tensorR],
    [ex_to], …) and the same notations ([⊢], [⊗], …). We [Require] them
    without importing their names and refer to the rules through the
    module aliases [I] and [C], as in [I.ax] and [C.tensorR]. Only the
    notations are imported. Inside a term, [%ill] and [%cll] select which
    reading of a notation is meant. [cll_scope] is opened last, so
    unannotated notations are classical. *)

From LinearLogic.Intuitionistic Require CutElim.
From LinearLogic.Classical Require Sequent.
From LinearLogic.Intuitionistic Require Import Formula.
From LinearLogic.Classical Require Import Formula.

Module I := LinearLogic.Intuitionistic.Sequent.
Module IPhase := LinearLogic.Intuitionistic.Phase.
Module C := LinearLogic.Classical.Sequent.

Import (notations) I C.

(** Sanity checks: the same notation, read in either scope. *)
Check (λ A B : iformula, [A ⊗ B] ⊢ B ⊗ A)%ill.
Check (λ A B : cformula, [A ⊗ B] ⊢ [B ⊗ A]).

(** ** The embedding

    Each ILL connective goes to the CLL connective of the same name.
    Linear implication goes to the classical [A ⊸ B], which unfolds to
    [A^⊥ ⅋ B]. So the image of [∼A = A ⊸ ⊥] is [(embed A)^⊥ ⅋ ⊥]. *)
Fixpoint embed (A : iformula) : cformula :=
  match A with
  | IAtom p => $p
  | IOne => 𝟙
  | IBot => ⊥
  | ITop => ⊤
  | IZero => 𝟘
  | ITensor A B => embed A ⊗ embed B
  | ILolli A B => embed A ⊸ embed B
  | IWith A B => embed A & embed B
  | IPlus A B => embed A ⊕ embed B
  | IBang A => !embed A
  end.

(** Embedding commutes with banging a whole context. ILL promotion needs
    this to become CLL promotion. *)
Lemma embed_bangs Σ : map embed (‼Σ)%ill = ‼(map embed Σ).
Proof. by rewrite !map_map. Qed.

(** ** Every ILL proof is a CLL proof

    The proof is by induction on the ILL derivation. Each ILL rule is the
    CLL rule of the same name with a one-element conclusion list. Only the
    list shapes need adjusting:

    - two-premise multiplicative rules ([cut], [⊗R], [⊸L]) split the
      conclusions as [Δ₁ ++ Δ₂]. One of the two parts is [[]], so we
      rewrite [[C]] as [[] ++ [C]] or [[A ⊗ B]] as [A ⊗ B :: [] ++ []];
    - ILL promotion [‼Σ ⊢ !A] is CLL promotion [‼Σ ⊢ !A, ⁇Π] with no
      [?]-formulas, [Π = []];
    - the [⊸] rules are the derived [C.lolliR] and [C.lolliL].

    The translation preserves cut-freeness: [c] is the same on both
    sides. *)
Theorem ill_to_cll c Γ A : (Γ ⊢[c] A)%ill -> map embed Γ ⊢[c] [embed A].
Proof.
  induction 1; cbn [map embed] in *; rewrite ?map_app.
  - (* ax *) apply C.ax.
  - (* cut: the cut formula is the only conclusion of the left premise *)
    change [embed C] with ([] ++ [embed C]). by eapply C.cut.
  - (* ex *) eapply C.ex'; [done | by apply Permutation_map | done].
  - (* 𝟙R *) apply C.oneR.
  - (* 𝟙L *) by apply C.oneL.
  - (* ⊗R *) change [embed A ⊗ embed B] with (embed A ⊗ embed B :: [] ++ []).
    by apply C.tensorR.
  - (* ⊗L *) by apply C.tensorL.
  - (* ⊸R *) by apply C.lolliR.
  - (* ⊸L *) change [embed C] with ([] ++ [embed C]). by apply C.lolliL.
  - (* &R *) by apply C.withR.
  - (* &L₁ *) by apply C.withL1.
  - (* &L₂ *) by apply C.withL2.
  - (* ⊤R *) apply C.topR.
  - (* ⊕R₁ *) by apply C.plusR1.
  - (* ⊕R₂ *) by apply C.plusR2.
  - (* ⊕L *) by apply C.plusL.
  - (* 𝟘L *) apply C.zeroL.
  - (* !R: no ?-formulas on the right, Π = [] *)
    rewrite embed_bangs in *. by apply (C.bangR _ _ []).
  - (* !D *) by apply C.bangD.
  - (* !W *) by apply C.bangW.
  - (* !C *) by apply C.bangC.
Qed.

(** ** Two negations agree classically

    In CLL, the defined negation [B ⊸ ⊥ = B^⊥ ⅋ ⊥] and the primitive
    [B^⊥] prove each other. In one direction, [⅋L] sends the [⊥] to a
    branch of its own, where [⊥L] closes it. In the other direction, [⊥R]
    adds a [⊥] to the conclusions. *)
Lemma neg_to_perp B : [B ⊸ ⊥] ⊢cf [B^⊥].
Proof.
  change [B ⊸ ⊥] with (B ⊸ ⊥ :: [] ++ []). change [B^⊥] with ([B^⊥] ++ []).
  apply C.parL; [apply C.ax | apply C.botL].
Qed.

Lemma perp_to_neg B : [B^⊥] ⊢cf [B ⊸ ⊥].
Proof. apply C.parR. C.ex_to [B^⊥] [⊥; B^⊥]. apply C.botR, C.ax. Qed.

(** ** Double-negation elimination, classically

    The image of [∼∼A ⊢ A] has a short cut-free CLL proof:

<<
                   -------- ax
                    A ⊢ A
                  ---------- ⊥R
                   A ⊢ ⊥, A
                 ------------ ⊸R          ----- ⊥L
                  ⊢ A ⊸ ⊥, A               ⊥ ⊢
                 ------------------------------- ⊸L
                       (A ⊸ ⊥) ⊸ ⊥ ⊢ A
>>

    The left premise of [⊸L] is the sequent [⊢ ∼A, A], which has _two_
    conclusions. It "proves [∼A]" while keeping [A] in reserve. In ILL,
    [⊸L] would need [⊢ ∼A] alone, and that sequent is not provable. *)
Lemma classical_dne A : map embed [∼∼A]%ill ⊢cf [embed A].
Proof.
  cbn [map embed].
  change [_ ⊸ ⊥] with (((embed A ⊸ ⊥) ⊸ ⊥) :: [] ++ []).
  change [embed A] with ([embed A] ++ []).
  apply C.lolliL; [apply C.lolliR, C.botR, C.ax | apply C.botL].
Qed.

(** ** CLL is not conservative over ILL

    So the embedding is not full. Some ILL sequents are unprovable but
    have a provable image. [∼∼$0 ⊢ $0] is one: ILL refutes it with a
    phase-space countermodel ([IPhase.no_dne]), and CLL proves it by
    [classical_dne]. *)
Theorem not_conservative :
  ∃ Γ A, ¬ (Γ ⊢ A)%ill ∧ map embed Γ ⊢ [embed A].
Proof.
  exists [∼∼$0]%ill, $0%ill. split.
  - apply IPhase.no_dne.
  - apply C.cf_to_full, classical_dne.
Qed.

(** ** What is known

    The counterexample uses [⊥] essentially: [⊥R] is the step that
    produced the two-conclusion sequent [A ⊢ ⊥, A]. Without [⊥] the
    situation is better. Schellinx (1991) showed that CLL is conservative
    over the fragment of ILL built from [⊗], [⊸], [&], [⊕], [!] and [𝟙]:
    for sequents in this fragment, [map embed Γ ⊢ [embed A]] implies
    [Γ ⊢ A]. The proof starts from a cut-free CLL derivation, which by the
    subformula property only mentions images of ILL formulas, and reads it
    back as an ILL derivation. Extra conclusions do appear in it, for
    instance while [⊸R] is decomposed into [⅋R] and [^⊥R], but without
    [⊥] none of them can be used to prove something ILL cannot. We state
    this as a remark only; it is not formalized here. *)
