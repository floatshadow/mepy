(** * Classical.Sequent: the two-sided sequent calculus for CLL

    A classical sequent [Γ ⊢ Δ] has a list of hypotheses _and_ a list of
    conclusions. Read it as: _consuming all of [Γ], we can produce all of
    [Δ]_. Compared with [Intuitionistic/Sequent.v]:

    - every rule now carries a right-hand context [Δ] as well;
    - each connective still has left and right rules, and the rules come in
      mirror-image pairs. The right rule of a connective looks like the left
      rule of its De Morgan dual;
    - multiplicative rules split _both_ sides: [Γ₁ ++ Γ₂ ⊢ Δ₁ ++ Δ₂];
    - negation just moves a formula across the turnstile ([negL], [negR]).

    As in ILL, one inductive family [Γ ⊢[ c ] Δ] covers both calculi.
    [Γ ⊢ Δ] allows [cut], and [Γ ⊢cf Δ] is cut-free. *)

From LinearLogic.Classical Require Export Formula.

Reserved Notation "Γ ⊢[ c ] Δ" (at level 80, c at level 0, no associativity,
  format "Γ  ⊢[ c ]  Δ").

(** ** The rules

    The principal formula always stands at the head of its side ([A :: Γ]
    or [A :: Δ]). Use [ex] to bring it there.

<<
   ------- ax       Γ₁ ⊢ A,Δ₁    A,Γ₂ ⊢ Δ₂          Γ ⊢ Δ   Γ ≡ₚ Γ'  Δ ≡ₚ Δ'
    A ⊢ A           ----------------------- cut    ------------------------- ex
                        Γ₁,Γ₂ ⊢ Δ₁,Δ₂                       Γ' ⊢ Δ'

     Γ ⊢ A,Δ              A,Γ ⊢ Δ
   ----------- ^⊥L     ------------ ^⊥R   (negation: move across ⊢)
   A^⊥,Γ ⊢ Δ           Γ ⊢ A^⊥,Δ

     Γ ⊢ Δ                                                    Γ ⊢ Δ
   ---------- 𝟙L     ------ 𝟙R      ------ ⊥L          ------------ ⊥R
   𝟙,Γ ⊢ Δ            ⊢ 𝟙            ⊥ ⊢               Γ ⊢ ⊥,Δ

   A,B,Γ ⊢ Δ           Γ₁ ⊢ A,Δ₁   Γ₂ ⊢ B,Δ₂
   ----------- ⊗L     ------------------------- ⊗R
   A⊗B,Γ ⊢ Δ           Γ₁,Γ₂ ⊢ A⊗B,Δ₁,Δ₂

   A,Γ₁ ⊢ Δ₁   B,Γ₂ ⊢ Δ₂          Γ ⊢ A,B,Δ
   ------------------------ ⅋L   ------------ ⅋R
    A⅋B,Γ₁,Γ₂ ⊢ Δ₁,Δ₂              Γ ⊢ A⅋B,Δ

   A,Γ ⊢ Δ            B,Γ ⊢ Δ             Γ ⊢ A,Δ   Γ ⊢ B,Δ
   ----------- &L₁   ----------- &L₂     ------------------- &R     ----------- ⊤R
   A&B,Γ ⊢ Δ         A&B,Γ ⊢ Δ              Γ ⊢ A&B,Δ                Γ ⊢ ⊤,Δ

   A,Γ ⊢ Δ   B,Γ ⊢ Δ           Γ ⊢ A,Δ             Γ ⊢ B,Δ
   ------------------ ⊕L     ----------- ⊕R₁     ----------- ⊕R₂     ----------- 𝟘L
     A⊕B,Γ ⊢ Δ                Γ ⊢ A⊕B,Δ           Γ ⊢ A⊕B,Δ           𝟘,Γ ⊢ Δ

   A,Γ ⊢ Δ        Γ ⊢ Δ        !A,!A,Γ ⊢ Δ        ‼Σ ⊢ A,⁇Π
   --------- !D  --------- !W  ------------ !C    ------------ !R
   !A,Γ ⊢ Δ      !A,Γ ⊢ Δ       !A,Γ ⊢ Δ           ‼Σ ⊢ !A,⁇Π

   Γ ⊢ A,Δ        Γ ⊢ Δ        Γ ⊢ ?A,?A,Δ         A,‼Σ ⊢ ⁇Π
   --------- ?D  --------- ?W  ------------ ?C    ------------ ?L
   Γ ⊢ ?A,Δ      Γ ⊢ ?A,Δ       Γ ⊢ ?A,Δ           ?A,‼Σ ⊢ ⁇Π
>>

    The [!] rules on the left mirror the [?] rules on the right. In
    promotion ([!R]) and its dual ([?L]), every other formula in the
    sequent must be a [!] on the left or a [?] on the right. *)
Inductive cll (c : bool) : list cformula -> list cformula -> Prop :=
(* identity and cut *)
| ax A :
    [A] ⊢[c] [A]
| cut Γ₁ Γ₂ Δ₁ Δ₂ A :
    c = true ->
    Γ₁ ⊢[c] A :: Δ₁ ->
    A :: Γ₂ ⊢[c] Δ₂ ->
    Γ₁ ++ Γ₂ ⊢[c] Δ₁ ++ Δ₂
| ex Γ Γ' Δ Δ' :
    Γ ≡ₚ Γ' -> Δ ≡ₚ Δ' ->
    Γ ⊢[c] Δ ->
    Γ' ⊢[c] Δ'
(* negation *)
| negL Γ Δ A :
    Γ ⊢[c] A :: Δ ->
    A^⊥ :: Γ ⊢[c] Δ
| negR Γ Δ A :
    A :: Γ ⊢[c] Δ ->
    Γ ⊢[c] A^⊥ :: Δ
(* multiplicatives *)
| oneL Γ Δ :
    Γ ⊢[c] Δ ->
    𝟙 :: Γ ⊢[c] Δ
| oneR :
    [] ⊢[c] [𝟙]
| botL :
    [⊥] ⊢[c] []
| botR Γ Δ :
    Γ ⊢[c] Δ ->
    Γ ⊢[c] ⊥ :: Δ
| tensorL Γ Δ A B :
    A :: B :: Γ ⊢[c] Δ ->
    A ⊗ B :: Γ ⊢[c] Δ
| tensorR Γ₁ Γ₂ Δ₁ Δ₂ A B :
    Γ₁ ⊢[c] A :: Δ₁ ->
    Γ₂ ⊢[c] B :: Δ₂ ->
    Γ₁ ++ Γ₂ ⊢[c] A ⊗ B :: Δ₁ ++ Δ₂
| parL Γ₁ Γ₂ Δ₁ Δ₂ A B :
    A :: Γ₁ ⊢[c] Δ₁ ->
    B :: Γ₂ ⊢[c] Δ₂ ->
    A ⅋ B :: Γ₁ ++ Γ₂ ⊢[c] Δ₁ ++ Δ₂
| parR Γ Δ A B :
    Γ ⊢[c] A :: B :: Δ ->
    Γ ⊢[c] A ⅋ B :: Δ
(* additives *)
| withL1 Γ Δ A B :
    A :: Γ ⊢[c] Δ ->
    A & B :: Γ ⊢[c] Δ
| withL2 Γ Δ A B :
    B :: Γ ⊢[c] Δ ->
    A & B :: Γ ⊢[c] Δ
| withR Γ Δ A B :
    Γ ⊢[c] A :: Δ ->
    Γ ⊢[c] B :: Δ ->
    Γ ⊢[c] A & B :: Δ
| topR Γ Δ :
    Γ ⊢[c] ⊤ :: Δ
| plusL Γ Δ A B :
    A :: Γ ⊢[c] Δ ->
    B :: Γ ⊢[c] Δ ->
    A ⊕ B :: Γ ⊢[c] Δ
| plusR1 Γ Δ A B :
    Γ ⊢[c] A :: Δ ->
    Γ ⊢[c] A ⊕ B :: Δ
| plusR2 Γ Δ A B :
    Γ ⊢[c] B :: Δ ->
    Γ ⊢[c] A ⊕ B :: Δ
| zeroL Γ Δ :
    𝟘 :: Γ ⊢[c] Δ
(* exponentials *)
| bangD Γ Δ A :
    A :: Γ ⊢[c] Δ ->
    !A :: Γ ⊢[c] Δ
| bangW Γ Δ A :
    Γ ⊢[c] Δ ->
    !A :: Γ ⊢[c] Δ
| bangC Γ Δ A :
    !A :: !A :: Γ ⊢[c] Δ ->
    !A :: Γ ⊢[c] Δ
| bangR Σ Π A :
    ‼Σ ⊢[c] A :: ⁇Π ->
    ‼Σ ⊢[c] !A :: ⁇Π
| whyD Γ Δ A :
    Γ ⊢[c] A :: Δ ->
    Γ ⊢[c] ? A :: Δ
| whyW Γ Δ A :
    Γ ⊢[c] Δ ->
    Γ ⊢[c] ? A :: Δ
| whyC Γ Δ A :
    Γ ⊢[c] ? A :: ? A :: Δ ->
    Γ ⊢[c] ? A :: Δ
| whyL Σ Π A :
    A :: ‼Σ ⊢[c] ⁇Π ->
    ? A :: ‼Σ ⊢[c] ⁇Π
where "Γ ⊢[ c ] Δ" := (cll c Γ Δ) : cll_scope.

Notation "Γ ⊢ Δ" := (cll true Γ Δ) (at level 80, no associativity) : cll_scope.
Notation "Γ ⊢cf Δ" := (cll false Γ Δ) (at level 80, no associativity)
  : cll_scope.

(** Every cut-free proof is a proof. *)
Lemma cf_to_full c Γ Δ : Γ ⊢cf Δ -> Γ ⊢[c] Δ.
Proof.
  (* The cut case is refuted by [false = true]. Every other rule is
     re-applied: [constructor] backtracks over the rules until [auto]
     closes the premises (so [withL1]/[withL2] etc. are told apart).
     It never picks [cut] or [ex], whose cut formula or source contexts
     do not occur in the conclusion; [ex] is handled by [eapply]. *)
  induction 1; try discriminate; solve [constructor; auto | eapply ex; eauto].
Qed.

(** ** Exchange, conveniently

    [ex_to Γ' Δ'] replaces the goal [Γ ⊢ Δ] with [Γ' ⊢ Δ'].
    [solve_Permutation] discharges both permutation side goals. *)
Lemma ex' {c Γ Γ' Δ Δ'} : Γ ⊢[c] Δ -> Γ ≡ₚ Γ' -> Δ ≡ₚ Δ' -> Γ' ⊢[c] Δ'.
Proof. intros; eapply ex; eauto. Qed.

Ltac ex_to G D :=
  apply (ex' (Γ := G) (Δ := D)); [| solve_Permutation | solve_Permutation].

(** ** Structural rules for [‼Σ] and [⁇Π]

    Weakening and contraction, one formula at a time, lift to whole
    contexts [‼Σ] and [⁇Π]. Cut elimination ([Classical/CutElim.v]) needs
    these. *)
Lemma weaken_bangs c Σ Γ Δ : Γ ⊢[c] Δ -> ‼Σ ++ Γ ⊢[c] Δ.
Proof. induction Σ; simpl; auto using bangW. Qed.

Lemma weaken_whys c Π Γ Δ : Γ ⊢[c] Δ -> Γ ⊢[c] ⁇Π ++ Δ.
Proof. induction Π; simpl; auto using whyW. Qed.

(** For contraction, the induction step contracts the two copies of the
    head [!A] with [bangC], parks the survivors in [Γ], and uses the
    induction hypothesis on the rest of [Σ]. *)
Lemma contract_bangs c Σ Γ Δ : ‼Σ ++ ‼Σ ++ Γ ⊢[c] Δ -> ‼Σ ++ Γ ⊢[c] Δ.
Proof.
  revert Γ. induction Σ as [| A Σ IH]; simpl; intros Γ H; [done |].
  apply bangC. ex_to (‼Σ ++ !A :: !A :: Γ) Δ. apply IH.
  ex_to (!A :: ‼Σ ++ !A :: ‼Σ ++ Γ) Δ. exact H.
Qed.

Lemma contract_whys c Π Γ Δ : Γ ⊢[c] ⁇Π ++ ⁇Π ++ Δ -> Γ ⊢[c] ⁇Π ++ Δ.
Proof.
  revert Δ. induction Π as [| A Π IH]; simpl; intros Δ H; [done |].
  apply whyC. ex_to Γ (⁇Π ++ ? A :: ? A :: Δ). apply IH.
  ex_to Γ (? A :: ⁇Π ++ ? A :: ⁇Π ++ Δ). exact H.
Qed.

(** ** Linear implication, derived

    [A ⊸ B] is [A^⊥ ⅋ B]. Its familiar rules are derivable. *)
Lemma lolliR c Γ Δ A B : A :: Γ ⊢[c] B :: Δ -> Γ ⊢[c] (A ⊸ B) :: Δ.
Proof. intros H. apply parR, negR, H. Qed.

Lemma lolliL c Γ₁ Γ₂ Δ₁ Δ₂ A B :
  Γ₁ ⊢[c] A :: Δ₁ -> B :: Γ₂ ⊢[c] Δ₂ -> (A ⊸ B) :: Γ₁ ++ Γ₂ ⊢[c] Δ₁ ++ Δ₂.
Proof. intros H1 H2. apply parL; [apply negL |]; assumption. Qed.

(** ** Examples

    These examples show what the extra room on the right buys.

    The multiplicative rules ([tensorR], [parL], [lolliL], [cut]) split
    both sides into [Γ₁ ++ Γ₂] and [Δ₁ ++ Δ₂]. Unification cannot guess
    such a split, so we name it: [apply (parL _ Γ₁ Γ₂ Δ₁ Δ₂)]. Rocq then
    checks by computation that [[A] ++ [B]] is the goal's [[A; B]]. When
    the principal formula is not at the head, [ex_to] moves it there
    first. *)
Section Examples.
  Variables A B C : cformula.

  (** Excluded middle, in its multiplicative form. Its additive form
      [A ⊕ A^⊥] is _not_ provable. *)
  Example excluded_middle : [] ⊢cf [A ⅋ A^⊥].
  Proof. apply parR. ex_to (@nil cformula) [A^⊥; A]. apply negR, ax. Qed.

  (** Negation is involutive. *)
  Example dne : [A^⊥^⊥] ⊢cf [A].
  Proof. apply negL, negR, ax. Qed.

  Example dni : [A] ⊢cf [A^⊥^⊥].
  Proof. apply negR, negL, ax. Qed.

  (** [⅋] splits the conclusions: an [A ⅋ B] gives an [A] and a [B] on the
      right, side by side. *)
  Example par_split : [A ⅋ B] ⊢cf [A; B].
  Proof. apply (parL _ [] [] [A] [B]); apply ax. Qed.

  (** De Morgan for the multiplicatives. *)
  Example de_morgan_tensor : [(A ⊗ B)^⊥] ⊢cf [A^⊥ ⅋ B^⊥].
  Proof.
    apply parR, negL, (tensorR _ [] [] [A^⊥] [B^⊥]).
    - ex_to (@nil cformula) [A^⊥; A]. apply negR, ax.
    - ex_to (@nil cformula) [B^⊥; B]. apply negR, ax.
  Qed.

  Example de_morgan_par : [A^⊥ ⅋ B^⊥] ⊢cf [(A ⊗ B)^⊥].
  Proof.
    apply negR, tensorL. ex_to [A^⊥ ⅋ B^⊥; A; B] (@nil cformula).
    apply (parL _ [A] [B] [] []); apply negL, ax.
  Qed.

  (** De Morgan for the exponentials: [!] and [?] are dual. Promotion
      ([bangR], [whyL]) also needs its contexts named: here [Σ] and [Π]
      hold at most one formula. *)
  Example de_morgan_bang : [(!A)^⊥] ⊢cf [? A^⊥].
  Proof.
    apply negL, (bangR _ [] [A^⊥]).
    ex_to (@nil cformula) [? A^⊥; A]. apply whyD, negR, ax.
  Qed.

  Example de_morgan_why : [? A^⊥] ⊢cf [(!A)^⊥].
  Proof.
    apply negR. ex_to [? A^⊥; !A] (@nil cformula).
    apply (whyL _ [A] []), negL, bangD, ax.
  Qed.

  (** The intuitionistic examples still work, through the derived [⊸]
      rules. *)
  Example curry : [A ⊗ B ⊸ C] ⊢cf [A ⊸ B ⊸ C].
  Proof.
    apply lolliR, lolliR. ex_to [A ⊗ B ⊸ C; A; B] [C].
    apply (lolliL _ [A; B] [] [] [C]); [| apply ax].
    apply (tensorR _ [A] [B] [] []); apply ax.
  Qed.

  (** [!A] can be duplicated. *)
  Example bang_dup : [!A] ⊢cf [!A ⊗ !A].
  Proof. apply bangC, (tensorR _ [!A] [!A] [] []); apply ax. Qed.

  (** A use of [cut]. [Classical/CutElim.v] shows the cut could be
      avoided. *)
  Example compose : [A ⊸ B; B ⊸ C; A] ⊢ [C].
  Proof.
    ex_to [A ⊸ B; A; B ⊸ C] [C].
    apply (cut _ [A ⊸ B; A] [B ⊸ C] [] [C] B); [done | |].
    - apply (lolliL _ [A] [] [] [B]); apply ax.
    - ex_to [B ⊸ C; B] [C]. apply (lolliL _ [B] [] [] [C]); apply ax.
  Qed.
End Examples.
