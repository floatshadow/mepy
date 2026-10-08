(** * Intuitionistic.Sequent: the sequent calculus for ILL

    A sequent [Γ ⊢ C] says: _consuming exactly the resources in [Γ], we can
    produce [C]_. The context [Γ] is a list. Its order does not matter
    because of the exchange rule [ex] ([≡ₚ] is stdpp's notation for
    [Permutation]). Its multiplicity does matter: [[A; A]] is not [[A]].

    Every connective gets a _right_ rule, which says how to prove it, and a
    _left_ rule, which says how to use it as a hypothesis. This is
    Gentzen's sequent calculus, minus contraction and weakening.

    Two calculi are defined at once:

    - [Γ ⊢ C] is the full calculus, which includes [cut];
    - [Γ ⊢cf C] is the cut-free calculus.

    Both are instances of one inductive family [Γ ⊢[ c ] C]. The boolean
    [c] says whether [cut] may be used. [Intuitionistic/CutElim.v] proves
    that the two calculi derive the same sequents. *)

From LinearLogic.Intuitionistic Require Export Formula.

Reserved Notation "Γ ⊢[ c ] A" (at level 80, c at level 0, no associativity,
  format "Γ  ⊢[ c ]  A").

(** ** The rules

    Read each rule bottom-up, as a step of proof search.

    - [ax] uses exactly one hypothesis, with nothing left over.
    - _Multiplicative_ rules with two premises ([tensorR], [lolliL],
      [cut]) _split_ the context [Γ ++ Δ] between the premises. Each
      resource goes to exactly one of them.
    - _Additive_ rules with two premises ([withR], [plusL]) _copy_ the
      context into both premises. This is fine because only one premise
      will ever "run".
    - [topR] consumes any context, and [zeroL] proves anything.
    - [⊥] has no rules. It behaves like an atom that every model must
      interpret somehow.
    - The four [!] rules are the only place where structural reasoning
      comes back:
      - [bangR] (promotion): [!A] can be built only if every hypothesis is
        banged ([‼Σ]). A reusable proof may use only reusable resources;
      - [bangD] (dereliction): take one copy of [A] out of [!A];
      - [bangW] (weakening): a [!A] may be thrown away;
      - [bangC] (contraction): a [!A] may be duplicated.

<<
   ------ ax         Γ ⊢ A    A,Δ ⊢ C           Γ ⊢ C   Γ ≡ₚ Γ'
    A ⊢ A           ------------------ cut     ---------------- ex
                         Γ,Δ ⊢ C                    Γ' ⊢ C

   ----- 𝟙R           Γ ⊢ C
    ⊢ 𝟙           ------------ 𝟙L
                    𝟙,Γ ⊢ C

   Γ ⊢ A   Δ ⊢ B         A,B,Γ ⊢ C            A,Γ ⊢ B
   -------------- ⊗R    ------------ ⊗L     ------------ ⊸R
    Γ,Δ ⊢ A ⊗ B          A⊗B,Γ ⊢ C           Γ ⊢ A ⊸ B

   Γ ⊢ A   B,Δ ⊢ C      Γ ⊢ A   Γ ⊢ B         A,Γ ⊢ C            B,Γ ⊢ C
   ---------------- ⊸L  -------------- &R  ------------ &L₁  ------------ &L₂
    A⊸B,Γ,Δ ⊢ C           Γ ⊢ A & B         A&B,Γ ⊢ C         A&B,Γ ⊢ C

   ------- ⊤R     Γ ⊢ A             Γ ⊢ B            A,Γ ⊢ C   B,Γ ⊢ C
    Γ ⊢ ⊤      ----------- ⊕R₁   ----------- ⊕R₂   ------------------ ⊕L
                Γ ⊢ A ⊕ B         Γ ⊢ A ⊕ B            A⊕B,Γ ⊢ C

   ---------- 𝟘L    ‼Σ ⊢ A          A,Γ ⊢ C         Γ ⊢ C       !A,!A,Γ ⊢ C
    𝟘,Γ ⊢ C       -------- !R    ---------- !D   ---------- !W  ------------ !C
                   ‼Σ ⊢ !A        !A,Γ ⊢ C       !A,Γ ⊢ C        !A,Γ ⊢ C
>>
*)
Inductive ill (c : bool) : list iformula -> iformula -> Prop :=
(* identity and cut *)
| ax A :
    [A] ⊢[c] A
| cut Γ Δ A C :
    c = true ->
    Γ ⊢[c] A ->
    A :: Δ ⊢[c] C ->
    Γ ++ Δ ⊢[c] C
(* structure: only exchange is unrestricted *)
| ex Γ Γ' C :
    Γ ≡ₚ Γ' ->
    Γ ⊢[c] C ->
    Γ' ⊢[c] C
(* multiplicatives *)
| oneR :
    [] ⊢[c] 𝟙
| oneL Γ C :
    Γ ⊢[c] C ->
    𝟙 :: Γ ⊢[c] C
| tensorR Γ Δ A B :
    Γ ⊢[c] A ->
    Δ ⊢[c] B ->
    Γ ++ Δ ⊢[c] A ⊗ B
| tensorL Γ A B C :
    A :: B :: Γ ⊢[c] C ->
    A ⊗ B :: Γ ⊢[c] C
| lolliR Γ A B :
    A :: Γ ⊢[c] B ->
    Γ ⊢[c] A ⊸ B
| lolliL Γ Δ A B C :
    Γ ⊢[c] A ->
    B :: Δ ⊢[c] C ->
    A ⊸ B :: Γ ++ Δ ⊢[c] C
(* additives *)
| withR Γ A B :
    Γ ⊢[c] A ->
    Γ ⊢[c] B ->
    Γ ⊢[c] A & B
| withL1 Γ A B C :
    A :: Γ ⊢[c] C ->
    A & B :: Γ ⊢[c] C
| withL2 Γ A B C :
    B :: Γ ⊢[c] C ->
    A & B :: Γ ⊢[c] C
| topR Γ :
    Γ ⊢[c] ⊤
| plusR1 Γ A B :
    Γ ⊢[c] A ->
    Γ ⊢[c] A ⊕ B
| plusR2 Γ A B :
    Γ ⊢[c] B ->
    Γ ⊢[c] A ⊕ B
| plusL Γ A B C :
    A :: Γ ⊢[c] C ->
    B :: Γ ⊢[c] C ->
    A ⊕ B :: Γ ⊢[c] C
| zeroL Γ C :
    𝟘 :: Γ ⊢[c] C
(* exponentials *)
| bangR Σ A :
    ‼Σ ⊢[c] A ->
    ‼Σ ⊢[c] !A
| bangD Γ A C :
    A :: Γ ⊢[c] C ->
    !A :: Γ ⊢[c] C
| bangW Γ A C :
    Γ ⊢[c] C ->
    !A :: Γ ⊢[c] C
| bangC Γ A C :
    !A :: !A :: Γ ⊢[c] C ->
    !A :: Γ ⊢[c] C
where "Γ ⊢[ c ] A" := (ill c Γ A) : ill_scope.

Notation "Γ ⊢ A" := (ill true Γ A) (at level 80, no associativity) : ill_scope.
Notation "Γ ⊢cf A" := (ill false Γ A) (at level 80, no associativity)
  : ill_scope.

(** [cut] is the only rule that mentions [c]. In the cut-free calculus its
    side condition [false = true] can never be met. So every cut-free proof
    is also a proof, with or without cut. *)
Lemma cf_to_full c Γ A : Γ ⊢cf A -> Γ ⊢[c] A.
Proof.
  (* [discriminate] refutes the cut case. Every other rule is re-applied
     to the induction hypotheses; [eauto using ill] finds the matching
     constructor. *)
  induction 1; try discriminate; eauto using ill.
Qed.

(** ** Exchange, conveniently

    [ex_to Γ'] replaces the goal [Γ ⊢ C] with [Γ' ⊢ C], and stdpp's
    reflective [solve_Permutation] proves [Γ' ≡ₚ Γ]. It is the usual way
    to bring the principal formula to the front, or to split a context
    into [Γ₁ ++ Γ₂] for a multiplicative rule. *)
Lemma ex' {c Γ Γ' C} : Γ ⊢[c] C -> Γ ≡ₚ Γ' -> Γ' ⊢[c] C.
Proof. intros; eapply ex; eauto. Qed.

Ltac ex_to G := apply (ex' (Γ := G)); [| solve_Permutation].

(** ** Structural rules for banged contexts

    [bangW] and [bangC] act on a single formula. Iterating them over a
    whole context [‼Σ] gives the two facts that the completeness proof and
    the Curry–Howard translation rely on. *)

(** Any number of [!]-formulas can be thrown away. *)
Lemma weaken_bangs c Σ Γ C : Γ ⊢[c] C -> ‼Σ ++ Γ ⊢[c] C.
Proof. induction Σ; simpl; auto using bangW. Qed.

(** Two copies of a banged context can be contracted to one. *)
Lemma contract_bangs c Σ Γ C : ‼Σ ++ ‼Σ ++ Γ ⊢[c] C -> ‼Σ ++ Γ ⊢[c] C.
Proof.
  revert Γ. induction Σ as [| A Σ IH]; intros Γ H; [done |]. simpl in *.
  (* park [!A] in [Γ] and use [IH] on [‼Σ]; then contract the two [!A]s
     and rearrange into [H] *)
  ex_to (‼Σ ++ !A :: Γ). apply IH.
  ex_to (!A :: ‼Σ ++ ‼Σ ++ Γ). apply bangC.
  ex_to (!A :: ‼Σ ++ !A :: ‼Σ ++ Γ). exact H.
Qed.

(** ** A derived rule

    _Modus ponens_: one [A ⊸ B] and one [A] give one [B]. This is
    [lolliL] with both premises closed by [ax]. Several examples below
    end with this step. *)
Lemma lolli_mp c A B : [A ⊸ B; A] ⊢[c] B.
Proof. apply (lolliL _ [A] []); apply ax. Qed.

(** ** Examples

    Each example below shows a different rule at work. Stepping through
    them in an IDE is a good way to get a feel for the calculus. *)
Section Examples.
  Variables A B C : iformula.

  (** [⊗] is commutative. *)
  Example tensor_comm : [A ⊗ B] ⊢cf B ⊗ A.
  Proof.
    apply tensorL.
    (* [A; B] ⊢ B ⊗ A: split the context as [B] ++ [A] *)
    ex_to ([B] ++ [A]). apply tensorR; apply ax.
  Qed.

  (** Currying: [⊗] is left adjoint to [⊸]. *)
  Example curry : [A ⊗ B ⊸ C] ⊢cf A ⊸ B ⊸ C.
  Proof.
    apply lolliR, lolliR.
    ex_to (A ⊗ B ⊸ C :: ([A] ++ [B]) ++ []).
    apply lolliL; [apply tensorR |]; apply ax.
  Qed.

  (** The coffee machine: one euro, your choice of drink. Under [withR]
      both branches receive the same context, so the single euro is
      "shared" by the two branches. Only one branch will ever run.

      The machine is offered as a _choice_ [(euro ⊸ coffee) & (euro ⊸
      tea)]. Two separate machines [euro ⊸ coffee; euro ⊸ tea] would not
      work: each branch would have a machine left over, and nothing can
      discard it. *)
  Example vending (euro coffee tea : iformula) :
    [(euro ⊸ coffee) & (euro ⊸ tea); euro] ⊢cf coffee & tea.
  Proof.
    apply withR; [apply withL1 | apply withL2]; apply lolli_mp.
  Qed.

  (** [!A] can be duplicated: the controlled form of contraction. *)
  Example bang_dup : [!A] ⊢cf !A ⊗ !A.
  Proof. apply bangC. change [!A; !A] with ([!A] ++ [!A]). apply tensorR; apply ax. Qed.

  (** [!A] can be thrown away: the controlled form of weakening. *)
  Example bang_drop : [!A; B] ⊢cf B.
  Proof. apply bangW, ax. Qed.

  (** The exponential isomorphism [!(A & B) ⊣⊢ !A ⊗ !B] turns additive
      structure into multiplicative structure. *)
  Example exp_iso_1 : [!(A & B)] ⊢cf !A ⊗ !B.
  Proof.
    apply bangC. change [!(A & B); !(A & B)] with ([!(A & B)] ++ [!(A & B)]).
    (* promotion: the context [!(A & B)] is ‼[A & B] *)
    apply tensorR; apply (bangR _ [A & B]), bangD;
      [apply withL1 | apply withL2]; apply ax.
  Qed.

  Example exp_iso_2 : [!A ⊗ !B] ⊢cf !(A & B).
  Proof.
    apply tensorL. apply (bangR _ [A; B]). simpl. apply withR.
    - apply bangD. ex_to [!B; A]. apply bangW, ax.
    - apply bangW, bangD, ax.
  Qed.

  (** Double-negation introduction holds. Its converse [∼∼A ⊢ A] does
      not; see [Comparison.v]. *)
  Example dni : [A] ⊢cf ∼∼A.
  Proof. apply lolliR, lolli_mp. Qed.

  (** A use of [cut]: chaining two linear implications.
      [Intuitionistic/CutElim.v] shows the cut could be avoided. *)
  Example compose : [A ⊸ B; B ⊸ C; A] ⊢ C.
  Proof.
    ex_to ([A ⊸ B; A] ++ [B ⊸ C]).
    apply (cut _ _ _ B); [reflexivity | apply lolli_mp |].
    ex_to [B ⊸ C; B]. apply lolli_mp.
  Qed.
End Examples.
