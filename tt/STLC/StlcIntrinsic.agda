module STLC.StlcIntrinsic where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)

infix  4 _⊢_
infix  4 _∋_
infixl 5 _◂_

infixr 7 _⇒_

infix  5 ƛ_
infixl 7 _·_
infix  9 `_
infix  9 𝕤_
infix  9 #_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ans  : Type

data Context : Set where
  ∅   : Context
  _◂_ : Context → Type → Context

variable
  A B C : Type
  Γ Δ : Context

data _∋_ : Context → Type → Set where
  𝕫 : Γ ◂ A ∋ A

  𝕤_ : Γ ∋ A
      ---------
    → Γ ◂ B ∋ A

data _⊢_ : Context → Type → Set where

  `_ : Γ ∋ A
      -----
    → Γ ⊢ A

  ƛ_ : Γ ◂ A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B
  
  `yes : Γ ⊢ `ans

  `no : Γ ⊢ `ans

-- PLFA's helper functions on de Bruijn indices
length : Context → ℕ
length ∅        =  zero
length (Γ ◂ _)  =  suc (length Γ)

lookup : {n : ℕ} → (p : n < length Γ) → Type
lookup {(_ ◂ A)} {zero}    (s≤s z≤n)  =  A
lookup {(Γ ◂ _)} {(suc n)} (s≤s p)    =  lookup p

count : {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup p
count {_ ◂ _} {zero}    (s≤s z≤n)  =  𝕫
count {Γ ◂ _} {(suc n)} (s≤s p)    =  𝕤 (count p)

#_ : (n : ℕ)
  → {n∈Γ : True (suc n ≤? length Γ)}
    --------------------------------
  → Γ ⊢ lookup (toWitness n∈Γ)
#_ n {n∈Γ}  =  ` count (toWitness n∈Γ)

Rename Subst Function : Context → Context → Set
Rename   Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A
Subst    Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A
Function Γ Δ = ∀ {A} → Γ ⊢ A → Δ ⊢ A

-- Renaming weakening
ext : Rename Γ Δ → Rename (Γ ◂ B) (Δ ◂ B)
ext ρ 𝕫     = 𝕫
ext ρ (𝕤 x) = 𝕤 (ρ x)

ren : Rename Γ Δ → Function Γ Δ
ren ρ (` x)   = ` (ρ x)
ren ρ (ƛ N)   = ƛ (ren (ext ρ) N)
ren ρ (M · N) = ren ρ M · ren ρ N
ren ρ (`yes)  = `yes
ren ρ (`no)   = `no

-- Substitution weakening
exts : Subst Γ Δ → Subst (Γ ◂ B) (Δ ◂ B)
exts σ 𝕫     = ` 𝕫
exts σ (𝕤 x) = ren 𝕤_ (σ x)

subst : Subst Γ Δ → Function Γ Δ
subst σ (` x)   = σ x
subst σ (ƛ N)   = ƛ (subst (exts σ) N)
subst σ (M · N) = subst σ M · subst σ N
subst σ (`yes)  = `yes
subst σ (`no)   = `no

⟪_⟫ : ∀{Γ Δ A} → Subst Γ Δ → Γ ⊢ A → Δ ⊢ A
⟪ σ ⟫ M = subst σ M

_[_] : ∀ {Γ A B}
  → Γ ◂ B ⊢ A
  → Γ ⊢ B
    ---------
  → Γ ⊢ A
_[_] {Γ} {A} {B} N M =  subst σ N
  where
  σ : ∀ {A} → Γ ◂ B ∋ A → Γ ⊢ A
  σ 𝕫      =  M
  σ (𝕤 x)  =  ` x


infixl 6 _•ₛ_

↑ₛ : Subst Γ (Γ ◂ A)
↑ₛ x = ` (𝕤 x)

_•ₛ_ : Subst Γ Δ → Δ ⊢ A → Subst (Γ ◂ A) Δ
(σ •ₛ M)  𝕫    = M
(σ •ₛ _) (𝕤 x) = σ x

ids : Subst Γ Γ
ids x = ` x




-- Subject reduction is intrinsically encoded by small-step evaluation relation
data Value : Γ ⊢ A → Set where

  V-ƛ : ∀ {N : Γ ◂ A ⊢ B}
      ---------------------------
    → Value (ƛ N)

  V-yes : Value (`yes {Γ})

  V-no :  Value (`no {Γ})


infix 2 _—→_

data _—→_ : (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-·₁ : ∀ {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      ---------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      ---------------
    → V · M —→ V · M′

  β-ƛ : ∀ {N : Γ ◂ A ⊢ B} {W : Γ ⊢ A}
    → Value W
      --------------------
    → (ƛ N) · W —→ N [ W ]

-- transitive closure of evaluation relation
infix  2 _—↠_
infix  1 begin_
infixr 2 _—↠⟨_⟩_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : (M : Γ ⊢ A)
      ------
    → M —↠ M

  step—→ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → M —↠ N
    → L —→ M
      ------
    → L —↠ N

pattern _—→⟨_⟩_ L L—→M M—↠N = step—→ L M—↠N L—→M

begin_ : {M N : Γ ⊢ A}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N

—↠-trans : (L : Γ ⊢ A) {M N : Γ ⊢ A}
  → M —↠ N
  → L —↠ M
    ------
  → L —↠ N
—↠-trans _ M—↠N (L—↠M ∎) = M—↠N
—↠-trans _ M—↠N (L —→⟨ L—→M′ ⟩ M′—↠M) = L —→⟨ L—→M′ ⟩ (—↠-trans _ M—↠N M′—↠M)

_—↠⟨_⟩_ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
  → L —↠ M
  → M —↠ N
    ------
  → L —↠ N
L —↠⟨ L—↠M ⟩ M—↠N = —↠-trans L M—↠N L—↠M

ξ-·₁/—↠ : ∀ {Γ A B} {M M′ : Γ ⊢ A ⇒ B} {N : Γ ⊢ A}
  → M —↠ M′
  → M · N —↠ M′ · N
ξ-·₁/—↠ {N = N} (M—↠M′ ∎) = M—↠M′ · N ∎
ξ-·₁/—↠ {N = N} (step—→ M L—↠M′ M—→L) =
  step—→ (M · N) (ξ-·₁/—↠ L—↠M′) (ξ-·₁ M—→L)

ξ-·₂/—↠ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {N N′ : Γ ⊢ A}
  → Value V
  → N —↠ N′
  → V · N —↠ V · N′
ξ-·₂/—↠ {V = V} V-ƛ (N—↠N′ ∎) = V · N—↠N′ ∎
ξ-·₂/—↠ {V = V} V-ƛ (step—→ N L—↠N′ N—→L) =
  step—→ (V · N) (ξ-·₂/—↠ V-ƛ L—↠N′) (ξ-·₂ V-ƛ N—→L)

-- Progress
data Progress (M : ∅ ⊢ A) : Set where

  step : ∀ {N : ∅ ⊢ A}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M


progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (ƛ M) = done V-ƛ
progress (L · M) with progress L
... | step L—→L′                = step (ξ-·₁ L—→L′)
... | done V-ƛ with progress M
...   | step M—→M′              = step (ξ-·₂ V-ƛ M—→M′)
...   | done VM                 = step (β-ƛ VM)
progress `yes = done V-yes
progress `no = done V-no

-- Termination (proof by logical relation)
ℰ : ∀ {Γ} → (B : Type) → Γ ⊢ B → Set
𝒱 : ∀ {Γ} → (A : Type) → Γ ⊢ A → Set

ℰ {Γ} B M = Σ[ w ∈ Γ ⊢ B ] (Value w) × (𝒱 B w) × (M —↠ w)

𝒱 `ans    `yes      = ⊤
𝒱 `ans    `no       = ⊤
𝒱 `ans     _        = ⊥
𝒱 {Γ} (A ⇒ B) (ƛ N) = ∀ {a : (Γ ⊢ A)} → 𝒱 A a → ℰ B (N [ a ])
𝒱 {Γ} (A ⇒ B) _     = ⊥ 


-- Fundamental theorem of logical relation
-- Stronger version
-- To prove `∅ ⊢ λx. N : A ⇒ B ∈ 𝒱 (A ⇒ B)`, we depends on the properties
-- of open term `N`.
-- The induction hypothesis is to strong in this case.
postulate
  fundamental/strong : ∀ (a : ∅ ⊢ A) → ℰ A a


-- Lemmas to prove the fundamental theorem
𝒱/Value : ∀ {a : Γ ⊢ A} → 𝒱 A a → Value a
𝒱/Value {a = ƛ N}  _ = V-ƛ
𝒱/Value {a = `yes} _ = V-yes
𝒱/Value {a = `no}  _ = V-no

𝒱/ℰ : ∀ {A} {a : Γ ⊢ A} → 𝒱 A a → ℰ A a
𝒱/ℰ {a = w} 𝒱w = ⟨ w , ⟨ 𝒱/Value 𝒱w , ⟨ 𝒱w , w ∎ ⟩ ⟩ ⟩ 

-- We requires a good property on substitution:
-- substition maps free variables in `Γ` to "good values" under `Δ`.
subst/Γ∋x/𝒱 : ∀ (Γ : Context) → Subst Γ ∅ → Set
subst/Γ∋x/𝒱 Γ σ = ∀ (A : Type) → (∋a : Γ ∋ A) → 𝒱 A (σ ∋a)

-- cons a "good value" preserves the "good" property of substitution
cons/subst/Γ∋x/𝒱 : ∀ {Γ A} {a : ∅ ⊢ A} {σ : Subst Γ ∅}
  → subst/Γ∋x/𝒱 Γ σ
  → 𝒱 A a
  --------------
  → subst/Γ∋x/𝒱 (Γ ◂ A) (σ •ₛ a)
cons/subst/Γ∋x/𝒱 σ/𝒱 a/𝒱 _ 𝕫 = a/𝒱
cons/subst/Γ∋x/𝒱 σ/𝒱 a/𝒱 A′ (𝕤 ∋a) = σ/𝒱 A′ ∋a

-- Substitution lemmas
postulate
  subst/ids : ∀ {M : Γ ⊢ A} → ⟪ ids ⟫ M ≡ M
  exts/subst/cons : ∀ (σ : Subst Γ Δ) (N : Γ ◂ A ⊢ B) (V : Δ ⊢ A) 
    → (⟪ exts σ ⟫ N) [ V ] ≡ ⟪ σ •ₛ V ⟫ N

-- Weaker version of fundamental theorem of logical relation.
-- Induction on `Γ ⊢ t : A`
fundamental : ∀ {Γ} {A} {a : Γ ⊢ A} {σ : Subst Γ ∅}
  → (subst/Γ∋x/𝒱 Γ σ)
  → ℰ A (⟪ σ ⟫ a)
-- t = x. x[σ] is a value.
-- By constraints on `σ`, x[σ] ∈ 𝒱 A
fundamental {A = A} {a = ` ∋x} {σ = σ} σ/𝒱 = 𝒱/ℰ (σ/𝒱 A ∋x)
fundamental {a = `yes}         _   = 𝒱/ℰ tt
fundamental {a = `no}          _   = 𝒱/ℰ tt
-- t = ƛx. N. t[σ] is self is a value.
-- The renaming part is to prove t[σ] is a "good value".
-- i.e., ∀ {a : (Γ ⊢ A)} → 𝒱 A a → ℰ B (N [ a ])
fundamental {Γ} {A = A ⇒ B} {ƛ N} {σ} σ/𝒱 =
  ⟨ w , ⟨ V-ƛ , ⟨ subst/ƛ/𝒱 , w ∎ ⟩ ⟩ ⟩ 
  where
  w : ∅ ⊢ A ⇒ B
  w = ⟪ σ ⟫ (ƛ N)
  -- For any `a ∈ 𝒱 A`, we have `σ •ₛ a ∈ Subst (Γ ◂ A) ∅`,
  -- By induction hypothesis, ∃ w ∈ 𝒱 B, ⟪ σ •ₛ a ⟫ N —↠ w.
  -- By β-reduction, f a = (⟪ σ ⟫ λx. N) a —↠ ⟪ σ •ₛ a ⟫ N —↠ w.
  subst/ƛ/𝒱 : ∀ {a : (∅ ⊢ A)} → 𝒱 A a → ℰ B ((⟪ exts σ ⟫ N) [ a ])
  subst/ƛ/𝒱 {a} a/𝒱 with fundamental {Γ ◂ A} {B} {N} {σ •ₛ a} (cons/subst/Γ∋x/𝒱 σ/𝒱 a/𝒱)
  ... | ⟨ w , ⟨ w/Value , ⟨ w/𝒱 , Nσ—↠w ⟩ ⟩ ⟩ 
        rewrite exts/subst/cons σ N a = ⟨ w , ⟨ w/Value , ⟨ w/𝒱 , Nσ—↠w ⟩ ⟩ ⟩
-- t = M · N.
-- By induction hypothesis, we have `∃ M′ ∈ 𝒱 (A ⇒ B)`, `M —↠ M′` and `∃ N′ ∈ 𝒱 A`, `N —↠ N′`
-- By definition of `𝒱 (A ⇒ B)`, `∀ v ∈ 𝒱 A, ∃ w ∈ 𝒱 B, M′ v —↠ w­`. 
fundamental {a = M · N} {σ = σ} σ/𝒱 with fundamental {a = M} σ/𝒱 | fundamental {a = N} σ/𝒱
... | ⟨ M′ , ⟨ V-ƛ {N = M′/body} , ⟨ M′/𝒱 , M—↠M′ ⟩ ⟩ ⟩ | ⟨ N′ , ⟨ N′/Value , ⟨ N′/𝒱 , N—↠N′ ⟩ ⟩ ⟩
      with M′/𝒱 N′/𝒱
...     | ⟨ v , ⟨ v/Value , ⟨ v/𝒱 , M′N′—↠v ⟩ ⟩ ⟩ = 
          ⟨ v , ⟨ v/Value , ⟨ v/𝒱 , MN—↠v ⟩ ⟩ ⟩
        where
        MN—↠v : ⟪ σ ⟫ M · ⟪ σ ⟫ N —↠ v
        MN—↠v = begin
            ⟪ σ ⟫ M · ⟪ σ ⟫ N
          —↠⟨ ξ-·₁/—↠ M—↠M′ ⟩
            M′ · ⟪ σ ⟫ N
          —↠⟨ ξ-·₂/—↠ V-ƛ N—↠N′ ⟩
            M′ · N′
          —→⟨ β-ƛ N′/Value ⟩
            M′/body [ N′ ]
          —↠⟨ M′N′—↠v ⟩
            v
          ∎

ids/∅∋x/𝒱 : subst/Γ∋x/𝒱 ∅ ids
ids/∅∋x/𝒱 A = λ{ () }

termination : ∀ (M : ∅ ⊢ A) → Σ[ w ∈ ∅ ⊢ A ] Value w × (M —↠ w)
termination M with fundamental {a = M} {σ = ids} ids/∅∋x/𝒱
... | ⟨ w , ⟨ w/Value , ⟨ _ , M—↠w ⟩ ⟩ ⟩ 
      rewrite subst/ids {M = M} = ⟨ w , ⟨ w/Value , M—↠w ⟩ ⟩