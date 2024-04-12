------------------------------------------------------------------------
-- A modality with simultaneous support for affine and linear types
------------------------------------------------------------------------

-- It might make sense to replace some of the proofs with automated
-- proofs.

module Graded.Modality.Instances.Linear-or-affine where

import Tools.Algebra
open import Tools.Bool using (T)
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Product
open import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)
open import Tools.Unit

import Graded.Modality
open import Graded.FullReduction.Assumptions
import Graded.Modality.Properties.Addition as Addition
import Graded.Modality.Properties.Meet as Meet
import Graded.Modality.Properties.Multiplication as Multiplication
import Graded.Modality.Properties.PartialOrder as PartialOrder
import Graded.Modality.Properties.Star as Star
open import Graded.Modality.Variant lzero
open import Definition.Typed.Restrictions
open import Graded.Usage.Restrictions

open import Definition.Untyped using (BMΣ; 𝕤; 𝕨)

private variable
  variant : Modality-variant
  trs     : Type-restrictions _
  urs     : Usage-restrictions _

------------------------------------------------------------------------
-- The type

-- Zero, one, at most one, or unlimited.

data Linear-or-affine : Set where
  𝟘 𝟙 ≤𝟙 ≤ω : Linear-or-affine

open Graded.Modality Linear-or-affine
open Tools.Algebra   Linear-or-affine

private variable
  n n₁ n₂ p q r s s₁ s₂ z z₁ z₂ : Linear-or-affine

------------------------------------------------------------------------
-- Basic operations

-- Meet.

infixr 40 _∧_

_∧_ : Linear-or-affine → Linear-or-affine → Linear-or-affine
𝟘  ∧ 𝟘  = 𝟘
𝟙  ∧ 𝟙  = 𝟙
≤ω ∧ _  = ≤ω
_  ∧ ≤ω = ≤ω
_  ∧ _  = ≤𝟙

-- Addition.

infixr 40 _+_

_+_ : Linear-or-affine → Linear-or-affine → Linear-or-affine
𝟘 + q = q
p + 𝟘 = p
_ + _ = ≤ω

-- Multiplication.

infixr 45 _·_

_·_ : Linear-or-affine → Linear-or-affine → Linear-or-affine
𝟘  · _  = 𝟘
_  · 𝟘  = 𝟘
𝟙  · q  = q
p  · 𝟙  = p
≤𝟙 · ≤𝟙 = ≤𝟙
_  · _  = ≤ω

-- A decision procedure for equality.

infix 10 _≟_

_≟_ : Decidable (_≡_ {A = Linear-or-affine})
𝟘  ≟ 𝟘  = yes refl
𝟘  ≟ 𝟙  = no (λ ())
𝟘  ≟ ≤𝟙 = no (λ ())
𝟘  ≟ ≤ω = no (λ ())
𝟙  ≟ 𝟘  = no (λ ())
𝟙  ≟ 𝟙  = yes refl
𝟙  ≟ ≤𝟙 = no (λ ())
𝟙  ≟ ≤ω = no (λ ())
≤𝟙 ≟ 𝟘  = no (λ ())
≤𝟙 ≟ 𝟙  = no (λ ())
≤𝟙 ≟ ≤𝟙 = yes refl
≤𝟙 ≟ ≤ω = no (λ ())
≤ω ≟ 𝟘  = no (λ ())
≤ω ≟ 𝟙  = no (λ ())
≤ω ≟ ≤𝟙 = no (λ ())
≤ω ≟ ≤ω = yes refl

------------------------------------------------------------------------
-- Some properties

-- The inferred ordering relation.

infix 10 _≤_

_≤_ : Linear-or-affine → Linear-or-affine → Set
p ≤ q = p ≡ p ∧ q

-- The quantity ≤ω is smaller than all others.

≤ω≤ : ∀ p → ≤ω ≤ p
≤ω≤ _ = refl

-- 𝟘 is maximal.

𝟘-maximal : 𝟘 ≤ p → p ≡ 𝟘
𝟘-maximal {p = 𝟘} refl = refl

-- 𝟙 is maximal.

𝟙-maximal : 𝟙 ≤ p → p ≡ 𝟙
𝟙-maximal {p = 𝟙} refl = refl

-- The value ≤ω is a left zero for _+_.

+-zeroˡ : LeftZero ≤ω _+_
+-zeroˡ 𝟘  = refl
+-zeroˡ 𝟙  = refl
+-zeroˡ ≤𝟙 = refl
+-zeroˡ ≤ω = refl

-- The value ≤ω is a right zero for _+_.

+-zeroʳ : RightZero ≤ω _+_
+-zeroʳ 𝟘  = refl
+-zeroʳ 𝟙  = refl
+-zeroʳ ≤𝟙 = refl
+-zeroʳ ≤ω = refl

-- The value ≤ω is a zero for _+_.

+-zero : Zero ≤ω _+_
+-zero = +-zeroˡ , +-zeroʳ

-- The sum of two non-zero values is ≤ω.

≢𝟘+≢𝟘 : p ≢ 𝟘 → q ≢ 𝟘 → p + q ≡ ≤ω
≢𝟘+≢𝟘 {p = 𝟘}           𝟘≢𝟘 _   = ⊥-elim (𝟘≢𝟘 refl)
≢𝟘+≢𝟘 {p = 𝟙}  {q = 𝟘}  _   𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 refl)
≢𝟘+≢𝟘 {p = 𝟙}  {q = 𝟙}  _   _   = refl
≢𝟘+≢𝟘 {p = 𝟙}  {q = ≤𝟙} _   _   = refl
≢𝟘+≢𝟘 {p = 𝟙}  {q = ≤ω} _   _   = refl
≢𝟘+≢𝟘 {p = ≤𝟙} {q = 𝟘}  _   𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 refl)
≢𝟘+≢𝟘 {p = ≤𝟙} {q = 𝟙}  _   _   = refl
≢𝟘+≢𝟘 {p = ≤𝟙} {q = ≤𝟙} _   _   = refl
≢𝟘+≢𝟘 {p = ≤𝟙} {q = ≤ω} _   _   = refl
≢𝟘+≢𝟘 {p = ≤ω} {q = 𝟘}  _   𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 refl)
≢𝟘+≢𝟘 {p = ≤ω} {q = 𝟙}  _   _   = refl
≢𝟘+≢𝟘 {p = ≤ω} {q = ≤𝟙} _   _   = refl
≢𝟘+≢𝟘 {p = ≤ω} {q = ≤ω} _   _   = refl

-- If p + q is 𝟙, then either p is 𝟙 and q is 𝟘, or q is 𝟙 and p is 𝟘.

+≡𝟙 : p + q ≡ 𝟙 → p ≡ 𝟙 × q ≡ 𝟘 ⊎ p ≡ 𝟘 × q ≡ 𝟙
+≡𝟙 {p = 𝟘} {q = 𝟙}  refl = inj₂ (refl , refl)
+≡𝟙 {p = 𝟙} {q = 𝟘}  refl = inj₁ (refl , refl)
+≡𝟙 {p = 𝟘} {q = ≤𝟙} ()
+≡𝟙 {p = 𝟘} {q = ≤ω} ()

-- If p ∧ q is 𝟙, then p and q is 𝟙.

∧≡𝟙 : p ∧ q ≡ 𝟙 → p ≡ 𝟙 × q ≡ 𝟙
∧≡𝟙 {p = 𝟙} {q = 𝟙}  _  = refl , refl
∧≡𝟙 {p = 𝟘} {q = 𝟘}  ()
∧≡𝟙 {p = 𝟘} {q = ≤𝟙} ()
∧≡𝟙 {p = 𝟘} {q = ≤ω} ()

-- Multiplication is idempotent.

·-idempotent : Idempotent _·_
·-idempotent 𝟘  = refl
·-idempotent 𝟙  = refl
·-idempotent ≤𝟙 = refl
·-idempotent ≤ω = refl

-- Multiplication is commutative.

·-comm : Commutative _·_
·-comm = λ where
  𝟘 𝟘   → refl
  𝟘 𝟙   → refl
  𝟘 ≤𝟙  → refl
  𝟘 ≤ω  → refl
  𝟙 𝟘   → refl
  𝟙 𝟙   → refl
  𝟙 ≤𝟙  → refl
  𝟙 ≤ω  → refl
  ≤𝟙 𝟘  → refl
  ≤𝟙 𝟙  → refl
  ≤𝟙 ≤𝟙 → refl
  ≤𝟙 ≤ω → refl
  ≤ω 𝟘  → refl
  ≤ω 𝟙  → refl
  ≤ω ≤𝟙 → refl
  ≤ω ≤ω → refl

-- If p is not 𝟘, then ≤ω · p is equal to ≤ω.

≤ω·≢𝟘 : p ≢ 𝟘 → ≤ω · p ≡ ≤ω
≤ω·≢𝟘 {p = 𝟘}  𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 refl)
≤ω·≢𝟘 {p = 𝟙}  _   = refl
≤ω·≢𝟘 {p = ≤𝟙} _   = refl
≤ω·≢𝟘 {p = ≤ω} _   = refl

-- The value of ≤ω · p is not 𝟙.

≤ω·≢𝟙 : ∀ p → ≤ω · p ≢ 𝟙
≤ω·≢𝟙 𝟘  ()
≤ω·≢𝟙 𝟙  ()
≤ω·≢𝟙 ≤𝟙 ()
≤ω·≢𝟙 ≤ω ()

-- If p is not 𝟘, then 𝟙 · p is not 𝟘.

𝟙·≢𝟘 : p ≢ 𝟘 → 𝟙 · p ≢ 𝟘
𝟙·≢𝟘 {p = 𝟘} 𝟘≢𝟘 = 𝟘≢𝟘

-- If p is not 𝟘, then ≤𝟙 · p is not 𝟘.

≤𝟙·≢𝟘 : p ≢ 𝟘 → ≤𝟙 · p ≢ 𝟘
≤𝟙·≢𝟘 {p = 𝟘} 𝟘≢𝟘 = 𝟘≢𝟘

opaque

  -- The grade ≤ω · (p + q) is bounded by ≤ω · q.

  ≤ω·+≤≤ω·ʳ : ∀ p → ≤ω · (p + q) ≤ ≤ω · q
  ≤ω·+≤≤ω·ʳ {q = 𝟘}  𝟘  = refl
  ≤ω·+≤≤ω·ʳ {q = 𝟙}  𝟘  = refl
  ≤ω·+≤≤ω·ʳ {q = ≤𝟙} 𝟘  = refl
  ≤ω·+≤≤ω·ʳ {q = ≤ω} 𝟘  = refl
  ≤ω·+≤≤ω·ʳ {q = 𝟘}  𝟙  = refl
  ≤ω·+≤≤ω·ʳ {q = 𝟙}  𝟙  = refl
  ≤ω·+≤≤ω·ʳ {q = ≤𝟙} 𝟙  = refl
  ≤ω·+≤≤ω·ʳ {q = ≤ω} 𝟙  = refl
  ≤ω·+≤≤ω·ʳ {q = 𝟘}  ≤𝟙 = refl
  ≤ω·+≤≤ω·ʳ {q = 𝟙}  ≤𝟙 = refl
  ≤ω·+≤≤ω·ʳ {q = ≤𝟙} ≤𝟙 = refl
  ≤ω·+≤≤ω·ʳ {q = ≤ω} ≤𝟙 = refl
  ≤ω·+≤≤ω·ʳ {q = 𝟘}  ≤ω = refl
  ≤ω·+≤≤ω·ʳ {q = 𝟙}  ≤ω = refl
  ≤ω·+≤≤ω·ʳ {q = ≤𝟙} ≤ω = refl
  ≤ω·+≤≤ω·ʳ {q = ≤ω} ≤ω = refl

------------------------------------------------------------------------
-- The modality without the star operation

-- The "linear or affine types" semiring with meet

linear-or-affine-semiring-with-meet : Semiring-with-meet
linear-or-affine-semiring-with-meet  = record
  { _+_          = _+_
  ; _·_          = _·_
  ; _∧_          = _∧_
  ; 𝟘            = 𝟘
  ; 𝟙            = 𝟙
  ; ω            = ≤ω
  ; ω≤𝟙          = refl
  ; ω·+≤ω·ʳ      = λ {p = p} → ≤ω·+≤≤ω·ʳ p
  ; is-𝟘?        = _≟ 𝟘
  ; +-·-Semiring = record
    { isSemiringWithoutAnnihilatingZero = record
      { +-isCommutativeMonoid = record
        { isMonoid = record
          { isSemigroup = record
            { isMagma = record
              { isEquivalence = PE.isEquivalence
              ; ∙-cong        = cong₂ _+_
              }
            ; assoc = +-assoc
            }
          ; identity =
                (λ _ → refl)
              , comm∧idˡ⇒idʳ +-comm (λ _ → refl)
          }
        ; comm = +-comm
        }
      ; *-cong = cong₂ _·_
      ; *-assoc = ·-assoc
      ; *-identity =
              ·-identityˡ
            , comm∧idˡ⇒idʳ ·-comm ·-identityˡ
      ; distrib =
            ·-distribˡ-+
          , comm∧distrˡ⇒distrʳ ·-comm ·-distribˡ-+
      }
    ; zero =
          (λ _ → refl)
        , comm∧zeˡ⇒zeʳ ·-comm (λ _ → refl)
    }
  ; ∧-Semilattice = record
    { isBand = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = PE.isEquivalence
          ; ∙-cong        = cong₂ _∧_
          }
        ; assoc = ∧-assoc
        }
      ; idem = λ where
          𝟘  → refl
          𝟙  → refl
          ≤𝟙 → refl
          ≤ω → refl
      }
    ; comm = ∧-comm
    }
  ; ·-distrib-∧ =
        ·-distribˡ-∧
      , comm∧distrˡ⇒distrʳ ·-comm ·-distribˡ-∧
  ; +-distrib-∧ =
        +-distribˡ-∧
      , comm∧distrˡ⇒distrʳ +-comm +-distribˡ-∧
  }
  where
  +-assoc : Associative _+_
  +-assoc = λ where
    𝟘  _  _  → refl
    𝟙  𝟘  _  → refl
    𝟙  𝟙  𝟘  → refl
    𝟙  𝟙  𝟙  → refl
    𝟙  𝟙  ≤𝟙 → refl
    𝟙  𝟙  ≤ω → refl
    𝟙  ≤𝟙 𝟘  → refl
    𝟙  ≤𝟙 𝟙  → refl
    𝟙  ≤𝟙 ≤𝟙 → refl
    𝟙  ≤𝟙 ≤ω → refl
    𝟙  ≤ω 𝟘  → refl
    𝟙  ≤ω 𝟙  → refl
    𝟙  ≤ω ≤𝟙 → refl
    𝟙  ≤ω ≤ω → refl
    ≤𝟙 𝟘  _  → refl
    ≤𝟙 𝟙  𝟘  → refl
    ≤𝟙 𝟙  𝟙  → refl
    ≤𝟙 𝟙  ≤𝟙 → refl
    ≤𝟙 𝟙  ≤ω → refl
    ≤𝟙 ≤𝟙 𝟘  → refl
    ≤𝟙 ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤ω → refl
    ≤𝟙 ≤ω 𝟘  → refl
    ≤𝟙 ≤ω 𝟙  → refl
    ≤𝟙 ≤ω ≤𝟙 → refl
    ≤𝟙 ≤ω ≤ω → refl
    ≤ω 𝟘  _  → refl
    ≤ω 𝟙  𝟘  → refl
    ≤ω 𝟙  𝟙  → refl
    ≤ω 𝟙  ≤𝟙 → refl
    ≤ω 𝟙  ≤ω → refl
    ≤ω ≤𝟙 𝟘  → refl
    ≤ω ≤𝟙 𝟙  → refl
    ≤ω ≤𝟙 ≤𝟙 → refl
    ≤ω ≤𝟙 ≤ω → refl
    ≤ω ≤ω 𝟘  → refl
    ≤ω ≤ω 𝟙  → refl
    ≤ω ≤ω ≤𝟙 → refl
    ≤ω ≤ω ≤ω → refl

  +-comm : Commutative _+_
  +-comm = λ where
    𝟘 𝟘   → refl
    𝟘 𝟙   → refl
    𝟘 ≤𝟙  → refl
    𝟘 ≤ω  → refl
    𝟙 𝟘   → refl
    𝟙 𝟙   → refl
    𝟙 ≤𝟙  → refl
    𝟙 ≤ω  → refl
    ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω → refl
    ≤ω 𝟘  → refl
    ≤ω 𝟙  → refl
    ≤ω ≤𝟙 → refl
    ≤ω ≤ω → refl

  ·-assoc : Associative _·_
  ·-assoc = λ where
    𝟘  _  _  → refl
    𝟙  𝟘  _  → refl
    𝟙  𝟙  𝟘  → refl
    𝟙  𝟙  𝟙  → refl
    𝟙  𝟙  ≤𝟙 → refl
    𝟙  𝟙  ≤ω → refl
    𝟙  ≤𝟙 𝟘  → refl
    𝟙  ≤𝟙 𝟙  → refl
    𝟙  ≤𝟙 ≤𝟙 → refl
    𝟙  ≤𝟙 ≤ω → refl
    𝟙  ≤ω 𝟘  → refl
    𝟙  ≤ω 𝟙  → refl
    𝟙  ≤ω ≤𝟙 → refl
    𝟙  ≤ω ≤ω → refl
    ≤𝟙 𝟘  _  → refl
    ≤𝟙 𝟙  𝟘  → refl
    ≤𝟙 𝟙  𝟙  → refl
    ≤𝟙 𝟙  ≤𝟙 → refl
    ≤𝟙 𝟙  ≤ω → refl
    ≤𝟙 ≤𝟙 𝟘  → refl
    ≤𝟙 ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤ω → refl
    ≤𝟙 ≤ω 𝟘  → refl
    ≤𝟙 ≤ω 𝟙  → refl
    ≤𝟙 ≤ω ≤𝟙 → refl
    ≤𝟙 ≤ω ≤ω → refl
    ≤ω 𝟘  _  → refl
    ≤ω 𝟙  𝟘  → refl
    ≤ω 𝟙  𝟙  → refl
    ≤ω 𝟙  ≤𝟙 → refl
    ≤ω 𝟙  ≤ω → refl
    ≤ω ≤𝟙 𝟘  → refl
    ≤ω ≤𝟙 𝟙  → refl
    ≤ω ≤𝟙 ≤𝟙 → refl
    ≤ω ≤𝟙 ≤ω → refl
    ≤ω ≤ω 𝟘  → refl
    ≤ω ≤ω 𝟙  → refl
    ≤ω ≤ω ≤𝟙 → refl
    ≤ω ≤ω ≤ω → refl

  ·-identityˡ : LeftIdentity 𝟙 _·_
  ·-identityˡ = λ where
    𝟘  → refl
    𝟙  → refl
    ≤𝟙 → refl
    ≤ω → refl

  ·-distribˡ-+ : _·_ DistributesOverˡ _+_
  ·-distribˡ-+ = λ where
    𝟘  _  _  → refl
    𝟙  𝟘  _  → refl
    𝟙  𝟙  𝟘  → refl
    𝟙  𝟙  𝟙  → refl
    𝟙  𝟙  ≤𝟙 → refl
    𝟙  𝟙  ≤ω → refl
    𝟙  ≤𝟙 𝟘  → refl
    𝟙  ≤𝟙 𝟙  → refl
    𝟙  ≤𝟙 ≤𝟙 → refl
    𝟙  ≤𝟙 ≤ω → refl
    𝟙  ≤ω 𝟘  → refl
    𝟙  ≤ω 𝟙  → refl
    𝟙  ≤ω ≤𝟙 → refl
    𝟙  ≤ω ≤ω → refl
    ≤𝟙 𝟘  _  → refl
    ≤𝟙 𝟙  𝟘  → refl
    ≤𝟙 𝟙  𝟙  → refl
    ≤𝟙 𝟙  ≤𝟙 → refl
    ≤𝟙 𝟙  ≤ω → refl
    ≤𝟙 ≤𝟙 𝟘  → refl
    ≤𝟙 ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤ω → refl
    ≤𝟙 ≤ω 𝟘  → refl
    ≤𝟙 ≤ω 𝟙  → refl
    ≤𝟙 ≤ω ≤𝟙 → refl
    ≤𝟙 ≤ω ≤ω → refl
    ≤ω 𝟘  _  → refl
    ≤ω 𝟙  𝟘  → refl
    ≤ω 𝟙  𝟙  → refl
    ≤ω 𝟙  ≤𝟙 → refl
    ≤ω 𝟙  ≤ω → refl
    ≤ω ≤𝟙 𝟘  → refl
    ≤ω ≤𝟙 𝟙  → refl
    ≤ω ≤𝟙 ≤𝟙 → refl
    ≤ω ≤𝟙 ≤ω → refl
    ≤ω ≤ω 𝟘  → refl
    ≤ω ≤ω 𝟙  → refl
    ≤ω ≤ω ≤𝟙 → refl
    ≤ω ≤ω ≤ω → refl

  ∧-assoc : Associative _∧_
  ∧-assoc = λ where
    𝟘  𝟘  𝟘  → refl
    𝟘  𝟘  𝟙  → refl
    𝟘  𝟘  ≤𝟙 → refl
    𝟘  𝟘  ≤ω → refl
    𝟘  𝟙  𝟘  → refl
    𝟘  𝟙  𝟙  → refl
    𝟘  𝟙  ≤𝟙 → refl
    𝟘  𝟙  ≤ω → refl
    𝟘  ≤𝟙 𝟘  → refl
    𝟘  ≤𝟙 𝟙  → refl
    𝟘  ≤𝟙 ≤𝟙 → refl
    𝟘  ≤𝟙 ≤ω → refl
    𝟘  ≤ω 𝟘  → refl
    𝟘  ≤ω 𝟙  → refl
    𝟘  ≤ω ≤𝟙 → refl
    𝟘  ≤ω ≤ω → refl
    𝟙  𝟘  𝟘  → refl
    𝟙  𝟘  𝟙  → refl
    𝟙  𝟘  ≤𝟙 → refl
    𝟙  𝟘  ≤ω → refl
    𝟙  𝟙  𝟘  → refl
    𝟙  𝟙  𝟙  → refl
    𝟙  𝟙  ≤𝟙 → refl
    𝟙  𝟙  ≤ω → refl
    𝟙  ≤𝟙 𝟘  → refl
    𝟙  ≤𝟙 𝟙  → refl
    𝟙  ≤𝟙 ≤𝟙 → refl
    𝟙  ≤𝟙 ≤ω → refl
    𝟙  ≤ω 𝟘  → refl
    𝟙  ≤ω 𝟙  → refl
    𝟙  ≤ω ≤𝟙 → refl
    𝟙  ≤ω ≤ω → refl
    ≤𝟙 𝟘  𝟘  → refl
    ≤𝟙 𝟘  𝟙  → refl
    ≤𝟙 𝟘  ≤𝟙 → refl
    ≤𝟙 𝟘  ≤ω → refl
    ≤𝟙 𝟙  𝟘  → refl
    ≤𝟙 𝟙  𝟙  → refl
    ≤𝟙 𝟙  ≤𝟙 → refl
    ≤𝟙 𝟙  ≤ω → refl
    ≤𝟙 ≤𝟙 𝟘  → refl
    ≤𝟙 ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤ω → refl
    ≤𝟙 ≤ω 𝟘  → refl
    ≤𝟙 ≤ω 𝟙  → refl
    ≤𝟙 ≤ω ≤𝟙 → refl
    ≤𝟙 ≤ω ≤ω → refl
    ≤ω 𝟘  𝟘  → refl
    ≤ω 𝟘  𝟙  → refl
    ≤ω 𝟘  ≤𝟙 → refl
    ≤ω 𝟘  ≤ω → refl
    ≤ω 𝟙  𝟘  → refl
    ≤ω 𝟙  𝟙  → refl
    ≤ω 𝟙  ≤𝟙 → refl
    ≤ω 𝟙  ≤ω → refl
    ≤ω ≤𝟙 𝟘  → refl
    ≤ω ≤𝟙 𝟙  → refl
    ≤ω ≤𝟙 ≤𝟙 → refl
    ≤ω ≤𝟙 ≤ω → refl
    ≤ω ≤ω 𝟘  → refl
    ≤ω ≤ω 𝟙  → refl
    ≤ω ≤ω ≤𝟙 → refl
    ≤ω ≤ω ≤ω → refl

  ∧-comm : Commutative _∧_
  ∧-comm = λ where
    𝟘 𝟘   → refl
    𝟘 𝟙   → refl
    𝟘 ≤𝟙  → refl
    𝟘 ≤ω  → refl
    𝟙 𝟘   → refl
    𝟙 𝟙   → refl
    𝟙 ≤𝟙  → refl
    𝟙 ≤ω  → refl
    ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω → refl
    ≤ω 𝟘  → refl
    ≤ω 𝟙  → refl
    ≤ω ≤𝟙 → refl
    ≤ω ≤ω → refl

  ·-distribˡ-∧ : _·_ DistributesOverˡ _∧_
  ·-distribˡ-∧ = λ where
    𝟘  𝟘  𝟘  → refl
    𝟘  𝟘  𝟙  → refl
    𝟘  𝟘  ≤𝟙 → refl
    𝟘  𝟘  ≤ω → refl
    𝟘  𝟙  𝟘  → refl
    𝟘  𝟙  𝟙  → refl
    𝟘  𝟙  ≤𝟙 → refl
    𝟘  𝟙  ≤ω → refl
    𝟘  ≤𝟙 𝟘  → refl
    𝟘  ≤𝟙 𝟙  → refl
    𝟘  ≤𝟙 ≤𝟙 → refl
    𝟘  ≤𝟙 ≤ω → refl
    𝟘  ≤ω 𝟘  → refl
    𝟘  ≤ω 𝟙  → refl
    𝟘  ≤ω ≤𝟙 → refl
    𝟘  ≤ω ≤ω → refl
    𝟙  𝟘  𝟘  → refl
    𝟙  𝟘  𝟙  → refl
    𝟙  𝟘  ≤𝟙 → refl
    𝟙  𝟘  ≤ω → refl
    𝟙  𝟙  𝟘  → refl
    𝟙  𝟙  𝟙  → refl
    𝟙  𝟙  ≤𝟙 → refl
    𝟙  𝟙  ≤ω → refl
    𝟙  ≤𝟙 𝟘  → refl
    𝟙  ≤𝟙 𝟙  → refl
    𝟙  ≤𝟙 ≤𝟙 → refl
    𝟙  ≤𝟙 ≤ω → refl
    𝟙  ≤ω 𝟘  → refl
    𝟙  ≤ω 𝟙  → refl
    𝟙  ≤ω ≤𝟙 → refl
    𝟙  ≤ω ≤ω → refl
    ≤𝟙 𝟘  𝟘  → refl
    ≤𝟙 𝟘  𝟙  → refl
    ≤𝟙 𝟘  ≤𝟙 → refl
    ≤𝟙 𝟘  ≤ω → refl
    ≤𝟙 𝟙  𝟘  → refl
    ≤𝟙 𝟙  𝟙  → refl
    ≤𝟙 𝟙  ≤𝟙 → refl
    ≤𝟙 𝟙  ≤ω → refl
    ≤𝟙 ≤𝟙 𝟘  → refl
    ≤𝟙 ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤ω → refl
    ≤𝟙 ≤ω 𝟘  → refl
    ≤𝟙 ≤ω 𝟙  → refl
    ≤𝟙 ≤ω ≤𝟙 → refl
    ≤𝟙 ≤ω ≤ω → refl
    ≤ω 𝟘  𝟘  → refl
    ≤ω 𝟘  𝟙  → refl
    ≤ω 𝟘  ≤𝟙 → refl
    ≤ω 𝟘  ≤ω → refl
    ≤ω 𝟙  𝟘  → refl
    ≤ω 𝟙  𝟙  → refl
    ≤ω 𝟙  ≤𝟙 → refl
    ≤ω 𝟙  ≤ω → refl
    ≤ω ≤𝟙 𝟘  → refl
    ≤ω ≤𝟙 𝟙  → refl
    ≤ω ≤𝟙 ≤𝟙 → refl
    ≤ω ≤𝟙 ≤ω → refl
    ≤ω ≤ω 𝟘  → refl
    ≤ω ≤ω 𝟙  → refl
    ≤ω ≤ω ≤𝟙 → refl
    ≤ω ≤ω ≤ω → refl

  +-distribˡ-∧ : _+_ DistributesOverˡ _∧_
  +-distribˡ-∧ = λ where
    𝟘  𝟘  𝟘  → refl
    𝟘  𝟘  𝟙  → refl
    𝟘  𝟘  ≤𝟙 → refl
    𝟘  𝟘  ≤ω → refl
    𝟘  𝟙  𝟘  → refl
    𝟘  𝟙  𝟙  → refl
    𝟘  𝟙  ≤𝟙 → refl
    𝟘  𝟙  ≤ω → refl
    𝟘  ≤𝟙 𝟘  → refl
    𝟘  ≤𝟙 𝟙  → refl
    𝟘  ≤𝟙 ≤𝟙 → refl
    𝟘  ≤𝟙 ≤ω → refl
    𝟘  ≤ω 𝟘  → refl
    𝟘  ≤ω 𝟙  → refl
    𝟘  ≤ω ≤𝟙 → refl
    𝟘  ≤ω ≤ω → refl
    𝟙  𝟘  𝟘  → refl
    𝟙  𝟘  𝟙  → refl
    𝟙  𝟘  ≤𝟙 → refl
    𝟙  𝟘  ≤ω → refl
    𝟙  𝟙  𝟘  → refl
    𝟙  𝟙  𝟙  → refl
    𝟙  𝟙  ≤𝟙 → refl
    𝟙  𝟙  ≤ω → refl
    𝟙  ≤𝟙 𝟘  → refl
    𝟙  ≤𝟙 𝟙  → refl
    𝟙  ≤𝟙 ≤𝟙 → refl
    𝟙  ≤𝟙 ≤ω → refl
    𝟙  ≤ω 𝟘  → refl
    𝟙  ≤ω 𝟙  → refl
    𝟙  ≤ω ≤𝟙 → refl
    𝟙  ≤ω ≤ω → refl
    ≤𝟙 𝟘  𝟘  → refl
    ≤𝟙 𝟘  𝟙  → refl
    ≤𝟙 𝟘  ≤𝟙 → refl
    ≤𝟙 𝟘  ≤ω → refl
    ≤𝟙 𝟙  𝟘  → refl
    ≤𝟙 𝟙  𝟙  → refl
    ≤𝟙 𝟙  ≤𝟙 → refl
    ≤𝟙 𝟙  ≤ω → refl
    ≤𝟙 ≤𝟙 𝟘  → refl
    ≤𝟙 ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤ω → refl
    ≤𝟙 ≤ω 𝟘  → refl
    ≤𝟙 ≤ω 𝟙  → refl
    ≤𝟙 ≤ω ≤𝟙 → refl
    ≤𝟙 ≤ω ≤ω → refl
    ≤ω 𝟘  𝟘  → refl
    ≤ω 𝟘  𝟙  → refl
    ≤ω 𝟘  ≤𝟙 → refl
    ≤ω 𝟘  ≤ω → refl
    ≤ω 𝟙  𝟘  → refl
    ≤ω 𝟙  𝟙  → refl
    ≤ω 𝟙  ≤𝟙 → refl
    ≤ω 𝟙  ≤ω → refl
    ≤ω ≤𝟙 𝟘  → refl
    ≤ω ≤𝟙 𝟙  → refl
    ≤ω ≤𝟙 ≤𝟙 → refl
    ≤ω ≤𝟙 ≤ω → refl
    ≤ω ≤ω 𝟘  → refl
    ≤ω ≤ω 𝟙  → refl
    ≤ω ≤ω ≤𝟙 → refl
    ≤ω ≤ω ≤ω → refl

instance

  -- The semiring has a well behaved zero

  linear-or-affine-has-well-behaved-zero :
    Has-well-behaved-zero linear-or-affine-semiring-with-meet
  linear-or-affine-has-well-behaved-zero = record
    { non-trivial = λ ()
    ; zero-product = λ where
        {p = 𝟘} _ → inj₁ refl
        {q = 𝟘} _ → inj₂ refl
    ; +-positiveˡ = λ where
        {p = 𝟘} {q = 𝟘}  _  → refl
        {p = 𝟘} {q = 𝟙}  _  → refl
        {p = 𝟘} {q = ≤𝟙} ()
        {p = 𝟘} {q = ≤ω} ()
    ; ∧-positiveˡ = λ where
        {p = 𝟘} {q = 𝟘}  _  → refl
        {p = 𝟘} {q = 𝟙}  _  → refl
        {p = 𝟘} {q = ≤𝟙} ()
        {p = 𝟘} {q = ≤ω} ()
    }

------------------------------------------------------------------------
-- Star

-- Some requirements of a star operation.

Star-requirements :
  (Linear-or-affine → Linear-or-affine → Linear-or-affine →
   Linear-or-affine) →
  Set
Star-requirements _⊛_▷_ =
  (∀ {q r} →                     (≤ω ⊛ q  ▷ r)  ≡ ≤ω) ×
  (∀ {p r} →                     (p  ⊛ ≤ω ▷ r)  ≡ ≤ω) ×
  (∀ {p q} → ¬ (p ≡ 𝟘 × q ≡ 𝟘) → (p  ⊛ q  ▷ ≤ω) ≡ ≤ω) ×
  (∀ {r} →                       (𝟘  ⊛ 𝟘  ▷ r)  ≡ 𝟘)  ×
  (∀ {p} →                       (p  ⊛ 𝟙  ▷ 𝟙)  ≡ ≤ω) ×
  (∀ {p} →                       (p  ⊛ 𝟙  ▷ ≤𝟙) ≡ ≤ω) ×
  (∀ {p} →                       (p  ⊛ ≤𝟙 ▷ 𝟙)  ≡ ≤ω) ×
  (∀ {p} →                       (p  ⊛ ≤𝟙 ▷ ≤𝟙) ≡ ≤ω) ×
                                ((𝟘  ⊛ 𝟙  ▷ 𝟘)  ≤ ≤𝟙) ×
                                ((𝟘  ⊛ ≤𝟙 ▷ 𝟘)  ≤ ≤𝟙) ×
                                ((𝟙  ⊛ 𝟘  ▷ 𝟘)  ≤ ≤𝟙) ×
                                ((≤𝟙 ⊛ 𝟘  ▷ 𝟘)  ≤ ≤𝟙) ×
                                ((𝟙  ⊛ 𝟘  ▷ 𝟙)  ≤ 𝟙)  ×
                                ((𝟙  ⊛ 𝟘  ▷ ≤𝟙) ≤ ≤𝟙) ×
                                ((≤𝟙 ⊛ 𝟘  ▷ 𝟙)  ≤ ≤𝟙) ×
                                ((≤𝟙 ⊛ 𝟘  ▷ ≤𝟙) ≤ ≤𝟙) ×
                                ((𝟙  ⊛ 𝟙  ▷ 𝟘)  ≤ 𝟙)  ×
                                ((𝟙  ⊛ ≤𝟙 ▷ 𝟘)  ≤ ≤𝟙) ×
                                ((≤𝟙 ⊛ 𝟙  ▷ 𝟘)  ≤ ≤𝟙) ×
                                ((≤𝟙 ⊛ ≤𝟙 ▷ 𝟘)  ≤ ≤𝟙)

-- A star operation for a ModalityWithout⊛ for Linear-or-affine for
-- which the zero is 𝟘, the one is 𝟙, addition is _+_, multiplication
-- is _·_, and the meet operation is _∧_ has to satisfy the
-- Star-requirements if certain conditions are satisfied.

Star-requirements-required′ :
  (M : Semiring-with-meet) →
  Semiring-with-meet.𝟘   M ≡ 𝟘 →
  Semiring-with-meet.𝟙   M ≡ 𝟙 →
  Semiring-with-meet._+_ M ≡ _+_ →
  Semiring-with-meet._·_ M ≡ _·_ →
  Semiring-with-meet._∧_ M ≡ _∧_ →
  (_⊛_▷_ :
   Linear-or-affine → Linear-or-affine → Linear-or-affine →
   Linear-or-affine) →
  (∀ p q r → (p ⊛ q ▷ r) ≤ q + r · (p ⊛ q ▷ r)) →
  (∀ p q r → (p ⊛ q ▷ r) ≤ p) →
  (∀ r → _·_ SubDistributesOverʳ (_⊛_▷ r) by _≤_) →
  Star-requirements _⊛_▷_
Star-requirements-required′
  M refl refl refl refl refl star ⊛-ineq₁ ⊛-ineq₂ ·-sub-distribʳ-⊛ =
    (λ {_ _} → ω⊛▷)
  , (λ {_ _} → ⊛ω▷)
  , (λ {_ _} → ⊛▷ω _ _)
  , (λ {r = r} → ≤-antisym
       (begin
          𝟘 ⊛ 𝟘 ▷ r  ≤⟨ ⊛-ineq₂ _ _ _ ⟩
          𝟘          ∎)
       (begin
          𝟘              ≡˘⟨ ·-zeroʳ (𝟘 ⊛ 𝟘 ▷ r) ⟩
          𝟘 ⊛ 𝟘 ▷ r · 𝟘  ≤⟨ ·-sub-distribʳ-⊛ _ _ _ _ ⟩
          𝟘 ⊛ 𝟘 ▷ r      ∎))
  , (λ {p = p} → ≤-antisym
       (begin
          p ⊛ 𝟙 ▷ 𝟙          ≤⟨ ⊛-ineq₁ _ _ _ ⟩
          𝟙 + 𝟙 · p ⊛ 𝟙 ▷ 𝟙  ≈⟨ ≢𝟘+≢𝟘 {p = 𝟙} (λ ()) (𝟙·≢𝟘 ⊛𝟙▷) ⟩
          ≤ω                 ∎)
       (≤ω≤ (p ⊛ 𝟙 ▷ 𝟙)))
  , (λ {p = p} → ≤-antisym
       (begin
          p ⊛ 𝟙 ▷ ≤𝟙           ≤⟨ ⊛-ineq₁ _ _ _ ⟩
          𝟙 + ≤𝟙 · p ⊛ 𝟙 ▷ ≤𝟙  ≈⟨ ≢𝟘+≢𝟘 {p = 𝟙} (λ ()) (≤𝟙·≢𝟘 ⊛𝟙▷) ⟩
          ≤ω                   ∎)
       (≤ω≤ (p ⊛ 𝟙 ▷ ≤𝟙)))
  , (λ {p = p} → ≤-antisym
       (begin
          p ⊛ ≤𝟙 ▷ 𝟙           ≤⟨ ⊛-ineq₁ _ _ _ ⟩
          ≤𝟙 + 𝟙 · p ⊛ ≤𝟙 ▷ 𝟙  ≈⟨ ≢𝟘+≢𝟘 {p = ≤𝟙} (λ ()) (𝟙·≢𝟘 ⊛≤𝟙▷) ⟩
          ≤ω                   ∎)
       (≤ω≤ (p ⊛ ≤𝟙 ▷ 𝟙)))
  , (λ {p = p} → ≤-antisym
       (begin
          p ⊛ ≤𝟙 ▷ ≤𝟙            ≤⟨ ⊛-ineq₁ _ _ _ ⟩
          ≤𝟙 + ≤𝟙 · p ⊛ ≤𝟙 ▷ ≤𝟙  ≈⟨ ≢𝟘+≢𝟘 {p = ≤𝟙} (λ ()) (≤𝟙·≢𝟘 ⊛≤𝟙▷) ⟩
          ≤ω                     ∎)
       (≤ω≤ (p ⊛ ≤𝟙 ▷ ≤𝟙)))
  , ∧-greatest-lower-bound
      (⊛-ineq₂ _ _ _)
      (begin
         𝟘 ⊛ 𝟙 ▷ 𝟘          ≤⟨ ⊛-ineq₁ _ _ _ ⟩
         𝟙 + 𝟘 · 𝟘 ⊛ 𝟙 ▷ 𝟘  ≡⟨⟩
         𝟙                  ∎)
  , (begin
       𝟘 ⊛ ≤𝟙 ▷ 𝟘           ≤⟨ ⊛-ineq₁ _ _ _ ⟩
       ≤𝟙 + 𝟘 · 𝟘 ⊛ ≤𝟙 ▷ 𝟘  ≡⟨⟩
       ≤𝟙                   ∎)
  , ∧-greatest-lower-bound
      (begin
         𝟙 ⊛ 𝟘 ▷ 𝟘          ≤⟨ ⊛-ineq₁ _ _ _ ⟩
         𝟘 + 𝟘 · 𝟙 ⊛ 𝟘 ▷ 𝟘  ≡⟨⟩
         𝟘                  ∎)
      (⊛-ineq₂ _ _ _)
  , ⊛-ineq₂ _ _ _
  , ⊛-ineq₂ _ _ _
  , (begin
       𝟙 ⊛ 𝟘 ▷ ≤𝟙       ≤⟨ ⊛-ineq₁ _ _ _ ⟩
       ≤𝟙 · 𝟙 ⊛ 𝟘 ▷ ≤𝟙  ≤⟨ ·-monotoneʳ {r = ≤𝟙} (⊛-ineq₂ _ _ _) ⟩
       ≤𝟙 · 𝟙           ≡⟨⟩
       ≤𝟙               ∎)
  , ⊛-ineq₂ _ _ _
  , ⊛-ineq₂ _ _ _
  , ⊛-ineq₂ _ _ _
  , (begin
       𝟙 ⊛ ≤𝟙 ▷ 𝟘           ≤⟨ ⊛-ineq₁ _ _ _ ⟩
       ≤𝟙 + 𝟘 · 𝟙 ⊛ ≤𝟙 ▷ 𝟘  ≡⟨⟩
       ≤𝟙                   ∎)
  , ⊛-ineq₂ _ _ _
  , ⊛-ineq₂ _ _ _
  where
  open Semiring-with-meet M using (·-zeroʳ)
  open PartialOrder M
  open Meet M
  open Multiplication M
  open Tools.Reasoning.PartialOrder ≤-poset

  infix 50 _⊛_▷_

  _⊛_▷_ :
    Linear-or-affine → Linear-or-affine → Linear-or-affine →
    Linear-or-affine
  _⊛_▷_ = star

  ω⊛▷ : ≤ω ⊛ q ▷ r ≡ ≤ω
  ω⊛▷ {q = q} {r = r} = ≤-antisym
    (begin
       ≤ω ⊛ q ▷ r  ≤⟨ ⊛-ineq₂ _ _ _ ⟩
       ≤ω          ∎)
    (≤ω≤ (≤ω ⊛ q ▷ r))

  ⊛ω▷ : p ⊛ ≤ω ▷ r ≡ ≤ω
  ⊛ω▷ {p = p} {r = r} = ≤-antisym
    (begin
       p ⊛ ≤ω ▷ r           ≤⟨ ⊛-ineq₁ _ _ _ ⟩
       ≤ω + r · p ⊛ ≤ω ▷ r  ≡⟨ +-zeroˡ (r · _) ⟩
       ≤ω                   ∎)
    (≤ω≤ (p ⊛ ≤ω ▷ r))

  𝟙⊛▷ : 𝟙 ⊛ q ▷ r ≢ 𝟘
  𝟙⊛▷ {q = q} {r = r} 𝟙⊛▷≡𝟘 =
    case begin
      𝟘                ≡⟨⟩
      𝟘 · ≤ω           ≡˘⟨ cong (_· _) 𝟙⊛▷≡𝟘 ⟩
      𝟙 ⊛ q ▷ r · ≤ω   ≤⟨ ·-sub-distribʳ-⊛ _ _ _ _ ⟩
      ≤ω ⊛ q · ≤ω ▷ r  ≡⟨ ω⊛▷ ⟩
      ≤ω               ∎
    of λ ()

  ≤𝟙⊛▷ : ≤𝟙 ⊛ q ▷ r ≢ 𝟘
  ≤𝟙⊛▷ {q = q} {r = r} ≤𝟙⊛▷≡𝟘 =
    case begin
      𝟘                ≡⟨⟩
      𝟘 · ≤ω           ≡˘⟨ cong (_· _) ≤𝟙⊛▷≡𝟘 ⟩
      ≤𝟙 ⊛ q ▷ r · ≤ω  ≤⟨ ·-sub-distribʳ-⊛ _ _ _ _ ⟩
      ≤ω ⊛ q · ≤ω ▷ r  ≡⟨ ω⊛▷ ⟩
      ≤ω               ∎
    of λ ()

  ⊛𝟙▷ : p ⊛ 𝟙 ▷ r ≢ 𝟘
  ⊛𝟙▷ {p = p} {r = r} ⊛𝟙▷≡𝟘 =
    case begin
      𝟘                  ≡⟨⟩
      𝟘 · ≤ω             ≡˘⟨ cong (_· _) ⊛𝟙▷≡𝟘 ⟩
      p ⊛ 𝟙 ▷ r · ≤ω     ≤⟨ ·-sub-distribʳ-⊛ _ _ _ _ ⟩
      (p · ≤ω) ⊛ ≤ω ▷ r  ≡⟨ ⊛ω▷ ⟩
      ≤ω                 ∎
    of λ ()

  ⊛≤𝟙▷ : p ⊛ ≤𝟙 ▷ r ≢ 𝟘
  ⊛≤𝟙▷ {p = p} {r = r} ⊛≤𝟙▷≡𝟘 =
    case begin
      𝟘                  ≡⟨⟩
      𝟘 · ≤ω             ≡˘⟨ cong (_· _) ⊛≤𝟙▷≡𝟘 ⟩
      p ⊛ ≤𝟙 ▷ r · ≤ω    ≤⟨ ·-sub-distribʳ-⊛ _ _ _ _ ⟩
      (p · ≤ω) ⊛ ≤ω ▷ r  ≡⟨ ⊛ω▷ ⟩
      ≤ω                 ∎
    of λ ()

  ⊛▷ω : ∀ p q → ¬ (p ≡ 𝟘 × q ≡ 𝟘) → (p ⊛ q ▷ ≤ω) ≡ ≤ω
  ⊛▷ω _ ≤ω _      = ⊛ω▷
  ⊛▷ω ≤ω _ _      = ω⊛▷
  ⊛▷ω 𝟘 𝟘 ¬≡𝟘×≡𝟘 = ⊥-elim (¬≡𝟘×≡𝟘 (refl , refl))
  ⊛▷ω p 𝟙 _      = ≤-antisym
    (begin
       p ⊛ 𝟙 ▷ ≤ω           ≤⟨ ⊛-ineq₁ _ _ _ ⟩
       𝟙 + ≤ω · p ⊛ 𝟙 ▷ ≤ω  ≡⟨ cong (𝟙 +_) (≤ω·≢𝟘 ⊛𝟙▷) ⟩
       𝟙 + ≤ω               ≡⟨⟩
       ≤ω                   ∎)
    (≤ω≤ (p ⊛ 𝟙 ▷ ≤ω))
  ⊛▷ω p ≤𝟙 _ = ≤-antisym
    (begin
       p ⊛ ≤𝟙 ▷ ≤ω            ≤⟨ ⊛-ineq₁ _ _ _ ⟩
       ≤𝟙 + ≤ω · p ⊛ ≤𝟙 ▷ ≤ω  ≡⟨ cong (≤𝟙 +_) (≤ω·≢𝟘 ⊛≤𝟙▷) ⟩
       ≤𝟙 + ≤ω                ≡⟨⟩
       ≤ω                     ∎)
    (≤ω≤ (p ⊛ 𝟙 ▷ ≤ω))
  ⊛▷ω 𝟙 𝟘 _ = ≤-antisym
    (begin
       𝟙 ⊛ 𝟘 ▷ ≤ω       ≤⟨ ⊛-ineq₁ _ _ _ ⟩
       ≤ω · 𝟙 ⊛ 𝟘 ▷ ≤ω  ≈⟨ ≤ω·≢𝟘 𝟙⊛▷ ⟩
       ≤ω               ∎)
    (≤ω≤ (𝟙 ⊛ 𝟘 ▷ ≤ω))
  ⊛▷ω ≤𝟙 𝟘 _ = ≤-antisym
    (begin
       ≤𝟙 ⊛ 𝟘 ▷ ≤ω       ≤⟨ ⊛-ineq₁ _ _ _ ⟩
       ≤ω · ≤𝟙 ⊛ 𝟘 ▷ ≤ω  ≈⟨ ≤ω·≢𝟘 ≤𝟙⊛▷ ⟩
       ≤ω                ∎)
    (≤ω≤ (≤𝟙 ⊛ 𝟘 ▷ ≤ω))

-- Every natrec-star operator for linear-or-affine-semiring-with-meet
-- has to satisfy the Star-requirements.

Star-requirements-required :
  (has-star : Has-star linear-or-affine-semiring-with-meet) →
  Star-requirements (Has-star._⊛_▷_ has-star)
Star-requirements-required has-star =
  Star-requirements-required′
    linear-or-affine-semiring-with-meet refl refl refl refl refl
    _⊛_▷_ ⊛-ineq₁ ⊛-ineq₂ ·-sub-distribʳ-⊛
  where
  open Has-star has-star

-- A "greatest" definition of the star operation.

infix 50 _⊛_▷_

_⊛_▷_ :
  Linear-or-affine → Linear-or-affine → Linear-or-affine →
  Linear-or-affine
p ⊛ q ▷ 𝟘  = p ∧ q
p ⊛ q ▷ 𝟙  = p + ≤ω · q
p ⊛ q ▷ ≤𝟙 = p ∧ ≤ω · q
p ⊛ q ▷ ≤ω = ≤ω · (p ∧ q)

-- A simplification lemma for the star operation.

≤ω⊛▷ : ∀ r → ≤ω ⊛ q ▷ r ≡ ≤ω
≤ω⊛▷          𝟘  = refl
≤ω⊛▷ {q = 𝟘}  𝟙  = refl
≤ω⊛▷ {q = 𝟙}  𝟙  = refl
≤ω⊛▷ {q = ≤𝟙} 𝟙  = refl
≤ω⊛▷ {q = ≤ω} 𝟙  = refl
≤ω⊛▷ {q = 𝟘}  ≤𝟙 = refl
≤ω⊛▷ {q = 𝟙}  ≤𝟙 = refl
≤ω⊛▷ {q = ≤𝟙} ≤𝟙 = refl
≤ω⊛▷ {q = ≤ω} ≤𝟙 = refl
≤ω⊛▷          ≤ω = refl

-- A simplification lemma for the star operation.

⊛≤ω▷ : ∀ r → p ⊛ ≤ω ▷ r ≡ ≤ω
⊛≤ω▷ {p = 𝟘}  𝟘  = refl
⊛≤ω▷ {p = 𝟙}  𝟘  = refl
⊛≤ω▷ {p = ≤𝟙} 𝟘  = refl
⊛≤ω▷ {p = ≤ω} 𝟘  = refl
⊛≤ω▷ {p = 𝟘}  𝟙  = refl
⊛≤ω▷ {p = 𝟙}  𝟙  = refl
⊛≤ω▷ {p = ≤𝟙} 𝟙  = refl
⊛≤ω▷ {p = ≤ω} 𝟙  = refl
⊛≤ω▷ {p = 𝟘}  ≤𝟙 = refl
⊛≤ω▷ {p = 𝟙}  ≤𝟙 = refl
⊛≤ω▷ {p = ≤𝟙} ≤𝟙 = refl
⊛≤ω▷ {p = ≤ω} ≤𝟙 = refl
⊛≤ω▷ {p = 𝟘}  ≤ω = refl
⊛≤ω▷ {p = 𝟙}  ≤ω = refl
⊛≤ω▷ {p = ≤𝟙} ≤ω = refl
⊛≤ω▷ {p = ≤ω} ≤ω = refl

-- A simplification lemma for the star operation.

𝟘⊛𝟘▷ : ∀ r → 𝟘 ⊛ 𝟘 ▷ r ≡ 𝟘
𝟘⊛𝟘▷ 𝟘  = refl
𝟘⊛𝟘▷ 𝟙  = refl
𝟘⊛𝟘▷ ≤𝟙 = refl
𝟘⊛𝟘▷ ≤ω = refl

-- A simplification lemma for the star operation.

⊛▷≤ω : ∀ p q → ¬ (p ≡ 𝟘 × q ≡ 𝟘) → (p ⊛ q ▷ ≤ω) ≡ ≤ω
⊛▷≤ω = λ where
  𝟘  𝟘  ¬≡𝟘×≡𝟘 → ⊥-elim (¬≡𝟘×≡𝟘 (refl , refl))
  𝟙  𝟘  _      → refl
  ≤𝟙 𝟘  _      → refl
  ≤ω 𝟘  _      → refl
  𝟘  𝟙  _      → refl
  𝟙  𝟙  _      → refl
  ≤𝟙 𝟙  _      → refl
  ≤ω 𝟙  _      → refl
  𝟘  ≤𝟙 _      → refl
  𝟙  ≤𝟙 _      → refl
  ≤𝟙 ≤𝟙 _      → refl
  ≤ω ≤𝟙 _      → refl
  p  ≤ω _      → ⊛≤ω▷ {p = p} ≤ω

-- A simplification lemma for the star operation.

⊛𝟙▷𝟙 : ∀ p → p ⊛ 𝟙 ▷ 𝟙 ≡ ≤ω
⊛𝟙▷𝟙 𝟘  = refl
⊛𝟙▷𝟙 𝟙  = refl
⊛𝟙▷𝟙 ≤𝟙 = refl
⊛𝟙▷𝟙 ≤ω = refl

-- A simplification lemma for the star operation.

⊛𝟙▷≤𝟙 : ∀ p → p ⊛ 𝟙 ▷ ≤𝟙 ≡ ≤ω
⊛𝟙▷≤𝟙 𝟘  = refl
⊛𝟙▷≤𝟙 𝟙  = refl
⊛𝟙▷≤𝟙 ≤𝟙 = refl
⊛𝟙▷≤𝟙 ≤ω = refl

-- A simplification lemma for the star operation.

⊛≤𝟙▷𝟙 : ∀ p → p ⊛ ≤𝟙 ▷ 𝟙 ≡ ≤ω
⊛≤𝟙▷𝟙 𝟘  = refl
⊛≤𝟙▷𝟙 𝟙  = refl
⊛≤𝟙▷𝟙 ≤𝟙 = refl
⊛≤𝟙▷𝟙 ≤ω = refl

-- A simplification lemma for the star operation.

⊛≤𝟙▷≤𝟙 : ∀ p → p ⊛ ≤𝟙 ▷ ≤𝟙 ≡ ≤ω
⊛≤𝟙▷≤𝟙 𝟘  = refl
⊛≤𝟙▷≤𝟙 𝟙  = refl
⊛≤𝟙▷≤𝟙 ≤𝟙 = refl
⊛≤𝟙▷≤𝟙 ≤ω = refl

-- The natrec-star operator returns results that are at least as large
-- as those of any other natrec-star operator for
-- linear-or-affine-semiring-with-meet.

⊛-greatest :
  (has-star : Has-star linear-or-affine-semiring-with-meet) →
  ∀ p q r → Has-star._⊛_▷_ has-star p q r ≤ p ⊛ q ▷ r
⊛-greatest has-star =
  case Star-requirements-required has-star of
    λ (≤ω⊛▷′ , ⊛≤ω▷′ , ⊛▷′≤ω , 𝟘⊛𝟘▷′ ,
       ⊛𝟙▷′𝟙 , ⊛𝟙▷′≤𝟙 , ⊛≤𝟙▷′𝟙 , ⊛≤𝟙▷′≤𝟙 ,
       𝟘⊛𝟙▷′𝟘 , 𝟘⊛≤𝟙▷′𝟘 , 𝟙⊛𝟘▷′𝟘 , ≤𝟙⊛𝟘▷′𝟘 ,
       𝟙⊛𝟘▷′𝟙 , 𝟙⊛𝟘▷′≤𝟙 , ≤𝟙⊛𝟘▷′𝟙 , ≤𝟙⊛𝟘▷′≤𝟙 ,
       𝟙⊛𝟙▷′𝟘 , 𝟙⊛≤𝟙▷′𝟘 , ≤𝟙⊛𝟙▷′𝟘 , ≤𝟙⊛≤𝟙▷′𝟘) → λ where
    ≤ω q r → begin
      ≤ω ⊛ q ▷′ r  ≈⟨ ≤ω⊛▷′ ⟩
      ≤ω           ≈˘⟨ ≤ω⊛▷ r ⟩
      ≤ω ⊛ q ▷ r   ∎
    p ≤ω r → begin
      p ⊛ ≤ω ▷′ r  ≈⟨ ⊛≤ω▷′ ⟩
      ≤ω           ≈˘⟨ ⊛≤ω▷ r ⟩
      p ⊛ ≤ω ▷ r   ∎
    𝟘 𝟘 r → begin
      𝟘 ⊛ 𝟘 ▷′ r  ≈⟨ 𝟘⊛𝟘▷′ ⟩
      𝟘           ≈˘⟨ 𝟘⊛𝟘▷ r ⟩
      𝟘 ⊛ 𝟘 ▷ r   ∎
    𝟘 𝟙 ≤ω → begin
      𝟘 ⊛ 𝟙 ▷′ ≤ω  ≈⟨ ⊛▷′≤ω (λ { (_ , ()) }) ⟩
      ≤ω           ≈˘⟨ ⊛▷≤ω 𝟘 𝟙 (λ { (_ , ()) }) ⟩
      𝟘 ⊛ 𝟙 ▷ ≤ω   ∎
    𝟘 ≤𝟙 ≤ω → begin
      𝟘 ⊛ ≤𝟙 ▷′ ≤ω  ≈⟨ ⊛▷′≤ω (λ { (_ , ()) }) ⟩
      ≤ω            ≈˘⟨ ⊛▷≤ω 𝟘 𝟙 (λ { (_ , ()) }) ⟩
      𝟘 ⊛ ≤𝟙 ▷ ≤ω   ∎
    𝟙 q ≤ω → begin
      𝟙 ⊛ q ▷′ ≤ω  ≈⟨ ⊛▷′≤ω (λ { (() , _) }) ⟩
      ≤ω           ≈˘⟨ ⊛▷≤ω 𝟙 q (λ { (() , _) }) ⟩
      𝟙 ⊛ q ▷ ≤ω   ∎
    ≤𝟙 q ≤ω → begin
      ≤𝟙 ⊛ q ▷′ ≤ω  ≈⟨ ⊛▷′≤ω (λ { (() , _) }) ⟩
      ≤ω            ≈˘⟨ ⊛▷≤ω ≤𝟙 q (λ { (() , _) }) ⟩
      ≤𝟙 ⊛ q ▷ ≤ω   ∎
    p 𝟙 𝟙 → begin
      p ⊛ 𝟙 ▷′ 𝟙  ≈⟨ ⊛𝟙▷′𝟙 ⟩
      ≤ω          ≈˘⟨ ⊛𝟙▷𝟙 p ⟩
      p ⊛ 𝟙 ▷ 𝟙   ∎
    p ≤𝟙 𝟙 → begin
      p ⊛ ≤𝟙 ▷′ 𝟙  ≈⟨ ⊛≤𝟙▷′𝟙 ⟩
      ≤ω           ≈˘⟨ ⊛≤𝟙▷𝟙 p ⟩
      p ⊛ ≤𝟙 ▷ 𝟙   ∎
    p 𝟙 ≤𝟙 → begin
      p ⊛ 𝟙 ▷′ ≤𝟙  ≈⟨ ⊛𝟙▷′≤𝟙 ⟩
      ≤ω           ≈˘⟨ ⊛𝟙▷≤𝟙 p ⟩
      p ⊛ 𝟙 ▷ ≤𝟙   ∎
    p ≤𝟙 ≤𝟙 → begin
      p ⊛ ≤𝟙 ▷′ ≤𝟙  ≈⟨ ⊛≤𝟙▷′≤𝟙 ⟩
      ≤ω            ≈˘⟨ ⊛≤𝟙▷≤𝟙 p ⟩
      p ⊛ ≤𝟙 ▷ ≤𝟙   ∎
    𝟘 𝟙 𝟘 → begin
      𝟘 ⊛ 𝟙 ▷′ 𝟘  ≤⟨ 𝟘⊛𝟙▷′𝟘 ⟩
      ≤𝟙          ∎
    𝟘 ≤𝟙 𝟘 → begin
      𝟘 ⊛ ≤𝟙 ▷′ 𝟘  ≤⟨ 𝟘⊛≤𝟙▷′𝟘 ⟩
      ≤𝟙           ∎
    𝟙 𝟘 𝟘 → begin
      𝟙 ⊛ 𝟘 ▷′ 𝟘  ≤⟨ 𝟙⊛𝟘▷′𝟘 ⟩
      ≤𝟙          ∎
    ≤𝟙 𝟘 𝟘 → begin
      ≤𝟙 ⊛ 𝟘 ▷′ 𝟘  ≤⟨ ≤𝟙⊛𝟘▷′𝟘 ⟩
      ≤𝟙           ∎
    𝟙 𝟘 𝟙 → begin
      𝟙 ⊛ 𝟘 ▷′ 𝟙  ≤⟨ 𝟙⊛𝟘▷′𝟙 ⟩
      𝟙           ∎
    𝟙 𝟘 ≤𝟙 → begin
      𝟙 ⊛ 𝟘 ▷′ ≤𝟙  ≤⟨ 𝟙⊛𝟘▷′≤𝟙 ⟩
      ≤𝟙           ∎
    ≤𝟙 𝟘 𝟙 → begin
      ≤𝟙 ⊛ 𝟘 ▷′ 𝟙  ≤⟨ ≤𝟙⊛𝟘▷′𝟙 ⟩
      ≤𝟙           ∎
    ≤𝟙 𝟘 ≤𝟙 → begin
      ≤𝟙 ⊛ 𝟘 ▷′ ≤𝟙  ≤⟨ ≤𝟙⊛𝟘▷′≤𝟙 ⟩
      ≤𝟙            ∎
    𝟙 𝟙 𝟘 → begin
      𝟙 ⊛ 𝟙 ▷′ 𝟘  ≤⟨ 𝟙⊛𝟙▷′𝟘 ⟩
      𝟙           ∎
    𝟙 ≤𝟙 𝟘 → begin
      𝟙 ⊛ ≤𝟙 ▷′ 𝟘  ≤⟨ 𝟙⊛≤𝟙▷′𝟘 ⟩
      ≤𝟙           ∎
    ≤𝟙 𝟙 𝟘 → begin
      ≤𝟙 ⊛ 𝟙 ▷′ 𝟘  ≤⟨ ≤𝟙⊛𝟙▷′𝟘 ⟩
      ≤𝟙           ∎
    ≤𝟙 ≤𝟙 𝟘 → begin
      ≤𝟙 ⊛ ≤𝟙 ▷′ 𝟘  ≤⟨ ≤𝟙⊛≤𝟙▷′𝟘 ⟩
      ≤𝟙            ∎
  where
  open Has-star has-star renaming (_⊛_▷_ to _⊛_▷′_)
  open PartialOrder linear-or-affine-semiring-with-meet
  open Tools.Reasoning.PartialOrder ≤-poset

-- The "greatest" star operator defined above is a proper natrec-star
-- operator.

linear-or-affine-has-star :
  Has-star linear-or-affine-semiring-with-meet
linear-or-affine-has-star = record
  { _⊛_▷_                   = _⊛_▷_
  ; ⊛-ineq                  = ⊛-ineq₁ , ⊛-ineq₂
  ; +-sub-interchangeable-⊛ = +-sub-interchangeable-⊛
  ; ·-sub-distribʳ-⊛        = λ r _ _ _ →
                                ≤-reflexive (·-distribʳ-⊛ r _ _ _)
  ; ⊛-sub-distrib-∧         = λ r →
      (λ _ _ _ → ≤-reflexive (⊛-distribˡ-∧ r _ _ _))
    , (λ _ _ _ → ≤-reflexive (⊛-distribʳ-∧ r _ _ _))
  }
  where
  semiring-with-meet = linear-or-affine-semiring-with-meet

  open Semiring-with-meet semiring-with-meet
    hiding (𝟘; 𝟙; _+_; _·_; _∧_; _≤_)
  open PartialOrder semiring-with-meet
  open Addition semiring-with-meet
  open Multiplication semiring-with-meet

  ⊛-ineq₁ : ∀ p q r → p ⊛ q ▷ r ≤ q + r · p ⊛ q ▷ r
  ⊛-ineq₁ = λ where
    𝟘  𝟘  𝟘  → refl
    𝟘  𝟘  𝟙  → refl
    𝟘  𝟘  ≤𝟙 → refl
    𝟘  𝟘  ≤ω → refl
    𝟘  𝟙  𝟘  → refl
    𝟘  𝟙  𝟙  → refl
    𝟘  𝟙  ≤𝟙 → refl
    𝟘  𝟙  ≤ω → refl
    𝟘  ≤𝟙 𝟘  → refl
    𝟘  ≤𝟙 𝟙  → refl
    𝟘  ≤𝟙 ≤𝟙 → refl
    𝟘  ≤𝟙 ≤ω → refl
    𝟘  ≤ω 𝟘  → refl
    𝟘  ≤ω 𝟙  → refl
    𝟘  ≤ω ≤𝟙 → refl
    𝟘  ≤ω ≤ω → refl
    𝟙  𝟘  𝟘  → refl
    𝟙  𝟘  𝟙  → refl
    𝟙  𝟘  ≤𝟙 → refl
    𝟙  𝟘  ≤ω → refl
    𝟙  𝟙  𝟘  → refl
    𝟙  𝟙  𝟙  → refl
    𝟙  𝟙  ≤𝟙 → refl
    𝟙  𝟙  ≤ω → refl
    𝟙  ≤𝟙 𝟘  → refl
    𝟙  ≤𝟙 𝟙  → refl
    𝟙  ≤𝟙 ≤𝟙 → refl
    𝟙  ≤𝟙 ≤ω → refl
    𝟙  ≤ω 𝟘  → refl
    𝟙  ≤ω 𝟙  → refl
    𝟙  ≤ω ≤𝟙 → refl
    𝟙  ≤ω ≤ω → refl
    ≤𝟙 𝟘  𝟘  → refl
    ≤𝟙 𝟘  𝟙  → refl
    ≤𝟙 𝟘  ≤𝟙 → refl
    ≤𝟙 𝟘  ≤ω → refl
    ≤𝟙 𝟙  𝟘  → refl
    ≤𝟙 𝟙  𝟙  → refl
    ≤𝟙 𝟙  ≤𝟙 → refl
    ≤𝟙 𝟙  ≤ω → refl
    ≤𝟙 ≤𝟙 𝟘  → refl
    ≤𝟙 ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤ω → refl
    ≤𝟙 ≤ω 𝟘  → refl
    ≤𝟙 ≤ω 𝟙  → refl
    ≤𝟙 ≤ω ≤𝟙 → refl
    ≤𝟙 ≤ω ≤ω → refl
    ≤ω 𝟘  𝟘  → refl
    ≤ω 𝟘  𝟙  → refl
    ≤ω 𝟘  ≤𝟙 → refl
    ≤ω 𝟘  ≤ω → refl
    ≤ω 𝟙  𝟘  → refl
    ≤ω 𝟙  𝟙  → refl
    ≤ω 𝟙  ≤𝟙 → refl
    ≤ω 𝟙  ≤ω → refl
    ≤ω ≤𝟙 𝟘  → refl
    ≤ω ≤𝟙 𝟙  → refl
    ≤ω ≤𝟙 ≤𝟙 → refl
    ≤ω ≤𝟙 ≤ω → refl
    ≤ω ≤ω 𝟘  → refl
    ≤ω ≤ω 𝟙  → refl
    ≤ω ≤ω ≤𝟙 → refl
    ≤ω ≤ω ≤ω → refl

  ⊛-ineq₂ : ∀ p q r → (p ⊛ q ▷ r) ≤ p
  ⊛-ineq₂ = λ where
    𝟘  𝟘  𝟘  → refl
    𝟘  𝟘  𝟙  → refl
    𝟘  𝟘  ≤𝟙 → refl
    𝟘  𝟘  ≤ω → refl
    𝟘  𝟙  𝟘  → refl
    𝟘  𝟙  𝟙  → refl
    𝟘  𝟙  ≤𝟙 → refl
    𝟘  𝟙  ≤ω → refl
    𝟘  ≤𝟙 𝟘  → refl
    𝟘  ≤𝟙 𝟙  → refl
    𝟘  ≤𝟙 ≤𝟙 → refl
    𝟘  ≤𝟙 ≤ω → refl
    𝟘  ≤ω 𝟘  → refl
    𝟘  ≤ω 𝟙  → refl
    𝟘  ≤ω ≤𝟙 → refl
    𝟘  ≤ω ≤ω → refl
    𝟙  𝟘  𝟘  → refl
    𝟙  𝟘  𝟙  → refl
    𝟙  𝟘  ≤𝟙 → refl
    𝟙  𝟘  ≤ω → refl
    𝟙  𝟙  𝟘  → refl
    𝟙  𝟙  𝟙  → refl
    𝟙  𝟙  ≤𝟙 → refl
    𝟙  𝟙  ≤ω → refl
    𝟙  ≤𝟙 𝟘  → refl
    𝟙  ≤𝟙 𝟙  → refl
    𝟙  ≤𝟙 ≤𝟙 → refl
    𝟙  ≤𝟙 ≤ω → refl
    𝟙  ≤ω 𝟘  → refl
    𝟙  ≤ω 𝟙  → refl
    𝟙  ≤ω ≤𝟙 → refl
    𝟙  ≤ω ≤ω → refl
    ≤𝟙 𝟘  𝟘  → refl
    ≤𝟙 𝟘  𝟙  → refl
    ≤𝟙 𝟘  ≤𝟙 → refl
    ≤𝟙 𝟘  ≤ω → refl
    ≤𝟙 𝟙  𝟘  → refl
    ≤𝟙 𝟙  𝟙  → refl
    ≤𝟙 𝟙  ≤𝟙 → refl
    ≤𝟙 𝟙  ≤ω → refl
    ≤𝟙 ≤𝟙 𝟘  → refl
    ≤𝟙 ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤ω → refl
    ≤𝟙 ≤ω 𝟘  → refl
    ≤𝟙 ≤ω 𝟙  → refl
    ≤𝟙 ≤ω ≤𝟙 → refl
    ≤𝟙 ≤ω ≤ω → refl
    ≤ω 𝟘  𝟘  → refl
    ≤ω 𝟘  𝟙  → refl
    ≤ω 𝟘  ≤𝟙 → refl
    ≤ω 𝟘  ≤ω → refl
    ≤ω 𝟙  𝟘  → refl
    ≤ω 𝟙  𝟙  → refl
    ≤ω 𝟙  ≤𝟙 → refl
    ≤ω 𝟙  ≤ω → refl
    ≤ω ≤𝟙 𝟘  → refl
    ≤ω ≤𝟙 𝟙  → refl
    ≤ω ≤𝟙 ≤𝟙 → refl
    ≤ω ≤𝟙 ≤ω → refl
    ≤ω ≤ω 𝟘  → refl
    ≤ω ≤ω 𝟙  → refl
    ≤ω ≤ω ≤𝟙 → refl
    ≤ω ≤ω ≤ω → refl

  +-sub-interchangeable-⊛ : ∀ r → _+_ SubInterchangeable (_⊛_▷ r) by _≤_
  +-sub-interchangeable-⊛ = λ where
      𝟘 p q p′ q′ → begin
        (p ∧ q) + (p′ ∧ q′)  ≤⟨ +-sub-interchangeable-∧ p _ _ _ ⟩
        (p + p′) ∧ (q + q′)  ∎
      𝟙 p q p′ q′ → begin
        (p + ≤ω · q) + (p′ + ≤ω · q′)  ≈⟨ +-assoc p _ _ ⟩
        p + (≤ω · q + (p′ + ≤ω · q′))  ≈˘⟨ cong (p +_) (+-assoc (≤ω · q) _ _) ⟩
        p + ((≤ω · q + p′) + ≤ω · q′)  ≈⟨ cong (λ q → p + (q + _)) (+-comm _ p′) ⟩
        p + ((p′ + ≤ω · q) + ≤ω · q′)  ≈⟨ cong (p +_) (+-assoc p′ _ _) ⟩
        p + (p′ + (≤ω · q + ≤ω · q′))  ≈˘⟨ +-assoc p _ _ ⟩
        (p + p′) + (≤ω · q + ≤ω · q′)  ≈˘⟨ cong ((p + _) +_) (·-distribˡ-+ ≤ω q _) ⟩
        (p + p′) + ≤ω · (q + q′)       ∎
      ≤𝟙 p q p′ q′ → begin
        (p ∧ ≤ω · q) + (p′ ∧ ≤ω · q′)  ≤⟨ +-sub-interchangeable-∧ p _ _ _ ⟩
        (p + p′) ∧ (≤ω · q + ≤ω · q′)  ≈˘⟨ ∧-congˡ (·-distribˡ-+ ≤ω q _) ⟩
        (p + p′) ∧ ≤ω · (q + q′)       ∎
      ≤ω p q p′ q′ → begin
        ≤ω · (p ∧ q) + ≤ω · (p′ ∧ q′)  ≈˘⟨ ·-distribˡ-+ ≤ω (p ∧ _) _ ⟩
        ≤ω · ((p ∧ q) + (p′ ∧ q′))     ≤⟨ ·-monotoneʳ {r = ≤ω} (+-sub-interchangeable-∧ p _ _ _) ⟩
        ≤ω · ((p + p′) ∧ (q + q′))     ∎
    where
    open Tools.Reasoning.PartialOrder ≤-poset

  ·-distribʳ-⊛ : ∀ r → _·_ DistributesOverʳ (_⊛_▷ r)
  ·-distribʳ-⊛ = λ where
      𝟘 q p p′ →
        (p ∧ p′) · q    ≡⟨ ·-distribʳ-∧ _ p _ ⟩
        p · q ∧ p′ · q  ∎
      𝟙 q p p′ →
        (p + ≤ω · p′) · q      ≡⟨ ·-distribʳ-+ _ p _ ⟩
        p · q + (≤ω · p′) · q  ≡⟨ cong (p · _ +_) (·-assoc ≤ω p′ _) ⟩
        p · q + ≤ω · p′ · q    ∎
      ≤𝟙 q p p′ →
        (p ∧ ≤ω · p′) · q      ≡⟨ ·-distribʳ-∧ _ p _ ⟩
        p · q ∧ (≤ω · p′) · q  ≡⟨ ∧-congˡ (·-assoc ≤ω p′ _) ⟩
        p · q ∧ ≤ω · p′ · q    ∎
      ≤ω q p p′ →
        (≤ω · (p ∧ p′)) · q    ≡⟨ ·-assoc ≤ω (p ∧ _) _ ⟩
        ≤ω · (p ∧ p′) · q      ≡⟨ cong (≤ω ·_) (·-distribʳ-∧ _ p _) ⟩
        ≤ω · (p · q ∧ p′ · q)  ∎
    where
    open Tools.Reasoning.PropositionalEquality

  ⊛-distribˡ-∧ : ∀ r → (_⊛_▷ r) DistributesOverˡ _∧_
  ⊛-distribˡ-∧ = λ where
      𝟘 p _ _  → lemma p _ _
      𝟙 p q q′ →
        p + ≤ω · (q ∧ q′)             ≡⟨ cong (p +_) (·-distribˡ-∧ ≤ω q _) ⟩
        p + (≤ω · q ∧ ≤ω · q′)        ≡⟨ +-distribˡ-∧ p _ _ ⟩
        (p + ≤ω · q) ∧ (p + ≤ω · q′)  ∎
      ≤𝟙 p q q′ →
        p ∧ ≤ω · (q ∧ q′)             ≡⟨ ∧-congˡ (·-distribˡ-∧ ≤ω q _) ⟩
        p ∧ (≤ω · q ∧ ≤ω · q′)        ≡⟨ lemma p _ _ ⟩
        (p ∧ ≤ω · q) ∧ (p ∧ ≤ω · q′)  ∎
      ≤ω p q q′ →
        ≤ω · (p ∧ q ∧ q′)             ≡⟨ cong (≤ω ·_) (lemma p _ _) ⟩
        ≤ω · ((p ∧ q) ∧ (p ∧ q′))     ≡⟨ ·-distribˡ-∧ ≤ω (p ∧ _) _ ⟩
        ≤ω · (p ∧ q) ∧ ≤ω · (p ∧ q′)  ∎
    where
    open Tools.Reasoning.PropositionalEquality

    lemma = λ p q q′ →
      p ∧ (q ∧ q′)        ≡˘⟨ cong (_∧ _) (∧-idem p) ⟩
      (p ∧ p) ∧ (q ∧ q′)  ≡⟨ ∧-assoc p _ _ ⟩
      p ∧ (p ∧ (q ∧ q′))  ≡˘⟨ cong (p ∧_) (∧-assoc p _ _) ⟩
      p ∧ ((p ∧ q) ∧ q′)  ≡⟨ cong (λ q → p ∧ (q ∧ _)) (∧-comm p _) ⟩
      p ∧ ((q ∧ p) ∧ q′)  ≡⟨ cong (p ∧_) (∧-assoc q _ _) ⟩
      p ∧ (q ∧ (p ∧ q′))  ≡˘⟨ ∧-assoc p _ _ ⟩
      (p ∧ q) ∧ (p ∧ q′)  ∎

  ⊛-distribʳ-∧ : ∀ r → (_⊛_▷ r) DistributesOverʳ _∧_
  ⊛-distribʳ-∧ = λ where
      𝟘 _ p _  → lemma _ p _
      𝟙 q p p′ →
        (p ∧ p′) + ≤ω · q             ≡⟨ +-distribʳ-∧ _ p _ ⟩
        (p + ≤ω · q) ∧ (p′ + ≤ω · q)  ∎
      ≤𝟙 q p p′ →
        (p ∧ p′) ∧ ≤ω · q             ≡⟨ lemma _ _ _ ⟩
        (p ∧ ≤ω · q) ∧ (p′ ∧ ≤ω · q)  ∎
      ≤ω q p p′ →
        ≤ω · ((p ∧ p′) ∧ q)           ≡⟨ cong (≤ω ·_) (lemma _ p _) ⟩
        ≤ω · ((p ∧ q) ∧ (p′ ∧ q))     ≡⟨ ·-distribˡ-∧ ≤ω (p ∧ _) _ ⟩
        ≤ω · (p ∧ q) ∧ ≤ω · (p′ ∧ q)  ∎
    where
    open Tools.Reasoning.PropositionalEquality

    lemma = λ q p p′ →
      (p ∧ p′) ∧ q        ≡⟨ ∧-comm _ q ⟩
      q ∧ (p ∧ p′)        ≡⟨ ⊛-distribˡ-∧ 𝟘 q _ _ ⟩
      (q ∧ p) ∧ (q ∧ p′)  ≡⟨ cong₂ _∧_ (∧-comm q _) (∧-comm q _) ⟩
      (p ∧ q) ∧ (p′ ∧ q)  ∎

------------------------------------------------------------------------
-- A modality

-- A (not very good) "linear or affine types" modality.
--
-- See Graded.Modality.Instances.Linear-or-affine.Bad for some
-- examples that illustrate in what sense this modality is not very
-- good. The modality linear-or-affine below does not suffer from
-- these problems (see
-- Graded.Modality.Instances.Linear-or-affine.Good), but note that, at
-- the time of writing, this formalisation does not contain any solid
-- evidence showing that linear-or-affine is "correct".

bad-linear-or-affine : Modality-variant → Modality
bad-linear-or-affine variant = record
  { variant            = variant
  ; semiring-with-meet = linear-or-affine-semiring-with-meet
  ; 𝟘-well-behaved     = λ _ → linear-or-affine-has-well-behaved-zero
  ; has-nr             = λ _ →
                           Star.has-nr _
                             ⦃ has-star = linear-or-affine-has-star ⦄
  }

------------------------------------------------------------------------
-- A variant of the modality with a custom nr function

-- An nr function for Linear-or-affine.
--
-- The value of nr p 𝟘 z s n is defined in the following way:
--
-- * If p = 𝟙, then there are no (non-erased) recursive calls, and the
--   argument is used exactly once in the successor case (excluding
--   erased uses):
--
--     f zero    = f_z
--     f (suc m) = f_s m
--
--   Let us use n + z for the zero case, and n + s for the successor
--   case: the result is a conservative approximation of these two
--   values (their meet).
--
-- * If p = 𝟘, then there are no (non-erased) recursive
--   calls, and the argument is not used (in non-erased positions) in
--   the successor case:
--
--     f zero    = f_z
--     f (suc m) = f_s
--
--   Let us again use n + z for the zero case. For the successor case
--   we use ≤𝟙 · n + s: the argument is not used linearly in the
--   successor case, because it is not used at all, so if n is 𝟙, then
--   the result should be at most ≤𝟙 (not 𝟙, because the function is
--   not linear, and not 𝟘, because that would amount to an erased
--   match on a natural number).
--
-- * If p = ≤𝟙, then there are no (non-erased) recursive calls, and
--   the argument is used at most once in the successor case
--   (excluding erased uses). Let us again use n + z for the zero
--   case, and ≤𝟙 · n + s for the successor case.
--
-- * If p = ≤ω, then there are no (non-erased) recursive calls. In the
--   successor case the argument is used an unlimited number of times,
--   so we use ≤ω · n + s. In the zero case we use n + z, as before.
--
-- All of these cases can be expressed in the following way (note that
-- 𝟙 ∧ 𝟘 and 𝟙 ∧ ≤𝟙 are both equal to ≤𝟙):
--
--   nr p 𝟘 z s n = ((𝟙 ∧ p) · n + s) ∧ (n + z)
--
-- The value of nr p 𝟙 z s n is defined in the following way:
--
-- * If p = 𝟘, then we have linear recursion: the argument is used
--   linearly (n), the successor case can occur an unlimited number of
--   times (≤ω · s), and the zero case occurs once (z).
--
-- * If p is 𝟙, ≤𝟙 or ≤ω, then there is recursion (≤ω · s), the
--   argument can be used in each recursive call (≤ω · n), and the
--   zero case occurs once (z).
--
-- We get the following definition:
--
--   nr p 𝟙 z s n = (𝟙 + p) · n + ≤ω · s + z
--
-- The value of nr p ≤𝟙 z s n is defined in the following way:
--
-- * If p = 𝟘, then we have affine recursion: the argument is used
--   affinely (≤𝟙 · n), the successor case can occur an unlimited
--   number of times (≤ω · s), and the zero case occurs at most once
--   (≤𝟙 · z).
--
-- * If p is 𝟙, ≤𝟙 or ≤ω, then there is recursion (≤ω · s), the
--   argument can be used in each recursive call (≤ω · n), and the
--   zero case occurs at most once (≤𝟙 · z).
--
-- We get the following definition:
--
--   nr p 𝟙 z s n = (≤𝟙 + p) · n + ≤ω · s + ≤𝟙 · z
--
-- Finally we use the following definition for nr p ≤ω z s n:
--
--   nr _ ≤ω z s n = ≤ω · (n + s + z)
--
-- There is recursion (≤ω · s), in the successor case there can be
-- multiple recursive calls (≤ω · n), and the zero case can occur
-- multiple times (≤ω · z).

nr :
  Linear-or-affine → Linear-or-affine →
  Linear-or-affine → Linear-or-affine → Linear-or-affine →
  Linear-or-affine
nr p 𝟘  z s n = ((𝟙 ∧ p) · n + s) ∧ (n + z)
nr p 𝟙  z s n = (𝟙  + p) · n + ≤ω · s +      z
nr p ≤𝟙 z s n = (≤𝟙 + p) · n + ≤ω · s + ≤𝟙 · z
nr _ ≤ω z s n = ≤ω · (n + s + z)

-- The value of nr p r z s n is 𝟘 iff z, s and n are all zero.

nr-𝟘 : ∀ r → nr p r z s n ≡ 𝟘 ⇔ (z ≡ 𝟘 × s ≡ 𝟘 × n ≡ 𝟘)
nr-𝟘 r =
    lemma₁ _ r _ _ _
  , λ { (refl , refl , refl) → lemma₂ _ r }
  where
  lemma₁ : ∀ p r z s n → nr p r z s n ≡ 𝟘 → z ≡ 𝟘 × s ≡ 𝟘 × n ≡ 𝟘
  lemma₁ = λ where
    𝟘  𝟘  𝟘  𝟘  𝟘  refl → refl , refl , refl
    𝟙  𝟘  𝟘  𝟘  𝟘  refl → refl , refl , refl
    ≤𝟙 𝟘  𝟘  𝟘  𝟘  refl → refl , refl , refl
    ≤ω 𝟘  𝟘  𝟘  𝟘  refl → refl , refl , refl
    𝟘  𝟙  𝟘  𝟘  𝟘  refl → refl , refl , refl
    𝟙  𝟙  𝟘  𝟘  𝟘  refl → refl , refl , refl
    ≤𝟙 𝟙  𝟘  𝟘  𝟘  refl → refl , refl , refl
    ≤ω 𝟙  𝟘  𝟘  𝟘  refl → refl , refl , refl
    𝟘  ≤𝟙 𝟘  𝟘  𝟘  refl → refl , refl , refl
    𝟙  ≤𝟙 𝟘  𝟘  𝟘  refl → refl , refl , refl
    ≤𝟙 ≤𝟙 𝟘  𝟘  𝟘  refl → refl , refl , refl
    ≤ω ≤𝟙 𝟘  𝟘  𝟘  refl → refl , refl , refl
    _  ≤ω 𝟘  𝟘  𝟘  refl → refl , refl , refl
    𝟘  𝟘  𝟘  𝟘  𝟙  ()
    𝟘  𝟘  𝟘  𝟘  ≤𝟙 ()
    𝟘  𝟘  𝟘  𝟘  ≤ω ()
    𝟘  𝟘  𝟘  𝟙  𝟘  ()
    𝟘  𝟘  𝟘  𝟙  𝟙  ()
    𝟘  𝟘  𝟘  𝟙  ≤𝟙 ()
    𝟘  𝟘  𝟘  𝟙  ≤ω ()
    𝟘  𝟘  𝟘  ≤𝟙 𝟘  ()
    𝟘  𝟘  𝟘  ≤𝟙 𝟙  ()
    𝟘  𝟘  𝟘  ≤𝟙 ≤𝟙 ()
    𝟘  𝟘  𝟘  ≤𝟙 ≤ω ()
    𝟘  𝟘  𝟘  ≤ω 𝟘  ()
    𝟘  𝟘  𝟘  ≤ω 𝟙  ()
    𝟘  𝟘  𝟘  ≤ω ≤𝟙 ()
    𝟘  𝟘  𝟘  ≤ω ≤ω ()
    𝟘  𝟘  𝟙  𝟘  𝟘  ()
    𝟘  𝟘  𝟙  𝟘  𝟙  ()
    𝟘  𝟘  𝟙  𝟘  ≤𝟙 ()
    𝟘  𝟘  𝟙  𝟘  ≤ω ()
    𝟘  𝟘  𝟙  𝟙  𝟘  ()
    𝟘  𝟘  𝟙  𝟙  𝟙  ()
    𝟘  𝟘  𝟙  𝟙  ≤𝟙 ()
    𝟘  𝟘  𝟙  𝟙  ≤ω ()
    𝟘  𝟘  𝟙  ≤𝟙 𝟘  ()
    𝟘  𝟘  𝟙  ≤𝟙 𝟙  ()
    𝟘  𝟘  𝟙  ≤𝟙 ≤𝟙 ()
    𝟘  𝟘  𝟙  ≤𝟙 ≤ω ()
    𝟘  𝟘  𝟙  ≤ω 𝟘  ()
    𝟘  𝟘  𝟙  ≤ω 𝟙  ()
    𝟘  𝟘  𝟙  ≤ω ≤𝟙 ()
    𝟘  𝟘  𝟙  ≤ω ≤ω ()
    𝟘  𝟘  ≤𝟙 𝟘  𝟘  ()
    𝟘  𝟘  ≤𝟙 𝟘  𝟙  ()
    𝟘  𝟘  ≤𝟙 𝟘  ≤𝟙 ()
    𝟘  𝟘  ≤𝟙 𝟘  ≤ω ()
    𝟘  𝟘  ≤𝟙 𝟙  𝟘  ()
    𝟘  𝟘  ≤𝟙 𝟙  𝟙  ()
    𝟘  𝟘  ≤𝟙 𝟙  ≤𝟙 ()
    𝟘  𝟘  ≤𝟙 𝟙  ≤ω ()
    𝟘  𝟘  ≤𝟙 ≤𝟙 𝟘  ()
    𝟘  𝟘  ≤𝟙 ≤𝟙 𝟙  ()
    𝟘  𝟘  ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘  𝟘  ≤𝟙 ≤𝟙 ≤ω ()
    𝟘  𝟘  ≤𝟙 ≤ω 𝟘  ()
    𝟘  𝟘  ≤𝟙 ≤ω 𝟙  ()
    𝟘  𝟘  ≤𝟙 ≤ω ≤𝟙 ()
    𝟘  𝟘  ≤𝟙 ≤ω ≤ω ()
    𝟘  𝟘  ≤ω 𝟘  𝟘  ()
    𝟘  𝟘  ≤ω 𝟘  𝟙  ()
    𝟘  𝟘  ≤ω 𝟘  ≤𝟙 ()
    𝟘  𝟘  ≤ω 𝟘  ≤ω ()
    𝟘  𝟘  ≤ω 𝟙  𝟘  ()
    𝟘  𝟘  ≤ω 𝟙  𝟙  ()
    𝟘  𝟘  ≤ω 𝟙  ≤𝟙 ()
    𝟘  𝟘  ≤ω 𝟙  ≤ω ()
    𝟘  𝟘  ≤ω ≤𝟙 𝟘  ()
    𝟘  𝟘  ≤ω ≤𝟙 𝟙  ()
    𝟘  𝟘  ≤ω ≤𝟙 ≤𝟙 ()
    𝟘  𝟘  ≤ω ≤𝟙 ≤ω ()
    𝟘  𝟘  ≤ω ≤ω 𝟘  ()
    𝟘  𝟘  ≤ω ≤ω 𝟙  ()
    𝟘  𝟘  ≤ω ≤ω ≤𝟙 ()
    𝟘  𝟘  ≤ω ≤ω ≤ω ()
    𝟙  𝟘  𝟘  𝟘  𝟙  ()
    𝟙  𝟘  𝟘  𝟘  ≤𝟙 ()
    𝟙  𝟘  𝟘  𝟘  ≤ω ()
    𝟙  𝟘  𝟘  𝟙  𝟘  ()
    𝟙  𝟘  𝟘  𝟙  𝟙  ()
    𝟙  𝟘  𝟘  𝟙  ≤𝟙 ()
    𝟙  𝟘  𝟘  𝟙  ≤ω ()
    𝟙  𝟘  𝟘  ≤𝟙 𝟘  ()
    𝟙  𝟘  𝟘  ≤𝟙 𝟙  ()
    𝟙  𝟘  𝟘  ≤𝟙 ≤𝟙 ()
    𝟙  𝟘  𝟘  ≤𝟙 ≤ω ()
    𝟙  𝟘  𝟘  ≤ω 𝟘  ()
    𝟙  𝟘  𝟘  ≤ω 𝟙  ()
    𝟙  𝟘  𝟘  ≤ω ≤𝟙 ()
    𝟙  𝟘  𝟘  ≤ω ≤ω ()
    𝟙  𝟘  𝟙  𝟘  𝟘  ()
    𝟙  𝟘  𝟙  𝟘  𝟙  ()
    𝟙  𝟘  𝟙  𝟘  ≤𝟙 ()
    𝟙  𝟘  𝟙  𝟘  ≤ω ()
    𝟙  𝟘  𝟙  𝟙  𝟘  ()
    𝟙  𝟘  𝟙  𝟙  𝟙  ()
    𝟙  𝟘  𝟙  𝟙  ≤𝟙 ()
    𝟙  𝟘  𝟙  𝟙  ≤ω ()
    𝟙  𝟘  𝟙  ≤𝟙 𝟘  ()
    𝟙  𝟘  𝟙  ≤𝟙 𝟙  ()
    𝟙  𝟘  𝟙  ≤𝟙 ≤𝟙 ()
    𝟙  𝟘  𝟙  ≤𝟙 ≤ω ()
    𝟙  𝟘  𝟙  ≤ω 𝟘  ()
    𝟙  𝟘  𝟙  ≤ω 𝟙  ()
    𝟙  𝟘  𝟙  ≤ω ≤𝟙 ()
    𝟙  𝟘  𝟙  ≤ω ≤ω ()
    𝟙  𝟘  ≤𝟙 𝟘  𝟘  ()
    𝟙  𝟘  ≤𝟙 𝟘  𝟙  ()
    𝟙  𝟘  ≤𝟙 𝟘  ≤𝟙 ()
    𝟙  𝟘  ≤𝟙 𝟘  ≤ω ()
    𝟙  𝟘  ≤𝟙 𝟙  𝟘  ()
    𝟙  𝟘  ≤𝟙 𝟙  𝟙  ()
    𝟙  𝟘  ≤𝟙 𝟙  ≤𝟙 ()
    𝟙  𝟘  ≤𝟙 𝟙  ≤ω ()
    𝟙  𝟘  ≤𝟙 ≤𝟙 𝟘  ()
    𝟙  𝟘  ≤𝟙 ≤𝟙 𝟙  ()
    𝟙  𝟘  ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙  𝟘  ≤𝟙 ≤𝟙 ≤ω ()
    𝟙  𝟘  ≤𝟙 ≤ω 𝟘  ()
    𝟙  𝟘  ≤𝟙 ≤ω 𝟙  ()
    𝟙  𝟘  ≤𝟙 ≤ω ≤𝟙 ()
    𝟙  𝟘  ≤𝟙 ≤ω ≤ω ()
    𝟙  𝟘  ≤ω 𝟘  𝟘  ()
    𝟙  𝟘  ≤ω 𝟘  𝟙  ()
    𝟙  𝟘  ≤ω 𝟘  ≤𝟙 ()
    𝟙  𝟘  ≤ω 𝟘  ≤ω ()
    𝟙  𝟘  ≤ω 𝟙  𝟘  ()
    𝟙  𝟘  ≤ω 𝟙  𝟙  ()
    𝟙  𝟘  ≤ω 𝟙  ≤𝟙 ()
    𝟙  𝟘  ≤ω 𝟙  ≤ω ()
    𝟙  𝟘  ≤ω ≤𝟙 𝟘  ()
    𝟙  𝟘  ≤ω ≤𝟙 𝟙  ()
    𝟙  𝟘  ≤ω ≤𝟙 ≤𝟙 ()
    𝟙  𝟘  ≤ω ≤𝟙 ≤ω ()
    𝟙  𝟘  ≤ω ≤ω 𝟘  ()
    𝟙  𝟘  ≤ω ≤ω 𝟙  ()
    𝟙  𝟘  ≤ω ≤ω ≤𝟙 ()
    𝟙  𝟘  ≤ω ≤ω ≤ω ()
    ≤𝟙 𝟘  𝟘  𝟘  𝟙  ()
    ≤𝟙 𝟘  𝟘  𝟘  ≤𝟙 ()
    ≤𝟙 𝟘  𝟘  𝟘  ≤ω ()
    ≤𝟙 𝟘  𝟘  𝟙  𝟘  ()
    ≤𝟙 𝟘  𝟘  𝟙  𝟙  ()
    ≤𝟙 𝟘  𝟘  𝟙  ≤𝟙 ()
    ≤𝟙 𝟘  𝟘  𝟙  ≤ω ()
    ≤𝟙 𝟘  𝟘  ≤𝟙 𝟘  ()
    ≤𝟙 𝟘  𝟘  ≤𝟙 𝟙  ()
    ≤𝟙 𝟘  𝟘  ≤𝟙 ≤𝟙 ()
    ≤𝟙 𝟘  𝟘  ≤𝟙 ≤ω ()
    ≤𝟙 𝟘  𝟘  ≤ω 𝟘  ()
    ≤𝟙 𝟘  𝟘  ≤ω 𝟙  ()
    ≤𝟙 𝟘  𝟘  ≤ω ≤𝟙 ()
    ≤𝟙 𝟘  𝟘  ≤ω ≤ω ()
    ≤𝟙 𝟘  𝟙  𝟘  𝟘  ()
    ≤𝟙 𝟘  𝟙  𝟘  𝟙  ()
    ≤𝟙 𝟘  𝟙  𝟘  ≤𝟙 ()
    ≤𝟙 𝟘  𝟙  𝟘  ≤ω ()
    ≤𝟙 𝟘  𝟙  𝟙  𝟘  ()
    ≤𝟙 𝟘  𝟙  𝟙  𝟙  ()
    ≤𝟙 𝟘  𝟙  𝟙  ≤𝟙 ()
    ≤𝟙 𝟘  𝟙  𝟙  ≤ω ()
    ≤𝟙 𝟘  𝟙  ≤𝟙 𝟘  ()
    ≤𝟙 𝟘  𝟙  ≤𝟙 𝟙  ()
    ≤𝟙 𝟘  𝟙  ≤𝟙 ≤𝟙 ()
    ≤𝟙 𝟘  𝟙  ≤𝟙 ≤ω ()
    ≤𝟙 𝟘  𝟙  ≤ω 𝟘  ()
    ≤𝟙 𝟘  𝟙  ≤ω 𝟙  ()
    ≤𝟙 𝟘  𝟙  ≤ω ≤𝟙 ()
    ≤𝟙 𝟘  𝟙  ≤ω ≤ω ()
    ≤𝟙 𝟘  ≤𝟙 𝟘  𝟘  ()
    ≤𝟙 𝟘  ≤𝟙 𝟘  𝟙  ()
    ≤𝟙 𝟘  ≤𝟙 𝟘  ≤𝟙 ()
    ≤𝟙 𝟘  ≤𝟙 𝟘  ≤ω ()
    ≤𝟙 𝟘  ≤𝟙 𝟙  𝟘  ()
    ≤𝟙 𝟘  ≤𝟙 𝟙  𝟙  ()
    ≤𝟙 𝟘  ≤𝟙 𝟙  ≤𝟙 ()
    ≤𝟙 𝟘  ≤𝟙 𝟙  ≤ω ()
    ≤𝟙 𝟘  ≤𝟙 ≤𝟙 𝟘  ()
    ≤𝟙 𝟘  ≤𝟙 ≤𝟙 𝟙  ()
    ≤𝟙 𝟘  ≤𝟙 ≤𝟙 ≤𝟙 ()
    ≤𝟙 𝟘  ≤𝟙 ≤𝟙 ≤ω ()
    ≤𝟙 𝟘  ≤𝟙 ≤ω 𝟘  ()
    ≤𝟙 𝟘  ≤𝟙 ≤ω 𝟙  ()
    ≤𝟙 𝟘  ≤𝟙 ≤ω ≤𝟙 ()
    ≤𝟙 𝟘  ≤𝟙 ≤ω ≤ω ()
    ≤𝟙 𝟘  ≤ω 𝟘  𝟘  ()
    ≤𝟙 𝟘  ≤ω 𝟘  𝟙  ()
    ≤𝟙 𝟘  ≤ω 𝟘  ≤𝟙 ()
    ≤𝟙 𝟘  ≤ω 𝟘  ≤ω ()
    ≤𝟙 𝟘  ≤ω 𝟙  𝟘  ()
    ≤𝟙 𝟘  ≤ω 𝟙  𝟙  ()
    ≤𝟙 𝟘  ≤ω 𝟙  ≤𝟙 ()
    ≤𝟙 𝟘  ≤ω 𝟙  ≤ω ()
    ≤𝟙 𝟘  ≤ω ≤𝟙 𝟘  ()
    ≤𝟙 𝟘  ≤ω ≤𝟙 𝟙  ()
    ≤𝟙 𝟘  ≤ω ≤𝟙 ≤𝟙 ()
    ≤𝟙 𝟘  ≤ω ≤𝟙 ≤ω ()
    ≤𝟙 𝟘  ≤ω ≤ω 𝟘  ()
    ≤𝟙 𝟘  ≤ω ≤ω 𝟙  ()
    ≤𝟙 𝟘  ≤ω ≤ω ≤𝟙 ()
    ≤𝟙 𝟘  ≤ω ≤ω ≤ω ()
    ≤ω 𝟘  𝟘  𝟘  𝟙  ()
    ≤ω 𝟘  𝟘  𝟘  ≤𝟙 ()
    ≤ω 𝟘  𝟘  𝟘  ≤ω ()
    ≤ω 𝟘  𝟘  𝟙  𝟘  ()
    ≤ω 𝟘  𝟘  𝟙  𝟙  ()
    ≤ω 𝟘  𝟘  𝟙  ≤𝟙 ()
    ≤ω 𝟘  𝟘  𝟙  ≤ω ()
    ≤ω 𝟘  𝟘  ≤𝟙 𝟘  ()
    ≤ω 𝟘  𝟘  ≤𝟙 𝟙  ()
    ≤ω 𝟘  𝟘  ≤𝟙 ≤𝟙 ()
    ≤ω 𝟘  𝟘  ≤𝟙 ≤ω ()
    ≤ω 𝟘  𝟘  ≤ω 𝟘  ()
    ≤ω 𝟘  𝟘  ≤ω 𝟙  ()
    ≤ω 𝟘  𝟘  ≤ω ≤𝟙 ()
    ≤ω 𝟘  𝟘  ≤ω ≤ω ()
    ≤ω 𝟘  𝟙  𝟘  𝟘  ()
    ≤ω 𝟘  𝟙  𝟘  𝟙  ()
    ≤ω 𝟘  𝟙  𝟘  ≤𝟙 ()
    ≤ω 𝟘  𝟙  𝟘  ≤ω ()
    ≤ω 𝟘  𝟙  𝟙  𝟘  ()
    ≤ω 𝟘  𝟙  𝟙  𝟙  ()
    ≤ω 𝟘  𝟙  𝟙  ≤𝟙 ()
    ≤ω 𝟘  𝟙  𝟙  ≤ω ()
    ≤ω 𝟘  𝟙  ≤𝟙 𝟘  ()
    ≤ω 𝟘  𝟙  ≤𝟙 𝟙  ()
    ≤ω 𝟘  𝟙  ≤𝟙 ≤𝟙 ()
    ≤ω 𝟘  𝟙  ≤𝟙 ≤ω ()
    ≤ω 𝟘  𝟙  ≤ω 𝟘  ()
    ≤ω 𝟘  𝟙  ≤ω 𝟙  ()
    ≤ω 𝟘  𝟙  ≤ω ≤𝟙 ()
    ≤ω 𝟘  𝟙  ≤ω ≤ω ()
    ≤ω 𝟘  ≤𝟙 𝟘  𝟘  ()
    ≤ω 𝟘  ≤𝟙 𝟘  𝟙  ()
    ≤ω 𝟘  ≤𝟙 𝟘  ≤𝟙 ()
    ≤ω 𝟘  ≤𝟙 𝟘  ≤ω ()
    ≤ω 𝟘  ≤𝟙 𝟙  𝟘  ()
    ≤ω 𝟘  ≤𝟙 𝟙  𝟙  ()
    ≤ω 𝟘  ≤𝟙 𝟙  ≤𝟙 ()
    ≤ω 𝟘  ≤𝟙 𝟙  ≤ω ()
    ≤ω 𝟘  ≤𝟙 ≤𝟙 𝟘  ()
    ≤ω 𝟘  ≤𝟙 ≤𝟙 𝟙  ()
    ≤ω 𝟘  ≤𝟙 ≤𝟙 ≤𝟙 ()
    ≤ω 𝟘  ≤𝟙 ≤𝟙 ≤ω ()
    ≤ω 𝟘  ≤𝟙 ≤ω 𝟘  ()
    ≤ω 𝟘  ≤𝟙 ≤ω 𝟙  ()
    ≤ω 𝟘  ≤𝟙 ≤ω ≤𝟙 ()
    ≤ω 𝟘  ≤𝟙 ≤ω ≤ω ()
    ≤ω 𝟘  ≤ω 𝟘  𝟘  ()
    ≤ω 𝟘  ≤ω 𝟘  𝟙  ()
    ≤ω 𝟘  ≤ω 𝟘  ≤𝟙 ()
    ≤ω 𝟘  ≤ω 𝟘  ≤ω ()
    ≤ω 𝟘  ≤ω 𝟙  𝟘  ()
    ≤ω 𝟘  ≤ω 𝟙  𝟙  ()
    ≤ω 𝟘  ≤ω 𝟙  ≤𝟙 ()
    ≤ω 𝟘  ≤ω 𝟙  ≤ω ()
    ≤ω 𝟘  ≤ω ≤𝟙 𝟘  ()
    ≤ω 𝟘  ≤ω ≤𝟙 𝟙  ()
    ≤ω 𝟘  ≤ω ≤𝟙 ≤𝟙 ()
    ≤ω 𝟘  ≤ω ≤𝟙 ≤ω ()
    ≤ω 𝟘  ≤ω ≤ω 𝟘  ()
    ≤ω 𝟘  ≤ω ≤ω 𝟙  ()
    ≤ω 𝟘  ≤ω ≤ω ≤𝟙 ()
    ≤ω 𝟘  ≤ω ≤ω ≤ω ()
    𝟘  𝟙  𝟘  𝟘  𝟙  ()
    𝟘  𝟙  𝟘  𝟘  ≤𝟙 ()
    𝟘  𝟙  𝟘  𝟘  ≤ω ()
    𝟘  𝟙  𝟘  𝟙  𝟘  ()
    𝟘  𝟙  𝟘  𝟙  𝟙  ()
    𝟘  𝟙  𝟘  𝟙  ≤𝟙 ()
    𝟘  𝟙  𝟘  𝟙  ≤ω ()
    𝟘  𝟙  𝟘  ≤𝟙 𝟘  ()
    𝟘  𝟙  𝟘  ≤𝟙 𝟙  ()
    𝟘  𝟙  𝟘  ≤𝟙 ≤𝟙 ()
    𝟘  𝟙  𝟘  ≤𝟙 ≤ω ()
    𝟘  𝟙  𝟘  ≤ω 𝟘  ()
    𝟘  𝟙  𝟘  ≤ω 𝟙  ()
    𝟘  𝟙  𝟘  ≤ω ≤𝟙 ()
    𝟘  𝟙  𝟘  ≤ω ≤ω ()
    𝟘  𝟙  𝟙  𝟘  𝟘  ()
    𝟘  𝟙  𝟙  𝟘  𝟙  ()
    𝟘  𝟙  𝟙  𝟘  ≤𝟙 ()
    𝟘  𝟙  𝟙  𝟘  ≤ω ()
    𝟘  𝟙  𝟙  𝟙  𝟘  ()
    𝟘  𝟙  𝟙  𝟙  𝟙  ()
    𝟘  𝟙  𝟙  𝟙  ≤𝟙 ()
    𝟘  𝟙  𝟙  𝟙  ≤ω ()
    𝟘  𝟙  𝟙  ≤𝟙 𝟘  ()
    𝟘  𝟙  𝟙  ≤𝟙 𝟙  ()
    𝟘  𝟙  𝟙  ≤𝟙 ≤𝟙 ()
    𝟘  𝟙  𝟙  ≤𝟙 ≤ω ()
    𝟘  𝟙  𝟙  ≤ω 𝟘  ()
    𝟘  𝟙  𝟙  ≤ω 𝟙  ()
    𝟘  𝟙  𝟙  ≤ω ≤𝟙 ()
    𝟘  𝟙  𝟙  ≤ω ≤ω ()
    𝟘  𝟙  ≤𝟙 𝟘  𝟘  ()
    𝟘  𝟙  ≤𝟙 𝟘  𝟙  ()
    𝟘  𝟙  ≤𝟙 𝟘  ≤𝟙 ()
    𝟘  𝟙  ≤𝟙 𝟘  ≤ω ()
    𝟘  𝟙  ≤𝟙 𝟙  𝟘  ()
    𝟘  𝟙  ≤𝟙 𝟙  𝟙  ()
    𝟘  𝟙  ≤𝟙 𝟙  ≤𝟙 ()
    𝟘  𝟙  ≤𝟙 𝟙  ≤ω ()
    𝟘  𝟙  ≤𝟙 ≤𝟙 𝟘  ()
    𝟘  𝟙  ≤𝟙 ≤𝟙 𝟙  ()
    𝟘  𝟙  ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘  𝟙  ≤𝟙 ≤𝟙 ≤ω ()
    𝟘  𝟙  ≤𝟙 ≤ω 𝟘  ()
    𝟘  𝟙  ≤𝟙 ≤ω 𝟙  ()
    𝟘  𝟙  ≤𝟙 ≤ω ≤𝟙 ()
    𝟘  𝟙  ≤𝟙 ≤ω ≤ω ()
    𝟘  𝟙  ≤ω 𝟘  𝟘  ()
    𝟘  𝟙  ≤ω 𝟘  𝟙  ()
    𝟘  𝟙  ≤ω 𝟘  ≤𝟙 ()
    𝟘  𝟙  ≤ω 𝟘  ≤ω ()
    𝟘  𝟙  ≤ω 𝟙  𝟘  ()
    𝟘  𝟙  ≤ω 𝟙  𝟙  ()
    𝟘  𝟙  ≤ω 𝟙  ≤𝟙 ()
    𝟘  𝟙  ≤ω 𝟙  ≤ω ()
    𝟘  𝟙  ≤ω ≤𝟙 𝟘  ()
    𝟘  𝟙  ≤ω ≤𝟙 𝟙  ()
    𝟘  𝟙  ≤ω ≤𝟙 ≤𝟙 ()
    𝟘  𝟙  ≤ω ≤𝟙 ≤ω ()
    𝟘  𝟙  ≤ω ≤ω 𝟘  ()
    𝟘  𝟙  ≤ω ≤ω 𝟙  ()
    𝟘  𝟙  ≤ω ≤ω ≤𝟙 ()
    𝟘  𝟙  ≤ω ≤ω ≤ω ()
    𝟙  𝟙  𝟘  𝟘  𝟙  ()
    𝟙  𝟙  𝟘  𝟘  ≤𝟙 ()
    𝟙  𝟙  𝟘  𝟘  ≤ω ()
    𝟙  𝟙  𝟘  𝟙  𝟘  ()
    𝟙  𝟙  𝟘  𝟙  𝟙  ()
    𝟙  𝟙  𝟘  𝟙  ≤𝟙 ()
    𝟙  𝟙  𝟘  𝟙  ≤ω ()
    𝟙  𝟙  𝟘  ≤𝟙 𝟘  ()
    𝟙  𝟙  𝟘  ≤𝟙 𝟙  ()
    𝟙  𝟙  𝟘  ≤𝟙 ≤𝟙 ()
    𝟙  𝟙  𝟘  ≤𝟙 ≤ω ()
    𝟙  𝟙  𝟘  ≤ω 𝟘  ()
    𝟙  𝟙  𝟘  ≤ω 𝟙  ()
    𝟙  𝟙  𝟘  ≤ω ≤𝟙 ()
    𝟙  𝟙  𝟘  ≤ω ≤ω ()
    𝟙  𝟙  𝟙  𝟘  𝟘  ()
    𝟙  𝟙  𝟙  𝟘  𝟙  ()
    𝟙  𝟙  𝟙  𝟘  ≤𝟙 ()
    𝟙  𝟙  𝟙  𝟘  ≤ω ()
    𝟙  𝟙  𝟙  𝟙  𝟘  ()
    𝟙  𝟙  𝟙  𝟙  𝟙  ()
    𝟙  𝟙  𝟙  𝟙  ≤𝟙 ()
    𝟙  𝟙  𝟙  𝟙  ≤ω ()
    𝟙  𝟙  𝟙  ≤𝟙 𝟘  ()
    𝟙  𝟙  𝟙  ≤𝟙 𝟙  ()
    𝟙  𝟙  𝟙  ≤𝟙 ≤𝟙 ()
    𝟙  𝟙  𝟙  ≤𝟙 ≤ω ()
    𝟙  𝟙  𝟙  ≤ω 𝟘  ()
    𝟙  𝟙  𝟙  ≤ω 𝟙  ()
    𝟙  𝟙  𝟙  ≤ω ≤𝟙 ()
    𝟙  𝟙  𝟙  ≤ω ≤ω ()
    𝟙  𝟙  ≤𝟙 𝟘  𝟘  ()
    𝟙  𝟙  ≤𝟙 𝟘  𝟙  ()
    𝟙  𝟙  ≤𝟙 𝟘  ≤𝟙 ()
    𝟙  𝟙  ≤𝟙 𝟘  ≤ω ()
    𝟙  𝟙  ≤𝟙 𝟙  𝟘  ()
    𝟙  𝟙  ≤𝟙 𝟙  𝟙  ()
    𝟙  𝟙  ≤𝟙 𝟙  ≤𝟙 ()
    𝟙  𝟙  ≤𝟙 𝟙  ≤ω ()
    𝟙  𝟙  ≤𝟙 ≤𝟙 𝟘  ()
    𝟙  𝟙  ≤𝟙 ≤𝟙 𝟙  ()
    𝟙  𝟙  ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙  𝟙  ≤𝟙 ≤𝟙 ≤ω ()
    𝟙  𝟙  ≤𝟙 ≤ω 𝟘  ()
    𝟙  𝟙  ≤𝟙 ≤ω 𝟙  ()
    𝟙  𝟙  ≤𝟙 ≤ω ≤𝟙 ()
    𝟙  𝟙  ≤𝟙 ≤ω ≤ω ()
    𝟙  𝟙  ≤ω 𝟘  𝟘  ()
    𝟙  𝟙  ≤ω 𝟘  𝟙  ()
    𝟙  𝟙  ≤ω 𝟘  ≤𝟙 ()
    𝟙  𝟙  ≤ω 𝟘  ≤ω ()
    𝟙  𝟙  ≤ω 𝟙  𝟘  ()
    𝟙  𝟙  ≤ω 𝟙  𝟙  ()
    𝟙  𝟙  ≤ω 𝟙  ≤𝟙 ()
    𝟙  𝟙  ≤ω 𝟙  ≤ω ()
    𝟙  𝟙  ≤ω ≤𝟙 𝟘  ()
    𝟙  𝟙  ≤ω ≤𝟙 𝟙  ()
    𝟙  𝟙  ≤ω ≤𝟙 ≤𝟙 ()
    𝟙  𝟙  ≤ω ≤𝟙 ≤ω ()
    𝟙  𝟙  ≤ω ≤ω 𝟘  ()
    𝟙  𝟙  ≤ω ≤ω 𝟙  ()
    𝟙  𝟙  ≤ω ≤ω ≤𝟙 ()
    𝟙  𝟙  ≤ω ≤ω ≤ω ()
    ≤𝟙 𝟙  𝟘  𝟘  𝟙  ()
    ≤𝟙 𝟙  𝟘  𝟘  ≤𝟙 ()
    ≤𝟙 𝟙  𝟘  𝟘  ≤ω ()
    ≤𝟙 𝟙  𝟘  𝟙  𝟘  ()
    ≤𝟙 𝟙  𝟘  𝟙  𝟙  ()
    ≤𝟙 𝟙  𝟘  𝟙  ≤𝟙 ()
    ≤𝟙 𝟙  𝟘  𝟙  ≤ω ()
    ≤𝟙 𝟙  𝟘  ≤𝟙 𝟘  ()
    ≤𝟙 𝟙  𝟘  ≤𝟙 𝟙  ()
    ≤𝟙 𝟙  𝟘  ≤𝟙 ≤𝟙 ()
    ≤𝟙 𝟙  𝟘  ≤𝟙 ≤ω ()
    ≤𝟙 𝟙  𝟘  ≤ω 𝟘  ()
    ≤𝟙 𝟙  𝟘  ≤ω 𝟙  ()
    ≤𝟙 𝟙  𝟘  ≤ω ≤𝟙 ()
    ≤𝟙 𝟙  𝟘  ≤ω ≤ω ()
    ≤𝟙 𝟙  𝟙  𝟘  𝟘  ()
    ≤𝟙 𝟙  𝟙  𝟘  𝟙  ()
    ≤𝟙 𝟙  𝟙  𝟘  ≤𝟙 ()
    ≤𝟙 𝟙  𝟙  𝟘  ≤ω ()
    ≤𝟙 𝟙  𝟙  𝟙  𝟘  ()
    ≤𝟙 𝟙  𝟙  𝟙  𝟙  ()
    ≤𝟙 𝟙  𝟙  𝟙  ≤𝟙 ()
    ≤𝟙 𝟙  𝟙  𝟙  ≤ω ()
    ≤𝟙 𝟙  𝟙  ≤𝟙 𝟘  ()
    ≤𝟙 𝟙  𝟙  ≤𝟙 𝟙  ()
    ≤𝟙 𝟙  𝟙  ≤𝟙 ≤𝟙 ()
    ≤𝟙 𝟙  𝟙  ≤𝟙 ≤ω ()
    ≤𝟙 𝟙  𝟙  ≤ω 𝟘  ()
    ≤𝟙 𝟙  𝟙  ≤ω 𝟙  ()
    ≤𝟙 𝟙  𝟙  ≤ω ≤𝟙 ()
    ≤𝟙 𝟙  𝟙  ≤ω ≤ω ()
    ≤𝟙 𝟙  ≤𝟙 𝟘  𝟘  ()
    ≤𝟙 𝟙  ≤𝟙 𝟘  𝟙  ()
    ≤𝟙 𝟙  ≤𝟙 𝟘  ≤𝟙 ()
    ≤𝟙 𝟙  ≤𝟙 𝟘  ≤ω ()
    ≤𝟙 𝟙  ≤𝟙 𝟙  𝟘  ()
    ≤𝟙 𝟙  ≤𝟙 𝟙  𝟙  ()
    ≤𝟙 𝟙  ≤𝟙 𝟙  ≤𝟙 ()
    ≤𝟙 𝟙  ≤𝟙 𝟙  ≤ω ()
    ≤𝟙 𝟙  ≤𝟙 ≤𝟙 𝟘  ()
    ≤𝟙 𝟙  ≤𝟙 ≤𝟙 𝟙  ()
    ≤𝟙 𝟙  ≤𝟙 ≤𝟙 ≤𝟙 ()
    ≤𝟙 𝟙  ≤𝟙 ≤𝟙 ≤ω ()
    ≤𝟙 𝟙  ≤𝟙 ≤ω 𝟘  ()
    ≤𝟙 𝟙  ≤𝟙 ≤ω 𝟙  ()
    ≤𝟙 𝟙  ≤𝟙 ≤ω ≤𝟙 ()
    ≤𝟙 𝟙  ≤𝟙 ≤ω ≤ω ()
    ≤𝟙 𝟙  ≤ω 𝟘  𝟘  ()
    ≤𝟙 𝟙  ≤ω 𝟘  𝟙  ()
    ≤𝟙 𝟙  ≤ω 𝟘  ≤𝟙 ()
    ≤𝟙 𝟙  ≤ω 𝟘  ≤ω ()
    ≤𝟙 𝟙  ≤ω 𝟙  𝟘  ()
    ≤𝟙 𝟙  ≤ω 𝟙  𝟙  ()
    ≤𝟙 𝟙  ≤ω 𝟙  ≤𝟙 ()
    ≤𝟙 𝟙  ≤ω 𝟙  ≤ω ()
    ≤𝟙 𝟙  ≤ω ≤𝟙 𝟘  ()
    ≤𝟙 𝟙  ≤ω ≤𝟙 𝟙  ()
    ≤𝟙 𝟙  ≤ω ≤𝟙 ≤𝟙 ()
    ≤𝟙 𝟙  ≤ω ≤𝟙 ≤ω ()
    ≤𝟙 𝟙  ≤ω ≤ω 𝟘  ()
    ≤𝟙 𝟙  ≤ω ≤ω 𝟙  ()
    ≤𝟙 𝟙  ≤ω ≤ω ≤𝟙 ()
    ≤𝟙 𝟙  ≤ω ≤ω ≤ω ()
    ≤ω 𝟙  𝟘  𝟘  𝟙  ()
    ≤ω 𝟙  𝟘  𝟘  ≤𝟙 ()
    ≤ω 𝟙  𝟘  𝟘  ≤ω ()
    ≤ω 𝟙  𝟘  𝟙  𝟘  ()
    ≤ω 𝟙  𝟘  𝟙  𝟙  ()
    ≤ω 𝟙  𝟘  𝟙  ≤𝟙 ()
    ≤ω 𝟙  𝟘  𝟙  ≤ω ()
    ≤ω 𝟙  𝟘  ≤𝟙 𝟘  ()
    ≤ω 𝟙  𝟘  ≤𝟙 𝟙  ()
    ≤ω 𝟙  𝟘  ≤𝟙 ≤𝟙 ()
    ≤ω 𝟙  𝟘  ≤𝟙 ≤ω ()
    ≤ω 𝟙  𝟘  ≤ω 𝟘  ()
    ≤ω 𝟙  𝟘  ≤ω 𝟙  ()
    ≤ω 𝟙  𝟘  ≤ω ≤𝟙 ()
    ≤ω 𝟙  𝟘  ≤ω ≤ω ()
    ≤ω 𝟙  𝟙  𝟘  𝟘  ()
    ≤ω 𝟙  𝟙  𝟘  𝟙  ()
    ≤ω 𝟙  𝟙  𝟘  ≤𝟙 ()
    ≤ω 𝟙  𝟙  𝟘  ≤ω ()
    ≤ω 𝟙  𝟙  𝟙  𝟘  ()
    ≤ω 𝟙  𝟙  𝟙  𝟙  ()
    ≤ω 𝟙  𝟙  𝟙  ≤𝟙 ()
    ≤ω 𝟙  𝟙  𝟙  ≤ω ()
    ≤ω 𝟙  𝟙  ≤𝟙 𝟘  ()
    ≤ω 𝟙  𝟙  ≤𝟙 𝟙  ()
    ≤ω 𝟙  𝟙  ≤𝟙 ≤𝟙 ()
    ≤ω 𝟙  𝟙  ≤𝟙 ≤ω ()
    ≤ω 𝟙  𝟙  ≤ω 𝟘  ()
    ≤ω 𝟙  𝟙  ≤ω 𝟙  ()
    ≤ω 𝟙  𝟙  ≤ω ≤𝟙 ()
    ≤ω 𝟙  𝟙  ≤ω ≤ω ()
    ≤ω 𝟙  ≤𝟙 𝟘  𝟘  ()
    ≤ω 𝟙  ≤𝟙 𝟘  𝟙  ()
    ≤ω 𝟙  ≤𝟙 𝟘  ≤𝟙 ()
    ≤ω 𝟙  ≤𝟙 𝟘  ≤ω ()
    ≤ω 𝟙  ≤𝟙 𝟙  𝟘  ()
    ≤ω 𝟙  ≤𝟙 𝟙  𝟙  ()
    ≤ω 𝟙  ≤𝟙 𝟙  ≤𝟙 ()
    ≤ω 𝟙  ≤𝟙 𝟙  ≤ω ()
    ≤ω 𝟙  ≤𝟙 ≤𝟙 𝟘  ()
    ≤ω 𝟙  ≤𝟙 ≤𝟙 𝟙  ()
    ≤ω 𝟙  ≤𝟙 ≤𝟙 ≤𝟙 ()
    ≤ω 𝟙  ≤𝟙 ≤𝟙 ≤ω ()
    ≤ω 𝟙  ≤𝟙 ≤ω 𝟘  ()
    ≤ω 𝟙  ≤𝟙 ≤ω 𝟙  ()
    ≤ω 𝟙  ≤𝟙 ≤ω ≤𝟙 ()
    ≤ω 𝟙  ≤𝟙 ≤ω ≤ω ()
    ≤ω 𝟙  ≤ω 𝟘  𝟘  ()
    ≤ω 𝟙  ≤ω 𝟘  𝟙  ()
    ≤ω 𝟙  ≤ω 𝟘  ≤𝟙 ()
    ≤ω 𝟙  ≤ω 𝟘  ≤ω ()
    ≤ω 𝟙  ≤ω 𝟙  𝟘  ()
    ≤ω 𝟙  ≤ω 𝟙  𝟙  ()
    ≤ω 𝟙  ≤ω 𝟙  ≤𝟙 ()
    ≤ω 𝟙  ≤ω 𝟙  ≤ω ()
    ≤ω 𝟙  ≤ω ≤𝟙 𝟘  ()
    ≤ω 𝟙  ≤ω ≤𝟙 𝟙  ()
    ≤ω 𝟙  ≤ω ≤𝟙 ≤𝟙 ()
    ≤ω 𝟙  ≤ω ≤𝟙 ≤ω ()
    ≤ω 𝟙  ≤ω ≤ω 𝟘  ()
    ≤ω 𝟙  ≤ω ≤ω 𝟙  ()
    ≤ω 𝟙  ≤ω ≤ω ≤𝟙 ()
    ≤ω 𝟙  ≤ω ≤ω ≤ω ()
    𝟘  ≤𝟙 𝟘  𝟘  𝟙  ()
    𝟘  ≤𝟙 𝟘  𝟘  ≤𝟙 ()
    𝟘  ≤𝟙 𝟘  𝟘  ≤ω ()
    𝟘  ≤𝟙 𝟘  𝟙  𝟘  ()
    𝟘  ≤𝟙 𝟘  𝟙  𝟙  ()
    𝟘  ≤𝟙 𝟘  𝟙  ≤𝟙 ()
    𝟘  ≤𝟙 𝟘  𝟙  ≤ω ()
    𝟘  ≤𝟙 𝟘  ≤𝟙 𝟘  ()
    𝟘  ≤𝟙 𝟘  ≤𝟙 𝟙  ()
    𝟘  ≤𝟙 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘  ≤𝟙 𝟘  ≤𝟙 ≤ω ()
    𝟘  ≤𝟙 𝟘  ≤ω 𝟘  ()
    𝟘  ≤𝟙 𝟘  ≤ω 𝟙  ()
    𝟘  ≤𝟙 𝟘  ≤ω ≤𝟙 ()
    𝟘  ≤𝟙 𝟘  ≤ω ≤ω ()
    𝟘  ≤𝟙 𝟙  𝟘  𝟘  ()
    𝟘  ≤𝟙 𝟙  𝟘  𝟙  ()
    𝟘  ≤𝟙 𝟙  𝟘  ≤𝟙 ()
    𝟘  ≤𝟙 𝟙  𝟘  ≤ω ()
    𝟘  ≤𝟙 𝟙  𝟙  𝟘  ()
    𝟘  ≤𝟙 𝟙  𝟙  𝟙  ()
    𝟘  ≤𝟙 𝟙  𝟙  ≤𝟙 ()
    𝟘  ≤𝟙 𝟙  𝟙  ≤ω ()
    𝟘  ≤𝟙 𝟙  ≤𝟙 𝟘  ()
    𝟘  ≤𝟙 𝟙  ≤𝟙 𝟙  ()
    𝟘  ≤𝟙 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘  ≤𝟙 𝟙  ≤𝟙 ≤ω ()
    𝟘  ≤𝟙 𝟙  ≤ω 𝟘  ()
    𝟘  ≤𝟙 𝟙  ≤ω 𝟙  ()
    𝟘  ≤𝟙 𝟙  ≤ω ≤𝟙 ()
    𝟘  ≤𝟙 𝟙  ≤ω ≤ω ()
    𝟘  ≤𝟙 ≤𝟙 𝟘  𝟘  ()
    𝟘  ≤𝟙 ≤𝟙 𝟘  𝟙  ()
    𝟘  ≤𝟙 ≤𝟙 𝟘  ≤𝟙 ()
    𝟘  ≤𝟙 ≤𝟙 𝟘  ≤ω ()
    𝟘  ≤𝟙 ≤𝟙 𝟙  𝟘  ()
    𝟘  ≤𝟙 ≤𝟙 𝟙  𝟙  ()
    𝟘  ≤𝟙 ≤𝟙 𝟙  ≤𝟙 ()
    𝟘  ≤𝟙 ≤𝟙 𝟙  ≤ω ()
    𝟘  ≤𝟙 ≤𝟙 ≤𝟙 𝟘  ()
    𝟘  ≤𝟙 ≤𝟙 ≤𝟙 𝟙  ()
    𝟘  ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘  ≤𝟙 ≤𝟙 ≤𝟙 ≤ω ()
    𝟘  ≤𝟙 ≤𝟙 ≤ω 𝟘  ()
    𝟘  ≤𝟙 ≤𝟙 ≤ω 𝟙  ()
    𝟘  ≤𝟙 ≤𝟙 ≤ω ≤𝟙 ()
    𝟘  ≤𝟙 ≤𝟙 ≤ω ≤ω ()
    𝟘  ≤𝟙 ≤ω 𝟘  𝟘  ()
    𝟘  ≤𝟙 ≤ω 𝟘  𝟙  ()
    𝟘  ≤𝟙 ≤ω 𝟘  ≤𝟙 ()
    𝟘  ≤𝟙 ≤ω 𝟘  ≤ω ()
    𝟘  ≤𝟙 ≤ω 𝟙  𝟘  ()
    𝟘  ≤𝟙 ≤ω 𝟙  𝟙  ()
    𝟘  ≤𝟙 ≤ω 𝟙  ≤𝟙 ()
    𝟘  ≤𝟙 ≤ω 𝟙  ≤ω ()
    𝟘  ≤𝟙 ≤ω ≤𝟙 𝟘  ()
    𝟘  ≤𝟙 ≤ω ≤𝟙 𝟙  ()
    𝟘  ≤𝟙 ≤ω ≤𝟙 ≤𝟙 ()
    𝟘  ≤𝟙 ≤ω ≤𝟙 ≤ω ()
    𝟘  ≤𝟙 ≤ω ≤ω 𝟘  ()
    𝟘  ≤𝟙 ≤ω ≤ω 𝟙  ()
    𝟘  ≤𝟙 ≤ω ≤ω ≤𝟙 ()
    𝟘  ≤𝟙 ≤ω ≤ω ≤ω ()
    𝟙  ≤𝟙 𝟘  𝟘  𝟙  ()
    𝟙  ≤𝟙 𝟘  𝟘  ≤𝟙 ()
    𝟙  ≤𝟙 𝟘  𝟘  ≤ω ()
    𝟙  ≤𝟙 𝟘  𝟙  𝟘  ()
    𝟙  ≤𝟙 𝟘  𝟙  𝟙  ()
    𝟙  ≤𝟙 𝟘  𝟙  ≤𝟙 ()
    𝟙  ≤𝟙 𝟘  𝟙  ≤ω ()
    𝟙  ≤𝟙 𝟘  ≤𝟙 𝟘  ()
    𝟙  ≤𝟙 𝟘  ≤𝟙 𝟙  ()
    𝟙  ≤𝟙 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙  ≤𝟙 𝟘  ≤𝟙 ≤ω ()
    𝟙  ≤𝟙 𝟘  ≤ω 𝟘  ()
    𝟙  ≤𝟙 𝟘  ≤ω 𝟙  ()
    𝟙  ≤𝟙 𝟘  ≤ω ≤𝟙 ()
    𝟙  ≤𝟙 𝟘  ≤ω ≤ω ()
    𝟙  ≤𝟙 𝟙  𝟘  𝟘  ()
    𝟙  ≤𝟙 𝟙  𝟘  𝟙  ()
    𝟙  ≤𝟙 𝟙  𝟘  ≤𝟙 ()
    𝟙  ≤𝟙 𝟙  𝟘  ≤ω ()
    𝟙  ≤𝟙 𝟙  𝟙  𝟘  ()
    𝟙  ≤𝟙 𝟙  𝟙  𝟙  ()
    𝟙  ≤𝟙 𝟙  𝟙  ≤𝟙 ()
    𝟙  ≤𝟙 𝟙  𝟙  ≤ω ()
    𝟙  ≤𝟙 𝟙  ≤𝟙 𝟘  ()
    𝟙  ≤𝟙 𝟙  ≤𝟙 𝟙  ()
    𝟙  ≤𝟙 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙  ≤𝟙 𝟙  ≤𝟙 ≤ω ()
    𝟙  ≤𝟙 𝟙  ≤ω 𝟘  ()
    𝟙  ≤𝟙 𝟙  ≤ω 𝟙  ()
    𝟙  ≤𝟙 𝟙  ≤ω ≤𝟙 ()
    𝟙  ≤𝟙 𝟙  ≤ω ≤ω ()
    𝟙  ≤𝟙 ≤𝟙 𝟘  𝟘  ()
    𝟙  ≤𝟙 ≤𝟙 𝟘  𝟙  ()
    𝟙  ≤𝟙 ≤𝟙 𝟘  ≤𝟙 ()
    𝟙  ≤𝟙 ≤𝟙 𝟘  ≤ω ()
    𝟙  ≤𝟙 ≤𝟙 𝟙  𝟘  ()
    𝟙  ≤𝟙 ≤𝟙 𝟙  𝟙  ()
    𝟙  ≤𝟙 ≤𝟙 𝟙  ≤𝟙 ()
    𝟙  ≤𝟙 ≤𝟙 𝟙  ≤ω ()
    𝟙  ≤𝟙 ≤𝟙 ≤𝟙 𝟘  ()
    𝟙  ≤𝟙 ≤𝟙 ≤𝟙 𝟙  ()
    𝟙  ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙  ≤𝟙 ≤𝟙 ≤𝟙 ≤ω ()
    𝟙  ≤𝟙 ≤𝟙 ≤ω 𝟘  ()
    𝟙  ≤𝟙 ≤𝟙 ≤ω 𝟙  ()
    𝟙  ≤𝟙 ≤𝟙 ≤ω ≤𝟙 ()
    𝟙  ≤𝟙 ≤𝟙 ≤ω ≤ω ()
    𝟙  ≤𝟙 ≤ω 𝟘  𝟘  ()
    𝟙  ≤𝟙 ≤ω 𝟘  𝟙  ()
    𝟙  ≤𝟙 ≤ω 𝟘  ≤𝟙 ()
    𝟙  ≤𝟙 ≤ω 𝟘  ≤ω ()
    𝟙  ≤𝟙 ≤ω 𝟙  𝟘  ()
    𝟙  ≤𝟙 ≤ω 𝟙  𝟙  ()
    𝟙  ≤𝟙 ≤ω 𝟙  ≤𝟙 ()
    𝟙  ≤𝟙 ≤ω 𝟙  ≤ω ()
    𝟙  ≤𝟙 ≤ω ≤𝟙 𝟘  ()
    𝟙  ≤𝟙 ≤ω ≤𝟙 𝟙  ()
    𝟙  ≤𝟙 ≤ω ≤𝟙 ≤𝟙 ()
    𝟙  ≤𝟙 ≤ω ≤𝟙 ≤ω ()
    𝟙  ≤𝟙 ≤ω ≤ω 𝟘  ()
    𝟙  ≤𝟙 ≤ω ≤ω 𝟙  ()
    𝟙  ≤𝟙 ≤ω ≤ω ≤𝟙 ()
    𝟙  ≤𝟙 ≤ω ≤ω ≤ω ()
    ≤𝟙 ≤𝟙 𝟘  𝟘  𝟙  ()
    ≤𝟙 ≤𝟙 𝟘  𝟘  ≤𝟙 ()
    ≤𝟙 ≤𝟙 𝟘  𝟘  ≤ω ()
    ≤𝟙 ≤𝟙 𝟘  𝟙  𝟘  ()
    ≤𝟙 ≤𝟙 𝟘  𝟙  𝟙  ()
    ≤𝟙 ≤𝟙 𝟘  𝟙  ≤𝟙 ()
    ≤𝟙 ≤𝟙 𝟘  𝟙  ≤ω ()
    ≤𝟙 ≤𝟙 𝟘  ≤𝟙 𝟘  ()
    ≤𝟙 ≤𝟙 𝟘  ≤𝟙 𝟙  ()
    ≤𝟙 ≤𝟙 𝟘  ≤𝟙 ≤𝟙 ()
    ≤𝟙 ≤𝟙 𝟘  ≤𝟙 ≤ω ()
    ≤𝟙 ≤𝟙 𝟘  ≤ω 𝟘  ()
    ≤𝟙 ≤𝟙 𝟘  ≤ω 𝟙  ()
    ≤𝟙 ≤𝟙 𝟘  ≤ω ≤𝟙 ()
    ≤𝟙 ≤𝟙 𝟘  ≤ω ≤ω ()
    ≤𝟙 ≤𝟙 𝟙  𝟘  𝟘  ()
    ≤𝟙 ≤𝟙 𝟙  𝟘  𝟙  ()
    ≤𝟙 ≤𝟙 𝟙  𝟘  ≤𝟙 ()
    ≤𝟙 ≤𝟙 𝟙  𝟘  ≤ω ()
    ≤𝟙 ≤𝟙 𝟙  𝟙  𝟘  ()
    ≤𝟙 ≤𝟙 𝟙  𝟙  𝟙  ()
    ≤𝟙 ≤𝟙 𝟙  𝟙  ≤𝟙 ()
    ≤𝟙 ≤𝟙 𝟙  𝟙  ≤ω ()
    ≤𝟙 ≤𝟙 𝟙  ≤𝟙 𝟘  ()
    ≤𝟙 ≤𝟙 𝟙  ≤𝟙 𝟙  ()
    ≤𝟙 ≤𝟙 𝟙  ≤𝟙 ≤𝟙 ()
    ≤𝟙 ≤𝟙 𝟙  ≤𝟙 ≤ω ()
    ≤𝟙 ≤𝟙 𝟙  ≤ω 𝟘  ()
    ≤𝟙 ≤𝟙 𝟙  ≤ω 𝟙  ()
    ≤𝟙 ≤𝟙 𝟙  ≤ω ≤𝟙 ()
    ≤𝟙 ≤𝟙 𝟙  ≤ω ≤ω ()
    ≤𝟙 ≤𝟙 ≤𝟙 𝟘  𝟘  ()
    ≤𝟙 ≤𝟙 ≤𝟙 𝟘  𝟙  ()
    ≤𝟙 ≤𝟙 ≤𝟙 𝟘  ≤𝟙 ()
    ≤𝟙 ≤𝟙 ≤𝟙 𝟘  ≤ω ()
    ≤𝟙 ≤𝟙 ≤𝟙 𝟙  𝟘  ()
    ≤𝟙 ≤𝟙 ≤𝟙 𝟙  𝟙  ()
    ≤𝟙 ≤𝟙 ≤𝟙 𝟙  ≤𝟙 ()
    ≤𝟙 ≤𝟙 ≤𝟙 𝟙  ≤ω ()
    ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 𝟘  ()
    ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 𝟙  ()
    ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ()
    ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ≤ω ()
    ≤𝟙 ≤𝟙 ≤𝟙 ≤ω 𝟘  ()
    ≤𝟙 ≤𝟙 ≤𝟙 ≤ω 𝟙  ()
    ≤𝟙 ≤𝟙 ≤𝟙 ≤ω ≤𝟙 ()
    ≤𝟙 ≤𝟙 ≤𝟙 ≤ω ≤ω ()
    ≤𝟙 ≤𝟙 ≤ω 𝟘  𝟘  ()
    ≤𝟙 ≤𝟙 ≤ω 𝟘  𝟙  ()
    ≤𝟙 ≤𝟙 ≤ω 𝟘  ≤𝟙 ()
    ≤𝟙 ≤𝟙 ≤ω 𝟘  ≤ω ()
    ≤𝟙 ≤𝟙 ≤ω 𝟙  𝟘  ()
    ≤𝟙 ≤𝟙 ≤ω 𝟙  𝟙  ()
    ≤𝟙 ≤𝟙 ≤ω 𝟙  ≤𝟙 ()
    ≤𝟙 ≤𝟙 ≤ω 𝟙  ≤ω ()
    ≤𝟙 ≤𝟙 ≤ω ≤𝟙 𝟘  ()
    ≤𝟙 ≤𝟙 ≤ω ≤𝟙 𝟙  ()
    ≤𝟙 ≤𝟙 ≤ω ≤𝟙 ≤𝟙 ()
    ≤𝟙 ≤𝟙 ≤ω ≤𝟙 ≤ω ()
    ≤𝟙 ≤𝟙 ≤ω ≤ω 𝟘  ()
    ≤𝟙 ≤𝟙 ≤ω ≤ω 𝟙  ()
    ≤𝟙 ≤𝟙 ≤ω ≤ω ≤𝟙 ()
    ≤𝟙 ≤𝟙 ≤ω ≤ω ≤ω ()
    ≤ω ≤𝟙 𝟘  𝟘  𝟙  ()
    ≤ω ≤𝟙 𝟘  𝟘  ≤𝟙 ()
    ≤ω ≤𝟙 𝟘  𝟘  ≤ω ()
    ≤ω ≤𝟙 𝟘  𝟙  𝟘  ()
    ≤ω ≤𝟙 𝟘  𝟙  𝟙  ()
    ≤ω ≤𝟙 𝟘  𝟙  ≤𝟙 ()
    ≤ω ≤𝟙 𝟘  𝟙  ≤ω ()
    ≤ω ≤𝟙 𝟘  ≤𝟙 𝟘  ()
    ≤ω ≤𝟙 𝟘  ≤𝟙 𝟙  ()
    ≤ω ≤𝟙 𝟘  ≤𝟙 ≤𝟙 ()
    ≤ω ≤𝟙 𝟘  ≤𝟙 ≤ω ()
    ≤ω ≤𝟙 𝟘  ≤ω 𝟘  ()
    ≤ω ≤𝟙 𝟘  ≤ω 𝟙  ()
    ≤ω ≤𝟙 𝟘  ≤ω ≤𝟙 ()
    ≤ω ≤𝟙 𝟘  ≤ω ≤ω ()
    ≤ω ≤𝟙 𝟙  𝟘  𝟘  ()
    ≤ω ≤𝟙 𝟙  𝟘  𝟙  ()
    ≤ω ≤𝟙 𝟙  𝟘  ≤𝟙 ()
    ≤ω ≤𝟙 𝟙  𝟘  ≤ω ()
    ≤ω ≤𝟙 𝟙  𝟙  𝟘  ()
    ≤ω ≤𝟙 𝟙  𝟙  𝟙  ()
    ≤ω ≤𝟙 𝟙  𝟙  ≤𝟙 ()
    ≤ω ≤𝟙 𝟙  𝟙  ≤ω ()
    ≤ω ≤𝟙 𝟙  ≤𝟙 𝟘  ()
    ≤ω ≤𝟙 𝟙  ≤𝟙 𝟙  ()
    ≤ω ≤𝟙 𝟙  ≤𝟙 ≤𝟙 ()
    ≤ω ≤𝟙 𝟙  ≤𝟙 ≤ω ()
    ≤ω ≤𝟙 𝟙  ≤ω 𝟘  ()
    ≤ω ≤𝟙 𝟙  ≤ω 𝟙  ()
    ≤ω ≤𝟙 𝟙  ≤ω ≤𝟙 ()
    ≤ω ≤𝟙 𝟙  ≤ω ≤ω ()
    ≤ω ≤𝟙 ≤𝟙 𝟘  𝟘  ()
    ≤ω ≤𝟙 ≤𝟙 𝟘  𝟙  ()
    ≤ω ≤𝟙 ≤𝟙 𝟘  ≤𝟙 ()
    ≤ω ≤𝟙 ≤𝟙 𝟘  ≤ω ()
    ≤ω ≤𝟙 ≤𝟙 𝟙  𝟘  ()
    ≤ω ≤𝟙 ≤𝟙 𝟙  𝟙  ()
    ≤ω ≤𝟙 ≤𝟙 𝟙  ≤𝟙 ()
    ≤ω ≤𝟙 ≤𝟙 𝟙  ≤ω ()
    ≤ω ≤𝟙 ≤𝟙 ≤𝟙 𝟘  ()
    ≤ω ≤𝟙 ≤𝟙 ≤𝟙 𝟙  ()
    ≤ω ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ()
    ≤ω ≤𝟙 ≤𝟙 ≤𝟙 ≤ω ()
    ≤ω ≤𝟙 ≤𝟙 ≤ω 𝟘  ()
    ≤ω ≤𝟙 ≤𝟙 ≤ω 𝟙  ()
    ≤ω ≤𝟙 ≤𝟙 ≤ω ≤𝟙 ()
    ≤ω ≤𝟙 ≤𝟙 ≤ω ≤ω ()
    ≤ω ≤𝟙 ≤ω 𝟘  𝟘  ()
    ≤ω ≤𝟙 ≤ω 𝟘  𝟙  ()
    ≤ω ≤𝟙 ≤ω 𝟘  ≤𝟙 ()
    ≤ω ≤𝟙 ≤ω 𝟘  ≤ω ()
    ≤ω ≤𝟙 ≤ω 𝟙  𝟘  ()
    ≤ω ≤𝟙 ≤ω 𝟙  𝟙  ()
    ≤ω ≤𝟙 ≤ω 𝟙  ≤𝟙 ()
    ≤ω ≤𝟙 ≤ω 𝟙  ≤ω ()
    ≤ω ≤𝟙 ≤ω ≤𝟙 𝟘  ()
    ≤ω ≤𝟙 ≤ω ≤𝟙 𝟙  ()
    ≤ω ≤𝟙 ≤ω ≤𝟙 ≤𝟙 ()
    ≤ω ≤𝟙 ≤ω ≤𝟙 ≤ω ()
    ≤ω ≤𝟙 ≤ω ≤ω 𝟘  ()
    ≤ω ≤𝟙 ≤ω ≤ω 𝟙  ()
    ≤ω ≤𝟙 ≤ω ≤ω ≤𝟙 ()
    ≤ω ≤𝟙 ≤ω ≤ω ≤ω ()
    _  ≤ω 𝟘  𝟘  𝟙  ()
    _  ≤ω 𝟘  𝟘  ≤𝟙 ()
    _  ≤ω 𝟘  𝟘  ≤ω ()
    _  ≤ω 𝟘  𝟙  𝟘  ()
    _  ≤ω 𝟘  𝟙  𝟙  ()
    _  ≤ω 𝟘  𝟙  ≤𝟙 ()
    _  ≤ω 𝟘  𝟙  ≤ω ()
    _  ≤ω 𝟘  ≤𝟙 𝟘  ()
    _  ≤ω 𝟘  ≤𝟙 𝟙  ()
    _  ≤ω 𝟘  ≤𝟙 ≤𝟙 ()
    _  ≤ω 𝟘  ≤𝟙 ≤ω ()
    _  ≤ω 𝟘  ≤ω 𝟘  ()
    _  ≤ω 𝟘  ≤ω 𝟙  ()
    _  ≤ω 𝟘  ≤ω ≤𝟙 ()
    _  ≤ω 𝟘  ≤ω ≤ω ()
    _  ≤ω 𝟙  𝟘  𝟘  ()
    _  ≤ω 𝟙  𝟘  𝟙  ()
    _  ≤ω 𝟙  𝟘  ≤𝟙 ()
    _  ≤ω 𝟙  𝟘  ≤ω ()
    _  ≤ω 𝟙  𝟙  𝟘  ()
    _  ≤ω 𝟙  𝟙  𝟙  ()
    _  ≤ω 𝟙  𝟙  ≤𝟙 ()
    _  ≤ω 𝟙  𝟙  ≤ω ()
    _  ≤ω 𝟙  ≤𝟙 𝟘  ()
    _  ≤ω 𝟙  ≤𝟙 𝟙  ()
    _  ≤ω 𝟙  ≤𝟙 ≤𝟙 ()
    _  ≤ω 𝟙  ≤𝟙 ≤ω ()
    _  ≤ω 𝟙  ≤ω 𝟘  ()
    _  ≤ω 𝟙  ≤ω 𝟙  ()
    _  ≤ω 𝟙  ≤ω ≤𝟙 ()
    _  ≤ω 𝟙  ≤ω ≤ω ()
    _  ≤ω ≤𝟙 𝟘  𝟘  ()
    _  ≤ω ≤𝟙 𝟘  𝟙  ()
    _  ≤ω ≤𝟙 𝟘  ≤𝟙 ()
    _  ≤ω ≤𝟙 𝟘  ≤ω ()
    _  ≤ω ≤𝟙 𝟙  𝟘  ()
    _  ≤ω ≤𝟙 𝟙  𝟙  ()
    _  ≤ω ≤𝟙 𝟙  ≤𝟙 ()
    _  ≤ω ≤𝟙 𝟙  ≤ω ()
    _  ≤ω ≤𝟙 ≤𝟙 𝟘  ()
    _  ≤ω ≤𝟙 ≤𝟙 𝟙  ()
    _  ≤ω ≤𝟙 ≤𝟙 ≤𝟙 ()
    _  ≤ω ≤𝟙 ≤𝟙 ≤ω ()
    _  ≤ω ≤𝟙 ≤ω 𝟘  ()
    _  ≤ω ≤𝟙 ≤ω 𝟙  ()
    _  ≤ω ≤𝟙 ≤ω ≤𝟙 ()
    _  ≤ω ≤𝟙 ≤ω ≤ω ()
    _  ≤ω ≤ω 𝟘  𝟘  ()
    _  ≤ω ≤ω 𝟘  𝟙  ()
    _  ≤ω ≤ω 𝟘  ≤𝟙 ()
    _  ≤ω ≤ω 𝟘  ≤ω ()
    _  ≤ω ≤ω 𝟙  𝟘  ()
    _  ≤ω ≤ω 𝟙  𝟙  ()
    _  ≤ω ≤ω 𝟙  ≤𝟙 ()
    _  ≤ω ≤ω 𝟙  ≤ω ()
    _  ≤ω ≤ω ≤𝟙 𝟘  ()
    _  ≤ω ≤ω ≤𝟙 𝟙  ()
    _  ≤ω ≤ω ≤𝟙 ≤𝟙 ()
    _  ≤ω ≤ω ≤𝟙 ≤ω ()
    _  ≤ω ≤ω ≤ω 𝟘  ()
    _  ≤ω ≤ω ≤ω 𝟙  ()
    _  ≤ω ≤ω ≤ω ≤𝟙 ()
    _  ≤ω ≤ω ≤ω ≤ω ()

  lemma₂ : ∀ p r → nr p r 𝟘 𝟘 𝟘 ≡ 𝟘
  lemma₂ = λ where
    𝟘  𝟘  → refl
    𝟘  𝟙  → refl
    𝟘  ≤𝟙 → refl
    𝟘  ≤ω → refl
    𝟙  𝟘  → refl
    𝟙  𝟙  → refl
    𝟙  ≤𝟙 → refl
    𝟙  ≤ω → refl
    ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω → refl
    ≤ω 𝟘  → refl
    ≤ω 𝟙  → refl
    ≤ω ≤𝟙 → refl
    ≤ω ≤ω → refl

-- An nr function can be defined for
-- linear-or-affine-semiring-with-meet.

linear-or-affine-has-nr : Has-nr linear-or-affine-semiring-with-meet
linear-or-affine-has-nr = record
  { nr          = nr
  ; nr-monotone = λ {p = p} {r = r} → nr-monotone p r
  ; nr-·        = λ {p = _} {r = r} → nr-· r
  ; nr-+        = λ {p = _} {r = r} → nr-+ r
  ; nr-𝟘        = λ {p = _} {r = r} → nr-𝟘 r .proj₂ (refl , refl , refl)
  ; nr-positive = λ {p = _} {r = r} → nr-𝟘 r .proj₁
  ; nr-zero     = λ {n = _} {p = _} {r = r} → nr-zero r _ _ _ _
  ; nr-suc      = λ {p = _} {r = r} → nr-suc r _ _ _ _
  }
  where
  open Semiring-with-meet linear-or-affine-semiring-with-meet
    hiding (𝟘; 𝟙; _+_; _·_; _∧_; _≤_)
  open Addition linear-or-affine-semiring-with-meet
  open Meet linear-or-affine-semiring-with-meet
  open Multiplication linear-or-affine-semiring-with-meet
  open PartialOrder linear-or-affine-semiring-with-meet

  nr-monotone :
    ∀ p r →
    z₁ ≤ z₂ → s₁ ≤ s₂ → n₁ ≤ n₂ →
    nr p r z₁ s₁ n₁ ≤ nr p r z₂ s₂ n₂
  nr-monotone = λ where
    p 𝟘 z₁≤z₂ s₁≤s₂ n₁≤n₂ →
      ∧-monotone (+-monotone (·-monotoneʳ {r = 𝟙 ∧ p} n₁≤n₂) s₁≤s₂)
        (+-monotone n₁≤n₂ z₁≤z₂)
    p 𝟙 z₁≤z₂ s₁≤s₂ n₁≤n₂ →
      +-monotone (·-monotoneʳ {r = 𝟙 + p} n₁≤n₂)
        (+-monotone (·-monotoneʳ {r = ≤ω} s₁≤s₂) z₁≤z₂)
    p ≤𝟙 z₁≤z₂ s₁≤s₂ n₁≤n₂ →
      +-monotone (·-monotoneʳ {r = ≤𝟙 + p} n₁≤n₂)
        (+-monotone (·-monotoneʳ {r = ≤ω} s₁≤s₂)
           (·-monotoneʳ {r = ≤𝟙} z₁≤z₂))
    _ ≤ω z₁≤z₂ s₁≤s₂ n₁≤n₂ →
      ·-monotoneʳ {r = ≤ω} (+-monotone n₁≤n₂ (+-monotone s₁≤s₂ z₁≤z₂))

  nr-· : ∀ r → nr p r z s n · q ≤ nr p r (z · q) (s · q) (n · q)
  nr-· {p = p} {z = z} {s = s} {n = n} {q = q} = λ where
      𝟘 → begin
        (((𝟙 ∧ p) · n + s) ∧ (n + z)) · q              ≡⟨ ·-distribʳ-∧ _ ((𝟙 ∧ p) · _ + _) _ ⟩
        ((𝟙 ∧ p) · n + s) · q ∧ (n + z) · q            ≡⟨ ∧-cong (·-distribʳ-+ _ ((𝟙 ∧ p) · _) _)
                                                            (·-distribʳ-+ _ n _) ⟩
        (((𝟙 ∧ p) · n) · q + s · q) ∧ (n · q + z · q)  ≡⟨ ∧-congʳ (+-congʳ (·-assoc (𝟙 ∧ p) _ _)) ⟩
        ((𝟙 ∧ p) · (n · q) + s · q) ∧ (n · q + z · q)  ∎
      𝟙 → begin
        ((𝟙 + p) · n + ≤ω · s + z) · q            ≡⟨ ·-distribʳ-+ _ ((𝟙 + p) · _) _ ⟩
        ((𝟙 + p) · n) · q + (≤ω · s + z) · q      ≡⟨ +-congˡ {x = ((𝟙 + p) · _) · _}
                                                       (·-distribʳ-+ _ (≤ω · s) _) ⟩
        ((𝟙 + p) · n) · q + (≤ω · s) · q + z · q  ≡⟨ +-cong (·-assoc (𝟙 + p) _ _)
                                                       (+-congʳ (·-assoc ≤ω s _)) ⟩
        (𝟙 + p) · (n · q) + ≤ω · (s · q) + z · q  ∎
      ≤𝟙 → begin
        ((≤𝟙 + p) · n + ≤ω · s + ≤𝟙 · z) · q              ≡⟨ ·-distribʳ-+ _ ((≤𝟙 + p) · _) _ ⟩
        ((≤𝟙 + p) · n) · q + (≤ω · s + ≤𝟙 · z) · q        ≡⟨ +-congˡ {x = ((≤𝟙 + p) · _) · _}
                                                               (·-distribʳ-+ _ (≤ω · s) _) ⟩
        ((≤𝟙 + p) · n) · q + (≤ω · s) · q + (≤𝟙 · z) · q  ≡⟨ +-cong (·-assoc (≤𝟙 + p) _ _)
                                                               (+-cong (·-assoc ≤ω s _) (·-assoc ≤𝟙 z _)) ⟩
        (≤𝟙 + p) · (n · q) + ≤ω · (s · q) + ≤𝟙 · (z · q)  ∎
      ≤ω → begin
        (≤ω · (n + s + z)) · q        ≡⟨ ·-assoc ≤ω (n + _) _ ⟩
        ≤ω · ((n + s + z) · q)        ≡⟨ ·-congˡ {x = ≤ω} (·-distribʳ-+ _ n _) ⟩
        ≤ω · (n · q + (s + z) · q)    ≡⟨ ·-congˡ {x = ≤ω} (+-congˡ {x = n · _} (·-distribʳ-+ _ s _)) ⟩
        ≤ω · (n · q + s · q + z · q)  ∎
    where
    open Tools.Reasoning.PartialOrder ≤-poset

  nr-+ :
    ∀ r →
    nr p r z₁ s₁ n₁ + nr p r z₂ s₂ n₂ ≤
    nr p r (z₁ + z₂) (s₁ + s₂) (n₁ + n₂)
  nr-+
    {p = p}
    {z₁ = z₁} {s₁ = s₁} {n₁ = n₁}
    {z₂ = z₂} {s₂ = s₂} {n₂ = n₂} = λ where
      𝟘 → begin
        (((𝟙 ∧ p) · n₁ + s₁) ∧ (n₁ + z₁)) +
        (((𝟙 ∧ p) · n₂ + s₂) ∧ (n₂ + z₂))                            ≤⟨ +-sub-interchangeable-∧ ((𝟙 ∧ p) · _ + _) _ _ _ ⟩

        (((𝟙 ∧ p) · n₁ + s₁) + ((𝟙 ∧ p) · n₂ + s₂)) ∧
        ((n₁ + z₁) + (n₂ + z₂))                                      ≡⟨ ∧-cong (+-sub-interchangeable-+ ((𝟙 ∧ p) · _) _ _ _)
                                                                          (+-sub-interchangeable-+ n₁ _ _ _) ⟩
        (((𝟙 ∧ p) · n₁ + (𝟙 ∧ p) · n₂) + (s₁ + s₂)) ∧
        ((n₁ + n₂) + (z₁ + z₂))                                      ≡˘⟨ ∧-congʳ (+-congʳ (·-distribˡ-+ (𝟙 ∧ p) _ _)) ⟩

        ((𝟙 ∧ p) · (n₁ + n₂) + (s₁ + s₂)) ∧ ((n₁ + n₂) + (z₁ + z₂))  ∎
      𝟙 → begin
        ((𝟙 + p) · n₁ + ≤ω · s₁ + z₁) + ((𝟙 + p) · n₂ + ≤ω · s₂ + z₂)    ≡⟨ +-sub-interchangeable-+ ((𝟙 + p) · _) _ _ _ ⟩
        ((𝟙 + p) · n₁ + (𝟙 + p) · n₂) + (≤ω · s₁ + z₁) + (≤ω · s₂ + z₂)  ≡⟨ +-cong (sym (·-distribˡ-+ (𝟙 + p) _ _))
                                                                              (+-sub-interchangeable-+ (≤ω · s₁) _ _ _) ⟩
        (𝟙 + p) · (n₁ + n₂) + (≤ω · s₁ + ≤ω · s₂) + (z₁ + z₂)            ≡˘⟨ +-congˡ {x = (𝟙 + p) · _}
                                                                               (+-congʳ (·-distribˡ-+ ≤ω s₁ _)) ⟩
        (𝟙 + p) · (n₁ + n₂) + ≤ω · (s₁ + s₂) + (z₁ + z₂)                 ∎
      ≤𝟙 → begin
        ((≤𝟙 + p) · n₁ + ≤ω · s₁ + ≤𝟙 · z₁) +
        ((≤𝟙 + p) · n₂ + ≤ω · s₂ + ≤𝟙 · z₂)                               ≡⟨ +-sub-interchangeable-+ ((≤𝟙 + p) · _) _ _ _ ⟩

        ((≤𝟙 + p) · n₁ + (≤𝟙 + p) · n₂) +
        (≤ω · s₁ + ≤𝟙 · z₁) + (≤ω · s₂ + ≤𝟙 · z₂)                         ≡⟨ +-cong (sym (·-distribˡ-+ (≤𝟙 + p) _ _))
                                                                               (+-sub-interchangeable-+ (≤ω · s₁) _ _ _) ⟩

        (≤𝟙 + p) · (n₁ + n₂) + (≤ω · s₁ + ≤ω · s₂) + (≤𝟙 · z₁ + ≤𝟙 · z₂)  ≡˘⟨ +-congˡ {x = (≤𝟙 + p) · _}
                                                                                (+-cong (·-distribˡ-+ ≤ω s₁ _)
                                                                                   (·-distribˡ-+ ≤𝟙 z₁ _)) ⟩
        (≤𝟙 + p) · (n₁ + n₂) + ≤ω · (s₁ + s₂) + ≤𝟙 · (z₁ + z₂)            ∎
      ≤ω → begin
        ≤ω · (n₁ + s₁ + z₁) + ≤ω · (n₂ + s₂ + z₂)  ≡˘⟨ ·-distribˡ-+ ≤ω (n₁ + _) _ ⟩
        ≤ω · ((n₁ + s₁ + z₁) + (n₂ + s₂ + z₂))     ≡⟨ ·-congˡ {x = ≤ω} lemma ⟩
        ≤ω · ((n₁ + n₂) + (s₁ + s₂) + (z₁ + z₂))   ∎
    where
    lemma =
      (n₁ + s₁ + z₁) + (n₂ + s₂ + z₂)    ≡⟨ +-sub-interchangeable-+ n₁ _ _ _ ⟩
      (n₁ + n₂) + (s₁ + z₁) + (s₂ + z₂)  ≡⟨ +-congˡ {x = n₁ + _}
                                              (+-sub-interchangeable-+ s₁ _ _ _) ⟩
      (n₁ + n₂) + (s₁ + s₂) + (z₁ + z₂)  ∎
      where
      open Tools.Reasoning.PropositionalEquality

    open Tools.Reasoning.PartialOrder ≤-poset

  nr-zero : ∀ r p z s n → n ≤ 𝟘 → nr p r z s n ≤ z
  nr-zero = λ where
    𝟘  𝟘  𝟘  𝟘  𝟘  refl → refl
    𝟘  𝟘  𝟘  𝟘  ≤𝟙 refl → refl
    𝟘  𝟘  𝟘  𝟘  ≤ω refl → refl
    𝟘  𝟘  𝟘  𝟙  𝟘  refl → refl
    𝟘  𝟘  𝟘  𝟙  ≤𝟙 refl → refl
    𝟘  𝟘  𝟘  𝟙  ≤ω refl → refl
    𝟘  𝟘  𝟘  ≤𝟙 𝟘  refl → refl
    𝟘  𝟘  𝟘  ≤𝟙 ≤𝟙 refl → refl
    𝟘  𝟘  𝟘  ≤𝟙 ≤ω refl → refl
    𝟘  𝟘  𝟘  ≤ω 𝟘  refl → refl
    𝟘  𝟘  𝟘  ≤ω ≤𝟙 refl → refl
    𝟘  𝟘  𝟘  ≤ω ≤ω refl → refl
    𝟘  𝟘  𝟙  𝟘  𝟘  refl → refl
    𝟘  𝟘  𝟙  𝟘  ≤𝟙 refl → refl
    𝟘  𝟘  𝟙  𝟘  ≤ω refl → refl
    𝟘  𝟘  𝟙  𝟙  𝟘  refl → refl
    𝟘  𝟘  𝟙  𝟙  ≤𝟙 refl → refl
    𝟘  𝟘  𝟙  𝟙  ≤ω refl → refl
    𝟘  𝟘  𝟙  ≤𝟙 𝟘  refl → refl
    𝟘  𝟘  𝟙  ≤𝟙 ≤𝟙 refl → refl
    𝟘  𝟘  𝟙  ≤𝟙 ≤ω refl → refl
    𝟘  𝟘  𝟙  ≤ω 𝟘  refl → refl
    𝟘  𝟘  𝟙  ≤ω ≤𝟙 refl → refl
    𝟘  𝟘  𝟙  ≤ω ≤ω refl → refl
    𝟘  𝟘  ≤𝟙 𝟘  𝟘  refl → refl
    𝟘  𝟘  ≤𝟙 𝟘  ≤𝟙 refl → refl
    𝟘  𝟘  ≤𝟙 𝟘  ≤ω refl → refl
    𝟘  𝟘  ≤𝟙 𝟙  𝟘  refl → refl
    𝟘  𝟘  ≤𝟙 𝟙  ≤𝟙 refl → refl
    𝟘  𝟘  ≤𝟙 𝟙  ≤ω refl → refl
    𝟘  𝟘  ≤𝟙 ≤𝟙 𝟘  refl → refl
    𝟘  𝟘  ≤𝟙 ≤𝟙 ≤𝟙 refl → refl
    𝟘  𝟘  ≤𝟙 ≤𝟙 ≤ω refl → refl
    𝟘  𝟘  ≤𝟙 ≤ω 𝟘  refl → refl
    𝟘  𝟘  ≤𝟙 ≤ω ≤𝟙 refl → refl
    𝟘  𝟘  ≤𝟙 ≤ω ≤ω refl → refl
    𝟘  𝟘  ≤ω 𝟘  𝟘  refl → refl
    𝟘  𝟘  ≤ω 𝟘  ≤𝟙 refl → refl
    𝟘  𝟘  ≤ω 𝟘  ≤ω refl → refl
    𝟘  𝟘  ≤ω 𝟙  𝟘  refl → refl
    𝟘  𝟘  ≤ω 𝟙  ≤𝟙 refl → refl
    𝟘  𝟘  ≤ω 𝟙  ≤ω refl → refl
    𝟘  𝟘  ≤ω ≤𝟙 𝟘  refl → refl
    𝟘  𝟘  ≤ω ≤𝟙 ≤𝟙 refl → refl
    𝟘  𝟘  ≤ω ≤𝟙 ≤ω refl → refl
    𝟘  𝟘  ≤ω ≤ω 𝟘  refl → refl
    𝟘  𝟘  ≤ω ≤ω ≤𝟙 refl → refl
    𝟘  𝟘  ≤ω ≤ω ≤ω refl → refl
    𝟘  𝟙  𝟘  𝟘  𝟘  refl → refl
    𝟘  𝟙  𝟘  𝟘  ≤𝟙 refl → refl
    𝟘  𝟙  𝟘  𝟘  ≤ω refl → refl
    𝟘  𝟙  𝟘  𝟙  𝟘  refl → refl
    𝟘  𝟙  𝟘  𝟙  ≤𝟙 refl → refl
    𝟘  𝟙  𝟘  𝟙  ≤ω refl → refl
    𝟘  𝟙  𝟘  ≤𝟙 𝟘  refl → refl
    𝟘  𝟙  𝟘  ≤𝟙 ≤𝟙 refl → refl
    𝟘  𝟙  𝟘  ≤𝟙 ≤ω refl → refl
    𝟘  𝟙  𝟘  ≤ω 𝟘  refl → refl
    𝟘  𝟙  𝟘  ≤ω ≤𝟙 refl → refl
    𝟘  𝟙  𝟘  ≤ω ≤ω refl → refl
    𝟘  𝟙  𝟙  𝟘  𝟘  refl → refl
    𝟘  𝟙  𝟙  𝟘  ≤𝟙 refl → refl
    𝟘  𝟙  𝟙  𝟘  ≤ω refl → refl
    𝟘  𝟙  𝟙  𝟙  𝟘  refl → refl
    𝟘  𝟙  𝟙  𝟙  ≤𝟙 refl → refl
    𝟘  𝟙  𝟙  𝟙  ≤ω refl → refl
    𝟘  𝟙  𝟙  ≤𝟙 𝟘  refl → refl
    𝟘  𝟙  𝟙  ≤𝟙 ≤𝟙 refl → refl
    𝟘  𝟙  𝟙  ≤𝟙 ≤ω refl → refl
    𝟘  𝟙  𝟙  ≤ω 𝟘  refl → refl
    𝟘  𝟙  𝟙  ≤ω ≤𝟙 refl → refl
    𝟘  𝟙  𝟙  ≤ω ≤ω refl → refl
    𝟘  𝟙  ≤𝟙 𝟘  𝟘  refl → refl
    𝟘  𝟙  ≤𝟙 𝟘  ≤𝟙 refl → refl
    𝟘  𝟙  ≤𝟙 𝟘  ≤ω refl → refl
    𝟘  𝟙  ≤𝟙 𝟙  𝟘  refl → refl
    𝟘  𝟙  ≤𝟙 𝟙  ≤𝟙 refl → refl
    𝟘  𝟙  ≤𝟙 𝟙  ≤ω refl → refl
    𝟘  𝟙  ≤𝟙 ≤𝟙 𝟘  refl → refl
    𝟘  𝟙  ≤𝟙 ≤𝟙 ≤𝟙 refl → refl
    𝟘  𝟙  ≤𝟙 ≤𝟙 ≤ω refl → refl
    𝟘  𝟙  ≤𝟙 ≤ω 𝟘  refl → refl
    𝟘  𝟙  ≤𝟙 ≤ω ≤𝟙 refl → refl
    𝟘  𝟙  ≤𝟙 ≤ω ≤ω refl → refl
    𝟘  𝟙  ≤ω 𝟘  𝟘  refl → refl
    𝟘  𝟙  ≤ω 𝟘  ≤𝟙 refl → refl
    𝟘  𝟙  ≤ω 𝟘  ≤ω refl → refl
    𝟘  𝟙  ≤ω 𝟙  𝟘  refl → refl
    𝟘  𝟙  ≤ω 𝟙  ≤𝟙 refl → refl
    𝟘  𝟙  ≤ω 𝟙  ≤ω refl → refl
    𝟘  𝟙  ≤ω ≤𝟙 𝟘  refl → refl
    𝟘  𝟙  ≤ω ≤𝟙 ≤𝟙 refl → refl
    𝟘  𝟙  ≤ω ≤𝟙 ≤ω refl → refl
    𝟘  𝟙  ≤ω ≤ω 𝟘  refl → refl
    𝟘  𝟙  ≤ω ≤ω ≤𝟙 refl → refl
    𝟘  𝟙  ≤ω ≤ω ≤ω refl → refl
    𝟘  ≤𝟙 𝟘  𝟘  𝟘  refl → refl
    𝟘  ≤𝟙 𝟘  𝟘  ≤𝟙 refl → refl
    𝟘  ≤𝟙 𝟘  𝟘  ≤ω refl → refl
    𝟘  ≤𝟙 𝟘  𝟙  𝟘  refl → refl
    𝟘  ≤𝟙 𝟘  𝟙  ≤𝟙 refl → refl
    𝟘  ≤𝟙 𝟘  𝟙  ≤ω refl → refl
    𝟘  ≤𝟙 𝟘  ≤𝟙 𝟘  refl → refl
    𝟘  ≤𝟙 𝟘  ≤𝟙 ≤𝟙 refl → refl
    𝟘  ≤𝟙 𝟘  ≤𝟙 ≤ω refl → refl
    𝟘  ≤𝟙 𝟘  ≤ω 𝟘  refl → refl
    𝟘  ≤𝟙 𝟘  ≤ω ≤𝟙 refl → refl
    𝟘  ≤𝟙 𝟘  ≤ω ≤ω refl → refl
    𝟘  ≤𝟙 𝟙  𝟘  𝟘  refl → refl
    𝟘  ≤𝟙 𝟙  𝟘  ≤𝟙 refl → refl
    𝟘  ≤𝟙 𝟙  𝟘  ≤ω refl → refl
    𝟘  ≤𝟙 𝟙  𝟙  𝟘  refl → refl
    𝟘  ≤𝟙 𝟙  𝟙  ≤𝟙 refl → refl
    𝟘  ≤𝟙 𝟙  𝟙  ≤ω refl → refl
    𝟘  ≤𝟙 𝟙  ≤𝟙 𝟘  refl → refl
    𝟘  ≤𝟙 𝟙  ≤𝟙 ≤𝟙 refl → refl
    𝟘  ≤𝟙 𝟙  ≤𝟙 ≤ω refl → refl
    𝟘  ≤𝟙 𝟙  ≤ω 𝟘  refl → refl
    𝟘  ≤𝟙 𝟙  ≤ω ≤𝟙 refl → refl
    𝟘  ≤𝟙 𝟙  ≤ω ≤ω refl → refl
    𝟘  ≤𝟙 ≤𝟙 𝟘  𝟘  refl → refl
    𝟘  ≤𝟙 ≤𝟙 𝟘  ≤𝟙 refl → refl
    𝟘  ≤𝟙 ≤𝟙 𝟘  ≤ω refl → refl
    𝟘  ≤𝟙 ≤𝟙 𝟙  𝟘  refl → refl
    𝟘  ≤𝟙 ≤𝟙 𝟙  ≤𝟙 refl → refl
    𝟘  ≤𝟙 ≤𝟙 𝟙  ≤ω refl → refl
    𝟘  ≤𝟙 ≤𝟙 ≤𝟙 𝟘  refl → refl
    𝟘  ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 refl → refl
    𝟘  ≤𝟙 ≤𝟙 ≤𝟙 ≤ω refl → refl
    𝟘  ≤𝟙 ≤𝟙 ≤ω 𝟘  refl → refl
    𝟘  ≤𝟙 ≤𝟙 ≤ω ≤𝟙 refl → refl
    𝟘  ≤𝟙 ≤𝟙 ≤ω ≤ω refl → refl
    𝟘  ≤𝟙 ≤ω 𝟘  𝟘  refl → refl
    𝟘  ≤𝟙 ≤ω 𝟘  ≤𝟙 refl → refl
    𝟘  ≤𝟙 ≤ω 𝟘  ≤ω refl → refl
    𝟘  ≤𝟙 ≤ω 𝟙  𝟘  refl → refl
    𝟘  ≤𝟙 ≤ω 𝟙  ≤𝟙 refl → refl
    𝟘  ≤𝟙 ≤ω 𝟙  ≤ω refl → refl
    𝟘  ≤𝟙 ≤ω ≤𝟙 𝟘  refl → refl
    𝟘  ≤𝟙 ≤ω ≤𝟙 ≤𝟙 refl → refl
    𝟘  ≤𝟙 ≤ω ≤𝟙 ≤ω refl → refl
    𝟘  ≤𝟙 ≤ω ≤ω 𝟘  refl → refl
    𝟘  ≤𝟙 ≤ω ≤ω ≤𝟙 refl → refl
    𝟘  ≤𝟙 ≤ω ≤ω ≤ω refl → refl
    𝟘  ≤ω 𝟘  𝟘  𝟘  refl → refl
    𝟘  ≤ω 𝟘  𝟘  ≤𝟙 refl → refl
    𝟘  ≤ω 𝟘  𝟘  ≤ω refl → refl
    𝟘  ≤ω 𝟘  𝟙  𝟘  refl → refl
    𝟘  ≤ω 𝟘  𝟙  ≤𝟙 refl → refl
    𝟘  ≤ω 𝟘  𝟙  ≤ω refl → refl
    𝟘  ≤ω 𝟘  ≤𝟙 𝟘  refl → refl
    𝟘  ≤ω 𝟘  ≤𝟙 ≤𝟙 refl → refl
    𝟘  ≤ω 𝟘  ≤𝟙 ≤ω refl → refl
    𝟘  ≤ω 𝟘  ≤ω 𝟘  refl → refl
    𝟘  ≤ω 𝟘  ≤ω ≤𝟙 refl → refl
    𝟘  ≤ω 𝟘  ≤ω ≤ω refl → refl
    𝟘  ≤ω 𝟙  𝟘  𝟘  refl → refl
    𝟘  ≤ω 𝟙  𝟘  ≤𝟙 refl → refl
    𝟘  ≤ω 𝟙  𝟘  ≤ω refl → refl
    𝟘  ≤ω 𝟙  𝟙  𝟘  refl → refl
    𝟘  ≤ω 𝟙  𝟙  ≤𝟙 refl → refl
    𝟘  ≤ω 𝟙  𝟙  ≤ω refl → refl
    𝟘  ≤ω 𝟙  ≤𝟙 𝟘  refl → refl
    𝟘  ≤ω 𝟙  ≤𝟙 ≤𝟙 refl → refl
    𝟘  ≤ω 𝟙  ≤𝟙 ≤ω refl → refl
    𝟘  ≤ω 𝟙  ≤ω 𝟘  refl → refl
    𝟘  ≤ω 𝟙  ≤ω ≤𝟙 refl → refl
    𝟘  ≤ω 𝟙  ≤ω ≤ω refl → refl
    𝟘  ≤ω ≤𝟙 𝟘  𝟘  refl → refl
    𝟘  ≤ω ≤𝟙 𝟘  ≤𝟙 refl → refl
    𝟘  ≤ω ≤𝟙 𝟘  ≤ω refl → refl
    𝟘  ≤ω ≤𝟙 𝟙  𝟘  refl → refl
    𝟘  ≤ω ≤𝟙 𝟙  ≤𝟙 refl → refl
    𝟘  ≤ω ≤𝟙 𝟙  ≤ω refl → refl
    𝟘  ≤ω ≤𝟙 ≤𝟙 𝟘  refl → refl
    𝟘  ≤ω ≤𝟙 ≤𝟙 ≤𝟙 refl → refl
    𝟘  ≤ω ≤𝟙 ≤𝟙 ≤ω refl → refl
    𝟘  ≤ω ≤𝟙 ≤ω 𝟘  refl → refl
    𝟘  ≤ω ≤𝟙 ≤ω ≤𝟙 refl → refl
    𝟘  ≤ω ≤𝟙 ≤ω ≤ω refl → refl
    𝟘  ≤ω ≤ω 𝟘  𝟘  refl → refl
    𝟘  ≤ω ≤ω 𝟘  ≤𝟙 refl → refl
    𝟘  ≤ω ≤ω 𝟘  ≤ω refl → refl
    𝟘  ≤ω ≤ω 𝟙  𝟘  refl → refl
    𝟘  ≤ω ≤ω 𝟙  ≤𝟙 refl → refl
    𝟘  ≤ω ≤ω 𝟙  ≤ω refl → refl
    𝟘  ≤ω ≤ω ≤𝟙 𝟘  refl → refl
    𝟘  ≤ω ≤ω ≤𝟙 ≤𝟙 refl → refl
    𝟘  ≤ω ≤ω ≤𝟙 ≤ω refl → refl
    𝟘  ≤ω ≤ω ≤ω 𝟘  refl → refl
    𝟘  ≤ω ≤ω ≤ω ≤𝟙 refl → refl
    𝟘  ≤ω ≤ω ≤ω ≤ω refl → refl
    𝟙  𝟘  𝟘  𝟘  𝟘  refl → refl
    𝟙  𝟘  𝟘  𝟘  ≤𝟙 refl → refl
    𝟙  𝟘  𝟘  𝟘  ≤ω refl → refl
    𝟙  𝟘  𝟘  𝟙  𝟘  refl → refl
    𝟙  𝟘  𝟘  𝟙  ≤𝟙 refl → refl
    𝟙  𝟘  𝟘  𝟙  ≤ω refl → refl
    𝟙  𝟘  𝟘  ≤𝟙 𝟘  refl → refl
    𝟙  𝟘  𝟘  ≤𝟙 ≤𝟙 refl → refl
    𝟙  𝟘  𝟘  ≤𝟙 ≤ω refl → refl
    𝟙  𝟘  𝟘  ≤ω 𝟘  refl → refl
    𝟙  𝟘  𝟘  ≤ω ≤𝟙 refl → refl
    𝟙  𝟘  𝟘  ≤ω ≤ω refl → refl
    𝟙  𝟘  𝟙  𝟘  𝟘  refl → refl
    𝟙  𝟘  𝟙  𝟘  ≤𝟙 refl → refl
    𝟙  𝟘  𝟙  𝟘  ≤ω refl → refl
    𝟙  𝟘  𝟙  𝟙  𝟘  refl → refl
    𝟙  𝟘  𝟙  𝟙  ≤𝟙 refl → refl
    𝟙  𝟘  𝟙  𝟙  ≤ω refl → refl
    𝟙  𝟘  𝟙  ≤𝟙 𝟘  refl → refl
    𝟙  𝟘  𝟙  ≤𝟙 ≤𝟙 refl → refl
    𝟙  𝟘  𝟙  ≤𝟙 ≤ω refl → refl
    𝟙  𝟘  𝟙  ≤ω 𝟘  refl → refl
    𝟙  𝟘  𝟙  ≤ω ≤𝟙 refl → refl
    𝟙  𝟘  𝟙  ≤ω ≤ω refl → refl
    𝟙  𝟘  ≤𝟙 𝟘  𝟘  refl → refl
    𝟙  𝟘  ≤𝟙 𝟘  ≤𝟙 refl → refl
    𝟙  𝟘  ≤𝟙 𝟘  ≤ω refl → refl
    𝟙  𝟘  ≤𝟙 𝟙  𝟘  refl → refl
    𝟙  𝟘  ≤𝟙 𝟙  ≤𝟙 refl → refl
    𝟙  𝟘  ≤𝟙 𝟙  ≤ω refl → refl
    𝟙  𝟘  ≤𝟙 ≤𝟙 𝟘  refl → refl
    𝟙  𝟘  ≤𝟙 ≤𝟙 ≤𝟙 refl → refl
    𝟙  𝟘  ≤𝟙 ≤𝟙 ≤ω refl → refl
    𝟙  𝟘  ≤𝟙 ≤ω 𝟘  refl → refl
    𝟙  𝟘  ≤𝟙 ≤ω ≤𝟙 refl → refl
    𝟙  𝟘  ≤𝟙 ≤ω ≤ω refl → refl
    𝟙  𝟘  ≤ω 𝟘  𝟘  refl → refl
    𝟙  𝟘  ≤ω 𝟘  ≤𝟙 refl → refl
    𝟙  𝟘  ≤ω 𝟘  ≤ω refl → refl
    𝟙  𝟘  ≤ω 𝟙  𝟘  refl → refl
    𝟙  𝟘  ≤ω 𝟙  ≤𝟙 refl → refl
    𝟙  𝟘  ≤ω 𝟙  ≤ω refl → refl
    𝟙  𝟘  ≤ω ≤𝟙 𝟘  refl → refl
    𝟙  𝟘  ≤ω ≤𝟙 ≤𝟙 refl → refl
    𝟙  𝟘  ≤ω ≤𝟙 ≤ω refl → refl
    𝟙  𝟘  ≤ω ≤ω 𝟘  refl → refl
    𝟙  𝟘  ≤ω ≤ω ≤𝟙 refl → refl
    𝟙  𝟘  ≤ω ≤ω ≤ω refl → refl
    𝟙  𝟙  𝟘  𝟘  𝟘  refl → refl
    𝟙  𝟙  𝟘  𝟘  ≤𝟙 refl → refl
    𝟙  𝟙  𝟘  𝟘  ≤ω refl → refl
    𝟙  𝟙  𝟘  𝟙  𝟘  refl → refl
    𝟙  𝟙  𝟘  𝟙  ≤𝟙 refl → refl
    𝟙  𝟙  𝟘  𝟙  ≤ω refl → refl
    𝟙  𝟙  𝟘  ≤𝟙 𝟘  refl → refl
    𝟙  𝟙  𝟘  ≤𝟙 ≤𝟙 refl → refl
    𝟙  𝟙  𝟘  ≤𝟙 ≤ω refl → refl
    𝟙  𝟙  𝟘  ≤ω 𝟘  refl → refl
    𝟙  𝟙  𝟘  ≤ω ≤𝟙 refl → refl
    𝟙  𝟙  𝟘  ≤ω ≤ω refl → refl
    𝟙  𝟙  𝟙  𝟘  𝟘  refl → refl
    𝟙  𝟙  𝟙  𝟘  ≤𝟙 refl → refl
    𝟙  𝟙  𝟙  𝟘  ≤ω refl → refl
    𝟙  𝟙  𝟙  𝟙  𝟘  refl → refl
    𝟙  𝟙  𝟙  𝟙  ≤𝟙 refl → refl
    𝟙  𝟙  𝟙  𝟙  ≤ω refl → refl
    𝟙  𝟙  𝟙  ≤𝟙 𝟘  refl → refl
    𝟙  𝟙  𝟙  ≤𝟙 ≤𝟙 refl → refl
    𝟙  𝟙  𝟙  ≤𝟙 ≤ω refl → refl
    𝟙  𝟙  𝟙  ≤ω 𝟘  refl → refl
    𝟙  𝟙  𝟙  ≤ω ≤𝟙 refl → refl
    𝟙  𝟙  𝟙  ≤ω ≤ω refl → refl
    𝟙  𝟙  ≤𝟙 𝟘  𝟘  refl → refl
    𝟙  𝟙  ≤𝟙 𝟘  ≤𝟙 refl → refl
    𝟙  𝟙  ≤𝟙 𝟘  ≤ω refl → refl
    𝟙  𝟙  ≤𝟙 𝟙  𝟘  refl → refl
    𝟙  𝟙  ≤𝟙 𝟙  ≤𝟙 refl → refl
    𝟙  𝟙  ≤𝟙 𝟙  ≤ω refl → refl
    𝟙  𝟙  ≤𝟙 ≤𝟙 𝟘  refl → refl
    𝟙  𝟙  ≤𝟙 ≤𝟙 ≤𝟙 refl → refl
    𝟙  𝟙  ≤𝟙 ≤𝟙 ≤ω refl → refl
    𝟙  𝟙  ≤𝟙 ≤ω 𝟘  refl → refl
    𝟙  𝟙  ≤𝟙 ≤ω ≤𝟙 refl → refl
    𝟙  𝟙  ≤𝟙 ≤ω ≤ω refl → refl
    𝟙  𝟙  ≤ω 𝟘  𝟘  refl → refl
    𝟙  𝟙  ≤ω 𝟘  ≤𝟙 refl → refl
    𝟙  𝟙  ≤ω 𝟘  ≤ω refl → refl
    𝟙  𝟙  ≤ω 𝟙  𝟘  refl → refl
    𝟙  𝟙  ≤ω 𝟙  ≤𝟙 refl → refl
    𝟙  𝟙  ≤ω 𝟙  ≤ω refl → refl
    𝟙  𝟙  ≤ω ≤𝟙 𝟘  refl → refl
    𝟙  𝟙  ≤ω ≤𝟙 ≤𝟙 refl → refl
    𝟙  𝟙  ≤ω ≤𝟙 ≤ω refl → refl
    𝟙  𝟙  ≤ω ≤ω 𝟘  refl → refl
    𝟙  𝟙  ≤ω ≤ω ≤𝟙 refl → refl
    𝟙  𝟙  ≤ω ≤ω ≤ω refl → refl
    𝟙  ≤𝟙 𝟘  𝟘  𝟘  refl → refl
    𝟙  ≤𝟙 𝟘  𝟘  ≤𝟙 refl → refl
    𝟙  ≤𝟙 𝟘  𝟘  ≤ω refl → refl
    𝟙  ≤𝟙 𝟘  𝟙  𝟘  refl → refl
    𝟙  ≤𝟙 𝟘  𝟙  ≤𝟙 refl → refl
    𝟙  ≤𝟙 𝟘  𝟙  ≤ω refl → refl
    𝟙  ≤𝟙 𝟘  ≤𝟙 𝟘  refl → refl
    𝟙  ≤𝟙 𝟘  ≤𝟙 ≤𝟙 refl → refl
    𝟙  ≤𝟙 𝟘  ≤𝟙 ≤ω refl → refl
    𝟙  ≤𝟙 𝟘  ≤ω 𝟘  refl → refl
    𝟙  ≤𝟙 𝟘  ≤ω ≤𝟙 refl → refl
    𝟙  ≤𝟙 𝟘  ≤ω ≤ω refl → refl
    𝟙  ≤𝟙 𝟙  𝟘  𝟘  refl → refl
    𝟙  ≤𝟙 𝟙  𝟘  ≤𝟙 refl → refl
    𝟙  ≤𝟙 𝟙  𝟘  ≤ω refl → refl
    𝟙  ≤𝟙 𝟙  𝟙  𝟘  refl → refl
    𝟙  ≤𝟙 𝟙  𝟙  ≤𝟙 refl → refl
    𝟙  ≤𝟙 𝟙  𝟙  ≤ω refl → refl
    𝟙  ≤𝟙 𝟙  ≤𝟙 𝟘  refl → refl
    𝟙  ≤𝟙 𝟙  ≤𝟙 ≤𝟙 refl → refl
    𝟙  ≤𝟙 𝟙  ≤𝟙 ≤ω refl → refl
    𝟙  ≤𝟙 𝟙  ≤ω 𝟘  refl → refl
    𝟙  ≤𝟙 𝟙  ≤ω ≤𝟙 refl → refl
    𝟙  ≤𝟙 𝟙  ≤ω ≤ω refl → refl
    𝟙  ≤𝟙 ≤𝟙 𝟘  𝟘  refl → refl
    𝟙  ≤𝟙 ≤𝟙 𝟘  ≤𝟙 refl → refl
    𝟙  ≤𝟙 ≤𝟙 𝟘  ≤ω refl → refl
    𝟙  ≤𝟙 ≤𝟙 𝟙  𝟘  refl → refl
    𝟙  ≤𝟙 ≤𝟙 𝟙  ≤𝟙 refl → refl
    𝟙  ≤𝟙 ≤𝟙 𝟙  ≤ω refl → refl
    𝟙  ≤𝟙 ≤𝟙 ≤𝟙 𝟘  refl → refl
    𝟙  ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 refl → refl
    𝟙  ≤𝟙 ≤𝟙 ≤𝟙 ≤ω refl → refl
    𝟙  ≤𝟙 ≤𝟙 ≤ω 𝟘  refl → refl
    𝟙  ≤𝟙 ≤𝟙 ≤ω ≤𝟙 refl → refl
    𝟙  ≤𝟙 ≤𝟙 ≤ω ≤ω refl → refl
    𝟙  ≤𝟙 ≤ω 𝟘  𝟘  refl → refl
    𝟙  ≤𝟙 ≤ω 𝟘  ≤𝟙 refl → refl
    𝟙  ≤𝟙 ≤ω 𝟘  ≤ω refl → refl
    𝟙  ≤𝟙 ≤ω 𝟙  𝟘  refl → refl
    𝟙  ≤𝟙 ≤ω 𝟙  ≤𝟙 refl → refl
    𝟙  ≤𝟙 ≤ω 𝟙  ≤ω refl → refl
    𝟙  ≤𝟙 ≤ω ≤𝟙 𝟘  refl → refl
    𝟙  ≤𝟙 ≤ω ≤𝟙 ≤𝟙 refl → refl
    𝟙  ≤𝟙 ≤ω ≤𝟙 ≤ω refl → refl
    𝟙  ≤𝟙 ≤ω ≤ω 𝟘  refl → refl
    𝟙  ≤𝟙 ≤ω ≤ω ≤𝟙 refl → refl
    𝟙  ≤𝟙 ≤ω ≤ω ≤ω refl → refl
    𝟙  ≤ω 𝟘  𝟘  𝟘  refl → refl
    𝟙  ≤ω 𝟘  𝟘  ≤𝟙 refl → refl
    𝟙  ≤ω 𝟘  𝟘  ≤ω refl → refl
    𝟙  ≤ω 𝟘  𝟙  𝟘  refl → refl
    𝟙  ≤ω 𝟘  𝟙  ≤𝟙 refl → refl
    𝟙  ≤ω 𝟘  𝟙  ≤ω refl → refl
    𝟙  ≤ω 𝟘  ≤𝟙 𝟘  refl → refl
    𝟙  ≤ω 𝟘  ≤𝟙 ≤𝟙 refl → refl
    𝟙  ≤ω 𝟘  ≤𝟙 ≤ω refl → refl
    𝟙  ≤ω 𝟘  ≤ω 𝟘  refl → refl
    𝟙  ≤ω 𝟘  ≤ω ≤𝟙 refl → refl
    𝟙  ≤ω 𝟘  ≤ω ≤ω refl → refl
    𝟙  ≤ω 𝟙  𝟘  𝟘  refl → refl
    𝟙  ≤ω 𝟙  𝟘  ≤𝟙 refl → refl
    𝟙  ≤ω 𝟙  𝟘  ≤ω refl → refl
    𝟙  ≤ω 𝟙  𝟙  𝟘  refl → refl
    𝟙  ≤ω 𝟙  𝟙  ≤𝟙 refl → refl
    𝟙  ≤ω 𝟙  𝟙  ≤ω refl → refl
    𝟙  ≤ω 𝟙  ≤𝟙 𝟘  refl → refl
    𝟙  ≤ω 𝟙  ≤𝟙 ≤𝟙 refl → refl
    𝟙  ≤ω 𝟙  ≤𝟙 ≤ω refl → refl
    𝟙  ≤ω 𝟙  ≤ω 𝟘  refl → refl
    𝟙  ≤ω 𝟙  ≤ω ≤𝟙 refl → refl
    𝟙  ≤ω 𝟙  ≤ω ≤ω refl → refl
    𝟙  ≤ω ≤𝟙 𝟘  𝟘  refl → refl
    𝟙  ≤ω ≤𝟙 𝟘  ≤𝟙 refl → refl
    𝟙  ≤ω ≤𝟙 𝟘  ≤ω refl → refl
    𝟙  ≤ω ≤𝟙 𝟙  𝟘  refl → refl
    𝟙  ≤ω ≤𝟙 𝟙  ≤𝟙 refl → refl
    𝟙  ≤ω ≤𝟙 𝟙  ≤ω refl → refl
    𝟙  ≤ω ≤𝟙 ≤𝟙 𝟘  refl → refl
    𝟙  ≤ω ≤𝟙 ≤𝟙 ≤𝟙 refl → refl
    𝟙  ≤ω ≤𝟙 ≤𝟙 ≤ω refl → refl
    𝟙  ≤ω ≤𝟙 ≤ω 𝟘  refl → refl
    𝟙  ≤ω ≤𝟙 ≤ω ≤𝟙 refl → refl
    𝟙  ≤ω ≤𝟙 ≤ω ≤ω refl → refl
    𝟙  ≤ω ≤ω 𝟘  𝟘  refl → refl
    𝟙  ≤ω ≤ω 𝟘  ≤𝟙 refl → refl
    𝟙  ≤ω ≤ω 𝟘  ≤ω refl → refl
    𝟙  ≤ω ≤ω 𝟙  𝟘  refl → refl
    𝟙  ≤ω ≤ω 𝟙  ≤𝟙 refl → refl
    𝟙  ≤ω ≤ω 𝟙  ≤ω refl → refl
    𝟙  ≤ω ≤ω ≤𝟙 𝟘  refl → refl
    𝟙  ≤ω ≤ω ≤𝟙 ≤𝟙 refl → refl
    𝟙  ≤ω ≤ω ≤𝟙 ≤ω refl → refl
    𝟙  ≤ω ≤ω ≤ω 𝟘  refl → refl
    𝟙  ≤ω ≤ω ≤ω ≤𝟙 refl → refl
    𝟙  ≤ω ≤ω ≤ω ≤ω refl → refl
    ≤𝟙 𝟘  𝟘  𝟘  𝟘  refl → refl
    ≤𝟙 𝟘  𝟘  𝟘  ≤𝟙 refl → refl
    ≤𝟙 𝟘  𝟘  𝟘  ≤ω refl → refl
    ≤𝟙 𝟘  𝟘  𝟙  𝟘  refl → refl
    ≤𝟙 𝟘  𝟘  𝟙  ≤𝟙 refl → refl
    ≤𝟙 𝟘  𝟘  𝟙  ≤ω refl → refl
    ≤𝟙 𝟘  𝟘  ≤𝟙 𝟘  refl → refl
    ≤𝟙 𝟘  𝟘  ≤𝟙 ≤𝟙 refl → refl
    ≤𝟙 𝟘  𝟘  ≤𝟙 ≤ω refl → refl
    ≤𝟙 𝟘  𝟘  ≤ω 𝟘  refl → refl
    ≤𝟙 𝟘  𝟘  ≤ω ≤𝟙 refl → refl
    ≤𝟙 𝟘  𝟘  ≤ω ≤ω refl → refl
    ≤𝟙 𝟘  𝟙  𝟘  𝟘  refl → refl
    ≤𝟙 𝟘  𝟙  𝟘  ≤𝟙 refl → refl
    ≤𝟙 𝟘  𝟙  𝟘  ≤ω refl → refl
    ≤𝟙 𝟘  𝟙  𝟙  𝟘  refl → refl
    ≤𝟙 𝟘  𝟙  𝟙  ≤𝟙 refl → refl
    ≤𝟙 𝟘  𝟙  𝟙  ≤ω refl → refl
    ≤𝟙 𝟘  𝟙  ≤𝟙 𝟘  refl → refl
    ≤𝟙 𝟘  𝟙  ≤𝟙 ≤𝟙 refl → refl
    ≤𝟙 𝟘  𝟙  ≤𝟙 ≤ω refl → refl
    ≤𝟙 𝟘  𝟙  ≤ω 𝟘  refl → refl
    ≤𝟙 𝟘  𝟙  ≤ω ≤𝟙 refl → refl
    ≤𝟙 𝟘  𝟙  ≤ω ≤ω refl → refl
    ≤𝟙 𝟘  ≤𝟙 𝟘  𝟘  refl → refl
    ≤𝟙 𝟘  ≤𝟙 𝟘  ≤𝟙 refl → refl
    ≤𝟙 𝟘  ≤𝟙 𝟘  ≤ω refl → refl
    ≤𝟙 𝟘  ≤𝟙 𝟙  𝟘  refl → refl
    ≤𝟙 𝟘  ≤𝟙 𝟙  ≤𝟙 refl → refl
    ≤𝟙 𝟘  ≤𝟙 𝟙  ≤ω refl → refl
    ≤𝟙 𝟘  ≤𝟙 ≤𝟙 𝟘  refl → refl
    ≤𝟙 𝟘  ≤𝟙 ≤𝟙 ≤𝟙 refl → refl
    ≤𝟙 𝟘  ≤𝟙 ≤𝟙 ≤ω refl → refl
    ≤𝟙 𝟘  ≤𝟙 ≤ω 𝟘  refl → refl
    ≤𝟙 𝟘  ≤𝟙 ≤ω ≤𝟙 refl → refl
    ≤𝟙 𝟘  ≤𝟙 ≤ω ≤ω refl → refl
    ≤𝟙 𝟘  ≤ω 𝟘  𝟘  refl → refl
    ≤𝟙 𝟘  ≤ω 𝟘  ≤𝟙 refl → refl
    ≤𝟙 𝟘  ≤ω 𝟘  ≤ω refl → refl
    ≤𝟙 𝟘  ≤ω 𝟙  𝟘  refl → refl
    ≤𝟙 𝟘  ≤ω 𝟙  ≤𝟙 refl → refl
    ≤𝟙 𝟘  ≤ω 𝟙  ≤ω refl → refl
    ≤𝟙 𝟘  ≤ω ≤𝟙 𝟘  refl → refl
    ≤𝟙 𝟘  ≤ω ≤𝟙 ≤𝟙 refl → refl
    ≤𝟙 𝟘  ≤ω ≤𝟙 ≤ω refl → refl
    ≤𝟙 𝟘  ≤ω ≤ω 𝟘  refl → refl
    ≤𝟙 𝟘  ≤ω ≤ω ≤𝟙 refl → refl
    ≤𝟙 𝟘  ≤ω ≤ω ≤ω refl → refl
    ≤𝟙 𝟙  𝟘  𝟘  𝟘  refl → refl
    ≤𝟙 𝟙  𝟘  𝟘  ≤𝟙 refl → refl
    ≤𝟙 𝟙  𝟘  𝟘  ≤ω refl → refl
    ≤𝟙 𝟙  𝟘  𝟙  𝟘  refl → refl
    ≤𝟙 𝟙  𝟘  𝟙  ≤𝟙 refl → refl
    ≤𝟙 𝟙  𝟘  𝟙  ≤ω refl → refl
    ≤𝟙 𝟙  𝟘  ≤𝟙 𝟘  refl → refl
    ≤𝟙 𝟙  𝟘  ≤𝟙 ≤𝟙 refl → refl
    ≤𝟙 𝟙  𝟘  ≤𝟙 ≤ω refl → refl
    ≤𝟙 𝟙  𝟘  ≤ω 𝟘  refl → refl
    ≤𝟙 𝟙  𝟘  ≤ω ≤𝟙 refl → refl
    ≤𝟙 𝟙  𝟘  ≤ω ≤ω refl → refl
    ≤𝟙 𝟙  𝟙  𝟘  𝟘  refl → refl
    ≤𝟙 𝟙  𝟙  𝟘  ≤𝟙 refl → refl
    ≤𝟙 𝟙  𝟙  𝟘  ≤ω refl → refl
    ≤𝟙 𝟙  𝟙  𝟙  𝟘  refl → refl
    ≤𝟙 𝟙  𝟙  𝟙  ≤𝟙 refl → refl
    ≤𝟙 𝟙  𝟙  𝟙  ≤ω refl → refl
    ≤𝟙 𝟙  𝟙  ≤𝟙 𝟘  refl → refl
    ≤𝟙 𝟙  𝟙  ≤𝟙 ≤𝟙 refl → refl
    ≤𝟙 𝟙  𝟙  ≤𝟙 ≤ω refl → refl
    ≤𝟙 𝟙  𝟙  ≤ω 𝟘  refl → refl
    ≤𝟙 𝟙  𝟙  ≤ω ≤𝟙 refl → refl
    ≤𝟙 𝟙  𝟙  ≤ω ≤ω refl → refl
    ≤𝟙 𝟙  ≤𝟙 𝟘  𝟘  refl → refl
    ≤𝟙 𝟙  ≤𝟙 𝟘  ≤𝟙 refl → refl
    ≤𝟙 𝟙  ≤𝟙 𝟘  ≤ω refl → refl
    ≤𝟙 𝟙  ≤𝟙 𝟙  𝟘  refl → refl
    ≤𝟙 𝟙  ≤𝟙 𝟙  ≤𝟙 refl → refl
    ≤𝟙 𝟙  ≤𝟙 𝟙  ≤ω refl → refl
    ≤𝟙 𝟙  ≤𝟙 ≤𝟙 𝟘  refl → refl
    ≤𝟙 𝟙  ≤𝟙 ≤𝟙 ≤𝟙 refl → refl
    ≤𝟙 𝟙  ≤𝟙 ≤𝟙 ≤ω refl → refl
    ≤𝟙 𝟙  ≤𝟙 ≤ω 𝟘  refl → refl
    ≤𝟙 𝟙  ≤𝟙 ≤ω ≤𝟙 refl → refl
    ≤𝟙 𝟙  ≤𝟙 ≤ω ≤ω refl → refl
    ≤𝟙 𝟙  ≤ω 𝟘  𝟘  refl → refl
    ≤𝟙 𝟙  ≤ω 𝟘  ≤𝟙 refl → refl
    ≤𝟙 𝟙  ≤ω 𝟘  ≤ω refl → refl
    ≤𝟙 𝟙  ≤ω 𝟙  𝟘  refl → refl
    ≤𝟙 𝟙  ≤ω 𝟙  ≤𝟙 refl → refl
    ≤𝟙 𝟙  ≤ω 𝟙  ≤ω refl → refl
    ≤𝟙 𝟙  ≤ω ≤𝟙 𝟘  refl → refl
    ≤𝟙 𝟙  ≤ω ≤𝟙 ≤𝟙 refl → refl
    ≤𝟙 𝟙  ≤ω ≤𝟙 ≤ω refl → refl
    ≤𝟙 𝟙  ≤ω ≤ω 𝟘  refl → refl
    ≤𝟙 𝟙  ≤ω ≤ω ≤𝟙 refl → refl
    ≤𝟙 𝟙  ≤ω ≤ω ≤ω refl → refl
    ≤𝟙 ≤𝟙 𝟘  𝟘  𝟘  refl → refl
    ≤𝟙 ≤𝟙 𝟘  𝟘  ≤𝟙 refl → refl
    ≤𝟙 ≤𝟙 𝟘  𝟘  ≤ω refl → refl
    ≤𝟙 ≤𝟙 𝟘  𝟙  𝟘  refl → refl
    ≤𝟙 ≤𝟙 𝟘  𝟙  ≤𝟙 refl → refl
    ≤𝟙 ≤𝟙 𝟘  𝟙  ≤ω refl → refl
    ≤𝟙 ≤𝟙 𝟘  ≤𝟙 𝟘  refl → refl
    ≤𝟙 ≤𝟙 𝟘  ≤𝟙 ≤𝟙 refl → refl
    ≤𝟙 ≤𝟙 𝟘  ≤𝟙 ≤ω refl → refl
    ≤𝟙 ≤𝟙 𝟘  ≤ω 𝟘  refl → refl
    ≤𝟙 ≤𝟙 𝟘  ≤ω ≤𝟙 refl → refl
    ≤𝟙 ≤𝟙 𝟘  ≤ω ≤ω refl → refl
    ≤𝟙 ≤𝟙 𝟙  𝟘  𝟘  refl → refl
    ≤𝟙 ≤𝟙 𝟙  𝟘  ≤𝟙 refl → refl
    ≤𝟙 ≤𝟙 𝟙  𝟘  ≤ω refl → refl
    ≤𝟙 ≤𝟙 𝟙  𝟙  𝟘  refl → refl
    ≤𝟙 ≤𝟙 𝟙  𝟙  ≤𝟙 refl → refl
    ≤𝟙 ≤𝟙 𝟙  𝟙  ≤ω refl → refl
    ≤𝟙 ≤𝟙 𝟙  ≤𝟙 𝟘  refl → refl
    ≤𝟙 ≤𝟙 𝟙  ≤𝟙 ≤𝟙 refl → refl
    ≤𝟙 ≤𝟙 𝟙  ≤𝟙 ≤ω refl → refl
    ≤𝟙 ≤𝟙 𝟙  ≤ω 𝟘  refl → refl
    ≤𝟙 ≤𝟙 𝟙  ≤ω ≤𝟙 refl → refl
    ≤𝟙 ≤𝟙 𝟙  ≤ω ≤ω refl → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟘  𝟘  refl → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟘  ≤𝟙 refl → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟘  ≤ω refl → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟙  𝟘  refl → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟙  ≤𝟙 refl → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟙  ≤ω refl → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 𝟘  refl → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 refl → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ≤ω refl → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤ω 𝟘  refl → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤ω ≤𝟙 refl → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤ω ≤ω refl → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟘  𝟘  refl → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟘  ≤𝟙 refl → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟘  ≤ω refl → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟙  𝟘  refl → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟙  ≤𝟙 refl → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟙  ≤ω refl → refl
    ≤𝟙 ≤𝟙 ≤ω ≤𝟙 𝟘  refl → refl
    ≤𝟙 ≤𝟙 ≤ω ≤𝟙 ≤𝟙 refl → refl
    ≤𝟙 ≤𝟙 ≤ω ≤𝟙 ≤ω refl → refl
    ≤𝟙 ≤𝟙 ≤ω ≤ω 𝟘  refl → refl
    ≤𝟙 ≤𝟙 ≤ω ≤ω ≤𝟙 refl → refl
    ≤𝟙 ≤𝟙 ≤ω ≤ω ≤ω refl → refl
    ≤𝟙 ≤ω 𝟘  𝟘  𝟘  refl → refl
    ≤𝟙 ≤ω 𝟘  𝟘  ≤𝟙 refl → refl
    ≤𝟙 ≤ω 𝟘  𝟘  ≤ω refl → refl
    ≤𝟙 ≤ω 𝟘  𝟙  𝟘  refl → refl
    ≤𝟙 ≤ω 𝟘  𝟙  ≤𝟙 refl → refl
    ≤𝟙 ≤ω 𝟘  𝟙  ≤ω refl → refl
    ≤𝟙 ≤ω 𝟘  ≤𝟙 𝟘  refl → refl
    ≤𝟙 ≤ω 𝟘  ≤𝟙 ≤𝟙 refl → refl
    ≤𝟙 ≤ω 𝟘  ≤𝟙 ≤ω refl → refl
    ≤𝟙 ≤ω 𝟘  ≤ω 𝟘  refl → refl
    ≤𝟙 ≤ω 𝟘  ≤ω ≤𝟙 refl → refl
    ≤𝟙 ≤ω 𝟘  ≤ω ≤ω refl → refl
    ≤𝟙 ≤ω 𝟙  𝟘  𝟘  refl → refl
    ≤𝟙 ≤ω 𝟙  𝟘  ≤𝟙 refl → refl
    ≤𝟙 ≤ω 𝟙  𝟘  ≤ω refl → refl
    ≤𝟙 ≤ω 𝟙  𝟙  𝟘  refl → refl
    ≤𝟙 ≤ω 𝟙  𝟙  ≤𝟙 refl → refl
    ≤𝟙 ≤ω 𝟙  𝟙  ≤ω refl → refl
    ≤𝟙 ≤ω 𝟙  ≤𝟙 𝟘  refl → refl
    ≤𝟙 ≤ω 𝟙  ≤𝟙 ≤𝟙 refl → refl
    ≤𝟙 ≤ω 𝟙  ≤𝟙 ≤ω refl → refl
    ≤𝟙 ≤ω 𝟙  ≤ω 𝟘  refl → refl
    ≤𝟙 ≤ω 𝟙  ≤ω ≤𝟙 refl → refl
    ≤𝟙 ≤ω 𝟙  ≤ω ≤ω refl → refl
    ≤𝟙 ≤ω ≤𝟙 𝟘  𝟘  refl → refl
    ≤𝟙 ≤ω ≤𝟙 𝟘  ≤𝟙 refl → refl
    ≤𝟙 ≤ω ≤𝟙 𝟘  ≤ω refl → refl
    ≤𝟙 ≤ω ≤𝟙 𝟙  𝟘  refl → refl
    ≤𝟙 ≤ω ≤𝟙 𝟙  ≤𝟙 refl → refl
    ≤𝟙 ≤ω ≤𝟙 𝟙  ≤ω refl → refl
    ≤𝟙 ≤ω ≤𝟙 ≤𝟙 𝟘  refl → refl
    ≤𝟙 ≤ω ≤𝟙 ≤𝟙 ≤𝟙 refl → refl
    ≤𝟙 ≤ω ≤𝟙 ≤𝟙 ≤ω refl → refl
    ≤𝟙 ≤ω ≤𝟙 ≤ω 𝟘  refl → refl
    ≤𝟙 ≤ω ≤𝟙 ≤ω ≤𝟙 refl → refl
    ≤𝟙 ≤ω ≤𝟙 ≤ω ≤ω refl → refl
    ≤𝟙 ≤ω ≤ω 𝟘  𝟘  refl → refl
    ≤𝟙 ≤ω ≤ω 𝟘  ≤𝟙 refl → refl
    ≤𝟙 ≤ω ≤ω 𝟘  ≤ω refl → refl
    ≤𝟙 ≤ω ≤ω 𝟙  𝟘  refl → refl
    ≤𝟙 ≤ω ≤ω 𝟙  ≤𝟙 refl → refl
    ≤𝟙 ≤ω ≤ω 𝟙  ≤ω refl → refl
    ≤𝟙 ≤ω ≤ω ≤𝟙 𝟘  refl → refl
    ≤𝟙 ≤ω ≤ω ≤𝟙 ≤𝟙 refl → refl
    ≤𝟙 ≤ω ≤ω ≤𝟙 ≤ω refl → refl
    ≤𝟙 ≤ω ≤ω ≤ω 𝟘  refl → refl
    ≤𝟙 ≤ω ≤ω ≤ω ≤𝟙 refl → refl
    ≤𝟙 ≤ω ≤ω ≤ω ≤ω refl → refl
    ≤ω _  𝟘  𝟘  𝟘  refl → refl
    ≤ω _  𝟘  𝟘  ≤𝟙 refl → refl
    ≤ω _  𝟘  𝟘  ≤ω refl → refl
    ≤ω _  𝟘  𝟙  𝟘  refl → refl
    ≤ω _  𝟘  𝟙  ≤𝟙 refl → refl
    ≤ω _  𝟘  𝟙  ≤ω refl → refl
    ≤ω _  𝟘  ≤𝟙 𝟘  refl → refl
    ≤ω _  𝟘  ≤𝟙 ≤𝟙 refl → refl
    ≤ω _  𝟘  ≤𝟙 ≤ω refl → refl
    ≤ω _  𝟘  ≤ω 𝟘  refl → refl
    ≤ω _  𝟘  ≤ω ≤𝟙 refl → refl
    ≤ω _  𝟘  ≤ω ≤ω refl → refl
    ≤ω _  𝟙  𝟘  𝟘  refl → refl
    ≤ω _  𝟙  𝟘  ≤𝟙 refl → refl
    ≤ω _  𝟙  𝟘  ≤ω refl → refl
    ≤ω _  𝟙  𝟙  𝟘  refl → refl
    ≤ω _  𝟙  𝟙  ≤𝟙 refl → refl
    ≤ω _  𝟙  𝟙  ≤ω refl → refl
    ≤ω _  𝟙  ≤𝟙 𝟘  refl → refl
    ≤ω _  𝟙  ≤𝟙 ≤𝟙 refl → refl
    ≤ω _  𝟙  ≤𝟙 ≤ω refl → refl
    ≤ω _  𝟙  ≤ω 𝟘  refl → refl
    ≤ω _  𝟙  ≤ω ≤𝟙 refl → refl
    ≤ω _  𝟙  ≤ω ≤ω refl → refl
    ≤ω _  ≤𝟙 𝟘  𝟘  refl → refl
    ≤ω _  ≤𝟙 𝟘  ≤𝟙 refl → refl
    ≤ω _  ≤𝟙 𝟘  ≤ω refl → refl
    ≤ω _  ≤𝟙 𝟙  𝟘  refl → refl
    ≤ω _  ≤𝟙 𝟙  ≤𝟙 refl → refl
    ≤ω _  ≤𝟙 𝟙  ≤ω refl → refl
    ≤ω _  ≤𝟙 ≤𝟙 𝟘  refl → refl
    ≤ω _  ≤𝟙 ≤𝟙 ≤𝟙 refl → refl
    ≤ω _  ≤𝟙 ≤𝟙 ≤ω refl → refl
    ≤ω _  ≤𝟙 ≤ω 𝟘  refl → refl
    ≤ω _  ≤𝟙 ≤ω ≤𝟙 refl → refl
    ≤ω _  ≤𝟙 ≤ω ≤ω refl → refl
    ≤ω _  ≤ω 𝟘  𝟘  refl → refl
    ≤ω _  ≤ω 𝟘  ≤𝟙 refl → refl
    ≤ω _  ≤ω 𝟘  ≤ω refl → refl
    ≤ω _  ≤ω 𝟙  𝟘  refl → refl
    ≤ω _  ≤ω 𝟙  ≤𝟙 refl → refl
    ≤ω _  ≤ω 𝟙  ≤ω refl → refl
    ≤ω _  ≤ω ≤𝟙 𝟘  refl → refl
    ≤ω _  ≤ω ≤𝟙 ≤𝟙 refl → refl
    ≤ω _  ≤ω ≤𝟙 ≤ω refl → refl
    ≤ω _  ≤ω ≤ω 𝟘  refl → refl
    ≤ω _  ≤ω ≤ω ≤𝟙 refl → refl
    ≤ω _  ≤ω ≤ω ≤ω refl → refl

  nr-suc : ∀ r p z s n → nr p r z s n ≤ s + p · n + r · nr p r z s n
  nr-suc = λ where
    𝟘  𝟘  𝟘  𝟘  𝟘  → refl
    𝟘  𝟘  𝟘  𝟘  𝟙  → refl
    𝟘  𝟘  𝟘  𝟘  ≤𝟙 → refl
    𝟘  𝟘  𝟘  𝟘  ≤ω → refl
    𝟘  𝟘  𝟘  𝟙  𝟘  → refl
    𝟘  𝟘  𝟘  𝟙  𝟙  → refl
    𝟘  𝟘  𝟘  𝟙  ≤𝟙 → refl
    𝟘  𝟘  𝟘  𝟙  ≤ω → refl
    𝟘  𝟘  𝟘  ≤𝟙 𝟘  → refl
    𝟘  𝟘  𝟘  ≤𝟙 𝟙  → refl
    𝟘  𝟘  𝟘  ≤𝟙 ≤𝟙 → refl
    𝟘  𝟘  𝟘  ≤𝟙 ≤ω → refl
    𝟘  𝟘  𝟘  ≤ω 𝟘  → refl
    𝟘  𝟘  𝟘  ≤ω 𝟙  → refl
    𝟘  𝟘  𝟘  ≤ω ≤𝟙 → refl
    𝟘  𝟘  𝟘  ≤ω ≤ω → refl
    𝟘  𝟘  𝟙  𝟘  𝟘  → refl
    𝟘  𝟘  𝟙  𝟘  𝟙  → refl
    𝟘  𝟘  𝟙  𝟘  ≤𝟙 → refl
    𝟘  𝟘  𝟙  𝟘  ≤ω → refl
    𝟘  𝟘  𝟙  𝟙  𝟘  → refl
    𝟘  𝟘  𝟙  𝟙  𝟙  → refl
    𝟘  𝟘  𝟙  𝟙  ≤𝟙 → refl
    𝟘  𝟘  𝟙  𝟙  ≤ω → refl
    𝟘  𝟘  𝟙  ≤𝟙 𝟘  → refl
    𝟘  𝟘  𝟙  ≤𝟙 𝟙  → refl
    𝟘  𝟘  𝟙  ≤𝟙 ≤𝟙 → refl
    𝟘  𝟘  𝟙  ≤𝟙 ≤ω → refl
    𝟘  𝟘  𝟙  ≤ω 𝟘  → refl
    𝟘  𝟘  𝟙  ≤ω 𝟙  → refl
    𝟘  𝟘  𝟙  ≤ω ≤𝟙 → refl
    𝟘  𝟘  𝟙  ≤ω ≤ω → refl
    𝟘  𝟘  ≤𝟙 𝟘  𝟘  → refl
    𝟘  𝟘  ≤𝟙 𝟘  𝟙  → refl
    𝟘  𝟘  ≤𝟙 𝟘  ≤𝟙 → refl
    𝟘  𝟘  ≤𝟙 𝟘  ≤ω → refl
    𝟘  𝟘  ≤𝟙 𝟙  𝟘  → refl
    𝟘  𝟘  ≤𝟙 𝟙  𝟙  → refl
    𝟘  𝟘  ≤𝟙 𝟙  ≤𝟙 → refl
    𝟘  𝟘  ≤𝟙 𝟙  ≤ω → refl
    𝟘  𝟘  ≤𝟙 ≤𝟙 𝟘  → refl
    𝟘  𝟘  ≤𝟙 ≤𝟙 𝟙  → refl
    𝟘  𝟘  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟘  𝟘  ≤𝟙 ≤𝟙 ≤ω → refl
    𝟘  𝟘  ≤𝟙 ≤ω 𝟘  → refl
    𝟘  𝟘  ≤𝟙 ≤ω 𝟙  → refl
    𝟘  𝟘  ≤𝟙 ≤ω ≤𝟙 → refl
    𝟘  𝟘  ≤𝟙 ≤ω ≤ω → refl
    𝟘  𝟘  ≤ω 𝟘  𝟘  → refl
    𝟘  𝟘  ≤ω 𝟘  𝟙  → refl
    𝟘  𝟘  ≤ω 𝟘  ≤𝟙 → refl
    𝟘  𝟘  ≤ω 𝟘  ≤ω → refl
    𝟘  𝟘  ≤ω 𝟙  𝟘  → refl
    𝟘  𝟘  ≤ω 𝟙  𝟙  → refl
    𝟘  𝟘  ≤ω 𝟙  ≤𝟙 → refl
    𝟘  𝟘  ≤ω 𝟙  ≤ω → refl
    𝟘  𝟘  ≤ω ≤𝟙 𝟘  → refl
    𝟘  𝟘  ≤ω ≤𝟙 𝟙  → refl
    𝟘  𝟘  ≤ω ≤𝟙 ≤𝟙 → refl
    𝟘  𝟘  ≤ω ≤𝟙 ≤ω → refl
    𝟘  𝟘  ≤ω ≤ω 𝟘  → refl
    𝟘  𝟘  ≤ω ≤ω 𝟙  → refl
    𝟘  𝟘  ≤ω ≤ω ≤𝟙 → refl
    𝟘  𝟘  ≤ω ≤ω ≤ω → refl
    𝟘  𝟙  𝟘  𝟘  𝟘  → refl
    𝟘  𝟙  𝟘  𝟘  𝟙  → refl
    𝟘  𝟙  𝟘  𝟘  ≤𝟙 → refl
    𝟘  𝟙  𝟘  𝟘  ≤ω → refl
    𝟘  𝟙  𝟘  𝟙  𝟘  → refl
    𝟘  𝟙  𝟘  𝟙  𝟙  → refl
    𝟘  𝟙  𝟘  𝟙  ≤𝟙 → refl
    𝟘  𝟙  𝟘  𝟙  ≤ω → refl
    𝟘  𝟙  𝟘  ≤𝟙 𝟘  → refl
    𝟘  𝟙  𝟘  ≤𝟙 𝟙  → refl
    𝟘  𝟙  𝟘  ≤𝟙 ≤𝟙 → refl
    𝟘  𝟙  𝟘  ≤𝟙 ≤ω → refl
    𝟘  𝟙  𝟘  ≤ω 𝟘  → refl
    𝟘  𝟙  𝟘  ≤ω 𝟙  → refl
    𝟘  𝟙  𝟘  ≤ω ≤𝟙 → refl
    𝟘  𝟙  𝟘  ≤ω ≤ω → refl
    𝟘  𝟙  𝟙  𝟘  𝟘  → refl
    𝟘  𝟙  𝟙  𝟘  𝟙  → refl
    𝟘  𝟙  𝟙  𝟘  ≤𝟙 → refl
    𝟘  𝟙  𝟙  𝟘  ≤ω → refl
    𝟘  𝟙  𝟙  𝟙  𝟘  → refl
    𝟘  𝟙  𝟙  𝟙  𝟙  → refl
    𝟘  𝟙  𝟙  𝟙  ≤𝟙 → refl
    𝟘  𝟙  𝟙  𝟙  ≤ω → refl
    𝟘  𝟙  𝟙  ≤𝟙 𝟘  → refl
    𝟘  𝟙  𝟙  ≤𝟙 𝟙  → refl
    𝟘  𝟙  𝟙  ≤𝟙 ≤𝟙 → refl
    𝟘  𝟙  𝟙  ≤𝟙 ≤ω → refl
    𝟘  𝟙  𝟙  ≤ω 𝟘  → refl
    𝟘  𝟙  𝟙  ≤ω 𝟙  → refl
    𝟘  𝟙  𝟙  ≤ω ≤𝟙 → refl
    𝟘  𝟙  𝟙  ≤ω ≤ω → refl
    𝟘  𝟙  ≤𝟙 𝟘  𝟘  → refl
    𝟘  𝟙  ≤𝟙 𝟘  𝟙  → refl
    𝟘  𝟙  ≤𝟙 𝟘  ≤𝟙 → refl
    𝟘  𝟙  ≤𝟙 𝟘  ≤ω → refl
    𝟘  𝟙  ≤𝟙 𝟙  𝟘  → refl
    𝟘  𝟙  ≤𝟙 𝟙  𝟙  → refl
    𝟘  𝟙  ≤𝟙 𝟙  ≤𝟙 → refl
    𝟘  𝟙  ≤𝟙 𝟙  ≤ω → refl
    𝟘  𝟙  ≤𝟙 ≤𝟙 𝟘  → refl
    𝟘  𝟙  ≤𝟙 ≤𝟙 𝟙  → refl
    𝟘  𝟙  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟘  𝟙  ≤𝟙 ≤𝟙 ≤ω → refl
    𝟘  𝟙  ≤𝟙 ≤ω 𝟘  → refl
    𝟘  𝟙  ≤𝟙 ≤ω 𝟙  → refl
    𝟘  𝟙  ≤𝟙 ≤ω ≤𝟙 → refl
    𝟘  𝟙  ≤𝟙 ≤ω ≤ω → refl
    𝟘  𝟙  ≤ω 𝟘  𝟘  → refl
    𝟘  𝟙  ≤ω 𝟘  𝟙  → refl
    𝟘  𝟙  ≤ω 𝟘  ≤𝟙 → refl
    𝟘  𝟙  ≤ω 𝟘  ≤ω → refl
    𝟘  𝟙  ≤ω 𝟙  𝟘  → refl
    𝟘  𝟙  ≤ω 𝟙  𝟙  → refl
    𝟘  𝟙  ≤ω 𝟙  ≤𝟙 → refl
    𝟘  𝟙  ≤ω 𝟙  ≤ω → refl
    𝟘  𝟙  ≤ω ≤𝟙 𝟘  → refl
    𝟘  𝟙  ≤ω ≤𝟙 𝟙  → refl
    𝟘  𝟙  ≤ω ≤𝟙 ≤𝟙 → refl
    𝟘  𝟙  ≤ω ≤𝟙 ≤ω → refl
    𝟘  𝟙  ≤ω ≤ω 𝟘  → refl
    𝟘  𝟙  ≤ω ≤ω 𝟙  → refl
    𝟘  𝟙  ≤ω ≤ω ≤𝟙 → refl
    𝟘  𝟙  ≤ω ≤ω ≤ω → refl
    𝟘  ≤𝟙 𝟘  𝟘  𝟘  → refl
    𝟘  ≤𝟙 𝟘  𝟘  𝟙  → refl
    𝟘  ≤𝟙 𝟘  𝟘  ≤𝟙 → refl
    𝟘  ≤𝟙 𝟘  𝟘  ≤ω → refl
    𝟘  ≤𝟙 𝟘  𝟙  𝟘  → refl
    𝟘  ≤𝟙 𝟘  𝟙  𝟙  → refl
    𝟘  ≤𝟙 𝟘  𝟙  ≤𝟙 → refl
    𝟘  ≤𝟙 𝟘  𝟙  ≤ω → refl
    𝟘  ≤𝟙 𝟘  ≤𝟙 𝟘  → refl
    𝟘  ≤𝟙 𝟘  ≤𝟙 𝟙  → refl
    𝟘  ≤𝟙 𝟘  ≤𝟙 ≤𝟙 → refl
    𝟘  ≤𝟙 𝟘  ≤𝟙 ≤ω → refl
    𝟘  ≤𝟙 𝟘  ≤ω 𝟘  → refl
    𝟘  ≤𝟙 𝟘  ≤ω 𝟙  → refl
    𝟘  ≤𝟙 𝟘  ≤ω ≤𝟙 → refl
    𝟘  ≤𝟙 𝟘  ≤ω ≤ω → refl
    𝟘  ≤𝟙 𝟙  𝟘  𝟘  → refl
    𝟘  ≤𝟙 𝟙  𝟘  𝟙  → refl
    𝟘  ≤𝟙 𝟙  𝟘  ≤𝟙 → refl
    𝟘  ≤𝟙 𝟙  𝟘  ≤ω → refl
    𝟘  ≤𝟙 𝟙  𝟙  𝟘  → refl
    𝟘  ≤𝟙 𝟙  𝟙  𝟙  → refl
    𝟘  ≤𝟙 𝟙  𝟙  ≤𝟙 → refl
    𝟘  ≤𝟙 𝟙  𝟙  ≤ω → refl
    𝟘  ≤𝟙 𝟙  ≤𝟙 𝟘  → refl
    𝟘  ≤𝟙 𝟙  ≤𝟙 𝟙  → refl
    𝟘  ≤𝟙 𝟙  ≤𝟙 ≤𝟙 → refl
    𝟘  ≤𝟙 𝟙  ≤𝟙 ≤ω → refl
    𝟘  ≤𝟙 𝟙  ≤ω 𝟘  → refl
    𝟘  ≤𝟙 𝟙  ≤ω 𝟙  → refl
    𝟘  ≤𝟙 𝟙  ≤ω ≤𝟙 → refl
    𝟘  ≤𝟙 𝟙  ≤ω ≤ω → refl
    𝟘  ≤𝟙 ≤𝟙 𝟘  𝟘  → refl
    𝟘  ≤𝟙 ≤𝟙 𝟘  𝟙  → refl
    𝟘  ≤𝟙 ≤𝟙 𝟘  ≤𝟙 → refl
    𝟘  ≤𝟙 ≤𝟙 𝟘  ≤ω → refl
    𝟘  ≤𝟙 ≤𝟙 𝟙  𝟘  → refl
    𝟘  ≤𝟙 ≤𝟙 𝟙  𝟙  → refl
    𝟘  ≤𝟙 ≤𝟙 𝟙  ≤𝟙 → refl
    𝟘  ≤𝟙 ≤𝟙 𝟙  ≤ω → refl
    𝟘  ≤𝟙 ≤𝟙 ≤𝟙 𝟘  → refl
    𝟘  ≤𝟙 ≤𝟙 ≤𝟙 𝟙  → refl
    𝟘  ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟘  ≤𝟙 ≤𝟙 ≤𝟙 ≤ω → refl
    𝟘  ≤𝟙 ≤𝟙 ≤ω 𝟘  → refl
    𝟘  ≤𝟙 ≤𝟙 ≤ω 𝟙  → refl
    𝟘  ≤𝟙 ≤𝟙 ≤ω ≤𝟙 → refl
    𝟘  ≤𝟙 ≤𝟙 ≤ω ≤ω → refl
    𝟘  ≤𝟙 ≤ω 𝟘  𝟘  → refl
    𝟘  ≤𝟙 ≤ω 𝟘  𝟙  → refl
    𝟘  ≤𝟙 ≤ω 𝟘  ≤𝟙 → refl
    𝟘  ≤𝟙 ≤ω 𝟘  ≤ω → refl
    𝟘  ≤𝟙 ≤ω 𝟙  𝟘  → refl
    𝟘  ≤𝟙 ≤ω 𝟙  𝟙  → refl
    𝟘  ≤𝟙 ≤ω 𝟙  ≤𝟙 → refl
    𝟘  ≤𝟙 ≤ω 𝟙  ≤ω → refl
    𝟘  ≤𝟙 ≤ω ≤𝟙 𝟘  → refl
    𝟘  ≤𝟙 ≤ω ≤𝟙 𝟙  → refl
    𝟘  ≤𝟙 ≤ω ≤𝟙 ≤𝟙 → refl
    𝟘  ≤𝟙 ≤ω ≤𝟙 ≤ω → refl
    𝟘  ≤𝟙 ≤ω ≤ω 𝟘  → refl
    𝟘  ≤𝟙 ≤ω ≤ω 𝟙  → refl
    𝟘  ≤𝟙 ≤ω ≤ω ≤𝟙 → refl
    𝟘  ≤𝟙 ≤ω ≤ω ≤ω → refl
    𝟘  ≤ω 𝟘  𝟘  𝟘  → refl
    𝟘  ≤ω 𝟘  𝟘  𝟙  → refl
    𝟘  ≤ω 𝟘  𝟘  ≤𝟙 → refl
    𝟘  ≤ω 𝟘  𝟘  ≤ω → refl
    𝟘  ≤ω 𝟘  𝟙  𝟘  → refl
    𝟘  ≤ω 𝟘  𝟙  𝟙  → refl
    𝟘  ≤ω 𝟘  𝟙  ≤𝟙 → refl
    𝟘  ≤ω 𝟘  𝟙  ≤ω → refl
    𝟘  ≤ω 𝟘  ≤𝟙 𝟘  → refl
    𝟘  ≤ω 𝟘  ≤𝟙 𝟙  → refl
    𝟘  ≤ω 𝟘  ≤𝟙 ≤𝟙 → refl
    𝟘  ≤ω 𝟘  ≤𝟙 ≤ω → refl
    𝟘  ≤ω 𝟘  ≤ω 𝟘  → refl
    𝟘  ≤ω 𝟘  ≤ω 𝟙  → refl
    𝟘  ≤ω 𝟘  ≤ω ≤𝟙 → refl
    𝟘  ≤ω 𝟘  ≤ω ≤ω → refl
    𝟘  ≤ω 𝟙  𝟘  𝟘  → refl
    𝟘  ≤ω 𝟙  𝟘  𝟙  → refl
    𝟘  ≤ω 𝟙  𝟘  ≤𝟙 → refl
    𝟘  ≤ω 𝟙  𝟘  ≤ω → refl
    𝟘  ≤ω 𝟙  𝟙  𝟘  → refl
    𝟘  ≤ω 𝟙  𝟙  𝟙  → refl
    𝟘  ≤ω 𝟙  𝟙  ≤𝟙 → refl
    𝟘  ≤ω 𝟙  𝟙  ≤ω → refl
    𝟘  ≤ω 𝟙  ≤𝟙 𝟘  → refl
    𝟘  ≤ω 𝟙  ≤𝟙 𝟙  → refl
    𝟘  ≤ω 𝟙  ≤𝟙 ≤𝟙 → refl
    𝟘  ≤ω 𝟙  ≤𝟙 ≤ω → refl
    𝟘  ≤ω 𝟙  ≤ω 𝟘  → refl
    𝟘  ≤ω 𝟙  ≤ω 𝟙  → refl
    𝟘  ≤ω 𝟙  ≤ω ≤𝟙 → refl
    𝟘  ≤ω 𝟙  ≤ω ≤ω → refl
    𝟘  ≤ω ≤𝟙 𝟘  𝟘  → refl
    𝟘  ≤ω ≤𝟙 𝟘  𝟙  → refl
    𝟘  ≤ω ≤𝟙 𝟘  ≤𝟙 → refl
    𝟘  ≤ω ≤𝟙 𝟘  ≤ω → refl
    𝟘  ≤ω ≤𝟙 𝟙  𝟘  → refl
    𝟘  ≤ω ≤𝟙 𝟙  𝟙  → refl
    𝟘  ≤ω ≤𝟙 𝟙  ≤𝟙 → refl
    𝟘  ≤ω ≤𝟙 𝟙  ≤ω → refl
    𝟘  ≤ω ≤𝟙 ≤𝟙 𝟘  → refl
    𝟘  ≤ω ≤𝟙 ≤𝟙 𝟙  → refl
    𝟘  ≤ω ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟘  ≤ω ≤𝟙 ≤𝟙 ≤ω → refl
    𝟘  ≤ω ≤𝟙 ≤ω 𝟘  → refl
    𝟘  ≤ω ≤𝟙 ≤ω 𝟙  → refl
    𝟘  ≤ω ≤𝟙 ≤ω ≤𝟙 → refl
    𝟘  ≤ω ≤𝟙 ≤ω ≤ω → refl
    𝟘  ≤ω ≤ω 𝟘  𝟘  → refl
    𝟘  ≤ω ≤ω 𝟘  𝟙  → refl
    𝟘  ≤ω ≤ω 𝟘  ≤𝟙 → refl
    𝟘  ≤ω ≤ω 𝟘  ≤ω → refl
    𝟘  ≤ω ≤ω 𝟙  𝟘  → refl
    𝟘  ≤ω ≤ω 𝟙  𝟙  → refl
    𝟘  ≤ω ≤ω 𝟙  ≤𝟙 → refl
    𝟘  ≤ω ≤ω 𝟙  ≤ω → refl
    𝟘  ≤ω ≤ω ≤𝟙 𝟘  → refl
    𝟘  ≤ω ≤ω ≤𝟙 𝟙  → refl
    𝟘  ≤ω ≤ω ≤𝟙 ≤𝟙 → refl
    𝟘  ≤ω ≤ω ≤𝟙 ≤ω → refl
    𝟘  ≤ω ≤ω ≤ω 𝟘  → refl
    𝟘  ≤ω ≤ω ≤ω 𝟙  → refl
    𝟘  ≤ω ≤ω ≤ω ≤𝟙 → refl
    𝟘  ≤ω ≤ω ≤ω ≤ω → refl
    𝟙  𝟘  𝟘  𝟘  𝟘  → refl
    𝟙  𝟘  𝟘  𝟘  𝟙  → refl
    𝟙  𝟘  𝟘  𝟘  ≤𝟙 → refl
    𝟙  𝟘  𝟘  𝟘  ≤ω → refl
    𝟙  𝟘  𝟘  𝟙  𝟘  → refl
    𝟙  𝟘  𝟘  𝟙  𝟙  → refl
    𝟙  𝟘  𝟘  𝟙  ≤𝟙 → refl
    𝟙  𝟘  𝟘  𝟙  ≤ω → refl
    𝟙  𝟘  𝟘  ≤𝟙 𝟘  → refl
    𝟙  𝟘  𝟘  ≤𝟙 𝟙  → refl
    𝟙  𝟘  𝟘  ≤𝟙 ≤𝟙 → refl
    𝟙  𝟘  𝟘  ≤𝟙 ≤ω → refl
    𝟙  𝟘  𝟘  ≤ω 𝟘  → refl
    𝟙  𝟘  𝟘  ≤ω 𝟙  → refl
    𝟙  𝟘  𝟘  ≤ω ≤𝟙 → refl
    𝟙  𝟘  𝟘  ≤ω ≤ω → refl
    𝟙  𝟘  𝟙  𝟘  𝟘  → refl
    𝟙  𝟘  𝟙  𝟘  𝟙  → refl
    𝟙  𝟘  𝟙  𝟘  ≤𝟙 → refl
    𝟙  𝟘  𝟙  𝟘  ≤ω → refl
    𝟙  𝟘  𝟙  𝟙  𝟘  → refl
    𝟙  𝟘  𝟙  𝟙  𝟙  → refl
    𝟙  𝟘  𝟙  𝟙  ≤𝟙 → refl
    𝟙  𝟘  𝟙  𝟙  ≤ω → refl
    𝟙  𝟘  𝟙  ≤𝟙 𝟘  → refl
    𝟙  𝟘  𝟙  ≤𝟙 𝟙  → refl
    𝟙  𝟘  𝟙  ≤𝟙 ≤𝟙 → refl
    𝟙  𝟘  𝟙  ≤𝟙 ≤ω → refl
    𝟙  𝟘  𝟙  ≤ω 𝟘  → refl
    𝟙  𝟘  𝟙  ≤ω 𝟙  → refl
    𝟙  𝟘  𝟙  ≤ω ≤𝟙 → refl
    𝟙  𝟘  𝟙  ≤ω ≤ω → refl
    𝟙  𝟘  ≤𝟙 𝟘  𝟘  → refl
    𝟙  𝟘  ≤𝟙 𝟘  𝟙  → refl
    𝟙  𝟘  ≤𝟙 𝟘  ≤𝟙 → refl
    𝟙  𝟘  ≤𝟙 𝟘  ≤ω → refl
    𝟙  𝟘  ≤𝟙 𝟙  𝟘  → refl
    𝟙  𝟘  ≤𝟙 𝟙  𝟙  → refl
    𝟙  𝟘  ≤𝟙 𝟙  ≤𝟙 → refl
    𝟙  𝟘  ≤𝟙 𝟙  ≤ω → refl
    𝟙  𝟘  ≤𝟙 ≤𝟙 𝟘  → refl
    𝟙  𝟘  ≤𝟙 ≤𝟙 𝟙  → refl
    𝟙  𝟘  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟙  𝟘  ≤𝟙 ≤𝟙 ≤ω → refl
    𝟙  𝟘  ≤𝟙 ≤ω 𝟘  → refl
    𝟙  𝟘  ≤𝟙 ≤ω 𝟙  → refl
    𝟙  𝟘  ≤𝟙 ≤ω ≤𝟙 → refl
    𝟙  𝟘  ≤𝟙 ≤ω ≤ω → refl
    𝟙  𝟘  ≤ω 𝟘  𝟘  → refl
    𝟙  𝟘  ≤ω 𝟘  𝟙  → refl
    𝟙  𝟘  ≤ω 𝟘  ≤𝟙 → refl
    𝟙  𝟘  ≤ω 𝟘  ≤ω → refl
    𝟙  𝟘  ≤ω 𝟙  𝟘  → refl
    𝟙  𝟘  ≤ω 𝟙  𝟙  → refl
    𝟙  𝟘  ≤ω 𝟙  ≤𝟙 → refl
    𝟙  𝟘  ≤ω 𝟙  ≤ω → refl
    𝟙  𝟘  ≤ω ≤𝟙 𝟘  → refl
    𝟙  𝟘  ≤ω ≤𝟙 𝟙  → refl
    𝟙  𝟘  ≤ω ≤𝟙 ≤𝟙 → refl
    𝟙  𝟘  ≤ω ≤𝟙 ≤ω → refl
    𝟙  𝟘  ≤ω ≤ω 𝟘  → refl
    𝟙  𝟘  ≤ω ≤ω 𝟙  → refl
    𝟙  𝟘  ≤ω ≤ω ≤𝟙 → refl
    𝟙  𝟘  ≤ω ≤ω ≤ω → refl
    𝟙  𝟙  𝟘  𝟘  𝟘  → refl
    𝟙  𝟙  𝟘  𝟘  𝟙  → refl
    𝟙  𝟙  𝟘  𝟘  ≤𝟙 → refl
    𝟙  𝟙  𝟘  𝟘  ≤ω → refl
    𝟙  𝟙  𝟘  𝟙  𝟘  → refl
    𝟙  𝟙  𝟘  𝟙  𝟙  → refl
    𝟙  𝟙  𝟘  𝟙  ≤𝟙 → refl
    𝟙  𝟙  𝟘  𝟙  ≤ω → refl
    𝟙  𝟙  𝟘  ≤𝟙 𝟘  → refl
    𝟙  𝟙  𝟘  ≤𝟙 𝟙  → refl
    𝟙  𝟙  𝟘  ≤𝟙 ≤𝟙 → refl
    𝟙  𝟙  𝟘  ≤𝟙 ≤ω → refl
    𝟙  𝟙  𝟘  ≤ω 𝟘  → refl
    𝟙  𝟙  𝟘  ≤ω 𝟙  → refl
    𝟙  𝟙  𝟘  ≤ω ≤𝟙 → refl
    𝟙  𝟙  𝟘  ≤ω ≤ω → refl
    𝟙  𝟙  𝟙  𝟘  𝟘  → refl
    𝟙  𝟙  𝟙  𝟘  𝟙  → refl
    𝟙  𝟙  𝟙  𝟘  ≤𝟙 → refl
    𝟙  𝟙  𝟙  𝟘  ≤ω → refl
    𝟙  𝟙  𝟙  𝟙  𝟘  → refl
    𝟙  𝟙  𝟙  𝟙  𝟙  → refl
    𝟙  𝟙  𝟙  𝟙  ≤𝟙 → refl
    𝟙  𝟙  𝟙  𝟙  ≤ω → refl
    𝟙  𝟙  𝟙  ≤𝟙 𝟘  → refl
    𝟙  𝟙  𝟙  ≤𝟙 𝟙  → refl
    𝟙  𝟙  𝟙  ≤𝟙 ≤𝟙 → refl
    𝟙  𝟙  𝟙  ≤𝟙 ≤ω → refl
    𝟙  𝟙  𝟙  ≤ω 𝟘  → refl
    𝟙  𝟙  𝟙  ≤ω 𝟙  → refl
    𝟙  𝟙  𝟙  ≤ω ≤𝟙 → refl
    𝟙  𝟙  𝟙  ≤ω ≤ω → refl
    𝟙  𝟙  ≤𝟙 𝟘  𝟘  → refl
    𝟙  𝟙  ≤𝟙 𝟘  𝟙  → refl
    𝟙  𝟙  ≤𝟙 𝟘  ≤𝟙 → refl
    𝟙  𝟙  ≤𝟙 𝟘  ≤ω → refl
    𝟙  𝟙  ≤𝟙 𝟙  𝟘  → refl
    𝟙  𝟙  ≤𝟙 𝟙  𝟙  → refl
    𝟙  𝟙  ≤𝟙 𝟙  ≤𝟙 → refl
    𝟙  𝟙  ≤𝟙 𝟙  ≤ω → refl
    𝟙  𝟙  ≤𝟙 ≤𝟙 𝟘  → refl
    𝟙  𝟙  ≤𝟙 ≤𝟙 𝟙  → refl
    𝟙  𝟙  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟙  𝟙  ≤𝟙 ≤𝟙 ≤ω → refl
    𝟙  𝟙  ≤𝟙 ≤ω 𝟘  → refl
    𝟙  𝟙  ≤𝟙 ≤ω 𝟙  → refl
    𝟙  𝟙  ≤𝟙 ≤ω ≤𝟙 → refl
    𝟙  𝟙  ≤𝟙 ≤ω ≤ω → refl
    𝟙  𝟙  ≤ω 𝟘  𝟘  → refl
    𝟙  𝟙  ≤ω 𝟘  𝟙  → refl
    𝟙  𝟙  ≤ω 𝟘  ≤𝟙 → refl
    𝟙  𝟙  ≤ω 𝟘  ≤ω → refl
    𝟙  𝟙  ≤ω 𝟙  𝟘  → refl
    𝟙  𝟙  ≤ω 𝟙  𝟙  → refl
    𝟙  𝟙  ≤ω 𝟙  ≤𝟙 → refl
    𝟙  𝟙  ≤ω 𝟙  ≤ω → refl
    𝟙  𝟙  ≤ω ≤𝟙 𝟘  → refl
    𝟙  𝟙  ≤ω ≤𝟙 𝟙  → refl
    𝟙  𝟙  ≤ω ≤𝟙 ≤𝟙 → refl
    𝟙  𝟙  ≤ω ≤𝟙 ≤ω → refl
    𝟙  𝟙  ≤ω ≤ω 𝟘  → refl
    𝟙  𝟙  ≤ω ≤ω 𝟙  → refl
    𝟙  𝟙  ≤ω ≤ω ≤𝟙 → refl
    𝟙  𝟙  ≤ω ≤ω ≤ω → refl
    𝟙  ≤𝟙 𝟘  𝟘  𝟘  → refl
    𝟙  ≤𝟙 𝟘  𝟘  𝟙  → refl
    𝟙  ≤𝟙 𝟘  𝟘  ≤𝟙 → refl
    𝟙  ≤𝟙 𝟘  𝟘  ≤ω → refl
    𝟙  ≤𝟙 𝟘  𝟙  𝟘  → refl
    𝟙  ≤𝟙 𝟘  𝟙  𝟙  → refl
    𝟙  ≤𝟙 𝟘  𝟙  ≤𝟙 → refl
    𝟙  ≤𝟙 𝟘  𝟙  ≤ω → refl
    𝟙  ≤𝟙 𝟘  ≤𝟙 𝟘  → refl
    𝟙  ≤𝟙 𝟘  ≤𝟙 𝟙  → refl
    𝟙  ≤𝟙 𝟘  ≤𝟙 ≤𝟙 → refl
    𝟙  ≤𝟙 𝟘  ≤𝟙 ≤ω → refl
    𝟙  ≤𝟙 𝟘  ≤ω 𝟘  → refl
    𝟙  ≤𝟙 𝟘  ≤ω 𝟙  → refl
    𝟙  ≤𝟙 𝟘  ≤ω ≤𝟙 → refl
    𝟙  ≤𝟙 𝟘  ≤ω ≤ω → refl
    𝟙  ≤𝟙 𝟙  𝟘  𝟘  → refl
    𝟙  ≤𝟙 𝟙  𝟘  𝟙  → refl
    𝟙  ≤𝟙 𝟙  𝟘  ≤𝟙 → refl
    𝟙  ≤𝟙 𝟙  𝟘  ≤ω → refl
    𝟙  ≤𝟙 𝟙  𝟙  𝟘  → refl
    𝟙  ≤𝟙 𝟙  𝟙  𝟙  → refl
    𝟙  ≤𝟙 𝟙  𝟙  ≤𝟙 → refl
    𝟙  ≤𝟙 𝟙  𝟙  ≤ω → refl
    𝟙  ≤𝟙 𝟙  ≤𝟙 𝟘  → refl
    𝟙  ≤𝟙 𝟙  ≤𝟙 𝟙  → refl
    𝟙  ≤𝟙 𝟙  ≤𝟙 ≤𝟙 → refl
    𝟙  ≤𝟙 𝟙  ≤𝟙 ≤ω → refl
    𝟙  ≤𝟙 𝟙  ≤ω 𝟘  → refl
    𝟙  ≤𝟙 𝟙  ≤ω 𝟙  → refl
    𝟙  ≤𝟙 𝟙  ≤ω ≤𝟙 → refl
    𝟙  ≤𝟙 𝟙  ≤ω ≤ω → refl
    𝟙  ≤𝟙 ≤𝟙 𝟘  𝟘  → refl
    𝟙  ≤𝟙 ≤𝟙 𝟘  𝟙  → refl
    𝟙  ≤𝟙 ≤𝟙 𝟘  ≤𝟙 → refl
    𝟙  ≤𝟙 ≤𝟙 𝟘  ≤ω → refl
    𝟙  ≤𝟙 ≤𝟙 𝟙  𝟘  → refl
    𝟙  ≤𝟙 ≤𝟙 𝟙  𝟙  → refl
    𝟙  ≤𝟙 ≤𝟙 𝟙  ≤𝟙 → refl
    𝟙  ≤𝟙 ≤𝟙 𝟙  ≤ω → refl
    𝟙  ≤𝟙 ≤𝟙 ≤𝟙 𝟘  → refl
    𝟙  ≤𝟙 ≤𝟙 ≤𝟙 𝟙  → refl
    𝟙  ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟙  ≤𝟙 ≤𝟙 ≤𝟙 ≤ω → refl
    𝟙  ≤𝟙 ≤𝟙 ≤ω 𝟘  → refl
    𝟙  ≤𝟙 ≤𝟙 ≤ω 𝟙  → refl
    𝟙  ≤𝟙 ≤𝟙 ≤ω ≤𝟙 → refl
    𝟙  ≤𝟙 ≤𝟙 ≤ω ≤ω → refl
    𝟙  ≤𝟙 ≤ω 𝟘  𝟘  → refl
    𝟙  ≤𝟙 ≤ω 𝟘  𝟙  → refl
    𝟙  ≤𝟙 ≤ω 𝟘  ≤𝟙 → refl
    𝟙  ≤𝟙 ≤ω 𝟘  ≤ω → refl
    𝟙  ≤𝟙 ≤ω 𝟙  𝟘  → refl
    𝟙  ≤𝟙 ≤ω 𝟙  𝟙  → refl
    𝟙  ≤𝟙 ≤ω 𝟙  ≤𝟙 → refl
    𝟙  ≤𝟙 ≤ω 𝟙  ≤ω → refl
    𝟙  ≤𝟙 ≤ω ≤𝟙 𝟘  → refl
    𝟙  ≤𝟙 ≤ω ≤𝟙 𝟙  → refl
    𝟙  ≤𝟙 ≤ω ≤𝟙 ≤𝟙 → refl
    𝟙  ≤𝟙 ≤ω ≤𝟙 ≤ω → refl
    𝟙  ≤𝟙 ≤ω ≤ω 𝟘  → refl
    𝟙  ≤𝟙 ≤ω ≤ω 𝟙  → refl
    𝟙  ≤𝟙 ≤ω ≤ω ≤𝟙 → refl
    𝟙  ≤𝟙 ≤ω ≤ω ≤ω → refl
    𝟙  ≤ω 𝟘  𝟘  𝟘  → refl
    𝟙  ≤ω 𝟘  𝟘  𝟙  → refl
    𝟙  ≤ω 𝟘  𝟘  ≤𝟙 → refl
    𝟙  ≤ω 𝟘  𝟘  ≤ω → refl
    𝟙  ≤ω 𝟘  𝟙  𝟘  → refl
    𝟙  ≤ω 𝟘  𝟙  𝟙  → refl
    𝟙  ≤ω 𝟘  𝟙  ≤𝟙 → refl
    𝟙  ≤ω 𝟘  𝟙  ≤ω → refl
    𝟙  ≤ω 𝟘  ≤𝟙 𝟘  → refl
    𝟙  ≤ω 𝟘  ≤𝟙 𝟙  → refl
    𝟙  ≤ω 𝟘  ≤𝟙 ≤𝟙 → refl
    𝟙  ≤ω 𝟘  ≤𝟙 ≤ω → refl
    𝟙  ≤ω 𝟘  ≤ω 𝟘  → refl
    𝟙  ≤ω 𝟘  ≤ω 𝟙  → refl
    𝟙  ≤ω 𝟘  ≤ω ≤𝟙 → refl
    𝟙  ≤ω 𝟘  ≤ω ≤ω → refl
    𝟙  ≤ω 𝟙  𝟘  𝟘  → refl
    𝟙  ≤ω 𝟙  𝟘  𝟙  → refl
    𝟙  ≤ω 𝟙  𝟘  ≤𝟙 → refl
    𝟙  ≤ω 𝟙  𝟘  ≤ω → refl
    𝟙  ≤ω 𝟙  𝟙  𝟘  → refl
    𝟙  ≤ω 𝟙  𝟙  𝟙  → refl
    𝟙  ≤ω 𝟙  𝟙  ≤𝟙 → refl
    𝟙  ≤ω 𝟙  𝟙  ≤ω → refl
    𝟙  ≤ω 𝟙  ≤𝟙 𝟘  → refl
    𝟙  ≤ω 𝟙  ≤𝟙 𝟙  → refl
    𝟙  ≤ω 𝟙  ≤𝟙 ≤𝟙 → refl
    𝟙  ≤ω 𝟙  ≤𝟙 ≤ω → refl
    𝟙  ≤ω 𝟙  ≤ω 𝟘  → refl
    𝟙  ≤ω 𝟙  ≤ω 𝟙  → refl
    𝟙  ≤ω 𝟙  ≤ω ≤𝟙 → refl
    𝟙  ≤ω 𝟙  ≤ω ≤ω → refl
    𝟙  ≤ω ≤𝟙 𝟘  𝟘  → refl
    𝟙  ≤ω ≤𝟙 𝟘  𝟙  → refl
    𝟙  ≤ω ≤𝟙 𝟘  ≤𝟙 → refl
    𝟙  ≤ω ≤𝟙 𝟘  ≤ω → refl
    𝟙  ≤ω ≤𝟙 𝟙  𝟘  → refl
    𝟙  ≤ω ≤𝟙 𝟙  𝟙  → refl
    𝟙  ≤ω ≤𝟙 𝟙  ≤𝟙 → refl
    𝟙  ≤ω ≤𝟙 𝟙  ≤ω → refl
    𝟙  ≤ω ≤𝟙 ≤𝟙 𝟘  → refl
    𝟙  ≤ω ≤𝟙 ≤𝟙 𝟙  → refl
    𝟙  ≤ω ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟙  ≤ω ≤𝟙 ≤𝟙 ≤ω → refl
    𝟙  ≤ω ≤𝟙 ≤ω 𝟘  → refl
    𝟙  ≤ω ≤𝟙 ≤ω 𝟙  → refl
    𝟙  ≤ω ≤𝟙 ≤ω ≤𝟙 → refl
    𝟙  ≤ω ≤𝟙 ≤ω ≤ω → refl
    𝟙  ≤ω ≤ω 𝟘  𝟘  → refl
    𝟙  ≤ω ≤ω 𝟘  𝟙  → refl
    𝟙  ≤ω ≤ω 𝟘  ≤𝟙 → refl
    𝟙  ≤ω ≤ω 𝟘  ≤ω → refl
    𝟙  ≤ω ≤ω 𝟙  𝟘  → refl
    𝟙  ≤ω ≤ω 𝟙  𝟙  → refl
    𝟙  ≤ω ≤ω 𝟙  ≤𝟙 → refl
    𝟙  ≤ω ≤ω 𝟙  ≤ω → refl
    𝟙  ≤ω ≤ω ≤𝟙 𝟘  → refl
    𝟙  ≤ω ≤ω ≤𝟙 𝟙  → refl
    𝟙  ≤ω ≤ω ≤𝟙 ≤𝟙 → refl
    𝟙  ≤ω ≤ω ≤𝟙 ≤ω → refl
    𝟙  ≤ω ≤ω ≤ω 𝟘  → refl
    𝟙  ≤ω ≤ω ≤ω 𝟙  → refl
    𝟙  ≤ω ≤ω ≤ω ≤𝟙 → refl
    𝟙  ≤ω ≤ω ≤ω ≤ω → refl
    ≤𝟙 𝟘  𝟘  𝟘  𝟘  → refl
    ≤𝟙 𝟘  𝟘  𝟘  𝟙  → refl
    ≤𝟙 𝟘  𝟘  𝟘  ≤𝟙 → refl
    ≤𝟙 𝟘  𝟘  𝟘  ≤ω → refl
    ≤𝟙 𝟘  𝟘  𝟙  𝟘  → refl
    ≤𝟙 𝟘  𝟘  𝟙  𝟙  → refl
    ≤𝟙 𝟘  𝟘  𝟙  ≤𝟙 → refl
    ≤𝟙 𝟘  𝟘  𝟙  ≤ω → refl
    ≤𝟙 𝟘  𝟘  ≤𝟙 𝟘  → refl
    ≤𝟙 𝟘  𝟘  ≤𝟙 𝟙  → refl
    ≤𝟙 𝟘  𝟘  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟘  𝟘  ≤𝟙 ≤ω → refl
    ≤𝟙 𝟘  𝟘  ≤ω 𝟘  → refl
    ≤𝟙 𝟘  𝟘  ≤ω 𝟙  → refl
    ≤𝟙 𝟘  𝟘  ≤ω ≤𝟙 → refl
    ≤𝟙 𝟘  𝟘  ≤ω ≤ω → refl
    ≤𝟙 𝟘  𝟙  𝟘  𝟘  → refl
    ≤𝟙 𝟘  𝟙  𝟘  𝟙  → refl
    ≤𝟙 𝟘  𝟙  𝟘  ≤𝟙 → refl
    ≤𝟙 𝟘  𝟙  𝟘  ≤ω → refl
    ≤𝟙 𝟘  𝟙  𝟙  𝟘  → refl
    ≤𝟙 𝟘  𝟙  𝟙  𝟙  → refl
    ≤𝟙 𝟘  𝟙  𝟙  ≤𝟙 → refl
    ≤𝟙 𝟘  𝟙  𝟙  ≤ω → refl
    ≤𝟙 𝟘  𝟙  ≤𝟙 𝟘  → refl
    ≤𝟙 𝟘  𝟙  ≤𝟙 𝟙  → refl
    ≤𝟙 𝟘  𝟙  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟘  𝟙  ≤𝟙 ≤ω → refl
    ≤𝟙 𝟘  𝟙  ≤ω 𝟘  → refl
    ≤𝟙 𝟘  𝟙  ≤ω 𝟙  → refl
    ≤𝟙 𝟘  𝟙  ≤ω ≤𝟙 → refl
    ≤𝟙 𝟘  𝟙  ≤ω ≤ω → refl
    ≤𝟙 𝟘  ≤𝟙 𝟘  𝟘  → refl
    ≤𝟙 𝟘  ≤𝟙 𝟘  𝟙  → refl
    ≤𝟙 𝟘  ≤𝟙 𝟘  ≤𝟙 → refl
    ≤𝟙 𝟘  ≤𝟙 𝟘  ≤ω → refl
    ≤𝟙 𝟘  ≤𝟙 𝟙  𝟘  → refl
    ≤𝟙 𝟘  ≤𝟙 𝟙  𝟙  → refl
    ≤𝟙 𝟘  ≤𝟙 𝟙  ≤𝟙 → refl
    ≤𝟙 𝟘  ≤𝟙 𝟙  ≤ω → refl
    ≤𝟙 𝟘  ≤𝟙 ≤𝟙 𝟘  → refl
    ≤𝟙 𝟘  ≤𝟙 ≤𝟙 𝟙  → refl
    ≤𝟙 𝟘  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟘  ≤𝟙 ≤𝟙 ≤ω → refl
    ≤𝟙 𝟘  ≤𝟙 ≤ω 𝟘  → refl
    ≤𝟙 𝟘  ≤𝟙 ≤ω 𝟙  → refl
    ≤𝟙 𝟘  ≤𝟙 ≤ω ≤𝟙 → refl
    ≤𝟙 𝟘  ≤𝟙 ≤ω ≤ω → refl
    ≤𝟙 𝟘  ≤ω 𝟘  𝟘  → refl
    ≤𝟙 𝟘  ≤ω 𝟘  𝟙  → refl
    ≤𝟙 𝟘  ≤ω 𝟘  ≤𝟙 → refl
    ≤𝟙 𝟘  ≤ω 𝟘  ≤ω → refl
    ≤𝟙 𝟘  ≤ω 𝟙  𝟘  → refl
    ≤𝟙 𝟘  ≤ω 𝟙  𝟙  → refl
    ≤𝟙 𝟘  ≤ω 𝟙  ≤𝟙 → refl
    ≤𝟙 𝟘  ≤ω 𝟙  ≤ω → refl
    ≤𝟙 𝟘  ≤ω ≤𝟙 𝟘  → refl
    ≤𝟙 𝟘  ≤ω ≤𝟙 𝟙  → refl
    ≤𝟙 𝟘  ≤ω ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟘  ≤ω ≤𝟙 ≤ω → refl
    ≤𝟙 𝟘  ≤ω ≤ω 𝟘  → refl
    ≤𝟙 𝟘  ≤ω ≤ω 𝟙  → refl
    ≤𝟙 𝟘  ≤ω ≤ω ≤𝟙 → refl
    ≤𝟙 𝟘  ≤ω ≤ω ≤ω → refl
    ≤𝟙 𝟙  𝟘  𝟘  𝟘  → refl
    ≤𝟙 𝟙  𝟘  𝟘  𝟙  → refl
    ≤𝟙 𝟙  𝟘  𝟘  ≤𝟙 → refl
    ≤𝟙 𝟙  𝟘  𝟘  ≤ω → refl
    ≤𝟙 𝟙  𝟘  𝟙  𝟘  → refl
    ≤𝟙 𝟙  𝟘  𝟙  𝟙  → refl
    ≤𝟙 𝟙  𝟘  𝟙  ≤𝟙 → refl
    ≤𝟙 𝟙  𝟘  𝟙  ≤ω → refl
    ≤𝟙 𝟙  𝟘  ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  𝟘  ≤𝟙 𝟙  → refl
    ≤𝟙 𝟙  𝟘  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟙  𝟘  ≤𝟙 ≤ω → refl
    ≤𝟙 𝟙  𝟘  ≤ω 𝟘  → refl
    ≤𝟙 𝟙  𝟘  ≤ω 𝟙  → refl
    ≤𝟙 𝟙  𝟘  ≤ω ≤𝟙 → refl
    ≤𝟙 𝟙  𝟘  ≤ω ≤ω → refl
    ≤𝟙 𝟙  𝟙  𝟘  𝟘  → refl
    ≤𝟙 𝟙  𝟙  𝟘  𝟙  → refl
    ≤𝟙 𝟙  𝟙  𝟘  ≤𝟙 → refl
    ≤𝟙 𝟙  𝟙  𝟘  ≤ω → refl
    ≤𝟙 𝟙  𝟙  𝟙  𝟘  → refl
    ≤𝟙 𝟙  𝟙  𝟙  𝟙  → refl
    ≤𝟙 𝟙  𝟙  𝟙  ≤𝟙 → refl
    ≤𝟙 𝟙  𝟙  𝟙  ≤ω → refl
    ≤𝟙 𝟙  𝟙  ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  𝟙  ≤𝟙 𝟙  → refl
    ≤𝟙 𝟙  𝟙  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟙  𝟙  ≤𝟙 ≤ω → refl
    ≤𝟙 𝟙  𝟙  ≤ω 𝟘  → refl
    ≤𝟙 𝟙  𝟙  ≤ω 𝟙  → refl
    ≤𝟙 𝟙  𝟙  ≤ω ≤𝟙 → refl
    ≤𝟙 𝟙  𝟙  ≤ω ≤ω → refl
    ≤𝟙 𝟙  ≤𝟙 𝟘  𝟘  → refl
    ≤𝟙 𝟙  ≤𝟙 𝟘  𝟙  → refl
    ≤𝟙 𝟙  ≤𝟙 𝟘  ≤𝟙 → refl
    ≤𝟙 𝟙  ≤𝟙 𝟘  ≤ω → refl
    ≤𝟙 𝟙  ≤𝟙 𝟙  𝟘  → refl
    ≤𝟙 𝟙  ≤𝟙 𝟙  𝟙  → refl
    ≤𝟙 𝟙  ≤𝟙 𝟙  ≤𝟙 → refl
    ≤𝟙 𝟙  ≤𝟙 𝟙  ≤ω → refl
    ≤𝟙 𝟙  ≤𝟙 ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  ≤𝟙 ≤𝟙 𝟙  → refl
    ≤𝟙 𝟙  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟙  ≤𝟙 ≤𝟙 ≤ω → refl
    ≤𝟙 𝟙  ≤𝟙 ≤ω 𝟘  → refl
    ≤𝟙 𝟙  ≤𝟙 ≤ω 𝟙  → refl
    ≤𝟙 𝟙  ≤𝟙 ≤ω ≤𝟙 → refl
    ≤𝟙 𝟙  ≤𝟙 ≤ω ≤ω → refl
    ≤𝟙 𝟙  ≤ω 𝟘  𝟘  → refl
    ≤𝟙 𝟙  ≤ω 𝟘  𝟙  → refl
    ≤𝟙 𝟙  ≤ω 𝟘  ≤𝟙 → refl
    ≤𝟙 𝟙  ≤ω 𝟘  ≤ω → refl
    ≤𝟙 𝟙  ≤ω 𝟙  𝟘  → refl
    ≤𝟙 𝟙  ≤ω 𝟙  𝟙  → refl
    ≤𝟙 𝟙  ≤ω 𝟙  ≤𝟙 → refl
    ≤𝟙 𝟙  ≤ω 𝟙  ≤ω → refl
    ≤𝟙 𝟙  ≤ω ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  ≤ω ≤𝟙 𝟙  → refl
    ≤𝟙 𝟙  ≤ω ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟙  ≤ω ≤𝟙 ≤ω → refl
    ≤𝟙 𝟙  ≤ω ≤ω 𝟘  → refl
    ≤𝟙 𝟙  ≤ω ≤ω 𝟙  → refl
    ≤𝟙 𝟙  ≤ω ≤ω ≤𝟙 → refl
    ≤𝟙 𝟙  ≤ω ≤ω ≤ω → refl
    ≤𝟙 ≤𝟙 𝟘  𝟘  𝟘  → refl
    ≤𝟙 ≤𝟙 𝟘  𝟘  𝟙  → refl
    ≤𝟙 ≤𝟙 𝟘  𝟘  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟘  𝟘  ≤ω → refl
    ≤𝟙 ≤𝟙 𝟘  𝟙  𝟘  → refl
    ≤𝟙 ≤𝟙 𝟘  𝟙  𝟙  → refl
    ≤𝟙 ≤𝟙 𝟘  𝟙  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟘  𝟙  ≤ω → refl
    ≤𝟙 ≤𝟙 𝟘  ≤𝟙 𝟘  → refl
    ≤𝟙 ≤𝟙 𝟘  ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 𝟘  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟘  ≤𝟙 ≤ω → refl
    ≤𝟙 ≤𝟙 𝟘  ≤ω 𝟘  → refl
    ≤𝟙 ≤𝟙 𝟘  ≤ω 𝟙  → refl
    ≤𝟙 ≤𝟙 𝟘  ≤ω ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟘  ≤ω ≤ω → refl
    ≤𝟙 ≤𝟙 𝟙  𝟘  𝟘  → refl
    ≤𝟙 ≤𝟙 𝟙  𝟘  𝟙  → refl
    ≤𝟙 ≤𝟙 𝟙  𝟘  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟙  𝟘  ≤ω → refl
    ≤𝟙 ≤𝟙 𝟙  𝟙  𝟘  → refl
    ≤𝟙 ≤𝟙 𝟙  𝟙  𝟙  → refl
    ≤𝟙 ≤𝟙 𝟙  𝟙  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟙  𝟙  ≤ω → refl
    ≤𝟙 ≤𝟙 𝟙  ≤𝟙 𝟘  → refl
    ≤𝟙 ≤𝟙 𝟙  ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 𝟙  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟙  ≤𝟙 ≤ω → refl
    ≤𝟙 ≤𝟙 𝟙  ≤ω 𝟘  → refl
    ≤𝟙 ≤𝟙 𝟙  ≤ω 𝟙  → refl
    ≤𝟙 ≤𝟙 𝟙  ≤ω ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟙  ≤ω ≤ω → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟘  𝟘  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟘  𝟙  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟘  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟘  ≤ω → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟙  𝟘  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟙  𝟙  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟙  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟙  ≤ω → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 𝟘  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ≤ω → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤ω 𝟘  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤ω 𝟙  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤ω ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤ω ≤ω → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟘  𝟘  → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟘  𝟙  → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟘  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟘  ≤ω → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟙  𝟘  → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟙  𝟙  → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟙  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟙  ≤ω → refl
    ≤𝟙 ≤𝟙 ≤ω ≤𝟙 𝟘  → refl
    ≤𝟙 ≤𝟙 ≤ω ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 ≤ω ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤ω ≤𝟙 ≤ω → refl
    ≤𝟙 ≤𝟙 ≤ω ≤ω 𝟘  → refl
    ≤𝟙 ≤𝟙 ≤ω ≤ω 𝟙  → refl
    ≤𝟙 ≤𝟙 ≤ω ≤ω ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤ω ≤ω ≤ω → refl
    ≤𝟙 ≤ω 𝟘  𝟘  𝟘  → refl
    ≤𝟙 ≤ω 𝟘  𝟘  𝟙  → refl
    ≤𝟙 ≤ω 𝟘  𝟘  ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟘  𝟘  ≤ω → refl
    ≤𝟙 ≤ω 𝟘  𝟙  𝟘  → refl
    ≤𝟙 ≤ω 𝟘  𝟙  𝟙  → refl
    ≤𝟙 ≤ω 𝟘  𝟙  ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟘  𝟙  ≤ω → refl
    ≤𝟙 ≤ω 𝟘  ≤𝟙 𝟘  → refl
    ≤𝟙 ≤ω 𝟘  ≤𝟙 𝟙  → refl
    ≤𝟙 ≤ω 𝟘  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟘  ≤𝟙 ≤ω → refl
    ≤𝟙 ≤ω 𝟘  ≤ω 𝟘  → refl
    ≤𝟙 ≤ω 𝟘  ≤ω 𝟙  → refl
    ≤𝟙 ≤ω 𝟘  ≤ω ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟘  ≤ω ≤ω → refl
    ≤𝟙 ≤ω 𝟙  𝟘  𝟘  → refl
    ≤𝟙 ≤ω 𝟙  𝟘  𝟙  → refl
    ≤𝟙 ≤ω 𝟙  𝟘  ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟙  𝟘  ≤ω → refl
    ≤𝟙 ≤ω 𝟙  𝟙  𝟘  → refl
    ≤𝟙 ≤ω 𝟙  𝟙  𝟙  → refl
    ≤𝟙 ≤ω 𝟙  𝟙  ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟙  𝟙  ≤ω → refl
    ≤𝟙 ≤ω 𝟙  ≤𝟙 𝟘  → refl
    ≤𝟙 ≤ω 𝟙  ≤𝟙 𝟙  → refl
    ≤𝟙 ≤ω 𝟙  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟙  ≤𝟙 ≤ω → refl
    ≤𝟙 ≤ω 𝟙  ≤ω 𝟘  → refl
    ≤𝟙 ≤ω 𝟙  ≤ω 𝟙  → refl
    ≤𝟙 ≤ω 𝟙  ≤ω ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟙  ≤ω ≤ω → refl
    ≤𝟙 ≤ω ≤𝟙 𝟘  𝟘  → refl
    ≤𝟙 ≤ω ≤𝟙 𝟘  𝟙  → refl
    ≤𝟙 ≤ω ≤𝟙 𝟘  ≤𝟙 → refl
    ≤𝟙 ≤ω ≤𝟙 𝟘  ≤ω → refl
    ≤𝟙 ≤ω ≤𝟙 𝟙  𝟘  → refl
    ≤𝟙 ≤ω ≤𝟙 𝟙  𝟙  → refl
    ≤𝟙 ≤ω ≤𝟙 𝟙  ≤𝟙 → refl
    ≤𝟙 ≤ω ≤𝟙 𝟙  ≤ω → refl
    ≤𝟙 ≤ω ≤𝟙 ≤𝟙 𝟘  → refl
    ≤𝟙 ≤ω ≤𝟙 ≤𝟙 𝟙  → refl
    ≤𝟙 ≤ω ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω ≤𝟙 ≤𝟙 ≤ω → refl
    ≤𝟙 ≤ω ≤𝟙 ≤ω 𝟘  → refl
    ≤𝟙 ≤ω ≤𝟙 ≤ω 𝟙  → refl
    ≤𝟙 ≤ω ≤𝟙 ≤ω ≤𝟙 → refl
    ≤𝟙 ≤ω ≤𝟙 ≤ω ≤ω → refl
    ≤𝟙 ≤ω ≤ω 𝟘  𝟘  → refl
    ≤𝟙 ≤ω ≤ω 𝟘  𝟙  → refl
    ≤𝟙 ≤ω ≤ω 𝟘  ≤𝟙 → refl
    ≤𝟙 ≤ω ≤ω 𝟘  ≤ω → refl
    ≤𝟙 ≤ω ≤ω 𝟙  𝟘  → refl
    ≤𝟙 ≤ω ≤ω 𝟙  𝟙  → refl
    ≤𝟙 ≤ω ≤ω 𝟙  ≤𝟙 → refl
    ≤𝟙 ≤ω ≤ω 𝟙  ≤ω → refl
    ≤𝟙 ≤ω ≤ω ≤𝟙 𝟘  → refl
    ≤𝟙 ≤ω ≤ω ≤𝟙 𝟙  → refl
    ≤𝟙 ≤ω ≤ω ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω ≤ω ≤𝟙 ≤ω → refl
    ≤𝟙 ≤ω ≤ω ≤ω 𝟘  → refl
    ≤𝟙 ≤ω ≤ω ≤ω 𝟙  → refl
    ≤𝟙 ≤ω ≤ω ≤ω ≤𝟙 → refl
    ≤𝟙 ≤ω ≤ω ≤ω ≤ω → refl
    ≤ω 𝟘  𝟘  𝟘  𝟘  → refl
    ≤ω 𝟙  𝟘  𝟘  𝟘  → refl
    ≤ω ≤𝟙 𝟘  𝟘  𝟘  → refl
    ≤ω ≤ω 𝟘  𝟘  𝟘  → refl
    ≤ω _  𝟘  𝟘  𝟙  → refl
    ≤ω _  𝟘  𝟘  ≤𝟙 → refl
    ≤ω _  𝟘  𝟘  ≤ω → refl
    ≤ω _  𝟘  𝟙  𝟘  → refl
    ≤ω _  𝟘  𝟙  𝟙  → refl
    ≤ω _  𝟘  𝟙  ≤𝟙 → refl
    ≤ω _  𝟘  𝟙  ≤ω → refl
    ≤ω _  𝟘  ≤𝟙 𝟘  → refl
    ≤ω _  𝟘  ≤𝟙 𝟙  → refl
    ≤ω _  𝟘  ≤𝟙 ≤𝟙 → refl
    ≤ω _  𝟘  ≤𝟙 ≤ω → refl
    ≤ω _  𝟘  ≤ω 𝟘  → refl
    ≤ω _  𝟘  ≤ω 𝟙  → refl
    ≤ω _  𝟘  ≤ω ≤𝟙 → refl
    ≤ω _  𝟘  ≤ω ≤ω → refl
    ≤ω _  𝟙  𝟘  𝟘  → refl
    ≤ω _  𝟙  𝟘  𝟙  → refl
    ≤ω _  𝟙  𝟘  ≤𝟙 → refl
    ≤ω _  𝟙  𝟘  ≤ω → refl
    ≤ω _  𝟙  𝟙  𝟘  → refl
    ≤ω _  𝟙  𝟙  𝟙  → refl
    ≤ω _  𝟙  𝟙  ≤𝟙 → refl
    ≤ω _  𝟙  𝟙  ≤ω → refl
    ≤ω _  𝟙  ≤𝟙 𝟘  → refl
    ≤ω _  𝟙  ≤𝟙 𝟙  → refl
    ≤ω _  𝟙  ≤𝟙 ≤𝟙 → refl
    ≤ω _  𝟙  ≤𝟙 ≤ω → refl
    ≤ω _  𝟙  ≤ω 𝟘  → refl
    ≤ω _  𝟙  ≤ω 𝟙  → refl
    ≤ω _  𝟙  ≤ω ≤𝟙 → refl
    ≤ω _  𝟙  ≤ω ≤ω → refl
    ≤ω _  ≤𝟙 𝟘  𝟘  → refl
    ≤ω _  ≤𝟙 𝟘  𝟙  → refl
    ≤ω _  ≤𝟙 𝟘  ≤𝟙 → refl
    ≤ω _  ≤𝟙 𝟘  ≤ω → refl
    ≤ω _  ≤𝟙 𝟙  𝟘  → refl
    ≤ω _  ≤𝟙 𝟙  𝟙  → refl
    ≤ω _  ≤𝟙 𝟙  ≤𝟙 → refl
    ≤ω _  ≤𝟙 𝟙  ≤ω → refl
    ≤ω _  ≤𝟙 ≤𝟙 𝟘  → refl
    ≤ω _  ≤𝟙 ≤𝟙 𝟙  → refl
    ≤ω _  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤ω _  ≤𝟙 ≤𝟙 ≤ω → refl
    ≤ω _  ≤𝟙 ≤ω 𝟘  → refl
    ≤ω _  ≤𝟙 ≤ω 𝟙  → refl
    ≤ω _  ≤𝟙 ≤ω ≤𝟙 → refl
    ≤ω _  ≤𝟙 ≤ω ≤ω → refl
    ≤ω _  ≤ω 𝟘  𝟘  → refl
    ≤ω _  ≤ω 𝟘  𝟙  → refl
    ≤ω _  ≤ω 𝟘  ≤𝟙 → refl
    ≤ω _  ≤ω 𝟘  ≤ω → refl
    ≤ω _  ≤ω 𝟙  𝟘  → refl
    ≤ω _  ≤ω 𝟙  𝟙  → refl
    ≤ω _  ≤ω 𝟙  ≤𝟙 → refl
    ≤ω _  ≤ω 𝟙  ≤ω → refl
    ≤ω _  ≤ω ≤𝟙 𝟘  → refl
    ≤ω _  ≤ω ≤𝟙 𝟙  → refl
    ≤ω _  ≤ω ≤𝟙 ≤𝟙 → refl
    ≤ω _  ≤ω ≤𝟙 ≤ω → refl
    ≤ω _  ≤ω ≤ω 𝟘  → refl
    ≤ω _  ≤ω ≤ω 𝟙  → refl
    ≤ω _  ≤ω ≤ω ≤𝟙 → refl
    ≤ω _  ≤ω ≤ω ≤ω → refl

-- A modality defined using linear-or-affine-has-nr.

linear-or-affine : Modality-variant → Modality
linear-or-affine variant = record
  { variant            = variant
  ; semiring-with-meet = linear-or-affine-semiring-with-meet
  ; 𝟘-well-behaved     = λ _ → linear-or-affine-has-well-behaved-zero
  ; has-nr             = λ _ → linear-or-affine-has-nr
  }

------------------------------------------------------------------------
-- Instances of Full-reduction-assumptions

-- Instances of Type-restrictions and Usage-restrictions are suitable
-- for the full reduction theorem if
-- * whenever Unitˢ-allowed holds, then Starˢ-sink holds,
-- * Unitʷ-allowed and Unitʷ-η do not both hold,
-- * Σˢ-allowed 𝟘 p does not hold,
-- * Σˢ-allowed ≤𝟙 p does not hold, and
-- * Σˢ-allowed ≤ω p does not hold.

Suitable-for-full-reduction :
  ∀ variant →
  Type-restrictions (linear-or-affine variant) →
  Usage-restrictions (linear-or-affine variant) →
  Set
Suitable-for-full-reduction variant rs us =
  (Unitˢ-allowed → Starˢ-sink) ×
  (Unitʷ-allowed → ¬ Unitʷ-η) ×
  (∀ p → ¬ Σˢ-allowed 𝟘 p) ×
  (∀ p → ¬ Σˢ-allowed ≤𝟙 p) ×
  (∀ p → ¬ Σˢ-allowed ≤ω p)
  where
  open Type-restrictions  rs
  open Usage-restrictions us

-- Given an instance of Type-restrictions (linear-or-affine variant)
-- one can create a "suitable" instance.

suitable-for-full-reduction :
  Type-restrictions (linear-or-affine variant) →
  ∃ λ rs → Suitable-for-full-reduction variant rs urs
suitable-for-full-reduction {urs} rs =
    record rs
      { Unit-allowed = λ where
          𝕤 → Unitˢ-allowed × Starˢ-sink
          𝕨 → Unitʷ-allowed × ¬ Unitʷ-η
      ; ΠΣ-allowed   = λ b p q →
          ΠΣ-allowed b p q × (b ≡ BMΣ 𝕤 → p ≡ 𝟙)
      ; []-cong-allowed = λ where
          𝕤 → ⊥
          𝕨 → []-congʷ-allowed × ¬ Unitʷ-η
      ; []-cong→Erased = λ where
          {s = 𝕨} (ok , no-η) →
            case []-cong→Erased ok of λ
              (ok₁ , ok₂) →
            (ok₁ , no-η) , ok₂ , (λ ())
      ; []-cong→¬Trivial = λ where
          {s = 𝕨} → []-cong→¬Trivial ∘→ proj₁
      }
  , proj₂
  , proj₂
  , (λ _ → ((λ ()) ∘→ (_$ PE.refl)) ∘→ proj₂)
  , (λ _ → ((λ ()) ∘→ (_$ PE.refl)) ∘→ proj₂)
  , (λ _ → ((λ ()) ∘→ (_$ PE.refl)) ∘→ proj₂)
  where
  open Type-restrictions rs
  open Usage-restrictions urs

-- The full reduction assumptions hold for any instance of
-- linear-or-affine and any "suitable" Type-restrictions and
-- Usage-restrictions.

full-reduction-assumptions :
  Suitable-for-full-reduction variant trs urs →
  Full-reduction-assumptions trs urs
full-reduction-assumptions (sink , no-η , ¬𝟘 , ¬≤𝟙 , ¬≤ω) = record
  { sink⊎𝟙≤𝟘 = λ where
      {s = 𝕤} ok _         → inj₁ (refl , sink ok)
      {s = 𝕨} _  (inj₁ ())
      {s = 𝕨} ok (inj₂ η)  → ⊥-elim (no-η ok η)
  ; ≡𝟙⊎𝟙≤𝟘 = λ where
      {p = 𝟘}  ok → ⊥-elim (¬𝟘 _ ok)
      {p = ≤𝟙} ok → ⊥-elim (¬≤𝟙 _ ok)
      {p = ≤ω} ok → ⊥-elim (¬≤ω _ ok)
      {p = 𝟙}  _  → inj₁ refl
  }

-- Type and usage restrictions that satisfy the full reduction
-- assumptions are "suitable".

full-reduction-assumptions-suitable :
  Full-reduction-assumptions trs urs →
  Suitable-for-full-reduction variant trs urs
full-reduction-assumptions-suitable {urs = urs} as =
     (λ ok → case sink⊎𝟙≤𝟘 ok (inj₁ refl) of λ where
        (inj₁ (_ , sink)) → sink
        (inj₂ ()))
   , (λ ok η → case sink⊎𝟙≤𝟘 ok (inj₂ η) of λ where
        (inj₁ (() , _))
        (inj₂ ()))
   , (λ p Σ-ok → case ≡𝟙⊎𝟙≤𝟘 Σ-ok of λ where
        (inj₁ ())
        (inj₂ (_ , _ , ())))
   , (λ p Σ-ok → case ≡𝟙⊎𝟙≤𝟘 Σ-ok of λ where
        (inj₁ ())
        (inj₂ (() , _)))
   , λ p Σ-ok → case ≡𝟙⊎𝟙≤𝟘 Σ-ok of λ where
        (inj₁ ())
        (inj₂ (() , _))
  where
  open Full-reduction-assumptions as
  open Usage-restrictions urs
