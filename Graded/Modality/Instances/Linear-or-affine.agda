------------------------------------------------------------------------
-- A modality with simultaneous support for affine and linear types
------------------------------------------------------------------------

-- It might make sense to replace some of the proofs with automated
-- proofs.

module Graded.Modality.Instances.Linear-or-affine where

import Tools.Algebra
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat using (1+; Sequence)
open import Tools.Product
open import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

import Graded.Modality
open import Graded.FullReduction.Assumptions
import Graded.Modality.Properties.Addition as Addition
import Graded.Modality.Properties.Greatest-lower-bound as GLB
import Graded.Modality.Properties.Meet as Meet
import Graded.Modality.Properties.Multiplication as Multiplication
import Graded.Modality.Properties.Natrec as Natrec
import Graded.Modality.Properties.PartialOrder as PartialOrder
import Graded.Modality.Properties.Star as Star
import Graded.Modality.Properties.Subtraction as Subtraction
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

infixr 43 _∧_

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
𝟘-maximal {p = 𝟘}  refl = refl
𝟘-maximal {p = 𝟙}  ()
𝟘-maximal {p = ≤𝟙} ()
𝟘-maximal {p = ≤ω} ()

-- 𝟙 is maximal.

𝟙-maximal : 𝟙 ≤ p → p ≡ 𝟙
𝟙-maximal {p = 𝟙}  refl = refl
𝟙-maximal {p = 𝟘}  ()
𝟙-maximal {p = ≤𝟙} ()
𝟙-maximal {p = ≤ω} ()

opaque

  -- Non-zero values are bounded by 𝟙.

  ≢𝟘→≤𝟙 : p ≢ 𝟘 → p ≤ 𝟙
  ≢𝟘→≤𝟙 {(𝟘)} 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 refl)
  ≢𝟘→≤𝟙 {(𝟙)} _ = refl
  ≢𝟘→≤𝟙 {(≤𝟙)} _ = refl
  ≢𝟘→≤𝟙 {(≤ω)} _ = refl

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

opaque

  -- The sum of ≤ω and p is ≤ω

  ≤ω+ : ∀ p → ≤ω + p ≡ ≤ω
  ≤ω+ 𝟘 = refl
  ≤ω+ 𝟙 = refl
  ≤ω+ ≤𝟙 = refl
  ≤ω+ ≤ω = refl

-- If p + q is 𝟙, then either p is 𝟙 and q is 𝟘, or q is 𝟙 and p is 𝟘.

+≡𝟙 : p + q ≡ 𝟙 → p ≡ 𝟙 × q ≡ 𝟘 ⊎ p ≡ 𝟘 × q ≡ 𝟙
+≡𝟙 {p = 𝟘}  {q = 𝟙}  refl = inj₂ (refl , refl)
+≡𝟙 {p = 𝟙}  {q = 𝟘}  refl = inj₁ (refl , refl)
+≡𝟙 {p = 𝟘}  {q = ≤𝟙} ()
+≡𝟙 {p = 𝟘}  {q = ≤ω} ()
+≡𝟙 {p = 𝟘}  {q = 𝟘}  ()
+≡𝟙 {p = 𝟙}  {q = 𝟙}  ()
+≡𝟙 {p = 𝟙}  {q = ≤𝟙} ()
+≡𝟙 {p = 𝟙}  {q = ≤ω} ()
+≡𝟙 {p = ≤𝟙} {q = 𝟘}  ()
+≡𝟙 {p = ≤𝟙} {q = 𝟙}  ()
+≡𝟙 {p = ≤𝟙} {q = ≤𝟙} ()
+≡𝟙 {p = ≤𝟙} {q = ≤ω} ()
+≡𝟙 {p = ≤ω} {q = 𝟘}  ()
+≡𝟙 {p = ≤ω} {q = 𝟙}  ()
+≡𝟙 {p = ≤ω} {q = ≤𝟙} ()
+≡𝟙 {p = ≤ω} {q = ≤ω} ()

-- If p ∧ q is 𝟙, then p and q is 𝟙.

∧≡𝟙 : p ∧ q ≡ 𝟙 → p ≡ 𝟙 × q ≡ 𝟙
∧≡𝟙 {p = 𝟙}  {q = 𝟙}  _  = refl , refl
∧≡𝟙 {p = 𝟘}  {q = 𝟘}  ()
∧≡𝟙 {p = 𝟘}  {q = ≤𝟙} ()
∧≡𝟙 {p = 𝟘}  {q = ≤ω} ()
∧≡𝟙 {p = 𝟘}  {q = 𝟙}  ()
∧≡𝟙 {p = 𝟙}  {q = 𝟘}  ()
∧≡𝟙 {p = 𝟙}  {q = ≤𝟙} ()
∧≡𝟙 {p = 𝟙}  {q = ≤ω} ()
∧≡𝟙 {p = ≤𝟙} {q = 𝟘}  ()
∧≡𝟙 {p = ≤𝟙} {q = 𝟙}  ()
∧≡𝟙 {p = ≤𝟙} {q = ≤𝟙} ()
∧≡𝟙 {p = ≤𝟙} {q = ≤ω} ()
∧≡𝟙 {p = ≤ω}          ()

opaque

  -- 𝟙 ∧ p is not 𝟘

  𝟙∧p≢𝟘 : ∀ p → 𝟙 ∧ p ≢ 𝟘
  𝟙∧p≢𝟘 𝟘 ()
  𝟙∧p≢𝟘 𝟙 ()
  𝟙∧p≢𝟘 ≤𝟙 ()
  𝟙∧p≢𝟘 ≤ω ()

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

opaque

  -- If p is not 𝟘, then p · ≤ω is equal to ≤ω.

  ≢𝟘·≤ω : p ≢ 𝟘 → p · ≤ω ≡ ≤ω
  ≢𝟘·≤ω {p} p≢𝟘 = trans (·-comm p ≤ω) (≤ω·≢𝟘 p≢𝟘)

-- The value of ≤ω · p is not 𝟙.

≤ω·≢𝟙 : ∀ p → ≤ω · p ≢ 𝟙
≤ω·≢𝟙 𝟘  ()
≤ω·≢𝟙 𝟙  ()
≤ω·≢𝟙 ≤𝟙 ()
≤ω·≢𝟙 ≤ω ()

-- If p is not 𝟘, then 𝟙 · p is not 𝟘.

𝟙·≢𝟘 : p ≢ 𝟘 → 𝟙 · p ≢ 𝟘
𝟙·≢𝟘 {p = 𝟘}  𝟘≢𝟘 = 𝟘≢𝟘
𝟙·≢𝟘 {p = 𝟙}  _   = λ ()
𝟙·≢𝟘 {p = ≤𝟙} _   = λ ()
𝟙·≢𝟘 {p = ≤ω} _   = λ ()

-- If p is not 𝟘, then ≤𝟙 · p is not 𝟘.

≤𝟙·≢𝟘 : p ≢ 𝟘 → ≤𝟙 · p ≢ 𝟘
≤𝟙·≢𝟘 {p = 𝟘}  𝟘≢𝟘 = 𝟘≢𝟘
≤𝟙·≢𝟘 {p = 𝟙}  _   = λ ()
≤𝟙·≢𝟘 {p = ≤𝟙} _   = λ ()
≤𝟙·≢𝟘 {p = ≤ω} _   = λ ()

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

opaque

  -- The product of two non-zero values is non-zero

  ≢𝟘·≢𝟘 : p ≢ 𝟘 → q ≢ 𝟘 → p · q ≢ 𝟘
  ≢𝟘·≢𝟘 {p = 𝟘}           p≢𝟘 _   _  = p≢𝟘 refl
  ≢𝟘·≢𝟘 {p = 𝟙}  {q = 𝟘}  _   q≢𝟘 _  = q≢𝟘 refl
  ≢𝟘·≢𝟘 {p = ≤𝟙} {q = 𝟘}  _   q≢𝟘 _  = q≢𝟘 refl
  ≢𝟘·≢𝟘 {p = ≤ω} {q = 𝟘}  _   q≢𝟘 _  = q≢𝟘 refl
  ≢𝟘·≢𝟘 {p = 𝟙}  {q = 𝟙}  _   _   ()
  ≢𝟘·≢𝟘 {p = 𝟙}  {q = ≤𝟙} _   _   ()
  ≢𝟘·≢𝟘 {p = 𝟙}  {q = ≤ω} _   _   ()
  ≢𝟘·≢𝟘 {p = ≤𝟙} {q = 𝟙}  _   _   ()
  ≢𝟘·≢𝟘 {p = ≤𝟙} {q = ≤𝟙} _   _   ()
  ≢𝟘·≢𝟘 {p = ≤𝟙} {q = ≤ω} _   _   ()
  ≢𝟘·≢𝟘 {p = ≤ω} {q = 𝟙}  _   _   ()
  ≢𝟘·≢𝟘 {p = ≤ω} {q = ≤𝟙} _   _   ()
  ≢𝟘·≢𝟘 {p = ≤ω} {q = ≤ω} _   _   ()

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
        {p = 𝟘}           _  → inj₁ refl
        {q = 𝟘}           _  → inj₂ refl
        {p = 𝟙}  {q = 𝟙}  ()
        {p = 𝟙}  {q = ≤𝟙} ()
        {p = 𝟙}  {q = ≤ω} ()
        {p = ≤𝟙} {q = 𝟙}  ()
        {p = ≤𝟙} {q = ≤𝟙} ()
        {p = ≤𝟙} {q = ≤ω} ()
        {p = ≤ω} {q = 𝟙}  ()
        {p = ≤ω} {q = ≤𝟙} ()
        {p = ≤ω} {q = ≤ω} ()
    ; +-positiveˡ = λ where
        {p = 𝟘}  {q = 𝟘}  _  → refl
        {p = 𝟘}  {q = 𝟙}  _  → refl
        {p = 𝟘}  {q = ≤𝟙} ()
        {p = 𝟘}  {q = ≤ω} ()
        {p = 𝟙}  {q = 𝟘}  ()
        {p = 𝟙}  {q = 𝟙}  ()
        {p = 𝟙}  {q = ≤𝟙} ()
        {p = 𝟙}  {q = ≤ω} ()
        {p = ≤𝟙} {q = 𝟘}  ()
        {p = ≤𝟙} {q = 𝟙}  ()
        {p = ≤𝟙} {q = ≤𝟙} ()
        {p = ≤𝟙} {q = ≤ω} ()
        {p = ≤ω} {q = 𝟘}  ()
        {p = ≤ω} {q = 𝟙}  ()
        {p = ≤ω} {q = ≤𝟙} ()
        {p = ≤ω} {q = ≤ω} ()
    ; ∧-positiveˡ = λ where
        {p = 𝟘}  {q = 𝟘}  _  → refl
        {p = 𝟘}  {q = 𝟙}  _  → refl
        {p = 𝟘}  {q = ≤𝟙} ()
        {p = 𝟘}  {q = ≤ω} ()
        {p = 𝟙}  {q = 𝟘}  ()
        {p = 𝟙}  {q = 𝟙}  ()
        {p = 𝟙}  {q = ≤𝟙} ()
        {p = 𝟙}  {q = ≤ω} ()
        {p = ≤𝟙} {q = 𝟘}  ()
        {p = ≤𝟙} {q = 𝟙}  ()
        {p = ≤𝟙} {q = ≤𝟙} ()
        {p = ≤𝟙} {q = ≤ω} ()
        {p = ≤ω}          ()
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
  M@record{} refl refl refl refl refl star ⊛-ineq₁ ⊛-ineq₂
  ·-sub-distribʳ-⊛ =
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

-- A modality for Linear-or-affine.

linear-or-affine : Modality-variant → Modality
linear-or-affine variant = record
  { variant            = variant
  ; semiring-with-meet = linear-or-affine-semiring-with-meet
  ; 𝟘-well-behaved     = λ _ → linear-or-affine-has-well-behaved-zero
  }

------------------------------------------------------------------------
-- Custom nr functions for the Modality

opaque

  -- A (not very good) nr function based on the natrec-star operator
  -- defined above.

  -- See Graded.Modality.Instances.Linear-or-affine.Bad for some
  -- examples that illustrate in what sense this nr function is not very
  -- good. The nr function below does not suffer from
  -- these problems (see
  -- Graded.Modality.Instances.Linear-or-affine.Good).

  bad-linear-or-affine-has-nr : Has-nr linear-or-affine-semiring-with-meet
  bad-linear-or-affine-has-nr =
    Star.has-nr _ ⦃ linear-or-affine-has-star ⦄

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
    _  _  _  _  𝟙  ()

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

opaque

  -- The nr-function defined above is factoring

  linear-or-affine-has-factoring-nr :
    Is-factoring-nr linear-or-affine-has-nr
  linear-or-affine-has-factoring-nr = record
    { nr₂ = nr₂
    ; nr₂≢𝟘 = λ {p} {r} → 𝟙∧p≢𝟘 (r + p)
    ; nr-factoring = λ {p} {r} {z} {s} {n} → nr-factoring p r z s n
    }
    where
    open Semiring-with-meet linear-or-affine-semiring-with-meet
      hiding (𝟘; 𝟙; _+_; _·_; _∧_; _≤_)

    nr₂ : Op₂ Linear-or-affine
    nr₂ p r = 𝟙 ∧ (r + p)

    𝟙∧≤𝟙+p≡≤1+p : ∀ p → 𝟙 ∧ (≤𝟙 + p) ≡ ≤𝟙 + p
    𝟙∧≤𝟙+p≡≤1+p 𝟘 = refl
    𝟙∧≤𝟙+p≡≤1+p 𝟙 = refl
    𝟙∧≤𝟙+p≡≤1+p ≤𝟙 = refl
    𝟙∧≤𝟙+p≡≤1+p ≤ω = refl

    𝟙∧𝟙+p≡1+p : ∀ p → 𝟙 ∧ (𝟙 + p) ≡ 𝟙 + p
    𝟙∧𝟙+p≡1+p 𝟘 = refl
    𝟙∧𝟙+p≡1+p 𝟙 = refl
    𝟙∧𝟙+p≡1+p ≤𝟙 = refl
    𝟙∧𝟙+p≡1+p ≤ω = refl

    lemma : ∀ p z s n → p ≢ 𝟘
          → (p · n + s) ∧ (n + z) ≡ p · n + s ∧ z
    lemma 𝟘 z s n p≢𝟘 = ⊥-elim (p≢𝟘 refl)
    lemma 𝟙 z s n p≢𝟘 rewrite ·-identityˡ n =
      sym (+-distribˡ-∧ n s z)
    lemma ≤𝟙 z s 𝟘 p≢𝟘 = refl
    lemma ≤𝟙 𝟘 𝟘 𝟙 p≢𝟘 = refl
    lemma ≤𝟙 𝟙 𝟘 𝟙 p≢𝟘 = refl
    lemma ≤𝟙 ≤𝟙 𝟘 𝟙 p≢𝟘 = refl
    lemma ≤𝟙 ≤ω 𝟘 𝟙 p≢𝟘 = refl
    lemma ≤𝟙 𝟘 𝟙 𝟙 p≢𝟘 = refl
    lemma ≤𝟙 𝟙 𝟙 𝟙 p≢𝟘 = refl
    lemma ≤𝟙 ≤𝟙 𝟙 𝟙 p≢𝟘 = refl
    lemma ≤𝟙 ≤ω 𝟙 𝟙 p≢𝟘 = refl
    lemma ≤𝟙 𝟘 ≤𝟙 𝟙 p≢𝟘 = refl
    lemma ≤𝟙 𝟙 ≤𝟙 𝟙 p≢𝟘 = refl
    lemma ≤𝟙 ≤𝟙 ≤𝟙 𝟙 p≢𝟘 = refl
    lemma ≤𝟙 ≤ω ≤𝟙 𝟙 p≢𝟘 = refl
    lemma ≤𝟙 z ≤ω 𝟙 p≢𝟘 = refl
    lemma ≤𝟙 z s ≤𝟙 p≢𝟘 = sym (+-distribˡ-∧ ≤𝟙 s z)
    lemma ≤𝟙 z s ≤ω p≢𝟘 = sym (+-distribˡ-∧ ≤ω s z)
    lemma ≤ω z s 𝟘 p≢𝟘 = refl
    lemma ≤ω z s 𝟙 p≢𝟘 rewrite ≤ω+ s rewrite ≤ω+ (s ∧ z) = refl
    lemma ≤ω z s ≤𝟙 p≢𝟘 rewrite ≤ω+ s rewrite ≤ω+ (s ∧ z) = refl
    lemma ≤ω z s ≤ω p≢𝟘 = sym (+-distribˡ-∧ ≤ω s z)

    nr-factoring : (p r z s n : Linear-or-affine)
                 → nr p r z s n ≡ nr₂ p r · n + nr p r z s 𝟘
    nr-factoring p 𝟘 z s n rewrite ·-zeroʳ (𝟙 ∧ p) =
      lemma (𝟙 ∧ p) z s n (𝟙∧p≢𝟘 p)
    nr-factoring p 𝟙 z s n rewrite ·-zeroʳ (𝟙 + p) =
      +-congʳ (·-congʳ (sym (𝟙∧𝟙+p≡1+p p)))
    nr-factoring p ≤𝟙 z s n rewrite ·-zeroʳ (≤𝟙 + p) =
      +-congʳ (·-congʳ (sym (𝟙∧≤𝟙+p≡≤1+p p)))
    nr-factoring p ≤ω z s n rewrite ≤ω+ p = ·-distribˡ-+ ω n (s + z)

opaque

  -- The nr function returns results that are at least as large as those
  -- of any other factoring nr function for linear-or-affine-semiring-with-meet.

  nr-greatest-factoring :
    (has-nr : Has-nr linear-or-affine-semiring-with-meet)
    (is-factoring-nr : Is-factoring-nr has-nr) →
    ∀ p r z s n → Has-nr.nr has-nr p r z s n ≤ nr p r z s n
  nr-greatest-factoring has-nr is-factoring-nr = λ where
      p r ≤ω s n → lemma $ begin
        nr′ p r ≤ω s n                ≡⟨ nr-factoring ⟩
        nr₂′ p r · n + nr′ p r ≤ω s 𝟘 ≤⟨ +-monotoneʳ {r = nr₂′ p r · n} (nr-zero refl) ⟩
        nr₂′ p r · n + ≤ω             ≡⟨ +-zeroʳ (nr₂′ p r · n) ⟩
        ≤ω                            ∎
      p r z ≤ω n → lemma $ begin
        nr′ p r z ≤ω n                  ≤⟨ nr-suc ⟩
        ≤ω + p · n + r · nr′ p r z ≤ω n ≡⟨ +-zeroˡ (p · n + r · nr′ p r z ≤ω n) ⟩
        ≤ω                              ∎
      p r z s ≤ω → lemma $ begin
        nr′ p r z s ≤ω                ≡⟨ nr-factoring ⟩
        nr₂′ p r · ≤ω + nr′ p r z s 𝟘 ≡⟨ +-congʳ (≢𝟘·≤ω nr₂≢𝟘) ⟩
        ≤ω + nr′ p r z s 𝟘            ≡⟨ +-zeroˡ (nr′ p r z s 𝟘) ⟩
        ≤ω                            ∎
      p r 𝟘 𝟘 𝟘 → begin
        nr′ p r 𝟘 𝟘 𝟘 ≡⟨ nr′-𝟘 ⟩
        𝟘             ≡˘⟨ nr-𝟘 r .proj₂ (refl , refl , refl) ⟩
        nr p r 𝟘 𝟘 𝟘  ∎
      ≤ω r z s 𝟙 → pn≡ω→nr′≤ refl
      ≤ω r z s ≤𝟙 → pn≡ω→nr′≤ refl
      𝟙 r z 𝟙 𝟙 → pn,s≢𝟘→nr′≤ (λ ()) (λ ())
      𝟙 r z ≤𝟙 𝟙 → pn,s≢𝟘→nr′≤ (λ ()) (λ ())
      𝟙 r z 𝟙 ≤𝟙 → pn,s≢𝟘→nr′≤ (λ ()) (λ ())
      ≤𝟙 r z 𝟙 𝟙 → pn,s≢𝟘→nr′≤ (λ ()) (λ ())
      ≤𝟙 r z 𝟙 ≤𝟙 → pn,s≢𝟘→nr′≤ (λ ()) (λ ())
      𝟙 r z ≤𝟙 ≤𝟙 → pn,s≢𝟘→nr′≤ (λ ()) (λ ())
      ≤𝟙 r z ≤𝟙 𝟙 → pn,s≢𝟘→nr′≤ (λ ()) (λ ())
      ≤𝟙 r z ≤𝟙 ≤𝟙 → pn,s≢𝟘→nr′≤ (λ ()) (λ ())
      p r 𝟘 𝟙 𝟙 → n≢𝟘→nr′≤ (λ ()) (λ ())
      p r 𝟘 ≤𝟙 𝟙 → n≢𝟘→nr′≤ (λ ()) λ ()
      p r 𝟙 s 𝟙 → n≢𝟘→nr′≤ (λ ()) (λ ())
      p r ≤𝟙 s 𝟙 → n≢𝟘→nr′≤ (λ ()) (λ ())
      p r 𝟘 𝟙 ≤𝟙 → n≢𝟘→nr′≤ (λ ()) (λ ())
      p r 𝟘 ≤𝟙 ≤𝟙 → n≢𝟘→nr′≤ (λ ()) (λ ())
      p r 𝟙 s ≤𝟙 → n≢𝟘→nr′≤ (λ ()) (λ ())
      p r ≤𝟙 s ≤𝟙 → n≢𝟘→nr′≤ (λ ()) (λ ())
      p ≤ω 𝟘 𝟘 𝟙 → nr′pω≤ λ ()
      p ≤ω 𝟘 𝟘 ≤𝟙 → nr′pω≤ λ ()
      p ≤ω 𝟘 𝟙 n → nr′pω≤ λ ()
      p ≤ω 𝟘 ≤𝟙 n → nr′pω≤ λ ()
      p ≤ω 𝟙 s n → nr′pω≤ λ ()
      p ≤ω ≤𝟙 s n → nr′pω≤ λ ()
      𝟙 𝟙 z s 𝟙 → p,r,n≢𝟘→nr′≤ (λ ()) (λ ()) (λ ())
      𝟙 𝟙 z s ≤𝟙 → p,r,n≢𝟘→nr′≤ (λ ()) (λ ()) (λ ())
      ≤𝟙 𝟙 z s 𝟙 → p,r,n≢𝟘→nr′≤ (λ ()) (λ ()) (λ ())
      ≤𝟙 𝟙 z s ≤𝟙 → p,r,n≢𝟘→nr′≤ (λ ()) (λ ()) (λ ())
      𝟙 ≤𝟙 z s 𝟙 → p,r,n≢𝟘→nr′≤ (λ ()) (λ ()) (λ ())
      𝟙 ≤𝟙 z s ≤𝟙 → p,r,n≢𝟘→nr′≤ (λ ()) (λ ()) (λ ())
      ≤𝟙 ≤𝟙 z s 𝟙 → p,r,n≢𝟘→nr′≤ (λ ()) (λ ()) (λ ())
      ≤𝟙 ≤𝟙 z s ≤𝟙 → p,r,n≢𝟘→nr′≤ (λ ()) (λ ()) (λ ())
      p 𝟙 z 𝟙 n → r,s≢𝟘→nr′≤ (λ ()) (λ ())
      p 𝟙 z ≤𝟙 n → r,s≢𝟘→nr′≤ (λ ()) (λ ())
      p ≤𝟙 z 𝟙 n → r,s≢𝟘→nr′≤ (λ ()) (λ ())
      p ≤𝟙 z ≤𝟙 n → r,s≢𝟘→nr′≤ (λ ()) (λ ())
      p 𝟘 z s 𝟘 → begin
        nr′ p 𝟘 z s 𝟘 ≤⟨ ∧-greatest-lower-bound
                          (≤-trans nr-suc′ (≤-reflexive (+-identityʳ s)))
                          (nr-zero refl) ⟩
        s ∧ z ≡⟨⟩
        (𝟘 + s) ∧ z ≡˘⟨ ∧-congʳ (+-congʳ (·-zeroʳ (𝟙 ∧ p))) ⟩
        ((𝟙 ∧ p) · 𝟘 + s) ∧ z ≡⟨⟩
        nr p 𝟘 z s 𝟘 ∎
      p 𝟘 𝟘 𝟘 n →
        let ≤pn : nr′ p 𝟘 𝟘 𝟘 n ≤ p · n
            ≤pn = begin
              nr′ p 𝟘 𝟘 𝟘 n                  ≤⟨ nr-suc ⟩
              𝟘 + p · n + 𝟘 · nr′ p 𝟘 𝟘 𝟘 𝟙 ≡⟨⟩
              p · n + 𝟘                      ≡⟨ +-identityʳ (p · n) ⟩
              p · n                          ∎
            ≤n : nr′ p 𝟘 𝟘 𝟘 n ≤ n
            ≤n = begin
              nr′ p 𝟘 𝟘 𝟘 n                 ≡⟨ nr-factoring ⟩
              nr₂′ p 𝟘 · n + nr′ p 𝟘 𝟘 𝟘 𝟘 ≡⟨ +-congˡ {nr₂′ p 𝟘 · n} nr′-𝟘 ⟩
              nr₂′ p 𝟘 · n + 𝟘              ≡⟨ +-identityʳ (nr₂′ p 𝟘 · n) ⟩
              nr₂′ p 𝟘 · n                  ≤⟨ ·-monotoneˡ (≢𝟘→≤𝟙 nr₂≢𝟘) ⟩
              𝟙 · n                         ≡⟨ ·-identityˡ n ⟩
              n                             ∎
        in begin
          nr′ p 𝟘 𝟘 𝟘 n              ≤⟨ ∧-greatest-lower-bound ≤n ≤pn ⟩
          n ∧ p · n                   ≡˘⟨ ∧-congʳ (∧-idem n) ⟩
          (n ∧ n) ∧ p · n             ≡⟨ ∧-assoc n n (p · n) ⟩
          n ∧ n ∧ p · n               ≡⟨ ∧-comm n (n ∧ p · n) ⟩
          (n ∧ p · n) ∧ n             ≡˘⟨ ∧-congʳ (∧-congʳ (·-identityˡ n)) ⟩
          (𝟙 · n ∧ p · n) ∧ n         ≡˘⟨ ∧-congʳ (·-distribʳ-∧ n 𝟙 p) ⟩
          ((𝟙 ∧ p) · n) ∧ n           ≡˘⟨ ∧-cong (+-identityʳ ((𝟙 ∧ p) · n)) (+-identityʳ n) ⟩
          ((𝟙 ∧ p) · n + 𝟘) ∧ (n + 𝟘) ≡⟨⟩
          nr p 𝟘 𝟘 𝟘 n                ∎
      p 𝟙 z 𝟘 𝟘 → begin
        nr′ p 𝟙 z 𝟘 𝟘 ≤⟨ nr-zero refl ⟩
        z              ≡⟨⟩
        𝟘 + z          ≡˘⟨ +-congʳ (·-zeroʳ (𝟙 + p)) ⟩
        (𝟙 + p) · 𝟘 + z ≡⟨⟩
        nr p 𝟙 z 𝟘 𝟘  ∎
      𝟘 𝟙 𝟘 𝟘 n → begin
        nr′ 𝟘 𝟙 𝟘 𝟘 n                 ≡⟨ nr-factoring ⟩
        nr₂′ 𝟘 𝟙 · n + nr′ 𝟘 𝟙 𝟘 𝟘 𝟘 ≡⟨ +-congˡ {nr₂′ 𝟘 𝟙 · n} nr′-𝟘 ⟩
        nr₂′ 𝟘 𝟙 · n + 𝟘              ≤⟨ +-monotoneˡ (·-monotoneˡ (≢𝟘→≤𝟙 nr₂≢𝟘)) ⟩
        𝟙 · n + 𝟘                     ≡⟨⟩
        nr 𝟘 𝟙 𝟘 𝟘 n                  ∎
      𝟘 ≤𝟙 𝟘 𝟘 n → begin
        nr′ 𝟘 ≤𝟙 𝟘 𝟘 n ≤⟨ nr-suc ⟩
        𝟘 + 𝟘 · n + ≤𝟙 · nr′ 𝟘 ≤𝟙 𝟘 𝟘 n       ≡⟨⟩
        ≤𝟙 · nr′ 𝟘 ≤𝟙 𝟘 𝟘 n                   ≡⟨ ·-congˡ {≤𝟙} nr-factoring ⟩
        ≤𝟙 · (nr₂′ 𝟘 ≤𝟙 · n + nr′ 𝟘 ≤𝟙 𝟘 𝟘 𝟘) ≡⟨ ·-congˡ {≤𝟙} (+-congˡ {nr₂′ 𝟘 ≤𝟙 · n} nr′-𝟘) ⟩
        ≤𝟙 · (nr₂′ 𝟘 ≤𝟙 · n + 𝟘)               ≡⟨ ·-distribˡ-+ ≤𝟙 (nr₂′ 𝟘 ≤𝟙 · n) 𝟘 ⟩
        ≤𝟙 · nr₂′ 𝟘 ≤𝟙 · n + 𝟘                 ≤⟨ +-monotoneˡ {r = 𝟘} (·-monotoneʳ {r = ≤𝟙}
                                                     (·-monotoneˡ (≢𝟘→≤𝟙 nr₂≢𝟘))) ⟩
        ≤𝟙 · 𝟙 · n + 𝟘                         ≡⟨ +-congʳ {𝟘} (·-congˡ {≤𝟙} (·-identityˡ n)) ⟩
        ≤𝟙 · n + 𝟘                             ≡⟨⟩
        nr 𝟘 ≤𝟙 𝟘 𝟘 n                          ∎
      p ≤𝟙 z 𝟘 𝟘 → begin
        nr′ p ≤𝟙 z 𝟘 𝟘           ≤⟨ nr-suc′ ⟩
        𝟘 + ≤𝟙 · nr′ p ≤𝟙 z 𝟘 𝟘 ≤⟨ +-monotoneʳ {r = 𝟘} (·-monotoneʳ {r = ≤𝟙} (nr-zero refl)) ⟩
        𝟘 + ≤𝟙 · z               ≡˘⟨ +-congʳ (·-zeroʳ (≤𝟙 + p)) ⟩
        (≤𝟙 + p) · 𝟘 + ≤𝟙 · z    ≡⟨⟩
        nr p ≤𝟙 z 𝟘 𝟘            ∎
    where
    open Is-factoring-nr is-factoring-nr renaming (nr₂ to nr₂′)
    open Has-nr has-nr renaming (nr to nr′; nr-positive to nr′-positive)
    open Addition linear-or-affine-semiring-with-meet
    open Meet linear-or-affine-semiring-with-meet
    open Multiplication linear-or-affine-semiring-with-meet
    open PartialOrder linear-or-affine-semiring-with-meet
    open Semiring-with-meet linear-or-affine-semiring-with-meet
      hiding (𝟘; 𝟙; ω; _+_; _·_; _∧_; _≤_)
    open Tools.Reasoning.PartialOrder ≤-poset
    lemma : nr′ p r z s n ≤ ≤ω → nr′ p r z s n ≤ nr p r z s n
    lemma {p} {r} {z} {s} {n} nr′≤ω =
      ≤-trans nr′≤ω (≤ω≤ (nr p r z s n))
    nr-suc′ : nr′ p r z s 𝟘 ≤ s + r · nr′ p r z s 𝟘
    nr-suc′ {p} {r} {z} {s} = begin
      nr′ p r z s 𝟘 ≤⟨ nr-suc ⟩
      s + p · 𝟘 + r · nr′ p r z s 𝟘 ≡⟨ +-congˡ {s} (+-congʳ (·-zeroʳ p)) ⟩
      s + 𝟘 + r · nr′ p r z s 𝟘     ≡⟨⟩
      s + r · nr′ p r z s 𝟘         ∎
    nr′-𝟘 : nr′ p r 𝟘 𝟘 𝟘 ≡ 𝟘
    nr′-𝟘 = Natrec.nr-𝟘 linear-or-affine-semiring-with-meet ⦃ has-nr ⦄
    pn≡ω→nr′≤ : p · n ≡ ≤ω → nr′ p r z s n ≤ nr p r z s n
    pn≡ω→nr′≤ {p} {n} {r} {z} {s} pn≡ω = lemma $ begin
      nr′ p r z s n                 ≤⟨ nr-suc ⟩
      s + p · n + r · nr′ p r z s n ≡⟨ +-congˡ {s} (+-congʳ pn≡ω) ⟩
      s + ≤ω + r · nr′ p r z s n    ≡⟨ +-congˡ {s} (+-zeroˡ (r · nr′ p r z s n)) ⟩
      s + ≤ω                        ≡⟨ +-zeroʳ s ⟩
      ≤ω                            ∎
    pn,s≢𝟘→nr′≤ : p · n ≢ 𝟘 → s ≢ 𝟘 → nr′ p r z s n ≤ nr p r z s n
    pn,s≢𝟘→nr′≤ {p} {n} {s} {r} {z} pn≢𝟘 s≢𝟘 = lemma $ begin
        nr′ p r z s n                   ≤⟨ nr-suc ⟩
        s + p · n + r · nr′ p r z s n   ≡˘⟨ +-assoc s (p · n) (r · nr′ p r z s n) ⟩
        (s + p · n) + r · nr′ p r z s n ≡⟨ +-congʳ (≢𝟘+≢𝟘 s≢𝟘 pn≢𝟘) ⟩
        ≤ω + r · nr′ p r z s n          ≡⟨ +-zeroˡ (r · nr′ p r z s n) ⟩
        ≤ω                              ∎
    n≢𝟘→nr′≤ : n ≢ 𝟘 → ¬ (z ≡ 𝟘 × s ≡ 𝟘) → nr′ p r z s n ≤ nr p r z s n
    n≢𝟘→nr′≤ {n} {z} {s} {p} {r} n≢𝟘 z,s≢𝟘 = lemma $ begin
      nr′ p r z s n ≡⟨ nr-factoring ⟩
      nr₂′ p r · n + nr′ p r z s 𝟘 ≡⟨ ≢𝟘+≢𝟘 (≢𝟘·≢𝟘 nr₂≢𝟘 n≢𝟘) (λ nr′≡𝟘 →
                                       let z≡𝟘 , s≡𝟘 , _ = nr′-positive nr′≡𝟘
                                       in  z,s≢𝟘 (z≡𝟘 , s≡𝟘)) ⟩
      ≤ω ∎
    nr′pω≤ : ¬ (z ≡ 𝟘 × s ≡ 𝟘 × n ≡ 𝟘) → nr′ p ≤ω z s n ≤ nr p ≤ω z s n
    nr′pω≤ {z} {s} {n} {p} ≢𝟘 = lemma $ begin
      nr′ p ≤ω z s n                  ≤⟨ nr-suc ⟩
      s + p · n + ≤ω · nr′ p ≤ω z s n ≡⟨ +-congˡ {s} (+-congˡ {p · n} (≤ω·≢𝟘 (≢𝟘 ∘→ nr′-positive))) ⟩
      s + p · n + ≤ω                  ≡⟨ +-congˡ {s} (+-zeroʳ (p · n)) ⟩
      s + ≤ω                          ≡⟨ +-zeroʳ s ⟩
      ≤ω                              ∎
    p,r,n≢𝟘→nr′≤ : p ≢ 𝟘 → r ≢ 𝟘 → n ≢ 𝟘 → nr′ p r z s n ≤ nr p r z s n
    p,r,n≢𝟘→nr′≤ {p} {r} {n} {z} {s} p≢𝟘 r≢𝟘 n≢𝟘 = lemma $ begin
      nr′ p r z s n ≤⟨ nr-suc ⟩
      s + p · n + r · nr′ p r z s n ≡⟨ +-congˡ {s} (≢𝟘+≢𝟘 (≢𝟘·≢𝟘 p≢𝟘 n≢𝟘)
                                        (≢𝟘·≢𝟘 r≢𝟘 (n≢𝟘 ∘→ proj₂ ∘→ proj₂ ∘→ nr′-positive))) ⟩
      s + ≤ω ≡⟨ +-zeroʳ s ⟩
      ≤ω ∎
    r,s≢𝟘→nr′≤ : r ≢ 𝟘 → s ≢ 𝟘 → nr′ p r z s n ≤ nr p r z s n
    r,s≢𝟘→nr′≤ {r} {s} {p} {z} {n} r≢𝟘 s≢𝟘 = lemma $ begin
      nr′ p r z s n                   ≤⟨ nr-suc ⟩
      s + p · n + r · nr′ p r z s n   ≡⟨ +-congˡ {s} (+-comm (p · n) (r · nr′ p r z s n)) ⟩
      s + r · nr′ p r z s n + p · n   ≡˘⟨ +-assoc s (r · nr′ p r z s n) (p · n) ⟩
      (s + r · nr′ p r z s n) + p · n ≡⟨ +-congʳ (≢𝟘+≢𝟘 s≢𝟘
                                          (≢𝟘·≢𝟘 r≢𝟘 (s≢𝟘 ∘→ proj₁ ∘→ proj₂ ∘→ nr′-positive))) ⟩
      ≤ω + p · n                      ≡⟨ +-zeroˡ (p · n) ⟩
      ≤ω                              ∎

opaque

  -- The nr function satisfies Linearity-like-nr-for-𝟘.

  nr-linearity-like-for-𝟘 :
    Has-nr.Linearity-like-nr-for-𝟘 linear-or-affine-has-nr
  nr-linearity-like-for-𝟘 = refl

opaque

  -- The nr function satisfies Linearity-like-nr-for-𝟙.

  nr-linearity-like-for-𝟙 :
    Has-nr.Linearity-like-nr-for-𝟙 linear-or-affine-has-nr
  nr-linearity-like-for-𝟙 = refl

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
          {s = 𝕤} ()
          {s = 𝕨} (ok , no-η) →
            case []-cong→Erased ok of λ
              (ok₁ , ok₂) →
            (ok₁ , no-η) , ok₂ , (λ ())
      ; []-cong→¬Trivial = λ where
          {s = 𝕤} ()
          {s = 𝕨}    → []-cong→¬Trivial ∘→ proj₁
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

------------------------------------------------------------------------
-- Subtraction

open Subtraction linear-or-affine-semiring-with-meet

opaque

  -- Subtraction of ω by anything is ω

  ω-p≡ω : ∀ p → ≤ω - p ≡ ≤ω
  ω-p≡ω p = ∞-p≡∞ PE.refl p

opaque

  -- Subtraction of 𝟙 by 𝟙 is 𝟘

  𝟙-𝟙≡𝟘 : 𝟙 - 𝟙 ≡ 𝟘
  𝟙-𝟙≡𝟘 =
    refl ,
    λ where
      𝟘  _  → refl
      𝟙  ()
      ≤𝟙 ()
      ≤ω ()

opaque

  -- Subtraction of ≤𝟙 by ≤𝟙 is 𝟘

  ≤𝟙-≤𝟙≡𝟘 : ≤𝟙 - ≤𝟙 ≡ 𝟘
  ≤𝟙-≤𝟙≡𝟘 =
    refl ,
    λ where
      𝟘  _  → refl
      𝟙  ()
      ≤𝟙 ()
      ≤ω ()

opaque

  -- Subtraction of ≤𝟙 by 𝟙 is 𝟘

  ≤𝟙-𝟙≡𝟘 : ≤𝟙 - 𝟙 ≡ 𝟘
  ≤𝟙-𝟙≡𝟘 =
    refl ,
    λ where
      𝟘  _  → refl
      𝟙  ()
      ≤𝟙 ()
      ≤ω ()

opaque

  -- Subtraction of p by ≤ω is not possible unless p ≡ ≤ω

  p-ω≰ : p - ≤ω ≤ q → p ≡ ≤ω
  p-ω≰ {(𝟘)} {(𝟘)} ()
  p-ω≰ {(𝟘)} {(𝟙)} ()
  p-ω≰ {(𝟘)} {(≤𝟙)} ()
  p-ω≰ {(𝟘)} {(≤ω)} ()
  p-ω≰ {(𝟙)} {(𝟘)} ()
  p-ω≰ {(𝟙)} {(𝟙)} ()
  p-ω≰ {(𝟙)} {(≤𝟙)} ()
  p-ω≰ {(𝟙)} {(≤ω)} ()
  p-ω≰ {(≤𝟙)} {(𝟘)} ()
  p-ω≰ {(≤𝟙)} {(𝟙)} ()
  p-ω≰ {(≤𝟙)} {(≤𝟙)} ()
  p-ω≰ {(≤𝟙)} {(≤ω)} ()
  p-ω≰ {(≤ω)} _ = refl

opaque

  -- Subtraction of p by ≤ω is not possible unless p ≡ ≤ω

  p-ω≢ : p - ≤ω ≡ q → p ≡ ≤ω
  p-ω≢ {q} = p-ω≰ {q = q} ∘→ proj₁

opaque

  -- Subtraction of 𝟙 by ≤𝟙 is not possible

  𝟙-≤𝟙≰ : 𝟙 - ≤𝟙 ≤ p → ⊥
  𝟙-≤𝟙≰ {(𝟘)} ()
  𝟙-≤𝟙≰ {(𝟙)} ()
  𝟙-≤𝟙≰ {(≤𝟙)} ()
  𝟙-≤𝟙≰ {(≤ω)} ()

opaque

  -- Subtraction of 𝟙 by ≤𝟙 is not possible

  𝟙-≤𝟙≢ : 𝟙 - ≤𝟙 ≡ p → ⊥
  𝟙-≤𝟙≢ {p} = 𝟙-≤𝟙≰ {p} ∘→ proj₁

opaque

  -- The semiring supports subtraction with
  --   ≤ω - p ≡ ≤ω for all p
  --   p - 𝟘 ≡ p for all p
  --   𝟙 - 𝟙 ≡ 𝟘
  --   ≤𝟙 - ≤𝟙 ≡ 𝟘
  --   ≤𝟙 - 𝟙 ≡ 𝟘
  -- and not defined otherwise

  supports-subtraction : Supports-subtraction
  supports-subtraction {p} {(≤ω)} {r} x =
    case p-ω≰ {q = r} x of λ {
      refl →
    ≤ω , ω-p≡ω ≤ω }
  supports-subtraction {p} {(𝟘)} {r} x =
    p , p-𝟘≡p
  supports-subtraction {(≤ω)} {q} _ =
    ≤ω , ω-p≡ω q
  supports-subtraction {(𝟘)} {r} x =
    case 𝟘-p≤q {q = r} x of λ {
      (refl , refl) →
    𝟘 , p-𝟘≡p }
  supports-subtraction {(𝟙)} {(𝟙)} _ =
    𝟘 , p-p≤𝟘 ,
    λ where
      𝟘  _  → refl
      𝟙  ()
      ≤𝟙 ()
      ≤ω ()
  supports-subtraction {(≤𝟙)} {(𝟙)} x =
    𝟘 , ≤𝟙-𝟙≡𝟘
  supports-subtraction {(≤𝟙)} {(≤𝟙)} x =
    𝟘 , p-p≤𝟘 ,
    λ where
      𝟘  _  → refl
      𝟙  ()
      ≤𝟙 ()
      ≤ω ()
  supports-subtraction {(𝟙)} {(≤𝟙)} {r} x =
    ⊥-elim (𝟙-≤𝟙≰ {p = r} x)

-- An alternative definition of the subtraction relation with
--   ≤ω - p ≡ ≤ω for all p
--   p - 𝟘 ≡ p for all p
--   𝟙 - 𝟙 ≡ 𝟘
--   ≤𝟙 - ≤𝟙 ≡ 𝟘
--   ≤𝟙 - 𝟙 ≡ 𝟘
-- and not defined otherwise

data _-_≡′_ : (p q r : Linear-or-affine) → Set where
  ω-p≡′ω : ≤ω - p ≡′ ≤ω
  p-𝟘≡′p : p - 𝟘 ≡′ p
  𝟙-𝟙≡′𝟘 : 𝟙 - 𝟙 ≡′ 𝟘
  ≤𝟙-≤𝟙≡′𝟘 : ≤𝟙 - ≤𝟙 ≡′ 𝟘
  ≤𝟙-𝟙≡′𝟘 : ≤𝟙 - 𝟙 ≡′ 𝟘

opaque

  -- The two subtraction relations are equivalent.

  -≡↔-≡′ : ∀ p q r → (p - q ≡ r) ⇔ (p - q ≡′ r)
  -≡↔-≡′ p q r = left p q r , right
    where
    left : ∀ p q r → p - q ≡ r → p - q ≡′ r
    left ≤ω q r p-q≡r =
      case -≡-functional {q = q} p-q≡r (ω-p≡ω q) of λ {
        refl →
      ω-p≡′ω }
    left p 𝟘 r p-q≡r =
      case -≡-functional p-q≡r p-𝟘≡p of λ {
        refl →
      p-𝟘≡′p }
    left 𝟘 q r p-q≡r =
      case 𝟘-p≡q p-q≡r of λ {
        (refl , refl) →
      p-𝟘≡′p}
    left 𝟙 𝟙 r p-q≡r =
      case -≡-functional p-q≡r 𝟙-𝟙≡𝟘 of λ {
        refl →
      𝟙-𝟙≡′𝟘 }
    left ≤𝟙 ≤𝟙 r p-q≡r =
      case -≡-functional p-q≡r ≤𝟙-≤𝟙≡𝟘 of λ {
        refl →
      ≤𝟙-≤𝟙≡′𝟘 }
    left ≤𝟙 𝟙 r p-q≡r =
      case -≡-functional p-q≡r ≤𝟙-𝟙≡𝟘 of λ {
        refl →
      ≤𝟙-𝟙≡′𝟘 }
    left 𝟙 ≤𝟙 r p-q≡r =
      ⊥-elim (𝟙-≤𝟙≢ {r} p-q≡r)
    left 𝟙 ≤ω r p-q≡r =
      case p-ω≢ p-q≡r of λ ()
    left ≤𝟙 ≤ω r p-q≡r =
      case p-ω≢ p-q≡r of λ ()
    right : p - q ≡′ r → p - q ≡ r
    right ω-p≡′ω = ω-p≡ω p
    right p-𝟘≡′p = p-𝟘≡p
    right 𝟙-𝟙≡′𝟘 = 𝟙-𝟙≡𝟘
    right ≤𝟙-≤𝟙≡′𝟘 = ≤𝟙-≤𝟙≡𝟘
    right ≤𝟙-𝟙≡′𝟘 = ≤𝟙-𝟙≡𝟘


------------------------------------------------------------------------
-- Properties of greatest lower bounds

opaque

  -- nr 𝟘 r z s 𝟘 is the greatest lower bound of nrᵢ r z s.

  nr-nrᵢ-GLB :
    let 𝕄 = linear-or-affine-semiring-with-meet in
      ∀ r → Semiring-with-meet.Greatest-lower-bound
              𝕄 (nr 𝟘 r z s 𝟘) (Semiring-with-meet.nrᵢ 𝕄 r z s)
  nr-nrᵢ-GLB = λ where
      𝟘 → GLB-congʳ (sym (trans (∧-congʳ (+-congʳ (·-zeroʳ (𝟙 ∧ 𝟘))))
            (∧-comm _ _))) nrᵢ-𝟘-GLB
      𝟙 → lemma-𝟙 _ _
      ≤𝟙 → lemma-≤𝟙 _ _
      ≤ω → lemma-ω _ _
    where
    open Semiring-with-meet linear-or-affine-semiring-with-meet
      hiding (𝟘; 𝟙; ω; _∧_; _·_; _+_)
    open GLB linear-or-affine-semiring-with-meet
    open Natrec linear-or-affine-semiring-with-meet
    open PartialOrder linear-or-affine-semiring-with-meet
    lemma′ : ∀ {z} i → nrᵢ 𝟙 z 𝟘 i ≡ z
    lemma′ 0 = refl
    lemma′ (1+ i) = trans (·-identityˡ _) (lemma′ i)
    lemma : ∀ {r z s} i →
      nrᵢ r z s i ≡ ≤ω → Greatest-lower-bound ≤ω (nrᵢ r z s)
    lemma {r} {z} {s} i nrᵢ≡ω =
      (λ i → ≤ω≤ (nrᵢ r z s i)) , λ q q≤ → ≤-trans (q≤ i) (≤-reflexive nrᵢ≡ω)
    lemma-𝟙 : ∀ z s → Greatest-lower-bound (≤ω · s + z) (nrᵢ 𝟙 z s)
    lemma-𝟙 𝟘 𝟘 = GLB-nrᵢ-𝟘
    lemma-𝟙 𝟘 𝟙 = lemma 2 refl
    lemma-𝟙 𝟘 ≤𝟙 = lemma 2 refl
    lemma-𝟙 𝟘 ≤ω = lemma 1 refl
    lemma-𝟙 𝟙 𝟘 = GLB-const lemma′
    lemma-𝟙 𝟙 𝟙 = lemma 1 refl
    lemma-𝟙 𝟙 ≤𝟙 = lemma 1 refl
    lemma-𝟙 𝟙 ≤ω = lemma 1 refl
    lemma-𝟙 ≤𝟙 𝟘 = GLB-const lemma′
    lemma-𝟙 ≤𝟙 𝟙 = lemma 1 refl
    lemma-𝟙 ≤𝟙 ≤𝟙 = lemma 1 refl
    lemma-𝟙 ≤𝟙 ≤ω = lemma 1 refl
    lemma-𝟙 ≤ω 𝟘 = lemma 0 refl
    lemma-𝟙 ≤ω 𝟙 = lemma 0 refl
    lemma-𝟙 ≤ω ≤𝟙 = lemma 0 refl
    lemma-𝟙 ≤ω ≤ω = lemma 0 refl
    lemma-≤𝟙 : ∀ z s → Greatest-lower-bound (≤ω · s + ≤𝟙 · z) (nrᵢ ≤𝟙 z s)
    lemma-≤𝟙 𝟘 𝟘 = GLB-nrᵢ-𝟘
    lemma-≤𝟙 𝟘 𝟙 = lemma 2 refl
    lemma-≤𝟙 𝟘 ≤𝟙 = lemma 2 refl
    lemma-≤𝟙 𝟘 ≤ω = lemma 1 refl
    lemma-≤𝟙 𝟙 𝟘 =
      (λ { 0 → refl
         ; (1+ i) → ≤-reflexive (lem i)}) ,
      λ { 𝟘 q≤ → case q≤ 0 of λ ()
        ; 𝟙 q≤ → case q≤ 1 of λ ()
        ; ≤𝟙 q≤ → refl
        ; ≤ω q≤ → refl}
      where
      lem : ∀ i → ≤𝟙 ≡ nrᵢ ≤𝟙 𝟙 𝟘 (1+ i)
      lem 0 = refl
      lem (1+ i) = ·-congˡ {x = ≤𝟙} (lem i)
    lemma-≤𝟙 𝟙 𝟙 = lemma 1 refl
    lemma-≤𝟙 𝟙 ≤𝟙 = lemma 1 refl
    lemma-≤𝟙 𝟙 ≤ω = lemma 1 refl
    lemma-≤𝟙 ≤𝟙 𝟘 = GLB-const lem
      where
      lem : ∀ i → nrᵢ ≤𝟙 ≤𝟙 𝟘 i ≡ ≤𝟙
      lem 0 = refl
      lem (1+ i) = ·-congˡ {x = ≤𝟙} (lem i)
    lemma-≤𝟙 ≤𝟙 𝟙 = lemma 1 refl
    lemma-≤𝟙 ≤𝟙 ≤𝟙 = lemma 1 refl
    lemma-≤𝟙 ≤𝟙 ≤ω = lemma 1 refl
    lemma-≤𝟙 ≤ω 𝟘 = lemma 0 refl
    lemma-≤𝟙 ≤ω 𝟙 = lemma 0 refl
    lemma-≤𝟙 ≤ω ≤𝟙 = lemma 0 refl
    lemma-≤𝟙 ≤ω ≤ω = lemma 0 refl
    lemma-ω : ∀ z s → Greatest-lower-bound (≤ω · (s + z)) (nrᵢ ≤ω z s)
    lemma-ω 𝟘 𝟘 = GLB-nrᵢ-𝟘
    lemma-ω 𝟙 𝟘 = lemma 1 refl
    lemma-ω ≤𝟙 𝟘 = lemma 1 refl
    lemma-ω ≤ω 𝟘 = lemma 0 refl
    lemma-ω 𝟘 𝟙 = lemma 2 refl
    lemma-ω 𝟙 𝟙 = lemma 1 refl
    lemma-ω ≤𝟙 𝟙 = lemma 1 refl
    lemma-ω ≤ω 𝟙 = lemma 0 refl
    lemma-ω 𝟘 ≤𝟙 = lemma 2 refl
    lemma-ω 𝟙 ≤𝟙 = lemma 1 refl
    lemma-ω ≤𝟙 ≤𝟙 = lemma 1 refl
    lemma-ω ≤ω ≤𝟙 = lemma 0 refl
    lemma-ω 𝟘 ≤ω = lemma 1 refl
    lemma-ω 𝟙 ≤ω = lemma 1 refl
    lemma-ω ≤𝟙 ≤ω = lemma 1 refl
    lemma-ω ≤ω ≤ω = lemma 0 refl

opaque

  -- The sequence nrᵢ r z s has a greatest lower bound

  nrᵢ-GLB :
    let 𝕄 = linear-or-affine-semiring-with-meet in
    ∀ r z s → ∃ λ p →
      Semiring-with-meet.Greatest-lower-bound
        𝕄 p (Semiring-with-meet.nrᵢ 𝕄 r z s)
  nrᵢ-GLB r z s = _ , nr-nrᵢ-GLB r

opaque

  -- The modality supports the usage rule for natrec using
  -- greatest lower bounds.

  linear-or-affine-supports-glb-for-natrec :
    Supports-GLB-for-natrec linear-or-affine-semiring-with-meet
  linear-or-affine-supports-glb-for-natrec = record
    { +-GLBˡ = λ {_} {_} {q} → +-GLBˡ {q = q}
    ; ·-GLBˡ = λ {_} {_} {q} → ·-GLBˡ {q = q}
    ; ·-GLBʳ = ·-GLBʳ
    ; +nrᵢ-GLB = +nrᵢ-GLB
    }
    where
    open Semiring-with-meet linear-or-affine-semiring-with-meet
      hiding (𝟘; 𝟙; ω; _+_; _·_; _∧_; _≤_)
    open GLB linear-or-affine-semiring-with-meet
    open Multiplication linear-or-affine-semiring-with-meet
    open PartialOrder linear-or-affine-semiring-with-meet

    ·-GLBˡ :
      {pᵢ : Sequence Linear-or-affine} →
      Greatest-lower-bound p pᵢ →
      Greatest-lower-bound (q · p) (λ i → q · pᵢ i)
    ·-GLBˡ {q = 𝟘} p-glb = GLB-const′
    ·-GLBˡ {q = 𝟙} p-glb =
      GLB-cong (sym (·-identityˡ _))
        (λ _ → sym (·-identityˡ _))
        p-glb
    ·-GLBˡ {q = ≤𝟙} {pᵢ} p-glb = lemma _ p-glb
      where
      lemma′ : 𝟘 ≤ ≤𝟙 · p → p ≡ 𝟘
      lemma′ {(𝟘)} _ = refl
      lemma′ {(𝟙)} ()
      lemma′ {(≤𝟙)} ()
      lemma′ {(≤ω)} ()
      lemma″ : ∀ p → 𝟙 ≤ ≤𝟙 · p → ⊥
      lemma″ 𝟘 ()
      lemma″ 𝟙 ()
      lemma″ ≤𝟙 ()
      lemma″ ≤ω ()
      lemma‴ : ≤𝟙 ≤ ≤𝟙 · p → ≤𝟙 ≤ p
      lemma‴ {(𝟘)} _ = refl
      lemma‴ {(𝟙)} _ = refl
      lemma‴ {(≤𝟙)} _ = refl
      lemma‴ {(≤ω)} ()
      lemma⁗ : Greatest-lower-bound ≤ω pᵢ → (∀ i → ≤𝟙 ≤ pᵢ i) → ⊥
      lemma⁗ ω-glb ≤pᵢ = case ω-glb .proj₂ ≤𝟙 ≤pᵢ of λ ()
      lemma :
        ∀ p → Greatest-lower-bound p pᵢ →
        Greatest-lower-bound (≤𝟙 · p) (λ i → ≤𝟙 · pᵢ i)
      lemma 𝟘 p-glb =
        GLB-const (λ i → ·-congˡ {x = ≤𝟙} (𝟘-GLB-inv p-glb i))
      lemma 𝟙 p-glb =
          (λ i → ·-monotoneʳ {r = ≤𝟙} (p-glb .proj₁ i))
        , λ { 𝟘 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma′ ∘→ q≤))
            ; 𝟙 q≤ → ⊥-elim (lemma″ (pᵢ 0) (q≤ 0))
            ; ≤𝟙 q≤ → refl
            ; ≤ω q≤ → refl}
      lemma ≤𝟙 p-glb =
          (λ i → ·-monotoneʳ {r = ≤𝟙} (p-glb .proj₁ i))
        , λ { 𝟘 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma′ ∘→ q≤))
            ; 𝟙 q≤ → ⊥-elim (lemma″ (pᵢ 0) (q≤ 0))
            ; ≤𝟙 q≤ → refl
            ; ≤ω q≤ → refl}
      lemma ≤ω p-glb =
          (λ _ → refl)
        , λ { 𝟘 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma′ ∘→ q≤))
            ; 𝟙 q≤ → ⊥-elim (lemma″ (pᵢ 0) (q≤ 0))
            ; ≤𝟙 q≤ → ⊥-elim (lemma⁗ p-glb (λ i → lemma‴ (q≤ i)))
            ; ≤ω q≤ → refl}
    ·-GLBˡ {q = ≤ω} {pᵢ} p-glb = lemma _ p-glb
      where
      lemma′ : 𝟘 ≤ ≤ω · p → p ≡ 𝟘
      lemma′ {(𝟘)} _ = refl
      lemma′ {(𝟙)} ()
      lemma′ {(≤𝟙)} ()
      lemma′ {(≤ω)} ()
      lemma″ : ∀ p → 𝟙 ≤ ≤ω · p → ⊥
      lemma″ 𝟘 ()
      lemma″ 𝟙 ()
      lemma″ ≤𝟙 ()
      lemma″ ≤ω ()
      lemma‴ : ≤𝟙 ≤ ≤ω · p → p ≡ 𝟘
      lemma‴ {(𝟘)} _ = refl
      lemma‴ {(𝟙)} ()
      lemma‴ {(≤𝟙)} ()
      lemma‴ {(≤ω)} ()
      lemma :
        ∀ p → Greatest-lower-bound p pᵢ →
        Greatest-lower-bound (≤ω · p) (λ i → ≤ω · pᵢ i)
      lemma 𝟘 p-glb =
        GLB-const (λ i → ·-congˡ {x = ≤ω} (𝟘-GLB-inv p-glb i))
      lemma 𝟙 p-glb =
          (λ _ → refl)
        , λ { 𝟘 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma′ ∘→ q≤))
            ; 𝟙 q≤ → ⊥-elim (lemma″ (pᵢ 0) (q≤ 0))
            ; ≤𝟙 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma‴ ∘→ q≤))
            ; ≤ω q≤ → refl}
      lemma ≤𝟙 p-glb =
          (λ _ → refl)
        , λ { 𝟘 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma′ ∘→ q≤))
            ; 𝟙 q≤ → ⊥-elim (lemma″ (pᵢ 0) (q≤ 0))
            ; ≤𝟙 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma‴ ∘→ q≤))
            ; ≤ω q≤ → refl}
      lemma ≤ω p-glb =
          (λ _ → refl)
        , λ { 𝟘 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma′ ∘→ q≤))
            ; 𝟙 q≤ → ⊥-elim (lemma″ (pᵢ 0) (q≤ 0))
            ; ≤𝟙 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma‴ ∘→ q≤))
            ; ≤ω q≤ → refl}

    ·-GLBʳ :
      {pᵢ : Sequence Linear-or-affine} →
      Greatest-lower-bound p pᵢ →
      Greatest-lower-bound (p · q) (λ i → pᵢ i · q)
    ·-GLBʳ {p} {q} {pᵢ} p-glb =
      GLB-cong (·-comm q p) (λ i → ·-comm q (pᵢ i)) (·-GLBˡ {q = q} p-glb)

    +-GLBˡ :
      {pᵢ : Sequence Linear-or-affine} →
      Greatest-lower-bound p pᵢ →
      Greatest-lower-bound (q + p) (λ i → q + pᵢ i)
    +-GLBˡ {q = 𝟘} p-glb = p-glb
    +-GLBˡ {q = 𝟙} {pᵢ} p-glb = lemma _ p-glb
      where
      lemma′ : ∀ p q → q ≢ ≤ω → q ≤ 𝟙 + p → p ≡ 𝟘
      lemma′ 𝟘 𝟘 _ _ = refl
      lemma′ 𝟘 𝟙 _ _ = refl
      lemma′ 𝟘 ≤𝟙 _ _ = refl
      lemma′ p ≤ω q≢ω _ = ⊥-elim (q≢ω refl)
      lemma′ 𝟙 𝟘 q≢ω ()
      lemma′ 𝟙 𝟙 q≢ω ()
      lemma′ 𝟙 ≤𝟙 q≢ω ()
      lemma′ ≤𝟙 𝟘 q≢ω ()
      lemma′ ≤𝟙 𝟙 q≢ω ()
      lemma′ ≤𝟙 ≤𝟙 q≢ω ()
      lemma′ ≤ω 𝟘 q≢ω ()
      lemma′ ≤ω 𝟙 q≢ω ()
      lemma′ ≤ω ≤𝟙 q≢ω ()
      lemma :
        ∀ p → Greatest-lower-bound p pᵢ →
        Greatest-lower-bound (𝟙 + p) (λ i → 𝟙 + pᵢ i)
      lemma 𝟘 p-glb =
        GLB-const (λ i → +-congˡ {x = 𝟙} (𝟘-GLB-inv p-glb i))
      lemma 𝟙 p-glb =
          (λ _ → refl)
        , λ { 𝟘 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma′ _ _ (λ ()) ∘→ q≤))
            ; 𝟙 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma′ _ _ (λ ()) ∘→ q≤))
            ; ≤𝟙 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma′ _ _ (λ ()) ∘→ q≤))
            ; ≤ω q≤ → refl}
      lemma ≤𝟙 p-glb =
          (λ _ → refl)
        , λ { 𝟘 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma′ _ _ (λ ()) ∘→ q≤))
            ; 𝟙 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma′ _ _ (λ ()) ∘→ q≤))
            ; ≤𝟙 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma′ _ _ (λ ()) ∘→ q≤))
            ; ≤ω q≤ → refl}
      lemma ≤ω p-glb =
          (λ _ → refl)
        , λ { 𝟘 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma′ _ _ (λ ()) ∘→ q≤))
            ; 𝟙 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma′ _ _ (λ ()) ∘→ q≤))
            ; ≤𝟙 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma′ _ _ (λ ()) ∘→ q≤))
            ; ≤ω q≤ → refl}
    +-GLBˡ {q = ≤𝟙} {pᵢ} p-glb = lemma _ p-glb
      where
      lemma :
        ∀ p → Greatest-lower-bound p pᵢ →
        Greatest-lower-bound (≤𝟙 + p) (λ i → ≤𝟙 + pᵢ i)
      lemma′ : ∀ p q → q ≢ ≤ω → q ≤ ≤𝟙 + p → p ≡ 𝟘
      lemma′ 𝟘 _ _ _ = refl
      lemma′ _ ≤ω q≢ω _ = ⊥-elim (q≢ω refl)
      lemma′ 𝟙 𝟘 _ ()
      lemma′ 𝟙 𝟙 _ ()
      lemma′ 𝟙 ≤𝟙 _ ()
      lemma′ ≤𝟙 𝟘 _ ()
      lemma′ ≤𝟙 𝟙 _ ()
      lemma′ ≤𝟙 ≤𝟙 _ ()
      lemma′ ≤ω 𝟘 _ ()
      lemma′ ≤ω 𝟙 _ ()
      lemma′ ≤ω ≤𝟙 _ ()
      lemma 𝟘 p-glb =
        GLB-const (λ i → +-congˡ {x = ≤𝟙} (𝟘-GLB-inv p-glb i))
      lemma 𝟙 p-glb =
          (λ _ → refl)
        , (λ { 𝟘 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma′ _ _ (λ ()) ∘→ q≤))
             ; 𝟙 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma′ _ _ (λ ()) ∘→ q≤))
             ; ≤𝟙 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma′ _ _ (λ ()) ∘→ q≤))
             ; ≤ω q≤ → refl})
      lemma ≤𝟙 p-glb =
          (λ _ → refl)
        , λ { 𝟘 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma′ _ _ (λ ()) ∘→ q≤))
            ; 𝟙 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma′ _ _ (λ ()) ∘→ q≤))
            ; ≤𝟙 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma′ _ _ (λ ()) ∘→ q≤))
            ; ≤ω q≤ → refl}
      lemma ≤ω p-glb =
          (λ _ → refl)
        , λ { 𝟘 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma′ _ _ (λ ()) ∘→ q≤))
            ; 𝟙 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma′ _ _ (λ ()) ∘→ q≤))
            ; ≤𝟙 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma′ _ _ (λ ()) ∘→ q≤))
            ; ≤ω q≤ → refl}
    +-GLBˡ {q = ≤ω} {pᵢ} p-glb = lemma _ p-glb
      where
      lemma′ : ∀ p q → q ≢ ≤ω → q ≤ ≤ω + p → ⊥
      lemma′ p 𝟘 q≢ω x rewrite ≤ω+ p = case x of λ ()
      lemma′ p 𝟙 q≢ω x rewrite ≤ω+ p = case x of λ ()
      lemma′ p ≤𝟙 q≢ω x rewrite ≤ω+ p = case x of λ ()
      lemma′ p ≤ω q≢ω _ = q≢ω refl
      lemma :
        ∀ p → Greatest-lower-bound p pᵢ →
        Greatest-lower-bound (≤ω + p) (λ i → ≤ω + pᵢ i)
      lemma 𝟘 p-glb =
        GLB-const (λ i → +-congˡ {x = ≤ω} (𝟘-GLB-inv p-glb i))
      lemma 𝟙 p-glb =
          (λ _ → refl)
        , λ { 𝟘 q≤ → ⊥-elim (lemma′ (pᵢ 0) _ (λ ()) (q≤ 0))
            ; 𝟙 q≤ → ⊥-elim (lemma′ (pᵢ 0) _ (λ ()) (q≤ 0))
            ; ≤𝟙 q≤ → ⊥-elim (lemma′ (pᵢ 0) _ (λ ()) (q≤ 0))
            ; ≤ω q≤ → refl}
      lemma ≤𝟙 p-glb =
          (λ _ → refl)
        , λ { 𝟘 q≤ → ⊥-elim (lemma′ (pᵢ 0) _ (λ ()) (q≤ 0))
            ; 𝟙 q≤ → ⊥-elim (lemma′ (pᵢ 0) _ (λ ()) (q≤ 0))
            ; ≤𝟙 q≤ → ⊥-elim (lemma′ (pᵢ 0) _ (λ ()) (q≤ 0))
            ; ≤ω q≤ → refl}
      lemma ≤ω p-glb =
          (λ _ → refl)
        , λ { 𝟘 q≤ → ⊥-elim (lemma′ (pᵢ 0) _ (λ ()) (q≤ 0))
            ; 𝟙 q≤ → ⊥-elim (lemma′ (pᵢ 0) _ (λ ()) (q≤ 0))
            ; ≤𝟙 q≤ → ⊥-elim (lemma′ (pᵢ 0) _ (λ ()) (q≤ 0))
            ; ≤ω q≤ → refl}

    open Tools.Reasoning.PartialOrder ≤-poset

    +nrᵢ-GLB :
      ∀ {p₁ p₂} →
      Greatest-lower-bound p₁ (nrᵢ r z₁ s₁) →
      Greatest-lower-bound p₂ (nrᵢ r z₂ s₂) →
      ∃ λ q → Greatest-lower-bound q (nrᵢ r (z₁ + z₂) (s₁ + s₂)) ×
          p₁ + p₂ ≤ q
    +nrᵢ-GLB {r} {z₁} {s₁} {z₂} {s₂} {p₁} {p₂} p₁-glb p₂-glb =
      _ , nr-nrᵢ-GLB r , (begin
        p₁ + p₂                         ≡⟨ +-cong (GLB-unique p₁-glb (nr-nrᵢ-GLB r))
                                           (GLB-unique p₂-glb (nr-nrᵢ-GLB r)) ⟩
        nr 𝟘 r z₁ s₁ 𝟘 + nr 𝟘 r z₂ s₂ 𝟘 ≤⟨ Has-nr.nr-+ linear-or-affine-has-nr {𝟘} {r} ⟩
        nr 𝟘 r (z₁ + z₂) (s₁ + s₂) 𝟘    ∎)
