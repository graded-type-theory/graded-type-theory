------------------------------------------------------------------------
-- A modality with simultaneous support for affine and linear types
------------------------------------------------------------------------

-- It might make sense to replace some of the proofs with automated
-- proofs.

module Definition.Modality.Instances.Linear-or-affine where

import Definition.Modality
open import Definition.Modality.FullReduction.Assumptions
import Definition.Modality.Properties
import Definition.Modality.Properties.Addition as Addition
import Definition.Modality.Properties.Meet as Meet
import Definition.Modality.Properties.Multiplication as Multiplication
import Definition.Modality.Properties.PartialOrder as PartialOrder
import Definition.Modality.Properties.Star as Star
import Definition.Modality.Type-restrictions

open import Definition.Mode.Restrictions

import Definition.Typed.Restrictions

import Tools.Algebra
open import Tools.Function
open import Tools.Nullary
open import Tools.Product
open import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Sum
open import Tools.Unit

------------------------------------------------------------------------
-- The type

-- Zero, one, at most one, or unlimited.

data Linear-or-affine : Set where
  𝟘 𝟙 ≤𝟙 ≤ω : Linear-or-affine

open Definition.Modality           Linear-or-affine
open Definition.Typed.Restrictions Linear-or-affine
open Tools.Algebra                 Linear-or-affine

private variable
  p q r : Linear-or-affine
  mrs   : Mode-restrictions
  trs   : Type-restrictions

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

-- If p is not 𝟘, then 𝟙 · p is not 𝟘.

𝟙·≢𝟘 : p ≢ 𝟘 → 𝟙 · p ≢ 𝟘
𝟙·≢𝟘 {p = 𝟘} 𝟘≢𝟘 = 𝟘≢𝟘

-- If p is not 𝟘, then ≤𝟙 · p is not 𝟘.

≤𝟙·≢𝟘 : p ≢ 𝟘 → ≤𝟙 · p ≢ 𝟘
≤𝟙·≢𝟘 {p = 𝟘} 𝟘≢𝟘 = 𝟘≢𝟘

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
              , comm+idˡ⇒idʳ +-comm (λ _ → refl)
          }
        ; comm = +-comm
        }
      ; *-isMonoid = record
        { isSemigroup = record
          { isMagma = record
            { isEquivalence = PE.isEquivalence
            ; ∙-cong        = cong₂ _·_
            }
          ; assoc = ·-assoc
          }
        ; identity =
              ·-identityˡ
            , comm+idˡ⇒idʳ ·-comm ·-identityˡ
        }
      ; distrib =
            ·-distribˡ-+
          , comm+distrˡ⇒distrʳ ·-comm ·-distribˡ-+
      }
    ; zero =
          (λ _ → refl)
        , comm+zeˡ⇒zeʳ ·-comm (λ _ → refl)
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
      , comm+distrˡ⇒distrʳ ·-comm ·-distribˡ-∧
  ; +-distrib-∧ =
        +-distribˡ-∧
      , comm+distrˡ⇒distrʳ +-comm +-distribˡ-∧
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

-- The semiring has a well behaved zero

linear-or-affine-has-well-behaved-zero : Has-well-behaved-zero linear-or-affine-semiring-with-meet
linear-or-affine-has-well-behaved-zero = record
  { 𝟙≉𝟘 = λ ()
  ; is-𝟘? = λ where
      𝟘  → yes refl
      𝟙  → no (λ ())
      ≤𝟙 → no (λ ())
      ≤ω → no (λ ())
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
  (∀ r → 𝟘 ⊛ 𝟘 ▷ r ≡ 𝟘) →
  (∀ p q r → p ⊛ q ▷ r ≡ 𝟘 → p ≡ 𝟘 × q ≡ 𝟘) →
  Star-requirements _⊛_▷_
Star-requirements-required′
  M refl refl refl refl refl star ⊛-ineq₁ ⊛-ineq₂ ⊛-idem-𝟘 ⊛≈𝟘 =
    (λ {_ _} → ω⊛▷)
  , (λ {_ _} → ⊛ω▷)
  , (λ {_ _} → ⊛▷ω _ _)
  , (λ {_} → ⊛-idem-𝟘 _)
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
  𝟙⊛▷ 𝟙⊛▷≡𝟘 = case ⊛≈𝟘 _ _ _ 𝟙⊛▷≡𝟘 .proj₁ of λ ()

  ≤𝟙⊛▷ : ≤𝟙 ⊛ q ▷ r ≢ 𝟘
  ≤𝟙⊛▷ ≤𝟙⊛▷≡𝟘 = case ⊛≈𝟘 _ _ _ ≤𝟙⊛▷≡𝟘 .proj₁ of λ ()

  ⊛𝟙▷ : p ⊛ 𝟙 ▷ r ≢ 𝟘
  ⊛𝟙▷ ⊛𝟙▷≡𝟘 = case ⊛≈𝟘 _ _ _ ⊛𝟙▷≡𝟘 .proj₂ of λ ()

  ⊛≤𝟙▷ : p ⊛ ≤𝟙 ▷ r ≢ 𝟘
  ⊛≤𝟙▷ ⊛≤𝟙▷≡𝟘 = case ⊛≈𝟘 _ _ _ ⊛≤𝟙▷≡𝟘 .proj₂ of λ ()

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

-- The star operation of a modality for Linear-or-affine for which the
-- zero is 𝟘, the one is 𝟙, 𝟘 is well behaved, addition is _+_,
-- multiplication is _·_, and the meet operation is _∧_ has to satisfy
-- the Star-requirements.

Star-requirements-required :
  (M : Modality) →
  Modality.𝟘          M ≡ 𝟘 →
  Modality.𝟙          M ≡ 𝟙 →
  Modality._+_        M ≡ _+_ →
  Modality._·_        M ≡ _·_ →
  Modality._∧_        M ≡ _∧_ →
  Has-well-behaved-zero (Modality.semiring-with-meet M) →
  Star-requirements (Modality._⊛_▷_ M)
Star-requirements-required M refl refl refl refl refl 𝟘-wb =
  Star-requirements-required′
    semiring-with-meet refl refl refl refl refl
    _⊛_▷_ ⊛-ineq₁ ⊛-ineq₂ ⊛-idem-𝟘
    (λ _ _ _ eq → ⊛≈𝟘ˡ eq , ⊛≈𝟘ʳ eq)
  where
  open Modality M
  open Star semiring-with-meet-and-star
  open import Definition.Modality.Properties.Has-well-behaved-zero
       semiring-with-meet-and-star 𝟘-wb

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

-- The star operation returns results that are at least as large as
-- those of the star operation of any modality for Linear-or-affine
-- for which the zero is 𝟘, the one is 𝟙, 𝟘 is well behaved, addition is
-- _+_, multiplication is _·_, and the meet operation is _∧_.

⊛-greatest :
  (M : Modality) →
  Modality.𝟘          M ≡ 𝟘 →
  Modality.𝟙          M ≡ 𝟙 →
  Modality._+_        M ≡ _+_ →
  Modality._·_        M ≡ _·_ →
  Modality._∧_        M ≡ _∧_ →
  Has-well-behaved-zero (Modality.semiring-with-meet M) →
  ∀ p q r → Modality._⊛_▷_ M p q r ≤ p ⊛ q ▷ r
⊛-greatest M refl refl refl refl refl 𝟘-wb =
  case Star-requirements-required
         M refl refl refl refl refl 𝟘-wb of
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
  open Modality M using (semiring-with-meet) renaming (_⊛_▷_ to _⊛_▷′_)
  open PartialOrder semiring-with-meet
  open Tools.Reasoning.PartialOrder ≤-poset


-- The "linear or affine types" semiring with meet and star

linear-or-affine-semiring-with-meet-and-star : Semiring-with-meet-and-star
linear-or-affine-semiring-with-meet-and-star = record
  { semiring-with-meet      = semiring-with-meet
  ; _⊛_▷_                   = _⊛_▷_
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
-- The modality

-- The "linear or affine types" modality (with arbitrary mode
-- restrictions).

linear-or-affine : Mode-restrictions → Modality
linear-or-affine rs = record
  { semiring-with-meet-and-star = linear-or-affine-semiring-with-meet-and-star
  ; mode-restrictions = rs
  ; 𝟘-well-behaved = λ _ → linear-or-affine-has-well-behaved-zero
  }

------------------------------------------------------------------------
-- Instances of Full-reduction-assumptions

-- An instance of Type-restrictions is suitable for the full reduction
-- theorem if
-- * Unit-restriction does not hold,
-- * Σₚ-restriction 𝟘 p does not hold,
-- * Σₚ-restriction ≤𝟙 p does not hold, and
-- * Σₚ-restriction ≤ω p does not hold.

Suitable-for-full-reduction :
  Type-restrictions → Set
Suitable-for-full-reduction rs =
  ¬ Unit-restriction ×
  (∀ p → ¬ Σₚ-restriction 𝟘 p) ×
  (∀ p → ¬ Σₚ-restriction ≤𝟙 p) ×
  (∀ p → ¬ Σₚ-restriction ≤ω p)
  where
  open Type-restrictions rs

-- Given an instance of Type-restrictions one can create a "suitable"
-- instance.

suitable-for-full-reduction :
  Type-restrictions → ∃ Suitable-for-full-reduction
suitable-for-full-reduction rs =
    record rs
      { Unit-restriction = ⊥
      ; ΠΣ-restriction   = λ b p q →
          ΠΣ-restriction b p q × p ≢ 𝟘 × p ≢ ≤𝟙 × p ≢ ≤ω
      }
  , idᶠ
  , (λ _ → (_$ refl) ∘→ proj₁ ∘→ proj₂)
  , (λ _ → (_$ refl) ∘→ proj₁ ∘→ proj₂ ∘→ proj₂)
  , (λ _ → (_$ refl) ∘→ proj₂ ∘→ proj₂ ∘→ proj₂)
  where
  open Type-restrictions rs

-- The full reduction assumptions hold for linear-or-affine mrs and
-- any "suitable" Type-restrictions.

full-reduction-assumptions :
  Suitable-for-full-reduction trs →
  Full-reduction-assumptions (linear-or-affine mrs) trs
full-reduction-assumptions {mrs = mrs} (¬Unit , ¬𝟘 , ¬≤𝟙 , ¬≤ω) = record
  { ≤𝟘           = ⊥-elim ∘→ ¬Unit
  ; ·-increasing = λ where
      {p = 𝟘}         ok → ⊥-elim (¬𝟘 _ ok)
      {p = ≤𝟙}        ok → ⊥-elim (¬≤𝟙 _ ok)
      {p = ≤ω}        ok → ⊥-elim (¬≤ω _ ok)
      {p = 𝟙} {r = q} _  → begin
        q      ≡˘⟨ ·-identityˡ _ ⟩
        𝟙 · q  ∎
  ; ⌞⌟≡𝟙ᵐ→≤𝟙 = λ where
      {p = 𝟘}  ok   → ⊥-elim (¬𝟘 _ ok)
      {p = ≤𝟙} ok   → ⊥-elim (¬≤𝟙 _ ok)
      {p = ≤ω} ok   → ⊥-elim (¬≤ω _ ok)
      {p = 𝟙}  _  _ → begin
        𝟙  ≡⟨⟩
        𝟙  ∎
  }
  where
  open Definition.Modality.Properties (linear-or-affine mrs)
  open Modality (linear-or-affine mrs) using (·-identityˡ)
  open Tools.Reasoning.PartialOrder ≤-poset
