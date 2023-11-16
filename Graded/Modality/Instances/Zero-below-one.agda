------------------------------------------------------------------------
-- A modality with 𝟘 < 𝟙
------------------------------------------------------------------------

module Graded.Modality.Instances.Zero-below-one where

import Tools.Algebra
open import Tools.Bool using (false)
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Product
open import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum

open import Graded.FullReduction.Assumptions
import Graded.Modality
import Graded.Modality.Properties.Has-well-behaved-zero
import Graded.Modality.Properties.Star as Star
open import Graded.Modality.Variant lzero

open import Definition.Typed.Restrictions
open import Definition.Untyped using (BMΣ; 𝕤; 𝕨)

private variable
  variant : Modality-variant
  R       : Type-restrictions _

import Graded.Usage.Restrictions

-- The modality has two grades, 𝟘 and 𝟙.

data Grade : Set where
  𝟘 𝟙 : Grade

open Graded.Usage.Restrictions     Grade
open Graded.Modality               Grade
open Tools.Algebra                 Grade

private variable
  p       : Grade
  UR      : Usage-restrictions

------------------------------------------------------------------------
-- Operators

-- Meet.
--
-- The meet operation is defined in such a way that 𝟘 ≤ 𝟙.

infixr 40 _∧_

_∧_ : Grade → Grade → Grade
𝟘 ∧ _ = 𝟘
𝟙 ∧ p = p

-- Addition.

infixr 40 _+_

_+_ : Grade → Grade → Grade
𝟘 + p = p
𝟙 + 𝟘 = 𝟙
𝟙 + 𝟙 = 𝟙

-- Multiplication.

infixr 45 _·_

_·_ : Grade → Grade → Grade
𝟙 · p = p
𝟘 · p = 𝟘

-- A star operator.

_⊛_▷_ : Grade → Grade → Grade → Grade
_ ⊛ _ ▷ _ = 𝟘

-- The inferred ordering relation.

infix 10 _≤_

_≤_ : Grade → Grade → Set
p ≤ q = p ≡ p ∧ q

-- A strict variant of the ordering relation.

infix 10 _<_

_<_ : Grade → Grade → Set
p < q = p ≤ q × p ≢ q

------------------------------------------------------------------------
-- Some properties

-- 𝟘 is the least grade.

𝟘≤ : ∀ p → 𝟘 ≤ p
𝟘≤ _ = refl

-- 𝟙 is the greatest grade.

≤𝟙 : p ≤ 𝟙
≤𝟙 {p = 𝟘} = refl
≤𝟙 {p = 𝟙} = refl

-- 𝟘 is strictly below 𝟙.

𝟘<𝟙 : 𝟘 < 𝟙
𝟘<𝟙 = 𝟘≤ 𝟙 , (λ ())

-- Multiplication is commutative.

·-comm : Commutative _·_
·-comm = λ where
  𝟘 𝟘 → refl
  𝟘 𝟙 → refl
  𝟙 𝟘 → refl
  𝟙 𝟙 → refl

-- Equality is decidable.

_≟_ : Decidable (_≡_ {A = Grade})
_≟_ = λ where
  𝟘 𝟘 → yes refl
  𝟘 𝟙 → no (λ ())
  𝟙 𝟘 → no (λ ())
  𝟙 𝟙 → yes refl

------------------------------------------------------------------------
-- The modality

-- A "semiring with meet" for Grade.

𝟘≤𝟙-semiring-with-meet : Semiring-with-meet
𝟘≤𝟙-semiring-with-meet = record
  { _+_          = _+_
  ; _·_          = _·_
  ; _∧_          = _∧_
  ; 𝟘            = 𝟘
  ; 𝟙            = 𝟙
  ; ω            = 𝟙
  ; ω≤𝟙          = refl
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
                (λ where
                   𝟘 → refl
                   𝟙 → refl)
              , (λ where
                   𝟘 → refl
                   𝟙 → refl)
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
              (λ where
                 𝟘 → refl
                 𝟙 → refl)
            , (λ where
                 𝟘 → refl
                 𝟙 → refl)
        }
      ; distrib = ·-distrib-+
      }
    ; zero =
          (λ where
             𝟘 → refl
             𝟙 → refl)
        , (λ where
             𝟘 → refl
             𝟙 → refl)
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
          𝟘 → refl
          𝟙 → refl
      }
    ; comm = ∧-comm
    }
  ; ·-distrib-∧ = ·-distrib-∧
  ; +-distrib-∧ = +-distrib-∧
  }
  where
  +-assoc : Associative _+_
  +-assoc = λ where
    𝟘 𝟘 𝟘 → refl
    𝟘 𝟘 𝟙 → refl
    𝟘 𝟙 𝟘 → refl
    𝟘 𝟙 𝟙 → refl
    𝟙 𝟘 𝟘 → refl
    𝟙 𝟘 𝟙 → refl
    𝟙 𝟙 𝟘 → refl
    𝟙 𝟙 𝟙 → refl

  +-comm : Commutative _+_
  +-comm = λ where
    𝟘 𝟘 → refl
    𝟘 𝟙 → refl
    𝟙 𝟘 → refl
    𝟙 𝟙 → refl

  ·-assoc : Associative _·_
  ·-assoc = λ where
    𝟘 𝟘 𝟘 → refl
    𝟘 𝟘 𝟙 → refl
    𝟘 𝟙 𝟘 → refl
    𝟘 𝟙 𝟙 → refl
    𝟙 𝟘 𝟘 → refl
    𝟙 𝟘 𝟙 → refl
    𝟙 𝟙 𝟘 → refl
    𝟙 𝟙 𝟙 → refl

  ·-distribˡ-+ : _·_ DistributesOverˡ _+_
  ·-distribˡ-+ = λ where
    𝟘 𝟘 𝟘 → refl
    𝟘 𝟘 𝟙 → refl
    𝟘 𝟙 𝟘 → refl
    𝟘 𝟙 𝟙 → refl
    𝟙 𝟘 𝟘 → refl
    𝟙 𝟘 𝟙 → refl
    𝟙 𝟙 𝟘 → refl
    𝟙 𝟙 𝟙 → refl

  ·-distrib-+ : _·_ DistributesOver _+_
  ·-distrib-+ =
    ·-distribˡ-+ , comm+distrˡ⇒distrʳ ·-comm ·-distribˡ-+

  ∧-assoc : Associative _∧_
  ∧-assoc = λ where
    𝟘 𝟘 𝟘 → refl
    𝟘 𝟘 𝟙 → refl
    𝟘 𝟙 𝟘 → refl
    𝟘 𝟙 𝟙 → refl
    𝟙 𝟘 𝟘 → refl
    𝟙 𝟘 𝟙 → refl
    𝟙 𝟙 𝟘 → refl
    𝟙 𝟙 𝟙 → refl

  ∧-comm : Commutative _∧_
  ∧-comm = λ where
    𝟘 𝟘 → refl
    𝟘 𝟙 → refl
    𝟙 𝟘 → refl
    𝟙 𝟙 → refl

  ·-distribˡ-∧ : _·_ DistributesOverˡ _∧_
  ·-distribˡ-∧ = λ where
    𝟘 𝟘 𝟘 → refl
    𝟘 𝟘 𝟙 → refl
    𝟘 𝟙 𝟘 → refl
    𝟘 𝟙 𝟙 → refl
    𝟙 𝟘 𝟘 → refl
    𝟙 𝟘 𝟙 → refl
    𝟙 𝟙 𝟘 → refl
    𝟙 𝟙 𝟙 → refl

  ·-distrib-∧ : _·_ DistributesOver _∧_
  ·-distrib-∧ =
    ·-distribˡ-∧ , comm+distrˡ⇒distrʳ ·-comm ·-distribˡ-∧

  +-distribˡ-∧ : _+_ DistributesOverˡ _∧_
  +-distribˡ-∧ = λ where
    𝟘 𝟘 𝟘 → refl
    𝟘 𝟘 𝟙 → refl
    𝟘 𝟙 𝟘 → refl
    𝟘 𝟙 𝟙 → refl
    𝟙 𝟘 𝟘 → refl
    𝟙 𝟘 𝟙 → refl
    𝟙 𝟙 𝟘 → refl
    𝟙 𝟙 𝟙 → refl

  +-distrib-∧ : _+_ DistributesOver _∧_
  +-distrib-∧ =
    +-distribˡ-∧ , comm+distrˡ⇒distrʳ +-comm +-distribˡ-∧

-- A natrec-star operator can be defined for Grade.

𝟘≤𝟙-has-star : Has-star 𝟘≤𝟙-semiring-with-meet
𝟘≤𝟙-has-star = record
  { _⊛_▷_                   = _⊛_▷_
  ; ⊛-ineq                  = (λ _ _ _ → refl) , (λ _ _ _ → refl)
  ; +-sub-interchangeable-⊛ = λ _ _ _ _ _ → refl
  ; ·-sub-distribʳ-⊛        = λ _ _ _ _ → refl
  ; ⊛-sub-distrib-∧         = λ _ → (λ _ _ _ → refl) , (λ _ _ _ → refl)
  }

-- The semiring does not have a well-behaved zero.

¬-𝟘≤𝟙-has-well-behaved-zero :
  ¬ Has-well-behaved-zero 𝟘≤𝟙-semiring-with-meet
¬-𝟘≤𝟙-has-well-behaved-zero well-behaved =
  ⊥-elim (𝟘≰𝟙 refl)
  where
  open Graded.Modality.Properties.Has-well-behaved-zero
         𝟘≤𝟙-semiring-with-meet ⦃ 𝟘-well-behaved = well-behaved ⦄

-- A modality for Grade (without 𝟘ᵐ).

𝟘≤𝟙 :
  (variant : Modality-variant) →
  let open Modality-variant variant in
  𝟘ᵐ-allowed ≡ false →
  Modality
𝟘≤𝟙 variant refl = record
  { variant            = variant
  ; semiring-with-meet = 𝟘≤𝟙-semiring-with-meet
  ; 𝟘-well-behaved     = λ ()
  ; has-nr             = λ _ → Star.has-nr _ ⦃ has-star = 𝟘≤𝟙-has-star ⦄
  }

------------------------------------------------------------------------
-- Instances of Full-reduction-assumptions

-- Instances of Type-restrictions (𝟘≤𝟙 variant ok) and
-- Usage-restrictions are suitable for the full reduction theorem if
-- * Unit-allowed does not hold or Starˢ-sink holds, and
-- * Σˢ-allowed 𝟘 p does not hold.

Suitable-for-full-reduction :
  ∀ variant ok → Type-restrictions (𝟘≤𝟙 variant ok) →
  Usage-restrictions → Set
Suitable-for-full-reduction _ _ TR UR =
  (¬ Unitˢ-allowed ⊎ Starˢ-sink) ×
  (∀ p → ¬ Σˢ-allowed 𝟘 p)
  where
  open Type-restrictions TR
  open Usage-restrictions UR

-- Given an instance of Type-restrictions (𝟘≤𝟙 variant ok) one can
-- create a "suitable" instance of Type-restrictions.

suitable-for-full-reduction :
  ∀ ok → Type-restrictions (𝟘≤𝟙 variant ok) →
  ∃ λ TR → (Suitable-for-full-reduction variant ok TR UR)
suitable-for-full-reduction refl R =
    record R
      { Unit-allowed =
          λ { 𝕤 → ⊥ ; 𝕨 → Unitʷ-allowed }
      ; ΠΣ-allowed = λ b p q →
          ΠΣ-allowed b p q × (b ≡ BMΣ 𝕤 → p ≡ 𝟙)
      ; []-cong-allowed =
          λ _ → ⊥
      ; []-cong→Erased =
          λ ()
      ; []-cong→¬Trivial =
          λ _ ()
      }
  , inj₁ idᶠ
  , (λ _ → (λ ()) ∘→ (_$ refl) ∘→ proj₂)
  where
  open Type-restrictions R

-- The full reduction assumptions hold for any instance of 𝟘≤𝟙 and any
-- "suitable" Type-restrictionsa and Usage-restrictions.

full-reduction-assumptions :
  ∀ ok {TR} →
  Suitable-for-full-reduction variant ok TR UR →
  Full-reduction-assumptions TR UR
full-reduction-assumptions refl (¬Unit⊎sink , ¬𝟘) = record
  { sink⊎𝟙≤𝟘    = case ¬Unit⊎sink of λ where
      (inj₁ ¬Unit) → ⊥-elim ∘→ ¬Unit
      (inj₂ sink) → λ _ → inj₁ sink
  ; ≡𝟙⊎𝟙≤𝟘 = λ where
      {p = 𝟘} ok → ⊥-elim (¬𝟘 _ ok)
      {p = 𝟙} _  → inj₁ refl
  }
