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
import Graded.Mode.Instances.Zero-one.Variant
import Graded.Mode.Instances.Zero-one
open import Graded.Usage.Restrictions

open import Definition.Typed.Restrictions
open import Definition.Untyped using (BMΣ; 𝕤; 𝕨)

private variable
  R       : Type-restrictions _
  UR      : Usage-restrictions _ _

-- The modality has two grades, 𝟘 and 𝟙.

data Grade : Set where
  𝟘 𝟙 : Grade

open Graded.Modality Grade
open Tools.Algebra   Grade

private variable
  p : Grade

------------------------------------------------------------------------
-- Operators

-- Meet.
--
-- The meet operation is defined in such a way that 𝟘 ≤ 𝟙.

infixr 43 _∧_

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
  { _+_     = _+_
  ; _·_     = _·_
  ; _∧_     = _∧_
  ; 𝟘       = 𝟘
  ; 𝟙       = 𝟙
  ; ω       = 𝟘
  ; ω≤𝟙     = refl
  ; ω·+≤ω·ʳ = refl
  ; is-𝟘?   = λ where
      𝟘 → yes refl
      𝟙 → no (λ ())
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
      ; *-cong = cong₂ _·_
      ; *-assoc = ·-assoc
      ; *-identity =
              (λ where
                 𝟘 → refl
                 𝟙 → refl)
            , (λ where
                 𝟘 → refl
                 𝟙 → refl)
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
    ·-distribˡ-+ , comm∧distrˡ⇒distrʳ ·-comm ·-distribˡ-+

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
    ·-distribˡ-∧ , comm∧distrˡ⇒distrʳ ·-comm ·-distribˡ-∧

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
    +-distribˡ-∧ , comm∧distrˡ⇒distrʳ +-comm +-distribˡ-∧

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

-- A modality for Grade.

𝟘≤𝟙 : Modality
𝟘≤𝟙 = record
  { semiring-with-meet = 𝟘≤𝟙-semiring-with-meet
  }

------------------------------------------------------------------------
-- Instances of Full-reduction-assumptions

open Graded.Mode.Instances.Zero-one.Variant 𝟘≤𝟙

private
  variant : Mode-variant
  variant = record
    { 𝟘ᵐ-allowed = false ; 𝟘-well-behaved = λ () }

open Graded.Mode.Instances.Zero-one variant

-- Instances of Type-restrictions 𝟘≤𝟙 and
-- Usage-restrictions are suitable for the full reduction theorem if
-- * whenever Unitˢ-allowed holds, then Starˢ-sink holds,
-- * Unitʷ-allowed and Unitʷ-η do not both hold, and
-- * Σˢ-allowed 𝟘 p does not hold.

Suitable-for-full-reduction :
  Type-restrictions 𝟘≤𝟙 →
  Usage-restrictions 𝟘≤𝟙 Zero-one-isMode →
  Set
Suitable-for-full-reduction TR UR =
  (Unitˢ-allowed → Starˢ-sink) ×
  (Unitʷ-allowed → ¬ Unitʷ-η) ×
  (∀ p → ¬ Σˢ-allowed 𝟘 p)
  where
  open Type-restrictions TR
  open Usage-restrictions UR

-- Given an instance of Type-restrictions 𝟘≤𝟙 one can
-- create a "suitable" instance of Type-restrictions.

suitable-for-full-reduction :
  ∀ {UR} → Type-restrictions 𝟘≤𝟙 →
  ∃ λ TR → (Suitable-for-full-reduction TR UR)
suitable-for-full-reduction {UR} R =
    record R
      { Unit-allowed = λ where
          𝕤 → Unitˢ-allowed × Starˢ-sink
          𝕨 → Unitʷ-allowed × ¬ Unitʷ-η
      ; ΠΣ-allowed = λ b p q →
          ΠΣ-allowed b p q × (b ≡ BMΣ 𝕤 → p ≡ 𝟙)
      ; []-cong-allowed =
          λ _ → ⊥
      ; []-cong→Erased =
          λ ()
      ; []-cong→¬Trivial =
          λ _ ()
      }
  , proj₂
  , proj₂
  , (λ _ → (λ ()) ∘→ (_$ refl) ∘→ proj₂)
  where
  open Type-restrictions R
  open Usage-restrictions UR

-- The full reduction assumptions hold for any instance of 𝟘≤𝟙 and any
-- "suitable" Type-restrictions and Usage-restrictions.

full-reduction-assumptions :
  ∀ {TR UR} →
  Suitable-for-full-reduction TR UR →
  Full-reduction-assumptions variant TR UR
full-reduction-assumptions (sink , no-η , ¬𝟘) = record
  { sink⊎𝟙≤𝟘 = λ where
      {s = 𝕤} ok _         → inj₁ (refl , sink ok)
      {s = 𝕨} _  (inj₁ ())
      {s = 𝕨} ok (inj₂ η)  → ⊥-elim (no-η ok η)
  ; ≡𝟙⊎𝟙≤𝟘 = λ where
      {p = 𝟘} ok → ⊥-elim (¬𝟘 _ ok)
      {p = 𝟙} _  → inj₁ refl
  }

-- Type and usage restrictions that satisfy the full reduction
-- assumptions are "suitable".

full-reduction-assumptions-suitable :
  ∀ {UR} {TR : Type-restrictions 𝟘≤𝟙} →
  Full-reduction-assumptions variant TR UR →
  Suitable-for-full-reduction TR UR
full-reduction-assumptions-suitable {UR = UR} as =
    (λ ok → case sink⊎𝟙≤𝟘 ok (inj₁ refl) of λ where
       (inj₁ (_ , sink)) → sink
       (inj₂ ()))
  , (λ ok η → case sink⊎𝟙≤𝟘 ok (inj₂ η) of λ where
       (inj₁ (() , _))
       (inj₂ ()))
  , λ p Σ-ok → case ≡𝟙⊎𝟙≤𝟘 Σ-ok of λ where
     (inj₁ ())
     (inj₂ (_ , ok , _)) → ok
  where
  open Full-reduction-assumptions as
  open Usage-restrictions UR
