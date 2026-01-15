------------------------------------------------------------------------
-- The relevancy modality
------------------------------------------------------------------------

module Graded.Modality.Instances.Relevancy where

import Tools.Algebra
open import Tools.Bool using (Bool)
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat using (1+; Sequence)
open import Tools.PropositionalEquality
open import Tools.Product
import Tools.Reasoning.PropositionalEquality
import Tools.Reasoning.PartialOrder
open import Tools.Relation
open import Tools.Sum

import Graded.FullReduction.Assumptions
import Graded.Usage.Restrictions
import Definition.Typed.Restrictions
open import Definition.Untyped.NotParametrised

import Graded.Modality
import Graded.Modality.Properties.Addition as Addition
import Graded.Modality.Properties.Greatest-lower-bound as GLB
import Graded.Modality.Properties.Natrec as Natrec
import Graded.Modality.Properties.PartialOrder as PartialOrder
import Graded.Modality.Properties.Subtraction as Subtraction
import Graded.Mode.Instances.Zero-one.Variant
import Graded.Mode.Instances.Zero-one

------------------------------------------------------------------------
-- The type

-- Zero, at least one or many.

data Relevancy : Set where
  𝟘 ≥𝟙 ω : Relevancy

private variable
  p q r p₁ p₂ z z₁ z₂ s s₁ s₂ n : Relevancy
  pᵢ : Sequence Relevancy

open Graded.Modality Relevancy
open Tools.Algebra   Relevancy

-- A decision procedure for equality.

infix 10 _≟_

_≟_ : Decidable (_≡_ {A = Relevancy})
𝟘 ≟ 𝟘 = yes refl
𝟘 ≟ ≥𝟙 = no λ ()
𝟘 ≟ ω = no λ ()
≥𝟙 ≟ 𝟘 = no λ ()
≥𝟙 ≟ ≥𝟙 = yes refl
≥𝟙 ≟ ω = no λ ()
ω ≟ 𝟘 = no λ ()
ω ≟ ≥𝟙 = no λ ()
ω ≟ ω = yes refl

------------------------------------------------------------------------
-- Addition

-- Addition.

infixr 40 _+_

_+_ : Relevancy → Relevancy → Relevancy
𝟘 + q = q
≥𝟙 + q = ≥𝟙
ω + 𝟘 = ω
ω + ≥𝟙 = ≥𝟙
ω + ω = ω

opaque

  -- The value ≥𝟙 is a right zero for _+_.

  +-zeroʳ : RightZero ≥𝟙 _+_
  +-zeroʳ 𝟘 = refl
  +-zeroʳ ≥𝟙 = refl
  +-zeroʳ ω = refl

opaque

  -- The value ≥𝟙 is a zero for _+_.

  +-zero : Zero ≥𝟙 _+_
  +-zero = (λ _ → refl) , +-zeroʳ

------------------------------------------------------------------------
-- Multiplication

-- Multiplication.

infixr 45 _·_

_·_ : Relevancy → Relevancy → Relevancy
𝟘 · q = 𝟘
≥𝟙 · 𝟘 = 𝟘
≥𝟙 · ≥𝟙 = ≥𝟙
≥𝟙 · ω = ω
ω · 𝟘 = 𝟘
ω · ≥𝟙 = ω
ω · ω = ω

opaque

  -- Multiplication is idempotent.

  ·-idempotent : Idempotent _·_
  ·-idempotent 𝟘 = refl
  ·-idempotent ≥𝟙 = refl
  ·-idempotent ω = refl

opaque

  -- Multiplication is commutative.

  ·-comm : Commutative _·_
  ·-comm = λ where
    𝟘 𝟘 → refl
    𝟘 ≥𝟙 → refl
    𝟘 ω → refl
    ≥𝟙 𝟘 → refl
    ≥𝟙 ≥𝟙 → refl
    ≥𝟙 ω → refl
    ω 𝟘 → refl
    ω ≥𝟙 → refl
    ω ω → refl

opaque

  -- If p is not 𝟘, then ω · p is equal to ω.

  ω·≢𝟘 : p ≢ 𝟘 → ω · p ≡ ω
  ω·≢𝟘 {(𝟘)} 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 refl)
  ω·≢𝟘 {(≥𝟙)} _   = refl
  ω·≢𝟘 {(ω)} _   = refl

opaque

  -- If p is not 𝟘, then p · ω is equal to ω.

  ≢𝟘·ω : p ≢ 𝟘 → p · ω ≡ ω
  ≢𝟘·ω {(𝟘)} 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 refl)
  ≢𝟘·ω {(≥𝟙)} _ = refl
  ≢𝟘·ω {(ω)} _ = refl

------------------------------------------------------------------------
-- Meet

-- Meet.

infixr 43 _∧_

_∧_ : Relevancy → Relevancy → Relevancy
𝟘 ∧ 𝟘 = 𝟘
𝟘 ∧ ≥𝟙 = ω
𝟘 ∧ ω = ω
≥𝟙 ∧ 𝟘 = ω
≥𝟙 ∧ ≥𝟙 = ≥𝟙
≥𝟙 ∧ ω = ω
ω ∧ q = ω

-- The value ω is a right zero for _∧_.

∧-zeroʳ : RightZero ω _∧_
∧-zeroʳ 𝟘 = refl
∧-zeroʳ ≥𝟙 = refl
∧-zeroʳ ω = refl

-- The value ω is a zero for _∧_.

∧-zero : Zero ω _∧_
∧-zero = (λ _ → refl) , ∧-zeroʳ

------------------------------------------------------------------------
-- Ordering

-- The inferred ordering relation.

infix 10 _≤_

_≤_ : Relevancy → Relevancy → Set
p ≤ q = p ≡ p ∧ q

-- The quantity ω is smaller than all others.

ω≤ : ∀ p → ω ≤ p
ω≤ _ = refl

------------------------------------------------------------------------
-- The modality

-- The relevancy modality structure

relevancy-modality : Modality
relevancy-modality = record
  { _+_ = _+_
  ; _·_ = _·_
  ; _∧_ = _∧_
  ; 𝟘 = 𝟘
  ; 𝟙 = ≥𝟙
  ; ω = ω
  ; +-·-Semiring = record
    { isSemiringWithoutAnnihilatingZero = record
      { +-isCommutativeMonoid = record
        { isMonoid = record
          { isSemigroup = record
            { isMagma = record
              { isEquivalence = isEquivalence
              ; ∙-cong = cong₂ _+_
              }
            ; assoc = λ where
                𝟘 _ _  → refl
                ≥𝟙 _ _ → refl
                ω 𝟘 _  → refl
                ω ≥𝟙 _ → refl
                ω ω 𝟘  → refl
                ω ω ≥𝟙 → refl
                ω ω ω  → refl
            }
          ; identity =
                (λ _ → refl)
              , (comm∧idˡ⇒idʳ +-comm (λ _ → refl))
          }
        ; comm = +-comm
        }
      ; *-cong = cong₂ _·_
      ; *-assoc = λ where
            𝟘 _ _    → refl
            ≥𝟙 𝟘 _   → refl
            ≥𝟙 ≥𝟙 𝟘  → refl
            ≥𝟙 ≥𝟙 ≥𝟙 → refl
            ≥𝟙 ≥𝟙 ω  → refl
            ≥𝟙 ω 𝟘   → refl
            ≥𝟙 ω ≥𝟙  → refl
            ≥𝟙 ω ω   → refl
            ω 𝟘 r    → refl
            ω ≥𝟙 𝟘   → refl
            ω ≥𝟙 ≥𝟙  → refl
            ω ≥𝟙 ω   → refl
            ω ω 𝟘    → refl
            ω ω ≥𝟙   → refl
            ω ω ω    → refl
      ; *-identity =
              ·-identityˡ
            , comm∧idˡ⇒idʳ ·-comm ·-identityˡ
      ; distrib =
            ·-distrib-+ˡ
          , (comm∧distrˡ⇒distrʳ ·-comm ·-distrib-+ˡ)
      }
    ; zero =
          (λ _ → refl)
        , (comm∧zeˡ⇒zeʳ ·-comm (λ _ → refl))
    }
  ; ∧-Semilattice = record
    { isBand = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = isEquivalence
          ; ∙-cong = cong₂ _∧_
          }
        ; assoc = λ where
            𝟘 𝟘 𝟘    → refl
            𝟘 𝟘 ≥𝟙   → refl
            𝟘 𝟘 ω    → refl
            𝟘 ≥𝟙 𝟘   → refl
            𝟘 ≥𝟙 ≥𝟙  → refl
            𝟘 ≥𝟙 ω   → refl
            𝟘 ω _    → refl
            ≥𝟙 𝟘 𝟘   → refl
            ≥𝟙 𝟘 ≥𝟙  → refl
            ≥𝟙 𝟘 ω   → refl
            ≥𝟙 ≥𝟙 𝟘  → refl
            ≥𝟙 ≥𝟙 ≥𝟙 → refl
            ≥𝟙 ≥𝟙 ω  → refl
            ≥𝟙 ω _   → refl
            ω _ _    → refl
        }
      ; idem = λ where
          𝟘  → refl
          ≥𝟙 → refl
          ω  → refl
      }
    ; comm = ∧-comm
    }
  ; ·-distrib-∧ =
        ·-distrib-∧ˡ
      , comm∧distrˡ⇒distrʳ ·-comm ·-distrib-∧ˡ
  ; +-distrib-∧ =
        +-distrib-∧ˡ
      , comm∧distrˡ⇒distrʳ +-comm +-distrib-∧ˡ
  ; ω≤𝟙 = refl
  ; ω·+≤ω·ʳ = ω·+≤ω·ʳ _ _
  ; is-𝟘? = _≟ 𝟘
  }
  where

  +-comm : Commutative _+_
  +-comm = λ where
    𝟘 𝟘   → refl
    𝟘 ≥𝟙  → refl
    𝟘 ω   → refl
    ≥𝟙 𝟘  → refl
    ≥𝟙 ≥𝟙 → refl
    ≥𝟙 ω  → refl
    ω 𝟘   → refl
    ω ≥𝟙  → refl
    ω ω   → refl

  ·-identityˡ : LeftIdentity ≥𝟙 _·_
  ·-identityˡ = λ where
    𝟘  → refl
    ≥𝟙 → refl
    ω  → refl

  ·-distrib-+ˡ : _·_ DistributesOverˡ _+_
  ·-distrib-+ˡ = λ where
    𝟘 _ _   → refl
    ≥𝟙 𝟘 _  → refl
    ≥𝟙 ≥𝟙 _ → refl
    ≥𝟙 ω 𝟘  → refl
    ≥𝟙 ω ≥𝟙 → refl
    ≥𝟙 ω ω  → refl
    ω 𝟘 _   → refl
    ω ≥𝟙 𝟘  → refl
    ω ≥𝟙 ≥𝟙 → refl
    ω ≥𝟙 ω  → refl
    ω ω 𝟘   → refl
    ω ω ≥𝟙  → refl
    ω ω ω   → refl

  ∧-comm : Commutative _∧_
  ∧-comm = λ where
    𝟘 𝟘   → refl
    𝟘 ≥𝟙  → refl
    𝟘 ω   → refl
    ≥𝟙 𝟘  → refl
    ≥𝟙 ≥𝟙 → refl
    ≥𝟙 ω  → refl
    ω 𝟘   → refl
    ω ≥𝟙  → refl
    ω ω   → refl

  ·-distrib-∧ˡ : _·_ DistributesOverˡ _∧_
  ·-distrib-∧ˡ = λ where
    𝟘 _ _    → refl
    ≥𝟙 𝟘 𝟘   → refl
    ≥𝟙 𝟘 ≥𝟙  → refl
    ≥𝟙 𝟘 ω   → refl
    ≥𝟙 ≥𝟙 𝟘  → refl
    ≥𝟙 ≥𝟙 ≥𝟙 → refl
    ≥𝟙 ≥𝟙 ω  → refl
    ≥𝟙 ω _   → refl
    ω 𝟘 𝟘    → refl
    ω 𝟘 ≥𝟙   → refl
    ω 𝟘 ω    → refl
    ω ≥𝟙 𝟘   → refl
    ω ≥𝟙 ≥𝟙  → refl
    ω ≥𝟙 ω   → refl
    ω ω _    → refl

  +-distrib-∧ˡ : _+_ DistributesOverˡ _∧_
  +-distrib-∧ˡ = λ where
    𝟘 _ _   → refl
    ≥𝟙 _ _  → refl
    ω 𝟘 𝟘   → refl
    ω 𝟘 ≥𝟙  → refl
    ω 𝟘 ω   → refl
    ω ≥𝟙 𝟘  → refl
    ω ≥𝟙 ≥𝟙 → refl
    ω ≥𝟙 ω  → refl
    ω ω _   → refl

  ω·+≤ω·ʳ : ∀ p q → ω · (p + q) ≤ ω · q
  ω·+≤ω·ʳ = λ where
    𝟘 𝟘  → refl
    𝟘 ≥𝟙 → refl
    𝟘 ω  → refl
    ≥𝟙 _ → refl
    ω 𝟘  → refl
    ω ≥𝟙 → refl
    ω ω  → refl

open Modality relevancy-modality
  hiding (_+_;_·_;_∧_;𝟘;ω;_≤_)
open Addition relevancy-modality
open GLB relevancy-modality
open Natrec relevancy-modality
open PartialOrder relevancy-modality
open Subtraction relevancy-modality

-- The modality has a well-behaved zero

instance
  relevancy-has-well-behaved-zero :
    Has-well-behaved-zero relevancy-modality
  relevancy-has-well-behaved-zero = record
    { non-trivial = λ ()
    ; zero-product = zero-product _ _
    ; +-positiveˡ = +-positive _ _
    ; ∧-positiveˡ = ∧-positive _ _
    }
    where

    zero-product : ∀ p q → p · q ≡ 𝟘 → p ≡ 𝟘 ⊎ q ≡ 𝟘
    zero-product 𝟘 q _ = inj₁ refl
    zero-product p 𝟘 _ = inj₂ refl
    zero-product ≥𝟙 ≥𝟙 ()
    zero-product ≥𝟙 ω ()
    zero-product ω ≥𝟙 ()
    zero-product ω ω ()

    +-positive : ∀ p q → p + q ≡ 𝟘 → p ≡ 𝟘
    +-positive 𝟘 q _ = refl
    +-positive ≥𝟙 q ()
    +-positive ω 𝟘 ()
    +-positive ω ≥𝟙 ()
    +-positive ω ω ()

    ∧-positive : ∀ p q → p ∧ q ≡ 𝟘 → p ≡ 𝟘
    ∧-positive 𝟘 q _ = refl
    ∧-positive ≥𝟙 𝟘 ()
    ∧-positive ≥𝟙 ≥𝟙 ()
    ∧-positive ≥𝟙 ω ()
    ∧-positive ω q ()

------------------------------------------------------------------------
-- Subtraction

opaque

  -- Subtraction of ω by anything is ω

  ω-p≡ω : ∀ p → ω - p ≡ ω
  ω-p≡ω p = ∞-p≡∞ refl p

opaque

  -- Subtraction of ≥𝟙 by ω is ≥𝟙

  ≥𝟙-ω≡≥𝟙 : ≥𝟙 - ω ≡ ≥𝟙
  ≥𝟙-ω≡≥𝟙 = refl , λ { 𝟘 () ; ≥𝟙 _ → refl ; ω ()}

opaque

  -- Subtraction of ≥𝟙 by ≥𝟙 is ω

  ≥𝟙-≥𝟙≡ω : ≥𝟙 - ≥𝟙 ≡ ω
  ≥𝟙-≥𝟙≡ω = refl , λ _ _ → refl

opaque

  -- The modality supports subtraction with
  --   ω - p ≡ ω for all p
  --   p - 𝟘 ≡ p for all p
  --   ≥𝟙 - ≥𝟙 ≡ ω
  --   ≥𝟙 - ω ≡ ≥𝟙
  -- and not defined otherwise

  relevancy-supports-subtraction : Supports-subtraction
  relevancy-supports-subtraction {p} {(𝟘)} {r} _ =
    _ , p-𝟘≡p
  relevancy-supports-subtraction {(ω)} {q} {r} _ =
    _ , ω-p≡ω q
  relevancy-supports-subtraction {(≥𝟙)} {(≥𝟙)} {(r)} _ =
    _ , ≥𝟙-≥𝟙≡ω
  relevancy-supports-subtraction {(≥𝟙)} {(ω)} {(r)} _ =
    _ , ≥𝟙-ω≡≥𝟙
  relevancy-supports-subtraction {(𝟘)} {(≥𝟙)} {(𝟘)} ()
  relevancy-supports-subtraction {(𝟘)} {(≥𝟙)} {(≥𝟙)} ()
  relevancy-supports-subtraction {(𝟘)} {(≥𝟙)} {(ω)} ()
  relevancy-supports-subtraction {(𝟘)} {(ω)} {(𝟘)} ()
  relevancy-supports-subtraction {(𝟘)} {(ω)} {(≥𝟙)} ()
  relevancy-supports-subtraction {(𝟘)} {(ω)} {(ω)} ()

-- An alternative definition of the subtraction relation with
--   ω - p ≡ ω for all p
--   p - 𝟘 ≡ p for all p
--   ≥𝟙 - ≥𝟙 ≡ ω
--   ≥𝟙 - ω ≡ ≥𝟙
-- and not defined otherwise

data _-_≡′_ : (p q r : Relevancy) → Set where
  ω-p≡′ω : ω - p ≡′ ω
  p-𝟘≡′p : p - 𝟘 ≡′ p
  ≥𝟙-≥𝟙≡′ω : ≥𝟙 - ≥𝟙 ≡′ ω
  ≥𝟙-ω≡′≥𝟙 : ≥𝟙 - ω ≡′ ≥𝟙

opaque

  -- The two subtraction relations are equivalent.

  -≡↔-≡′ : ∀ p q r → (p - q ≡ r) ⇔ (p - q ≡′ r)
  -≡↔-≡′ p q r = left p q r , right
    where
    left : ∀ p q r → p - q ≡ r → p - q ≡′ r
    left ω q r p-q≡r =
      case -≡-functional {q = q} p-q≡r (ω-p≡ω q) of λ where
        refl →
          ω-p≡′ω
    left p 𝟘 r p-q≡r =
      case -≡-functional p-q≡r p-𝟘≡p of λ where
        refl →
          p-𝟘≡′p
    left 𝟘 q r p-q≡r =
      case 𝟘-p≡q p-q≡r of λ where
        (refl , refl) →
          p-𝟘≡′p
    left ≥𝟙 ≥𝟙 r p-q≡r =
      case -≡-functional p-q≡r ≥𝟙-≥𝟙≡ω of λ where
        refl →
          ≥𝟙-≥𝟙≡′ω
    left ≥𝟙 ω r p-q≡r =
      case -≡-functional p-q≡r ≥𝟙-ω≡≥𝟙 of λ where
        refl →
          ≥𝟙-ω≡′≥𝟙
    right : p - q ≡′ r → p - q ≡ r
    right ω-p≡′ω = ω-p≡ω q
    right p-𝟘≡′p = p-𝟘≡p
    right ≥𝟙-≥𝟙≡′ω = ≥𝟙-≥𝟙≡ω
    right ≥𝟙-ω≡′≥𝟙 = ≥𝟙-ω≡≥𝟙

------------------------------------------------------------------------
-- Natrec

-- A function used to compute usage for natrec

nr₃ : (r z s : Relevancy) → Relevancy
nr₃ 𝟘 z s = z ∧ s
nr₃ ≥𝟙 z s = ω · s + z
nr₃ ω z s = z ∧ s

opaque

  -- Addition is sub-interchangeable with nr₃ r.

  nr₃-+ : ∀ r → nr₃ r z₁ s₁ + nr₃ r z₂ s₂ ≤ nr₃ r (z₁ + z₂) (s₁ + s₂)
  nr₃-+ {z₁} {s₁} {z₂} {s₂} 𝟘 = +-sub-interchangeable-∧ z₁ s₁ z₂ s₂
  nr₃-+ {z₁} {s₁} {z₂} {s₂} ≥𝟙 = begin
    (ω · s₁ + z₁) + ω · s₂ + z₂ ≡⟨ +-sub-interchangeable-+ (ω · s₁) z₁ (ω · s₂) z₂ ⟩
    (ω · s₁ + ω · s₂) + z₁ + z₂ ≡˘⟨ +-congʳ (·-distribˡ-+ ω s₁ s₂) ⟩
    ω · (s₁ + s₂) + z₁ + z₂     ∎
    where
    open Tools.Reasoning.PartialOrder ≤-poset
  nr₃-+ {z₁} {s₁} {z₂} {s₂} ω = +-sub-interchangeable-∧ z₁ s₁ z₂ s₂

opaque

  -- The function nr₃ computes greatest lower bounds of nrᵢ sequences.

  nr₃-nrᵢ-GLB :
    ∀ r → Greatest-lower-bound (nr₃ r p q) (nrᵢ r p q)
  nr₃-nrᵢ-GLB = λ where
      𝟘  → nrᵢ-𝟘-GLB
      ≥𝟙 → lemma-≥𝟙 _ _
      ω  → lemma-ω _ _
    where
    open Tools.Reasoning.PropositionalEquality
    lemma : ∀ i → nrᵢ r p q i ≡ ω → Greatest-lower-bound ω (nrᵢ r p q)
    lemma i nrᵢ≡ω =
        (λ _ → refl)
      , (λ q q≤ → ≤-trans (q≤ i) (≤-reflexive nrᵢ≡ω))
    lemma-≥𝟙 : ∀ p q → Greatest-lower-bound (nr₃ ≥𝟙 p q) (nrᵢ ≥𝟙 p q)
    lemma-≥𝟙 p 𝟘 = GLB-const lemma′
      where
      lemma′ : ∀ i → nrᵢ ≥𝟙 p 𝟘 i ≡ p
      lemma′ 0 = refl
      lemma′ (1+ i) = begin
        nrᵢ ≥𝟙 p 𝟘 (1+ i) ≡⟨⟩
        ≥𝟙 · nrᵢ ≥𝟙 p 𝟘 i ≡⟨ ·-identityˡ _ ⟩
        nrᵢ ≥𝟙 p 𝟘 i      ≡⟨ lemma′ i ⟩
        p                 ∎
    lemma-≥𝟙 𝟘 ≥𝟙 =
        (λ _ → refl)
      , λ { 𝟘 q≤ → case q≤ 1 of λ ()
          ; ≥𝟙 q≤ → case q≤ 0 of λ ()
          ; ω q≤ → refl}
    lemma-≥𝟙 ≥𝟙 ≥𝟙 = GLB-const lemma′
      where
      lemma′ : ∀ i → nrᵢ ≥𝟙 ≥𝟙 ≥𝟙 i ≡ ≥𝟙
      lemma′ 0 = refl
      lemma′ (1+ i) = begin
        nrᵢ ≥𝟙 ≥𝟙 ≥𝟙 (1+ i)      ≡⟨⟩
        ≥𝟙 + ≥𝟙 · nrᵢ ≥𝟙 ≥𝟙 ≥𝟙 i ≡⟨ +-congˡ {≥𝟙} (·-congˡ {≥𝟙} (lemma′ i)) ⟩
        ≥𝟙 + ≥𝟙 · ≥𝟙             ≡⟨⟩
        ≥𝟙                       ∎
    lemma-≥𝟙 ω ≥𝟙 = lemma 0 refl
    lemma-≥𝟙 𝟘 ω = lemma 1 refl
    lemma-≥𝟙 ≥𝟙 ω = GLB-const lemma′
      where
      lemma′ : ∀ i → nrᵢ ≥𝟙 ≥𝟙 ω i ≡ ≥𝟙
      lemma′ 0 = refl
      lemma′ (1+ i) = begin
        nrᵢ ≥𝟙 ≥𝟙 ω (1+ i)     ≡⟨⟩
        ω + ≥𝟙 · nrᵢ ≥𝟙 ≥𝟙 ω i ≡⟨ +-congˡ {ω} (·-congˡ {≥𝟙} (lemma′ i)) ⟩
        ω + ≥𝟙 · ≥𝟙            ≡⟨⟩
        ≥𝟙                     ∎
    lemma-≥𝟙 ω ω = lemma 0 refl
    lemma-ω : ∀ p q → Greatest-lower-bound (nr₃ ω p q) (nrᵢ ω p q)
    lemma-ω 𝟘 𝟘 = GLB-nrᵢ-𝟘
    lemma-ω ≥𝟙 𝟘 = lemma 1 refl
    lemma-ω ω 𝟘 = lemma 0 refl
    lemma-ω 𝟘 ≥𝟙 =
        (λ _ → refl)
      , (λ { 𝟘 q≤ → case q≤ 1 of λ ()
           ; ≥𝟙 q≤ → case q≤ 0 of λ ()
           ; ω q≤ → refl})
    lemma-ω ≥𝟙 ≥𝟙 = GLB-const lemma′
      where
      lemma′ : ∀ i → nrᵢ ω ≥𝟙 ≥𝟙 i ≡ ≥𝟙
      lemma′ 0 = refl
      lemma′ (1+ i) = begin
        nrᵢ ω ≥𝟙 ≥𝟙 (1+ i)     ≡⟨⟩
        ≥𝟙 + ω · nrᵢ ω ≥𝟙 ≥𝟙 i ≡⟨ +-congˡ {≥𝟙} (·-congˡ {ω} (lemma′ i)) ⟩
        ≥𝟙 + ω · ≥𝟙            ≡⟨⟩
        ≥𝟙                     ∎
    lemma-ω ω ≥𝟙 = lemma 0 refl
    lemma-ω 𝟘 ω = lemma 1 refl
    lemma-ω ≥𝟙 ω = lemma 1 refl
    lemma-ω ω ω = lemma 0 refl

opaque

  ≥𝟙-GLB-inv :
    Greatest-lower-bound ≥𝟙 pᵢ → ∀ i → pᵢ i ≡ ≥𝟙
  ≥𝟙-GLB-inv (≤p , p-glb) i = lemma _ (≤p i)
    where
    lemma : ∀ p → ≥𝟙 ≤ p → p ≡ ≥𝟙
    lemma 𝟘 ()
    lemma ≥𝟙 _ = refl
    lemma ω ()

opaque instance

  -- The modality has well-behaved GLBs.

  relevancy-supports-glb-for-natrec :
    Has-well-behaved-GLBs relevancy-modality
  relevancy-supports-glb-for-natrec = record
    { +-GLBˡ = +-GLB _ _
    ; ·-GLBˡ = ·-GLB _ _
    ; ·-GLBʳ = comm∧·-GLBˡ⇒·-GLBʳ ·-comm (·-GLB _ _)
    ; +nrᵢ-GLB = +nrᵢ-GLB
    }
    where
    +-GLB :
      ∀ p q →
      Greatest-lower-bound p pᵢ →
      Greatest-lower-bound (q + p) (λ i → q + pᵢ i)
    +-GLB p 𝟘 p-glb = p-glb
    +-GLB p ≥𝟙 p-glb = GLB-const′
    +-GLB 𝟘 ω p-glb =
      GLB-const (λ i → trans (+-congˡ (𝟘-GLB-inv p-glb i)) (+-identityʳ _))
    +-GLB ≥𝟙 ω p-glb =
      GLB-const (λ i → +-congˡ (≥𝟙-GLB-inv p-glb i))
    +-GLB {pᵢ} ω ω p-glb =
        (λ _ → refl)
      , (λ { 𝟘 q≤ → ⊥-elim (lemma₁ (pᵢ 0) (q≤ 0))
           ; ≥𝟙 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma₂ _ ∘→ q≤))
           ; ω q≤ → refl})
      where
      lemma₁ : ∀ p → 𝟘 ≤ ω + p → ⊥
      lemma₁ 𝟘 ()
      lemma₁ ≥𝟙 ()
      lemma₁ ω ()
      lemma₂ : ∀ p → ≥𝟙 ≤ ω + p → p ≡ ≥𝟙
      lemma₂ 𝟘 ()
      lemma₂ ≥𝟙 _ = refl
      lemma₂ ω ()

    ·-GLB :
      ∀ p q →
      Greatest-lower-bound p pᵢ →
      Greatest-lower-bound (q · p) (λ i → q · pᵢ i)
    ·-GLB p 𝟘 p-glb = GLB-const′
    ·-GLB p ≥𝟙 p-glb =
      GLB-cong (sym (·-identityˡ _))
        (λ _ → sym (·-identityˡ _))
        p-glb
    ·-GLB 𝟘 ω p-glb =
      GLB-const λ i → ·-congˡ (𝟘-GLB-inv p-glb i)
    ·-GLB ≥𝟙 ω p-glb =
      GLB-const λ i → ·-congˡ (≥𝟙-GLB-inv p-glb i)
    ·-GLB ω ω p-glb =
        (λ i → refl)
      , (λ { 𝟘 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma₁ _ ∘→ q≤))
           ; ≥𝟙 q≤ → ⊥-elim (lemma₂ _ (q≤ 0))
           ; ω q≤ → refl})
      where
      lemma₁ : ∀ p → 𝟘 ≤ ω · p → p ≡ 𝟘
      lemma₁ 𝟘 _ = refl
      lemma₁ ≥𝟙 ()
      lemma₁ ω ()
      lemma₂ : ∀ p → ≥𝟙 ≤ ω · p → ⊥
      lemma₂ 𝟘 ()
      lemma₂ ≥𝟙 ()
      lemma₂ ω ()

    open Tools.Reasoning.PartialOrder ≤-poset
    +nrᵢ-GLB :
      Greatest-lower-bound p₁ (nrᵢ r z₁ s₁) →
      Greatest-lower-bound p₂ (nrᵢ r z₂ s₂) →
      ∃ λ q → Greatest-lower-bound q (nrᵢ r (z₁ + z₂) (s₁ + s₂)) ×
          p₁ + p₂ ≤ q
    +nrᵢ-GLB {p₁} {r} {z₁} {s₁} {p₂} {z₂} {s₂} p₁-glb p₂-glb =
      _ , nr₃-nrᵢ-GLB r , (begin
      p₁ + p₂                   ≡⟨ +-cong (GLB-unique p₁-glb (nr₃-nrᵢ-GLB r))
                                    (GLB-unique p₂-glb (nr₃-nrᵢ-GLB r)) ⟩
      nr₃ r z₁ s₁ + nr₃ r z₂ s₂ ≤⟨ nr₃-+ r ⟩
      nr₃ r (z₁ + z₂) (s₁ + s₂) ∎)

opaque instance

  -- The modality has an nr function

  relevancy-has-nr : Has-nr relevancy-modality
  relevancy-has-nr =
    nrᵢ-GLB→nr λ r _ _ → _ , nr₃-nrᵢ-GLB r

opaque
  unfolding relevancy-has-nr

  instance

    -- The nr function is factoring

    relevancy-has-factoring-nr : Is-factoring-nr relevancy-has-nr
    relevancy-has-factoring-nr =
      nrᵢ-GLB→nr-factoring (λ r _ _ → _ , nr₃-nrᵢ-GLB r)

opaque
  unfolding relevancy-has-nr nrᵢ-GLB→nr

  -- The nr function can be expressed using the function nr₃

  nr≡ : Has-nr.nr relevancy-has-nr p r z s n ≡ nr₃ r ≥𝟙 p · n + nr₃ r z s
  nr≡ = refl

opaque

  -- The nr function does not satisfy Linearity-like-nr-for-𝟘.

  not-nr-linearity-like-for-𝟘 :
    ¬ Has-nr.Linearity-like-nr-for-𝟘 relevancy-has-nr
  not-nr-linearity-like-for-𝟘 ass =
    case trans (sym (nr≡ {𝟘} {𝟘} {𝟘} {≥𝟙} {≥𝟙})) (ass {𝟘} {𝟘} {≥𝟙} {≥𝟙}) of λ ()

opaque

  -- The nr function satisfies Linearity-like-nr-for-𝟙.

  nr-linearity-like-for-𝟙 :
    Has-nr.Linearity-like-nr-for-𝟙 relevancy-has-nr
  nr-linearity-like-for-𝟙 {p} {z} {s} {n} = begin
    nr p ≥𝟙 z s n                 ≡⟨ nr≡ ⟩
    nr₃ ≥𝟙 ≥𝟙 p · n + nr₃ ≥𝟙 z s  ≡⟨⟩
    (ω · p + ≥𝟙) · n + ω · s + z  ≡⟨ +-congʳ (·-congʳ (+-comm (ω · p) ≥𝟙)) ⟩
    (≥𝟙 + ω · p) · n + ω · s + z  ≡⟨⟩
    ≥𝟙 · n + ω · s + z            ∎
    where
    open Tools.Reasoning.PropositionalEquality
    nr : (p r z s n : Relevancy) → Relevancy
    nr = Has-nr.nr relevancy-has-nr

------------------------------------------------------------------------
-- Full reduction

module _ {𝟘ᵐ-allowed : Bool} where

  open Graded.Mode.Instances.Zero-one.Variant relevancy-modality

  private
    𝕄 : Modality
    𝕄 = relevancy-modality

    variant : Mode-variant
    variant = record
      { 𝟘ᵐ-allowed = 𝟘ᵐ-allowed
      ; 𝟘-well-behaved = λ _ → relevancy-has-well-behaved-zero
      }

  open Graded.FullReduction.Assumptions variant
  open Graded.Mode.Instances.Zero-one variant
  open Graded.Usage.Restrictions 𝕄 Zero-one-isMode
  open Definition.Typed.Restrictions 𝕄

  private variable
    TR : Type-restrictions
    UR : Usage-restrictions

  -- Instances of Type-restrictions and Usage-restrictions are suitable
  -- for the full reduction theorem if
  -- * whenever Unitˢ-allowed holds, then Starˢ-sink holds,
  -- * Unitʷ-allowed and Unitʷ-η do not both hold,
  -- * Σˢ-allowed 𝟘 p does not hold, and
  -- * Σˢ-allowed ω p does not hold.

  Suitable-for-full-reduction : Type-restrictions → Usage-restrictions → Set
  Suitable-for-full-reduction TR UR =
    (Unitˢ-allowed → Starˢ-sink) ×
    (Unitʷ-allowed → ¬ Unitʷ-η) ×
    (∀ p → ¬ Σˢ-allowed 𝟘 p) ×
    (∀ p → ¬ Σˢ-allowed ω p)
    where
    open Type-restrictions TR
    open Usage-restrictions UR

  -- Given an instance of Type-restrictions one can create a "suitable"
  -- instance.

  suitable-for-full-reduction :
    Type-restrictions → ∃ λ TR → Suitable-for-full-reduction TR UR
  suitable-for-full-reduction {UR} TR =
      record TR
        { Unit-allowed = λ where
            𝕨 → Unitʷ-allowed × ¬ Unitʷ-η
            𝕤 → Unitˢ-allowed × Starˢ-sink
        ; ΠΣ-allowed = λ b p q →
            ΠΣ-allowed b p q × (b ≡ BMΣ 𝕤 → p ≡ 𝟙)
        ; []-cong-allowed = λ where
            𝕨 → []-congʷ-allowed × ¬ Unitʷ-η
            𝕤 → ⊥
        ; []-cong→Erased = λ where
            {s = 𝕨} (ok , no-η) →
                ([]-cong→Erased ok .proj₁ , no-η)
              , []-cong→Erased ok .proj₂
              , λ ()
            {s = 𝕤} ()
        ; []-cong→¬Trivial = λ { {s = 𝕨} _ (); {s = 𝕤} () }
        }
    , proj₂
    , proj₂
    , (λ _ → ((λ ()) ∘→ (_$ refl)) ∘→ proj₂)
    , (λ _ → ((λ ()) ∘→ (_$ refl)) ∘→ proj₂)
    where
    open Type-restrictions TR
    open Usage-restrictions UR

  -- The full reduction assumptions hold for linearityModality and any
  -- "suitable" Type-restrictions and Usage-restrictions.

  full-reduction-assumptions :
    Suitable-for-full-reduction TR UR →
    Full-reduction-assumptions TR UR
  full-reduction-assumptions (sink , no-η , ¬𝟘 , ¬ω) = record
    { sink⊎𝟙≤𝟘 = λ where
        {s = 𝕤} ok _         → inj₁ (refl , sink ok)
        {s = 𝕨} _  (inj₁ ())
        {s = 𝕨} ok (inj₂ η)  → ⊥-elim (no-η ok η)
    ; ≡𝟙⊎𝟙≤𝟘   = λ where
        {p = 𝟘} ok → ⊥-elim (¬𝟘 _ ok)
        {p = ω} ok → ⊥-elim (¬ω _ ok)
        {p = ≥𝟙} _  → inj₁ refl
    }

  -- Type and usage restrictions that satisfy the full reduction
  -- assumptions are "suitable".

  full-reduction-assumptions-suitable :
    Full-reduction-assumptions TR UR → Suitable-for-full-reduction TR UR
  full-reduction-assumptions-suitable {UR} as =
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
    where
    open Full-reduction-assumptions _ _ as
    open Usage-restrictions UR
