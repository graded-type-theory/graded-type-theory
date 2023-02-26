------------------------------------------------------------------------
-- The zero-one-many modality
------------------------------------------------------------------------

-- Based on Conor McBride's "I Got Plenty o’ Nuttin’".

-- It might make sense to replace some of the proofs with automated
-- proofs.

open import Tools.Bool using (Bool; true; false; if_then_else_; T)

module Definition.Modality.Instances.Zero-one-many
  -- Should 𝟙 be below 𝟘?
  (𝟙≤𝟘 : Bool)
  where

import Definition.Modality
import Definition.Modality.Instances.LowerBounded as LowerBounded
import Definition.Modality.Properties.Meet as Meet
import Definition.Modality.Properties.PartialOrder as PartialOrder
import Definition.Modality.Properties.Star as Star
import Definition.Modality.Restrictions

import Tools.Algebra
open import Tools.Function
open import Tools.Nullary
open import Tools.Product
open import Tools.PropositionalEquality as PE
open import Tools.Relation
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Sum using (_⊎_; inj₁; inj₂)

------------------------------------------------------------------------
-- The type

-- Zero, one or many.

data Zero-one-many : Set where
  𝟘 𝟙 ω : Zero-one-many

private variable
  p p₁ p₂ q r : Zero-one-many

-- A setoid for Zero-one-many. Propositional equality is used as the
-- equivalence relation.

Zero-one-many-setoid : Setoid _ _
Zero-one-many-setoid = record
  { Carrier       = Zero-one-many
  ; _≈_           = _≡_
  ; isEquivalence = PE.isEquivalence
  }

open Definition.Modality              Zero-one-many-setoid public
open Definition.Modality.Restrictions Zero-one-many-setoid public
open Tools.Algebra                    Zero-one-many-setoid

------------------------------------------------------------------------
-- Meet

-- Some requirements of a meet operation.

Meet-requirements :
  (Zero-one-many → Zero-one-many → Zero-one-many) → Set
Meet-requirements _∧_ =
  (𝟘 ∧ 𝟘 ≡ 𝟘) ×
  (𝟙 ∧ 𝟙 ≡ 𝟙) ×
  (ω ∧ ω ≡ ω) ×
  (𝟘 ∧ ω ≡ ω) ×
  (ω ∧ 𝟘 ≡ ω) ×
  (𝟙 ∧ ω ≡ ω) ×
  (ω ∧ 𝟙 ≡ ω) ×
  (𝟘 ∧ 𝟙 ≢ 𝟘) ×
  (𝟙 ∧ 𝟘 ≢ 𝟘)

-- The meet operation of a "ModalityWithout⊛" for Zero-one-many-setoid
-- for which the zero is 𝟘 and the one is 𝟙 has to satisfy the
-- Meet-requirements.

Meet-requirements-required :
  (M : ModalityWithout⊛) →
  ModalityWithout⊛.𝟘 M ≡ 𝟘 →
  ModalityWithout⊛.𝟙 M ≡ 𝟙 →
  Meet-requirements (ModalityWithout⊛._∧_ M)
Meet-requirements-required M refl refl =
    (𝟘 ∧ 𝟘  ≡⟨ ∧-idem _ ⟩
     𝟘      ∎)
  , (𝟙 ∧ 𝟙  ≡⟨ ∧-idem _ ⟩
     𝟙      ∎)
  , (ω ∧ ω  ≡⟨ ∧-idem _ ⟩
     ω      ∎)
  , 𝟘∧ω≡ω
  , (ω ∧ 𝟘  ≡⟨ ∧-comm _ _ ⟩
     𝟘 ∧ ω  ≡⟨ 𝟘∧ω≡ω ⟩
     ω      ∎)
  , (𝟙 ∧ ω  ≡⟨ ∧-comm _ _ ⟩
     ω ∧ 𝟙  ≡˘⟨ ≉𝟘→≤𝟙 {p = ω} (λ ()) ⟩
     ω      ∎)
  , (ω ∧ 𝟙  ≡˘⟨ ≉𝟘→≤𝟙 {p = ω} (λ ()) ⟩
     ω      ∎)
  , 𝟘∧𝟙≢𝟘
  , (λ 𝟙∧𝟘≡𝟘 → 𝟘∧𝟙≢𝟘 (
       𝟘 ∧ 𝟙  ≡⟨ ∧-comm _ _ ⟩
       𝟙 ∧ 𝟘  ≡⟨ 𝟙∧𝟘≡𝟘 ⟩
       𝟘      ∎))
  where
  open ModalityWithout⊛ M hiding (𝟘; 𝟙)
  open Meet M
  open PartialOrder M

  𝟘∧ω≡ω : 𝟘 ∧ ω ≡ ω
  𝟘∧ω≡ω = lemma _ refl
    where
    lemma : ∀ p → p ≡ 𝟘 ∧ ω → p ≡ ω
    lemma ω _  = refl
    lemma 𝟘 eq =
      𝟘  ≡˘⟨ 𝟘≮ eq ⟩
      ω  ∎
      where
      open Tools.Reasoning.PropositionalEquality
    lemma 𝟙 eq = ≤-antisym
      (begin
         𝟙      ≡⟨ eq ⟩
         𝟘 ∧ ω  ≤⟨ ∧-decreasingʳ _ _ ⟩
         ω      ∎)
      (≉𝟘→≤𝟙 λ ())
      where
      open Tools.Reasoning.PartialOrder ≤-poset

  open Tools.Reasoning.PropositionalEquality

  𝟘∧𝟙≢𝟘 : 𝟘 ∧ 𝟙 ≢ 𝟘
  𝟘∧𝟙≢𝟘 𝟘∧𝟙≡𝟘 with
    𝟙  ≡⟨ 𝟘≮ (sym 𝟘∧𝟙≡𝟘) ⟩
    𝟘  ∎
  … | ()

-- The result of 𝟘 ∧ 𝟙 and 𝟙 ∧ 𝟘.

𝟘∧𝟙 : Zero-one-many
𝟘∧𝟙 = if 𝟙≤𝟘 then 𝟙 else ω

-- Meet.

infixr 40 _∧_

_∧_ : Zero-one-many → Zero-one-many → Zero-one-many
𝟘 ∧ 𝟘 = 𝟘
𝟙 ∧ 𝟙 = 𝟙
𝟘 ∧ 𝟙 = 𝟘∧𝟙
𝟙 ∧ 𝟘 = 𝟘∧𝟙
_ ∧ _ = ω

-- If 𝟙≤𝟘 is true, then 𝟘∧𝟙 ≡ 𝟙.

𝟘∧𝟙≡𝟙 : T 𝟙≤𝟘 → 𝟘∧𝟙 ≡ 𝟙
𝟘∧𝟙≡𝟙 = lemma _
  where
  lemma : ∀ b → T b → (if b then 𝟙 else ω) ≡ 𝟙
  lemma true _ = refl

-- If 𝟙≤𝟘 is false, then 𝟘∧𝟙 ≡ ω.

𝟘∧𝟙≡ω : ¬ T 𝟙≤𝟘 → 𝟘∧𝟙 ≡ ω
𝟘∧𝟙≡ω = lemma _
  where
  lemma : ∀ b → ¬ T b → (if b then 𝟙 else ω) ≡ ω
  lemma false _  = refl
  lemma true  ¬⊤ = ⊥-elim (¬⊤ _)

-- The value of 𝟘∧𝟙 is not 𝟘.

𝟘∧𝟙≢𝟘 : 𝟘∧𝟙 ≢ 𝟘
𝟘∧𝟙≢𝟘 = lemma _
  where
  lemma : ∀ b → (if b then 𝟙 else ω) ≢ 𝟘
  lemma false ()
  lemma true  ()

-- One can prove that something holds for 𝟘∧𝟙 by proving that it holds
-- for 𝟙 (under the assumption that 𝟘∧𝟙 is 𝟙), and that it holds for ω
-- (under the assumption that 𝟘∧𝟙 is ω).

𝟘∧𝟙-elim :
  ∀ {p} (P : Zero-one-many → Set p) →
  (𝟘∧𝟙 ≡ 𝟙 → P 𝟙) →
  (𝟘∧𝟙 ≡ ω → P ω) →
  P 𝟘∧𝟙
𝟘∧𝟙-elim P one omega = lemma _ refl
  where
  lemma : ∀ p → 𝟘∧𝟙 ≡ p → P p
  lemma 𝟘 𝟘∧𝟙≡𝟘 = ⊥-elim (𝟘∧𝟙≢𝟘 𝟘∧𝟙≡𝟘)
  lemma 𝟙 𝟘∧𝟙≡𝟙 = one 𝟘∧𝟙≡𝟙
  lemma ω 𝟘∧𝟙≡ω = omega 𝟘∧𝟙≡ω

-- 𝟘 ∧ 𝟘∧𝟙 is equal to 𝟘∧𝟙.

𝟘∧[𝟘∧𝟙] : 𝟘 ∧ 𝟘∧𝟙 ≡ 𝟘∧𝟙
𝟘∧[𝟘∧𝟙] = 𝟘∧𝟙-elim
  (λ p → 𝟘 ∧ p ≡ p)
  (λ 𝟘∧𝟙≡𝟙 → 𝟘∧𝟙≡𝟙)
  (λ _ → refl)

-- 𝟙 ∧ 𝟘∧𝟙 is equal to 𝟘∧𝟙.

𝟙∧[𝟘∧𝟙] : 𝟙 ∧ 𝟘∧𝟙 ≡ 𝟘∧𝟙
𝟙∧[𝟘∧𝟙] = 𝟘∧𝟙-elim
  (λ p → 𝟙 ∧ p ≡ p)
  (λ _ → refl)
  (λ _ → refl)

------------------------------------------------------------------------
-- Ordering

-- Some requirements of an ordering relation.

Order-requirements : (Zero-one-many → Zero-one-many → Set) → Set
Order-requirements _≤_ = (ω ≤ 𝟙) × (ω ≤ 𝟘) × ¬ (𝟘 ≤ 𝟙)

-- The ordering relation of a "ModalityWithout⊛" for
-- Zero-one-many-setoid for which the zero is 𝟘 and the one is 𝟙 has
-- to satisfy the Order-requirements.

Order-requirements-required :
  (M : ModalityWithout⊛) →
  ModalityWithout⊛.𝟘 M ≡ 𝟘 →
  ModalityWithout⊛.𝟙 M ≡ 𝟙 →
  Order-requirements (ModalityWithout⊛._≤_ M)
Order-requirements-required M refl refl =
  case Meet-requirements-required M refl refl of λ where
    (_ , _ , _ , _ , ω⊓𝟘≡ω , _ , ω⊓𝟙≡ω , 𝟘⊓𝟙≢𝟘 , _) →
        (ω      ≡˘⟨ ω⊓𝟙≡ω ⟩
         ω ⊓ 𝟙  ∎)
      , (ω      ≡˘⟨ ω⊓𝟘≡ω ⟩
         ω ⊓ 𝟘  ∎)
      , (λ 𝟘≡𝟘⊓𝟙 → 𝟘⊓𝟙≢𝟘 (
           𝟘 ⊓ 𝟙  ≡˘⟨ 𝟘≡𝟘⊓𝟙 ⟩
           𝟘      ∎))
  where
  open ModalityWithout⊛ M using () renaming (_∧_ to _⊓_)
  open Tools.Reasoning.PropositionalEquality

-- The inferred ordering relation.

infix 10 _≤_

_≤_ : Zero-one-many → Zero-one-many → Set
p ≤ q = p ≡ p ∧ q

-- The quantity ω is smaller than all others.

ω≤ : ∀ p → ω ≤ p
ω≤ _ = refl

-- 𝟘 is maximal.

𝟘-maximal : 𝟘 ≤ p → p ≡ 𝟘
𝟘-maximal {p = 𝟘} refl = refl
𝟘-maximal {p = 𝟙}      = 𝟘∧𝟙-elim
  (λ q → 𝟘 ≡ q → 𝟙 ≡ 𝟘)
  (λ _ → sym)
  (λ _ ())

-- If 𝟙≤𝟘 is true, then 𝟙 ≤ 𝟘.

𝟙≤𝟘→𝟙≤𝟘 : T 𝟙≤𝟘 → 𝟙 ≤ 𝟘
𝟙≤𝟘→𝟙≤𝟘 𝟙≤𝟘 =
  𝟙      ≡˘⟨ 𝟘∧𝟙≡𝟙 𝟙≤𝟘 ⟩
  𝟙 ∧ 𝟘  ∎
  where
  open Tools.Reasoning.PropositionalEquality

-- If 𝟙≤𝟘 is false, then 𝟙 is maximal.

𝟙-maximal : ¬ T 𝟙≤𝟘 → 𝟙 ≤ p → p ≡ 𝟙
𝟙-maximal {p = 𝟙} _   refl = refl
𝟙-maximal {p = 𝟘} 𝟙≰𝟘 𝟙≤𝟘  = ⊥-elim (
  case
    𝟙      ≡⟨ 𝟙≤𝟘 ⟩
    𝟙 ∧ 𝟘  ≡⟨ 𝟘∧𝟙≡ω 𝟙≰𝟘 ⟩
    ω      ∎
  of λ ())
  where
  open Tools.Reasoning.PropositionalEquality

------------------------------------------------------------------------
-- Addition

-- Addition.

infixr 40 _+_

_+_ : Zero-one-many → Zero-one-many → Zero-one-many
𝟘 + q = q
𝟙 + 𝟘 = 𝟙
_ + _ = ω

-- The sum of two non-zero values is ω.

≢𝟘+≢𝟘 : p ≢ 𝟘 → q ≢ 𝟘 → p + q ≡ ω
≢𝟘+≢𝟘 {p = 𝟘}         𝟘≢𝟘 _   = ⊥-elim (𝟘≢𝟘 refl)
≢𝟘+≢𝟘 {p = 𝟙} {q = 𝟘} _   𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 refl)
≢𝟘+≢𝟘 {p = 𝟙} {q = 𝟙} _   _   = refl
≢𝟘+≢𝟘 {p = 𝟙} {q = ω} _   _   = refl
≢𝟘+≢𝟘 {p = ω}         _   _   = refl

------------------------------------------------------------------------
-- Multiplication

-- Multiplication.

infixr 45 _·_

_·_ : Zero-one-many → Zero-one-many → Zero-one-many
𝟘 · _ = 𝟘
_ · 𝟘 = 𝟘
𝟙 · 𝟙 = 𝟙
_ · _ = ω

-- Multiplication is commutative.

·-comm : Commutative _·_
·-comm = λ where
  𝟘 𝟘 → refl
  𝟘 𝟙 → refl
  𝟘 ω → refl
  𝟙 𝟘 → refl
  𝟙 𝟙 → refl
  𝟙 ω → refl
  ω 𝟘 → refl
  ω 𝟙 → refl
  ω ω → refl

-- If p is not 𝟘, then ω · p is equal to ω.

ω·≢𝟘 : p ≢ 𝟘 → ω · p ≡ ω
ω·≢𝟘 {p = 𝟘} 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 refl)
ω·≢𝟘 {p = 𝟙} _   = refl
ω·≢𝟘 {p = ω} _   = refl

-- If p is not 𝟘, then 𝟙 · p is not 𝟘.

𝟙·≢𝟘 : p ≢ 𝟘 → 𝟙 · p ≢ 𝟘
𝟙·≢𝟘 {p = 𝟘} 𝟘≢𝟘 = 𝟘≢𝟘
𝟙·≢𝟘 {p = 𝟙} 𝟙≢𝟘 = 𝟙≢𝟘
𝟙·≢𝟘 {p = ω} ω≢𝟘 = ω≢𝟘

------------------------------------------------------------------------
-- The modality without the star operation

-- The zero-one-many modality without the star operation (with
-- arbitrary "restrictions").

zero-one-many-without-⊛ : Restrictions → ModalityWithout⊛
zero-one-many-without-⊛ restrictions = record
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
              ; ∙-cong = cong₂ _+_
              }
            ; assoc = λ where
                𝟘 _ _ → refl
                𝟙 𝟘 _ → refl
                𝟙 𝟙 𝟘 → refl
                𝟙 𝟙 𝟙 → refl
                𝟙 𝟙 ω → refl
                𝟙 ω _ → refl
                ω _ _ → refl
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
          ; assoc = λ where
              𝟘 _ _ → refl
              𝟙 𝟘 _ → refl
              𝟙 𝟙 𝟘 → refl
              𝟙 𝟙 𝟙 → refl
              𝟙 𝟙 ω → refl
              𝟙 ω 𝟘 → refl
              𝟙 ω 𝟙 → refl
              𝟙 ω ω → refl
              ω 𝟘 _ → refl
              ω 𝟙 𝟘 → refl
              ω 𝟙 𝟙 → refl
              ω 𝟙 ω → refl
              ω ω 𝟘 → refl
              ω ω 𝟙 → refl
              ω ω ω → refl
          }
        ; identity =
              ·-identityˡ
            , comm+idˡ⇒idʳ ·-comm ·-identityˡ
        }
      ; distrib =
            ·-distrib-+ˡ
          , comm+distrˡ⇒distrʳ (cong₂ _+_) ·-comm ·-distrib-+ˡ
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
        ; assoc = λ where
            𝟘 𝟘 𝟘 → refl
            𝟘 𝟘 𝟙 →
              𝟘∧𝟙      ≡˘⟨ 𝟘∧[𝟘∧𝟙] ⟩
              𝟘 ∧ 𝟘∧𝟙  ∎
            𝟘 𝟘 ω → refl
            𝟘 𝟙 𝟘 →
              𝟘∧𝟙 ∧ 𝟘  ≡⟨⟩
              𝟘∧𝟙 ∧ 𝟘  ≡⟨ ∧-comm 𝟘∧𝟙 _ ⟩
              𝟘 ∧ 𝟘∧𝟙  ∎
            𝟘 𝟙 𝟙 →
              𝟘∧𝟙 ∧ 𝟙  ≡⟨ ∧-comm 𝟘∧𝟙 _ ⟩
              𝟙 ∧ 𝟘∧𝟙  ≡⟨ 𝟙∧[𝟘∧𝟙] ⟩
              𝟘∧𝟙      ∎
            𝟘 𝟙 ω →
              𝟘∧𝟙 ∧ ω  ≡⟨ ∧-comm 𝟘∧𝟙 _ ⟩
              ω ∧ 𝟘∧𝟙  ≡⟨⟩
              ω        ∎
            𝟘 ω _ → refl
            𝟙 𝟘 𝟘 →
              𝟘∧𝟙 ∧ 𝟘  ≡⟨ ∧-comm 𝟘∧𝟙 _ ⟩
              𝟘 ∧ 𝟘∧𝟙  ≡⟨ 𝟘∧[𝟘∧𝟙] ⟩
              𝟘∧𝟙      ∎
            𝟙 𝟘 𝟙 →
              𝟘∧𝟙 ∧ 𝟙  ≡⟨⟩
              𝟘∧𝟙 ∧ 𝟙  ≡⟨ ∧-comm 𝟘∧𝟙 _ ⟩
              𝟙 ∧ 𝟘∧𝟙  ∎
            𝟙 𝟘 ω →
              𝟘∧𝟙 ∧ ω  ≡⟨ ∧-comm 𝟘∧𝟙 _ ⟩
              ω ∧ 𝟘∧𝟙  ≡⟨⟩
              ω        ∎
            𝟙 𝟙 𝟘 →
              𝟘∧𝟙      ≡˘⟨ 𝟙∧[𝟘∧𝟙] ⟩
              𝟙 ∧ 𝟘∧𝟙  ∎
            𝟙 𝟙 𝟙 → refl
            𝟙 𝟙 ω → refl
            𝟙 ω _ → refl
            ω _ _ → refl
        }
      ; idem = λ where
          𝟘 → refl
          𝟙 → refl
          ω → refl
      }
    ; comm = ∧-comm
    }
  ; ·-distrib-∧ =
        ·-distrib-∧ˡ
      , comm+distrˡ⇒distrʳ (cong₂ _∧_) ·-comm ·-distrib-∧ˡ
  ; +-distrib-∧ =
        +-distrib-∧ˡ
      , comm+distrˡ⇒distrʳ (cong₂ _∧_) +-comm +-distrib-∧ˡ
  ; restrictions = restrictions
  ; 𝟘ᵐ→𝟙≉𝟘       = λ _ ()
  ; is-𝟘?        = λ where
      𝟘 → yes refl
      𝟙 → no (λ ())
      ω → no (λ ())
  ; zero-product = λ where
      {p = 𝟘} _ → inj₁ refl
      {q = 𝟘} _ → inj₂ refl
  ; positiveˡ = λ where
      {p = 𝟘} {q = 𝟘} _  → refl
      {p = 𝟘} {q = 𝟙} ()
      {p = 𝟘} {q = ω} ()
  ; 𝟘≮ = λ where
      {p = 𝟘} _   → refl
      {p = 𝟙} 𝟘≤𝟙 → 𝟘-maximal 𝟘≤𝟙
  ; ∧≤𝟘ˡ = λ where
      {p = 𝟘} {q = 𝟘} _     → refl
      {p = 𝟘} {q = 𝟙} _     → refl
      {p = 𝟙} {q = 𝟘} 𝟘∧𝟙≡𝟘 → ⊥-elim (
        case
          𝟙  ≡⟨ 𝟘-maximal (sym 𝟘∧𝟙≡𝟘) ⟩
          𝟘  ∎
        of λ ())
  ; ≉𝟘→≤𝟙 = λ where
      {p = 𝟘} 𝟘≢𝟘 → ⊥-elim (𝟘≢𝟘 refl)
      {p = 𝟙} _   → refl
      {p = ω} _   → refl
  }
  where
  open Tools.Reasoning.PropositionalEquality

  +-comm : Commutative _+_
  +-comm = λ where
    𝟘 𝟘 → refl
    𝟘 𝟙 → refl
    𝟘 ω → refl
    𝟙 𝟘 → refl
    𝟙 𝟙 → refl
    𝟙 ω → refl
    ω 𝟘 → refl
    ω 𝟙 → refl
    ω ω → refl

  ·-identityˡ : LeftIdentity 𝟙 _·_
  ·-identityˡ = λ where
    𝟘 → refl
    𝟙 → refl
    ω → refl

  ·-distrib-+ˡ : _·_ DistributesOverˡ _+_
  ·-distrib-+ˡ = λ where
    𝟘 _ _ → refl
    𝟙 𝟘 _ → refl
    𝟙 𝟙 𝟘 → refl
    𝟙 𝟙 𝟙 → refl
    𝟙 𝟙 ω → refl
    𝟙 ω _ → refl
    ω 𝟘 _ → refl
    ω 𝟙 𝟘 → refl
    ω 𝟙 𝟙 → refl
    ω 𝟙 ω → refl
    ω ω _ → refl

  ∧-comm : Commutative _∧_
  ∧-comm = λ where
    𝟘 𝟘 → refl
    𝟘 𝟙 → refl
    𝟘 ω → refl
    𝟙 𝟘 → refl
    𝟙 𝟙 → refl
    𝟙 ω → refl
    ω 𝟘 → refl
    ω 𝟙 → refl
    ω ω → refl

  ·-distrib-∧ˡ : _·_ DistributesOverˡ _∧_
  ·-distrib-∧ˡ = λ where
    𝟘 _ _ → refl
    𝟙 𝟘 𝟘 → refl
    𝟙 𝟘 𝟙 →
      𝟙 · 𝟘∧𝟙  ≡⟨ ·-identityˡ _ ⟩
      𝟘∧𝟙      ∎
    𝟙 𝟘 ω → refl
    𝟙 𝟙 𝟘 →
      𝟙 · 𝟘∧𝟙  ≡⟨ ·-identityˡ _ ⟩
      𝟘∧𝟙      ∎
    𝟙 𝟙 𝟙 → refl
    𝟙 𝟙 ω → refl
    𝟙 ω _ → refl
    ω 𝟘 𝟘 → refl
    ω 𝟘 𝟙 →
      ω · 𝟘∧𝟙  ≡⟨ ω·≢𝟘 𝟘∧𝟙≢𝟘 ⟩
      ω        ∎
    ω 𝟘 ω → refl
    ω 𝟙 𝟘 →
      ω · 𝟘∧𝟙  ≡⟨ ω·≢𝟘 𝟘∧𝟙≢𝟘 ⟩
      ω        ∎
    ω 𝟙 𝟙 → refl
    ω 𝟙 ω → refl
    ω ω _ → refl

  +-distrib-∧ˡ : _+_ DistributesOverˡ _∧_
  +-distrib-∧ˡ = λ where
    𝟘 _ _ → refl
    𝟙 𝟘 𝟘 → refl
    𝟙 𝟘 𝟙 →
      𝟙 + 𝟘∧𝟙  ≡⟨ ≢𝟘+≢𝟘 (λ ()) 𝟘∧𝟙≢𝟘 ⟩
      ω        ∎
    𝟙 𝟘 ω → refl
    𝟙 𝟙 𝟘 →
      𝟙 + 𝟘∧𝟙  ≡⟨ ≢𝟘+≢𝟘 (λ ()) 𝟘∧𝟙≢𝟘 ⟩
      ω        ∎
    𝟙 𝟙 𝟙 → refl
    𝟙 𝟙 ω → refl
    𝟙 ω _ → refl
    ω _ _ → refl

------------------------------------------------------------------------
-- Star

-- Some requirements of a star operation and a meet operation.

Star-requirements :
  (Zero-one-many → Zero-one-many → Zero-one-many → Zero-one-many) →
  (Zero-one-many → Zero-one-many → Zero-one-many) →
  Set
Star-requirements _⊛_▷_ _∧_ =
  let _≤_ : Zero-one-many → Zero-one-many → Set
      p ≤ q = p ≡ (p ∧ q)
  in
  (∀ {q r} →                     (ω ⊛ q ▷ r) ≡ ω) ×
  (∀ {p r} →                     (p ⊛ ω ▷ r) ≡ ω) ×
  (∀ {p q} → ¬ (p ≡ 𝟘 × q ≡ 𝟘) → (p ⊛ q ▷ ω) ≡ ω) ×
  (∀ {r} →                       (𝟘 ⊛ 𝟘 ▷ r) ≡ 𝟘) ×
  (∀ {p} →                       (p ⊛ 𝟙 ▷ 𝟙) ≡ ω) ×
                                ((𝟘 ⊛ 𝟙 ▷ 𝟘) ≤ (𝟘 ∧ 𝟙)) ×
                                ((𝟙 ⊛ 𝟘 ▷ 𝟘) ≤ (𝟘 ∧ 𝟙)) ×
                                ((𝟙 ⊛ 𝟘 ▷ 𝟙) ≤ 𝟙) ×
                                ((𝟙 ⊛ 𝟙 ▷ 𝟘) ≤ 𝟙)

-- A star operation for a ModalityWithout⊛ for Zero-one-many-setoid
-- for which the zero is 𝟘, the one is 𝟙, addition is _+_,
-- multiplication is _·_, and the meet operation is _∧_ has to satisfy
-- the Star-requirements (for _∧_) if certain conditions are
-- satisfied.

Star-requirements-required′ :
  (M : ModalityWithout⊛) →
  ModalityWithout⊛.𝟘   M ≡ 𝟘 →
  ModalityWithout⊛.𝟙   M ≡ 𝟙 →
  ModalityWithout⊛._+_ M ≡ _+_ →
  ModalityWithout⊛._·_ M ≡ _·_ →
  ModalityWithout⊛._∧_ M ≡ _∧_ →
  (_⊛_▷_ :
   Zero-one-many → Zero-one-many → Zero-one-many → Zero-one-many) →
  (∀ p q r → (p ⊛ q ▷ r) ≤ q + r · (p ⊛ q ▷ r)) →
  (∀ p q r → (p ⊛ q ▷ r) ≤ p) →
  (∀ r → 𝟘 ⊛ 𝟘 ▷ r ≡ 𝟘) →
  (∀ p q r → p ⊛ q ▷ r ≡ 𝟘 → p ≡ 𝟘 × q ≡ 𝟘) →
  Star-requirements _⊛_▷_ _∧_
Star-requirements-required′
  M refl refl refl refl refl star ⊛-ineq₁ ⊛-ineq₂ ⊛-idem-𝟘 ⊛≈𝟘 =
  case Meet-requirements-required M refl refl of λ where
    (_ , _ , ω⊓ω≡ω , _ , ω⊓𝟘≡ω , _ , ω⊓𝟙≡ω , _ , _) →
        (λ {_ _} → ω⊛▷)
      , (λ {_ _} → ⊛ω▷)
      , (λ {_ _} → ⊛▷ω _ _)
      , (λ {_} → ⊛-idem-𝟘 _)
      , (λ {p = p} → ≤-antisym
           (begin
              p ⊛ 𝟙 ▷ 𝟙          ≤⟨ ⊛-ineq₁ _ _ _ ⟩
              𝟙 + 𝟙 · p ⊛ 𝟙 ▷ 𝟙  ≈⟨ ≢𝟘+≢𝟘 (λ ()) (𝟙·≢𝟘 ⊛𝟙▷) ⟩
              ω                  ∎)
           (ω≤ (p ⊛ 𝟙 ▷ 𝟙)))
      , ∧-greatest-lower-bound
          (⊛-ineq₂ _ _ _)
          (begin
             𝟘 ⊛ 𝟙 ▷ 𝟘          ≤⟨ ⊛-ineq₁ _ _ _ ⟩
             𝟙 + 𝟘 · 𝟘 ⊛ 𝟙 ▷ 𝟘  ≡⟨⟩
             𝟙                  ∎)
      , ∧-greatest-lower-bound
          (begin
             𝟙 ⊛ 𝟘 ▷ 𝟘          ≤⟨ ⊛-ineq₁ _ _ _ ⟩
             𝟘 + 𝟘 · 𝟙 ⊛ 𝟘 ▷ 𝟘  ≡⟨⟩
             𝟘                  ∎)
          (⊛-ineq₂ _ _ _)
      , ⊛-ineq₂ _ _ _
      , ⊛-ineq₂ _ _ _
  where
  open ModalityWithout⊛ M hiding (𝟘; 𝟙; _+_; _·_; _∧_; _≤_)
  open PartialOrder M
  open Meet M
  open Tools.Reasoning.PartialOrder ≤-poset

  infix 50 _⊛_▷_

  _⊛_▷_ : Zero-one-many → Zero-one-many → Zero-one-many → Zero-one-many
  _⊛_▷_ = star

  ω⊛▷ : ω ⊛ q ▷ r ≡ ω
  ω⊛▷ {q = q} {r = r} = ≤-antisym
    (begin
       ω ⊛ q ▷ r  ≤⟨ ⊛-ineq₂ _ _ _ ⟩
       ω          ∎)
    (ω≤ (ω ⊛ q ▷ r))

  ⊛ω▷ : p ⊛ ω ▷ r ≡ ω
  ⊛ω▷ {p = p} {r = r} = ≤-antisym
    (begin
       p ⊛ ω ▷ r          ≤⟨ ⊛-ineq₁ _ _ _ ⟩
       ω + r · p ⊛ ω ▷ r  ≡⟨⟩
       ω                  ∎)
    (ω≤ (p ⊛ ω ▷ r))

  𝟙⊛▷ : 𝟙 ⊛ q ▷ r ≢ 𝟘
  𝟙⊛▷ 𝟙⊛▷≡𝟘 = case ⊛≈𝟘 _ _ _ 𝟙⊛▷≡𝟘 .proj₁ of λ ()

  ⊛𝟙▷ : p ⊛ 𝟙 ▷ r ≢ 𝟘
  ⊛𝟙▷ ⊛𝟙▷≡𝟘 = case ⊛≈𝟘 _ _ _ ⊛𝟙▷≡𝟘 .proj₂ of λ ()

  ⊛▷ω : ∀ p q → ¬ (p ≡ 𝟘 × q ≡ 𝟘) → (p ⊛ q ▷ ω) ≡ ω
  ⊛▷ω _ ω _      = ⊛ω▷
  ⊛▷ω ω _ _      = ω⊛▷
  ⊛▷ω 𝟘 𝟘 ¬≡𝟘×≡𝟘 = ⊥-elim (¬≡𝟘×≡𝟘 (refl , refl))
  ⊛▷ω p 𝟙 _      = ≤-antisym
    (begin
       p ⊛ 𝟙 ▷ ω          ≤⟨ ⊛-ineq₁ _ _ _ ⟩
       𝟙 + ω · p ⊛ 𝟙 ▷ ω  ≈⟨ +-congˡ (ω·≢𝟘 ⊛𝟙▷) ⟩
       𝟙 + ω              ≡⟨⟩
       ω                  ∎)
    (ω≤ (p ⊛ 𝟙 ▷ ω))
  ⊛▷ω 𝟙 𝟘 _ = ≤-antisym
    (begin
       𝟙 ⊛ 𝟘 ▷ ω      ≤⟨ ⊛-ineq₁ _ _ _ ⟩
       ω · 𝟙 ⊛ 𝟘 ▷ ω  ≈⟨ ω·≢𝟘 𝟙⊛▷ ⟩
       ω              ∎)
    (ω≤ (𝟙 ⊛ 𝟘 ▷ ω))

-- The star operation of a modality for Zero-one-many-setoid for which
-- the zero is 𝟘, the one is 𝟙, addition is _+_, multiplication is
-- _·_, and the meet operation is _∧_ has to satisfy the
-- Star-requirements (for _∧_).

Star-requirements-required :
  (M : Modality) →
  Modality.𝟘   M ≡ 𝟘 →
  Modality.𝟙   M ≡ 𝟙 →
  Modality._+_ M ≡ _+_ →
  Modality._·_ M ≡ _·_ →
  Modality._∧_ M ≡ _∧_ →
  Star-requirements (Modality._⊛_▷_ M) _∧_
Star-requirements-required M refl refl refl refl refl =
  Star-requirements-required′
    modalityWithout⊛ refl refl refl refl refl
    _⊛_▷_
    ⊛-ineq₁
    ⊛-ineq₂
    ⊛-idem-𝟘
    (λ _ _ _ eq → ⊛≈𝟘ˡ eq , ⊛≈𝟘ʳ eq)
  where
  open Modality M
  open Star M

------------------------------------------------------------------------
-- One variant of the modality

-- A zero-one-many modality (with arbitrary "restrictions").
--
-- The star operation is defined using the construction in
-- Definition.Modality.Instances.LowerBounded.

zero-one-many-lower-bounded : Restrictions → Modality
zero-one-many-lower-bounded restrictions =
  LowerBounded.isModality
    (zero-one-many-without-⊛ restrictions) ω ω≤

-- With this definition the result of p ⊛ q ▷ r is 𝟘 when p and q are
-- 𝟘, and ω otherwise.

zero-one-many-lower-bounded-⊛ :
  (rs : Restrictions) →
  let open Modality (zero-one-many-lower-bounded rs) hiding (𝟘) in
  (∀ r → 𝟘 ⊛ 𝟘 ▷ r ≡ 𝟘) ×
  (∀ p q r → ¬ (p ≡ 𝟘 × q ≡ 𝟘) → p ⊛ q ▷ r ≡ ω)
zero-one-many-lower-bounded-⊛ rs =
    (λ _ → refl)
  , (λ where
       𝟘 𝟘 _ ¬≡𝟘×≡𝟘 → ⊥-elim (¬≡𝟘×≡𝟘 (refl , refl))
       𝟘 𝟙 _ _      →
         ω · 𝟘∧𝟙  ≡⟨ ω·≢𝟘 𝟘∧𝟙≢𝟘 ⟩
         ω        ∎
       𝟘 ω _ _ → refl
       𝟙 𝟘 _ _ →
         ω · 𝟘∧𝟙  ≡⟨ ω·≢𝟘 𝟘∧𝟙≢𝟘 ⟩
         ω        ∎
       𝟙 𝟙 _ _ → refl
       𝟙 ω _ _ → refl
       ω _ _ _ → refl)
  where
  open Modality (zero-one-many-lower-bounded rs) hiding (𝟘; 𝟙; _·_)
  open Tools.Reasoning.PropositionalEquality

------------------------------------------------------------------------
-- A variant of the modality with a "greatest" star operation

-- A "greatest" definition of the star operation.

infix 50 _⊛_▷_

_⊛_▷_ : Zero-one-many → Zero-one-many → Zero-one-many → Zero-one-many
𝟘 ⊛ 𝟘 ▷ _ = 𝟘
ω ⊛ _ ▷ _ = ω
_ ⊛ ω ▷ _ = ω
_ ⊛ _ ▷ ω = ω
_ ⊛ 𝟙 ▷ 𝟙 = ω
𝟘 ⊛ 𝟙 ▷ 𝟘 = 𝟘∧𝟙
𝟙 ⊛ 𝟘 ▷ 𝟘 = 𝟘∧𝟙
𝟙 ⊛ 𝟘 ▷ 𝟙 = 𝟙
𝟙 ⊛ 𝟙 ▷ 𝟘 = 𝟙

-- This definition is not equal to the one obtained from
-- zero-one-many-lower-bounded.

lower-bounded≢greatest :
  (rs : Restrictions) →
  Modality._⊛_▷_ (zero-one-many-lower-bounded rs) ≢ _⊛_▷_
lower-bounded≢greatest rs hyp =
  case cong (λ f → f 𝟙 𝟙 𝟘) hyp of λ ()

-- A simplification lemma for the star operation.

⊛ω▷ : ∀ p → p ⊛ ω ▷ r ≡ ω
⊛ω▷ 𝟘 = refl
⊛ω▷ 𝟙 = refl
⊛ω▷ ω = refl

-- A simplification lemma for the star operation.

⊛▷ω : ∀ p q → ¬ (p ≡ 𝟘 × q ≡ 𝟘) → (p ⊛ q ▷ ω) ≡ ω
⊛▷ω p ω _      = ⊛ω▷ p
⊛▷ω ω _ _      = refl
⊛▷ω 𝟘 𝟘 ¬≡𝟘×≡𝟘 = ⊥-elim (¬≡𝟘×≡𝟘 (refl , refl))
⊛▷ω 𝟘 𝟙 _      = refl
⊛▷ω 𝟙 𝟙 _      = refl
⊛▷ω 𝟙 𝟘 _      = refl

-- A simplification lemma for the star operation.

⊛𝟙▷𝟙 : ∀ p → p ⊛ 𝟙 ▷ 𝟙 ≡ ω
⊛𝟙▷𝟙 𝟘 = refl
⊛𝟙▷𝟙 𝟙 = refl
⊛𝟙▷𝟙 ω = refl

-- A simplification lemma for the star operation.

⊛𝟘∧𝟙▷𝟙 : ∀ p → p ⊛ 𝟘∧𝟙 ▷ 𝟙 ≡ ω
⊛𝟘∧𝟙▷𝟙 𝟘 = 𝟘∧𝟙-elim (λ q → 𝟘 ⊛ q ▷ 𝟙 ≡ ω) (λ _ → refl) (λ _ → refl)
⊛𝟘∧𝟙▷𝟙 𝟙 = 𝟘∧𝟙-elim (λ q → 𝟙 ⊛ q ▷ 𝟙 ≡ ω) (λ _ → refl) (λ _ → refl)
⊛𝟘∧𝟙▷𝟙 ω = refl

-- A simplification lemma for the star operation.

𝟘⊛𝟘∧𝟙▷𝟘 : 𝟘 ⊛ 𝟘∧𝟙 ▷ 𝟘 ≡ 𝟘∧𝟙
𝟘⊛𝟘∧𝟙▷𝟘 = 𝟘∧𝟙-elim
  (λ q → 𝟘 ⊛ q ▷ 𝟘 ≡ q)
  (λ 𝟘∧𝟙≡𝟙 → 𝟘∧𝟙≡𝟙)
  (λ _ → refl)

-- A simplification lemma for the star operation.

𝟙⊛𝟘∧𝟙▷𝟘 : 𝟙 ⊛ 𝟘∧𝟙 ▷ 𝟘 ≡ 𝟘∧𝟙
𝟙⊛𝟘∧𝟙▷𝟘 = 𝟘∧𝟙-elim
  (λ q → 𝟙 ⊛ q ▷ 𝟘 ≡ q)
  (λ _ → refl)
  (λ _ → refl)

-- The star operation returns results that are at least as large as
-- those of the star operation of any modality for
-- Zero-one-many-setoid for which the zero is 𝟘, the one is 𝟙,
-- addition is _+_, multiplication is _·_, and the meet operation is
-- _∧_.

⊛-greatest :
  (M : Modality) →
  Modality.𝟘   M ≡ 𝟘 →
  Modality.𝟙   M ≡ 𝟙 →
  Modality._+_ M ≡ _+_ →
  Modality._·_ M ≡ _·_ →
  Modality._∧_ M ≡ _∧_ →
  ∀ p q r → Modality._⊛_▷_ M p q r ≤ p ⊛ q ▷ r
⊛-greatest M refl refl refl refl refl = λ where
    ω q r → begin
      ω ⊛ q ▷′ r  ≈⟨ reqs .proj₁ ⟩
      ω           ∎
    p ω r → begin
      p ⊛ ω ▷′ r  ≈⟨ reqs .proj₂ .proj₁ ⟩
      ω           ≈˘⟨ ⊛ω▷ p ⟩
      p ⊛ ω ▷ r   ∎
    𝟘 𝟘 r → begin
      𝟘 ⊛ 𝟘 ▷′ r  ≈⟨ reqs .proj₂ .proj₂ .proj₂ .proj₁ ⟩
      𝟘           ∎
    𝟘 𝟙 ω → begin
      𝟘 ⊛ 𝟙 ▷′ ω  ≈⟨ reqs .proj₂ .proj₂ .proj₁ (λ { (_ , ()) }) ⟩
      ω           ≈˘⟨ ⊛▷ω 𝟘 𝟙 (λ { (_ , ()) }) ⟩
      𝟘 ⊛ 𝟙 ▷ ω   ∎
    𝟙 q ω → begin
      𝟙 ⊛ q ▷′ ω  ≈⟨ reqs .proj₂ .proj₂ .proj₁ (λ { (() , _) }) ⟩
      ω           ≈˘⟨ ⊛▷ω 𝟙 q (λ { (() , _) }) ⟩
      𝟙 ⊛ q ▷ ω   ∎
    p 𝟙 𝟙 → begin
      p ⊛ 𝟙 ▷′ 𝟙  ≈⟨ reqs .proj₂ .proj₂ .proj₂ .proj₂ .proj₁ ⟩
      ω           ≈˘⟨ ⊛𝟙▷𝟙 p ⟩
      p ⊛ 𝟙 ▷ 𝟙   ∎
    𝟘 𝟙 𝟘 → begin
      𝟘 ⊛ 𝟙 ▷′ 𝟘  ≤⟨ reqs .proj₂ .proj₂ .proj₂ .proj₂ .proj₂ .proj₁ ⟩
      𝟘 ∧ 𝟙       ∎
    𝟙 𝟘 𝟘 → begin
      𝟙 ⊛ 𝟘 ▷′ 𝟘  ≤⟨ reqs .proj₂ .proj₂ .proj₂ .proj₂ .proj₂ .proj₂ .proj₁ ⟩
      𝟘 ∧ 𝟙       ∎
    𝟙 𝟘 𝟙 → begin
      𝟙 ⊛ 𝟘 ▷′ 𝟙  ≤⟨ reqs .proj₂ .proj₂ .proj₂ .proj₂ .proj₂ .proj₂ .proj₂ .proj₁ ⟩
      𝟙           ∎
    𝟙 𝟙 𝟘 → begin
      𝟙 ⊛ 𝟙 ▷′ 𝟘  ≤⟨ reqs .proj₂ .proj₂ .proj₂ .proj₂ .proj₂ .proj₂ .proj₂ .proj₂ ⟩
      𝟙           ∎
  where
  open Modality M using (modalityWithout⊛) renaming (_⊛_▷_ to _⊛_▷′_)
  open PartialOrder modalityWithout⊛
  open Tools.Reasoning.PartialOrder ≤-poset

  reqs : Star-requirements _⊛_▷′_ _∧_
  reqs = Star-requirements-required M refl refl refl refl refl

-- The zero-one-many modality (with arbitrary "restrictions").
--
-- The star operation is the "greatest" one defined above.

zero-one-many-greatest : Restrictions → Modality
zero-one-many-greatest restrictions = record
  { modalityWithout⊛       = modalityWithout⊛
  ; _⊛_▷_                  = _⊛_▷_
  ; ⊛-ineq                 = ⊛-ineq₁ , ⊛-ineq₂
  ; ⊛-cong                 = λ where
                               refl refl refl → refl
  ; +-sub-interchangable-⊛ = +-sub-interchangeable-⊛
  ; ·-sub-distribʳ-⊛       = ·-sub-distribʳ-⊛
  ; ⊛-sub-distrib-∧        = λ _ → ⊛-sub-distrib-∧ˡ _
                                 , ⊛-sub-distrib-∧ʳ _
  ; ⊛≤𝟘ˡ                   = λ eq → ≤-reflexive (⊛≈𝟘 _ _ _ eq .proj₁)
  ; ⊛≤𝟘ʳ                   = λ {p = p} eq →
                               ≤-reflexive (⊛≈𝟘 p _ _ eq .proj₂)
  }
  where
  modalityWithout⊛ = zero-one-many-without-⊛ restrictions

  open ModalityWithout⊛ modalityWithout⊛
    hiding (𝟘; 𝟙; _+_; _·_; _∧_; _≤_)
  open PartialOrder modalityWithout⊛
  open Meet modalityWithout⊛
  open Tools.Reasoning.PartialOrder ≤-poset

  ⊛-ineq₁ : ∀ p q r → p ⊛ q ▷ r ≤ q + r · p ⊛ q ▷ r
  ⊛-ineq₁ = λ where
    𝟘 𝟘 r → begin
      𝟘          ≈˘⟨ ·-zeroʳ _ ⟩
      r · 𝟘      ≈˘⟨ +-identityˡ _ ⟩
      𝟘 + r · 𝟘  ∎
    ω _ _ → ≤-refl
    𝟘 ω _ → ≤-refl
    𝟙 ω _ → ≤-refl
    𝟘 𝟙 ω → ≤-refl
    𝟙 𝟘 ω → ≤-refl
    𝟙 𝟙 ω → ≤-refl
    𝟘 𝟙 𝟙 → ≤-refl
    𝟙 𝟙 𝟙 → ≤-refl
    𝟙 𝟘 𝟙 → ≤-refl
    𝟙 𝟙 𝟘 → ≤-refl
    𝟘 𝟙 𝟘 → begin
      𝟘∧𝟙  ≤⟨ ∧-decreasingʳ 𝟘 𝟙 ⟩
      𝟙    ∎
    𝟙 𝟘 𝟘 → begin
      𝟘∧𝟙  ≤⟨ ∧-decreasingˡ 𝟘 𝟙 ⟩
      𝟘    ∎

  ⊛-ineq₂ : ∀ p q r → (p ⊛ q ▷ r) ≤ p
  ⊛-ineq₂ = λ where
    𝟘 𝟘 _ → ≤-refl
    ω _ _ → ≤-refl
    𝟘 ω _ → ≤-refl
    𝟙 ω _ → ≤-refl
    𝟘 𝟙 ω → ≤-refl
    𝟙 𝟘 ω → ≤-refl
    𝟙 𝟙 ω → ≤-refl
    𝟘 𝟙 𝟙 → ≤-refl
    𝟙 𝟙 𝟙 → ≤-refl
    𝟙 𝟘 𝟙 → ≤-refl
    𝟙 𝟙 𝟘 → ≤-refl
    𝟘 𝟙 𝟘 → begin
      𝟘∧𝟙  ≤⟨ ∧-decreasingˡ 𝟘 𝟙 ⟩
      𝟘    ∎
    𝟙 𝟘 𝟘 → begin
      𝟘∧𝟙  ≤⟨ ∧-decreasingʳ 𝟘 𝟙 ⟩
      𝟙    ∎

  ⊛≈𝟘 : ∀ p q r → p ⊛ q ▷ r ≡ 𝟘 → p ≡ 𝟘 × q ≡ 𝟘
  ⊛≈𝟘 = λ where
    𝟘 𝟘 _ _     → refl , refl
    𝟘 𝟙 𝟘 𝟘∧𝟙≡𝟘 → ⊥-elim (𝟘∧𝟙≢𝟘 𝟘∧𝟙≡𝟘)
    𝟙 𝟘 𝟘 𝟘∧𝟙≡𝟘 → ⊥-elim (𝟘∧𝟙≢𝟘 𝟘∧𝟙≡𝟘)
    ω _ _ ()
    𝟘 ω _ ()
    𝟙 ω _ ()
    𝟘 𝟙 ω ()
    𝟙 𝟘 ω ()
    𝟙 𝟙 ω ()
    𝟘 𝟙 𝟙 ()
    𝟙 𝟙 𝟙 ()
    𝟙 𝟘 𝟙 ()
    𝟙 𝟙 𝟘 ()

  ·-sub-distribʳ-⊛ : ∀ r → _·_ SubDistributesOverʳ (_⊛_▷ r) by _≤_
  ·-sub-distribʳ-⊛ = λ where
    _ _ 𝟘 𝟘 → refl
    _ 𝟘 ω 𝟘 → refl
    _ 𝟘 ω 𝟙 → refl
    _ 𝟘 ω ω → refl
    _ 𝟙 ω _ → refl
    _ ω ω _ → refl
    _ 𝟘 𝟘 ω → refl
    _ 𝟙 𝟘 ω → refl
    _ ω 𝟘 ω → refl
    _ 𝟘 𝟙 ω → refl
    _ 𝟙 𝟙 ω → refl
    _ ω 𝟙 ω → refl
    ω 𝟘 𝟘 𝟙 → refl
    ω 𝟙 𝟘 𝟙 → refl
    ω ω 𝟘 𝟙 → refl
    ω 𝟘 𝟙 𝟘 → refl
    ω 𝟙 𝟙 𝟘 → refl
    ω ω 𝟙 𝟘 → refl
    ω 𝟘 𝟙 𝟙 → refl
    ω 𝟙 𝟙 𝟙 → refl
    ω ω 𝟙 𝟙 → refl
    𝟙 𝟘 𝟘 𝟙 → refl
    𝟙 𝟙 𝟘 𝟙 → refl
    𝟙 ω 𝟘 𝟙 → refl
    𝟙 𝟘 𝟙 𝟙 → refl
    𝟙 𝟙 𝟙 𝟙 → refl
    𝟙 ω 𝟙 𝟙 → refl
    𝟙 𝟘 𝟙 𝟘 → refl
    𝟙 𝟙 𝟙 𝟘 → refl
    𝟙 ω 𝟙 𝟘 → refl
    𝟘 𝟘 𝟙 𝟙 → refl
    𝟘 𝟙 𝟙 𝟙 → refl
    𝟘 ω 𝟙 𝟙 → refl
    𝟘 𝟘 𝟘 𝟙 → begin
      𝟘∧𝟙 · 𝟘  ≈⟨ ·-zeroʳ _ ⟩
      𝟘        ∎
    𝟘 𝟙 𝟘 𝟙 → begin
      𝟘∧𝟙 · 𝟙  ≈⟨ ·-identityʳ _ ⟩
      𝟘∧𝟙      ∎
    𝟘 ω 𝟘 𝟙 → begin
      𝟘∧𝟙 · ω  ≈⟨ ·-comm _ _ ⟩
      ω · 𝟘∧𝟙  ≈⟨ ω·≢𝟘 𝟘∧𝟙≢𝟘 ⟩
      ω        ∎
    𝟘 𝟘 𝟙 𝟘 → begin
      𝟘∧𝟙 · 𝟘  ≈⟨ ·-zeroʳ _ ⟩
      𝟘        ∎
    𝟘 𝟙 𝟙 𝟘 → begin
      𝟘∧𝟙 · 𝟙  ≈⟨ ·-identityʳ _ ⟩
      𝟘∧𝟙      ∎
    𝟘 ω 𝟙 𝟘 → begin
      𝟘∧𝟙 · ω  ≈⟨ ·-comm _ _ ⟩
      ω · 𝟘∧𝟙  ≈⟨ ω·≢𝟘 𝟘∧𝟙≢𝟘 ⟩
      ω        ∎

  ⊛-sub-distrib-∧ˡ : ∀ r → (_⊛_▷ r) SubDistributesOverˡ _∧_ by _≤_
  ⊛-sub-distrib-∧ˡ = λ where
    _ 𝟘 𝟘 𝟘 → refl
    𝟘 𝟘 𝟘 𝟙 → begin
      𝟘 ⊛ 𝟘∧𝟙 ▷ 𝟘            ≤⟨ ⊛-ineq₁ 𝟘 𝟘∧𝟙 _ ⟩
      𝟘∧𝟙 + 𝟘 · 𝟘 ⊛ 𝟘∧𝟙 ▷ 𝟘  ≡⟨⟩
      𝟘∧𝟙 + 𝟘                ≈⟨ +-identityʳ _ ⟩
      𝟘∧𝟙                    ≈˘⟨ 𝟘∧[𝟘∧𝟙] ⟩
      𝟘 ∧ 𝟘∧𝟙                ∎
    𝟙 𝟘 𝟘 𝟙 → begin
      𝟘 ⊛ 𝟘∧𝟙 ▷ 𝟙  ≡⟨ ⊛𝟘∧𝟙▷𝟙 𝟘 ⟩
      ω            ∎
    ω 𝟘 𝟘 𝟙 → begin
      𝟘 ⊛ 𝟘∧𝟙 ▷ ω  ≡⟨ ⊛▷ω 𝟘 𝟘∧𝟙 (λ (_ , 𝟘∧𝟙≡𝟘) → 𝟘∧𝟙≢𝟘 𝟘∧𝟙≡𝟘) ⟩
      ω            ∎
    _ 𝟘 𝟘 ω → refl
    _ ω _ _ → refl
    _ 𝟘 ω _ → refl
    _ 𝟙 ω _ → refl
    ω 𝟘 𝟙 𝟘 → begin
      𝟘 ⊛ 𝟘∧𝟙 ▷ ω  ≡⟨ ⊛▷ω 𝟘 𝟘∧𝟙 (λ (_ , 𝟘∧𝟙≡𝟘) → 𝟘∧𝟙≢𝟘 𝟘∧𝟙≡𝟘) ⟩
      ω            ∎
    ω 𝟘 𝟙 𝟙 → refl
    ω 𝟘 𝟙 ω → refl
    ω 𝟙 𝟘 𝟘 → refl
    ω 𝟙 𝟘 𝟙 → begin
      𝟙 ⊛ 𝟘∧𝟙 ▷ ω  ≡⟨ ⊛▷ω 𝟙 𝟘∧𝟙 (λ (_ , 𝟘∧𝟙≡𝟘) → 𝟘∧𝟙≢𝟘 𝟘∧𝟙≡𝟘) ⟩
      ω            ∎
    ω 𝟙 𝟘 ω → refl
    ω 𝟙 𝟙 𝟘 → begin
      𝟙 ⊛ 𝟘∧𝟙 ▷ ω  ≡⟨ ⊛▷ω 𝟙 𝟘∧𝟙 (λ (_ , 𝟘∧𝟙≡𝟘) → 𝟘∧𝟙≢𝟘 𝟘∧𝟙≡𝟘) ⟩
      ω            ∎
    ω 𝟙 𝟙 𝟙 → refl
    ω 𝟙 𝟙 ω → refl
    𝟙 𝟘 𝟙 𝟘 → begin
      𝟘 ⊛ 𝟘∧𝟙 ▷ 𝟙  ≡⟨ ⊛𝟘∧𝟙▷𝟙 𝟘 ⟩
      ω            ∎
    𝟙 𝟘 𝟙 𝟙 → refl
    𝟙 𝟘 𝟙 ω → refl
    𝟙 𝟙 𝟙 𝟘 → begin
      𝟙 ⊛ 𝟘∧𝟙 ▷ 𝟙  ≡⟨ ⊛𝟘∧𝟙▷𝟙 𝟙 ⟩
      ω            ∎
    𝟙 𝟙 𝟙 𝟙 → refl
    𝟙 𝟙 𝟙 ω → refl
    𝟙 𝟙 𝟘 𝟘 → refl
    𝟙 𝟙 𝟘 𝟙 → begin
      𝟙 ⊛ 𝟘∧𝟙 ▷ 𝟙  ≡⟨ ⊛𝟘∧𝟙▷𝟙 𝟙 ⟩
      ω            ∎
    𝟙 𝟙 𝟘 ω → refl
    𝟘 𝟙 𝟙 𝟘 → begin
      𝟙 ⊛ 𝟘∧𝟙 ▷ 𝟘  ≈⟨ 𝟙⊛𝟘∧𝟙▷𝟘 ⟩
      𝟘∧𝟙          ≈˘⟨ 𝟙∧[𝟘∧𝟙] ⟩
      𝟙 ∧ 𝟘∧𝟙      ∎
    𝟘 𝟙 𝟙 𝟙 → refl
    𝟘 𝟙 𝟙 ω → refl
    𝟘 𝟘 𝟙 𝟘 → begin
      𝟘 ⊛ 𝟘∧𝟙 ▷ 𝟘  ≈⟨ 𝟘⊛𝟘∧𝟙▷𝟘 ⟩
      𝟘∧𝟙          ≈˘⟨ 𝟘∧[𝟘∧𝟙] ⟩
      𝟘 ∧ 𝟘∧𝟙      ≈⟨ ∧-comm 𝟘 𝟘∧𝟙 ⟩
      𝟘∧𝟙 ∧ 𝟘      ∎
    𝟘 𝟘 𝟙 𝟙 → begin
      𝟘∧𝟙        ≈˘⟨ ∧-idem _ ⟩
      𝟘∧𝟙 ∧ 𝟘∧𝟙  ∎
    𝟘 𝟘 𝟙 ω → refl
    𝟘 𝟙 𝟘 𝟘 → begin
      𝟘∧𝟙        ≈˘⟨ ∧-idem _ ⟩
      𝟘∧𝟙 ∧ 𝟘∧𝟙  ∎
    𝟘 𝟙 𝟘 𝟙 → begin
      𝟙 ⊛ 𝟘∧𝟙 ▷ 𝟘  ≈⟨ 𝟙⊛𝟘∧𝟙▷𝟘 ⟩
      𝟘∧𝟙          ≈˘⟨ 𝟙∧[𝟘∧𝟙] ⟩
      𝟙 ∧ 𝟘∧𝟙      ≈⟨ ∧-comm 𝟙 𝟘∧𝟙 ⟩
      𝟘∧𝟙 ∧ 𝟙      ∎
    𝟘 𝟙 𝟘 ω → refl

  𝟙≤𝟘-⊛-monotone : ∀ q r → 𝟙 ≤ 𝟘 → 𝟙 ⊛ q ▷ r ≤ 𝟘 ⊛ q ▷ r
  𝟙≤𝟘-⊛-monotone ω _ _   = refl
  𝟙≤𝟘-⊛-monotone 𝟘 ω _   = ω≤ 𝟘
  𝟙≤𝟘-⊛-monotone 𝟘 𝟙 𝟙≤𝟘 = 𝟙≤𝟘
  𝟙≤𝟘-⊛-monotone 𝟙 ω _   = refl
  𝟙≤𝟘-⊛-monotone 𝟙 𝟙 _   = refl
  𝟙≤𝟘-⊛-monotone 𝟘 𝟘 _   = begin
    𝟘∧𝟙  ≤⟨ ∧-decreasingˡ 𝟘 𝟙 ⟩
    𝟘    ∎
  𝟙≤𝟘-⊛-monotone 𝟙 𝟘 𝟙≤𝟘 = begin
    𝟙      ≡⟨⟩
    𝟙 ∧ 𝟙  ≤⟨ ∧-monotoneˡ {q = 𝟘} {r = 𝟙} 𝟙≤𝟘 ⟩
    𝟘∧𝟙    ∎

  ⊛-sub-distrib-∧ʳ-lemma :
    ∀ q r → 𝟘∧𝟙 ⊛ q ▷ r ≤ 𝟘 ⊛ q ▷ r ∧ 𝟙 ⊛ q ▷ r
  ⊛-sub-distrib-∧ʳ-lemma q r = 𝟘∧𝟙-elim
    (λ p → p ⊛ q ▷ r ≤ 𝟘 ⊛ q ▷ r ∧ 𝟙 ⊛ q ▷ r)
    (λ 𝟘∧𝟙≡𝟙 →
       let 𝟙≤𝟘 = begin
             𝟙    ≡˘⟨ 𝟘∧𝟙≡𝟙 ⟩
             𝟘∧𝟙  ≤⟨ ∧-decreasingˡ 𝟘 𝟙 ⟩
             𝟘    ∎
       in begin
         𝟙 ⊛ q ▷ r              ≈˘⟨ ∧-idem _ ⟩
         𝟙 ⊛ q ▷ r ∧ 𝟙 ⊛ q ▷ r  ≤⟨ ∧-monotoneˡ (𝟙≤𝟘-⊛-monotone q r 𝟙≤𝟘) ⟩
         𝟘 ⊛ q ▷ r ∧ 𝟙 ⊛ q ▷ r  ∎)
    (λ _ → refl)

  ⊛-sub-distrib-∧ʳ : ∀ r → (_⊛_▷ r) SubDistributesOverʳ _∧_ by _≤_
  ⊛-sub-distrib-∧ʳ = λ where
    r q 𝟘 𝟘 → begin
      𝟘 ⊛ q ▷ r              ≈˘⟨ ∧-idem _ ⟩
      𝟘 ⊛ q ▷ r ∧ 𝟘 ⊛ q ▷ r  ∎
    _ _ 𝟘 𝟙 → ⊛-sub-distrib-∧ʳ-lemma _ _
    _ _ 𝟘 ω → refl
    r q 𝟙 𝟘 → begin
      𝟘∧𝟙 ⊛ q ▷ r            ≤⟨ ⊛-sub-distrib-∧ʳ-lemma _ _ ⟩
      𝟘 ⊛ q ▷ r ∧ 𝟙 ⊛ q ▷ r  ≈⟨ ∧-comm (𝟘 ⊛ q ▷ _) _ ⟩
      𝟙 ⊛ q ▷ r ∧ 𝟘 ⊛ q ▷ r  ∎
    r 𝟘 𝟙 𝟙 → begin
      𝟙 ⊛ 𝟘 ▷ r              ≈˘⟨ ∧-idem _ ⟩
      𝟙 ⊛ 𝟘 ▷ r ∧ 𝟙 ⊛ 𝟘 ▷ r  ∎
    r 𝟙 𝟙 𝟙 → begin
      𝟙 ⊛ 𝟙 ▷ r              ≈˘⟨ ∧-idem _ ⟩
      𝟙 ⊛ 𝟙 ▷ r ∧ 𝟙 ⊛ 𝟙 ▷ r  ∎
    _ ω 𝟙 𝟙 → refl
    _ _ 𝟙 ω → refl
    _ _ ω _ → refl

  ≢𝟘+≢𝟘≤ : p ≢ 𝟘 → q ≢ 𝟘 → p + q ≤ r
  ≢𝟘+≢𝟘≤ {p = p} {q = q} {r = r} p≢𝟘 q≢𝟘 = begin
    p + q  ≡⟨ ≢𝟘+≢𝟘 p≢𝟘 q≢𝟘 ⟩
    ω      ≤⟨ ω≤ r ⟩
    r      ∎

  +-sub-interchangeable-⊛ : ∀ r → _+_ SubInterchangable (_⊛_▷ r) by _≤_
  +-sub-interchangeable-⊛ = λ where
    _ ω _ _ _ → refl
    _ 𝟘 ω _ _ → refl
    ω 𝟘 𝟙 _ _ → refl
    𝟙 𝟘 𝟙 _ _ → refl
    _ 𝟙 ω _ _ → refl
    ω 𝟙 𝟘 _ _ → refl
    𝟙 𝟙 𝟙 _ _ → refl
    ω 𝟙 𝟙 _ _ → refl
    _ 𝟘 𝟘 _ _ → ≤-refl
    𝟘 𝟘 𝟙 𝟘 𝟘 → begin
      𝟘∧𝟙 + 𝟘  ≈⟨ +-identityʳ _ ⟩
      𝟘∧𝟙      ∎
    𝟘 𝟘 𝟙 𝟘 𝟙 → ≢𝟘+≢𝟘≤ 𝟘∧𝟙≢𝟘 𝟘∧𝟙≢𝟘
    𝟘 𝟘 𝟙 𝟘 ω → ≢𝟘+≢𝟘≤ 𝟘∧𝟙≢𝟘 (λ ())
    𝟘 𝟘 𝟙 𝟙 𝟘 → ≢𝟘+≢𝟘≤ 𝟘∧𝟙≢𝟘 𝟘∧𝟙≢𝟘
    𝟘 𝟘 𝟙 𝟙 𝟙 → ≢𝟘+≢𝟘≤ 𝟘∧𝟙≢𝟘 (λ ())
    𝟘 𝟘 𝟙 𝟙 ω → ≢𝟘+≢𝟘≤ 𝟘∧𝟙≢𝟘 (λ ())
    𝟘 𝟘 𝟙 ω _ → ≢𝟘+≢𝟘≤ 𝟘∧𝟙≢𝟘 (λ ())
    𝟘 𝟙 𝟘 𝟘 𝟘 → begin
      𝟘∧𝟙 + 𝟘  ≈⟨ +-identityʳ _ ⟩
      𝟘∧𝟙      ∎
    𝟘 𝟙 𝟘 𝟘 𝟙 → ≢𝟘+≢𝟘≤ 𝟘∧𝟙≢𝟘 𝟘∧𝟙≢𝟘
    𝟘 𝟙 𝟘 𝟘 ω → ≢𝟘+≢𝟘≤ 𝟘∧𝟙≢𝟘 (λ ())
    𝟘 𝟙 𝟘 𝟙 𝟘 → ≢𝟘+≢𝟘≤ 𝟘∧𝟙≢𝟘 𝟘∧𝟙≢𝟘
    𝟘 𝟙 𝟘 𝟙 𝟙 → ≢𝟘+≢𝟘≤ 𝟘∧𝟙≢𝟘 (λ ())
    𝟘 𝟙 𝟘 𝟙 ω → ≢𝟘+≢𝟘≤ 𝟘∧𝟙≢𝟘 (λ ())
    𝟘 𝟙 𝟘 ω _ → ≢𝟘+≢𝟘≤ 𝟘∧𝟙≢𝟘 (λ ())
    𝟙 𝟙 𝟘 𝟘 𝟘 → refl
    𝟙 𝟙 𝟘 𝟘 𝟙 → refl
    𝟙 𝟙 𝟘 𝟘 ω → refl
    𝟙 𝟙 𝟘 𝟙 𝟘 → refl
    𝟙 𝟙 𝟘 𝟙 𝟙 → refl
    𝟙 𝟙 𝟘 𝟙 ω → refl
    𝟙 𝟙 𝟘 ω _ → refl
    𝟘 𝟙 𝟙 𝟘 𝟘 → refl
    𝟘 𝟙 𝟙 𝟘 𝟙 → ≢𝟘+≢𝟘≤ (λ ()) 𝟘∧𝟙≢𝟘
    𝟘 𝟙 𝟙 𝟘 ω → refl
    𝟘 𝟙 𝟙 𝟙 𝟘 → ≢𝟘+≢𝟘≤ (λ ()) 𝟘∧𝟙≢𝟘
    𝟘 𝟙 𝟙 𝟙 𝟙 → refl
    𝟘 𝟙 𝟙 𝟙 ω → refl
    𝟘 𝟙 𝟙 ω _ → refl
