------------------------------------------------------------------------
-- The zero-one-many modality
------------------------------------------------------------------------

-- Based on Conor McBride's "I Got Plenty o’ Nuttin’".

-- It might make sense to replace some of the proofs with automated
-- proofs.

open import Tools.Bool using (Bool; true; false; if_then_else_; T)

module Graded.Modality.Instances.Zero-one-many
  -- Should 𝟙 be below 𝟘?
  (𝟙≤𝟘 : Bool)
  where
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
import Graded.Modality.Instances.LowerBounded as LowerBounded
import Graded.Modality.Properties.Addition as Addition
import Graded.Modality.Properties.Greatest-lower-bound as GLB
import Graded.Modality.Properties.Meet as Meet
import Graded.Modality.Properties.Multiplication as Multiplication
import Graded.Modality.Properties.PartialOrder as PartialOrder
import Graded.Modality.Properties.Star as Star
import Graded.Modality.Properties.Natrec as Natrec
import Graded.Modality.Properties.Subtraction as Subtraction
import Graded.Context
import Graded.Context.Properties

------------------------------------------------------------------------
-- The type

-- Zero, one or many.

data Zero-one-many : Set where
  𝟘 𝟙 ω : Zero-one-many

private variable
  n n₁ n₂ p p₁ p₂ q r result s s₁ s₂ z z₁ z₂ : Zero-one-many

open Graded.Modality Zero-one-many
open Tools.Algebra   Zero-one-many

-- A decision procedure for equality.

infix 10 _≟_

_≟_ : Decidable (_≡_ {A = Zero-one-many})
𝟘 ≟ 𝟘 = yes refl
𝟘 ≟ 𝟙 = no (λ ())
𝟘 ≟ ω = no (λ ())
𝟙 ≟ 𝟘 = no (λ ())
𝟙 ≟ 𝟙 = yes refl
𝟙 ≟ ω = no (λ ())
ω ≟ 𝟘 = no (λ ())
ω ≟ 𝟙 = no (λ ())
ω ≟ ω = yes refl

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

-- The meet operation of a "Modality" for Zero-one-many for
-- which the zero is 𝟘, the one is 𝟙, ω ≤ p for all p
-- and 𝟘 ∧ 𝟙 ≢ 𝟘 has to satisfy the Meet-requirements.

Meet-requirements-required :
  (M : Modality) →
  Modality.𝟘          M ≡ 𝟘 →
  Modality.𝟙          M ≡ 𝟙 →
  Modality._∧_ M    𝟘 𝟙 ≢ 𝟘 →
  (∀ p → Modality._≤_ M ω p) →
  Meet-requirements (Modality._∧_ M)
Meet-requirements-required M@record{} refl refl 𝟘∧𝟙≢𝟘 ω≤ =
    (𝟘 ∧ 𝟘  ≡⟨ ∧-idem _ ⟩
     𝟘      ∎)
  , (𝟙 ∧ 𝟙  ≡⟨ ∧-idem _ ⟩
     𝟙      ∎)
  , (ω ∧ ω  ≡⟨ ∧-idem _ ⟩
     ω      ∎)
  , (𝟘 ∧ ω  ≡⟨ ∧-comm _ _ ⟩
     ω ∧ 𝟘  ≡˘⟨ ω≤ 𝟘 ⟩
     ω      ∎)
  , (ω ∧ 𝟘  ≡˘⟨ ω≤ 𝟘 ⟩
     ω      ∎)
  , (𝟙 ∧ ω  ≡⟨ ∧-comm _ _ ⟩
     ω ∧ 𝟙  ≡˘⟨ ω≤ 𝟙 ⟩
     ω      ∎)
  , (ω ∧ 𝟙  ≡˘⟨ ω≤ 𝟙 ⟩
     ω      ∎)
  , 𝟘∧𝟙≢𝟘
  , (λ 𝟙∧𝟘≡𝟘 → 𝟘∧𝟙≢𝟘 (
       𝟘 ∧ 𝟙  ≡⟨ ∧-comm _ _ ⟩
       𝟙 ∧ 𝟘  ≡⟨ 𝟙∧𝟘≡𝟘 ⟩
       𝟘      ∎))
  where
  open Modality M hiding (𝟘; 𝟙; ω)
  open Meet M
  open PartialOrder M
  open Tools.Reasoning.PropositionalEquality

-- The result of 𝟘 ∧ 𝟙 and 𝟙 ∧ 𝟘.

𝟘∧𝟙 : Zero-one-many
𝟘∧𝟙 = if 𝟙≤𝟘 then 𝟙 else ω

-- Meet.

infixr 43 _∧_

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
  lemma true  _  = refl
  lemma false ()

-- If 𝟘∧𝟙 ≡ 𝟙, then 𝟙≤𝟘 is true.

𝟘∧𝟙≡𝟙→𝟙≤𝟘 : 𝟘∧𝟙 ≡ 𝟙 → T 𝟙≤𝟘
𝟘∧𝟙≡𝟙→𝟙≤𝟘 = lemma _
  where
  lemma : ∀ b → (if b then 𝟙 else ω) ≡ 𝟙 → T b
  lemma true  _  = _
  lemma false ()

-- If 𝟙≤𝟘 is false, then 𝟘∧𝟙 ≡ ω.

𝟘∧𝟙≡ω : ¬ T 𝟙≤𝟘 → 𝟘∧𝟙 ≡ ω
𝟘∧𝟙≡ω = lemma _
  where
  lemma : ∀ b → ¬ T b → (if b then 𝟙 else ω) ≡ ω
  lemma false _  = refl
  lemma true  ¬⊤ = ⊥-elim (¬⊤ _)

-- If 𝟘∧𝟙 ≢ 𝟙, then 𝟙≤𝟘 is false.

𝟘∧𝟙≢𝟙→𝟙≰𝟘 : 𝟘∧𝟙 ≢ 𝟙 → ¬ T 𝟙≤𝟘
𝟘∧𝟙≢𝟙→𝟙≰𝟘 = lemma _
  where
  lemma : ∀ b → (if b then 𝟙 else ω) ≢ 𝟙 → ¬ T b
  lemma true  𝟙≢𝟙 = λ _ → 𝟙≢𝟙 refl
  lemma false _   = idᶠ

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

-- The value ω is a right zero for _∧_.

∧-zeroʳ : RightZero ω _∧_
∧-zeroʳ 𝟘 = refl
∧-zeroʳ 𝟙 = refl
∧-zeroʳ ω = refl

-- The value ω is a zero for _∧_.

∧-zero : Zero ω _∧_
∧-zero = (λ _ → refl) , ∧-zeroʳ

-- If p ∧ q is 𝟙, then at least one of p and q is 𝟙, and if the other
-- one is not 𝟙, then it is 𝟘, and 𝟙 ≤ 𝟘.

∧≡𝟙 :
  p ∧ q ≡ 𝟙 →
  p ≡ 𝟘 × q ≡ 𝟙 × T 𝟙≤𝟘 ⊎
  p ≡ 𝟙 × q ≡ 𝟘 × T 𝟙≤𝟘 ⊎
  p ≡ 𝟙 × q ≡ 𝟙
∧≡𝟙 {p = 𝟘} {q = 𝟙} eq = inj₁ (refl , refl , 𝟘∧𝟙≡𝟙→𝟙≤𝟘 eq)
∧≡𝟙 {p = 𝟙} {q = 𝟘} eq = inj₂ (inj₁ (refl , refl , 𝟘∧𝟙≡𝟙→𝟙≤𝟘 eq))
∧≡𝟙 {p = 𝟙} {q = 𝟙} _  = inj₂ (inj₂ (refl , refl))
∧≡𝟙 {p = 𝟘} {q = 𝟘} ()
∧≡𝟙 {p = 𝟘} {q = ω} ()
∧≡𝟙 {p = 𝟙} {q = ω} ()
∧≡𝟙 {p = ω}         ()

opaque

  -- 𝟙 ∧ p is not equal to 𝟘

  𝟙∧p≢𝟘 : ∀ p → 𝟙 ∧ p ≢ 𝟘
  𝟙∧p≢𝟘 𝟘 = 𝟘∧𝟙≢𝟘
  𝟙∧p≢𝟘 𝟙 = λ ()
  𝟙∧p≢𝟘 ω = λ ()

------------------------------------------------------------------------
-- Ordering

-- Some requirements of an ordering relation.

Order-requirements : (Zero-one-many → Zero-one-many → Set) → Set
Order-requirements _≤_ = (ω ≤ 𝟙) × (ω ≤ 𝟘) × ¬ (𝟘 ≤ 𝟙)

-- The ordering relation of a "Modality" for Zero-one-many for
-- which the zero is 𝟘, the one is 𝟙 and p ∧ ω equals ω for all p
-- has to satisfy the Order-requirements.

Order-requirements-required :
  (M : Modality) →
  Modality.𝟘          M ≡ 𝟘 →
  Modality.𝟙          M ≡ 𝟙 →
  Modality._∧_ M    𝟘 𝟙 ≢ 𝟘 →
  (∀ p → Modality._≤_ M ω p) →
  Order-requirements (Modality._≤_ M)
Order-requirements-required M@record{} refl refl 𝟘∧𝟙≢𝟘 ω≤ =
  case Meet-requirements-required M refl refl 𝟘∧𝟙≢𝟘 ω≤ of λ where
    (_ , _ , _ , _ , ω⊓𝟘≡ω , _ , ω⊓𝟙≡ω , 𝟘⊓𝟙≢𝟘 , _) →
        (ω      ≡˘⟨ ω⊓𝟙≡ω ⟩
         ω ⊓ 𝟙  ∎)
      , (ω      ≡˘⟨ ω⊓𝟘≡ω ⟩
         ω ⊓ 𝟘  ∎)
      , (λ 𝟘≡𝟘⊓𝟙 → 𝟘⊓𝟙≢𝟘 (
           𝟘 ⊓ 𝟙  ≡˘⟨ 𝟘≡𝟘⊓𝟙 ⟩
           𝟘      ∎))
  where
  open Modality M using () renaming (_∧_ to _⊓_)
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
𝟘-maximal {p = ω} ()
𝟘-maximal {p = 𝟘} refl = refl
𝟘-maximal {p = 𝟙}      = 𝟘∧𝟙-elim
  (λ q → 𝟘 ≡ q → 𝟙 ≡ 𝟘)
  (λ _ → sym)
  (λ _ ())

-- 𝟘 is not below 𝟘∧𝟙.

𝟘≰𝟘∧𝟙 : ¬ 𝟘 ≤ 𝟘∧𝟙
𝟘≰𝟘∧𝟙 = 𝟘∧𝟙≢𝟘 ∘→ 𝟘-maximal

-- If 𝟙≤𝟘 is true, then 𝟙 ≤ 𝟘.

𝟙≤𝟘→𝟙≤𝟘 : T 𝟙≤𝟘 → 𝟙 ≤ 𝟘
𝟙≤𝟘→𝟙≤𝟘 𝟙≤𝟘 =
  𝟙      ≡˘⟨ 𝟘∧𝟙≡𝟙 𝟙≤𝟘 ⟩
  𝟙 ∧ 𝟘  ∎
  where
  open Tools.Reasoning.PropositionalEquality

-- If 𝟙≤𝟘 is false, then 𝟙 is maximal.

𝟙-maximal : ¬ T 𝟙≤𝟘 → 𝟙 ≤ p → p ≡ 𝟙
𝟙-maximal {p = ω} _   ()
𝟙-maximal {p = 𝟙} _   refl = refl
𝟙-maximal {p = 𝟘} 𝟙≰𝟘 𝟙≤𝟘  = ⊥-elim (
  case
    𝟙      ≡⟨ 𝟙≤𝟘 ⟩
    𝟙 ∧ 𝟘  ≡⟨ 𝟘∧𝟙≡ω 𝟙≰𝟘 ⟩
    ω      ∎
  of λ ())
  where
  open Tools.Reasoning.PropositionalEquality

opaque

  -- Non-zero grades are less than or equal to 𝟙

  ≢𝟘→≤𝟙 : ∀ p → p ≢ 𝟘 → p ≤ 𝟙
  ≢𝟘→≤𝟙 𝟘 p≢𝟘 = ⊥-elim (p≢𝟘 refl)
  ≢𝟘→≤𝟙 𝟙 p≢𝟘 = refl
  ≢𝟘→≤𝟙 ω p≢𝟘 = refl

------------------------------------------------------------------------
-- Addition

-- Addition.

infixr 40 _+_

_+_ : Zero-one-many → Zero-one-many → Zero-one-many
𝟘 + q = q
𝟙 + 𝟘 = 𝟙
_ + _ = ω

-- If 𝟙≤𝟘 is true, then _+_ is decreasing in its left argument.

+-decreasingˡ : T 𝟙≤𝟘 → ∀ p q → p + q ≤ p
+-decreasingˡ 𝟙≤𝟘 = λ where
  𝟘 𝟘 → refl
  𝟘 𝟙 → 𝟙≤𝟘→𝟙≤𝟘 𝟙≤𝟘
  𝟘 ω → refl
  𝟙 𝟘 → refl
  𝟙 𝟙 → refl
  𝟙 ω → refl
  ω _ → refl

-- If 𝟙≤𝟘 is not true, then _+_ is not decreasing in its left argument.

¬-+-decreasingˡ : ¬ T 𝟙≤𝟘 → ¬ (∀ p q → p + q ≤ p)
¬-+-decreasingˡ 𝟙≰𝟘 hyp =
  case 𝟙-maximal {p = 𝟘} 𝟙≰𝟘 (hyp 𝟘 𝟙) of λ ()

-- The sum of two non-zero values is ω.

≢𝟘+≢𝟘 : p ≢ 𝟘 → q ≢ 𝟘 → p + q ≡ ω
≢𝟘+≢𝟘 {p = 𝟘}         𝟘≢𝟘 _   = ⊥-elim (𝟘≢𝟘 refl)
≢𝟘+≢𝟘 {p = 𝟙} {q = 𝟘} _   𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 refl)
≢𝟘+≢𝟘 {p = 𝟙} {q = 𝟙} _   _   = refl
≢𝟘+≢𝟘 {p = 𝟙} {q = ω} _   _   = refl
≢𝟘+≢𝟘 {p = ω}         _   _   = refl

-- If p + q is 𝟙, then either p is 𝟙 and q is 𝟘, or q is 𝟙 and p is 𝟘.

+≡𝟙 : p + q ≡ 𝟙 → p ≡ 𝟙 × q ≡ 𝟘 ⊎ p ≡ 𝟘 × q ≡ 𝟙
+≡𝟙 {p = 𝟘} {q = 𝟙} refl = inj₂ (refl , refl)
+≡𝟙 {p = 𝟙} {q = 𝟘} refl = inj₁ (refl , refl)
+≡𝟙 {p = 𝟘} {q = 𝟘} ()
+≡𝟙 {p = 𝟘} {q = ω} ()
+≡𝟙 {p = 𝟙} {q = 𝟙} ()
+≡𝟙 {p = 𝟙} {q = ω} ()
+≡𝟙 {p = ω}         ()

-- The value ω is a right zero for _+_.

+-zeroʳ : RightZero ω _+_
+-zeroʳ 𝟘 = refl
+-zeroʳ 𝟙 = refl
+-zeroʳ ω = refl

-- The value ω is a zero for _+_.

+-zero : Zero ω _+_
+-zero = (λ _ → refl) , +-zeroʳ

------------------------------------------------------------------------
-- Multiplication

-- Multiplication.

infixr 45 _·_

_·_ : Zero-one-many → Zero-one-many → Zero-one-many
𝟘 · _ = 𝟘
_ · 𝟘 = 𝟘
𝟙 · 𝟙 = 𝟙
_ · _ = ω

-- Multiplication is idempotent.

·-idempotent : Idempotent _·_
·-idempotent 𝟘 = refl
·-idempotent 𝟙 = refl
·-idempotent ω = refl

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

opaque

  -- If p is not 𝟘, then p · ω is equal to ω.

  ≢𝟘·ω : p ≢ 𝟘 → p · ω ≡ ω
  ≢𝟘·ω {(𝟘)} 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 refl)
  ≢𝟘·ω {(𝟙)} _ = refl
  ≢𝟘·ω {(ω)} _ = refl

-- If p is not 𝟘, then 𝟙 · p is not 𝟘.

𝟙·≢𝟘 : p ≢ 𝟘 → 𝟙 · p ≢ 𝟘
𝟙·≢𝟘 {p = 𝟘} 𝟘≢𝟘 = 𝟘≢𝟘
𝟙·≢𝟘 {p = 𝟙} 𝟙≢𝟘 = 𝟙≢𝟘
𝟙·≢𝟘 {p = ω} ω≢𝟘 = ω≢𝟘

-- The value of ω · p is not 𝟙.

ω·≢𝟙 : ω · p ≢ 𝟙
ω·≢𝟙 {p = 𝟘} ()
ω·≢𝟙 {p = 𝟙} ()
ω·≢𝟙 {p = ω} ()

opaque

  -- The grade ω · (p + q) is bounded by ω · q.

  ω·+≤ω·ʳ : ∀ p → ω · (p + q) ≤ ω · q
  ω·+≤ω·ʳ {q = 𝟘} 𝟘 = refl
  ω·+≤ω·ʳ {q = 𝟙} 𝟘 = refl
  ω·+≤ω·ʳ {q = ω} 𝟘 = refl
  ω·+≤ω·ʳ {q = 𝟘} 𝟙 = refl
  ω·+≤ω·ʳ {q = 𝟙} 𝟙 = refl
  ω·+≤ω·ʳ {q = ω} 𝟙 = refl
  ω·+≤ω·ʳ         ω = refl

------------------------------------------------------------------------
-- The modality

-- The zero-one-many modality

zero-one-many-modality : Modality
zero-one-many-modality = record
  { _+_          = _+_
  ; _·_          = _·_
  ; _∧_          = _∧_
  ; 𝟘            = 𝟘
  ; 𝟙            = 𝟙
  ; ω            = ω
  ; ω≤𝟙          = refl
  ; ω·+≤ω·ʳ      = λ {p = p} → ω·+≤ω·ʳ p
  ; is-𝟘?        = _≟ 𝟘
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
              , comm∧idˡ⇒idʳ +-comm (λ _ → refl)
          }
        ; comm = +-comm
        }
        ; *-cong = cong₂ _·_
        ; *-assoc = λ where
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
        ; *-identity =
                ·-identityˡ
              , comm∧idˡ⇒idʳ ·-comm ·-identityˡ
      ; distrib =
            ·-distrib-+ˡ
          , comm∧distrˡ⇒distrʳ ·-comm ·-distrib-+ˡ
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
      , comm∧distrˡ⇒distrʳ ·-comm ·-distrib-∧ˡ
  ; +-distrib-∧ =
        +-distrib-∧ˡ
      , comm∧distrˡ⇒distrʳ +-comm +-distrib-∧ˡ
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

instance

  zero-one-many-has-well-behaved-zero :
    Has-well-behaved-zero zero-one-many-modality
  zero-one-many-has-well-behaved-zero = record
    { non-trivial = λ ()
    ; zero-product =  λ where
        {p = 𝟘}         _  → inj₁ refl
        {q = 𝟘}         _  → inj₂ refl
        {p = 𝟙} {q = 𝟙} ()
        {p = 𝟙} {q = ω} ()
        {p = ω} {q = 𝟙} ()
        {p = ω} {q = ω} ()
    ; +-positiveˡ =  λ where
        {p = 𝟘} {q = 𝟘} _  → refl
        {p = 𝟘} {q = 𝟙} ()
        {p = 𝟘} {q = ω} ()
        {p = 𝟙} {q = 𝟘} ()
        {p = 𝟙} {q = 𝟙} ()
        {p = 𝟙} {q = ω} ()
        {p = ω}         ()
    ; ∧-positiveˡ = λ where
        {p = 𝟘} {q = 𝟘} _     → refl
        {p = 𝟘} {q = 𝟙} _     → refl
        {p = 𝟙} {q = 𝟘} 𝟘∧𝟙≡𝟘 →
          ⊥-elim (
            case
              𝟙  ≡⟨ 𝟘-maximal (sym 𝟘∧𝟙≡𝟘) ⟩
              𝟘  ∎
            of λ ())
        {p = 𝟘} {q = ω} ()
        {p = 𝟙} {q = 𝟙} ()
        {p = 𝟙} {q = ω} ()
        {p = ω}         ()
    }
    where open Tools.Reasoning.PropositionalEquality

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

-- A star operation for a Modality for Zero-one-many for
-- which the zero is 𝟘, the one is 𝟙, addition is _+_, multiplication
-- is _·_, and the meet operation is _∧_ has to satisfy the
-- Star-requirements (for _∧_) if certain conditions are satisfied.

Star-requirements-required′ :
  (M : Modality) →
  Modality.𝟘   M ≡ 𝟘 →
  Modality.𝟙   M ≡ 𝟙 →
  Modality._+_ M ≡ _+_ →
  Modality._·_ M ≡ _·_ →
  Modality._∧_ M ≡ _∧_ →
  (_⊛_▷_ :
   Zero-one-many → Zero-one-many → Zero-one-many → Zero-one-many) →
  (∀ p q r → (p ⊛ q ▷ r) ≤ q + r · (p ⊛ q ▷ r)) →
  (∀ p q r → (p ⊛ q ▷ r) ≤ p) →
  (∀ r → _·_ SubDistributesOverʳ (_⊛_▷ r) by _≤_) →
  Star-requirements _⊛_▷_ _∧_
Star-requirements-required′
  M@record{} refl refl refl refl refl star ⊛-ineq₁ ⊛-ineq₂
  ·-sub-distribʳ-⊛ =
  case Meet-requirements-required M refl refl 𝟘∧𝟙≢𝟘 ω≤ of λ where
    (_ , _ , ω⊓ω≡ω , _ , ω⊓𝟘≡ω , _ , ω⊓𝟙≡ω , _ , _) →
        (λ {_ _} → ω⊛▷)
      , (λ {_ _} → ⊛ω▷)
      , (λ {_ _} → ⊛▷ω _ _)
      , (λ {r = r} → ≤-antisym
           (begin
              𝟘 ⊛ 𝟘 ▷ r  ≤⟨ ⊛-ineq₂ _ _ _ ⟩
              𝟘          ∎)
           (begin
              𝟘              ≡˘⟨ ·-zeroʳ _ ⟩
              𝟘 ⊛ 𝟘 ▷ r · 𝟘  ≤⟨ ·-sub-distribʳ-⊛ _ _ _ _ ⟩
              𝟘 ⊛ 𝟘 ▷ r      ∎))
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
  open Modality M hiding (𝟘; 𝟙; ω; _+_; _·_; _∧_; _≤_)
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
  𝟙⊛▷ {q = q} {r = r} 𝟙⊛▷≡𝟘 =
    case begin
      𝟘              ≡⟨⟩
      𝟘 · ω          ≡˘⟨ ·-congʳ 𝟙⊛▷≡𝟘 ⟩
      𝟙 ⊛ q ▷ r · ω  ≤⟨ ·-sub-distribʳ-⊛ _ _ _ _ ⟩
      ω ⊛ q · ω ▷ r  ≡⟨ ω⊛▷ ⟩
      ω              ∎
    of λ ()

  ⊛𝟙▷ : p ⊛ 𝟙 ▷ r ≢ 𝟘
  ⊛𝟙▷ {p = p} {r = r} ⊛𝟙▷≡𝟘 =
    case begin
      𝟘                ≡⟨⟩
      𝟘 · ω            ≡˘⟨ ·-congʳ ⊛𝟙▷≡𝟘 ⟩
      p ⊛ 𝟙 ▷ r · ω    ≤⟨ ·-sub-distribʳ-⊛ _ _ _ _ ⟩
      (p · ω) ⊛ ω ▷ r  ≡⟨ ⊛ω▷ ⟩
      ω                ∎
    of λ ()

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

-- Every natrec-star operator for zero-one-many-modality has
-- to satisfy the Star-requirements (for _∧_).

Star-requirements-required :
  (has-star : Has-star zero-one-many-modality) →
  Star-requirements (Has-star._⊛_▷_ has-star) _∧_
Star-requirements-required has-star =
  Star-requirements-required′
    zero-one-many-modality refl refl refl refl refl
    _⊛_▷_
    ⊛-ineq₁
    ⊛-ineq₂
    ·-sub-distribʳ-⊛
  where
  open Has-star has-star

------------------------------------------------------------------------
-- A star opaerator for the modality

-- A natrec-star operator defined using the construction in
-- Graded.Modality.Instances.LowerBounded.

zero-one-many-lower-bounded-star :
  Has-star zero-one-many-modality
zero-one-many-lower-bounded-star =
  LowerBounded.has-star zero-one-many-modality ω ω≤

-- With this definition the result of p ⊛ q ▷ r is 𝟘 when p and q are
-- 𝟘, and ω otherwise.

zero-one-many-lower-bounded-⊛ :
  let open Has-star zero-one-many-lower-bounded-star in
  (∀ r → 𝟘 ⊛ 𝟘 ▷ r ≡ 𝟘) ×
  (∀ p q r → ¬ (p ≡ 𝟘 × q ≡ 𝟘) → p ⊛ q ▷ r ≡ ω)
zero-one-many-lower-bounded-⊛ =
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
  open Has-star zero-one-many-lower-bounded-star
  open Tools.Reasoning.PropositionalEquality

------------------------------------------------------------------------
-- A "greatest" star operation for the modality

-- A "greatest" definition of the star operation.

infix 50 _⊛_▷_

_⊛_▷_ : Zero-one-many → Zero-one-many → Zero-one-many → Zero-one-many
p ⊛ q ▷ 𝟘 = p ∧ q
p ⊛ q ▷ 𝟙 = p + ω · q
p ⊛ q ▷ ω = ω · (p ∧ q)

-- This definition is not equal to the one obtained from
-- zero-one-many-lower-bounded-star.

lower-bounded≢greatest :
  Has-star._⊛_▷_ zero-one-many-lower-bounded-star ≢ _⊛_▷_
lower-bounded≢greatest hyp =
  case cong (λ f → f 𝟙 𝟙 𝟘) hyp of λ ()

-- A simplification lemma for the star operation.

ω⊛▷ : ∀ r → ω ⊛ q ▷ r ≡ ω
ω⊛▷ 𝟘 = refl
ω⊛▷ 𝟙 = refl
ω⊛▷ ω = refl

-- A simplification lemma for the star operation.

⊛ω▷ : ∀ r → p ⊛ ω ▷ r ≡ ω
⊛ω▷ {p = p} = λ where
    𝟘 →
      p ∧ ω  ≡⟨ M.∧-comm p _ ⟩
      ω ∧ p  ≡⟨⟩
      ω      ∎
    𝟙 →
      p + ω  ≡⟨ M.+-comm p _ ⟩
      ω + p  ≡⟨⟩
      ω      ∎
    ω →
      ω · (p ∧ ω)  ≡⟨ cong (_ ·_) (M.∧-comm p _) ⟩
      ω · (ω ∧ p)  ≡⟨⟩
      ω            ∎
  where
  open Tools.Reasoning.PropositionalEquality
  module M = Modality zero-one-many-modality

-- A simplification lemma for the star operation.

𝟘⊛𝟘▷ : ∀ r → 𝟘 ⊛ 𝟘 ▷ r ≡ 𝟘
𝟘⊛𝟘▷ 𝟘 = refl
𝟘⊛𝟘▷ 𝟙 = refl
𝟘⊛𝟘▷ ω = refl

-- A simplification lemma for the star operation.

⊛▷ω : ∀ p q → ¬ (p ≡ 𝟘 × q ≡ 𝟘) → (p ⊛ q ▷ ω) ≡ ω
⊛▷ω p ω _      = ⊛ω▷ {p = p} ω
⊛▷ω ω _ _      = refl
⊛▷ω 𝟘 𝟘 ¬≡𝟘×≡𝟘 = ⊥-elim (¬≡𝟘×≡𝟘 (refl , refl))
⊛▷ω 𝟘 𝟙 _      = ω·≢𝟘 𝟘∧𝟙≢𝟘
⊛▷ω 𝟙 𝟙 _      = refl
⊛▷ω 𝟙 𝟘 _      = ω·≢𝟘 𝟘∧𝟙≢𝟘

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

-- The natrec-star operator returns results that are at least as large
-- as those of any other natrec-star operator for
-- zero-one-many-modality.

⊛-greatest :
  (has-star : Has-star zero-one-many-modality) →
  ∀ p q r → Has-star._⊛_▷_ has-star p q r ≤ p ⊛ q ▷ r
⊛-greatest has-star =
  case Star-requirements-required has-star of λ where
    (ω⊛▷′ , ⊛ω▷′ , ⊛▷′ω ,
     𝟘⊛𝟘▷′ , ⊛𝟙▷′𝟙 , 𝟘⊛𝟙▷′𝟘 , 𝟙⊛𝟘▷′𝟘 , 𝟙⊛𝟘▷′𝟙 , 𝟙⊛𝟙▷′𝟘) → λ where
      ω q r → begin
        ω ⊛ q ▷′ r  ≈⟨ ω⊛▷′ ⟩
        ω           ≈˘⟨ ω⊛▷ r ⟩
        ω ⊛ q ▷ r   ∎
      p ω r → begin
        p ⊛ ω ▷′ r  ≈⟨ ⊛ω▷′ ⟩
        ω           ≈˘⟨ ⊛ω▷ r ⟩
        p ⊛ ω ▷ r   ∎
      𝟘 𝟘 r → begin
        𝟘 ⊛ 𝟘 ▷′ r  ≈⟨ 𝟘⊛𝟘▷′ ⟩
        𝟘           ≈˘⟨ 𝟘⊛𝟘▷ r ⟩
        𝟘 ⊛ 𝟘 ▷ r   ∎
      𝟘 𝟙 ω → begin
        𝟘 ⊛ 𝟙 ▷′ ω  ≈⟨ ⊛▷′ω (λ { (_ , ()) }) ⟩
        ω           ≈˘⟨ ⊛▷ω 𝟘 𝟙 (λ { (_ , ()) }) ⟩
        𝟘 ⊛ 𝟙 ▷ ω   ∎
      𝟙 q ω → begin
        𝟙 ⊛ q ▷′ ω  ≈⟨ ⊛▷′ω (λ { (() , _) }) ⟩
        ω           ≈˘⟨ ⊛▷ω 𝟙 q (λ { (() , _) }) ⟩
        𝟙 ⊛ q ▷ ω   ∎
      p 𝟙 𝟙 → begin
        p ⊛ 𝟙 ▷′ 𝟙  ≈⟨ ⊛𝟙▷′𝟙 ⟩
        ω           ≈˘⟨ ⊛𝟙▷𝟙 p ⟩
        p ⊛ 𝟙 ▷ 𝟙   ∎
      𝟘 𝟙 𝟘 → begin
        𝟘 ⊛ 𝟙 ▷′ 𝟘  ≤⟨ 𝟘⊛𝟙▷′𝟘 ⟩
        𝟘 ∧ 𝟙       ∎
      𝟙 𝟘 𝟘 → begin
        𝟙 ⊛ 𝟘 ▷′ 𝟘  ≤⟨ 𝟙⊛𝟘▷′𝟘 ⟩
        𝟘 ∧ 𝟙       ∎
      𝟙 𝟘 𝟙 → begin
        𝟙 ⊛ 𝟘 ▷′ 𝟙  ≤⟨ 𝟙⊛𝟘▷′𝟙 ⟩
        𝟙           ∎
      𝟙 𝟙 𝟘 → begin
        𝟙 ⊛ 𝟙 ▷′ 𝟘  ≤⟨ 𝟙⊛𝟙▷′𝟘 ⟩
        𝟙           ∎
  where
  open Has-star has-star renaming (_⊛_▷_ to _⊛_▷′_)
  open PartialOrder zero-one-many-modality
  open Tools.Reasoning.PartialOrder ≤-poset

-- The "greatest" star operator defined above is a proper natrec-star
-- operator.

zero-one-many-greatest-star : Has-star zero-one-many-modality
zero-one-many-greatest-star = record
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

  open Modality zero-one-many-modality
    hiding (𝟘; 𝟙; ω; _+_; _·_; _∧_; _≤_)
  open PartialOrder zero-one-many-modality
  open Addition zero-one-many-modality
  open Meet zero-one-many-modality
  open Multiplication zero-one-many-modality

  ⊛-ineq₁ : ∀ p q r → p ⊛ q ▷ r ≤ q + r · p ⊛ q ▷ r
  ⊛-ineq₁ p = λ where
      q 𝟘 → begin
        p ∧ q  ≤⟨ ∧-decreasingʳ p _ ⟩
        q      ≈˘⟨ +-identityʳ _ ⟩
        q + 𝟘  ∎
      𝟘 𝟙 → begin
        p ⊛ 𝟘 ▷ 𝟙      ≈˘⟨ ·-identityˡ _ ⟩
        𝟙 · p ⊛ 𝟘 ▷ 𝟙  ∎
      𝟙 𝟙 → begin
        p + ω            ≈⟨ +-zeroʳ _ ⟩
        ω                ≡⟨⟩
        𝟙 + 𝟙 · ω        ≈˘⟨ cong (λ p → 𝟙 + 𝟙 · p) (+-zeroʳ p) ⟩
        𝟙 + 𝟙 · (p + ω)  ∎
      ω 𝟙 → begin
        p + ω  ≈⟨ +-zeroʳ _ ⟩
        ω      ∎
      𝟘 ω → begin
        ω · (p ∧ 𝟘)        ≡⟨⟩
        (ω · ω) · (p ∧ 𝟘)  ≈⟨ ·-assoc _ _ _ ⟩
        ω · ω · (p ∧ 𝟘)    ∎
      𝟙 ω → begin
        ω · (p ∧ 𝟙)          ≈⟨ ·-distribˡ-∧ _ p _ ⟩
        ω · p ∧ ω            ≈⟨ ∧-comm (ω · p) _ ⟩
        ω ∧ ω · p            ≡⟨⟩
        ω                    ≡⟨⟩
        𝟙 + ω · ω            ≈⟨ cong (λ p → _ + ω · p) (∧-comm _ (ω · p)) ⟩
        𝟙 + ω · (ω · p ∧ ω)  ≈˘⟨ cong (λ p → _ + ω · p) (·-distribˡ-∧ ω p _) ⟩
        𝟙 + ω · ω · (p ∧ 𝟙)  ∎
      ω ω → begin
        ω · (p ∧ ω)  ≈⟨ ·-distribˡ-∧ _ p _ ⟩
        ω · p ∧ ω    ≤⟨ ∧-decreasingʳ (ω · p) _ ⟩
        ω            ∎
    where
    open Tools.Reasoning.PartialOrder ≤-poset

  ⊛-ineq₂ : ∀ p q r → (p ⊛ q ▷ r) ≤ p
  ⊛-ineq₂ p = λ where
      q 𝟘 → begin
        p ∧ q  ≤⟨ ∧-decreasingˡ p _ ⟩
        p      ∎
      𝟘 𝟙 → begin
        p + 𝟘  ≈⟨ +-identityʳ _ ⟩
        p      ∎
      𝟙 𝟙 → begin
        p + ω  ≈⟨ +-zeroʳ _ ⟩
        ω      ≤⟨ ω≤ p ⟩
        p      ∎
      ω 𝟙 → begin
        p + ω  ≈⟨ +-zeroʳ _ ⟩
        ω      ≤⟨ ω≤ p ⟩
        p      ∎
      q ω → begin
        ω · (p ∧ q)    ≈⟨ ·-distribˡ-∧ _ p _ ⟩
        ω · p ∧ ω · q  ≤⟨ ∧-decreasingˡ (ω · p) _ ⟩
        ω · p          ≤⟨ ·-monotoneˡ (ω≤ 𝟙) ⟩
        𝟙 · p          ≈⟨ ·-identityˡ _ ⟩
        p              ∎
    where
    open Tools.Reasoning.PartialOrder ≤-poset

  +-sub-interchangeable-⊛ : ∀ r → _+_ SubInterchangeable (_⊛_▷ r) by _≤_
  +-sub-interchangeable-⊛ = λ where
      𝟘 p q p′ q′ → begin
        (p ∧ q) + (p′ ∧ q′)  ≤⟨ +-sub-interchangeable-∧ p _ _ _ ⟩
        (p + p′) ∧ (q + q′)  ∎
      𝟙 p q p′ q′ → begin
        (p + ω · q) + (p′ + ω · q′)  ≈⟨ +-assoc p _ _ ⟩
        p + (ω · q + (p′ + ω · q′))  ≈˘⟨ cong (p +_) (+-assoc (ω · q) _ _) ⟩
        p + ((ω · q + p′) + ω · q′)  ≈⟨ cong (λ q → p + (q + _)) (+-comm _ p′) ⟩
        p + ((p′ + ω · q) + ω · q′)  ≈⟨ cong (p +_) (+-assoc p′ _ _) ⟩
        p + (p′ + (ω · q + ω · q′))  ≈˘⟨ +-assoc p _ _ ⟩
        (p + p′) + (ω · q + ω · q′)  ≈˘⟨ cong (_ +_) (·-distribˡ-+ ω q _) ⟩
        (p + p′) + ω · (q + q′)      ∎
      ω p q p′ q′ → begin
        ω · (p ∧ q) + ω · (p′ ∧ q′)  ≈˘⟨ ·-distribˡ-+ ω (p ∧ q) (p′ ∧ q′) ⟩
        ω · ((p ∧ q) + (p′ ∧ q′))    ≤⟨ ·-monotoneʳ (+-sub-interchangeable-∧ p q p′ q′) ⟩
        ω · ((p + p′) ∧ (q + q′))    ∎
    where
    open Tools.Reasoning.PartialOrder ≤-poset

  ·-distribʳ-⊛ : ∀ r → _·_ DistributesOverʳ (_⊛_▷ r)
  ·-distribʳ-⊛ = λ where
      𝟘 q p p′ →
        (p ∧ p′) · q    ≡⟨ ·-distribʳ-∧ _ p _ ⟩
        p · q ∧ p′ · q  ∎
      𝟙 q p p′ →
        (p + ω · p′) · q      ≡⟨ ·-distribʳ-+ _ p _ ⟩
        p · q + (ω · p′) · q  ≡⟨ cong (_ +_) (·-assoc ω p′ _) ⟩
        p · q + ω · p′ · q    ∎
      ω q p p′ →
        (ω · (p ∧ p′)) · q    ≡⟨ ·-assoc _ _ _ ⟩
        ω · (p ∧ p′) · q      ≡⟨ cong (_ ·_) (·-distribʳ-∧ _ p _) ⟩
        ω · (p · q ∧ p′ · q)  ∎
    where
    open Tools.Reasoning.PropositionalEquality

  ⊛-distribˡ-∧ : ∀ r → (_⊛_▷ r) DistributesOverˡ _∧_
  ⊛-distribˡ-∧ = λ where
      𝟘 p _ _ →
        lemma p _ _
      𝟙 p q q′ →
        p + ω · (q ∧ q′)            ≡⟨ cong (_ +_) (·-distribˡ-∧ ω q _) ⟩
        p + (ω · q ∧ ω · q′)        ≡⟨ +-distribˡ-∧ p _ _ ⟩
        (p + ω · q) ∧ (p + ω · q′)  ∎
      ω p q q′ →
        ω · (p ∧ q ∧ q′)            ≡⟨ cong (_ ·_) (lemma p _ _) ⟩
        ω · ((p ∧ q) ∧ (p ∧ q′))    ≡⟨ ·-distribˡ-∧ ω (p ∧ _) _ ⟩
        ω · (p ∧ q) ∧ ω · (p ∧ q′)  ∎
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
      𝟘 q p p′ →
        lemma _ p _
      𝟙 q p p′ →
        (p ∧ p′) + ω · q            ≡⟨ +-distribʳ-∧ _ p _ ⟩
        (p + ω · q) ∧ (p′ + ω · q)  ∎
      ω q p p′ →
        ω · ((p ∧ p′) ∧ q)          ≡⟨ cong (_ ·_) (lemma _ p _) ⟩
        ω · ((p ∧ q) ∧ (p′ ∧ q))    ≡⟨ ·-distribˡ-∧ ω (p ∧ _) _ ⟩
        ω · (p ∧ q) ∧ ω · (p′ ∧ q)  ∎
    where
    open Tools.Reasoning.PropositionalEquality

    lemma = λ q p p′ →
      (p ∧ p′) ∧ q        ≡⟨ ∧-comm _ q ⟩
      q ∧ (p ∧ p′)        ≡⟨ ⊛-distribˡ-∧ 𝟘 q _ _ ⟩
      (q ∧ p) ∧ (q ∧ p′)  ≡⟨ cong₂ _∧_ (∧-comm q _) (∧-comm q _) ⟩
      (p ∧ q) ∧ (p′ ∧ q)  ∎

-- The natrec-star operator obtained from
-- zero-one-many-lower-bounded-star is not the (pointwise) greatest
-- one.

¬-lower-bounded-greatest :
  ¬ ((has-star : Has-star zero-one-many-modality) →
     ∀ p q r →
     Has-star._⊛_▷_ has-star                         p q r ≤
     Has-star._⊛_▷_ zero-one-many-lower-bounded-star p q r)
¬-lower-bounded-greatest hyp =
  case hyp zero-one-many-greatest-star 𝟙 𝟙 𝟘 of λ ()

-- The "greatest" natrec-star operator defined above provides a
-- possible nr function.

zero-one-many-greatest-star-nr : Has-nr zero-one-many-modality
zero-one-many-greatest-star-nr =
  Star.has-nr _ ⦃ has-star = zero-one-many-greatest-star ⦄

opaque

  -- The nr function given by the "greatest" natrec-star operator does
  -- not give a "factoring" nr function.

  ¬zero-one-many-greatest-star-factoring-nr :
    ¬ Is-factoring-nr zero-one-many-greatest-star-nr
  ¬zero-one-many-greatest-star-factoring-nr factoring = case 𝟙≡ω of λ ()
    where
    open Has-nr zero-one-many-greatest-star-nr
    open Is-factoring-nr factoring
    open Modality zero-one-many-modality
      hiding (𝟘; 𝟙; ω; _+_; _·_)
    open Tools.Reasoning.PropositionalEquality
    𝟙≡ω : 𝟙 ≡ ω
    𝟙≡ω = begin
      𝟙                            ≡⟨⟩
      nr 𝟘 𝟙 𝟙 𝟘 𝟙                ≡⟨ nr-factoring {z = 𝟙} {s = 𝟘} ⟩
      nr₂ 𝟘 𝟙 · 𝟙 + nr 𝟘 𝟙 𝟙 𝟘 𝟘 ≡⟨⟩
      nr₂ 𝟘 𝟙 · 𝟙 + 𝟘∧𝟙 + 𝟘       ≡⟨ +-cong (·-identityʳ _) (+-identityʳ 𝟘∧𝟙) ⟩
      nr₂ 𝟘 𝟙 + 𝟘∧𝟙               ≡⟨ ≢𝟘+≢𝟘 nr₂≢𝟘 𝟘∧𝟙≢𝟘 ⟩
      ω ∎

------------------------------------------------------------------------
-- A custim nr function for the modality

-- An nr function for Zero-one-many.
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
--   Let us again use n + z for the zero case. If affine types are
--   used, then we use n + s for the successor case again, but if
--   linear types are used, then we use ω · n + s: the argument is not
--   used linearly in the successor case, because it is not used at
--   all, so if n is 𝟙, then the result should be ω (not 𝟙, because
--   the function is not linear, and not 𝟘, because that would amount
--   to an erased match on a natural number).
--
-- * If p = ω, then there are no (non-erased) recursive calls. In the
--   successor case the argument is used an unlimited number of times,
--   so we use ω · n + s. In the zero case we use n + z, as before.
--
-- All of these cases can be expressed in the following way (note that
-- 𝟙 ∧ 𝟘 is 𝟙 for affine types and ω for linear types):
--
--   nr p 𝟘 z s n = ((𝟙 ∧ p) · n + s) ∧ (n + z)
--
-- The value of nr p 𝟙 z s n is defined in the following way:
--
-- * If p = 𝟘, then we have linear or affine recursion: the argument
--   is used linearly or affinely (n), the successor case can occur an
--   unlimited number of times (ω · s), and the zero case occurs at
--   most once (z).
--
-- * If p = 𝟙 or p = ω, then there is recursion (ω · s), the argument
--   can be used in each recursive call (ω · n), and the zero case
--   occurs at most once (z).
--
-- We get the following definition:
--
--   nr p 𝟙 z s n = (𝟙 + p) · n + ω · s + z
--
-- Finally we use the following definition for nr p ω z s n:
--
--   nr _ ω z s n = ω · (n + s + z)
--
-- There is recursion (ω · s), in the successor case there can be
-- multiple recursive calls (ω · n), and the zero case can occur
-- multiple times (ω · z).

nr :
  Zero-one-many → Zero-one-many →
  Zero-one-many → Zero-one-many → Zero-one-many → Zero-one-many
nr p 𝟘 z s n = ((𝟙 ∧ p) · n + s) ∧ (n + z)
nr p 𝟙 z s n = (𝟙 + p) · n + ω · s + z
nr _ ω z s n = ω · (n + s + z)

-- An alternative implementation of nr.

nr′ :
  Zero-one-many → Zero-one-many →
  Zero-one-many → Zero-one-many → Zero-one-many → Zero-one-many
nr′ _ _ 𝟘 𝟘 𝟘 = 𝟘
nr′ _ 𝟘 𝟙 𝟙 𝟘 = 𝟙
nr′ _ 𝟘 𝟙 𝟘 𝟘 = 𝟙 ∧ 𝟘
nr′ _ 𝟙 𝟙 𝟘 𝟘 = 𝟙
nr′ _ 𝟘 𝟘 𝟙 𝟘 = 𝟙 ∧ 𝟘
nr′ 𝟙 𝟘 𝟘 𝟘 𝟙 = 𝟙
nr′ 𝟘 𝟘 𝟘 𝟘 𝟙 = 𝟙 ∧ 𝟘
nr′ 𝟘 𝟙 𝟘 𝟘 𝟙 = 𝟙
nr′ _ _ _ _ _ = ω

-- A type used in the implementation of Nr.

data Nr-ω : (p r z s n : Zero-one-many) → Set where
  nr≡ω₁  : Nr-ω p r ω s n
  nr≡ω₂  : Nr-ω p r z ω n
  nr≡ω₃  : Nr-ω p r z s ω
  nr≡ω₄  : Nr-ω p ω 𝟙 s n
  nr≡ω₅  : Nr-ω p ω 𝟘 𝟙 n
  nr≡ω₆  : Nr-ω p ω 𝟘 𝟘 𝟙
  nr≡ω₇  : Nr-ω ω 𝟘 𝟘 𝟘 𝟙
  nr≡ω₈  : Nr-ω ω 𝟙 𝟘 𝟘 𝟙
  nr≡ω₉  : Nr-ω 𝟙 𝟙 𝟘 𝟘 𝟙
  nr≡ω₁₀ : Nr-ω p 𝟘 𝟘 𝟙 𝟙
  nr≡ω₁₁ : Nr-ω p 𝟙 z 𝟙 n
  nr≡ω₁₂ : Nr-ω p 𝟘 𝟙 s 𝟙
  nr≡ω₁₃ : Nr-ω p 𝟙 𝟙 𝟘 𝟙

-- Another type used in the implementation of Nr.

data Nr-𝟙∧𝟘 : (p r z s n : Zero-one-many) → Set where
  nr≡𝟙∧𝟘₁ : Nr-𝟙∧𝟘 p 𝟘 𝟙 𝟘 𝟘
  nr≡𝟙∧𝟘₂ : Nr-𝟙∧𝟘 p 𝟘 𝟘 𝟙 𝟘
  nr≡𝟙∧𝟘₃ : Nr-𝟙∧𝟘 𝟘 𝟘 𝟘 𝟘 𝟙

-- A view of the functions nr and nr′.

data Nr : (p r z s n result : Zero-one-many) → Set where
  nr≡𝟘   :                    result ≡ 𝟘     → Nr p r 𝟘 𝟘 𝟘 result
  nr≡𝟙₁  :                    result ≡ 𝟙     → Nr p 𝟘 𝟙 𝟙 𝟘 result
  nr≡𝟙₂  :                    result ≡ 𝟙     → Nr p 𝟙 𝟙 𝟘 𝟘 result
  nr≡𝟙₃  :                                     Nr 𝟙 𝟘 𝟘 𝟘 𝟙 𝟙
  nr≡𝟙₄  :                                     Nr 𝟘 𝟙 𝟘 𝟘 𝟙 𝟙
  nr≡𝟙∧𝟘 : Nr-𝟙∧𝟘 p r z s n → result ≡ 𝟙 ∧ 𝟘 → Nr p r z s n result
  nr≡ω   : Nr-ω p r z s n   → result ≡ ω     → Nr p r z s n result

-- The view is correctly defined for nr′.

nr′-view : ∀ p r z s n → Nr p r z s n (nr′ p r z s n)
nr′-view = λ where
  _ _ 𝟘 𝟘 𝟘 → nr≡𝟘 refl
  _ 𝟘 𝟙 𝟙 𝟘 → nr≡𝟙₁ refl
  _ 𝟙 𝟙 𝟘 𝟘 → nr≡𝟙₂ refl
  𝟙 𝟘 𝟘 𝟘 𝟙 → nr≡𝟙₃
  𝟘 𝟙 𝟘 𝟘 𝟙 → nr≡𝟙₄
  _ 𝟘 𝟙 𝟘 𝟘 → nr≡𝟙∧𝟘 nr≡𝟙∧𝟘₁ refl
  _ 𝟘 𝟘 𝟙 𝟘 → nr≡𝟙∧𝟘 nr≡𝟙∧𝟘₂ refl
  𝟘 𝟘 𝟘 𝟘 𝟙 → nr≡𝟙∧𝟘 nr≡𝟙∧𝟘₃ refl
  _ _ ω _ _ → nr≡ω nr≡ω₁ refl
  _ _ 𝟘 ω _ → nr≡ω nr≡ω₂ refl
  _ 𝟘 𝟙 ω _ → nr≡ω nr≡ω₂ refl
  _ 𝟙 𝟙 ω _ → nr≡ω nr≡ω₂ refl
  _ _ 𝟘 𝟘 ω → nr≡ω nr≡ω₃ refl
  _ 𝟘 𝟘 𝟙 ω → nr≡ω nr≡ω₃ refl
  _ 𝟘 𝟙 𝟘 ω → nr≡ω nr≡ω₃ refl
  _ 𝟙 𝟙 𝟘 ω → nr≡ω nr≡ω₃ refl
  _ 𝟘 𝟙 𝟙 ω → nr≡ω nr≡ω₃ refl
  _ ω 𝟙 _ _ → nr≡ω nr≡ω₄ refl
  _ ω 𝟘 𝟙 _ → nr≡ω nr≡ω₅ refl
  𝟘 ω 𝟘 𝟘 𝟙 → nr≡ω nr≡ω₆ refl
  𝟙 ω 𝟘 𝟘 𝟙 → nr≡ω nr≡ω₆ refl
  ω ω 𝟘 𝟘 𝟙 → nr≡ω nr≡ω₆ refl
  ω 𝟘 𝟘 𝟘 𝟙 → nr≡ω nr≡ω₇ refl
  ω 𝟙 𝟘 𝟘 𝟙 → nr≡ω nr≡ω₈ refl
  𝟙 𝟙 𝟘 𝟘 𝟙 → nr≡ω nr≡ω₉ refl
  _ 𝟘 𝟘 𝟙 𝟙 → nr≡ω nr≡ω₁₀ refl
  _ 𝟙 𝟘 𝟙 _ → nr≡ω nr≡ω₁₁ refl
  _ 𝟙 𝟙 𝟙 _ → nr≡ω nr≡ω₁₁ refl
  _ 𝟘 𝟙 𝟘 𝟙 → nr≡ω nr≡ω₁₂ refl
  _ 𝟘 𝟙 𝟙 𝟙 → nr≡ω nr≡ω₁₂ refl
  _ 𝟙 𝟙 𝟘 𝟙 → nr≡ω nr≡ω₁₃ refl

-- The functions nr and nr′ are pointwise equal.

nr≡nr′ : ∀ p r → nr p r z s n ≡ nr′ p r z s n
nr≡nr′ p r = lemma _ _ _ _ _ (nr′-view p r _ _ _)
  where
  open Modality zero-one-many-modality
    hiding (𝟘; 𝟙; ω; _+_; _·_; _∧_)
  open Tools.Reasoning.PropositionalEquality

  lemma :
    ∀ p r z s n → Nr p r z s n (nr′ p r z s n) →
    nr p r z s n ≡ nr′ p r z s n
  lemma p 𝟘 .𝟘 .𝟘 .𝟘 (nr≡𝟘 _) =
    ((𝟙 ∧ p) · 𝟘 + 𝟘) ∧ 𝟘  ≡⟨ cong (_∧ _) (+-identityʳ ((𝟙 ∧ p) · _)) ⟩
    ((𝟙 ∧ p) · 𝟘) ∧ 𝟘      ≡⟨ cong (_∧ _) (·-zeroʳ (𝟙 ∧ p)) ⟩
    𝟘 ∧ 𝟘                  ≡⟨⟩
    𝟘                      ∎
  lemma p 𝟙 .𝟘 .𝟘 .𝟘 (nr≡𝟘 _) =
    (𝟙 + p) · 𝟘 + 𝟘  ≡⟨ +-identityʳ _ ⟩
    (𝟙 + p) · 𝟘      ≡⟨ ·-zeroʳ _ ⟩
    𝟘                ∎
  lemma _ ω .𝟘 .𝟘 .𝟘 (nr≡𝟘 _) =
    𝟘  ∎
  lemma p .𝟘 .𝟙 .𝟙 .𝟘 (nr≡𝟙₁ _) =
    ((𝟙 ∧ p) · 𝟘 + 𝟙) ∧ 𝟙  ≡⟨ cong ((_∧ _) ∘→ (_+ _)) (·-zeroʳ (𝟙 ∧ p)) ⟩
    (𝟘 + 𝟙) ∧ 𝟙            ≡⟨⟩
    𝟙                      ∎
  lemma p .𝟙 .𝟙 .𝟘 .𝟘 (nr≡𝟙₂ _) =
    (𝟙 + p) · 𝟘 + 𝟙  ≡⟨ cong (_+ _) (·-zeroʳ (𝟙 + p)) ⟩
    𝟘 + 𝟙            ≡⟨⟩
    𝟙                ∎
  lemma .𝟙 .𝟘 .𝟘 .𝟘 .𝟙 nr≡𝟙₃ =
    𝟙  ∎
  lemma .𝟘 .𝟙 .𝟘 .𝟘 .𝟙 nr≡𝟙₄ =
    𝟙  ∎
  lemma p .𝟘 .𝟙 .𝟘 .𝟘 (nr≡𝟙∧𝟘 nr≡𝟙∧𝟘₁ _) =
    ((𝟙 ∧ p) · 𝟘 + 𝟘) ∧ 𝟙  ≡⟨ cong (_∧ _) (+-identityʳ ((𝟙 ∧ p) · _)) ⟩
    ((𝟙 ∧ p) · 𝟘) ∧ 𝟙      ≡⟨ cong (_∧ _) (·-zeroʳ (𝟙 ∧ p)) ⟩
    𝟘 ∧ 𝟙                  ∎
  lemma p .𝟘 .𝟘 .𝟙 .𝟘 (nr≡𝟙∧𝟘 nr≡𝟙∧𝟘₂ _) =
    ((𝟙 ∧ p) · 𝟘 + 𝟙) ∧ 𝟘  ≡⟨ cong ((_∧ _) ∘→ (_+ _)) (·-zeroʳ (𝟙 ∧ p)) ⟩
    𝟙 ∧ 𝟘                  ≡⟨⟩
    𝟘 ∧ 𝟙                  ∎
  lemma .𝟘 .𝟘 .𝟘 .𝟘 .𝟙 (nr≡𝟙∧𝟘 nr≡𝟙∧𝟘₃ _) =
    ((𝟘 ∧ 𝟙) · 𝟙 + 𝟘) ∧ 𝟙  ≡⟨ cong (_∧ _) (+-identityʳ (𝟘∧𝟙 · _)) ⟩
    (𝟘 ∧ 𝟙) · 𝟙 ∧ 𝟙        ≡⟨ cong (_∧ _) (·-identityʳ 𝟘∧𝟙) ⟩
    (𝟘 ∧ 𝟙) ∧ 𝟙            ≡⟨ ∧-assoc 𝟘 𝟙 _ ⟩
    𝟘 ∧ (𝟙 ∧ 𝟙)            ≡⟨⟩
    𝟘 ∧ 𝟙                  ∎
  lemma p 𝟘 .ω s n (nr≡ω nr≡ω₁ _) =
    ((𝟙 ∧ p) · n + s) ∧ (n + ω)  ≡⟨ cong (((𝟙 ∧ p) · _ + _) ∧_) (+-zeroʳ _) ⟩
    ((𝟙 ∧ p) · n + s) ∧ ω        ≡⟨ ∧-zeroʳ ((𝟙 ∧ p) · _ + _) ⟩
    ω                            ∎
  lemma p 𝟙 .ω s n (nr≡ω nr≡ω₁ _) =
    (𝟙 + p) · n + ω · s + ω  ≡⟨ cong ((𝟙 + p) · _ +_) (+-zeroʳ _) ⟩
    (𝟙 + p) · n + ω          ≡⟨ +-zeroʳ _ ⟩
    ω                        ∎
  lemma p ω .ω s n (nr≡ω nr≡ω₁ _) =
    ω · (n + s + ω)      ≡⟨ ·-distribˡ-+ _ n _ ⟩
    ω · n + ω · (s + ω)  ≡⟨ cong (ω · n +_) (·-distribˡ-+ _ s _) ⟩
    ω · n + ω · s + ω    ≡⟨ cong (ω · n +_) (+-zeroʳ _) ⟩
    ω · n + ω            ≡⟨ +-zeroʳ _ ⟩
    ω                    ∎
  lemma p 𝟘 z .ω n (nr≡ω nr≡ω₂ ≡ω) =
    ((𝟙 ∧ p) · n + ω) ∧ (n + z)  ≡⟨ cong (_∧ _) (+-zeroʳ ((𝟙 ∧ p) · _)) ⟩
    ω ∧ (n + z)                  ≡⟨⟩
    ω                            ≡˘⟨ ≡ω ⟩
    nr′ p 𝟘 z ω n                ∎
  lemma p 𝟙 z .ω n (nr≡ω nr≡ω₂ ≡ω) =
    (𝟙 + p) · n + ω  ≡⟨ +-zeroʳ _ ⟩
    ω                ≡˘⟨ ≡ω ⟩
    nr′ p 𝟙 z ω n    ∎
  lemma p ω z .ω n (nr≡ω nr≡ω₂ ≡ω) =
    ω · (n + ω)    ≡⟨ ·-distribˡ-+ _ n _ ⟩
    ω · n + ω      ≡⟨ +-zeroʳ _ ⟩
    ω              ≡˘⟨ ≡ω ⟩
    nr′ p ω z ω n  ∎
  lemma p 𝟘 z s .ω (nr≡ω nr≡ω₃ ≡ω) =
    ((𝟙 ∧ p) · ω + s) ∧ ω  ≡⟨ ∧-zeroʳ ((𝟙 ∧ p) · _ + _) ⟩
    ω                      ≡˘⟨ ≡ω ⟩
    nr′ p 𝟘 z s ω          ∎
  lemma p 𝟙 z s .ω (nr≡ω nr≡ω₃ ≡ω) =
    (𝟙 + p) · ω + ω · s + z  ≡⟨ cong (_+ _) (·-distribʳ-+ _ 𝟙 p) ⟩
    (ω + p · ω) + ω · s + z  ≡⟨⟩
    ω                        ≡˘⟨ ≡ω ⟩
    nr′ p 𝟙 z s ω            ∎
  lemma p ω z s .ω (nr≡ω nr≡ω₃ ≡ω) =
    ω              ≡˘⟨ ≡ω ⟩
    nr′ p ω z s ω  ∎
  lemma p .ω .𝟙 s n (nr≡ω nr≡ω₄ _) =
    ω · (n + s + 𝟙)    ≡˘⟨ cong (ω ·_) (+-assoc n _ _) ⟩
    ω · ((n + s) + 𝟙)  ≡⟨ ·-distribˡ-+ _ (n + _) _ ⟩
    ω · (n + s) + ω    ≡⟨ +-zeroʳ _ ⟩
    ω                  ∎
  lemma p .ω .𝟘 .𝟙 n (nr≡ω nr≡ω₅ _) =
    ω · (n + 𝟙)  ≡⟨ ·-distribˡ-+ _ n _ ⟩
    ω · n + ω    ≡⟨ +-zeroʳ _ ⟩
    ω            ∎
  lemma p .ω .𝟘 .𝟘 .𝟙 (nr≡ω nr≡ω₆ ≡ω) =
    ω              ≡˘⟨ ≡ω ⟩
    nr′ p ω 𝟘 𝟘 𝟙  ∎
  lemma .ω 𝟘 .𝟘 .𝟘 .𝟙 (nr≡ω nr≡ω₇ _) =
    ω  ∎
  lemma .ω 𝟙 .𝟘 .𝟘 .𝟙 (nr≡ω nr≡ω₈ _) =
    ω  ∎
  lemma .𝟙 .𝟙 .𝟘 .𝟘 .𝟙 (nr≡ω nr≡ω₉ _) =
    ω  ∎
  lemma p .𝟘 .𝟘 .𝟙 .𝟙 (nr≡ω nr≡ω₁₀ _) =
    ((𝟙 ∧ p) · 𝟙 + 𝟙) ∧ 𝟙  ≡⟨ cong ((_∧ _) ∘→ (_+ _)) (·-distribʳ-∧ _ 𝟙 p) ⟩
    ((𝟙 ∧ p · 𝟙) + 𝟙) ∧ 𝟙  ≡⟨ cong ((_∧ _) ∘→ (_+ _) ∘→ (𝟙 ∧_)) (·-identityʳ p) ⟩
    ((𝟙 ∧ p) + 𝟙) ∧ 𝟙      ≡⟨ cong (_∧ _) (+-distribʳ-∧ _ 𝟙 p) ⟩
    (ω ∧ (p + 𝟙)) ∧ 𝟙      ≡⟨⟩
    ω                      ∎
  lemma p .𝟙 z .𝟙 n (nr≡ω nr≡ω₁₁ ≡ω) =
    (𝟙 + p) · n + ω  ≡⟨ +-zeroʳ _ ⟩
    ω                ≡˘⟨ ≡ω ⟩
    nr′ p 𝟙 z 𝟙 n    ∎
  lemma p .𝟘 .𝟙 s .𝟙 (nr≡ω nr≡ω₁₂ ≡ω) =
    ((𝟙 ∧ p) · 𝟙 + s) ∧ ω  ≡⟨ ∧-zeroʳ ((𝟙 ∧ p) · _ + _) ⟩
    ω                      ≡˘⟨ ≡ω ⟩
    nr′ p 𝟘 𝟙 s 𝟙          ∎
  lemma p .𝟙 .𝟙 .𝟘 .𝟙 (nr≡ω nr≡ω₁₃ _) =
    (𝟙 + p) · 𝟙 + 𝟙  ≡⟨ cong (_+ _) (·-distribʳ-+ _ 𝟙 p) ⟩
    (𝟙 + p · 𝟙) + 𝟙  ≡⟨ cong (_+ _) (+-comm _ (p · _)) ⟩
    (p · 𝟙 + 𝟙) + 𝟙  ≡⟨ +-assoc (p · _) _ _ ⟩
    p · 𝟙 + ω        ≡⟨ +-zeroʳ _ ⟩
    ω                ∎

-- The view is correctly defined for nr.

nr-view : ∀ p r z s n → Nr p r z s n (nr p r z s n)
nr-view p r z s n =             $⟨ nr′-view _ _ _ _ _ ⟩
  Nr p r z s n (nr′ p r z s n)  →⟨ subst (Nr _ _ _ _ _) (sym (nr≡nr′ p r)) ⟩
  Nr p r z s n (nr p r z s n)   □

-- The value of nr p r z s n is 𝟘 iff z, s and n are all zero.

nr-𝟘 : ∀ p r → nr p r z s n ≡ 𝟘 ⇔ (z ≡ 𝟘 × s ≡ 𝟘 × n ≡ 𝟘)
nr-𝟘 p r =
    lemma₁ (nr-view _ _ _ _ _)
  , λ { (refl , refl , refl) → lemma₂ p r }
  where
  open Modality zero-one-many-modality
    hiding (𝟘; 𝟙; _+_; _·_; _∧_)
  open Tools.Reasoning.PropositionalEquality

  lemma₁ : Nr p r z s n result → result ≡ 𝟘 → z ≡ 𝟘 × s ≡ 𝟘 × n ≡ 𝟘
  lemma₁ (nr≡𝟘 _)         refl = refl , refl , refl
  lemma₁ (nr≡𝟙∧𝟘 _ 𝟘≡𝟘∧𝟙) refl = ⊥-elim (𝟘∧𝟙≢𝟘 (sym 𝟘≡𝟘∧𝟙))
  lemma₁ (nr≡𝟙₁ ())       refl
  lemma₁ (nr≡𝟙₂ ())       refl
  lemma₁ nr≡𝟙₃            ()
  lemma₁ nr≡𝟙₄            ()
  lemma₁ (nr≡ω _ ())      refl

  lemma₂ : ∀ p r → nr p r 𝟘 𝟘 𝟘 ≡ 𝟘
  lemma₂ = λ where
    _ ω → refl
    ω 𝟙 → refl
    𝟙 𝟙 → refl
    𝟘 𝟙 → refl
    ω 𝟘 → refl
    𝟙 𝟘 → refl
    𝟘 𝟘 →
      ((𝟘 ∧ 𝟙) · 𝟘 + 𝟘) ∧ 𝟘  ≡⟨ cong (_∧ _) (+-identityʳ (𝟘∧𝟙 · _)) ⟩
      ((𝟘 ∧ 𝟙) · 𝟘) ∧ 𝟘      ≡⟨ cong (_∧ _) (·-zeroʳ 𝟘∧𝟙) ⟩
      𝟘 ∧ 𝟘                  ≡⟨⟩
      𝟘                      ∎

-- An nr function can be defined for zero-one-many-modality.

zero-one-many-has-nr : Has-nr zero-one-many-modality
zero-one-many-has-nr = record
  { nr          = nr
  ; nr-monotone = λ {p = p} {r = r} → nr-monotone p r
  ; nr-·        = λ {p = p} {r = r} → nr-· p r
  ; nr-+        = λ {p = p} {r = r} → nr-+ p r
  ; nr-positive = λ {p = p} {r = r} → nr-𝟘 p r .proj₁
  ; nr-zero     = λ {n = _} {p = p} {r = r} n≤𝟘 → nr-zero p r n≤𝟘
  ; nr-suc      = λ {p = p} {r = r} → nr-suc p r
  }
  where
  open Modality zero-one-many-modality
    hiding (𝟘; 𝟙; ω; _+_; _·_; _∧_; _≤_)
  open Addition zero-one-many-modality
  open Meet zero-one-many-modality
  open Multiplication zero-one-many-modality
  open PartialOrder zero-one-many-modality

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
        (+-monotone (·-monotoneʳ s₁≤s₂) z₁≤z₂)
    _ ω z₁≤z₂ s₁≤s₂ n₁≤n₂ →
      ·-monotoneʳ (+-monotone n₁≤n₂ (+-monotone s₁≤s₂ z₁≤z₂))

  nr-· : ∀ p r → nr p r z s n · q ≤ nr p r (z · q) (s · q) (n · q)
  nr-· {z = z} {s = s} {n = n} {q = q} p = λ where
      𝟘 → begin
        (((𝟙 ∧ p) · n + s) ∧ (n + z)) · q              ≡⟨ ·-distribʳ-∧ _ ((𝟙 ∧ p) · _ + _) _ ⟩
        ((𝟙 ∧ p) · n + s) · q ∧ (n + z) · q            ≡⟨ ∧-cong (·-distribʳ-+ _ ((𝟙 ∧ p) · _) _)
                                                            (·-distribʳ-+ _ n _) ⟩
        (((𝟙 ∧ p) · n) · q + s · q) ∧ (n · q + z · q)  ≡⟨ ∧-congʳ (+-congʳ (·-assoc (𝟙 ∧ p) _ _)) ⟩
        ((𝟙 ∧ p) · (n · q) + s · q) ∧ (n · q + z · q)  ∎
      𝟙 → begin
        ((𝟙 + p) · n + ω · s + z) · q            ≡⟨ ·-distribʳ-+ _ ((𝟙 + p) · _) _ ⟩
        ((𝟙 + p) · n) · q + (ω · s + z) · q      ≡⟨ +-congˡ (·-distribʳ-+ _ (ω · s) _) ⟩
        ((𝟙 + p) · n) · q + (ω · s) · q + z · q  ≡⟨ +-cong (·-assoc (𝟙 + p) _ _)
                                                      (+-congʳ (·-assoc ω s _)) ⟩
        (𝟙 + p) · (n · q) + ω · (s · q) + z · q  ∎
      ω → begin
        (ω · (n + s + z)) · q        ≡⟨ ·-assoc _ _ _ ⟩
        ω · ((n + s + z) · q)        ≡⟨ ·-congˡ (·-distribʳ-+ _ n _) ⟩
        ω · (n · q + (s + z) · q)    ≡⟨ ·-congˡ (+-congˡ (·-distribʳ-+ _ s _)) ⟩
        ω · (n · q + s · q + z · q)  ∎
    where
    open Tools.Reasoning.PartialOrder ≤-poset

  nr-+ :
    ∀ p r →
    nr p r z₁ s₁ n₁ + nr p r z₂ s₂ n₂ ≤
    nr p r (z₁ + z₂) (s₁ + s₂) (n₁ + n₂)
  nr-+ {z₁ = z₁} {s₁ = s₁} {n₁ = n₁} {z₂ = z₂} {s₂ = s₂} {n₂ = n₂} p =
    λ where
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
        ((𝟙 + p) · n₁ + ω · s₁ + z₁) + ((𝟙 + p) · n₂ + ω · s₂ + z₂)    ≡⟨ +-sub-interchangeable-+ ((𝟙 + p) · _) _ _ _ ⟩
        ((𝟙 + p) · n₁ + (𝟙 + p) · n₂) + (ω · s₁ + z₁) + (ω · s₂ + z₂)  ≡⟨ +-cong (sym (·-distribˡ-+ (𝟙 + p) _ _))
                                                                            (+-sub-interchangeable-+ (ω · s₁) _ _ _) ⟩
        (𝟙 + p) · (n₁ + n₂) + (ω · s₁ + ω · s₂) + (z₁ + z₂)            ≡˘⟨ +-congˡ {x = (𝟙 + p) · _}
                                                                             (+-congʳ (·-distribˡ-+ ω s₁ _)) ⟩
        (𝟙 + p) · (n₁ + n₂) + ω · (s₁ + s₂) + (z₁ + z₂)                ∎
      ω → begin
        ω · (n₁ + s₁ + z₁) + ω · (n₂ + s₂ + z₂)  ≡˘⟨ ·-distribˡ-+ _ (n₁ + _) _ ⟩
        ω · ((n₁ + s₁ + z₁) + (n₂ + s₂ + z₂))    ≡⟨ ·-congˡ lemma ⟩
        ω · ((n₁ + n₂) + (s₁ + s₂) + (z₁ + z₂))  ∎
    where
    lemma =
      (n₁ + s₁ + z₁) + (n₂ + s₂ + z₂)    ≡⟨ +-sub-interchangeable-+ n₁ _ _ _ ⟩
      (n₁ + n₂) + (s₁ + z₁) + (s₂ + z₂)  ≡⟨ +-congˡ {x = n₁ + _}
                                              (+-sub-interchangeable-+ s₁ _ _ _) ⟩
      (n₁ + n₂) + (s₁ + s₂) + (z₁ + z₂)  ∎
      where
      open Tools.Reasoning.PropositionalEquality

    open Tools.Reasoning.PartialOrder ≤-poset

  nr-zero : ∀ p r → n ≤ 𝟘 → nr p r z s n ≤ z
  nr-zero {n = n} {z = z} {s = s} p r n≤𝟘 =
    case nr-view p r z s n of λ where
      (nr≡𝟘 ≡𝟘) → begin
        nr p r 𝟘 𝟘 𝟘  ≡⟨ ≡𝟘 ⟩
        𝟘             ∎
      (nr≡𝟙₁ ≡𝟙) → begin
        nr p 𝟘 𝟙 𝟙 𝟘  ≡⟨ ≡𝟙 ⟩
        𝟙             ∎
      (nr≡𝟙₂ ≡𝟙) → begin
        nr p 𝟙 𝟙 𝟘 𝟘  ≡⟨ ≡𝟙 ⟩
        𝟙             ∎
      nr≡𝟙₃ → begin
        𝟙  ≤⟨ n≤𝟘 ⟩
        𝟘  ∎
      nr≡𝟙₄ → begin
        𝟙  ≤⟨ n≤𝟘 ⟩
        𝟘  ∎
      (nr≡𝟙∧𝟘 nr≡𝟙∧𝟘₁ ≡𝟘∧𝟙) → begin
        ((𝟙 ∧ p) · 𝟘 + 𝟘) ∧ 𝟙  ≡⟨ ≡𝟘∧𝟙 ⟩
        𝟘 ∧ 𝟙                  ≤⟨ ∧-decreasingʳ 𝟘 𝟙 ⟩
        𝟙                      ∎
      (nr≡𝟙∧𝟘 nr≡𝟙∧𝟘₂ ≡𝟘∧𝟙) → begin
        ((𝟙 ∧ p) · 𝟘 + 𝟙) ∧ 𝟘  ≡⟨ ≡𝟘∧𝟙 ⟩
        𝟘 ∧ 𝟙                  ≤⟨ ∧-decreasingˡ 𝟘 𝟙 ⟩
        𝟘                      ∎
      (nr≡𝟙∧𝟘 nr≡𝟙∧𝟘₃ ≡𝟘∧𝟙) → begin
        ((𝟘 ∧ 𝟙) · 𝟙 + 𝟘) ∧ 𝟙  ≡⟨ ≡𝟘∧𝟙 ⟩
        𝟘 ∧ 𝟙                  ≤⟨ ∧-decreasingˡ 𝟘 𝟙 ⟩
        𝟘                      ∎
      (nr≡ω _ ≡ω) → begin
        nr p r z s n  ≡⟨ ≡ω ⟩
        ω             ≤⟨ refl ⟩
        z             ∎
    where
    open Tools.Reasoning.PartialOrder ≤-poset

  nr-suc : ∀ p r → nr p r z s n ≤ s + p · n + r · nr p r z s n
  nr-suc {z = z} {s = s} {n = n} p r =
    case nr-view p r z s n of λ where
      (nr≡𝟘 ≡𝟘) → begin
        nr p r 𝟘 𝟘 𝟘                  ≡⟨ ≡𝟘 ⟩
        𝟘                             ≡˘⟨ ·-zeroʳ _ ⟩
        r · 𝟘                         ≡˘⟨ +-identityˡ _ ⟩
        𝟘 + r · 𝟘                     ≡˘⟨ +-cong (·-zeroʳ p) (·-congˡ ≡𝟘) ⟩
        p · 𝟘 + r · nr p r 𝟘 𝟘 𝟘      ≡⟨⟩
        𝟘 + p · 𝟘 + r · nr p r 𝟘 𝟘 𝟘  ∎
      (nr≡𝟙₁ ≡𝟙) → begin
        nr p 𝟘 𝟙 𝟙 𝟘                  ≡⟨ ≡𝟙 ⟩
        𝟙                             ≡⟨⟩
        𝟙 + 𝟘 + 𝟘                     ≡˘⟨ +-congˡ (+-congʳ {x = 𝟘} (·-zeroʳ p)) ⟩
        𝟙 + p · 𝟘 + 𝟘                 ≡⟨⟩
        𝟙 + p · 𝟘 + 𝟘 · nr p 𝟘 𝟙 𝟙 𝟘  ∎
      (nr≡𝟙₂ _) → begin
        nr p 𝟙 𝟙 𝟘 𝟘                  ≡⟨⟩
        𝟘 + nr p 𝟙 𝟙 𝟘 𝟘              ≡˘⟨ +-cong (·-zeroʳ p) (·-identityˡ _) ⟩
        p · 𝟘 + 𝟙 · nr p 𝟙 𝟙 𝟘 𝟘      ≡˘⟨ +-identityˡ _ ⟩
        𝟘 + p · 𝟘 + 𝟙 · nr p 𝟙 𝟙 𝟘 𝟘  ∎
      nr≡𝟙₃ → begin
        nr 𝟙 𝟘 𝟘 𝟘 𝟙                  ≡⟨⟩
        𝟙                             ≡⟨⟩
        𝟘 + 𝟙 · 𝟙 + 𝟘 · nr 𝟙 𝟘 𝟘 𝟘 𝟙  ∎
      nr≡𝟙₄ → begin
        nr 𝟘 𝟙 𝟘 𝟘 𝟙                  ≡⟨⟩
        𝟙                             ≡⟨⟩
        𝟘 + 𝟘 · 𝟙 + 𝟙 · nr 𝟙 𝟘 𝟘 𝟘 𝟙  ∎
      (nr≡𝟙∧𝟘 nr≡𝟙∧𝟘₁ ≡𝟘∧𝟙) → begin
        ((𝟙 ∧ p) · 𝟘 + 𝟘) ∧ 𝟙  ≡⟨ ≡𝟘∧𝟙 ⟩
        𝟘 ∧ 𝟙                  ≤⟨ ∧-decreasingˡ 𝟘 𝟙 ⟩
        𝟘                      ≡˘⟨ ·-zeroʳ _ ⟩
        p · 𝟘                  ≡˘⟨ +-identityʳ _ ⟩
        p · 𝟘 + 𝟘              ∎
      (nr≡𝟙∧𝟘 nr≡𝟙∧𝟘₂ ≡𝟘∧𝟙) → begin
        ((𝟙 ∧ p) · 𝟘 + 𝟙) ∧ 𝟘  ≡⟨ ≡𝟘∧𝟙 ⟩
        𝟘 ∧ 𝟙                  ≤⟨ ∧-decreasingʳ 𝟘 𝟙 ⟩
        𝟙                      ≡˘⟨ +-identityʳ _ ⟩
        𝟙 + 𝟘                  ≡˘⟨ cong (_ +_) (·-zeroʳ p) ⟩
        𝟙 + p · 𝟘              ≡˘⟨ cong (_ +_) (+-identityʳ (p · _)) ⟩
        𝟙 + p · 𝟘 + 𝟘          ∎
      (nr≡𝟙∧𝟘 nr≡𝟙∧𝟘₃ ≡𝟘∧𝟙) → begin
        ((𝟘 ∧ 𝟙) · 𝟙 + 𝟘) ∧ 𝟙  ≡⟨ ≡𝟘∧𝟙 ⟩
        𝟘 ∧ 𝟙                  ≤⟨ ∧-decreasingˡ 𝟘 𝟙 ⟩
        𝟘                      ∎
      (nr≡ω _ ≡ω) → begin
        nr p r z s n                  ≡⟨ ≡ω ⟩
        ω                             ≤⟨ refl ⟩
        s + p · n + r · nr p r z s n  ∎
    where
    open Tools.Reasoning.PartialOrder ≤-poset

opaque

  -- The nr function defined above is factoring.

  zero-one-many-has-factoring-nr :
    Is-factoring-nr zero-one-many-has-nr
  zero-one-many-has-factoring-nr = record
    { nr₂ = nr₂
    ; nr₂≢𝟘 = λ {p} {r} → 𝟙∧p≢𝟘 (r + p)
    ; nr-factoring = λ {p} {r} {z} {s} {n} → nr-factoring p r z s n
    }
    where
    open Tools.Reasoning.PropositionalEquality
    open Modality zero-one-many-modality
           hiding (𝟘; 𝟙; ω; _+_; _·_; _∧_)
    nr₂ : Op₂ Zero-one-many
    nr₂ p r = 𝟙 ∧ (r + p)
    𝟙+p≡𝟙∧𝟙+p : ∀ p → 𝟙 + p ≡ 𝟙 ∧ (𝟙 + p)
    𝟙+p≡𝟙∧𝟙+p 𝟘 = refl
    𝟙+p≡𝟙∧𝟙+p 𝟙 = refl
    𝟙+p≡𝟙∧𝟙+p ω = refl
    lemma : ∀ p q r → p ≢ 𝟘 → (p + q) ∧ (𝟙 + r) ≡ p + q ∧ r
    lemma 𝟘 q r p≢𝟘 = ⊥-elim (p≢𝟘 refl)
    lemma 𝟙 q r p≢𝟘 = sym (+-distribˡ-∧ 𝟙 q r)
    lemma ω q r p≢𝟘 = refl
    nr-factoring : (p r z s n : Zero-one-many) → nr p r z s n ≡ nr₂ p r · n + nr p r z s 𝟘
    nr-factoring p 𝟘 z s 𝟘
      rewrite ·-zeroʳ (𝟙 ∧ p) = refl
    nr-factoring p 𝟘 z s 𝟙
      rewrite ·-zeroʳ (𝟙 ∧ p) rewrite ·-identityʳ (𝟙 ∧ p) = lemma (𝟙 ∧ p) s z (𝟙∧p≢𝟘 p)
    nr-factoring p 𝟘 z s ω
      rewrite ·-distribʳ-∧ ω 𝟙 p = refl
    nr-factoring p 𝟙 z s n rewrite ·-zeroʳ (𝟙 + p) =
      +-congʳ (·-congʳ (𝟙+p≡𝟙∧𝟙+p p))
    nr-factoring p ω z s n = ·-distribˡ-+ ω n (s + z)

opaque

  -- The nr function returns results that are at least as large as those
  -- of any other factoring nr function for zero-one-many-modality.

  nr-greatest-factoring :
    (has-nr : Has-nr zero-one-many-modality)
    (is-factoring-nr : Is-factoring-nr has-nr) →
    ∀ p r z s n → Has-nr.nr has-nr p r z s n ≤ nr p r z s n
  nr-greatest-factoring has-nr is-factoring-nr = λ where
      p r ω s n → lemma $ begin
        nr″ p r ω s n                ≡⟨ nr-factoring ⟩
        nr₂″ p r · n + nr″ p r ω s 𝟘 ≤⟨ +-monotoneʳ (nr-zero refl) ⟩
        nr₂″ p r · n + ω             ≡⟨ +-zeroʳ _ ⟩
        ω                            ∎
      p r z ω n → lemma $ begin
        nr″ p r z ω n                 ≤⟨ nr-suc ⟩
        ω + p · n + r · nr″ p r z ω n ≡⟨⟩
        ω                             ∎
      p r z s ω → lemma $ begin
        nr″ p r z s ω                ≡⟨ nr-factoring ⟩
        nr₂″ p r · ω + nr″ p r z s 𝟘 ≡⟨ +-congʳ (≢𝟘·ω nr₂≢𝟘) ⟩
        ω                            ∎
      p r 𝟘 𝟘 𝟘 → begin
        nr″ p r 𝟘 𝟘 𝟘 ≡⟨ nr″-𝟘 ⦃ has-nr ⦄ ⟩
        𝟘             ≡˘⟨ nr-𝟘 p r .proj₂ (refl , refl , refl)  ⟩
        nr p r 𝟘 𝟘 𝟘  ∎
      ω r z s 𝟙 → lemma $ begin
        nr″ ω r z s 𝟙             ≤⟨ nr-suc ⟩
        s + ω + r · nr″ ω r z s 𝟙 ≡⟨⟩
        s + ω                     ≡⟨ +-zeroʳ s ⟩
        ω                         ∎
      𝟙 r z 𝟙 𝟙 → lemma $ begin
        nr″ 𝟙 r z 𝟙 𝟙              ≤⟨ nr-suc ⟩
        𝟙 + 𝟙 + r · nr″ 𝟙 r z 𝟙 𝟙 ≡˘⟨ +-assoc 𝟙 𝟙 (r · nr″ 𝟙 r z 𝟙 𝟙) ⟩
        ω + r · nr″ 𝟙 r z 𝟙 𝟙      ≡⟨⟩
        ω                           ∎
      p r 𝟘 𝟙 𝟙 → nr″przs𝟙≤ λ ()
      p r 𝟙 s 𝟙 → nr″przs𝟙≤ λ ()
      p ω 𝟙 𝟘 𝟘 → nr″pω≤ λ ()
      p ω z 𝟙 𝟘 → nr″pω≤ λ ()
      p ω z s 𝟙 → nr″pω≤ λ ()
      𝟙 𝟙 z s 𝟙 → lemma $ begin
        nr″ 𝟙 𝟙 z s 𝟙              ≤⟨ nr-suc ⟩
        s + 𝟙 + 𝟙 · nr″ 𝟙 𝟙 z s 𝟙 ≡⟨ +-congˡ {s} (+-congˡ {𝟙} (·-identityˡ (nr″ 𝟙 𝟙 z s 𝟙))) ⟩
        s + 𝟙 + nr″ 𝟙 𝟙 z s 𝟙     ≡⟨ +-congˡ {s} (≢𝟘+≢𝟘 {𝟙} {nr″ 𝟙 𝟙 z s 𝟙} (λ ())
                                        λ nr″≡𝟘 → case nr″-positive nr″≡𝟘 of λ ()) ⟩
        s + ω                      ≡⟨ +-zeroʳ s ⟩
        ω                          ∎
      p 𝟙 z 𝟙 n → lemma $ begin
        nr″ p 𝟙 z 𝟙 n                  ≤⟨ nr-suc ⟩
        𝟙 + p · n + 𝟙 · nr″ p 𝟙 z 𝟙 n ≡⟨ +-congˡ {𝟙} (+-congˡ {p · n} (·-identityˡ _)) ⟩
        𝟙 + p · n + nr″ p 𝟙 z 𝟙 n     ≡⟨ +-congˡ {𝟙} (+-comm (p · n) (nr″ p 𝟙 z 𝟙 n)) ⟩
        𝟙 + nr″ p 𝟙 z 𝟙 n + p · n     ≡˘⟨ +-assoc 𝟙 (nr″ p 𝟙 z 𝟙 n) (p · n) ⟩
        (𝟙 + nr″ p 𝟙 z 𝟙 n) + p · n   ≡⟨ +-congʳ {p · n} (≢𝟘+≢𝟘 {𝟙} {nr″ p 𝟙 z 𝟙 n} (λ ())
                                            λ nr″≡𝟘 → case nr″-positive nr″≡𝟘 of λ ()) ⟩
        ω + p · n                      ≡⟨⟩
        ω                              ∎
      𝟘 𝟘 𝟘 𝟘 𝟙 → begin
        nr″ 𝟘 𝟘 𝟘 𝟘 𝟙 ≤⟨ ∧-greatest-lower-bound {q = 𝟘} {𝟙} nr-suc
                            (≢𝟘→≤𝟙 (nr″ 𝟘 𝟘 𝟘 𝟘 𝟙) (λ nr″≡𝟘 → case nr″-positive nr″≡𝟘 of λ ())) ⟩
        𝟘∧𝟙           ≡⟨⟩
        nr′ 𝟘 𝟘 𝟘 𝟘 𝟙 ≡˘⟨ nr≡nr′ {𝟘} {𝟘} {𝟙} 𝟘 𝟘 ⟩
        nr  𝟘 𝟘 𝟘 𝟘 𝟙 ∎
      𝟙 𝟘 𝟘 𝟘 𝟙 → begin
        nr″ 𝟙 𝟘 𝟘 𝟘 𝟙 ≤⟨ nr-suc ⟩
        𝟙              ≡⟨⟩
        nr  𝟙 𝟘 𝟘 𝟘 𝟙 ∎
      𝟘 𝟙 𝟘 𝟘 𝟙 → begin
        nr″ 𝟘 𝟙 𝟘 𝟘 𝟙 ≤⟨ ≢𝟘→≤𝟙 (nr″ 𝟘 𝟙 𝟘 𝟘 𝟙) (λ nr″≡𝟘 → case nr″-positive nr″≡𝟘 of λ ()) ⟩
        𝟙              ≡⟨⟩
        nr  𝟘 𝟙 𝟘 𝟘 𝟙 ∎
      p 𝟘 𝟘 𝟙 𝟘 → begin
        nr″ p 𝟘 𝟘 𝟙 𝟘 ≤⟨ ∧-greatest-lower-bound {q = 𝟘} {𝟙} (nr-zero refl) nr-suc′ ⟩
        𝟘∧𝟙           ≡⟨⟩
        nr′ p 𝟘 𝟘 𝟙 𝟘 ≡˘⟨ nr≡nr′ {𝟘} {𝟙} {𝟘} p 𝟘 ⟩
        nr  p 𝟘 𝟘 𝟙 𝟘 ∎
      p 𝟘 𝟙 𝟘 𝟘 → begin
        nr″ p 𝟘 𝟙 𝟘 𝟘 ≤⟨ ∧-greatest-lower-bound {q = 𝟘} {𝟙} nr-suc′ (nr-zero refl) ⟩
        𝟘∧𝟙           ≡⟨⟩
        nr′ p 𝟘 𝟙 𝟘 𝟘 ≡˘⟨ nr≡nr′ {𝟙} {𝟘} {𝟘} p 𝟘  ⟩
        nr  p 𝟘 𝟙 𝟘 𝟘 ∎
      p 𝟘 𝟙 𝟙 𝟘 → begin
        nr″ p 𝟘 𝟙 𝟙 𝟘 ≤⟨ nr-suc′ ⟩
        𝟙              ≡⟨⟩
        nr′ p 𝟘 𝟙 𝟙 𝟘 ≡˘⟨ nr≡nr′ {𝟙} {𝟙} {𝟘} p 𝟘 ⟩
        nr  p 𝟘 𝟙 𝟙 𝟘 ∎
      p 𝟙 𝟙 𝟘 𝟘 → begin
        nr″ p 𝟙 𝟙 𝟘 𝟘 ≤⟨ nr-zero refl ⟩
        𝟙              ≡⟨⟩
        nr′ p 𝟙 𝟙 𝟘 𝟘 ≡˘⟨ nr≡nr′ {𝟙} {𝟘} {𝟘} p 𝟙 ⟩
        nr  p 𝟙 𝟙 𝟘 𝟘 ∎
    where
    open Is-factoring-nr is-factoring-nr renaming (nr₂ to nr₂″)
    open Has-nr has-nr renaming (nr to nr″; nr-positive to nr″-positive)
    open Addition zero-one-many-modality
    open Meet zero-one-many-modality
    open Natrec zero-one-many-modality renaming (nr-𝟘 to nr″-𝟘)
    open PartialOrder zero-one-many-modality
    open Modality zero-one-many-modality
      hiding (𝟘; 𝟙; ω; _+_; _·_; _∧_; _≤_)
    open Tools.Reasoning.PartialOrder ≤-poset
    lemma : nr″ p r z s n ≤ ω → nr″ p r z s n ≤ nr p r z s n
    lemma {p} {r} {z} {s} {n} nr″≤ω =
      ≤-trans nr″≤ω (ω≤ (nr p r z s n))
    nr-suc′ : nr″ p r z s 𝟘 ≤ s + r · nr″ p r z s 𝟘
    nr-suc′ {p} {r} {z} {s} = begin
      nr″ p r z s 𝟘 ≤⟨ nr-suc ⟩
      s + p · 𝟘 + r · nr″ p r z s 𝟘 ≡⟨ +-congˡ {s} (+-congʳ (·-zeroʳ p)) ⟩
      s + 𝟘 + r · nr″ p r z s 𝟘     ≡⟨⟩
      s + r · nr″ p r z s 𝟘         ∎
    nr″pω≤ : ¬ (z ≡ 𝟘 × s ≡ 𝟘 × n ≡ 𝟘) → nr″ p ω z s n ≤ nr p ω z s n
    nr″pω≤ {z} {s} {n} {p} ≢𝟘 = lemma $ begin
      nr″ p ω z s n                 ≤⟨ nr-suc ⟩
      s + p · n + ω · nr″ p ω z s n ≡⟨ +-congˡ {s} (+-congˡ (ω·≢𝟘 (≢𝟘 ∘→ nr″-positive))) ⟩
      s + p · n + ω                 ≡⟨ +-congˡ (+-zeroʳ _) ⟩
      s + ω                         ≡⟨ +-zeroʳ _ ⟩
      ω                             ∎
    nr″przs𝟙≤ : ¬ (z ≡ 𝟘 × s ≡ 𝟘) → nr″ p r z s 𝟙 ≤ nr p r z s 𝟙
    nr″przs𝟙≤ {z} {s} {p} {r} ≢𝟘 = lemma $ begin
        nr″ p r z s 𝟙                ≡⟨ nr-factoring ⟩
        nr₂″ p r · 𝟙 + nr″ p r z s 𝟘 ≡⟨ +-congʳ {nr″ p r z s 𝟘} (·-identityʳ _) ⟩
        nr₂″ p r + nr″ p r z s 𝟘     ≡⟨ ≢𝟘+≢𝟘 nr₂≢𝟘 (λ nr″≡𝟘 →
                                         let z≡𝟘 , s≡𝟘 , _ = nr″-positive nr″≡𝟘
                                         in  ≢𝟘 (z≡𝟘 , s≡𝟘)) ⟩
        ω                            ∎

opaque

  -- The nr function satisfies Linearity-like-nr-for-𝟘.

  nr-linearity-like-for-𝟘 :
    Has-nr.Linearity-like-nr-for-𝟘 zero-one-many-has-nr
  nr-linearity-like-for-𝟘 = refl

opaque

  -- The nr function satisfies Linearity-like-nr-for-𝟙.

  nr-linearity-like-for-𝟙 :
    Has-nr.Linearity-like-nr-for-𝟙 zero-one-many-has-nr
  nr-linearity-like-for-𝟙 = refl

------------------------------------------------------------------------
-- Subtraction

open Subtraction zero-one-many-modality

opaque

  -- Subtraction of ω by anything is ω

  ω-p≡ω : ∀ p → ω - p ≡ ω
  ω-p≡ω p = ∞-p≡∞ PE.refl p

opaque

  -- Subtraction of 𝟙 by 𝟙 is 𝟘

  𝟙-𝟙≡𝟘 : 𝟙 - 𝟙 ≡ 𝟘
  𝟙-𝟙≡𝟘 =
    p-p≤𝟘 ,
    λ where
      𝟘 _  → refl
      𝟙 ()
      ω ()

opaque

  -- Subtraction of p by ω is not possible unless p ≡ ω

  p-ω≰ : p - ω ≤ q → p ≡ ω
  p-ω≰ {(𝟘)} {(𝟘)} ()
  p-ω≰ {(𝟘)} {(𝟙)} ()
  p-ω≰ {(𝟘)} {(ω)} ()
  p-ω≰ {(𝟙)} {(𝟘)} ()
  p-ω≰ {(𝟙)} {(𝟙)} ()
  p-ω≰ {(𝟙)} {(ω)} ()
  p-ω≰ {(ω)} _ = refl

opaque

  -- Subtraction of p by ω is not possible unless p ≡ ω

  p-ω≢ : p - ω ≡ q → p ≡ ω
  p-ω≢ {q} = p-ω≰ {q = q} ∘→ proj₁

opaque

  -- The modality supports subtraction with
  --   ω - p ≡ ω for all p
  --   p - 𝟘 ≡ p for all p
  --   𝟙 - 𝟙 ≡ 𝟘
  -- and not defined otherwise

  supports-subtraction : Supports-subtraction
  supports-subtraction {p} {(ω)} {r} x =
    case p-ω≰ {q = r} x of λ {
      refl →
    ω , ω-p≡ω ω }
  supports-subtraction {p} {(𝟘)} _ =
    p , p-𝟘≡p
  supports-subtraction {(ω)} {q} _ =
    ω , ω-p≡ω q
  supports-subtraction {(𝟘)} {r} x =
    case 𝟘-p≤q {q = r} x of λ {
      (refl , refl) →
    𝟘 , p-𝟘≡p }
  supports-subtraction {(𝟙)} {(𝟙)} {(r)} x =
    𝟘 , 𝟙-𝟙≡𝟘

-- An alternative definition of the subtraction relation with
--   ω - p ≡ ω for all p
--   p - 𝟘 ≡ p for all p
--   𝟙 - 𝟙 ≡ 𝟘
-- and not defined otherwise

data _-_≡′_ : (p q r : Zero-one-many) → Set where
  ω-p≡′ω : ω - p ≡′ ω
  p-𝟘≡′p : p - 𝟘 ≡′ p
  𝟙-𝟙≡′𝟘 : 𝟙 - 𝟙 ≡′ 𝟘

opaque

  -- The two subtraction relations are equivalent.

  -≡↔-≡′ : ∀ p q r → (p - q ≡ r) ⇔ (p - q ≡′ r)
  -≡↔-≡′ p q r = left p q r , right
    where
    left : ∀ p q r → p - q ≡ r → p - q ≡′ r
    left ω q r p-q≡r =
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
    left 𝟙 ω r p-q≡r =
      case p-ω≢ p-q≡r of λ ()
    right : p - q ≡′ r → p - q ≡ r
    right ω-p≡′ω = ω-p≡ω q
    right p-𝟘≡′p = p-𝟘≡p
    right 𝟙-𝟙≡′𝟘 = 𝟙-𝟙≡𝟘

------------------------------------------------------------------------
-- Properties of greatest lower bounds

opaque

  -- nr 𝟘 r z s 𝟘 is the greatest lower bound of nrᵢ r z s.

  nr-nrᵢ-GLB :
    let 𝕄 = zero-one-many-modality in
    ∀ r → Modality.Greatest-lower-bound
            𝕄 (nr 𝟘 r z s 𝟘) (Modality.nrᵢ 𝕄 r z s)
  nr-nrᵢ-GLB {z} {s} = λ where
      𝟘 → GLB-congʳ (sym (trans (∧-congʳ (+-congʳ (·-zeroʳ (𝟙 ∧ 𝟘))))
            (∧-comm s z))) nrᵢ-𝟘-GLB
      𝟙 → lemma-𝟙 _ _
      ω → lemma-ω _ _
    where
    open Modality zero-one-many-modality
      hiding (𝟘; 𝟙; ω; _∧_; _·_; _+_)
    open GLB zero-one-many-modality
    open Natrec zero-one-many-modality
    open PartialOrder zero-one-many-modality
    lemma′ : ∀ {z} i → nrᵢ 𝟙 z 𝟘 i ≡ z
    lemma′ 0 = refl
    lemma′ (1+ i) =
      trans (·-identityˡ _) (lemma′ i)
    lemma : ∀ {r z s} i →
      nrᵢ r z s i ≡ ω → Greatest-lower-bound ω (nrᵢ r z s)
    lemma {r} {z} {s} i nrᵢ≡ω =
      (λ i → ω≤ (nrᵢ r z s i)) , λ q q≤ → ≤-trans (q≤ i) (≤-reflexive nrᵢ≡ω)
    lemma-𝟙 : ∀ z s → Greatest-lower-bound (ω · s + z) (nrᵢ 𝟙 z s)
    lemma-𝟙 z 𝟘 =
      GLB-const lemma′
    lemma-𝟙 𝟘 𝟙 = lemma 2 refl
    lemma-𝟙 𝟙 𝟙 = lemma 1 refl
    lemma-𝟙 ω 𝟙 = lemma 0 refl
    lemma-𝟙 z ω = lemma 1 refl
    lemma-ω : ∀ z s → Greatest-lower-bound (ω · (s + z)) (nrᵢ ω z s)
    lemma-ω 𝟘 𝟘 = GLB-nrᵢ-𝟘
    lemma-ω 𝟙 𝟘 = lemma 1 refl
    lemma-ω ω 𝟘 = lemma 0 refl
    lemma-ω 𝟘 𝟙 = lemma 2 refl
    lemma-ω 𝟙 𝟙 = lemma 1 refl
    lemma-ω ω 𝟙 = lemma 0 refl
    lemma-ω z ω = lemma 1 refl

opaque

  -- The sequence nrᵢ r z s has a greatest lower bound

  nrᵢ-GLB :
    let 𝕄 = zero-one-many-modality in
    ∀ r z s → ∃ λ p →
      Modality.Greatest-lower-bound
        𝕄 p (Modality.nrᵢ 𝕄 r z s)
  nrᵢ-GLB r z s = _ , nr-nrᵢ-GLB r

opaque

  -- The greatest lower bound for certain nrᵢ sequences

  nrᵢ-𝟘-GLB :
    let 𝕄 = zero-one-many-modality in
    ∀ p q → Modality.Greatest-lower-bound
            𝕄 (p ∧ q) (Modality.nrᵢ 𝕄 𝟘 p q)
  nrᵢ-𝟘-GLB p q = Natrec.nrᵢ-𝟘-GLB zero-one-many-modality

opaque

  -- The greatest lower bound for certain nrᵢ sequences

  nrᵢ-𝟙-GLB :
    let 𝕄 = zero-one-many-modality in
    ∀ p q → Modality.Greatest-lower-bound
            𝕄 (p + ω · q) (Modality.nrᵢ 𝕄 𝟙 p q)
  nrᵢ-𝟙-GLB p q =
    GLB.GLB-congʳ zero-one-many-modality (+-comm (ω · q) p) (nr-nrᵢ-GLB {z = p} {s = q} 𝟙)
    where
    open Modality zero-one-many-modality
      hiding (𝟙; ω; _·_; _+_)

opaque

  -- The greatest lower bound for certain nrᵢ sequences

  nrᵢ-ω-GLB :
    let 𝕄 = zero-one-many-modality in
    ∀ p q → Modality.Greatest-lower-bound
            𝕄 (ω · (p + q)) (Modality.nrᵢ 𝕄 ω p q)
  nrᵢ-ω-GLB p q =
    GLB.GLB-congʳ zero-one-many-modality (·-congˡ (+-comm q p)) (nr-nrᵢ-GLB {z = p} {s = q} ω)
    where
    open Modality zero-one-many-modality
      hiding (ω; _·_; _+_)

opaque

  -- The modality has well-behaved GLBs

  zero-one-many-supports-glb-for-natrec :
    Has-well-behaved-GLBs zero-one-many-modality
  zero-one-many-supports-glb-for-natrec = record
    { +-GLBˡ = +-GLBˡ
    ; ·-GLBˡ = ·-GLBˡ
    ; ·-GLBʳ = comm∧·-GLBˡ⇒·-GLBʳ ·-comm ·-GLBˡ
    ; +nrᵢ-GLB = +nrᵢ-GLB
    }
    where
    open Modality zero-one-many-modality
      hiding (_+_; _·_; _≤_; 𝟘; 𝟙; ω)
    open GLB zero-one-many-modality
    open Multiplication zero-one-many-modality
    open PartialOrder zero-one-many-modality

    ·-GLBˡ :
      {pᵢ : Sequence Zero-one-many} →
      Greatest-lower-bound p pᵢ →
      Greatest-lower-bound (q · p) (λ i → q · pᵢ i)
    ·-GLBˡ {q = 𝟘} p-glb = GLB-const′
    ·-GLBˡ {q = 𝟙} p-glb =
      GLB-cong (sym (·-identityˡ _)) (λ _ → sym (·-identityˡ _)) p-glb
    ·-GLBˡ {q = ω} {pᵢ} p-glb = lemma _ p-glb
      where
      lemma″ : 𝟙 ≤ ω · p → p ≡ 𝟘
      lemma″ {(𝟘)} _ = refl
      lemma″ {(𝟙)} ()
      lemma″ {(ω)} ()
      lemma′ : 𝟘 ≤ ω · p → p ≡ 𝟘
      lemma′ {(𝟘)} _ = refl
      lemma′ {(𝟙)} ()
      lemma′ {(ω)} ()
      lemma : ∀ p → Greatest-lower-bound p pᵢ →
              Greatest-lower-bound (ω · p) (λ i → ω · pᵢ i)
      lemma 𝟘 p-glb =
        GLB-const λ i → ·-congˡ (𝟘-GLB-inv p-glb i)
      lemma 𝟙 p-glb =
          (λ i → ω≤ (pᵢ i))
        , λ { 𝟘 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma′ ∘→ q≤))
            ; 𝟙 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma″ ∘→ q≤))
            ; ω q≤ → refl}
      lemma ω p-glb =
          (λ i → ω≤ (pᵢ i))
        , λ { 𝟘 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma′ ∘→ q≤))
            ; 𝟙 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma″ ∘→ q≤))
            ; ω q≤ → refl}

    +-GLBˡ :
      {pᵢ : Sequence Zero-one-many} →
      Greatest-lower-bound p pᵢ →
      Greatest-lower-bound (q + p) (λ i → q + pᵢ i)
    +-GLBˡ {q = 𝟘} p-glb = p-glb
    +-GLBˡ {(𝟘)} {q = 𝟙} p-glb =
      GLB-const (λ i → +-congˡ (𝟘-GLB-inv p-glb i))
    +-GLBˡ {q = 𝟙} {pᵢ} p-glb = lemma _ p-glb
      where
      lemma″ : 𝟙 ≤ 𝟙 + p → p ≡ 𝟘
      lemma″ {(𝟘)} _ = refl
      lemma″ {(𝟙)} ()
      lemma″ {(ω)} ()
      lemma′ : 𝟘 ≤ 𝟙 + p → p ≡ 𝟘
      lemma′ {(𝟘)} _ = refl
      lemma′ {(𝟙)} ()
      lemma′ {(ω)} ()
      lemma : ∀ p → Greatest-lower-bound p pᵢ →
              Greatest-lower-bound (𝟙 + p) (λ i → 𝟙 + pᵢ i)
      lemma 𝟘 p-glb =
        GLB-const (λ i → +-congˡ (𝟘-GLB-inv p-glb i))
      lemma 𝟙 p-glb =
          (λ _ → refl)
        , λ { 𝟘 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma′ ∘→ q≤))
            ; 𝟙 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma″ ∘→ q≤))
            ; ω q≤ → refl}
      lemma ω p-glb =
          (λ _ → refl)
        , λ { 𝟘 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma′ ∘→ q≤))
            ; 𝟙 q≤ → ⊥-elim (≢p-GLB-inv (λ ()) p-glb (lemma″ ∘→ q≤))
            ; ω q≤ → refl }
    +-GLBˡ {q = ω} p-glb = GLB-const′

    open Tools.Reasoning.PartialOrder ≤-poset

    +nrᵢ-GLB :
      Greatest-lower-bound p₁ (nrᵢ r z₁ s₁) →
      Greatest-lower-bound p₂ (nrᵢ r z₂ s₂) →
      ∃ λ q → Greatest-lower-bound q (nrᵢ r (z₁ + z₂) (s₁ + s₂)) ×
          p₁ + p₂ ≤ q
    +nrᵢ-GLB {p₁} {r} {z₁} {s₁} {p₂} {z₂} {s₂} p₁-glb p₂-glb =
      _ , nr-nrᵢ-GLB r , (begin
        p₁ + p₂                         ≡⟨ +-cong (GLB-unique p₁-glb (nr-nrᵢ-GLB r))
                                           (GLB-unique p₂-glb (nr-nrᵢ-GLB r)) ⟩
        nr 𝟘 r z₁ s₁ 𝟘 + nr 𝟘 r z₂ s₂ 𝟘 ≤⟨ Has-nr.nr-+ zero-one-many-has-nr {𝟘} {r} ⟩
        nr 𝟘 r (z₁ + z₂) (s₁ + s₂) 𝟘    ∎)

------------------------------------------------------------------------
-- Some properties lifted to contexts

open Graded.Context zero-one-many-modality
open Graded.Context.Properties zero-one-many-modality

private variable
  γ δ η : Conₘ _

opaque

  -- Evaluation of nrᶜ for r = 𝟘.

  nrᶜ-𝟘-≈ᶜ :
    nrᶜ ⦃ zero-one-many-has-nr ⦄ p 𝟘 γ δ η ≈ᶜ (((𝟙 ∧ p) ·ᶜ η +ᶜ δ) ∧ᶜ (η +ᶜ γ))
  nrᶜ-𝟘-≈ᶜ {γ = ε} {δ = ε} {η = ε} = ε
  nrᶜ-𝟘-≈ᶜ {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} =
    nrᶜ-𝟘-≈ᶜ ∙ refl

opaque

  -- Evaluation of nrᶜ for r = 𝟙.

  nrᶜ-𝟙-≈ᶜ :
    nrᶜ ⦃ zero-one-many-has-nr ⦄ p 𝟙 γ δ η ≈ᶜ (𝟙 + p) ·ᶜ η +ᶜ ω ·ᶜ δ +ᶜ γ
  nrᶜ-𝟙-≈ᶜ {γ = ε} {δ = ε} {η = ε} = ε
  nrᶜ-𝟙-≈ᶜ {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} =
    nrᶜ-𝟙-≈ᶜ ∙ refl

opaque

  -- Evaluation of nrᶜ for r = ω.

  nrᶜ-ω-≈ᶜ :
    nrᶜ ⦃ zero-one-many-has-nr ⦄ p ω γ δ η ≈ᶜ ω ·ᶜ (η +ᶜ δ +ᶜ γ)
  nrᶜ-ω-≈ᶜ {γ = ε} {δ = ε} {η = ε} = ε
  nrᶜ-ω-≈ᶜ {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} =
    nrᶜ-ω-≈ᶜ ∙ refl

opaque

  -- The greatest lower bound for certain nrᵢᶜ sequences

  nrᵢᶜ-𝟘-GLBᶜ : Greatest-lower-boundᶜ (γ ∧ᶜ δ) (nrᵢᶜ 𝟘 γ δ)
  nrᵢᶜ-𝟘-GLBᶜ {γ = ε} {δ = ε} = ε-GLB
  nrᵢᶜ-𝟘-GLBᶜ {γ = γ ∙ p} {δ = δ ∙ q} =
    GLBᶜ-pointwise′ nrᵢᶜ-𝟘-GLBᶜ (nrᵢ-𝟘-GLB p q)

opaque

  -- The greatest lower bound for certain nrᵢᶜ sequences

  nrᵢᶜ-𝟙-GLBᶜ : Greatest-lower-boundᶜ (γ +ᶜ ω ·ᶜ δ) (nrᵢᶜ 𝟙 γ δ)
  nrᵢᶜ-𝟙-GLBᶜ {γ = ε} {δ = ε} = ε-GLB
  nrᵢᶜ-𝟙-GLBᶜ {γ = γ ∙ p} {δ = δ ∙ q} =
    GLBᶜ-pointwise′ nrᵢᶜ-𝟙-GLBᶜ (nrᵢ-𝟙-GLB p q)

opaque

  -- The greatest lower bound for certain nrᵢᶜ sequences

  nrᵢᶜ-ω-GLBᶜ : Greatest-lower-boundᶜ (ω ·ᶜ (γ +ᶜ δ)) (nrᵢᶜ ω γ δ)
  nrᵢᶜ-ω-GLBᶜ {γ = ε} {δ = ε} = ε-GLB
  nrᵢᶜ-ω-GLBᶜ {γ = γ ∙ p} {δ = δ ∙ q} =
    GLBᶜ-pointwise′ nrᵢᶜ-ω-GLBᶜ (nrᵢ-ω-GLB p q)

opaque

  -- nrᶜ 𝟘 r γ δ 𝟘ᶜ is the greatest lower bound of nrᵢᶜ r γ δ

  nrᶜ-nrᵢᶜ-GLBᶜ :
    Greatest-lower-boundᶜ (nrᶜ ⦃ zero-one-many-has-nr ⦄ 𝟘 r γ δ 𝟘ᶜ) (nrᵢᶜ r γ δ)
  nrᶜ-nrᵢᶜ-GLBᶜ {γ = ε} {δ = ε} = ε-GLB
  nrᶜ-nrᵢᶜ-GLBᶜ {γ = _ ∙ _} {δ = _ ∙ _} =
    GLBᶜ-pointwise′ nrᶜ-nrᵢᶜ-GLBᶜ (nr-nrᵢ-GLB _)
