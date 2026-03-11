------------------------------------------------------------------------
-- A modality for the natural numbers extended with infinity
------------------------------------------------------------------------

open import Tools.Bool hiding (_∧_; ∧-decreasingˡ; ∧-decreasingʳ)

module Graded.Modality.Instances.Nat-plus-infinity
  -- Should the total order be used (as opposed to the flat)
  (total : Bool) where

import Tools.Algebra
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat as N using (Nat; 1+; 2+; Sequence)
open import Tools.Product as Σ
open import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum as ⊎ using (_⊎_; inj₁; inj₂)

import Graded.FullReduction.Assumptions
import Graded.Modality
import Graded.Modality.Instances.BoundedStar as BoundedStar
import Graded.Modality.Instances.LowerBounded as LowerBounded
import Graded.Modality.Instances.Recursive.Sequences
import Graded.Modality.Properties.Addition
import Graded.Modality.Properties.Division
import Graded.Modality.Properties.Has-well-behaved-zero
import Graded.Modality.Properties.Meet
import Graded.Modality.Properties.Multiplication
import Graded.Modality.Properties.Natrec
import Graded.Modality.Properties.PartialOrder
import Graded.Modality.Properties.Subtraction
import Graded.Mode.Instances.Zero-one.Variant
import Graded.Mode.Instances.Zero-one

import Definition.Typed.Restrictions
open import Definition.Untyped using (BMΣ; 𝕤; 𝕨)
import Graded.Usage.Restrictions

-- The grades are the natural numbers extended with ∞.

data ℕ⊎∞ : Set where
  ⌞_⌟ : Nat → ℕ⊎∞
  ∞   : ℕ⊎∞

open Graded.Modality ℕ⊎∞
open Tools.Algebra   ℕ⊎∞

private variable
  m n o   : ℕ⊎∞

------------------------------------------------------------------------
-- Operators

-- Addition.

infixr 40 _+_

_+_ : ℕ⊎∞ → ℕ⊎∞ → ℕ⊎∞
∞     + _     = ∞
⌞ _ ⌟ + ∞     = ∞
⌞ m ⌟ + ⌞ n ⌟ = ⌞ m N.+ n ⌟


-- Meet.

-- The meet operation used for the total order

_∧ᵗ_ : ℕ⊎∞ → ℕ⊎∞ → ℕ⊎∞
∞ ∧ᵗ _ = ∞
⌞ _ ⌟ ∧ᵗ ∞ = ∞
⌞ m ⌟ ∧ᵗ ⌞ n ⌟ = ⌞ m N.⊔ n ⌟

-- The meet operation used for the flat order

_∧ᶠ_ : ℕ⊎∞ → ℕ⊎∞ → ℕ⊎∞
∞ ∧ᶠ _ = ∞
⌞ _ ⌟ ∧ᶠ ∞ = ∞
⌞ m ⌟ ∧ᶠ ⌞ n ⌟ =
  case m N.≟ n of λ where
    (yes _) → ⌞ m ⌟
    (no _) → ∞

-- The meet operation is defined in such a way that
-- ∞ ≤ … ≤ ⌞ 1 ⌟ ≤ ⌞ 0 ⌟ if "total" is true
-- and ∞ ≤ ⌞ m ⌟ and ⌞ m ⌟≰⌞ n ⌟ otherwise (for all m and n).
-- These correspond to ⌞ n ⌟ representing at most n and exactly n
-- uses respectively.

infixr 43 _∧_

_∧_ : ℕ⊎∞ → ℕ⊎∞ → ℕ⊎∞
p ∧ q = if total then p ∧ᵗ q else p ∧ᶠ q

-- An "introduction rule" for predicates over _∧_

∧-intro : (P : Op₂ ℕ⊎∞ → Set) (Pₐ : P _∧ᵗ_) (Pₑ : P _∧ᶠ_) → P _∧_
∧-intro P Pₐ Pₑ = lemma total
  where
  lemma : ∀ b → P (λ p q → if b then p ∧ᵗ q else p ∧ᶠ q)
  lemma false = Pₑ
  lemma true = Pₐ

-- Multiplication.

infixr 45 _·_

_·_ : ℕ⊎∞ → ℕ⊎∞ → ℕ⊎∞
⌞ 0 ⌟ · _     = ⌞ 0 ⌟
_     · ⌞ 0 ⌟ = ⌞ 0 ⌟
∞     · _     = ∞
⌞ _ ⌟ · ∞     = ∞
⌞ m ⌟ · ⌞ n ⌟ = ⌞ m N.* n ⌟

-- Division.

infixl 45 _/_

_/_ : ℕ⊎∞ → ℕ⊎∞ → ℕ⊎∞
_     / ⌞ 0 ⌟    = ∞
⌞ m ⌟ / ⌞ 1+ n ⌟ = ⌞ m N./ 1+ n ⌟
∞     / ⌞ 1+ _ ⌟ = ∞
∞     / ∞        = ∞
⌞ _ ⌟ / ∞        = ⌞ 0 ⌟

-- A star operator.

infix 50 _*

_* : ℕ⊎∞ → ℕ⊎∞
⌞ 0 ⌟ * = ⌞ 1 ⌟
_     * = ∞

-- The inferred ordering relation.

infix 10 _≤_

_≤_ : ℕ⊎∞ → ℕ⊎∞ → Set
m ≤ n = m ≡ m ∧ n

-- The inferred ordering relation for the "total" order

infix 10 _≤ᵗ_

_≤ᵗ_ : ℕ⊎∞ → ℕ⊎∞ → Set
m ≤ᵗ n = m ≡ m ∧ᵗ n

-- The inferred ordering relation for the "flat" order

infix 10 _≤ᶠ_

_≤ᶠ_ : ℕ⊎∞ → ℕ⊎∞ → Set
m ≤ᶠ n = m ≡ m ∧ᶠ n

opaque

  -- An "introduction rule" for the order relation

  ≤-intro : m ≤ᵗ n → m ≤ᶠ n → m ≤ n
  ≤-intro {m} {n} ≤ᵗ ≤ᶠ = lemma total
    where
    lemma : ∀ b → m ≡ (if b then m ∧ᵗ n else (m ∧ᶠ n))
    lemma false = ≤ᶠ
    lemma true = ≤ᵗ

opaque

  -- Another "introduction rule" for the order relation

  ≤ᵗ-intro : T total → m ≤ᵗ n → m ≤ n
  ≤ᵗ-intro {m} {n} x ≤ᵗ = lemma total x
    where
    lemma : ∀ b → T b → m ≡ (if b then m ∧ᵗ n else (m ∧ᶠ n))
    lemma true  _  = ≤ᵗ
    lemma false ()

opaque

  -- The "flat" order relation is a subset of the "total" order

  ≤ᶠ→≤ᵗ : m ≤ᶠ n → m ≤ᵗ n
  ≤ᶠ→≤ᵗ {m = ∞}                 _  = refl
  ≤ᶠ→≤ᵗ {m = ⌞ _ ⌟} {n = ∞}     ()
  ≤ᶠ→≤ᵗ {m = ⌞ m ⌟} {n = ⌞ n ⌟} _  with m N.≟ n
  ≤ᶠ→≤ᵗ _  | yes refl = cong ⌞_⌟ (sym (N.⊔-idem _))
  ≤ᶠ→≤ᵗ () | no _

opaque

  -- Another "introduction rule" for the order relation

  ≤ᶠ-intro : m ≤ᶠ n → m ≤ n
  ≤ᶠ-intro ≤ᶠ = ≤-intro (≤ᶠ→≤ᵗ ≤ᶠ) ≤ᶠ

------------------------------------------------------------------------
-- Some properties

opaque

  -- The grade ∞ is not equal to ⌞ m ⌟

  ∞≢⌞m⌟ : ∀ {m} → ∞ ≢ ⌞ m ⌟
  ∞≢⌞m⌟ ()

-- The grade ∞ is the least one.

∞≤ : ∀ n → ∞ ≤ n
∞≤ _ = ≤ᶠ-intro {n = ∞} refl

opaque

  -- The grade ∞ is not larger than ⌞ n ⌟ for any n

  ≰∞ : ∀ {n} → ⌞ n ⌟ ≤ ∞ → ⊥
  ≰∞ = lemma total
    where
    lemma : ∀ {n} → (b : Bool) → ⌞ n ⌟ ≢ (if b then ∞ else ∞)
    lemma true ()
    lemma false ()

-- For the total order, the grade ⌞ 0 ⌟ is the greatest one.

≤0 : T total → n ≤ ⌞ 0 ⌟
≤0 x = ≤ᵗ-intro x lemma
  where
  open Tools.Reasoning.PropositionalEquality
  lemma : n ≤ᵗ ⌞ 0 ⌟
  lemma {n = ∞} = refl
  lemma {n = ⌞ n ⌟} = cong ⌞_⌟ (
    n        ≡˘⟨ N.⊔-identityʳ _ ⟩
    n N.⊔ 0  ∎)

opaque

  -- A non-zero grade is at most ⌞ 1 ⌟ in the total order

  ≢𝟘→≤ᵗ𝟙 : m ≢ ⌞ 0 ⌟ → m ≤ᵗ ⌞ 1 ⌟
  ≢𝟘→≤ᵗ𝟙 {⌞ 0 ⌟} m≢𝟘 = ⊥-elim (m≢𝟘 refl)
  ≢𝟘→≤ᵗ𝟙 {⌞ 1+ m ⌟} m≢𝟘 rewrite N.⊔-identityʳ m = refl
  ≢𝟘→≤ᵗ𝟙 {(∞)} m≢𝟘 = refl

opaque

  -- In the flat order, ⌞ m ⌟ ≤ ⌞ n ⌟ only if m ≡ n.

  ⌞⌟≤ᶠ⌞⌟ : ∀ {m n} → ⌞ m ⌟ ≤ᶠ ⌞ n ⌟ → m ≡ n
  ⌞⌟≤ᶠ⌞⌟ {m} {n} m≤n with m N.≟ n
  ⌞⌟≤ᶠ⌞⌟ _ | yes m≡n = m≡n
  ⌞⌟≤ᶠ⌞⌟ () | no m≢n

-- Multiplication is commutative.

·-comm : Commutative _·_
·-comm = λ where
  ⌞ 0 ⌟    ⌞ 0 ⌟    → refl
  ⌞ 1+ _ ⌟ ⌞ 0 ⌟    → refl
  ⌞ 0 ⌟    ⌞ 1+ _ ⌟ → refl
  ⌞ 1+ m ⌟ ⌞ 1+ _ ⌟ → cong ⌞_⌟ (N.*-comm (1+ m) _)
  ⌞ 0 ⌟    ∞        → refl
  ⌞ 1+ _ ⌟ ∞        → refl
  ∞        ⌞ 0 ⌟    → refl
  ∞        ⌞ 1+ _ ⌟ → refl
  ∞        ∞        → refl

-- The function ⌞_⌟ is injective.

⌞⌟-injective : ∀ {m n} → ⌞ m ⌟ ≡ ⌞ n ⌟ → m ≡ n
⌞⌟-injective refl = refl

opaque
  -- The function ⌞_⌟ is antitone for the "total" order

  ⌞⌟-antitoneₐ : ∀ {m n} → m N.≤ n → ⌞ n ⌟ ≤ᵗ ⌞ m ⌟
  ⌞⌟-antitoneₐ {m = m} {n = n} m≤n =
    ⌞ n ⌟        ≡˘⟨ cong ⌞_⌟ (N.m≥n⇒m⊔n≡m m≤n) ⟩
    ⌞ n N.⊔ m ⌟  ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque

  ⌞⌟-antitone : ∀ {m n} → T total → m N.≤ n → ⌞ n ⌟ ≤ ⌞ m ⌟
  ⌞⌟-antitone {m = m} {n = n} x m≤n =
    ≤ᵗ-intro x (⌞⌟-antitoneₐ m≤n)

opaque

  -- An inverse to ⌞⌟-antitone.
  -- Note that unlike ⌞⌟-antitone this property holds for both the
  -- "total" and "flat" orders.

  ⌞⌟-antitone⁻¹ : ∀ {m n} → ⌞ n ⌟ ≤ ⌞ m ⌟ → m N.≤ n
  ⌞⌟-antitone⁻¹ {m = m} {n = n} = lemma total
    where
    lemma : ∀ b → ⌞ n ⌟ ≡ (if b then ⌞ n ⌟ ∧ᵗ ⌞ m ⌟ else ⌞ n ⌟ ∧ᶠ ⌞ m ⌟)
          → m N.≤ n
    lemma false n≤m with n N.≟ m
    … | yes refl = N.≤-refl
    lemma false () | no n≢m
    lemma true n≤m = N.m⊔n≡m⇒n≤m (sym (⌞⌟-injective n≤m))

-- The function ⌞_⌟ is homomorphic with respect to _·_/N._*_.

⌞⌟·⌞⌟≡⌞*⌟ : ∀ {m n} → ⌞ m ⌟ · ⌞ n ⌟ ≡ ⌞ m N.* n ⌟
⌞⌟·⌞⌟≡⌞*⌟ {m = 0}               = refl
⌞⌟·⌞⌟≡⌞*⌟ {m = 1+ _} {n = 1+ _} = refl
⌞⌟·⌞⌟≡⌞*⌟ {m = 1+ m} {n = 0}    = cong ⌞_⌟ (sym (N.*-zeroʳ m))

opaque

  -- Addition is decreasing for the left argument for the "total" order

  +-decreasingˡₐ : m + n ≤ᵗ m
  +-decreasingˡₐ {m = ∞}                 = refl
  +-decreasingˡₐ {m = ⌞ _ ⌟} {n = ∞}     = refl
  +-decreasingˡₐ {m = ⌞ _ ⌟} {n = ⌞ n ⌟} = ⌞⌟-antitoneₐ (N.m≤m+n _ n)

opaque

  +-decreasingˡ : T total → m + n ≤ m
  +-decreasingˡ x = ≤ᵗ-intro x +-decreasingˡₐ

opaque

  -- Multiplication by ∞ is decreasing

  ∞·-decreasing : ∞ · m ≤ m
  ∞·-decreasing {⌞ 0 ⌟} = lemma _
    where
    lemma : ∀ b → m ≡ (if b then m else m)
    lemma false = refl
    lemma true = refl
  ∞·-decreasing {⌞ 1+ x ⌟} = ∞≤ (⌞ 1+ x ⌟)
  ∞·-decreasing {(∞)} = ∞≤ ∞

opaque

  -- Multiplication by non-zero grades is decreasing in the "total" order

  ·-decreasingˡₐ : n ≢ ⌞ 0 ⌟ → m · n ≤ᵗ m
  ·-decreasingˡₐ {⌞ 0 ⌟} {(m)} n≢𝟘 = ⊥-elim (n≢𝟘 refl)
  ·-decreasingˡₐ {⌞ 1+ n ⌟} {⌞ 0 ⌟} n≢𝟘 = refl
  ·-decreasingˡₐ {⌞ 1+ n ⌟} {⌞ 1+ m ⌟} n≢𝟘 =
    ⌞⌟-antitoneₐ (N.m≤m*n (1+ m) (1+ n))
  ·-decreasingˡₐ {⌞ 1+ x ⌟} {(∞)} n≢𝟘 = refl
  ·-decreasingˡₐ {(∞)} {⌞ 0 ⌟} n≢𝟘 = refl
  ·-decreasingˡₐ {(∞)} {⌞ 1+ m ⌟} n≢𝟘 = refl
  ·-decreasingˡₐ {(∞)} {(∞)} n≢𝟘 = refl

-- One of the two characteristic properties of the star operator of a
-- star semiring.

*≡+·* : n * ≡ ⌞ 1 ⌟ + n · n *
*≡+·* {n = ∞}        = refl
*≡+·* {n = ⌞ 0 ⌟}    = refl
*≡+·* {n = ⌞ 1+ _ ⌟} = refl

-- One of the two characteristic properties of the star operator of a
-- star semiring.

*≡+*· : n * ≡ ⌞ 1 ⌟ + n * · n
*≡+*· {n = ∞}        = refl
*≡+*· {n = ⌞ 0 ⌟}    = refl
*≡+*· {n = ⌞ 1+ _ ⌟} = refl

opaque

  -- The star operator is bounded from above by ⌞ 1 ⌟

  n*≤1 : n * ≤ ⌞ 1 ⌟
  n*≤1 = ≤ᶠ-intro n*≤ᶠ1
    where
    n*≤ᶠ1 : n * ≤ᶠ ⌞ 1 ⌟
    n*≤ᶠ1 {n = ⌞ 0 ⌟} = refl
    n*≤ᶠ1 {n = ⌞ 1+ _ ⌟} = refl
    n*≤ᶠ1 {n = ∞} = refl

-- Equality is decidable.

_≟_ : Decidable (_≡_ {A = ℕ⊎∞})
_≟_ = λ where
  ∞     ∞     → yes refl
  ⌞ _ ⌟ ∞     → no (λ ())
  ∞     ⌞ _ ⌟ → no (λ ())
  ⌞ m ⌟ ⌞ n ⌟ → case m N.≟ n of λ where
    (yes refl) → yes refl
    (no m≢n)   → no (λ { refl → m≢n refl })

opaque

  -- The relation _≤ᵗ_ is total.

  ≤ᵗ-total : ∀ m n → m ≤ᵗ n ⊎ n ≤ᵗ m
  ≤ᵗ-total ∞     _     = inj₁ refl
  ≤ᵗ-total _     ∞     = inj₂ refl
  ≤ᵗ-total ⌞ m ⌟ ⌞ n ⌟ = case N.≤-total m n of λ where
    (inj₁ m≤n) → inj₂ (⌞⌟-antitoneₐ m≤n)
    (inj₂ n≤m) → inj₁ (⌞⌟-antitoneₐ n≤m)

opaque

  -- The relation _≤_ is total for the total order

  ≤-total : T total → ∀ m n → m ≤ n ⊎ n ≤ m
  ≤-total x m n =
    case ≤ᵗ-total m n of λ where
      (inj₁ m≤n) → inj₁ (≤ᵗ-intro x m≤n)
      (inj₂ n≤m) → inj₂ (≤ᵗ-intro x n≤m)

-- The type ℕ⊎∞ is a set.

ℕ⊎∞-set : Is-set ℕ⊎∞
ℕ⊎∞-set {x = ∞}     {y = ∞}     {x = refl} {y = refl} = refl
ℕ⊎∞-set {x = ∞}     {y = ⌞ _ ⌟} {x = ()}
ℕ⊎∞-set {x = ⌞ _ ⌟} {y = ∞}     {x = ()}
ℕ⊎∞-set {x = ⌞ m ⌟} {y = ⌞ n ⌟} {x = p}    {y = q}    =
                                                         $⟨ N.Nat-set ⟩
  ⌞⌟-injective p ≡ ⌞⌟-injective q                        →⟨ cong (cong ⌞_⌟) ⟩
  cong ⌞_⌟ (⌞⌟-injective p) ≡ cong ⌞_⌟ (⌞⌟-injective q)  →⟨ (λ hyp → trans (sym (lemma _)) (trans hyp (lemma _))) ⟩
  p ≡ q                                                  □
  where
  lemma : (p : ⌞ m ⌟ ≡ ⌞ n ⌟) → cong ⌞_⌟ (⌞⌟-injective p) ≡ p
  lemma refl = refl

opaque

  -- The grade ∞ · (m + n) is bounded by ∞ · n.

  ∞·+≤∞·ʳ : ∞ · (m + n) ≤ ∞ · n
  ∞·+≤∞·ʳ {m = ∞}        {n = n}        = ∞≤ (∞ · n)
  ∞·+≤∞·ʳ {m = ⌞ _ ⌟}    {n = ∞}        = ∞≤ ∞
  ∞·+≤∞·ʳ {m = ⌞ 0 ⌟}    {n = ⌞ 0 ⌟}    = lemma total
    where
    lemma : ∀ b → ⌞ 0 ⌟ ≡ (if b then ⌞ 0 ⌟ else ⌞ 0 ⌟)
    lemma false = refl
    lemma true = refl
  ∞·+≤∞·ʳ {m = ⌞ 1+ _ ⌟} {n = ⌞ 0 ⌟}    = ∞≤ ⌞ 0 ⌟
  ∞·+≤∞·ʳ {m = ⌞ 0 ⌟}    {n = ⌞ 1+ _ ⌟} = ∞≤ ∞
  ∞·+≤∞·ʳ {m = ⌞ 1+ _ ⌟} {n = ⌞ 1+ _ ⌟} = ∞≤ ∞

opaque

  m≢n→m∧ᶠn≡∞ : ∀ {m n} → m ≢ n → ⌞ m ⌟ ∧ᶠ ⌞ n ⌟ ≡ ∞
  m≢n→m∧ᶠn≡∞ {m} {n} m≢n with m N.≟ n
  … | yes m≡n = ⊥-elim (m≢n m≡n)
  … | no _ = refl

opaque

  -- The grade ∞ is a right zero for _+_

  +-zeroʳ : RightZero ∞ _+_
  +-zeroʳ ⌞ x ⌟ = refl
  +-zeroʳ ∞ = refl

opaque

  -- The grade ∞ is a zero for _+_.

  +-zero : Zero ∞ _+_
  +-zero = (λ _ → refl) , +-zeroʳ

opaque

  -- If m is not ⌞ 0 ⌟, then m · ∞ is equal to ∞.

  ≢𝟘·∞ : m ≢ ⌞ 0 ⌟ → m · ∞ ≡ ∞
  ≢𝟘·∞ {⌞ 0 ⌟} m≢𝟘 = ⊥-elim (m≢𝟘 refl)
  ≢𝟘·∞ {⌞ 1+ x ⌟} m≢𝟘 = refl
  ≢𝟘·∞ {(∞)} _ = refl

opaque

  -- If m is not ⌞ 0 ⌟, then ∞ · m is equal to ∞.

  ∞·≢𝟘 : m ≢ ⌞ 0 ⌟ → ∞ · m ≡ ∞
  ∞·≢𝟘 m≢𝟘 = trans (·-comm ∞ _) (≢𝟘·∞ m≢𝟘)

------------------------------------------------------------------------
-- The modality

-- A modality structure for ℕ⊎∞.

ℕ⊎∞-modality : Modality
ℕ⊎∞-modality = record
  { _+_          = _+_
  ; _·_          = _·_
  ; _∧_          = _∧_
  ; 𝟘            = ⌞ 0 ⌟
  ; 𝟙            = ⌞ 1 ⌟
  ; ω            = ∞
  ; ω≤𝟙          = ∞≤ ⌞ 1 ⌟
  ; ω·+≤ω·ʳ      = ∞·+≤∞·ʳ
  ; is-𝟘?        = _≟ ⌞ 0 ⌟
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
                   ⌞ _ ⌟ → refl
                   ∞     → refl)
              , (λ where
                   ⌞ _ ⌟ → cong ⌞_⌟ (N.+-identityʳ _)
                   ∞     → refl)
          }
        ; comm = +-comm
        }
      ; *-cong = cong₂ _·_
      ; *-assoc = ·-assoc
      ; *-identity =
            (λ where
               ⌞ 0 ⌟    → refl
               ⌞ 1+ _ ⌟ → cong ⌞_⌟ (N.+-identityʳ _)
               ∞        → refl)
          , (λ where
               ⌞ 0 ⌟    → refl
               ⌞ 1+ _ ⌟ → cong (⌞_⌟ ∘→ 1+) (N.*-identityʳ _)
               ∞        → refl)
      ; distrib = ·-distrib-+
      }
    ; zero =
          (λ _ → refl)
        , (λ where
             ⌞ 0 ⌟    → refl
             ⌞ 1+ _ ⌟ → refl
             ∞        → refl)
    }
  ; ∧-Semilattice = record
    { isBand = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = PE.isEquivalence
          ; ∙-cong        = cong₂ _∧_
          }
        ; assoc = ∧-intro Associative ∧ᵗ-assoc ∧ᶠ-assoc
        }
      ; idem = ∧-intro Idempotent ∧ᵗ-idem ∧ᶠ-idem
      }
    ; comm = ∧-intro Commutative ∧ᵗ-comm ∧ᶠ-comm
    }
  ; ·-distrib-∧ = ·-distrib-∧
  ; +-distrib-∧ = +-distrib-∧
  }
  where
  open Tools.Reasoning.PropositionalEquality

  +-assoc : Associative _+_
  +-assoc = λ where
    ⌞ m ⌟ ⌞ _ ⌟ ⌞ _ ⌟ → cong ⌞_⌟ (N.+-assoc m _ _)
    ⌞ _ ⌟ ⌞ _ ⌟ ∞     → refl
    ⌞ _ ⌟ ∞     _     → refl
    ∞     _     _     → refl

  +-comm : Commutative _+_
  +-comm = λ where
    ⌞ 0 ⌟    ⌞ 0 ⌟    → refl
    ⌞ 1+ _ ⌟ ⌞ 0 ⌟    → cong ⌞_⌟ (N.+-identityʳ _)
    ⌞ 0 ⌟    ⌞ 1+ _ ⌟ → cong ⌞_⌟ (sym (N.+-identityʳ _))
    ⌞ 1+ m ⌟ ⌞ 1+ _ ⌟ → cong ⌞_⌟ (N.+-comm (1+ m) _)
    ⌞ 0 ⌟    ∞        → refl
    ⌞ 1+ _ ⌟ ∞        → refl
    ∞        ⌞ 0 ⌟    → refl
    ∞        ⌞ 1+ _ ⌟ → refl
    ∞        ∞        → refl

  ·-assoc : Associative _·_
  ·-assoc = λ where
    ⌞ 0 ⌟    _        _        → refl
    ⌞ 1+ _ ⌟ ⌞ 0    ⌟ _        → refl
    ⌞ 1+ _ ⌟ ⌞ 1+ _ ⌟ ⌞ 0 ⌟    → refl
    ⌞ 1+ m ⌟ ⌞ 1+ n ⌟ ⌞ 1+ _ ⌟ → cong ⌞_⌟ $
                                 N.*-assoc (1+ m) (1+ n) (1+ _)
    ⌞ 1+ _ ⌟ ⌞ 1+ _ ⌟ ∞        → refl
    ⌞ 1+ _ ⌟ ∞        ⌞ 0  ⌟   → refl
    ⌞ 1+ _ ⌟ ∞        ⌞ 1+ _ ⌟ → refl
    ⌞ 1+ _ ⌟ ∞        ∞        → refl
    ∞        ⌞ 0    ⌟ _        → refl
    ∞        ⌞ 1+ _ ⌟ ⌞ 0 ⌟    → refl
    ∞        ⌞ 1+ _ ⌟ ⌞ 1+ _ ⌟ → refl
    ∞        ⌞ 1+ _ ⌟ ∞        → refl
    ∞        ∞        ⌞ 0  ⌟   → refl
    ∞        ∞        ⌞ 1+ _ ⌟ → refl
    ∞        ∞        ∞        → refl

  ·-distribˡ-+ : _·_ DistributesOverˡ _+_
  ·-distribˡ-+ = λ where
    ⌞ 0 ⌟    _        _        → refl
    ⌞ 1+ _ ⌟ ⌞ 0    ⌟ ⌞ 0 ⌟    → refl
    ⌞ 1+ _ ⌟ ⌞ 0    ⌟ ⌞ 1+ _ ⌟ → refl
    ⌞ 1+ _ ⌟ ⌞ 0    ⌟ ∞        → refl
    ⌞ 1+ m ⌟ ⌞ 1+ n ⌟ ⌞ 0 ⌟    →
      ⌞ 1+ m ⌟ · (⌞ 1+ n ⌟ + ⌞ 0 ⌟)           ≡⟨⟩
      ⌞ 1+ m N.* (1+ n N.+ 0) ⌟               ≡⟨ cong ⌞_⌟ (N.*-distribˡ-+ (1+ m) (1+ _) 0) ⟩
      ⌞ 1+ m N.* 1+ n N.+ 1+ m N.* 0 ⌟        ≡⟨ cong (λ o → ⌞ 1+ m N.* 1+ n N.+ o ⌟) (N.*-zeroʳ (1+ m)) ⟩
      ⌞ 1+ m N.* 1+ n N.+ 0 ⌟                 ≡⟨⟩
      ⌞ 1+ m ⌟ · ⌞ 1+ n ⌟ + ⌞ 1+ m ⌟ · ⌞ 0 ⌟  ∎
    ⌞ 1+ m ⌟ ⌞ 1+ _ ⌟ ⌞ 1+ _ ⌟ → cong ⌞_⌟ $
                                 N.*-distribˡ-+ (1+ m) (1+ _) (1+ _)
    ⌞ 1+ _ ⌟ ⌞ 1+ _ ⌟ ∞        → refl
    ⌞ 1+ _ ⌟ ∞        ⌞ 0  ⌟   → refl
    ⌞ 1+ _ ⌟ ∞        ⌞ 1+ _ ⌟ → refl
    ⌞ 1+ _ ⌟ ∞        ∞        → refl
    ∞        ⌞ 0    ⌟ ⌞ 0 ⌟    → refl
    ∞        ⌞ 0    ⌟ ⌞ 1+ _ ⌟ → refl
    ∞        ⌞ 0    ⌟ ∞        → refl
    ∞        ⌞ 1+ _ ⌟ ⌞ 0 ⌟    → refl
    ∞        ⌞ 1+ _ ⌟ ⌞ 1+ _ ⌟ → refl
    ∞        ⌞ 1+ _ ⌟ ∞        → refl
    ∞        ∞        ⌞ 0  ⌟   → refl
    ∞        ∞        ⌞ 1+ _ ⌟ → refl
    ∞        ∞        ∞        → refl

  ·-distrib-+ : _·_ DistributesOver _+_
  ·-distrib-+ =
    ·-distribˡ-+ , comm∧distrˡ⇒distrʳ ·-comm ·-distribˡ-+

  ∧ᵗ-comm : Commutative _∧ᵗ_
  ∧ᵗ-comm ⌞ m ⌟ ⌞ n ⌟ = cong ⌞_⌟ (N.⊔-comm m n)
  ∧ᵗ-comm ⌞ m ⌟ ∞ = refl
  ∧ᵗ-comm ∞ ⌞ n ⌟ = refl
  ∧ᵗ-comm ∞ ∞ = refl

  ∧ᶠ-comm : Commutative _∧ᶠ_
  ∧ᶠ-comm ⌞ m ⌟ ⌞ n ⌟ with m N.≟ n | n N.≟ m
  … | yes refl | yes _ = refl
  … | no m≢n | no n≢m = refl
  … | yes m≡n | no n≢m = ⊥-elim (n≢m (sym m≡n))
  … | no m≢n | yes n≡m = ⊥-elim (m≢n (sym n≡m))
  ∧ᶠ-comm ⌞ m ⌟ ∞ = refl
  ∧ᶠ-comm ∞ ⌞ n ⌟ = refl
  ∧ᶠ-comm ∞ ∞ = refl

  ∧ᵗ-assoc : Associative _∧ᵗ_
  ∧ᵗ-assoc = λ where
    ⌞ m ⌟ ⌞ _ ⌟ ⌞ _ ⌟ → cong ⌞_⌟ (N.⊔-assoc m _ _)
    ⌞ _ ⌟ ⌞ _ ⌟ ∞     → refl
    ⌞ _ ⌟ ∞     _     → refl
    ∞     _     _     → refl

  ∧ᶠ-assoc : Associative _∧ᶠ_
  ∧ᶠ-assoc = λ where
    ⌞ m ⌟ ⌞ n ⌟ ⌞ o ⌟ → lemma m n o
    ⌞ m ⌟ ⌞ n ⌟ ∞ → ∧ᶠ-comm (⌞ m ⌟ ∧ᶠ ⌞ n ⌟) ∞
    ⌞ _ ⌟ ∞ _ → refl
    ∞ _ _ → refl
      where
      lemma : ∀ m n o
            → (⌞ m ⌟ ∧ᶠ ⌞ n ⌟) ∧ᶠ ⌞ o ⌟
            ≡ ⌞ m ⌟ ∧ᶠ (⌞ n ⌟ ∧ᶠ ⌞ o ⌟)
      lemma m n o with n N.≟ o
      lemma m n o | yes n≡o with m N.≟ n
      lemma m n o | yes n≡o | no m≢n = refl
      lemma m n o | yes n≡o | yes m≡n with m N.≟ o
      lemma m n o | yes n≡o | yes m≡n | yes m≡o = refl
      lemma m n o | yes n≡o | yes m≡n | no m≢o = ⊥-elim (m≢o (trans m≡n n≡o))
      lemma m n o | no n≢o with m N.≟ n
      lemma m n o | no n≢o | no m≢n = refl
      lemma m n o | no n≢o | yes m≡n with m N.≟ o
      lemma m n o | no n≢o | yes m≡n | yes m≡o = ⊥-elim (n≢o (trans (sym m≡n) m≡o))
      lemma m n o | no n≢o | yes m≡n | no m≢o = refl

  ∧ᵗ-idem : Idempotent _∧ᵗ_
  ∧ᵗ-idem = λ where
    ∞     → refl
    ⌞ _ ⌟ → cong ⌞_⌟ (N.⊔-idem _)

  ∧ᶠ-idem : Idempotent _∧ᶠ_
  ∧ᶠ-idem ⌞ m ⌟ with m N.≟ m
  … | yes _ = refl
  … | no m≢m = ⊥-elim (m≢m refl)
  ∧ᶠ-idem ∞ = refl

  ·-distribˡ-∧ᵗ : _·_ DistributesOverˡ _∧ᵗ_
  ·-distribˡ-∧ᵗ ⌞ 0 ⌟ _ _ = refl
  ·-distribˡ-∧ᵗ ⌞ 1+ _ ⌟ ⌞ 0 ⌟ ⌞ 0 ⌟ = refl
  ·-distribˡ-∧ᵗ ⌞ 1+ _ ⌟ ⌞ 0 ⌟ ⌞ 1+ _ ⌟ = refl
  ·-distribˡ-∧ᵗ ⌞ 1+ _ ⌟ ⌞ 0 ⌟ ∞ = refl
  ·-distribˡ-∧ᵗ ⌞ 1+ _ ⌟ ⌞ 1+ _ ⌟ ⌞ 0 ⌟ = refl
  ·-distribˡ-∧ᵗ ⌞ 1+ m ⌟ ⌞ 1+ n ⌟ ⌞ 1+ _ ⌟ = cong ⌞_⌟ $
                                             N.*-distribˡ-⊔ (1+ m) (1+ n) (1+ _)
  ·-distribˡ-∧ᵗ ⌞ 1+ _ ⌟ ⌞ 1+ _ ⌟ ∞ = refl
  ·-distribˡ-∧ᵗ ⌞ 1+ _ ⌟ ∞ _ = refl
  ·-distribˡ-∧ᵗ ∞ ⌞ 0 ⌟ ⌞ 0 ⌟ = refl
  ·-distribˡ-∧ᵗ ∞ ⌞ 0 ⌟ ⌞ 1+ _ ⌟ = refl
  ·-distribˡ-∧ᵗ ∞ ⌞ 0 ⌟ ∞ = refl
  ·-distribˡ-∧ᵗ ∞ ⌞ 1+ _ ⌟ ⌞ 0 ⌟ = refl
  ·-distribˡ-∧ᵗ ∞ ⌞ 1+ _ ⌟ ⌞ 1+ _ ⌟ = refl
  ·-distribˡ-∧ᵗ ∞ ⌞ 1+ _ ⌟ ∞ = refl
  ·-distribˡ-∧ᵗ ∞ ∞ _ = refl

  ·-distribˡ-∧ᶠ : _·_ DistributesOverˡ _∧ᶠ_
  ·-distribˡ-∧ᶠ ⌞ 0 ⌟ _ _ = refl
  ·-distribˡ-∧ᶠ ⌞ 1+ m ⌟ ⌞ 0 ⌟ ⌞ 0 ⌟ = refl
  ·-distribˡ-∧ᶠ ⌞ 1+ m ⌟ ⌞ 0 ⌟ ⌞ 1+ o ⌟ = refl
  ·-distribˡ-∧ᶠ ⌞ 1+ m ⌟ ⌞ 1+ n ⌟ ⌞ 0 ⌟ = refl
  ·-distribˡ-∧ᶠ ⌞ 1+ m ⌟ ⌞ 1+ n ⌟ ⌞ 1+ o ⌟
    with 1+ n N.≟ 1+ o | 1+ m N.* 1+ n N.≟ 1+ m N.* 1+ o
  … | yes refl | yes _ = refl
  … | yes refl | no ¬≡ = ⊥-elim (¬≡ refl)
  … | no n≢o | yes eq = ⊥-elim (n≢o (N.*-cancelˡ-≡ (1+ n) (1+ o) (1+ m) eq))
  … | no _ | no _ = refl
  ·-distribˡ-∧ᶠ ⌞ 1+ m ⌟ ⌞ n ⌟ ∞ = sym (∧ᶠ-comm (⌞ 1+ m ⌟ · ⌞ n ⌟) ∞)
  ·-distribˡ-∧ᶠ ⌞ 1+ _ ⌟ ∞ _ = refl
  ·-distribˡ-∧ᶠ ∞ ⌞ n ⌟ ⌞ o ⌟ with n N.≟ o
  … | yes refl = sym (∧ᶠ-idem (∞ · ⌞ n ⌟))
  ·-distribˡ-∧ᶠ ∞ ⌞ 0 ⌟ ⌞ 0 ⌟ | no n≢o = ⊥-elim (n≢o refl)
  ·-distribˡ-∧ᶠ ∞ ⌞ 0 ⌟ ⌞ 1+ o ⌟ | no n≢o = refl
  ·-distribˡ-∧ᶠ ∞ ⌞ 1+ n ⌟ ⌞ o ⌟ | no n≢o = refl
  ·-distribˡ-∧ᶠ ∞ ⌞ n ⌟ ∞ = sym (∧ᶠ-comm (∞ · ⌞ n ⌟) ∞)
  ·-distribˡ-∧ᶠ ∞ ∞ _ = refl

  ·-distribˡ-∧ : _·_ DistributesOverˡ _∧_
  ·-distribˡ-∧ =
    ∧-intro (_·_ DistributesOverˡ_) ·-distribˡ-∧ᵗ ·-distribˡ-∧ᶠ

  ·-distrib-∧ : _·_ DistributesOver _∧_
  ·-distrib-∧ =
    ·-distribˡ-∧ , comm∧distrˡ⇒distrʳ ·-comm ·-distribˡ-∧

  +-distribˡ-∧ᵗ : _+_ DistributesOverˡ _∧ᵗ_
  +-distribˡ-∧ᵗ ⌞ m ⌟ ⌞ _ ⌟ ⌞ _ ⌟ = cong ⌞_⌟ (N.+-distribˡ-⊔ m _ _)
  +-distribˡ-∧ᵗ ⌞ _ ⌟ ⌞ _ ⌟ ∞     = refl
  +-distribˡ-∧ᵗ ⌞ _ ⌟ ∞     _     = refl
  +-distribˡ-∧ᵗ ∞     _     _     = refl

  +-distribˡ-∧ᶠ : _+_ DistributesOverˡ _∧ᶠ_
  +-distribˡ-∧ᶠ ⌞ m ⌟ ⌞ n ⌟ ⌞ o ⌟ with n N.≟ o | m N.+ n N.≟ m N.+ o
  … | yes n≡o | yes m+n≡m+o = refl
  … | yes refl | no m+n≢m+o = ⊥-elim (m+n≢m+o refl)
  … | no n≢o | yes m+n≡m+o = ⊥-elim (n≢o (N.+-cancelˡ-≡ m n o m+n≡m+o))
  … | no n≢o | no m+n≢m+o = refl
  +-distribˡ-∧ᶠ ⌞ _ ⌟ ⌞ _ ⌟ ∞     = refl
  +-distribˡ-∧ᶠ ⌞ _ ⌟ ∞     _     = refl
  +-distribˡ-∧ᶠ ∞     _     _     = refl

  +-distribˡ-∧ : _+_ DistributesOverˡ _∧_
  +-distribˡ-∧ =
    ∧-intro (_+_ DistributesOverˡ_) +-distribˡ-∧ᵗ +-distribˡ-∧ᶠ

  +-distrib-∧ : _+_ DistributesOver _∧_
  +-distrib-∧ =
    +-distribˡ-∧ , comm∧distrˡ⇒distrʳ +-comm +-distribˡ-∧

instance

  -- The modality has a well-behaved zero.

  ℕ⊎∞-has-well-behaved-zero :
    Has-well-behaved-zero ℕ⊎∞-modality
  ℕ⊎∞-has-well-behaved-zero = record
    { non-trivial  = λ ()
    ; zero-product = λ where
        {p = ⌞ 0 ⌟}    {q = ⌞ _ ⌟}    _  → inj₁ refl
        {p = ⌞ 0 ⌟}    {q = ∞}        _  → inj₁ refl
        {p = ⌞ _ ⌟}    {q = ⌞ 0 ⌟}    _  → inj₂ refl
        {p = ∞}        {q = ⌞ 0 ⌟}    _  → inj₂ refl
        {p = ⌞ 1+ _ ⌟} {q = ⌞ 1+ _ ⌟} ()
        {p = ⌞ 1+ _ ⌟} {q = ∞}        ()
        {p = ∞}        {q = ⌞ 1+ _ ⌟} ()
        {p = ∞}        {q = ∞}        ()
    ; +-positiveˡ  = λ where
        {p = ⌞ 0 ⌟} {q = ⌞ _ ⌟}    _  → refl
        {p = ⌞ 1+ _ ⌟} {q = ⌞ _ ⌟} ()
        {p = ⌞ _ ⌟} {q = ∞}        ()
        {p = ∞}                    ()
    ; ∧-positiveˡ  = ∧-intro (λ _∧₁_ → {p q : ℕ⊎∞} → (p ∧₁ q) ≡ ⌞ 0 ⌟ → p ≡ ⌞ 0 ⌟)
      (λ where
        {p = ⌞ 0 ⌟}    {q = ⌞ _ ⌟}    _  → refl
        {p = ⌞ 1+ _ ⌟} {q = ⌞ 0 ⌟}    ()
        {p = ⌞ 1+ _ ⌟} {q = ⌞ 1+ _ ⌟} ()
        {p = ⌞ _ ⌟}    {q = ∞}        ()
        {p = ∞}                       ())
      (λ where
        {p = ⌞ 0 ⌟}    {q = ⌞ _ ⌟}    _  → refl
        {p = ⌞ 1+ _ ⌟} {q = ⌞ 0 ⌟}    ()
        {p = ⌞ 1+ m ⌟} {q = ⌞ 1+ n ⌟} x  → ⊥-elim (lemma m n x)
        {p = ⌞ _ ⌟}    {q = ∞}        ()
        {p = ∞}                       ())
    }
   where
   lemma : ∀ m n → ⌞ 1+ m ⌟ ∧ᶠ ⌞ 1+ n ⌟ ≢ ⌞ 0 ⌟
   lemma m n 1+m∧1+n≡0 with 1+ m N.≟ 1+ n
   lemma m .m () | yes refl
   lemma m n () | no _

private
  module BS =
    BoundedStar
      ℕ⊎∞-modality _* (λ _ → *≡+·*) (λ _ → inj₂ n*≤1)

-- A natrec-star operator for ℕ⊎∞ defined using the construction in
-- Graded.Modality.Instances.BoundedStar.

ℕ⊎∞-has-star-bounded-star : Has-star ℕ⊎∞-modality
ℕ⊎∞-has-star-bounded-star = BS.has-star

-- A natrec-star operator for ℕ⊎∞ defined using the construction in
-- Graded.Modality.Instances.LowerBounded.

ℕ⊎∞-has-star-lower-bounded : Has-star ℕ⊎∞-modality
ℕ⊎∞-has-star-lower-bounded =
  LowerBounded.has-star ℕ⊎∞-modality ∞ ∞≤

-- The _⊛_▷_ operator of the second modality is equal to the _⊛_▷_
-- operator of the first modality for non-zero last arguments.

≢𝟘→⊛▷≡⊛▷ :
  let module HS₁ = Has-star ℕ⊎∞-has-star-bounded-star
      module HS₂ = Has-star ℕ⊎∞-has-star-lower-bounded
  in
  o ≢ ⌞ 0 ⌟ →
  m HS₁.⊛ n ▷ o ≡ m HS₂.⊛ n ▷ o
≢𝟘→⊛▷≡⊛▷ {o = ∞}        _   = refl
≢𝟘→⊛▷≡⊛▷ {o = ⌞ 1+ _ ⌟} _   = refl
≢𝟘→⊛▷≡⊛▷ {o = ⌞ 0 ⌟}    0≢0 = ⊥-elim (0≢0 refl)

-- The _⊛_▷_ operator of the second modality is bounded strictly by
-- the _⊛_▷_ operator of the first modality.

⊛▷<⊛▷ :
  let module HS₁ = Has-star ℕ⊎∞-has-star-bounded-star
      module HS₂ = Has-star ℕ⊎∞-has-star-lower-bounded
  in
  (∀ m n o → m HS₂.⊛ n ▷ o ≤ m HS₁.⊛ n ▷ o) ×
  (∃₃ λ m n o → m HS₂.⊛ n ▷ o ≢ m HS₁.⊛ n ▷ o)
⊛▷<⊛▷ =
    BS.LowerBounded.⊛′≤⊛ ∞ ∞≤
  , ⌞ 1 ⌟ , ⌞ 1 ⌟ , ⌞ 0 ⌟ , lemma total
  where
  lemma : ∀ b
        → ∞ · (if b then ⌞ 1 ⌟ else ⌞ 1 ⌟)
        ≢ ⌞ 1 ⌟ · (if b then ⌞ 1 ⌟ else ⌞ 1 ⌟)
  lemma false ()
  lemma true ()

------------------------------------------------------------------------
-- Properties related to division

private
  module D = Graded.Modality.Properties.Division ℕ⊎∞-modality

opaque

  -- The division operator is correctly defined (for the total order).

  /≡/ : T total → m D./ n ≡ m / n
  /≡/ {m} {n} x = lemma (proj₁ T-true x) m n
    where
    lemma : total ≡ true → (m n : ℕ⊎∞) → m D./ n ≡ m / n
    lemma refl ∞     ∞        = refl , λ _ _ → refl
    lemma refl ⌞ _ ⌟ ∞        = ≤0 _ ,
                                λ where
                                  ⌞ 0    ⌟ _  → refl
                                  ⌞ 1+ _ ⌟ ()
                                  ∞        ()
    lemma refl _     ⌞ 0 ⌟    = ≤0 _ , λ _ _ → refl
    lemma refl ∞     ⌞ 1+ _ ⌟ = refl , λ _ _ → refl
    lemma refl ⌞ m ⌟ ⌞ 1+ n ⌟ =
      (begin
           ⌞ m ⌟                      ≤⟨ ⌞⌟-antitone _ (N.m/n*n≤m _ (1+ _)) ⟩
           ⌞ (m N./ 1+ n) N.* 1+ n ⌟  ≡⟨ cong ⌞_⌟ (N.*-comm _ (1+ n)) ⟩
           ⌞ 1+ n N.* (m N./ 1+ n) ⌟  ≡˘⟨ ⌞⌟·⌞⌟≡⌞*⌟ ⟩
           ⌞ 1+ n ⌟ · ⌞ m N./ 1+ n ⌟  ∎)
      , λ where
          ∞     → λ ()
          ⌞ o ⌟ →
            ⌞ m ⌟ ≤ ⌞ 1+ n ⌟ · ⌞ o ⌟  ≡⟨ cong (_ ≤_) ⌞⌟·⌞⌟≡⌞*⌟ ⟩→
            ⌞ m ⌟ ≤ ⌞ 1+ n N.* o ⌟    →⟨ ⌞⌟-antitone⁻¹ ⟩
            1+ n N.* o N.≤ m          →⟨ N.*≤→≤/ ⟩
            o N.≤ m N./ 1+ n          →⟨ ⌞⌟-antitone _ ⟩
            ⌞ m N./ 1+ n ⌟ ≤ ⌞ o ⌟    □
      where
      open Graded.Modality.Properties.PartialOrder ℕ⊎∞-modality
      open Tools.Reasoning.PartialOrder ≤-poset

opaque

  -- The division operator is not correctly defined (for the flat order).

  ¬/≡/ : T (not total) → ¬ (∀ m n → m D./ n ≡ m / n)
  ¬/≡/ x /≡/ = lemma (proj₁ ¬-T (proj₁ T-not⇔¬-T x)) /≡/
    where
    lemma : total ≡ false → ¬ (∀ m n → m D./ n ≡ m / n)
    lemma refl /≡/ = case /≡/ ⌞ 1 ⌟ ∞ of λ {(() , _)}

------------------------------------------------------------------------
-- A lemma related to Graded.Modality.Instances.Recursive

module _ where

  open Graded.Modality.Instances.Recursive.Sequences
         ℕ⊎∞-modality

  -- The family of sequences that Graded.Modality.Instances.Recursive is
  -- about does not have the required fixpoints.

  ¬-Has-fixpoints-nr : T total → ¬ Has-fixpoints-nr
  ¬-Has-fixpoints-nr x = lemma (proj₁ T-true x)
    where
    open module S = Modality ℕ⊎∞-modality using (𝟘; 𝟙)
    open Graded.Modality.Properties.Meet ℕ⊎∞-modality
    open Tools.Reasoning.PropositionalEquality

    r = 𝟙
    p = 𝟘
    q = 𝟙

    increasing : total ≡ true → ∀ n → nr (1+ n) p q r ≡ 𝟙 + nr n p q r
    increasing refl 0      = refl
    increasing refl (1+ n) =
      p ∧ (q + r · nr (1+ n) p q r)   ≡⟨ largest→∧≡ʳ (λ _ → ≤0 _) ⟩
      q + r · nr (1+ n) p q r         ≡⟨ cong (λ n → q + r · n) (increasing refl n) ⟩
      q + r · (𝟙 + nr n p q r)        ≡⟨ cong (q +_) (S.·-identityˡ _) ⟩
      q + (𝟙 + nr n p q r)            ≡˘⟨ S.+-assoc _ _ _ ⟩
      (q + 𝟙) + nr n p q r            ≡⟨ cong (_+ nr n p q r) (S.+-comm q _) ⟩
      (𝟙 + q) + nr n p q r            ≡⟨ S.+-assoc _ _ _ ⟩
      𝟙 + (q + nr n p q r)            ≡˘⟨ cong ((𝟙 +_) ∘→ (q +_)) (S.·-identityˡ _) ⟩
      𝟙 + (q + r · nr n p q r)        ≡˘⟨ cong (𝟙 +_) (largest→∧≡ʳ (λ _ → ≤0 _)) ⟩
      𝟙 + (p ∧ (q + r · nr n p q r))  ∎

    always-⌞⌟ : total ≡ true → ∀ m → ∃ λ n → nr m p q r ≡ ⌞ n ⌟
    always-⌞⌟ refl 0      = _ , refl
    always-⌞⌟ refl (1+ m) =
      case always-⌞⌟ refl m of λ {
        (n , eq) →
        1+ n
      , (nr (1+ m) p q r  ≡⟨ increasing refl m ⟩
         𝟙 + nr m p q r   ≡⟨ cong (𝟙 +_) eq ⟩
         ⌞ 1+ n ⌟         ∎) }

    lemma : total ≡ true → ¬ Has-fixpoints-nr
    lemma refl =
      (∀ r → ∃ λ n → ∀ p q → nr (1+ n) p q r ≡ nr n p q r)  →⟨ (λ hyp → Σ.map idᶠ (λ f → f p q) (hyp r)) ⟩
      (∃ λ n → nr (1+ n) p q r ≡ nr n p q r)                →⟨ Σ.map idᶠ (λ {x = n} → trans (sym (increasing refl n))) ⟩
      (∃ λ n → ⌞ 1 ⌟ + nr n p q r ≡ nr n p q r)             →⟨ (λ (n , hyp) →
                                                                     _
                                                                  , subst (λ n → ⌞ 1 ⌟ + n ≡ n) (always-⌞⌟ refl n .proj₂) hyp) ⟩
      (∃ λ n → ⌞ 1+ n ⌟ ≡ ⌞ n ⌟)                            →⟨ (λ { (_ , ()) }) ⟩
      ⊥                                                     □

------------------------------------------------------------------------
-- An nr function for ℕ⊎∞

private variable
  z₁ z₂ s₁ s₂ n₁ n₂ : ℕ⊎∞

-- A function used to define nr

nr₃ : Op₃ ℕ⊎∞
nr₃ ⌞ 0 ⌟    z s = z ∧ s
nr₃ ⌞ 1 ⌟ z s = z + ∞ · s
nr₃ ⌞ 2+ _ ⌟ z s = ∞ · (z + s)
nr₃ ∞        z s = ∞ · (z + s)

opaque

  -- nr₃ is zero only if the two latter arguments are zero

  nr₃-positive : ∀ {z s} r → nr₃ r z s ≡ ⌞ 0 ⌟ → z ≡ ⌞ 0 ⌟ × s ≡ ⌞ 0 ⌟
  nr₃-positive = λ where
    ⌞ 0 ⌟ → ∧-positive
    ⌞ 1 ⌟ nr₃≡𝟘 →
      case +-positive nr₃≡𝟘 of λ
        (z≡𝟘 , ∞s≡𝟘) →
      case zero-product ∞s≡𝟘 of λ where
        (inj₁ ())
        (inj₂ s≡𝟘) → z≡𝟘 , s≡𝟘
    ⌞ 2+ _ ⌟ nr₃≡𝟘 →
      case zero-product nr₃≡𝟘 of λ where
        (inj₁ ())
        (inj₂ z+s≡𝟘) → +-positive z+s≡𝟘
    ∞ nr₃≡𝟘 →
        case zero-product nr₃≡𝟘 of λ where
          (inj₁ ())
          (inj₂ z+s≡𝟘) → +-positive z+s≡𝟘
      where
      open Graded.Modality.Properties.Has-well-behaved-zero ℕ⊎∞-modality

opaque

  -- nr₃ r z s ≤ s + r · nr₃ r z s

  nr₃-suc : ∀ {z s} r → nr₃ r z s ≤ s + r · nr₃ r z s
  nr₃-suc {z} {s} = λ where
    ⌞ 0 ⌟ → begin
      z ∧ s     ≤⟨ ∧-decreasingʳ z s ⟩
      s         ≡˘⟨ +-identityʳ s ⟩
      s + ⌞ 0 ⌟ ∎
    ⌞ 1 ⌟ → begin
      z + ∞ · s               ≡⟨⟩
      z + (∞ + ⌞ 1 ⌟) · s     ≡⟨ +-congˡ (·-distribʳ-+ _ _ _) ⟩
      z + ∞ · s + ⌞ 1 ⌟ · s   ≡⟨ +-congˡ (+-congˡ (·-identityˡ _)) ⟩
      z + ∞ · s + s           ≡˘⟨ +-assoc _ _ _ ⟩
      (z + ∞ · s) + s         ≡⟨ +-comm _ _ ⟩
      s + (z + ∞ · s)         ≡˘⟨ +-congˡ (·-identityˡ _) ⟩
      s + ⌞ 1 ⌟ · (z + ∞ · s) ∎
    ⌞ 2+ r ⌟ → begin
      ∞ · (z + s)                  ≡⟨ lemma z s ⟩
      s + ∞ · (z + s)              ≡⟨⟩
      s + (∞ · ⌞ 2+ r ⌟) · (z + s) ≡⟨ +-congˡ (·-congʳ (·-comm ∞ ⌞ 2+ r ⌟)) ⟩
      s + (⌞ 2+ r ⌟ · ∞) · (z + s) ≡⟨ +-congˡ (·-assoc _ _ _) ⟩
      s + ⌞ 2+ r ⌟ · ∞ · (z + s)   ∎
    ∞ → begin
      ∞ · (z + s)           ≡⟨ lemma z s ⟩
      s + ∞ · (z + s)       ≡⟨⟩
      s + (∞ · ∞) · (z + s) ≡⟨ +-congˡ (·-assoc _ _ _) ⟩
      s + ∞ · ∞ · (z + s)   ∎
      where
      open Modality ℕ⊎∞-modality
        using (+-congˡ; +-identityʳ; +-identityˡ; +-assoc; +-comm;
               ·-congʳ; ·-identityˡ; ·-assoc; ·-distribʳ-+)
      open Graded.Modality.Properties.Meet ℕ⊎∞-modality
      open Graded.Modality.Properties.PartialOrder ℕ⊎∞-modality
      open Tools.Reasoning.PartialOrder ≤-poset
      lemma : ∀ z s → ∞ · (z + s) ≡ s + ∞ · (z + s)
      lemma z ⌞ 0 ⌟ = sym (+-identityˡ _)
      lemma ⌞ 0 ⌟ ⌞ 1+ s ⌟ = refl
      lemma ⌞ 1+ z ⌟ ⌞ 1+ s ⌟ = refl
      lemma ∞ ⌞ 1+ s ⌟ = refl
      lemma z ∞ rewrite +-comm z ∞ = refl

opaque

  -- nr₃ r ⌞ 0 ⌟ ⌞ 0 ⌟ is equal to ⌞ 0 ⌟ for all r.

  nr₃-𝟘 : ∀ r → nr₃ r ⌞ 0 ⌟ ⌞ 0 ⌟ ≡ ⌞ 0 ⌟
  nr₃-𝟘 ⌞ 0 ⌟ =
    Modality.∧-idem ℕ⊎∞-modality ⌞ 0 ⌟
  nr₃-𝟘 ⌞ 1+ 0 ⌟ = refl
  nr₃-𝟘 ⌞ 2+ x ⌟ = refl
  nr₃-𝟘 ∞ = refl

opaque

  -- A sub-distributivity property for nr₃ over _+_.

  nr₃-+ : ∀ r → nr₃ r z₁ s₁ + nr₃ r z₂ s₂ ≤ nr₃ r (z₁ + z₂) (s₁ + s₂)
  nr₃-+ {z₁} {s₁} {z₂} {s₂} = λ where
    ⌞ 0 ⌟ → +-sub-interchangeable-∧ z₁ s₁ z₂ s₂
    ⌞ 1+ 0 ⌟ → begin
      (z₁ + ∞ · s₁) + z₂ + ∞ · s₂ ≡⟨ +-assoc _ _ _ ⟩
      z₁ + ∞ · s₁ + z₂ + ∞ · s₂   ≡˘⟨ +-congˡ (+-assoc _ _ _) ⟩
      z₁ + (∞ · s₁ + z₂) + ∞ · s₂ ≡⟨ +-congˡ (+-congʳ (+-comm _ _)) ⟩
      z₁ + (z₂ + ∞ · s₁) + ∞ · s₂ ≡⟨ +-congˡ (+-assoc _ _ _) ⟩
      z₁ + z₂ + ∞ · s₁ + ∞ · s₂   ≡˘⟨ +-assoc _ _ _ ⟩
      (z₁ + z₂) + ∞ · s₁ + ∞ · s₂ ≡˘⟨ +-congˡ (·-distribˡ-+ _ _ _) ⟩
      (z₁ + z₂) + ∞ · (s₁ + s₂)   ∎
    ⌞ 2+ r ⌟ → lemma
    ∞ → lemma
     where
     open Graded.Modality.Properties.PartialOrder ℕ⊎∞-modality
     open Graded.Modality.Properties.Addition ℕ⊎∞-modality
     open Modality ℕ⊎∞-modality
       hiding (_≤_; _·_; _+_)
     open Tools.Reasoning.PartialOrder ≤-poset
     lemma : ∞ · (z₁ + s₁) + ∞ · (z₂ + s₂) ≤ ∞ · ((z₁ + z₂) + (s₁ + s₂))
     lemma = begin
       ∞ · (z₁ + s₁) + ∞ · (z₂ + s₂) ≡˘⟨ ·-distribˡ-+ _ _ _ ⟩
       ∞ · ((z₁ + s₁) + (z₂ + s₂))   ≡⟨ ·-congˡ (+-assoc _ _ _) ⟩
       ∞ · (z₁ + s₁ + z₂ + s₂)       ≡˘⟨ ·-congˡ (+-congˡ (+-assoc _ _ _)) ⟩
       ∞ · (z₁ + (s₁ + z₂) + s₂)     ≡⟨ ·-congˡ (+-congˡ (+-congʳ (+-comm _ _))) ⟩
       ∞ · (z₁ + (z₂ + s₁) + s₂)     ≡⟨ ·-congˡ (+-congˡ (+-assoc _ _ _)) ⟩
       ∞ · (z₁ + z₂ + s₁ + s₂)       ≡˘⟨ ·-congˡ (+-assoc _ _ _) ⟩
       ∞ · ((z₁ + z₂) + (s₁ + s₂))   ∎

opaque

  -- Given a function nr₂, satisfying some properties, one can construct
  -- an nr function from nr₃.

  nr₂→has-nr : (nr₂ : Op₂ ℕ⊎∞) → (∀ {p r} → nr₂ p r ≢ ⌞ 0 ⌟)
             → (∀ {p r} → nr₂ p r ≤ p + r · nr₂ p r)
             → Has-nr ℕ⊎∞-modality
  nr₂→has-nr nr₂ nr₂≢𝟘 nr₂≤ = record
    { nr = nr
    ; nr-monotone = λ {p = p} {r} → nr-monotone p r
    ; nr-· = λ {p} {r} {z} {s} {n} {q} → ≤-reflexive (nr-· p r z s n q)
    ; nr-+ = λ {p} {r} {z₁} {s₁} {n₁} {z₂} {s₂} {n₂} → nr-+ p r z₁ s₁ n₁ z₂ s₂ n₂
    ; nr-positive = λ {p} {r} → nr-positive {p} {r}
    ; nr-zero = λ {n} {p} {r} {z} {s} → nr-zero p r z s n
    ; nr-suc = λ {p} {r} {z} {s} {n} → nr-suc p r z s n
    }
    where
    open Modality ℕ⊎∞-modality
      hiding (_≤_; _+_; _·_; _∧_)
    open Graded.Modality.Properties.Addition ℕ⊎∞-modality
    open Graded.Modality.Properties.Has-well-behaved-zero ℕ⊎∞-modality
    open Graded.Modality.Properties.Meet ℕ⊎∞-modality
    open Graded.Modality.Properties.Multiplication ℕ⊎∞-modality
    open Graded.Modality.Properties.PartialOrder ℕ⊎∞-modality

    nr : (p r z s n : ℕ⊎∞) → ℕ⊎∞
    nr p r z s n = nr₂ p r · n + nr₃ r z s

    nr-monotone :
      ∀ p r →
      z₁ ≤ z₂ → s₁ ≤ s₂ → n₁ ≤ n₂ →
      nr p r z₁ s₁ n₁ ≤ nr p r z₂ s₂ n₂
    nr-monotone p r z₁≤z₂ s₁≤s₂ n₁≤n₂ =
      +-monotone (·-monotoneʳ n₁≤n₂) (lemma r z₁≤z₂ s₁≤s₂)
      where
      lemma : ∀ r → z₁ ≤ z₂ → s₁ ≤ s₂ → nr₃ r z₁ s₁ ≤ nr₃ r z₂ s₂
      lemma ⌞ 0 ⌟    z₁≤z₂ s₁≤s₂ = ∧-monotone z₁≤z₂ s₁≤s₂
      lemma ⌞ 1 ⌟    z₁≤z₂ s₁≤s₂ = +-monotone z₁≤z₂ (·-monotoneʳ s₁≤s₂)
      lemma ⌞ 2+ _ ⌟ z₁≤z₂ s₁≤s₂ = ·-monotoneʳ (+-monotone z₁≤z₂ s₁≤s₂)
      lemma ∞        z₁≤z₂ s₁≤s₂ = ·-monotoneʳ (+-monotone z₁≤z₂ s₁≤s₂)

    nr-· : ∀ p r z s n q → nr p r z s n · q ≡ nr p r (z · q) (s · q) (n · q)
    nr-· p r z s n q = begin
      nr p r z s n · q                          ≡⟨⟩
      (nr₂ p r · n + nr₃ r z s) · q             ≡⟨ ·-distribʳ-+ _ _ _ ⟩
      (nr₂ p r · n) · q + nr₃ r z s · q         ≡⟨ +-cong (·-assoc _ _ _) (lemma r) ⟩
      nr₂ p r · (n · q) + nr₃ r (z · q) (s · q) ≡⟨⟩
      nr p r (z · q) (s · q) (n · q)            ∎
      where
      open Tools.Reasoning.PropositionalEquality
      lemma : ∀ r → nr₃ r z s · q ≡ nr₃ r (z · q) (s · q)
      lemma ⌞ 0 ⌟    = ·-distribʳ-∧ _ _ _
      lemma ⌞ 1 ⌟    = trans (·-distribʳ-+ _ _ _) (+-congˡ (·-assoc _ _ _))
      lemma ⌞ 2+ _ ⌟ = trans (·-assoc _ _ _) (·-congˡ (·-distribʳ-+ _ _ _))
      lemma ∞        = trans (·-assoc _ _ _) (·-congˡ (·-distribʳ-+ _ _ _))

    nr-+ : ∀ p r z₁ s₁ n₁ z₂ s₂ n₂ → nr p r z₁ s₁ n₁ + nr p r z₂ s₂ n₂ ≤ nr p r (z₁ + z₂) (s₁ + s₂) (n₁ + n₂)
    nr-+ p r z₁ s₁ n₁ z₂ s₂ n₂ = begin
      nr p r z₁ s₁ n₁ + nr p r z₂ s₂ n₂                           ≡⟨⟩
      (nr₂ p r · n₁ + nr₃ r z₁ s₁) + (nr₂ p r · n₂ + nr₃ r z₂ s₂) ≡⟨ +-assoc _ _ _ ⟩
      nr₂ p r · n₁ + nr₃ r z₁ s₁ + nr₂ p r · n₂ + nr₃ r z₂ s₂     ≡˘⟨ +-congˡ (+-assoc _ _ _) ⟩
      nr₂ p r · n₁ + (nr₃ r z₁ s₁ + nr₂ p r · n₂) + nr₃ r z₂ s₂   ≡⟨ +-congˡ (+-congʳ (+-comm _ _)) ⟩
      nr₂ p r · n₁ + (nr₂ p r · n₂ + nr₃ r z₁ s₁) + nr₃ r z₂ s₂   ≡⟨ +-congˡ (+-assoc _ _ _) ⟩
      nr₂ p r · n₁ + nr₂ p r · n₂ + nr₃ r z₁ s₁ + nr₃ r z₂ s₂     ≡˘⟨ +-assoc _ _ _ ⟩
      (nr₂ p r · n₁ + nr₂ p r · n₂) + nr₃ r z₁ s₁ + nr₃ r z₂ s₂   ≡˘⟨ +-congʳ (·-distribˡ-+ _ _ _) ⟩
      nr₂ p r · (n₁ + n₂) + nr₃ r z₁ s₁ + nr₃ r z₂ s₂             ≤⟨ +-monotoneʳ (nr₃-+ r) ⟩
      nr₂ p r · (n₁ + n₂) + nr₃ r (z₁ + z₂) (s₁ + s₂)             ≡⟨⟩
      nr p r (z₁ + z₂) (s₁ + s₂) (n₁ + n₂)                        ∎
      where
      open Tools.Reasoning.PartialOrder ≤-poset

    nr-positive : ∀ {p r z s n} → nr p r z s n ≡ 𝟘 → z ≡ 𝟘 × s ≡ 𝟘 × n ≡ 𝟘
    nr-positive {r = r} nr≡𝟘 =
      case +-positive nr≡𝟘 of λ
        (x , y) →
      case nr₃-positive r y of λ
        (z≡𝟘 , s≡𝟘) →
      case zero-product x of λ where
        (inj₁ nr₂≡𝟘) →
          ⊥-elim (nr₂≢𝟘 nr₂≡𝟘)
        (inj₂ n≡𝟘) →
          z≡𝟘 , s≡𝟘 , n≡𝟘

    nr-zero : ∀ p r z s n → n ≤ 𝟘 → nr p r z s n ≤ z
    nr-zero p r z s n n≤𝟘 = begin
      nr p r z s n              ≡⟨⟩
      nr₂ p r · n + nr₃ r z s ≤⟨ +-monotoneˡ (·-monotoneʳ n≤𝟘) ⟩
      nr₂ p r · 𝟘 + nr₃ r z s ≡⟨ +-congʳ (·-zeroʳ _) ⟩
      𝟘 + nr₃ r z s             ≡⟨ +-identityˡ _ ⟩
      nr₃ r z s                 ≤⟨ lemma r ⟩
      z                         ∎
      where
      open Tools.Reasoning.PartialOrder ≤-poset
      lemma′ : ∞ · (z + s) ≤ z
      lemma′ = begin
        ∞ · (z + s) ≤⟨ ω·+≤ω·ˡ ⟩
        ∞ · z       ≤⟨ ·-monotoneˡ ω≤𝟙 ⟩
        𝟙 · z       ≡⟨ ·-identityˡ _ ⟩
        z           ∎
      lemma : ∀ r → nr₃ r z s ≤ z
      lemma ⌞ 0 ⌟ = ∧-decreasingˡ _ _
      lemma ⌞ 1 ⌟ = begin
        z + ∞ · s ≤⟨ +-monotoneʳ (·-monotoneˡ {q = 𝟘} ω≤𝟘) ⟩
        z + 𝟘 · s ≡⟨⟩
        z + 𝟘     ≡⟨ +-identityʳ _ ⟩
        z         ∎
      lemma ⌞ 2+ _ ⌟ = lemma′
      lemma ∞        = lemma′

    nr-suc : ∀ p r z s n → nr p r z s n ≤ s + p · n + r · nr p r z s n
    nr-suc p r z s n = begin
      nr p r z s n                                    ≡⟨⟩
      nr₂ p r · n + nr₃ r z s                         ≤⟨ +-monotone (·-monotoneˡ nr₂≤) (nr₃-suc r) ⟩
      (p + r · nr₂ p r) · n + s + r · nr₃ r z s       ≡⟨ +-congʳ (·-distribʳ-+ _ _ _) ⟩
      (p · n + (r · nr₂ p r) · n) + s + r · nr₃ r z s ≡⟨ +-congʳ (+-congˡ (·-assoc _ _ _)) ⟩
      (p · n + r · nr₂ p r · n) + s + r · nr₃ r z s   ≡⟨ +-assoc _ _ _ ⟩
      p · n + r · nr₂ p r · n + s + r · nr₃ r z s     ≡˘⟨ +-congˡ (+-assoc _ _ _) ⟩
      p · n + (r · nr₂ p r · n + s) + r · nr₃ r z s   ≡⟨ +-congˡ (+-congʳ (+-comm _ _)) ⟩
      p · n + (s + r · nr₂ p r · n) + r · nr₃ r z s   ≡⟨ +-congˡ (+-assoc _ _ _) ⟩
      p · n + s + r · nr₂ p r · n + r · nr₃ r z s     ≡˘⟨ +-assoc _ _ _ ⟩
      (p · n + s) + r · nr₂ p r · n + r · nr₃ r z s   ≡˘⟨ +-cong (+-comm _ _) (·-distribˡ-+ _ _ _) ⟩
      (s + p · n) + r · (nr₂ p r · n + nr₃ r z s)     ≡⟨ +-assoc _ _ _ ⟩
      s + p · n + r · (nr₂ p r · n + nr₃ r z s)       ≡⟨⟩
      s + p · n + r · nr p r z s n ∎
      where
      open Tools.Reasoning.PartialOrder ≤-poset

opaque

  unfolding nr₂→has-nr

  -- Given a function nr₂, satisfying some properties, the nr function given by
  -- nr₂→has-nr is factoring.

  nr₂→has-factoring-nr :
    (nr₂ : Op₂ ℕ⊎∞) →
    (nr₂≢𝟘 : ∀ {p r} → nr₂ p r ≢ ⌞ 0 ⌟) →
    (nr₂≤ : ∀ {p r} → nr₂ p r ≤ p + r · nr₂ p r) →
    Is-factoring-nr (nr₂→has-nr nr₂ nr₂≢𝟘 nr₂≤)
  nr₂→has-factoring-nr nr₂ nr₂≢𝟘 nr₂≤ = record
    { nr₂ = nr₂
    ; nr₂≢𝟘 = nr₂≢𝟘
    ; nr-factoring = λ {p} {r} {z} {s} {n} → begin
        nr p r z s n                              ≡⟨⟩
        nr₂ p r · n + nr₃ r z s                   ≡˘⟨ +-congˡ (+-identityˡ _) ⟩
        nr₂ p r · n + ⌞ 0 ⌟ + nr₃ r z s           ≡˘⟨ +-congˡ (+-congʳ (·-zeroʳ _)) ⟩
        nr₂ p r · n + nr₂ p r · ⌞ 0 ⌟ + nr₃ r z s ≡⟨⟩
        nr₂ p r · n + nr p r z s ⌞ 0 ⌟            ∎
    }
    where
    open Tools.Reasoning.PropositionalEquality
    open Modality ℕ⊎∞-modality
      using (+-congʳ; +-congˡ; +-identityˡ; ·-zeroʳ)
    open Has-nr (nr₂→has-nr nr₂ nr₂≢𝟘 nr₂≤)

instance

  -- An instance of Has-nr using nr₂ to define nr₃.

  ℕ⊎∞-has-nr : Has-nr ℕ⊎∞-modality
  ℕ⊎∞-has-nr =
   nr₂→has-nr (λ p r → nr₃ r ⌞ 1 ⌟ p)
     (λ {_} {r} nr₃≡𝟘 → case nr₃-positive r nr₃≡𝟘 of λ ())
     (nr₃-suc _)

instance

  -- The Has-nr instance above has a factoring nr function

  ℕ⊎∞-has-factoring-nr : Is-factoring-nr ℕ⊎∞-has-nr
  ℕ⊎∞-has-factoring-nr =
    nr₂→has-factoring-nr (λ p r → nr₃ r ⌞ 1 ⌟ p)
     (λ {_} {r} nr₃≡𝟘 → case nr₃-positive r nr₃≡𝟘 of λ ())
     (nr₃-suc _)


-- The nr function of the instance above
-- nr p r z s n = nr₃ r ⌞ 1 ⌟ p · n + nr₃ r z s

nr : (p r z s n : ℕ⊎∞) → ℕ⊎∞
nr = Has-nr.nr ℕ⊎∞-has-nr

opaque
  unfolding nr₂→has-nr

  -- Unfolding of nr

  nr≡ : ∀ {p r z s n} → nr p r z s n ≡ nr₃ r ⌞ 1 ⌟ p · n + nr₃ r z s
  nr≡ = refl

opaque

  -- An inequality for the nr₂ function used to define nr.

  nr₂p𝟘≤𝟙 : ∀ {p} → nr₃ ⌞ 0 ⌟ ⌞ 1 ⌟ p ≤ ⌞ 1 ⌟
  nr₂p𝟘≤𝟙 = ∧-decreasingˡ _ _
    where
    open Graded.Modality.Properties.Meet ℕ⊎∞-modality

opaque

  -- An inequality for the nr₂ function used to define nr.

  nr₂𝟘𝟙≤𝟙 : nr₃ ⌞ 1 ⌟ ⌞ 1 ⌟ ⌞ 0 ⌟ ≤ ⌞ 1 ⌟
  nr₂𝟘𝟙≤𝟙 = ≤-refl
    where
    open Graded.Modality.Properties.PartialOrder ℕ⊎∞-modality

open Graded.Modality.Properties.Natrec ℕ⊎∞-modality

opaque
  unfolding nr₂→has-nr

  -- With the the flat order, there is no greatest factoring nr function.

  no-greatest-nrₑ : T (not total) → No-greatest-factoring-nr
  no-greatest-nrₑ not-total = lemma _ refl not-total
    where
    nr₂ : (p r : ℕ⊎∞) → ℕ⊎∞
    nr₂ p r = nr₃ r ⌞ 2 ⌟ p
    nr₂≢𝟘 : ∀ {p r} → nr₂ p r ≢ ⌞ 0 ⌟
    nr₂≢𝟘 {r} nr₂≡𝟘 = case nr₃-positive r nr₂≡𝟘 of λ ()
    lemma : ∀ b → total ≡ b → T (not b) → No-greatest-factoring-nr
    lemma true _ ()
    lemma false refl _ = record
      { has-nr₁ = ℕ⊎∞-has-nr
      ; has-nr₂ = nr₂→has-nr nr₂ (λ {p} {r} → nr₂≢𝟘 {p} {r}) (λ {p} {r} → nr₃-suc r)
      ; factoring₁ = ℕ⊎∞-has-factoring-nr
      ; factoring₂ = nr₂→has-factoring-nr nr₂ (λ {p} {r} → nr₂≢𝟘 {p} {r}) (λ {p} {r} → nr₃-suc r)
      ; p₀ = ⌞ 0 ⌟
      ; r₀ = ⌞ 1 ⌟
      ; z₀ = ⌞ 0 ⌟
      ; s₀ = ⌞ 0 ⌟
      ; n₀ = ⌞ 1 ⌟
      ; nr₁≢nr₂ = λ ()
      ; nr≰ = λ { ⌞ 0 ⌟ () _ ; ⌞ 1 ⌟ _ () ; ⌞ 2+ _ ⌟ () _ ; ∞ () _}
      }

opaque
  unfolding nr₂→has-nr

  -- The nr function returns results that are at least as large as those
  -- of any other factoring nr function with nr₂ p ⌞ 0 ⌟ ≤ ⌞ 1 ⌟ and
  -- nr₂ ⌞ 0 ⌟ ⌞ 1 ⌟ ≤ ⌞ 1 ⌟ for ℕ⊎∞-modality.
  -- (Note that the nr₂ function used by nr has these properties,
  -- see nr₂p𝟘≤𝟙 and nr₂𝟘𝟙≤𝟙 above)

  nr-greatest-factoring :
    (has-nr : Has-nr ℕ⊎∞-modality)
    (is-factoring-nr : Is-factoring-nr has-nr)
    (nr₂p𝟘≤𝟙 : ∀ {p} → Is-factoring-nr.nr₂ is-factoring-nr p ⌞ 0 ⌟ ≤ ⌞ 1 ⌟)
    (nr₂𝟘𝟙≤𝟙 : Is-factoring-nr.nr₂ is-factoring-nr ⌞ 0 ⌟ ⌞ 1 ⌟ ≤ ⌞ 1 ⌟) →
    ∀ p r z s n → Has-nr.nr has-nr p r z s n ≤ nr p r z s n
  nr-greatest-factoring has-nr is-factoring-nr nr₂p𝟘≤𝟙 nr₂𝟘𝟙≤𝟙 = λ where
      p r ∞ s n → lemma $ begin
        nr′ p r ∞ s n                ≡⟨ nr-factoring ⟩
        nr₂′ p r · n + nr′ p r ∞ s 𝟘 ≤⟨ +-monotoneʳ (nr-zero ≤-refl) ⟩
        nr₂′ p r · n + ∞             ≡⟨ +-zeroʳ (nr₂′ p r · n) ⟩
        ∞                            ∎
      p r z ∞ n → lemma nr-suc
      p r z s ∞ → lemma $ begin
        nr′ p r z s ∞                ≡⟨ nr-factoring ⟩
        nr₂′ p r · ∞ + nr′ p r z s 𝟘 ≡⟨ +-congʳ (≢𝟘·∞ nr₂≢𝟘) ⟩
        ∞ + nr′ p r z s 𝟘            ≡⟨⟩
        ∞                            ∎
      p r ⌞ 0 ⌟ ⌞ 0 ⌟ ⌞ 0 ⌟ → begin
        nr′ p r 𝟘 𝟘 𝟘 ≡⟨ nr-𝟘 ⦃ has-nr ⦄ ⟩
        𝟘             ≡˘⟨ nr-𝟘 {p} {r} ⟩
        nr p r 𝟘 𝟘 𝟘  ∎
      ∞ r z s ⌞ 1+ n ⌟ → lemma $ begin
        nr′ ∞ r z s ⌞ 1+ n ⌟             ≤⟨ nr-suc ⟩
        s + ∞ + r · nr′ ∞ r z s ⌞ 1+ n ⌟ ≡⟨⟩
        s + ∞                            ≡⟨ +-zeroʳ s ⟩
        ∞                                ∎
      p ∞ ⌞ 0 ⌟ ⌞ 0 ⌟ ⌞ 1+ n ⌟ → nr′p∞≤ λ ()
      p ∞ ⌞ 0 ⌟ ⌞ 1+ s ⌟ n → nr′p∞≤ λ ()
      p ∞ ⌞ 1+ x ⌟ s n → nr′p∞≤ λ ()
      p ⌞ 0 ⌟ z s n → begin
        nr′ p 𝟘 z s n ≡⟨ nr-factoring ⟩
        nr₂′ p 𝟘 · n + nr′ p 𝟘 z s 𝟘 ≤⟨ +-monotoneʳ (∧-greatest-lower-bound (nr-zero ≤-refl)
                                          (≤-trans nr-suc′ (≤-reflexive (+-identityʳ s)))) ⟩
        nr₂′ p 𝟘 · n + (z ∧ s)        ≤⟨ +-monotoneˡ (·-monotoneˡ (∧-greatest-lower-bound nr₂p𝟘≤𝟙 nr₂p𝟘≤p)) ⟩
        (𝟙 ∧ p) · n + (z ∧ s)         ≡⟨⟩
        nr p 𝟘 z s n                  ∎
      p ⌞ 1 ⌟ z ⌞ 1+ s ⌟ n → lemma ∘→ ≤-reflexive ∘→ x≤y+x→x≡∞ (≢𝟘+ (λ ())) $ begin
        nr′ p 𝟙 z ⌞ 1+ s ⌟ n                          ≤⟨ nr-suc ⟩
        ⌞ 1+ s ⌟ + p · n + 𝟙 · nr′ p 𝟙 z ⌞ 1+ s ⌟ n   ≡˘⟨ +-assoc ⌞ 1+ s ⌟ (p · n) _ ⟩
        (⌞ 1+ s ⌟ + p · n) + 𝟙 · nr′ p 𝟙 z ⌞ 1+ s ⌟ n ≡⟨ +-congˡ (·-identityˡ _) ⟩
        (⌞ 1+ s ⌟ + p · n) + nr′ p 𝟙 z ⌞ 1+ s ⌟ n     ∎
      ⌞ 1+ p ⌟ ⌞ 1 ⌟ z s ⌞ 1+ n ⌟ → lemma ∘→ ≤-reflexive ∘→ x≤y+x→x≡∞ (+≢𝟘 (λ ())) $ begin
        nr′ ⌞ 1+ p ⌟ 𝟙 z s ⌞ 1+ n ⌟                               ≤⟨ nr-suc ⟩
        s + ⌞ 1+ p N.* 1+ n ⌟ + 𝟙 · nr′ ⌞ 1+ p ⌟ 𝟙 z s ⌞ 1+ n ⌟   ≡˘⟨ +-assoc s _ _ ⟩
        (s + ⌞ 1+ p N.* 1+ n ⌟) + 𝟙 · nr′ ⌞ 1+ p ⌟ 𝟙 z s ⌞ 1+ n ⌟ ≡⟨ +-congˡ (·-identityˡ _) ⟩
        (s + ⌞ 1+ p N.* 1+ n ⌟) + nr′ ⌞ 1+ p ⌟ 𝟙 z s ⌞ 1+ n ⌟     ∎
      p ⌞ 1 ⌟ z ⌞ 0 ⌟ ⌞ 0 ⌟ → begin
        nr′ p 𝟙 z 𝟘 𝟘           ≤⟨ nr-zero ≤-refl ⟩
        z                       ≡˘⟨ +-identityʳ z ⟩
        z + 𝟘                   ≡˘⟨ +-identityˡ (z + 𝟘) ⟩
        𝟘 + z + 𝟘               ≡˘⟨ +-congʳ (·-zeroʳ _) ⟩
        (𝟙 + ∞ · p) · 𝟘 + z + 𝟘 ≡⟨⟩
        nr p 𝟙 z 𝟘 𝟘            ∎
      ⌞ 0 ⌟ ⌞ 1 ⌟ z ⌞ 0 ⌟ n → begin
        nr′ 𝟘 𝟙 z 𝟘 n                 ≡⟨ nr-factoring ⟩
        nr₂′ 𝟘 𝟙 · n + nr′ 𝟘 𝟙 z 𝟘 𝟘 ≤⟨ +-monotone (·-monotoneˡ nr₂𝟘𝟙≤𝟙) (nr-zero ≤-refl) ⟩
        𝟙 · n + z                     ≡˘⟨ +-congˡ (+-identityʳ z) ⟩
        𝟙 · n + z + 𝟘                 ≡⟨⟩
        nr 𝟘 𝟙 z 𝟘 n                  ∎
      p ⌞ 2+ r ⌟ ⌞ 0 ⌟ ⌞ 0 ⌟ ⌞ 1+ n ⌟ → (lemma ∘→ ≤-reflexive ∘→ nr′p2+r≡∞) λ ()
      p ⌞ 2+ r ⌟ ⌞ 0 ⌟ ⌞ 1+ s ⌟ n → (lemma ∘→ ≤-reflexive ∘→ nr′p2+r≡∞) λ ()
      p ⌞ 2+ r ⌟ ⌞ 1+ z ⌟ s n → (lemma ∘→ ≤-reflexive ∘→ nr′p2+r≡∞) λ ()
    where
    𝟘 𝟙 : ℕ⊎∞
    𝟘 = ⌞ 0 ⌟
    𝟙 = ⌞ 1 ⌟
    open Has-nr has-nr
      renaming (nr to nr′; nr-positive to nr′-positive)
    open Is-factoring-nr is-factoring-nr
      renaming (nr₂ to nr₂′)
    open Graded.Modality.Properties.Addition ℕ⊎∞-modality
    open Graded.Modality.Properties.Meet ℕ⊎∞-modality
    open Graded.Modality.Properties.Multiplication ℕ⊎∞-modality
    open Graded.Modality.Properties.PartialOrder ℕ⊎∞-modality
    open Modality ℕ⊎∞-modality
      hiding (𝟘; 𝟙; _+_; _·_; _∧_; _≤_)
    open Tools.Reasoning.PartialOrder ≤-poset
    lemma : ∀ {p r z s n} → nr′ p r z s n ≤ ∞ → nr′ p r z s n ≤ nr p r z s n
    lemma {p} {r} {z} {s} {n} nr′≤∞ =
      ≤-trans nr′≤∞ (∞≤ (nr p r z s n))
    nr-suc′ : ∀ {p r z s} → nr′ p r z s 𝟘 ≤ s + r · nr′ p r z s 𝟘
    nr-suc′ {p} {r} {z} {s} = begin
      nr′ p r z s 𝟘                 ≤⟨ nr-suc ⟩
      s + p · 𝟘 + r · nr′ p r z s 𝟘 ≡⟨ +-congˡ (+-congʳ (·-zeroʳ p)) ⟩
      s + 𝟘 + r · nr′ p r z s 𝟘     ≡⟨ +-congˡ (+-identityˡ _) ⟩
      s + r · nr′ p r z s 𝟘         ∎
    nr′p∞≤ : ∀ {z s n p} → ¬ (z ≡ 𝟘 × s ≡ 𝟘 × n ≡ 𝟘) → nr′ p ∞ z s n ≤ nr p ω z s n
    nr′p∞≤ {z} {s} {n} {p} ≢𝟘 = lemma $ begin
      nr′ p ∞ z s n                 ≤⟨ nr-suc ⟩
      s + p · n + ∞ · nr′ p ∞ z s n ≡⟨ +-congˡ {s} (+-congˡ (∞·≢𝟘 (≢𝟘 ∘→ nr′-positive))) ⟩
      s + p · n + ∞                 ≡⟨ +-congˡ (+-zeroʳ _) ⟩
      s + ∞                         ≡⟨ +-zeroʳ _ ⟩
      ∞                             ∎
    x≤y+x→x≡∞ : ∀ {x y} → y ≢ 𝟘 → x ≤ y + x → x ≡ ∞
    x≤y+x→x≡∞ {x} {⌞ 0 ⌟} y≢𝟘 x≤y+x = ⊥-elim (y≢𝟘 refl)
    x≤y+x→x≡∞ {(∞)} {y} y≢𝟘 x≤y+x = refl
    x≤y+x→x≡∞ {⌞ 1+ x ⌟} {⌞ 1+ y ⌟} y≢𝟘 x≤y+x =
      case ⌞⌟-antitone⁻¹ {m = 1+ (y N.+ 1+ x)} x≤y+x of λ where
        (N.s≤s ≤x) → ⊥-elim (N.m+1+n≰m x
          (N.≤-trans (N.≤-reflexive (trans (N.+-comm x (1+ y)) (sym (N.+-suc y x)))) ≤x))
    x≤y+x→x≡∞ {⌞ x ⌟} {⌞ 1+ y ⌟} _ x≤y+x =
      ⊥-elim (N.m+1+n≰m x (N.≤-trans (N.≤-reflexive (N.+-comm x (1+ y))) (⌞⌟-antitone⁻¹ x≤y+x)))
    x≤y+x→x≡∞ {⌞ x ⌟} {(∞)} _ x≤∞ = ⊥-elim (≰∞ x≤∞)
    ≢𝟘+ : ∀ {x y} → x ≢ 𝟘 → x + y ≢ 𝟘
    ≢𝟘+ {x = ⌞ 0 ⌟}                x≢𝟘 _  = x≢𝟘 refl
    ≢𝟘+ {x = ⌞ 1+ _ ⌟} {y = ⌞ _ ⌟} _   ()
    ≢𝟘+ {x = ⌞ 1+ _ ⌟} {y = ∞}     _   ()
    ≢𝟘+ {x = ∞}                    _   ()
    +≢𝟘 : ∀ {x y} → y ≢ 𝟘 → x + y ≢ 𝟘
    +≢𝟘 y≢𝟘 x+y≡𝟘 = ≢𝟘+ y≢𝟘 (trans (+-comm _ _) x+y≡𝟘)
    nr₂p𝟘≤p : ∀ {p} → nr₂′ p 𝟘 ≤ p
    nr₂p𝟘≤p {p} = begin
      nr₂′ p 𝟘                       ≡˘⟨ ·-identityʳ _ ⟩
      nr₂′ p 𝟘 · 𝟙                   ≡˘⟨ +-identityʳ _ ⟩
      nr₂′ p 𝟘 · 𝟙 + 𝟘               ≡˘⟨ +-congˡ (nr-𝟘 ⦃ has-nr ⦄) ⟩
      nr₂′ p 𝟘 · 𝟙 + nr′ p 𝟘 𝟘 𝟘 𝟘  ≡˘⟨ nr-factoring ⟩
      nr′ p 𝟘 𝟘 𝟘 𝟙                 ≤⟨ nr-suc ⟩
      𝟘 + p · 𝟙 + 𝟘                 ≡⟨ +-identityˡ _ ⟩
      p · 𝟙 + 𝟘                     ≡⟨ +-identityʳ _ ⟩
      p · 𝟙                         ≡⟨ ·-identityʳ _ ⟩
      p                             ∎
    q≤p+rq→q≡∞ : ∀ {q p r} → q ≢ 𝟘 → q ≤ p + ⌞ 2+ r ⌟ · q → q ≡ ∞
    q≤p+rq→q≡∞ {⌞ Nat.zero ⌟} q≢𝟘 _ = ⊥-elim (q≢𝟘 refl)
    q≤p+rq→q≡∞ {⌞ 1+ q ⌟} {⌞ p ⌟} {(r)} q≢𝟘 q≤ =
      case N.≤-trans (N.≤-reflexive (N.+-comm _ p)) (⌞⌟-antitone⁻¹ q≤) of λ {
        (N.s≤s q+x≤q) →
      ⊥-elim (N.m+1+n≰m q (N.≤-trans (N.≤-reflexive (sym (N.+-assoc q _ p))) q+x≤q)) }
    q≤p+rq→q≡∞ {⌞ 1+ x ⌟} {(∞)} {(r)} q≢𝟘 q≤ = ⊥-elim (≰∞ q≤)
    q≤p+rq→q≡∞ {(∞)} _ _ = refl
    nr′p2+r≡∞ : ∀ {z s n p r} → ¬ (z ≡ 𝟘 × s ≡ 𝟘 × n ≡ 𝟘) → nr′ p ⌞ 2+ r ⌟ z s n ≡ ∞
    nr′p2+r≡∞ {z} {s} {n} {p} {r} ≢𝟘 = q≤p+rq→q≡∞ (≢𝟘 ∘→ nr′-positive) $ begin
      nr′ p ⌞ 2+ r ⌟ z s n                          ≤⟨ nr-suc ⟩
      s + p · n + ⌞ 2+ r ⌟ · nr′ p ⌞ 2+ r ⌟ z s n   ≡˘⟨ +-assoc _ _ _ ⟩
      (s + p · n) + ⌞ 2+ r ⌟ · nr′ p ⌞ 2+ r ⌟ z s n ∎

opaque

  -- The nr function returns results that are at least as large as those
  -- of any other factoring nr function for ℕ⊎∞-modality
  -- when the total order is used.

  nr-greatest-factoringₐ :
    T total →
    (has-nr : Has-nr ℕ⊎∞-modality)
    (has-factoring-nr : Is-factoring-nr has-nr) →
    ∀ p r z s n → Has-nr.nr has-nr p r z s n ≤ nr p r z s n
  nr-greatest-factoringₐ x has-nr is-factoring-nr = lemma _ refl x
    where
    open Is-factoring-nr is-factoring-nr
    lemma : ∀ b → b ≡ total → T b →
            ∀ p r z s n → Has-nr.nr has-nr p r z s n ≤ nr p r z s n
    lemma false _    ()
    lemma true refl _ =
      nr-greatest-factoring has-nr is-factoring-nr
        (≢𝟘→≤ᵗ𝟙 nr₂≢𝟘) (≢𝟘→≤ᵗ𝟙 nr₂≢𝟘)

------------------------------------------------------------------------
-- Instances of Full-reduction-assumptions

module _ {𝟘ᵐ-allowed : Bool} where

  open Graded.Mode.Instances.Zero-one.Variant ℕ⊎∞-modality

  private

    variant : Mode-variant
    variant = record
      { 𝟘ᵐ-allowed = 𝟘ᵐ-allowed
      ; 𝟘-well-behaved = λ _ → ℕ⊎∞-has-well-behaved-zero
      }

  open Graded.Mode.Instances.Zero-one   variant
    hiding (⌞_⌟)
  open Definition.Typed.Restrictions    ℕ⊎∞-modality
  open Graded.Usage.Restrictions        ℕ⊎∞-modality Zero-one-isMode
  open Graded.FullReduction.Assumptions variant

  private variable
    TRs : Type-restrictions
    URs : Usage-restrictions

  -- Instances of Type-restrictions ℕ⊎∞-modality and
  -- Usage-restrictions ℕ⊎∞-modality are suitable for the full
  -- reduction theorem if
  -- * whenever Σˢ-allowed m n holds, then m is ⌞ 1 ⌟, or the total
  --   ordering is used, m is ⌞ 0 ⌟, and 𝟘ᵐ is allowed, and
  -- * if the "flat" ordering is used, then strong unit types are
  --   allowed to be used as sinks (if such types are allowed), and
  --   η-equality is not allowed for weak unit types (if such types are
  --   allowed).

  Suitable-for-full-reduction :
    Type-restrictions →
    Usage-restrictions → Set
  Suitable-for-full-reduction TRs URs =
    (∀ m n → Σˢ-allowed m n →
     m ≡ ⌞ 1 ⌟ ⊎ T total × m ≡ ⌞ 0 ⌟ × T 𝟘ᵐ-allowed) ×
    (¬ T total →
     (Unitˢ-allowed → Starˢ-sink) ×
     (Unitʷ-allowed → ¬ Unitʷ-η))
    where
    open Type-restrictions TRs
    open Usage-restrictions URs

  -- Given instances of Type-restrictions ℕ⊎∞-modality and
  -- Usage-restrictions ℕ⊎∞-modality one can create
  -- "suitable" instances.

  suitable-for-full-reduction :
    Type-restrictions →
    Usage-restrictions →
    ∃₂ Suitable-for-full-reduction
  suitable-for-full-reduction TRs URs =
      record TRs
        { Unit-allowed = λ s →
            Unit-allowed s ×
            (¬ T total → s ≡ 𝕨 → ¬ Unitʷ-η)
        ; ΠΣ-allowed = λ b m n →
            ΠΣ-allowed b m n ×
            (b ≡ BMΣ 𝕤 → m ≡ ⌞ 1 ⌟ ⊎ T total × m ≡ ⌞ 0 ⌟ × T 𝟘ᵐ-allowed)
        ; []-cong-allowed = λ s →
            []-cong-allowed s ×
            (T total → T 𝟘ᵐ-allowed) ×
            (¬ T total → s ≢ 𝕤 × (s ≡ 𝕨 → ¬ Unitʷ-η))
        ; []-cong→Erased = λ (ok , hyp₁ , hyp₂) →
            let ok₁ , ok₂ = []-cong→Erased ok in
              (ok₁ , proj₂ ∘→ hyp₂)
            , ok₂
            , (case PE.singleton total of λ where
                 (true  , refl) _    → inj₂ (_ , refl , hyp₁ _)
                 (false , refl) refl → ⊥-elim (hyp₂ idᶠ .proj₁ refl))
        ; []-cong→¬Trivial = λ _ ()
        }
    , record URs { starˢ-sink = not total ∨ starˢ-sink }
    , (λ _ _ (_ , hyp) → hyp refl)
    , (λ not-total →
           (λ (_ , hyp) → case PE.singleton total of λ where
              (true  , refl) → ⊥-elim (not-total _)
              (false , refl) → _)
         , (λ (_ , hyp) → hyp not-total refl))
    where
    open Type-restrictions TRs
    open Usage-restrictions URs

  -- The full reduction assumptions hold for ℕ⊎∞-modality and
  -- any "suitable" instance of Type-restrictions.

  full-reduction-assumptions :
    Suitable-for-full-reduction TRs URs →
    Full-reduction-assumptions TRs URs
  full-reduction-assumptions (hyp₁ , hyp₂) =
    case PE.singleton total of λ where
      (true , refl) → record
        { sink⊎𝟙≤𝟘 = λ _ _ → inj₂ refl
        ; ≡𝟙⊎𝟙≤𝟘   = ⊎.map idᶠ (Σ.map idᶠ (_, refl) ∘→ proj₂) ∘→ hyp₁ _ _
        }
      (false , refl) → record
        { sink⊎𝟙≤𝟘 = λ where
            {s = 𝕤} ok _         → inj₁ (refl , hyp₂ idᶠ .proj₁ ok)
            {s = 𝕨} _  (inj₁ ())
            {s = 𝕨} ok (inj₂ η)  → ⊥-elim (hyp₂ idᶠ .proj₂ ok η)
        ; ≡𝟙⊎𝟙≤𝟘 = ⊎.map idᶠ (⊥-elim ∘→ proj₁) ∘→ hyp₁ _ _
        }

  -- Type and usage restrictions that satisfy the full reduction
  -- assumptions are "suitable".

  full-reduction-assumptions-suitable :
    Full-reduction-assumptions TRs URs →
    Suitable-for-full-reduction TRs URs
  full-reduction-assumptions-suitable as =
    case PE.singleton total of λ where
      (true , refl) →
          (λ _ _ → ⊎.map idᶠ ((_ ,_) ∘→ Σ.map idᶠ proj₁) ∘→ ≡𝟙⊎𝟙≤𝟘)
        , ⊥-elim ∘→ (_$ _)
      (false , refl) →
          (λ _ _ → inj₁ ∘→ ⊎.[ idᶠ , (λ { (_ , _ , ()) }) ] ∘→ ≡𝟙⊎𝟙≤𝟘)
        , (λ _ →
               ⊎.[ proj₂ , (λ ()) ] ∘→ flip sink⊎𝟙≤𝟘 (inj₁ refl)
             , (λ ok η →
                  ⊎.[ (λ { (() , _) }) , (λ ()) ] (sink⊎𝟙≤𝟘 ok (inj₂ η))))
    where
    open Full-reduction-assumptions _ _ as

------------------------------------------------------------------------
-- Subtraction

open Graded.Modality.Properties.Subtraction ℕ⊎∞-modality

opaque

  -- Subtraction of ⌞ m ⌟ by ∞ is not possible

  ⌞m⌟-∞≰ : ∀ {m p} → ⌞ m ⌟ - ∞ ≤ p → ⊥
  ⌞m⌟-∞≰ {p = ⌞ m ⌟} x = ≰∞ x
  ⌞m⌟-∞≰ {p = ∞} x = ≰∞ x

opaque

  -- Subtraction of ⌞ m ⌟ by ⌞ n ⌟ is only possible if n ≤ m

  ⌞m⌟-⌞n⌟≤ : ∀ {m n} → ⌞ m ⌟ - ⌞ n ⌟ ≤ o → n N.≤ m
  ⌞m⌟-⌞n⌟≤ {⌞ o ⌟} {m} {n} m≤o+n = lemma total refl
    where
    lemma : ∀ b → b ≡ total → n N.≤ m
    lemma false refl with m N.≟ o N.+ n
    … | yes refl = N.m≤n+m n o
    … | no _ = ⊥-elim (∞≢⌞m⌟ (sym m≤o+n))
    lemma true refl =
      N.m+n≤o⇒n≤o _ (N.m⊔n≡m⇒n≤m (sym (⌞⌟-injective m≤o+n)))
  ⌞m⌟-⌞n⌟≤ {(∞)} x = ⊥-elim (≰∞ x)

opaque

  -- An inversion lemma for subtraction

  ⌞m⌟-q≤r-inv : ∀ {m q r} → ⌞ m ⌟ - q ≤ r →
                ∃ λ n → q ≡ ⌞ n ⌟ × n N.≤ m
  ⌞m⌟-q≤r-inv {q = ⌞ n ⌟} m-q≤r = n , refl , ⌞m⌟-⌞n⌟≤ m-q≤r
  ⌞m⌟-q≤r-inv {q = ∞} m-q≤r = ⊥-elim (⌞m⌟-∞≰ m-q≤r)

opaque

  -- Subtraction for natural numbers is supported if the first argument
  -- is greater than the second (in the natural number order)

  m-n≡ : ∀ m n → (n≤m : n N.≤ m) → ⌞ m ⌟ - ⌞ n ⌟ ≡ ⌞ m N.∸ n ⌟
  m-n≡ m n n≤m = lemma total refl
    where
    lemma₁ : ∀ m n → n N.≤ m → m ≡ m N.⊔ (m N.∸ n N.+ n)
    lemma₁ m 0 n≤m
      rewrite N.+-identityʳ m = sym (N.⊔-idem m)
    lemma₁ 0 (1+ n) ()
    lemma₁ (1+ m) (1+ n) (N.s≤s n≤m)
      rewrite N.+-suc (m N.∸ n) n = cong 1+ (lemma₁ m n n≤m)

    lemma₂ : ∀ m n k → m ≡ m N.⊔ (k N.+ n) → m N.∸ n ≡ m N.∸ n N.⊔ k
    lemma₂ m 0 k x rewrite N.+-comm k 0 = x
    lemma₂ 0 (1+ n) 0 x = refl
    lemma₂ 0 (1+ n) (1+ k) ()
    lemma₂ (1+ m) (1+ n) k x rewrite N.+-suc k n =
      lemma₂ m n k (N.1+-injective x)

    lemma₃ : ∀ k → ⌞ m ⌟ ≤ᶠ ⌞ k N.+ n ⌟ → ⌞ m N.∸ n ⌟ ≤ᶠ ⌞ k ⌟
    lemma₃ k m≤ with m N.∸ n N.≟ k
    … | yes _ = refl
    … | no m-n≢k with m N.≟ k N.+ n
    … | yes refl = ⊥-elim (m-n≢k (N.m+n∸n≡m k n))
    lemma₃ k () | no _ | no _

    lemma : ∀ b → b ≡ total → ⌞ m ⌟ - ⌞ n ⌟ ≡ ⌞ m N.∸ n ⌟
    lemma false refl with m N.≟ m N.∸ n N.+ n
    … | yes _ =
      refl ,
      λ where
        ⌞ k ⌟ x  → lemma₃ k x
        ∞     ()
    … | no m≢m-n+n = ⊥-elim (m≢m-n+n (sym (N.m∸n+n≡m n≤m)))
    lemma true refl =
      cong ⌞_⌟ (lemma₁ m n n≤m) ,
      λ where
        ⌞ k ⌟ x  → cong ⌞_⌟ (lemma₂ m n k (⌞⌟-injective x))
        ∞     ()

opaque

  -- The semiring supports subtraction with
  --   ∞ - p ≡ ∞ for any p
  --   ⌞ m ⌟ - ⌞ n ⌟ ≡ ⌞ m - n ⌟ whenever n ≤ m
  -- and not defined otherwise

  supports-subtraction : Supports-subtraction
  supports-subtraction {⌞ m ⌟} {⌞ n ⌟} {⌞ k ⌟} m≤k+n =
    ⌞ m N.∸ n ⌟ , m-n≡ m n (N.m+n≤o⇒n≤o k (⌞⌟-antitone⁻¹ m≤k+n))
  supports-subtraction {(∞)}     {(n)}           m≤k+n = ∞ , ∞-p≡∞ (λ {q} → ∞≤ q) n
  supports-subtraction {(⌞ _ ⌟)} {(⌞ _ ⌟)} {(∞)} m≤k+n = ⊥-elim (≰∞ m≤k+n)
  supports-subtraction {(⌞ _ ⌟)} {(∞)} {(⌞ _ ⌟)} m≤k+n = ⊥-elim (≰∞ m≤k+n)
  supports-subtraction {(⌞ _ ⌟)} {(∞)} {(∞)}     m≤k+n = ⊥-elim (≰∞ m≤k+n)

-- An alternative definition of the subtraction relation with
--   ∞ - p ≡ ∞ for any p
--   ⌞ m ⌟ - ⌞ n ⌟ ≡ ⌞ m - n ⌟ whenever n ≤ m
-- and not defined otherwise

data _-_≡′_ : (p q r : ℕ⊎∞) → Set where
  ∞-p≡′∞ : ∀ {p} → ∞ - p ≡′ ∞
  m-n≡′m∸n : ∀ {m n} → n N.≤ m → ⌞ m ⌟ - ⌞ n ⌟ ≡′ ⌞ m N.∸ n ⌟

opaque

  -- The two subtraction relations are equivalent.

  -≡↔-≡′ : ∀ p q r → (p - q ≡ r) ⇔ (p - q ≡′ r)
  -≡↔-≡′ p q r = left p q r , right
    where
    left : ∀ p q r → p - q ≡ r → p - q ≡′ r
    left ∞ q r p-q≡r =
      case -≡-functional {q = q} p-q≡r (∞-p≡∞ (λ {q} → ∞≤ q) q) of λ {
        refl →
      ∞-p≡′∞ }
    left ⌞ m ⌟ q r p-q≡r =
      case ⌞m⌟-q≤r-inv (p-q≡r .proj₁) of λ {
        (n , refl , n≤m) →
      case -≡-functional {q = q} p-q≡r (m-n≡ m n n≤m) of λ {
        refl →
      m-n≡′m∸n n≤m }}
    right : p - q ≡′ r → p - q ≡ r
    right ∞-p≡′∞ = ∞-p≡∞ (λ {q} → ∞≤ q) q
    right (m-n≡′m∸n n≤m) = m-n≡ _ _ n≤m

------------------------------------------------------------------------
-- Greatest-lower-bounds

open Modality ℕ⊎∞-modality
  hiding (_+_; _·_; _≤_; _∧_)
open import Graded.Modality.Properties.Greatest-lower-bound ℕ⊎∞-modality
open import Graded.Modality.Properties.Multiplication ℕ⊎∞-modality
open import Graded.Modality.Properties.Addition ℕ⊎∞-modality
open import Graded.Modality.Properties.PartialOrder ℕ⊎∞-modality
open import Graded.Modality.Properties.Has-well-behaved-zero ℕ⊎∞-modality

opaque

  -- An "inversion" property for sequences where ∞ is the greatest lower bound.

  ∞-GLB-inv : (n : Nat) (pᵢ : Sequence ℕ⊎∞) → Greatest-lower-bound ∞ pᵢ →
              (∀ i → ⌞ n ⌟ ≤ pᵢ i) → ⊥
  ∞-GLB-inv n pᵢ ∞-GLB n≤ = ≰∞ (∞-GLB .proj₂ ⌞ n ⌟ n≤)

opaque

  -- An "inversion" property for sequences where ⌞ 1+ p ⌟ is the greatest lower bound.

  1+-GLB-inv :
    ∀ {p} →
    (pᵢ : Sequence ℕ⊎∞) → Greatest-lower-bound ⌞ 1+ p ⌟ pᵢ →
    ((∀ i → pᵢ i ≡ 𝟘) → ⊥) × (∀ i → pᵢ i ≢ ∞)
  1+-GLB-inv pᵢ 1+p-GLB =
    (λ pᵢ≡𝟘 → case 𝟘≮ (1+p-GLB .proj₂ 𝟘 λ i → ≤-reflexive (sym (pᵢ≡𝟘 i))) of λ ()) ,
    (λ i pᵢ≡∞ → ≰∞ (≤-trans (1+p-GLB .proj₁ i) (≤-reflexive pᵢ≡∞)))

opaque

  -- An "inversion" property for sequences where ⌞ p ⌟ is the greatest lower bound.

  ⌞⌟-GLB-inv :
    ∀ {p} →
    (pᵢ : Sequence ℕ⊎∞) → Greatest-lower-bound ⌞ p ⌟ pᵢ →
    ∀ i → ∃ λ q → pᵢ i ≡ ⌞ q ⌟
  ⌞⌟-GLB-inv pᵢ glb i = lemma (pᵢ i) refl
    where
    lemma : ∀ r → r ≡ pᵢ i → ∃ λ q → r ≡ ⌞ q ⌟
    lemma ⌞ x ⌟ eq = x , refl
    lemma ∞ eq = ⊥-elim (≰∞ (≤-trans (glb .proj₁ i) (≤-reflexive (sym eq))))

opaque

  -- A variant of the above

  ⌞⌟-GLB-inv′ :
    ∀ {p} → T total →
    (pᵢ : Sequence ℕ⊎∞) → Greatest-lower-bound ⌞ p ⌟ pᵢ →
    Σ (Sequence Nat) λ nᵢ → (∀ i → ⌞ nᵢ i ⌟ ≡ pᵢ i) ×
    (∀ i → nᵢ i N.≤ p) ×
    (∀ m → (∀ i → nᵢ i N.≤ m) → p N.≤ m)
  ⌞⌟-GLB-inv′ {p} x pᵢ p-GLB =
    let nᵢ = λ i → ⌞⌟-GLB-inv pᵢ p-GLB i .proj₁
        nᵢ≡ = λ i → sym (⌞⌟-GLB-inv pᵢ p-GLB i .proj₂)
    in  nᵢ , nᵢ≡
           , (λ i → ⌞⌟-antitone⁻¹ (≤-trans (p-GLB .proj₁ i)
                (≤-reflexive (sym (nᵢ≡ i)))))
           , λ m m≤ → ⌞⌟-antitone⁻¹ (p-GLB .proj₂ ⌞ m ⌟ λ i →
               ≤-trans (⌞⌟-antitone x (m≤ i)) (≤-reflexive (nᵢ≡ i)))

private

  opaque

    nrᵢ+-∞-GLB : ∀ {r z s} i →
      nrᵢ r z s i ≡ ∞ →
      Greatest-lower-bound ∞ (nrᵢ r z s)
    nrᵢ+-∞-GLB {r} {z} {s} i nrᵢ≡∞ =
      (λ i → ∞≤ (nrᵢ r z s i)) , λ q q≤ → ≤-trans (q≤ i) (≤-reflexive nrᵢ≡∞)

  opaque

    1+n≤ : ∀ {n} m → n ≢ 0 → 1+ n N.≤ n N.+ (n N.+ m N.* n)
    1+n≤ {n} m n≢0 = begin
      1 N.+ n               ≤⟨ N.+-mono-≤ (N.1≤n n≢0) N.≤-refl ⟩
      n N.+ n               ≡˘⟨ N.+-identityʳ _ ⟩
      n N.+ n N.+ 0         ≤⟨ N.+-mono-≤ N.≤-refl N.z≤n ⟩
      n N.+ n N.+ m N.* n   ≡⟨ N.+-assoc n n (m N.* n) ⟩
      n N.+ (n N.+ m N.* n) ∎
      where
      open N.≤-Reasoning

opaque

  -- The greatest lower bound of nrᵢ r z s is given by nr₃ r z s

  nr₃-GLB : ∀ r z s → Greatest-lower-bound (nr₃ r z s) (nrᵢ r z s)
  nr₃-GLB r ⌞ 0 ⌟ ⌞ 0 ⌟ =
    GLB-cong (sym (nr₃-𝟘 r)) (λ i → sym (nrᵢ-𝟘 i)) GLB-const′
  nr₃-GLB ⌞ 0 ⌟ z s = nrᵢ-𝟘-GLB
  nr₃-GLB ⌞ 1+ 0 ⌟ z ⌞ 0 ⌟ =
    GLB-cong (sym (+-identityʳ z)) lemma GLB-const′
    where
    lemma : ∀ i → z ≡ nrᵢ ⌞ 1 ⌟ z ⌞ 0 ⌟ i
    lemma 0 = refl
    lemma (1+ i) = sym (trans (+-identityˡ _) (trans (·-identityˡ _) (sym (lemma i))))
  nr₃-GLB ⌞ 1+ 0 ⌟ ∞ s =
    nrᵢ+-∞-GLB 0 refl
  nr₃-GLB ⌞ 1+ 0 ⌟ z ∞ =
    GLB-congʳ (+-comm ∞ z) (nrᵢ+-∞-GLB {r = ⌞ 1 ⌟} {s = ∞} 1 refl)
  nr₃-GLB ⌞ 1+ 0 ⌟ ⌞ z ⌟ ⌞ 1+ s ⌟ =
    (λ i → ≤-refl) ,
    (λ { ⌞ q ⌟ q≤ →
           let n , n≡ , <n = lemma q
               q≤n = ≤-trans (q≤ (1+ q)) (≤-reflexive (sym n≡))
           in  ⊥-elim (N.n≮n n (N.≤-<-trans (⌞⌟-antitone⁻¹ q≤n) <n))
       ; ∞ q≤ → ≤-refl})
    where
    open N.≤-Reasoning
    lemma : ∀ i → ∃ λ n → ⌞ n ⌟ ≡ nrᵢ ⌞ 1 ⌟ ⌞ z ⌟ ⌞ 1+ s ⌟ (1+ i) × i N.< n
    lemma 0 = _ , sym (+-congˡ (·-identityˡ _)) , N.s≤s N.z≤n
    lemma (1+ i) =
      let n , n≡ , i<n = lemma i
      in  _ , sym (trans (+-congˡ (·-congˡ (sym n≡)))
                (+-congˡ (·-identityˡ _)))
            , (begin
                2+ i         ≤⟨ N.s≤s i<n ⟩
                1+ n         ≤⟨ N.m≤n+m (1+ n) s ⟩
                s N.+ 1+ n   ≡⟨ N.+-suc s n ⟩
                1+ (s N.+ n) ∎)
  nr₃-GLB ⌞ 2+ r ⌟ z ∞ =
    GLB-congʳ (sym (·-congˡ (+-comm z ∞)))
      (nrᵢ+-∞-GLB {r = ⌞ 2+ r ⌟} {s = ∞} 1 refl)
  nr₃-GLB ⌞ 2+ r ⌟ ∞ s =
    nrᵢ+-∞-GLB 0 refl
  nr₃-GLB ⌞ 2+ r ⌟ ⌞ z ⌟ ⌞ 1+ s ⌟ =
    GLB-congʳ (sym (·-congˡ (+-comm ⌞ z ⌟ ⌞ 1+ s ⌟)))
      ((λ i → ≤-refl) ,
      (λ { ⌞ q ⌟ q≤ →
           let n , n≡ , <n = lemma q
               q≤n = ≤-trans (q≤ (1+ q)) (≤-reflexive (sym n≡))
           in  ⊥-elim (N.n≮n n (N.≤-<-trans (⌞⌟-antitone⁻¹ q≤n) <n))
         ; ∞ q≤ → ≤-refl}))
    where
    open N.≤-Reasoning
    lemma : ∀ i → ∃ λ n → ⌞ n ⌟ ≡ nrᵢ ⌞ 2+ r ⌟ ⌞ z ⌟ ⌞ 1+ s ⌟ (1+ i) × i N.< n
    lemma 0 = _ , sym (+-congˡ ⌞⌟·⌞⌟≡⌞*⌟) , N.s≤s N.z≤n
    lemma (1+ i) =
      let n , n≡ , i<n = lemma i
      in  _ , sym (trans (+-congˡ (·-congˡ (sym n≡))) (+-congˡ ⌞⌟·⌞⌟≡⌞*⌟))
            , (begin
                2+ i                               ≤⟨ N.s≤s i<n ⟩
                1+ n                               ≤⟨ 1+n≤ r (N.m<n⇒n≢0 i<n) ⟩
                n N.+ (n N.+ r N.* n)              ≤⟨ N.m≤m+n _ (1+ s) ⟩
                n N.+ (n N.+ r N.* n) N.+ 1+ s     ≡⟨ N.+-comm _ (1+ s) ⟩
                1+ (s N.+ (n N.+ (n N.+ r N.* n))) ∎)
  nr₃-GLB ⌞ 2+ r ⌟ ⌞ 1+ z ⌟ ⌞ Nat.zero ⌟ =
    (λ i → ≤-refl) ,
    λ { ⌞ q ⌟ q≤ →
        let n , n≡ , <n = lemma q
            q≤n = ≤-trans (q≤ (1+ q)) (≤-reflexive (sym n≡))
        in  ⊥-elim (N.n≮n n (N.≤-<-trans (⌞⌟-antitone⁻¹ q≤n) <n))
      ; ∞ q≤ → ≤-refl}
    where
    open N.≤-Reasoning
    lemma : ∀ i → ∃ λ n → ⌞ n ⌟ ≡ nrᵢ ⌞ 2+ r ⌟ ⌞ 1+ z ⌟ 𝟘 (1+ i) × i N.< n
    lemma 0 = _ , refl , N.s≤s N.z≤n
    lemma (1+ i) =
      let n , n≡ , i<n = lemma i
      in  _ , sym (trans (+-identityˡ _) (trans (·-congˡ (sym n≡)) ⌞⌟·⌞⌟≡⌞*⌟))
            , (begin
                2+ i                  ≤⟨ N.s≤s i<n ⟩
                1+ n                  ≤⟨ 1+n≤ r (N.m<n⇒n≢0 i<n) ⟩
                n N.+ (n N.+ r N.* n) ∎)
  nr₃-GLB ∞ ⌞ 0 ⌟ ⌞ 1+ s ⌟ =
    nrᵢ+-∞-GLB 2 refl
  nr₃-GLB ∞ ⌞ 0 ⌟ ∞ =
    nrᵢ+-∞-GLB {r = ∞} {s = ∞} 1 refl
  nr₃-GLB ∞ ⌞ 1+ z ⌟ s =
    GLB-congʳ (sym (·-distribˡ-+ _ _ _))
      (nrᵢ+-∞-GLB 1 (+-comm s ∞))
  nr₃-GLB ∞ ∞ s =
    nrᵢ+-∞-GLB 0 refl

opaque

  -- The sequence nrᵢ r z s has a greatest lower bound

  nrᵢ-GLB : ∀ r z s → ∃ λ p → Greatest-lower-bound p (nrᵢ r z s)
  nrᵢ-GLB r z s = _ , nr₃-GLB r z s

opaque

  -- The modality has well-behaved GLBs.

  ℕ⊎∞-supports-glb-for-natrec :
    Has-well-behaved-GLBs ℕ⊎∞-modality
  ℕ⊎∞-supports-glb-for-natrec = record
    { +-GLBˡ = +-GLBˡ
    ; ·-GLBˡ = ·-GLBˡ
    ; ·-GLBʳ = comm∧·-GLBˡ⇒·-GLBʳ ·-comm ·-GLBˡ
    ; +nrᵢ-GLB = +nrᵢ-GLB
    }
    where
    ·-GLBˡ : {p q : ℕ⊎∞} {pᵢ : Sequence ℕ⊎∞} →
            Greatest-lower-bound p pᵢ →
            Greatest-lower-bound (q · p) (λ i → q · pᵢ i)
    ·-GLBˡ {p} {q} {pᵢ} p-glb =
      (λ i → ·-monotoneʳ (p-glb .proj₁ i)) , lemma p q p-glb
      where
      lemma″ : ∀ {q r} p → ⌞ r ⌟ ≤ᶠ ⌞ 1+ q ⌟ · p → p ≡ ⌞ r N./ 1+ q ⌟
      lemma″ ∞ ()
      lemma″ {q} {r} ⌞ p ⌟ r≤ = cong ⌞_⌟ $ begin
        p                   ≡˘⟨ N.m*n/n≡m p (1+ q) ⟩
        p N.* 1+ q N./ 1+ q ≡⟨ cong (N._/ 1+ q) (N.*-comm p (1+ q)) ⟩
        1+ q N.* p N./ 1+ q ≡˘⟨ cong (N._/ 1+ q) (⌞⌟≤ᶠ⌞⌟ (subst (⌞ r ⌟ ≤ᶠ_)
                                  (⌞⌟·⌞⌟≡⌞*⌟ {1+ q} {p}) r≤)) ⟩
        r N./ 1+ q          ∎
        where
        open Tools.Reasoning.PropositionalEquality
      open Tools.Reasoning.PartialOrder ≤-poset
      lemma′ : ∀ {q r} p b → b ≡ total → Greatest-lower-bound p pᵢ →
               (∀ i → ⌞ r ⌟ ≤ ⌞ 1+ q ⌟ · pᵢ i) →
               ⌞ r ⌟ ≤ ⌞ 1+ q ⌟ · p
      lemma′ ⌞ 0 ⌟ _ _ p-glb r≤ =
        ≤-trans (r≤ 0) (≤-reflexive (·-congˡ (𝟘-GLB-inv p-glb 0)))
      lemma′ {q} {r} ⌞ 1+ p ⌟ false refl p-glb r≤ =
        let r≡ = λ i → lemma″ (pᵢ i) (r≤ i)
        in  begin
          ⌞ r ⌟               ≤⟨ r≤ 0 ⟩
          ⌞ 1+ q ⌟ · pᵢ 0     ≤⟨ ·-monotoneʳ (p-glb .proj₂ (pᵢ 0) (λ i →
                                   ≤-reflexive (trans (r≡ 0) (sym (r≡ i))))) ⟩
          ⌞ 1+ q ⌟ · ⌞ 1+ p ⌟ ∎
      lemma′ {q} {r} ⌞ 1+ p ⌟ true refl p-glb r≤ =
        let nᵢ , nᵢ≡ , nᵢ≤ , p≤ = ⌞⌟-GLB-inv′ _ pᵢ p-glb
        in  ⌞⌟-antitoneₐ $ N.*-LUB {k = 1+ q} nᵢ nᵢ≤ p≤ .proj₂ r λ i →
              ⌞⌟-antitone⁻¹ $ begin
                ⌞ r ⌟               ≤⟨ r≤ i ⟩
                ⌞ 1+ q ⌟ · pᵢ i     ≡˘⟨ ·-congˡ (nᵢ≡ i) ⟩
                ⌞ 1+ q ⌟ · ⌞ nᵢ i ⌟ ≡⟨ ⌞⌟·⌞⌟≡⌞*⌟ ⟩
                ⌞ 1+ q N.* nᵢ i ⌟   ∎
      lemma′ ∞ false refl p-glb r≤ =
        ⊥-elim (∞-GLB-inv _ pᵢ p-glb (λ i →
          ≤-reflexive (sym (lemma″ (pᵢ i) (r≤ i)))))
      lemma′ ∞ true refl p-glb r≤ =
        ⊥-elim (∞-GLB-inv _ pᵢ p-glb (λ i →
          ≤-trans (r≤ i) (≤-trans (≤-reflexive (·-comm _ _))
            (·-decreasingˡₐ (λ ())))))
      lemma : ∀ p q → Greatest-lower-bound p pᵢ →
              ∀ r → (∀ i → r ≤ q · pᵢ i) → r ≤ q · p
      lemma p q p-glb ∞ r≤ = ∞≤ (q · p)
      lemma ⌞ 0 ⌟ q p-glb ⌞ r ⌟ r≤ =
        ≤-trans (r≤ 0) (≤-reflexive (·-congˡ (𝟘-GLB-inv p-glb 0)))
      lemma p ⌞ 0 ⌟ p-glb ⌞ r ⌟ r≤ = r≤ 0
      lemma ⌞ 1+ p ⌟ ∞ p-glb ⌞ r ⌟ r≤ =
        ⊥-elim (1+-GLB-inv pᵢ p-glb .proj₁ λ i → r≤∞p→p≡𝟘 _ (r≤ i))
        where
        r≤∞p→p≡𝟘 : ∀ p → ⌞ r ⌟ ≤ ∞ · p → p ≡ 𝟘
        r≤∞p→p≡𝟘 ⌞ 0 ⌟ r≤ = refl
        r≤∞p→p≡𝟘 ⌞ 1+ x ⌟ r≤ = ⊥-elim (≰∞ r≤)
        r≤∞p→p≡𝟘 ∞ r≤ = ⊥-elim (≰∞ r≤)
      lemma p ⌞ 1+ q ⌟ p-glb ⌞ r ⌟ r≤ = lemma′ p _ refl p-glb r≤
      lemma ∞ ∞ p-glb ⌞ r ⌟ r≤ =
        ⊥-elim (∞-GLB-inv r pᵢ p-glb (λ i →
          ≤-trans (r≤ i) ∞·-decreasing))

    +-GLBˡ : {p q : ℕ⊎∞} {pᵢ : Sequence ℕ⊎∞} →
            Greatest-lower-bound p pᵢ →
            Greatest-lower-bound (q + p) (λ i → q + pᵢ i)
    +-GLBˡ {p} {q} {pᵢ} p-glb =
      (λ i → +-monotoneʳ (p-glb .proj₁ i)) , lemma p q p-glb
      where
      lemma″ : ∀ {q r} p → ⌞ r ⌟ ≤ᶠ ⌞ q ⌟ + p → p ≡ ⌞ r N.∸ q ⌟
      lemma″ ∞ ()
      lemma″ {q} {r} ⌞ p ⌟ r≤ = cong ⌞_⌟ $ begin
        p             ≡˘⟨ N.m+n∸n≡m p q ⟩
        p N.+ q N.∸ q ≡⟨ cong (N._∸ q) (N.+-comm p q) ⟩
        q N.+ p N.∸ q ≡˘⟨ cong (N._∸ q) (⌞⌟≤ᶠ⌞⌟ r≤) ⟩
        r N.∸ q       ∎
        where
        open Tools.Reasoning.PropositionalEquality
      lemma′ : ∀ {q r} p b → b ≡ total → Greatest-lower-bound p pᵢ →
               (∀ i → ⌞ r ⌟ ≤ ⌞ q ⌟ + pᵢ i) →
               ⌞ r ⌟ ≤ ⌞ q ⌟ + p
      lemma′ {q} {r} ⌞ p ⌟ false refl p-glb r≤ =
        let r≡ = λ i → lemma″ (pᵢ i) (r≤ i)
        in  begin
          ⌞ r ⌟          ≤⟨ r≤ 0 ⟩
          ⌞ q ⌟ + pᵢ 0   ≤⟨ +-monotoneʳ (p-glb .proj₂ (pᵢ 0) (λ i →
                             ≤-reflexive (trans (r≡ 0) (sym (r≡ i))))) ⟩
          ⌞ q ⌟ + ⌞ p ⌟  ∎
        where
        open Tools.Reasoning.PartialOrder ≤-poset
      lemma′ {q} {r} ⌞ p ⌟ true refl p-glb r≤ =
        let nᵢ , nᵢ≡ , nᵢ≤ , p≤ = ⌞⌟-GLB-inv′ _ pᵢ p-glb
        in  ⌞⌟-antitoneₐ $ N.+-LUB nᵢ nᵢ≤ p≤ .proj₂ _ λ i →
              ⌞⌟-antitone⁻¹ $ begin
                ⌞ r ⌟             ≤⟨ r≤ i ⟩
                ⌞ q ⌟ + pᵢ i      ≡˘⟨ +-congˡ (nᵢ≡ i) ⟩
                ⌞ q ⌟ + ⌞ nᵢ i ⌟  ∎
        where
        open Tools.Reasoning.PartialOrder ≤-poset
      lemma′ ∞ false refl p-glb r≤ =
        ⊥-elim (∞-GLB-inv _ pᵢ p-glb λ i →
          ≤-reflexive (sym (lemma″ (pᵢ i) (r≤ i))))
      lemma′ ∞ true refl p-glb r≤ =
        ⊥-elim (∞-GLB-inv _ pᵢ p-glb λ i →
          ≤-trans (r≤ i) (≤-trans (≤-reflexive (+-comm _ _))
            +-decreasingˡₐ))
      lemma : ∀ p q → Greatest-lower-bound p pᵢ →
              ∀ r → (∀ i → r ≤ q + pᵢ i) → r ≤ q + p
      lemma p ∞ p-glb r r≤ = r≤ 0
      lemma p q p-glb ∞ r≤ = ∞≤ (q + p)
      lemma p ⌞ q ⌟ p-glb ⌞ r ⌟ r≤ = lemma′ p total refl p-glb r≤

    +nrᵢ-GLB : ∀ {p q r z z′ s s′} →
      Greatest-lower-bound p (nrᵢ r z s) →
      Greatest-lower-bound q (nrᵢ r z′ s′) →
      ∃ λ x → Greatest-lower-bound x (nrᵢ r (z + z′) (s + s′)) × p + q ≤ x
    +nrᵢ-GLB {p} {q} {r} {z} {z′} {s} {s′} p-glb q-glb =
        nr₃ r (z + z′) (s + s′)
      , nr₃-GLB r (z + z′) (s + s′)
      , (begin
          p + q                   ≡⟨ +-cong (GLB-unique p-glb (nr₃-GLB r z s))
                                      (GLB-unique q-glb (nr₃-GLB r z′ s′)) ⟩
          nr₃ r z s + nr₃ r z′ s′ ≤⟨ nr₃-+ r ⟩
          nr₃ r (z + z′) (s + s′) ∎)
      where
      open Tools.Reasoning.PartialOrder ≤-poset
