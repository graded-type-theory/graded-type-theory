------------------------------------------------------------------------
-- A modality for the natural numbers extended with infinity
------------------------------------------------------------------------

open import Tools.Bool hiding (_∧_)

module Graded.Modality.Instances.Nat-plus-infinity
  -- Should the order give "affine" uses (as opposed to exact)
  (affine : Bool) where

import Tools.Algebra
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat as N using (Nat; 1+; 2+)
open import Tools.Product as Σ
open import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum as ⊎ using (_⊎_; inj₁; inj₂)

open import Graded.FullReduction.Assumptions
import Graded.Modality
import Graded.Modality.Instances.BoundedStar as BoundedStar
import Graded.Modality.Instances.LowerBounded as LowerBounded
import Graded.Modality.Instances.Recursive.Sequences
import Graded.Modality.Properties.Addition
import Graded.Modality.Properties.Division
import Graded.Modality.Properties.Has-well-behaved-zero
import Graded.Modality.Properties.Meet
import Graded.Modality.Properties.Multiplication
import Graded.Modality.Properties.PartialOrder
import Graded.Modality.Properties.Subtraction
open import Graded.Modality.Variant lzero

open import Definition.Typed.Restrictions
open import Definition.Untyped using (BMΣ; 𝕤; 𝕨)
open import Graded.Usage.Restrictions

-- The grades are the natural numbers extended with ∞.

data ℕ⊎∞ : Set where
  ⌞_⌟ : Nat → ℕ⊎∞
  ∞   : ℕ⊎∞

open Graded.Modality ℕ⊎∞
open Tools.Algebra   ℕ⊎∞

private variable
  m n o   : ℕ⊎∞
  TRs     : Type-restrictions _
  URs     : Usage-restrictions _
  variant : Modality-variant

------------------------------------------------------------------------
-- Operators

-- Addition.

infixr 40 _+_

_+_ : ℕ⊎∞ → ℕ⊎∞ → ℕ⊎∞
∞     + _     = ∞
⌞ _ ⌟ + ∞     = ∞
⌞ m ⌟ + ⌞ n ⌟ = ⌞ m N.+ n ⌟


-- Meet.

-- The meet operation used for the "affine" order

_∧ₐ_ : ℕ⊎∞ → ℕ⊎∞ → ℕ⊎∞
∞ ∧ₐ _ = ∞
⌞ _ ⌟ ∧ₐ ∞ = ∞
⌞ m ⌟ ∧ₐ ⌞ n ⌟ = ⌞ m N.⊔ n ⌟

-- The meet operation used for the "exact" order

_∧ₑ_ : ℕ⊎∞ → ℕ⊎∞ → ℕ⊎∞
∞ ∧ₑ _ = ∞
⌞ _ ⌟ ∧ₑ ∞ = ∞
⌞ m ⌟ ∧ₑ ⌞ n ⌟ =
  case m N.≟ n of λ where
    (yes _) → ⌞ m ⌟
    (no _) → ∞
  -- if m N.== n then ⌞ m ⌟ else ∞

-- The meet operation is defined in such a way that
-- ∞ ≤ … ≤ ⌞ 1 ⌟ ≤ ⌞ 0 ⌟ if "affine" is true
-- and ∞ ≤ ⌞ m ⌟ and ⌞ m ⌟≰⌞ n ⌟ otherwise (for all m and n).

infixr 40 _∧_

_∧_ : ℕ⊎∞ → ℕ⊎∞ → ℕ⊎∞
p ∧ q = if affine then p ∧ₐ q else p ∧ₑ q

-- An "introduction rule" for predicates over _∧_

∧-intro : (P : Op₂ ℕ⊎∞ → Set) (Pₐ : P _∧ₐ_) (Pₑ : P _∧ₑ_) → P _∧_
∧-intro P Pₐ Pₑ = lemma affine
  where
  lemma : ∀ b → P (λ p q → if b then p ∧ₐ q else p ∧ₑ q)
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

-- The inferred ordering relation for the "affine" order

infix 10 _≤ₐ_

_≤ₐ_ : ℕ⊎∞ → ℕ⊎∞ → Set
m ≤ₐ n = m ≡ m ∧ₐ n

-- The inferred ordering relation for the "exact" order

infix 10 _≤ₑ_

_≤ₑ_ : ℕ⊎∞ → ℕ⊎∞ → Set
m ≤ₑ n = m ≡ m ∧ₑ n

opaque

  -- An "introduction rule" for the order relation

  ≤-intro : m ≤ₐ n → m ≤ₑ n → m ≤ n
  ≤-intro {m} {n} ≤ₐ ≤ₑ = lemma affine
    where
    lemma : ∀ b → m ≡ (if b then m ∧ₐ n else (m ∧ₑ n))
    lemma false = ≤ₑ
    lemma true = ≤ₐ

opaque

  -- Another "introduction rule" for the order relation

  ≤ₐ-intro : T affine → m ≤ₐ n → m ≤ n
  ≤ₐ-intro {m} {n} x ≤ₐ = lemma affine x
    where
    lemma : ∀ b → T b → m ≡ (if b then m ∧ₐ n else (m ∧ₑ n))
    lemma true _ = ≤ₐ

opaque

  -- The "exact" order relation is a subset of the "affine" order

  ≤ₑ→≤ₐ : m ≤ₑ n → m ≤ₐ n
  ≤ₑ→≤ₐ {(∞)} {n} ≤ₑ = refl
  ≤ₑ→≤ₐ {(⌞ m ⌟)} {(⌞ n ⌟)} ≤ₑ with m N.≟ n
  ≤ₑ→≤ₐ ≤ₑ | yes refl = cong ⌞_⌟ (sym (N.⊔-idem _))
  ≤ₑ→≤ₐ () | no _

opaque

  -- Another "introduction rule" for the order relation

  ≤ₑ-intro : m ≤ₑ n → m ≤ n
  ≤ₑ-intro ≤ₑ = ≤-intro (≤ₑ→≤ₐ ≤ₑ) ≤ₑ

------------------------------------------------------------------------
-- Some properties

opaque

  -- The grade ∞ is not equal to ⌞ m ⌟

  ∞≢⌞m⌟ : ∀ {m} → ∞ ≢ ⌞ m ⌟
  ∞≢⌞m⌟ ()

-- The grade ∞ is the least one.

∞≤ : ∀ n → ∞ ≤ n
∞≤ _ = ≤ₑ-intro {n = ∞} refl

opaque

  -- The grade ∞ is not larger than ⌞ n ⌟ for any n

  ≰∞ : ∀ {n} → ⌞ n ⌟ ≤ ∞ → ⊥
  ≰∞ = lemma affine
    where
    lemma : ∀ {n} → (b : Bool) → ⌞ n ⌟ ≢ (if b then ∞ else ∞)
    lemma true ()
    lemma false ()

-- For the affine order, the grade ⌞ 0 ⌟ is the greatest one.

≤0 : T affine → n ≤ ⌞ 0 ⌟
≤0 x = ≤ₐ-intro x lemma
  where
  open Tools.Reasoning.PropositionalEquality
  lemma : n ≤ₐ ⌞ 0 ⌟
  lemma {n = ∞} = refl
  lemma {n = ⌞ n ⌟} = cong ⌞_⌟ (
    n        ≡˘⟨ N.⊔-identityʳ _ ⟩
    n N.⊔ 0  ∎)

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
  -- The function ⌞_⌟ is antitone for the "affine" order

  ⌞⌟-antitoneₐ : ∀ {m n} → m N.≤ n → ⌞ n ⌟ ≤ₐ ⌞ m ⌟
  ⌞⌟-antitoneₐ {m = m} {n = n} m≤n =
    ⌞ n ⌟        ≡˘⟨ cong ⌞_⌟ (N.m≥n⇒m⊔n≡m m≤n) ⟩
    ⌞ n N.⊔ m ⌟  ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque

  ⌞⌟-antitone : ∀ {m n} → T affine → m N.≤ n → ⌞ n ⌟ ≤ ⌞ m ⌟
  ⌞⌟-antitone {m = m} {n = n} x m≤n =
    ≤ₐ-intro x (⌞⌟-antitoneₐ m≤n)

opaque

  -- An inverse to ⌞⌟-antitone.
  -- Note that unlike ⌞⌟-antitone this property holds for both the
  -- "affine" and "exact" orders.

  ⌞⌟-antitone⁻¹ : ∀ {m n} → ⌞ n ⌟ ≤ ⌞ m ⌟ → m N.≤ n
  ⌞⌟-antitone⁻¹ {m = m} {n = n} = lemma affine
    where
    lemma : ∀ b → ⌞ n ⌟ ≡ (if b then ⌞ n ⌟ ∧ₐ ⌞ m ⌟ else ⌞ n ⌟ ∧ₑ ⌞ m ⌟)
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

  -- Addition is decreasing for the left argument for the "affine" order

  +-decreasingˡₐ : m + n ≤ₐ m
  +-decreasingˡₐ {m = ∞}                 = refl
  +-decreasingˡₐ {m = ⌞ _ ⌟} {n = ∞}     = refl
  +-decreasingˡₐ {m = ⌞ _ ⌟} {n = ⌞ n ⌟} = ⌞⌟-antitoneₐ (N.m≤m+n _ n)

opaque

  +-decreasingˡ : T affine → m + n ≤ m
  +-decreasingˡ x = ≤ₐ-intro x +-decreasingˡₐ


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
  n*≤1 = ≤ₑ-intro n*≤ₑ1
    where
    n*≤ₑ1 : n * ≤ₑ ⌞ 1 ⌟
    n*≤ₑ1 {n = ⌞ 0 ⌟} = refl
    n*≤ₑ1 {n = ⌞ 1+ _ ⌟} = refl
    n*≤ₑ1 {n = ∞} = refl

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

  -- The relation _≤ₐ_ is total.

  ≤ₐ-total : ∀ m n → m ≤ₐ n ⊎ n ≤ₐ m
  ≤ₐ-total ∞     _     = inj₁ refl
  ≤ₐ-total _     ∞     = inj₂ refl
  ≤ₐ-total ⌞ m ⌟ ⌞ n ⌟ = case N.≤-total m n of λ where
    (inj₁ m≤n) → inj₂ (⌞⌟-antitoneₐ m≤n)
    (inj₂ n≤m) → inj₁ (⌞⌟-antitoneₐ n≤m)

opaque

  -- The relation _≤_ is total for the affine order

  ≤-total : T affine → ∀ m n → m ≤ n ⊎ n ≤ m
  ≤-total x m n =
    case ≤ₐ-total m n of λ where
      (inj₁ m≤n) → inj₁ (≤ₐ-intro x m≤n)
      (inj₂ n≤m) → inj₂ (≤ₐ-intro x n≤m)

-- The type ℕ⊎∞ is a set.

ℕ⊎∞-set : Is-set ℕ⊎∞
ℕ⊎∞-set {x = ∞}     {y = ∞}     {x = refl} {y = refl} = refl
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
  ∞·+≤∞·ʳ {m = ⌞ 0 ⌟}    {n = ⌞ 0 ⌟}    = lemma affine
    where
    lemma : ∀ b → ⌞ 0 ⌟ ≡ (if b then ⌞ 0 ⌟ else ⌞ 0 ⌟)
    lemma false = refl
    lemma true = refl
  ∞·+≤∞·ʳ {m = ⌞ 1+ _ ⌟} {n = ⌞ 0 ⌟}    = ∞≤ ⌞ 0 ⌟
  ∞·+≤∞·ʳ {m = ⌞ 0 ⌟}    {n = ⌞ 1+ _ ⌟} = ∞≤ ∞
  ∞·+≤∞·ʳ {m = ⌞ 1+ _ ⌟} {n = ⌞ 1+ _ ⌟} = ∞≤ ∞

opaque

  m≢n→m∧ₑn≡∞ : ∀ {m n} → m ≢ n → ⌞ m ⌟ ∧ₑ ⌞ n ⌟ ≡ ∞
  m≢n→m∧ₑn≡∞ {m} {n} m≢n with m N.≟ n
  … | yes m≡n = ⊥-elim (m≢n m≡n)
  … | no _ = refl

------------------------------------------------------------------------
-- The modality

-- A "semiring with meet" for ℕ⊎∞.

ℕ⊎∞-semiring-with-meet : Semiring-with-meet
ℕ⊎∞-semiring-with-meet = record
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
        ; assoc = ∧-intro Associative ∧ₐ-assoc ∧ₑ-assoc
        }
      ; idem = ∧-intro Idempotent ∧ₐ-idem ∧ₑ-idem
      }
    ; comm = ∧-intro Commutative ∧ₐ-comm ∧ₑ-comm
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

  ∧ₐ-comm : Commutative _∧ₐ_
  ∧ₐ-comm ⌞ m ⌟ ⌞ n ⌟ = cong ⌞_⌟ (N.⊔-comm m n)
  ∧ₐ-comm ⌞ m ⌟ ∞ = refl
  ∧ₐ-comm ∞ ⌞ n ⌟ = refl
  ∧ₐ-comm ∞ ∞ = refl

  ∧ₑ-comm : Commutative _∧ₑ_
  ∧ₑ-comm ⌞ m ⌟ ⌞ n ⌟ with m N.≟ n | n N.≟ m
  … | yes refl | yes _ = refl
  … | no m≢n | no n≢m = refl
  … | yes m≡n | no n≢m = ⊥-elim (n≢m (sym m≡n))
  … | no m≢n | yes n≡m = ⊥-elim (m≢n (sym n≡m))
  ∧ₑ-comm ⌞ m ⌟ ∞ = refl
  ∧ₑ-comm ∞ ⌞ n ⌟ = refl
  ∧ₑ-comm ∞ ∞ = refl

  ∧ₐ-assoc : Associative _∧ₐ_
  ∧ₐ-assoc = λ where
    ⌞ m ⌟ ⌞ _ ⌟ ⌞ _ ⌟ → cong ⌞_⌟ (N.⊔-assoc m _ _)
    ⌞ _ ⌟ ⌞ _ ⌟ ∞     → refl
    ⌞ _ ⌟ ∞     _     → refl
    ∞     _     _     → refl

  ∧ₑ-assoc : Associative _∧ₑ_
  ∧ₑ-assoc = λ where
    ⌞ m ⌟ ⌞ n ⌟ ⌞ o ⌟ → lemma m n o
    ⌞ m ⌟ ⌞ n ⌟ ∞ → ∧ₑ-comm (⌞ m ⌟ ∧ₑ ⌞ n ⌟) ∞
    ⌞ _ ⌟ ∞ _ → refl
    ∞ _ _ → refl
      where
      lemma : ∀ m n o
            → (⌞ m ⌟ ∧ₑ ⌞ n ⌟) ∧ₑ ⌞ o ⌟
            ≡ ⌞ m ⌟ ∧ₑ (⌞ n ⌟ ∧ₑ ⌞ o ⌟)
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

  ∧ₐ-idem : Idempotent _∧ₐ_
  ∧ₐ-idem = λ where
    ∞     → refl
    ⌞ _ ⌟ → cong ⌞_⌟ (N.⊔-idem _)

  ∧ₑ-idem : Idempotent _∧ₑ_
  ∧ₑ-idem ⌞ m ⌟ with m N.≟ m
  … | yes _ = refl
  … | no m≢m = ⊥-elim (m≢m refl)
  ∧ₑ-idem ∞ = refl

  ·-distribˡ-∧ₐ : _·_ DistributesOverˡ _∧ₐ_
  ·-distribˡ-∧ₐ ⌞ 0 ⌟ _ _ = refl
  ·-distribˡ-∧ₐ ⌞ 1+ _ ⌟ ⌞ 0 ⌟ ⌞ 0 ⌟ = refl
  ·-distribˡ-∧ₐ ⌞ 1+ _ ⌟ ⌞ 0 ⌟ ⌞ 1+ _ ⌟ = refl
  ·-distribˡ-∧ₐ ⌞ 1+ _ ⌟ ⌞ 0 ⌟ ∞ = refl
  ·-distribˡ-∧ₐ ⌞ 1+ _ ⌟ ⌞ 1+ _ ⌟ ⌞ 0 ⌟ = refl
  ·-distribˡ-∧ₐ ⌞ 1+ m ⌟ ⌞ 1+ n ⌟ ⌞ 1+ _ ⌟ = cong ⌞_⌟ $
                                             N.*-distribˡ-⊔ (1+ m) (1+ n) (1+ _)
  ·-distribˡ-∧ₐ ⌞ 1+ _ ⌟ ⌞ 1+ _ ⌟ ∞ = refl
  ·-distribˡ-∧ₐ ⌞ 1+ _ ⌟ ∞ _ = refl
  ·-distribˡ-∧ₐ ∞ ⌞ 0 ⌟ ⌞ 0 ⌟ = refl
  ·-distribˡ-∧ₐ ∞ ⌞ 0 ⌟ ⌞ 1+ _ ⌟ = refl
  ·-distribˡ-∧ₐ ∞ ⌞ 0 ⌟ ∞ = refl
  ·-distribˡ-∧ₐ ∞ ⌞ 1+ _ ⌟ ⌞ 0 ⌟ = refl
  ·-distribˡ-∧ₐ ∞ ⌞ 1+ _ ⌟ ⌞ 1+ _ ⌟ = refl
  ·-distribˡ-∧ₐ ∞ ⌞ 1+ _ ⌟ ∞ = refl
  ·-distribˡ-∧ₐ ∞ ∞ _ = refl

  ·-distribˡ-∧ₑ : _·_ DistributesOverˡ _∧ₑ_
  ·-distribˡ-∧ₑ ⌞ 0 ⌟ _ _ = refl
  ·-distribˡ-∧ₑ ⌞ 1+ m ⌟ ⌞ 0 ⌟ ⌞ 0 ⌟ = refl
  ·-distribˡ-∧ₑ ⌞ 1+ m ⌟ ⌞ 0 ⌟ ⌞ 1+ o ⌟ = refl
  ·-distribˡ-∧ₑ ⌞ 1+ m ⌟ ⌞ 1+ n ⌟ ⌞ 0 ⌟ = refl
  ·-distribˡ-∧ₑ ⌞ 1+ m ⌟ ⌞ 1+ n ⌟ ⌞ 1+ o ⌟
    with 1+ n N.≟ 1+ o | 1+ m N.* 1+ n N.≟ 1+ m N.* 1+ o
  … | yes refl | yes _ = refl
  … | yes refl | no ¬≡ = ⊥-elim (¬≡ refl)
  … | no n≢o | yes eq = ⊥-elim (n≢o (N.*-cancelˡ-≡ (1+ n) (1+ o) (1+ m) eq))
  … | no _ | no _ = refl
  ·-distribˡ-∧ₑ ⌞ 1+ m ⌟ ⌞ n ⌟ ∞ = sym (∧ₑ-comm (⌞ 1+ m ⌟ · ⌞ n ⌟) ∞)
  ·-distribˡ-∧ₑ ⌞ 1+ _ ⌟ ∞ _ = refl
  ·-distribˡ-∧ₑ ∞ ⌞ n ⌟ ⌞ o ⌟ with n N.≟ o
  … | yes refl = sym (∧ₑ-idem (∞ · ⌞ n ⌟))
  ·-distribˡ-∧ₑ ∞ ⌞ 0 ⌟ ⌞ 0 ⌟ | no n≢o = ⊥-elim (n≢o refl)
  ·-distribˡ-∧ₑ ∞ ⌞ 0 ⌟ ⌞ 1+ o ⌟ | no n≢o = refl
  ·-distribˡ-∧ₑ ∞ ⌞ 1+ n ⌟ ⌞ o ⌟ | no n≢o = refl
  ·-distribˡ-∧ₑ ∞ ⌞ n ⌟ ∞ = sym (∧ₑ-comm (∞ · ⌞ n ⌟) ∞)
  ·-distribˡ-∧ₑ ∞ ∞ _ = refl

  ·-distribˡ-∧ : _·_ DistributesOverˡ _∧_
  ·-distribˡ-∧ =
    ∧-intro (_·_ DistributesOverˡ_) ·-distribˡ-∧ₐ ·-distribˡ-∧ₑ

  ·-distrib-∧ : _·_ DistributesOver _∧_
  ·-distrib-∧ =
    ·-distribˡ-∧ , comm∧distrˡ⇒distrʳ ·-comm ·-distribˡ-∧

  +-distribˡ-∧ₐ : _+_ DistributesOverˡ _∧ₐ_
  +-distribˡ-∧ₐ ⌞ m ⌟ ⌞ _ ⌟ ⌞ _ ⌟ = cong ⌞_⌟ (N.+-distribˡ-⊔ m _ _)
  +-distribˡ-∧ₐ ⌞ _ ⌟ ⌞ _ ⌟ ∞     = refl
  +-distribˡ-∧ₐ ⌞ _ ⌟ ∞     _     = refl
  +-distribˡ-∧ₐ ∞     _     _     = refl

  +-distribˡ-∧ₑ : _+_ DistributesOverˡ _∧ₑ_
  +-distribˡ-∧ₑ ⌞ m ⌟ ⌞ n ⌟ ⌞ o ⌟ with n N.≟ o | m N.+ n N.≟ m N.+ o
  … | yes n≡o | yes m+n≡m+o = refl
  … | yes refl | no m+n≢m+o = ⊥-elim (m+n≢m+o refl)
  … | no n≢o | yes m+n≡m+o = ⊥-elim (n≢o (N.+-cancelˡ-≡ m n o m+n≡m+o))
  … | no n≢o | no m+n≢m+o = refl
  +-distribˡ-∧ₑ ⌞ _ ⌟ ⌞ _ ⌟ ∞     = refl
  +-distribˡ-∧ₑ ⌞ _ ⌟ ∞     _     = refl
  +-distribˡ-∧ₑ ∞     _     _     = refl

  +-distribˡ-∧ : _+_ DistributesOverˡ _∧_
  +-distribˡ-∧ =
    ∧-intro (_+_ DistributesOverˡ_) +-distribˡ-∧ₐ +-distribˡ-∧ₑ

  +-distrib-∧ : _+_ DistributesOver _∧_
  +-distrib-∧ =
    +-distribˡ-∧ , comm∧distrˡ⇒distrʳ +-comm +-distribˡ-∧

instance

  -- The semiring has a well-behaved zero.

  ℕ⊎∞-has-well-behaved-zero :
    Has-well-behaved-zero ℕ⊎∞-semiring-with-meet
  ℕ⊎∞-has-well-behaved-zero = record
    { non-trivial  = λ ()
    ; zero-product = λ where
        {p = ⌞ 0 ⌟} {q = ⌞ _ ⌟} _ → inj₁ refl
        {p = ⌞ 0 ⌟} {q = ∞}     _ → inj₁ refl
        {p = ⌞ _ ⌟} {q = ⌞ 0 ⌟} _ → inj₂ refl
        {p = ∞}     {q = ⌞ 0 ⌟} _ → inj₂ refl
    ; +-positiveˡ  = λ where
        {p = ⌞ 0 ⌟} {q = ⌞ _ ⌟} _ → refl
    ; ∧-positiveˡ  = ∧-intro (λ _∧₁_ → {p q : ℕ⊎∞} → (p ∧₁ q) ≡ ⌞ 0 ⌟ → p ≡ ⌞ 0 ⌟)
      (λ where
        {p = ⌞ 0 ⌟}    {q = ⌞ _ ⌟} _ → refl
        {p = ⌞ 1+ _ ⌟} {q = ⌞ 0 ⌟} ())
      (λ where
        {p = ⌞ 0 ⌟}    {q = ⌞ _ ⌟}    _ → refl
        {p = ⌞ 1+ _ ⌟} {q = ⌞ 0 ⌟}   ()
        {p = ⌞ 1+ m ⌟} {q = ⌞ 1+ n ⌟} x → ⊥-elim (lemma m n x))
    }
   where
   lemma : ∀ m n → ⌞ 1+ m ⌟ ∧ₑ ⌞ 1+ n ⌟ ≢ ⌞ 0 ⌟
   lemma m n 1+m∧1+n≡0 with 1+ m N.≟ 1+ n
   lemma m .m () | yes refl
   lemma m n () | no _

private
  module BS =
    BoundedStar
      ℕ⊎∞-semiring-with-meet _* (λ _ → *≡+·*) (λ _ → inj₂ n*≤1)

-- A natrec-star operator for ℕ⊎∞ defined using the construction in
-- Graded.Modality.Instances.BoundedStar.

ℕ⊎∞-has-star-bounded-star : Has-star ℕ⊎∞-semiring-with-meet
ℕ⊎∞-has-star-bounded-star = BS.has-star

-- A natrec-star operator for ℕ⊎∞ defined using the construction in
-- Graded.Modality.Instances.LowerBounded.

ℕ⊎∞-has-star-lower-bounded : Has-star ℕ⊎∞-semiring-with-meet
ℕ⊎∞-has-star-lower-bounded =
  LowerBounded.has-star ℕ⊎∞-semiring-with-meet ∞ ∞≤

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
  , ⌞ 1 ⌟ , ⌞ 1 ⌟ , ⌞ 0 ⌟ , lemma affine
  where
  lemma : ∀ b
        → ∞ · (if b then ⌞ 1 ⌟ else ⌞ 1 ⌟)
        ≢ ⌞ 1 ⌟ · (if b then ⌞ 1 ⌟ else ⌞ 1 ⌟)
  lemma false ()
  lemma true ()

------------------------------------------------------------------------
-- Properties related to division

private
  module D = Graded.Modality.Properties.Division ℕ⊎∞-semiring-with-meet

opaque

  -- The division operator is correctly defined (for the affine order).

  /≡/ : T affine → m D./ n ≡ m / n
  /≡/ {m} {n} x = lemma (proj₁ T-true x) m n
    where
    lemma : affine ≡ true → (m n : ℕ⊎∞) → m D./ n ≡ m / n
    lemma refl ∞     ∞        = refl , λ _ _ → refl
    lemma refl ⌞ _ ⌟ ∞        = ≤0 _ , λ { ⌞ 0 ⌟ _ → refl }
    lemma refl _     ⌞ 0 ⌟    = ≤0 _ , λ _ _ → refl
    lemma refl ∞     ⌞ 1+ _ ⌟ = refl , λ _ _ → refl
    lemma refl ⌞ m ⌟ ⌞ 1+ n ⌟ =
      (begin
           ⌞ m ⌟                      ≤⟨ ⌞⌟-antitone _ (N.m/n*n≤m _ (1+ _)) ⟩
           ⌞ (m N./ 1+ n) N.* 1+ n ⌟  ≡⟨ cong ⌞_⌟ (N.*-comm _ (1+ n)) ⟩
           ⌞ 1+ n N.* (m N./ 1+ n) ⌟  ≡˘⟨ ⌞⌟·⌞⌟≡⌞*⌟ ⟩
           ⌞ 1+ n ⌟ · ⌞ m N./ 1+ n ⌟  ∎)
      , λ where
          ⌞ o ⌟ →
            ⌞ m ⌟ ≤ ⌞ 1+ n ⌟ · ⌞ o ⌟  ≡⟨ cong (_ ≤_) ⌞⌟·⌞⌟≡⌞*⌟ ⟩→
            ⌞ m ⌟ ≤ ⌞ 1+ n N.* o ⌟    →⟨ ⌞⌟-antitone⁻¹ ⟩
            1+ n N.* o N.≤ m          →⟨ N.*≤→≤/ ⟩
            o N.≤ m N./ 1+ n          →⟨ ⌞⌟-antitone _ ⟩
            ⌞ m N./ 1+ n ⌟ ≤ ⌞ o ⌟    □
      where
      open Graded.Modality.Properties.PartialOrder ℕ⊎∞-semiring-with-meet
      open Tools.Reasoning.PartialOrder ≤-poset

opaque

  -- The division operator is not correctly defined (for the exact order).

  ¬/≡/ : T (not affine) → ¬ (∀ m n → m D./ n ≡ m / n)
  ¬/≡/ x /≡/ = lemma (proj₁ ¬-T (proj₁ T-not⇔¬-T x)) /≡/
    where
    lemma : affine ≡ false → ¬ (∀ m n → m D./ n ≡ m / n)
    lemma refl /≡/ = case /≡/ ⌞ 1 ⌟ ∞ of λ {(() , _)}

------------------------------------------------------------------------
-- A lemma related to Graded.Modality.Instances.Recursive

module _ where

  open Graded.Modality.Instances.Recursive.Sequences
         ℕ⊎∞-semiring-with-meet

  -- The family of sequences that Graded.Modality.Instances.Recursive is
  -- about does not have the required fixpoints.

  ¬-Has-fixpoints-nr : T affine → ¬ Has-fixpoints-nr
  ¬-Has-fixpoints-nr x = lemma (proj₁ T-true x)
    where
    open module S = Semiring-with-meet ℕ⊎∞-semiring-with-meet using (𝟘; 𝟙)
    open Graded.Modality.Properties.Meet ℕ⊎∞-semiring-with-meet
    open Tools.Reasoning.PropositionalEquality

    r = 𝟙
    p = 𝟘
    q = 𝟙

    increasing : affine ≡ true → ∀ n → nr (1+ n) p q r ≡ 𝟙 + nr n p q r
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

    always-⌞⌟ : affine ≡ true → ∀ m → ∃ λ n → nr m p q r ≡ ⌞ n ⌟
    always-⌞⌟ refl 0      = _ , refl
    always-⌞⌟ refl (1+ m) =
      case always-⌞⌟ refl m of λ {
        (n , eq) →
        1+ n
      , (nr (1+ m) p q r  ≡⟨ increasing refl m ⟩
         𝟙 + nr m p q r   ≡⟨ cong (𝟙 +_) eq ⟩
         ⌞ 1+ n ⌟         ∎) }

    lemma : affine ≡ true → ¬ Has-fixpoints-nr
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

nr : (p r z s n : ℕ⊎∞) → ℕ⊎∞
nr p r z s n = nr₃ r ⌞ 1 ⌟ p · n + nr₃ r z s

instance

  ℕ⊎∞-has-nr : Has-nr ℕ⊎∞-semiring-with-meet
  ℕ⊎∞-has-nr = record
    { nr = nr
    ; nr-monotone = λ {p = p} {r} → nr-monotone p r
    ; nr-· = λ {p} {r} {z} {s} {n} {q} → ≤-reflexive (nr-· p r z s n q)
    ; nr-+ = λ {p} {r} {z₁} {s₁} {n₁} {z₂} {s₂} {n₂} → nr-+ p r z₁ s₁ n₁ z₂ s₂ n₂
    ; nr-𝟘 = λ {p} {r} → nr-𝟘 p r
    ; nr-positive = λ {p} {r} → nr-positive {p} {r}
    ; nr-zero = λ {n} {p} {r} {z} {s} → nr-zero p r z s n
    ; nr-suc = λ {p} {r} {z} {s} {n} → nr-suc p r z s n
    }
    where
    open Semiring-with-meet ℕ⊎∞-semiring-with-meet
      hiding (_≤_; _+_; _·_; _∧_)
    open Graded.Modality.Properties.Addition ℕ⊎∞-semiring-with-meet
    open Graded.Modality.Properties.Has-well-behaved-zero ℕ⊎∞-semiring-with-meet
    open Graded.Modality.Properties.Meet ℕ⊎∞-semiring-with-meet
    open Graded.Modality.Properties.Multiplication ℕ⊎∞-semiring-with-meet
    open Graded.Modality.Properties.PartialOrder ℕ⊎∞-semiring-with-meet

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
      nr p r z s n · q ≡⟨⟩
      (nr₃ r 𝟙 p · n + nr₃ r z s) · q ≡⟨ ·-distribʳ-+ _ _ _ ⟩
      (nr₃ r 𝟙 p · n) · q + nr₃ r z s · q ≡⟨ +-cong (·-assoc _ _ _) (lemma r) ⟩
      nr₃ r 𝟙 p · (n · q) + nr₃ r (z · q) (s · q) ≡⟨⟩
      nr p r (z · q) (s · q) (n · q) ∎
      where
      open Tools.Reasoning.PropositionalEquality
      lemma : ∀ r → nr₃ r z s · q ≡ nr₃ r (z · q) (s · q)
      lemma ⌞ 0 ⌟    = ·-distribʳ-∧ _ _ _
      lemma ⌞ 1 ⌟    = trans (·-distribʳ-+ _ _ _) (+-congˡ (·-assoc _ _ _))
      lemma ⌞ 2+ _ ⌟ = trans (·-assoc _ _ _) (·-congˡ (·-distribʳ-+ _ _ _))
      lemma ∞        = trans (·-assoc _ _ _) (·-congˡ (·-distribʳ-+ _ _ _))

    nr-+ : ∀ p r z₁ s₁ n₁ z₂ s₂ n₂ → nr p r z₁ s₁ n₁ + nr p r z₂ s₂ n₂ ≤ nr p r (z₁ + z₂) (s₁ + s₂) (n₁ + n₂)
    nr-+ p r z₁ s₁ n₁ z₂ s₂ n₂ = begin
      nr p r z₁ s₁ n₁ + nr p r z₂ s₂ n₂                               ≡⟨⟩
      (nr₃ r 𝟙 p · n₁ + nr₃ r z₁ s₁) + (nr₃ r 𝟙 p · n₂ + nr₃ r z₂ s₂) ≡⟨ +-assoc _ _ _ ⟩
      nr₃ r 𝟙 p · n₁ + nr₃ r z₁ s₁ + nr₃ r 𝟙 p · n₂ + nr₃ r z₂ s₂     ≡˘⟨ +-congˡ (+-assoc _ _ _) ⟩
      nr₃ r 𝟙 p · n₁ + (nr₃ r z₁ s₁ + nr₃ r 𝟙 p · n₂) + nr₃ r z₂ s₂   ≡⟨ +-congˡ (+-congʳ (+-comm _ _)) ⟩
      nr₃ r 𝟙 p · n₁ + (nr₃ r 𝟙 p · n₂ + nr₃ r z₁ s₁) + nr₃ r z₂ s₂   ≡⟨ +-congˡ (+-assoc _ _ _) ⟩
      nr₃ r 𝟙 p · n₁ + nr₃ r 𝟙 p · n₂ + nr₃ r z₁ s₁ + nr₃ r z₂ s₂     ≡˘⟨ +-assoc _ _ _ ⟩
      (nr₃ r 𝟙 p · n₁ + nr₃ r 𝟙 p · n₂) + nr₃ r z₁ s₁ + nr₃ r z₂ s₂   ≡˘⟨ +-congʳ (·-distribˡ-+ _ _ _) ⟩
      nr₃ r 𝟙 p · (n₁ + n₂) + nr₃ r z₁ s₁ + nr₃ r z₂ s₂               ≤⟨ +-monotoneʳ (lemma r) ⟩
      nr₃ r 𝟙 p · (n₁ + n₂) + nr₃ r (z₁ + z₂) (s₁ + s₂)               ≡⟨⟩
      nr p r (z₁ + z₂) (s₁ + s₂) (n₁ + n₂)                            ∎
      where
      open Tools.Reasoning.PartialOrder ≤-poset
      lemma′ : ∞ · (z₁ + s₁) + ∞ · (z₂ + s₂) ≤ ∞ · ((z₁ + z₂) + (s₁ + s₂))
      lemma′ = begin
        ∞ · (z₁ + s₁) + ∞ · (z₂ + s₂) ≡˘⟨ ·-distribˡ-+ _ _ _ ⟩
        ∞ · ((z₁ + s₁) + (z₂ + s₂))   ≡⟨ ·-congˡ (+-assoc _ _ _) ⟩
        ∞ · (z₁ + s₁ + z₂ + s₂)       ≡˘⟨ ·-congˡ (+-congˡ (+-assoc _ _ _)) ⟩
        ∞ · (z₁ + (s₁ + z₂) + s₂)     ≡⟨ ·-congˡ (+-congˡ (+-congʳ (+-comm _ _))) ⟩
        ∞ · (z₁ + (z₂ + s₁) + s₂)     ≡⟨ ·-congˡ (+-congˡ (+-assoc _ _ _)) ⟩
        ∞ · (z₁ + z₂ + s₁ + s₂)       ≡˘⟨ ·-congˡ (+-assoc _ _ _) ⟩
        ∞ · ((z₁ + z₂) + (s₁ + s₂))   ∎
      lemma : ∀ r → nr₃ r z₁ s₁ + nr₃ r z₂ s₂ ≤ nr₃ r (z₁ + z₂) (s₁ + s₂)
      lemma ⌞ 0 ⌟ = +-sub-interchangeable-∧ z₁ s₁ z₂ s₂
      lemma ⌞ 1 ⌟ = begin
        (z₁ + ∞ · s₁) + z₂ + ∞ · s₂ ≡⟨ +-assoc _ _ _ ⟩
        z₁ + ∞ · s₁ + z₂ + ∞ · s₂   ≡˘⟨ +-congˡ (+-assoc _ _ _) ⟩
        z₁ + (∞ · s₁ + z₂) + ∞ · s₂ ≡⟨ +-congˡ (+-congʳ (+-comm _ _)) ⟩
        z₁ + (z₂ + ∞ · s₁) + ∞ · s₂ ≡⟨ +-congˡ (+-assoc _ _ _) ⟩
        z₁ + z₂ + ∞ · s₁ + ∞ · s₂   ≡˘⟨ +-assoc _ _ _ ⟩
        (z₁ + z₂) + ∞ · s₁ + ∞ · s₂ ≡˘⟨ +-congˡ (·-distribˡ-+ _ _ _) ⟩
        (z₁ + z₂) + ∞ · (s₁ + s₂)   ∎
      lemma ⌞ 2+ _ ⌟ = lemma′
      lemma ∞        = lemma′

    nr-𝟘 : ∀ p r → nr p r 𝟘 𝟘 𝟘 ≡ 𝟘
    nr-𝟘 p r = begin
      nr p r 𝟘 𝟘 𝟘 ≡⟨⟩
      nr₃ r 𝟙 p · 𝟘 + nr₃ r 𝟘 𝟘 ≡⟨ +-congʳ (·-zeroʳ _) ⟩
      𝟘 + nr₃ r 𝟘 𝟘 ≡⟨ +-identityˡ _ ⟩
      nr₃ r 𝟘 𝟘 ≡⟨ lemma r ⟩
      𝟘 ∎
      where
      open Tools.Reasoning.PropositionalEquality
      lemma : ∀ r → nr₃ r 𝟘 𝟘 ≡ 𝟘
      lemma ⌞ 0 ⌟    = ∧-idem 𝟘
      lemma ⌞ 1 ⌟    = refl
      lemma ⌞ 2+ _ ⌟ = refl
      lemma ∞        = refl

    nr-positive : ∀ {p r z s n} → nr p r z s n ≡ 𝟘 → z ≡ 𝟘 × s ≡ 𝟘 × n ≡ 𝟘
    nr-positive {r = r} nr≡𝟘 =
      case +-positive nr≡𝟘 of λ
        (x , y) →
      case lemma r y of λ
        (z≡𝟘 , s≡𝟘) →
      case zero-product x of λ where
        (inj₁ nr₂≡𝟘) →
          case lemma r nr₂≡𝟘 .proj₁ of λ ()
        (inj₂ n≡𝟘) →
          z≡𝟘 , s≡𝟘 , n≡𝟘
      where
      lemma : ∀ {z s} r → nr₃ r z s ≡ 𝟘 → z ≡ 𝟘 × s ≡ 𝟘
      lemma ⌞ 0 ⌟ = ∧-positive
      lemma ⌞ 1 ⌟ nr≡𝟘 =
        case +-positive nr≡𝟘 of λ
          (z≡𝟘 , ∞s≡𝟘) →
        case zero-product ∞s≡𝟘 of λ where
          (inj₁ ())
          (inj₂ s≡𝟘) → z≡𝟘 , s≡𝟘
      lemma ∞ nr≡𝟘 =
        case zero-product nr≡𝟘 of λ where
          (inj₁ ())
          (inj₂ z+s≡𝟘) → +-positive z+s≡𝟘
      lemma ⌞ 2+ _ ⌟ nr≡𝟘 =
        case zero-product nr≡𝟘 of λ where
          (inj₁ ())
          (inj₂ z+s≡𝟘) → +-positive z+s≡𝟘

    nr-zero : ∀ p r z s n → n ≤ 𝟘 → nr p r z s n ≤ z
    nr-zero p r z s n n≤𝟘 = begin
      nr p r z s n              ≡⟨⟩
      nr₃ r 𝟙 p · n + nr₃ r z s ≤⟨ +-monotoneˡ (·-monotoneʳ n≤𝟘) ⟩
      nr₃ r 𝟙 p · 𝟘 + nr₃ r z s ≡⟨ +-congʳ (·-zeroʳ _) ⟩
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
      nr p r z s n                                      ≡⟨⟩
      nr₃ r 𝟙 p · n + nr₃ r z s                         ≤⟨ +-monotone (·-monotoneˡ (lemma r 𝟙 p)) (lemma r z s) ⟩
      (p + r · nr₃ r 𝟙 p) · n + s + r · nr₃ r z s       ≡⟨ +-congʳ (·-distribʳ-+ _ _ _) ⟩
      (p · n + (r · nr₃ r 𝟙 p) · n) + s + r · nr₃ r z s ≡⟨ +-congʳ (+-congˡ (·-assoc _ _ _)) ⟩
      (p · n + r · nr₃ r 𝟙 p · n) + s + r · nr₃ r z s   ≡⟨ +-assoc _ _ _ ⟩
      p · n + r · nr₃ r 𝟙 p · n + s + r · nr₃ r z s     ≡˘⟨ +-congˡ (+-assoc _ _ _) ⟩
      p · n + (r · nr₃ r 𝟙 p · n + s) + r · nr₃ r z s   ≡⟨ +-congˡ (+-congʳ (+-comm _ _)) ⟩
      p · n + (s + r · nr₃ r 𝟙 p · n) + r · nr₃ r z s   ≡⟨ +-congˡ (+-assoc _ _ _) ⟩
      p · n + s + r · nr₃ r 𝟙 p · n + r · nr₃ r z s     ≡˘⟨ +-assoc _ _ _ ⟩
      (p · n + s) + r · nr₃ r 𝟙 p · n + r · nr₃ r z s   ≡˘⟨ +-cong (+-comm _ _) (·-distribˡ-+ _ _ _) ⟩
      (s + p · n) + r · (nr₃ r 𝟙 p · n + nr₃ r z s)     ≡⟨ +-assoc _ _ _ ⟩
      s + p · n + r · (nr₃ r 𝟙 p · n + nr₃ r z s)       ≡⟨⟩
      s + p · n + r · nr p r z s n ∎
      where
      open Tools.Reasoning.PartialOrder ≤-poset
      lemma′ : ∀ p q → ∞ · (p + q) ≤ q + ∞ · (p + q)
      lemma′ p ⌞ Nat.zero ⌟ = ≤-reflexive (sym (+-identityˡ _))
      lemma′ ⌞ Nat.zero ⌟ ⌞ 1+ x ⌟ = ≤-refl
      lemma′ ⌞ 1+ x₁ ⌟ ⌞ 1+ x ⌟ = ≤-refl
      lemma′ ∞ ⌞ 1+ x ⌟ = ≤-refl
      lemma′ p ∞ rewrite +-comm p ∞ = ≤-refl
      lemma : ∀ r p q → nr₃ r p q ≤ q + r · nr₃ r p q
      lemma ⌞ 0 ⌟ p q rewrite +-identityʳ q = ∧-decreasingʳ _ _
      lemma ⌞ 1 ⌟ p ⌞ 0 ⌟ = ≤-reflexive (sym (trans (+-identityˡ _) (·-identityˡ _)))
      lemma ⌞ 1 ⌟ p ⌞ 1+ x ⌟ rewrite +-comm p ∞ = ≤-refl
      lemma ⌞ 1 ⌟ p ∞ rewrite +-comm p ∞ = ≤-refl
      lemma ⌞ 2+ n ⌟ p q = begin
        ∞ · (p + q) ≤⟨ lemma′ p q ⟩
        q + ∞ · (p + q) ≡⟨ +-congˡ (·-congʳ (·-comm ∞ ⌞ 2+ n ⌟)) ⟩
        q + (⌞ 2+ n ⌟ · ∞) · (p + q) ≡⟨ +-congˡ (·-assoc _ _ _) ⟩
        q + ⌞ 2+ n ⌟ · ∞ · (p + q) ∎
      lemma ∞ p q = begin
        ∞ · (p + q) ≤⟨ lemma′ p q ⟩
        q + ∞ · (p + q) ≡⟨⟩
        q + (∞ · ∞) · (p + q) ≡⟨ +-congˡ (·-assoc _ _ _) ⟩
        q + ∞ · ∞ · (p + q) ∎

-- A modality (of any kind) for ℕ⊎∞ defined using the nr function

ℕ⊎∞-modality : Modality-variant → Modality
ℕ⊎∞-modality variant = record
  { variant = variant
  ; semiring-with-meet = ℕ⊎∞-semiring-with-meet
  ; 𝟘-well-behaved = λ _ → ℕ⊎∞-has-well-behaved-zero
  ; has-nr = λ _ → ℕ⊎∞-has-nr
  }

------------------------------------------------------------------------
-- Instances of Full-reduction-assumptions

-- Instances of Type-restrictions (ℕ⊎∞-modality variant) and
-- Usage-restrictions (ℕ⊎∞-modality variant) are suitable for the full
-- reduction theorem if
-- * whenever Σˢ-allowed m n holds, then m is ⌞ 1 ⌟, or the affine
--   ordering is used, m is ⌞ 0 ⌟, and 𝟘ᵐ is allowed, and
-- * if the "exact" ordering is used, then strong unit types are
--   allowed to be used as sinks (if such types are allowed), and
--   η-equality is not allowed for weak unit types (if such types are
--   allowed).

Suitable-for-full-reduction :
  ∀ variant → Type-restrictions (ℕ⊎∞-modality variant) →
  Usage-restrictions (ℕ⊎∞-modality variant) → Set
Suitable-for-full-reduction variant TRs URs =
  (∀ m n → Σˢ-allowed m n →
   m ≡ ⌞ 1 ⌟ ⊎ T affine × m ≡ ⌞ 0 ⌟ × T 𝟘ᵐ-allowed) ×
  (¬ T affine →
   (Unitˢ-allowed → Starˢ-sink) ×
   (Unitʷ-allowed → ¬ Unitʷ-η))
  where
  open Modality-variant variant
  open Type-restrictions TRs
  open Usage-restrictions URs

-- Given instances of Type-restrictions (ℕ⊎∞-modality variant) and
-- Usage-restrictions (ℕ⊎∞-modality variant) one can create
-- "suitable" instances.

suitable-for-full-reduction :
  Type-restrictions (ℕ⊎∞-modality variant) →
  Usage-restrictions (ℕ⊎∞-modality variant) →
  ∃₂ (Suitable-for-full-reduction variant)
suitable-for-full-reduction {variant} TRs URs =
    record TRs
      { Unit-allowed = λ s →
          Unit-allowed s ×
          (¬ T affine → s ≡ 𝕨 → ¬ Unitʷ-η)
      ; ΠΣ-allowed = λ b m n →
          ΠΣ-allowed b m n ×
          (b ≡ BMΣ 𝕤 → m ≡ ⌞ 1 ⌟ ⊎ T affine × m ≡ ⌞ 0 ⌟ × T 𝟘ᵐ-allowed)
      ; []-cong-allowed = λ s →
          []-cong-allowed s ×
          (T affine → T 𝟘ᵐ-allowed) ×
          (¬ T affine → s ≢ 𝕤 × (s ≡ 𝕨 → ¬ Unitʷ-η))
      ; []-cong→Erased = λ (ok , hyp₁ , hyp₂) →
          let ok₁ , ok₂ = []-cong→Erased ok in
            (ok₁ , proj₂ ∘→ hyp₂)
          , ok₂
          , (case PE.singleton affine of λ where
               (true  , refl) _    → inj₂ (_ , refl , hyp₁ _)
               (false , refl) refl → ⊥-elim (hyp₂ idᶠ .proj₁ refl))
      ; []-cong→¬Trivial = λ _ ()
      }
  , record URs { starˢ-sink = not affine ∨ starˢ-sink }
  , (λ _ _ (_ , hyp) → hyp refl)
  , (λ not-affine →
         (λ (_ , hyp) → case PE.singleton affine of λ where
            (true  , refl) → ⊥-elim (not-affine _)
            (false , refl) → _)
       , (λ (_ , hyp) → hyp not-affine refl))
  where
  open Modality-variant variant
  open Type-restrictions TRs
  open Usage-restrictions URs

-- The full reduction assumptions hold for ℕ⊎∞-modality variant and
-- any "suitable" instance of Type-restrictions.

full-reduction-assumptions :
  Suitable-for-full-reduction variant TRs URs →
  Full-reduction-assumptions TRs URs
full-reduction-assumptions (hyp₁ , hyp₂) =
  case PE.singleton affine of λ where
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
  Suitable-for-full-reduction variant TRs URs
full-reduction-assumptions-suitable as =
  case PE.singleton affine of λ where
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
  open Full-reduction-assumptions as

------------------------------------------------------------------------
-- Subtraction

open Graded.Modality.Properties.Subtraction ℕ⊎∞-semiring-with-meet

opaque

  -- Subtraction of ⌞ m ⌟ by ∞ is not possible

  ⌞m⌟-∞≰ : ∀ {m p} → ⌞ m ⌟ - ∞ ≤ p → ⊥
  ⌞m⌟-∞≰ {p = ⌞ m ⌟} x = ≰∞ x
  ⌞m⌟-∞≰ {p = ∞} x = ≰∞ x

opaque

  -- Subtraction of ⌞ m ⌟ by ⌞ n ⌟ is only possible if n ≤ m

  ⌞m⌟-⌞n⌟≤ : ∀ {m n} → ⌞ m ⌟ - ⌞ n ⌟ ≤ o → n N.≤ m
  ⌞m⌟-⌞n⌟≤ {⌞ o ⌟} {m} {n} m≤o+n = lemma affine refl
    where
    lemma : ∀ b → b ≡ affine → n N.≤ m
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
  m-n≡ m n n≤m = lemma affine refl
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
      lemma₂ m n k (N.+1-injective x)

    lemma₃ : ∀ k → ⌞ m ⌟ ≤ₑ ⌞ k N.+ n ⌟ → ⌞ m N.∸ n ⌟ ≤ₑ ⌞ k ⌟
    lemma₃ k m≤ with m N.∸ n N.≟ k
    … | yes _ = refl
    … | no m-n≢k with m N.≟ k N.+ n
    … | yes refl = ⊥-elim (m-n≢k (N.m+n∸n≡m k n))
    lemma₃ k () | no _ | no _

    lemma : ∀ b → b ≡ affine → ⌞ m ⌟ - ⌞ n ⌟ ≡ ⌞ m N.∸ n ⌟
    lemma false refl with m N.≟ m N.∸ n N.+ n
    … | yes _ = refl , λ { ⌞ k ⌟ x → lemma₃ k x}
    … | no m≢m-n+n = ⊥-elim (m≢m-n+n (sym (N.m∸n+n≡m n≤m)))
    lemma true refl =
      cong ⌞_⌟ (lemma₁ m n n≤m) , λ { ⌞ k ⌟ x → cong ⌞_⌟ (lemma₂ m n k (⌞⌟-injective x))}

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
