------------------------------------------------------------------------
-- A modality with simultaneous support for "exact" or "at most" usage
-- counting.
--
-- This generalizes the two ℕ⊎∞ instances in a similar way that
-- Linear-or-affine generalizes the Linearity and Affine instances.
------------------------------------------------------------------------

module Graded.Modality.Instances.Exact-or-at-most where

open import Tools.Nat using (Nat; 1+; _*_; _⊔_) renaming (_+_ to _+ⁿ_)
import Tools.Nat as N
open import Tools.Bool using (Bool; true; false)
import Tools.Bool as B
open import Tools.Empty
open import Tools.Function
open import Tools.Level using (ℓ₀)
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
import Tools.Reasoning.PropositionalEquality as RPe
import Tools.Reasoning.PartialOrder as RPo
open import Tools.Sum

open import Definition.Untyped.NotParametrised
import Definition.Typed.Restrictions
import Graded.Usage.Restrictions
import Graded.FullReduction.Assumptions

import Graded.Modality.Properties.Addition
import Graded.Modality.Properties.Has-well-behaved-zero
import Graded.Modality.Properties.Meet
import Graded.Modality.Properties.Multiplication
import Graded.Modality.Properties.Natrec
import Graded.Modality.Properties.PartialOrder
import Graded.Mode.Instances.Zero-one.Variant
import Graded.Mode.Instances.Zero-one

infixr 40 _+_
infixr 43 _∧_
infixr 45 _·_

-- The grade ≈/≤1+ b m represents 1+ m uses
-- If b is true, this means exactly 1+ m uses.
-- If b is false, this means at most 1+ m uses.

data Exact-or-at-most : Set where
  𝟘 : Exact-or-at-most
  ≈/≤1+ : (b : Bool) (m : Nat) → Exact-or-at-most
  ∞ : Exact-or-at-most

-- ≈1+ m represents exactly 1+ m uses.
-- ≤1+ m represents at most 1+ m uses.

pattern ≈1+ m = ≈/≤1+ true m
pattern ≤1+ m = ≈/≤1+ false m
pattern 𝟙 = ≈1+ 0
pattern ≤𝟙 = ≤1+ 0

open import Tools.Algebra Exact-or-at-most
open import Graded.Modality Exact-or-at-most

private variable
  p q r z z₁ z₂ s s₁ s₂ n n₁ n₂ : Exact-or-at-most
  k m : Nat
  b b′ : Bool

opaque

  -- Decidable equality

  _≟_ : (p q : Exact-or-at-most) → Dec (p ≡ q)
  𝟘 ≟ 𝟘 = yes refl
  𝟘 ≟ ≈/≤1+ _ _ = no λ ()
  𝟘 ≟ ∞ = no λ ()
  ≈/≤1+ _ _ ≟ 𝟘 = no λ ()
  ≤1+ m ≟ ≤1+ n =
    case m N.≟ n of λ where
      (yes refl) → yes refl
      (no m≢n) → no λ { refl → m≢n refl }
  ≈1+ m ≟ ≈1+ n =
    case m N.≟ n of λ where
      (yes refl) → yes refl
      (no m≢n) → no λ { refl → m≢n refl }
  ≤1+ m ≟ ≈1+ n = no λ ()
  ≈1+ m ≟ ≤1+ n = no λ ()
  ≈/≤1+ b m ≟ ∞ = no λ ()
  ∞ ≟ 𝟘 = no λ ()
  ∞ ≟ ≈/≤1+ b m = no λ ()
  ∞ ≟ ∞ = yes refl

opaque

  -- Injectivity of ≈/≤1+_

  ≈/≤1+-injective : ≈/≤1+ b m ≡ ≈/≤1+ b′ k → b ≡ b′ × m ≡ k
  ≈/≤1+-injective refl = refl , refl

--------------
-- Addition --
--------------

-- Adding two usage counts together gives an exact count iff
-- the usage counts of both arguments were exact.

_+_ : Op₂ Exact-or-at-most
𝟘 + q = q
≈/≤1+ b m + 𝟘 = ≈/≤1+ b m
≈/≤1+ b m + ≈/≤1+ b′ m′ = ≈/≤1+ (b B.∧ b′) (1+ m +ⁿ m′)
≈/≤1+ b m + ∞ = ∞
∞ + q = ∞

opaque

  -- ∞ is a right zero for addition

  +-zeroʳ : RightZero ∞ _+_
  +-zeroʳ 𝟘 = refl
  +-zeroʳ (≈/≤1+ b m) = refl
  +-zeroʳ ∞ = refl

opaque

  +-zero : Zero ∞ _+_
  +-zero = (λ _ → refl) , +-zeroʳ

--------------------
-- Multiplication --
--------------------

-- Multiplying two usage counts together gives an exact count iff
-- the usage counts of both arguments were exact.

_·_ : Op₂ Exact-or-at-most
𝟘 · q = 𝟘
≈/≤1+ b m · 𝟘 = 𝟘
≈/≤1+ b m · ≈/≤1+ b₁ m₁ = ≈/≤1+ (b B.∧ b₁) (m * m₁ +ⁿ m +ⁿ m₁)
≈/≤1+ b m · ∞ = ∞
∞ · 𝟘 = 𝟘
∞ · ≈/≤1+ b m = ∞
∞ · ∞ = ∞

opaque

  -- Multiplication is commutative

  ·-comm : Commutative _·_
  ·-comm 𝟘 𝟘 = refl
  ·-comm 𝟘 (≈/≤1+ b m) = refl
  ·-comm 𝟘 ∞ = refl
  ·-comm (≈/≤1+ b m) 𝟘 = refl
  ·-comm (≈/≤1+ b m) (≈/≤1+ b₁ m₁) =
    cong₂ ≈/≤1+ (B.∧-comm b b₁) (lemma m m₁)
    where
    open RPe
    lemma : ∀ p q → p * q +ⁿ p +ⁿ q ≡ q * p +ⁿ q +ⁿ p
    lemma p q = begin
      p * q +ⁿ p +ⁿ q   ≡⟨ N.+-assoc (p * q) p q ⟩
      p * q +ⁿ (p +ⁿ q) ≡⟨ cong₂ _+ⁿ_ (N.*-comm p q) (N.+-comm p q) ⟩
      q * p +ⁿ (q +ⁿ p) ≡˘⟨ N.+-assoc (q * p) q p ⟩
      q * p +ⁿ q +ⁿ p   ∎
  ·-comm (≈/≤1+ b m) ∞ = refl
  ·-comm ∞ 𝟘 = refl
  ·-comm ∞ (≈/≤1+ b m) = refl
  ·-comm ∞ ∞ = refl

opaque

  -- If p is not 𝟘, then p · ∞ is equal to ∞.

  ≢𝟘·∞ : p ≢ 𝟘 → p · ∞ ≡ ∞
  ≢𝟘·∞ {(𝟘)} p≢𝟘 = ⊥-elim (p≢𝟘 refl)
  ≢𝟘·∞ {≈/≤1+ b m} _ = refl
  ≢𝟘·∞ {(∞)} _ = refl

opaque

  -- If p is not 𝟘, then ∞ · ∞ is equal to ∞.

  ∞·≢𝟘 : p ≢ 𝟘 → ∞ · p ≡ ∞
  ∞·≢𝟘 {(𝟘)} p≢𝟘 = ⊥-elim (p≢𝟘 refl)
  ∞·≢𝟘 {≈/≤1+ b m} _ = refl
  ∞·≢𝟘 {(∞)} _ = refl

----------
-- Meet --
----------

-- The meet of two usage counts together gives an exact count iff
-- the usage counts of both arguments were exact and equal.
-- Otherwise, it gives at most the maximum of the two arguments.

_∧_ : Op₂ Exact-or-at-most
𝟘 ∧ 𝟘 = 𝟘
𝟘 ∧ ≈/≤1+ b m = ≤1+ m
𝟘 ∧ ∞ = ∞
≈/≤1+ b m ∧ 𝟘 = ≤1+ m
≈/≤1+ b m ∧ ≈/≤1+ b₁ m₁ =
  ≈/≤1+ ((b B.∧ b₁) B.∧ (m N.== m₁)) (m ⊔ m₁)
≈/≤1+ b m ∧ ∞ = ∞
∞ ∧ q = ∞

_≤_ : (p q : Exact-or-at-most) → Set
p ≤ q = p ≡ p ∧ q

opaque

  -- A kind of inversion lemma for the ordering relation
  --  If ≈/≤1+ b m ≤ ≈/≤1+ b′ k then b B.≤ᵇ b′ and k N.≤ m

  ≈/≤1+-≤-inv : ≈/≤1+ b m ≤ ≈/≤1+ b′ k → b B.≤ᵇ b′ × k N.≤ m
  ≈/≤1+-≤-inv {b} {m} {b′} {k} x = lemma₁ b b′ x , lemma₂ m k x
    where
    lemma₁ : ∀ b b′ → ≈/≤1+ b m ≤ ≈/≤1+ b′ k → b B.≤ᵇ b′
    lemma₁ false false _  = B.b≤b
    lemma₁ false true  _  = B.f≤t
    lemma₁ true  true  _  = B.b≤b
    lemma₁ true  false ()
    lemma₂ : ∀ m k → ≈/≤1+ b m ≤ ≈/≤1+ b′ k → k N.≤ m
    lemma₂ m 0 x = N.z≤n
    lemma₂ m (1+ k) x =
      case ≈/≤1+-injective x of λ
        (_ , m≡) →
      N.m⊔n≡m⇒n≤m (sym m≡)

------------------------------------------------------------------------
-- The modality

-- A modality instance for Exact-or-at-most.

exact-or-at-most-modality : Modality
exact-or-at-most-modality = record
  { _+_ = _+_
  ; _·_ = _·_
  ; _∧_ = _∧_
  ; 𝟘 = 𝟘
  ; 𝟙 = 𝟙
  ; ω = ∞
  ; +-·-Semiring = record
    { isSemiringWithoutAnnihilatingZero = record
      { +-isCommutativeMonoid = record
        { isMonoid = record
          { isSemigroup = record
            { isMagma = record
              { isEquivalence = isEquivalence
              ; ∙-cong = cong₂ _+_
              }
            ; assoc = +-assoc
            }
          ; identity = (λ _ → refl) , (comm∧idˡ⇒idʳ +-comm λ _ → refl)
          }
        ; comm = +-comm
        }
      ; *-cong = cong₂ _·_
      ; *-assoc = ·-assoc
      ; *-identity = ·-identityˡ , comm∧idˡ⇒idʳ ·-comm ·-identityˡ
      ; distrib = ·-distribˡ-+ , (comm∧distrˡ⇒distrʳ ·-comm ·-distribˡ-+)
      }
    ; zero = (λ _ → refl) , (comm∧zeˡ⇒zeʳ ·-comm (λ _ → refl))
    }
  ; ∧-Semilattice = record
    { isBand = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = isEquivalence
          ; ∙-cong = cong₂ _∧_
          }
        ; assoc = ∧-assoc
        }
      ; idem = ∧-idem
      }
    ; comm = ∧-comm
    }
  ; ·-distrib-∧ = ·-distribˡ-∧ , (comm∧distrˡ⇒distrʳ ·-comm ·-distribˡ-∧)
  ; +-distrib-∧ = +-distribˡ-∧ , (comm∧distrˡ⇒distrʳ +-comm +-distribˡ-∧)
  ; ω≤𝟙 = refl
  ; ω·+≤ω·ʳ = ω·+≤ω·ʳ
  ; is-𝟘? = λ p → p ≟ 𝟘
  }
  where
  +-assoc : Associative _+_
  +-assoc 𝟘 q r = refl
  +-assoc (≈/≤1+ b m) 𝟘 r = refl
  +-assoc (≈/≤1+ b m) (≈/≤1+ b₁ m₁) 𝟘 = refl
  +-assoc (≈/≤1+ b m) (≈/≤1+ b₁ m₁) (≈/≤1+ b₂ m₂) =
    cong₂ ≈/≤1+ (B.∧-assoc b b₁ b₂)
      (trans (cong (λ x → 1+ x +ⁿ m₂) (sym (N.+-suc m m₁)))
        (N.+-assoc (1+ m) (1+ m₁) m₂))
  +-assoc (≈/≤1+ b m) (≈/≤1+ b₁ m₁) ∞ = refl
  +-assoc (≈/≤1+ b m) ∞ r = refl
  +-assoc ∞ q r = refl

  +-comm : Commutative _+_
  +-comm 𝟘 𝟘 = refl
  +-comm 𝟘 (≈/≤1+ b m) = refl
  +-comm 𝟘 ∞ = refl
  +-comm (≈/≤1+ b m) 𝟘 = refl
  +-comm (≈/≤1+ b m) (≈/≤1+ b₁ m₁) =
    cong₂ ≈/≤1+ (B.∧-comm b b₁) (cong 1+ (N.+-comm m m₁))
  +-comm (≈/≤1+ b m) ∞ = refl
  +-comm ∞ 𝟘 = refl
  +-comm ∞ (≈/≤1+ b m) = refl
  +-comm ∞ ∞ = refl

  ·-assoc : Associative _·_
  ·-assoc 𝟘 q r = refl
  ·-assoc (≈/≤1+ b m) 𝟘 r = refl
  ·-assoc (≈/≤1+ b m) (≈/≤1+ b₁ m₁) 𝟘 = refl
  ·-assoc (≈/≤1+ b m) (≈/≤1+ b₁ m₁) ∞ = refl
  ·-assoc (≈/≤1+ b m) ∞ 𝟘 = refl
  ·-assoc (≈/≤1+ b m) ∞ (≈/≤1+ b₁ m₁) = refl
  ·-assoc (≈/≤1+ b m) ∞ ∞ = refl
  ·-assoc ∞ 𝟘 r = refl
  ·-assoc ∞ (≈/≤1+ b m) 𝟘 = refl
  ·-assoc ∞ (≈/≤1+ b m) (≈/≤1+ b₁ m₁) = refl
  ·-assoc ∞ (≈/≤1+ b m) ∞ = refl
  ·-assoc ∞ ∞ 𝟘 = refl
  ·-assoc ∞ ∞ (≈/≤1+ b m) = refl
  ·-assoc ∞ ∞ ∞ = refl
  ·-assoc (≈/≤1+ b m) (≈/≤1+ b₁ m₁) (≈/≤1+ b₂ m₂) =
    cong₂ ≈/≤1+ (B.∧-assoc b b₁ b₂) (lemma m m₁ m₂)
    where
    open RPe
    lemma : ∀ p q r → (p * q +ⁿ p +ⁿ q) * r +ⁿ (p * q +ⁿ p +ⁿ q) +ⁿ r ≡
                               p * (q * r +ⁿ q +ⁿ r) +ⁿ p +ⁿ (q * r +ⁿ q +ⁿ r)
    lemma p q r = begin
      (p * q +ⁿ p +ⁿ q) * r +ⁿ (p * q +ⁿ p +ⁿ q) +ⁿ r
        ≡⟨ cong (λ x → x +ⁿ (p * q +ⁿ p +ⁿ q) +ⁿ r) (N.*-distribʳ-+ r (p * q +ⁿ p) q ) ⟩
      ((p * q +ⁿ p) * r +ⁿ q * r) +ⁿ (p * q +ⁿ p +ⁿ q) +ⁿ r
        ≡⟨ cong (λ x → (x +ⁿ q * r) +ⁿ (p * q +ⁿ p +ⁿ q) +ⁿ r) (N.*-distribʳ-+ r (p * q) p) ⟩
      ((p * q) * r +ⁿ p * r +ⁿ q * r) +ⁿ (p * q +ⁿ p +ⁿ q) +ⁿ r
        ≡⟨ cong₂ (λ x y → x +ⁿ p * r +ⁿ q * r +ⁿ y +ⁿ r) (N.*-assoc p q r) (N.+-assoc (p * q) p q) ⟩
      (p * (q * r) +ⁿ p * r +ⁿ q * r) +ⁿ (p * q +ⁿ (p +ⁿ q)) +ⁿ r
        ≡˘⟨ cong (_+ⁿ r) (N.+-assoc (p * (q * r) +ⁿ p * r +ⁿ q * r) (p * q) (p +ⁿ q) ) ⟩
      ((p * (q * r) +ⁿ p * r +ⁿ q * r) +ⁿ p * q) +ⁿ (p +ⁿ q) +ⁿ r
        ≡⟨ cong (λ x → x +ⁿ (p +ⁿ q) +ⁿ r) (N.+-assoc (p * (q * r) +ⁿ p * r) (q * r) (p * q) ) ⟩
      ((p * (q * r) +ⁿ p * r) +ⁿ (q * r +ⁿ p * q)) +ⁿ (p +ⁿ q) +ⁿ r
        ≡⟨ cong (λ x → (p * (q * r) +ⁿ p * r) +ⁿ x +ⁿ (p +ⁿ q) +ⁿ r) (N.+-comm (q * r) (p * q)) ⟩
      ((p * (q * r) +ⁿ p * r) +ⁿ (p * q +ⁿ q * r)) +ⁿ (p +ⁿ q) +ⁿ r
        ≡˘⟨ cong (λ x → x +ⁿ (p +ⁿ q) +ⁿ r) (N.+-assoc (p * (q * r) +ⁿ p * r) (p * q) (q * r) ) ⟩
      (p * (q * r) +ⁿ p * r +ⁿ p * q) +ⁿ q * r +ⁿ (p +ⁿ q) +ⁿ r
        ≡⟨ cong (λ x → x +ⁿ q * r +ⁿ (p +ⁿ q) +ⁿ r) (N.+-assoc (p * (q * r)) (p * r) (p * q)) ⟩
      p * (q * r) +ⁿ (p * r +ⁿ p * q) +ⁿ q * r +ⁿ (p +ⁿ q) +ⁿ r
        ≡⟨ cong (_+ⁿ r) (N.+-assoc (p * (q * r) +ⁿ (p * r +ⁿ p * q)) (q * r) (p +ⁿ q)) ⟩
      p * (q * r) +ⁿ (p * r +ⁿ p * q) +ⁿ (q * r +ⁿ (p +ⁿ q)) +ⁿ r
        ≡˘⟨ cong₂ (λ x y → (p * (q * r) +ⁿ x) +ⁿ y +ⁿ r) (N.+-comm (p * q) (p * r)) (N.+-assoc (q * r) p q ) ⟩
      p * (q * r) +ⁿ (p * q +ⁿ p * r) +ⁿ ((q * r +ⁿ p) +ⁿ q) +ⁿ r
        ≡˘⟨ cong₂ (λ x y → x +ⁿ (y +ⁿ q) +ⁿ r) (N.+-assoc (p * (q * r)) (p * q) (p * r)) (N.+-comm p (q * r)) ⟩
      (p * (q * r) +ⁿ p * q +ⁿ p * r) +ⁿ (p +ⁿ q * r +ⁿ q) +ⁿ r
        ≡⟨ cong (λ x → p * (q * r) +ⁿ p * q +ⁿ p * r +ⁿ x +ⁿ r) (N.+-assoc p (q * r) q) ⟩
      (p * (q * r) +ⁿ p * q +ⁿ p * r) +ⁿ (p +ⁿ (q * r +ⁿ q)) +ⁿ r
        ≡˘⟨ cong (_+ⁿ r) (N.+-assoc (p * (q * r) +ⁿ p * q +ⁿ p * r) p (q * r +ⁿ q)) ⟩
      (p * (q * r) +ⁿ p * q +ⁿ p * r) +ⁿ p +ⁿ (q * r +ⁿ q) +ⁿ r
        ≡⟨ N.+-assoc (p * (q * r) +ⁿ p * q +ⁿ p * r +ⁿ p) (q * r +ⁿ q) r ⟩
      (p * (q * r) +ⁿ p * q +ⁿ p * r) +ⁿ p +ⁿ (q * r +ⁿ q +ⁿ r)
        ≡˘⟨ cong (λ x → x +ⁿ p * r +ⁿ p +ⁿ (q * r +ⁿ q +ⁿ r)) (N.*-distribˡ-+ p (q * r) q) ⟩
      (p * (q * r +ⁿ q) +ⁿ p * r) +ⁿ p +ⁿ (q * r +ⁿ q +ⁿ r)
        ≡˘⟨ cong (λ x → x +ⁿ p +ⁿ (q * r +ⁿ q +ⁿ r)) (N.*-distribˡ-+ p (q * r +ⁿ q) r) ⟩
      p * (q * r +ⁿ q +ⁿ r) +ⁿ p +ⁿ (q * r +ⁿ q +ⁿ r) ∎

  ·-identityˡ : LeftIdentity 𝟙 _·_
  ·-identityˡ 𝟘 = refl
  ·-identityˡ (≈/≤1+ b m) = refl
  ·-identityˡ ∞ = refl

  ·-distribˡ-+ : _·_ DistributesOverˡ _+_
  ·-distribˡ-+ 𝟘 q r = refl
  ·-distribˡ-+ (≈/≤1+ b m) 𝟘 r = refl
  ·-distribˡ-+ (≈/≤1+ b m) (≈/≤1+ b₁ m₁) 𝟘 = refl
  ·-distribˡ-+ (≈/≤1+ b m) (≈/≤1+ b₁ m₁) ∞ = refl
  ·-distribˡ-+ (≈/≤1+ b m) ∞ r = refl
  ·-distribˡ-+ ∞ 𝟘 r = refl
  ·-distribˡ-+ ∞ (≈/≤1+ b m) 𝟘 = refl
  ·-distribˡ-+ ∞ (≈/≤1+ b m) (≈/≤1+ b₁ m₁) = refl
  ·-distribˡ-+ ∞ (≈/≤1+ b m) ∞ = refl
  ·-distribˡ-+ ∞ ∞ r = refl
  ·-distribˡ-+ (≈/≤1+ b m) (≈/≤1+ b₁ m₁) (≈/≤1+ b₂ m₂) =
    cong₂ ≈/≤1+ (lemma b b₁ b₂) (lemma′ m m₁ m₂)
    where
    open RPe
    lemma : ∀ b b₁ b₂ → b B.∧ b₁ B.∧ b₂ ≡ (b B.∧ b₁) B.∧ b B.∧ b₂
    lemma b b₁ b₂ = begin
      b B.∧ b₁ B.∧ b₂           ≡˘⟨ cong (B._∧ _) (B.∧-idem b) ⟩
      (b B.∧ b) B.∧ b₁ B.∧ b₂   ≡˘⟨ B.∧-assoc _ b₁ b₂ ⟩
      ((b B.∧ b) B.∧ b₁) B.∧ b₂ ≡⟨ cong (B._∧ b₂) (B.∧-assoc b b b₁) ⟩
      (b B.∧ b B.∧ b₁) B.∧ b₂   ≡⟨ cong (λ x → (b B.∧ x) B.∧ b₂) (B.∧-comm b b₁) ⟩
      (b B.∧ b₁ B.∧ b) B.∧ b₂   ≡˘⟨ cong (B._∧ b₂) (B.∧-assoc b b₁ b) ⟩
      ((b B.∧ b₁) B.∧ b) B.∧ b₂ ≡⟨ B.∧-assoc _ b b₂ ⟩
      (b B.∧ b₁) B.∧ b B.∧ b₂   ∎
    lemma′ : ∀ m n k
           → m * (1+ n +ⁿ k) +ⁿ m +ⁿ (1+ n +ⁿ k)
           ≡ 1+ (m * n +ⁿ m +ⁿ n +ⁿ (m * k +ⁿ m +ⁿ k))
    lemma′ m n k = begin
      m * (1+ n +ⁿ k) +ⁿ m +ⁿ (1+ n +ⁿ k)         ≡⟨ cong (λ x → x +ⁿ m +ⁿ (1+ n +ⁿ k)) (N.*-distribˡ-+ m (1+ n) k) ⟩
      (m * 1+ n +ⁿ m * k) +ⁿ m +ⁿ (1+ n +ⁿ k)     ≡⟨ cong (λ x → (x +ⁿ m * k) +ⁿ m +ⁿ (1+ n +ⁿ k)) (N.*-suc m n) ⟩
      m +ⁿ m * n +ⁿ m * k +ⁿ m +ⁿ (1+ n +ⁿ k)     ≡⟨ cong (λ x → x +ⁿ m * k +ⁿ m +ⁿ (1+ n +ⁿ k)) (N.+-comm m (m * n)) ⟩
      m * n +ⁿ m +ⁿ m * k +ⁿ m +ⁿ (1+ n +ⁿ k)     ≡⟨ N.+-assoc (m * n +ⁿ m +ⁿ m * k) m (1+ n +ⁿ k) ⟩
      m * n +ⁿ m +ⁿ m * k +ⁿ (m +ⁿ (1+ n +ⁿ k))   ≡˘⟨ cong (m * n +ⁿ m +ⁿ m * k +ⁿ_) (N.+-assoc m (1+ n) k) ⟩
      m * n +ⁿ m +ⁿ m * k +ⁿ (m +ⁿ 1+ n +ⁿ k)     ≡⟨ cong (λ x → m * n +ⁿ m +ⁿ m * k +ⁿ (x +ⁿ k)) (N.+-comm m (1+ n)) ⟩
      m * n +ⁿ m +ⁿ m * k +ⁿ (1+ n +ⁿ m +ⁿ k)     ≡⟨ cong (m * n +ⁿ m +ⁿ m * k +ⁿ_) (N.+-assoc (1+ n) m k) ⟩
      m * n +ⁿ m +ⁿ m * k +ⁿ (1+ n +ⁿ (m +ⁿ k))   ≡⟨ N.+-assoc (m * n +ⁿ m) (m * k) (1+ n +ⁿ (m +ⁿ k)) ⟩
      m * n +ⁿ m +ⁿ (m * k +ⁿ (1+ n +ⁿ (m +ⁿ k))) ≡˘⟨ cong (m * n +ⁿ m +ⁿ_) (N.+-assoc (m * k) (1+ n) (m +ⁿ k)) ⟩
      m * n +ⁿ m +ⁿ (m * k +ⁿ 1+ n +ⁿ (m +ⁿ k))   ≡⟨ cong (λ x → m * n +ⁿ m +ⁿ (x +ⁿ (m +ⁿ k))) (N.+-comm (m * k) (1+ n)) ⟩
      m * n +ⁿ m +ⁿ (1+ n +ⁿ m * k +ⁿ (m +ⁿ k))   ≡⟨ cong (m * n +ⁿ m +ⁿ_) (N.+-assoc (1+ n) (m * k) (m +ⁿ k)) ⟩
      m * n +ⁿ m +ⁿ (1+ n +ⁿ (m * k +ⁿ (m +ⁿ k))) ≡˘⟨ cong (λ x → m * n +ⁿ m +ⁿ (1+ n +ⁿ x)) (N.+-assoc (m * k) m k) ⟩
      m * n +ⁿ m +ⁿ (1+ n +ⁿ (m * k +ⁿ m +ⁿ k))   ≡˘⟨ N.+-assoc (m * n +ⁿ m) (1+ n) (m * k +ⁿ m +ⁿ k) ⟩
      m * n +ⁿ m +ⁿ 1+ n +ⁿ (m * k +ⁿ m +ⁿ k)     ≡⟨ cong (_+ⁿ (m * k +ⁿ m +ⁿ k)) (N.+-suc (m * n +ⁿ m) n) ⟩
      1+ (m * n +ⁿ m +ⁿ n +ⁿ (m * k +ⁿ m +ⁿ k))   ∎

  ∧-assoc-lemma : ∀ b b′ → false ≡ (b B.∧ false) B.∧ b′
  ∧-assoc-lemma b b′ = cong (B._∧ b′) (sym (B.∧-zeroʳ b))

  ∧-assoc : Associative _∧_
  ∧-assoc 𝟘 𝟘 𝟘 = refl
  ∧-assoc 𝟘 𝟘 (≈/≤1+ b m) = refl
  ∧-assoc 𝟘 𝟘 ∞ = refl
  ∧-assoc 𝟘 (≈/≤1+ b m) 𝟘 = refl
  ∧-assoc 𝟘 (≈/≤1+ b m) (≈/≤1+ b₁ m₁) = refl
  ∧-assoc 𝟘 (≈/≤1+ b m) ∞ = refl
  ∧-assoc 𝟘 ∞ r = refl
  ∧-assoc (≈/≤1+ b m) 𝟘 𝟘 = refl
  ∧-assoc (≈/≤1+ b m) 𝟘 (≈/≤1+ b₁ m₁) =
    cong (λ x → ≈/≤1+ x _) (∧-assoc-lemma b (m N.== m₁))
  ∧-assoc (≈/≤1+ b m) 𝟘 ∞ = refl
  ∧-assoc (≈/≤1+ b m) (≈/≤1+ b₁ m₁) 𝟘 =
    cong (λ x → ≈/≤1+ x _) (∧-assoc-lemma b (m N.== m₁))
  ∧-assoc (≈/≤1+ b m) (≈/≤1+ b₁ m₁) ∞ = refl
  ∧-assoc (≈/≤1+ b m) ∞ r = refl
  ∧-assoc ∞ q r = refl
  ∧-assoc (≈/≤1+ b m) (≈/≤1+ b₁ m₁) (≈/≤1+ b₂ m₂) =
    flip (cong₂ ≈/≤1+) (N.⊔-assoc m m₁ m₂) (begin
      (((b B.∧ b₁) B.∧ (m N.== m₁)) B.∧ b₂) B.∧ (m ⊔ m₁ N.== m₂)  ≡⟨ cong (B._∧ (m ⊔ m₁ N.== m₂)) (B.∧-assoc (b B.∧ b₁) (m N.== m₁) b₂) ⟩
      ((b B.∧ b₁) B.∧ (m N.== m₁) B.∧ b₂) B.∧ (m ⊔ m₁ N.== m₂)    ≡⟨ cong (λ x → ((b B.∧ b₁) B.∧ x) B.∧ (m ⊔ m₁ N.== m₂)) (B.∧-comm (m N.== m₁) b₂) ⟩
      ((b B.∧ b₁) B.∧ b₂ B.∧ (m N.== m₁)) B.∧ (m ⊔ m₁ N.== m₂)    ≡˘⟨ cong (B._∧ (m ⊔ m₁ N.== m₂)) (B.∧-assoc (b B.∧ b₁) b₂ (m N.== m₁)) ⟩
      (((b B.∧ b₁) B.∧ b₂) B.∧ (m N.== m₁)) B.∧ (m ⊔ m₁ N.== m₂)  ≡⟨ B.∧-assoc ((b B.∧ b₁) B.∧ b₂) (m N.== m₁) (m ⊔ m₁ N.== m₂) ⟩
      ((b B.∧ b₁) B.∧ b₂) B.∧ (m N.== m₁) B.∧ (m ⊔ m₁ N.== m₂)    ≡⟨ cong₂ B._∧_ (B.∧-assoc b b₁ b₂) (lemma m m₁ m₂) ⟩
      (b B.∧ b₁ B.∧ b₂) B.∧ (m₁ N.== m₂) B.∧ (m N.== m₁ ⊔ m₂)     ≡˘⟨ B.∧-assoc (b B.∧ b₁ B.∧ b₂) (m₁ N.== m₂) (m N.== m₁ ⊔ m₂) ⟩
      ((b B.∧ (b₁ B.∧ b₂)) B.∧ (m₁ N.== m₂)) B.∧ (m N.== m₁ ⊔ m₂) ≡⟨ cong (B._∧ (m N.== m₁ ⊔ m₂)) (B.∧-assoc b (b₁ B.∧ b₂) (m₁ N.== m₂)) ⟩
      (b B.∧ (b₁ B.∧ b₂) B.∧ (m₁ N.== m₂)) B.∧ (m N.== m₁ ⊔ m₂)   ∎)
    where
    open RPe
    lemma : ∀ m m₁ m₂ → (m N.== m₁) B.∧ (m ⊔ m₁ N.== m₂) ≡ (m₁ N.== m₂) B.∧ (m N.== m₁ ⊔ m₂)
    lemma 0 0 m₂ = sym (B.∧-idem (0 N.== m₂))
    lemma 0 (1+ m₁) 0 = refl
    lemma 0 (1+ m₁) (1+ m₂) = sym (B.∧-zeroʳ _)
    lemma (1+ m) 0 0 = refl
    lemma (1+ m) 0 (1+ m₂) = refl
    lemma (1+ m) (1+ m₁) 0 = B.∧-zeroʳ _
    lemma (1+ m) (1+ m₁) (1+ m₂) = lemma m m₁ m₂
  ∧-idem : Idempotent _∧_
  ∧-idem 𝟘 = refl
  ∧-idem (≈/≤1+ b m) =
    cong₂ ≈/≤1+ lemma (N.⊔-idem m)
    where
    open RPe
    lemma : (b B.∧ b) B.∧ (m N.== m) ≡ b
    lemma = begin
      (b B.∧ b) B.∧ (m N.== m) ≡⟨ cong₂ B._∧_ (B.∧-idem b) (N.==-refl m) ⟩
      b B.∧ true               ≡⟨ B.∧-identityʳ b ⟩
      b                        ∎
  ∧-idem ∞ = refl

  ∧-comm : Commutative _∧_
  ∧-comm 𝟘 𝟘 = refl
  ∧-comm 𝟘 (≈/≤1+ b m) = refl
  ∧-comm 𝟘 ∞ = refl
  ∧-comm (≈/≤1+ b m) 𝟘 = refl
  ∧-comm (≈/≤1+ b m) (≈/≤1+ b₁ m₁) =
    cong₂ ≈/≤1+ (cong₂ B._∧_ (B.∧-comm b b₁) (N.==-sym m m₁))
      (N.⊔-comm m m₁)
  ∧-comm (≈/≤1+ b m) ∞ = refl
  ∧-comm ∞ 𝟘 = refl
  ∧-comm ∞ (≈/≤1+ b m) = refl
  ∧-comm ∞ ∞ = refl

  ·-distribˡ-∧ : _·_ DistributesOverˡ _∧_
  ·-distribˡ-∧ 𝟘 q r = refl
  ·-distribˡ-∧ (≈/≤1+ b m) 𝟘 𝟘 = refl
  ·-distribˡ-∧ (≈/≤1+ b m) 𝟘 (≈/≤1+ b₁ m₁) =
    cong (λ x → ≈/≤1+ x _) (B.∧-zeroʳ b)
  ·-distribˡ-∧ (≈/≤1+ b m) 𝟘 ∞ = refl
  ·-distribˡ-∧ (≈/≤1+ b m) (≈/≤1+ b₁ m₁) 𝟘 =
    cong (λ x → ≈/≤1+ x _) (B.∧-zeroʳ b)
  ·-distribˡ-∧ (≈/≤1+ b m) (≈/≤1+ b₁ m₁) (≈/≤1+ b₂ m₂) =
    cong₂ ≈/≤1+
      (trans (sym (B.∧-assoc b (b₁ B.∧ b₂) (m₁ N.== m₂))) (cong₂ B._∧_ lemma₁ lemma₂))
      lemma₃
    where
    open RPe
    lemma₁ : b B.∧ (b₁ B.∧ b₂) ≡ (b B.∧ b₁) B.∧ b B.∧ b₂
    lemma₁ = begin
      b B.∧ b₁ B.∧ b₂         ≡˘⟨ cong (B._∧ _) (B.∧-idem b) ⟩
      (b B.∧ b) B.∧ b₁ B.∧ b₂ ≡⟨ B.∧-assoc b b (b₁ B.∧ b₂) ⟩
      b B.∧ b B.∧ b₁ B.∧ b₂   ≡˘⟨ cong (b B.∧_) (B.∧-assoc b b₁ b₂) ⟩
      b B.∧ (b B.∧ b₁) B.∧ b₂ ≡⟨ cong (λ x → b B.∧ x B.∧ b₂) (B.∧-comm b b₁) ⟩
      b B.∧ (b₁ B.∧ b) B.∧ b₂ ≡⟨ cong (b B.∧_) (B.∧-assoc b₁ b b₂) ⟩
      b B.∧ b₁ B.∧ b B.∧ b₂   ≡˘⟨ B.∧-assoc b b₁ (b B.∧ b₂) ⟩
      (b B.∧ b₁) B.∧ b B.∧ b₂ ∎
    lemma₂-+ : ∀ a b c → (b N.== c) ≡ (a +ⁿ b N.== a +ⁿ c)
    lemma₂-+ 0 b c = refl
    lemma₂-+ (1+ a) b c = lemma₂-+ a b c
    lemma₂-* : ∀ a b c → (b N.== c) ≡ (b * 1+ a N.== c * 1+ a)
    lemma₂-* a Nat.zero Nat.zero = refl
    lemma₂-* a Nat.zero (1+ c) = refl
    lemma₂-* a (1+ b) Nat.zero = refl
    lemma₂-* a (1+ b) (1+ c) = trans (lemma₂-* a b c) (lemma₂-+ a (b * 1+ a) (c * 1+ a))
    lemma₂ : (m₁ N.== m₂) ≡ (m * m₁ +ⁿ m +ⁿ m₁ N.== m * m₂ +ⁿ m +ⁿ m₂)
    lemma₂ = begin
      m₁ N.== m₂                                   ≡⟨ lemma₂-* m m₁ m₂ ⟩
      m₁ * 1+ m N.== m₂ * 1+ m                     ≡⟨ cong₂ N._==_ (N.*-comm m₁ (1+ m)) (N.*-comm m₂ (1+ m)) ⟩
      m₁ +ⁿ m * m₁ N.== m₂ +ⁿ m * m₂               ≡⟨ cong₂ N._==_ (N.+-comm m₁ (m * m₁)) (N.+-comm m₂ (m * m₂)) ⟩
      m * m₁ +ⁿ m₁ N.== m * m₂ +ⁿ m₂               ≡⟨ lemma₂-+ m (m * m₁ +ⁿ m₁) (m * m₂ +ⁿ m₂) ⟩
      m +ⁿ (m * m₁ +ⁿ m₁) N.== m +ⁿ (m * m₂ +ⁿ m₂) ≡⟨ cong₂ N._==_ (N.+-comm m (m * m₁ +ⁿ m₁)) (N.+-comm m (m * m₂ +ⁿ m₂)) ⟩
      m * m₁ +ⁿ m₁ +ⁿ m N.== m * m₂ +ⁿ m₂ +ⁿ m     ≡⟨ cong₂ N._==_ (N.+-assoc (m * m₁) m₁ m) (N.+-assoc (m * m₂) m₂ m) ⟩
      m * m₁ +ⁿ (m₁ +ⁿ m) N.== m * m₂ +ⁿ (m₂ +ⁿ m) ≡⟨ cong₂ N._==_ (cong (m * m₁ +ⁿ_) (N.+-comm m₁ m)) (cong (m * m₂ +ⁿ_) (N.+-comm m₂ m)) ⟩
      m * m₁ +ⁿ (m +ⁿ m₁) N.== m * m₂ +ⁿ (m +ⁿ m₂) ≡˘⟨ cong₂ N._==_ (N.+-assoc (m * m₁) m m₁) (N.+-assoc (m * m₂) m m₂) ⟩
      m * m₁ +ⁿ m +ⁿ m₁ N.== m * m₂ +ⁿ m +ⁿ m₂     ∎
    lemma₃ : m * (m₁ ⊔ m₂) +ⁿ m +ⁿ (m₁ ⊔ m₂) ≡ m * m₁ +ⁿ m +ⁿ m₁ ⊔ (m * m₂ +ⁿ m +ⁿ m₂)
    lemma₃ = begin
      m * (m₁ ⊔ m₂) +ⁿ m +ⁿ (m₁ ⊔ m₂) ≡⟨ N.+-comm (m * (m₁ ⊔ m₂) +ⁿ m) (m₁ ⊔ m₂) ⟩
      (m₁ ⊔ m₂) +ⁿ (m * (m₁ ⊔ m₂) +ⁿ m) ≡˘⟨ N.+-assoc (m₁ ⊔ m₂) (m * (m₁ ⊔ m₂)) m ⟩
      (m₁ ⊔ m₂) +ⁿ m * (m₁ ⊔ m₂) +ⁿ m ≡⟨⟩
      (1+ m) * (m₁ ⊔ m₂) +ⁿ m ≡⟨ cong (_+ⁿ m) (N.*-distribˡ-⊔ (1+ m) m₁ m₂) ⟩
      (1+ m * m₁ ⊔ 1+ m * m₂) +ⁿ m ≡⟨ N.+-distribʳ-⊔ m (1+ m * m₁) (1+ m * m₂) ⟩
      (1+ m * m₁ +ⁿ m) ⊔ (1+ m * m₂ +ⁿ m) ≡⟨⟩
      (m₁ +ⁿ m * m₁ +ⁿ m) ⊔ (m₂ +ⁿ m * m₂ +ⁿ m) ≡⟨ cong₂ _⊔_ (N.+-assoc m₁ (m * m₁) m)
                                                            (N.+-assoc m₂ (m * m₂) m) ⟩
      (m₁ +ⁿ (m * m₁ +ⁿ m)) ⊔ (m₂ +ⁿ (m * m₂ +ⁿ m)) ≡⟨ cong₂ _⊔_ (N.+-comm m₁ (m * m₁ +ⁿ m))
                                                                (N.+-comm m₂ (m * m₂ +ⁿ m)) ⟩
      m * m₁ +ⁿ m +ⁿ m₁ ⊔ (m * m₂ +ⁿ m +ⁿ m₂) ∎

  ·-distribˡ-∧ (≈/≤1+ b m) (≈/≤1+ b₁ m₁) ∞ = refl
  ·-distribˡ-∧ (≈/≤1+ b m) ∞ r = refl
  ·-distribˡ-∧ ∞ 𝟘 𝟘 = refl
  ·-distribˡ-∧ ∞ 𝟘 (≈/≤1+ b m) = refl
  ·-distribˡ-∧ ∞ 𝟘 ∞ = refl
  ·-distribˡ-∧ ∞ (≈/≤1+ b m) 𝟘 = refl
  ·-distribˡ-∧ ∞ (≈/≤1+ b m) (≈/≤1+ b₁ m₁) = refl
  ·-distribˡ-∧ ∞ (≈/≤1+ b m) ∞ = refl
  ·-distribˡ-∧ ∞ ∞ r = refl

  +-distribˡ-∧-lemma₁ : ∀ b b′ m n → b B.∧ false ≡ b′ B.∧ (m N.== 1+ (m +ⁿ n))
  +-distribˡ-∧-lemma₁ b b′ m n = begin
    b B.∧ false                 ≡⟨ B.∧-zeroʳ b ⟩
    false                       ≡˘⟨ B.∧-zeroʳ b′ ⟩
    b′ B.∧ false                ≡˘⟨ cong (b′ B.∧_) (lemma m) ⟩
    b′ B.∧ (m N.== 1+ (m +ⁿ n)) ∎
    where
    open RPe
    lemma : ∀ m → (m N.== 1+ (m +ⁿ n)) ≡ false
    lemma 0 = refl
    lemma (1+ m) = lemma m

  +-distribˡ-∧-lemma₂ : ∀ m n → 1+ (m +ⁿ n) ≡ m ⊔ 1+ (m +ⁿ n)
  +-distribˡ-∧-lemma₂ 0 n = refl
  +-distribˡ-∧-lemma₂ (1+ m) n = cong 1+ (+-distribˡ-∧-lemma₂ m n)

  +-distribˡ-∧ : _+_ DistributesOverˡ _∧_
  +-distribˡ-∧ 𝟘 q r = refl
  +-distribˡ-∧ (≈/≤1+ b m) 𝟘 𝟘 =
    flip (cong₂ ≈/≤1+) (sym (N.⊔-idem m)) (begin
      b                        ≡˘⟨ B.∧-idem b ⟩
      b B.∧ b                  ≡˘⟨ B.∧-identityʳ _ ⟩
      (b B.∧ b) B.∧ true       ≡˘⟨ cong ((b B.∧ b) B.∧_) (N.==-refl m) ⟩
      (b B.∧ b) B.∧ (m N.== m) ∎)
    where
    open RPe
  +-distribˡ-∧ (≈/≤1+ b m) 𝟘 (≈/≤1+ b₁ m₁) =
    cong₂ ≈/≤1+ (+-distribˡ-∧-lemma₁ b (b B.∧ b B.∧ b₁) m m₁)
      (+-distribˡ-∧-lemma₂ m m₁)
  +-distribˡ-∧ (≈/≤1+ b m) 𝟘 ∞ = refl
  +-distribˡ-∧ (≈/≤1+ b m) (≈/≤1+ b₁ m₁) 𝟘 =
    cong₂ ≈/≤1+
      (trans (+-distribˡ-∧-lemma₁ b ((b B.∧ b₁) B.∧ b) m m₁)
        (cong (((b B.∧ b₁) B.∧ b) B.∧_) (N.==-sym m (1+ (m +ⁿ m₁)))))
      (trans (+-distribˡ-∧-lemma₂ m m₁)
        (N.⊔-comm m (1+ (m +ⁿ m₁))))
  +-distribˡ-∧ (≈/≤1+ b m) (≈/≤1+ b₁ m₁) (≈/≤1+ b₂ m₂) =
    flip (cong₂ ≈/≤1+) (cong 1+ (N.+-distribˡ-⊔ m m₁ m₂)) (begin
       b B.∧ (b₁ B.∧ b₂) B.∧ (m₁ N.== m₂) ≡˘⟨ cong (B._∧ _) (B.∧-idem b) ⟩
       (b B.∧ b) B.∧ (b₁ B.∧ b₂) B.∧ (m₁ N.== m₂) ≡˘⟨ B.∧-assoc (b B.∧ b) (b₁ B.∧ b₂) (m₁ N.== m₂) ⟩
       ((b B.∧ b) B.∧ b₁ B.∧ b₂) B.∧ (m₁ N.== m₂) ≡˘⟨ cong (B._∧ (m₁ N.== m₂)) (B.∧-assoc (b B.∧ b) b₁ b₂) ⟩
       (((b B.∧ b) B.∧ b₁) B.∧ b₂) B.∧ (m₁ N.== m₂) ≡⟨ cong (λ x → (x B.∧ b₂) B.∧ (m₁ N.== m₂)) (B.∧-assoc b b b₁) ⟩
       ((b B.∧ b B.∧ b₁) B.∧ b₂) B.∧ (m₁ N.== m₂) ≡⟨ cong (λ x → ((b B.∧ x) B.∧ b₂) B.∧ (m₁ N.== m₂)) (B.∧-comm b b₁) ⟩
       ((b B.∧ b₁ B.∧ b) B.∧ b₂) B.∧ (m₁ N.== m₂) ≡˘⟨ cong (λ x → (x B.∧ b₂) B.∧ (m₁ N.== m₂)) (B.∧-assoc b b₁ b) ⟩
       (((b B.∧ b₁) B.∧ b) B.∧ b₂) B.∧ (m₁ N.== m₂) ≡⟨ cong₂ B._∧_ (B.∧-assoc (b B.∧ b₁) b b₂) (lemma m) ⟩
       ((b B.∧ b₁) B.∧ b B.∧ b₂) B.∧ (m +ⁿ m₁ N.== m +ⁿ m₂) ∎)
    where
    open RPe
    lemma : ∀ m → (m₁ N.== m₂) ≡ (m +ⁿ m₁ N.== m +ⁿ m₂)
    lemma 0 = refl
    lemma (1+ m) = lemma m
  +-distribˡ-∧ (≈/≤1+ b m) (≈/≤1+ b₁ m₁) ∞ = refl
  +-distribˡ-∧ (≈/≤1+ b m) ∞ r = refl
  +-distribˡ-∧ ∞ q r = refl

  ω·+≤ω·ʳ : ∞ · (p + q) ≤ ∞ · q
  ω·+≤ω·ʳ {(𝟘)} = sym (∧-idem _)
  ω·+≤ω·ʳ {≈/≤1+ b m} {(𝟘)} = refl
  ω·+≤ω·ʳ {≈/≤1+ b m} {≈/≤1+ b₁ m₁} = refl
  ω·+≤ω·ʳ {≈/≤1+ b m} {(∞)} = refl
  ω·+≤ω·ʳ {(∞)} = refl

opaque instance

  -- The zero is well-behaved

  exact-or-at-most-has-well-behaved-zero :
    Has-well-behaved-zero exact-or-at-most-modality
  exact-or-at-most-has-well-behaved-zero = record
    { non-trivial = λ ()
    ; zero-product = zero-product
    ; +-positiveˡ = +-positiveˡ
    ; ∧-positiveˡ = ∧-positiveˡ
    }
    where
    zero-product : ∀ {p q} → p · q ≡ 𝟘 → p ≡ 𝟘 ⊎ q ≡ 𝟘
    zero-product {p = 𝟘}                         _  = inj₁ refl
    zero-product {p = ≈/≤1+ _ _} {q = 𝟘}         _  = inj₂ refl
    zero-product {p = ∞}         {q = 𝟘}         _  = inj₂ refl
    zero-product {p = ≈/≤1+ _ _} {q = ≈/≤1+ _ _} ()
    zero-product {p = ≈/≤1+ _ _} {q = ∞}         ()
    zero-product {p = ∞}         {q = ≈/≤1+ _ _} ()
    zero-product {p = ∞}         {q = ∞}         ()
    +-positiveˡ : ∀ {p q} → p + q ≡ 𝟘 → p ≡ 𝟘
    +-positiveˡ {p = 𝟘}                         _  = refl
    +-positiveˡ {p = ≈/≤1+ _ _} {q = 𝟘}         ()
    +-positiveˡ {p = ≈/≤1+ _ _} {q = ≈/≤1+ _ _} ()
    +-positiveˡ {p = ≈/≤1+ _ _} {q = ∞}         ()
    +-positiveˡ {p = ∞}                         ()
    ∧-positiveˡ : ∀ {p q} → p ∧ q ≡ 𝟘 → p ≡ 𝟘
    ∧-positiveˡ {p = 𝟘}         {q = 𝟘}         refl = refl
    ∧-positiveˡ {p = 𝟘}         {q = ≈/≤1+ _ _} ()
    ∧-positiveˡ {p = 𝟘}         {q = ∞}         ()
    ∧-positiveˡ {p = ≈/≤1+ _ _} {q = 𝟘}         ()
    ∧-positiveˡ {p = ≈/≤1+ _ _} {q = ≈/≤1+ _ _} ()
    ∧-positiveˡ {p = ≈/≤1+ _ _} {q = ∞}         ()
    ∧-positiveˡ {p = ∞}                         ()

open Modality exact-or-at-most-modality
  hiding (_+_; _·_; _∧_; 𝟘; 𝟙; _≤_)
open Graded.Modality.Properties.Addition exact-or-at-most-modality
open Graded.Modality.Properties.Has-well-behaved-zero exact-or-at-most-modality
open Graded.Modality.Properties.Meet exact-or-at-most-modality
open Graded.Modality.Properties.Multiplication exact-or-at-most-modality
open Graded.Modality.Properties.Natrec exact-or-at-most-modality
open Graded.Modality.Properties.PartialOrder exact-or-at-most-modality

opaque

  -- Multiplication by an "affine" value is decreasing

  ≤·-decreasing : ≤1+ m · p ≤ p
  ≤·-decreasing {p = 𝟘} = refl
  ≤·-decreasing {p = ∞} = refl
  ≤·-decreasing {(m)} {≈/≤1+ b n} =
    cong ≤1+ (sym (N.m≥n⇒m⊔n≡m (N.m≤n+m n (m * n +ⁿ m))))

opaque

  -- Multiplication of an "affine" value by a non-zero value is decreasing

  ≤·≢𝟘-decreasing : p ≢ 𝟘 → ≤1+ m · p ≤ ≤1+ m
  ≤·≢𝟘-decreasing {(𝟘)} p≢𝟘 = ⊥-elim (p≢𝟘 refl)
  ≤·≢𝟘-decreasing {(∞)} _ = refl
  ≤·≢𝟘-decreasing {≈/≤1+ b n} {m} _ =
    cong ≤1+ (sym (N.m≥n⇒m⊔n≡m (N.≤-trans (N.m≤n+m m (m * n +ⁿ n))
      (N.≤-reflexive (trans (N.+-assoc (m * n) n m)
        (trans (cong (m * n +ⁿ_) (N.+-comm n m))
          (sym (N.+-assoc (m * n) m n))))))))

opaque

  -- Multiplication by ≈𝟙 or ≤𝟙 is decreasing

  ≈𝟙/≤𝟙·-decreasing : ≈/≤1+ b 0 · p ≤ p
  ≈𝟙/≤𝟙·-decreasing {(false)} = ≤·-decreasing
  ≈𝟙/≤𝟙·-decreasing {(true)} = ≤-reflexive (·-identityˡ _)

------------------------------------------------------------------------
-- An nr function for Exact-or-at-most

-- A function used to define nr.

nr₃ : Op₃ Exact-or-at-most
nr₃ 𝟘 z s = z ∧ s
nr₃ (≈/≤1+ b 0) z s = (≈/≤1+ b 0) · z + ∞ · s
nr₃ (≈/≤1+ b (1+ m)) z s = ∞ · (z + s)
nr₃ ∞ z s = ∞ · (z + s)

opaque

  -- nr₃ is 𝟘 only if the latter two arguments are 𝟘.

  nr₃-positive : ∀ r → nr₃ r z s ≡ 𝟘 → z ≡ 𝟘 × s ≡ 𝟘
  nr₃-positive {z} {s} = λ where
    𝟘 nr₃≡𝟘 → ∧-positive nr₃≡𝟘
    (≈/≤1+ b 0) nr₃≡𝟘 →
      case +-positive {p = ≈/≤1+ b 0 · z} nr₃≡𝟘 of λ
        (qz≡𝟘 , ∞s≡𝟘) →
      case zero-product qz≡𝟘 of λ where
        (inj₁ ())
        (inj₂ z≡𝟘) → case zero-product ∞s≡𝟘 of λ where
          (inj₁ ())
          (inj₂ s≡𝟘) → z≡𝟘 , s≡𝟘
    (≈/≤1+ b (1+ m)) nr₃≡𝟘 → lemma nr₃≡𝟘
    ∞ nr₃≡𝟘 → lemma nr₃≡𝟘
      where
      lemma : ∞ · (z + s) ≡ 𝟘 → z ≡ 𝟘 × s ≡ 𝟘
      lemma ≡𝟘 =
        case zero-product ≡𝟘 of λ where
          (inj₁ ())
          (inj₂ z+s≡𝟘) → +-positive z+s≡𝟘

opaque

  -- An inequality property for nr₃.

  nr₃-suc : ∀ r z s → nr₃ r z s ≤ s + r · nr₃ r z s
  nr₃-suc 𝟘 z s = begin
    z ∧ s ≤⟨ ∧-decreasingʳ z s ⟩
    s     ≡˘⟨ +-identityʳ s ⟩
    s + 𝟘 ∎
    where
    open RPo ≤-poset
  nr₃-suc (≈/≤1+ b 0) 𝟘 𝟘 = refl
  nr₃-suc (≤1+ 0) (≤1+ m) 𝟘 = ≤-refl
  nr₃-suc (≤1+ 0) (≈1+ m) 𝟘 = ≤-refl
  nr₃-suc (≈1+ 0) (≤1+ m) 𝟘 = ≤-refl
  nr₃-suc (≈1+ 0) (≈1+ m) 𝟘 = ≤-refl
  nr₃-suc (≈/≤1+ b 0) ∞ 𝟘 = refl
  nr₃-suc (≈/≤1+ b 0) 𝟘 (≈/≤1+ b₁ m) = refl
  nr₃-suc (≈/≤1+ b 0) (≈/≤1+ b₂ m₁) (≈/≤1+ b₁ m) = refl
  nr₃-suc (≈/≤1+ b 0) ∞ (≈/≤1+ b₁ m) = refl
  nr₃-suc (≈/≤1+ b 0) 𝟘 ∞ = refl
  nr₃-suc (≈/≤1+ b 0) (≈/≤1+ b₁ m) ∞ = refl
  nr₃-suc (≈/≤1+ b 0) ∞ ∞ = refl
  nr₃-suc (≈/≤1+ b (1+ m)) 𝟘 𝟘 = refl
  nr₃-suc (≈/≤1+ b (1+ m)) 𝟘 (≈/≤1+ b₁ m₁) = refl
  nr₃-suc (≈/≤1+ b (1+ m)) 𝟘 ∞ = refl
  nr₃-suc (≈/≤1+ b (1+ m)) (≈/≤1+ b₁ m₁) 𝟘 = refl
  nr₃-suc (≈/≤1+ b (1+ m)) (≈/≤1+ b₁ m₁) (≈/≤1+ b₂ m₂) = refl
  nr₃-suc (≈/≤1+ b (1+ m)) (≈/≤1+ b₁ m₁) ∞ = refl
  nr₃-suc (≈/≤1+ b (1+ m)) ∞ s = refl
  nr₃-suc ∞ 𝟘 𝟘 = refl
  nr₃-suc ∞ (≈/≤1+ b m) 𝟘 = refl
  nr₃-suc ∞ ∞ 𝟘 = refl
  nr₃-suc ∞ 𝟘 (≈/≤1+ b m) = refl
  nr₃-suc ∞ (≈/≤1+ b₁ m₁) (≈/≤1+ b m) = refl
  nr₃-suc ∞ ∞ (≈/≤1+ b m) = refl
  nr₃-suc ∞ z ∞ rewrite +-comm z ∞ = refl

opaque

  -- Given a function nr₂, satisfying some properties, one can construct
  -- an nr function using nr₃.

  nr₂→exact-or-at-most-has-nr : (nr₂ : Op₂ Exact-or-at-most) → (∀ {p r} → nr₂ p r ≢ 𝟘)
                              → (∀ {p r} → nr₂ p r ≤ p + r · nr₂ p r)
                              → Has-nr exact-or-at-most-modality
  nr₂→exact-or-at-most-has-nr nr₂ nr₂≢𝟘 nr₂≤ = record
    { nr = nr
    ; nr-monotone = λ {p = p} {r} → nr-monotone {p = p} {r}
    ; nr-· = λ {p r} → ≤-reflexive (nr-· {p} {r})
    ; nr-+ = λ {p r} → nr-+ {p} {r}
    ; nr-positive = λ {p r} → nr-positive {p} {r}
    ; nr-zero = λ {n p r} → nr-zero {n} {p} {r}
    ; nr-suc = λ {p r} → nr-suc {p} {r}
    }
    where

    nr : (p r z s n : Exact-or-at-most) → Exact-or-at-most
    nr p r z s n = nr₂ p r · n + nr₃ r z s

    nr-monotone :
        z₁ ≤ z₂ → s₁ ≤ s₂ → n₁ ≤ n₂ →
        nr p r z₁ s₁ n₁ ≤ nr p r z₂ s₂ n₂
    nr-monotone {p} {r} z₁≤z₂ s₁≤s₂ n₁≤n₂ =
      +-monotone (·-monotoneʳ n₁≤n₂) (lemma r z₁≤z₂ s₁≤s₂)
      where
      lemma : ∀ r → z₁ ≤ z₂ → s₁ ≤ s₂ → nr₃ r z₁ s₁ ≤ nr₃ r z₂ s₂
      lemma 𝟘 z₁≤z₂ s₁≤s₂ = ∧-monotone z₁≤z₂ s₁≤s₂
      lemma (≈/≤1+ b 0) z₁≤z₂ s₁≤s₂ = +-monotone (·-monotoneʳ {r = ≈/≤1+ b 0} z₁≤z₂) (·-monotoneʳ {r = ∞} s₁≤s₂)
      lemma (≈/≤1+ b (1+ m)) z₁≤z₂ s₁≤s₂ = ·-monotoneʳ (+-monotone z₁≤z₂ s₁≤s₂)
      lemma ∞ z₁≤z₂ s₁≤s₂ = ·-monotoneʳ (+-monotone z₁≤z₂ s₁≤s₂)

    nr-· : nr p r z s n · q ≡ nr p r (z · q) (s · q) (n · q)
    nr-· {p} {r} {z} {s} {n} {q} = begin
      nr p r z s n · q                          ≡⟨⟩
      (nr₂ p r · n + nr₃ r z s) · q             ≡⟨ ·-distribʳ-+ _ (nr₂ p r · n) (nr₃ r z s) ⟩
      (nr₂ p r · n) · q + nr₃ r z s · q         ≡⟨ +-cong (·-assoc (nr₂ p r) n q) (lemma r) ⟩
      nr₂ p r · (n · q) + nr₃ r (z · q) (s · q) ≡⟨⟩
      nr p r (z · q) (s · q) (n · q)            ∎
      where
      open RPe
      lemma : ∀ r → nr₃ r z s · q ≡ nr₃ r (z · q) (s · q)
      lemma 𝟘 = ·-distribʳ-∧ q z s
      lemma (≈/≤1+ b 0) =
        trans (·-distribʳ-+ q (≈/≤1+ b 0 · z) (∞ · s))
          (+-cong (·-assoc (≈/≤1+ b 0) z q) (·-assoc ∞ s q))
      lemma (≈/≤1+ b (1+ m)) = trans (·-assoc ∞ (z + s) q) (·-congˡ (·-distribʳ-+ q z s))
      lemma ∞ = trans (·-assoc ∞ (z + s) q) (·-congˡ (·-distribʳ-+ q z s))

    nr-+ : nr p r z₁ s₁ n₁ + nr p r z₂ s₂ n₂ ≤ nr p r (z₁ + z₂) (s₁ + s₂) (n₁ + n₂)
    nr-+ {p} {r} {z₁} {s₁} {n₁} {z₂} {s₂} {n₂} = begin
      nr p r z₁ s₁ n₁ + nr p r z₂ s₂ n₂                         ≡⟨⟩
      (nr₂ p r · n₁ + nr₃ r z₁ s₁) + nr₂ p r · n₂ + nr₃ r z₂ s₂ ≡⟨ lemma₁ (nr₂ p r · n₁) (nr₃ r z₁ s₁) (nr₂ p r · n₂) (nr₃ r z₂ s₂) ⟩
      (nr₂ p r · n₁ + nr₂ p r · n₂) + nr₃ r z₁ s₁ + nr₃ r z₂ s₂ ≡˘⟨ +-congʳ (·-distribˡ-+ (nr₂ p r) n₁ n₂) ⟩
      nr₂ p r · (n₁ + n₂) + nr₃ r z₁ s₁ + nr₃ r z₂ s₂           ≤⟨ +-monotoneʳ (lemma₃ r) ⟩
      nr₂ p r · (n₁ + n₂) + nr₃ r (z₁ + z₂) (s₁ + s₂)           ≡⟨⟩
      nr p r (z₁ + z₂) (s₁ + s₂) (n₁ + n₂)                      ∎
      where
      lemma₁ : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
      lemma₁ a b c d =
        (a + b) + c + d   ≡˘⟨ +-assoc (a + b) c d ⟩
        ((a + b) + c) + d ≡⟨ +-congʳ (+-assoc a b c) ⟩
        (a + b + c) + d   ≡⟨ cong (λ x → (a + x) + d) (+-comm b c) ⟩
        (a + c + b) + d   ≡˘⟨ +-congʳ (+-assoc a c b) ⟩
        ((a + c) + b) + d ≡⟨ +-assoc (a + c) b d ⟩
        (a + c) + b + d   ∎
        where
        open RPe
      open RPo ≤-poset
      lemma₂ : ∞ · (z₁ + s₁) + ∞ · (z₂ + s₂) ≤ ∞ · ((z₁ + z₂) + s₁ + s₂)
      lemma₂ = begin
        ∞ · (z₁ + s₁) + ∞ · (z₂ + s₂) ≡˘⟨ ·-distribˡ-+ ∞ (z₁ + s₁) (z₂ + s₂) ⟩
        ∞ · ((z₁ + s₁) + z₂ + s₂)     ≡⟨ ·-congˡ (lemma₁ z₁ s₁ z₂ s₂) ⟩
        ∞ · ((z₁ + z₂) + s₁ + s₂)     ∎
      lemma₃ : ∀ r → nr₃ r z₁ s₁ + nr₃ r z₂ s₂ ≤ nr₃ r (z₁ + z₂) (s₁ + s₂)
      lemma₃ 𝟘 = +-sub-interchangeable-∧ z₁ s₁ z₂ s₂
      lemma₃ (≈/≤1+ b 0) = begin
        ((≈/≤1+ b 0) · z₁ + ∞ · s₁) + (≈/≤1+ b 0) · z₂ + ∞ · s₂     ≡⟨ lemma₁ ((≈/≤1+ b 0) · z₁) (∞ · s₁) ((≈/≤1+ b 0) · z₂) (∞ · s₂) ⟩
        ((≈/≤1+ b 0) · z₁ + (≈/≤1+ b 0) · z₂) + (∞ · s₁) + (∞ · s₂) ≡˘⟨ +-cong (·-distribˡ-+ (≈/≤1+ b 0) z₁ z₂) (·-distribˡ-+ ∞ s₁ s₂) ⟩
        (≈/≤1+ b 0) · (z₁ + z₂) + ∞ · (s₁ + s₂)                     ∎
      lemma₃ (≈/≤1+ b (1+ m)) = lemma₂
      lemma₃ ∞ = lemma₂

    nr-positive : nr p r z s n ≡ 𝟘 → z ≡ 𝟘 × s ≡ 𝟘 × n ≡ 𝟘
    nr-positive {p} {r} {z} {s} {n} nr≡𝟘 =
      case +-positive {p = nr₂ p r · n} nr≡𝟘 of λ
        (nr₃n≡𝟘 , nr₃≡𝟘) →
      case nr₃-positive r nr₃≡𝟘 of λ
        (z≡𝟘 , s≡𝟘) →
      case zero-product nr₃n≡𝟘 of λ where
        (inj₁ nr₂≡𝟘) → ⊥-elim (nr₂≢𝟘 nr₂≡𝟘)
        (inj₂ n≡𝟘) → z≡𝟘 , s≡𝟘 , n≡𝟘

    nr-zero : n ≤ 𝟘 → nr p r z s n ≤ z
    nr-zero {n} {p} {r} {z} {s} n≤𝟘 = begin
      nr p r z s n            ≡⟨⟩
      nr₂ p r · n + nr₃ r z s ≤⟨ +-monotoneˡ (·-monotoneʳ {r = nr₂ p r} n≤𝟘) ⟩
      nr₂ p r · 𝟘 + nr₃ r z s ≡⟨ +-congʳ (·-zeroʳ _) ⟩
      𝟘 + nr₃ r z s           ≡⟨ +-identityˡ _ ⟩
      nr₃ r z s               ≤⟨ lemma r z s ⟩
      z                       ∎
      where
      open RPo ≤-poset
      lemma : ∀ r z s → nr₃ r z s ≤ z
      lemma 𝟘 z s = ∧-decreasingˡ z s
      lemma (≈/≤1+ b 0) 𝟘 𝟘 = refl
      lemma (≤1+ 0) (≈/≤1+ b₁ m) 𝟘 = ≤-refl
      lemma 𝟙 (≈/≤1+ b₁ m) 𝟘 = ≤-refl
      lemma (≈/≤1+ b 0) ∞ 𝟘 = refl
      lemma (≈/≤1+ b 0) 𝟘 (≈/≤1+ b₁ m) = refl
      lemma (≈/≤1+ b 0) (≈/≤1+ b₂ m₁) (≈/≤1+ b₁ m) = refl
      lemma (≈/≤1+ b 0) ∞ (≈/≤1+ b₁ m) = refl
      lemma (≈/≤1+ b 0) 𝟘 ∞ = refl
      lemma (≈/≤1+ b 0) (≈/≤1+ b₁ m) ∞ = refl
      lemma (≈/≤1+ b 0) ∞ ∞ = refl
      lemma (≈/≤1+ b (1+ m)) 𝟘 𝟘 = refl
      lemma (≈/≤1+ b (1+ m)) 𝟘 (≈/≤1+ b₁ m₁) = refl
      lemma (≈/≤1+ b (1+ m)) 𝟘 ∞ = refl
      lemma (≈/≤1+ b (1+ m)) (≈/≤1+ b₁ m₁) 𝟘 = refl
      lemma (≈/≤1+ b (1+ m)) (≈/≤1+ b₁ m₁) (≈/≤1+ b₂ m₂) = refl
      lemma (≈/≤1+ b (1+ m)) (≈/≤1+ b₁ m₁) ∞ = refl
      lemma (≈/≤1+ b (1+ m)) ∞ s = ≤-refl
      lemma ∞ 𝟘 𝟘 = refl
      lemma ∞ 𝟘 (≈/≤1+ b m) = refl
      lemma ∞ 𝟘 ∞ = refl
      lemma ∞ (≈/≤1+ b m) 𝟘 = refl
      lemma ∞ (≈/≤1+ b m) (≈/≤1+ b₁ m₁) = refl
      lemma ∞ (≈/≤1+ b m) ∞ = refl
      lemma ∞ ∞ s = ≤-refl

    nr-suc : nr p r z s n ≤ s + p · n + r · nr p r z s n
    nr-suc {p} {r} {z} {s} {n} = begin
      nr p r z s n                                    ≡⟨⟩
      nr₂ p r · n + nr₃ r z s                         ≤⟨ +-monotone (·-monotoneˡ nr₂≤) (nr₃-suc r z s) ⟩
      (p + r · nr₂ p r) · n + (s + r · nr₃ r z s)     ≡⟨ +-congʳ (·-distribʳ-+ n p (r · nr₂ p r)) ⟩
      (p · n + (r · nr₂ p r) · n) + s + r · nr₃ r z s ≡⟨ cong (λ x → (p · n + x) + s + r · nr₃ r z s) (·-assoc r (nr₂ p r) n) ⟩
      (p · n + r · nr₂ p r · n) + s + r · nr₃ r z s   ≡˘⟨ +-assoc (p · n + r · nr₂ p r · n) s (r · nr₃ r z s) ⟩
      ((p · n + r · nr₂ p r · n) + s) + r · nr₃ r z s ≡⟨ +-congʳ (+-comm (p · n + r · nr₂ p r · n) s) ⟩
      (s + p · n + r · nr₂ p r · n) + r · nr₃ r z s   ≡⟨ +-assoc s (p · n + r · nr₂ p r · n) (r · nr₃ r z s) ⟩
      s + (p · n + r · nr₂ p r · n) + r · nr₃ r z s   ≡⟨ +-congˡ {s} (+-assoc (p · n) (r · nr₂ p r · n) (r · nr₃ r z s)) ⟩
      s + p · n + r · nr₂ p r · n + r · nr₃ r z s     ≡˘⟨ +-congˡ {s} (+-congˡ {p · n} (·-distribˡ-+ r (nr₂ p r · n) (nr₃ r z s))) ⟩
      s + p · n + r · (nr₂ p r · n + nr₃ r z s)       ≡⟨⟩
      s + p · n + r · nr p r z s n                    ∎
      where
      open RPo ≤-poset


opaque
  unfolding nr₂→exact-or-at-most-has-nr

  -- Given a function nr₂, satisfying some properties, the nr function given by
  -- nr₂→has-nr is factoring.

  nr₂→exact-or-at-most-has-factoring-nr :
    (nr₂ : Op₂ Exact-or-at-most) (nr₂≢𝟘 : ∀ {p r} → nr₂ p r ≢ 𝟘)
    (nr₂≤ : ∀ {p r} → nr₂ p r ≤ p + r · nr₂ p r) →
    Is-factoring-nr (nr₂→exact-or-at-most-has-nr nr₂ nr₂≢𝟘 nr₂≤)
  nr₂→exact-or-at-most-has-factoring-nr nr₂ nr₂≢𝟘 _ = record
    { nr₂ = nr₂
    ; nr₂≢𝟘 = nr₂≢𝟘
    ; nr-factoring = λ {p r z s n} →
        sym (+-congˡ {x = nr₂ p r · n} (+-congʳ (·-zeroʳ (nr₂ p r))))
    }

instance opaque

  exact-or-at-most-has-nr : Has-nr exact-or-at-most-modality
  exact-or-at-most-has-nr =
    nr₂→exact-or-at-most-has-nr (λ p r → nr₃ r 𝟙 p)
      (λ {_} {r} nr₃≡𝟘 → case nr₃-positive r nr₃≡𝟘 of λ ())
      (λ {p} {r} → nr₃-suc r 𝟙 p)


instance opaque
  unfolding exact-or-at-most-has-nr

  -- The nr function is factoring

  exact-or-at-most-has-factoring-nr : Is-factoring-nr exact-or-at-most-has-nr
  exact-or-at-most-has-factoring-nr =
    nr₂→exact-or-at-most-has-factoring-nr (λ p r → nr₃ r 𝟙 p)
      (λ {_} {r} nr₃≡𝟘 → case nr₃-positive r nr₃≡𝟘 of λ ())
      (λ {p} {r} → nr₃-suc r 𝟙 p)

opaque

  -- An inequality for the nr₂ function used to define nr.

  nr₂p𝟘≤𝟙 : nr₃ 𝟘 𝟙 p ≤ 𝟙
  nr₂p𝟘≤𝟙 = ∧-decreasingˡ _ _

opaque

  -- An inequality for the nr₂ function used to define nr.

  nr₂𝟘𝟙≤𝟙 : nr₃ 𝟙 𝟙 𝟘 ≤ 𝟙
  nr₂𝟘𝟙≤𝟙 = refl

-- The nr function that is used in the Has-nr instance below.

nr : (p r z s n : Exact-or-at-most) → Exact-or-at-most
nr = Has-nr.nr exact-or-at-most-has-nr

opaque
  unfolding nr₂→exact-or-at-most-has-nr exact-or-at-most-has-nr

  -- There is no greatest factoring nr function

  no-greatest-factoring-nr : No-greatest-factoring-nr
  no-greatest-factoring-nr = record
    { has-nr₁ = exact-or-at-most-has-nr
    ; has-nr₂ = nr₂→exact-or-at-most-has-nr nr₂
                  (λ {p} {r} → nr₂≢𝟘 {p} {r}) λ {p} {r} → nr₃-suc r _ p
    ; factoring₁ = exact-or-at-most-has-factoring-nr
    ; factoring₂ = nr₂→exact-or-at-most-has-factoring-nr nr₂
                     (λ {p} {r} → nr₂≢𝟘 {p} {r}) λ {p} {r} → nr₃-suc r _ p
    ; p₀ = 𝟘
    ; r₀ = 𝟙
    ; z₀ = 𝟘
    ; s₀ = 𝟘
    ; n₀ = 𝟙
    ; nr₁≢nr₂ = λ ()
    ; nr≰ = λ where
        (≈1+ 0)      _  ()
        (≈1+ (1+ _)) () _
        𝟘            _  ()
        (≤1+ _)      _  ()
        ∞            _  ()
    }
    where
    nr₂ : Op₂ Exact-or-at-most
    nr₂ p r = nr₃ r (≈1+ 1) p
    nr₂≢𝟘 : nr₂ p r ≢ 𝟘
    nr₂≢𝟘 {r} nr₂≡𝟘 = case nr₃-positive r nr₂≡𝟘 of λ ()

opaque
  unfolding nr₂→exact-or-at-most-has-nr exact-or-at-most-has-nr

  -- The nr function returns results that are at least as large as those
  -- of any other factoring nr function with nr₂ p 𝟘 ≤ 𝟙 and
  -- nr₂ 𝟘 𝟙 ≤ 𝟙 for exact-or-at-most-semiring-with-meet
  -- (Note that the nr₂ function used by nr has these properties,
  -- see nr₂p𝟘≤𝟙 and nr₂𝟘𝟙≤𝟙 above)

  nr-greatest-factoring :
    (has-nr : Has-nr exact-or-at-most-modality)
    (is-factoring-nr : Is-factoring-nr has-nr)
    (nr₂p𝟘≤𝟙 : ∀ {p} → Is-factoring-nr.nr₂ is-factoring-nr p 𝟘 ≤ 𝟙)
    (nr₂𝟘𝟙≤𝟙 : Is-factoring-nr.nr₂ is-factoring-nr 𝟘 𝟙 ≤ 𝟙) →
    ∀ p r z s n → Has-nr.nr has-nr p r z s n ≤ nr p r z s n
  nr-greatest-factoring has-nr is-factoring-nr nr₂p𝟘≤𝟙 nr₂𝟘𝟙≤𝟙 = λ where
    p r ∞ s n → lemma $ begin
      nr′ p r ∞ s n                ≡⟨ nr-factoring ⟩
      nr₂′ p r · n + nr′ p r ∞ s 𝟘 ≤⟨ +-monotoneʳ (nr-zero ≤-refl) ⟩
      nr₂′ p r · n + ∞             ≡⟨ +-zeroʳ _ ⟩
      ∞                            ∎
    p r z ∞ n → lemma $ begin
      nr′ p r z ∞ n                 ≤⟨ nr-suc ⟩
      ∞ + p · n + r · nr′ p r z ∞ n ≡⟨⟩
      ∞                             ∎
    p r z s ∞ → lemma $ begin
      nr′ p r z s ∞                ≡⟨ nr-factoring ⟩
      nr₂′ p r · ∞ + nr′ p r z s 𝟘 ≡⟨ +-congʳ (≢𝟘·∞ nr₂′≢𝟘) ⟩
      ∞ + nr′ p r z s 𝟘            ≡⟨⟩
      ∞                            ∎
    p r 𝟘 𝟘 𝟘 → begin
      nr′ p r 𝟘 𝟘 𝟘 ≡⟨ nr-𝟘 ⦃ has-nr ⦄ ⟩
      𝟘             ≡˘⟨ nr-𝟘 {p} {r} ⟩
      nr p r 𝟘 𝟘 𝟘  ∎
    ∞ r z s (≈/≤1+ b m) → lemma $ begin
      nr′ ∞ r z s (≈/≤1+ b m)             ≤⟨ nr-suc ⟩
      s + ∞ + r · nr′ ∞ r z s (≈/≤1+ b m) ≡⟨⟩
      s + ∞                               ≡⟨ +-zeroʳ s ⟩
      ∞                                   ∎
    p ∞ 𝟘 𝟘 (≈/≤1+ b m) → nr′p∞≤ λ ()
    p ∞ 𝟘 (≈/≤1+ b m) n → nr′p∞≤ λ ()
    p ∞ (≈/≤1+ b m) s n → nr′p∞≤ λ ()
    p 𝟘 z s n → begin
      nr′ p 𝟘 z s n ≡⟨ nr-factoring ⟩
      nr₂′ p 𝟘 · n + nr′ p 𝟘 z s 𝟘 ≤⟨ +-monotoneʳ (∧-greatest-lower-bound (nr-zero ≤-refl)
                                       (≤-trans nr-suc′ (≤-reflexive (+-identityʳ s)))) ⟩
      nr₂′ p 𝟘 · n + (z ∧ s)       ≤⟨ +-monotoneˡ (·-monotoneˡ (∧-greatest-lower-bound nr₂p𝟘≤𝟙
                                        (≤-trans (nr₂′≤ {p} {𝟘}) (≤-reflexive (+-identityʳ p))))) ⟩
      (𝟙 ∧ p) · n + (z ∧ s)        ≡⟨⟩
      nr p 𝟘 z s n                 ∎
    p r@(≈/≤1+ b 0) z s@(≈/≤1+ b′ m) n → lemma ∘→ ≤-reflexive ∘→ x≤y+x→x≡∞
                                           (≢𝟘+ {s} {p · n} (λ ())) $ begin
      nr′ p r z s n                   ≤⟨ nr-suc ⟩
      s + p · n + r · nr′ p r z s n   ≡˘⟨ +-assoc s (p · n) _ ⟩
      (s + p · n) + r · nr′ p r z s n ≤⟨ +-monotoneʳ {r = s + p · n} ≈𝟙/≤𝟙·-decreasing ⟩
      (s + p · n) + nr′ p r z s n     ∎
    p@(≈/≤1+ b′ m) r@(≈/≤1+ b 0) z s n@(≈/≤1+ b″ k) → lemma ∘→ ≤-reflexive ∘→ x≤y+x→x≡∞
                                                        (+≢𝟘 {p · n} {s} (λ ())) $ begin
      nr′ p r z s n                   ≤⟨ nr-suc ⟩
      s + p · n + r · nr′ p r z s n   ≡˘⟨ +-assoc s (p · n) _ ⟩
      (s + p · n) + r · nr′ p r z s n ≤⟨ +-monotoneʳ {r = s + p · n} ≈𝟙/≤𝟙·-decreasing ⟩
      (s + p · n) + nr′ p r z s n     ∎
    𝟘 𝟙 z 𝟘 n@(≈/≤1+ b m) → begin
      nr′ 𝟘 𝟙 z 𝟘 n ≡⟨ nr-factoring ⟩
      nr₂′ 𝟘 𝟙 · n + nr′ 𝟘 𝟙 z 𝟘 𝟘 ≤⟨ +-monotone (·-monotoneˡ nr₂𝟘𝟙≤𝟙) (nr-zero ≤-refl) ⟩
      𝟙 · n + z                    ≡⟨ +-cong (·-identityˡ n) (sym (·-identityˡ z)) ⟩
      n + 𝟙 · z                    ≡˘⟨ +-congˡ (+-identityʳ (𝟙 · z)) ⟩
      n + 𝟙 · z + 𝟘                ≡⟨⟩
      nr 𝟘 𝟙 z 𝟘 n                 ∎
    𝟘 ≤𝟙 z 𝟘 n@(≈/≤1+ b m) → begin
      nr′ 𝟘 ≤𝟙 z 𝟘 n ≡⟨ nr-factoring ⟩
      nr₂′ 𝟘 ≤𝟙 · n + nr′ 𝟘 ≤𝟙 z 𝟘 𝟘 ≤⟨ +-monotone (·-monotoneˡ nr₂′≤) nr-suc′ ⟩
      (≤𝟙 · nr₂′ 𝟘 ≤𝟙) · n + ≤𝟙 · nr′ 𝟘 ≤𝟙 z 𝟘 𝟘 ≤⟨ +-monotone (·-monotoneˡ (≤·≢𝟘-decreasing nr₂′≢𝟘))
                                                       (·-monotoneʳ (nr-zero ≤-refl)) ⟩
      ≤𝟙 · n + ≤𝟙 · z                 ≡˘⟨ +-congˡ (+-identityʳ (≤𝟙 · z)) ⟩
      ≤𝟙 · n + ≤𝟙 · z + 𝟘             ≡⟨⟩
      nr 𝟘 ≤𝟙 z 𝟘 n ∎
    p r@(≈/≤1+ b′ 0) z@(≈/≤1+ b m) 𝟘 𝟘 → begin
      nr′ p r z 𝟘 𝟘                               ≤⟨ nr-suc′ ⟩
      r · nr′ p r z 𝟘 𝟘                           ≤⟨ ·-monotoneʳ (nr-zero ≤-refl) ⟩
      r · z                                       ≡˘⟨ +-identityˡ (r · z) ⟩
      𝟘 + r · z                                   ≡˘⟨ +-congʳ (·-zeroʳ _) ⟩
      (≈/≤1+ (b′ B.∧ true) 0 + ∞ · p) · 𝟘 + r · z ≡⟨⟩
      nr p r z 𝟘 𝟘                                ∎
    p (≈/≤1+ b (1+ m)) 𝟘 𝟘 (≈/≤1+ b₁ m₁) → (lemma ∘→ ≤-reflexive ∘→ nr′p2+r≡∞) λ ()
    p (≈/≤1+ b (1+ m)) 𝟘 (≈/≤1+ b₁ m₁) n → (lemma ∘→ ≤-reflexive ∘→ nr′p2+r≡∞) λ ()
    p (≈/≤1+ b (1+ m)) (≈/≤1+ b₁ m₁) s n → (lemma ∘→ ≤-reflexive ∘→ nr′p2+r≡∞) λ ()
      where
      q≤p+rq→q≡∞ : q ≢ 𝟘 → q ≤ p + (≈/≤1+ b (1+ m)) · q → q ≡ ∞
      q≤p+rq→q≡∞ {q = 𝟘} q≢𝟘 _ = ⊥-elim (q≢𝟘 refl)
      q≤p+rq→q≡∞ {q = ≈/≤1+ _ k} {p = 𝟘} {m} _ q≤ =
        case ≈/≤1+-≤-inv q≤ of λ
          (_ , ≤k) →
        ⊥-elim (N.m+1+n≰m k (begin
          k +ⁿ 1+ (m * k +ⁿ (m +ⁿ k)) ≡˘⟨ cong (k +ⁿ_) (N.+-suc (m * k) (m +ⁿ k)) ⟩
          k +ⁿ (m * k +ⁿ 1+ (m +ⁿ k)) ≡˘⟨ N.+-assoc k (m * k) (1+ (m +ⁿ k)) ⟩
          k +ⁿ m * k +ⁿ 1+ (m +ⁿ k)   ≡˘⟨ N.+-assoc (k +ⁿ m * k) (1+ m) k ⟩
          k +ⁿ m * k +ⁿ 1+ m +ⁿ k     ≤⟨ ≤k ⟩
          k                           ∎))
        where
        open N.≤-Reasoning
      q≤p+rq→q≡∞ {q = ≈/≤1+ _ k} {p = ≈/≤1+ _ n} {m} _ q≤ =
        case ≈/≤1+-≤-inv q≤ of λ
          (_ , ≤k) →
        ⊥-elim (N.m+1+n≰m k (begin
          k +ⁿ 1+ (m * k +ⁿ m +ⁿ (k +ⁿ 1+ n))   ≡˘⟨ cong (λ x → k +ⁿ (x +ⁿ (k +ⁿ 1+ n))) (N.+-suc (m * k) m) ⟩
          k +ⁿ ((m * k +ⁿ 1+ m) +ⁿ (k +ⁿ 1+ n)) ≡˘⟨ N.+-assoc k (m * k +ⁿ 1+ m) (k +ⁿ 1+ n) ⟩
          k +ⁿ (m * k +ⁿ 1+ m) +ⁿ (k +ⁿ 1+ n)   ≡˘⟨ N.+-assoc (k +ⁿ (m * k +ⁿ 1+ m)) k (1+ n) ⟩
          (k +ⁿ (m * k +ⁿ 1+ m) +ⁿ k) +ⁿ 1+ n   ≡˘⟨ cong (_+ⁿ 1+ n) (cong (_+ⁿ k) (N.+-assoc k (m * k) (1+ m)) ) ⟩
          (k +ⁿ m * k +ⁿ 1+ m +ⁿ k) +ⁿ 1+ n     ≡⟨ N.+-comm (k +ⁿ m * k +ⁿ 1+ m +ⁿ k) (1+ n) ⟩
          1+ n +ⁿ (k +ⁿ m * k +ⁿ 1+ m +ⁿ k)     ≤⟨ ≤k ⟩
          k ∎))
        where
        open N.≤-Reasoning
      q≤p+rq→q≡∞ {q = ∞} q≢𝟘 q≤ = refl
      q≤p+rq→q≡∞ {q = ≈/≤1+ _ _} {p = ∞} _ ()
      x≤y+x→x≡∞ : ∀ {x y} → y ≢ 𝟘 → x ≤ y + x → x ≡ ∞
      x≤y+x→x≡∞ {x = 𝟘} {y = ∞} _ ()
      x≤y+x→x≡∞ {x = 𝟘} {y = ≈/≤1+ _ _} _ ()
      x≤y+x→x≡∞ {x = ≈/≤1+ _ _} {y = ∞} _ ()
      x≤y+x→x≡∞ {x = ∞} _ _ = refl
      x≤y+x→x≡∞ {y = 𝟘} y≢𝟘 _ = ⊥-elim (y≢𝟘 refl)
      x≤y+x→x≡∞ {x = ≈/≤1+ b m} {y = ≈/≤1+ b₁ n} _ x≤ =
        case ≈/≤1+-≤-inv x≤ of λ
          (_ , ≤m) →
        ⊥-elim (N.m+1+n≰m m (N.≤-trans (N.≤-reflexive (N.+-comm m (1+ n))) ≤m))
      ≢𝟘+ : p ≢ 𝟘 → p + q ≢ 𝟘
      ≢𝟘+ p≢𝟘 p+q≡𝟘 = p≢𝟘 (+-positiveˡ p+q≡𝟘)
      +≢𝟘 : q ≢ 𝟘 → p + q ≢ 𝟘
      +≢𝟘 q≢𝟘 p+q≡𝟘 = q≢𝟘 (+-positiveʳ p+q≡𝟘)

      open Has-nr has-nr
        renaming (nr to nr′; nr-positive to nr′-positive)
      open Is-factoring-nr is-factoring-nr
        renaming (nr₂ to nr₂′; nr₂≢𝟘 to nr₂′≢𝟘)

      nr₂′≡ : nr₂′ p r ≡ nr′ p r 𝟘 𝟘 𝟙
      nr₂′≡ {p} {r} = begin
        nr₂′ p r                     ≡˘⟨ ·-identityʳ _ ⟩
        nr₂′ p r · 𝟙                 ≡˘⟨ +-identityʳ _ ⟩
        nr₂′ p r · 𝟙 + 𝟘             ≡˘⟨ +-congˡ (nr-𝟘 ⦃ has-nr ⦄) ⟩
        nr₂′ p r · 𝟙 + nr′ p r 𝟘 𝟘 𝟘 ≡˘⟨ nr-factoring ⟩
        nr′ p r 𝟘 𝟘 𝟙                ∎
        where
        open RPe

      open RPo ≤-poset
      lemma : nr′ p r z s n ≤ ∞ → nr′ p r z s n ≤ nr p r z s n
      lemma nr′≤∞ = ≤-trans nr′≤∞ refl
      nr-suc′ : nr′ p r z s 𝟘 ≤ s + r · nr′ p r z s 𝟘
      nr-suc′ {p} {r} {z} {s} = begin
        nr′ p r z s 𝟘 ≤⟨ nr-suc ⟩
        s + p · 𝟘 + r · nr′ p r z s 𝟘 ≡⟨ +-congˡ {s} (+-congʳ (·-zeroʳ p)) ⟩
        s + 𝟘 + r · nr′ p r z s 𝟘 ≡⟨⟩
        s + r · nr′ p r z s 𝟘 ∎
      nr₂′≤ : nr₂′ p r ≤ p + r · nr₂′ p r
      nr₂′≤ {p} {r} = begin
        nr₂′ p r                   ≡⟨ nr₂′≡ ⟩
        nr′ p r 𝟘 𝟘 𝟙              ≤⟨ nr-suc ⟩
        p · 𝟙 + r · nr′ p r 𝟘 𝟘 𝟙 ≡⟨ +-cong (·-identityʳ p) (·-congˡ (sym nr₂′≡)) ⟩
        p + r · nr₂′ p r           ∎
      nr′p∞≤ : ¬ (z ≡ 𝟘 × s ≡ 𝟘 × n ≡ 𝟘) → nr′ p ∞ z s n ≤ nr p ∞ z s n
      nr′p∞≤ {z} {s} {n} {p} ≢𝟘 = lemma $ begin
        nr′ p ∞ z s n                 ≤⟨ nr-suc ⟩
        s + p · n + ∞ · nr′ p ∞ z s n ≡⟨ +-congˡ {s} (+-congˡ (∞·≢𝟘 (≢𝟘 ∘→ nr′-positive))) ⟩
        s + p · n + ∞                 ≡⟨ +-congˡ (+-zeroʳ _) ⟩
        s + ∞                         ≡⟨ +-zeroʳ s ⟩
        ∞                             ∎

      nr′p2+r≡∞ : ¬ (z ≡ 𝟘 × s ≡ 𝟘 × n ≡ 𝟘) → nr′ p (≈/≤1+ b (1+ m)) z s n ≡ ∞
      nr′p2+r≡∞ {z} {s} {n} {p} {b} {m} ≢𝟘 = q≤p+rq→q≡∞ (≢𝟘 ∘→ nr′-positive) $ begin
        nr′ p (≈/≤1+ b (1+ m)) z s n                                ≤⟨ nr-suc ⟩
        s + p · n + ≈/≤1+ b (1+ m) · nr′ p (≈/≤1+ b (1+ m)) z s n   ≡˘⟨ +-assoc s (p · n) _ ⟩
        (s + p · n) + ≈/≤1+ b (1+ m) · nr′ p (≈/≤1+ b (1+ m)) z s n ∎

------------------------------------------------------------------------
-- Instances of Full-reduction-assumptions

module _ {𝟘ᵐ-allowed : Bool} where

  open Graded.Mode.Instances.Zero-one.Variant exact-or-at-most-modality

  private opaque

    variant : Mode-variant
    variant = record
      { 𝟘ᵐ-allowed = 𝟘ᵐ-allowed
      ; 𝟘-well-behaved = λ _ → exact-or-at-most-has-well-behaved-zero
      }

  open Graded.Mode.Instances.Zero-one   variant
  open Definition.Typed.Restrictions    exact-or-at-most-modality
  open Graded.Usage.Restrictions        exact-or-at-most-modality Zero-one-isMode
  open Graded.FullReduction.Assumptions variant

  private variable
    TR : Type-restrictions
    UR : Usage-restrictions

  -- Instances of Type-restrictions and Usage-restrictions are suitable
  -- for the full reduction theorem if
  -- * whenever Unitˢ-allowed holds, then Starˢ-sink holds,
  -- * Unitʷ-allowed and Unitʷ-η do not both hold,
  -- * Σˢ-allowed p q holds only if p ≡ 𝟙.

  Suitable-for-full-reduction :
    Type-restrictions →
    Usage-restrictions →
    Set
  Suitable-for-full-reduction TR UR =
    (Unitˢ-allowed → Starˢ-sink) ×
    (Unitʷ-allowed → ¬ Unitʷ-η) ×
    (∀ p q → Σˢ-allowed p q → p ≡ 𝟙)
    where
    open Type-restrictions  TR
    open Usage-restrictions UR

  opaque

    -- Given an instance of Type-restrictions exact-or-at-most-modality
    -- one can create a "suitable" instance.

    suitable-for-full-reduction :
      Type-restrictions →
      ∃ λ TR → Suitable-for-full-reduction TR UR
    suitable-for-full-reduction {UR} TR =
        record TR
          { Unit-allowed = λ where
              𝕤 → Unitˢ-allowed × Starˢ-sink
              𝕨 → Unitʷ-allowed × ¬ Unitʷ-η
          ; ΠΣ-allowed = λ b p q →
              ΠΣ-allowed b p q × (b ≡ BMΣ 𝕤 → p ≡ 𝟙)
          ; []-cong-allowed = λ where
              𝕤 → ⊥
              𝕨 → []-congʷ-allowed × ¬ Unitʷ-η
          ; []-cong→Erased = λ where
              {s = 𝕤} ()
              {s = 𝕨} (ok , no-η) →
                case []-cong→Erased ok of λ
                  (ok₁ , ok₂) →
                (ok₁ , no-η) , ok₂ , λ ()
          ; []-cong→¬Trivial = λ where
              {s = 𝕤} ()
              {s = 𝕨} (ok , no-η) → []-cong→¬Trivial ok
          }
      , proj₂
      , proj₂
      , λ _ _ ok → proj₂ ok refl
      where
      open Type-restrictions  TR
      open Usage-restrictions UR

  opaque

    -- The full reduction assumptions hold for any instance of
    -- exact-or-at-most-modality and any "suitable" Type-restrictions and
    -- Usage-restrictions.

    full-reduction-assumptions :
      Suitable-for-full-reduction TR UR →
      Full-reduction-assumptions TR UR
    full-reduction-assumptions (sink , no-η , Σ-ok) = record
      { sink⊎𝟙≤𝟘 = λ where
          {s = 𝕤} ok η-ok → inj₁ (refl , sink ok)
          {s = 𝕨} ok (inj₁ ())
          {s = 𝕨} ok (inj₂ η) → ⊥-elim (no-η ok η)
      ; ≡𝟙⊎𝟙≤𝟘 = λ where
          {p} ok → inj₁ (Σ-ok p _ ok)
      }

  opaque

    -- Type and usage restrictions that satisfy the full reduction
    -- assumptions are "suitable".

    full-reduction-assumptions-suitable :
      Full-reduction-assumptions TR UR →
      Suitable-for-full-reduction TR UR
    full-reduction-assumptions-suitable as =
        (λ ok → case sink⊎𝟙≤𝟘 ok (inj₁ refl) of λ where
           (inj₁ (_ , sink)) → sink
           (inj₂ ()))
      , (λ ok η → case sink⊎𝟙≤𝟘 ok (inj₂ η) of λ where
           (inj₁ ())
           (inj₂ ()))
      , λ _ _ Σ-ok → case ≡𝟙⊎𝟙≤𝟘 Σ-ok of λ where
          (inj₁ p≡𝟙) → p≡𝟙
          (inj₂ ())
      where
      open Full-reduction-assumptions _ _ as

------------------------------------------------------------------------
-- Subtraction

open import Graded.Modality.Properties.Subtraction
  exact-or-at-most-modality

opaque

  -- Subtraction of p by ∞ is not possible unless p ≡ ∞

  p-∞≰ : p - ∞ ≤ q → p ≡ ∞
  p-∞≰ {(𝟘)} {(𝟘)} ()
  p-∞≰ {(𝟘)} {≈/≤1+ b m} ()
  p-∞≰ {(𝟘)} {(∞)} ()
  p-∞≰ {≈/≤1+ b m} {(𝟘)} ()
  p-∞≰ {≈/≤1+ b m} {≈/≤1+ b₁ m₁} ()
  p-∞≰ {≈/≤1+ b m} {(∞)} ()
  p-∞≰ {(∞)} {(q)} x = refl

opaque

  -- A kind of inversion lemma for subtraction.
  -- Subtraction of ≈/≤1+ b m by ≈/≤1+ b′ k is only defined if k ≤ m and b ≤ b′

  ≈/≤m-≈/≤n≤-inv : ≈/≤1+ b m - ≈/≤1+ b′ k ≤ r → k N.≤ m × b B.≤ᵇ b′
  ≈/≤m-≈/≤n≤-inv                  {r = ∞} ()
  ≈/≤m-≈/≤n≤-inv {b} {m} {b′} {k} {r = 𝟘} m-n≤r =
    case ≈/≤1+-injective m-n≤r of λ
      (b≡ , m≡m⊔k) →
    N.m⊔n≡m⇒n≤m (sym m≡m⊔k) , (begin
      b                         ≡⟨ b≡ ⟩
      (b B.∧ b′) B.∧ (m N.== k) ≤⟨ B.∧-decreasingˡ ⟩
      b B.∧ b′                  ≤⟨ B.∧-decreasingʳ ⟩
      b′                        ∎)
    where
    open B.≤ᵇ-Reasoning
  ≈/≤m-≈/≤n≤-inv {b} {m} {b′} {k} {r = ≈/≤1+ b″ n} m-n≤r =
    case ≈/≤1+-injective m-n≤r of λ
      (b≡ , m≡m⊔) →
      lemma₁ (N.m⊔n≡m⇒n≤m (sym m≡m⊔))
    , lemma₂ b≡
    where
    lemma₁ : 1+ (n +ⁿ k) N.≤ m → k N.≤ m
    lemma₁ ≤m = begin
      k           ≤⟨ N.m≤n+m k n ⟩
      n +ⁿ k      ≤⟨ N.n≤1+n (n +ⁿ k) ⟩
      1+ (n +ⁿ k) ≤⟨ ≤m ⟩
      m           ∎
      where
      open N.≤-Reasoning
    lemma₂ : b ≡ (b B.∧ b″ B.∧ b′) B.∧ (m N.== 1+ (n +ⁿ k)) → b B.≤ᵇ b′
    lemma₂ b≡ = begin
      b                                          ≡⟨ b≡ ⟩
      (b B.∧ b″ B.∧ b′) B.∧ (m N.== 1+ (n +ⁿ k)) ≤⟨ B.∧-decreasingˡ ⟩
      b B.∧ b″ B.∧ b′                            ≤⟨ B.∧-decreasingʳ {b} ⟩
      b″ B.∧ b′                                  ≤⟨ B.∧-decreasingʳ ⟩
      b′                                         ∎
      where
      open B.≤ᵇ-Reasoning

opaque private

  ≈/≤m-≈/≤n≤-lemma : k N.< m → 1+ (m N.∸ 1+ k +ⁿ k) ≡ m
  ≈/≤m-≈/≤n≤-lemma {k} {m} k<m = begin
    1+ (m N.∸ 1+ k +ⁿ k) ≡˘⟨ N.+-suc (m N.∸ 1+ k) k ⟩
    m N.∸ 1+ k +ⁿ 1+ k   ≡⟨ N.m∸n+n≡m k<m ⟩
    m                    ∎
    where
    open RPe

opaque

  -- Subtraction of ≈/≤1+ b m by ≈/≤1+ b′ k is ≈/≤1+ (b ∧ b′) (m ∸ 1+ k)
  -- when k < m and b ≤ b′

  ≈/≤m-≈/≤n≤ : k N.< m → b B.≤ᵇ b′
             → ≈/≤1+ b m - ≈/≤1+ b′ k ≤ ≈/≤1+ (b B.∧ b′) (m N.∸ 1+ k)
  ≈/≤m-≈/≤n≤ {k} {m} {b} {b′} k<m b≤b′ rewrite ≈/≤m-≈/≤n≤-lemma k<m =
    flip (cong₂ ≈/≤1+) (sym (N.⊔-idem m)) $ begin
    b                                        ≡˘⟨ B.≤ᵇ-∧ b≤b′ ⟩
    b B.∧ b′                                 ≡˘⟨ B.∧-idem (b B.∧ b′) ⟩
    (b B.∧ b′) B.∧ b B.∧ b′                  ≡˘⟨ B.∧-assoc (b B.∧ b′) b b′ ⟩
    ((b B.∧ b′) B.∧ b) B.∧ b′                ≡⟨ cong (B._∧ b′) (B.∧-assoc b b′ b) ⟩
    (b B.∧ b′ B.∧ b) B.∧ b′                  ≡⟨ cong (λ x → (b B.∧ x) B.∧ b′) (B.∧-comm b′ b) ⟩
    (b B.∧ b B.∧ b′) B.∧ b′                  ≡⟨ B.∧-assoc b (b B.∧ b′) b′ ⟩
    b B.∧ (b B.∧ b′) B.∧ b′                  ≡˘⟨ B.∧-identityʳ _ ⟩
    (b B.∧ (b B.∧ b′) B.∧ b′) B.∧ true       ≡˘⟨ cong ((b B.∧ (b B.∧ b′) B.∧ b′) B.∧_) (N.==-refl m) ⟩
    (b B.∧ (b B.∧ b′) B.∧ b′) B.∧ (m N.== m) ∎
    where
    open RPe

opaque

  -- Subtraction of ≈/≤1+ b m by ≈/≤1+ b′ k is ≈/≤1+ (b ∧ b′) (m ∸ 1+ k)
  -- when k < m and b ≤ b′

  ≈/≤m-≈/≤n≡ : k N.< m → b B.≤ᵇ b′
             → ≈/≤1+ b m - ≈/≤1+ b′ k ≡ ≈/≤1+ (b B.∧ b′) (m N.∸ 1+ k)
  ≈/≤m-≈/≤n≡ {k} {m} {b} {b′} k<m b≤b′ =
    ≈/≤m-≈/≤n≤ k<m b≤b′ , λ where
      ∞ ()
      𝟘 x  →
        case ≈/≤1+-injective x of λ
          (b≡ , _) →
        cong (λ b → ≈/≤1+ b _) $ begin
          b B.∧ b′                           ≡⟨ cong (B._∧ b′) b≡ ⟩
          ((b B.∧ b′) B.∧ (m N.== k)) B.∧ b′ ≡⟨ cong (λ x → ((b B.∧ b′) B.∧ x) B.∧ b′) (N.<⇒¬== k<m) ⟩
          ((b B.∧ b′) B.∧ false) B.∧ b′      ≡⟨ cong (B._∧ b′) (B.∧-zeroʳ (b B.∧ b′)) ⟩
          false B.∧ b′                       ≡⟨ B.∧-zeroˡ b′ ⟩
          false                              ∎
      (≈/≤1+ b″ n) x →
        case ≈/≤1+-injective x of λ
          (b≡ , m≡) →
        case begin
            b B.∧ b′                                                   ≡⟨ cong (B._∧ b′) b≡ ⟩
            ((b B.∧ b″ B.∧ b′) B.∧ (m N.== 1+ (n +ⁿ k))) B.∧ b′        ≡⟨ B.∧-assoc (b B.∧ b″ B.∧ b′) (m N.== 1+ (n +ⁿ k)) b′ ⟩
            (b B.∧ b″ B.∧ b′) B.∧ (m N.== 1+ (n +ⁿ k)) B.∧ b′          ≡˘⟨ cong₂ B._∧_ (B.∧-assoc b b″ b′)
                                                                                       (B.∧-comm b′ (m N.== 1+ (n +ⁿ k))) ⟩
            ((b B.∧ b″) B.∧ b′) B.∧ b′ B.∧ (m N.== 1+ (n +ⁿ k))        ≡˘⟨ B.∧-assoc ((b B.∧ b″) B.∧ b′) b′ (m N.== 1+ (n +ⁿ k)) ⟩
            (((b B.∧ b″) B.∧ b′) B.∧ b′) B.∧ (m N.== 1+ (n +ⁿ k))      ≡⟨ cong (B._∧ (m N.== 1+ (n +ⁿ k))) (B.∧-assoc (b B.∧ b″) b′ b′) ⟩
            ((b B.∧ b″) B.∧ b′ B.∧ b′) B.∧ (m N.== 1+ (n +ⁿ k))        ≡⟨ cong (λ x → ((b B.∧ b″) B.∧ x) B.∧ (m N.== 1+ (n +ⁿ k))) (B.∧-idem b′) ⟩
            ((b B.∧ b″) B.∧ b′) B.∧ (m N.== 1+ (n +ⁿ k))               ≡⟨ cong₂ B._∧_ (B.∧-assoc b b″ b′)
                                                                                      (cong (m N.==_) (sym (N.+-suc n k))) ⟩
            (b B.∧ b″ B.∧ b′) B.∧ (m N.== (n +ⁿ 1+ k))                 ≡⟨ cong₂ B._∧_ (cong (b B.∧_) (B.∧-comm b″ b′))
                                                                                      (N.<⇒==∸ k<m (N.m≤n+m (1+ k) n)) ⟩
            (b B.∧ b′ B.∧ b″) B.∧ (m N.∸ 1+ k N.== n +ⁿ 1+ k N.∸ 1+ k) ≡⟨ cong₂ B._∧_ (sym (B.∧-assoc b b′ b″))
                                                                                      (cong (m N.∸ 1+ k N.==_) (N.m+n∸n≡m n (1+ k))) ⟩
            ((b B.∧ b′) B.∧ b″) B.∧ (m N.∸ 1+ k N.== n)                ∎ of λ
          b∧b′≡ →
        case begin
            m N.∸ 1+ k                          ≡⟨ cong (N._∸ 1+ k) m≡ ⟩
            (m ⊔ 1+ (n +ⁿ k)) N.∸ 1+ k          ≡⟨ N.∸-distribʳ-⊔ (1+ k) m (1+ (n +ⁿ k)) ⟩
            m N.∸ 1+ k ⊔ (1+ (n +ⁿ k) N.∸ 1+ k) ≡˘⟨ cong (λ x → m N.∸ 1+ k ⊔ (x N.∸ 1+ k)) (N.+-suc n k) ⟩
            m N.∸ 1+ k ⊔ (n +ⁿ 1+ k N.∸ 1+ k)   ≡⟨ cong (m N.∸ 1+ k ⊔_) (N.m+n∸n≡m n (1+ k)) ⟩
            m N.∸ 1+ k ⊔ n                      ∎ of λ
          m-1+k≡ →
        cong₂ ≈/≤1+ b∧b′≡ m-1+k≡
    where
    open RPe

opaque

  -- Subtraction of ≈/≤1+ b m by ≈/≤1+ b′ m is at most 𝟘 when b ≤ b′

  ≈/≤m-≈/≤m≤𝟘 : b B.≤ᵇ b′ → ≈/≤1+ b m - ≈/≤1+ b′ m ≤ 𝟘
  ≈/≤m-≈/≤m≤𝟘 {b} {b′} {m} b≤b′ =
    flip (cong₂ ≈/≤1+) (sym (N.⊔-idem m)) $ begin
      b                         ≡˘⟨ B.≤ᵇ-∧ b≤b′ ⟩
      b B.∧ b′                  ≡˘⟨ B.∧-identityʳ (b B.∧ b′) ⟩
      (b B.∧ b′) B.∧ true       ≡˘⟨ cong ((b B.∧ b′) B.∧_) (N.==-refl m) ⟩
      (b B.∧ b′) B.∧ (m N.== m) ∎
    where
    open RPe

opaque

  -- Subtraction of ≈/≤1+ b m by ≈/≤1+ b′ m is 𝟘
  -- when b ≤ b′

  ≈/≤m-≈/≤m≡𝟘 : b B.≤ᵇ b′ → ≈/≤1+ b m - ≈/≤1+ b′ m ≡ 𝟘
  ≈/≤m-≈/≤m≡𝟘 {m} b≤b′ =
    ≈/≤m-≈/≤m≤𝟘 b≤b′ , λ where
      ∞            ()
      𝟘            _  → refl
      (≈/≤1+ b″ n) x  →
        case ≈/≤1+-injective x of λ
          (_ , m≡) →
        case N.m⊔n≡m⇒n≤m (sym m≡) of λ
          ≤m →
        case N.≤-trans (N.m≤n+m (1+ m) n) (N.≤-reflexive (N.+-suc n m)) of λ
          1+m≤ →
        case N.≤-antisym (N.n≤1+n m) (N.≤-trans 1+m≤ ≤m) of λ
          ()

opaque

  -- Subtraction is supported with
  --   ∞ - p ≡ ∞ for any p
  --   p - 𝟘 ≡ p for any p
  --   ≈1+ m - ≈1+ m ≡ 𝟘
  --   ≤1+ m - ≤1+ m ≡ 𝟘
  --   ≤1+ m - ≈1+ m ≡ 𝟘
  --   ≈1+ m - ≈1+ n ≡ ≈1+ (m ∸ 1+ n) if n < m
  --   ≤1+ m - ≤1+ n ≡ ≤1+ (m ∸ 1+ n) if n < m
  --   ≤1+ m - ≈1+ n ≡ ≤1+ (m ∸ 1+ n) if n < m
  -- and not defined otherwise

  supports-subtraction : Supports-subtraction
  supports-subtraction {(∞)} {(q)} {(r)} refl = ∞ , ∞-p≡∞ refl q
  supports-subtraction {(𝟘)} {q} {r} p-q≤r =
    case 𝟘-p≤q {q = r} p-q≤r of λ {
      (refl , refl) →
    𝟘 , p-𝟘≡p }
  supports-subtraction {p} {(∞)} {r} p-q≤r =
    case p-∞≰ {q = r} p-q≤r of λ {
      refl →
    ∞ , ∞-p≡∞ refl ∞ }
  supports-subtraction {p} {(𝟘)} {r} p-q≤r =
    p , p-𝟘≡p
  supports-subtraction {≈/≤1+ b m} {≈/≤1+ b′ n} {(r)} p-q≤r =
    case ≈/≤m-≈/≤n≤-inv p-q≤r of λ
      (n<m , b≤b′) →
    case n N.≟ m of λ where
      (yes refl) →
        𝟘 , ≈/≤m-≈/≤m≡𝟘 b≤b′
      (no n≢m) →
        ≈/≤1+ (b B.∧ b′) (m N.∸ 1+ n) , ≈/≤m-≈/≤n≡ (N.≤∧≢⇒< n<m n≢m) b≤b′

-- An alternative definition of the subtraction relation with
--   ∞ - p ≡ ∞ for any p
--   p - 𝟘 ≡ p for any p
--   ≈1+ m - ≈1+ m ≡ 𝟘
--   ≤1+ m - ≤1+ m ≡ 𝟘
--   ≤1+ m - ≈1+ m ≡ 𝟘
--   ≈1+ m - ≈1+ n ≡ ≈1+ (m ∸ 1+ n) if n ≤ m
--   ≤1+ m - ≤1+ n ≡ ≤1+ (m ∸ 1+ n) if n ≤ m
--   ≤1+ m - ≈1+ n ≡ ≤1+ (m ∸ 1+ n) if n ≤ m
-- and not defined otherwise

data _-_≡′_ : (p q r : Exact-or-at-most) → Set where
  ∞-p≡′∞ : ∞ - p ≡′ ∞
  p-𝟘≡′p : p - 𝟘 ≡′ p
  ≈1+m-≈1+m≡′𝟘 : ≈1+ m - ≈1+ m ≡′ 𝟘
  ≤1+m-≤1+m≡′𝟘 : ≤1+ m - ≤1+ m ≡′ 𝟘
  ≤1+m-≈1+m≡′𝟘 : ≤1+ m - ≈1+ m ≡′ 𝟘
  ≈1+m-≈1+n≡′≈1+m∸n : k N.< m → ≈1+ m - ≈1+ k ≡′ ≈1+ (m N.∸ 1+ k)
  ≤1+m-≤1+n≡′≤1+m∸n : k N.< m → ≤1+ m - ≤1+ k ≡′ ≤1+ (m N.∸ 1+ k)
  ≤1+m-≈1+n≡′≤1+m∸n : k N.< m → ≤1+ m - ≈1+ k ≡′ ≤1+ (m N.∸ 1+ k)

opaque

  -- The two subtraction relations are equivalent.

  -≡↔-≡′ : ∀ p q r → (p - q ≡ r) ⇔ (p - q ≡′ r)
  -≡↔-≡′ p q r = left p q r , right
    where
    lemma₁ : b B.≤ᵇ b′ → ≈/≤1+ b m - ≈/≤1+ b′ m ≡′ 𝟘
    lemma₁ {b = false} {b′ = false} B.b≤b = ≤1+m-≤1+m≡′𝟘
    lemma₁ {b = false} {b′ = true}  B.f≤t = ≤1+m-≈1+m≡′𝟘
    lemma₁ {b = true}  {b′ = true}  B.b≤b = ≈1+m-≈1+m≡′𝟘
    lemma₁ {b = true}  {b′ = false} ()
    lemma₂ : b B.≤ᵇ b′ → k N.< m → ≈/≤1+ b m - ≈/≤1+ b′ k ≡′ ≈/≤1+ (b B.∧ b′) (m N.∸ 1+ k)
    lemma₂ {b = false} {b′ = false} B.b≤b n<m = ≤1+m-≤1+n≡′≤1+m∸n n<m
    lemma₂ {b = false} {b′ = true}  B.f≤t n<m = ≤1+m-≈1+n≡′≤1+m∸n n<m
    lemma₂ {b = true}  {b′ = true}  B.b≤b n<m = ≈1+m-≈1+n≡′≈1+m∸n n<m
    lemma₂ {b = true}  {b′ = false} ()
    left : ∀ p q r → p - q ≡ r → p - q ≡′ r
    left ∞ q r p-q≡r =
      case -≡-functional {q = q} p-q≡r (∞-p≡∞ refl q) of λ {
        refl →
      ∞-p≡′∞ }
    left p 𝟘 r p-q≡r =
      case -≡-functional p-q≡r p-𝟘≡p of λ {
        refl →
      p-𝟘≡′p }
    left 𝟘 q r p-q≡r =
      case 𝟘-p≡q p-q≡r of λ {
        (refl , refl) →
      p-𝟘≡′p }
    left p ∞ r p-q≡r =
      case p-∞≰ (p-q≡r .proj₁) of λ {
        refl →
      case -≡-functional {q = ∞} p-q≡r (∞-p≡∞ refl ∞) of λ {
        refl →
      ∞-p≡′∞ }}
    left (≈/≤1+ b m) (≈/≤1+ b′ n) r p-q≡r =
      case ≈/≤m-≈/≤n≤-inv (p-q≡r .proj₁) of λ
        (n≤m , b≤b′) →
      case n N.≟ m of λ where
        (yes refl) →
          case -≡-functional p-q≡r (≈/≤m-≈/≤m≡𝟘 b≤b′) of λ {
            refl →
          lemma₁ b≤b′ }
        (no n≢m) →
          case N.≤∧≢⇒< n≤m n≢m of λ
            n<m →
          case -≡-functional p-q≡r (≈/≤m-≈/≤n≡ n<m b≤b′) of λ {
            refl →
          lemma₂ b≤b′ n<m }
    right : p - q ≡′ r → p - q ≡ r
    right ∞-p≡′∞ = ∞-p≡∞ refl p
    right p-𝟘≡′p = p-𝟘≡p
    right ≈1+m-≈1+m≡′𝟘 = ≈/≤m-≈/≤m≡𝟘 B.b≤b
    right ≤1+m-≤1+m≡′𝟘 = ≈/≤m-≈/≤m≡𝟘 B.b≤b
    right ≤1+m-≈1+m≡′𝟘 = ≈/≤m-≈/≤m≡𝟘 B.f≤t
    right (≈1+m-≈1+n≡′≈1+m∸n x) = ≈/≤m-≈/≤n≡ x B.b≤b
    right (≤1+m-≤1+n≡′≤1+m∸n x) = ≈/≤m-≈/≤n≡ x B.b≤b
    right (≤1+m-≈1+n≡′≤1+m∸n x) = ≈/≤m-≈/≤n≡ x B.f≤t
