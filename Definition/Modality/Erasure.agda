{-# OPTIONS --without-K --safe #-}

module Definition.Modality.Erasure where

open import Tools.Product
open import Tools.PropositionalEquality

data Erasure : Set where
  𝟘 ω : Erasure

open import Definition.Modality Erasure _≡_ public
open import Tools.Algebra {A = Erasure} _≡_
open import Tools.Nat hiding (_+_)

_+_ : Op₂ Erasure
x + 𝟘 = x
x + ω = ω

_·_ : Op₂ Erasure
x · 𝟘 = 𝟘
x · ω = x

_∧_ : Op₂ Erasure
_∧_ = _+_

nr : Op₃ Erasure
nr 𝟘 q 𝟘 = q
nr 𝟘 𝟘 ω = 𝟘
nr 𝟘 ω ω = ω
nr ω q r = ω

nrⁿ : Nat → Op₃ Erasure
nrⁿ Nat.zero p q r = 𝟘
nrⁿ (1+ n) p q r = p ∧ (q + (r · (nrⁿ n p q r)))

nr-fix₁ : (p q r : Erasure) → (p ∧ (q + (r · (p ∧ q)))) ≡ (p ∧ q)
nr-fix₁ 𝟘 𝟘 𝟘 = refl
nr-fix₁ 𝟘 𝟘 ω = refl
nr-fix₁ 𝟘 ω 𝟘 = refl
nr-fix₁ 𝟘 ω ω = refl
nr-fix₁ ω 𝟘 𝟘 = refl
nr-fix₁ ω 𝟘 ω = refl
nr-fix₁ ω ω 𝟘 = refl
nr-fix₁ ω ω ω = refl

nr-fix : ∃ (λ n → (p q r : Erasure) → (p ∧ (q + (r · nrⁿ n p q r))) ≡ nrⁿ n p q r)
nr-fix = 1 , nr-fix₁

_≤_ : (p q : Erasure) → Set
p ≤ q = p ≡ p ∧ q

-- Properties of addition (and meet)

+-Congruent : Congruent₂ _+_
+-Congruent refl refl = refl

+-Commutative : Commutative _+_
+-Commutative 𝟘 𝟘 = refl
+-Commutative 𝟘 ω = refl
+-Commutative ω 𝟘 = refl
+-Commutative ω ω = refl

+-Associative : Associative _+_
+-Associative x y 𝟘 = refl
+-Associative x y ω = refl

+-Idempotent : Idempotent _+_
+-Idempotent 𝟘 = refl
+-Idempotent ω = refl

+-LeftIdentity : LeftIdentity 𝟘 _+_
+-LeftIdentity 𝟘 = refl
+-LeftIdentity ω = refl

+-RightIdentity : RightIdentity 𝟘 _+_
+-RightIdentity x = refl

+-Identity : Identity 𝟘 _+_
+-Identity = +-LeftIdentity , +-RightIdentity

+-positive : (p q : Erasure) → 𝟘 ≤ (p + q) → 𝟘 ≤ p × 𝟘 ≤ q
+-positive 𝟘 𝟘 refl = refl , refl
+-positive 𝟘 ω ()
+-positive ω 𝟘 ()
+-positive ω ω ()


-- Properties of multiplication
·-Congruent : Congruent₂ _·_
·-Congruent = cong₂ _·_

·-Associative : Associative _·_
·-Associative x y 𝟘 = refl
·-Associative x y ω = refl

·-LeftZero : LeftZero 𝟘 _·_
·-LeftZero 𝟘 = refl
·-LeftZero ω = refl

·-RightZero : RightZero 𝟘 _·_
·-RightZero x = refl

·-zero : Zero 𝟘 _·_
·-zero = ·-LeftZero , ·-RightZero

·-LeftIdentity : LeftIdentity ω _·_
·-LeftIdentity 𝟘 = refl
·-LeftIdentity ω = refl

·-RightIdentity : RightIdentity ω _·_
·-RightIdentity x = refl

·-Identity : Identity ω _·_
·-Identity = ·-LeftIdentity , ·-RightIdentity


-- Distributive properties of addition, multiplication (and meet)
·-distribˡ-+ : _·_ DistributesOverˡ _+_
·-distribˡ-+ x y 𝟘 = refl
·-distribˡ-+ ω y ω = refl
·-distribˡ-+ 𝟘 𝟘 ω = refl
·-distribˡ-+ 𝟘 ω ω = refl

·-distribʳ-+ : _·_ DistributesOverʳ _+_
·-distribʳ-+ 𝟘 y z = refl
·-distribʳ-+ ω y z = refl

·-distrib-+ : _·_ DistributesOver _+_
·-distrib-+ = ·-distribˡ-+ , ·-distribʳ-+

+-distribˡ-+ : _+_ DistributesOverˡ _+_
+-distribˡ-+ x y ω = refl
+-distribˡ-+ 𝟘 y 𝟘 = refl
+-distribˡ-+ ω 𝟘 𝟘 = refl
+-distribˡ-+ ω ω 𝟘 = refl

+-distribʳ-+ : _+_ DistributesOverʳ _+_
+-distribʳ-+ 𝟘 y z = refl
+-distribʳ-+ ω y z = refl

+-distrib-+ : _+_ DistributesOver _+_
+-distrib-+ = +-distribˡ-+ , +-distribʳ-+

-- Addition (and meet) form the following algebras

+-Magma : IsMagma _+_
+-Magma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = +-Congruent
  }

+-Semigroup : IsSemigroup _+_
+-Semigroup = record
  { isMagma = +-Magma
  ; assoc   = +-Associative
  }

+-Monoid : IsMonoid _+_ 𝟘
+-Monoid = record
  { isSemigroup = +-Semigroup
  ; identity    = +-Identity
  }

+-CommutativeMonoid : IsCommutativeMonoid _+_ 𝟘
+-CommutativeMonoid = record
  { isMonoid = +-Monoid
  ; comm     = +-Commutative
  }

+-Band : IsBand _+_
+-Band = record
  { isSemigroup = +-Semigroup
  ; idem        = +-Idempotent
  }

+-Semilattice : IsSemilattice _+_
+-Semilattice = record
  { isBand = +-Band
  ; comm   = +-Commutative
  }


-- Multiplication forms the following algebras

·-Magma : IsMagma _·_
·-Magma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = ·-Congruent
  }

·-Semigroup : IsSemigroup _·_
·-Semigroup = record
  { isMagma = ·-Magma
  ; assoc   = ·-Associative
  }

·-Monoid : IsMonoid _·_ ω
·-Monoid = record
  { isSemigroup = ·-Semigroup
  ; identity    = ·-Identity
  }

ErasureModality : Modality
ErasureModality = record
  { _+_                 = _+_
  ; _·_                 = _·_
  ; _∧_                 = _∧_
  ; nrⁿ                 = nrⁿ
  ; 𝟘                   = 𝟘
  ; 𝟙                   = ω
  ; +-CommutativeMonoid = +-CommutativeMonoid
  ; ·-Monoid            = ·-Monoid
  ; ∧-Semilattice       = +-Semilattice
  ; ·-zero              = ·-zero
  ; +-positive          = +-positive
  ; nrⁿ-rec             = λ n p q r → refl
  ; nrⁿ-0               = λ p q r → refl
  ; nrⁿ-fix             = nr-fix
  ; ·-distrib-+         = ·-distrib-+
  ; ·-distrib-∧         = ·-distrib-+
  ; +-distrib-∧         = +-distrib-+
  ; ≈-equivalence       = isEquivalence
  }
