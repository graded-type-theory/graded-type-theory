{-# OPTIONS --without-K --safe #-}

module Definition.Modality.Erasure where

open import Tools.Product
open import Tools.PropositionalEquality

-- The set of erasure annotations with 𝟘 corresponding to no usage
-- and ω to any usage.

data Erasure : Set where
  𝟘 ω : Erasure

open import Definition.Modality Erasure _≡_ public
open import Tools.Algebra {A = Erasure} _≡_
open import Tools.Nat hiding (_+_)

-- Addition of erasure annotations

_+_ : Op₂ Erasure
x + 𝟘 = x
x + ω = ω

-- Multiplication of erasure annotations

_·_ : Op₂ Erasure
x · 𝟘 = 𝟘
x · ω = x

-- Meet for erasure annotations coincides with addition

_∧_ : Op₂ Erasure
_∧_ = _+_

-- Natrec recurrence function

nr : Op₃ Erasure
nr 𝟘 q 𝟘 = q
nr 𝟘 𝟘 ω = 𝟘
nr 𝟘 ω ω = ω
nr ω q r = ω

-- Iteratively defined natrec recurrence function

nrⁿ : Nat → Op₃ Erasure
nrⁿ Nat.zero p q r = 𝟘
nrⁿ (1+ n) p q r = p ∧ (q + (r · (nrⁿ n p q r)))

-- Ordering relation for erasures
-- Reflexive closure of ω ≤ 𝟘

_≤_ : (p q : Erasure) → Set
p ≤ q = p ≡ p ∧ q

---------------------------------------
-- Properties of addition (and meet) --
---------------------------------------

-- Addition is commutative
-- p + q ≡ q + p

+-Commutative : Commutative _+_
+-Commutative 𝟘 𝟘 = refl
+-Commutative 𝟘 ω = refl
+-Commutative ω 𝟘 = refl
+-Commutative ω ω = refl

-- Addition is associative
-- p + (q + r) ≡ (p + q) + r

+-Associative : Associative _+_
+-Associative p q 𝟘 = refl
+-Associative p q ω = refl

-- Addition is idempotent

+-Idempotent : Idempotent _+_
+-Idempotent 𝟘 = refl
+-Idempotent ω = refl

-- 𝟘 is a left identity of addition
-- 𝟘 + p ≡ p

+-LeftIdentity : LeftIdentity 𝟘 _+_
+-LeftIdentity 𝟘 = refl
+-LeftIdentity ω = refl

-- 𝟘 is a right identity of addition
-- p + 𝟘 ≡ p

+-RightIdentity : RightIdentity 𝟘 _+_
+-RightIdentity x = refl

-- 𝟘 is an identity of addition
-- 𝟘 + p ≡ p ≡ p + 𝟘

+-Identity : Identity 𝟘 _+_
+-Identity = +-LeftIdentity , +-RightIdentity

-- Addition is positive
-- If 𝟘 ≤ p + q then 𝟘 ≤ p and 𝟘 ≤ q

+-positive : (p q : Erasure) → 𝟘 ≤ (p + q) → 𝟘 ≤ p × 𝟘 ≤ q
+-positive 𝟘 𝟘 refl = refl , refl
+-positive 𝟘 ω ()
+-positive ω 𝟘 ()
+-positive ω ω ()

----------------------------------
-- Properties of multiplication --
----------------------------------

-- Multiplication is associative
-- p · (q · r) ≡ (p · q) · r

·-Associative : Associative _·_
·-Associative x y 𝟘 = refl
·-Associative x y ω = refl

-- 𝟘 is a left zero for multiplication
-- 𝟘 · p ≡ 𝟘

·-LeftZero : LeftZero 𝟘 _·_
·-LeftZero 𝟘 = refl
·-LeftZero ω = refl

-- 𝟘 is a right zero for multiplication
-- p · 𝟘 ≡ 𝟘

·-RightZero : RightZero 𝟘 _·_
·-RightZero x = refl

-- 𝟘 is a zero for multiplication
-- 𝟘 · p ≡ 𝟘 ≡ p · 𝟘

·-zero : Zero 𝟘 _·_
·-zero = ·-LeftZero , ·-RightZero

-- ω is a left identity for multiplication
-- ω · p ≡ p

·-LeftIdentity : LeftIdentity ω _·_
·-LeftIdentity 𝟘 = refl
·-LeftIdentity ω = refl

-- ω is a right identity for multiplication
-- p · ω ≡ p

·-RightIdentity : RightIdentity ω _·_
·-RightIdentity x = refl

-- ω is an identity for multiplication
-- ω · p ≡ p ≡ p · ω

·-Identity : Identity ω _·_
·-Identity = ·-LeftIdentity , ·-RightIdentity

----------------------------------------------
-- Properties of natrec recurrence function --
----------------------------------------------

-- nr iteration reaches a fixpoint after one iteration
-- nrⁿ 1 p q r ≡ nrⁿ 0 p q r

nr-fix₁ : (p q r : Erasure) → (p ∧ (q + (r · (p ∧ q)))) ≡ (p ∧ q)
nr-fix₁ 𝟘 𝟘 r = refl
nr-fix₁ ω 𝟘 𝟘 = refl
nr-fix₁ ω 𝟘 ω = refl
nr-fix₁ p ω 𝟘 = refl
nr-fix₁ p ω ω = refl

-- nr coincides with nrⁿ at the fixpoint, i.e. with nr in the modality ringoid.
-- nr p q r ≡ nrⁿ 1 p q r

nr-correct : (p q r : Erasure) → nr p q r ≡ nrⁿ 1 p q r
nr-correct 𝟘 𝟘 𝟘 = refl
nr-correct 𝟘 ω 𝟘 = refl
nr-correct 𝟘 𝟘 ω = refl
nr-correct 𝟘 ω ω = refl
nr-correct ω 𝟘 r = refl
nr-correct ω ω r = refl


--------------------------------------------------------------------
-- Distributive properties of addition, multiplication (and meet) --
--------------------------------------------------------------------

-- Multiplication is left distributive over addition
-- p · (q + r) ≡ (p · q) + (p · r)

·-distribˡ-+ : _·_ DistributesOverˡ _+_
·-distribˡ-+ p q 𝟘 = refl
·-distribˡ-+ ω q ω = refl
·-distribˡ-+ 𝟘 𝟘 ω = refl
·-distribˡ-+ 𝟘 ω ω = refl

-- Multiplication is right distributive over addition
-- (q + r) · p ≡ (q · p) + (r · p)

·-distribʳ-+ : _·_ DistributesOverʳ _+_
·-distribʳ-+ 𝟘 q r = refl
·-distribʳ-+ ω q r = refl

-- Multiplication is distributive over addition
-- p · (q + r) ≡ (p · q) + (p · r) and (q + r) · p ≡ (q · p) + (r · p)

·-distrib-+ : _·_ DistributesOver _+_
·-distrib-+ = ·-distribˡ-+ , ·-distribʳ-+

-- Addition is left distributive over addition
-- p + (q + r) ≡ (p + q) + (p + r)

+-distribˡ-+ : _+_ DistributesOverˡ _+_
+-distribˡ-+ p q ω = refl
+-distribˡ-+ 𝟘 q 𝟘 = refl
+-distribˡ-+ ω 𝟘 𝟘 = refl
+-distribˡ-+ ω ω 𝟘 = refl

-- Addition is right distributive over addition
-- (q + r) + p ≡ (q + p) + (r + p)

+-distribʳ-+ : _+_ DistributesOverʳ _+_
+-distribʳ-+ 𝟘 q r = refl
+-distribʳ-+ ω q r = refl

-- Addition is distributive over addition
-- p + (q + r) ≡ (p + q) + (p + r) and (q + r) + p ≡ (q + p) + (r + p)

+-distrib-+ : _+_ DistributesOver _+_
+-distrib-+ = +-distribˡ-+ , +-distribʳ-+

-----------------------------------------------------
-- Addition (and meet) form the following algebras --
-----------------------------------------------------

-- Addition forms a magma

+-Magma : IsMagma _+_
+-Magma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = cong₂ _+_
  }

-- Addition forms a semigroup

+-Semigroup : IsSemigroup _+_
+-Semigroup = record
  { isMagma = +-Magma
  ; assoc   = +-Associative
  }

-- Addition forms a monoid for 𝟘 as identity

+-Monoid : IsMonoid _+_ 𝟘
+-Monoid = record
  { isSemigroup = +-Semigroup
  ; identity    = +-Identity
  }

-- Addition forms a commutative monoid with 𝟘 as identity

+-CommutativeMonoid : IsCommutativeMonoid _+_ 𝟘
+-CommutativeMonoid = record
  { isMonoid = +-Monoid
  ; comm     = +-Commutative
  }

-- Addition forms a band

+-Band : IsBand _+_
+-Band = record
  { isSemigroup = +-Semigroup
  ; idem        = +-Idempotent
  }

-- Addition forms a semilattice

+-Semilattice : IsSemilattice _+_
+-Semilattice = record
  { isBand = +-Band
  ; comm   = +-Commutative
  }

-------------------------------------------------
-- Multiplication forms the following algebras --
-------------------------------------------------

-- Multiplication forms a magma

·-Magma : IsMagma _·_
·-Magma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = cong₂ _·_
  }

-- Multiplication forms a semigroup

·-Semigroup : IsSemigroup _·_
·-Semigroup = record
  { isMagma = ·-Magma
  ; assoc   = ·-Associative
  }

-- Multiplication forms a monoid with ω as identity

·-Monoid : IsMonoid _·_ ω
·-Monoid = record
  { isSemigroup = ·-Semigroup
  ; identity    = ·-Identity
  }

-- Erasures form a modality

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
  ; nrⁿ-fix             = 1 , nr-fix₁
  ; ·-distrib-+         = ·-distrib-+
  ; ·-distrib-∧         = ·-distrib-+
  ; +-distrib-∧         = +-distrib-+
  ; ≈-equivalence       = isEquivalence
  }
