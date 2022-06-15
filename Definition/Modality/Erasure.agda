{-# OPTIONS --without-K --safe #-}

module Definition.Modality.Erasure where

open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation

-- The set of erasure annotations with 𝟘 corresponding to no usage
-- and ω to any usage.

data Erasure : Set where
  𝟘 ω : Erasure

Erasure′ : Setoid _ _
Erasure′ = record { Carrier = Erasure ; _≈_ = _≡_ ; isEquivalence = isEquivalence }

open import Definition.Modality Erasure′ public
open import Tools.Algebra Erasure′
open import Tools.Nat hiding (_+_)

infixl 40 _+_
infixl 40 _∧_
infixl 45 _·_
infix  10 _≤_
infix  50 _⊛_▷_


-- Addition of erasure annotations

_+_ : Op₂ Erasure
𝟘 + q = q
ω + q = ω

-- Multiplication of erasure annotations

_·_ : Op₂ Erasure
𝟘 · q = 𝟘
ω · q = q

-- Meet for erasure annotations coincides with addition

_∧_ : Op₂ Erasure
_∧_ = _+_

-- Natrec recurrence function

_⊛_▷_ : Op₃ Erasure
p ⊛ q ▷ r = p + q


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
+-Associative 𝟘 q r = refl
+-Associative ω q r = refl

-- Addition is idempotent

+-Idempotent : Idempotent _+_
+-Idempotent 𝟘 = refl
+-Idempotent ω = refl

-- 𝟘 is a left identity of addition
-- 𝟘 + p ≡ p

+-LeftIdentity : LeftIdentity 𝟘 _+_
+-LeftIdentity p = refl

-- 𝟘 is a right identity of addition
-- p + 𝟘 ≡ p

+-RightIdentity : RightIdentity 𝟘 _+_
+-RightIdentity 𝟘 = refl
+-RightIdentity ω = refl

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
·-Associative 𝟘 q r = refl
·-Associative ω q r = refl

-- 𝟘 is a left zero for multiplication
-- 𝟘 · p ≡ 𝟘

·-LeftZero : LeftZero 𝟘 _·_
·-LeftZero p = refl

-- 𝟘 is a right zero for multiplication
-- p · 𝟘 ≡ 𝟘

·-RightZero : RightZero 𝟘 _·_
·-RightZero 𝟘 = refl
·-RightZero ω = refl

-- 𝟘 is a zero for multiplication
-- 𝟘 · p ≡ 𝟘 ≡ p · 𝟘

·-zero : Zero 𝟘 _·_
·-zero = ·-LeftZero , ·-RightZero

-- ω is a left identity for multiplication
-- ω · p ≡ p

·-LeftIdentity : LeftIdentity ω _·_
·-LeftIdentity p = refl

-- ω is a right identity for multiplication
-- p · ω ≡ p

·-RightIdentity : RightIdentity ω _·_
·-RightIdentity 𝟘 = refl
·-RightIdentity ω = refl

-- ω is an identity for multiplication
-- ω · p ≡ p ≡ p · ω

·-Identity : Identity ω _·_
·-Identity = ·-LeftIdentity , ·-RightIdentity

----------------------
-- Properties of ⊛  --
----------------------

-- p ⊛ᵣ q is a solution to the inequality x ≤ q + rx
-- p ⊛ᵣ q ≤ q + r · (p ⊛ᵣ q)

⊛-ineq₁ : (p q r : Erasure) → p ⊛ q ▷ r ≤ q + r · p ⊛ q ▷ r
⊛-ineq₁ 𝟘 𝟘 𝟘 = refl
⊛-ineq₁ 𝟘 𝟘 ω = refl
⊛-ineq₁ 𝟘 ω r = refl
⊛-ineq₁ ω q r = refl

-- p ⊛ᵣ q is a solution to the the inequality x ≤ p
-- p ⊛ᵣ q ≤ p

⊛-ineq₂ : (p q r : Erasure) → p ⊛ q ▷ r ≤ p
⊛-ineq₂ 𝟘 𝟘 r = refl
⊛-ineq₂ 𝟘 ω r = refl
⊛-ineq₂ ω q r = refl

-- Addition is sub-interchangable with ⊛ᵣ
-- (p ⊛ᵣ q) + (p′ ⊛ᵣ q′) ≤ (p + p′) ⊛ᵣ (q + q′)

+-sub-interchangable-⊛ : (r : Erasure) → _+_ SubInterchangable (_⊛_▷ r) by _≤_
+-sub-interchangable-⊛ r 𝟘 𝟘 𝟘 𝟘 = refl
+-sub-interchangable-⊛ r 𝟘 𝟘 𝟘 ω = refl
+-sub-interchangable-⊛ r 𝟘 𝟘 ω q′ = refl
+-sub-interchangable-⊛ r 𝟘 ω p′ q′ = refl
+-sub-interchangable-⊛ r ω q p′ q′ = refl

-- Multiplation right sub-distributes over ⊛ᵣ
-- (p ⊛ᵣ p′) · q ≤ (p · q) ⊛ᵣ (p′ · q)

·-sub-distribʳ-⊛ : (r : Erasure) → _·_ SubDistributesOverʳ (_⊛_▷ r) by _≤_
·-sub-distribʳ-⊛ r q 𝟘 p′ = sym (+-Idempotent (p′ · q))
·-sub-distribʳ-⊛ r 𝟘 ω 𝟘 = refl
·-sub-distribʳ-⊛ r 𝟘 ω ω = refl
·-sub-distribʳ-⊛ r ω ω p′ = refl

-- ⊛ᵣ left sub-distributes over meet
-- p ⊛ᵣ (q ∧ q′) ≤ (p ⊛ᵣ q) ∧ (p ⊛ᵣ q′)

⊛-sub-distribˡ-∧ : (r : Erasure) → (_⊛_▷ r) SubDistributesOverˡ _∧_ by _≤_
⊛-sub-distribˡ-∧ r 𝟘 q q′ = sym (+-Idempotent (q + q′))
⊛-sub-distribˡ-∧ r ω q q′ = refl

-- ⊛ᵣ left sub-distributes over meet
-- (p ∧ p′) ⊛ᵣ q ≤ (p ⊛ᵣ q) ∧ (p′ ⊛ᵣ q)

⊛-sub-distribʳ-∧ : (r : Erasure) → (_⊛_▷ r) SubDistributesOverʳ _∧_ by _≤_
⊛-sub-distribʳ-∧ r q ω p′ = refl
⊛-sub-distribʳ-∧ r q 𝟘 ω = refl
⊛-sub-distribʳ-∧ r 𝟘 𝟘 𝟘 = refl
⊛-sub-distribʳ-∧ r ω 𝟘 𝟘 = refl

--------------------------------------------------------------------
-- Distributive properties of addition, multiplication (and meet) --
--------------------------------------------------------------------

-- Multiplication is left distributive over addition
-- p · (q + r) ≡ (p · q) + (p · r)

·-distribˡ-+ : _·_ DistributesOverˡ _+_
·-distribˡ-+ 𝟘 q r = refl
·-distribˡ-+ ω q r = refl

-- Multiplication is right distributive over addition
-- (q + r) · p ≡ (q · p) + (r · p)

·-distribʳ-+ : _·_ DistributesOverʳ _+_
·-distribʳ-+ p 𝟘 r = refl
·-distribʳ-+ 𝟘 ω 𝟘 = refl
·-distribʳ-+ 𝟘 ω ω = refl
·-distribʳ-+ ω ω r = refl

-- Multiplication is distributive over addition
-- p · (q + r) ≡ (p · q) + (p · r) and (q + r) · p ≡ (q · p) + (r · p)

·-distrib-+ : _·_ DistributesOver _+_
·-distrib-+ = ·-distribˡ-+ , ·-distribʳ-+

-- Addition is left distributive over addition
-- p + (q + r) ≡ (p + q) + (p + r)

+-distribˡ-+ : _+_ DistributesOverˡ _+_
+-distribˡ-+ 𝟘 q r = refl
+-distribˡ-+ ω q r = refl

-- Addition is right distributive over addition
-- (q + r) + p ≡ (q + p) + (r + p)

+-distribʳ-+ : _+_ DistributesOverʳ _+_
+-distribʳ-+ p ω r = refl
+-distribʳ-+ 𝟘 𝟘 r = refl
+-distribʳ-+ ω 𝟘 𝟘 = refl
+-distribʳ-+ ω 𝟘 ω = refl

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
  { _+_ = _+_
  ; _·_ = _·_
  ; _∧_ = _∧_
  ; _⊛_▷_ = _⊛_▷_
  ; 𝟘 = 𝟘
  ; 𝟙 = ω
  ; +-CommutativeMonoid = +-CommutativeMonoid
  ; ·-Monoid = ·-Monoid
  ; ∧-Semilattice = +-Semilattice
  ; ·-zero = ·-zero
  ; +-positive = +-positive
  ; ⊛-ineq = ⊛-ineq₁ , ⊛-ineq₂
  ; ⊛-cong = cong₃ _⊛_▷_
  ; ·-distrib-+ = ·-distrib-+
  ; ·-distrib-∧ = ·-distrib-+
  ; +-distrib-∧ = +-distrib-+
  ; +-sub-interchangable-⊛ = +-sub-interchangable-⊛
  ; ·-sub-distribʳ-⊛ = ·-sub-distribʳ-⊛
  ; ⊛-sub-distrib-∧ = λ r → (⊛-sub-distribˡ-∧ r) , (⊛-sub-distribʳ-∧ r)
  ; ≈-equivalence = isEquivalence
  }
