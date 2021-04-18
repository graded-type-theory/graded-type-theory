{-# OPTIONS --without-K --safe #-}

module Definition.Modality.Erasure where

open import Tools.Algebra
open import Tools.Product
open import Tools.PropositionalEquality

data Erasure : Set where
  𝟘 ω : Erasure

open import Definition.Modality Erasure _≡_ public

_+_ : Op₂ Erasure
x + 𝟘 = x
x + ω = ω

_·_ : Op₂ Erasure
x · 𝟘 = 𝟘
x · ω = x

_∧_ : Op₂ Erasure
_∧_ = _+_

nr : Erasure → Erasure → Erasure → Erasure
nr 𝟘 q 𝟘 = q
nr 𝟘 𝟘 ω = 𝟘
nr 𝟘 ω ω = ω
nr ω q r = ω

_≤_ : (p q : Erasure) → Set
p ≤ q = p ≡ p ∧ q

-- Properties of addition (and meet)

+-Congruent : Congruent₂ _≡_ _+_
+-Congruent refl refl = refl

+-Commutative : Commutative _≡_ _+_
+-Commutative 𝟘 𝟘 = refl
+-Commutative 𝟘 ω = refl
+-Commutative ω 𝟘 = refl
+-Commutative ω ω = refl

+-Associative : Associative _≡_ _+_
+-Associative x y 𝟘 = refl
+-Associative x y ω = refl

+-Idempotent : Idempotent _≡_ _+_
+-Idempotent 𝟘 = refl
+-Idempotent ω = refl

+-LeftIdentity : LeftIdentity _≡_ 𝟘 _+_
+-LeftIdentity 𝟘 = refl
+-LeftIdentity ω = refl

+-RightIdentity : RightIdentity _≡_ 𝟘 _+_
+-RightIdentity x = refl

+-Identity : Identity _≡_ 𝟘 _+_
+-Identity = +-LeftIdentity , +-RightIdentity

+-Positive : (p q : Erasure) → 𝟘 ≤ (p + q) → 𝟘 ≤ p × 𝟘 ≤ q
+-Positive 𝟘 𝟘 refl = refl , refl
+-Positive 𝟘 ω ()
+-Positive ω 𝟘 ()
+-Positive ω ω ()


-- Properties of multiplication
·-Congruent : Congruent₂ _≡_ _·_
·-Congruent refl refl = refl

·-Associative : Associative _≡_ _·_
·-Associative x y 𝟘 = refl
·-Associative x y ω = refl

·-LeftZero : LeftZero _≡_ 𝟘 _·_
·-LeftZero 𝟘 = refl
·-LeftZero ω = refl

·-RightZero : RightZero _≡_ 𝟘 _·_
·-RightZero x = refl

·-Zero : Zero _≡_ 𝟘 _·_
·-Zero = ·-LeftZero , ·-RightZero

·-LeftIdentity : LeftIdentity _≡_ ω _·_
·-LeftIdentity 𝟘 = refl
·-LeftIdentity ω = refl

·-RightIdentity : RightIdentity _≡_ ω _·_
·-RightIdentity x = refl

·-Identity : Identity _≡_ ω _·_
·-Identity = ·-LeftIdentity , ·-RightIdentity


-- Distributive properties of addition, multiplication (and meet)
·Distrˡ+ : _DistributesOverˡ_ _≡_ _·_ _+_
·Distrˡ+ x y 𝟘 = refl
·Distrˡ+ ω y ω = refl
·Distrˡ+ 𝟘 𝟘 ω = refl
·Distrˡ+ 𝟘 ω ω = refl

·Distrʳ+ : _DistributesOverʳ_ _≡_ _·_ _+_
·Distrʳ+ 𝟘 y z = refl
·Distrʳ+ ω y z = refl

·Distr+ : _DistributesOver_ _≡_ _·_ _+_
·Distr+ = ·Distrˡ+ , ·Distrʳ+

+Distrˡ+ : _DistributesOverˡ_ _≡_ _+_ _+_
+Distrˡ+ x y ω = refl
+Distrˡ+ 𝟘 y 𝟘 = refl
+Distrˡ+ ω 𝟘 𝟘 = refl
+Distrˡ+ ω ω 𝟘 = refl

+Distrʳ+ : _DistributesOverʳ_ _≡_ _+_ _+_
+Distrʳ+ 𝟘 y z = refl
+Distrʳ+ ω y z = refl

+Distr+ : _DistributesOver_ _≡_ _+_ _+_
+Distr+ = +Distrˡ+ , +Distrʳ+

-- Properties of nr

nr-rec : (p q r : Erasure) → nr p q r ≡ p ∧ (q + (r · nr p q r))
nr-rec 𝟘 𝟘 𝟘 = refl
nr-rec 𝟘 𝟘 ω = refl
nr-rec 𝟘 ω 𝟘 = refl
nr-rec 𝟘 ω ω = refl
nr-rec ω q r = subst₂ _≡_ refl (+-Commutative (q + r) ω) refl

nr-mono : (a b c d e : Erasure) → a ≤ b → c ≤ d → nr a c e ≤ nr b d e
nr-mono 𝟘 𝟘 𝟘 𝟘 𝟘 refl refl = refl
nr-mono 𝟘 𝟘 𝟘 𝟘 ω refl refl = refl
nr-mono 𝟘 𝟘 𝟘 ω 𝟘 refl ()
nr-mono 𝟘 𝟘 𝟘 ω ω refl ()
nr-mono 𝟘 𝟘 ω 𝟘 𝟘 refl refl = refl
nr-mono 𝟘 𝟘 ω 𝟘 ω refl refl = refl
nr-mono 𝟘 𝟘 ω ω 𝟘 refl refl = refl
nr-mono 𝟘 𝟘 ω ω ω refl refl = refl
nr-mono 𝟘 ω 𝟘 𝟘 𝟘 () Q
nr-mono 𝟘 ω 𝟘 𝟘 ω () Q
nr-mono 𝟘 ω 𝟘 ω 𝟘 () Q
nr-mono 𝟘 ω 𝟘 ω ω () Q
nr-mono 𝟘 ω ω 𝟘 𝟘 () Q
nr-mono 𝟘 ω ω 𝟘 ω () Q
nr-mono 𝟘 ω ω ω 𝟘 () Q
nr-mono 𝟘 ω ω ω ω () Q
nr-mono ω 𝟘 𝟘 𝟘 𝟘 refl refl = refl
nr-mono ω 𝟘 𝟘 𝟘 ω refl refl = refl
nr-mono ω 𝟘 𝟘 ω 𝟘 refl ()
nr-mono ω 𝟘 𝟘 ω ω refl ()
nr-mono ω 𝟘 ω 𝟘 𝟘 refl refl = refl
nr-mono ω 𝟘 ω 𝟘 ω refl refl = refl
nr-mono ω 𝟘 ω ω 𝟘 refl refl = refl
nr-mono ω 𝟘 ω ω ω refl refl = refl
nr-mono ω ω 𝟘 𝟘 𝟘 refl refl = refl
nr-mono ω ω 𝟘 𝟘 ω refl refl = refl
nr-mono ω ω 𝟘 ω 𝟘 refl ()
nr-mono ω ω 𝟘 ω ω refl ()
nr-mono ω ω ω 𝟘 𝟘 refl refl = refl
nr-mono ω ω ω 𝟘 ω refl refl = refl
nr-mono ω ω ω ω 𝟘 refl refl = refl
nr-mono ω ω ω ω ω refl refl = refl

-- Addition (and meet) form the following algebras
+-Magma : IsMagma _≡_ _+_
+-Magma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = +-Congruent
  }

+-Semigroup : IsSemigroup _≡_ _+_
+-Semigroup = record
  { isMagma = +-Magma
  ; assoc   = +-Associative
  }

+-Monoid : IsMonoid _≡_ _+_ 𝟘
+-Monoid = record
  { isSemigroup = +-Semigroup
  ; identity    = +-Identity
  }

+-CommutativeMonoid : IsCommutativeMonoid _≡_ _+_ 𝟘
+-CommutativeMonoid = record
  { isMonoid = +-Monoid
  ; comm     = +-Commutative
  }

+-Band : IsBand _≡_ _+_
+-Band = record
  { isSemigroup = +-Semigroup
  ; idem        = +-Idempotent
  }

+-Semilattice : IsSemilattice _≡_ _+_
+-Semilattice = record
  { isBand = +-Band
  ; comm   = +-Commutative
  }

-- Multiplication forms the following algebras
·-Magma : IsMagma _≡_ _·_
·-Magma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = ·-Congruent
  }

·-Semigroup : IsSemigroup _≡_ _·_
·-Semigroup = record
  { isMagma = ·-Magma
  ; assoc   = ·-Associative
  }

·-Monoid : IsMonoid _≡_ _·_ ω
·-Monoid = record
  { isSemigroup = ·-Semigroup
  ; identity    = ·-Identity
  }

-- ErasureModality : Modality
-- ErasureModality = record
--   { _+_                  = _+_
--   ; _·_                  = _·_
--   ; _∧_                  = _∧_
--   ; 𝟘                    = 𝟘
--   ; 𝟙                    = ω
--   ; +-CommutativeMonoid  = +-CommutativeMonoid
--   ; ·-Monoid             = ·-Monoid
--   ; ∧-Semilattice        = +-Semilattice
--   ; nr-rec = nr-rec
--   ; ·-zero               = ·-Zero
--   ; +-positive           = +-Positive
--   ; ·-distrib-+              = ·Distr+
--   ; ·-distrib-∧              = ·Distr+
--   ; +-distrib-∧              = +Distr+
--   }
