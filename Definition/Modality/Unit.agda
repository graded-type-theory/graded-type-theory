{-# OPTIONS --without-K --safe #-}

module Definition.Modality.Unit where

open import Tools.Nat hiding (_+_)
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Unit

open import Tools.Algebra {A = ⊤} _≡_

open import Definition.Modality ⊤ _≡_ public

_+_ : Op₂ ⊤
_ + _ = tt

nrⁿ : (n : Nat) → Op₃ ⊤
nrⁿ _ _ _ _ = tt

infixr 20 _+_

-- Properties of +

-- + is commutative
+-Commutative : Commutative _+_
+-Commutative x y = refl

-- + is associative
+-Associative : Associative _+_
+-Associative x y z = refl

-- + is left distributive of itself
+-Distributiveˡ : _+_ DistributesOverˡ _+_
+-Distributiveˡ x y z = refl

-- + is right distributive over itself
+-Distributiveʳ : _+_ DistributesOverʳ _+_
+-Distributiveʳ x y z = refl

-- tt is the left identity of +
+-LeftIdentity : LeftIdentity tt _+_
+-LeftIdentity tt = refl

-- tt is the right identity of +
+-RightIdentity : RightIdentity tt _+_
+-RightIdentity tt = refl

+-Identity : Identity tt _+_
+-Identity = +-LeftIdentity , +-RightIdentity

-- + is idempotent
+-Idempotent : Idempotent _+_
+-Idempotent tt = refl

-- + forms the following algebras:

+-Magma : IsMagma _+_
+-Magma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = cong₂ _+_
  }

+-Semigroup : IsSemigroup _+_
+-Semigroup = record
  { isMagma = +-Magma
  ; assoc   = +-Associative
  }

+-Monoid : IsMonoid _+_ tt
+-Monoid = record
  { isSemigroup = +-Semigroup
  ; identity    = +-Identity
  }

+-CommutativeMonoid : IsCommutativeMonoid _+_ tt
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

-- ⊤ form a modality with + as addition, multiplication and meet
UnitModality : Modality
UnitModality = record
  { _+_                  = _+_
  ; _·_                  = _+_
  ; _∧_                  = _+_
  ; nrⁿ                  = nrⁿ
  ; 𝟘                    = tt
  ; 𝟙                    = tt
  ; +-CommutativeMonoid  = +-CommutativeMonoid
  ; ·-Monoid             = +-Monoid
  ; ∧-Semilattice        = +-Semilattice
  ; ·-zero               = (λ _ → refl)    , (λ _ → refl)
  ; +-positive           = λ _ _ _ → refl , refl
  ; nrⁿ-rec              = λ _ _ _ _ → refl
  ; nrⁿ-0                = λ _ _ _ → refl
  ; nrⁿ-fix              = 0 , (λ _ _ _ → refl)
  ; ·-distrib-+          = +-Distributiveˡ , +-Distributiveʳ
  ; ·-distrib-∧          = +-Distributiveˡ , +-Distributiveʳ
  ; +-distrib-∧          = +-Distributiveˡ , +-Distributiveʳ
  ; ≈-equivalence        = isEquivalence
  }
