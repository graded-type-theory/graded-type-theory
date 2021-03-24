{-# OPTIONS --without-K --safe #-}

module Definition.Modality.Unit where

open import Algebra
open import Definition.Modality
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Unit

_+_ : Op₂ ⊤
_ + _ = tt

_* : Op₁ ⊤
_ * = tt

infixr 20 _+_

-- Properties of +

-- + is commutative
+-Commutative : Commutative _≡_ _+_
+-Commutative x y = refl

-- + is associative
+-Associative : Associative _≡_ _+_
+-Associative x y z = refl

-- + is left distributive of itself
+-Distributiveˡ : _DistributesOverˡ_ _≡_ _+_ _+_
+-Distributiveˡ x y z = refl

-- + is right distributive over itself
+-Distributiveʳ : _DistributesOverʳ_ _≡_ _+_ _+_
+-Distributiveʳ x y z = refl

-- tt is the left identity of +
+-LeftIdentity : LeftIdentity _≡_ tt _+_
+-LeftIdentity tt = refl

-- tt is the right identity of +
+-RightIdentity : RightIdentity _≡_ tt _+_
+-RightIdentity tt = refl

+-Identity : Identity _≡_ tt _+_
+-Identity = +-LeftIdentity , +-RightIdentity

-- + is idempotent
+-Idempotent : Idempotent _≡_ _+_
+-Idempotent tt = refl

-- + forms the following algebras:

+-Magma : IsMagma _≡_ _+_
+-Magma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = λ _ _ → refl
  }

+-Semigroup : IsSemigroup _≡_ _+_
+-Semigroup = record
  { isMagma = +-Magma
  ; assoc   = +-Associative
  }

+-Monoid : IsMonoid _≡_ _+_ tt
+-Monoid = record
  { isSemigroup = +-Semigroup
  ; identity    = +-Identity
  }

+-CommutativeMonoid : IsCommutativeMonoid _≡_ _+_ tt
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

-- ⊤ form a modality with + as addition, multiplication and meet
UnitModality : Modality ⊤
UnitModality = record
  { _+_                 = _+_
  ; _·_                 = _+_
  ; _∧_                 = _+_
  ; _*                  = _*
  ; 𝟘                   = tt
  ; 𝟙                   = tt
  ; +-CommutativeMonoid = +-CommutativeMonoid
  ; ·-Monoid            = +-Monoid
  ; ∧-Semilattice       = +-Semilattice
  ; *-StarSemiring      = λ p → refl
  ; ·-Zero              = (λ x → refl)    , (λ x → refl)
  ; 𝟘-max               = λ p → refl
  ; +-noInverse         = λ p q x → refl , refl
  ; ·Distr+             = +-Distributiveˡ , +-Distributiveʳ
  ; ·Distr∧             = +-Distributiveˡ , +-Distributiveʳ
  ; +Distr∧             = +-Distributiveˡ , +-Distributiveʳ
  }
