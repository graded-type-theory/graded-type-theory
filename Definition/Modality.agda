{-# OPTIONS --without-K --safe #-}

module Definition.Modality where

open import Algebra
open import Tools.Product
open import Tools.PropositionalEquality

-- Star ringoid
record Modality (M : Set) : Set where
  field
    -- A modality consists of a type M with three binary operations...
    _+_ : Op₂ M -- Addition
    _·_ : Op₂ M -- Multiplication
    _∧_ : Op₂ M -- Meet

    -- ... one unary operator ...
    _* : Op₁ M

    -- ... and two special elements
    𝟘 : M
    𝟙 : M

    -- + forms a commutative monoid with 𝟘 as unit element
    +-CommutativeMonoid : IsCommutativeMonoid _≡_ _+_ 𝟘
    -- · forms a monoid with 𝟙 as unit element
    ·-Monoid            : IsMonoid _≡_ _·_ 𝟙
    -- ∧ forms a bounded semilattice with 𝟘 as identity
    ∧-BoundedSemilattice       : IsBoundedLattice _≡_ _∧_ 𝟘
    -- * forms a star semiring
    *-StarSemiring      : (p : M) → p * ≡ 𝟙 + (p · (p *))

    -- 𝟘 is zero for multiplication
    ·-Zero              : Zero _≡_ 𝟘 _·_
    -- There are no additive inverses (except 𝟘)
    +-noInverse         : (p q : M) → p + q ≡ 𝟘 → p ≡ 𝟘 × q ≡ 𝟘

    -- Multiplication distributes over addition
    ·Distr+             : _DistributesOver_ _≡_ _·_ _+_
    -- Multiplation distributes over meet
    ·Distr∧             : _DistributesOver_ _≡_ _·_ _∧_
    -- Addition distributes over meet
    +Distr∧             : _DistributesOver_ _≡_ _+_ _∧_

  -- Semilattice partial ordering relation
  _≤_ : M → M → Set
  p ≤ q = p ≡ (p ∧ q)

  -- Easier access to some operator properties
  +-Commutative : Commutative _≡_ _+_
  +-Commutative = IsCommutativeMonoid.comm +-CommutativeMonoid

  +-Associative : Associative _≡_ _+_
  +-Associative = IsSemigroup.assoc (IsMonoid.isSemigroup
                    (IsCommutativeMonoid.isMonoid +-CommutativeMonoid))

  +-Identity : Identity _≡_ 𝟘 _+_
  +-Identity = IsMonoid.identity (IsCommutativeMonoid.isMonoid +-CommutativeMonoid)

  ·-Associative : Associative _≡_ _·_
  ·-Associative = IsSemigroup.assoc (IsMonoid.isSemigroup ·-Monoid)

  ·-Identity : Identity _≡_ 𝟙 _·_
  ·-Identity = (IsMonoid.identity ·-Monoid)

  ∧-Commutative : Commutative _≡_ _∧_
  ∧-Commutative = IsBoundedLattice.comm _≡_ ∧-BoundedSemilattice

  ∧-Associative : Associative _≡_ _∧_
  ∧-Associative = IsBoundedLattice.assoc _≡_ ∧-BoundedSemilattice

  ∧-Idempotent : Idempotent _≡_ _∧_
  ∧-Idempotent = IsBoundedLattice.idem ∧-BoundedSemilattice

  𝟘-max : (p : M) → p ≤ 𝟘
  𝟘-max p = sym (proj₂ (IsBoundedLattice.identity _≡_ ∧-BoundedSemilattice) p)
