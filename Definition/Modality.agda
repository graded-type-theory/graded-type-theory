module Definition.Modality where

open import Algebra
open import Tools.PropositionalEquality

record Modality (M : Set) : Set where
  field
    -- A modality consists of a type M with three binary operations...
    _+_ : Op₂ M -- Addition
    _·_ : Op₂ M -- Multiplication
    _∧_ : Op₂ M -- Meet

    -- ... and two special elements
    𝟘 : M
    𝟙 : M

    -- + forms a commutative monoid with 𝟘 as unit element
    +-CommutativeMonoid : IsCommutativeMonoid _≡_ _+_ 𝟘
    -- · forms a monoid with 𝟙 as unit element
    ·-Monoid            : IsMonoid _≡_ _·_ 𝟙
    -- ∧ forms a semilattice
    ∧-Semilattice       : IsSemilattice _≡_ _∧_

    -- 𝟘 is zero for multiplication
    ·-Zero              : Zero _≡_ 𝟘 _·_

    -- Multiplication distributes over addition
    ·Distr+             : _DistributesOver_ _≡_ _·_ _+_
    -- Multiplation distributes over meet
    ·Distr∧             : _DistributesOver_ _≡_ _·_ _∧_
    -- Addition distributes over meet
    +Distr∧             : _DistributesOver_ _≡_ _+_ _∧_

  -- Semilattice partial ordering relation
  _≤_ : M → M → Set
  p ≤ q = p ≡ (p ∧ q)


