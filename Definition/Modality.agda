{-# OPTIONS --without-K --safe #-}

module Definition.Modality where

open import Algebra
open import Tools.Product
open import Tools.PropositionalEquality


-- Star ringoid modality structure
record Modality (M : Set) : Set where
  infixr 20 _+_
  infixr 20 _∧_
  infixr 25 _·_
  infix  10 _≤_

  field
    -- A modality consists of a type M with three binary operations...
    _+_ : Op₂ M -- Addition
    _·_ : Op₂ M -- Multiplication
    _∧_ : Op₂ M -- Meet

    -- ... one teritary operator...
    nr : M → M → M → M

    -- ... and two special elements
    𝟘 : M
    𝟙 : M

    -- + forms a commutative monoid with 𝟘 as unit element
    +-CommutativeMonoid : IsCommutativeMonoid _≡_ _+_ 𝟘
    -- · forms a monoid with 𝟙 as unit element
    ·-Monoid            : IsMonoid _≡_ _·_ 𝟙
    -- ∧ forms a semilattice
    ∧-Semilattice       : IsSemilattice _≡_ _∧_


  -- Semilattice partial ordering relation
  _≤_ : M → M → Set
  p ≤ q = p ≡ (p ∧ q)

  field
    -- 𝟘 is zero for multiplication
    ·-Zero              : Zero _≡_ 𝟘 _·_
    -- The semiring is positive
    +-Positive          : (p q : M) → 𝟘 ≤ (p + q) → 𝟘 ≤ p × 𝟘 ≤ q
    -- nr is a solution to the following recurrence relation
    nr-rec : (p q r : M) → nr p q r ≡ p ∧ (q + r · nr p q r)


    -- Multiplication distributes over addition
    ·Distr+             : _DistributesOver_ _≡_ _·_ _+_
    -- Multiplation distributes over meet
    ·Distr∧             : _DistributesOver_ _≡_ _·_ _∧_
    -- Addition distributes over meet
    +Distr∧             : _DistributesOver_ _≡_ _+_ _∧_


  -- Easier access to some operator properties
  +-Commutative : Commutative _≡_ _+_
  +-Commutative = IsCommutativeMonoid.comm +-CommutativeMonoid

  +-Associative : Associative _≡_ _+_
  +-Associative = IsCommutativeMonoid.assoc +-CommutativeMonoid

  +-Identity : Identity _≡_ 𝟘 _+_
  +-Identity = IsCommutativeMonoid.identity +-CommutativeMonoid

  ·-Associative : Associative _≡_ _·_
  ·-Associative = IsMonoid.assoc ·-Monoid

  ·-Identity : Identity _≡_ 𝟙 _·_
  ·-Identity = IsMonoid.identity ·-Monoid

  ∧-Commutative : Commutative _≡_ _∧_
  ∧-Commutative = IsSemilattice.comm ∧-Semilattice

  ∧-Associative : Associative _≡_ _∧_
  ∧-Associative = IsSemilattice.assoc ∧-Semilattice

  ∧-Idempotent : Idempotent _≡_ _∧_
  ∧-Idempotent = IsSemilattice.idem ∧-Semilattice
