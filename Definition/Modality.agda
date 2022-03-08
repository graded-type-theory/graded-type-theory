{-# OPTIONS --without-K --safe #-}

open import Tools.Level
open import Tools.Relation

module Definition.Modality {a ℓ} (M′ : Setoid a ℓ) where

open Setoid M′ renaming (Carrier to M)

open import Tools.Algebra M′
open import Tools.Nat hiding (_+_)
open import Tools.Product

-- Modality ringoid
record Modality : Set (a ⊔ ℓ) where
  infixr 40 _+_
  infixr 40 _∧_
  infixr 45 _·_
  infix  10 _≤_

  -- open Setoid M′ renaming (Carrier to M) public

  field
    -- A modality consists of a type M with three binary operations...
    _+_ : Op₂ M -- Addition
    _·_ : Op₂ M -- Multiplication
    _∧_ : Op₂ M -- Meet

    -- ... one natural number-indexed tertiary operator...
    nrⁿ : Nat → Op₃ M

    -- ... and two special elements
    𝟘 : M
    𝟙 : M

    -- + forms a commutative monoid with 𝟘 as unit element
    +-CommutativeMonoid : IsCommutativeMonoid  _+_ 𝟘
    -- · forms a monoid with 𝟙 as unit element
    ·-Monoid            : IsMonoid _·_ 𝟙
    -- ∧ forms a semilattice
    ∧-Semilattice       : IsSemilattice _∧_


  -- Semilattice partial ordering relation
  _≤_ : Rel M ℓ
  p ≤ q = p ≈ (p ∧ q)

  field
    -- 𝟘 is zero for multiplication
    ·-zero              : Zero 𝟘 _·_
    -- The semiring is positive
    +-positive          : (p q : M) → 𝟘 ≤ (p + q) → 𝟘 ≤ p × 𝟘 ≤ q

    -- nr is a solution to the following recurrence relation
    nrⁿ-rec : (n : Nat) (p q r : M) → nrⁿ (1+ n) p q r ≈ p ∧ (q + r · nrⁿ n p q r)
    -- The base case value of nrᶜ is 𝟘
    nrⁿ-0 : (p q r : M) → nrⁿ 0 p q r ≈ 𝟘
    -- nrⁿ has a fixpoint
    nrⁿ-fix : ∃ (λ n → ∀ (p q r : M) → nrⁿ (1+ n) p q r ≈ nrⁿ n p q r)

    -- Multiplication distributes over addition
    ·-distrib-+         : _·_ DistributesOver _+_
    -- Multiplation distributes over meet
    ·-distrib-∧         : _·_ DistributesOver _∧_
    -- Addition distributes over meet
    +-distrib-∧         : _+_ DistributesOver _∧_

    -- ≈ is an equivallence relation
    ≈-equivalence       : IsEquivalence _≈_

  -- The fixpoint of nrⁿ defines a tertiary operator
  nr : Op₃ M
  nr = nrⁿ (proj₁ nrⁿ-fix)

  -- Easier access to some operator properties
  +-comm : Commutative _+_
  +-comm = IsCommutativeMonoid.comm +-CommutativeMonoid

  +-assoc : Associative _+_
  +-assoc = IsCommutativeMonoid.assoc +-CommutativeMonoid

  +-identity : Identity 𝟘 _+_
  +-identity = IsCommutativeMonoid.identity +-CommutativeMonoid

  ·-assoc : Associative _·_
  ·-assoc = IsMonoid.assoc ·-Monoid

  ·-identity : Identity 𝟙 _·_
  ·-identity = IsMonoid.identity ·-Monoid

  ∧-comm : Commutative _∧_
  ∧-comm = IsSemilattice.comm ∧-Semilattice

  ∧-assoc : Associative _∧_
  ∧-assoc = IsSemilattice.assoc ∧-Semilattice

  ∧-idem : Idempotent _∧_
  ∧-idem = IsSemilattice.idem ∧-Semilattice

  ≈-refl : Reflexive _≈_
  ≈-refl = IsEquivalence.refl ≈-equivalence

  ≈-sym : Symmetric _≈_
  ≈-sym = IsEquivalence.sym ≈-equivalence

  ≈-trans : Transitive _≈_
  ≈-trans = IsEquivalence.trans ≈-equivalence

  +-cong : Congruent₂ _+_
  +-cong = IsCommutativeMonoid.∙-cong +-CommutativeMonoid

  ·-cong : Congruent₂ _·_
  ·-cong = IsMonoid.∙-cong ·-Monoid

  ∧-cong : Congruent₂ _∧_
  ∧-cong = IsSemilattice.∧-cong ∧-Semilattice
