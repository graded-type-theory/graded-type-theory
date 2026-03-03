------------------------------------------------------------------------
-- The modality structure.
------------------------------------------------------------------------

open import Tools.Level
open import Tools.Relation

module Graded.Modality {a} (M : Set a) where

open import Tools.Algebra M
open import Tools.Bool using (Bool; T)
open import Tools.Nat using (Nat; 1+; Sequence)
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Sum

private variable
  n n₁ n₂ p p′ q r z z₁ s s₁ s₂ z₂ : M
  pᵢ : Sequence M

-- Semiring with meet
record Modality : Set a where
  no-eta-equality
  pattern

  infixr 40 _+_
  infixr 43 _∧_
  infixr 45 _·_
  infix  10 _≤_ _<_


  field
    -- A modality structure consists of a type M with three binary
    -- operations (addition, multiplication and meet), and three
    -- special elements.
    _+_ _·_ _∧_ : Op₂ M
    𝟘 𝟙 ω       : M

    -- + and · form a semiring with 𝟙 as multiplicative unit and 𝟘 as
    -- zero
    +-·-Semiring  : IsSemiring _+_ _·_ 𝟘 𝟙
    -- ∧ forms a semilattice
    ∧-Semilattice : IsMeetSemilattice _∧_

    -- Multiplation distributes over meet
    ·-distrib-∧         : _·_ DistributesOver _∧_
    -- Addition distributes over meet
    +-distrib-∧         : _+_ DistributesOver _∧_

  -- Semilattice partial ordering relation
  _≤_ : Rel M a
  p ≤ q = p ≡ p ∧ q

  -- A strict variant of the ordering relation.
  _<_ : Rel M a
  p < q = p ≤ q × p ≢ q

  field
    -- In some modalities the grade ω stands for "an unlimited number
    -- of uses". This grade must be bounded from above by 𝟙.
    ω≤𝟙 : ω ≤ 𝟙

    -- Furthermore ω · (p + q) must be bounded by ω · q.
    ω·+≤ω·ʳ : ω · (p + q) ≤ ω · q

    -- It is decidable whether a grade is equal to 𝟘.
    is-𝟘? : (p : M) → Dec (p ≡ 𝟘)

  -- A modality structure is said to be trivial if 𝟙 ≡ 𝟘.
  --
  -- This implies that all values of type M are equal, see
  -- Graded.Modality.Properties.Equivalence.≡-trivial.

  Trivial : Set a
  Trivial = 𝟙 ≡ 𝟘

  -- Least-such-that P p means that p is the least value which
  -- satisfies P.

  Least-such-that : (M → Set a) → M → Set a
  Least-such-that P p = P p × (∀ q → P q → p ≤ q)

  -- Greatest-such-that P p means that p is the greatest value which
  -- satisfies P.

  Greatest-such-that : ∀ {ℓ} → (M → Set ℓ) → M → Set (a ⊔ ℓ)
  Greatest-such-that P p = P p × (∀ q → P q → q ≤ p)

  -- Greatest-lower-bound p pᵢ means that p is the greatest value which
  -- is lower than all grades of the sequence pᵢ.

  Greatest-lower-bound : M → Sequence M → Set a
  Greatest-lower-bound p pᵢ = Greatest-such-that (λ r → ∀ i → r ≤ pᵢ i) p

  -- A (family of) sequence(s) used to define one of the
  -- usage rules for natrec

  nrᵢ : (r z s : M) → Sequence M
  nrᵢ r z s 0 = z
  nrᵢ r z s (1+ i) = s + r · nrᵢ r z s i

  ·-distribˡ-∧ : _·_ DistributesOverˡ _∧_
  ·-distribˡ-∧ = proj₁ ·-distrib-∧

  ·-distribʳ-∧ : _·_ DistributesOverʳ _∧_
  ·-distribʳ-∧ = proj₂ ·-distrib-∧

  +-distribˡ-∧ : _+_ DistributesOverˡ _∧_
  +-distribˡ-∧ = proj₁ +-distrib-∧

  +-distribʳ-∧ : _+_ DistributesOverʳ _∧_
  +-distribʳ-∧ = proj₂ +-distrib-∧

  +-·-Semiring′ : Semiring a a
  +-·-Semiring′ = record
    { Carrier = M
    ; _≈_ = _≡_
    ; _+_ = _+_
    ; _*_ = _·_
    ; 0# = 𝟘
    ; 1# = 𝟙
    ; isSemiring = +-·-Semiring
    }

  open IsSemiring +-·-Semiring public
    using (
            +-assoc;
            +-cong;
            +-congˡ;
            +-congʳ;
            +-identity;
            +-identityˡ;
            +-identityʳ;
            +-comm
          )
    renaming (
              *-assoc to ·-assoc;
              *-cong to ·-cong;
              *-congˡ to ·-congˡ;
              *-congʳ to ·-congʳ;
              *-identity to ·-identity;
              *-identityˡ to ·-identityˡ;
              *-identityʳ to ·-identityʳ;

              distrib to ·-distrib-+;
              distribˡ to ·-distribˡ-+;
              distribʳ to ·-distribʳ-+;
              zero to ·-zero;
              zeroˡ to ·-zeroˡ;
              zeroʳ to ·-zeroʳ
             )

  open IsMeetSemilattice ∧-Semilattice public
    using (∧-cong; ∧-congˡ; ∧-congʳ)
    renaming (comm to ∧-comm;
              idem to ∧-idem;
              assoc to ∧-assoc
             )

-- Modality structures with well-behaved zero
record Has-well-behaved-zero (𝕄 : Modality) : Set a where
  no-eta-equality
  pattern
  open Modality 𝕄
  field
    -- 𝕄 is non-trivial.
    non-trivial : ¬ Trivial

    -- The following two assumptions are based on assumptions from
    -- Conor McBride's "I Got Plenty o’ Nuttin’" and Robert Atkey's
    -- "Syntax and Semantics of Quantitative Type Theory".

    -- The semiring has the zero-product property:
    -- if p · q is 𝟘, then either p is 𝟘 or q is 𝟘.
    zero-product : {p q : M} → p · q ≡ 𝟘 → p ≡ 𝟘 ⊎ q ≡ 𝟘

    -- The semiring is positive (with respect to addition and meet):

    -- if p + q is 𝟘, then p and q are 𝟘. (The statement that p + q ≡ 𝟘
    -- implies q ≡ 𝟘 follows from the one below, see
    -- Definition.Modality.Properties.Has-well-behaved-zero.+-positiveʳ.)
    +-positiveˡ : {p q : M} → p + q ≡ 𝟘 → p ≡ 𝟘

    -- If p ∧ q is equal to 𝟘, then p ≡ 𝟘.  (The statement that p ∧ q ≡ 𝟘
    -- implies q ≡ 𝟘 follows from the one below, see
    -- Definition.Modality.Properties.Has-well-behaved-zero.∧-positiveʳ.)
    ∧-positiveˡ : {p q : M} → p ∧ q ≡ 𝟘 → p ≡ 𝟘

-- The property of having an nr function (a "natrec usage function").
-- Such a function is used in one of the usage rules for natrec.

record Has-nr (𝕄 : Modality) : Set a where
  no-eta-equality
  pattern

  open Modality 𝕄

  field
    -- The nr function.
    nr : M → M → M → M → M → M

    -- The function is monotone in its last three arguments.
    nr-monotone :
      z₁ ≤ z₂ → s₁ ≤ s₂ → n₁ ≤ n₂ →
      nr p r z₁ s₁ n₁ ≤ nr p r z₂ s₂ n₂

    -- Multiplication from the right sub-distributes over nr p r.
    nr-· : nr p r z s n · q ≤ nr p r (z · q) (s · q) (n · q)

    -- Addition is sub-interchangeable with nr p r.
    nr-+ :
      nr p r z₁ s₁ n₁ + nr p r z₂ s₂ n₂ ≤
      nr p r (z₁ + z₂) (s₁ + s₂) (n₁ + n₂)

    -- If the zero is well-behaved, then nr p r is only 𝟘 for 𝟘, 𝟘
    -- and 𝟘.
    nr-positive :
      ⦃ 𝟘-well-behaved : Has-well-behaved-zero 𝕄 ⦄ →
      nr p r z s n ≡ 𝟘 → z ≡ 𝟘 × s ≡ 𝟘 × n ≡ 𝟘

    -- If n is bounded by 𝟘, then nr p r z s n is bounded by n. This
    -- property is used to prove that the reduction rule natrec-zero
    -- preserves usage.
    nr-zero : n ≤ 𝟘 → nr p r z s n ≤ z

    -- The value nr p r z s n is bounded by
    -- s + p · n + r · nr p r z s n. This property is used to prove
    -- that the reduction rule natrec-suc preserves usage.
    nr-suc : nr p r z s n ≤ s + p · n + r · nr p r z s n

  -- A property that nr functions can satisfy.

  Linearity-like-nr-for-𝟘 : Set a
  Linearity-like-nr-for-𝟘 =
    ∀ {p z s n} →
    nr p 𝟘 z s n ≡ ((𝟙 ∧ p) · n + s) ∧ (n + z)

  -- Another property that nr functions can satisfy.

  Linearity-like-nr-for-𝟙 : Set a
  Linearity-like-nr-for-𝟙 =
    ∀ {p z s n} →
    nr p 𝟙 z s n ≡ (𝟙 + p) · n + ω · s + z

-- The property of having an nr function that factors in a certain way

record Is-factoring-nr {𝕄 : Modality} (has-nr : Has-nr 𝕄)  : Set a where
  no-eta-equality
  pattern

  open Modality 𝕄
  open Has-nr has-nr

  field
    nr₂ : (p r : M) → M

    nr₂≢𝟘 : {p r : M} → nr₂ p r ≢ 𝟘
    nr-factoring :
      {p r z s n : M} → nr p r z s n ≡ nr₂ p r · n + nr p r z s 𝟘

-- A bundling of properties that the modality is required to satisfy
-- when a certain usage rule for natrec is used.

record Has-well-behaved-GLBs (𝕄 : Modality) : Set a where
  no-eta-equality

  open Modality 𝕄

  field
    +-GLBˡ :
      Greatest-lower-bound p pᵢ →
      Greatest-lower-bound (q + p) (λ i → q + pᵢ i)

    ·-GLBˡ :
      Greatest-lower-bound p pᵢ →
      Greatest-lower-bound (q · p) (λ i → q · pᵢ i)

    ·-GLBʳ :
      Greatest-lower-bound p pᵢ →
      Greatest-lower-bound (p · q) (λ i → pᵢ i · q)

    +nrᵢ-GLB :
      Greatest-lower-bound p (nrᵢ r z₁ s₁) →
      Greatest-lower-bound p′ (nrᵢ r z₂ s₂) →
      ∃ λ q → Greatest-lower-bound q (nrᵢ r (z₁ + z₂) (s₁ + s₂)) × p + p′ ≤ q


-- The property of having a natrec-star operator.
record Has-star (r : Modality) : Set a where
  no-eta-equality
  pattern

  open Modality r

  infix 50 _⊛_▷_

  field
    -- The natrec-star operator.
    _⊛_▷_ : Op₃ M

    -- ⊛ is a solution to the following system of inequalities
    ⊛-ineq : ((p q r : M) → p ⊛ q ▷ r ≤ q + r · p ⊛ q ▷ r)
           × ((p q r : M) → p ⊛ q ▷ r ≤ p)

    -- addition is sub-interchangeable over ⊛ w.r.t the first two arguments
    +-sub-interchangeable-⊛ : (r : M) → _+_ SubInterchangeable (_⊛_▷ r) by _≤_
    -- multiplication is right sub-distributive over ⊛ w.r.t the first two arguments
    ·-sub-distribʳ-⊛ : (r : M) → _·_ SubDistributesOverʳ (_⊛_▷ r) by _≤_
    -- ⊛ is sub-distributive over meet w.r.t the first two arguments
    ⊛-sub-distrib-∧    : (r : M) → (_⊛_▷ r) SubDistributesOver _∧_ by _≤_

  ⊛-ineq₁ : (p q r : M) → p ⊛ q ▷ r ≤ q + r · (p ⊛ q ▷ r)
  ⊛-ineq₁ = proj₁ ⊛-ineq

  ⊛-ineq₂ : (p q r : M) → p ⊛ q ▷ r ≤ p
  ⊛-ineq₂ = proj₂ ⊛-ineq

  ⊛-sub-distribˡ-∧ : (r : M) → (_⊛_▷ r) SubDistributesOverˡ _∧_ by _≤_
  ⊛-sub-distribˡ-∧ r = proj₁ (⊛-sub-distrib-∧ r)

  ⊛-sub-distribʳ-∧ : (r : M) → (_⊛_▷ r) SubDistributesOverʳ _∧_ by _≤_
  ⊛-sub-distribʳ-∧ r = proj₂ (⊛-sub-distrib-∧ r)
