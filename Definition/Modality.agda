open import Tools.Level
open import Tools.Relation

module Definition.Modality {a} (M : Set a) where

open import Tools.Algebra M
open import Tools.Bool using (T)
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Sum

open import Definition.Modality.Restrictions M

-- Modality ringoid
record ModalityWithout⊛ : Set (lsuc a) where
  infixr 40 _+_
  infixr 40 _∧_
  infixr 45 _·_
  infix  10 _≤_ _<_


  field
    -- A modality consists of a type M with three binary operations...
    _+_ : Op₂ M -- Addition
    _·_ : Op₂ M -- Multiplication
    _∧_ : Op₂ M -- Meet

    -- ... and two special elements
    𝟘 : M
    𝟙 : M

    -- + and · form a semiring with 𝟙 as multiplicativ unit and 𝟘 as zero
    +-·-Semiring  : IsSemiring _+_ _·_ 𝟘 𝟙
    -- ∧ forms a semilattice
    ∧-Semilattice       : IsSemilattice _∧_

    -- Multiplation distributes over meet
    ·-distrib-∧         : _·_ DistributesOver _∧_
    -- Addition distributes over meet
    +-distrib-∧         : _+_ DistributesOver _∧_

    -- "Extra" restrictions for certain term/type constructors.
    restrictions : Restrictions

  open Restrictions restrictions public

  field

    -- If the mode 𝟘ᵐ is allowed, then 𝟙 is not equivalent to 𝟘.
    𝟘ᵐ→𝟙≉𝟘 : T 𝟘ᵐ-allowed → 𝟙 ≉ 𝟘

    -- If the mode 𝟘ᵐ is allowed, then it is decidable whether a value
    -- is equivalent to 𝟘.
    is-𝟘? : T 𝟘ᵐ-allowed → (p : M) → Dec (p ≈ 𝟘)

    -- The following two assumptions are based on assumptions from Bob
    -- Atkey's "Syntax and Semantics of Quantitative Type Theory".

    -- If the mode 𝟘ᵐ is allowed, then the semiring has the
    -- zero-product property: if p · q is 𝟘, then either p is 𝟘 or q
    -- is 𝟘.
    zero-product :
      T 𝟘ᵐ-allowed → {p q : M} → p · q ≈ 𝟘 → (p ≈ 𝟘) ⊎ (q ≈ 𝟘)

    -- If the mode 𝟘ᵐ is allowed, then the semiring is positive: if
    -- p + q is 𝟘, then p and q are 𝟘. (The statement that p + q ≈ 𝟘
    -- implies q ≈ 𝟘 follows from the one below, see
    -- Definition.Modality.Properties.Addition.positiveʳ.)
    positiveˡ : T 𝟘ᵐ-allowed → {p q : M} → p + q ≈ 𝟘 → p ≈ 𝟘

  -- Semilattice partial ordering relation
  _≤_ : Rel M a
  p ≤ q = p ≈ (p ∧ q)

  -- A strict variant of the ordering relation.
  _<_ : Rel M a
  p < q = p ≤ q × p ≢ q

  field
    -- If the mode 𝟘ᵐ is allowed and p ∧ q is equal to 𝟘, then p ≤ 𝟘.
    ∧≤𝟘ˡ : T 𝟘ᵐ-allowed → {p q : M} → p ∧ q ≈ 𝟘 → p ≤ 𝟘

    -- If the mode 𝟘ᵐ is allowed, then non-zero quantities must be
    -- bounded by 𝟙.
    ≉𝟘→≤𝟙 : T 𝟘ᵐ-allowed → {p : M} → p ≉ 𝟘 → p ≤ 𝟙

  ·-distribˡ-∧ : _·_ DistributesOverˡ _∧_
  ·-distribˡ-∧ = proj₁ ·-distrib-∧

  ·-distribʳ-∧ : _·_ DistributesOverʳ _∧_
  ·-distribʳ-∧ = proj₂ ·-distrib-∧

  +-distribˡ-∧ : _+_ DistributesOverˡ _∧_
  +-distribˡ-∧ = proj₁ +-distrib-∧

  +-distribʳ-∧ : _+_ DistributesOverʳ _∧_
  +-distribʳ-∧ = proj₂ +-distrib-∧

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
              zeroʳ to ·-zeroʳ;

              isEquivalence to ≈-equivalence
             )

  open IsSemilattice ∧-Semilattice public
    using (∧-cong; ∧-congˡ; ∧-congʳ)
    renaming (comm to ∧-comm;
              idem to ∧-idem;
              assoc to ∧-assoc
             )

record Modality : Set (lsuc a) where
  infix  50 _⊛_▷_
  field
    modalityWithout⊛ : ModalityWithout⊛
  open ModalityWithout⊛ modalityWithout⊛ public

  field
    -- ... one tertiary operator...
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
