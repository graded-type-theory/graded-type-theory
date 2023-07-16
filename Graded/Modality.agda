------------------------------------------------------------------------
-- The modality structure.
------------------------------------------------------------------------

open import Tools.Level
open import Tools.Relation

module Graded.Modality {a} (M : Set a) where

open import Tools.Algebra M
open import Tools.Bool using (T)
open import Tools.Nullary
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Sum

open import Graded.Modality.Variant a

-- Semiring with meet
record Semiring-with-meet : Set a where
  infixr 40 _+_
  infixr 40 _∧_
  infixr 45 _·_
  infix  10 _≤_ _<_


  field
    -- A semiring with meet consists of a type M with three binary operations...
    _+_ : Op₂ M -- Addition
    _·_ : Op₂ M -- Multiplication
    _∧_ : Op₂ M -- Meet

    -- ... and two special elements
    𝟘 : M
    𝟙 : M

    -- + and · form a semiring with 𝟙 as multiplicative unit and 𝟘 as zero
    +-·-Semiring  : IsSemiring _+_ _·_ 𝟘 𝟙
    -- ∧ forms a semilattice
    ∧-Semilattice       : IsSemilattice _∧_

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

  open IsSemilattice ∧-Semilattice public
    using (∧-cong; ∧-congˡ; ∧-congʳ)
    renaming (comm to ∧-comm;
              idem to ∧-idem;
              assoc to ∧-assoc
             )

-- Meet-Semirings with well-behaved zero
record Has-well-behaved-zero (𝕄 : Semiring-with-meet) : Set a where
  open Semiring-with-meet 𝕄
  field
    -- 𝟙 is not equal to 𝟘.
    𝟙≢𝟘 : 𝟙 ≢ 𝟘

    -- It is decidable whether a value is equal to 𝟘.
    is-𝟘? : (p : M) → Dec (p ≡ 𝟘)

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

-- The property of having a natrec-star operator.
record Has-star (r : Semiring-with-meet) : Set a where
  open Semiring-with-meet r

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

-- The modality structure
record Modality : Set (lsuc a) where
  field
    -- The modality variant.
    variant            : Modality-variant
    semiring-with-meet : Semiring-with-meet

  open Semiring-with-meet semiring-with-meet public
  open Modality-variant variant public

  field
    -- If the mode 𝟘ᵐ is allowed, then the zero is well-behaved
    𝟘-well-behaved : T 𝟘ᵐ-allowed → Has-well-behaved-zero semiring-with-meet

    -- If the modality is supposed to come with a dedicated
    -- natrec-star operator, then such an operator is available.
    has-star : ⊛-available → Has-star semiring-with-meet

    -- If the mode 𝟘ᵐ is allowed and the modality does not come with a
    -- dedicated natrec-star operator, then _+ q is decreasing.
    +-decreasingˡ : T 𝟘ᵐ-allowed → ¬ ⊛-available → ∀ p q → p + q ≤ p
