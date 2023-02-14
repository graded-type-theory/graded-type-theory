{-# OPTIONS --without-K --safe #-}

open import Tools.Level
open import Tools.Relation

module Definition.Modality {a ℓ} (M′ : Setoid a ℓ) where

open Setoid M′ renaming (Carrier to M)

open import Tools.Algebra M′
open import Tools.Nat hiding (_+_)
open import Tools.Product
open import Tools.Sum

open import Definition.Modality.Restrictions M′

-- Modality ringoid
record ModalityWithout⊛ : Set (lsuc (a ⊔ ℓ)) where
  infixr 40 _+_
  infixr 40 _∧_
  infixr 45 _·_
  infix  10 _≤_


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

    -- It is decidable whether a value is equivalent to 𝟘.
    is-𝟘? : (p : M) → Dec (p ≈ 𝟘)

    -- The following two assumptions match assumptions from Bob
    -- Atkey's "Syntax and Semantics of Quantitative Type Theory".

    -- The semiring has the zero-product property: if p · q is 𝟘, then
    -- either p is 𝟘 or q is 𝟘.
    zero-product : {p q : M} → p · q ≈ 𝟘 → (p ≈ 𝟘) ⊎ (q ≈ 𝟘)

    -- The semiring is positive: if p + q is 𝟘, then p and q are 𝟘.
    -- (The statement that p + q ≈ 𝟘 implies q ≈ 𝟘 follows from the
    -- one below, see
    -- Definition.Modality.Properties.Addition.positiveʳ.)
    positiveˡ : {p q : M} → p + q ≈ 𝟘 → p ≈ 𝟘

  -- Semilattice partial ordering relation
  _≤_ : Rel M ℓ
  p ≤ q = p ≈ (p ∧ q)

  field
    -- The following assumption matches one in Conor McBride's
    -- "I Got Plenty o’ Nuttin’".

    -- Every value that is "greater than or equal to" 𝟘 is equivalent
    -- to 𝟘.
    𝟘≮ : {p : M} → 𝟘 ≤ p → p ≈ 𝟘

    -- If p ∧ q is equivalent to 𝟘, then p ≤ 𝟘.
    ∧≤𝟘ˡ : {p q : M} → p ∧ q ≈ 𝟘 → p ≤ 𝟘

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

  open IsEquivalence ≈-equivalence public
    using ()
    renaming (refl to ≈-refl;
              sym to ≈-sym;
              trans to ≈-trans;
              reflexive to ≈-reflexive
             )

  open Restrictions restrictions public

record Modality : Set (lsuc (a ⊔ ℓ)) where
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
    -- ⊛ respects the equivalence relation
    ⊛-cong : ∀ {p p′ q q′ r r′} → p ≈ p′ → q ≈ q′ → r ≈ r′ → p ⊛ q ▷ r ≈ p′ ⊛ q′ ▷ r′

    -- addition is sub-interchangable over ⊛ w.r.t the first two arguments
    +-sub-interchangable-⊛ : (r : M) → _+_ SubInterchangable (_⊛_▷ r) by _≤_
    -- multiplication is right sub-distributive over ⊛ w.r.t the first two arguments
    ·-sub-distribʳ-⊛ : (r : M) → _·_ SubDistributesOverʳ (_⊛_▷ r) by _≤_
    -- ⊛ is sub-distributive over meet w.r.t the first two arguments
    ⊛-sub-distrib-∧    : (r : M) → (_⊛_▷ r) SubDistributesOver _∧_ by _≤_

    -- If p ⊛ q ▷ r is equivalent to 𝟘, then p ≤ 𝟘.
    ⊛≤𝟘ˡ : {p q r : M} → p ⊛ q ▷ r ≈ 𝟘 → p ≤ 𝟘
    -- If p ⊛ q ▷ r is equivalent to 𝟘, then q ≤ 𝟘.
    ⊛≤𝟘ʳ : {p q r : M} → p ⊛ q ▷ r ≈ 𝟘 → q ≤ 𝟘

  ⊛-ineq₁ : (p q r : M) → p ⊛ q ▷ r ≤ q + r · (p ⊛ q ▷ r)
  ⊛-ineq₁ = proj₁ ⊛-ineq

  ⊛-ineq₂ : (p q r : M) → p ⊛ q ▷ r ≤ p
  ⊛-ineq₂ = proj₂ ⊛-ineq

  ⊛-sub-distribˡ-∧ : (r : M) → (_⊛_▷ r) SubDistributesOverˡ _∧_ by _≤_
  ⊛-sub-distribˡ-∧ r = proj₁ (⊛-sub-distrib-∧ r)

  ⊛-sub-distribʳ-∧ : (r : M) → (_⊛_▷ r) SubDistributesOverʳ _∧_ by _≤_
  ⊛-sub-distribʳ-∧ r = proj₂ (⊛-sub-distrib-∧ r)
