------------------------------------------------------------------------
-- Algebraic structures and properties
------------------------------------------------------------------------

open import Tools.Relation

module Tools.Algebra {a} (A : Set a) where

open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality

open import Algebra.Consequences.Propositional public
      using (comm∧idˡ⇒idʳ; comm∧zeˡ⇒zeʳ; comm∧distrˡ⇒distrʳ; comm∧distrʳ⇒distrˡ)
open import Algebra.Core public using (Op₁; Op₂)
open import Algebra.Definitions (_≡_ {A = A}) public
     using (Associative; Commutative; Congruent₂;
            _DistributesOver_; _DistributesOverˡ_; _DistributesOverʳ_;
            Idempotent; _IdempotentOn_;
            Identity; LeftIdentity; RightIdentity;
            Zero; LeftZero; RightZero;
            Absorptive)
open import Algebra.Structures (_≡_ {A = A}) public
     using (IsBand; IsCommutativeMonoid; IsMagma; IsMonoid;
            IsSemigroup; IsSemiring;
            IsSemiringWithoutAnnihilatingZero; IsCommutativeSemiring)
open import Algebra.Lattice.Structures (_≡_ {A = A}) public
     using (IsMeetSemilattice; IsDistributiveLattice)
open import Algebra.Bundles public
     using (Semiring)
open import Algebra.Module.Structures public
     using (IsLeftSemimodule; IsPreleftSemimodule)
import Algebra.Lattice.Properties.DistributiveLattice

Op₃ : ∀ {ℓ} → Set ℓ → Set ℓ
Op₃ A = A → A → A → A


-- Sub-distributivity
_SubDistributesOverˡ_by_ : Op₂ A → Op₂ A → Rel A a → Set a
_*_ SubDistributesOverˡ _+_ by _≤_ =
  ∀ x y z → (x * (y + z)) ≤ ((x * y) + (x * z))

_SubDistributesOverʳ_by_ : Op₂ A → Op₂ A → Rel A a → Set a
_*_ SubDistributesOverʳ _+_ by _≤_ =
  ∀ x y z → ((y + z) * x) ≤ ((y * x) + (z * x))

_SubDistributesOver_by_ : Op₂ A → Op₂ A → Rel A a → Set a
* SubDistributesOver + by ≤ =
  * SubDistributesOverˡ + by ≤ × * SubDistributesOverʳ + by ≤

-- Sub-interchangeable
_SubInterchangeable_by_ : Op₂ A → Op₂ A → Rel A a → Set _
_∘_ SubInterchangeable _∙_ by _≤_ = ∀ w x y z → ((w ∙ x) ∘ (y ∙ z)) ≤ ((w ∘ y) ∙ (x ∘ z))

-- Some properties related to distributive lattices.

module DistributiveLattice
  {_∨_ _∧_ : Op₂ A}
  (dl : IsDistributiveLattice _∨_ _∧_)
  where

  open Algebra.Lattice.Properties.DistributiveLattice
    (record { isDistributiveLattice = dl })
    public

-- Bounded, distributive lattices over A.

record Bounded-distributive-lattice : Set a where
  no-eta-equality
  pattern
  infixr 40 _∨_
  infixr 43 _∧_
  field
    -- Meet.
    _∧_ : A → A → A

    -- Join.
    _∨_ : A → A → A

    -- The least element.
    ⊥ : A

    -- The greatest element.
    ⊤ : A

    -- Join and meet form a distributive lattice.
    is-distributive-lattice : IsDistributiveLattice _∨_ _∧_

  open IsDistributiveLattice is-distributive-lattice public
  open DistributiveLattice is-distributive-lattice public

  -- An induced ordering relation.

  _≤_ : A → A → Set a
  p ≤ q = p ≡ p ∧ q

  field
    -- ⊥ is the least element.
    ⊥≤ : ∀ p → ⊥ ≤ p

    -- ⊤ is the greatest element.
    ≤⊤ : ∀ p → p ≤ ⊤

  ∨-identityˡ : LeftIdentity ⊥ _∨_
  ∨-identityˡ p =
    ⊥ ∨ p        ≡⟨ cong (_∨ _) (⊥≤ _) ⟩
    (⊥ ∧ p) ∨ p  ≡⟨ cong (_∨ _) (∧-comm _ _) ⟩
    (p ∧ ⊥) ∨ p  ≡⟨ ∨-comm _ _ ⟩
    p ∨ (p ∧ ⊥)  ≡⟨ ∨-absorbs-∧ _ _ ⟩
    p            ∎
    where
    open Tools.Reasoning.PropositionalEquality
