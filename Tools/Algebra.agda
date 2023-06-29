------------------------------------------------------------------------
-- Algebraic structures and properties
------------------------------------------------------------------------

open import Tools.Relation

module Tools.Algebra {a} (A : Set a) where

open import Tools.Product
open import Tools.PropositionalEquality

open import Algebra.Consequences.Propositional public
  using (comm+idˡ⇒idʳ; comm+zeˡ⇒zeʳ; comm+distrˡ⇒distrʳ)
open import Algebra.Core using (Op₁; Op₂) public
open import Algebra.Definitions (_≡_ {A = A})
     using (Associative; Commutative; Congruent₂; _DistributesOver_;
            _DistributesOverˡ_; _DistributesOverʳ_; Idempotent; _IdempotentOn_;
            Identity; LeftIdentity; LeftZero; RightIdentity; RightZero; Zero) public
open import Algebra.Structures (_≡_ {A = A})
     using (IsBand; IsCommutativeMonoid; IsMagma; IsMonoid;
            IsSemigroup; IsSemilattice; IsSemiring;
            IsSemiringWithoutAnnihilatingZero; IsCommutativeSemiring)
     public
open import Algebra.Bundles using (Semiring) public
open import Algebra.Module.Structures
     using (IsLeftSemimodule; IsPreleftSemimodule) public

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
