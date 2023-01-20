{-# OPTIONS --without-K --safe #-}

open import Tools.Relation

module Tools.Algebra {a ℓ} (S : Setoid a ℓ) where

open Setoid S renaming (Carrier to A)

open import Tools.Level
open import Tools.Product

open import Algebra.Core using (Op₁; Op₂) public
open import Algebra.Definitions (_≈_)
     using (Associative; Commutative; Congruent₂; _DistributesOver_;
            _DistributesOverˡ_; _DistributesOverʳ_; Idempotent; _IdempotentOn_;
            Identity; LeftIdentity; LeftZero; RightIdentity; RightZero; Zero) public
open import Algebra.Structures (_≈_)
     using (IsBand; IsCommutativeMonoid; IsMagma; IsMonoid;
            IsSemigroup; IsSemilattice; IsSemiring;
            IsSemiringWithoutAnnihilatingZero) public

Op₃ : ∀ {ℓ} → Set ℓ → Set ℓ
Op₃ A = A → A → A → A


-- Sub-distributivity
_SubDistributesOverˡ_by_ : Op₂ A → Op₂ A → Rel A ℓ → Set (a ⊔ ℓ)
_*_ SubDistributesOverˡ _+_ by _≤_ =
  ∀ x y z → (x * (y + z)) ≤ ((x * y) + (x * z))

_SubDistributesOverʳ_by_ : Op₂ A → Op₂ A → Rel A ℓ → Set (a ⊔ ℓ)
_*_ SubDistributesOverʳ _+_ by _≤_ =
  ∀ x y z → ((y + z) * x) ≤ ((y * x) + (z * x))

_SubDistributesOver_by_ : Op₂ A → Op₂ A → Rel A ℓ → Set (a ⊔ ℓ)
* SubDistributesOver + by ≤ =
  * SubDistributesOverˡ + by ≤ × * SubDistributesOverʳ + by ≤

-- Sub-interchangable
_SubInterchangable_by_ : Op₂ A → Op₂ A → Rel A ℓ → Set _
_∘_ SubInterchangable _∙_ by _≤_ = ∀ w x y z → ((w ∙ x) ∘ (y ∙ z)) ≤ ((w ∘ y) ∙ (x ∘ z))
