{-# OPTIONS --without-K --safe #-}

open import Tools.Relation

module Definition.Typechecking.Deterministic {a ℓ} (M′ : Setoid a ℓ) where

open Setoid M′ using () renaming (Carrier to M)

open import Definition.Typechecking M′
open import Definition.Typed M′
open import Definition.Typed.Properties M′
open import Definition.Untyped M hiding (_∷_; U≢B; ℕ≢B; B≢ne)

open import Tools.Fin
open import Tools.Nat
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    t A B : Term n
    Γ : Con Term n


deterministic⇉-var : {x : Fin n} → x ∷ A ∈ Γ → x ∷ B ∈ Γ → A PE.≡ B
deterministic⇉-var {x = x0} here here = PE.refl
deterministic⇉-var {x = x +1} (there y) (there z) rewrite deterministic⇉-var y z = PE.refl

-- Type inference is deterministic
-- If Γ ⊢ t ⇉ A and Γ ⊢ t ⇉ B then A ≡ B

deterministic⇉ : Γ ⊢ t ⇉ A → Γ ⊢ t ⇉ B → A PE.≡ B
deterministic⇉ (Πᵢ x x₁) (Πᵢ x₂ x₃) = PE.refl
deterministic⇉ (Σᵢ x x₁) (Σᵢ x₂ x₃) = PE.refl
deterministic⇉ (varᵢ x) (varᵢ x₁) = deterministic⇉-var x x₁
deterministic⇉ (appᵢ x x₁ x₂ p≈p′) (appᵢ y x₃ x₄ q≈q′) with deterministic⇉ x y
... | PE.refl with whrDet* x₁ x₃
... | PE.refl = PE.refl
deterministic⇉ (fstᵢ x x₁) (fstᵢ y x₂) with deterministic⇉ x y
... | PE.refl with whrDet* x₁ x₂
... | PE.refl = PE.refl
deterministic⇉ (sndᵢ x x₁) (sndᵢ y x₂) with deterministic⇉ x y
... | PE.refl with whrDet* x₁ x₂
... | PE.refl = PE.refl
deterministic⇉ (prodrecᵢ x x₁ x₂ x₃) (prodrecᵢ x₄ y x₅ x₆) = PE.refl
deterministic⇉ ℕᵢ ℕᵢ = PE.refl
deterministic⇉ zeroᵢ zeroᵢ = PE.refl
deterministic⇉ (sucᵢ x) (sucᵢ x₁) = PE.refl
deterministic⇉ (natrecᵢ x x₁ x₂ x₃) (natrecᵢ x₄ x₅ x₆ x₇) = PE.refl
deterministic⇉ Unitᵢ Unitᵢ = PE.refl
deterministic⇉ starᵢ starᵢ = PE.refl
deterministic⇉ Emptyᵢ Emptyᵢ = PE.refl
deterministic⇉ (Emptyrecᵢ x x₁) (Emptyrecᵢ x₂ x₃) = PE.refl
