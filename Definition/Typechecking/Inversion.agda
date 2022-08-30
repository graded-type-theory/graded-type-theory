{-# OPTIONS --safe --without-K #-}

open import Tools.Relation

module Definition.Typechecking.Inversion {a ℓ} (M′ : Setoid a ℓ) where

open Setoid M′ using (_≈_) renaming (Carrier to M; refl to ≈-refl)

open import Definition.Typechecking M′
open import Definition.Typed M′
open import Definition.Untyped M hiding (_∷_)

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    t u A B : Term n
    p p′ : M

inversion⇉-app : Γ ⊢ t ∘ p′ ▷ u ⇉ B → ∃₄ λ F G p q → ∃ λ A → (Γ ⊢ t ⇉ A) × (Γ ⊢ A ↘ (Π p , q ▷ F ▹ G)) × (Γ ⊢ u ⇇ F) × (p ≈ p′) × G [ u ] PE.≡ B
inversion⇉-app (appᵢ x x₁ x₂ x₃) = _ , _ , _ , _ , _ , x , x₁ , x₂ , x₃ , PE.refl
