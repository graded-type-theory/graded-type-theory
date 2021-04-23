{-# OPTIONS --without-K --safe  #-}

open import Tools.Relation
open import Definition.Modality

module Definition.Usage
  {M : Set} {_≈_ : Rel M _}
  (𝕄 : Modality M _≈_)
  where

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Usage 𝕄
open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed M

open import Tools.Nat
open import Tools.Product

open Modality 𝕄

private
  variable
    n : Nat

infix 22 _▷_▹▹_
infix 22 _××_

-- Combined well-typed and usage relations

_⊢_◂_ : (Γ : Con Term n) (A : Term n) (γ : Conₘ n) → Set
Γ ⊢ A ◂ γ = (Γ ⊢ A) × (γ ▸ A)

_⊢_▸_∷_◂_ : (Γ : Con Term n) (γ : Conₘ n) (t A : Term n) (δ : Conₘ n) → Set
Γ ⊢ γ ▸ t ∷ A ◂ δ = (Γ ⊢ t ∷ A) × (γ ▸ t) × (δ ▸ A)

-- Non-dependent version of Π.

_▷_▹▹_ : (p : M) → (F G : Term n) → Term n
p ▷ F ▹▹ G = Π p , 𝟘 ▷ F ▹ wk1 G

-- Non-dependent products.

_××_ : (F G : Term n) → Term n
F ×× G = Σ 𝟘 ▷ F ▹ wk1 G
