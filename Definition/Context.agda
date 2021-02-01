{-# OPTIONS --without-K --safe #-}

module Definition.Context where

open import Definition.Modality
open import Tools.Nat
open import Tools.PropositionalEquality

infixr 20 _·_

data Con (A : Set) : Set where
  ε   : Con A
  _·_ : Con A → A → Con A

-- Addition lifted to modality contexts
_[_+_] : {M : Set} → Modality M → (γ δ : Con M) → Con M
M [ γ     + ε     ] = γ
M [ ε     + δ     ] = δ
M [ γ · p + δ · q ] = (M [ γ + δ ]) · (Modality._+_ M p q)

infixr 15 _∷_+_
infixr 15 _∷_∧_
infixr 18 _∷_·_

_∷_+_  : {M : Set} → Modality M →  (γ δ : Con M) → Con M
M ∷ γ     + ε     = γ
M ∷ ε     + δ     = δ
M ∷ γ · p + δ · q = M ∷ γ + δ · Modality._+_ M p q

-- Meet lifted to modality contexts
_∷_∧_ : {M : Set} → Modality M → (γ δ : Con M) → Con M
M ∷ γ     ∧ ε     = γ
M ∷ ε     ∧ δ     = δ
M ∷ γ · p ∧ δ · q = M ∷ γ ∧ δ · Modality._∧_ M p q

-- Scaling of modality contexts
_∷_·_ : {M : Set} → Modality M → (p : M) → (γ : Con M) → Con M
M ∷ p ·  ε      = ε
M ∷ p · (γ · q) = (M ∷ p · γ) · Modality._·_ M p q

-- Partial order for modalities lifted to modality contexts
_∷_≤_ : {M : Set} → Modality M → (γ δ : Con M) → Set
M ∷ γ ≤ δ = γ ≡ (M ∷ γ ∧ δ )

-- Zero modality context of length n
𝟘ᶜ : {M : Set} → Modality M → (n : Nat) → Con M
𝟘ᶜ M 0      = ε
𝟘ᶜ M (1+ n) = (𝟘ᶜ M n) · (Modality.𝟘 M)

-- Unit modality context of length n
𝟙ᶜ : {M : Set} → Modality M → (n : Nat) → Con M
𝟙ᶜ M 0      = ε
𝟙ᶜ M (1+ n) = (𝟙ᶜ M n) · (Modality.𝟙 M)
