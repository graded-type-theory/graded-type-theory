{-# OPTIONS --without-K --safe #-}

module Definition.Context where

open import Definition.Modality
open import Tools.PropositionalEquality

data Con (A : Set) : Set where
  ε   : Con A
  _·_ : Con A → A → Con A

-- Addition lifted to modality contexts
_[_+_] : {M : Set} → Modality M → (γ δ : Con M) → Con M
M [ γ     + ε     ] = γ
M [ ε     + δ     ] = δ
M [ γ · p + δ · q ] = (M [ γ + δ ]) · (Modality._+_ M p q)

-- Meet lifted to modality contexts
_[_∧_] : {M : Set} → Modality M → (γ δ : Con M) → Con M
M [ γ     ∧ ε     ] = γ
M [ ε     ∧ δ     ] = δ
M [ γ · p ∧ δ · q ] = (M [ γ ∧ δ ]) · (Modality._∧_ M p q)

-- Scaling of modality contexts
_[_·_] : {M : Set} → Modality M → (p : M) → (γ : Con M) → Con M
M [ p ·  ε      ] = ε
M [ p · (γ · q) ] = (M [ p · γ ]) · Modality._·_ M p q

-- Partial order for modalities lifted to modality contexts
_[_≤_] : {M : Set} → Modality M → ( γ δ : Con M) → Set
M [ γ ≤ δ ] = γ ≡ (M [ γ ∧ δ ])

