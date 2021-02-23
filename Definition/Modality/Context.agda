{-# OPTIONS --without-K --safe #-}

module Definition.Modality.Context where

open import Definition.Modality

open import Tools.Nat
open import Tools.PropositionalEquality

infixl 30 _∙_
infixr 20 _+ᶜ_
infixr 20 _∧ᶜ_
infix  25 _·ᶜ_
infix  10 _≤ᶜ_
infix  10 _≋_

private
  variable
    n : Nat
    M : Set
    𝕄 : Modality M


-- Modality Context
data ConM {M : Set} (𝕄 : Modality M) : Nat → Set where
  ε   : ConM 𝕄 0
  _∙_ : {n : Nat} → ConM 𝕄 n → M → ConM 𝕄 (1+ n)

-- Addition lifted to modality contexts
_+ᶜ_ : (γ δ : ConM 𝕄 n) → ConM 𝕄 n
ε +ᶜ ε = ε
_+ᶜ_ {𝕄 = 𝕄} (γ ∙ p) (δ ∙ q) = (γ +ᶜ δ) ∙ Modality._+_ 𝕄 p q

-- Meet lifted to modality contexts
_∧ᶜ_ : (γ δ : ConM 𝕄 n) → ConM 𝕄 n
ε ∧ᶜ ε = ε
_∧ᶜ_ {𝕄 = 𝕄} (γ ∙ p) (δ ∙ q) = (γ ∧ᶜ δ) ∙ Modality._∧_ 𝕄 p q

-- Modality context scaling
_·ᶜ_ : {𝕄 : Modality M} (p : M) (γ : ConM 𝕄 n) → ConM 𝕄 n
p ·ᶜ ε = ε
_·ᶜ_ {𝕄 = 𝕄} p (γ ∙ q) = (p ·ᶜ γ) ∙ Modality._·_ 𝕄 p q

-- Partial order of modality contexts
_≤ᶜ_ : (γ δ : ConM 𝕄 n) → Set
γ ≤ᶜ δ = γ ≡ γ ∧ᶜ δ

-- Equality relation for modality contexts
data _≋_ {𝕄 : Modality M} : (γ δ : ConM 𝕄 n) → Set where
  ε   : ε ≋ ε
  _∙_ : ∀ {n} {γ δ : ConM 𝕄 n} {p q} → γ ≋ δ → Modality._≈_ 𝕄 p q → γ ∙ p ≋ δ ∙ q
  
-- Zero modality context
𝟘ᶜ : ConM 𝕄 n
𝟘ᶜ          {n = 0}    = ε
𝟘ᶜ {𝕄 = 𝕄} {n = 1+ n} = 𝟘ᶜ ∙ Modality.𝟘 𝕄

-- Unit modality context
𝟙ᶜ : ConM 𝕄 n
𝟙ᶜ          {n = 0}    = ε
𝟙ᶜ {𝕄 = 𝕄} {n = 1+ n} = 𝟙ᶜ ∙ Modality.𝟙 𝕄
