{-# OPTIONS --without-K --safe #-}

module Definition.Modality.Context where

open import Definition.Modality

open import Tools.Fin
open import Tools.Nat
open import Tools.PropositionalEquality

import Definition.Modality.Properties

infixl 30 _∙_
infixr 20 _+ᶜ_
infixr 20 _∧ᶜ_
infixr 25 _·ᶜ_
infix  10 _≤ᶜ_
infix  15 _,_≔_
infix  14 _⟨_⟩

private
  variable
    m n : Nat
    M : Set
    𝕄 : Modality M


-- Modality Contexts are snoc-lists carrying a proof that its elements belong to a modality ringoid

data Conₘ {M : Set} (𝕄 : Modality M) : Nat → Set where
  ε   : Conₘ 𝕄 0
  _∙_ : {n : Nat} → (γ : Conₘ 𝕄 n) → (p : M) → Conₘ 𝕄 (1+ n)

headₘ : {𝕄 : Modality M} (γ : Conₘ 𝕄 (1+ n)) → M
headₘ (γ ∙ p) = p

tailₘ : (γ : Conₘ 𝕄 (1+ n)) → Conₘ 𝕄 n
tailₘ (γ ∙ p) = γ


-- Update the value of an element in a context

_,_≔_ : {𝕄 : Modality M} (γ : Conₘ 𝕄 n) (x : Fin n) (p : M) → Conₘ 𝕄 n
(γ ∙ q) , x0     ≔ p = γ ∙ p
(γ ∙ q) , (x +1) ≔ p = (γ , x ≔ p) ∙ q

-- Insert a new element in a context at a given position
insertAt : {𝕄 : Modality M} → (m : Nat) → (γ : Conₘ 𝕄 (m + n)) → (p : M) → Conₘ 𝕄 (m + 1+ n)
insertAt 0       γ      p = γ ∙ p
insertAt (1+ m) (γ ∙ q) p = insertAt m γ p ∙ q


-- Look up an element in a context

_⟨_⟩ : {𝕄 : Modality M} → (γ : Conₘ 𝕄 n) → (x : Fin n) → M
(γ ∙ p) ⟨ x0 ⟩ = p
(γ ∙ p) ⟨ x +1 ⟩ = γ ⟨ x ⟩


-- Scalar product of modality contexts

_*_ : {𝕄 : Modality M} (γ δ : Conₘ 𝕄 n) → M
_*_ {𝕄 = 𝕄} ε ε = Modality.𝟘 𝕄
_*_ {𝕄 = 𝕄} (γ ∙ p) (δ ∙ q) = Modality._+_ 𝕄 (γ * δ) (Modality._·_ 𝕄 p q)

-- Addition lifted to modality contexts

_+ᶜ_ : (γ δ : Conₘ 𝕄 n) → Conₘ 𝕄 n
ε +ᶜ ε = ε
_+ᶜ_ {𝕄 = 𝕄} (γ ∙ p) (δ ∙ q) = (γ +ᶜ δ) ∙ Modality._+_ 𝕄 p q

-- Meet lifted to modality contexts

_∧ᶜ_ : (γ δ : Conₘ 𝕄 n) → Conₘ 𝕄 n
ε ∧ᶜ ε = ε
_∧ᶜ_ {𝕄 = 𝕄} (γ ∙ p) (δ ∙ q) = (γ ∧ᶜ δ) ∙ Modality._∧_ 𝕄 p q

-- Modality context scaling

_·ᶜ_ : {𝕄 : Modality M} (p : M) (γ : Conₘ 𝕄 n) → Conₘ 𝕄 n
p ·ᶜ ε = ε
_·ᶜ_ {𝕄 = 𝕄} p (γ ∙ q) = (p ·ᶜ γ) ∙ Modality._·_ 𝕄 p q

-- Partial order of modality contexts

_≤ᶜ_ : (γ δ : Conₘ 𝕄 n) → Set
γ ≤ᶜ  δ = γ ≡ γ ∧ᶜ δ


-- Zero modality context

𝟘ᶜ : Conₘ 𝕄 n
𝟘ᶜ          {n = 0}    = ε
𝟘ᶜ {𝕄 = 𝕄} {n = 1+ n} = 𝟘ᶜ ∙ Modality.𝟘 𝕄

-- Unit modality context

𝟙ᶜ : Conₘ 𝕄 n
𝟙ᶜ          {n = 0}    = ε
𝟙ᶜ {𝕄 = 𝕄} {n = 1+ n} = 𝟙ᶜ ∙ Modality.𝟙 𝕄
