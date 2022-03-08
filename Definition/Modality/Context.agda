{-# OPTIONS --without-K --safe #-}

open import Tools.Level
open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Context {a ℓ}
       {M′ : Setoid a ℓ} (𝕄 : Modality M′)
       where

open Modality 𝕄
open Setoid M′ renaming (Carrier to M)

open import Tools.Fin
open import Tools.Nat renaming (_+_ to _+ⁿ_)
open import Tools.Product
open import Tools.Unit

open import Definition.Modality.Properties 𝕄

infixl 30 _∙_
infixr 40 _+ᶜ_
infixr 40 _∧ᶜ_
infixr 45 _·ᶜ_
infixr 45 _*_
infix  10 _≤ᶜ_
infix  35 _,_≔_
infix  60 _⟨_⟩

private
  variable
    m n : Nat


-- Modality Contexts are snoc-lists

data Conₘ : Nat → Set a where
  ε   : Conₘ 0
  _∙_ : (γ : Conₘ n) → (p : M) → Conₘ (1+ n)

-- Modality equality lifted pointwise to contexts

data _≈ᶜ_ : (γ δ : Conₘ n) → Set (a ⊔ ℓ) where
  ε : ε ≈ᶜ ε
  _∙_ : {γ δ : Conₘ n} {p q : M} → γ ≈ᶜ δ → p ≈ q → (γ ∙ p) ≈ᶜ (δ ∙ q)


headₘ : (γ : Conₘ (1+ n)) → M
headₘ (γ ∙ p) = p

tailₘ : (γ : Conₘ (1+ n)) → Conₘ n
tailₘ (γ ∙ p) = γ

-- Update the value of an element in a context

_,_≔_ : (γ : Conₘ n) (x : Fin n) (p : M) → Conₘ n
(γ ∙ q) , x0     ≔ p = γ ∙ p
(γ ∙ q) , (x +1) ≔ p = (γ , x ≔ p) ∙ q

-- Insert a new element in a context at a given position

insertAt : (m : Nat) → (γ : Conₘ (m +ⁿ n)) → (p : M) → Conₘ (m +ⁿ 1+ n)
insertAt 0       γ      p = γ ∙ p
insertAt (1+ m) (γ ∙ q) p = insertAt m γ p ∙ q


-- Look up an element in a context

_⟨_⟩ : (γ : Conₘ n) → (x : Fin n) → M
(γ ∙ p) ⟨ x0 ⟩   = p
(γ ∙ p) ⟨ x +1 ⟩ = γ ⟨ x ⟩


-- Scalar product of modality contexts

_*_ : (γ δ : Conₘ n) → M
ε * ε = 𝟘
(γ ∙ p) * (δ ∙ q) = γ * δ + p · q

-- Addition lifted to modality contexts

_+ᶜ_ : (γ δ : Conₘ n) → Conₘ n
ε +ᶜ ε = ε
(γ ∙ p) +ᶜ (δ ∙ q) = (γ +ᶜ δ) ∙ (p + q)

-- Meet lifted to modality contexts

_∧ᶜ_ : (γ δ : Conₘ n) → Conₘ n
ε ∧ᶜ ε = ε
(γ ∙ p) ∧ᶜ (δ ∙ q) = (γ ∧ᶜ δ) ∙ (p ∧ q)

-- Modality context scaling

_·ᶜ_ : (p : M) (γ : Conₘ n) → Conₘ n
p ·ᶜ ε = ε
p ·ᶜ (γ ∙ q) = (p ·ᶜ γ) ∙ (p · q)


-- Partial order of modality contexts

_≤ᶜ_ : (γ δ : Conₘ n) → Set (a ⊔ ℓ)
γ ≤ᶜ δ = γ ≈ᶜ γ ∧ᶜ δ

-- nr-recurrence relation lifted to modality contexts

nrᶜ : (γ δ : Conₘ n) (r : M) → Conₘ n
nrᶜ ε ε r = ε
nrᶜ (γ ∙ p) (δ ∙ q) r = (nrᶜ γ δ r) ∙ nr p q r


-- Zero modality context

𝟘ᶜ : Conₘ n
𝟘ᶜ {n = 0}    = ε
𝟘ᶜ {n = 1+ n} = 𝟘ᶜ ∙ 𝟘

-- Unit modality context

𝟙ᶜ : Conₘ n
𝟙ᶜ {n = 0}    = ε
𝟙ᶜ {n = 1+ n} = 𝟙ᶜ ∙ 𝟙
