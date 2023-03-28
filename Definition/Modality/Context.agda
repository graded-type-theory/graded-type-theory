open import Definition.Modality

module Definition.Modality.Context
  {a} {M : Set a} (𝕄 : Modality M) where

open Modality 𝕄

open import Tools.Fin
open import Tools.Nat renaming (_+_ to _+ⁿ_)
open import Tools.PropositionalEquality

infixl 30 _∙_
infixr 40 _+ᶜ_
infixr 40 _∧ᶜ_
infixr 45 _·ᶜ_
infixr 45 _*_
infix  50 _⊛ᶜ_▷_
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

data _≈ᶜ_ : (γ δ : Conₘ n) → Set a where
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

_≤ᶜ_ : (γ δ : Conₘ n) → Set a
γ ≤ᶜ δ = γ ≈ᶜ γ ∧ᶜ δ

-- ⊛ lifted to modality contexts

_⊛ᶜ_▷_ : (γ δ : Conₘ n) (r : M) → Conₘ n
ε ⊛ᶜ ε ▷ r = ε
(γ ∙ p) ⊛ᶜ (δ ∙ q) ▷ r = (γ ⊛ᶜ δ ▷ r) ∙ (p ⊛ q ▷ r)

-- Zero modality context

𝟘ᶜ : Conₘ n
𝟘ᶜ {n = 0}    = ε
𝟘ᶜ {n = 1+ n} = 𝟘ᶜ ∙ 𝟘

-- Unit modality context

𝟙ᶜ : Conₘ n
𝟙ᶜ {n = 0}    = ε
𝟙ᶜ {n = 1+ n} = 𝟙ᶜ ∙ 𝟙
