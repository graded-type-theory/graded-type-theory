------------------------------------------------------------------------
-- Modality (grade) contexts.
------------------------------------------------------------------------

import Graded.Modality

module Graded.Context
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  where

open Modality 𝕄

open import Graded.Modality.Nr-instances

open import Tools.Fin
open import Tools.Level
open import Tools.Nat using (Nat; 1+; Sequence)
open import Tools.Product
open import Tools.PropositionalEquality

infixl 24 _∙_
infixr 40 _+ᶜ_
infixr 43 _∧ᶜ_
infixr 45 _·ᶜ_
infixr 45 _*_
infix  50 _⊛ᶜ_▷_
infix  10 _≤ᶜ_
infixl 35 _,_≔_
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
  _∙_ : {γ δ : Conₘ n} {p q : M} → γ ≈ᶜ δ → p ≡ q → (γ ∙ p) ≈ᶜ (δ ∙ q)


headₘ : (γ : Conₘ (1+ n)) → M
headₘ (γ ∙ p) = p

tailₘ : (γ : Conₘ (1+ n)) → Conₘ n
tailₘ (γ ∙ p) = γ

-- Update the value of an element in a context

_,_≔_ : (γ : Conₘ n) (x : Fin n) (p : M) → Conₘ n
ε , ()           ≔ _
(γ ∙ q) , x0     ≔ p = γ ∙ p
(γ ∙ q) , (x +1) ≔ p = (γ , x ≔ p) ∙ q

-- Look up an element in a context

_⟨_⟩ : (γ : Conₘ n) → (x : Fin n) → M
ε       ⟨ () ⟩
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

-- Nr functions can be lifted to usage contexts (the first two
-- arguments are still single grades).

nrᶜ :
  ⦃ has-nr : Has-nr 𝕄 ⦄ →
  M → M → Conₘ n → Conₘ n → Conₘ n → Conₘ n
nrᶜ p r ε       ε       ε       = ε
nrᶜ p r (γ ∙ g) (δ ∙ d) (η ∙ e) = nrᶜ p r γ δ η ∙ nr p r g d e

-- Natrec-star operators can be lifted to usage contexts (the last
-- argument is still a single grade).

_⊛ᶜ_▷_ :
  ⦃ has-star : Has-star 𝕄 ⦄ →
  Conₘ n → Conₘ n → M → Conₘ n
ε       ⊛ᶜ ε     ▷ r = ε
(γ ∙ p) ⊛ᶜ δ ∙ q ▷ r = (γ ⊛ᶜ δ ▷ r) ∙ (p ⊛ q ▷ r)

-- Constant contexts

replicateᶜ : (n : Nat) → M → Conₘ n
replicateᶜ 0 m = ε
replicateᶜ (1+ n) m = replicateᶜ n m ∙ m

-- Zero modality context

𝟘ᶜ : Conₘ n
𝟘ᶜ {n} = replicateᶜ n 𝟘

-- Unit modality context

𝟙ᶜ : Conₘ n
𝟙ᶜ {n} = replicateᶜ n 𝟙

-- Greatest-such-thatᶜ P γ means that γ is the greatest context which
-- satisfies P.

Greatest-such-thatᶜ : ∀ {ℓ} → (Conₘ n → Set ℓ) → Conₘ n → Set (a ⊔ ℓ)
Greatest-such-thatᶜ P γ = P γ × (∀ δ → P δ → δ ≤ᶜ γ)

-- Greatest-lower-boundᶜ γ γᵢ means that γ is the greatest context which
-- is lower than all contexts of the sequence γᵢ.

Greatest-lower-boundᶜ : Conₘ n → Sequence (Conₘ n) → Set a
Greatest-lower-boundᶜ γ γᵢ = Greatest-such-thatᶜ (λ δ → ∀ i → δ ≤ᶜ γᵢ i) γ
