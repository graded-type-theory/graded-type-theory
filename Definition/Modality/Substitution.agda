{-#OPTIONS --without-K --safe #-}

open import Tools.Level
open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Substitution
  {M′ : Setoid _ _} (𝕄 : Modality M′)
  where

open Modality 𝕄

open import Definition.Untyped M
  using (Subst ; tail ; head ; Wk ; id ; step ; lift)
open import Definition.Untyped.Properties M
open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties 𝕄
open import Definition.Modality.Properties 𝕄
open import Definition.Modality.Usage 𝕄

open import Tools.Fin
open import Tools.Nat
open import Tools.Product

infixr 50 _*>_
infix  20 ∥_∥
infixl 30 _⊙_

private
  variable
    ℓ m n : Nat

-- Substitutions are matrices represented as snoc-lists of modality contexts.

data Substₘ : (m n : Nat) → Set where
  []  : Substₘ m 0
  _⊙_ : Substₘ m n →  Conₘ m → Substₘ m (1+ n)

private
  variable
    Ψ Φ : Substₘ m n

-- Application of substitution matrix from the left

_*>_ : (Ψ : Substₘ m n) → (γ : Conₘ n) → Conₘ m
[] *> ε = 𝟘ᶜ
(Ψ ⊙ δ) *> (γ ∙ p) = p ·ᶜ δ +ᶜ (Ψ *> γ)

substₘ = _*>_

-- Application of substitution matrix from the right

_<*_ : (γ : Conₘ m) → (Ψ : Substₘ m n) → Conₘ n
γ <* [] = ε
γ <* (Ψ ⊙ δ) = (γ <* Ψ) ∙ (γ * δ)

-- Composition of substitution matrices

_<*>_ : (Ψ : Substₘ m ℓ) (Φ : Substₘ ℓ n) → Substₘ m n
Ψ <*> [] = []
Ψ <*> (Φ ⊙ δ) = (Ψ <*> Φ) ⊙ (Ψ *> δ)

-- Prepend a substitution matrix with a row

addrow : (Ψ : Substₘ m n) → (γ : Conₘ n) → Substₘ (1+ m) n
addrow [] ε = []
addrow (Ψ ⊙ δ) (γ ∙ p) = addrow Ψ γ ⊙ (δ ∙ p)

---------------------------------------------------------------

-- Well formed modality substitutions
-- If ∀ x. γₓ ▸ σ x, where γₓ is the x-th column vector of Ψ, then Ψ ▶ σ

_▶_ : (Ψ : Substₘ m n) → (σ : Subst m n) → Set
_▶_ {n = n} Ψ σ = ∀ (x : Fin n) → (Ψ *> (𝟘ᶜ , x ≔ 𝟙)) ▸ (σ x)

-- Substitution matrix inference

∥_∥ : (σ : Subst m n) → Substₘ m n
∥_∥ {n = 0}    σ = []
∥_∥ {n = 1+ n} σ = ∥ tail σ ∥ ⊙ ⌈ head σ ⌉

---------------------------------------------------------------
-- Modality substitutions corresponding to (term) weakenings --
---------------------------------------------------------------

-- Single step weakening of a substitution matrix

wk1Substₘ : Substₘ m n → Substₘ (1+ m) n
wk1Substₘ [] = []
wk1Substₘ (Ψ ⊙ δ) = (wk1Substₘ Ψ) ⊙ (δ ∙ 𝟘)

-- Lifting a substitution matrix

liftSubstₘ : Substₘ m n → Substₘ (1+ m) (1+ n)
liftSubstₘ Ψ = (wk1Substₘ Ψ) ⊙ (𝟘ᶜ , x0 ≔ 𝟙)

-- Identity substitution matrix

idSubstₘ : Substₘ n n
idSubstₘ {n = 0} = []
idSubstₘ {n = 1+ n} = liftSubstₘ idSubstₘ

-- Substitution matrix from a weakening

wkSubstₘ : (ρ : Wk m n) → Substₘ m n
wkSubstₘ id       = idSubstₘ
wkSubstₘ (step ρ) = wk1Substₘ (wkSubstₘ ρ)
wkSubstₘ (lift ρ) = liftSubstₘ (wkSubstₘ ρ)

------------------------------------------------------------------
-- Modality substitutions corresponding to (term) substitutions --
------------------------------------------------------------------

-- Extend a  substitution matrix with a single term substitution

consSubstₘ : (Ψ : Substₘ m n) → (γ : Conₘ m) → Substₘ m (1+ n)
consSubstₘ = _⊙_

-- Single term substitution matrix

sgSubstₘ : (γ : Conₘ n) → Substₘ n (1+ n)
sgSubstₘ = consSubstₘ idSubstₘ
