{-# OPTIONS --without-K --allow-unsolved-metas #-}
module Definition.Modality.Substitution where

open import Definition.Untyped as U
open import Definition.Untyped.Properties
open import Definition.Modality
open import Definition.Modality.Context
open import Definition.Modality.Context.Properties
open import Definition.Modality.Properties
open import Definition.Modality.Usage

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE

infix 28 _*>_
infix 50 ∥_∥

private
  variable
    M : Set
    ℓ m n : Nat
    𝕄 : Modality M

-- Substitutions are matrices represented as snoc-lists of modality contexts.

data Substₘ (𝕄 : Modality M) : (m n : Nat) → Set where
  ε   : Substₘ 𝕄 m 0
  _∙_ : Substₘ 𝕄 m n →  Conₘ 𝕄 m → Substₘ 𝕄 m (1+ n)

private
  variable
    Ψ Φ : Substₘ 𝕄 m n

-- Application of substitution matrix from the left

_*>_ : (Ψ : Substₘ 𝕄 m n) → (γ : Conₘ 𝕄 n) → Conₘ 𝕄 m
ε *> ε = 𝟘ᶜ
(Ψ ∙ δ) *> (γ ∙ p) = p ·ᶜ δ +ᶜ (Ψ *> γ)

substₘ = _*>_

-- Application of substitution matrix from the right

_<*_ : (γ : Conₘ 𝕄 m) → (Ψ : Substₘ 𝕄 m n) → Conₘ 𝕄 n
γ <* ε = ε
γ <* (Ψ ∙ δ) = (γ <* Ψ) ∙ (γ * δ)

-- Composition of substitution matrices

_<*>_ : (Ψ : Substₘ 𝕄 m ℓ) (Φ : Substₘ 𝕄 ℓ n) → Substₘ 𝕄 m n
Ψ <*> ε = ε
Ψ <*> (Φ ∙ δ) = (Ψ <*> Φ) ∙ (Ψ *> δ)

-- Prepend a substitution matrix with a row

addrow : (Ψ : Substₘ 𝕄 m n) → (γ : Conₘ 𝕄 n) → Substₘ 𝕄 (1+ m) n
addrow ε ε = ε
addrow (Ψ ∙ δ) (γ ∙ p) = addrow Ψ γ ∙ (δ ∙ p)

---------------------------------------------------------------

-- Well formed modality substitutions
-- If ∀ x. γₓ ▸ σ x, where γₓ is the x-th column vector of Ψ, then Ψ ▶ σ

_▶_ : {𝕄 : Modality M} (Ψ : Substₘ 𝕄 m n) → (σ : Subst M m n) → Set
_▶_ {n = n} {𝕄 = 𝕄} Ψ σ = ∀ (x : Fin n) → (Ψ *> (𝟘ᶜ , x ≔ (Modality.𝟙 𝕄))) ▸ (σ x)

-- Substitution matrix calculation

∥_∥ : {𝕄 : Modality M} (σ : Subst M m n) → Substₘ 𝕄 m n
∥_∥ {n = Nat.zero} {𝕄 = 𝕄} σ = ε
∥_∥ {n = 1+ n} {𝕄 = 𝕄} σ = ∥ (str σ) ∥ ∙ ⌈ σ x0 ⌉

---------------------------------------------------------------
-- Modality substitutions corresponding to (term) weakenings --
---------------------------------------------------------------

-- Single step weakening of a substitution matrix

wk1Substₘ : Substₘ 𝕄 m n → Substₘ 𝕄 (1+ m) n
wk1Substₘ ε = ε
wk1Substₘ {𝕄 = 𝕄} (Ψ ∙ δ) = (wk1Substₘ Ψ) ∙ (δ ∙ Modality.𝟘 𝕄)

-- Lifting a substitution matrix

liftSubstₘ : Substₘ 𝕄 m n → Substₘ 𝕄 (1+ m) (1+ n)
liftSubstₘ {𝕄 = 𝕄} Ψ = (wk1Substₘ Ψ) ∙ (𝟘ᶜ , x0 ≔ Modality.𝟙 𝕄)

-- Identity substitution matrix

idSubstₘ : Substₘ 𝕄 n n
idSubstₘ {n = Nat.zero} = ε
idSubstₘ {𝕄 = 𝕄} {n = 1+ n} = liftSubstₘ idSubstₘ

-- Substitution matrix from a weakening

wkSubstₘ : (ρ : Wk m n) → Substₘ 𝕄 m n
wkSubstₘ id       = idSubstₘ
wkSubstₘ (step ρ) = wk1Substₘ (wkSubstₘ ρ)
wkSubstₘ (lift ρ) = liftSubstₘ (wkSubstₘ ρ)

------------------------------------------------------------------
-- Modality substitutions corresponding to (term) substitutions --
------------------------------------------------------------------

-- Extend a  substitution matrix with a single term substitution

consSubstₘ : (Ψ : Substₘ 𝕄 m n) → (γ : Conₘ 𝕄 m) → Substₘ 𝕄 m (1+ n)
consSubstₘ = _∙_

-- Single term substitution matrix

sgSubstₘ : (γ : Conₘ 𝕄 n) → Substₘ 𝕄 n (1+ n)
sgSubstₘ = consSubstₘ idSubstₘ
