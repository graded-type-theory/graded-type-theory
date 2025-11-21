------------------------------------------------------------------------
-- Substitution matrices (action of substitutions on modality contexts).
------------------------------------------------------------------------

import Graded.Modality
import Graded.Mode
open import Graded.Usage.Restrictions

module Graded.Substitution
  {a b} {M : Set a} {Mode : Set b}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (open Graded.Mode Mode 𝕄)
  {𝐌 : IsMode}
  (R : Usage-restrictions 𝕄 𝐌)
  where

open Modality 𝕄
open IsMode 𝐌
open Usage-restrictions R

open import Definition.Untyped M
  using (Subst ; tail ; head ; Wk ; id ; step ; lift)
open import Graded.Context 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Usage R
open import Graded.Usage.Restrictions.Natrec 𝕄

open import Tools.Fin
open import Tools.Function
open import Tools.Level
open import Tools.Nat as N using (Nat; 1+)

infixl 50 _<*_
infixr 50 _*>_
infix  20 ∥_∥
infixl 30 _⊙_

private
  variable
    k m n : Nat

-- Substitutions are matrices represented as snoc-lists of modality contexts.
-- Ψ : Substₘ m n is an n×m-matrix.

data Substₘ : (m n : Nat) → Set a where
  []  : Substₘ m 0
  _⊙_ : Substₘ m n → Conₘ m → Substₘ m (1+ n)

private
  variable
    Ψ Φ : Substₘ m n

-- Substitutions that contain empty usage contexts.

εₘ : Substₘ 0 n
εₘ {n = 0}    = []
εₘ {n = 1+ n} = εₘ ⊙ ε

-- Application of substitution matrix from the left

_*>_ : (Ψ : Substₘ m n) → (γ : Conₘ m) → Conₘ n
[] *> γ = ε
(Ψ ⊙ δ) *> γ = Ψ *> γ ∙ γ * δ

-- Application of substitution matrix from the right

_<*_ : (γ : Conₘ n) → (Ψ : Substₘ m n) → Conₘ m
ε <* [] = 𝟘ᶜ
(γ ∙ p) <* (Ψ ⊙ δ) = p ·ᶜ δ +ᶜ (γ <* Ψ)

substₘ : (Ψ : Substₘ m n) → (γ : Conₘ n) → Conₘ m
substₘ Ψ γ = γ <* Ψ

-- Composition of substitution matrices

_<*>_ : (Ψ : Substₘ m k) (Φ : Substₘ k n) → Substₘ m n
Ψ <*> [] = []
Ψ <*> (Φ ⊙ δ) = (Ψ <*> Φ) ⊙ (δ <* Ψ)

---------------------------------------------------------------

-- Well-formed modality substitutions: if ∀ x. γ_x ▸[ γ x ] σ x, where
-- γ_x is the x-th row vector of Ψ, multiplied by ⌜ γ x ⌝, then
-- Ψ ▶[ γ ] σ.

_▶[_]_ : Substₘ m n → Mode-vector n → Subst m n → Set (a ⊔ b)
_▶[_]_ {n = n} Ψ γ σ =
  (x : Fin n) → ((𝟘ᶜ , x ≔ ⌜ γ x ⌝) <* Ψ) ▸[ γ x ] σ x

-- Substitution matrix inference (for modalities with nr functions).

∥_∥ :
  ⦃ ok : Natrec-mode-supports-usage-inference natrec-mode ⦄ →
  Subst m n → Mode-vector n → Substₘ m n
∥_∥ {n = 0}    _ _  = []
∥_∥ {n = 1+ n} σ ms = ∥ tail σ ∥ (tailᵐ ms) ⊙ ⌈ head σ ⌉ (headᵐ ms)

---------------------------------------------------------------
-- Modality substitutions corresponding to (term) weakenings --
---------------------------------------------------------------

-- Single step weakening of a substitution matrix

wk1Substₘ : Substₘ m n → Substₘ (1+ m) n
wk1Substₘ [] = []
wk1Substₘ (Ψ ⊙ δ) = (wk1Substₘ Ψ) ⊙ wkConₘ (step id) δ

-- Lifting a substitution matrix

liftSubstₘ : Substₘ m n → Substₘ (1+ m) (1+ n)
liftSubstₘ Ψ = (wk1Substₘ Ψ) ⊙ (𝟘ᶜ ∙ 𝟙)

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

-- Substitution matrices corresponding to the substitutions returned
-- by Definition.Untyped.wkSubst.

wkSubstₘ′ : ∀ k → Substₘ m n → Substₘ (k N.+ m) n
wkSubstₘ′ 0      = idᶠ
wkSubstₘ′ (1+ k) = wk1Substₘ ∘→ wkSubstₘ′ k
