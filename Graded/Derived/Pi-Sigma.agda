------------------------------------------------------------------------
-- Properties related to usage, Π and Σ
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Derived.Pi-Sigma
  {a} {M : Set a} {𝕄 : Modality M}
  (UR : Usage-restrictions 𝕄)
  where

open Modality 𝕄

open import Definition.Untyped M
open import Definition.Untyped.Pi-Sigma M

open import Graded.Context 𝕄
open import Graded.Derived.Lift UR
open import Graded.Mode 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Weakening 𝕄 UR

private variable
  A B l₁ l₂   : Term _
  γ₁ γ₂ γ₃ γ₄ : Conₘ _
  p q         : M
  m           : Mode
  b           : BinderMode

opaque
  unfolding ΠΣʰ

  -- A usage lemma for ΠΣʰ.

  ▸ΠΣʰ :
    γ₁ ▸[ 𝟘ᵐ? ] l₁ →
    γ₂ ▸[ 𝟘ᵐ? ] l₂ →
    γ₃ ▸[ m ᵐ· p ] A →
    γ₄ ∙ ⌜ m ⌝ · q ▸[ m ] B →
    γ₃ +ᶜ γ₄ ▸[ m ] ΠΣʰ b p q l₁ l₂ A B
  ▸ΠΣʰ ▸l₁ ▸l₂ ▸A ▸B =
    ΠΣₘ (Liftₘ ▸l₂ ▸A) (Liftₘ (wkUsage _ ▸l₁) (▸lower₀ ▸B))
