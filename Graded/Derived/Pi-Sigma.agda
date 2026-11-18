------------------------------------------------------------------------
-- Properties related to usage, Π and Σ
------------------------------------------------------------------------

open import Configuration-types
open import Graded.Modality
open import Graded.Mode

module Graded.Derived.Pi-Sigma
  {a a′} {M : Set a} {Mode : Set a′}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (C : Configuration 𝐌)
  where

open Modality 𝕄
open IsMode 𝐌

open import Definition.Untyped M
open import Definition.Untyped.Pi-Sigma M

open import Graded.Context 𝕄
open import Graded.Derived.Lift C
open import Graded.Usage C
open import Graded.Usage.Weakening C

private variable
  A B         : Term _
  l₁ l₂       : Lvl _
  γ₁ γ₂ γ₃ γ₄ : Conₘ _
  p q         : M
  m           : Mode
  b           : BinderMode

opaque
  unfolding ΠΣʰ

  -- A usage lemma for ΠΣʰ.

  ▸ΠΣʰ :
    γ₁ ▸[ 𝟘ᵐ ] l₁ →
    γ₂ ▸[ 𝟘ᵐ ] l₂ →
    γ₃ ▸[ m ᵐ· p ] A →
    γ₄ ∙ ⌜ m ⌝ · q ▸[ m ] B →
    p ·ᶜ γ₃ +ᶜ γ₄ ▸[ m ] ΠΣʰ b p q l₁ l₂ A B
  ▸ΠΣʰ ▸l₁ ▸l₂ ▸A ▸B =
    ΠΣₘ (Liftₘ ▸l₂ ▸A) (Liftₘ (wkUsage _ ▸l₁) (▸lower₀ ▸B))
