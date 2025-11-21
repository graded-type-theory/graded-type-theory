------------------------------------------------------------------------
-- Properties related to usage and Π
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Derived.Pi
  {a} {M : Set a} {𝕄 : Modality M}
  (UR : Usage-restrictions 𝕄)
  where

open Modality 𝕄

open import Definition.Untyped M
open import Definition.Untyped.Pi M

open import Graded.Context 𝕄
open import Graded.Derived.Lift UR
open import Graded.Mode 𝕄
open import Graded.Usage 𝕄 UR

private variable
  t u : Term _
  γ δ : Conₘ _
  p   : M
  m   : Mode

opaque
  unfolding lamʰ

  -- A usage lemma for lamʰ.

  ▸lamʰ :
    γ ∙ ⌜ m ⌝ · p ▸[ m ] t →
    γ ▸[ m ] lamʰ p t
  ▸lamʰ ▸t = lamₘ (liftₘ (▸lower₀ ▸t))

opaque
  unfolding ∘ʰ

  -- A usage lemma for ∘ʰ.

  ▸∘ʰ :
    γ ▸[ m ] t →
    δ ▸[ m ᵐ· p ] u →
    γ +ᶜ p ·ᶜ δ ▸[ m ] ∘ʰ p t u
  ▸∘ʰ ▸t ▸u = lowerₘ (▸t ∘ₘ liftₘ ▸u)
