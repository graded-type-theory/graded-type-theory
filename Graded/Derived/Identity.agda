------------------------------------------------------------------------
-- Properties related to usage and Id
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Definition.Typed.Restrictions
open import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Derived.Identity
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄)
  where

open Modality 𝕄

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Properties 𝕄 UR
open import Graded.Usage.Weakening 𝕄 UR

open import Definition.Untyped M
open import Definition.Typed.Consequences.DerivedRules.Identity TR

open import Tools.Function
import Tools.Reasoning.PartialOrder

private variable
  A B t u v w         : Term _
  γ₁ γ₂ γ₃ γ₄ γ₅ γ₆ δ : Conₘ _
  m                   : Mode

opaque
  unfolding subst

  -- A (possibly suboptimal) usage rule for subst.

  ▸subst :
    γ₁ ▸[ 𝟘ᵐ? ] A →
    γ₂ ∙ ⌜ m ⌝ · ω ▸[ m ] B →
    γ₃ ▸[ m ] t →
    γ₄ ▸[ m ] u →
    γ₅ ▸[ m ] v →
    γ₆ ▸[ m ] w →
    ω ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅ ∧ᶜ γ₆) ▸[ m ] subst A B t u v w
  ▸subst {γ₁} {γ₂} {m} {γ₃} {γ₄} {γ₅} {γ₆} ▸A ▸B ▸t ▸u ▸v ▸w = sub
    (Jₘ-generalised ▸A ▸t
       (sub (wkUsage (step id) ▸B) $
        let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
          γ₂ ∙ ⌜ m ⌝ · ω ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
          γ₂ ∙ ⌜ m ⌝ · ω ∙ 𝟘          ∎)
       ▸w ▸u ▸v)
    (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       ω ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅ ∧ᶜ γ₆)  ≈⟨ ·ᶜ-congˡ $
                                             ≈ᶜ-trans (≈ᶜ-sym $ ∧ᶜ-assoc _ _ _) $
                                             ≈ᶜ-trans (∧ᶜ-congʳ $ ∧ᶜ-comm _ _) $
                                             ≈ᶜ-trans (∧ᶜ-assoc _ _ _) $
                                             ∧ᶜ-congˡ $ ∧ᶜ-congˡ $
                                             ≈ᶜ-trans (≈ᶜ-sym $ ∧ᶜ-assoc _ _ _) $
                                             ∧ᶜ-comm _ _ ⟩
       ω ·ᶜ (γ₃ ∧ᶜ γ₂ ∧ᶜ γ₆ ∧ᶜ γ₄ ∧ᶜ γ₅)  ∎)
