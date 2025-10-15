------------------------------------------------------------------------
-- Properties related to usage and Lift
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Derived.Lift
  {a} {M : Set a} {𝕄 : Modality M}
  (UR : Usage-restrictions 𝕄)
  where

open Modality 𝕄

open import Definition.Untyped M
open import Definition.Untyped.Lift M

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Mode 𝕄
open import Graded.Substitution 𝕄 UR
open import Graded.Substitution.Properties 𝕄 UR
open import Graded.Usage 𝕄 UR

open import Tools.Fin
open import Tools.Function
open import Tools.PropositionalEquality

private variable
  t : Term _
  γ : Conₘ _
  m : Mode

opaque
  unfolding lower₀

  -- A usage lemma for lower₀.

  ▸lower₀ :
    γ ▸[ m ] t →
    γ ▸[ m ] lower₀ t
  ▸lower₀ {γ = γ ∙ p} ▸t =
    sub
      (substₘ-lemma _
         (▶-cong _ (λ { x0 → refl; (_ +1) → refl }) $
          wf-replace₁ₘ $ lowerₘ $ sub var $ begin
            ⌜ ⌞ p ⌟ ⌝ ·ᶜ 𝟘ᶜ ∙ ⌜ ⌞ p ⌟ ⌝ · 𝟙  ≈⟨ ·ᶜ-zeroʳ _ ∙ ·-identityʳ _ ⟩
            𝟘ᶜ              ∙ ⌜ ⌞ p ⌟ ⌝      ∎)
         ▸t)
      (begin
         γ ∙ p                            ≈˘⟨ +ᶜ-identityˡ _ ∙ ·-identityʳ _ ⟩
         𝟘ᶜ +ᶜ γ ∙ p · 𝟙                  ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ∙ +-identityʳ _ ⟩
         p ·ᶜ 𝟘ᶜ +ᶜ γ ∙ p · 𝟙 + 𝟘         ≈˘⟨ <*-replace₁ₘ ⟩
         (γ ∙ p) <* replace₁ₘ 1 (𝟘ᶜ ∙ 𝟙)  ∎)
    where
    open ≤ᶜ-reasoning
