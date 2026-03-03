------------------------------------------------------------------------
-- Properties related to usage and Lift
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions

module Graded.Derived.Lift
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (R : Usage-restrictions 𝕄 𝐌)
  where

open Modality 𝕄
open IsMode 𝐌

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Substitution R
open import Graded.Substitution.Properties R
open import Graded.Usage R

open import Definition.Untyped M hiding (lift)
open import Definition.Untyped.Lift M

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
      (substₘ-lemma
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
