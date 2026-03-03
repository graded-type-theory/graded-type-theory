------------------------------------------------------------------------
-- Properties related to usage, ω and Ω
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions

module Graded.Derived.Omega
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (UR : Usage-restrictions 𝕄 𝐌)
  where

open Modality 𝕄 hiding (ω)
open IsMode 𝐌

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Usage UR

open import Definition.Untyped.Omega M

open import Tools.Bool
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
open import Tools.Relation

private variable
  n : Nat
  γ : Conₘ _
  m : Mode
  p : M

opaque
  unfolding ω

  -- A usage lemma for ω.

  ▸ω :
    (⌜ m ⌝ ≢ 𝟘 → p ≤ 𝟙 + p) →
    𝟘ᶜ ▸[ m ] ω {n = n} p
  ▸ω {m} {p} hyp =
    lamₘ $
    sub (var ∘ₘ var) $ begin
      𝟘ᶜ ∙ ⌜ m ⌝ · p                          ≤⟨ ≤ᶜ-refl ∙ lemma _ hyp ⟩
      𝟘ᶜ ∙ ⌜ m ⌝ + p · ⌜ m ᵐ· p ⌝             ≈˘⟨ +ᶜ-identityˡ _ ∙ refl ⟩
      𝟘ᶜ +ᶜ 𝟘ᶜ ∙ ⌜ m ⌝ + p · ⌜ m ᵐ· p ⌝       ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _) ∙ refl ⟩
      (𝟘ᶜ ∙ ⌜ m ⌝) +ᶜ p ·ᶜ (𝟘ᶜ ∙ ⌜ m ᵐ· p ⌝)  ∎
    where
    lemma :
      ∀ m → (⌜ m ⌝ ≢ 𝟘 → p ≤ 𝟙 + p) → ⌜ m ⌝ · p ≤ ⌜ m ⌝ + p · ⌜ m ᵐ· p ⌝
    lemma m hyp =
      case is-𝟘? ⌜ m ⌝ of λ where
        (yes ⌜m⌝≡𝟘) → begin
          ⌜ m ⌝ · p              ≈⟨ ⌜⌝-·-comm _ ⟩
          p · ⌜ m ⌝              ≡˘⟨ +-identityˡ _ ⟩
          𝟘 + p · ⌜ m ⌝          ≡˘⟨ +-cong ⌜m⌝≡𝟘 (·⌜ᵐ·⌝ _) ⟩
          ⌜ m ⌝ + p · ⌜ m ᵐ· p ⌝ ∎
        (no ⌜m⌝≢𝟘) → begin
          ⌜ m ⌝ · p              ≤⟨ ·-monotoneʳ (hyp ⌜m⌝≢𝟘) ⟩
          ⌜ m ⌝ · (𝟙 + p)        ≡⟨ ·-distribˡ-+ _ _ _ ⟩
          ⌜ m ⌝ · 𝟙 + ⌜ m ⌝ · p  ≡⟨ +-cong (·-identityʳ _) (⌜⌝-·-comm _) ⟩
          ⌜ m ⌝ + p · ⌜ m ⌝      ≡˘⟨ +-congˡ (·⌜ᵐ·⌝ _) ⟩
          ⌜ m ⌝ + p · ⌜ m ᵐ· p ⌝ ∎
      where
      open ≤-reasoning

    open ≤ᶜ-reasoning

opaque
  unfolding Ω

  -- A usage lemma for Ω.

  ▸Ω :
    (⌜ m ⌝ ≢ 𝟘 → p ≤ 𝟙 + p) →
    𝟘ᶜ ▸[ m ] Ω {n = n} p
  ▸Ω {m} {p} hyp =
    sub (▸ω hyp ∘ₘ ▸ω (hyp ∘→ ⌜⌝-·ᵐ-𝟘ˡ)) $ begin
      𝟘ᶜ             ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
      p ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityˡ _ ⟩
      𝟘ᶜ +ᶜ p ·ᶜ 𝟘ᶜ  ∎
    where
    open ≤ᶜ-reasoning
