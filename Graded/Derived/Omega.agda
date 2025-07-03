------------------------------------------------------------------------
-- Properties related to usage, ω and Ω
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Derived.Omega
  {a} {M : Set a}
  {𝕄 : Modality M}
  (UR : Usage-restrictions 𝕄)
  where

open Modality 𝕄 hiding (ω)

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄
open import Graded.Usage 𝕄 UR

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
    (m ≡ 𝟙ᵐ → p ≤ 𝟙 + p) →
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
      ∀ m → (m ≡ 𝟙ᵐ → p ≤ 𝟙 + p) → ⌜ m ⌝ · p ≤ ⌜ m ⌝ + p · ⌜ m ᵐ· p ⌝
    lemma 𝟘ᵐ hyp = begin
      𝟘 · p      ≡⟨ ·-zeroˡ _ ⟩
      𝟘          ≡˘⟨ ·-zeroʳ _ ⟩
      p · 𝟘      ≡˘⟨ +-identityˡ _ ⟩
      𝟘 + p · 𝟘  ∎
      where
      open Tools.Reasoning.PartialOrder ≤-poset
    lemma 𝟙ᵐ hyp = begin
      𝟙 · p              ≡⟨ ·-identityˡ _ ⟩
      p                  ≤⟨ hyp refl ⟩
      𝟙 + p              ≡˘⟨ +-congˡ ·⌜⌞⌟⌝ ⟩
      𝟙 + p · ⌜ ⌞ p ⌟ ⌝  ∎
      where
      open Tools.Reasoning.PartialOrder ≤-poset

    open ≤ᶜ-reasoning

opaque
  unfolding Ω

  -- A usage lemma for Ω.

  ▸Ω :
    (m ≡ 𝟙ᵐ → p ≤ 𝟙 + p) →
    𝟘ᶜ ▸[ m ] Ω {n = n} p
  ▸Ω {m} {p} hyp =
    sub (▸ω hyp ∘ₘ ▸ω hyp′) $ begin
      𝟘ᶜ             ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
      p ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityˡ _ ⟩
      𝟘ᶜ +ᶜ p ·ᶜ 𝟘ᶜ  ∎
    where
    hyp′ : m ᵐ· p ≡ 𝟙ᵐ → p ≤ 𝟙 + p
    hyp′ = case is-𝟘? p of λ where
      (yes refl) →
        m ᵐ· 𝟘 ≡ 𝟙ᵐ     →⟨ trans (sym (ᵐ·-zeroʳ m)) ⟩
        𝟘ᵐ? ≡ 𝟙ᵐ        ⇔⟨ 𝟘ᵐ?≡𝟙ᵐ⇔ ⟩→
        ¬ T 𝟘ᵐ-allowed  →⟨ Mode-propositional-without-𝟘ᵐ ⟩
        m ≡ 𝟙ᵐ          →⟨ hyp ⟩
        𝟘 ≤ 𝟙 + 𝟘       □
      (no p≢𝟘) →
        m ᵐ· p ≡ 𝟙ᵐ  →⟨ trans (sym (≢𝟘→ᵐ·≡ p≢𝟘)) ⟩
        m ≡ 𝟙ᵐ       →⟨ hyp ⟩
        p ≤ 𝟙 + p    □

    open ≤ᶜ-reasoning
