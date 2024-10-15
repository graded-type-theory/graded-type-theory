------------------------------------------------------------------------
-- A property related to usage and ℕ
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Derived.Nat
  {a} {M : Set a}
  (𝕄 : Modality M)
  (R : Usage-restrictions 𝕄)
  where

open Modality 𝕄

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Dedicated-nr 𝕄
open import Graded.Modality.Dedicated-nr.Instance
open import Graded.Mode 𝕄
open import Graded.Usage 𝕄 R
open import Graded.Usage.Weakening 𝕄 R

open import Definition.Untyped M
open import Definition.Untyped.Nat 𝕄

open import Tools.Function

private variable
  A t u v : Term _
  γ δ η θ : Conₘ _
  m       : Mode
  p q     : M

opaque
  unfolding natcase

  -- A usage lemma for natcase.

  ▸natcase :
    ⦃ has-nr : Dedicated-nr ⦄ →
    γ ▸[ m ] t →
    δ ∙ ⌜ m ⌝ · p ▸[ m ] u →
    η ▸[ m ] v →
    θ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A →
    nrᶜ p 𝟘 γ δ η ▸[ m ] natcase p q A t u v
  ▸natcase {m} {δ} {p} ▸t ▸u ▸v ▸A =
    natrecₘ ▸t
      (sub (wkUsage (step id) ▸u) $ begin
         δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
         δ ∙ ⌜ m ⌝ · p ∙ 𝟘          ∎)
      ▸v ▸A
    where
    open ≤ᶜ-reasoning

opaque
  unfolding strict-const

  -- A usage lemma for strict-const.

  ▸strict-const :
    ⦃ has-nr : Dedicated-nr ⦄ →
    γ ▸[ 𝟘ᵐ? ] A →
    δ ▸[ m ] t →
    η ▸[ m ] u →
    nrᶜ 𝟘 𝟙 δ 𝟘ᶜ η ▸[ m ] strict-const A t u
  ▸strict-const {γ} {m} ▸A ▸t ▸u =
    natrecₘ ▸t
      (sub var $ begin
         𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟙  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-identityʳ _ ⟩
         𝟘ᶜ ∙ ⌜ m ⌝                  ∎)
      ▸u
      (sub (wkUsage (step id) ▸A) $ begin
         γ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
         γ ∙ 𝟘            ∎)
    where
    open ≤ᶜ-reasoning
