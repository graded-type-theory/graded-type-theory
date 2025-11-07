------------------------------------------------------------------------
-- A property related to usage and ℕ
------------------------------------------------------------------------

import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Derived.Nat
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  (R : Usage-restrictions 𝕄)
  where

open Modality 𝕄
open Usage-restrictions R

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄
open import Graded.Usage 𝕄 R
open import Graded.Usage.Properties 𝕄 R
open import Graded.Usage.Restrictions.Instance R
open import Graded.Usage.Weakening 𝕄 R

open import Definition.Untyped M
open import Definition.Untyped.Nat 𝕄

open import Tools.Bool using (T)
open import Tools.Function
open import Tools.Product

private variable
  A t u v   : Term _
  γ δ η θ χ : Conₘ _
  m         : Mode
  p q       : M

opaque
  unfolding natcase

  -- A usage lemma for natcase.

  ▸natcase′ :
    γ ▸[ m ] t →
    δ ∙ ⌜ m ⌝ · p ▸[ m ] u →
    η ▸[ m ] v →
    θ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A →
    (⦃ has-nr : Nr-available ⦄ →
     χ ≤ᶜ nrᶜ p 𝟘 γ δ η) →
    (⦃ no-nr : Nr-not-available ⦄ →
     χ ≤ᶜ γ ×
     (T 𝟘ᵐ-allowed →
      χ ≤ᶜ δ) ×
     (⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
      χ ≤ᶜ η) ×
     χ ≤ᶜ δ +ᶜ p ·ᶜ η) →
    (⦃ no-nr : Nr-not-available-GLB ⦄ →
      χ ≤ᶜ (𝟙 ∧ p) ·ᶜ η +ᶜ (γ ∧ᶜ δ)) →
    χ ▸[ m ] natcase p q A t u v
  ▸natcase′ {m} {δ} {p} {η} {χ} ▸t ▸u ▸v ▸A hyp₁ hyp₂ hyp₃ =
    natrec-nr-or-no-nrₘ ▸t
      (sub (wkUsage _ ▸u) $ begin
         δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
         δ ∙ ⌜ m ⌝ · p ∙ 𝟘          ∎)
      ▸v ▸A hyp₁
      (let le₁ , le₂ , le₃ , le₄ = hyp₂ in
      le₁ , le₂ , le₃ ,
      (begin
         χ                      ≤⟨ le₄ ⟩
         δ +ᶜ p ·ᶜ η            ≈˘⟨ +ᶜ-congˡ $
                                    ≈ᶜ-trans (+ᶜ-congˡ (·ᶜ-zeroˡ _)) $
                                    +ᶜ-identityʳ _ ⟩
         δ +ᶜ p ·ᶜ η +ᶜ 𝟘 ·ᶜ χ  ∎))
      (_ , _ ,
       Greatest-lower-bound-nrᵢ-𝟘 ,
       Greatest-lower-boundᶜ-nrᵢᶜ-𝟘 ,
       hyp₃)
    where
    open ≤ᶜ-reasoning

opaque
  unfolding natcase

  -- A usage lemma for natcase.

  ▸natcase :
    ⦃ has-nr : Nr-available ⦄ →
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
    ⦃ has-nr : Nr-available ⦄ →
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
