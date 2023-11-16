------------------------------------------------------------------------
-- Some properties related to usage and Erased
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Untyped.NotParametrised using (Strength)

module Graded.Derived.Erased.Usage
  {a} {M : Set a}
  (𝕄 : Modality M)
  (R : Usage-restrictions M)
  (s : Strength)
  where

open Modality 𝕄

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Usage 𝕄 R
open import Graded.Usage.Inversion 𝕄 R
open import Graded.Usage.Properties 𝕄 R
open import Graded.Mode 𝕄

open import Definition.Untyped M hiding (_∷_)
import Graded.Derived.Erased.Untyped
open Graded.Derived.Erased.Untyped 𝕄 s

open import Tools.Bool
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

private variable
  A t : Term _
  γ   : Conₘ _
  m   : Mode

------------------------------------------------------------------------
-- Usage rules

opaque

  -- A usage rule for Erased.

  ▸Erased :
    γ ▸[ 𝟘ᵐ? ] A →
    γ ▸[ m ] Erased A
  ▸Erased {γ} {m} ▸A = sub
    (ΠΣₘ
       (▸-cong (PE.sym (ᵐ·-zeroʳ m)) ▸A)
       (sub Unitₘ
          (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
             𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
             𝟘ᶜ              ∎)))
    (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       γ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
       γ +ᶜ 𝟘ᶜ  ∎)

opaque

  ▸[] : γ ▸[ 𝟘ᵐ? ] t → 𝟘ᶜ ▸[ m ] [ t ]
  ▸[] {(n)} {γ} {t} {m} ▸t = lemma s PE.refl
    where
    open Tools.Reasoning.PartialOrder (≤ᶜ-poset {n})
    lemma : ∀ s′ → s PE.≡ s′ → 𝟘ᶜ ▸[ m ] [ t ]
    lemma 𝕤 PE.refl = sub
      (prodˢₘ (▸-cong (PE.sym (ᵐ·-zeroʳ m)) ▸t) starₘ)
      (begin
         𝟘ᶜ             ≈˘⟨ ∧ᶜ-idem _ ⟩
         𝟘ᶜ ∧ᶜ 𝟘ᶜ       ≈˘⟨ ∧ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
         𝟘 ·ᶜ γ ∧ᶜ 𝟘ᶜ  ∎)
    lemma 𝕨 PE.refl = sub
      (prodʷₘ (▸-cong (PE.sym (ᵐ·-zeroʳ m)) ▸t) starₘ)
      (begin
         𝟘ᶜ             ≈˘⟨ +ᶜ-identityˡ _ ⟩
         𝟘ᶜ +ᶜ 𝟘ᶜ       ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
         𝟘 ·ᶜ γ +ᶜ 𝟘ᶜ  ∎)

------------------------------------------------------------------------
-- Inversion lemmas for usage

opaque

  -- An inversion lemma for Erased.

  inv-usage-Erased : γ ▸[ m ] Erased A → γ ▸[ 𝟘ᵐ? ] A
  inv-usage-Erased {γ} {m} ▸Erased =
    case inv-usage-ΠΣ ▸Erased of λ {
      (invUsageΠΣ {δ = δ} {η = η} ▸A ▸Unit γ≤) →
    sub (▸-cong (ᵐ·-zeroʳ m) ▸A) $ begin
      γ        ≤⟨ γ≤ ⟩
      δ +ᶜ η   ≤⟨ +ᶜ-monotoneʳ (tailₘ-monotone (inv-usage-Unit ▸Unit)) ⟩
      δ +ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityʳ _ ⟩
      δ        ∎ }
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

opaque

  -- An inversion lemma for [_].

  inv-usage-[] : γ ▸[ m ] [ t ] → (∃ λ δ → δ ▸[ 𝟘ᵐ? ] t) × γ ≤ᶜ 𝟘ᶜ
  inv-usage-[] {(n)} {γ} {m} {t} ▸[] = lemma s PE.refl
    where
    open Tools.Reasoning.PartialOrder (≤ᶜ-poset {n})
    lemma : ∀ s′ → s PE.≡ s′ → (∃ λ δ → δ ▸[ 𝟘ᵐ? ] t) × γ ≤ᶜ 𝟘ᶜ
    lemma 𝕤 PE.refl =
      case inv-usage-prodˢ ▸[] of λ {
        (invUsageProdˢ {δ = δ} {η = η} ▸t ▸star γ≤) →
      (_ , ▸-cong (ᵐ·-zeroʳ m) ▸t)
      , (begin
          γ            ≤⟨ γ≤ ⟩
          𝟘 ·ᶜ δ ∧ᶜ η  ≈⟨ ∧ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
          𝟘ᶜ ∧ᶜ η      ≤⟨ ∧ᶜ-decreasingˡ _ _ ⟩
          𝟘ᶜ           ∎) }
    lemma 𝕨 PE.refl =
      case inv-usage-prodʷ ▸[] of λ {
        (invUsageProdʷ {δ = δ} {η} ▸t ▸star γ≤) →
      case inv-usage-starʷ ▸star of λ
        η≤𝟘 →
      (_ , ▸-cong (ᵐ·-zeroʳ m) ▸t)
      , (begin
          γ            ≤⟨ γ≤ ⟩
          𝟘 ·ᶜ δ +ᶜ η  ≈⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
          𝟘ᶜ +ᶜ η      ≈⟨ +ᶜ-identityˡ _ ⟩
          η            ≤⟨ η≤𝟘 ⟩
          𝟘ᶜ           ∎) }
