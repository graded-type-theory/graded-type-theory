------------------------------------------------------------------------
-- Properties related to usage and Empty
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions

module Graded.Derived.Empty
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (UR : Usage-restrictions 𝕄 𝐌)
  where

open Modality 𝕄
open IsMode 𝐌
open Usage-restrictions UR

open import Definition.Untyped M
open import Definition.Untyped.Empty 𝕄

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Usage UR
open import Graded.Usage.Inversion UR
open import Graded.Usage.Properties UR
open import Graded.Usage.Weakening UR

open import Tools.Empty
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality

open ≤ᶜ-reasoning

private variable
  A t   : Term _
  γ δ η : Conₘ _
  m     : Mode

opaque
  unfolding emptyrec-sink

  -- A usage rule for emptyrec-sink.

  ▸emptyrec-sink : γ ▸[ 𝟘ᵐ ] t → δ ▸[ 𝟘ᵐ ] A →
                   Emptyrec-allowed m 𝟘 → Starˢ-sink →
                   ⌜ m ⌝ ·ᶜ η ▸[ m ] emptyrec-sink A t
  ▸emptyrec-sink {γ} {δ} {m} {η} ▸t ▸A ok ok′ =
    sub ((emptyrecₘ (▸-cong (sym (ᵐ·-zeroʳ m)) ▸t)
           (ΠΣₘ {δ = δ} Unitₘ
              (sub-≈ᶜ (wkUsage (step id) ▸A) (≈ᶜ-refl ∙ ·-zeroʳ _)))
           ok)
        ∘ₘ (starˢₘ (⊥-elim ∘→ not-sink-and-no-sink ok′)))
      (begin
        ⌜ m ⌝ ·ᶜ η                     ≈˘⟨ ·ᶜ-congʳ (cong ⌜_⌝ (ᵐ·-identityʳ {m})) ⟩
        ⌜ m ᵐ· 𝟙 ⌝ ·ᶜ η                ≈˘⟨ +ᶜ-identityˡ _ ⟩
        𝟘ᶜ +ᶜ ⌜ m ᵐ· 𝟙 ⌝ ·ᶜ η          ≈˘⟨ +ᶜ-cong (·ᶜ-zeroˡ γ) (·ᶜ-identityˡ _) ⟩
        𝟘 ·ᶜ γ +ᶜ 𝟙 ·ᶜ ⌜ m ᵐ· 𝟙 ⌝ ·ᶜ η ∎)

opaque
  unfolding emptyrec-sink

  -- A usage inversion lemma for emptyrec-sink.

  inv-usage-emptyrec-sink :
    γ ▸[ m ] emptyrec-sink A t →
    ∃₂ λ δ η → δ ▸[ 𝟘ᵐ ] t × η ▸[ 𝟘ᵐ ] A × Emptyrec-allowed m 𝟘
  inv-usage-emptyrec-sink {m} ▸ers =
    let invUsageApp ▸er ▸s γ≤ = inv-usage-app ▸ers
        invUsageEmptyrec ▸t ▸Π ok δ≤ = inv-usage-emptyrec ▸er
        invUsageΠΣ ▸⊤ ▸A η≤ = inv-usage-ΠΣ ▸Π
    in  _ , _ , ▸-cong (ᵐ·-zeroʳ m) ▸t , wkUsage⁻¹ ▸A , ok
