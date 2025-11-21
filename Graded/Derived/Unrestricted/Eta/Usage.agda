------------------------------------------------------------------------
-- Some properties related to usage and Unrestricted
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions

module Graded.Derived.Unrestricted.Eta.Usage
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (R : Usage-restrictions 𝕄 𝐌)
  where

open Modality 𝕄
open IsMode 𝐌

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Usage R
open import Graded.Usage.Inversion R
open import Graded.Usage.Properties R

open import Definition.Untyped M
open import Graded.Derived.Unrestricted.Eta.Untyped 𝕄

open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≡_)
import Tools.Reasoning.PartialOrder

private variable
  A t : Term _
  p   : M
  γ   : Conₘ _
  m   : Mode

private

  -- The quantity ω · p is bounded by 𝟘.

  ω·≤𝟘 : ω · p ≤ 𝟘
  ω·≤𝟘 {p = p} = begin
    ω · p  ≤⟨ ·-monotoneˡ ω≤𝟘 ⟩
    𝟘 · p  ≈⟨ ·-zeroˡ _ ⟩
    𝟘      ∎
    where
    open Tools.Reasoning.PartialOrder ≤-poset

  -- If γ is multiplied by ω (from the left), then the result is
  -- bounded by 𝟘ᶜ.

  ω·ᶜ≤ᶜ𝟘ᶜ : ω ·ᶜ γ ≤ᶜ 𝟘ᶜ
  ω·ᶜ≤ᶜ𝟘ᶜ {γ = ε}     = ε
  ω·ᶜ≤ᶜ𝟘ᶜ {γ = _ ∙ _} = ω·ᶜ≤ᶜ𝟘ᶜ ∙ ω·≤𝟘

------------------------------------------------------------------------
-- Usage rules

-- A usage rule for Unrestricted.

▸Unrestricted :
  ⌜ m ⌝ · ω ≤ 𝟘 →
  γ ▸[ m ] A →
  γ ▸[ m ] Unrestricted A
▸Unrestricted {m = m} {γ = γ} mω≤𝟘 ▸A = sub
  (ΠΣₘ ▸A
     (sub Unitₘ
        (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
           𝟘ᶜ ∙ ⌜ m ⌝ · ω  ≤⟨ ≤ᶜ-refl ∙ mω≤𝟘 ⟩
           𝟘ᶜ              ∎)))
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     γ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
     γ +ᶜ 𝟘ᶜ  ∎)

-- A usage rule for [_].

▸[] : γ ▸[ m ] t → ω ·ᶜ γ ▸[ m ] [ t ]
▸[] {γ = γ} {m = m} ▸t = sub
  (prodˢₘ (▸-cong (PE.sym ᵐ·-identityʳ-ω) ▸t) starₘ)
  (begin
     ω ·ᶜ γ        ≤⟨ ∧ᶜ-greatest-lower-bound ≤ᶜ-refl ω·ᶜ≤ᶜ𝟘ᶜ ⟩
     ω ·ᶜ γ ∧ᶜ 𝟘ᶜ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- A usage rule for unbox.

▸unbox : γ ▸[ m ] t → γ ▸[ m ] unbox t
▸unbox {m = m} ▸t = fstₘ
  m
  (▸-cong (PE.sym ᵐ·-identityʳ-ω) ▸t)
  ᵐ·-identityʳ-ω
  λ _ → ω≤𝟙

------------------------------------------------------------------------
-- Inversion lemmas for usage

-- An inversion lemma for Unrestricted.

inv-usage-Unrestricted :
  γ ▸[ m ] Unrestricted A →
  ⌜ m ⌝ · ω ≤ 𝟘 × γ ▸[ m ] A
inv-usage-Unrestricted {γ = γ} {m = m} ▸Unrestricted =
  case inv-usage-ΠΣ ▸Unrestricted of λ {
    (invUsageΠΣ {δ = δ} {η = η} ▸A ▸Unit γ≤) →
  case inv-usage-Unit ▸Unit of λ {
    (η≤𝟘 ∙ mω≤𝟘) →
      mω≤𝟘
    , sub ▸A (begin
       γ        ≤⟨ γ≤ ⟩
       δ +ᶜ η   ≤⟨ +ᶜ-monotoneʳ η≤𝟘 ⟩
       δ +ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityʳ _ ⟩
       δ        ∎) }}
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- An inversion lemma for [_].

inv-usage-[] : γ ▸[ m ] [ t ] → ∃ λ δ → δ ▸[ m ] t × γ ≤ᶜ ω ·ᶜ δ
inv-usage-[] {γ = γ} {m = m} ▸[] =
  case inv-usage-prodˢ ▸[] of λ {
    (invUsageProdˢ {δ = δ} {η = η} ▸t ▸star γ≤) →
    δ
  , ▸-cong ᵐ·-identityʳ-ω ▸t
  , (begin
       γ            ≤⟨ γ≤ ⟩
       ω ·ᶜ δ ∧ᶜ η  ≤⟨ ∧ᶜ-decreasingˡ _ _ ⟩
       ω ·ᶜ δ       ∎) }
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- An inversion lemma for unbox.

inv-usage-unbox : γ ▸[ m ] unbox t → γ ▸[ m ] t
inv-usage-unbox ▸[] =
  case inv-usage-fst ▸[] of λ {
    (invUsageFst _ _ ▸t γ≤ _) →
  sub ▸t γ≤ }
