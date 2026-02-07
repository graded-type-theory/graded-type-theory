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
open import Graded.Usage.Weakening R

open import Definition.Untyped M
open import Graded.Derived.Unrestricted.Eta.Untyped 𝕄

open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≡_)
import Tools.Reasoning.PartialOrder

private variable
  A l t : Term _
  p     : M
  γ δ   : Conₘ _
  m     : Mode

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

opaque
  unfolding Unrestricted

  -- A usage rule for Unrestricted.

  ▸Unrestricted :
    δ ▸[ 𝟘ᵐ ] l →
    γ ▸[ m ] A →
    ω ·ᶜ γ ▸[ m ] Unrestricted l A
  ▸Unrestricted {γ} {m} ▸l ▸A = sub
    (ΠΣₘ
       (▸-cong (PE.sym ᵐ·-identityʳ-ω) ▸A)
       (sub (Liftₘ (wkUsage _ ▸l) Unitₘ) $ begin
           𝟘ᶜ ∙ ⌜ m ⌝ · ω  ≤⟨ ≤ᶜ-refl ∙ ·-monotoneʳ ω≤𝟘 ⟩
           𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
           𝟘ᶜ              ∎))
    (begin
       ω ·ᶜ γ       ≈˘⟨ +ᶜ-identityʳ _ ⟩
       ω ·ᶜ γ +ᶜ 𝟘ᶜ ∎)
    where
    open ≤ᶜ-reasoning

opaque
  unfolding [_]

  -- A usage rule for [_].

  ▸[] : γ ▸[ m ] t → ω ·ᶜ γ ▸[ m ] [ t ]
  ▸[] {γ} {m} ▸t = sub
    (prodˢₘ (▸-cong (PE.sym ᵐ·-identityʳ-ω) ▸t) (liftₘ starₘ))
    (begin
       ω ·ᶜ γ        ≤⟨ ∧ᶜ-greatest-lower-bound ≤ᶜ-refl ω·ᶜ≤ᶜ𝟘ᶜ ⟩
       ω ·ᶜ γ ∧ᶜ 𝟘ᶜ  ∎)
    where
    open ≤ᶜ-reasoning


opaque
  unfolding unbox

  -- A usage rule for unbox.

  ▸unbox : γ ▸[ m ] t → γ ▸[ m ] unbox t
  ▸unbox {m = m} ▸t = fstₘ ▸t ·ω-decreasing

------------------------------------------------------------------------
-- Inversion lemmas for usage

opaque
  unfolding Unrestricted

  -- An inversion lemma for Unrestricted.

  inv-usage-Unrestricted :
    γ ▸[ m ] Unrestricted l A →
    (∃ λ δ → δ ▸[ 𝟘ᵐ ] l) × γ ▸[ m ] A
  inv-usage-Unrestricted {γ} {m} ▸Unrestricted =
    let invUsageΠΣ {δ} {η} ▸A ▸Lift γ≤ = inv-usage-ΠΣ ▸Unrestricted
        (_ , ▸wk1-l) , ▸Unit           = inv-usage-Lift ▸Lift
    in
    case inv-usage-Unit ▸Unit of λ {
      (η≤𝟘 ∙ _) →
    (_ , wkUsage⁻¹ ▸wk1-l) ,
    (sub (▸-cong ᵐ·-identityʳ-ω ▸A) $ begin
       γ            ≤⟨ γ≤ ⟩
       ω ·ᶜ δ +ᶜ η  ≤⟨ +ᶜ-monotone ω·ᶜ-decreasing η≤𝟘 ⟩
       δ +ᶜ 𝟘ᶜ      ≈⟨ +ᶜ-identityʳ _ ⟩
       δ            ∎) }
    where
    open ≤ᶜ-reasoning

opaque
  unfolding [_]

  -- An inversion lemma for [_].

  inv-usage-[] : γ ▸[ m ] [ t ] → ∃ λ δ → δ ▸[ m ] t × γ ≤ᶜ ω ·ᶜ δ
  inv-usage-[] {γ} ▸[] =
    let invUsageProdˢ {δ} {η} ▸t ▸star γ≤ = inv-usage-prodˢ ▸[] in
    δ ,
    ▸-cong ᵐ·-identityʳ-ω ▸t ,
    (begin
       γ            ≤⟨ γ≤ ⟩
       ω ·ᶜ δ ∧ᶜ η  ≤⟨ ∧ᶜ-decreasingˡ _ _ ⟩
       ω ·ᶜ δ       ∎)
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

opaque
  unfolding unbox

  -- An inversion lemma for unbox.

  inv-usage-unbox : γ ▸[ m ] unbox t → γ ▸[ m ] t
  inv-usage-unbox ▸[] =
    let invUsageFst ▸t γ≤ _ = inv-usage-fst ▸[]
    in  sub ▸t γ≤
