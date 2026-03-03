------------------------------------------------------------------------
-- Properties related to usage and _⟶×⟨_⟩[_]_
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions

module Graded.Derived.Non-dependent
  {a a′} {M : Set a} {Mode : Set a′}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (UR : Usage-restrictions 𝕄 𝐌)
  where

open Modality 𝕄
open IsMode 𝐌

open import Definition.Untyped M
open import Definition.Untyped.Non-dependent 𝕄

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Usage UR
open import Graded.Usage.Inversion UR
open import Graded.Usage.Weakening UR

open import Tools.Function
open import Tools.Product

open ≤ᶜ-reasoning

private variable
  A B : Term _
  b   : BinderMode
  γ δ : Conₘ _
  m   : Mode
  p   : M

opaque
  unfolding _⟶×⟨_⟩[_]_

  -- A usage rule for _⟶×⟨_⟩[_]_.

  ▸⟶× :
    γ ▸[ m ᵐ· p ] A →
    δ ▸[ m ] B →
    p ·ᶜ γ +ᶜ δ ▸[ m ] A ⟶×⟨ b ⟩[ p ] B
  ▸⟶× {m} {δ} ▸A ▸B =
    ΠΣₘ ▸A $
    sub (wkUsage _ ▸B) $ begin
      δ ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
      δ ∙ 𝟘          ∎

opaque
  unfolding _⟶×⟨_⟩[_]_

  -- An inversion lemma for _⟶×⟨_⟩[_]_.

  inv-usage-⟶× :
    γ ▸[ m ] A ⟶×⟨ b ⟩[ p ] B →
    ∃₂ λ δ η →
      γ ≤ᶜ p ·ᶜ δ +ᶜ η ×
      δ ▸[ m ᵐ· p ] A ×
      η ▸[ m ] B
  inv-usage-⟶× ▸⟶× =
    let invUsageΠΣ ▸A ▸B γ≤ = inv-usage-ΠΣ ▸⟶× in
    _ , _ , γ≤ , ▸A , wkUsage⁻¹ ▸B
