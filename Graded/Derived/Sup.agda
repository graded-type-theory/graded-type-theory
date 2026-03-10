------------------------------------------------------------------------
-- Some properties related to usage and sup and some related terms.
------------------------------------------------------------------------

import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions

module Graded.Derived.Sup
  {ℓ ℓ′} {M : Set ℓ} {Mode : Set ℓ′}
  (open Graded.Modality M)
  {𝕄 : Modality}
  {𝐌 : IsMode Mode 𝕄}
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄 𝐌)
  where

open Type-restrictions TR

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Usage UR
open import Graded.Usage.Inversion UR

open import Definition.Untyped M
open import Definition.Untyped.Sup TR

open import Tools.Product
open import Tools.Relation

open import Tools.Function
open import Tools.Nat using (Nat; 1+)

private variable
  n k : Nat
  l l₁ l₂ : Term _
  m : Mode
  γ δ : Conₘ _

opaque

  -- A usage lemma for sucᵘᵏ

  ▸sucᵘᵏ :
    γ ▸[ m ] l →
    γ ▸[ m ] sucᵘᵏ k l
  ▸sucᵘᵏ {k = 0} ▸l = ▸l
  ▸sucᵘᵏ {k = 1+ k} ▸l = sucᵘₘ (▸sucᵘᵏ ▸l)

opaque

  -- A usage lemma for ↓ᵘ

  ▸↓ᵘ : 𝟘ᶜ {n = n} ▸[ m ] ↓ᵘ k
  ▸↓ᵘ = ▸sucᵘᵏ zeroᵘₘ

opaque
  unfolding _supᵘₗ′_

  -- A usage lemma for supᵘₗ′

  ▸supᵘₗ′ :
    γ ▸[ m ] l₁ →
    δ ▸[ m ] l₂ →
    γ +ᶜ δ ▸[ m ] l₁ supᵘₗ′ l₂
  ▸supᵘₗ′ {γ} {l₁} {δ} {l₂} ▸l₁ ▸l₂
    with Level-literal? l₁ ×-dec Level-literal? l₂
  … | no _ = supᵘₘ ▸l₁ ▸l₂
  … | yes (lit₁ , lit₂) = sub ▸↓ᵘ $ begin
    γ +ᶜ δ   ≤⟨ +ᶜ-monotone (inv-usage-level-literal lit₁ ▸l₁) (inv-usage-level-literal lit₂ ▸l₂) ⟩
    𝟘ᶜ +ᶜ 𝟘ᶜ ≈⟨ +ᶜ-identityˡ _ ⟩
    𝟘ᶜ       ∎
    where
    open ≤ᶜ-reasoning

opaque
  unfolding _supᵘₗ_

  -- A usage lemma for supᵘₗ.

  ▸supᵘₗ :
    γ ▸[ m ] l₁ →
    δ ▸[ m ] l₂ →
    γ +ᶜ δ ▸[ m ] l₁ supᵘₗ l₂
  ▸supᵘₗ ▸l₁ ▸l₂ with level-support
  … | only-literals = ▸supᵘₗ′ ▸l₁ ▸l₂
  … | level-type _  = supᵘₘ ▸l₁ ▸l₂
