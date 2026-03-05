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
  n n₁ n₂ : Nat
  t t₁ t₂ : Term[ _ ] _
  k : Term-kind
  m : Mode
  γ δ : Conₘ _

opaque

  -- A usage lemma for 1ᵘ+.

  ▸1ᵘ+ :
    {t : Term[ k ] n} →
    γ ▸[ m ] t → γ ▸[ m ] 1ᵘ+ t
  ▸1ᵘ+ {k = tm}                ▸t = sucᵘₘ ▸t
  ▸1ᵘ+ {k = lvl} {t = ωᵘ+ m}   ▸t = sub ωᵘ+ (inv-usage-ωᵘ+ ▸t)
  ▸1ᵘ+ {k = lvl} {t = level t} ▸t = level (sucᵘₘ (inv-usage-level ▸t))

opaque

  -- A usage lemma for 1ᵘ+ⁿ.

  ▸1ᵘ+ⁿ : ∀ n → γ ▸[ m ] t → γ ▸[ m ] 1ᵘ+ⁿ n t
  ▸1ᵘ+ⁿ 0      ▸t = ▸t
  ▸1ᵘ+ⁿ (1+ n) ▸t = ▸1ᵘ+ (▸1ᵘ+ⁿ n ▸t)

opaque
  unfolding ↓ᵘ_

  -- A usage lemma for ↓ᵘ

  ▸↓ᵘ : 𝟘ᶜ {n = n₁} ▸[ m ] ↓ᵘ n₂
  ▸↓ᵘ {n₂} = ▸1ᵘ+ⁿ n₂ zeroᵘₘ

opaque
  unfolding _supᵘₗ′_

  -- A usage lemma for supᵘₗ′

  ▸supᵘₗ′ :
    γ ▸[ m ] t₁ →
    δ ▸[ m ] t₂ →
    γ +ᶜ δ ▸[ m ] t₁ supᵘₗ′ t₂
  ▸supᵘₗ′ {γ} {t₁} {δ} {t₂} ▸t₁ ▸t₂
    with Level-literal? t₁ ×-dec Level-literal? t₂
  … | no _ = supᵘₘ ▸t₁ ▸t₂
  … | yes (lit₁ , lit₂) = sub ▸↓ᵘ $ begin
    γ +ᶜ δ   ≤⟨ +ᶜ-monotone (inv-usage-level-literal lit₁ ▸t₁) (inv-usage-level-literal lit₂ ▸t₂) ⟩
    𝟘ᶜ +ᶜ 𝟘ᶜ ≈⟨ +ᶜ-identityˡ _ ⟩
    𝟘ᶜ       ∎
    where
    open ≤ᶜ-reasoning

opaque
  unfolding _supᵘₗ_

  -- A usage lemma for _supᵘₗ_.

  ▸supᵘₗ-tm :
    {t₁ t₂ : Term n} →
    γ ▸[ m ] t₁ →
    δ ▸[ m ] t₂ →
    γ +ᶜ δ ▸[ m ] t₁ supᵘₗ t₂
  ▸supᵘₗ-tm ▸t₁ ▸t₂ with level-support
  … | only-literals = ▸supᵘₗ′ ▸t₁ ▸t₂
  … | level-type _  = supᵘₘ ▸t₁ ▸t₂

opaque
  unfolding _supᵘₗ_

  -- A usage lemma for supᵘₗ.

  ▸supᵘₗ :
    {t₁ t₂ : Term[ k ] n} →
    γ ▸[ m ] t₁ →
    δ ▸[ m ] t₂ →
    ∃ λ θ → θ ▸[ m ] t₁ supᵘₗ t₂
  ▸supᵘₗ {k = tm} ▸t₁ ▸t₂ =
    _ , ▸supᵘₗ-tm ▸t₁ ▸t₂
  ▸supᵘₗ {t₁ = ωᵘ+ _} {t₂ = ωᵘ+ _} _ _ =
    _ , ωᵘ+
  ▸supᵘₗ {t₁ = ωᵘ+ _} {t₂ = level _} _ _ =
    _ , ωᵘ+
  ▸supᵘₗ {t₁ = level _} {t₂ = ωᵘ+ _} _ _ =
    _ , ωᵘ+
  ▸supᵘₗ {t₁ = level _} {t₂ = level _} ▸t₁ ▸t₂ =
    let ▸t₁ = inv-usage-level ▸t₁
        ▸t₂ = inv-usage-level ▸t₂
    in
    _ , level (▸supᵘₗ-tm ▸t₁ ▸t₂)
