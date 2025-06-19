------------------------------------------------------------------------
-- Properties related to usage and Unit
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Derived.Unit
  {a} {M : Set a}
  {𝕄 : Modality M}
  (UR : Usage-restrictions 𝕄)
  where

open Modality 𝕄
open Usage-restrictions UR

open import Definition.Untyped M
open import Definition.Untyped.Unit 𝕄

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Mode 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Properties 𝕄 UR
open import Graded.Usage.Weakening 𝕄 UR

open import Tools.Nat
open import Tools.Fin
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
open import Tools.Relation

private variable
  n       : Nat
  A t u v : Term _
  γ δ η θ : Conₘ _
  p q     : M
  m       : Mode
  s       : Strength

opaque
  unfolding unitrec⟨_⟩

  -- A usage rule for unitrec⟨_⟩.

  ▸unitrec⟨⟩ :
    (s ≡ 𝕨 → Unitrec-allowed m p q) →
    (s ≡ 𝕨 → ∃ λ γ → γ ▸[ 𝟘ᵐ? ] t) →
    (s ≡ 𝕨 → ∃ λ γ → γ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A) →
    (s ≡ 𝕨 → ∃ λ δ → δ ▸[ m ᵐ· p ] u × θ ≤ᶜ p ·ᶜ δ +ᶜ η) →
    (s ≡ 𝕤 → θ ≤ᶜ η) →
    η ▸[ m ] v →
    θ ▸[ m ] unitrec⟨ s ⟩ p q t A u v
  ▸unitrec⟨⟩ {s = 𝕨} ok ▸t ▸A ▸u _ ▸v =
    let _ , ▸u , θ≤pδ+η = ▸u refl in
    sub (unitrecₘ (▸t refl .proj₂) (▸A refl .proj₂) ▸u ▸v (ok refl))
      θ≤pδ+η
  ▸unitrec⟨⟩ {s = 𝕤} _ _ _ _ θ≤η ▸u =
    sub ▸u (θ≤η refl)

opaque

  -- A grade used to state ▸Unit-η.

  Unit-η-grade : M
  Unit-η-grade = case Id-erased? of λ where
    (yes _) → 𝟘
    (no _)  → 𝟙

opaque
  unfolding Unit-η Unit-η-grade

  -- A usage rule for Unit-η.

  ▸Unit-η :
    (s ≡ 𝕨 → Unitrec-allowed m 𝟙 Unit-η-grade) →
    (s ≡ 𝕨 → ∃ λ γ → γ ▸[ 𝟘ᵐ? ] t) →
    (s ≡ 𝕨 → γ ▸[ m ] u) →
    (s ≡ 𝕤 → γ ≤ᶜ 𝟘ᶜ) →
    γ ▸[ m ] Unit-η s Unit-η-grade t u
  ▸Unit-η {s} {t} {γ} ok ▸t ▸u ≤𝟘ᶜ =
    ▸unitrec⟨⟩ ok ▸t (λ s≡𝕨 → 𝟘ᶜ , lemma s≡𝕨)
      (λ s≡𝕨 →
           γ
         , ▸-cong (sym ᵐ·-identityʳ) (▸u s≡𝕨)
         , (begin
              γ             ≈˘⟨ ≈ᶜ-trans (+ᶜ-identityʳ _) $
                                ·ᶜ-identityˡ _ ⟩
              𝟙 ·ᶜ γ +ᶜ 𝟘ᶜ  ∎))
      ≤𝟘ᶜ rflₘ
    where
    open ≤ᶜ-reasoning

    ▸wk1-t : s ≡ 𝕨 → ∃ λ δ → δ ▸[ 𝟘ᵐ? ] wk1 t
    ▸wk1-t s≡𝕨 = _ , wkUsage (step id) (▸t s≡𝕨 .proj₂)

    lemma :
      s ≡ 𝕨 →
      𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · Unit-η-grade ▸[ 𝟘ᵐ? ]
        Id (Unit s (wk1 t)) (star s (wk1 t)) (var x0)
    lemma refl with Id-erased?
    … | yes erased = sub
      (Id₀ₘ erased (Unitₘ (▸wk1-t refl .proj₂))
         (starₘ (▸wk1-t refl .proj₂)) var)
      (begin
         𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
         𝟘ᶜ                ∎)
    … | no not-erased = sub
      (Idₘ not-erased (Unitₘ (▸wk1-t refl .proj₂))
         (starₘ (▸wk1-t refl .proj₂)) var)
      (begin
         𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟙      ≈⟨ ≈ᶜ-refl ∙ ·-identityʳ _ ⟩
         𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝          ≈˘⟨ +ᶜ-identityˡ _ ⟩
         𝟘ᶜ +ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝)  ∎)

opaque

  -- A variant of ▸Unit-η.

  ▸Unit-η′ :
    (s ≡ 𝕨 → Unitrec-allowed m 𝟙 Unit-η-grade) →
    (s ≡ 𝕨 → ∃ λ γ → γ ▸[ 𝟘ᵐ? ] t) →
    (s ≡ 𝕨 → ∃ λ γ → γ ▸[ m ] u) →
    ∃ λ γ → γ ▸[ m ] Unit-η s Unit-η-grade t u
  ▸Unit-η′ {s = 𝕤} _ _ _ =
    𝟘ᶜ , ▸Unit-η (λ ()) (λ ()) (λ ()) (λ _ → ≤ᶜ-refl)
  ▸Unit-η′ {s = 𝕨} ok ▸t ▸u = case ▸u refl of λ where
    (γ , ▸u) → γ , ▸Unit-η ok ▸t (λ _ → ▸u) (λ ())
