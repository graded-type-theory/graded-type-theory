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

open import Tools.Nat
open import Tools.Fin
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
open import Tools.Relation

private variable
  n       : Nat
  A t u   : Term _
  γ δ η θ : Conₘ _
  p q     : M
  m       : Mode
  s       : Strength
  l       : Universe-level

opaque
  unfolding unitrec⟨_⟩

  -- A usage rule for unitrec⟨_⟩.

  ▸unitrec⟨⟩ :
    (s ≡ 𝕨 → Unitrec-allowed m p q) →
    (s ≡ 𝕨 → ∃ λ γ → γ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A) →
    (s ≡ 𝕨 → ∃ λ δ → δ ▸[ m ᵐ· p ] t × θ ≤ᶜ p ·ᶜ δ +ᶜ η) →
    (s ≡ 𝕤 → θ ≤ᶜ η) →
    η ▸[ m ] u →
    θ ▸[ m ] unitrec⟨ s ⟩ l p q A t u
  ▸unitrec⟨⟩ {s = 𝕨} ok ▸A ▸t _ ▸u =
    let _ , ▸t , θ≤pδ+η = ▸t refl in
    sub (unitrecₘ ▸t ▸u (▸A refl .proj₂) (ok refl)) θ≤pδ+η
  ▸unitrec⟨⟩ {s = 𝕤} _ _ _ θ≤η ▸u =
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
    (s ≡ 𝕨 → γ ▸[ m ] t) →
    (s ≡ 𝕤 → γ ≤ᶜ 𝟘ᶜ) →
    γ ▸[ m ] Unit-η s l Unit-η-grade t
  ▸Unit-η {γ} {l} ok ▸t ≤𝟘ᶜ =
    ▸unitrec⟨⟩ ok ((_ ,_) ∘→ lemma)
      (λ s≡𝕨 →
           γ
         , ▸-cong (sym ᵐ·-identityʳ) (▸t s≡𝕨)
         , (begin
              γ             ≈˘⟨ ≈ᶜ-trans (+ᶜ-identityʳ _) $
                                ·ᶜ-identityˡ _ ⟩
              𝟙 ·ᶜ γ +ᶜ 𝟘ᶜ  ∎))
      ≤𝟘ᶜ rflₘ
    where
    open ≤ᶜ-reasoning

    lemma :
      s ≡ 𝕨 →
      𝟘ᶜ {n = n} ∙ ⌜ 𝟘ᵐ? ⌝ · Unit-η-grade ▸[ 𝟘ᵐ? ]
        Id (Unit s l) (star s l) (var x0)
    lemma refl with Id-erased?
    … | yes erased = sub
      (Id₀ₘ erased Unitₘ starₘ var)
      (begin
         𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
         𝟘ᶜ                ∎)
    … | no not-erased = sub
      (Idₘ not-erased Unitₘ starₘ var)
      (begin
         𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟙      ≈⟨ ≈ᶜ-refl ∙ ·-identityʳ _ ⟩
         𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝          ≈˘⟨ +ᶜ-identityˡ _ ⟩
         𝟘ᶜ +ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝)  ∎)

opaque

  -- A variant of ▸Unit-η.

  ▸Unit-η′ :
    (s ≡ 𝕨 → Unitrec-allowed m 𝟙 Unit-η-grade) →
    (s ≡ 𝕨 → ∃ λ γ → γ ▸[ m ] t) →
    ∃ λ γ → γ ▸[ m ] Unit-η s l Unit-η-grade t
  ▸Unit-η′ {s = 𝕤} _  _  = 𝟘ᶜ , ▸Unit-η (λ ()) (λ ()) (λ _ → ≤ᶜ-refl)
  ▸Unit-η′ {s = 𝕨} ok ▸t = case ▸t refl of λ where
    (γ , ▸t) → γ , ▸Unit-η ok (λ _ → ▸t) (λ ())
