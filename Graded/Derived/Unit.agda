------------------------------------------------------------------------
-- Properties related to usage and Unit
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

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

opaque
  unfolding unitrec⟨_⟩

  -- A usage rule for unitrec⟨_⟩.

  ▸unitrec⟨⟩ :
    (s ≡ 𝕨 → Unitrec-allowed m p q) →
    (s ≡ 𝕨 → γ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A) →
    (s ≡ 𝕨 → δ ▸[ m ᵐ· p ] t) →
    η ▸[ m ] u →
    (s ≡ 𝕨 → θ ≤ᶜ p ·ᶜ δ +ᶜ η) →
    (s ≡ 𝕤 → θ ≤ᶜ η) →
    θ ▸[ m ] unitrec⟨ s ⟩ p q A t u
  ▸unitrec⟨⟩ {s = 𝕨} ok ▸A ▸t ▸u hyp₁ _ =
    sub (unitrecₘ (▸t refl) ▸u (▸A refl) (ok refl)) (hyp₁ refl)
  ▸unitrec⟨⟩ {s = 𝕤} _ _ _ ▸u _ hyp₂ =
    sub ▸u (hyp₂ refl)

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
    γ ▸[ m ] Unit-η s Unit-η-grade t
  ▸Unit-η {γ} ok ▸t ≤𝟘ᶜ =
    ▸unitrec⟨⟩ ok lemma (▸-cong (sym ᵐ·-identityʳ) ∘→ ▸t) rflₘ
      (λ _ → begin
         γ             ≈˘⟨ ≈ᶜ-trans (+ᶜ-identityʳ _) $
                           ·ᶜ-identityˡ _ ⟩
         𝟙 ·ᶜ γ +ᶜ 𝟘ᶜ  ∎)
      ≤𝟘ᶜ
    where
    open ≤ᶜ-reasoning

    lemma :
      s ≡ 𝕨 →
      𝟘ᶜ {n = n} ∙ ⌜ 𝟘ᵐ? ⌝ · Unit-η-grade ▸[ 𝟘ᵐ? ]
        Id (Unit s) (star s) (var x0)
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
    ∃ λ γ → γ ▸[ m ] Unit-η s Unit-η-grade t
  ▸Unit-η′ {s = 𝕤} _  _  = 𝟘ᶜ , ▸Unit-η (λ ()) (λ ()) (λ _ → ≤ᶜ-refl)
  ▸Unit-η′ {s = 𝕨} ok ▸t = case ▸t refl of λ where
    (γ , ▸t) → γ , ▸Unit-η ok (λ _ → ▸t) (λ ())
