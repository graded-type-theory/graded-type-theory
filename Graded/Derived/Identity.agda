------------------------------------------------------------------------
-- Properties related to usage and Id
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Derived.Identity
  {a} {M : Set a}
  {𝕄 : Modality M}
  (UR : Usage-restrictions 𝕄)
  where

open Modality 𝕄
open Usage-restrictions UR

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Erased-matches
open import Graded.Usage.Properties 𝕄 UR
open import Graded.Usage.Weakening 𝕄 UR

open import Definition.Untyped M
open import Definition.Untyped.Identity 𝕄

open import Tools.Bool
open import Tools.Function
open import Tools.PropositionalEquality as PE using (_≡_)
import Tools.Reasoning.PartialOrder

private variable
  A B t u v w       : Term _
  p                 : M
  γ₁ γ₂ γ₃ γ₄ γ₅ γ₆ : Conₘ _
  m                 : Mode
  sem               : Some-erased-matches

opaque
  unfolding subst

  -- A usage rule for subst.

  ▸subst :
    γ₁ ▸[ 𝟘ᵐ? ] A →
    γ₂ ∙ ⌜ m ⌝ · p ▸[ m ] B →
    γ₃ ▸[ m ] t →
    γ₄ ▸[ m ] u →
    γ₅ ▸[ m ] v →
    γ₆ ▸[ m ] w →
    ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆) ▸[ m ] subst p A B t u v w
  ▸subst {γ₁} {γ₂} {m} {p} {γ₃} {γ₄} {γ₅} {γ₆} ▸A ▸B ▸t ▸u ▸v ▸w = sub
    (Jₘ-generalised ▸A ▸t
       (sub (wkUsage (step id) ▸B) $
        let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
          γ₂ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
          γ₂ ∙ ⌜ m ⌝ · p ∙ 𝟘          ∎)
       ▸w ▸u ▸v)
    (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)  ≈⟨ ·ᶜ-congˡ $
                                             ≈ᶜ-trans (≈ᶜ-sym $ +ᶜ-assoc _ _ _) $
                                             ≈ᶜ-trans (+ᶜ-congʳ $ +ᶜ-comm _ _) $
                                             ≈ᶜ-trans (+ᶜ-assoc _ _ _) $
                                             +ᶜ-congˡ $ +ᶜ-congˡ $
                                             ≈ᶜ-trans (≈ᶜ-sym $ +ᶜ-assoc _ _ _) $
                                             +ᶜ-comm _ _ ⟩
       ω ·ᶜ (γ₃ +ᶜ γ₂ +ᶜ γ₆ +ᶜ γ₄ +ᶜ γ₅)  ∎)

opaque
  unfolding subst

  -- A usage rule for subst 𝟘.

  ▸subst-𝟘 :
    erased-matches-for-J m ≡ not-none sem →
    γ₁ ▸[ 𝟘ᵐ? ] A →
    γ₂ ∙ 𝟘 ▸[ m ] B →
    γ₃ ▸[ 𝟘ᵐ? ] t →
    γ₄ ▸[ 𝟘ᵐ? ] u →
    γ₅ ▸[ 𝟘ᵐ? ] v →
    γ₆ ▸[ m ] w →
    ω ·ᶜ (γ₂ +ᶜ γ₆) ▸[ m ] subst 𝟘 A B t u v w
  ▸subst-𝟘 ≡not-none ▸A ▸B ▸t ▸u ▸v ▸w =
    J₀ₘ₁-generalised ≡not-none PE.refl PE.refl ▸A ▸t
      (wkUsage (step id) ▸B) ▸w ▸u ▸v
