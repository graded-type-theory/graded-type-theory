------------------------------------------------------------------------
-- Some properties related to usage and List
------------------------------------------------------------------------

import Graded.Modality
open import Graded.Usage.Restrictions
import Definition.Untyped

module Graded.Derived.List
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (open Definition.Untyped M)
  (pₕ pₗ : M)
  (R : Usage-restrictions 𝕄)
  where

open Modality 𝕄
open Usage-restrictions R

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
import Graded.Derived.Vec 𝕨 pₕ R as V
open import Graded.Mode 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Usage 𝕄 R
open import Graded.Usage.Properties 𝕄 R
open import Graded.Usage.Weakening 𝕄 R
open import Graded.Substitution 𝕄 R
open import Graded.Substitution.Properties 𝕄 R

import Definition.Untyped.Vec 𝕄 𝕨 pₕ as UV
open import Definition.Untyped.List 𝕄 pₕ pₗ

open import Tools.Fin
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder

private variable
  l : Universe-level
  A P k t h xs nl cs : Term _
  γ δ η θ χ γ₁ γ₂ δ₁ δ₂ η₁ η₂ θ₁ θ₂ : Conₘ _
  m : Mode
  p₁ p₂ p₃ p₄ q r r₁ r₂ : M

------------------------------------------------------------------------
-- Usage rules for List

opaque
  unfolding List

  -- A usage rule for List

  ▸List :
    ⦃ no-nr : Nr-not-available-GLB ⦄ →
    γ ▸[ m ᵐ· pₕ ] A →
    Greatest-lower-boundᶜ δ (nrᵢᶜ 𝟙 𝟘ᶜ γ) →
    δ ▸[ m ] List l A
  ▸List ▸A δ-GLB =
    let ▸A′ = wkUsage (step id) ▸A
        δ-GLB′ = wk-GLBᶜ (step id) δ-GLB
        δ-GLB″ = GLBᶜ-congˡ (λ i → ≈ᶜ-refl ∙ sym (nrᵢ-𝟘 i)) δ-GLB′
    in  sub-≈ᶜ (ΠΣₘ ℕₘ (sub-≈ᶜ (V.▸Vec′ var ▸A′ δ-GLB″)
                          (≈ᶜ-sym (+ᶜ-identityˡ _) ∙ trans (·-identityʳ _) (sym (+-identityʳ _)))))
          (≈ᶜ-sym (+ᶜ-identityˡ _))

opaque
  unfolding nil

  -- A usage rule for nil

  ▸nil : 𝟘ᶜ ▸[ m ] nil l A
  ▸nil =
    sub-≈ᶜ (prodʷₘ zeroₘ V.▸nil′) $ begin
      𝟘ᶜ             ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
      pₗ ·ᶜ 𝟘ᶜ       ≈˘⟨ +ᶜ-identityʳ _ ⟩
      pₗ ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ ∎
      where
      open ≈ᶜ-reasoning

opaque
  unfolding cons

  -- A usage rule for cons

  ▸cons :
    ⦃ no-nr : Nr-not-available-GLB ⦄ →
    γ ▸[ m ᵐ· pₕ ] h →
    δ ▸[ m ] t →
    η ▸[ 𝟘ᵐ? ] A →
    Greatest-lower-boundᶜ θ (nrᵢᶜ 𝟙 𝟘ᶜ η) →
    Prodrec-allowed m 𝟙 pₗ 𝟘 →
    pₕ ·ᶜ γ +ᶜ δ ▸[ m ] cons l A h t
  ▸cons {γ} {m} {δ} ▸h ▸t ▸A θ-GLB ok =
    let ▸t′ = ▸-cong (sym ᵐ·-identityʳ) ▸t
        ▸A′ = ▸-cong (sym ᵐ·-zeroˡ) ▸A
        ▸L = sub-≈ᶜ (wkUsage (step id) (▸List ▸A′ θ-GLB))
               (≈ᶜ-refl ∙ ·-zeroʳ _)
        ▸h′ = wkUsage (step (step id)) ▸h
        ▸u = prodʷₘ (sucₘ var) (V.▸cons′ʷ refl ▸h′ var)
        open ≈ᶜ-reasoning
        ▸u′ = sub-≈ᶜ ▸u $ begin
          pₕ ·ᶜ γ ∙ ⌜ m ⌝ · 𝟙 · pₗ ∙ ⌜ m ⌝ · 𝟙  ≈⟨ ≈ᶜ-refl ∙ ·-congˡ (·-identityˡ _)
                                                 ∙ ·-identityʳ _ ⟩
          pₕ ·ᶜ γ ∙ ⌜ m ⌝ · pₗ ∙ ⌜ m ⌝          ≈˘⟨ ≈ᶜ-refl ∙ +-identityʳ _ ∙ +-identityˡ _ ⟩
          pₕ ·ᶜ γ ∙ ⌜ m ⌝ · pₗ + 𝟘 ∙ 𝟘 + ⌜ m ⌝  ≈˘⟨ +ᶜ-identityˡ _
                                                  ∙ +-cong (sym (⌜⌝-·-comm m)) (·-zeroʳ _)
                                                  ∙ +-identityˡ _ ⟩
          𝟘ᶜ +ᶜ pₕ ·ᶜ γ
           ∙ pₗ · ⌜ m ⌝ + pₕ · 𝟘
           ∙ 𝟘 + 𝟘 + ⌜ m ⌝                      ≈˘⟨ +ᶜ-cong (·ᶜ-zeroʳ _) (+ᶜ-identityʳ _)
                                                  ∙ +-cong (·⌜ᵐ·⌝ m) (+-identityʳ _)
                                                  ∙ +-cong (·-zeroʳ _) (+-congʳ (·-zeroʳ _)) ⟩
          pₗ ·ᶜ 𝟘ᶜ +ᶜ pₕ ·ᶜ γ +ᶜ 𝟘ᶜ
           ∙ pₗ · ⌜ m ᵐ· pₗ ⌝ + pₕ · 𝟘 + 𝟘
           ∙ pₗ · 𝟘 + pₕ · 𝟘 + ⌜ m ⌝            ≡⟨⟩
          pₗ ·ᶜ (𝟘ᶜ ∙ ⌜ m ᵐ· pₗ ⌝ ∙ 𝟘) +ᶜ
            pₕ ·ᶜ (γ ∙ 𝟘 ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ ⌜ m ⌝)   ∎
    in  sub-≈ᶜ (prodrecₘ ▸t′ ▸u′ ▸L ok) $ begin
      pₕ ·ᶜ γ +ᶜ δ      ≈⟨ +ᶜ-comm _ _ ⟩
      δ +ᶜ pₕ ·ᶜ γ      ≈˘⟨ +ᶜ-congʳ (·ᶜ-identityˡ _) ⟩
      𝟙 ·ᶜ δ +ᶜ pₕ ·ᶜ γ ∎

opaque
  unfolding listrec

  -- A usage rule for listrec
  --
  -- The grades can be interpreted as follows:
  -- p₁ represents the uses of the head in cs
  -- p₂ represents the uses of the tail in cs
  -- p₃ represents the uses of the recustive call in cs
  -- q represents the uses of the list in the motive P
  -- r₁ represents the total uses of the length component of the list
  -- r₂ represents the total uses of the vector component of the list
  -- r represents the total uses of the list
  -- Since a list is composed of its length and a corresponding
  -- vector, r is constrained to be compatible with both r₁ and r₂.

  ▸listrec :
    ⦃ no-nr : Nr-not-available-GLB ⦄ →
    γ₁ ▸[ m ] nl →
    γ₂ ∙ ⌜ m ⌝ · p₁ · pₕ ∙ ⌜ m ⌝ · p₂ ∙ ⌜ m ⌝ · p₃ ▸[ m ] cs →
    δ ▸[ m ] xs →
    η₁ ▸[ 𝟘ᵐ? ] A →
    η₂ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] P →
    Greatest-lower-bound r₁ (nrᵢ p₃ 𝟙 (p₂ · pₗ)) →
    Greatest-lower-bound r₂ (nrᵢ p₃ p₁ p₂) →
    Greatest-lower-boundᶜ γ (nrᵢᶜ p₃ γ₁ γ₂) →
    Greatest-lower-boundᶜ θ (nrᵢᶜ 𝟙 𝟘ᶜ η₁) →
    r · pₗ ≤ r₁ →
    r ≤ r₂ →
    Unitrec-allowed m r₂ q →
    Prodrec-allowed m r₂ pₕ q →
    Prodrec-allowed m r pₗ q →
    r ·ᶜ δ +ᶜ γ ▸[ m ] listrec l r r₂ p₂ p₃ q A P nl cs xs
  ▸listrec {m} {γ₂} {p₁} {p₂} {p₃} {η₂} {q} {r₁} {r₂} {γ} {r}
            ▸nl ▸cs ▸xs ▸A ▸P r₁-GLB r₂-GLB γ-GLB θ-GLB ≤r₁ ≤r₂ ok₁ ok₂ ok₃ =
    let ▸nl′ = wkUsage (step (step id)) ▸nl
        ▸x0 = sub-≈ᶜ var (·ᶜ-zeroʳ _ ∙ ·-identityʳ _)
        ▸x2 = sub-≈ᶜ var (·ᶜ-zeroʳ _ ∙ ·-identityʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _)
        ▸x3x1 = let open ≈ᶜ-reasoning in sub-≈ᶜ (prodʷₘ var var) $ begin
          ⌜ ⌞ ⌜ m ⌝ · p₂ ⌟ ⌝ ·ᶜ (𝟘ᶜ ∙ pₗ ∙ 𝟘 ∙ 𝟙 ∙ 𝟘)
            ≈⟨ ·ᶜ-zeroʳ _ ∙ ⌜⌝-·-comm ⌞ ⌜ m ⌝ · p₂ ⌟ ∙ ·-zeroʳ _ ∙ ·-identityʳ _ ∙ ·-zeroʳ _ ⟩
          𝟘ᶜ ∙ pₗ · ⌜ ⌞ ⌜ m ⌝ · p₂ ⌟ ⌝ ∙ 𝟘 ∙  ⌜ ⌞ ⌜ m ⌝ · p₂ ⌟ ⌝ ∙ 𝟘
            ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityʳ _ ∙ +-identityʳ _ ∙ +-identityˡ _ ∙ +-identityʳ _ ⟩
          (𝟘ᶜ , x3 ≔ pₗ · ⌜ ⌞ ⌜ m ⌝ · p₂ ⌟ ⌝) +ᶜ (𝟘ᶜ , x1 ≔ ⌜ ⌞ ⌜ m ⌝ · p₂ ⌟ ⌝)
            ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _ ∙ ·⌜ᵐ·⌝ ⌞ ⌜ m ⌝ · p₂ ⌟ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _) ⟩
          pₗ ·ᶜ (𝟘ᶜ , x3 ≔ ⌜ ⌞ ⌜ m ⌝ · p₂ ⌟ ᵐ· pₗ ⌝) +ᶜ (𝟘ᶜ , x1 ≔ ⌜ ⌞ ⌜ m ⌝ · p₂ ⌟ ⌝) ∎
        Ψ▶σ = ▶-cong _
                (λ { x0 → refl ; (x0 +1) → refl ; (x0 +2) → refl ; (x +1 +2) → refl})
                (wf-consSubstₘ (wf-consSubstₘ (wf-consSubstₘ
                  (wf-wkSubstₘ′ wf-idSubstₘ) ▸x2) ▸x3x1) ▸x0)
        ▸cs′ = let open ≈ᶜ-reasoning in sub-≈ᶜ (substₘ-lemma _ Ψ▶σ ▸cs) $ begin
          γ₂ ∙ 𝟘 ∙ 𝟘 ∙ ⌜ m ⌝ · p₂ · pₗ ∙ ⌜ m ⌝ · p₁ · pₕ ∙ ⌜ m ⌝ · p₂ ∙ ⌜ m ⌝ · p₃
            ≈˘⟨ +ᶜ-identityˡ _ ∙ +-identityʳ _ ⟩
          (𝟘ᶜ , x0 ≔ ⌜ m ⌝ · p₃) +ᶜ
          (γ₂ ∙ 𝟘 ∙ 𝟘 ∙ ⌜ m ⌝ · p₂ · pₗ ∙ ⌜ m ⌝ · p₁ · pₕ ∙ ⌜ m ⌝ · p₂ ∙ 𝟘)
            ≈˘⟨ +ᶜ-congˡ (+ᶜ-identityˡ _ ∙ +-identityʳ _ ∙ +-identityˡ _ ∙ +-identityʳ _ ∙ +-identityˡ _) ⟩
          (𝟘ᶜ , x0 ≔ ⌜ m ⌝ · p₃)                        +ᶜ
          (𝟘ᶜ , x3 ≔ ⌜ m ⌝ · p₂ · pₗ , x1 ≔ ⌜ m ⌝ · p₂) +ᶜ
          (γ₂ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ ⌜ m ⌝ · p₁ · pₕ ∙ 𝟘 ∙ 𝟘)
            ≈˘⟨ +ᶜ-congˡ (+ᶜ-congˡ (+ᶜ-identityˡ _ ∙ +-identityʳ _ ∙ +-identityˡ _ ∙ +-identityˡ _)) ⟩
          (𝟘ᶜ , x0 ≔ ⌜ m ⌝ · p₃)                        +ᶜ
          (𝟘ᶜ , x3 ≔ ⌜ m ⌝ · p₂ · pₗ , x1 ≔ ⌜ m ⌝ · p₂) +ᶜ
          (𝟘ᶜ , x2 ≔ ⌜ m ⌝ · p₁ · pₕ)                   +ᶜ
          (γ₂ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟘)
            ≈˘⟨ +ᶜ-cong (update-cong {x = x0} (·ᶜ-zeroʳ _) (·-identityʳ _))
                (+ᶜ-cong (update-cong {x = x3} (update-cong {x = x1} (·ᶜ-zeroʳ _) (·-identityʳ _)) (·-assoc _ _ _))
                (+ᶜ-congʳ (update-cong {x = x2} (·ᶜ-zeroʳ _) (·-identityʳ _)))) ⟩
          ((⌜ m ⌝ · p₃) ·ᶜ 𝟘ᶜ , x0 ≔ (⌜ m ⌝ · p₃) · 𝟙)                          +ᶜ
          ((⌜ m ⌝ · p₂) ·ᶜ 𝟘ᶜ , x3 ≔ (⌜ m ⌝ · p₂) · pₗ , x1 ≔ (⌜ m ⌝ · p₂) · 𝟙) +ᶜ
          ((⌜ m ⌝ · p₁ · pₕ) ·ᶜ 𝟘ᶜ , x2 ≔ (⌜ m ⌝ · p₁ · pₕ) · 𝟙)                +ᶜ
          (γ₂ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟘)
            ≈˘⟨ +ᶜ-congˡ (+ᶜ-congˡ (+ᶜ-congˡ (≈ᶜ-trans (<*-wkSubstₘ′ {k = 6} γ₂)
                (<*-identityˡ _ ∙ refl ∙ refl ∙ refl ∙ refl ∙ refl ∙ refl)))) ⟩
          (⌜ m ⌝ · p₃) ·ᶜ (𝟘ᶜ , x0 ≔ 𝟙)             +ᶜ
          (⌜ m ⌝ · p₂) ·ᶜ ((𝟘ᶜ , x3 ≔ pₗ) , x1 ≔ 𝟙) +ᶜ
          (⌜ m ⌝ · p₁ · pₕ) ·ᶜ (𝟘ᶜ , x2 ≔ 𝟙)        +ᶜ
          γ₂ <* wkSubstₘ′ 6 idSubstₘ                ∎
        ▸A′ = wkUsage (step (step id)) ▸A
        ▸x1x0 = let open ≈ᶜ-reasoning in sub-≈ᶜ (prodʷₘ var var) $ begin
          ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ⌝ ·ᶜ (𝟘ᶜ ∙ pₗ ∙ 𝟙)
            ≈⟨ ·ᶜ-zeroʳ _ ∙ ⌜⌝-·-comm ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ∙ ·-identityʳ _ ⟩
          𝟘ᶜ ∙ pₗ · ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ⌝ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ⌝
            ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityʳ _ ∙ +-identityˡ _ ⟩
          (𝟘ᶜ ∙ pₗ · ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ⌝ ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ⌝)
            ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _ ∙ ·⌜ᵐ·⌝ ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ∙ ·-zeroʳ _) ⟩
          pₗ ·ᶜ (𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ᵐ· pₗ ⌝ ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ⌝) ∎
        Ψ▶σ′ = ▶-cong _
                 (λ { x0 → refl ; (x +1) → refl})
                 (wf-consSubstₘ (wf-wkSubstₘ′ wf-idSubstₘ) ▸x1x0)
        ▸P₊ = let open ≈ᶜ-reasoning in sub-≈ᶜ (substₘ-lemma _ Ψ▶σ′ ▸P) $ begin
          η₂ ∙ 𝟘 ∙ 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ · q · pₗ ∙ ⌜ 𝟘ᵐ? ⌝ · q                     ≈˘⟨ +ᶜ-identityˡ _ ∙ +-identityʳ _ ∙ +-identityʳ _ ⟩
          (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · q · pₗ ∙ ⌜ 𝟘ᵐ? ⌝ · q) +ᶜ (η₂ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟘)  ≈˘⟨ +ᶜ-cong (·ᶜ-zeroʳ _ ∙ ·-assoc _ _ _ ∙ ·-identityʳ _)
                                                                            (≈ᶜ-trans (<*-wkSubstₘ′ {k = 4} η₂)
                                                                              (<*-identityˡ _ ∙ refl ∙ refl ∙ refl ∙ refl)) ⟩
          (⌜ 𝟘ᵐ? ⌝ · q) ·ᶜ (𝟘ᶜ ∙ pₗ ∙ 𝟙) +ᶜ (η₂ <* wkSubstₘ′ 4 idSubstₘ)  ∎
        γ-GLB′ = GLBᶜ-congˡ ((λ i → ≈ᶜ-refl ∙ sym (nrᵢ-𝟘 i) ∙ sym (nrᵢ-𝟘 i)))
                   (wk-GLBᶜ (step (step id)) γ-GLB)
        θ-GLB′ = GLBᶜ-congˡ ((λ i → ≈ᶜ-refl ∙ sym (nrᵢ-𝟘 i) ∙ sym (nrᵢ-𝟘 i)))
                   (wk-GLBᶜ (step (step id)) θ-GLB)
        ▸vr = let open ≤ᶜ-reasoning in sub
          (V.▸vecrec′ ▸nl′ ▸cs′ var var ▸A′ ▸P₊ r₁-GLB r₂-GLB γ-GLB′ θ-GLB′ ok₁ ok₂) $ begin
          γ ∙ ⌜ m ⌝ · r · pₗ ∙ ⌜ m ⌝ · r
            ≤⟨ ≤ᶜ-refl ∙ ·-monotoneʳ ≤r₁ ∙ ·-monotoneʳ ≤r₂ ⟩
          γ ∙ ⌜ m ⌝ · r₁ ∙ ⌜ m ⌝ · r₂
            ≈⟨ ≈ᶜ-refl ∙ ⌜⌝-·-comm m ∙ ⌜⌝-·-comm m ⟩
          γ ∙ r₁ · ⌜ m ⌝ ∙ r₂ · ⌜ m ⌝
            ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityˡ _ ∙ +-identityˡ _ ⟩
          (γ ∙ 𝟘 ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ r₁ · ⌜ m ⌝ ∙ r₂ · ⌜ m ⌝)
            ≈˘⟨ +ᶜ-congˡ (+ᶜ-identityˡ _ ∙ +-identityʳ _ ∙ +-identityˡ _) ⟩
          (γ ∙ 𝟘 ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ r₁ · ⌜ m ⌝ ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ r₂ · ⌜ m ⌝)
            ≈˘⟨ +ᶜ-congˡ (+ᶜ-cong (·ᶜ-zeroʳ _ ∙ refl ∙ ·-zeroʳ _) (·ᶜ-zeroʳ _ ∙ ·⌜ᵐ·⌝ m)) ⟩
          (γ ∙ 𝟘 ∙ 𝟘) +ᶜ r₁ ·ᶜ (𝟘ᶜ ∙ ⌜ m ⌝ ∙ 𝟘) +ᶜ r₂ ·ᶜ (𝟘ᶜ ∙ ⌜ m ᵐ· r₂ ⌝) ∎
        ▸xs′ = let open Tools.Reasoning.PartialOrder ≤-poset
               in  ▸-cong (sym (≢𝟘→ᵐ·≡′ λ ok r≡𝟘 →
                     𝟘≰𝟙 ⦃ 𝟘-well-behaved ok ⦄ $ begin
                       𝟘      ≈˘⟨ ·-zeroˡ _ ⟩
                       𝟘 · pₗ ≈˘⟨ ·-congʳ r≡𝟘 ⟩
                       r · pₗ ≤⟨ ≤r₁ ⟩
                       r₁     ≤⟨ r₁-GLB .proj₁ 0 ⟩
                       𝟙 ∎))
                     ▸xs
    in  prodrecₘ ▸xs′ ▸vr ▸P ok₃
