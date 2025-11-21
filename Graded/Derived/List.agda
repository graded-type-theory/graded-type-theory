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
open import Graded.Usage.Inversion 𝕄 R
open import Graded.Usage.Properties 𝕄 R
open import Graded.Usage.Weakening 𝕄 R
open import Graded.Substitution 𝕄 R
open import Graded.Substitution.Properties 𝕄 R

import Definition.Untyped.Vec 𝕄 𝕨 pₕ as UV
open import Definition.Untyped.List 𝕄 pₕ pₗ
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

private variable
  A P k l t h xs nl cs : Term _
  γ δ η θ χ γ₁ γ₂ γ₃ γ₄ γ₅ δ₁ δ₂ η₁ η₂ η₃ θ₁ θ₂ : Conₘ _
  m : Mode
  p₁ p₂ p₃ p₄ q r r₁ r₂ : M

------------------------------------------------------------------------
-- Usage rules for List

opaque
  unfolding List

  -- A usage rule for List

  ▸List :
    ⦃ no-nr : Nr-not-available-GLB ⦄ →
    γ ▸[ 𝟘ᵐ? ] l →
    δ ▸[ m ᵐ· pₕ ] A →
    Greatest-lower-boundᶜ η (nrᵢᶜ 𝟙 𝟘ᶜ δ) →
    η ▸[ m ] List l A
  ▸List ▸l ▸A η-GLB =
    let ▸A′ = wkUsage (step id) ▸A
        η-GLB′ = wk-GLBᶜ (step id) η-GLB
        η-GLB″ = GLBᶜ-congˡ (λ i → ≈ᶜ-refl ∙ sym (nrᵢ-𝟘 i)) η-GLB′
    in
    sub-≈ᶜ
      (ΠΣₘ (Liftₘ ▸l ℕₘ) $
       sub-≈ᶜ (V.▸Vec′ (wkUsage _ ▸l) ▸A′ (lowerₘ var) η-GLB″) $
       ≈ᶜ-sym (+ᶜ-identityˡ _) ∙
       trans (·-identityʳ _) (sym (+-identityʳ _)))
      (≈ᶜ-sym (+ᶜ-identityˡ _))

opaque
  unfolding nil

  -- A usage rule for nil

  ▸nil : 𝟘ᶜ ▸[ m ] nil A
  ▸nil =
    sub-≈ᶜ (prodʷₘ (liftₘ zeroₘ) V.▸nil′) $ begin
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
    γ₁ ▸[ 𝟘ᵐ? ] l →
    γ₂ ▸[ 𝟘ᵐ? ] A →
    γ₃ ▸[ m ᵐ· pₕ ] h →
    γ₄ ▸[ m ] t →
    Greatest-lower-boundᶜ γ₅ (nrᵢᶜ 𝟙 𝟘ᶜ γ₂) →
    Prodrec-allowed m 𝟙 pₗ 𝟘 →
    pₕ ·ᶜ γ₃ +ᶜ γ₄ ▸[ m ] cons l A h t
  ▸cons {γ₃} {m} {γ₄} ▸l ▸A ▸h ▸t γ₅-GLB ok =
    let ▸t′ = ▸-cong (sym ᵐ·-identityʳ) ▸t
        ▸A′ = ▸-cong (sym ᵐ·-zeroˡ) ▸A
        ▸L = sub-≈ᶜ (wkUsage (step id) (▸List ▸l ▸A′ γ₅-GLB))
               (≈ᶜ-refl ∙ ·-zeroʳ _)
        ▸h′ = wkUsage (step (step id)) ▸h
        ▸u = prodʷₘ (liftₘ (sucₘ (lowerₘ var))) (V.▸cons′ʷ refl ▸h′ var)
        open ≈ᶜ-reasoning
        ▸u′ = sub-≈ᶜ ▸u $ begin
          pₕ ·ᶜ γ₃ ∙ ⌜ m ⌝ · 𝟙 · pₗ ∙ ⌜ m ⌝ · 𝟙                         ≈⟨ ≈ᶜ-refl ∙ ·-congˡ (·-identityˡ _) ∙ ·-identityʳ _ ⟩
          pₕ ·ᶜ γ₃ ∙ ⌜ m ⌝ · pₗ ∙ ⌜ m ⌝                                 ≈˘⟨ ≈ᶜ-refl ∙ +-identityʳ _ ∙ +-identityˡ _ ⟩
          pₕ ·ᶜ γ₃ ∙ ⌜ m ⌝ · pₗ + 𝟘 ∙ 𝟘 + ⌜ m ⌝                         ≈˘⟨ +ᶜ-identityˡ _ ∙ +-cong (sym (⌜⌝-·-comm m)) (·-zeroʳ _) ∙ +-identityˡ _ ⟩
          𝟘ᶜ +ᶜ pₕ ·ᶜ γ₃ ∙ pₗ · ⌜ m ⌝ + pₕ · 𝟘 ∙ 𝟘 + 𝟘 + ⌜ m ⌝          ≈˘⟨ +ᶜ-cong (·ᶜ-zeroʳ _) (+ᶜ-identityʳ _) ∙
                                                                            +-cong (·⌜ᵐ·⌝ m) (+-identityʳ _) ∙
                                                                            +-cong (·-zeroʳ _) (+-congʳ (·-zeroʳ _)) ⟩
          pₗ ·ᶜ 𝟘ᶜ +ᶜ pₕ ·ᶜ γ₃ +ᶜ 𝟘ᶜ ∙ pₗ · ⌜ m ᵐ· pₗ ⌝ + pₕ · 𝟘 + 𝟘 ∙
          pₗ · 𝟘 + pₕ · 𝟘 + ⌜ m ⌝                                       ≡⟨⟩

          pₗ ·ᶜ (𝟘ᶜ ∙ ⌜ m ᵐ· pₗ ⌝ ∙ 𝟘) +ᶜ
          pₕ ·ᶜ (γ₃ ∙ 𝟘 ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ ⌜ m ⌝)                            ∎
    in
    sub-≈ᶜ (prodrecₘ ▸t′ ▸u′ ▸L ok) $ begin
      pₕ ·ᶜ γ₃ +ᶜ γ₄       ≈⟨ +ᶜ-comm _ _ ⟩
      γ₄ +ᶜ pₕ ·ᶜ γ₃       ≈˘⟨ +ᶜ-congʳ (·ᶜ-identityˡ _) ⟩
      𝟙 ·ᶜ γ₄ +ᶜ pₕ ·ᶜ γ₃  ∎

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
    η₁ ▸[ 𝟘ᵐ? ] l →
    η₂ ▸[ 𝟘ᵐ? ] A →
    η₃ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] P →
    Greatest-lower-bound r₁ (nrᵢ p₃ 𝟙 (p₂ · pₗ)) →
    Greatest-lower-bound r₂ (nrᵢ p₃ p₁ p₂) →
    Greatest-lower-boundᶜ γ (nrᵢᶜ p₃ γ₁ γ₂) →
    Greatest-lower-boundᶜ θ (nrᵢᶜ 𝟙 𝟘ᶜ η₂) →
    r · pₗ ≤ r₁ →
    r ≤ r₂ →
    Unitrec-allowed m r₂ q →
    Prodrec-allowed m r₂ pₕ q →
    Prodrec-allowed m r pₗ q →
    r ·ᶜ δ +ᶜ γ ▸[ m ] listrec r r₂ p₂ p₃ q l A P nl cs xs
  ▸listrec {m} {γ₂} {p₁} {p₂} {p₃} {η₃} {q} {r₁} {r₂} {γ} {r}
            ▸nl ▸cs ▸xs ▸l ▸A ▸P r₁-GLB r₂-GLB γ-GLB θ-GLB ≤r₁ ≤r₂ ok₁ ok₂ ok₃ =
    let ▸nl′ = wkUsage (step (step id)) ▸nl
        ▸x0 = sub-≈ᶜ var (·ᶜ-zeroʳ _ ∙ ·-identityʳ _)
        ▸x2 = sub-≈ᶜ var (·ᶜ-zeroʳ _ ∙ ·-identityʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _)
        ▸x3x1 =
          let open ≈ᶜ-reasoning in
          sub-≈ᶜ (prodʷₘ (liftₘ var) var) $ begin
            ⌜ ⌞ ⌜ m ⌝ · p₂ ⌟ ⌝ ·ᶜ (𝟘ᶜ ∙ pₗ ∙ 𝟘 ∙ 𝟙 ∙ 𝟘)                 ≈⟨ ·ᶜ-zeroʳ _ ∙ ⌜⌝-·-comm ⌞ ⌜ m ⌝ · p₂ ⌟ ∙ ·-zeroʳ _ ∙ ·-identityʳ _ ∙
                                                                           ·-zeroʳ _ ⟩

            𝟘ᶜ ∙ pₗ · ⌜ ⌞ ⌜ m ⌝ · p₂ ⌟ ⌝ ∙ 𝟘 ∙  ⌜ ⌞ ⌜ m ⌝ · p₂ ⌟ ⌝ ∙ 𝟘  ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityʳ _ ∙ +-identityʳ _ ∙ +-identityˡ _ ∙
                                                                            +-identityʳ _ ⟩
            (𝟘ᶜ , x3 ≔ pₗ · ⌜ ⌞ ⌜ m ⌝ · p₂ ⌟ ⌝) +ᶜ
            (𝟘ᶜ , x1 ≔ ⌜ ⌞ ⌜ m ⌝ · p₂ ⌟ ⌝)                              ≈˘⟨ +ᶜ-congʳ
                                                                              (·ᶜ-zeroʳ _ ∙ ·⌜ᵐ·⌝ ⌞ ⌜ m ⌝ · p₂ ⌟ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙
                                                                               ·-zeroʳ _) ⟩
            pₗ ·ᶜ (𝟘ᶜ , x3 ≔ ⌜ ⌞ ⌜ m ⌝ · p₂ ⌟ ᵐ· pₗ ⌝) +ᶜ
            (𝟘ᶜ , x1 ≔ ⌜ ⌞ ⌜ m ⌝ · p₂ ⌟ ⌝)                              ∎
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
        ▸x1x0 =
          let open ≈ᶜ-reasoning in
          sub-≈ᶜ (prodʷₘ (liftₘ var) var) $ begin
            ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ⌝ ·ᶜ (𝟘ᶜ ∙ pₗ ∙ 𝟙)                 ≈⟨ ·ᶜ-zeroʳ _ ∙ ⌜⌝-·-comm ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ∙ ·-identityʳ _ ⟩

            𝟘ᶜ ∙ pₗ · ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ⌝ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ⌝  ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityʳ _ ∙ +-identityˡ _ ⟩

            (𝟘ᶜ ∙ pₗ · ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ⌝ ∙ 𝟘) +ᶜ
            (𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ⌝)                           ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _ ∙ ·⌜ᵐ·⌝ ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ∙ ·-zeroʳ _) ⟩

            pₗ ·ᶜ (𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ᵐ· pₗ ⌝ ∙ 𝟘) +ᶜ
            (𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ⌝)                           ∎
        Ψ▶σ′ = ▶-cong _
                 (λ { x0 → refl ; (x +1) → refl})
                 (wf-consSubstₘ (wf-wkSubstₘ′ wf-idSubstₘ) ▸x1x0)
        ▸P₊ = let open ≈ᶜ-reasoning in sub-≈ᶜ (substₘ-lemma _ Ψ▶σ′ ▸P) $ begin
          η₃ ∙ 𝟘 ∙ 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ · q · pₗ ∙ ⌜ 𝟘ᵐ? ⌝ · q                     ≈˘⟨ +ᶜ-identityˡ _ ∙ +-identityʳ _ ∙ +-identityʳ _ ⟩
          (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · q · pₗ ∙ ⌜ 𝟘ᵐ? ⌝ · q) +ᶜ (η₃ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟘)   ≈˘⟨ +ᶜ-cong (·ᶜ-zeroʳ _ ∙ ·-assoc _ _ _ ∙ ·-identityʳ _) $
                                                                              ≈ᶜ-trans (<*-wkSubstₘ′ {k = 4} η₃)
                                                                                (<*-identityˡ _ ∙ refl ∙ refl ∙ refl ∙ refl) ⟩
          (⌜ 𝟘ᵐ? ⌝ · q) ·ᶜ (𝟘ᶜ ∙ pₗ ∙ 𝟙) +ᶜ (η₃ <* wkSubstₘ′ 4 idSubstₘ)  ∎
        γ-GLB′ = GLBᶜ-congˡ ((λ i → ≈ᶜ-refl ∙ sym (nrᵢ-𝟘 i) ∙ sym (nrᵢ-𝟘 i)))
                   (wk-GLBᶜ (step (step id)) γ-GLB)
        θ-GLB′ = GLBᶜ-congˡ ((λ i → ≈ᶜ-refl ∙ sym (nrᵢ-𝟘 i) ∙ sym (nrᵢ-𝟘 i)))
                   (wk-GLBᶜ (step (step id)) θ-GLB)
        ▸vr = let open ≤ᶜ-reasoning in sub
          (V.▸vecrec′ ▸nl′ ▸cs′ (lowerₘ var) var (wkUsage _ ▸l) ▸A′ ▸P₊
             r₁-GLB r₂-GLB γ-GLB′ θ-GLB′ ok₁ ok₂) $ begin
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

------------------------------------------------------------------------
-- Inversion lemmas for usage

opaque
  unfolding List

  -- A usage inversion lemma for List

  inv-usage-List :
    ⦃ no-nr : Nr-not-available-GLB ⦄ →
    γ ▸[ m ] List l A →
    ∃₅ λ η₁ η₂ γ₃ γ₄ γ₅ →
    η₁ ▸[ 𝟘ᵐ? ] l ×
    η₂ ▸[ m ᵐ· pₕ ] A ×
    Greatest-lower-boundᶜ γ₃ (nrᵢᶜ 𝟙 γ₄ γ₅) ×
    γ ≤ᶜ γ₃ ×
    γ₄ ≤ᶜ 𝟘ᶜ ×
    γ₅ ≤ᶜ η₂
  inv-usage-List {γ} ▸L =
    let invUsageΠΣ {δ = γ₁} {η = γ₂} ▸Lift-ℕ ▸V γ≤ = inv-usage-ΠΣ ▸L
        _ , η , δ , θ , δ′ , η′ ,
          ▸l , ▸A , ▸x0 , θ-GLB , γ₂≤ , δ′≤𝟘 , η′≤η =
          V.inv-usage-Vec′ ▸V
        open ≤ᶜ-reasoning
    in  _ , _ , _ , tailₘ δ′ , tailₘ η′ , wkUsage⁻¹ ▸l , wkUsage⁻¹ ▸A
          , GLBᶜ-congˡ (nrᵢᶜ-tailₘ {γ = δ′} {δ = η′})
              (GLBᶜ-pointwise θ-GLB .proj₁)
          , (begin
               γ                     ≤⟨ γ≤ ⟩
               γ₁ +ᶜ γ₂              ≤⟨ +ᶜ-monotone (inv-usage-ℕ (inv-usage-Lift ▸Lift-ℕ .proj₂)) (tailₘ-monotone γ₂≤) ⟩
               𝟘ᶜ +ᶜ tailₘ (δ +ᶜ θ)  ≈⟨ +ᶜ-identityˡ _ ⟩
               tailₘ (δ +ᶜ θ)        ≈⟨ tailₘ-distrib-+ᶜ δ θ ⟩
               tailₘ δ +ᶜ tailₘ θ    ≤⟨ +ᶜ-monotoneˡ (tailₘ-monotone (inv-usage-var (inv-usage-lower ▸x0))) ⟩
               𝟘ᶜ +ᶜ tailₘ θ         ≈⟨ +ᶜ-identityˡ _ ⟩
               tailₘ θ               ∎)
          , tailₘ-monotone δ′≤𝟘
          , (begin
              tailₘ η′             ≤⟨ tailₘ-monotone η′≤η ⟩
              tailₘ η              ≈˘⟨ wkConₘ⁻¹-step η ⟩
              wkConₘ⁻¹ (step id) η ∎)

opaque
  unfolding nil

  -- A usage inversion lemma for nil

  inv-usage-nil : γ ▸[ m ] nil A → γ ≤ᶜ 𝟘ᶜ
  inv-usage-nil {γ} ▸nil =
    let invUsageProdʷ {δ} {η} ▸lift-zero ▸nil′ γ≤ = inv-usage-prodʷ ▸nil
        open ≤ᶜ-reasoning
    in  begin
      γ              ≤⟨ γ≤ ⟩
      pₗ ·ᶜ δ +ᶜ η   ≤⟨ +ᶜ-monotone (·ᶜ-monotoneʳ (inv-usage-zero (inv-usage-lift ▸lift-zero))) (V.inv-usage-nil′ʷ refl ▸nil′) ⟩
      pₗ ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ ≈⟨ +ᶜ-identityʳ _ ⟩
      pₗ ·ᶜ 𝟘ᶜ       ≈⟨ ·ᶜ-zeroʳ _ ⟩
      𝟘ᶜ             ∎

opaque
  unfolding cons

  -- A usage inversion lemma for cons

  inv-usage-cons :
    γ ▸[ m ] cons l A h t →
    ∃₃ λ δ η θ → δ ▸[ m ᵐ· pₕ ] h × η ▸[ m ] t × θ ▸[ 𝟘ᵐ? ] List l A × Prodrec-allowed m 𝟙 pₗ 𝟘 × γ ≤ᶜ pₕ ·ᶜ δ +ᶜ η
  inv-usage-cons {γ} {m} ▸cons =
    let invUsageProdrec {δ = δ₁} {η = δ₂} ▸t ▸u ▸A ok γ≤ = inv-usage-prodrec ▸cons
        invUsageProdʷ {δ = η₁} {η = η₂} ▸suc ▸cons′ δ₂≤ = inv-usage-prodʷ ▸u
        invUsageSuc {δ = η₁′} ▸x1 η₁≤ =
          inv-usage-suc (inv-usage-lift ▸suc)
        θ₁ , θ₂ , ▸h , ▸x0 , η₂≤ = V.inv-usage-cons′ʷ refl ▸cons′
        open ≤ᶜ-reasoning
    in  _ , _ , _ , wkUsage⁻¹ ▸h , ▸-cong ᵐ·-identityʳ ▸t , wkUsage⁻¹ ▸A , ok , (begin
      γ
        ≤⟨ γ≤ ⟩
      𝟙 ·ᶜ δ₁ +ᶜ δ₂
        ≈⟨ +ᶜ-congʳ (·ᶜ-identityˡ _) ⟩
      δ₁ +ᶜ δ₂
        ≤⟨ +ᶜ-monotoneʳ (tailₘ-monotone (tailₘ-monotone δ₂≤)) ⟩
      δ₁ +ᶜ tailₘ (tailₘ (pₗ ·ᶜ η₁ +ᶜ η₂))
        ≤⟨ +ᶜ-monotoneʳ (tailₘ-monotone (tailₘ-monotone (+ᶜ-monotone (·ᶜ-monotoneʳ η₁≤) η₂≤))) ⟩
      δ₁ +ᶜ tailₘ (tailₘ (pₗ ·ᶜ η₁′ +ᶜ pₕ ·ᶜ θ₁ +ᶜ θ₂))
        ≤⟨ +ᶜ-monotoneʳ $
           tailₘ-monotone (tailₘ-monotone (+ᶜ-monotone (·ᶜ-monotoneʳ (inv-usage-var (inv-usage-lower ▸x1))) (+ᶜ-monotoneʳ (inv-usage-var ▸x0)))) ⟩
      δ₁ +ᶜ tailₘ (tailₘ (pₗ ·ᶜ (𝟘ᶜ , x1 ≔ ⌜ m ᵐ· pₗ ⌝) +ᶜ pₕ ·ᶜ θ₁ +ᶜ (𝟘ᶜ , x0 ≔ ⌜ m ⌝)))
        ≈⟨ +ᶜ-congˡ (tailₘ-cong (tailₘ-distrib-+ᶜ (pₗ ·ᶜ (𝟘ᶜ , x1 ≔ ⌜ m ᵐ· pₗ ⌝)) (pₕ ·ᶜ θ₁ +ᶜ (𝟘ᶜ , x0 ≔ ⌜ m ⌝)))) ⟩
      δ₁ +ᶜ tailₘ (pₗ ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ m ᵐ· pₗ ⌝) +ᶜ tailₘ (pₕ ·ᶜ θ₁ +ᶜ (𝟘ᶜ , x0 ≔ ⌜ m ⌝)))
        ≈⟨ +ᶜ-congˡ (tailₘ-cong (+ᶜ-congˡ {γ = pₗ ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ m ᵐ· pₗ ⌝)} (tailₘ-distrib-+ᶜ (pₕ ·ᶜ θ₁) (𝟘ᶜ , x0 ≔ ⌜ m ⌝)))) ⟩
      δ₁ +ᶜ tailₘ (pₗ ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ m ᵐ· pₗ ⌝) +ᶜ tailₘ (pₕ ·ᶜ θ₁) +ᶜ 𝟘ᶜ)
        ≈⟨ +ᶜ-congˡ (tailₘ-cong (+ᶜ-congˡ {γ = pₗ ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ m ᵐ· pₗ ⌝)} (+ᶜ-identityʳ (tailₘ (pₕ ·ᶜ θ₁))))) ⟩
      δ₁ +ᶜ tailₘ (pₗ ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ m ᵐ· pₗ ⌝) +ᶜ tailₘ (pₕ ·ᶜ θ₁))
        ≈⟨ +ᶜ-congˡ (tailₘ-distrib-+ᶜ (pₗ ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ m ᵐ· pₗ ⌝)) (tailₘ (pₕ ·ᶜ θ₁))) ⟩
      δ₁ +ᶜ pₗ ·ᶜ 𝟘ᶜ +ᶜ tailₘ (tailₘ (pₕ ·ᶜ θ₁))
        ≈⟨ +ᶜ-congˡ (+ᶜ-cong (·ᶜ-zeroʳ _) (tailₘ-cong (tailₘ-distrib-·ᶜ pₕ θ₁))) ⟩
      δ₁ +ᶜ 𝟘ᶜ +ᶜ tailₘ (pₕ ·ᶜ tailₘ θ₁)
        ≈⟨ +ᶜ-congˡ (+ᶜ-identityˡ _) ⟩
      δ₁ +ᶜ tailₘ (pₕ ·ᶜ tailₘ θ₁)
        ≈⟨ +ᶜ-congˡ (tailₘ-distrib-·ᶜ pₕ (tailₘ θ₁)) ⟩
      δ₁ +ᶜ pₕ ·ᶜ tailₘ (tailₘ θ₁)
        ≈˘⟨ +ᶜ-congˡ (·ᶜ-congˡ (wkConₘ⁻¹-step (tailₘ θ₁))) ⟩
      δ₁ +ᶜ pₕ ·ᶜ wkConₘ⁻¹ (step id) (tailₘ θ₁)
        ≈˘⟨ +ᶜ-congˡ (·ᶜ-congˡ (wkConₘ⁻¹-step θ₁)) ⟩
      δ₁ +ᶜ pₕ ·ᶜ wkConₘ⁻¹ (step (step id)) θ₁
        ≈⟨ +ᶜ-comm _ _ ⟩
      pₕ ·ᶜ wkConₘ⁻¹ (step (step id)) θ₁ +ᶜ δ₁ ∎)


opaque
  unfolding listrec

  -- A usage inversion lemma for listrec

  inv-usage-listrec :
    ⦃ no-nr : Nr-not-available-GLB ⦄ →
    γ ▸[ m ] listrec r₁ r₂ p₁ p₂ q l A P nl cs xs →
    ∃₁₀ λ δ₁ δ₁′ δ₂ δ₂′ η θ₀ θ₁ θ₁′ θ₁″ θ₂ → ∃₃ λ x χ φ →
    θ₀ ▸[ 𝟘ᵐ? ] l × θ₁ ▸[ 𝟘ᵐ? ] A × θ₂ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] P ×
    δ₁ ▸[ m ] nl ×
    δ₂ ∙ ⌜ m ⌝ · r₂ · pₕ ∙ ⌜ m ⌝ · r₂ ▸[ m ]
      cs [ flip consSubst (var x3 ∘⟨ r₂ ⟩ var x0) $
           flip consSubst (prodʷ pₗ (lift (var x4)) (var x0)) $
           flip consSubst (var x1) $
           wkSubst 7 idSubst ] ×
    η ▸[ m ᵐ· r₁ ] xs ×
    Greatest-lower-bound x (nrᵢ p₂ 𝟙 (p₁ · pₗ)) ×
    Greatest-lower-boundᶜ χ (nrᵢᶜ p₂ δ₁′ δ₂′) ×
    Greatest-lower-boundᶜ φ (nrᵢᶜ 𝟙 θ₁′ θ₁″) ×
    Prodrec-allowed m r₁ pₗ q × Unitrec-allowed m r₂ q × Prodrec-allowed m r₂ pₕ q ×
    γ ≤ᶜ r₁ ·ᶜ η +ᶜ tailₘ (tailₘ χ) ×
    tailₘ (tailₘ δ₁′) ≤ᶜ δ₁ ×
    δ₂′ ∙ ⌜ m ⌝ · p₁ · pₗ ∙ ⌜ m ⌝ · p₂ ∙ ⌜ m ⌝ · r₂ ≤ᶜ δ₂ +ᶜ (𝟘ᶜ ∙ ⌜ m ⌝ · r₂) ×
    θ₁′ ≤ᶜ 𝟘ᶜ ×
    tailₘ (tailₘ (tailₘ θ₁″)) ≤ᶜ θ₁
  inv-usage-listrec {γ} {m} {r₁} {r₂} {p₁} {p₂} {cs} ▸lr =
    let invUsageProdrec {δ = γ₁} {η = γ₂} ▸xs ▸vr ▸P ok₁ γ≤ = inv-usage-prodrec ▸lr
        δ₁ , δ₁′ , δ₂ , δ₂′ , η₁ , η₂ , θ₀ , θ₁ , θ₁′ , θ₁″ , θ₂ , x , χ
         , φ , ▸l , ▸A₂ , ▸P′ , ▸nl₂ , ▸cs , ▸x1 , ▸x0 , ok₂ , ok₃
         , x-GLB , χ-GLB , φ-GLB , le₁ , le₂ , le₃ , le₄ , le₅ =
         V.inv-usage-vecrec′ refl ▸vr
        ▸A = wkUsage⁻¹ ▸A₂
        ▸nl = wkUsage⁻¹ ▸nl₂
        cs[]≡ = let open Tools.Reasoning.PropositionalEquality in begin
          cs [ flip consSubst (var x0) $
               flip consSubst (prodʷ pₗ (lift (var x3)) (var x1)) $
               flip consSubst (var x2) $
               wkSubst 6 idSubst
             ]
             [ flip consSubst (var x3 ∘⟨ r₂ ⟩ var x0) $
               flip consSubst (var x0) $
               flip consSubst (var x1) $
               flip consSubst (var x4) $
               wkSubst 5 idSubst
             ]                                                          ≡⟨ substCompEq cs ⟩

          cs [ flip consSubst (var x3 ∘⟨ r₂ ⟩ var x0)
                 (flip consSubst (var x0) $
                  flip consSubst (var x1) $
                  flip consSubst (var x4) $
                  wkSubst 5 idSubst) ₛ•ₛ
               flip consSubst (var x0)
                 (flip consSubst (prodʷ pₗ (lift (var x3)) (var x1)) $
                  flip consSubst (var x2) $
                  wkSubst 6 idSubst)
             ]                                                          ≡⟨ (flip substVar-to-subst cs λ where
                                                                              x0        → refl
                                                                              (x0 +1)   → refl
                                                                              (x0 +2)   → refl
                                                                              (_ +1 +2) → refl) ⟩
          cs [ flip consSubst (var x3 ∘⟨ r₂ ⟩ var x0) $
               flip consSubst (prodʷ pₗ (lift (var x4)) (var x0)) $
               flip consSubst (var x1) $
               wkSubst 7 idSubst
             ]                                                          ∎
        ▸cs′ = subst (_▸[_]_ _ _) cs[]≡ ▸cs
        open ≤ᶜ-reasoning
    in  _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _
          , wkUsage⁻¹ ▸l , ▸A , ▸P , ▸nl , ▸cs′ , ▸xs
          , x-GLB , χ-GLB , φ-GLB
          , ok₁ , ok₂ , ok₃
          , (begin
               γ
                 ≤⟨ γ≤ ⟩
               r₁ ·ᶜ γ₁ +ᶜ γ₂
                 ≤⟨ +ᶜ-monotoneʳ (tailₘ-monotone (tailₘ-monotone le₁)) ⟩
               r₁ ·ᶜ γ₁ +ᶜ tailₘ (tailₘ (x ·ᶜ η₁ +ᶜ χ +ᶜ r₂ ·ᶜ η₂))
                 ≤⟨ +ᶜ-monotoneʳ $ tailₘ-monotone $ tailₘ-monotone $
                    +ᶜ-monotone (·ᶜ-monotoneʳ (inv-usage-var (inv-usage-lower ▸x1)))
                      (+ᶜ-monotoneʳ (·ᶜ-monotoneʳ (inv-usage-var ▸x0))) ⟩
               r₁ ·ᶜ γ₁ +ᶜ tailₘ (tailₘ (x ·ᶜ (𝟘ᶜ ∙ ⌜ m ⌝ ∙ 𝟘) +ᶜ χ +ᶜ r₂ ·ᶜ (𝟘ᶜ ∙ ⌜ m ᵐ· r₂ ⌝)))
                 ≈⟨ +ᶜ-congˡ (tailₘ-cong (tailₘ-distrib-+ᶜ (x ·ᶜ (𝟘ᶜ ∙ ⌜ m ⌝ ∙ 𝟘)) (χ +ᶜ r₂ ·ᶜ (𝟘ᶜ ∙ ⌜ m ᵐ· r₂ ⌝)))) ⟩
               r₁ ·ᶜ γ₁ +ᶜ tailₘ (x ·ᶜ (𝟘ᶜ ∙ ⌜ m ⌝) +ᶜ tailₘ (χ +ᶜ r₂ ·ᶜ (𝟘ᶜ ∙ ⌜ m ᵐ· r₂ ⌝)))
                 ≈⟨ +ᶜ-congˡ (tailₘ-cong (+ᶜ-congˡ {γ = x ·ᶜ (𝟘ᶜ ∙ ⌜ m ⌝)} (tailₘ-distrib-+ᶜ χ (r₂ ·ᶜ (𝟘ᶜ ∙ ⌜ m ᵐ· r₂ ⌝))))) ⟩
               r₁ ·ᶜ γ₁ +ᶜ tailₘ (x ·ᶜ (𝟘ᶜ ∙ ⌜ m ⌝) +ᶜ tailₘ χ +ᶜ r₂ ·ᶜ 𝟘ᶜ)
                 ≈⟨ +ᶜ-congˡ (tailₘ-cong (+ᶜ-congˡ {γ = x ·ᶜ (𝟘ᶜ ∙ ⌜ m ⌝)} (+ᶜ-congˡ {γ = tailₘ χ} (·ᶜ-zeroʳ r₂)))) ⟩
               r₁ ·ᶜ γ₁ +ᶜ tailₘ (x ·ᶜ (𝟘ᶜ ∙ ⌜ m ⌝) +ᶜ tailₘ χ +ᶜ 𝟘ᶜ)
                 ≈⟨ +ᶜ-congˡ (tailₘ-cong (+ᶜ-congˡ {γ = x ·ᶜ (𝟘ᶜ ∙ ⌜ m ⌝)} (+ᶜ-identityʳ (tailₘ χ)))) ⟩
               r₁ ·ᶜ γ₁ +ᶜ tailₘ (x ·ᶜ (𝟘ᶜ ∙ ⌜ m ⌝) +ᶜ tailₘ χ)
                 ≈⟨ +ᶜ-congˡ (tailₘ-distrib-+ᶜ (x ·ᶜ (𝟘ᶜ ∙ ⌜ m ⌝)) (tailₘ χ)) ⟩
               r₁ ·ᶜ γ₁ +ᶜ x ·ᶜ 𝟘ᶜ +ᶜ tailₘ (tailₘ χ)
                 ≈⟨ +ᶜ-congˡ (+ᶜ-congʳ (·ᶜ-zeroʳ _)) ⟩
               r₁ ·ᶜ γ₁ +ᶜ 𝟘ᶜ +ᶜ tailₘ (tailₘ χ)
                 ≈⟨ +ᶜ-congˡ (+ᶜ-identityˡ _) ⟩
               r₁ ·ᶜ γ₁ +ᶜ tailₘ (tailₘ χ) ∎)
          , (begin
               tailₘ (tailₘ δ₁′)             ≤⟨ tailₘ-monotone (tailₘ-monotone le₂) ⟩
               tailₘ (tailₘ δ₁)              ≈˘⟨ wkConₘ⁻¹-step (tailₘ δ₁) ⟩
               wkConₘ⁻¹ (step id) (tailₘ δ₁) ≈˘⟨ wkConₘ⁻¹-step δ₁ ⟩
               wkConₘ⁻¹ (step (step id)) δ₁  ∎)
          , le₃ , le₄
          , (begin
               tailₘ (tailₘ (tailₘ θ₁″)) ≤⟨ tailₘ-monotone (tailₘ-monotone (tailₘ-monotone le₅)) ⟩
               tailₘ (tailₘ (tailₘ θ₁))             ≈˘⟨ wkConₘ⁻¹-step (tailₘ (tailₘ θ₁)) ⟩
               wkConₘ⁻¹ (step id) (tailₘ (tailₘ θ₁)) ≈˘⟨ wkConₘ⁻¹-step (tailₘ θ₁) ⟩
               wkConₘ⁻¹ (step (step id)) (tailₘ θ₁) ∎)
