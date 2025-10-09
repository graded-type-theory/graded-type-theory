------------------------------------------------------------------------
-- Some properties related to usage and Vec
------------------------------------------------------------------------

import Graded.Modality
open import Graded.Usage.Restrictions
import Definition.Untyped

module Graded.Derived.Vec
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (open Definition.Untyped M)
  (s : Strength)
  (p : M)
  (R : Usage-restrictions 𝕄)
  where

open Modality 𝕄
open Usage-restrictions R

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Mode 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Usage 𝕄 R
open import Graded.Usage.Inversion 𝕄 R
open import Graded.Usage.Properties 𝕄 R
import Graded.Usage.Restrictions.Instance
open import Graded.Usage.Weakening 𝕄 R
open import Graded.Substitution 𝕄 R
open import Graded.Substitution.Properties 𝕄 R

open import Definition.Untyped.Vec 𝕄 s p

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+; 2+; 4+)
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
import Tools.Reasoning.PropositionalEquality

private variable
  n : Nat
  l : Universe-level
  A P k t h xs nl cs : Term _
  γ δ η γ₁ γ₂ δ₁ δ₂ η₁ η₂ θ₁ θ₂ : Conₘ _
  m : Mode
  p₁ p₂ p₃ p₄ q q₁ q₂ r r₁ r₂ : M

------------------------------------------------------------------------
-- Usage rules for Vec

opaque
  unfolding Vec′

  -- A usage rule for Vec′

  ▸Vec′ :
    ⦃ no-nr : Nr-not-available-GLB ⦄ →
    γ ▸[ m ] k →
    δ ▸[ m ᵐ· p ] A →
    Greatest-lower-boundᶜ η (nrᵢᶜ 𝟙 𝟘ᶜ δ) →
    γ +ᶜ η ▸[ m ] Vec′ l A k
  ▸Vec′ {δ} ▸k ▸A η-GLB =
    let ▸wk₂A = wkUsage (step (step id)) ▸A
        ▸Σ = sub-≈ᶜ {δ = δ ∙ _ ∙ _}
              (ΠΣₘ ▸wk₂A (sub var (≤ᶜ-refl ∙ ≤-reflexive (·-zeroʳ _))))
              (≈ᶜ-sym (+ᶜ-identityʳ _) ∙
                trans (·-zeroʳ _) (sym (+-identityʳ _)) ∙
                trans (·-identityʳ _) (sym (+-identityˡ _)))
        ▸U = sub-≈ᶜ Uₘ (≈ᶜ-refl ∙ ·-zeroʳ _)
    in  sub-≈ᶜ (natrec-no-nr-glbₘ Unitₘ ▸Σ ▸k ▸U nrᵢ-const-GLB₁ η-GLB)
          (+ᶜ-congʳ (≈ᶜ-sym (·ᶜ-identityˡ _)))

opaque
  unfolding nil′

  -- A usage rule for nil′

  ▸nil′ : 𝟘ᶜ ▸[ m ] nil′ l A
  ▸nil′ = starₘ

opaque
  unfolding cons′

  -- A usage rule for cons′ where weak unit and Σ-types are used

  ▸cons′ʷ :
    s ≡ 𝕨 →
    γ ▸[ m ᵐ· p ] h →
    δ ▸[ m ] t →
    p ·ᶜ γ +ᶜ δ ▸[ m ] cons′ A k h t
  ▸cons′ʷ refl ▸h ▸t = prodʷₘ ▸h ▸t

opaque
  unfolding cons′

  -- A usage rule for cons′ where strong unit and Σ-types are used

  ▸cons′ˢ :
    s ≡ 𝕤 →
    γ ▸[ m ᵐ· p ] h →
    δ ▸[ m ] t →
    p ·ᶜ γ ∧ᶜ δ ▸[ m ] cons′ A k h t
  ▸cons′ˢ refl ▸h ▸t = prodˢₘ ▸h ▸t

opaque
  unfolding vecrec-nil

  -- A usage lemma for vecrec-nil

  ▸vecrec-nil :
    γ ▸[ m ] nl →
    δ ∙ ⌜ 𝟘ᵐ? ⌝ · q₁ ∙ ⌜ 𝟘ᵐ? ⌝ · q₂ ▸[ 𝟘ᵐ? ] P →
    Unitrec-allowed m r q₂ →
    γ ▸[ m ] vecrec-nil l r q₂ P nl
  ▸vecrec-nil {γ} {m} {δ} {q₁} {q₂} {r} ▸nl ▸P ok =
    let ▸wk1nl = wkUsage (step id) ▸nl
        Ψ▶σ = ▶-cong _
               (λ { x0 → refl ; (x0 +1) → refl ; (x +2) → refl})
               (wf-liftSubstₘ (wf-consSubstₘ (wf-wk1Substₘ idSubstₘ idSubst wf-idSubstₘ)
                 (sub-≈ᶜ zeroₘ (·ᶜ-zeroʳ _))))
        ▸P′ = substₘ-lemma (liftSubstₘ (consSubstₘ (wk1Substₘ idSubstₘ) 𝟘ᶜ)) Ψ▶σ ▸P
        δ≤ = begin
          δ ∙ 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ · q₂
            ≈˘⟨ +ᶜ-identityˡ _ ∙ +-identityʳ _ ⟩
          (𝟘ᶜ ∙ 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ · q₂) +ᶜ (δ ∙ 𝟘 ∙ 𝟘)
            ≈˘⟨ +ᶜ-cong (·ᶜ-zeroʳ _ ∙ ·-identityʳ _) (+ᶜ-identityˡ _) ⟩
          (⌜ 𝟘ᵐ? ⌝ · q₂) ·ᶜ (𝟘ᶜ , x0 ≔ 𝟙) +ᶜ 𝟘ᶜ +ᶜ (δ ∙ 𝟘 ∙ 𝟘)
            ≈˘⟨ +ᶜ-congˡ (+ᶜ-congˡ (<*-identityˡ _ ∙ refl ∙ refl)) ⟩
          (⌜ 𝟘ᵐ? ⌝ · q₂) ·ᶜ (𝟘ᶜ , x0 ≔ 𝟙) +ᶜ 𝟘ᶜ +ᶜ (δ <* idSubstₘ ∙ 𝟘 ∙ 𝟘)
            ≈˘⟨ +ᶜ-congˡ (+ᶜ-cong (·ᶜ-zeroʳ _) (<*-wkSubstₘ′ {k = 2} δ)) ⟩
          (⌜ 𝟘ᵐ? ⌝ · q₂) ·ᶜ (𝟘ᶜ , x0 ≔ 𝟙) +ᶜ (⌜ 𝟘ᵐ? ⌝ · q₁) ·ᶜ 𝟘ᶜ +ᶜ
                            δ <* wk1Substₘ (wk1Substₘ idSubstₘ) ∎
        ▸P″ = sub ▸P′ δ≤
        γ≤ = begin
          γ ∙ ⌜ m ⌝ · r                      ≈⟨ ≈ᶜ-refl ∙ ⌜⌝-·-comm m ⟩
          γ ∙ r · ⌜ m ⌝                      ≈˘⟨ ≈ᶜ-refl ∙ ·⌜ᵐ·⌝ m ⟩
          γ ∙ r · ⌜ m ᵐ· r ⌝                ≈˘⟨ +ᶜ-identityˡ _ ∙ +-identityʳ _ ⟩
          (𝟘ᶜ ∙ r · ⌜ m ᵐ· r ⌝) +ᶜ (γ ∙ 𝟘)  ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _ ∙ refl) ⟩
          r ·ᶜ (𝟘ᶜ ∙ ⌜ m ᵐ· r ⌝) +ᶜ (γ ∙ 𝟘) ∎
    in  lamₘ (sub (unitrecₘ var ▸wk1nl ▸P″ ok) γ≤)
    where
    open ≤ᶜ-reasoning

opaque
  unfolding vecrec-cons

  -- A usage lemma for vecrec-cons

  ▸vecrec-cons :
    ⦃ Has-well-behaved-GLBs semiring-with-meet ⦄ →
    γ ∙ ⌜ m ⌝ · p₁ ∙ ⌜ m ⌝ · p₂ · p ∙ ⌜ m ⌝ · p₃ ∙ ⌜ m ⌝ · p₄ ▸[ m ] cs →
    δ ∙ ⌜ 𝟘ᵐ? ⌝ · q₁ ∙ ⌜ 𝟘ᵐ? ⌝ · q₂ ▸[ 𝟘ᵐ? ] P →
    Greatest-lower-bound r (nrᵢ p₄ p₂ p₃) →
    Prodrec-allowed m r p q₂ →
    γ ∙ ⌜ m ⌝ · p₁ ∙ ⌜ m ⌝ · p₄ ▸[ m ] vecrec-cons r q₂ P cs
  ▸vecrec-cons {γ} {m} {p₁} {p₂} {p₃} {p₄} {δ} {q₁} {q₂} {r} ▸cs ▸P r-GLB ok =
    let ▸x0 = sub-≈ᶜ var (·ᶜ-zeroʳ _ ∙ ·-identityʳ _)
        ▸x1 = sub-≈ᶜ var (·ᶜ-zeroʳ _ ∙ ·-identityʳ _ ∙ ·-zeroʳ _)
        ▸x4 = sub-≈ᶜ var (·ᶜ-zeroʳ _ ∙ ·-identityʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _)
        ▸x3x0 = sub-≈ᶜ (var ∘ₘ var) (lemma₃ _ _ ∙ lemma₂ _ _ ∙ lemma₁ _ _ ∙ lemma₂ _ _ ∙ lemma₂ _ _ ∙ lemma₄ ⌞ ⌜ m ⌝ · p₄ ⌟ r)
        Ψ▶σ = ▶-cong _
               (λ { x0 → refl ; (x0 +1) → refl ; (x0 +2) → refl
                  ; (x0 +1 +2) → refl ; ((x +2) +2) → refl})
               (wf-consSubstₘ (wf-consSubstₘ (wf-consSubstₘ
                 (wf-consSubstₘ (wf-wkSubstₘ′ {k = 5} wf-idSubstₘ) ▸x4) ▸x1) ▸x0) ▸x3x0)
        ▸cs′ = substₘ-lemma _ Ψ▶σ ▸cs
        open ≤ᶜ-reasoning
        γ≤′ = begin
          γ ∙ ⌜ m ⌝ · p₁ ∙ ⌜ m ⌝ · p₄ ∙ 𝟘 ∙ ⌜ m ⌝ · r · p
            ∙ ⌜ m ⌝ · r                                            ≤⟨ ≤ᶜ-refl ∙ ·-monotoneʳ (·-monotoneˡ (nrᵢ-GLB-≤₀ r-GLB)) ∙ ·-monotoneʳ (nrᵢ-GLB-≤ r-GLB) ⟩
          γ ∙ ⌜ m ⌝ · p₁ ∙ ⌜ m ⌝ · p₄ ∙ 𝟘 ∙ ⌜ m ⌝ · p₂ · p
            ∙ ⌜ m ⌝ · (p₃ + p₄ · r)                                ≈⟨ ≈ᶜ-refl ∙ ·-congˡ (+-comm _ _) ⟩
          γ ∙ ⌜ m ⌝ · p₁ ∙ ⌜ m ⌝ · p₄ ∙ 𝟘 ∙ ⌜ m ⌝ · p₂ · p
            ∙ ⌜ m ⌝ · (p₄ · r + p₃)                                ≈⟨ ≈ᶜ-refl ∙ ·-distribˡ-+ _ _ _ ⟩
          γ ∙ ⌜ m ⌝ · p₁ ∙ ⌜ m ⌝ · p₄ ∙ 𝟘 ∙ ⌜ m ⌝ · p₂ · p
            ∙ ⌜ m ⌝ · p₄ · r + ⌜ m ⌝ · p₃                          ≈˘⟨ +ᶜ-identityˡ _ ∙ +-identityˡ _ ∙ +-identityʳ _ ∙ +-identityˡ _ ∙ +-identityˡ _ ∙ +-congʳ (·-assoc _ _ _) ⟩
          (𝟘ᶜ , x3 ≔ ⌜ m ⌝ · p₄ , x0 ≔ (⌜ m ⌝ · p₄) · r) +ᶜ
          (γ ∙ ⌜ m ⌝ · p₁ ∙ 𝟘 ∙ 𝟘 ∙ (⌜ m ⌝ · p₂ · p) ∙ ⌜ m ⌝ · p₃)   ≈˘⟨ +ᶜ-congʳ (update-congˡ {x = x0} (update-cong {x = x3} (·ᶜ-zeroʳ (⌜ m ⌝ · p₄)) (·-identityʳ _))) ⟩
          (((⌜ m ⌝ · p₄) ·ᶜ 𝟘ᶜ , x3 ≔ (⌜ m ⌝ · p₄) · 𝟙)
                               , x0 ≔ (⌜ m ⌝ · p₄) · r)           +ᶜ
          (γ ∙ ⌜ m ⌝ · p₁ ∙ 𝟘 ∙ 𝟘 ∙ (⌜ m ⌝ · p₂ · p) ∙ ⌜ m ⌝ · p₃)   ≡˘⟨ cong (λ x → (x , x0 ≔ (⌜ m ⌝ · p₄) · r) +ᶜ (γ ∙ ⌜ m ⌝ · p₁ ∙ 𝟘 ∙ 𝟘 ∙ (⌜ m ⌝ · p₂ · p) ∙ ⌜ m ⌝ · p₃))
                                                                          (update-distrib-·ᶜ 𝟘ᶜ (⌜ m ⌝ · p₄) 𝟙 x3) ⟩
          ((⌜ m ⌝ · p₄) ·ᶜ (𝟘ᶜ , x3 ≔ 𝟙) , x0 ≔ (⌜ m ⌝ · p₄) · r) +ᶜ
          (γ ∙ ⌜ m ⌝ · p₁ ∙ 𝟘 ∙ 𝟘 ∙ (⌜ m ⌝ · p₂ · p) ∙ ⌜ m ⌝ · p₃)   ≈˘⟨ +ᶜ-congˡ (+ᶜ-identityˡ _ ∙ +-identityˡ _ ∙ +-identityʳ _ ∙ +-identityʳ _ ∙ +-identityˡ _ ∙ +-identityʳ _) ⟩
          ((⌜ m ⌝ · p₄) ·ᶜ (𝟘ᶜ , x3 ≔ 𝟙) , x0 ≔ (⌜ m ⌝ · p₄) · r) +ᶜ
          (𝟘ᶜ , x0 ≔ (⌜ m ⌝ · p₃))                                +ᶜ
          (γ ∙ ⌜ m ⌝ · p₁ ∙ 𝟘 ∙ 𝟘 ∙ (⌜ m ⌝ · p₂ · p) ∙ 𝟘)            ≈˘⟨ +ᶜ-congˡ (+ᶜ-congˡ (+ᶜ-identityˡ _ ∙ +-identityˡ _ ∙ +-identityʳ _ ∙ +-identityʳ _ ∙ +-identityʳ _ ∙ +-identityʳ _)) ⟩
          ((⌜ m ⌝ · p₄) ·ᶜ (𝟘ᶜ , x3 ≔ 𝟙) , x0 ≔ (⌜ m ⌝ · p₄) · r) +ᶜ
          (𝟘ᶜ , x0 ≔ (⌜ m ⌝ · p₃))                                +ᶜ
          (𝟘ᶜ , x1 ≔ (⌜ m ⌝ · p₂ · p))                            +ᶜ
          (γ ∙ ⌜ m ⌝ · p₁ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟘)                           ≈˘⟨ +ᶜ-congˡ (+ᶜ-congˡ (+ᶜ-congˡ (+ᶜ-identityˡ _ ∙ +-identityʳ _ ∙ +-identityʳ _ ∙ +-identityʳ _ ∙ +-identityʳ _ ∙ +-identityʳ _))) ⟩
          ((⌜ m ⌝ · p₄) ·ᶜ (𝟘ᶜ , x3 ≔ 𝟙) , x0 ≔ (⌜ m ⌝ · p₄) · r) +ᶜ
          (𝟘ᶜ , x0 ≔ (⌜ m ⌝ · p₃))                                +ᶜ
          (𝟘ᶜ , x1 ≔ (⌜ m ⌝ · p₂ · p))                            +ᶜ
          (𝟘ᶜ , x4 ≔ (⌜ m ⌝ · p₁))                                +ᶜ
          (γ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟘)                                   ≈˘⟨ +ᶜ-congˡ (+ᶜ-cong (update-cong {x = x0} (·ᶜ-zeroʳ (⌜ m ⌝ · p₃)) (·-identityʳ _))
                                                                          (+ᶜ-cong (update-cong {x = x1} (·ᶜ-zeroʳ (⌜ m ⌝ · p₂ · p)) (·-identityʳ _))
                                                                          (+ᶜ-congʳ (update-cong {x = x4} (·ᶜ-zeroʳ (⌜ m ⌝ · p₁)) (·-identityʳ _))))) ⟩
          ((⌜ m ⌝ · p₄) ·ᶜ (𝟘ᶜ , x3 ≔ 𝟙) , x0 ≔ (⌜ m ⌝ · p₄) · r) +ᶜ
          ((⌜ m ⌝ · p₃) ·ᶜ 𝟘ᶜ , x0 ≔ (⌜ m ⌝ · p₃) · 𝟙)            +ᶜ
          ((⌜ m ⌝ · p₂ · p) ·ᶜ 𝟘ᶜ , x1 ≔ (⌜ m ⌝ · p₂ · p) · 𝟙)    +ᶜ
          ((⌜ m ⌝ · p₁) ·ᶜ 𝟘ᶜ , x4 ≔ (⌜ m ⌝ · p₁) · 𝟙)            +ᶜ
          (γ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟘)                                   ≡˘⟨ cong₄ (λ x₁ x₂ x₃ x₄ → x₁ +ᶜ x₂ +ᶜ x₃ +ᶜ x₄ +ᶜ (γ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟘))
                                                                         (update-distrib-·ᶜ (𝟘ᶜ , x3 ≔ 𝟙) _ _ x0)
                                                                         (update-distrib-·ᶜ 𝟘ᶜ _ _ x0)
                                                                         (update-distrib-·ᶜ 𝟘ᶜ _ _ x1)
                                                                         (update-distrib-·ᶜ 𝟘ᶜ _ _ x4) ⟩
          (⌜ m ⌝ · p₄) ·ᶜ (𝟘ᶜ , x3 ≔ 𝟙 , x0 ≔ r) +ᶜ
          (⌜ m ⌝ · p₃) ·ᶜ (𝟘ᶜ , x0 ≔ 𝟙)          +ᶜ
          (⌜ m ⌝ · p₂ · p) ·ᶜ (𝟘ᶜ , x1 ≔ 𝟙)      +ᶜ
          (⌜ m ⌝ · p₁) ·ᶜ (𝟘ᶜ , x4 ≔ 𝟙)          +ᶜ
          (γ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟘)                                    ≈˘⟨ +ᶜ-congˡ (+ᶜ-congˡ (+ᶜ-congˡ (+ᶜ-congˡ
                                                                           (≈ᶜ-trans (<*-wkSubstₘ′ {k = 5} γ)
                                                                             (<*-identityˡ _ ∙ refl ∙ refl ∙ refl ∙ refl ∙ refl))))) ⟩
          (⌜ m ⌝ · p₄) ·ᶜ (𝟘ᶜ , x3 ≔ 𝟙 , x0 ≔ r) +ᶜ
          (⌜ m ⌝ · p₃) ·ᶜ (𝟘ᶜ , x0 ≔ 𝟙)          +ᶜ
          (⌜ m ⌝ · p₂ · p) ·ᶜ (𝟘ᶜ , x1 ≔ 𝟙)      +ᶜ
          (⌜ m ⌝ · p₁) ·ᶜ (𝟘ᶜ , x4 ≔ 𝟙)          +ᶜ
          γ <* wkSubstₘ′ 5 idSubstₘ                                   ∎
        ▸cs″ = sub ▸cs′ γ≤′
        ▸x2 = sub-≈ᶜ (sucₘ var) (·ᶜ-zeroʳ _ ∙ ·-identityʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _)
        Ψ▶σ′ = ▶-cong {σ = consSubst (wkSubst 3 idSubst) (suc (var x2)) ⇑} _
                (λ { x0 → refl ; (_+1 x0) → refl ; (x +2) → refl})
                (wf-liftSubstₘ (wf-consSubstₘ (wf-wkSubstₘ′ wf-idSubstₘ) ▸x2))
        ▸P′ = substₘ-lemma _ Ψ▶σ′ ▸P
        δ≤ = begin
          δ ∙ ⌜ 𝟘ᵐ? ⌝ · q₁ ∙ 𝟘 ∙ 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ · q₂ ≈˘⟨ +ᶜ-identityˡ _ ∙ +-identityˡ _ ∙ +-identityˡ _ ∙ +-identityʳ _ ∙ +-identityʳ _ ⟩
          (𝟘ᶜ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ · q₂) +ᶜ
          (δ ∙ ⌜ 𝟘ᵐ? ⌝ · q₁ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘)          ≈˘⟨ +ᶜ-congˡ (+ᶜ-identityˡ _ ∙ +-identityʳ _ ∙ +-identityʳ _ ∙ +-identityʳ _ ∙ +-identityʳ _) ⟩
          (𝟘ᶜ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ · q₂) +ᶜ
          (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · q₁ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘) +ᶜ
          (δ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟘)                     ≈˘⟨ +ᶜ-cong (·ᶜ-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-identityʳ _)
                                                      (+ᶜ-congʳ (·ᶜ-zeroʳ _ ∙ ·-identityʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _)) ⟩
          (⌜ 𝟘ᵐ? ⌝ · q₂) ·ᶜ (𝟘ᶜ , x0 ≔ 𝟙) +ᶜ
          (⌜ 𝟘ᵐ? ⌝ · q₁) ·ᶜ (𝟘ᶜ , x3 ≔ 𝟙) +ᶜ
          (δ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟘)                     ≈˘⟨ +ᶜ-congˡ (+ᶜ-congˡ (≈ᶜ-trans (<*-wkSubstₘ′ {k = 4} δ)
                                                        (<*-identityˡ _ ∙ refl ∙ refl ∙ refl ∙ refl))) ⟩
          (⌜ 𝟘ᵐ? ⌝ · q₂) ·ᶜ (𝟘ᶜ , x0 ≔ 𝟙) +ᶜ
          (⌜ 𝟘ᵐ? ⌝ · q₁) ·ᶜ (𝟘ᶜ , x3 ≔ 𝟙) +ᶜ
          δ <* wkSubstₘ′ 4 idSubstₘ                ∎
        ▸P″ = sub ▸P′ δ≤
        γ≤ = begin
          γ  ∙ ⌜ m ⌝ · p₁ ∙ ⌜ m ⌝ · p₄ ∙ ⌜ m ⌝ · r            ≈⟨ ≈ᶜ-refl ∙ lemma₄′ m _ ⟩
          γ  ∙ ⌜ m ⌝ · p₁ ∙ ⌜ m ⌝ · p₄ ∙ r ·  ⌜ m ᵐ· r ⌝      ≈˘⟨ +ᶜ-identityˡ _ ∙ +-identityˡ _ ∙ +-identityˡ _ ∙ +-identityʳ _ ⟩
          (𝟘ᶜ ∙ 𝟘         ∙ 𝟘          ∙ r ·  ⌜ m ᵐ· r ⌝) +ᶜ
          (γ ∙ ⌜ m ⌝ · p₁ ∙ ⌜ m ⌝ · p₄ ∙ 𝟘)                   ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ r ∙ ·-zeroʳ r ∙ ·-zeroʳ r ∙ refl) ⟩
          r ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ m ᵐ· r ⌝)                     +ᶜ
          (γ ∙ ⌜ m ⌝ · p₁ ∙ ⌜ m ⌝ · p₄ ∙ 𝟘)                   ∎
    in lamₘ (sub (prodrecₘ var ▸cs″ ▸P″ ok) γ≤)
    where
    lemma₁ : ∀ p q → p · 𝟙 ≡ p + q · 𝟘
    lemma₁ p q =
      let open Tools.Reasoning.PropositionalEquality
      in  begin
        p · 𝟙     ≡⟨ ·-identityʳ _ ⟩
        p         ≡˘⟨ +-identityʳ _ ⟩
        p + 𝟘     ≡˘⟨ +-congˡ (·-zeroʳ _) ⟩
        p + q · 𝟘 ∎
    lemma₂ : ∀ p q → p · 𝟘 ≡ 𝟘 + q · 𝟘
    lemma₂ p q =
      let open Tools.Reasoning.PropositionalEquality
      in  begin
        p · 𝟘     ≡⟨ ·-zeroʳ _ ⟩
        𝟘         ≡˘⟨ +-identityʳ _ ⟩
        𝟘 + 𝟘     ≡˘⟨ +-congˡ (·-zeroʳ _) ⟩
        𝟘 + q · 𝟘 ∎
    lemma₃ : ∀ {n} p q → p ·ᶜ 𝟘ᶜ {n = n} ≈ᶜ 𝟘ᶜ +ᶜ q ·ᶜ 𝟘ᶜ
    lemma₃ p q =
      let open ≈ᶜ-reasoning in
      begin
        p ·ᶜ 𝟘ᶜ       ≈⟨ ·ᶜ-zeroʳ _ ⟩
        𝟘ᶜ            ≈˘⟨ +ᶜ-identityˡ _ ⟩
        𝟘ᶜ +ᶜ 𝟘ᶜ      ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _) ⟩
        𝟘ᶜ +ᶜ q ·ᶜ 𝟘ᶜ ∎
    lemma₄′ : ∀ m p → ⌜ m ⌝ · p ≡ p · ⌜ m ᵐ· p ⌝
    lemma₄′ m p =
      let open Tools.Reasoning.PropositionalEquality
      in  begin
        ⌜ m ⌝ · p      ≡⟨ ⌜⌝-·-comm m ⟩
        p · ⌜ m ⌝      ≡˘⟨ ·⌜ᵐ·⌝  m ⟩
        p · ⌜ m ᵐ· p ⌝ ∎
    lemma₄ : ∀ m p → ⌜ m ⌝ · p ≡ 𝟘 + p · ⌜ m ᵐ· p ⌝
    lemma₄ m p =
      let open Tools.Reasoning.PropositionalEquality
      in  begin
        ⌜ m ⌝ · p          ≡⟨ lemma₄′ m p ⟩
        p · ⌜ m ᵐ· p ⌝     ≡˘⟨ +-identityˡ _ ⟩
        𝟘 + p · ⌜ m ᵐ· p ⌝ ∎

opaque
  unfolding vecrec′

  -- A usage rule for vecrec′
  --
  -- The grades can be interpreted as follows:
  -- p₁ represents the uses of the length in cs
  -- p₂ represents the uses of the head in cs
  -- p₃ represents the uses of the tail in cs
  -- p₄ represents the uses of the recursive call in cs
  -- q₁ represents the uses of the length in the motive P
  -- q₂ represents the uses of the vector in the motive P
  -- r₁ represents the total uses of the length
  -- r₂ represents the total of the vector

  ▸vecrec′ :
    ⦃ no-nr : Nr-not-available-GLB ⦄ →
    γ₁ ▸[ m ] nl →
    γ₂ ∙ ⌜ m ⌝ · p₁ ∙ ⌜ m ⌝ · p₂ · p ∙ ⌜ m ⌝ · p₃ ∙ ⌜ m ⌝ · p₄ ▸[ m ] cs →
    δ₁ ▸[ m ] k →
    δ₂ ▸[ m ᵐ· r₂ ] xs →
    η₁ ▸[ 𝟘ᵐ? ] A →
    η₂ ∙ ⌜ 𝟘ᵐ? ⌝ · q₁ ∙ ⌜ 𝟘ᵐ? ⌝ · q₂ ▸[ 𝟘ᵐ? ] P →
    Greatest-lower-bound r₁ (nrᵢ p₄ 𝟙 p₁) →
    Greatest-lower-bound r₂ (nrᵢ p₄ p₂ p₃) →
    Greatest-lower-boundᶜ θ₁ (nrᵢᶜ p₄ γ₁ γ₂) →
    Greatest-lower-boundᶜ θ₂ (nrᵢᶜ 𝟙 𝟘ᶜ η₁) →
    Unitrec-allowed m r₂ q₂ →
    Prodrec-allowed m r₂ p q₂ →
    θ₁ +ᶜ r₁ ·ᶜ δ₁ +ᶜ r₂ ·ᶜ δ₂ ▸[ m ] vecrec′ l p₁ p₄ r₂ q₁ q₂ A P nl cs k xs
  ▸vecrec′ {δ₁} {δ₂} {r₂} {η₂} {q₁} {r₁} {θ₁} {θ₂}
    ▸nl ▸cs ▸k ▸xs ▸A ▸P r₁-GLB r₂-GLB θ₁-GLB θ₂-GLB ok₁ ok₂ =
    let open Graded.Usage.Restrictions.Instance R
        open ≈ᶜ-reasoning
        ▸wk1A = wkUsage (step id) (▸-cong (sym (trans (cong (_ᵐ· p) ᵐ·-zeroˡ) ᵐ·-zeroˡ)) ▸A)
        θ₂-GLB′ = GLBᶜ-congˡ (λ i → ≈ᶜ-refl ∙ sym (nrᵢ-𝟘 i))
                   (wk-GLBᶜ (step id) θ₂-GLB)
        ▸Π = ΠΣₘ (▸Vec′ {η = θ₂ ∙ 𝟘} (var {x = x0}) ▸wk1A θ₂-GLB′) ▸P
        ▸Π′ = sub-≈ᶜ ▸Π $ begin
          θ₂ +ᶜ η₂ ∙ (⌜ 𝟘ᵐ? ⌝ · (⌜ ⌞ r₂ ⌟ ⌝ + q₁))              ≈⟨ ≈ᶜ-refl ∙ ·-distribˡ-+ _ _ _ ⟩
          θ₂ +ᶜ η₂ ∙ (⌜ 𝟘ᵐ? ⌝ · ⌜ ⌞ r₂ ⌟ ⌝ + ⌜ 𝟘ᵐ? ⌝ · q₁)      ≈˘⟨ ≈ᶜ-refl ∙ +-congʳ (⌜ᵐ·⌝ 𝟘ᵐ?) ⟩
          θ₂ +ᶜ η₂ ∙ ⌜ 𝟘ᵐ? ᵐ· r₂ ⌝ + ⌜ 𝟘ᵐ? ⌝ · q₁               ≈˘⟨ +ᶜ-congʳ (+ᶜ-identityˡ _) ∙
                                                                   +-congʳ (+-identityʳ _) ⟩
          (𝟘ᶜ +ᶜ θ₂) +ᶜ η₂ ∙ (⌜ 𝟘ᵐ? ᵐ· r₂ ⌝ + 𝟘) + ⌜ 𝟘ᵐ? ⌝ · q₁ ∎
    in  sub-≈ᶜ (natrec-no-nr-glbₘ
              (▸vecrec-nil ▸nl ▸P ok₁)
              (▸vecrec-cons ▸cs ▸P r₂-GLB ok₂)
              ▸k ▸Π′ r₁-GLB θ₁-GLB
            ∘ₘ ▸xs)
            (begin
              θ₁ +ᶜ r₁ ·ᶜ δ₁ +ᶜ r₂ ·ᶜ δ₂   ≈˘⟨ +ᶜ-assoc _ _ _ ⟩
              (θ₁ +ᶜ r₁ ·ᶜ δ₁) +ᶜ r₂ ·ᶜ δ₂ ≈⟨ +ᶜ-congʳ (+ᶜ-comm _ _) ⟩
              (r₁ ·ᶜ δ₁ +ᶜ θ₁) +ᶜ r₂ ·ᶜ δ₂ ∎)

------------------------------------------------------------------------
-- Inversion lemmas for usage

opaque
  unfolding Vec′

  -- A usage inversion lemma for Vec′

  inv-usage-Vec′ :
    ⦃ no-nr : Nr-not-available-GLB ⦄ →
    γ ▸[ m ] Vec′ l A k →
    ∃₅ λ δ η θ δ′ η′ → δ ▸[ m ] k × η ▸[ m ᵐ· p ] A ×
      Greatest-lower-boundᶜ θ (nrᵢᶜ 𝟙 δ′ η′) ×
      γ ≤ᶜ δ +ᶜ θ × δ′ ≤ᶜ 𝟘ᶜ × η′ ≤ᶜ η
  inv-usage-Vec′ {γ} {m} ▸Vec =
    let δ , η , θ , φ , q , χ , ▸⊤ , ▸Σ , ▸k , ▸U
          , γ≤ , q-GLB , χ-GLB = inv-usage-natrec-no-nr-glb ▸Vec
        invUsageΠΣ {δ = δ′} {η = η′} ▸A ▸x1 η≤ = inv-usage-ΠΣ ▸Σ
        open ≤ᶜ-reasoning
    in  _ , _ , _ , _ , _ , ▸k  , wkUsage⁻¹ ▸A , χ-GLB
          , (begin
              γ            ≤⟨ γ≤ ⟩
              q ·ᶜ θ +ᶜ χ  ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneˡ (nrᵢ-GLB-≤₀ q-GLB)) ⟩
              𝟙 ·ᶜ θ +ᶜ χ  ≈⟨  +ᶜ-congʳ (·ᶜ-identityˡ _) ⟩
              θ +ᶜ χ ∎)
          , inv-usage-Unit ▸⊤
          , (begin
              η                                  ≤⟨ tailₘ-monotone (tailₘ-monotone η≤) ⟩
              tailₘ (tailₘ (δ′ +ᶜ η′))           ≤⟨ tailₘ-monotone (tailₘ-monotone (+ᶜ-monotoneʳ {η = δ′}
                                                     (tailₘ-monotone (inv-usage-var ▸x1)))) ⟩
              tailₘ (tailₘ (δ′ +ᶜ (𝟘ᶜ ∙ ⌜ m ⌝))) ≈⟨ tailₘ-cong (tailₘ-distrib-+ᶜ δ′ (𝟘ᶜ ∙ ⌜ m ⌝)) ⟩
              tailₘ (tailₘ δ′ +ᶜ 𝟘ᶜ)             ≈⟨ tailₘ-cong (+ᶜ-identityʳ (tailₘ δ′)) ⟩
              tailₘ (tailₘ δ′)                   ≡⟨⟩
              wkConₘ⁻¹ id (tailₘ (tailₘ δ′))     ≈˘⟨ wkConₘ⁻¹-step (tailₘ δ′) ⟩
              wkConₘ⁻¹ (step id) (tailₘ δ′)      ≈˘⟨ wkConₘ⁻¹-step δ′ ⟩
              wkConₘ⁻¹ (step (step id)) δ′       ∎)

opaque
  unfolding nil′

  -- A usage inversion lemma for nil′ when weak unit and Σ-types are used

  inv-usage-nil′ʷ :
    s ≡ 𝕨 → γ ▸[ m ] nil′ l A → γ ≤ᶜ 𝟘ᶜ
  inv-usage-nil′ʷ refl ▸nil = inv-usage-starʷ ▸nil

opaque
  unfolding nil′

  -- A usage inversion lemma for nil′ when strong unit and Σ-types are used

  inv-usage-nil′ˢ :
    s ≡ 𝕤 → γ ▸[ m ] nil′ l A →
    ∃ λ δ → γ ≤ᶜ ⌜ m ⌝ ·ᶜ δ × (¬ Starˢ-sink → 𝟘ᶜ ≈ᶜ δ)
  inv-usage-nil′ˢ refl ▸nil =
    let invUsageStarˢ γ≤ 𝟘ᶜ≈ = inv-usage-starˢ ▸nil
    in  _ , γ≤ , 𝟘ᶜ≈

opaque
  unfolding cons′

  -- A usage inversion lemma for cons′ when weak unit and Σ-types are used

  inv-usage-cons′ʷ :
    s ≡ 𝕨 → γ ▸[ m ] cons′ A k h t →
    ∃₂ λ δ η → δ ▸[ m ᵐ· p ] h × η ▸[ m ] t × γ ≤ᶜ p ·ᶜ δ +ᶜ η
  inv-usage-cons′ʷ refl ▸cons =
    let invUsageProdʷ ▸h ▸t γ≤ = inv-usage-prodʷ ▸cons
    in  _ , _ , ▸h , ▸t , γ≤

opaque
  unfolding cons′

  -- A usage inversion lemma for cons′ when strong unit and Σ-types are used

  inv-usage-cons′ˢ :
    s ≡ 𝕤 → γ ▸[ m ] cons′ A k h t →
    ∃₂ λ δ η → δ ▸[ m ᵐ· p ] h × η ▸[ m ] t × γ ≤ᶜ p ·ᶜ δ ∧ᶜ η
  inv-usage-cons′ˢ refl ▸cons =
    let invUsageProdˢ ▸h ▸t γ≤ = inv-usage-prodˢ ▸cons
    in  _ , _ , ▸h , ▸t , γ≤

opaque
  unfolding vecrec-nil

  -- A usage inversion lemma for vecrec-nil

  inv-usage-vecrec-nil :
    γ ▸[ m ] vecrec-nil l r q P nl →
    ∃₂ λ δ η → δ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] P [ consSubst (wk1Subst idSubst) zero ⇑ ] ×
      η ▸[ m ] nl × Unitrec-allowed m r q × γ ≤ᶜ η
  inv-usage-vecrec-nil {γ} {r} ▸λur =
    let invUsageLam {δ} ▸ur γ≤ = inv-usage-lam ▸λur
        invUsageUnitrec {δ = η′} {η = η} ▸x0 ▸nl ▸P ok δ≤ = inv-usage-unitrec ▸ur
        open ≤ᶜ-reasoning
    in _ , _ , ▸P , wkUsage⁻¹ ▸nl , ok , (begin
        γ                          ≤⟨ γ≤ ⟩
        δ                          ≤⟨ tailₘ-monotone δ≤ ⟩
        tailₘ (r ·ᶜ η′ +ᶜ η)       ≈⟨ tailₘ-distrib-+ᶜ (r ·ᶜ η′) η ⟩
        tailₘ (r ·ᶜ η′) +ᶜ tailₘ η ≈⟨ +ᶜ-congʳ (tailₘ-distrib-·ᶜ _ η′) ⟩
        r ·ᶜ tailₘ η′ +ᶜ tailₘ η   ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (tailₘ-monotone (inv-usage-var ▸x0))) ⟩
        r ·ᶜ 𝟘ᶜ +ᶜ tailₘ η         ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
        𝟘ᶜ +ᶜ tailₘ η              ≈⟨ +ᶜ-identityˡ _ ⟩
        tailₘ η                    ≈˘⟨ wkConₘ⁻¹-step η ⟩
        wkConₘ⁻¹ (step id) η       ∎)

opaque
  unfolding vecrec-cons

  inv-usage-vecrec-cons :
    γ ▸[ m ] vecrec-cons r q P cs →
    ∃₂ λ δ₁ δ₂ →
    δ₁ ∙ ⌜ m ⌝ · r · p ∙ ⌜ m ⌝ · r ▸[ m ] cs [ consSubst (consSubst (consSubst (consSubst (wkSubst 5 idSubst)
                                                (var x4)) (var x1)) (var x0)) (var x3 ∘⟨ r ⟩ var x0) ] ×
    δ₂ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] P [ consSubst (wkSubst 3 idSubst) (suc (var x2)) ⇑ ] ×
    Prodrec-allowed m r p q ×
    γ ∙ ⌜ m ⌝ · r ≤ᶜ δ₁ +ᶜ (𝟘ᶜ ∙ ⌜ m ⌝ · r)
  inv-usage-vecrec-cons {γ} {m} {r} ▸λpr =
    let invUsageLam {δ = γ′} ▸pr γ≤γ′ = inv-usage-lam ▸λpr
        invUsageProdrec {δ} {η} {θ} ▸x0 ▸cs[] ▸P[] ok γ′≤ = inv-usage-prodrec ▸pr
        open ≤ᶜ-reasoning
    in  _ , _ , ▸cs[] , ▸P[] , ok , (begin
      γ ∙ ⌜ m ⌝ · r                   ≤⟨ γ≤γ′ ∙ ≤-refl ⟩
      γ′ ∙ ⌜ m ⌝ · r                  ≤⟨ γ′≤ ⟩
      r ·ᶜ δ +ᶜ η                     ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (inv-usage-var ▸x0)) ⟩
      r ·ᶜ (𝟘ᶜ ∙ ⌜ m ᵐ· r ⌝) +ᶜ η     ≡⟨⟩
      (r ·ᶜ 𝟘ᶜ ∙ r · ⌜ m ᵐ· r ⌝) +ᶜ η ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _ ∙ ·⌜ᵐ·⌝ m) ⟩
      (𝟘ᶜ ∙ r · ⌜ m ⌝) +ᶜ η           ≈˘⟨ +ᶜ-congʳ (≈ᶜ-refl ∙ ⌜⌝-·-comm m) ⟩
      (𝟘ᶜ ∙ ⌜ m ⌝ · r) +ᶜ η           ≈⟨ +ᶜ-comm _ _ ⟩
      η +ᶜ (𝟘ᶜ ∙ ⌜ m ⌝ · r)           ∎)

opaque
  unfolding vecrec′

  -- A usage inversion lemma for vecrec′.
  -- If a kind of inversion lemma for substitution is proved then this can
  -- perhaps be improved.

  inv-usage-vecrec′ :
    ⦃ no-nr : Nr-not-available-GLB ⦄ →
    s ≡ 𝕨 → γ ▸[ m ] vecrec′ l p₁ p₄ r₁ q₁ q₂ A P nl cs k xs →
    ∃₁₀ λ δ₁ δ₁′ δ₂ δ₂′ η₁ η₂ θ₁ θ₁′ θ₁″ θ₂ → ∃₃ λ x χ φ →
      wkConₘ⁻¹ (step id) θ₁ ▸[ 𝟘ᵐ? ] A ×
      θ₂ ∙ ⌜ 𝟘ᵐ? ⌝ · q₂ ▸[ 𝟘ᵐ? ] P ×
      δ₁ ▸[ m ] nl ×
      δ₂ ∙ ⌜ m ⌝ · r₁ · p ∙ ⌜ m ⌝ · r₁ ▸[ m ]
        cs [ consSubst (consSubst (consSubst (consSubst (wkSubst 5 idSubst)
               (var x4)) (var x1)) (var x0)) (var x3 ∘⟨ r₁ ⟩ var x0) ] ×
      η₁ ▸[ m ] k ×
      η₂ ▸[ m ᵐ· r₁ ] xs ×
      Unitrec-allowed m r₁ q₂ ×
      Prodrec-allowed m r₁ p q₂ ×
      Greatest-lower-bound x (nrᵢ p₄ 𝟙 p₁) ×
      Greatest-lower-boundᶜ χ (nrᵢᶜ p₄ δ₁′ δ₂′) ×
      Greatest-lower-boundᶜ φ (nrᵢᶜ 𝟙 θ₁′ θ₁″) ×
      γ ≤ᶜ x ·ᶜ η₁ +ᶜ χ +ᶜ r₁ ·ᶜ η₂ ×
      δ₁′ ≤ᶜ δ₁ ×
      δ₂′ ∙ ⌜ m ⌝ · p₁ ∙ ⌜ m ⌝ · p₄ ∙ ⌜ m ⌝ · r₁ ≤ᶜ δ₂ +ᶜ (𝟘ᶜ ∙ ⌜ m ⌝ · r₁) ×
      θ₁′ ≤ᶜ 𝟘ᶜ ×
      θ₁″ ≤ᶜ θ₁
  inv-usage-vecrec′ {γ} {r₁} refl ▸vr =
    let invUsageApp {δ} {η = η₂} ▸nr ▸xs γ≤ = inv-usage-app ▸vr
        _ , _ , θ , _ , x , χ
          , ▸vrn , ▸vrc , ▸k , ▸ΠVP , δ≤ , x-GLB , χ-GLB = inv-usage-natrec-no-nr-glb ▸nr
        invUsageΠΣ ▸V ▸P φ≤ = inv-usage-ΠΣ ▸ΠVP
        _ , _ , _ , _ , _ , ▸x0 , ▸A , θ′-GLB , le₁ , le₂ , le₃ = inv-usage-Vec′ ▸V
        _ , _ , _ , ▸nl , ok₁ , le₄ = inv-usage-vecrec-nil ▸vrn
        _ , _ , ▸cs[] , _ , ok₂ , le₅ = inv-usage-vecrec-cons ▸vrc
        open ≤ᶜ-reasoning
    in  _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _
          , ▸-cong (trans (cong (_ᵐ· p) ᵐ·-zeroˡ) ᵐ·-zeroˡ) (wkUsage⁻¹ ▸A)
          , ▸P , ▸nl , ▸cs[] , ▸k , ▸xs
          , ok₁ , ok₂ , x-GLB , χ-GLB , θ′-GLB
          , (begin
              γ                        ≤⟨ γ≤ ⟩
              δ +ᶜ r₁ ·ᶜ η₂             ≤⟨ +ᶜ-monotoneˡ δ≤ ⟩
              (x ·ᶜ θ +ᶜ χ) +ᶜ r₁ ·ᶜ η₂ ≈⟨ +ᶜ-assoc _ _ _ ⟩
              x ·ᶜ θ +ᶜ χ +ᶜ r₁ ·ᶜ η₂   ∎)
          , le₄ , le₅ , le₂ , le₃
