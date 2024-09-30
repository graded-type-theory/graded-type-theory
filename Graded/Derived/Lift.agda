------------------------------------------------------------------------
-- Some properties related to usage and Lift
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Derived.Lift
  {a} {M : Set a}
  (𝕄 : Modality M)
  (R : Usage-restrictions 𝕄)
  where

open Modality 𝕄
open Usage-restrictions R

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Derived.Sigma 𝕄 R
open import Graded.Derived.Unit R
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄
open import Graded.Substitution 𝕄 R
open import Graded.Substitution.Properties 𝕄 R
open import Graded.Usage 𝕄 R
open import Graded.Usage.Properties 𝕄 R
open import Graded.Usage.Weakening 𝕄 R

open import Definition.Untyped M hiding (lift)
open import Definition.Untyped.Lift 𝕄

open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  A t u  : Term _
  s      : Strength
  l      : Universe-level
  γ δ η  : Conₘ _
  m      : Mode
  q r r′ : M

opaque
  unfolding Lift

  -- A usage lemma for Lift.

  ▸Lift :
    γ ▸[ m ] A →
    γ ▸[ m ] Lift s l A
  ▸Lift {γ} {m} ▸A = sub
    (ΠΣₘ (▸-cong (PE.sym $ ᵐ·-identityʳ) ▸A) $
     sub Unitₘ $ begin
       𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
       𝟘ᶜ              ∎)
    (begin
       γ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
       γ +ᶜ 𝟘ᶜ  ∎)
    where
    open ≤ᶜ-reasoning

opaque
  unfolding lift

  -- A usage lemma for lift.

  ▸lift :
    (s PE.≡ 𝕤 → γ ≤ᶜ 𝟘ᶜ) →
    γ ▸[ m ] t →
    γ ▸[ m ] lift s l t
  ▸lift {γ} ≤𝟘 ▸t =
    prodₘ (▸-cong (PE.sym $ ᵐ·-identityʳ) ▸t) starₘ
      (λ _ → begin
         γ             ≈˘⟨ ·ᶜ-identityˡ _ ⟩
         𝟙 ·ᶜ γ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
         𝟙 ·ᶜ γ +ᶜ 𝟘ᶜ  ∎)
      (λ s≡𝕤 → begin
         γ             ≤⟨ ∧ᶜ-greatest-lower-bound ≤ᶜ-refl (≤𝟘 s≡𝕤) ⟩
         γ ∧ᶜ 𝟘ᶜ       ≈˘⟨ ∧ᶜ-congʳ (·ᶜ-identityˡ _) ⟩
         𝟙 ·ᶜ γ ∧ᶜ 𝟘ᶜ  ∎)
    where
    open ≤ᶜ-reasoning

opaque
  unfolding liftrec

  -- A usage lemma for liftrec.

  ▸liftrec :
    (s PE.≡ 𝕤 → ⌜ m ⌝ · r ≤ 𝟘) →
    (s PE.≡ 𝕤 → r′ ≤ ⌜ m ⌝ · r · (𝟙 + 𝟙)) →
    (s PE.≡ 𝕨 → r′ ≤ r) →
    (s PE.≡ 𝕨 → Prodrec-allowed m r 𝟙 q) →
    (s PE.≡ 𝕨 → Unitrec-allowed m r q) →
    (s PE.≡ 𝕨 → ∃ λ γ → γ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A) →
    δ ∙ ⌜ m ⌝ · r ▸[ m ] t →
    η ▸[ m ᵐ· r ] u →
    δ +ᶜ r′ ·ᶜ η ▸[ m ] liftrec r q s l A t u
  ▸liftrec {m} {r} {q} {δ} mr≤𝟘 r′≤₁ r′≤₂ ok₁ ok₂ ▸A ▸t ▸u = sub
    (▸prodrec⟨⟩ (λ _ _ → ≤-refl) r′≤₁ r′≤₂ ok₁ ▸A ▸u $
     ▸unitrec⟨⟩ ok₂
       (λ { PE.refl →
            let γ , ▸A = ▸A PE.refl in
              γ ∙ ⌜ 𝟘ᵐ? ⌝ · q ∙ 𝟘
            , sub
                (substₘ-lemma _
                   (▶-cong _
                      (λ where
                         x0     → PE.refl
                         (_ +1) → PE.refl) $
                    wf-consSubstₘ
                      (wf-wk1Substₘ _ _ $ wf-wk1Substₘ _ _ $
                       wf-wk1Substₘ _ _ wf-idSubstₘ) $
                    prodₘ var var
                      (λ _ → begin
                         ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ⌝ ·ᶜ (𝟘ᶜ ∙ 𝟙 ∙ 𝟘 ∙ 𝟙)       ≈⟨ ·ᶜ-zeroʳ _ ∙ ·-identityʳ _ ∙ ·-zeroʳ _ ∙ ·-identityʳ _ ⟩

                         𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ⌝ ∙ 𝟘 ∙
                         ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ⌝                           ≈˘⟨ ≈ᶜ-refl ∙ PE.cong ⌜_⌝ (ᵐ·-identityʳ {m = ⌞ _ ⌟}) ∙
                                                                           PE.refl ∙ PE.refl ⟩
                         𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ᵐ· 𝟙 ⌝ ∙ 𝟘 ∙
                         ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ⌝                           ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityˡ _ ⟩

                         𝟘ᶜ +ᶜ 𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ᵐ· 𝟙 ⌝ + 𝟘 ∙
                         𝟘 + 𝟘 ∙ 𝟘 + ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ⌝               ≡⟨⟩

                         (𝟘ᶜ , x2 ≔ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ᵐ· 𝟙 ⌝) +ᶜ
                         (𝟘ᶜ , x0 ≔ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ⌝)               ≈˘⟨ +ᶜ-congʳ (·ᶜ-identityˡ _) ⟩

                         𝟙 ·ᶜ (𝟘ᶜ , x2 ≔ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ᵐ· 𝟙 ⌝) +ᶜ
                         (𝟘ᶜ , x0 ≔ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · q ⌟ ⌝)               ∎)
                      (λ ()))
                   ▸A)
                (begin
                   γ ∙ ⌜ 𝟘ᵐ? ⌝ · q ∙ 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ · q                     ≈˘⟨ +ᶜ-identityˡ _ ∙ +-identityʳ _ ∙ +-identityʳ _ ∙ +-identityʳ _ ⟩

                   (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · q ∙ 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ · q) +ᶜ
                   (γ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘)                                       ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _ ∙ ·-identityʳ _ ∙ ·-zeroʳ _ ∙ ·-identityʳ _) ⟩

                   (⌜ 𝟘ᵐ? ⌝ · q) ·ᶜ (𝟘ᶜ ∙ 𝟙 ∙ 𝟘 ∙ 𝟙) +ᶜ (γ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘)  ≈˘⟨ +ᶜ-congˡ $
                                                                            ≈ᶜ-trans (wk1Substₘ-app _ γ) $ flip _≈ᶜ_._∙_ PE.refl $
                                                                            ≈ᶜ-trans (wk1Substₘ-app _ γ) $ flip _≈ᶜ_._∙_ PE.refl $
                                                                            ≈ᶜ-trans (wk1Substₘ-app _ γ) $ flip _≈ᶜ_._∙_ PE.refl $
                                                                            <*-identityˡ _ ⟩
                   (⌜ 𝟘ᵐ? ⌝ · q) ·ᶜ (𝟘ᶜ ∙ 𝟙 ∙ 𝟘 ∙ 𝟙) +ᶜ
                   γ <* wk1Substₘ (wk1Substₘ (wk1Substₘ idSubstₘ))       ∎) })
       (λ _ →
            𝟘ᶜ ∙ ⌜ m ᵐ· r ⌝
          , var
          , (begin
               δ ∙ ⌜ m ⌝ · r · 𝟙 ∙ ⌜ m ⌝ · r                       ≈⟨ ≈ᶜ-refl ∙ PE.cong (_ ·_) (·-identityʳ _) ∙ ⌜⌝-·-comm m ⟩
               δ ∙ ⌜ m ⌝ · r ∙ r · ⌜ m ⌝                           ≈˘⟨ ≈ᶜ-refl ∙ ·⌜ᵐ·⌝ m ⟩
               δ ∙ ⌜ m ⌝ · r ∙ r · ⌜ m ᵐ· r ⌝                      ≈˘⟨ +ᶜ-identityˡ _ ∙ +-identityʳ _ ⟩
               (𝟘ᶜ ∙ r · ⌜ m ᵐ· r ⌝) +ᶜ (δ ∙ ⌜ m ⌝ · r ∙ 𝟘)        ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _ ∙ PE.refl) ⟩
               r ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ m ᵐ· r ⌝) +ᶜ (δ ∙ ⌜ m ⌝ · r ∙ 𝟘)  ∎))
       (λ s≡𝕤 → begin
          δ ∙ ⌜ m ⌝ · r · 𝟙 ∙ ⌜ m ⌝ · r  ≈⟨ ≈ᶜ-refl ∙ PE.cong (_ ·_) (·-identityʳ _) ∙ PE.refl ⟩
          δ ∙ ⌜ m ⌝ · r ∙ ⌜ m ⌝ · r      ≤⟨ ≤ᶜ-refl ∙ mr≤𝟘 s≡𝕤 ⟩
          δ ∙ ⌜ m ⌝ · r ∙ 𝟘              ∎)
       (wkUsage _ ▸t))
    (≤ᶜ-reflexive (+ᶜ-comm _ _))
    where
    open ≤ᶜ-reasoning
