------------------------------------------------------------------------
-- Properties related to usage and Id
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions

module Graded.Derived.Identity
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (UR : Usage-restrictions 𝕄 𝐌)
  where

open Modality 𝕄
open IsMode 𝐌
open Usage-restrictions UR

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Substitution.Properties UR
open import Graded.Usage UR
open import Graded.Usage.Erased-matches
open import Graded.Usage.Properties UR
open import Graded.Usage.Weakening UR

open import Definition.Untyped M
open import Definition.Untyped.Identity 𝕄

open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≡_)
import Tools.Reasoning.PartialOrder
open import Tools.Relation

private variable
  n                    : Nat
  A B t u v w          : Term _
  p p′                 : M
  γ₁ γ₂ γ₃ γ₄ γ₅ γ₆ γ₇ : Conₘ _
  m m₁ m₂ m₃ m₄        : Mode
  sem                  : Some-erased-matches

opaque
  unfolding subst

  -- A usage rule for subst.

  ▸subst :
    γ₁ ▸[ 𝟘ᵐ ] A →
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
    γ₁ ▸[ m₁ ] A →
    γ₂ ∙ 𝟘 ▸[ m ] B →
    γ₃ ▸[ m₂ ] t →
    γ₄ ▸[ m₃ ] u →
    γ₅ ▸[ m₄ ] v →
    γ₆ ▸[ m ] w →
    ω ·ᶜ (γ₂ +ᶜ γ₆) ▸[ m ] subst 𝟘 A B t u v w
  ▸subst-𝟘 ≡not-none ▸A ▸B ▸t ▸u ▸v ▸w =
    J₀ₘ₁-generalised ≡not-none PE.refl PE.refl ▸A ▸t
      (wkUsage (step id) ▸B) ▸w ▸u ▸v

opaque
  unfolding cong

  -- A usage rule for cong.

  ▸cong :
    γ₁ ▸[ 𝟘ᵐ ] A →
    γ₂ ▸[ m ] t →
    γ₃ ▸[ m ] u →
    γ₄ ▸[ m ] B →
    γ₅ ∙ ⌜ m ⌝ · p ▸[ m ] v →
    γ₆ ▸[ m ] w →
    (Id-erased →
     γ₇ ∙ ⌜ m ⌝ · p ≤ᶜ 𝟘ᶜ) →
    (¬ Id-erased →
     γ₇ ≤ᶜ (⌜ m ⌝ · p) ·ᶜ γ₂ +ᶜ γ₄ +ᶜ (𝟙 + 𝟙) ·ᶜ γ₅) →
    ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₆ +ᶜ γ₇) ▸[ m ] cong p A t u B v w
  ▸cong
    {γ₂} {m} {t} {γ₃} {γ₄} {γ₅} {p} {γ₆} {γ₇}
    ▸A ▸t ▸u ▸B ▸v ▸w hyp₁ hyp₂ =
    case ▸→▸[ᵐ·] ▸t of λ
      (γ₂′ , ▸t′ , pγ₂≈pγ₂′) →
    sub
      (▸subst ▸A
         (Idₘ-generalised (wkUsage (step id) ▸B)
            (wkUsage (step id) $ sgSubstₘ-lemma₁ ▸v ▸t′)
            ▸v
            hyp₁
            (λ not-erased → begin
               γ₇ ∙ ⌜ m ⌝ · p                                          ≤⟨ hyp₂ not-erased ∙ ≤-refl ⟩

               ((⌜ m ⌝ · p) ·ᶜ γ₂ +ᶜ γ₄ +ᶜ (𝟙 + 𝟙) ·ᶜ γ₅) ∙ ⌜ m ⌝ · p  ≈˘⟨ (≈ᶜ-trans (+ᶜ-congˡ $ +ᶜ-congʳ $ +ᶜ-comm _ _) $
                                                                            ≈ᶜ-trans (+ᶜ-congˡ $ +ᶜ-assoc _ _ _) $
                                                                            ≈ᶜ-trans (≈ᶜ-sym $ +ᶜ-assoc _ _ _) $
                                                                            ≈ᶜ-trans
                                                                              (+ᶜ-cong
                                                                                 (+ᶜ-comm _ _)
                                                                                 (≈ᶜ-sym $
                                                                                  ≈ᶜ-trans (·ᶜ-distribʳ-+ᶜ _ _ _) $
                                                                                  +ᶜ-cong (·ᶜ-identityˡ _) (·ᶜ-identityˡ _))) $
                                                                            ≈ᶜ-trans (+ᶜ-assoc _ _ _) $
                                                                            +ᶜ-congʳ $
                                                                            ≈ᶜ-trans (·ᶜ-assoc _ _ _) $
                                                                            ≈ᶜ-trans (≈ᶜ-sym $ ·ᶜ-congˡ pγ₂≈pγ₂′) $
                                                                            ≈ᶜ-sym $ ·ᶜ-assoc _ _ _) ∙
                                                                           PE.trans (+-identityˡ _) (+-identityˡ _) ⟩
               (γ₄ +ᶜ (γ₅ +ᶜ (⌜ m ⌝ · p) ·ᶜ γ₂′) +ᶜ γ₅) ∙
               𝟘 + 𝟘 + ⌜ m ⌝ · p                                       ∎))
         ▸t ▸u ▸w rflₘ)
      (begin
         ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₆ +ᶜ γ₇)        ≈˘⟨ ·ᶜ-congˡ $
                                                ≈ᶜ-trans (≈ᶜ-sym $ +ᶜ-assoc _ _ _) $
                                                ≈ᶜ-trans (+ᶜ-congʳ $ +ᶜ-comm _ _) $
                                                ≈ᶜ-trans (+ᶜ-assoc _ _ _) $
                                                +ᶜ-congˡ $
                                                ≈ᶜ-trans (≈ᶜ-sym $ +ᶜ-assoc _ _ _) $
                                                ≈ᶜ-trans (+ᶜ-congʳ $ +ᶜ-comm _ _) $
                                                ≈ᶜ-trans (+ᶜ-assoc _ _ _) $
                                                +ᶜ-congˡ $
                                                ≈ᶜ-trans (≈ᶜ-sym $ +ᶜ-assoc _ _ _) $
                                                ≈ᶜ-trans (+ᶜ-congʳ $ +ᶜ-comm _ _) $
                                                ≈ᶜ-trans (+ᶜ-assoc _ _ _) $
                                                +ᶜ-congˡ $
                                                +ᶜ-identityʳ _ ⟩
         ω ·ᶜ (γ₇ +ᶜ γ₂ +ᶜ γ₃ +ᶜ γ₆ +ᶜ 𝟘ᶜ)  ∎)
    where
    open ≤ᶜ-reasoning

opaque
  unfolding cong

  -- A usage rule for cong 𝟘.

  ▸cong-𝟘 :
    erased-matches-for-J m ≡ not-none sem →
    γ₁ ▸[ 𝟘ᵐ ] A →
    γ₂ ▸[ m ] t →
    γ₃ ▸[ m ] u →
    γ₄ ▸[ m ] B →
    γ₅ ∙ 𝟘 ▸[ m ] v →
    γ₆ ▸[ m ] w →
    (Id-erased → γ₇ ≤ᶜ 𝟘ᶜ) →
    (¬ Id-erased → γ₇ ≤ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₅) →
    ω ·ᶜ γ₇ ▸[ m ] cong 𝟘 A t u B v w
  ▸cong-𝟘 {γ₂} {γ₄} {γ₅} {γ₇} ≡not-none ▸A ▸t ▸u ▸B ▸v ▸w hyp₁ hyp₂ =
    sub-≈ᶜ
      (▸subst-𝟘 ≡not-none ▸A
        (Idₘ-generalised (wkUsage _ ▸B)
          (wkUsage _ (sgSubstₘ-lemma₃ (sub-≈ᶜ ▸v (≈ᶜ-refl ∙ ·-zeroʳ _)) ▸t)) ▸v
          (λ ok → begin
            γ₇ ∙ 𝟘 ≤⟨ hyp₁ ok ∙ ≤-refl ⟩
            𝟘ᶜ     ∎)
          (λ ok → begin
            γ₇ ∙ 𝟘                                  ≤⟨ hyp₂ ok ∙ ≤-refl ⟩
            γ₄ +ᶜ γ₅ +ᶜ γ₅ ∙ 𝟘                      ≈˘⟨ +ᶜ-congˡ (+ᶜ-congʳ (+ᶜ-identityʳ _)) ∙ +-identityʳ _ ⟩
            γ₄ +ᶜ (γ₅ +ᶜ 𝟘ᶜ) +ᶜ γ₅ ∙ 𝟘 + 𝟘          ≈˘⟨ +ᶜ-congˡ (+ᶜ-congʳ (+ᶜ-congˡ (·ᶜ-zeroˡ _))) ∙ +-identityˡ _ ⟩
            γ₄ +ᶜ (γ₅ +ᶜ 𝟘 ·ᶜ γ₂) +ᶜ γ₅ ∙ 𝟘 + 𝟘 + 𝟘 ∎))
        ▸t ▸u ▸w rflₘ)
      (·ᶜ-congˡ (≈ᶜ-sym (+ᶜ-identityʳ _)))
    where
    open ≤ᶜ-reasoning

opaque
  unfolding funext

  -- A usage rule for funext.

  ▸funext :
    ⌜ m ⌝ · p ≤ 𝟘 →
    ⌜ m ⌝ · p′ ≤ 𝟘 →
    𝟘ᶜ {n = n} ▸[ m ] funext p p′
  ▸funext {m} {p} {p′} hyp hyp′ =
    lamₘ $ lamₘ $ lamₘ $ lamₘ $ lamₘ $ sub rflₘ $ begin
      𝟘ᶜ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · p′ ∙ ⌜ m ⌝ · p′ ∙ ⌜ m ⌝ · p′ ∙ ⌜ m ⌝ · p′  ≤⟨ ≤ᶜ-refl ∙ hyp ∙ hyp′ ∙ hyp′ ∙ hyp′ ∙ hyp′ ⟩
      𝟘ᶜ                                                                  ∎
    where
    open ≤ᶜ-reasoning

opaque
  unfolding poly-funext

  -- A usage rule for poly-funext.

  ▸poly-funext :
    ⌜ m ⌝ · p ≤ 𝟘 →
    ⌜ m ⌝ · p′ ≤ 𝟘 →
    𝟘ᶜ {n = n} ▸[ m ] poly-funext p p′
  ▸poly-funext {m} {p} hyp hyp′ =
    lamₘ $ lamₘ $ sub (▸funext hyp hyp′) $ begin
      𝟘ᶜ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · p  ≤⟨ ≤ᶜ-refl ∙ hyp ∙ hyp ⟩
      𝟘ᶜ                          ∎
    where
    open ≤ᶜ-reasoning
