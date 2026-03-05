------------------------------------------------------------------------
-- Some properties related to usage and Erased
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions
open import Definition.Untyped.NotParametrised using (Strength)

module Graded.Derived.Erased.Usage
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (R : Usage-restrictions 𝕄 𝐌)
  (s : Strength)
  where

open Modality 𝕄
open IsMode 𝐌
open Usage-restrictions R

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Substitution R
open import Graded.Substitution.Properties R
open import Graded.Usage R
open import Graded.Usage.Inversion R
open import Graded.Usage.Properties R
open import Graded.Usage.Weakening R

open import Definition.Untyped M
open import Definition.Untyped.Erased 𝕄 s
open import Definition.Untyped.Properties M
import Graded.Derived.Erased.Usage.Eta R as Eta
import Graded.Derived.Erased.Usage.No-eta R as NoEta
open import Graded.Derived.Identity R
open import Graded.Derived.Sigma R
open import Graded.Derived.Unit R

open import Tools.Bool using (T)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Product as Σ
open import Tools.PropositionalEquality as PE using (_≡_; _≢_)
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private variable
  A B t u v w             : Term _
  l                       : Lvl _
  γ γ₁ γ₂ γ₃ γ₄ γ₅ γ₆ δ η : Conₘ _
  p                       : M
  m                       : Mode
  ok                      : T _

------------------------------------------------------------------------
-- Usage rules

opaque
  unfolding Erased

  -- A usage rule for Erased.

  ▸Erased :
    γ ▸[ 𝟘ᵐ ] l →
    δ ▸[ 𝟘ᵐ ] A →
    𝟘ᶜ ▸[ m ] Erased l A
  ▸Erased {δ} {m} ▸l ▸A = sub
    (ΠΣₘ (▸-cong (PE.sym (ᵐ·-zeroʳ _)) ▸A)
       (sub (Liftₘ (wkUsage _ ▸l) Unitₘ)
          (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
             𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
             𝟘ᶜ              ∎)))
    (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       𝟘ᶜ            ≈˘⟨ +ᶜ-identityʳ _ ⟩
       𝟘ᶜ +ᶜ 𝟘ᶜ      ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
       𝟘 ·ᶜ δ +ᶜ 𝟘ᶜ  ∎)

opaque
  unfolding [_]

  ▸[] : γ ▸[ 𝟘ᵐ ] t → 𝟘ᶜ ▸[ m ] [ t ]
  ▸[] {(n)} {γ} {t} {m} ▸t = lemma s PE.refl
    where
    open Tools.Reasoning.PartialOrder (≤ᶜ-poset {n})
    lemma : ∀ s′ → s PE.≡ s′ → 𝟘ᶜ ▸[ m ] [ t ]
    lemma 𝕤 PE.refl = sub
      (prodˢₘ (▸-cong (PE.sym (ᵐ·-zeroʳ m)) ▸t) (liftₘ starₘ))
      (begin
         𝟘ᶜ             ≈˘⟨ ∧ᶜ-idem _ ⟩
         𝟘ᶜ ∧ᶜ 𝟘ᶜ       ≈˘⟨ ∧ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
         𝟘 ·ᶜ γ ∧ᶜ 𝟘ᶜ  ∎)
    lemma 𝕨 PE.refl = sub
      (prodʷₘ (▸-cong (PE.sym (ᵐ·-zeroʳ m)) ▸t) (liftₘ starₘ))
      (begin
         𝟘ᶜ             ≈˘⟨ +ᶜ-identityˡ _ ⟩
         𝟘ᶜ +ᶜ 𝟘ᶜ       ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
         𝟘 ·ᶜ γ +ᶜ 𝟘ᶜ  ∎)

opaque
  unfolding erased

  -- A usage rule for erased.

  ▸erased′ :
    (s ≡ 𝕨 → Trivialᵐ → Trivial) →
    (s ≡ 𝕨 → Prodrec-allowed 𝟘ᵐ (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    (s ≡ 𝕤 → Trivialᵐ → 𝟘 ≤ 𝟙) →
    γ ▸[ 𝟘ᵐ ] t →
    (s ≡ 𝕨 → ∃ λ δ → δ ▸[ 𝟘ᵐ ] A) →
    𝟘ᶜ ▸[ 𝟘ᵐ ] erased A t
  ▸erased′ {γ} trivial ok 𝟘≤𝟙 ▸t ▸A =
    case PE.singleton s of λ where
      (𝕨 , PE.refl) →
        NoEta.▸erased′ (trivial PE.refl) ▸t (▸A PE.refl .proj₂) (ok PE.refl)
      (𝕤 , PE.refl) →
        Eta.▸erased′ (𝟘≤𝟙 PE.refl) ▸t

opaque
  unfolding erased

  -- Another usage rule for erased.

  ▸erased :
    ¬ Trivialᵐ →
    γ ▸[ 𝟘ᵐ ] t →
    (s ≡ 𝕨 → ∃ λ δ → δ ▸[ 𝟘ᵐ ] A) →
    (s ≡ 𝕨 → Prodrec-allowed 𝟘ᵐ (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    𝟘ᶜ ▸[ 𝟘ᵐ ] erased A t
  ▸erased 𝟙ᵐ≢𝟘ᵐ ▸t ▸A ok = case PE.singleton s of λ where
    (𝕤 , PE.refl) → Eta.▸erased 𝟙ᵐ≢𝟘ᵐ ▸t
    (𝕨 , PE.refl) → NoEta.▸erased 𝟙ᵐ≢𝟘ᵐ ▸t (▸A PE.refl .proj₂) (ok PE.refl)

opaque
  unfolding erasedrec is-𝕨

  -- A usage rule for erasedrec.

  ▸erasedrec :
    (s ≡ 𝕤 → Trivialᵐ → Trivial) →
    (s ≡ 𝕨 → Prodrec-allowed m 𝟙 𝟘 p) →
    (s ≡ 𝕨 → Unitrec-allowed m 𝟙 p) →
    (s ≡ 𝕨 → ∃ λ γ → γ ∙ ⌜ 𝟘ᵐ ⌝ · p ▸[ 𝟘ᵐ ] B) →
    δ ∙ 𝟘 ▸[ m ] t →
    η ▸[ m ᵐ· is-𝕨 ] u →
    δ +ᶜ η ▸[ m ] erasedrec p B t u
  ▸erasedrec {m} {p} {δ} {η} hyp₁ P-ok U-ok ▸B ▸t ▸u = sub
    (▸prodrec⟨⟩
      lemma₅
       (λ { PE.refl → lemma₁ })
       (λ _ → ≤-refl)
       (λ { PE.refl → P-ok PE.refl })
       ▸B ▸u
       (▸unitrec⟨⟩ U-ok
          (λ s≡𝕨 →
             let γ , ▸B = ▸B s≡𝕨 in
               γ ∙ 𝟘 ∙ 𝟘
             , sub
                 (substₘ-lemma
                    (▶-cong _
                       (λ where
                          x0     → PE.refl
                          (_ +1) → PE.refl) $
                     wf-consSubstₘ
                       (wf-wk1Substₘ _ _ $ wf-wk1Substₘ _ _ $
                        wf-wk1Substₘ _ _ wf-idSubstₘ) $
                     prodₘ var (liftₘ var)
                       (λ _ → begin
                          ⌜ ⌞ ⌜ 𝟘ᵐ ⌝ · p ⌟ ⌝ ·ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝)         ≈⟨ ·ᶜ-congʳ lemma₂ ⟩

                          ⌜ 𝟘ᵐ ⌝ ·ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝)                     ≈⟨ ·ᶜ-zeroʳ _ ∙ ·-idem-⌜⌝ 𝟘ᵐ ⟩

                          𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝                                  ≈˘⟨ ≈ᶜ-refl ∙ lemma₂ ⟩

                          𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ ⌝ · p ⌟ ⌝                      ≈˘⟨ ≈ᶜ-trans (+ᶜ-congʳ $ ·ᶜ-zeroˡ _) $
                                                                            +ᶜ-identityˡ _ ⟩
                          𝟘 ·ᶜ (𝟘ᶜ , x2 ≔ ⌜ ⌞ ⌜ 𝟘ᵐ ⌝ · p ⌟ ᵐ· 𝟘 ⌝) +ᶜ
                          (𝟘ᶜ , x0 ≔ ⌜ ⌞ ⌜ 𝟘ᵐ ⌝ · p ⌟ ⌝)               ∎)
                       (λ s≡𝕤 → case PE.trans (PE.sym s≡𝕤) s≡𝕨 of λ ()))
                    ▸B)
                 (begin
                    γ ∙ 𝟘 ∙ 𝟘 ∙ ⌜ 𝟘ᵐ ⌝ · p                          ≈˘⟨ +ᶜ-identityˡ _ ∙ +-identityʳ _ ⟩

                    (𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · p) +ᶜ (γ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘)            ≈˘⟨ +ᶜ-cong
                                                                           (·ᶜ-zeroʳ _ ∙ lemma₃)
                                                                           (≈ᶜ-trans (wk1Substₘ-app _ γ)
                                                                              (≈ᶜ-trans (wk1Substₘ-app _ γ)
                                                                                 (≈ᶜ-trans (wk1Substₘ-app _ γ)
                                                                                    (<*-identityˡ _ ∙
                                                                                     PE.refl) ∙
                                                                                  PE.refl) ∙
                                                                              PE.refl)) ⟩
                    (⌜ 𝟘ᵐ ⌝ · p) ·ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝) +ᶜ
                    γ <* wk1Substₘ (wk1Substₘ (wk1Substₘ idSubstₘ))  ∎))
          (λ where
             PE.refl →
                 𝟘ᶜ ∙ ⌜ m ᵐ· 𝟙 ⌝
               , lowerₘ var
               , (begin
                    δ ∙ ⌜ m ⌝ · 𝟙 · 𝟘 ∙ ⌜ m ⌝ · 𝟙          ≈⟨ ≈ᶜ-refl ∙ PE.trans (·-congˡ $ ·-zeroʳ _) (·-zeroʳ _) ∙
                                                              ·-identityʳ _ ⟩
                    δ ∙ 𝟘 ∙ ⌜ m ⌝                          ≈˘⟨ +ᶜ-identityˡ _ ∙ +-identityʳ _ ⟩
                    (𝟘ᶜ ∙ ⌜ m ⌝) +ᶜ (δ ∙ 𝟘 ∙ 𝟘)            ≈˘⟨ +ᶜ-congʳ $
                                                               ≈ᶜ-trans (·ᶜ-identityˡ _) $
                                                               ≈ᶜ-refl ∙ PE.cong ⌜_⌝ (ᵐ·-identityʳ {m = m}) ⟩
                    𝟙 ·ᶜ (𝟘ᶜ ∙ ⌜ m ᵐ· 𝟙 ⌝) +ᶜ (δ ∙ 𝟘 ∙ 𝟘)  ∎))
          (λ where
             PE.refl → begin
               δ ∙ ⌜ m ⌝ · 𝟘 · 𝟘 ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ PE.trans (·-congˡ $ ·-zeroʳ _) (·-zeroʳ _) ∙ ·-zeroʳ _ ⟩
               δ ∙ 𝟘 ∙ 𝟘                      ∎)
          (wkUsage _ ▸t)))
    lemma₄
    where
    lemma₁ : 𝟘 ≤ ⌜ m ⌝ · 𝟘 · (𝟙 + 𝟘)
    lemma₁ = begin
      𝟘                    ≈˘⟨ PE.trans (·-congˡ $ ·-zeroˡ _) (·-zeroʳ _) ⟩
      ⌜ m ⌝ · 𝟘 · (𝟙 + 𝟘)  ∎
      where
      open Tools.Reasoning.PartialOrder ≤-poset

    lemma₂ : ⌜ ⌞ ⌜ 𝟘ᵐ ⌝ · p ⌟ ⌝ ≡ ⌜ 𝟘ᵐ ⌝
    lemma₂ = ⌜⌝-cong (⌜𝟘ᵐ⌝≡𝟘→ (λ ⌜𝟘ᵐ⌝ → begin
      ⌞ ⌜ 𝟘ᵐ ⌝ · p ⌟ ≡⟨ ⌞⌟-cong (·-congʳ ⌜𝟘ᵐ⌝) ⟩
      ⌞ 𝟘 · p ⌟      ≡⟨ ⌞⌟-cong (·-zeroˡ _) ⟩
      ⌞ 𝟘 ⌟          ≡⟨ ⌞𝟘⌟ ⟩
      𝟘ᵐ             ∎))
      where
      open Tools.Reasoning.PropositionalEquality

    lemma₃ : (⌜ 𝟘ᵐ ⌝ · p) · ⌜ 𝟘ᵐ ⌝ ≡ ⌜ 𝟘ᵐ ⌝ · p
    lemma₃ = begin
      (⌜ 𝟘ᵐ ⌝ · p) · ⌜ 𝟘ᵐ ⌝ ≡˘⟨ ⌜⌝-·-comm _ ⟩
      ⌜ 𝟘ᵐ ⌝ · ⌜ 𝟘ᵐ ⌝ · p   ≡⟨ ·-idem-⌜⌝′ ⟩
      ⌜ 𝟘ᵐ ⌝ · p            ∎
      where
      open Tools.Reasoning.PropositionalEquality

    lemma₅ : s PE.≡ 𝕤 → ⌜ m ᵐ· is-𝕨 · 𝟘 ⌝ · 𝟘 ≤ ⌜ m ᵐ· is-𝕨 · 𝟘 ⌝
    lemma₅ s≡𝕤 = begin
      ⌜ m ᵐ· is-𝕨 · 𝟘 ⌝ · 𝟘 ≈⟨ ·-zeroʳ _ ⟩
      𝟘 ≈˘⟨ lemma ⟩
      ⌜ 𝟘ᵐ ⌝ ≈˘⟨ ⌜⌝-cong (ᵐ·-zeroʳ _) ⟩
      ⌜ m ᵐ· 𝟘 ⌝ ≈˘⟨ ⌜⌝-cong (ᵐ·-congˡ (·-zeroʳ _)) ⟩
      ⌜ m ᵐ· is-𝕨 · 𝟘 ⌝ ∎
      where
      lemma : ⌜ 𝟘ᵐ ⌝ ≡ 𝟘
      lemma =
        case trivialᵐ? of λ where
          (yes 𝟙ᵐ≡𝟘ᵐ) → ≡-trivial (hyp₁ s≡𝕤 𝟙ᵐ≡𝟘ᵐ)
          (no 𝟙ᵐ≢𝟘ᵐ) → ⌜𝟘ᵐ⌝ 𝟙ᵐ≢𝟘ᵐ
      open ≤-reasoning

    open ≤ᶜ-reasoning

    lemma₄ : δ +ᶜ η ≤ᶜ is-𝕨 ·ᶜ η +ᶜ δ
    lemma₄ with PE.singleton s
    … | 𝕨 , PE.refl = begin
      δ +ᶜ η       ≈⟨ +ᶜ-comm _ _ ⟩
      η +ᶜ δ       ≈˘⟨ +ᶜ-congʳ $ ·ᶜ-identityˡ _ ⟩
      𝟙 ·ᶜ η +ᶜ δ  ∎
    … | 𝕤 , PE.refl = case trivialᵐ? of λ where
        (yes 𝟙ᵐ≡𝟘ᵐ) → ≈ᶜ-trivial (hyp₁ PE.refl 𝟙ᵐ≡𝟘ᵐ)
        (no 𝟙ᵐ≢𝟘ᵐ) → lemma $ ▸-𝟘ᵐ 𝟙ᵐ≢𝟘ᵐ (▸-cong (ᵐ·-zeroʳ _) ▸u)
      where
      lemma : η ≤ᶜ 𝟘ᶜ → δ +ᶜ η ≤ᶜ 𝟘 ·ᶜ η +ᶜ δ
      lemma hyp = begin
        δ +ᶜ η       ≤⟨ +ᶜ-monotoneʳ hyp ⟩
        δ +ᶜ 𝟘ᶜ      ≈˘⟨ ≈ᶜ-trans (+ᶜ-congʳ $ ·ᶜ-zeroˡ _) $
                         +ᶜ-comm _ _ ⟩
        𝟘 ·ᶜ η +ᶜ δ  ∎

opaque
  unfolding Erased-η

  -- A usage rule for Erased-η.

  ▸Erased-η :
    (Trivialᵐ → Trivial) →
    (s ≡ 𝕨 → Prodrec-allowed m 𝟙 𝟘 𝟙) →
    (s ≡ 𝕨 → Prodrec-allowed 𝟘ᵐ (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    (s ≡ 𝕨 → Unitrec-allowed m 𝟙 𝟙) →
    (s ≡ 𝕨 → ∃ λ γ → γ ▸[ 𝟘ᵐ ] l) →
    (s ≡ 𝕨 → ∃ λ γ → γ ▸[ 𝟘ᵐ ] A) →
    δ ▸[ m ᵐ· is-𝕨 ] t →
    δ ▸[ m ] Erased-η l A t
  ▸Erased-η {A} {δ} trivial P-ok₁ P-ok₂ U-ok ▸l ▸A ▸t = sub
    (▸erasedrec (λ _ → trivial) P-ok₁ U-ok
       (λ s≡𝕨 →
            𝟘ᶜ
          , Idₘ-generalised
              (▸Erased (wkUsage _ (▸l s≡𝕨 .proj₂))
                (wkUsage _ (▸A′ s≡𝕨)))
              (▸[] $ ▸erased′
                 (λ s≡𝕨 → trivial)
                 P-ok₂
                 (λ s≡𝕤 → ≡-trivial ∘→ trivial) var
                 (Σ.map _ (wkUsage _) ∘→ ▸A))
              var
              (λ _ → case trivialᵐ? of λ where
                (yes 𝟙ᵐ≡𝟘ᵐ) → ≈ᶜ-trivial (trivial 𝟙ᵐ≡𝟘ᵐ)
                (no 𝟙ᵐ≢𝟘ᵐ) → begin
                  𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · 𝟙 ≈⟨ ≈ᶜ-refl ∙ ·-identityʳ _ ⟩
                  𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝     ≈⟨ ≈ᶜ-refl ∙ ⌜𝟘ᵐ⌝ 𝟙ᵐ≢𝟘ᵐ ⟩
                  𝟘ᶜ ∙ 𝟘          ∎)
              (λ _ → begin
                 𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · 𝟙                 ≈⟨ ≈ᶜ-refl ∙ ·-identityʳ _ ⟩
                 𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝                     ≈˘⟨ ≈ᶜ-trans (+ᶜ-identityˡ _) (+ᶜ-identityˡ _) ⟩
                 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ (𝟘ᶜ , x0 ≔ ⌜ 𝟘ᵐ ⌝)  ∎))
       rflₘ
       ▸t)
    (begin
       δ        ≈˘⟨ +ᶜ-identityˡ _ ⟩
       𝟘ᶜ +ᶜ δ  ∎)
    where
    open ≤ᶜ-reasoning

    ▸A′ : s ≡ 𝕨 → 𝟘ᶜ ▸[ 𝟘ᵐ ] A
    ▸A′ s≡𝕨 = case trivialᵐ? of λ where
      (yes 𝟙ᵐ≡𝟘ᵐ) → sub (▸A s≡𝕨 .proj₂) (≈ᶜ-trivial (trivial 𝟙ᵐ≡𝟘ᵐ))
      (no 𝟙ᵐ≢𝟘ᵐ) → ▸-𝟘′ 𝟙ᵐ≢𝟘ᵐ (▸A s≡𝕨 .proj₂)

opaque
  unfolding mapᴱ

  -- A usage rule for mapᴱ.

  ▸mapᴱ′ :
    (s ≡ 𝕨 → Trivialᵐ → Trivial) →
    (s ≡ 𝕨 → Prodrec-allowed 𝟘ᵐ (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    (s ≡ 𝕤 → Trivialᵐ → 𝟘 ≤ 𝟙) →
    (s ≡ 𝕨 → ∃ λ γ₁ → γ₁ ▸[ 𝟘ᵐ ] A) →
    γ₂ ∙ ⌜ 𝟘ᵐ ⌝ · p ▸[ 𝟘ᵐ ] t →
    γ₃ ▸[ 𝟘ᵐ ] u →
    𝟘ᶜ ▸[ m ] mapᴱ A t u
  ▸mapᴱ′ trivial ok 𝟘≤𝟙 ▸A ▸t ▸u =
    ▸[] $ sgSubstₘ-lemma₃ ▸t $
      ▸erased′ trivial ok 𝟘≤𝟙 ▸u ▸A

opaque
  unfolding mapᴱ

  -- Another usage rule for mapᴱ.

  ▸mapᴱ :
    ¬ Trivialᵐ →
    (s ≡ 𝕨 → Prodrec-allowed 𝟘ᵐ (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    (s ≡ 𝕨 → ∃ λ γ₁ → γ₁ ▸[ 𝟘ᵐ ] A) →
    γ₂ ∙ 𝟘 ▸[ 𝟘ᵐ ] t →
    γ₃ ▸[ 𝟘ᵐ ] u →
    𝟘ᶜ ▸[ m ] mapᴱ A t u
  ▸mapᴱ {γ₂} 𝟙ᵐ≢𝟘ᵐ ok ▸A ▸t ▸u =
    ▸mapᴱ′ (λ _ → ⊥-elim ∘→ 𝟙ᵐ≢𝟘ᵐ) ok (λ _ → ⊥-elim ∘→ 𝟙ᵐ≢𝟘ᵐ)
      ▸A (sub ▸t $ begin
         γ₂ ∙ ⌜ 𝟘ᵐ ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
         γ₂ ∙ 𝟘           ∎)
      ▸u
    where
    open ≤ᶜ-reasoning

opaque
  unfolding substᵉ

  -- A usage rule for substᵉ.

  ▸substᵉ :
    (s ≡ 𝕨 → Trivialᵐ → Trivial) →
    (s ≡ 𝕨 → Prodrec-allowed 𝟘ᵐ (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    (s ≡ 𝕤 → Trivialᵐ → 𝟘 ≤ 𝟙) →
    []-cong-allowed-mode s m →
    γ₁ ▸[ 𝟘ᵐ ] A →
    γ₂ ∙ 𝟘 ▸[ m ] B →
    γ₃ ▸[ 𝟘ᵐ ] t →
    γ₄ ▸[ 𝟘ᵐ ] u →
    γ₅ ▸[ 𝟘ᵐ ] v →
    γ₆ ▸[ m ] w →
    ω ·ᶜ (γ₂ +ᶜ γ₆) ▸[ m ] substᵉ A B t u v w
  ▸substᵉ {m} {γ₂} {γ₆} trivial P-ok 𝟘≤𝟙 ok ▸A ▸B ▸t ▸u ▸v ▸w = sub
    (▸subst (▸Erased (level zeroᵘₘ) ▸A)
       (sub
          (substₘ-lemma
             (▶-cong _
                (λ where
                   x0     → PE.refl
                   (_ +1) → PE.refl) $
              wf-consSubstₘ (wf-wk1Substₘ _ _ wf-idSubstₘ) $
              sub (▸-cong (PE.sym ⌞𝟘⌟) $
                 ▸erased′ trivial P-ok 𝟘≤𝟙 var
                   (λ _ → _ , wkUsage (step id) ▸A))
                (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
                   ⌜ ⌞ 𝟘 ⌟ ⌝ ·ᶜ 𝟘ᶜ  ≈⟨ ·ᶜ-zeroʳ _ ⟩
                   𝟘ᶜ               ∎))
             ▸B)
          (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
             γ₂ ∙ ⌜ m ⌝ · 𝟘                       ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
             γ₂ ∙ 𝟘                               ≈˘⟨ <*-identityˡ _ ∙ PE.refl ⟩
             γ₂ <* idSubstₘ ∙ 𝟘                   ≈˘⟨ wk1Substₘ-app _ γ₂ ⟩
             γ₂ <* wk1Substₘ idSubstₘ             ≈˘⟨ ≈ᶜ-trans (+ᶜ-congʳ $ ·ᶜ-zeroˡ _) $
                                                      +ᶜ-identityˡ _ ⟩
             𝟘 ·ᶜ 𝟘ᶜ +ᶜ γ₂ <* wk1Substₘ idSubstₘ  ∎))
       (▸[] ▸t) (▸[] ▸u) ([]-congₘ (level zeroᵘₘ) ▸A ▸t ▸u ▸v ok) ▸w)
    (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       ω ·ᶜ (γ₂ +ᶜ γ₆)                    ≈˘⟨ ·ᶜ-congˡ $ +ᶜ-congˡ $
                                              ≈ᶜ-trans (+ᶜ-identityˡ _) $
                                              ≈ᶜ-trans (+ᶜ-identityˡ _) $
                                              +ᶜ-identityˡ _ ⟩
       ω ·ᶜ (γ₂ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ γ₆)  ∎)

opaque
  unfolding Jᵉ

  -- A usage rule for Jᵉ.

  ▸Jᵉ :
    (s ≡ 𝕨 → Trivialᵐ → Trivial) →
    (s ≡ 𝕨 → Prodrec-allowed 𝟘ᵐ (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    (s ≡ 𝕤 → Trivialᵐ → 𝟘 ≤ 𝟙) →
    []-cong-allowed-mode s m →
    γ₁ ▸[ 𝟘ᵐ ] A →
    γ₂ ▸[ 𝟘ᵐ ] t →
    γ₃ ∙ 𝟘 ∙ 𝟘 ▸[ m ] B →
    γ₄ ▸[ m ] u →
    γ₅ ▸[ 𝟘ᵐ ] v →
    γ₆ ▸[ 𝟘ᵐ ] w →
    ω ·ᶜ (γ₃ +ᶜ γ₄) ▸[ m ] Jᵉ A t B u v w
  ▸Jᵉ {γ₁} {γ₂} {γ₃} {γ₅} {γ₆} trivial P-ok 𝟘≤𝟙 ok ▸A ▸t ▸B ▸u ▸v ▸w =
    let 𝟘≤⌜𝟘ᵐ⌝ = case trivialᵐ? of λ where
      (yes 𝟙ᵐ≡𝟘ᵐ) →
        case PE.singleton s of λ where
          (𝕤 , PE.refl) → PE.trans (𝟘≤𝟙 _≡_.refl 𝟙ᵐ≡𝟘ᵐ) (∧-congˡ (PE.sym (⌜𝟘ᵐ⌝′ 𝟙ᵐ≡𝟘ᵐ)))
          (𝕨 , PE.refl) → ≡-trivial (trivial PE.refl 𝟙ᵐ≡𝟘ᵐ)
      (no 𝟙ᵐ≢𝟘ᵐ) → PE.sym (PE.trans (∧-congˡ (⌜𝟘ᵐ⌝ 𝟙ᵐ≢𝟘ᵐ)) (∧-idem _))
    in
    case
      (ΠΣₘ (▸-cong (PE.sym (ᵐ·-zeroʳ _)) ▸A) $
       Idₘ-generalised (wkUsage _ ▸A) (wkUsage _ ▸t) var
         (λ _ → begin
            ((γ₁ +ᶜ γ₂) ∧ᶜ 𝟘ᶜ) ∙ ⌜ 𝟘ᵐ ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
            ((γ₁ +ᶜ γ₂) ∧ᶜ 𝟘ᶜ) ∙ 𝟘            ≤⟨ ∧ᶜ-decreasingʳ _ _ ∙ ≤-refl ⟩
            𝟘ᶜ                                ∎)
         (λ _ → begin
            ((γ₁ +ᶜ γ₂) ∧ᶜ 𝟘ᶜ) ∙ ⌜ 𝟘ᵐ ⌝ · 𝟘        ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
            ((γ₁ +ᶜ γ₂) ∧ᶜ 𝟘ᶜ) ∙ 𝟘                  ≤⟨ ∧ᶜ-decreasingˡ _ _ ∙ 𝟘≤⌜𝟘ᵐ⌝ ⟩
            γ₁ +ᶜ γ₂ ∙ ⌜ 𝟘ᵐ ⌝                      ≈˘⟨ +ᶜ-congˡ (+ᶜ-identityʳ _) ∙ PE.trans (+-identityˡ _) (+-identityˡ _) ⟩
            (γ₁ ∙ 𝟘) +ᶜ (γ₂ ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝)  ∎)) of λ
      ▸Singleton →
    case (prodₘ (▸-cong (PE.sym ᵐ·-zeroˡ) ▸t) rflₘ
            (λ _ → begin
               𝟘ᶜ             ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
               𝟘 ·ᶜ γ₂        ≈˘⟨ +ᶜ-identityʳ _ ⟩
               𝟘 ·ᶜ γ₂ +ᶜ 𝟘ᶜ  ∎)
            (λ _ → begin
               𝟘ᶜ             ≈˘⟨ ∧ᶜ-idem _ ⟩
               𝟘ᶜ ∧ᶜ 𝟘ᶜ       ≈˘⟨ ∧ᶜ-congʳ $ ·ᶜ-zeroˡ _ ⟩
               𝟘 ·ᶜ γ₂ ∧ᶜ 𝟘ᶜ  ∎)) of λ
      ▸t,rfl →
    let ok′ : ⌜ 𝟘ᵐ ⌝ ≢ 𝟘 → 𝟘 ≤ 𝟙
        ok′ = case trivialᵐ? of λ where
          (yes 𝟙ᵐ≡𝟘ᵐ) → case PE.singleton s of λ where
            (𝕤 , PE.refl) → λ _ → 𝟘≤𝟙 PE.refl 𝟙ᵐ≡𝟘ᵐ
            (𝕨 , PE.refl) → λ _ → ≡-trivial (trivial PE.refl 𝟙ᵐ≡𝟘ᵐ)
          (no 𝟙ᵐ≢𝟘ᵐ) → ⊥-elim ∘→ 𝟙ᵐ≢𝟘ᵐ ∘→ ⌜𝟘ᵐ⌝≢𝟘→
        ok″ : s ≡ 𝕤 → ⌜ 𝟘ᵐ ⌝ · 𝟘 ≤ ⌜ 𝟘ᵐ ⌝
        ok″ s≡𝕤 = case trivialᵐ? of λ where
          (yes 𝟙ᵐ≡𝟘ᵐ) →
            ≤-trans (≤-reflexive (·-zeroʳ _))
              (≤-trans (𝟘≤𝟙 s≡𝕤 𝟙ᵐ≡𝟘ᵐ) (≤-reflexive (PE.sym (⌜𝟘ᵐ⌝′ 𝟙ᵐ≡𝟘ᵐ))))
          (no 𝟙ᵐ≢𝟘ᵐ) →
            ≤-reflexive (PE.trans (·-zeroʳ _) (PE.sym (⌜𝟘ᵐ⌝ 𝟙ᵐ≢𝟘ᵐ)))
    in
    ▸substᵉ trivial P-ok 𝟘≤𝟙 ok ▸Singleton
      (sub
         (flip substₘ-lemma ▸B $
          ▶-cong _
            (λ where
               x0        → PE.sym ⌞𝟘⌟
               (x0 +1)   → PE.sym ⌞𝟘⌟
               (_ +1 +1) → PE.refl) $
          wf-consSubstₘ
            (wf-consSubstₘ (wf-wk1Substₘ _ _ wf-idSubstₘ) $
             sub (▸fst⟨⟩ (λ _ → PE.sym ᵐ·-zeroˡ) P-ok (λ _ → ok′)
                    ok″ var (λ _ → wkUsage _ ▸A))
               (begin
                  ⌜ 𝟘ᵐ ⌝ ·ᶜ (𝟘ᶜ ∙ 𝟘 ∧ 𝟙)  ≈⟨ ·ᶜ-zeroʳ _ ∙ ·[𝟘∧𝟙]≡𝟘∧ ⟩
                  𝟘ᶜ ∙ 𝟘 ∧ ⌜ 𝟘ᵐ ⌝         ≈˘⟨ ∧ᶜ-idem _ ∙ PE.refl ⟩
                  𝟘ᶜ ∧ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝)     ∎)) $
          sub
            (▸snd⟨⟩ (λ _ → ᵐ·-zeroˡ) P-ok var
               (λ _ →
                  Idₘ-generalised
                    (PE.subst (_▸[_]_ _ _) (PE.sym wk[]′-[]↑) $
                     wkUsage _ ▸A)
                    (PE.subst (_▸[_]_ _ _) (PE.sym wk[]′-[]↑) $
                     wkUsage _ ▸t)
                    (▸fst⟨⟩ (λ _ → PE.sym ᵐ·-zeroˡ) P-ok (λ _ → ok′) ok″ var
                       (λ _ → wkUsage _ $ wkUsage _ ▸A))
                    (λ _ → begin
                       (((γ₁ +ᶜ γ₂) ∙ 𝟘) ∧ᶜ 𝟘ᶜ) ∙ ⌜ 𝟘ᵐ ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
                       (((γ₁ +ᶜ γ₂) ∙ 𝟘) ∧ᶜ 𝟘ᶜ) ∙ 𝟘            ≤⟨ ∧ᶜ-decreasingʳ _ _ ∙ ≤-refl ⟩
                       𝟘ᶜ                                      ∎)
                    (λ _ → begin
                       (((γ₁ +ᶜ γ₂) ∙ 𝟘) ∧ᶜ 𝟘ᶜ) ∙ ⌜ 𝟘ᵐ ⌝ · 𝟘        ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩

                       (((γ₁ +ᶜ γ₂) ∙ 𝟘) ∧ᶜ 𝟘ᶜ) ∙ 𝟘                  ≤⟨ ∧ᶜ-decreasingˡ _ _ ∙ ≤-refl ⟩

                       γ₁ +ᶜ γ₂ ∙ 𝟘 ∙ 𝟘                              ≈˘⟨ +ᶜ-identityʳ _ ⟩

                       (γ₁ +ᶜ γ₂ ∙ 𝟘 ∙ 𝟘) +ᶜ 𝟘ᶜ                      ≈˘⟨ +ᶜ-congˡ $ ∧ᶜ-idem _ ⟩

                       (γ₁ +ᶜ γ₂ ∙ 𝟘 ∙ 𝟘) +ᶜ (𝟘ᶜ ∧ᶜ 𝟘ᶜ)              ≤⟨ +ᶜ-monotoneʳ (∧ᶜ-monotoneʳ (≤ᶜ-refl ∙ 𝟘≤⌜𝟘ᵐ⌝)) ⟩

                       (γ₁ +ᶜ γ₂ ∙ 𝟘 ∙ 𝟘) +ᶜ (𝟘ᶜ ∧ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝))  ≈˘⟨ +ᶜ-congʳ (≈ᶜ-refl ∙ +-identityˡ _ ∙ +-identityˡ _) ⟩

                       ((γ₁ ∙ 𝟘 ∙ 𝟘) +ᶜ (γ₂ ∙ 𝟘 ∙ 𝟘)) +ᶜ
                       (𝟘ᶜ ∧ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝))                        ≈⟨ +ᶜ-assoc _ _ _ ⟩

                       (γ₁ ∙ 𝟘 ∙ 𝟘) +ᶜ (γ₂ ∙ 𝟘 ∙ 𝟘) +ᶜ
                       (𝟘ᶜ ∧ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝))                        ∎)))
          (begin
             ⌜ 𝟘ᵐ ⌝ ·ᶜ (𝟘ᶜ ∙ 𝟘 ∧ ⌜ 𝟘ᵐ ⌝)         ≈⟨ ·ᶜ-zeroʳ _ ∙ ·-distribˡ-∧ _ _ _ ⟩
             𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · 𝟘 ∧ ⌜ 𝟘ᵐ ⌝ · ⌜ 𝟘ᵐ ⌝  ≈⟨ ≈ᶜ-refl ∙ ∧-cong (·-zeroʳ _) (·-idem-⌜⌝ 𝟘ᵐ) ⟩
             𝟘ᶜ ∙ 𝟘 ∧ ⌜ 𝟘ᵐ ⌝                      ≈˘⟨ ∧ᶜ-idem _ ∙ PE.refl ⟩
             𝟘ᶜ ∧ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝)                  ∎))
       (begin
          γ₃ ∙ 𝟘                                             ≈˘⟨ <*-identityˡ _ ∙ PE.refl ⟩

          γ₃ <* idSubstₘ ∙ 𝟘                                 ≈˘⟨ ≈ᶜ-trans (+ᶜ-identityˡ _) $
                                                                 +ᶜ-identityˡ _ ⟩

          𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ (γ₃ <* idSubstₘ ∙ 𝟘)                   ≈˘⟨ +ᶜ-cong (·ᶜ-zeroˡ _) $
                                                                 +ᶜ-cong (·ᶜ-zeroˡ _) (wk1Substₘ-app _ γ₃) ⟩
          (𝟘 ·ᶜ (𝟘ᶜ ∙ 𝟘 ∧ ⌜ 𝟘ᵐ ⌝)) +ᶜ 𝟘 ·ᶜ (𝟘ᶜ ∙ 𝟘 ∧ 𝟙) +ᶜ
          γ₃ <* wk1Substₘ idSubstₘ                           ∎))
      ▸t,rfl
      (prodₘ (▸-cong (PE.sym ᵐ·-zeroˡ) ▸v) ▸w
         (λ _ → begin
            𝟘ᶜ ∧ᶜ γ₆       ≤⟨ ∧ᶜ-decreasingʳ _ _ ⟩
            γ₆             ≈˘⟨ +ᶜ-identityˡ _ ⟩
            𝟘ᶜ +ᶜ γ₆       ≈˘⟨ +ᶜ-congʳ $ ·ᶜ-zeroˡ _ ⟩
            𝟘 ·ᶜ γ₅ +ᶜ γ₆  ∎)
         (λ _ → begin
            𝟘ᶜ ∧ᶜ γ₆       ≈˘⟨ ∧ᶜ-congʳ $ ·ᶜ-zeroˡ _ ⟩
            𝟘 ·ᶜ γ₅ ∧ᶜ γ₆  ∎))
      (Jₘ-generalised ▸A ▸t
         (sub
            (Idₘ-generalised (wkUsage _ ▸Singleton) (wkUsage _ ▸t,rfl)
               (prodₘ var var
                  (λ _ → begin
                     𝟘ᶜ ∙ 𝟘 ∧ ⌜ 𝟘ᵐ ⌝                                ≤⟨ ≤ᶜ-refl ∙ ∧-decreasingʳ _ _ ⟩
                     𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝                                    ≈˘⟨ +ᶜ-identityˡ _ ⟩
                     𝟘ᶜ +ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝)                            ≈˘⟨ +ᶜ-congʳ $ ·ᶜ-zeroˡ _ ⟩
                     𝟘 ·ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ ᵐ· 𝟘 ⌝ ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝)  ∎)
                  (λ _ → begin
                     𝟘ᶜ ∙ 𝟘 ∧ ⌜ 𝟘ᵐ ⌝                                ≈˘⟨ ∧ᶜ-idem _ ∙ PE.refl ⟩
                     𝟘ᶜ ∧ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝)                            ≈˘⟨ ∧ᶜ-congʳ $ ·ᶜ-zeroˡ _ ⟩
                     𝟘 ·ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ ᵐ· 𝟘 ⌝ ∙ 𝟘) ∧ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝)  ∎))
               (λ _ → begin
                  γ₁ ∧ᶜ 𝟘ᶜ +ᶜ (γ₁ +ᶜ γ₂) ∧ᶜ 𝟘ᶜ ∙ 𝟘 ∙ 𝟘  ≤⟨ +ᶜ-monotone (∧ᶜ-decreasingʳ _ _) (∧ᶜ-decreasingʳ _ _) ∙ ≤-refl ∙ ≤-refl ⟩
                  𝟘ᶜ +ᶜ 𝟘ᶜ ∙ 𝟘 ∙ 𝟘                      ≈⟨ +ᶜ-identityˡ _ ∙ PE.refl ∙ PE.refl ⟩
                  𝟘ᶜ                                    ∎)
               (λ _ → begin
                  γ₁ ∧ᶜ 𝟘ᶜ +ᶜ (γ₁ +ᶜ γ₂) ∧ᶜ 𝟘ᶜ ∙ 𝟘 ∙ 𝟘                        ≤⟨ +ᶜ-monotoneˡ (∧ᶜ-decreasingʳ _ _) ∙ ≤-refl ∙ ≤-refl ⟩

                  𝟘ᶜ +ᶜ (γ₁ +ᶜ γ₂) ∧ᶜ 𝟘ᶜ ∙ 𝟘 ∙ 𝟘                              ≈˘⟨ +ᶜ-identityʳ _ ⟩

                  (𝟘ᶜ +ᶜ (γ₁ +ᶜ γ₂) ∧ᶜ 𝟘ᶜ ∙ 𝟘 ∙ 𝟘) +ᶜ 𝟘ᶜ                      ≈˘⟨ +ᶜ-cong (+ᶜ-congʳ (·ᶜ-zeroˡ _) ∙ PE.refl ∙ PE.refl)
                                                                                   (≈ᶜ-refl ∙ ∧-idem _) ⟩

                  ((𝟘 ·ᶜ γ₁) +ᶜ (γ₁ +ᶜ γ₂) ∧ᶜ 𝟘ᶜ ∙ 𝟘 ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ 𝟘 ∧ 𝟘)     ≤⟨ +ᶜ-monotoneʳ (≤ᶜ-refl ∙ ∧-monotoneʳ 𝟘≤⌜𝟘ᵐ⌝) ⟩

                  (𝟘 ·ᶜ γ₁ +ᶜ (γ₁ +ᶜ γ₂) ∧ᶜ 𝟘ᶜ ∙ 𝟘 ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ 𝟘 ∧ ⌜ 𝟘ᵐ ⌝)  ≈˘⟨ +ᶜ-congˡ (+ᶜ-identityˡ _) ⟩

                  (𝟘 ·ᶜ γ₁ +ᶜ (γ₁ +ᶜ γ₂) ∧ᶜ 𝟘ᶜ ∙ 𝟘 ∙ 𝟘) +ᶜ
                  𝟘ᶜ +ᶜ (𝟘ᶜ ∙ 𝟘 ∧ ⌜ 𝟘ᵐ ⌝)                                     ∎)) $
          (begin
             γ₁ ∧ᶜ 𝟘ᶜ +ᶜ (γ₁ +ᶜ γ₂) ∧ᶜ 𝟘ᶜ ∙
             ⌜ 𝟘ᵐ ⌝ · 𝟘 ∙ ⌜ 𝟘ᵐ ⌝ · (𝟘 ∧ 𝟙)                           ≈⟨ ≈ᶜ-refl ∙ ·[𝟘∧𝟙]≡𝟘∧ ⟩

             γ₁ ∧ᶜ 𝟘ᶜ +ᶜ (γ₁ +ᶜ γ₂) ∧ᶜ 𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · 𝟘 ∙ 𝟘 ∧ ⌜ 𝟘ᵐ ⌝  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ PE.refl ⟩

             γ₁ ∧ᶜ 𝟘ᶜ +ᶜ (γ₁ +ᶜ γ₂) ∧ᶜ 𝟘ᶜ ∙ 𝟘 ∙ 𝟘 ∧ ⌜ 𝟘ᵐ ⌝            ≤⟨ ≤ᶜ-refl ∙ ∧-decreasingˡ _ _ ⟩

             γ₁ ∧ᶜ 𝟘ᶜ +ᶜ (γ₁ +ᶜ γ₂) ∧ᶜ 𝟘ᶜ ∙ 𝟘 ∙ 𝟘                      ∎))
         rflₘ ▸v ▸w)
      ▸u
    where
    open ≤ᶜ-reasoning

------------------------------------------------------------------------
-- Inversion lemmas for usage

opaque
  unfolding Erased

  -- An inversion lemma for Erased.

  inv-usage-Erased :
    γ ▸[ m ] Erased l A → ∃₂ λ δ η → δ ▸[ 𝟘ᵐ ] A × η ▸[ 𝟘ᵐ ] l × γ ≤ᶜ 𝟘ᶜ
  inv-usage-Erased {γ} {m} ▸Erased =
    let invUsageΠΣ {δ} {η} ▸A ▸Lift-Unit γ≤ =
          inv-usage-ΠΣ ▸Erased
        (_ , ▸wk1-l) , ▸Unit =
          inv-usage-Lift ▸Lift-Unit
    in _ , _ , ▸-cong (ᵐ·-zeroʳ _) ▸A , wkUsage⁻¹ ▸wk1-l , (begin
      γ           ≤⟨ γ≤ ⟩
      𝟘 ·ᶜ δ +ᶜ η ≈⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
      𝟘ᶜ +ᶜ η     ≈⟨ +ᶜ-identityˡ _ ⟩
      η           ≤⟨ tailₘ-monotone (inv-usage-Unit ▸Unit) ⟩
      𝟘ᶜ          ∎)
    where
    open ≤ᶜ-reasoning

opaque
  unfolding [_]

  -- An inversion lemma for [_].

  inv-usage-[] : γ ▸[ m ] [ t ] → (∃ λ δ → δ ▸[ 𝟘ᵐ ] t) × γ ≤ᶜ 𝟘ᶜ
  inv-usage-[] {(n)} {γ} {m} {t} ▸[] = lemma s PE.refl
    where
    open Tools.Reasoning.PartialOrder (≤ᶜ-poset {n})
    lemma : ∀ s′ → s PE.≡ s′ → (∃ λ δ → δ ▸[ 𝟘ᵐ ] t) × γ ≤ᶜ 𝟘ᶜ
    lemma 𝕤 PE.refl =
      case inv-usage-prodˢ ▸[] of λ {
        (invUsageProdˢ {δ = δ} {η = η} ▸t ▸star γ≤) →
      (_ , ▸-cong (ᵐ·-zeroʳ m) ▸t)
      , (begin
          γ            ≤⟨ γ≤ ⟩
          𝟘 ·ᶜ δ ∧ᶜ η  ≈⟨ ∧ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
          𝟘ᶜ ∧ᶜ η      ≤⟨ ∧ᶜ-decreasingˡ _ _ ⟩
          𝟘ᶜ           ∎) }
    lemma 𝕨 PE.refl =
      let invUsageProdʷ {δ} {η} ▸t ▸lift-star γ≤ =
            inv-usage-prodʷ ▸[]
          η≤𝟘 =
            inv-usage-starʷ (inv-usage-lift ▸lift-star)
      in
      (_ , ▸-cong (ᵐ·-zeroʳ m) ▸t)
      , (begin
          γ            ≤⟨ γ≤ ⟩
          𝟘 ·ᶜ δ +ᶜ η  ≈⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
          𝟘ᶜ +ᶜ η      ≈⟨ +ᶜ-identityˡ _ ⟩
          η            ≤⟨ η≤𝟘 ⟩
          𝟘ᶜ           ∎)

opaque
  unfolding erased

  -- An inversion lemma for erased.

  inv-usage-erased :
    ¬ Trivialᵐ →
    γ ▸[ m ] erased A t →
    𝟘ᶜ ▸[ 𝟘ᵐ ] t ×
    γ ≤ᶜ 𝟘ᶜ ×
    (s ≡ 𝕤 → m ≡ 𝟘ᵐ) ×
    (s ≡ 𝕨 → 𝟘 ≤ ⌜ m ⌝ × 𝟘ᶜ ▸[ 𝟘ᵐ ] A × Prodrec-allowed m (𝟘 ∧ 𝟙) 𝟘 𝟘)
  inv-usage-erased 𝟙ᵐ≢𝟘ᵐ ▸erased = case PE.singleton s of λ where
    (𝕤 , PE.refl) →
      case Eta.inv-usage-erased 𝟙ᵐ≢𝟘ᵐ ▸erased of λ
        (▸t , γ≤𝟘 , m≡𝟘ᵐ) →
          ▸t , γ≤𝟘 , (λ _ → m≡𝟘ᵐ) , λ ()
    (𝕨 , PE.refl) →
      case NoEta.inv-usage-erased ▸erased of λ
        (_ , ▸t , ▸A , γ≤𝟘 , 𝟘≤m , ok) →
          ▸t , γ≤𝟘 , (λ ()) , λ _ →
            𝟘≤m , (sub-≈ᶜ ▸A (≈ᶜ-sym (≈ᶜ-trans (·ᶜ-congʳ (⌜𝟘ᵐ⌝ 𝟙ᵐ≢𝟘ᵐ)) (·ᶜ-zeroˡ _)))) , ok
