------------------------------------------------------------------------
-- Some properties related to usage and Erased
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Untyped.NotParametrised using (Strength)

module Graded.Derived.Erased.Usage
  {a} {M : Set a}
  (𝕄 : Modality M)
  (R : Usage-restrictions 𝕄)
  (s : Strength)
  where

open Modality 𝕄
open Usage-restrictions R

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Substitution 𝕄 R
open import Graded.Substitution.Properties 𝕄 R
open import Graded.Usage 𝕄 R
open import Graded.Usage.Inversion 𝕄 R
open import Graded.Usage.Properties 𝕄 R
open import Graded.Usage.Weakening 𝕄 R
open import Graded.Mode 𝕄

open import Definition.Untyped M hiding (_∷_)
open import Definition.Untyped.Identity 𝕄
open import Definition.Untyped.Properties M
import Graded.Derived.Erased.Eta.Usage 𝕄 R as Eta
import Graded.Derived.Erased.NoEta.Usage 𝕄 R as NoEta
import Graded.Derived.Erased.Untyped
open Graded.Derived.Erased.Untyped 𝕄 s
open import Graded.Derived.Identity R
open import Graded.Derived.Sigma 𝕄 R

open import Tools.Bool using (T)
open import Tools.Fin
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≡_)
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (inj₁; inj₂)

private variable
  A B t u v w           : Term _
  γ γ₁ γ₂ γ₃ γ₄ γ₅ γ₆ δ : Conₘ _
  m                     : Mode
  ok                    : T _

------------------------------------------------------------------------
-- Usage rules

opaque

  -- A usage rule for Erased.

  ▸Erased :
    γ ▸[ 𝟘ᵐ? ] A →
    γ ▸[ m ] Erased A
  ▸Erased {γ} {m} ▸A = sub
    (ΠΣₘ
       (▸-cong (PE.sym (ᵐ·-zeroʳ m)) ▸A)
       (sub Unitₘ
          (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
             𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
             𝟘ᶜ              ∎)))
    (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       γ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
       γ +ᶜ 𝟘ᶜ  ∎)

opaque

  ▸[] : γ ▸[ 𝟘ᵐ? ] t → 𝟘ᶜ ▸[ m ] [ t ]
  ▸[] {(n)} {γ} {t} {m} ▸t = lemma s PE.refl
    where
    open Tools.Reasoning.PartialOrder (≤ᶜ-poset {n})
    lemma : ∀ s′ → s PE.≡ s′ → 𝟘ᶜ ▸[ m ] [ t ]
    lemma 𝕤 PE.refl = sub
      (prodˢₘ (▸-cong (PE.sym (ᵐ·-zeroʳ m)) ▸t) starₘ)
      (begin
         𝟘ᶜ             ≈˘⟨ ∧ᶜ-idem _ ⟩
         𝟘ᶜ ∧ᶜ 𝟘ᶜ       ≈˘⟨ ∧ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
         𝟘 ·ᶜ γ ∧ᶜ 𝟘ᶜ  ∎)
    lemma 𝕨 PE.refl = sub
      (prodʷₘ (▸-cong (PE.sym (ᵐ·-zeroʳ m)) ▸t) starₘ)
      (begin
         𝟘ᶜ             ≈˘⟨ +ᶜ-identityˡ _ ⟩
         𝟘ᶜ +ᶜ 𝟘ᶜ       ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
         𝟘 ·ᶜ γ +ᶜ 𝟘ᶜ  ∎)

opaque
  unfolding erased

  -- A usage rule for erased.

  ▸erased′ :
    (s ≡ 𝕨 → ¬ T 𝟘ᵐ-allowed → Trivial) →
    (s ≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → 𝟘 ≤ 𝟙) →
    γ ▸[ 𝟘ᵐ? ] t →
    (s ≡ 𝕨 → δ ▸[ 𝟘ᵐ? ] A) →
    (s ≡ 𝕨 → Prodrec-allowed 𝟘ᵐ? (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    𝟘ᶜ ▸[ 𝟘ᵐ? ] erased A t
  ▸erased′ {γ} trivial 𝟘≤𝟙 ▸t ▸A ok =
    case PE.singleton s of λ where
      (𝕨 , PE.refl) →
        NoEta.▸erased′ (trivial PE.refl) ▸t (▸A PE.refl) (ok PE.refl)
      (𝕤 , PE.refl) →
        let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
        sub (Eta.▸erased′ (𝟘≤𝟙 PE.refl) ▸t) $
        𝟘ᵐ?-elim
          (λ m → 𝟘ᶜ ≤ᶜ ⌜ m ⌝ ·ᶜ γ)
          (begin
             𝟘ᶜ      ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
             𝟘 ·ᶜ γ  ∎)
          (λ not-ok → begin
             𝟘ᶜ      ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
             𝟘 ·ᶜ γ  ≤⟨ ·ᶜ-monotoneˡ $ 𝟘≤𝟙 PE.refl not-ok ⟩
             𝟙 ·ᶜ γ  ∎)

opaque
  unfolding erased

  -- Another usage rule for erased.

  ▸erased :
    γ ▸[ 𝟘ᵐ[ ok ] ] t →
    (s ≡ 𝕨 → δ ▸[ 𝟘ᵐ[ ok ] ] A) →
    (s ≡ 𝕨 → Prodrec-allowed 𝟘ᵐ[ ok ] (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] erased A t
  ▸erased ▸t ▸A ok = case PE.singleton s of λ where
    (𝕤 , PE.refl) → Eta.▸erased ▸t
    (𝕨 , PE.refl) → NoEta.▸erased ▸t (▸A PE.refl) (ok PE.refl)

opaque
  unfolding substᵉ

  -- A usage rule for substᵉ.

  ▸substᵉ :
    (s ≡ 𝕨 → Prodrec-allowed 𝟘ᵐ? (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    (s ≡ 𝕨 → ¬ T 𝟘ᵐ-allowed → Trivial) →
    (s ≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → 𝟘 ≤ 𝟙) →
    γ₁ ▸[ 𝟘ᵐ? ] A →
    γ₂ ∙ 𝟘 ▸[ m ] B →
    γ₃ ▸[ 𝟘ᵐ? ] t →
    γ₄ ▸[ 𝟘ᵐ? ] u →
    γ₅ ▸[ 𝟘ᵐ? ] v →
    γ₆ ▸[ m ] w →
    𝟘ᶜ ∧ᶜ ω ·ᶜ (γ₂ ∧ᶜ γ₆) ▸[ m ] substᵉ A B t u v w
  ▸substᵉ {γ₂} {m} {γ₆} ok trivial 𝟘≤𝟙 ▸A ▸B ▸t ▸u ▸v ▸w = sub
    (▸subst (▸Erased ▸A)
       (sub
          (substₘ-lemma _
             (▶-cong _
                (λ where
                   x0     → PE.refl
                   (_ +1) → PE.refl) $
              wf-consSubstₘ (wf-wk1Substₘ _ _ wf-idSubstₘ) $
              sub
                (▸-cong (PE.sym ⌞𝟘⌟≡𝟘ᵐ?) $
                 ▸erased′ trivial 𝟘≤𝟙
                   var (λ _ → wkUsage (step id) ▸A) ok)
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
       (▸[] ▸t) (▸[] ▸u) ([]-congₘ ▸A ▸t ▸u ▸v) ▸w)
    (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       𝟘ᶜ ∧ᶜ ω ·ᶜ (γ₂ ∧ᶜ γ₆)              ≈˘⟨ ≈ᶜ-trans
                                                (·ᶜ-congˡ $
                                                 ≈ᶜ-trans
                                                   (∧ᶜ-congˡ $
                                                    ≈ᶜ-trans (≈ᶜ-sym $ ∧ᶜ-assoc _ _ _) $
                                                    ≈ᶜ-trans (∧ᶜ-congʳ $ ∧ᶜ-idem _) $
                                                    ≈ᶜ-trans (≈ᶜ-sym $ ∧ᶜ-assoc _ _ _) $
                                                    ∧ᶜ-congʳ $ ∧ᶜ-idem _) $
                                                 ≈ᶜ-trans (≈ᶜ-sym $ ∧ᶜ-assoc _ _ _) $
                                                 ≈ᶜ-trans (∧ᶜ-congʳ $ ∧ᶜ-comm _ _) $
                                                 ∧ᶜ-assoc _ _ _) $
                                              ≈ᶜ-trans (·ᶜ-distribˡ-∧ᶜ _ _ _) $
                                              ∧ᶜ-congʳ $ ·ᶜ-zeroʳ _ ⟩
       ω ·ᶜ (γ₂ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ γ₆)  ∎)

opaque

  -- A variant of the usage rule for substᵉ given above.

  ▸substᵉ′ :
    (s ≡ 𝕨 → Prodrec-allowed 𝟘ᵐ? (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    (s ≡ 𝕨 → ¬ T 𝟘ᵐ-allowed → Trivial) →
    (s ≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → 𝟘 ≤ 𝟙) →
    ω ≤ 𝟘 →
    γ₁ ▸[ 𝟘ᵐ? ] A →
    γ₂ ∙ 𝟘 ▸[ m ] B →
    γ₃ ▸[ 𝟘ᵐ? ] t →
    γ₄ ▸[ 𝟘ᵐ? ] u →
    γ₅ ▸[ 𝟘ᵐ? ] v →
    γ₆ ▸[ m ] w →
    ω ·ᶜ (γ₂ ∧ᶜ γ₆) ▸[ m ] substᵉ A B t u v w
  ▸substᵉ′ {γ₂} {γ₆} ok trivial 𝟘≤𝟙 ω≤𝟘 ▸A ▸B ▸t ▸u ▸v ▸w = sub
    (▸substᵉ ok trivial 𝟘≤𝟙 ▸A ▸B ▸t ▸u ▸v ▸w)
    (begin
       ω ·ᶜ (γ₂ ∧ᶜ γ₆)        ≤⟨ ∧ᶜ-greatest-lower-bound
                                   (≤ᶜ-trans (·ᶜ-monotoneˡ ω≤𝟘) (≤ᶜ-reflexive (·ᶜ-zeroˡ _)))
                                   ≤ᶜ-refl ⟩
       𝟘ᶜ ∧ᶜ ω ·ᶜ (γ₂ ∧ᶜ γ₆)  ∎)
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

opaque
  unfolding Jᵉ

  -- A usage rule for Jᵉ.

  ▸Jᵉ :
    (s ≡ 𝕨 → Prodrec-allowed 𝟘ᵐ? (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    (s ≡ 𝕨 → ¬ T 𝟘ᵐ-allowed → Trivial) →
    (s ≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → 𝟘 ≤ 𝟙) →
    γ₁ ▸[ 𝟘ᵐ? ] A →
    γ₂ ▸[ 𝟘ᵐ? ] t →
    γ₃ ∙ 𝟘 ∙ 𝟘 ▸[ m ] B →
    γ₄ ▸[ m ] u →
    γ₅ ▸[ 𝟘ᵐ? ] v →
    γ₆ ▸[ 𝟘ᵐ? ] w →
    𝟘ᶜ ∧ᶜ ω ·ᶜ (γ₃ ∧ᶜ γ₄) ▸[ m ] Jᵉ A t B u v w
  ▸Jᵉ {γ₂} {γ₃} {γ₅} {γ₆} ok trivial 𝟘≤𝟙 ▸A ▸t ▸B ▸u ▸v ▸w =
    case
      𝟘ᵐ?-elim (λ m → 𝟘 ≤ ⌜ m ⌝) ≤-refl
        (λ not-ok →
           case PE.singleton s of λ where
             (𝕤 , s≡𝕤) → 𝟘≤𝟙 s≡𝕤 not-ok
             (𝕨 , s≡𝕨) → ≡-trivial $ trivial s≡𝕨 not-ok) of λ
      𝟘≤⌜𝟘ᵐ?⌝ →
    case
      (ΠΣₘ (▸-cong (PE.sym ᵐ·-zeroˡ) ▸A) $
       Idₘ-generalised (wkUsage _ ▸A) (wkUsage _ ▸t) var
         (λ _ → begin
            (γ₂ ∧ᶜ 𝟘ᶜ) ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
            (γ₂ ∧ᶜ 𝟘ᶜ) ∙ 𝟘            ≤⟨ ∧ᶜ-decreasingʳ _ _ ∙ ≤-refl ⟩
            𝟘ᶜ                        ∎)
         (λ _ → begin
            (γ₂ ∧ᶜ 𝟘ᶜ) ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘    ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
            (γ₂ ∧ᶜ 𝟘ᶜ) ∙ 𝟘              ≤⟨ ∧ᶜ-decreasingˡ _ _ ∙ 𝟘≤⌜𝟘ᵐ?⌝ ⟩
            γ₂ ∙ ⌜ 𝟘ᵐ? ⌝                ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityˡ _ ⟩
            (γ₂ ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝)  ∎)) of λ
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
    case
      (λ s≡𝕨 →
         𝟘ᵐ-allowed-elim (inj₁ ∘→ 𝟘ᵐ.𝟘≰𝟙)
           (inj₂ ∘→ inj₁ ∘→ trivial s≡𝕨)) of λ
      ok′ →
    case
      (case PE.singleton s of λ where
         (𝕤 , s≡𝕤) → 𝟘≤𝟙 s≡𝕤
         (𝕨 , s≡𝕨) → ≡-trivial ∘→ trivial s≡𝕨) ∘→
      𝟘ᵐ?≡𝟙ᵐ⇔ .proj₁ of λ
      𝟘≤𝟙′ →
    ▸substᵉ ok trivial 𝟘≤𝟙 ▸Singleton
      (sub
         (flip (substₘ-lemma _) ▸B $
          ▶-cong _
            (λ where
               x0        → PE.sym ⌞𝟘⌟≡𝟘ᵐ?
               (x0 +1)   → PE.sym ⌞𝟘⌟≡𝟘ᵐ?
               (_ +1 +1) → PE.refl) $
          wf-consSubstₘ
            (wf-consSubstₘ (wf-wk1Substₘ _ _ wf-idSubstₘ) $
             sub (▸fst⟨⟩ ok′ ok 𝟘≤𝟙′ var (λ _ → wkUsage _ ▸A))
               (begin
                  ⌜ 𝟘ᵐ? ⌝ ·ᶜ (𝟘ᶜ ∙ 𝟘 ∧ 𝟙)  ≈⟨ ·ᶜ-zeroʳ _ ∙ ·[𝟘∧𝟙]≡𝟘∧ ⟩
                  𝟘ᶜ ∙ 𝟘 ∧ ⌜ 𝟘ᵐ? ⌝         ≈˘⟨ ∧ᶜ-idem _ ∙ PE.refl ⟩
                  𝟘ᶜ ∧ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝)     ∎)) $
          sub
            (▸snd⟨⟩ ok′ ok var
               (λ _ →
                  Idₘ-generalised
                    (PE.subst (_▸[_]_ _ _) (PE.sym wk₂-[]↑) $
                     wkUsage _ ▸A)
                    (PE.subst (_▸[_]_ _ _) (PE.sym wk₂-[]↑) $
                     wkUsage _ ▸t)
                    (▸fst⟨⟩ ok′ ok 𝟘≤𝟙′ var
                       (λ _ → wkUsage _ $ wkUsage _ ▸A))
                    (λ _ → begin
                       ((γ₂ ∙ 𝟘) ∧ᶜ 𝟘ᶜ) ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
                       ((γ₂ ∙ 𝟘) ∧ᶜ 𝟘ᶜ) ∙ 𝟘            ≤⟨ ∧ᶜ-decreasingʳ _ _ ∙ ≤-refl ⟩
                       𝟘ᶜ                              ∎)
                    (λ _ → begin
                       ((γ₂ ∙ 𝟘) ∧ᶜ 𝟘ᶜ) ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘          ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
                       ((γ₂ ∙ 𝟘) ∧ᶜ 𝟘ᶜ) ∙ 𝟘                    ≤⟨ ∧ᶜ-decreasingˡ _ _ ∙ ≤-refl ⟩
                       γ₂ ∙ 𝟘 ∙ 𝟘                              ≈˘⟨ +ᶜ-identityʳ _ ⟩
                       (γ₂ ∙ 𝟘 ∙ 𝟘) +ᶜ 𝟘ᶜ                      ≈˘⟨ +ᶜ-congˡ $ ∧ᶜ-idem _ ⟩
                       (γ₂ ∙ 𝟘 ∙ 𝟘) +ᶜ (𝟘ᶜ ∧ᶜ 𝟘ᶜ)              ≤⟨ +ᶜ-monotoneʳ $ ∧ᶜ-monotoneʳ (≤ᶜ-refl ∙ 𝟘≤⌜𝟘ᵐ?⌝) ⟩
                       (γ₂ ∙ 𝟘 ∙ 𝟘) +ᶜ (𝟘ᶜ ∧ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝))  ∎)))
          (begin
             ⌜ 𝟘ᵐ? ⌝ ·ᶜ (𝟘ᶜ ∙ 𝟘 ∧ ⌜ 𝟘ᵐ? ⌝)         ≈⟨ ·ᶜ-zeroʳ _ ∙ ·-distribˡ-∧ _ _ _ ⟩
             𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘 ∧ ⌜ 𝟘ᵐ? ⌝ · ⌜ 𝟘ᵐ? ⌝  ≈⟨ ≈ᶜ-refl ∙ ∧-cong (·-zeroʳ _) (·-idem-⌜⌝ 𝟘ᵐ?) ⟩
             𝟘ᶜ ∙ 𝟘 ∧ ⌜ 𝟘ᵐ? ⌝                      ≈˘⟨ ∧ᶜ-idem _ ∙ PE.refl ⟩
             𝟘ᶜ ∧ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝)                  ∎))
       (begin
          γ₃ ∙ 𝟘                                             ≈˘⟨ <*-identityˡ _ ∙ PE.refl ⟩

          γ₃ <* idSubstₘ ∙ 𝟘                                 ≈˘⟨ ≈ᶜ-trans (+ᶜ-identityˡ _) $
                                                                 +ᶜ-identityˡ _ ⟩

          𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ (γ₃ <* idSubstₘ ∙ 𝟘)                   ≈˘⟨ +ᶜ-cong (·ᶜ-zeroˡ _) $
                                                                 +ᶜ-cong (·ᶜ-zeroˡ _) (wk1Substₘ-app _ γ₃) ⟩
          (𝟘 ·ᶜ (𝟘ᶜ ∙ 𝟘 ∧ ⌜ 𝟘ᵐ? ⌝)) +ᶜ 𝟘 ·ᶜ (𝟘ᶜ ∙ 𝟘 ∧ 𝟙) +ᶜ
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
                     𝟘ᶜ ∙ 𝟘 ∧ ⌜ 𝟘ᵐ? ⌝                                ≤⟨ ≤ᶜ-refl ∙ ∧-decreasingʳ _ _ ⟩
                     𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝                                    ≈˘⟨ +ᶜ-identityˡ _ ⟩
                     𝟘ᶜ +ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝)                            ≈˘⟨ +ᶜ-congʳ $ ·ᶜ-zeroˡ _ ⟩
                     𝟘 ·ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ᵐ· 𝟘 ⌝ ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝)  ∎)
                  (λ _ → begin
                     𝟘ᶜ ∙ 𝟘 ∧ ⌜ 𝟘ᵐ? ⌝                                ≈˘⟨ ∧ᶜ-idem _ ∙ PE.refl ⟩
                     𝟘ᶜ ∧ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝)                            ≈˘⟨ ∧ᶜ-congʳ $ ·ᶜ-zeroˡ _ ⟩
                     𝟘 ·ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ᵐ· 𝟘 ⌝ ∙ 𝟘) ∧ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝)  ∎))
               (λ _ → begin
                  𝟘ᶜ ∙ 𝟘 ∧ ⌜ 𝟘ᵐ? ⌝  ≤⟨ ≤ᶜ-refl ∙ ∧-decreasingˡ _ _ ⟩
                  𝟘ᶜ                ∎)
               (λ _ → begin
                  𝟘ᶜ ∙ 𝟘 ∧ ⌜ 𝟘ᵐ? ⌝          ≈˘⟨ +ᶜ-identityˡ _ ⟩
                  𝟘ᶜ +ᶜ (𝟘ᶜ ∙ 𝟘 ∧ ⌜ 𝟘ᵐ? ⌝)  ∎)) $
          begin
            𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ · (𝟘 ∧ 𝟙)  ≈⟨ ≈ᶜ-refl ∙ ·[𝟘∧𝟙]≡𝟘∧ ⟩
            𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘 ∙ 𝟘 ∧ ⌜ 𝟘ᵐ? ⌝        ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ PE.refl ⟩
            𝟘ᶜ ∙ 𝟘 ∧ ⌜ 𝟘ᵐ? ⌝                      ∎)
         rflₘ ▸v ▸w)
      ▸u
    where
    open ≤ᶜ-reasoning

opaque

  -- A variant of the usage rule for Jᵉ given above.

  ▸Jᵉ′ :
    (s ≡ 𝕨 → Prodrec-allowed 𝟘ᵐ? (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    (s ≡ 𝕨 → ¬ T 𝟘ᵐ-allowed → Trivial) →
    (s ≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → 𝟘 ≤ 𝟙) →
    ω ≤ 𝟘 →
    γ₁ ▸[ 𝟘ᵐ? ] A →
    γ₂ ▸[ 𝟘ᵐ? ] t →
    γ₃ ∙ 𝟘 ∙ 𝟘 ▸[ m ] B →
    γ₄ ▸[ m ] u →
    γ₅ ▸[ 𝟘ᵐ? ] v →
    γ₆ ▸[ 𝟘ᵐ? ] w →
    ω ·ᶜ (γ₃ ∧ᶜ γ₄) ▸[ m ] Jᵉ A t B u v w
  ▸Jᵉ′ {γ₃} {γ₄} ok trivial 𝟘≤𝟙 ω≤𝟘 ▸A ▸t ▸B ▸u ▸v ▸w = sub
    (▸Jᵉ ok trivial 𝟘≤𝟙 ▸A ▸t ▸B ▸u ▸v ▸w)
    (begin
       ω ·ᶜ (γ₃ ∧ᶜ γ₄)        ≤⟨ ∧ᶜ-greatest-lower-bound
                                   (≤ᶜ-trans (·ᶜ-monotoneˡ ω≤𝟘) (≤ᶜ-reflexive (·ᶜ-zeroˡ _)))
                                   ≤ᶜ-refl ⟩
       𝟘ᶜ ∧ᶜ ω ·ᶜ (γ₃ ∧ᶜ γ₄)  ∎)
    where
    open ≤ᶜ-reasoning

------------------------------------------------------------------------
-- Inversion lemmas for usage

opaque

  -- An inversion lemma for Erased.

  inv-usage-Erased : γ ▸[ m ] Erased A → γ ▸[ 𝟘ᵐ? ] A
  inv-usage-Erased {γ} {m} ▸Erased =
    case inv-usage-ΠΣ ▸Erased of λ {
      (invUsageΠΣ {δ = δ} {η = η} ▸A ▸Unit γ≤) →
    sub (▸-cong (ᵐ·-zeroʳ m) ▸A) $ begin
      γ        ≤⟨ γ≤ ⟩
      δ +ᶜ η   ≤⟨ +ᶜ-monotoneʳ (tailₘ-monotone (inv-usage-Unit ▸Unit)) ⟩
      δ +ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityʳ _ ⟩
      δ        ∎ }
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

opaque

  -- An inversion lemma for [_].

  inv-usage-[] : γ ▸[ m ] [ t ] → (∃ λ δ → δ ▸[ 𝟘ᵐ? ] t) × γ ≤ᶜ 𝟘ᶜ
  inv-usage-[] {(n)} {γ} {m} {t} ▸[] = lemma s PE.refl
    where
    open Tools.Reasoning.PartialOrder (≤ᶜ-poset {n})
    lemma : ∀ s′ → s PE.≡ s′ → (∃ λ δ → δ ▸[ 𝟘ᵐ? ] t) × γ ≤ᶜ 𝟘ᶜ
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
      case inv-usage-prodʷ ▸[] of λ {
        (invUsageProdʷ {δ = δ} {η} ▸t ▸star γ≤) →
      case inv-usage-starʷ ▸star of λ
        η≤𝟘 →
      (_ , ▸-cong (ᵐ·-zeroʳ m) ▸t)
      , (begin
          γ            ≤⟨ γ≤ ⟩
          𝟘 ·ᶜ δ +ᶜ η  ≈⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
          𝟘ᶜ +ᶜ η      ≈⟨ +ᶜ-identityˡ _ ⟩
          η            ≤⟨ η≤𝟘 ⟩
          𝟘ᶜ           ∎) }

opaque
  unfolding erased

  -- An inversion lemma for erased.

  inv-usage-erased :
    γ ▸[ m ] erased A t →
    𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] t ×
    γ ≤ᶜ 𝟘ᶜ ×
    m ≡ 𝟘ᵐ[ ok ] ×
    (s ≡ 𝕨 → 𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] A × Prodrec-allowed m (𝟘 ∧ 𝟙) 𝟘 𝟘)
  inv-usage-erased ▸erased = case PE.singleton s of λ where
    (𝕤 , PE.refl) →
      case Eta.inv-usage-erased ▸erased of λ
        (▸t , γ≤𝟘 , m≡𝟘ᵐ) →
          ▸t , γ≤𝟘 , m≡𝟘ᵐ , (λ ())
    (𝕨 , PE.refl) →
      case NoEta.inv-usage-erased ▸erased of λ
        (▸t , ▸A , γ≤𝟘 , m≡𝟘ᵐ , ok) →
          ▸t , γ≤𝟘 , m≡𝟘ᵐ , λ _ → ▸A , ok
