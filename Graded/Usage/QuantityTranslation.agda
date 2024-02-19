------------------------------------------------------------------------
-- Modality morphisms preserve some things related to usage
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Graded.Modality
open import Graded.Modality.Morphism as M
  using (Is-morphism; Is-order-embedding;
         Is-Σ-morphism; Is-Σ-order-embedding)
  hiding (module Is-morphism; module Is-order-embedding)
open import Graded.Usage.Restrictions

module Graded.Usage.QuantityTranslation
  {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
  (𝕄₁ : Modality M₁) (𝕄₂ : Modality M₂)
  (R₁ : Usage-restrictions 𝕄₁) (R₂ : Usage-restrictions 𝕄₂)
  (tr tr-Σ : M₁ → M₂)
  where

open import Definition.Untyped
open import Definition.Untyped.QuantityTranslation tr tr-Σ

open import Graded.Context
import Graded.Context.Properties
open import Graded.Context.QuantityTranslation 𝕄₁ 𝕄₂ tr
  as CQ using (tr-Conₘ)
import Graded.Modality.Properties
open import Graded.Usage
open import Graded.Usage.Erased-matches
import Graded.Usage.Properties
import Graded.Usage.Restrictions.Satisfied
open import Graded.Modality.Morphism.Usage-restrictions

open import Graded.Mode
open import Graded.Mode.QuantityTranslation 𝕄₁ 𝕄₂ tr tr-Σ
  as MQ hiding (module Is-morphism; module Is-order-embedding)

open Graded.Modality.Properties 𝕄₂
open Graded.Usage.Properties 𝕄₂ R₂
open Graded.Usage.Restrictions.Satisfied 𝕄₂ R₂

private
  module C₁  = Graded.Context 𝕄₁
  module C₂  = Graded.Context 𝕄₂
  module CP₁ = Graded.Context.Properties 𝕄₁
  module CP₂ = Graded.Context.Properties 𝕄₂
  module MP₁ = Graded.Modality.Properties 𝕄₁
  module U₁  = Graded.Usage 𝕄₁ R₁
  module U₂  = Graded.Usage 𝕄₂ R₂
  module UP₁ = Graded.Usage.Properties 𝕄₁ R₁
  module RS₁ = Graded.Usage.Restrictions.Satisfied 𝕄₁ R₁
  module RS₂ = Graded.Usage.Restrictions.Satisfied 𝕄₂ R₂
  module Mo₁ = Graded.Mode 𝕄₁
  module Mo₂ = Graded.Mode 𝕄₂
  module M₁  = Modality 𝕄₁
  module M₂  = Modality 𝕄₂
  module UR₁ = Usage-restrictions R₁
  module UR₂ = Usage-restrictions R₂

open import Tools.Bool
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product as Σ
open import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (inj₁; inj₂)

private
  module R₁      = Tools.Reasoning.PartialOrder MP₁.≤-poset
  module R₂      = Tools.Reasoning.PartialOrder ≤-poset
  module CR₁ {n} = Tools.Reasoning.PartialOrder (CP₁.≤ᶜ-poset {n = n})
  module CR₂ {n} = Tools.Reasoning.PartialOrder (CP₂.≤ᶜ-poset {n = n})

private variable
  n          : Nat
  x          : Fin _
  p q        : M₁
  p′         : M₂
  γ γ′ δ     : Conₘ _ _
  m m₁ m₂ m′ : Mode _
  t          : Term _ _
  ok₂        : T _

------------------------------------------------------------------------
-- If certain properties hold, then they hold also after translation
-- by morphisms that preserve usage restrictions

module Is-morphism
  (tr-m   : Is-morphism 𝕄₁ 𝕄₂ tr)
  (tr-Σ-m : Is-Σ-morphism 𝕄₁ 𝕄₂ tr tr-Σ)
  (r      : Are-preserving-usage-restrictions R₁ R₂ tr tr-Σ)
  where

  open Are-preserving-usage-restrictions r
  open CQ.Is-morphism tr-m
  open M.Is-morphism tr-m
  open M.Is-Σ-morphism tr-Σ-m
  open MQ.Is-morphism tr-m tr-Σ-m

  open CP₂

  -- Preservation of _◂_∈_.

  tr-◂∈ : x U₁.◂ p ∈ γ → x U₂.◂ tr p ∈ tr-Conₘ γ
  tr-◂∈ here      = here
  tr-◂∈ (there x) = there (tr-◂∈ x)

  mutual

    -- Preservation of _▸[_]_.

    tr-▸ : γ U₁.▸[ m ] t → tr-Conₘ γ U₂.▸[ tr-Mode m ] tr-Term t
    tr-▸ Uₘ =
      sub Uₘ tr-Conₘ-𝟘ᶜ-≤ᶜ
    tr-▸ ℕₘ =
      sub ℕₘ tr-Conₘ-𝟘ᶜ-≤ᶜ
    tr-▸ Emptyₘ =
      sub Emptyₘ tr-Conₘ-𝟘ᶜ-≤ᶜ
    tr-▸ Unitₘ =
      sub Unitₘ tr-Conₘ-𝟘ᶜ-≤ᶜ
    tr-▸ (ΠΣₘ {γ = γ} {m = m} {δ = δ} {q = q} {b = b} ▸A ▸P) = sub
      (ΠΣₘ (▸-cong (tr-Mode-ᵐ· m b) (tr-▸ ▸A))
        (sub (tr-▸ ▸P) (begin
           tr-Conₘ δ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr q  ≈⟨ ≈ᶜ-refl ∙ tr-⌜⌝-· m ⟩
           tr-Conₘ δ ∙ tr (Mo₁.⌜ m ⌝ M₁.· q)        ∎)))
      (≤ᶜ-reflexive tr-Conₘ-+ᶜ)
      where
      open CR₂
    tr-▸ (var {x = x} {m = m}) = sub
      var
      (begin
         tr-Conₘ (C₁.𝟘ᶜ C₁., x ≔ Mo₁.⌜ m ⌝)   ≡⟨ CQ.tr-,≔ ⟩
         tr-Conₘ C₁.𝟘ᶜ C₂., x ≔ tr Mo₁.⌜ m ⌝  ≤⟨ update-monotoneˡ _ tr-Conₘ-𝟘ᶜ-≤ᶜ ⟩
         C₂.𝟘ᶜ C₂., x ≔ tr Mo₁.⌜ m ⌝          ≤⟨ update-monotoneʳ _ (tr-⌜⌝ m) ⟩
         C₂.𝟘ᶜ C₂., x ≔ Mo₂.⌜ tr-Mode m ⌝     ∎)
      where
      open CR₂
    tr-▸ (lamₘ {γ = γ} {m = m} {p = p} {t = t} ▸t) = lamₘ
      (sub (tr-▸ ▸t) (begin
         tr-Conₘ γ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p  ≈⟨ ≈ᶜ-refl ∙ tr-⌜⌝-· m ⟩
         tr-Conₘ γ ∙ tr (Mo₁.⌜ m ⌝ M₁.· p)        ∎))
      where
      open CR₂
    tr-▸ (_∘ₘ_ {γ = γ} {m = m} {δ = δ} {p = p} ▸t ▸u) = sub
      (tr-▸ ▸t ∘ₘ ▸-cong (tr-Mode-ᵐ· m BMΠ) (tr-▸ ▸u))
      (begin
         tr-Conₘ (γ C₁.+ᶜ p C₁.·ᶜ δ)           ≈⟨ tr-Conₘ-+ᶜ ⟩
         tr-Conₘ γ C₂.+ᶜ tr-Conₘ (p C₁.·ᶜ δ)   ≈⟨ +ᶜ-congˡ tr-Conₘ-·ᶜ ⟩
         tr-Conₘ γ C₂.+ᶜ tr p C₂.·ᶜ tr-Conₘ δ  ∎)
      where
      open CR₂
    tr-▸ (prodʷₘ {γ = γ} {m = m} {p = p} {δ = δ} ▸t ▸u) = sub
      (prodʷₘ (▸-cong (tr-Mode-ᵐ· m (BMΣ 𝕨)) (tr-▸ ▸t)) (tr-▸ ▸u))
      (begin
         tr-Conₘ (p C₁.·ᶜ γ C₁.+ᶜ δ)             ≈⟨ tr-Conₘ-+ᶜ ⟩
         tr-Conₘ (p C₁.·ᶜ γ) C₂.+ᶜ tr-Conₘ δ     ≈⟨ +ᶜ-congʳ tr-Conₘ-·ᶜ ⟩
         tr p C₂.·ᶜ tr-Conₘ γ C₂.+ᶜ tr-Conₘ δ    ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneˡ tr-≤-tr-Σ) ⟩
         tr-Σ p C₂.·ᶜ tr-Conₘ γ C₂.+ᶜ tr-Conₘ δ  ∎)
      where
      open CR₂
    tr-▸ (prodˢₘ {γ = γ} {m = m} {p = p} {δ = δ} ▸t ▸u) = sub
      (prodˢₘ (▸-cong (tr-Mode-ᵐ· m (BMΣ 𝕤)) (tr-▸ ▸t)) (tr-▸ ▸u))
      (begin
         tr-Conₘ (p C₁.·ᶜ γ C₁.∧ᶜ δ)             ≤⟨ tr-Conₘ-∧ᶜ ⟩
         tr-Conₘ (p C₁.·ᶜ γ) C₂.∧ᶜ tr-Conₘ δ     ≈⟨ ∧ᶜ-congʳ tr-Conₘ-·ᶜ ⟩
         tr p C₂.·ᶜ tr-Conₘ γ C₂.∧ᶜ tr-Conₘ δ    ≤⟨ ∧ᶜ-monotoneˡ (·ᶜ-monotoneˡ tr-≤-tr-Σ) ⟩
         tr-Σ p C₂.·ᶜ tr-Conₘ γ C₂.∧ᶜ tr-Conₘ δ  ∎)
      where
      open CR₂
    tr-▸ (fstₘ {p = p} m ▸t refl ok) = fstₘ
      (tr-Mode m)
      (▸-cong (tr-Mode-ᵐ· m (BMΣ 𝕤)) (tr-▸ ▸t))
      (sym (tr-Mode-ᵐ· m (BMΣ 𝕤)))
      λ mp≡𝟙 → tr-Σ-≤-𝟙 (ok (tr-Mode-injective mp≡𝟙))
    tr-▸ (sndₘ ▸t) =
      sndₘ (tr-▸ ▸t)
    tr-▸
      (prodrecₘ {γ = γ} {m = m} {r = r} {δ = δ} {p = p} {η = η} {q = q}
         ▸t ▸u ▸Q ok) = sub
      (prodrecₘ (▸-cong (tr-Mode-ᵐ· m BMΠ) (tr-▸ ▸t))
         (sub (tr-▸ ▸u) (begin
            tr-Conₘ δ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr r M₂.· tr-Σ p ∙
            Mo₂.⌜ tr-Mode m ⌝ M₂.· tr r                            ≤⟨ ≤ᶜ-refl ∙ ·-monotoneʳ tr-·-tr-Σ-≤ ∙ ≤-refl ⟩

            tr-Conₘ δ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr (r M₁.· p) ∙
            Mo₂.⌜ tr-Mode m ⌝ M₂.· tr r                            ≈⟨ ≈ᶜ-refl ∙ tr-⌜⌝-· m ∙ tr-⌜⌝-· m ⟩

            tr-Conₘ δ ∙ tr (Mo₁.⌜ m ⌝ M₁.· r M₁.· p) ∙
            tr (Mo₁.⌜ m ⌝ M₁.· r)                                  ∎))
         (tr-∙▸[𝟘ᵐ?] ▸Q) (Prodrec-preserved ≈ᵐ-tr-Mode ok))
      (begin
         tr-Conₘ (r C₁.·ᶜ γ C₁.+ᶜ δ)           ≈⟨ tr-Conₘ-+ᶜ ⟩
         tr-Conₘ (r C₁.·ᶜ γ) C₂.+ᶜ tr-Conₘ δ   ≈⟨ +ᶜ-congʳ tr-Conₘ-·ᶜ ⟩
         tr r C₂.·ᶜ tr-Conₘ γ C₂.+ᶜ tr-Conₘ δ  ∎)
      where
      open CR₂
    tr-▸ zeroₘ =
      sub zeroₘ tr-Conₘ-𝟘ᶜ-≤ᶜ
    tr-▸ (sucₘ ▸t) =
      sucₘ (tr-▸ ▸t)
    tr-▸
      (natrecₘ {γ = γ} {m = m} {δ = δ} {p = p} {r = r} {η = η} {θ = θ}
         {q = q} ▸z ▸s ▸n ▸P) = sub
      (natrecₘ (tr-▸ ▸z)
         (sub (tr-▸ ▸s) (begin
            tr-Conₘ δ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p ∙
            Mo₂.⌜ tr-Mode m ⌝ M₂.· tr r                                ≈⟨ ≈ᶜ-refl ∙ tr-⌜⌝-· m ∙ tr-⌜⌝-· m ⟩

            tr-Conₘ δ ∙ tr (Mo₁.⌜ m ⌝ M₁.· p) ∙ tr (Mo₁.⌜ m ⌝ M₁.· r)  ∎))
         (tr-▸ ▸n)
         (tr-∙▸[𝟘ᵐ?] ▸P))
      tr-Conₘ-nrᶜ
      where
      open import Graded.Modality.Morphism.Forward-instances tr-m
      open import Graded.Modality.Dedicated-nr.Instance
      open CR₂
    tr-▸
      (natrec-no-nrₘ {m = m} {δ = δ} {p = p} {r = r} {η = η} {χ = χ}
         ▸z ▸s ▸n ▸P χ≤γ χ≤δ χ≤η fix) =
      natrec-no-nrₘ (tr-▸ ▸z)
        (sub (tr-▸ ▸s) (begin
           tr-Conₘ δ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p ∙
           Mo₂.⌜ tr-Mode m ⌝ M₂.· tr r                                ≈⟨ ≈ᶜ-refl ∙ tr-⌜⌝-· m ∙ tr-⌜⌝-· m ⟩

           tr-Conₘ δ ∙ tr (Mo₁.⌜ m ⌝ M₁.· p) ∙ tr (Mo₁.⌜ m ⌝ M₁.· r)  ∎))
        (tr-▸ ▸n)
        (tr-∙▸[𝟘ᵐ?] ▸P)
        (tr-Conₘ-monotone χ≤γ)
        (λ ok →
           case 𝟘ᵐ-in-first-if-in-second (inj₁ ok) of λ where
             (inj₁ ok) →
               tr-Conₘ-monotone (χ≤δ ok)
             (inj₂ trivial) → begin
               tr-Conₘ χ  ≡⟨ cong tr-Conₘ (CP₁.≈ᶜ→≡ (CP₁.≈ᶜ-trivial trivial)) ⟩
               tr-Conₘ δ  ∎)
        (λ ⦃ 𝟘-well-behaved = 𝟘-well-behaved ⦄ →
           case 𝟘-well-behaved-in-first-if-in-second
                  (inj₁ 𝟘-well-behaved) of λ where
             (inj₁ 𝟘-well-behaved) →
               tr-Conₘ-monotone
                 (χ≤η ⦃ 𝟘-well-behaved = 𝟘-well-behaved ⦄)
             (inj₂ trivial) → begin
               tr-Conₘ χ  ≡⟨ cong tr-Conₘ (CP₁.≈ᶜ→≡ (CP₁.≈ᶜ-trivial trivial)) ⟩
               tr-Conₘ η  ∎)
        (begin
           tr-Conₘ χ                                    ≤⟨ tr-Conₘ-monotone fix ⟩

           tr-Conₘ (δ C₁.+ᶜ p C₁.·ᶜ η C₁.+ᶜ r C₁.·ᶜ χ)  ≈⟨ ≈ᶜ-trans tr-Conₘ-+ᶜ $ +ᶜ-congˡ $
                                                           ≈ᶜ-trans tr-Conₘ-+ᶜ $
                                                           +ᶜ-cong tr-Conₘ-·ᶜ tr-Conₘ-·ᶜ ⟩
           tr-Conₘ δ C₂.+ᶜ tr p C₂.·ᶜ tr-Conₘ η C₂.+ᶜ
           tr r C₂.·ᶜ tr-Conₘ χ                         ∎)
      where
      open import Graded.Modality.Morphism.Forward-instances tr-m
      open CR₂
    tr-▸ (emptyrecₘ {m = m} ▸t ▸A) = sub
      (emptyrecₘ (▸-cong (tr-Mode-ᵐ· m BMΠ) (tr-▸ ▸t)) (tr-▸[𝟘ᵐ?] ▸A))
      (≤ᶜ-reflexive tr-Conₘ-·ᶜ)
    tr-▸ starʷₘ = sub starʷₘ tr-Conₘ-𝟘ᶜ-≤ᶜ
    tr-▸ {m = m} (starˢₘ {γ = γ} prop) =
      let _ , prop′ , γ≤ = lemma starˢ-sink-preserved prop
      in  sub (starˢₘ prop′) γ≤
      where
      open CR₂
      lemma : {b b′ : Bool} →
        b ≡ b′ →
        (T (not b) → C₁.𝟘ᶜ C₁.≈ᶜ γ) →
          ∃ λ γ′ →
            (T (not b′) → C₂.𝟘ᶜ C₂.≈ᶜ γ′) ×
            tr-Conₘ (Mo₁.⌜ m ⌝ C₁.·ᶜ γ) C₂.≤ᶜ Mo₂.⌜ tr-Mode m ⌝ C₂.·ᶜ γ′
      lemma {(false)} refl prop =
        _ , (λ _ → ≈ᶜ-refl) , (begin
          tr-Conₘ (Mo₁.⌜ m ⌝ C₁.·ᶜ γ)       ≈⟨ tr-Conₘ-·ᶜ ⟩
          tr Mo₁.⌜ m ⌝ C₂.·ᶜ tr-Conₘ γ      ≈⟨ ·ᶜ-congˡ (CQ.tr-≈ᶜ (CP₁.≈ᶜ-sym (prop _))) ⟩
          tr Mo₁.⌜ m ⌝ C₂.·ᶜ tr-Conₘ C₁.𝟘ᶜ  ≤⟨ ·ᶜ-monotone tr-Conₘ-𝟘ᶜ-≤ᶜ (tr-⌜⌝ m) ⟩
          Mo₂.⌜ tr-Mode m ⌝ C₂.·ᶜ C₂.𝟘ᶜ     ∎)
      lemma {(true)} refl prop =
        _ , (λ ()) , (begin
          tr-Conₘ (Mo₁.⌜ m ⌝ C₁.·ᶜ γ)        ≈⟨ tr-Conₘ-·ᶜ ⟩
          tr Mo₁.⌜ m ⌝ C₂.·ᶜ tr-Conₘ γ       ≤⟨ ·ᶜ-monotoneˡ (tr-⌜⌝ m) ⟩
          Mo₂.⌜ tr-Mode m ⌝ C₂.·ᶜ tr-Conₘ γ  ∎)

    tr-▸ {m = m} (unitrecₘ {γ = γ} {p = p} {δ = δ} ▸t ▸u ▸A ok) =
      sub (unitrecₘ (▸-cong (tr-Mode-ᵐ· m BMΠ) (tr-▸ ▸t)) (tr-▸ ▸u)
            (tr-∙▸[𝟘ᵐ?] ▸A) (Unitrec-preserved ≈ᵐ-tr-Mode ok))
          (begin
            tr-Conₘ (p C₁.·ᶜ γ C₁.+ᶜ δ)           ≈⟨ tr-Conₘ-+ᶜ ⟩
            tr-Conₘ (p C₁.·ᶜ γ) C₂.+ᶜ tr-Conₘ δ   ≈⟨ +ᶜ-congʳ tr-Conₘ-·ᶜ ⟩
            tr p C₂.·ᶜ tr-Conₘ γ C₂.+ᶜ tr-Conₘ δ  ∎)
      where
      open CR₂
    tr-▸ (Idₘ ok ▸A ▸t ▸u) = sub
      (Idₘ (ok ∘→ Id-erased-preserved .proj₂) (tr-▸[𝟘ᵐ?] ▸A) (tr-▸ ▸t)
         (tr-▸ ▸u))
      (≤ᶜ-reflexive tr-Conₘ-+ᶜ)
    tr-▸ (Id₀ₘ ok ▸A ▸t ▸u) = sub
      (Id₀ₘ (Id-erased-preserved .proj₁ ok) (tr-▸[𝟘ᵐ?] ▸A)
         (tr-▸[𝟘ᵐ?] ▸t) (tr-▸[𝟘ᵐ?] ▸u))
      tr-Conₘ-𝟘ᶜ-≤ᶜ
    tr-▸ rflₘ =
      sub rflₘ tr-Conₘ-𝟘ᶜ-≤ᶜ
    tr-▸
      (Jₘ {m} {γ₂} {γ₃} {p} {q} {γ₄} {γ₅} {γ₆}
         _ ▸A ▸t ▸B ▸u ▸v ▸w) = sub
      (Jₘ-generalised (tr-▸[𝟘ᵐ?] ▸A) (tr-▸ ▸t)
         (sub (tr-▸ ▸B) $ begin
            tr-Conₘ γ₃ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p ∙
            Mo₂.⌜ tr-Mode m ⌝ M₂.· tr q                                 ≈⟨ ≈ᶜ-refl ∙ tr-⌜⌝-· m ∙ tr-⌜⌝-· m ⟩

            tr-Conₘ γ₃ ∙ tr (Mo₁.⌜ m ⌝ M₁.· p) ∙ tr (Mo₁.⌜ m ⌝ M₁.· q)  ∎)
         (tr-▸ ▸u) (tr-▸ ▸v) (tr-▸ ▸w))
      (begin
         tr-Conₘ (M₁.ω C₁.·ᶜ (γ₂ C₁.∧ᶜ γ₃ C₁.∧ᶜ γ₄ C₁.∧ᶜ γ₅ C₁.∧ᶜ γ₆))   ≈⟨ tr-Conₘ-·ᶜ ⟩

         tr M₁.ω C₂.·ᶜ tr-Conₘ (γ₂ C₁.∧ᶜ γ₃ C₁.∧ᶜ γ₄ C₁.∧ᶜ γ₅ C₁.∧ᶜ γ₆)  ≤⟨ flip ·ᶜ-monotone tr-ω $
                                                                            ≤ᶜ-trans tr-Conₘ-∧ᶜ $ ∧ᶜ-monotoneʳ $
                                                                            ≤ᶜ-trans tr-Conₘ-∧ᶜ $ ∧ᶜ-monotoneʳ $
                                                                            ≤ᶜ-trans tr-Conₘ-∧ᶜ $ ∧ᶜ-monotoneʳ
                                                                            tr-Conₘ-∧ᶜ ⟩
         M₂.ω C₂.·ᶜ
         (tr-Conₘ γ₂ C₂.∧ᶜ tr-Conₘ γ₃ C₂.∧ᶜ tr-Conₘ γ₄ C₂.∧ᶜ
          tr-Conₘ γ₅ C₂.∧ᶜ tr-Conₘ γ₆)                                   ∎)
      where
      open CR₂
    tr-▸
      (Jₘ′ {m} {γ₂} {p} {q} {γ₃} {γ₄} {γ₅} {γ₆}
         ≡some ▸A ▸t ▸B ▸u ▸v ▸w) = sub
      (Jₘ′-generalised
         (≤ᵉᵐ→≡some→≡not-none
            (erased-matches-for-J-preserved ≈ᵐ-tr-Mode) ≡some
            .proj₂)
         (tr-▸[𝟘ᵐ?] ▸A) (▸-cong (tr-Mode-ᵐ·-+ m) (tr-▸ ▸t))
         (sub (tr-▸ ▸B) $ begin
            tr-Conₘ γ₃ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p ∙
            Mo₂.⌜ tr-Mode m ⌝ M₂.· tr q                                 ≈⟨ ≈ᶜ-refl ∙ tr-⌜⌝-· m ∙ tr-⌜⌝-· m ⟩

            tr-Conₘ γ₃ ∙ tr (Mo₁.⌜ m ⌝ M₁.· p) ∙ tr (Mo₁.⌜ m ⌝ M₁.· q)  ∎)
         (tr-▸ ▸u) (▸-cong (tr-Mode-ᵐ·-+ m) (tr-▸ ▸v))
         (▸-cong (tr-Mode-ᵐ·-+ m) (tr-▸ ▸w)))
      (begin
         tr-Conₘ (M₁.ω C₁.·ᶜ (γ₂ C₁.∧ᶜ γ₃ C₁.∧ᶜ γ₄ C₁.∧ᶜ γ₅ C₁.∧ᶜ γ₆))   ≈⟨ tr-Conₘ-·ᶜ ⟩

         tr M₁.ω C₂.·ᶜ tr-Conₘ (γ₂ C₁.∧ᶜ γ₃ C₁.∧ᶜ γ₄ C₁.∧ᶜ γ₅ C₁.∧ᶜ γ₆)  ≤⟨ flip ·ᶜ-monotone tr-ω $
                                                                            ≤ᶜ-trans tr-Conₘ-∧ᶜ $ ∧ᶜ-monotoneʳ $
                                                                            ≤ᶜ-trans tr-Conₘ-∧ᶜ $ ∧ᶜ-monotoneʳ $
                                                                            ≤ᶜ-trans tr-Conₘ-∧ᶜ $ ∧ᶜ-monotoneʳ
                                                                            tr-Conₘ-∧ᶜ ⟩
         M₂.ω C₂.·ᶜ
         (tr-Conₘ γ₂ C₂.∧ᶜ tr-Conₘ γ₃ C₂.∧ᶜ tr-Conₘ γ₄ C₂.∧ᶜ
          tr-Conₘ γ₅ C₂.∧ᶜ tr-Conₘ γ₆)                                   ∎)
      where
      open CR₂
    tr-▸ (J₀ₘ ≡all ▸A ▸t ▸B ▸u ▸v ▸w) = J₀ₘ
      (≤ᵉᵐ→≡all→≡all (erased-matches-for-J-preserved ≈ᵐ-tr-Mode) ≡all)
      (tr-▸[𝟘ᵐ?] ▸A) (tr-▸[𝟘ᵐ?] ▸t) (tr-∙∙▸[𝟘ᵐ?] ▸B) (tr-▸ ▸u)
      (tr-▸[𝟘ᵐ?] ▸v) (tr-▸[𝟘ᵐ?] ▸w)
    tr-▸ (Kₘ {m} {γ₂} {γ₃} {p} {γ₄} {γ₅} _ ▸A ▸t ▸B ▸u ▸v) = sub
      (Kₘ-generalised (tr-▸[𝟘ᵐ?] ▸A) (tr-▸ ▸t)
         (sub (tr-▸ ▸B) $ begin
            tr-Conₘ γ₃ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p  ≈⟨ ≈ᶜ-refl ∙ tr-⌜⌝-· m ⟩
            tr-Conₘ γ₃ ∙ tr (Mo₁.⌜ m ⌝ M₁.· p)        ∎)
         (tr-▸ ▸u) (tr-▸ ▸v))
      (begin
         tr-Conₘ (M₁.ω C₁.·ᶜ (γ₂ C₁.∧ᶜ γ₃ C₁.∧ᶜ γ₄ C₁.∧ᶜ γ₅))   ≈⟨ tr-Conₘ-·ᶜ ⟩

         tr M₁.ω C₂.·ᶜ tr-Conₘ (γ₂ C₁.∧ᶜ γ₃ C₁.∧ᶜ γ₄ C₁.∧ᶜ γ₅)  ≤⟨ flip ·ᶜ-monotone tr-ω $
                                                                   ≤ᶜ-trans tr-Conₘ-∧ᶜ $ ∧ᶜ-monotoneʳ $
                                                                   ≤ᶜ-trans tr-Conₘ-∧ᶜ $ ∧ᶜ-monotoneʳ
                                                                   tr-Conₘ-∧ᶜ ⟩
         M₂.ω C₂.·ᶜ
         (tr-Conₘ γ₂ C₂.∧ᶜ tr-Conₘ γ₃ C₂.∧ᶜ tr-Conₘ γ₄ C₂.∧ᶜ
          tr-Conₘ γ₅)                                           ∎)
      where
      open CR₂
    tr-▸ (Kₘ′ {m} {γ₂} {p} {γ₃} {γ₄} {γ₅} ≡some ▸A ▸t ▸B ▸u ▸v) = sub
      (Kₘ′-generalised
         (≤ᵉᵐ→≡some→≡not-none
            (erased-matches-for-K-preserved ≈ᵐ-tr-Mode) ≡some
            .proj₂)
         (tr-▸[𝟘ᵐ?] ▸A) (▸-cong (tr-Mode-ᵐ· m _) (tr-▸ ▸t))
         (sub (tr-▸ ▸B) $ begin
            tr-Conₘ γ₃ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p  ≈⟨ ≈ᶜ-refl ∙ tr-⌜⌝-· m ⟩
            tr-Conₘ γ₃ ∙ tr (Mo₁.⌜ m ⌝ M₁.· p)        ∎)
         (tr-▸ ▸u) (▸-cong (tr-Mode-ᵐ· m _) (tr-▸ ▸v)))
      (begin
         tr-Conₘ (M₁.ω C₁.·ᶜ (γ₂ C₁.∧ᶜ γ₃ C₁.∧ᶜ γ₄ C₁.∧ᶜ γ₅))   ≈⟨ tr-Conₘ-·ᶜ ⟩

         tr M₁.ω C₂.·ᶜ tr-Conₘ (γ₂ C₁.∧ᶜ γ₃ C₁.∧ᶜ γ₄ C₁.∧ᶜ γ₅)  ≤⟨ flip ·ᶜ-monotone tr-ω $
                                                                   ≤ᶜ-trans tr-Conₘ-∧ᶜ $ ∧ᶜ-monotoneʳ $
                                                                   ≤ᶜ-trans tr-Conₘ-∧ᶜ $ ∧ᶜ-monotoneʳ
                                                                   tr-Conₘ-∧ᶜ ⟩
         M₂.ω C₂.·ᶜ
         (tr-Conₘ γ₂ C₂.∧ᶜ tr-Conₘ γ₃ C₂.∧ᶜ tr-Conₘ γ₄ C₂.∧ᶜ
          tr-Conₘ γ₅)                                           ∎)
      where
      open CR₂
    tr-▸ (K₀ₘ ≡none ▸A ▸t ▸B ▸u ▸v) = K₀ₘ
      (≤ᵉᵐ→≡all→≡all (erased-matches-for-K-preserved ≈ᵐ-tr-Mode) ≡none)
      (tr-▸[𝟘ᵐ?] ▸A) (tr-▸[𝟘ᵐ?] ▸t) (tr-∙▸[𝟘ᵐ?] ▸B) (tr-▸ ▸u)
      (tr-▸[𝟘ᵐ?] ▸v)
    tr-▸ ([]-congₘ ▸A ▸t ▸u ▸v) = sub
      ([]-congₘ (tr-▸[𝟘ᵐ?] ▸A) (tr-▸[𝟘ᵐ?] ▸t)
         (tr-▸[𝟘ᵐ?] ▸u) (tr-▸[𝟘ᵐ?] ▸v))
      tr-Conₘ-𝟘ᶜ-≤ᶜ
    tr-▸ (sub ▸t γ≤δ) =
      sub (tr-▸ ▸t) (tr-Conₘ-monotone γ≤δ)

    private

      -- A variant of tr-▸.

      tr-▸[𝟘ᵐ?] :
        γ U₁.▸[ Mo₁.𝟘ᵐ? ] t → tr-Conₘ γ U₂.▸[ Mo₂.𝟘ᵐ? ] tr-Term t
      tr-▸[𝟘ᵐ?] {γ = γ} {t = t} = Mo₁.𝟘ᵐ?-elim
        (λ m → γ U₁.▸[ m ] t → tr-Conₘ γ U₂.▸[ Mo₂.𝟘ᵐ? ] tr-Term t)
        (▸-cong (sym Mo₂.𝟘ᵐ?≡𝟘ᵐ) ∘→ tr-▸)
        (λ not-ok ▸t → Mo₂.𝟘ᵐ?-elim
           (λ m → tr-Conₘ γ U₂.▸[ m ] tr-Term t)
           (λ ⦃ ok = ok ⦄ →
              sub (▸-𝟘 (tr-▸ ▸t)) (tr-Conₘ-≤ᶜ-𝟘ᶜ not-ok ok))
           (λ _ → tr-▸ ▸t))

      -- A variant of tr-▸[𝟘ᵐ?].

      tr-▸[𝟘ᵐ?]′ :
        γ U₁.▸[ m ] t → ∃ λ δ → δ U₂.▸[ Mo₂.𝟘ᵐ? ] tr-Term t
      tr-▸[𝟘ᵐ?]′ {t} ▸t = Mo₂.𝟘ᵐ?-elim
        (λ m → ∃ λ δ → δ U₂.▸[ m ] tr-Term t)
        (_ , ▸-𝟘 (tr-▸ ▸t))
        (λ not-ok →
             _
           , ▸-cong (Mo₂.Mode-propositional-without-𝟘ᵐ not-ok)
               (tr-▸ ▸t))

      -- A variant of tr-▸.

      tr-∙▸[𝟘ᵐ?] :
        γ ∙ Mo₁.⌜ Mo₁.𝟘ᵐ? ⌝ M₁.· p U₁.▸[ Mo₁.𝟘ᵐ? ] t →
        tr-Conₘ γ ∙ Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr p U₂.▸[ Mo₂.𝟘ᵐ? ] tr-Term t
      tr-∙▸[𝟘ᵐ?] {γ = γ} {p = p} {t = t} = Mo₁.𝟘ᵐ?-elim
        (λ m →
           γ ∙ Mo₁.⌜ m ⌝ M₁.· p U₁.▸[ m ] t →
           tr-Conₘ γ ∙ Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr p U₂.▸[ Mo₂.𝟘ᵐ? ]
             tr-Term t)
        (λ ⦃ ok = ok ⦄ ▸t →
           sub (▸-cong (sym Mo₂.𝟘ᵐ?≡𝟘ᵐ) (tr-▸ ▸t)) (begin
             tr-Conₘ γ ∙ Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr p  ≈⟨ ≈ᶜ-refl ∙
                                                       Mo₂.𝟘ᵐ?-elim (λ m → Mo₂.⌜ m ⌝ M₂.· tr p ≡ M₂.𝟘)
                                                         (M₂.·-zeroˡ _)
                                                         (λ not-ok → ⊥-elim (not-ok (𝟘ᵐ-in-second-if-in-first ok))) ⟩
             tr-Conₘ γ ∙ M₂.𝟘                       ≈˘⟨ ≈ᶜ-refl ∙ tr-𝟘-≡-𝟘ᵐ ok ⟩
             tr-Conₘ γ ∙ tr M₁.𝟘                    ≈˘⟨ ≈ᶜ-refl ∙ cong tr (M₁.·-zeroˡ _) ⟩
             tr-Conₘ γ ∙ tr (M₁.𝟘 M₁.· p)           ∎))
        (λ not-ok ▸t → Mo₂.𝟘ᵐ?-elim
           (λ m → tr-Conₘ γ ∙ Mo₂.⌜ m ⌝ M₂.· tr p U₂.▸[ m ] tr-Term t)
           (λ ⦃ ok = ok ⦄ →
              sub (▸-𝟘 (tr-▸ ▸t)) (begin
                tr-Conₘ γ ∙ M₂.𝟘 M₂.· tr p  ≤⟨ tr-Conₘ-≤ᶜ-𝟘ᶜ not-ok ok ∙ ≤-reflexive (M₂.·-zeroˡ _) ⟩
                C₂.𝟘ᶜ                       ∎))
           (λ not-ok →
              sub (tr-▸ ▸t) (begin
                tr-Conₘ γ ∙ M₂.𝟙 M₂.· tr p    ≈⟨ ≈ᶜ-refl ∙ M₂.·-identityˡ _ ⟩
                tr-Conₘ γ ∙ tr p              ≈˘⟨ ≈ᶜ-refl ∙ cong tr (M₁.·-identityˡ _) ⟩
                tr-Conₘ γ ∙ tr (M₁.𝟙 M₁.· p)  ∎)))
        where
        open CR₂

      -- A variant of tr-∙▸[𝟘ᵐ?].

      tr-∙▸[𝟘ᵐ?]′ :
        γ ∙ Mo₁.⌜ m ⌝ M₁.· p U₁.▸[ m ] t →
        ∃ λ δ → δ ∙ Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr p U₂.▸[ Mo₂.𝟘ᵐ? ] tr-Term t
      tr-∙▸[𝟘ᵐ?]′ {γ} {m = 𝟘ᵐ[ ok ]} {p} ▸t =
          tr-Conₘ γ
        , sub (▸-cong (sym Mo₂.𝟘ᵐ?≡𝟘ᵐ) (tr-▸ ▸t)) (begin
            tr-Conₘ γ ∙ Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr p  ≈⟨ ≈ᶜ-refl ∙
                                                      Mo₂.𝟘ᵐ?-elim (λ m → Mo₂.⌜ m ⌝ M₂.· tr p ≡ M₂.𝟘)
                                                        (M₂.·-zeroˡ _)
                                                        (λ not-ok → ⊥-elim (not-ok (𝟘ᵐ-in-second-if-in-first ok))) ⟩
            tr-Conₘ γ ∙ M₂.𝟘                       ≈˘⟨ ≈ᶜ-refl ∙ tr-𝟘-≡-𝟘ᵐ ok ⟩
            tr-Conₘ γ ∙ tr M₁.𝟘                    ≈˘⟨ ≈ᶜ-refl ∙ cong tr (M₁.·-zeroˡ _) ⟩
            tr-Conₘ γ ∙ tr (M₁.𝟘 M₁.· p)           ∎)
        where
        open CR₂
      tr-∙▸[𝟘ᵐ?]′ {γ} {m = 𝟙ᵐ} {p} {t} ▸t = Mo₂.𝟘ᵐ?-elim
        (λ m → ∃ λ δ → δ ∙ Mo₂.⌜ m ⌝ M₂.· tr p U₂.▸[ m ] tr-Term t)
        ( C₂.𝟘ᶜ
        , sub (▸-𝟘 (tr-▸ ▸t)) (begin
            C₂.𝟘ᶜ ∙ M₂.𝟘 M₂.· tr p  ≈⟨ ≈ᶜ-refl ∙ M₂.·-zeroˡ _ ⟩
            C₂.𝟘ᶜ                   ∎)
        )
        (λ not-ok →
             tr-Conₘ γ
           , sub (tr-▸ ▸t) (begin
               tr-Conₘ γ ∙ M₂.𝟙 M₂.· tr p    ≈⟨ ≈ᶜ-refl ∙ M₂.·-identityˡ _ ⟩
               tr-Conₘ γ ∙ tr p              ≈˘⟨ ≈ᶜ-refl ∙ cong tr (M₁.·-identityˡ _) ⟩
               tr-Conₘ γ ∙ tr (M₁.𝟙 M₁.· p)  ∎))
        where
        open CR₂

      -- A variant of tr-▸.

      tr-∙∙▸[𝟘ᵐ?] :
        γ ∙ Mo₁.⌜ Mo₁.𝟘ᵐ? ⌝ M₁.· p ∙ Mo₁.⌜ Mo₁.𝟘ᵐ? ⌝ M₁.· q
          U₁.▸[ Mo₁.𝟘ᵐ? ] t →
        tr-Conₘ γ ∙ Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr p ∙
          Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr q
          U₂.▸[ Mo₂.𝟘ᵐ? ] tr-Term t
      tr-∙∙▸[𝟘ᵐ?] {γ} {p} {q} {t} = Mo₁.𝟘ᵐ?-elim
        (λ m →
           γ ∙ Mo₁.⌜ m ⌝ M₁.· p ∙ Mo₁.⌜ m ⌝ M₁.· q U₁.▸[ m ] t →
           tr-Conₘ γ ∙ Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr p ∙
             Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr q
             U₂.▸[ Mo₂.𝟘ᵐ? ] tr-Term t)
        (λ ⦃ ok = ok ⦄ ▸t →
           sub (▸-cong (sym Mo₂.𝟘ᵐ?≡𝟘ᵐ) (tr-▸ ▸t)) $ begin
             tr-Conₘ γ ∙ Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr p ∙
             Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr q                        ≈⟨ Mo₂.𝟘ᵐ?-elim
                                                                   (λ m →
                                                                      tr-Conₘ γ ∙ Mo₂.⌜ m ⌝ M₂.· tr p ∙ Mo₂.⌜ m ⌝ M₂.· tr q C₂.≈ᶜ
                                                                      tr-Conₘ γ ∙ M₂.𝟘 ∙ M₂.𝟘)
                                                                   (≈ᶜ-refl ∙ M₂.·-zeroˡ _ ∙ M₂.·-zeroˡ _)
                                                                   (λ not-ok → ⊥-elim (not-ok (𝟘ᵐ-in-second-if-in-first ok))) ⟩
             tr-Conₘ γ ∙ M₂.𝟘 ∙ M₂.𝟘                          ≈˘⟨ ≈ᶜ-refl ∙ tr-𝟘-≡-𝟘ᵐ ok ∙ tr-𝟘-≡-𝟘ᵐ ok ⟩
             tr-Conₘ γ ∙ tr M₁.𝟘 ∙ tr M₁.𝟘                    ≈˘⟨ ≈ᶜ-refl ∙ cong tr (M₁.·-zeroˡ _) ∙ cong tr (M₁.·-zeroˡ _) ⟩
             tr-Conₘ γ ∙ tr (M₁.𝟘 M₁.· p) ∙ tr (M₁.𝟘 M₁.· q)  ∎)
        (λ not-ok ▸t → Mo₂.𝟘ᵐ?-elim
           (λ m →
              tr-Conₘ γ ∙ Mo₂.⌜ m ⌝ M₂.· tr p ∙ Mo₂.⌜ m ⌝ M₂.· tr q
                U₂.▸[ m ] tr-Term t)
           (λ ⦃ ok = ok ⦄ →
              sub (▸-𝟘 (tr-▸ ▸t)) $ begin
                tr-Conₘ γ ∙ M₂.𝟘 M₂.· tr p ∙ M₂.𝟘 M₂.· tr q  ≤⟨ tr-Conₘ-≤ᶜ-𝟘ᶜ not-ok ok ∙ ≤-reflexive (M₂.·-zeroˡ _) ∙
                                                                ≤-reflexive (M₂.·-zeroˡ _) ⟩
                C₂.𝟘ᶜ                                        ∎)
           (λ not-ok →
              sub (tr-▸ ▸t) $ begin
                tr-Conₘ γ ∙ M₂.𝟙 M₂.· tr p ∙ M₂.𝟙 M₂.· tr q      ≈⟨ ≈ᶜ-refl ∙ M₂.·-identityˡ _ ∙ M₂.·-identityˡ _ ⟩
                tr-Conₘ γ ∙ tr p ∙ tr q                          ≈˘⟨ ≈ᶜ-refl ∙ cong tr (M₁.·-identityˡ _) ∙ cong tr (M₁.·-identityˡ _) ⟩
                tr-Conₘ γ ∙ tr (M₁.𝟙 M₁.· p) ∙ tr (M₁.𝟙 M₁.· q)  ∎))
        where
        open CR₂

      -- A variant of tr-∙∙▸[𝟘ᵐ?].

      tr-∙∙▸[𝟘ᵐ?]′ :
        γ ∙ Mo₁.⌜ m ⌝ M₁.· p ∙ Mo₁.⌜ m ⌝ M₁.· q U₁.▸[ m ] t →
        ∃ λ δ →
            δ ∙ Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr p ∙ Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr q
              U₂.▸[ Mo₂.𝟘ᵐ? ] tr-Term t
      tr-∙∙▸[𝟘ᵐ?]′ {γ} {m = 𝟘ᵐ[ ok ]} {p} {q} ▸t =
          tr-Conₘ γ
        , sub (▸-cong (sym Mo₂.𝟘ᵐ?≡𝟘ᵐ) (tr-▸ ▸t)) (begin
            tr-Conₘ γ ∙ Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr p ∙
            Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr q                        ≈⟨ Mo₂.𝟘ᵐ?-elim
                                                                  (λ m →
                                                                     tr-Conₘ γ ∙ Mo₂.⌜ m ⌝ M₂.· tr p ∙ Mo₂.⌜ m ⌝ M₂.· tr q C₂.≈ᶜ
                                                                     tr-Conₘ γ ∙ M₂.𝟘 ∙ M₂.𝟘)
                                                                  (≈ᶜ-refl ∙ M₂.·-zeroˡ _ ∙ M₂.·-zeroˡ _)
                                                                  (λ not-ok → ⊥-elim (not-ok (𝟘ᵐ-in-second-if-in-first ok))) ⟩
            tr-Conₘ γ ∙ M₂.𝟘 ∙ M₂.𝟘                          ≈˘⟨ ≈ᶜ-refl ∙ tr-𝟘-≡-𝟘ᵐ ok ∙ tr-𝟘-≡-𝟘ᵐ ok ⟩
            tr-Conₘ γ ∙ tr M₁.𝟘 ∙ tr M₁.𝟘                    ≈˘⟨ ≈ᶜ-refl ∙ cong tr (M₁.·-zeroˡ _) ∙ cong tr (M₁.·-zeroˡ _) ⟩
            tr-Conₘ γ ∙ tr (M₁.𝟘 M₁.· p) ∙ tr (M₁.𝟘 M₁.· q)  ∎)
        where
        open CR₂
      tr-∙∙▸[𝟘ᵐ?]′ {γ} {m = 𝟙ᵐ} {p} {q} {t} ▸t = Mo₂.𝟘ᵐ?-elim
        (λ m →
           ∃ λ δ →
               δ ∙ Mo₂.⌜ m ⌝ M₂.· tr p ∙ Mo₂.⌜ m ⌝ M₂.· tr q
                 U₂.▸[ m ] tr-Term t)
        ( C₂.𝟘ᶜ
        , sub (▸-𝟘 (tr-▸ ▸t)) (begin
            C₂.𝟘ᶜ ∙ M₂.𝟘 M₂.· tr p ∙ M₂.𝟘 M₂.· tr q  ≈⟨ ≈ᶜ-refl ∙ M₂.·-zeroˡ _ ∙ M₂.·-zeroˡ _ ⟩
            C₂.𝟘ᶜ                                    ∎)
        )
        (λ _ →
             tr-Conₘ γ
           , sub (tr-▸ ▸t) (begin
               tr-Conₘ γ ∙ M₂.𝟙 M₂.· tr p ∙ M₂.𝟙 M₂.· tr q      ≈⟨ ≈ᶜ-refl ∙ M₂.·-identityˡ _ ∙ M₂.·-identityˡ _ ⟩
               tr-Conₘ γ ∙ tr p ∙ tr q                          ≈˘⟨ ≈ᶜ-refl ∙ cong tr (M₁.·-identityˡ _) ∙ cong tr (M₁.·-identityˡ _) ⟩
               tr-Conₘ γ ∙ tr (M₁.𝟙 M₁.· p) ∙ tr (M₁.𝟙 M₁.· q)  ∎))
        where
        open CR₂

------------------------------------------------------------------------
-- If certain properties hold after translation by order embeddings
-- that reflect usage restrictions, then they hold also before
-- translation

module Is-order-embedding
  (tr-emb   : Is-order-embedding 𝕄₁ 𝕄₂ tr)
  (tr-Σ-emb : Is-Σ-order-embedding 𝕄₁ 𝕄₂ tr tr-Σ)
  (r        : Are-reflecting-usage-restrictions R₁ R₂ tr tr-Σ)
  where

  open Are-reflecting-usage-restrictions r
  open CQ.Is-order-embedding tr-emb
  open CQ.Is-Σ-order-embedding tr-Σ-emb
  open M.Is-order-embedding tr-emb
  open M.Is-Σ-order-embedding tr-Σ-emb
  open MQ.Is-order-embedding tr-emb tr-Σ-morphism

  -- Preservation of _◂_∈_.

  tr-◂∈⁻¹ : x U₂.◂ tr p ∈ tr-Conₘ γ → x U₁.◂ p ∈ γ
  tr-◂∈⁻¹ = λ x → tr-◂∈⁻¹′ x refl
    where
    tr-◂∈⁻¹′ : x U₂.◂ p′ ∈ tr-Conₘ γ → p′ ≡ tr p → x U₁.◂ p ∈ γ
    tr-◂∈⁻¹′ {γ = ε}     ()
    tr-◂∈⁻¹′ {γ = _ ∙ _} (there x) refl = there (tr-◂∈⁻¹ x)
    tr-◂∈⁻¹′ {γ = _ ∙ _} here      eq   =
      PE.subst (_ U₁.◂_∈ _) (tr-injective eq) here

  opaque

    -- Preservation of Usage-restrictions-satisfied.

    Usage-restrictions-satisfied-tr-Term :
      m₁ ≳ᵐ m₂ →
      RS₂.Usage-restrictions-satisfied m₂ (tr-Term t) →
      RS₁.Usage-restrictions-satisfied m₁ t
    Usage-restrictions-satisfied-tr-Term = flip lemma _
      where
      lemma :
        m₁ ≳ᵐ m₂ →
        (t : Term M₁ n) →
        RS₂.Usage-restrictions-satisfied m₂ (tr-Term t) →
        RS₁.Usage-restrictions-satisfied m₁ t

      lemma-𝟘ᵐ?-𝟘ᵐ? :
        RS₂.Usage-restrictions-satisfied Mo₂.𝟘ᵐ? (tr-Term t) →
        RS₁.Usage-restrictions-satisfied Mo₁.𝟘ᵐ? t
      lemma-𝟘ᵐ?-𝟘ᵐ? {t} = Mo₁.𝟘ᵐ?-elim
        (λ m →
           RS₂.Usage-restrictions-satisfied Mo₂.𝟘ᵐ? (tr-Term t) →
           RS₁.Usage-restrictions-satisfied m t)
        (λ ⦃ ok = ok₁ ⦄ →
           Mo₂.𝟘ᵐ?-elim
             (λ m →
                RS₂.Usage-restrictions-satisfied m (tr-Term t) →
                RS₁.Usage-restrictions-satisfied 𝟘ᵐ t)
             (lemma [ 𝟘ᵐ ] _)
             (λ not-ok₂ →
                ⊥-elim $ not-ok₂ (𝟘ᵐ-in-second-if-in-first ok₁)))
        (λ not-ok₁ →
           Mo₂.𝟘ᵐ?-elim
             (λ m →
                RS₂.Usage-restrictions-satisfied m (tr-Term t) →
                RS₁.Usage-restrictions-satisfied 𝟙ᵐ t)
             (λ ⦃ ok = ok₂ ⦄ →
                lemma (𝟙ᵐ≳𝟘ᵐ (trivial not-ok₁ ok₂)) _)
             (λ _ → lemma [ 𝟙ᵐ ] _))

      lemma-𝟘ᵐ? :
        _≳ᵐ_ {𝕄₁ = 𝕄₁} {𝕄₂ = 𝕄₂} 𝟙ᵐ 𝟘ᵐ[ ok₂ ] →
        RS₂.Usage-restrictions-satisfied Mo₂.𝟘ᵐ? (tr-Term t) →
        RS₁.Usage-restrictions-satisfied m t
      lemma-𝟘ᵐ? 𝟙≳𝟘 =
        RS₁.Usage-restrictions-satisfied-𝟙ᵐ→ ∘→
        lemma (subst (_ ≳ᵐ_) (sym Mo₂.𝟘ᵐ?≡𝟘ᵐ) 𝟙≳𝟘) _

      lemma-ᵐ·-+ :
        m₁ ≳ᵐ m₂ →
        RS₂.Usage-restrictions-satisfied
          (m₂ Mo₂.ᵐ· (tr p M₂.+ tr q)) (tr-Term t) →
        RS₁.Usage-restrictions-satisfied (m₁ Mo₁.ᵐ· (p M₁.+ q)) t
      lemma-ᵐ·-+ {m₂} m₁≳m₂ =
        lemma (ᵐ·≳ᵐᵐ· m₁≳m₂) _ ∘→
        subst (flip Usage-restrictions-satisfied _)
          (cong (m₂ Mo₂.ᵐ·_) $ sym tr-+)

      lemma {m₁} m₁≳m₂ = λ where
        (var _) varᵤ →
          RS₁.varᵤ
        Empty Emptyᵤ →
          RS₁.Emptyᵤ
        (emptyrec _ _ _) (emptyrecᵤ A t) →
          RS₁.emptyrecᵤ (lemma-𝟘ᵐ?-𝟘ᵐ? A) (lemma (ᵐ·≳ᵐᵐ· m₁≳m₂) _ t)
        (Unit _) Unitᵤ →
          RS₁.Unitᵤ
        (star _) starᵤ →
          RS₁.starᵤ
        (unitrec _ _ _ _ _) (unitrecᵤ ok A t u) →
          RS₁.unitrecᵤ (Unitrec-reflected m₁≳m₂ ok) (lemma-𝟘ᵐ?-𝟘ᵐ? A)
            (lemma (ᵐ·≳ᵐᵐ· m₁≳m₂) _ t) (lemma m₁≳m₂ _ u)
        (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) (ΠΣᵤ A B) →
          RS₁.ΠΣᵤ (lemma (ᵐ·≳ᵐᵐ·-BinderMode m₁≳m₂) _ A)
            (lemma m₁≳m₂ _ B)
        (lam _ _) (lamᵤ t) →
          RS₁.lamᵤ (lemma m₁≳m₂ _ t)
        (_ ∘⟨ _ ⟩ _) (∘ᵤ t u) →
          RS₁.∘ᵤ (lemma m₁≳m₂ _ t) (lemma (ᵐ·≳ᵐᵐ· m₁≳m₂) _ u)
        (prod _ _ _ _) (prodᵤ t u) →
          RS₁.prodᵤ (lemma (ᵐ·≳ᵐᵐ·-Σ m₁≳m₂) _ t) (lemma m₁≳m₂ _ u)
        (prodrec _ _ _ _ _ _) (prodrecᵤ ok A t u) →
          RS₁.prodrecᵤ (Prodrec-reflected m₁≳m₂ ok) (lemma-𝟘ᵐ?-𝟘ᵐ? A)
            (lemma (ᵐ·≳ᵐᵐ· m₁≳m₂) _ t) (lemma m₁≳m₂ _ u)
        (fst _ _) (fstᵤ t) →
          RS₁.fstᵤ (lemma m₁≳m₂ _ t)
        (snd _ _) (sndᵤ t) →
          RS₁.sndᵤ (lemma m₁≳m₂ _ t)
        ℕ ℕᵤ →
          RS₁.ℕᵤ
        zero zeroᵤ →
          RS₁.zeroᵤ
        (suc _) (sucᵤ t) →
          RS₁.sucᵤ (lemma m₁≳m₂ _ t)
        (natrec _ _ _ _ _ _ _) (natrecᵤ A t u v) →
          RS₁.natrecᵤ (lemma-𝟘ᵐ?-𝟘ᵐ? A) (lemma m₁≳m₂ _ t)
            (lemma m₁≳m₂ _ u) (lemma m₁≳m₂ _ v)
        U Uᵤ →
          RS₁.Uᵤ
        (Id _ _ _) (Idᵤ not-erased A t u) →
          RS₁.Idᵤ (not-erased ∘→ Id-erased-preserved .proj₁)
            (lemma-𝟘ᵐ?-𝟘ᵐ? A) (lemma m₁≳m₂ _ t) (lemma m₁≳m₂ _ u)
        (Id _ _ _) (Id₀ᵤ erased A t u) →
          RS₁.Id₀ᵤ (Id-erased-preserved .proj₂ erased) (lemma-𝟘ᵐ?-𝟘ᵐ? A)
            (lemma-𝟘ᵐ?-𝟘ᵐ? t) (lemma-𝟘ᵐ?-𝟘ᵐ? u)
        rfl rflᵤ →
          RS₁.rflᵤ
        (J _ _ _ _ _ _ _ _) (Jᵤ _ A t B u v w) →
          RS₁.Jᵤ-generalised (lemma-𝟘ᵐ?-𝟘ᵐ? A) (lemma m₁≳m₂ _ t)
            (lemma m₁≳m₂ _ B) (lemma m₁≳m₂ _ u) (lemma m₁≳m₂ _ v)
            (lemma m₁≳m₂ _ w)
        (J _ _ _ _ _ _ _ _) (Jᵤ′ ≡some A t B u v w) →
          case m₁≳m₂ of λ where
            [ m₁≈m₂ ] →
              case singleton $ UR₁.erased-matches-for-J m₁ of λ where
                (none , ≡none) →
                  case
                    PE.trans (PE.sym ≡some)
                      (≤ᵉᵐ→≡none→≡none
                         (erased-matches-for-J-reflected m₁≈m₂) ≡none)
                  of λ ()
                (not-none _ , ≡not-none) →
                  RS₁.Jᵤ′-generalised ≡not-none (lemma-𝟘ᵐ?-𝟘ᵐ? A)
                    (lemma-ᵐ·-+ m₁≳m₂ t) (lemma m₁≳m₂ _ B)
                    (lemma m₁≳m₂ _ u) (lemma-ᵐ·-+ m₁≳m₂ v)
                    (lemma-ᵐ·-+ m₁≳m₂ w)
            (𝟙ᵐ≳𝟘ᵐ _) →
              RS₁.Jᵤ-generalised (lemma-𝟘ᵐ?-𝟘ᵐ? A) (lemma m₁≳m₂ _ t)
                (lemma m₁≳m₂ _ B) (lemma m₁≳m₂ _ u) (lemma m₁≳m₂ _ v)
                (lemma m₁≳m₂ _ w)
        (J _ _ _ _ _ _ _ _) (J₀ᵤ ≡all A t B u v w) →
          case m₁≳m₂ of λ where
            [ m₁≈m₂ ] →
              RS₁.J₀ᵤ
                (≤ᵉᵐ→≡all→≡all (erased-matches-for-J-reflected m₁≈m₂)
                   ≡all)
                (lemma-𝟘ᵐ?-𝟘ᵐ? A) (lemma-𝟘ᵐ?-𝟘ᵐ? t) (lemma-𝟘ᵐ?-𝟘ᵐ? B)
                (lemma m₁≳m₂ _ u) (lemma-𝟘ᵐ?-𝟘ᵐ? v) (lemma-𝟘ᵐ?-𝟘ᵐ? w)
            (𝟙ᵐ≳𝟘ᵐ _) →
              RS₁.Jᵤ-generalised (lemma-𝟘ᵐ?-𝟘ᵐ? A) (lemma-𝟘ᵐ? m₁≳m₂ t)
                (lemma-𝟘ᵐ? m₁≳m₂ B) (lemma m₁≳m₂ _ u)
                (lemma-𝟘ᵐ? m₁≳m₂ v) (lemma-𝟘ᵐ? m₁≳m₂ w)
        (K _ _ _ _ _ _) (Kᵤ _ A t B u v) →
          RS₁.Kᵤ-generalised (lemma-𝟘ᵐ?-𝟘ᵐ? A) (lemma m₁≳m₂ _ t)
            (lemma m₁≳m₂ _ B) (lemma m₁≳m₂ _ u) (lemma m₁≳m₂ _ v)
        (K _ _ _ _ _ _) (Kᵤ′ ≡some A t B u v) →
          case m₁≳m₂ of λ where
            [ m₁≈m₂ ] →
              case singleton $ UR₁.erased-matches-for-K m₁ of λ where
                (none , ≡none) →
                  case
                    PE.trans (PE.sym ≡some)
                      (≤ᵉᵐ→≡none→≡none
                         (erased-matches-for-K-reflected m₁≈m₂) ≡none)
                  of λ ()
                (not-none _ , ≡not-none) →
                  RS₁.Kᵤ′-generalised ≡not-none (lemma-𝟘ᵐ?-𝟘ᵐ? A)
                    (lemma (ᵐ·≳ᵐᵐ· m₁≳m₂) _ t) (lemma m₁≳m₂ _ B)
                    (lemma m₁≳m₂ _ u) (lemma (ᵐ·≳ᵐᵐ· m₁≳m₂) _ v)
            (𝟙ᵐ≳𝟘ᵐ _) →
              RS₁.Kᵤ-generalised (lemma-𝟘ᵐ?-𝟘ᵐ? A) (lemma m₁≳m₂ _ t)
                (lemma m₁≳m₂ _ B) (lemma m₁≳m₂ _ u) (lemma m₁≳m₂ _ v)
        (K _ _ _ _ _ _) (K₀ᵤ ≡all A t B u v) →
          case m₁≳m₂ of λ where
            [ m₁≈m₂ ] →
              RS₁.K₀ᵤ
                (≤ᵉᵐ→≡all→≡all (erased-matches-for-K-reflected m₁≈m₂)
                   ≡all)
                (lemma-𝟘ᵐ?-𝟘ᵐ? A) (lemma-𝟘ᵐ?-𝟘ᵐ? t) (lemma-𝟘ᵐ?-𝟘ᵐ? B)
                (lemma m₁≳m₂ _ u) (lemma-𝟘ᵐ?-𝟘ᵐ? v)
            (𝟙ᵐ≳𝟘ᵐ _) →
              RS₁.Kᵤ-generalised (lemma-𝟘ᵐ?-𝟘ᵐ? A) (lemma-𝟘ᵐ? m₁≳m₂ t)
                (lemma-𝟘ᵐ? m₁≳m₂ B) (lemma m₁≳m₂ _ u)
                (lemma-𝟘ᵐ? m₁≳m₂ v)
        ([]-cong _ _ _ _ _) ([]-congᵤ A t u v) →
          RS₁.[]-congᵤ (lemma-𝟘ᵐ?-𝟘ᵐ? A) (lemma-𝟘ᵐ?-𝟘ᵐ? t)
            (lemma-𝟘ᵐ?-𝟘ᵐ? u) (lemma-𝟘ᵐ?-𝟘ᵐ? v)

  -- Preservation of _▸[_]_ for trivial source modalities.

  tr-▸⁻¹-trivial :
    M₁.Trivial → γ U₂.▸[ m ] tr-Term t → C₁.𝟘ᶜ U₁.▸[ 𝟙ᵐ ] t
  tr-▸⁻¹-trivial {γ} {m} {t} 𝟙≡𝟘 =
    γ U₂.▸[ m ] tr-Term t                       →⟨ ▸→Usage-restrictions-satisfied ⟩
    Usage-restrictions-satisfied m (tr-Term t)  →⟨ Usage-restrictions-satisfied-tr-Term (𝟙ᵐ≳ᵐ m) ⟩
    RS₁.Usage-restrictions-satisfied 𝟙ᵐ t       →⟨ RS₁.Trivial→▸⇔ 𝟙≡𝟘 .proj₂ ⟩
    C₁.𝟘ᶜ U₁.▸[ 𝟙ᵐ ] t                          □
    where
    𝟙ᵐ≳ᵐ : (m : Mo₂.Mode) → Mo₁.𝟙ᵐ ≳ᵐ m
    𝟙ᵐ≳ᵐ 𝟙ᵐ = [ 𝟙ᵐ ]
    𝟙ᵐ≳ᵐ 𝟘ᵐ = 𝟙ᵐ≳𝟘ᵐ 𝟙≡𝟘

  -- Preservation of _▸[_]_.

  tr-▸⁻¹ : tr-Conₘ γ U₂.▸[ tr-Mode m ] tr-Term t → γ U₁.▸[ m ] t
  tr-▸⁻¹ = λ ▸t → tr-▸⁻¹′ _ ▸t refl CP₂.≤ᶜ-refl
    where mutual
    tr-▸⁻¹′ :
      ∀ t → γ′ U₂.▸[ m′ ] tr-Term t →
      m′ ≡ tr-Mode m → tr-Conₘ γ C₂.≤ᶜ γ′ → γ U₁.▸[ m ] t
    tr-▸⁻¹′ {γ = γ} U Uₘ refl ≤𝟘 = sub
      Uₘ
      (begin
         γ      ≤⟨ tr-Conₘ-≤ᶜ-𝟘ᶜ-→-≤ᶜ-𝟘ᶜ ≤𝟘 ⟩
         C₁.𝟘ᶜ  ∎)
      where
      open CR₁

    tr-▸⁻¹′ Unit! Unitₘ refl ≤𝟘 =
      sub Unitₘ (tr-Conₘ-≤ᶜ-𝟘ᶜ-→-≤ᶜ-𝟘ᶜ ≤𝟘)

    tr-▸⁻¹′ starʷ starʷₘ refl ≤𝟘 =
      sub starʷₘ (tr-Conₘ-≤ᶜ-𝟘ᶜ-→-≤ᶜ-𝟘ᶜ ≤𝟘)

    tr-▸⁻¹′ Empty Emptyₘ refl ≤𝟘 =
      sub Emptyₘ (tr-Conₘ-≤ᶜ-𝟘ᶜ-→-≤ᶜ-𝟘ᶜ ≤𝟘)

    tr-▸⁻¹′ ℕ ℕₘ refl ≤𝟘 =
      sub ℕₘ (tr-Conₘ-≤ᶜ-𝟘ᶜ-→-≤ᶜ-𝟘ᶜ ≤𝟘)

    tr-▸⁻¹′ zero zeroₘ refl ≤𝟘 =
      sub zeroₘ (tr-Conₘ-≤ᶜ-𝟘ᶜ-→-≤ᶜ-𝟘ᶜ ≤𝟘)

    tr-▸⁻¹′ (suc _) (sucₘ ▸t) refl ≤γ′ =
      sucₘ (tr-▸⁻¹′ _ ▸t refl ≤γ′)

    tr-▸⁻¹′ (snd _ _) (sndₘ ▸t) refl ≤γ′ =
      sndₘ (tr-▸⁻¹′ _ ▸t refl ≤γ′)

    tr-▸⁻¹′ {m = m} {γ = γ} starˢ (starˢₘ {γ = δ} prop) refl ≤mδ =
      case lemma″ starˢ-sink-preserved prop of λ (_ , prop′ , γ≤) →
        sub (starˢₘ prop′) γ≤
      where
      open CR₂
      lemma′ : ∀ m → tr-Conₘ γ C₂.≤ᶜ Mo₂.⌜ tr-Mode m ⌝ C₂.·ᶜ δ →
               ∃ λ η → γ C₁.≤ᶜ Mo₁.⌜ m ⌝ C₁.·ᶜ η
      lemma′ 𝟘ᵐ ≤𝟘 = C₁.𝟘ᶜ ,
        (case trivial-⊎-tr-Conₘ-𝟘ᶜ-≈ᶜ of λ where
          (inj₁ trivial) → trivial
          (inj₂ tr-Conₘ-𝟘ᶜ-≈ᶜ) → tr-Conₘ-order-reflecting (begin
            tr-Conₘ γ ≤⟨ ≤𝟘 ⟩
            Mo₂.⌜ tr-Mode Mo₁.𝟘ᵐ ⌝ C₂.·ᶜ δ    ≈⟨ CP₂.·ᶜ-zeroˡ δ ⟩
            C₂.𝟘ᶜ                             ≈˘⟨ tr-Conₘ-𝟘ᶜ-≈ᶜ ⟩
            tr-Conₘ C₁.𝟘ᶜ                     ≈˘⟨ CQ.tr-≈ᶜ (CP₁.·ᶜ-zeroˡ _) ⟩
            tr-Conₘ (Mo₁.⌜ Mo₁.𝟘ᵐ ⌝ C₁.·ᶜ _)  ∎))
      lemma′ 𝟙ᵐ ≤δ = γ ,
        tr-Conₘ-order-reflecting (begin
          tr-Conₘ γ                         ≈˘⟨ CQ.tr-≈ᶜ (CP₁.·ᶜ-identityˡ γ) ⟩
          tr-Conₘ (Mo₁.⌜ Mo₁.𝟙ᵐ ⌝ C₁.·ᶜ γ)  ∎)

      lemma″ :
        ∀ {b b′} → b′ ≡ b →
        (T (not b) → C₂.𝟘ᶜ C₂.≈ᶜ δ) →
          ∃ λ η → (T (not b′) → C₁.𝟘ᶜ C₁.≈ᶜ η) × γ C₁.≤ᶜ Mo₁.⌜ m ⌝ C₁.·ᶜ η
      lemma″ {(false)} refl prop =
        _ , (λ _ → CP₁.≈ᶜ-refl) ,
        (case trivial-⊎-tr-Conₘ-𝟘ᶜ-≈ᶜ of λ where
          (inj₁ trivial) → trivial
          (inj₂ tr-Conₘ-𝟘ᶜ-≈ᶜ) → tr-Conₘ-order-reflecting (begin
            tr-Conₘ γ                         ≤⟨ ≤mδ ⟩
            Mo₂.⌜ tr-Mode m ⌝ C₂.·ᶜ δ         ≈˘⟨ CP₂.·ᶜ-congˡ (prop _) ⟩
            Mo₂.⌜ tr-Mode m ⌝ C₂.·ᶜ C₂.𝟘ᶜ     ≈⟨ CP₂.·ᶜ-zeroʳ _ ⟩
            C₂.𝟘ᶜ                             ≈˘⟨ CP₂.·ᶜ-zeroʳ _ ⟩
            tr Mo₁.⌜ m ⌝ C₂.·ᶜ C₂.𝟘ᶜ          ≈˘⟨ CP₂.·ᶜ-congˡ tr-Conₘ-𝟘ᶜ-≈ᶜ ⟩
            tr Mo₁.⌜ m ⌝ C₂.·ᶜ tr-Conₘ C₁.𝟘ᶜ  ≈˘⟨ tr-Conₘ-·ᶜ ⟩
            tr-Conₘ (Mo₁.⌜ m ⌝ C₁.·ᶜ C₁.𝟘ᶜ)   ∎))
      lemma″ {(true)} refl _ = case lemma′ m ≤mδ of λ (_ , γ≤) →
        _ , (λ ()) , γ≤

    tr-▸⁻¹′ {m = m} {γ = γ} (var x) var refl ≤𝟘,x≔⌜tr-m⌝ = sub
      var
      (case trivial-⊎-tr-Conₘ-𝟘ᶜ-≈ᶜ of λ where
         (inj₁ trivial)   → trivial
         (inj₂ tr-Conₘ-𝟘) → begin
            γ                          ≡˘⟨ CP₁.update-self _ _ ⟩
            γ     C₁., x ≔ γ C₁.⟨ x ⟩  ≤⟨ CP₁.update-monotoneʳ _ (tr-≤-⌜tr-Mode⌝ m lemma₁) ⟩
            γ     C₁., x ≔ Mo₁.⌜ m ⌝   ≤⟨ tr-Conₘ-order-reflecting (lemma₂ tr-Conₘ-𝟘) ⟩
            C₁.𝟘ᶜ C₁., x ≔ Mo₁.⌜ m ⌝   ∎)
      where
      lemma₁ = begin
        tr (γ C₁.⟨ x ⟩)                              ≡⟨ CQ.tr-⟨⟩ γ ⟩
        tr-Conₘ γ C₂.⟨ x ⟩                           ≤⟨ CP₂.lookup-monotone _ ≤𝟘,x≔⌜tr-m⌝ ⟩
        (C₂.𝟘ᶜ C₂., x ≔ Mo₂.⌜ tr-Mode m ⌝) C₂.⟨ x ⟩  ≡⟨ CP₂.update-lookup C₂.𝟘ᶜ x ⟩
        Mo₂.⌜ tr-Mode m ⌝                            ∎
        where
        open R₂

      lemma₂ = λ tr-Conₘ-𝟘 → begin
        tr-Conₘ (γ C₁., x ≔ Mo₁.⌜ m ⌝)                            ≡⟨ CQ.tr-,≔ ⟩
        tr-Conₘ γ C₂., x ≔ tr Mo₁.⌜ m ⌝                           ≤⟨ CP₂.update-monotoneˡ _ ≤𝟘,x≔⌜tr-m⌝ ⟩
        (C₂.𝟘ᶜ C₂., x ≔ Mo₂.⌜ tr-Mode m ⌝) C₂., x ≔ tr Mo₁.⌜ m ⌝  ≡⟨ CP₂.update-twice ⟩
        C₂.𝟘ᶜ C₂., x ≔ tr Mo₁.⌜ m ⌝                               ≈˘⟨ CP₂.update-congˡ tr-Conₘ-𝟘 ⟩
        tr-Conₘ C₁.𝟘ᶜ C₂., x ≔ tr Mo₁.⌜ m ⌝                       ≡˘⟨ CQ.tr-,≔ ⟩
        tr-Conₘ (C₁.𝟘ᶜ C₁., x ≔ Mo₁.⌜ m ⌝)                        ∎
        where
        open CR₂

      open CR₁

    tr-▸⁻¹′ {m = m} (lam _ _) (lamₘ ▸t) refl ≤γ′ = lamₘ
      (tr-▸⁻¹′ _ ▸t refl (≤γ′ ∙ ≤-reflexive (sym (tr-⌜⌝-· m))))

    tr-▸⁻¹′
      {m = m} {γ = γ} (_ ∘⟨ p ⟩ _)
      (_∘ₘ_ {γ = δ} {δ = η} ▸t ▸u) refl ≤γ′ =
      case tr-Conₘ-≤ᶜ-+ᶜ ≤γ′ of λ (δ′ , η′ , ≤δ , ≤pη , γ≤) →
      case tr-Conₘ-≤ᶜ-·ᶜ ≤pη of λ (η″ , ≤η , η′≤) →
      sub
        (tr-▸⁻¹′ _ ▸t refl ≤δ ∘ₘ
         tr-▸⁻¹′ _ ▸u (sym (tr-Mode-ᵐ· m BMΠ)) ≤η)
        (begin
           γ                    ≤⟨ γ≤ ⟩
           δ′ C₁.+ᶜ η′          ≤⟨ CP₁.+ᶜ-monotoneʳ η′≤ ⟩
           δ′ C₁.+ᶜ p C₁.·ᶜ η″  ∎)
      where
      open CR₁

    tr-▸⁻¹′
      {m = m} (ΠΣ⟨ b ⟩ _ , q ▷ _ ▹ _)
      (ΠΣₘ {δ = η} ▸A ▸P) refl ≤γ′ =
      case tr-Conₘ-≤ᶜ-+ᶜ ≤γ′ of λ (δ′ , η′ , ≤δ , ≤η , γ≤) →
      sub
        (ΠΣₘ (tr-▸⁻¹′ _ ▸A (sym (tr-Mode-ᵐ· m b)) ≤δ)
           (tr-▸⁻¹′ _ ▸P refl (begin
              tr-Conₘ η′ ∙ tr (Mo₁.⌜ m ⌝ M₁.· q)  ≤⟨ ≤η ∙ ≤-reflexive (sym (tr-⌜⌝-· m)) ⟩
              η C₂.∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr q  ∎)))
        γ≤
      where
      open CR₂

    tr-▸⁻¹′
      {m = m} {γ = γ} (prodʷ p _ _)
      (prodʷₘ {γ = δ} {δ = η} ▸t ▸u) refl ≤γ′ =
      case tr-Conₘ-≤ᶜ-+ᶜ ≤γ′ of λ (δ′ , η′ , ≤pδ , ≤η , γ≤) →
      case tr-Conₘ-≤ᶜ-tr-Σ-·ᶜ ≤pδ of λ (δ″ , ≤δ , δ′≤) →
      sub
        (prodʷₘ (tr-▸⁻¹′ _ ▸t (sym (tr-Mode-ᵐ· m (BMΣ 𝕨))) ≤δ)
           (tr-▸⁻¹′ _ ▸u refl ≤η))
        (begin
           γ                    ≤⟨ γ≤ ⟩
           δ′ C₁.+ᶜ η′          ≤⟨ CP₁.+ᶜ-monotoneˡ δ′≤ ⟩
           p C₁.·ᶜ δ″ C₁.+ᶜ η′  ∎)
      where
      open CR₁

    tr-▸⁻¹′
      {m = m} {γ = γ} (prodˢ p _ _)
      (prodˢₘ {γ = δ} {δ = η} ▸t ▸u) refl ≤γ′ =
      case tr-Conₘ-≤ᶜ-∧ᶜ ≤γ′ of λ (δ′ , η′ , ≤pδ , ≤η , γ≤) →
      case tr-Conₘ-≤ᶜ-tr-Σ-·ᶜ ≤pδ of λ (δ″ , ≤δ , δ′≤) →
      sub
        (prodˢₘ (tr-▸⁻¹′ _ ▸t (sym (tr-Mode-ᵐ· m (BMΣ 𝕤))) ≤δ)
           (tr-▸⁻¹′ _ ▸u refl ≤η))
        (begin
           γ                    ≤⟨ γ≤ ⟩
           δ′ C₁.∧ᶜ η′          ≤⟨ CP₁.∧ᶜ-monotoneˡ δ′≤ ⟩
           p C₁.·ᶜ δ″ C₁.∧ᶜ η′  ∎)
      where
      open CR₁

    tr-▸⁻¹′ {m = m} (fst p _) (fstₘ m′ ▸t ≡tr-m′ ok) refl ≤γ′ =
      case tr-Mode-≡-ᵐ· {m = m′} ≡tr-m′ of λ (m″ , ≡m′ , ≡m) →
      fstₘ m″
        (tr-▸⁻¹′ _ ▸t
           (let open Tools.Reasoning.PropositionalEquality in
              m′ Mo₂.ᵐ· tr-Σ p          ≡˘⟨ cong (Mo₂._ᵐ· _) ≡m′ ⟩
              tr-Mode m″ Mo₂.ᵐ· tr-Σ p  ≡˘⟨ tr-Mode-ᵐ· m″ (BMΣ 𝕤) ⟩
              tr-Mode (m″ Mo₁.ᵐ· p)     ∎)
           ≤γ′)
        ≡m
        λ {refl → tr-Σ-≤-𝟙-→ tr-emb (ok refl)}

    tr-▸⁻¹′
      {m = m} {γ = γ} (prodrec r p _ _ _ _)
      (prodrecₘ {γ = δ} {δ = η} ▸t ▸u ▸Q ok) refl γ≤rδ+η =
      case tr-Conₘ-≤ᶜ-+ᶜ γ≤rδ+η of
        λ (δ′ , η′ , δ′≤rδ , η′≤η , γ≤δ′+η′) →
      case tr-Conₘ-≤ᶜ-·ᶜ δ′≤rδ of
        λ (δ″ , δ″≤δ , δ′≤rδ″) →
      sub
        (prodrecₘ (tr-▸⁻¹′ _ ▸t (sym (tr-Mode-ᵐ· m BMΠ)) δ″≤δ)
           (tr-▸⁻¹′ _ ▸u refl let open CR₂ in begin
              tr-Conₘ η′ ∙ tr (Mo₁.⌜ m ⌝ M₁.· r M₁.· p) ∙
              tr (Mo₁.⌜ m ⌝ M₁.· r)                          ≤⟨ η′≤η ∙ ≤-reflexive (sym (tr-⌜⌝-· m)) ∙
                                                                ≤-reflexive (sym (tr-⌜⌝-· m)) ⟩
              η ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr (r M₁.· p) ∙
              Mo₂.⌜ tr-Mode m ⌝ M₂.· tr r                    ≈˘⟨ CP₂.≈ᶜ-refl ∙ M₂.·-congˡ (tr-·-tr-Σ-≡ tr-morphism) ∙ refl ⟩

              η ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr r M₂.· tr-Σ p ∙
              Mo₂.⌜ tr-Mode m ⌝ M₂.· tr r                    ∎)
           (tr-∙▸[𝟘ᵐ?]⁻¹ ▸Q .proj₂)
           (Prodrec-reflected [ ≈ᵐ-tr-Mode ] ok))
        (let open CR₁ in begin
           γ                    ≤⟨ γ≤δ′+η′ ⟩
           δ′ C₁.+ᶜ η′          ≤⟨ CP₁.+ᶜ-monotoneˡ δ′≤rδ″ ⟩
           r C₁.·ᶜ δ″ C₁.+ᶜ η′  ∎)

    tr-▸⁻¹′
      {m = m} (natrec p _ r _ _ _ _)
      (natrecₘ {δ = δ} ▸z ▸s ▸n ▸P) refl γ≤nr-prθδη =
      case tr-Conₘ-≤ᶜ-nrᶜ γ≤nr-prθδη of
        λ (_ , δ′ , _ , θ′≤θ , δ′≤δ , η′≤η , γ≤nr-prθ′δ′η′) →
      sub
        (natrecₘ (tr-▸⁻¹′ _ ▸z refl θ′≤θ)
           (tr-▸⁻¹′ _ ▸s refl (let open CR₂ in begin
              tr-Conₘ δ′ ∙ tr (Mo₁.⌜ m ⌝ M₁.· p) ∙
              tr (Mo₁.⌜ m ⌝ M₁.· r)                 ≤⟨ δ′≤δ ∙ ≤-reflexive (sym (tr-⌜⌝-· m)) ∙
                                                       ≤-reflexive (sym (tr-⌜⌝-· m)) ⟩
              δ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p ∙
              Mo₂.⌜ tr-Mode m ⌝ M₂.· tr r           ∎))
           (tr-▸⁻¹′ _ ▸n refl η′≤η)
           (tr-∙▸[𝟘ᵐ?]⁻¹ ▸P .proj₂))
        γ≤nr-prθ′δ′η′
      where
      open import
        Graded.Modality.Morphism.Backward-instances tr-morphism

    tr-▸⁻¹′
      {m = m} (natrec p _ r _ _ _ _)
      (natrec-no-nrₘ {δ = η} ▸z ▸s ▸n ▸P γ′≤δ γ′≤η γ′≤θ fix) refl γ≤γ′ =
      case tr-≤ᶜ-no-nr γ≤γ′ γ′≤δ γ′≤η γ′≤θ fix of λ {
        (_ , _ , η′ , _ ,
         δ′≤δ , η′≤η , θ′≤θ , γ≤γ″ , γ″≤δ′ , γ″≤η′ , γ″≤θ′ , fix′) →
      sub
        (natrec-no-nrₘ (tr-▸⁻¹′ _ ▸z refl δ′≤δ)
           (tr-▸⁻¹′ _ ▸s refl $ let open CR₂ in begin
              tr-Conₘ η′ ∙ tr (Mo₁.⌜ m ⌝ M₁.· p) ∙
              tr (Mo₁.⌜ m ⌝ M₁.· r)                 ≤⟨ η′≤η ∙ ≤-reflexive (sym (tr-⌜⌝-· m)) ∙
                                                       ≤-reflexive (sym (tr-⌜⌝-· m)) ⟩
              η ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p ∙
              Mo₂.⌜ tr-Mode m ⌝ M₂.· tr r           ∎)
           (tr-▸⁻¹′ _ ▸n refl θ′≤θ)
           (tr-∙▸[𝟘ᵐ?]⁻¹ ▸P .proj₂)
           γ″≤δ′
           γ″≤η′
           γ″≤θ′
           fix′)
        γ≤γ″ }
      where
      open import
        Graded.Modality.Morphism.Backward-instances tr-morphism

    tr-▸⁻¹′
      {m = m} {γ = γ} (emptyrec p _ _)
      (emptyrecₘ ▸t ▸A) refl γ≤pδ =
      case tr-Conₘ-≤ᶜ-·ᶜ γ≤pδ of λ (δ′ , δ′≤δ , γ≤pδ′) →
      sub
        (emptyrecₘ (tr-▸⁻¹′ _ ▸t (sym (tr-Mode-ᵐ· m BMΠ)) δ′≤δ)
           (tr-▸[𝟘ᵐ?]⁻¹ ▸A .proj₂))
        (begin
           γ           ≤⟨ γ≤pδ′ ⟩
           p C₁.·ᶜ δ′  ∎)
      where
      open CR₁

    tr-▸⁻¹′
      {m = m} {γ = γ} (unitrec p _ _ _ _)
      (unitrecₘ {γ = δ} {δ = η} ▸t ▸u ▸A ok) refl γ≤pδ+η =
      case tr-Conₘ-≤ᶜ-+ᶜ γ≤pδ+η of λ (δ′ , η′ , δ′≤pδ , η′≤η , γ≤δ′+η′) →
      case tr-Conₘ-≤ᶜ-·ᶜ δ′≤pδ of λ (δ″ , δ″≤δ , δ′≤pδ″) →
      sub
        (unitrecₘ (tr-▸⁻¹′ _ ▸t (sym (tr-Mode-ᵐ· m BMΠ)) δ″≤δ)
           (tr-▸⁻¹′ _ ▸u refl η′≤η) (tr-∙▸[𝟘ᵐ?]⁻¹ ▸A .proj₂)
           (Unitrec-reflected [ ≈ᵐ-tr-Mode ] ok))
        (begin
          γ                    ≤⟨ γ≤δ′+η′ ⟩
          δ′ C₁.+ᶜ η′          ≤⟨ CP₁.+ᶜ-monotoneˡ δ′≤pδ″ ⟩
          p C₁.·ᶜ δ″ C₁.+ᶜ η′  ∎)
      where
      open CR₁

    tr-▸⁻¹′ (Id _ _ _) (Idₘ ok ▸A ▸t ▸u) refl γ≤δ+η =
      case tr-Conₘ-≤ᶜ-+ᶜ γ≤δ+η of λ {
        (_ , _ , ≤δ , ≤η , γ≤δ′+η′) → sub
      (Idₘ (ok ∘→ Id-erased-preserved .proj₁) (tr-▸[𝟘ᵐ?]⁻¹ ▸A .proj₂)
         (tr-▸⁻¹′ _ ▸t refl ≤δ) (tr-▸⁻¹′ _ ▸u refl ≤η))
      γ≤δ′+η′ }

    tr-▸⁻¹′ (Id _ _ _) (Id₀ₘ ok ▸A ▸t ▸u) refl ≤𝟘 = sub
      (Id₀ₘ (Id-erased-preserved .proj₂ ok) (tr-▸[𝟘ᵐ?]⁻¹ ▸A .proj₂)
         (tr-▸[𝟘ᵐ?]⁻¹ ▸t .proj₂) (tr-▸[𝟘ᵐ?]⁻¹ ▸u .proj₂))
      (tr-Conₘ-≤ᶜ-𝟘ᶜ-→-≤ᶜ-𝟘ᶜ ≤𝟘)

    tr-▸⁻¹′ rfl rflₘ refl ≤𝟘 =
      sub rflₘ (tr-Conₘ-≤ᶜ-𝟘ᶜ-→-≤ᶜ-𝟘ᶜ ≤𝟘)

    tr-▸⁻¹′
      {m} {γ} (J p q _ _ _ _ _ _)
      (Jₘ {γ₂} {γ₃} {γ₄} {γ₅} {γ₆} _ ▸A ▸t ▸B ▸u ▸v ▸w) refl
      γ≤ω[γ₂∧γ₃∧γ₄∧γ₅∧γ₆] =
      case
        (let open CR₂ in
         tr-Conₘ-≤ᶜ-·ᶜ $ begin
           tr-Conₘ γ                                               ≤⟨ γ≤ω[γ₂∧γ₃∧γ₄∧γ₅∧γ₆] ⟩
           M₂.ω C₂.·ᶜ (γ₂ C₂.∧ᶜ γ₃ C₂.∧ᶜ γ₄ C₂.∧ᶜ γ₅ C₂.∧ᶜ γ₆)     ≈⟨ CP₂.·ᶜ-congʳ (sym tr-ω) ⟩
           tr M₁.ω C₂.·ᶜ (γ₂ C₂.∧ᶜ γ₃ C₂.∧ᶜ γ₄ C₂.∧ᶜ γ₅ C₂.∧ᶜ γ₆)  ∎)
      of λ {
        (γ′ , γ′≤γ₂∧γ₃∧γ₄∧γ₅∧γ₆ , γ≤ωγ′) → sub
      (UP₁.Jₘ-generalised
         (tr-▸[𝟘ᵐ?]⁻¹ ▸A .proj₂)
         (let open CR₂ in
          tr-▸⁻¹′ _ ▸t refl $ begin
            tr-Conₘ γ′                              ≤⟨ γ′≤γ₂∧γ₃∧γ₄∧γ₅∧γ₆ ⟩
            γ₂ C₂.∧ᶜ γ₃ C₂.∧ᶜ γ₄ C₂.∧ᶜ γ₅ C₂.∧ᶜ γ₆  ≤⟨ CP₂.∧ᶜ-decreasingˡ _ _ ⟩
            γ₂                                      ∎)
         (let open CR₂ in
          tr-▸⁻¹′ _ ▸B refl $ begin
            tr-Conₘ γ′ ∙ tr (Mo₁.⌜ m ⌝ M₁.· p) ∙ tr (Mo₁.⌜ m ⌝ M₁.· q)  ≤⟨ γ′≤γ₂∧γ₃∧γ₄∧γ₅∧γ₆ ∙ ≤-reflexive (sym (tr-⌜⌝-· m)) ∙
                                                                           ≤-reflexive (sym (tr-⌜⌝-· m)) ⟩
            γ₂ C₂.∧ᶜ γ₃ C₂.∧ᶜ γ₄ C₂.∧ᶜ γ₅ C₂.∧ᶜ γ₆ ∙
            Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr q   ≤⟨ (CP₂.≤ᶜ-trans (CP₂.∧ᶜ-decreasingʳ _ _) $
                                                                            CP₂.∧ᶜ-decreasingˡ _ _) ∙
                                                                           ≤-refl ∙ ≤-refl ⟩
            γ₃ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p ∙
            Mo₂.⌜ tr-Mode m ⌝ M₂.· tr q                                 ∎)
         (let open CR₂ in
          tr-▸⁻¹′ _ ▸u refl $ begin
            tr-Conₘ γ′                              ≤⟨ γ′≤γ₂∧γ₃∧γ₄∧γ₅∧γ₆ ⟩
            γ₂ C₂.∧ᶜ γ₃ C₂.∧ᶜ γ₄ C₂.∧ᶜ γ₅ C₂.∧ᶜ γ₆  ≤⟨ CP₂.≤ᶜ-trans (CP₂.∧ᶜ-decreasingʳ _ _) $
                                                       CP₂.≤ᶜ-trans (CP₂.∧ᶜ-decreasingʳ _ _) $
                                                       CP₂.∧ᶜ-decreasingˡ _ _ ⟩
            γ₄                                      ∎)
         (let open CR₂ in
          tr-▸⁻¹′ _ ▸v refl $ begin
            tr-Conₘ γ′                              ≤⟨ γ′≤γ₂∧γ₃∧γ₄∧γ₅∧γ₆ ⟩
            γ₂ C₂.∧ᶜ γ₃ C₂.∧ᶜ γ₄ C₂.∧ᶜ γ₅ C₂.∧ᶜ γ₆  ≤⟨ CP₂.≤ᶜ-trans (CP₂.∧ᶜ-decreasingʳ _ _) $
                                                       CP₂.≤ᶜ-trans (CP₂.∧ᶜ-decreasingʳ _ _) $
                                                       CP₂.≤ᶜ-trans (CP₂.∧ᶜ-decreasingʳ _ _) $
                                                       CP₂.∧ᶜ-decreasingˡ _ _ ⟩
            γ₅                                      ∎)
         (let open CR₂ in
          tr-▸⁻¹′ _ ▸w refl $ begin
            tr-Conₘ γ′                              ≤⟨ γ′≤γ₂∧γ₃∧γ₄∧γ₅∧γ₆ ⟩
            γ₂ C₂.∧ᶜ γ₃ C₂.∧ᶜ γ₄ C₂.∧ᶜ γ₅ C₂.∧ᶜ γ₆  ≤⟨ CP₂.≤ᶜ-trans (CP₂.∧ᶜ-decreasingʳ _ _) $
                                                       CP₂.≤ᶜ-trans (CP₂.∧ᶜ-decreasingʳ _ _) $
                                                       CP₂.≤ᶜ-trans (CP₂.∧ᶜ-decreasingʳ _ _) $
                                                       CP₂.∧ᶜ-decreasingʳ _ _ ⟩
            γ₆                                      ∎))
      (let open CR₁ in begin
         γ                                                    ≤⟨ γ≤ωγ′ ⟩
         M₁.ω C₁.·ᶜ γ′                                        ≤⟨ flip CP₁.·ᶜ-monotone MP₁.≤-refl $
                                                                 CP₁.≤ᶜ-reflexive $ CP₁.≈ᶜ-sym $
                                                                 CP₁.≈ᶜ-trans
                                                                   (CP₁.∧ᶜ-congˡ $
                                                                    CP₁.≈ᶜ-trans
                                                                      (CP₁.∧ᶜ-congˡ $
                                                                       CP₁.≈ᶜ-trans
                                                                         (CP₁.∧ᶜ-congˡ $
                                                                          CP₁.∧ᶜ-idem _) $
                                                                       CP₁.∧ᶜ-idem _) $
                                                                    CP₁.∧ᶜ-idem _) $
                                                                 CP₁.∧ᶜ-idem _ ⟩
         M₁.ω C₁.·ᶜ (γ′ C₁.∧ᶜ γ′ C₁.∧ᶜ γ′ C₁.∧ᶜ γ′ C₁.∧ᶜ γ′)  ∎) }

    tr-▸⁻¹′
      {m} {γ} (J p q _ _ _ _ _ _)
      (Jₘ′ {γ₂} {γ₃} {γ₄} {γ₅} {γ₆} ≡some ▸A ▸t ▸B ▸u ▸v ▸w) refl
      γ≤ω[γ₂∧γ₃∧γ₄∧γ₅∧γ₆] =
      case
        (let open CR₂ in
         tr-Conₘ-≤ᶜ-·ᶜ $ begin
           tr-Conₘ γ                                               ≤⟨ γ≤ω[γ₂∧γ₃∧γ₄∧γ₅∧γ₆] ⟩
           M₂.ω C₂.·ᶜ (γ₂ C₂.∧ᶜ γ₃ C₂.∧ᶜ γ₄ C₂.∧ᶜ γ₅ C₂.∧ᶜ γ₆)     ≈⟨ CP₂.·ᶜ-congʳ (sym tr-ω) ⟩
           tr M₁.ω C₂.·ᶜ (γ₂ C₂.∧ᶜ γ₃ C₂.∧ᶜ γ₄ C₂.∧ᶜ γ₅ C₂.∧ᶜ γ₆)  ∎)
      of λ {
        (γ′ , γ′≤γ₂∧γ₃∧γ₄∧γ₅∧γ₆ , γ≤ωγ′) → sub
      (UP₁.Jₘ′-generalised
         (≤ᵉᵐ→≡some→≡not-none
            (erased-matches-for-J-reflected ≈ᵐ-tr-Mode) ≡some
            .proj₂)
         (tr-▸[𝟘ᵐ?]⁻¹ ▸A .proj₂)
         (let open CR₂ in
          tr-▸⁻¹′ _ ▸t (sym $ tr-Mode-ᵐ·-+ m) $ begin
            tr-Conₘ γ′                              ≤⟨ γ′≤γ₂∧γ₃∧γ₄∧γ₅∧γ₆ ⟩
            γ₂ C₂.∧ᶜ γ₃ C₂.∧ᶜ γ₄ C₂.∧ᶜ γ₅ C₂.∧ᶜ γ₆  ≤⟨ CP₂.∧ᶜ-decreasingˡ _ _ ⟩
            γ₂                                      ∎)
         (let open CR₂ in
          tr-▸⁻¹′ _ ▸B refl $ begin
            tr-Conₘ γ′ ∙ tr (Mo₁.⌜ m ⌝ M₁.· p) ∙ tr (Mo₁.⌜ m ⌝ M₁.· q)  ≤⟨ γ′≤γ₂∧γ₃∧γ₄∧γ₅∧γ₆ ∙ ≤-reflexive (sym (tr-⌜⌝-· m)) ∙
                                                                           ≤-reflexive (sym (tr-⌜⌝-· m)) ⟩
            γ₂ C₂.∧ᶜ γ₃ C₂.∧ᶜ γ₄ C₂.∧ᶜ γ₅ C₂.∧ᶜ γ₆ ∙
            Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr q   ≤⟨ (CP₂.≤ᶜ-trans (CP₂.∧ᶜ-decreasingʳ _ _) $
                                                                            CP₂.∧ᶜ-decreasingˡ _ _) ∙
                                                                           ≤-refl ∙ ≤-refl ⟩
            γ₃ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p ∙
            Mo₂.⌜ tr-Mode m ⌝ M₂.· tr q                                 ∎)
         (let open CR₂ in
          tr-▸⁻¹′ _ ▸u refl $ begin
            tr-Conₘ γ′                              ≤⟨ γ′≤γ₂∧γ₃∧γ₄∧γ₅∧γ₆ ⟩
            γ₂ C₂.∧ᶜ γ₃ C₂.∧ᶜ γ₄ C₂.∧ᶜ γ₅ C₂.∧ᶜ γ₆  ≤⟨ CP₂.≤ᶜ-trans (CP₂.∧ᶜ-decreasingʳ _ _) $
                                                       CP₂.≤ᶜ-trans (CP₂.∧ᶜ-decreasingʳ _ _) $
                                                       CP₂.∧ᶜ-decreasingˡ _ _ ⟩
            γ₄                                      ∎)
         (let open CR₂ in
          tr-▸⁻¹′ _ ▸v (sym $ tr-Mode-ᵐ·-+ m) $ begin
            tr-Conₘ γ′                              ≤⟨ γ′≤γ₂∧γ₃∧γ₄∧γ₅∧γ₆ ⟩
            γ₂ C₂.∧ᶜ γ₃ C₂.∧ᶜ γ₄ C₂.∧ᶜ γ₅ C₂.∧ᶜ γ₆  ≤⟨ CP₂.≤ᶜ-trans (CP₂.∧ᶜ-decreasingʳ _ _) $
                                                       CP₂.≤ᶜ-trans (CP₂.∧ᶜ-decreasingʳ _ _) $
                                                       CP₂.≤ᶜ-trans (CP₂.∧ᶜ-decreasingʳ _ _) $
                                                       CP₂.∧ᶜ-decreasingˡ _ _ ⟩
            γ₅                                      ∎)
         (let open CR₂ in
          tr-▸⁻¹′ _ ▸w (sym $ tr-Mode-ᵐ·-+ m) $ begin
            tr-Conₘ γ′                              ≤⟨ γ′≤γ₂∧γ₃∧γ₄∧γ₅∧γ₆ ⟩
            γ₂ C₂.∧ᶜ γ₃ C₂.∧ᶜ γ₄ C₂.∧ᶜ γ₅ C₂.∧ᶜ γ₆  ≤⟨ CP₂.≤ᶜ-trans (CP₂.∧ᶜ-decreasingʳ _ _) $
                                                       CP₂.≤ᶜ-trans (CP₂.∧ᶜ-decreasingʳ _ _) $
                                                       CP₂.≤ᶜ-trans (CP₂.∧ᶜ-decreasingʳ _ _) $
                                                       CP₂.∧ᶜ-decreasingʳ _ _ ⟩
            γ₆                                      ∎))
      (let open CR₁ in begin
         γ                                                    ≤⟨ γ≤ωγ′ ⟩
         M₁.ω C₁.·ᶜ γ′                                        ≤⟨ flip CP₁.·ᶜ-monotone MP₁.≤-refl $
                                                                 CP₁.≤ᶜ-reflexive $ CP₁.≈ᶜ-sym $
                                                                 CP₁.≈ᶜ-trans
                                                                   (CP₁.∧ᶜ-congˡ $
                                                                    CP₁.≈ᶜ-trans
                                                                      (CP₁.∧ᶜ-congˡ $
                                                                       CP₁.≈ᶜ-trans
                                                                         (CP₁.∧ᶜ-congˡ $
                                                                          CP₁.∧ᶜ-idem _) $
                                                                       CP₁.∧ᶜ-idem _) $
                                                                    CP₁.∧ᶜ-idem _) $
                                                                 CP₁.∧ᶜ-idem _ ⟩
         M₁.ω C₁.·ᶜ (γ′ C₁.∧ᶜ γ′ C₁.∧ᶜ γ′ C₁.∧ᶜ γ′ C₁.∧ᶜ γ′)  ∎) }

    tr-▸⁻¹′
      (J _ _ _ _ _ _ _ _) (J₀ₘ ≡all ▸A ▸t ▸B ▸u ▸v ▸w) refl ≤γ′ = J₀ₘ
      (≤ᵉᵐ→≡all→≡all (erased-matches-for-J-reflected ≈ᵐ-tr-Mode) ≡all)
      (tr-▸[𝟘ᵐ?]⁻¹ ▸A .proj₂) (tr-▸[𝟘ᵐ?]⁻¹ ▸t .proj₂)
      (tr-∙∙▸[𝟘ᵐ?]⁻¹ ▸B .proj₂) (tr-▸⁻¹′ _ ▸u refl ≤γ′)
      (tr-▸[𝟘ᵐ?]⁻¹ ▸v .proj₂) (tr-▸[𝟘ᵐ?]⁻¹ ▸w .proj₂)

    tr-▸⁻¹′
      {m} {γ} (K p _ _ _ _ _) (Kₘ {γ₂} {γ₃} {γ₄} {γ₅} _ ▸A ▸t ▸B ▸u ▸v)
      refl γ≤ω[γ₂∧γ₃∧γ₄∧γ₅] =
      case
        (let open CR₂ in
         tr-Conₘ-≤ᶜ-·ᶜ $ begin
           tr-Conₘ γ                                      ≤⟨ γ≤ω[γ₂∧γ₃∧γ₄∧γ₅] ⟩
           M₂.ω C₂.·ᶜ (γ₂ C₂.∧ᶜ γ₃ C₂.∧ᶜ γ₄ C₂.∧ᶜ γ₅)     ≈⟨ CP₂.·ᶜ-congʳ (sym tr-ω) ⟩
           tr M₁.ω C₂.·ᶜ (γ₂ C₂.∧ᶜ γ₃ C₂.∧ᶜ γ₄ C₂.∧ᶜ γ₅)  ∎)
      of λ {
        (γ′ , γ′≤γ₂∧γ₃∧γ₄∧γ₅ , γ≤ωγ′) → sub
      (UP₁.Kₘ-generalised
         (tr-▸[𝟘ᵐ?]⁻¹ ▸A .proj₂)
         (let open CR₂ in
          tr-▸⁻¹′ _ ▸t refl $ begin
            tr-Conₘ γ′                     ≤⟨ γ′≤γ₂∧γ₃∧γ₄∧γ₅ ⟩
            γ₂ C₂.∧ᶜ γ₃ C₂.∧ᶜ γ₄ C₂.∧ᶜ γ₅  ≤⟨ CP₂.∧ᶜ-decreasingˡ _ _ ⟩
            γ₂                             ∎)
         (let open CR₂ in
          tr-▸⁻¹′ _ ▸B refl $ begin
            tr-Conₘ γ′ ∙ tr (Mo₁.⌜ m ⌝ M₁.· p)                           ≤⟨ γ′≤γ₂∧γ₃∧γ₄∧γ₅ ∙ ≤-reflexive (sym (tr-⌜⌝-· m)) ⟩
            γ₂ C₂.∧ᶜ γ₃ C₂.∧ᶜ γ₄ C₂.∧ᶜ γ₅ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p  ≤⟨ (CP₂.≤ᶜ-trans (CP₂.∧ᶜ-decreasingʳ _ _) $
                                                                             CP₂.∧ᶜ-decreasingˡ _ _) ∙
                                                                            ≤-refl ⟩
            γ₃ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p                             ∎)
         (let open CR₂ in
          tr-▸⁻¹′ _ ▸u refl $ begin
            tr-Conₘ γ′                     ≤⟨ γ′≤γ₂∧γ₃∧γ₄∧γ₅ ⟩
            γ₂ C₂.∧ᶜ γ₃ C₂.∧ᶜ γ₄ C₂.∧ᶜ γ₅  ≤⟨ CP₂.≤ᶜ-trans (CP₂.∧ᶜ-decreasingʳ _ _) $
                                              CP₂.≤ᶜ-trans (CP₂.∧ᶜ-decreasingʳ _ _) $
                                              CP₂.∧ᶜ-decreasingˡ _ _ ⟩
            γ₄                             ∎)
         (let open CR₂ in
          tr-▸⁻¹′ _ ▸v refl $ begin
            tr-Conₘ γ′                     ≤⟨ γ′≤γ₂∧γ₃∧γ₄∧γ₅ ⟩
            γ₂ C₂.∧ᶜ γ₃ C₂.∧ᶜ γ₄ C₂.∧ᶜ γ₅  ≤⟨ CP₂.≤ᶜ-trans (CP₂.∧ᶜ-decreasingʳ _ _) $
                                              CP₂.≤ᶜ-trans (CP₂.∧ᶜ-decreasingʳ _ _) $
                                              CP₂.∧ᶜ-decreasingʳ _ _ ⟩
            γ₅                             ∎))
      (let open CR₁ in begin
         γ                                           ≤⟨ γ≤ωγ′ ⟩
         M₁.ω C₁.·ᶜ γ′                               ≤⟨ flip CP₁.·ᶜ-monotone MP₁.≤-refl $
                                                        CP₁.≤ᶜ-reflexive $ CP₁.≈ᶜ-sym $
                                                        CP₁.≈ᶜ-trans
                                                          (CP₁.∧ᶜ-congˡ $
                                                           CP₁.≈ᶜ-trans
                                                             (CP₁.∧ᶜ-congˡ $
                                                              CP₁.∧ᶜ-idem _) $
                                                           CP₁.∧ᶜ-idem _) $
                                                        CP₁.∧ᶜ-idem _ ⟩
         M₁.ω C₁.·ᶜ (γ′ C₁.∧ᶜ γ′ C₁.∧ᶜ γ′ C₁.∧ᶜ γ′)  ∎) }

    tr-▸⁻¹′
      {m} {γ} (K p _ _ _ _ _)
      (Kₘ′ {γ₂} {γ₃} {γ₄} {γ₅} ≡some ▸A ▸t ▸B ▸u ▸v) refl
      γ≤ω[γ₂∧γ₃∧γ₄∧γ₅] =
      case
        (let open CR₂ in
         tr-Conₘ-≤ᶜ-·ᶜ $ begin
           tr-Conₘ γ                                      ≤⟨ γ≤ω[γ₂∧γ₃∧γ₄∧γ₅] ⟩
           M₂.ω C₂.·ᶜ (γ₂ C₂.∧ᶜ γ₃ C₂.∧ᶜ γ₄ C₂.∧ᶜ γ₅)     ≈⟨ CP₂.·ᶜ-congʳ (sym tr-ω) ⟩
           tr M₁.ω C₂.·ᶜ (γ₂ C₂.∧ᶜ γ₃ C₂.∧ᶜ γ₄ C₂.∧ᶜ γ₅)  ∎)
      of λ {
        (γ′ , γ′≤γ₂∧γ₃∧γ₄∧γ₅ , γ≤ωγ′) → sub
      (UP₁.Kₘ′-generalised
         (≤ᵉᵐ→≡some→≡not-none
            (erased-matches-for-K-reflected ≈ᵐ-tr-Mode) ≡some
            .proj₂)
         (tr-▸[𝟘ᵐ?]⁻¹ ▸A .proj₂)
         (let open CR₂ in
          tr-▸⁻¹′ _ ▸t (sym $ tr-Mode-ᵐ· m _) $ begin
            tr-Conₘ γ′                     ≤⟨ γ′≤γ₂∧γ₃∧γ₄∧γ₅ ⟩
            γ₂ C₂.∧ᶜ γ₃ C₂.∧ᶜ γ₄ C₂.∧ᶜ γ₅  ≤⟨ CP₂.∧ᶜ-decreasingˡ _ _ ⟩
            γ₂                             ∎)
         (let open CR₂ in
          tr-▸⁻¹′ _ ▸B refl $ begin
            tr-Conₘ γ′ ∙ tr (Mo₁.⌜ m ⌝ M₁.· p)                           ≤⟨ γ′≤γ₂∧γ₃∧γ₄∧γ₅ ∙ ≤-reflexive (sym (tr-⌜⌝-· m)) ⟩
            γ₂ C₂.∧ᶜ γ₃ C₂.∧ᶜ γ₄ C₂.∧ᶜ γ₅ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p  ≤⟨ (CP₂.≤ᶜ-trans (CP₂.∧ᶜ-decreasingʳ _ _) $
                                                                             CP₂.∧ᶜ-decreasingˡ _ _) ∙
                                                                            ≤-refl ⟩
            γ₃ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p                             ∎)
         (let open CR₂ in
          tr-▸⁻¹′ _ ▸u refl $ begin
            tr-Conₘ γ′                     ≤⟨ γ′≤γ₂∧γ₃∧γ₄∧γ₅ ⟩
            γ₂ C₂.∧ᶜ γ₃ C₂.∧ᶜ γ₄ C₂.∧ᶜ γ₅  ≤⟨ CP₂.≤ᶜ-trans (CP₂.∧ᶜ-decreasingʳ _ _) $
                                              CP₂.≤ᶜ-trans (CP₂.∧ᶜ-decreasingʳ _ _) $
                                              CP₂.∧ᶜ-decreasingˡ _ _ ⟩
            γ₄                             ∎)
         (let open CR₂ in
          tr-▸⁻¹′ _ ▸v (sym $ tr-Mode-ᵐ· m _) $ begin
            tr-Conₘ γ′                     ≤⟨ γ′≤γ₂∧γ₃∧γ₄∧γ₅ ⟩
            γ₂ C₂.∧ᶜ γ₃ C₂.∧ᶜ γ₄ C₂.∧ᶜ γ₅  ≤⟨ CP₂.≤ᶜ-trans (CP₂.∧ᶜ-decreasingʳ _ _) $
                                              CP₂.≤ᶜ-trans (CP₂.∧ᶜ-decreasingʳ _ _) $
                                              CP₂.∧ᶜ-decreasingʳ _ _ ⟩
            γ₅                             ∎))
      (let open CR₁ in begin
         γ                                           ≤⟨ γ≤ωγ′ ⟩
         M₁.ω C₁.·ᶜ γ′                               ≤⟨ flip CP₁.·ᶜ-monotone MP₁.≤-refl $
                                                        CP₁.≤ᶜ-reflexive $ CP₁.≈ᶜ-sym $
                                                        CP₁.≈ᶜ-trans
                                                          (CP₁.∧ᶜ-congˡ $
                                                           CP₁.≈ᶜ-trans
                                                             (CP₁.∧ᶜ-congˡ $
                                                              CP₁.∧ᶜ-idem _) $
                                                           CP₁.∧ᶜ-idem _) $
                                                        CP₁.∧ᶜ-idem _ ⟩
         M₁.ω C₁.·ᶜ (γ′ C₁.∧ᶜ γ′ C₁.∧ᶜ γ′ C₁.∧ᶜ γ′)  ∎) }

    tr-▸⁻¹′ (K _ _ _ _ _ _) (K₀ₘ ≡all ▸A ▸t ▸B ▸u ▸v) refl ≤γ′ = K₀ₘ
      (≤ᵉᵐ→≡all→≡all (erased-matches-for-K-reflected ≈ᵐ-tr-Mode) ≡all)
      (tr-▸[𝟘ᵐ?]⁻¹ ▸A .proj₂) (tr-▸[𝟘ᵐ?]⁻¹ ▸t .proj₂)
      (tr-∙▸[𝟘ᵐ?]⁻¹ ▸B .proj₂) (tr-▸⁻¹′ _ ▸u refl ≤γ′)
      (tr-▸[𝟘ᵐ?]⁻¹ ▸v .proj₂)

    tr-▸⁻¹′ ([]-cong _ _ _ _ _) ([]-congₘ ▸A ▸t ▸u ▸v) refl ≤𝟘 = sub
      ([]-congₘ (tr-▸[𝟘ᵐ?]⁻¹ ▸A .proj₂) (tr-▸[𝟘ᵐ?]⁻¹ ▸t .proj₂)
         (tr-▸[𝟘ᵐ?]⁻¹ ▸u .proj₂) (tr-▸[𝟘ᵐ?]⁻¹ ▸v .proj₂))
      (tr-Conₘ-≤ᶜ-𝟘ᶜ-→-≤ᶜ-𝟘ᶜ ≤𝟘)

    tr-▸⁻¹′ {γ′ = γ′} {γ = γ} t (sub {γ = δ} ▸t γ′≤δ) refl γ≤γ′ =
      tr-▸⁻¹′ t ▸t refl (begin
        tr-Conₘ γ  ≤⟨ γ≤γ′ ⟩
        γ′         ≤⟨ γ′≤δ ⟩
        δ          ∎)
      where
      open CR₂

    tr-▸[𝟘ᵐ?]⁻¹ : γ U₂.▸[ m ] tr-Term t → ∃ λ δ → δ U₁.▸[ Mo₁.𝟘ᵐ? ] t
    tr-▸[𝟘ᵐ?]⁻¹ {m = 𝟙ᵐ} {t} ▸t =
      case tr-Conₘ-≤ᶜ of λ
        (δ , ≤γ) →
      Mo₁.𝟘ᵐ?-elim
        (λ m → ∃ λ δ → δ U₁.▸[ m ] t)
        (C₁.𝟘ᶜ , UP₁.▸-𝟘 (tr-▸⁻¹′ {γ = δ} _ ▸t refl ≤γ))
        (λ _ → δ , tr-▸⁻¹′ _ ▸t refl ≤γ)
    tr-▸[𝟘ᵐ?]⁻¹ {m = 𝟘ᵐ[ ok ]} {t} ▸t =
      Mo₁.𝟘ᵐ?-elim
        (λ m → ∃ λ δ → δ U₁.▸[ m ] t)
        (case tr-Conₘ-≤ᶜ of λ
           (δ , ≤γ) →
         δ , tr-▸⁻¹′ _ ▸t Mo₂.𝟘ᵐ-cong ≤γ)
        (λ not-ok → C₁.𝟘ᶜ , tr-▸⁻¹-trivial (trivial not-ok ok) ▸t)

    tr-∙▸[𝟘ᵐ?]⁻¹ :
      γ ∙ Mo₂.⌜ m ⌝ M₂.· tr p U₂.▸[ m ] tr-Term t →
      ∃ λ δ → δ ∙ Mo₁.⌜ Mo₁.𝟘ᵐ? ⌝ M₁.· p U₁.▸[ Mo₁.𝟘ᵐ? ] t
    tr-∙▸[𝟘ᵐ?]⁻¹ {γ} {m = 𝟙ᵐ} {p} {t} ▸t =
      Mo₁.𝟘ᵐ?-elim
        (λ m → ∃ λ δ → δ ∙ Mo₁.⌜ m ⌝ M₁.· p U₁.▸[ m ] t)
        (case tr-Conₘ-≤ᶜ of λ
           (δ , ≤γ) →
           C₁.𝟘ᶜ
         , sub (UP₁.▸-𝟘 (tr-▸⁻¹′ {γ = δ} _ ▸t refl ≤γ))
             (let open CR₁ in begin
                C₁.𝟘ᶜ ∙ M₁.𝟘 M₁.· p  ≈⟨ CP₁.≈ᶜ-refl ∙ M₁.·-zeroˡ _ ⟩
                C₁.𝟘ᶜ                ∎))
        (λ _ →
           case tr-Conₘ-≤ᶜ of λ
             (δ , ≤γ) →
             δ
           , tr-▸⁻¹′ _ ▸t refl
               (let open CR₂ in begin
                  tr-Conₘ δ ∙ tr (M₁.𝟙 M₁.· p)   ≈⟨ CP₂.≈ᶜ-refl ∙ tr-· ⟩
                  tr-Conₘ δ ∙ tr M₁.𝟙 M₂.· tr p  ≤⟨ ≤γ ∙ ·-monotoneˡ tr-𝟙 ⟩
                  γ ∙ M₂.𝟙 M₂.· tr p             ∎))
    tr-∙▸[𝟘ᵐ?]⁻¹ {γ} {m = 𝟘ᵐ[ ok ]} {p} {t} ▸t =
      Mo₁.𝟘ᵐ?-elim
        (λ m → ∃ λ δ → δ ∙ Mo₁.⌜ m ⌝ M₁.· p U₁.▸[ m ] t)
        (case tr-Conₘ-≤ᶜ of λ
           (δ , ≤γ) →
           δ
         , tr-▸⁻¹′ _ ▸t Mo₂.𝟘ᵐ-cong (begin
             tr-Conₘ δ ∙ tr (M₁.𝟘 M₁.· p)  ≈⟨ CP₂.≈ᶜ-refl ∙ cong tr (M₁.·-zeroˡ _) ⟩
             tr-Conₘ δ ∙ tr M₁.𝟘           ≤⟨ ≤γ ∙ tr-𝟘-≤ ⟩
             γ ∙ M₂.𝟘                      ≈˘⟨ CP₂.≈ᶜ-refl ∙ M₂.·-zeroˡ _ ⟩
             γ ∙ M₂.𝟘 M₂.· tr p            ∎))
        (λ not-ok →
           let triv = trivial not-ok ok in
           C₁.𝟘ᶜ , sub (tr-▸⁻¹-trivial triv ▸t) (CP₁.≈ᶜ-trivial triv))
      where
      open CR₂

    tr-∙∙▸[𝟘ᵐ?]⁻¹ :
      γ ∙ Mo₂.⌜ m ⌝ M₂.· tr p ∙ Mo₂.⌜ m ⌝ M₂.· tr q
        U₂.▸[ m ] tr-Term t →
      ∃ λ δ →
      δ ∙ Mo₁.⌜ Mo₁.𝟘ᵐ? ⌝ M₁.· p ∙ Mo₁.⌜ Mo₁.𝟘ᵐ? ⌝ M₁.· q
        U₁.▸[ Mo₁.𝟘ᵐ? ] t
    tr-∙∙▸[𝟘ᵐ?]⁻¹ {γ} {m = 𝟙ᵐ} {p} {q} {t} ▸t =
      Mo₁.𝟘ᵐ?-elim
        (λ m →
           ∃ λ δ → δ ∙ Mo₁.⌜ m ⌝ M₁.· p ∙ Mo₁.⌜ m ⌝ M₁.· q U₁.▸[ m ] t)
        (case tr-Conₘ-≤ᶜ of λ
           (δ , ≤γ) →
           C₁.𝟘ᶜ
         , sub (UP₁.▸-𝟘 (tr-▸⁻¹′ {γ = δ} _ ▸t refl ≤γ))
             (let open CR₁ in begin
                C₁.𝟘ᶜ ∙ M₁.𝟘 M₁.· p ∙ M₁.𝟘 M₁.· q  ≈⟨ CP₁.≈ᶜ-refl ∙ M₁.·-zeroˡ _ ∙ M₁.·-zeroˡ _ ⟩
                C₁.𝟘ᶜ                              ∎))
        (λ _ →
           case tr-Conₘ-≤ᶜ of λ
             (δ , ≤γ) →
             δ
           , tr-▸⁻¹′ _ ▸t refl
               (let open CR₂ in begin
                  tr-Conₘ δ ∙ tr (M₁.𝟙 M₁.· p) ∙ tr (M₁.𝟙 M₁.· q)    ≈⟨ CP₂.≈ᶜ-refl ∙ tr-· ∙ tr-· ⟩
                  tr-Conₘ δ ∙ tr M₁.𝟙 M₂.· tr p ∙ tr M₁.𝟙 M₂.· tr q  ≤⟨ ≤γ ∙ ·-monotoneˡ tr-𝟙 ∙ ·-monotoneˡ tr-𝟙 ⟩
                  γ ∙ M₂.𝟙 M₂.· tr p ∙ M₂.𝟙 M₂.· tr q                ∎))
    tr-∙∙▸[𝟘ᵐ?]⁻¹ {γ} {m = 𝟘ᵐ[ ok ]} {p} {q} {t} ▸t =
      Mo₁.𝟘ᵐ?-elim
        (λ m →
           ∃ λ δ → δ ∙ Mo₁.⌜ m ⌝ M₁.· p ∙ Mo₁.⌜ m ⌝ M₁.· q U₁.▸[ m ] t)
        (case tr-Conₘ-≤ᶜ of λ
           (δ , ≤γ) →
           δ
         , tr-▸⁻¹′ _ ▸t Mo₂.𝟘ᵐ-cong (begin
             tr-Conₘ δ ∙ tr (M₁.𝟘 M₁.· p) ∙ tr (M₁.𝟘 M₁.· q)  ≈⟨ CP₂.≈ᶜ-refl ∙ cong tr (M₁.·-zeroˡ _) ∙ cong tr (M₁.·-zeroˡ _) ⟩
             tr-Conₘ δ ∙ tr M₁.𝟘 ∙ tr M₁.𝟘                    ≤⟨ ≤γ ∙ tr-𝟘-≤ ∙ tr-𝟘-≤ ⟩
             γ ∙ M₂.𝟘 ∙ M₂.𝟘                                  ≈˘⟨ CP₂.≈ᶜ-refl ∙ M₂.·-zeroˡ _ ∙ M₂.·-zeroˡ _ ⟩
             γ ∙ M₂.𝟘 M₂.· tr p ∙ M₂.𝟘 M₂.· tr q              ∎))
        (λ not-ok →
           let triv = trivial not-ok ok in
           C₁.𝟘ᶜ , sub (tr-▸⁻¹-trivial triv ▸t) (CP₁.≈ᶜ-trivial triv))
      where
      open CR₂
