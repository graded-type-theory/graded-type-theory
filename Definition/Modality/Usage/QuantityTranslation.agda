------------------------------------------------------------------------
-- Modality morphisms preserve some things related to usage
------------------------------------------------------------------------

open import Definition.Modality
open import Definition.Modality.Morphism as M
  using (Is-morphism; Is-order-embedding;
         Is-Σ-morphism; Is-Σ-order-embedding)
  hiding (module Is-morphism; module Is-order-embedding)
open import Definition.Modality.Usage.Restrictions

module Definition.Modality.Usage.QuantityTranslation
  {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
  (𝕄₁ : Modality M₁) (𝕄₂ : Modality M₂)
  (R₁ : Usage-restrictions M₁) (R₂ : Usage-restrictions M₂)
  (tr tr-Σ : M₁ → M₂)
  where

open import Definition.Untyped
open import Definition.Untyped.QuantityTranslation tr tr-Σ

open import Definition.Modality.Context
import Definition.Modality.Context.Properties
open import Definition.Modality.Context.QuantityTranslation 𝕄₁ 𝕄₂ tr
  as CQ using (tr-Conₘ)
import Definition.Modality.Properties
open import Definition.Modality.Usage
open import Definition.Modality.Usage.Properties 𝕄₂ R₂
open import Definition.Modality.Morphism.Usage-restrictions

open import Definition.Mode
open import Definition.Mode.QuantityTranslation 𝕄₁ 𝕄₂ tr tr-Σ
  as MQ hiding (module Is-morphism; module Is-order-embedding)

open Definition.Modality.Properties 𝕄₂

private
  module C₁  = Definition.Modality.Context 𝕄₁
  module C₂  = Definition.Modality.Context 𝕄₂
  module CP₁ = Definition.Modality.Context.Properties 𝕄₁
  module CP₂ = Definition.Modality.Context.Properties 𝕄₂
  module MP₁ = Definition.Modality.Properties 𝕄₁
  module U₁  = Definition.Modality.Usage 𝕄₁ R₁
  module U₂  = Definition.Modality.Usage 𝕄₂ R₂
  module Mo₁ = Definition.Mode 𝕄₁
  module Mo₂ = Definition.Mode 𝕄₂
  module M₁  = Modality 𝕄₁
  module M₂  = Modality 𝕄₂

open import Tools.Fin
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Sum using (inj₁; inj₂)

private
  module R₁      = Tools.Reasoning.PartialOrder MP₁.≤-poset
  module R₂      = Tools.Reasoning.PartialOrder ≤-poset
  module CR₁ {n} = Tools.Reasoning.PartialOrder (CP₁.≤ᶜ-poset {n = n})
  module CR₂ {n} = Tools.Reasoning.PartialOrder (CP₂.≤ᶜ-poset {n = n})

private variable
  x      : Fin _
  p      : M₁
  p′     : M₂
  γ γ′ δ : Conₘ _ _
  m m′   : Mode _
  t      : Term _ _

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
      tr-Conₘ-+ᶜ
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
         tr-Conₘ (γ C₁.+ᶜ p C₁.·ᶜ δ)           ≤⟨ tr-Conₘ-+ᶜ ⟩
         tr-Conₘ γ C₂.+ᶜ tr-Conₘ (p C₁.·ᶜ δ)   ≈⟨ +ᶜ-congˡ tr-Conₘ-·ᶜ ⟩
         tr-Conₘ γ C₂.+ᶜ tr p C₂.·ᶜ tr-Conₘ δ  ∎)
      where
      open CR₂
    tr-▸ (prodᵣₘ {γ = γ} {m = m} {p = p} {δ = δ} ▸t ▸u) = sub
      (prodᵣₘ (▸-cong (tr-Mode-ᵐ· m (BMΣ Σᵣ)) (tr-▸ ▸t)) (tr-▸ ▸u))
      (begin
         tr-Conₘ (p C₁.·ᶜ γ C₁.+ᶜ δ)             ≤⟨ tr-Conₘ-+ᶜ ⟩
         tr-Conₘ (p C₁.·ᶜ γ) C₂.+ᶜ tr-Conₘ δ     ≈⟨ +ᶜ-congʳ tr-Conₘ-·ᶜ ⟩
         tr p C₂.·ᶜ tr-Conₘ γ C₂.+ᶜ tr-Conₘ δ    ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneˡ tr-≤-tr-Σ) ⟩
         tr-Σ p C₂.·ᶜ tr-Conₘ γ C₂.+ᶜ tr-Conₘ δ  ∎)
      where
      open CR₂
    tr-▸ (prodₚₘ {γ = γ} {m = m} {p = p} {δ = δ} ▸t ▸u) = sub
      (prodₚₘ (▸-cong (tr-Mode-ᵐ· m (BMΣ Σₚ)) (tr-▸ ▸t)) (tr-▸ ▸u))
      (begin
         tr-Conₘ (p C₁.·ᶜ γ C₁.∧ᶜ δ)             ≤⟨ tr-Conₘ-∧ᶜ ⟩
         tr-Conₘ (p C₁.·ᶜ γ) C₂.∧ᶜ tr-Conₘ δ     ≈⟨ ∧ᶜ-congʳ tr-Conₘ-·ᶜ ⟩
         tr p C₂.·ᶜ tr-Conₘ γ C₂.∧ᶜ tr-Conₘ δ    ≤⟨ ∧ᶜ-monotoneˡ (·ᶜ-monotoneˡ tr-≤-tr-Σ) ⟩
         tr-Σ p C₂.·ᶜ tr-Conₘ γ C₂.∧ᶜ tr-Conₘ δ  ∎)
      where
      open CR₂
    tr-▸ (fstₘ {p = p} m ▸t refl ok) = fstₘ
      (tr-Mode m)
      (▸-cong (tr-Mode-ᵐ· m (BMΣ Σₚ)) (tr-▸ ▸t))
      (sym (tr-Mode-ᵐ· m (BMΣ Σₚ)))
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
         (tr-∙▸[𝟘̂ᵐ?] ▸Q)
         (Prodrec-preserved ok))
      (begin
         tr-Conₘ (r C₁.·ᶜ γ C₁.+ᶜ δ)           ≤⟨ tr-Conₘ-+ᶜ ⟩
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
         (tr-∙▸[𝟘̂ᵐ?] ▸P))
      (begin
         tr-Conₘ ((γ C₁.∧ᶜ η) C₁.⊛ᶜ δ C₁.+ᶜ p C₁.·ᶜ η ▷ r)             ≤⟨ tr-Conₘ-⊛ᶜ ⟩

         tr-Conₘ (γ C₁.∧ᶜ η) C₂.⊛ᶜ tr-Conₘ (δ C₁.+ᶜ p C₁.·ᶜ η) ▷ tr r  ≤⟨ ⊛ᶜ-monotone tr-Conₘ-∧ᶜ tr-Conₘ-+ᶜ ⟩

         (tr-Conₘ γ C₂.∧ᶜ tr-Conₘ η) C₂.⊛ᶜ
         tr-Conₘ δ C₂.+ᶜ tr-Conₘ (p C₁.·ᶜ η) ▷ tr r                    ≈⟨ ⊛ᵣᶜ-congˡ (+ᶜ-congˡ tr-Conₘ-·ᶜ) ⟩

         (tr-Conₘ γ C₂.∧ᶜ tr-Conₘ η) C₂.⊛ᶜ
         tr-Conₘ δ C₂.+ᶜ tr p C₂.·ᶜ tr-Conₘ η ▷ tr r                   ∎)
      where
      open CR₂
    tr-▸ (Emptyrecₘ {m = m} ▸t ▸A) = sub
      (Emptyrecₘ (▸-cong (tr-Mode-ᵐ· m BMΠ) (tr-▸ ▸t)) (tr-▸[𝟘̂ᵐ?] ▸A))
      (≤ᶜ-reflexive tr-Conₘ-·ᶜ)
    tr-▸ starₘ =
      sub starₘ tr-Conₘ-𝟘ᶜ-≤ᶜ
    tr-▸ (sub ▸t γ≤δ) =
      sub (tr-▸ ▸t) (tr-Conₘ-monotone γ≤δ)

    private

      -- A variant of tr-▸.

      tr-▸[𝟘̂ᵐ?] :
        γ U₁.▸[ Mo₁.𝟘ᵐ? ] t → tr-Conₘ γ U₂.▸[ Mo₂.𝟘ᵐ? ] tr-Term t
      tr-▸[𝟘̂ᵐ?] {γ = γ} {t = t} = Mo₁.𝟘ᵐ?-elim
        (λ m → γ U₁.▸[ m ] t → tr-Conₘ γ U₂.▸[ Mo₂.𝟘ᵐ? ] tr-Term t)
        (▸-cong (sym Mo₂.𝟘ᵐ?≡𝟘ᵐ) ∘→ tr-▸)
        (λ not-ok ▸t → Mo₂.𝟘ᵐ?-elim
           (λ m → tr-Conₘ γ U₂.▸[ m ] tr-Term t)
           (λ ⦃ ok = ok ⦄ →
              sub (▸-𝟘 (tr-▸ ▸t)) (tr-Conₘ-≤ᶜ-𝟘ᶜ not-ok ok))
           (λ _ → tr-▸ ▸t))

      -- Another variant of tr-▸.

      tr-∙▸[𝟘̂ᵐ?] :
        γ ∙ Mo₁.⌜ Mo₁.𝟘ᵐ? ⌝ M₁.· p U₁.▸[ Mo₁.𝟘ᵐ? ] t →
        tr-Conₘ γ ∙ Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr p U₂.▸[ Mo₂.𝟘ᵐ? ] tr-Term t
      tr-∙▸[𝟘̂ᵐ?] {γ = γ} {p = p} {t = t} = Mo₁.𝟘ᵐ?-elim
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
             tr-Conₘ γ ∙ M₂.𝟘                       ≈˘⟨ ≈ᶜ-refl ∙ tr-𝟘-≡ ok ⟩
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

  -- Preservation of _▸[_]_ for trivial source modalities.

  tr-▸⁻¹-𝟙≡𝟘 :
    M₁.𝟙 ≡ M₁.𝟘 → γ U₂.▸[ m ] tr-Term t → C₁.𝟘ᶜ U₁.▸[ 𝟙ᵐ ] t
  tr-▸⁻¹-𝟙≡𝟘 {m = m₁} 𝟙≡𝟘 = tr-▸⁻¹-𝟙≡𝟘′ _
    where mutual
    tr-▸⁻¹-𝟙≡𝟘′ : ∀ t → γ U₂.▸[ m ] tr-Term t → C₁.𝟘ᶜ U₁.▸[ m′ ] t
    tr-▸⁻¹-𝟙≡𝟘′ U Uₘ =
      Uₘ

    tr-▸⁻¹-𝟙≡𝟘′ Unit Unitₘ =
      Unitₘ

    tr-▸⁻¹-𝟙≡𝟘′ star starₘ =
      starₘ

    tr-▸⁻¹-𝟙≡𝟘′ Empty Emptyₘ =
      Emptyₘ

    tr-▸⁻¹-𝟙≡𝟘′ ℕ ℕₘ =
      ℕₘ

    tr-▸⁻¹-𝟙≡𝟘′ zero zeroₘ =
      zeroₘ

    tr-▸⁻¹-𝟙≡𝟘′ (suc _) (sucₘ ▸t) =
      sucₘ (tr-▸⁻¹-𝟙≡𝟘′ _ ▸t)

    tr-▸⁻¹-𝟙≡𝟘′ (snd _ _) (sndₘ ▸t) =
      sndₘ (tr-▸⁻¹-𝟙≡𝟘′ _ ▸t)

    tr-▸⁻¹-𝟙≡𝟘′ (var _) var =
      sub var (CP₁.≈ᶜ-trivial 𝟙≡𝟘)

    tr-▸⁻¹-𝟙≡𝟘′ (lam _ _) (lamₘ ▸t) =
      lamₘ (tr-▸⁻¹-𝟙≡𝟘″ ▸t)

    tr-▸⁻¹-𝟙≡𝟘′ (_ ∘⟨ _ ⟩ _) (_∘ₘ_ ▸t ▸u) = sub
      (tr-▸⁻¹-𝟙≡𝟘′ _ ▸t ∘ₘ tr-▸⁻¹-𝟙≡𝟘′ _ ▸u)
      (CP₁.≈ᶜ-trivial 𝟙≡𝟘)

    tr-▸⁻¹-𝟙≡𝟘′ (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) (ΠΣₘ ▸A ▸P) = sub
      (ΠΣₘ {δ = C₁.𝟘ᶜ}
         (tr-▸⁻¹-𝟙≡𝟘′ _ ▸A)
         (tr-▸⁻¹-𝟙≡𝟘″ ▸P))
      (CP₁.≈ᶜ-trivial 𝟙≡𝟘)

    tr-▸⁻¹-𝟙≡𝟘′ (prodᵣ _ _ _) (prodᵣₘ ▸t ▸u) = sub
      (prodᵣₘ (tr-▸⁻¹-𝟙≡𝟘′ _ ▸t) (tr-▸⁻¹-𝟙≡𝟘′ _ ▸u))
      (CP₁.≈ᶜ-trivial 𝟙≡𝟘)

    tr-▸⁻¹-𝟙≡𝟘′ (prodₚ _ _ _) (prodₚₘ ▸t ▸u) = sub
      (prodₚₘ (tr-▸⁻¹-𝟙≡𝟘′ _ ▸t) (tr-▸⁻¹-𝟙≡𝟘′ _ ▸u))
      (CP₁.≈ᶜ-trivial 𝟙≡𝟘)

    tr-▸⁻¹-𝟙≡𝟘′ {m = m} {m′ = m′} (fst p _) (fstₘ m″ ▸t mp≡m₂ ok) = fstₘ
      𝟙ᵐ
      (tr-▸⁻¹-𝟙≡𝟘′ _ ▸t)
      (Mo₁.Mode-propositional-without-𝟘ᵐ (flip MP₁.𝟘ᵐ→𝟙≉𝟘 𝟙≡𝟘))
      λ {refl → MP₁.≤-reflexive (MP₁.≈-trivial 𝟙≡𝟘)}

    tr-▸⁻¹-𝟙≡𝟘′ (prodrec _ _ _ _ _ _) (prodrecₘ ▸t ▸u ▸Q ok) = sub
      (prodrecₘ {δ = C₁.𝟘ᶜ} {η = C₁.𝟘ᶜ}
         (tr-▸⁻¹-𝟙≡𝟘′ _ ▸t)
         (tr-▸⁻¹-𝟙≡𝟘″ ▸u)
         (tr-▸⁻¹-𝟙≡𝟘″ ▸Q)
         (Prodrec-reflected ok))
      (CP₁.≈ᶜ-trivial 𝟙≡𝟘)

    tr-▸⁻¹-𝟙≡𝟘′ (natrec _ _ _ _ _ _ _) (natrecₘ ▸z ▸s ▸n ▸P) = sub
      (natrecₘ {δ = C₁.𝟘ᶜ} {θ = C₁.𝟘ᶜ}
         (tr-▸⁻¹-𝟙≡𝟘′ _ ▸z)
         (tr-▸⁻¹-𝟙≡𝟘″ ▸s)
         (tr-▸⁻¹-𝟙≡𝟘′ _ ▸n)
         (tr-▸⁻¹-𝟙≡𝟘″ ▸P))
      (CP₁.≈ᶜ-trivial 𝟙≡𝟘)

    tr-▸⁻¹-𝟙≡𝟘′ (Emptyrec _ _ _) (Emptyrecₘ ▸t ▸A) = sub
      (Emptyrecₘ
         (tr-▸⁻¹-𝟙≡𝟘′ _ ▸t)
         (tr-▸⁻¹-𝟙≡𝟘′ _ ▸A))
      (CP₁.≈ᶜ-trivial 𝟙≡𝟘)

    tr-▸⁻¹-𝟙≡𝟘′ _ (sub ▸t _) =
      tr-▸⁻¹-𝟙≡𝟘″ ▸t

    tr-▸⁻¹-𝟙≡𝟘″ : γ U₂.▸[ m ] tr-Term t → δ U₁.▸[ m′ ] t
    tr-▸⁻¹-𝟙≡𝟘″ ▸t = sub
      (tr-▸⁻¹-𝟙≡𝟘′ _ ▸t)
      (CP₁.≈ᶜ-trivial 𝟙≡𝟘)

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

    tr-▸⁻¹′ Unit Unitₘ refl ≤𝟘 =
      sub Unitₘ (tr-Conₘ-≤ᶜ-𝟘ᶜ-→-≤ᶜ-𝟘ᶜ ≤𝟘)

    tr-▸⁻¹′ star starₘ refl ≤𝟘 =
      sub starₘ (tr-Conₘ-≤ᶜ-𝟘ᶜ-→-≤ᶜ-𝟘ᶜ ≤𝟘)

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
      {m = m} {γ = γ} (prodᵣ p _ _)
      (prodᵣₘ {γ = δ} {δ = η} ▸t ▸u) refl ≤γ′ =
      case tr-Conₘ-≤ᶜ-+ᶜ ≤γ′ of λ (δ′ , η′ , ≤pδ , ≤η , γ≤) →
      case tr-Conₘ-≤ᶜ-tr-Σ-·ᶜ ≤pδ of λ (δ″ , ≤δ , δ′≤) →
      sub
        (prodᵣₘ (tr-▸⁻¹′ _ ▸t (sym (tr-Mode-ᵐ· m (BMΣ Σᵣ))) ≤δ)
           (tr-▸⁻¹′ _ ▸u refl ≤η))
        (begin
           γ                    ≤⟨ γ≤ ⟩
           δ′ C₁.+ᶜ η′          ≤⟨ CP₁.+ᶜ-monotoneˡ δ′≤ ⟩
           p C₁.·ᶜ δ″ C₁.+ᶜ η′  ∎)
      where
      open CR₁

    tr-▸⁻¹′
      {m = m} {γ = γ} (prodₚ p _ _)
      (prodₚₘ {γ = δ} {δ = η} ▸t ▸u) refl ≤γ′ =
      case tr-Conₘ-≤ᶜ-∧ᶜ ≤γ′ of λ (δ′ , η′ , ≤pδ , ≤η , γ≤) →
      case tr-Conₘ-≤ᶜ-tr-Σ-·ᶜ ≤pδ of λ (δ″ , ≤δ , δ′≤) →
      sub
        (prodₚₘ (tr-▸⁻¹′ _ ▸t (sym (tr-Mode-ᵐ· m (BMΣ Σₚ))) ≤δ)
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
              tr-Mode m″ Mo₂.ᵐ· tr-Σ p  ≡˘⟨ tr-Mode-ᵐ· m″ (BMΣ Σₚ) ⟩
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
              Mo₂.⌜ tr-Mode m ⌝ M₂.· tr r                    ≈˘⟨ CP₂.≈ᶜ-refl ∙ M₂.·-congˡ (tr-·-tr-Σ-≡ tr-morphism) ∙ ≈-refl ⟩

              η ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr r M₂.· tr-Σ p ∙
              Mo₂.⌜ tr-Mode m ⌝ M₂.· tr r                    ∎)
           (tr-∙▸[𝟘̂ᵐ?]⁻¹ ▸Q .proj₂)
           (Prodrec-reflected ok))
        (let open CR₁ in begin
           γ                    ≤⟨ γ≤δ′+η′ ⟩
           δ′ C₁.+ᶜ η′          ≤⟨ CP₁.+ᶜ-monotoneˡ δ′≤rδ″ ⟩
           r C₁.·ᶜ δ″ C₁.+ᶜ η′  ∎)

    tr-▸⁻¹′
      {m = m} (natrec p _ r _ _ _ _)
      (natrecₘ {δ = η} ▸z ▸s ▸n ▸P) refl γ≤δ∧θ⊛η+pθ▷r =
      case tr-Conₘ-≤ᶜ-⊛ᶜ γ≤δ∧θ⊛η+pθ▷r of
        λ (_ , _ , η′ , δ′≤δ , θ′≤θ , η′≤η , γ≤δ′∧θ′⊛η′+pθ′▷r) →
      sub
        (natrecₘ (tr-▸⁻¹′ _ ▸z refl δ′≤δ)
           (tr-▸⁻¹′ _ ▸s refl (let open CR₂ in begin
              tr-Conₘ η′ ∙ tr (Mo₁.⌜ m ⌝ M₁.· p) ∙
              tr (Mo₁.⌜ m ⌝ M₁.· r)                 ≤⟨ η′≤η ∙ ≤-reflexive (sym (tr-⌜⌝-· m)) ∙
                                                       ≤-reflexive (sym (tr-⌜⌝-· m)) ⟩
              η ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p ∙
              Mo₂.⌜ tr-Mode m ⌝ M₂.· tr r           ∎))
           (tr-▸⁻¹′ _ ▸n refl θ′≤θ)
           (tr-∙▸[𝟘̂ᵐ?]⁻¹ ▸P .proj₂))
        γ≤δ′∧θ′⊛η′+pθ′▷r

    tr-▸⁻¹′
      {m = m} {γ = γ} (Emptyrec p _ _)
      (Emptyrecₘ ▸t ▸A) refl γ≤pδ =
      case tr-Conₘ-≤ᶜ-·ᶜ γ≤pδ of λ (δ′ , δ′≤δ , γ≤pδ′) →
      sub
        (Emptyrecₘ (tr-▸⁻¹′ _ ▸t (sym (tr-Mode-ᵐ· m BMΠ)) δ′≤δ)
           (tr-▸[𝟘̂ᵐ?]⁻¹ ▸A .proj₂))
        (begin
           γ           ≤⟨ γ≤pδ′ ⟩
           p C₁.·ᶜ δ′  ∎)
      where
      open CR₁

    tr-▸⁻¹′ {γ′ = γ′} {γ = γ} t (sub {γ = δ} ▸t γ′≤δ) refl γ≤γ′ =
      tr-▸⁻¹′ t ▸t refl (begin
        tr-Conₘ γ  ≤⟨ γ≤γ′ ⟩
        γ′         ≤⟨ γ′≤δ ⟩
        δ          ∎)
      where
      open CR₂

    tr-▸[𝟘̂ᵐ?]⁻¹ :
      γ U₂.▸[ Mo₂.𝟘ᵐ? ] tr-Term t → ∃ λ δ → δ U₁.▸[ Mo₁.𝟘ᵐ? ] t
    tr-▸[𝟘̂ᵐ?]⁻¹ {γ = γ} {t = t} = Mo₁.𝟘ᵐ?-elim
      (λ m → γ U₂.▸[ Mo₂.𝟘ᵐ? ] tr-Term t → ∃ λ δ → δ U₁.▸[ m ] t)
      (λ ▸t →
         case tr-Conₘ-≤ᶜ of λ (δ , ≤γ) →
         δ , tr-▸⁻¹′ _ ▸t Mo₂.𝟘ᵐ?≡𝟘ᵐ ≤γ)
      (λ not-ok → Mo₂.𝟘ᵐ?-elim
         (λ m → γ U₂.▸[ m ] tr-Term t → ∃ λ δ → δ U₁.▸[ 𝟙ᵐ ] t)
         (λ ⦃ ok = ok ⦄ ▸t →
            C₁.𝟘ᶜ , tr-▸⁻¹-𝟙≡𝟘 (trivial not-ok ok) ▸t)
         (λ _ ▸t →
            case tr-Conₘ-≤ᶜ of λ (δ , ≤γ) →
            δ , tr-▸⁻¹′ _ ▸t refl ≤γ))

    tr-∙▸[𝟘̂ᵐ?]⁻¹ :
      γ ∙ Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr p U₂.▸[ Mo₂.𝟘ᵐ? ] tr-Term t →
      ∃ λ δ → δ ∙ Mo₁.⌜ Mo₁.𝟘ᵐ? ⌝ M₁.· p U₁.▸[ Mo₁.𝟘ᵐ? ] t
    tr-∙▸[𝟘̂ᵐ?]⁻¹ {γ = γ} {p = p} {t = t} = Mo₁.𝟘ᵐ?-elim
      (λ m →
         γ ∙ Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr p U₂.▸[ Mo₂.𝟘ᵐ? ] tr-Term t →
         ∃ λ δ → δ ∙ Mo₁.⌜ m ⌝ M₁.· p U₁.▸[ m ] t)
      (λ ⦃ ok = ok ⦄ ▸t →
         case tr-Conₘ-≤ᶜ of λ (δ , ≤γ) →
           δ
         , tr-▸⁻¹′ _ ▸t Mo₂.𝟘ᵐ?≡𝟘ᵐ (begin
             tr-Conₘ δ ∙ tr (M₁.𝟘 M₁.· p)   ≈⟨ CP₂.≈ᶜ-refl ∙ cong tr (M₁.·-zeroˡ _) ⟩
             tr-Conₘ δ ∙ tr M₁.𝟘            ≤⟨ ≤γ ∙ tr-𝟘-≤ ⟩
             γ ∙ M₂.𝟘                       ≤⟨ CP₂.≤ᶜ-refl ∙ lemma ok ⟩
             γ ∙ Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr p  ∎))
      (λ not-ok → Mo₂.𝟘ᵐ?-elim
         (λ m →
            γ ∙ Mo₂.⌜ m ⌝ M₂.· tr p U₂.▸[ m ] tr-Term t →
            ∃ λ δ → δ ∙ M₁.𝟙 M₁.· p U₁.▸[ 𝟙ᵐ ] t)
         (λ ⦃ ok = ok ⦄ ▸t →
            let triv = trivial not-ok ok in
            C₁.𝟘ᶜ , sub (tr-▸⁻¹-𝟙≡𝟘 triv ▸t) (CP₁.≈ᶜ-trivial triv))
         (λ _ ▸t →
            case tr-Conₘ-≤ᶜ of λ (δ , ≤γ) →
            δ , tr-▸⁻¹′ _ ▸t refl (begin
             tr-Conₘ δ ∙ tr (M₁.𝟙 M₁.· p)  ≤⟨ ≤γ ∙ ≤-reflexive tr-· ⟩
             γ ∙ tr M₁.𝟙 M₂.· tr p         ≤⟨ CP₂.≤ᶜ-refl ∙ ·-monotoneˡ tr-𝟙 ⟩
             γ ∙ M₂.𝟙 M₂.· tr p            ∎)))
      where
      lemma = λ ok → Mo₂.𝟘ᵐ?-elim
        (λ m → M₂.𝟘 M₂.≤ Mo₂.⌜ m ⌝ M₂.· tr p)
        (begin
           M₂.𝟘            ≈˘⟨ M₂.·-zeroˡ _ ⟩
           M₂.𝟘 M₂.· tr p  ∎)
        (λ not-ok →
           ⊥-elim (not-ok (𝟘ᵐ-in-second-if-in-first ok)))
        where
        open R₂

      open CR₂
