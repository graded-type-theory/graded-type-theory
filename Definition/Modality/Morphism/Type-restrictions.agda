------------------------------------------------------------------------
-- Preserving/reflecting type restrictions
------------------------------------------------------------------------

module Definition.Modality.Morphism.Type-restrictions where

open import Tools.Bool
open import Tools.Function
open import Tools.Level
open import Tools.Nullary
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PropositionalEquality
open import Tools.Sum using (_⊎_; inj₁; inj₂)
open import Tools.Unit

open import Definition.Modality
open import Definition.Modality.Instances.Affine
  using (affineModality)
open import Definition.Modality.Instances.Erasure
  using (𝟘; ω)
open import Definition.Modality.Instances.Erasure.Modality
  using (ErasureModality)
open import Definition.Modality.Instances.Linear-or-affine
  using (𝟘; 𝟙; ≤𝟙; ≤ω; linear-or-affine)
open import Definition.Modality.Instances.Linearity
  using (linearityModality)
open import Definition.Modality.Instances.Unit using (UnitModality)
open import Definition.Modality.Instances.Zero-one-many
  using (𝟘; 𝟙; ω; zero-one-many-greatest)
open import Definition.Modality.Morphism
import Definition.Modality.Properties
open import Definition.Modality.Type-restrictions

open import Definition.Mode as Mode hiding (module Mode)
open import Definition.Mode.Restrictions

open Mode-restrictions

open import Definition.Typed.Restrictions

open import Definition.Untyped.NotParametrised
open import Definition.Untyped.QuantityTranslation

private variable
  𝟙≤𝟘 ok                      : Bool
  R R₁ R₂ R₃                  : Type-restrictions _
  rs rs₁ rs₂                  : Mode-restrictions
  b                           : BinderMode
  M M₁ M₂                     : Set _
  𝕄₁ 𝕄₂                       : Modality _
  tr tr₁ tr₂ tr-Σ tr-Σ₁ tr-Σ₂ : M₁ → M₂
  p q r                       : M

------------------------------------------------------------------------
-- Are-preserving-type-restrictions and
-- Are-reflecting-type-restrictions

-- The property of preserving Type-restrictions.

record Are-preserving-type-restrictions
         {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
         (R₁ : Type-restrictions M₁) (R₂ : Type-restrictions M₂)
         (tr tr-Σ : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  private
    module R₁ = Type-restrictions R₁
    module R₂ = Type-restrictions R₂

  field
    -- If R₁.Unit-restriction holds, then R₂.Unit-restriction holds.
    Unit-preserved :
      R₁.Unit-restriction → R₂.Unit-restriction

    -- The functions tr and tr-Σ preserve the ΠΣ-restriction property
    -- in a certain way.
    ΠΣ-preserved :
      R₁.ΠΣ-restriction b p q →
      R₂.ΠΣ-restriction b (tr-BinderMode tr tr-Σ b p) (tr q)

    -- The functions tr and tr-Σ preserve the Prodrec-restriction
    -- property in a certain way.
    Prodrec-preserved :
      R₁.Prodrec-restriction r p q →
      R₂.Prodrec-restriction (tr r) (tr-Σ p) (tr q)

-- The property of reflecting Type-restrictions.

record Are-reflecting-type-restrictions
         {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
         (R₁ : Type-restrictions M₁) (R₂ : Type-restrictions M₂)
         (tr tr-Σ : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  private
    module R₁ = Type-restrictions R₁
    module R₂ = Type-restrictions R₂

  field
    -- If R₂.Unit-restriction holds, then R₁.Unit-restriction holds.
    Unit-reflected :
      R₂.Unit-restriction → R₁.Unit-restriction

    -- The functions tr and tr-Σ reflect the ΠΣ-restriction property
    -- in a certain way.
    ΠΣ-reflected :
      R₂.ΠΣ-restriction b (tr-BinderMode tr tr-Σ b p) (tr q) →
      R₁.ΠΣ-restriction b p q

    -- The functions tr and tr-Σ reflect the Prodrec-restriction
    -- property in a certain way.
    Prodrec-reflected :
      R₂.Prodrec-restriction (tr r) (tr-Σ p) (tr q) →
      R₁.Prodrec-restriction r p q

------------------------------------------------------------------------
-- Identity

-- For every value R of type Type-restrictions the identity function
-- preserves Type-restrictions for R and R.

Are-preserving-type-restrictions-id :
  Are-preserving-type-restrictions R R idᶠ idᶠ
Are-preserving-type-restrictions-id {R = R} = λ where
    .Unit-preserved           → idᶠ
    .Prodrec-preserved        → idᶠ
    .ΠΣ-preserved {b = BMΠ}   → idᶠ
    .ΠΣ-preserved {b = BMΣ _} → idᶠ
  where
  open Are-preserving-type-restrictions
  open Type-restrictions R

-- For every value R of type Type-restrictions the identity function
-- reflects Type-restrictions for R and R.

Are-reflecting-type-restrictions-id :
  Are-reflecting-type-restrictions R R idᶠ idᶠ
Are-reflecting-type-restrictions-id {R = R} = λ where
    .Unit-reflected           → idᶠ
    .Prodrec-reflected        → idᶠ
    .ΠΣ-reflected {b = BMΠ}   → idᶠ
    .ΠΣ-reflected {b = BMΣ _} → idᶠ
  where
  open Are-reflecting-type-restrictions
  open Type-restrictions R

------------------------------------------------------------------------
-- Composition

-- Composition preserves Are-preserving-type-restrictions.

Are-preserving-type-restrictions-∘ :
  Are-preserving-type-restrictions R₂ R₃ tr₁ tr-Σ₁ →
  Are-preserving-type-restrictions R₁ R₂ tr₂ tr-Σ₂ →
  Are-preserving-type-restrictions
    R₁ R₃ (tr₁ ∘→ tr₂) (tr-Σ₁ ∘→ tr-Σ₂)
Are-preserving-type-restrictions-∘ m₁ m₂ = λ where
    .Unit-preserved →
      M₁.Unit-preserved ∘→ M₂.Unit-preserved
    .Prodrec-preserved →
      M₁.Prodrec-preserved ∘→ M₂.Prodrec-preserved
    .ΠΣ-preserved {b = BMΠ} →
      M₁.ΠΣ-preserved ∘→ M₂.ΠΣ-preserved
    .ΠΣ-preserved {b = BMΣ _} →
      M₁.ΠΣ-preserved ∘→ M₂.ΠΣ-preserved
  where
  open Are-preserving-type-restrictions
  module M₁ = Are-preserving-type-restrictions m₁
  module M₂ = Are-preserving-type-restrictions m₂

-- Composition preserves Are-reflecting-type-restrictions.

Are-reflecting-type-restrictions-∘ :
  Are-reflecting-type-restrictions R₂ R₃ tr₁ tr-Σ₁ →
  Are-reflecting-type-restrictions R₁ R₂ tr₂ tr-Σ₂ →
  Are-reflecting-type-restrictions R₁ R₃ (tr₁ ∘→ tr₂) (tr-Σ₁ ∘→ tr-Σ₂)
Are-reflecting-type-restrictions-∘ m₁ m₂ = λ where
    .Unit-reflected →
      M₂.Unit-reflected ∘→ M₁.Unit-reflected
    .Prodrec-reflected →
      M₂.Prodrec-reflected ∘→ M₁.Prodrec-reflected
    .ΠΣ-reflected {b = BMΠ} →
      M₂.ΠΣ-reflected ∘→ M₁.ΠΣ-reflected
    .ΠΣ-reflected {b = BMΣ _} →
      M₂.ΠΣ-reflected ∘→ M₁.ΠΣ-reflected
  where
  open Are-reflecting-type-restrictions
  module M₁ = Are-reflecting-type-restrictions m₁
  module M₂ = Are-reflecting-type-restrictions m₂

------------------------------------------------------------------------
-- Preserving/reflecting certain type restrictions

-- If tr preserves type restrictions for R₁ and R₂, then it also does
-- this for equal-binder-quantities M₁ R₁ and
-- equal-binder-quantities M₂ R₂.

Are-preserving-type-restrictions-equal-binder-quantities :
  Are-preserving-type-restrictions R₁ R₂ tr tr →
  Are-preserving-type-restrictions
    (equal-binder-quantities R₁)
    (equal-binder-quantities R₂)
    tr tr
Are-preserving-type-restrictions-equal-binder-quantities {tr = tr} r =
  record
    { Unit-preserved    = R.Unit-preserved
    ; Prodrec-preserved = R.Prodrec-preserved
    ; ΠΣ-preserved      = λ {b = b} → λ where
        (bn , refl) →
            R.ΠΣ-preserved bn
          , tr-BinderMode-one-function _ _ refl b
    }
  where
  module R = Are-preserving-type-restrictions r

-- If tr reflects type restrictions for R₁ and R₂, then it also does
-- this for equal-binder-quantities M₁ R₁ and
-- equal-binder-quantities M₂ R₂, assuming that the function is
-- injective.

Are-reflecting-type-restrictions-equal-binder-quantities :
  (∀ {p q} → tr p ≡ tr q → p ≡ q) →
  Are-reflecting-type-restrictions R₁ R₂ tr tr →
  Are-reflecting-type-restrictions
    (equal-binder-quantities R₁)
    (equal-binder-quantities R₂)
    tr tr
Are-reflecting-type-restrictions-equal-binder-quantities
  {tr = tr} inj r = record
  { Unit-reflected    = Unit-reflected
  ; Prodrec-reflected = Prodrec-reflected
  ; ΠΣ-reflected      =
      λ {b = b} {p = p} {q = q} (bn , eq) →
          ΠΣ-reflected bn
        , inj (
            tr p                     ≡˘⟨ tr-BinderMode-one-function _ _ refl b ⟩
            tr-BinderMode tr tr b p  ≡⟨ eq ⟩
            tr q                     ∎)
  }
  where
  open Are-reflecting-type-restrictions r
  open Tools.Reasoning.PropositionalEquality

-- If the functions tr and tr-Σ preserve certain type restrictions,
-- then they also do this for certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘, assuming that tr maps a certain zero to a
-- certain zero.

Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘 :
  tr (Modality.𝟘 𝕄₁) ≡ Modality.𝟘 𝕄₂ →
  Are-preserving-type-restrictions R₁ R₂ tr tr-Σ →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘 𝕄₁ R₁)
    (second-ΠΣ-quantities-𝟘 𝕄₂ R₂)
    tr tr-Σ
Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘 tr-𝟘 r = record
  { Unit-preserved    = Unit-preserved
  ; Prodrec-preserved = Prodrec-preserved
  ; ΠΣ-preserved      = λ where
      (b , refl) → ΠΣ-preserved b , tr-𝟘
  }
  where
  open Are-preserving-type-restrictions r

-- If the functions tr and tr-Σ reflect certain type restrictions,
-- then they also do this for certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘, assuming that tr only maps a certain zero
-- to a certain zero.

Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘 :
  (∀ {p} → tr p ≡ Modality.𝟘 𝕄₂ → p ≡ Modality.𝟘 𝕄₁) →
  Are-reflecting-type-restrictions R₁ R₂ tr tr-Σ →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘 𝕄₁ R₁)
    (second-ΠΣ-quantities-𝟘 𝕄₂ R₂)
    tr tr-Σ
Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘 tr-𝟘 r = record
  { Unit-reflected    = Unit-reflected
  ; Prodrec-reflected = Prodrec-reflected
  ; ΠΣ-reflected      = λ (b , eq) → ΠΣ-reflected b , tr-𝟘 eq
  }
  where
  open Are-reflecting-type-restrictions r

-- If the functions tr and tr-Σ preserve certain type restrictions,
-- then they also do this for certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω, given that certain assumptions hold.

Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ {ω₁ ω₂} →
  Is-morphism 𝕄₁ 𝕄₂ tr →
  Is-Σ-morphism 𝕄₁ 𝕄₂ tr tr-Σ →
  (¬ T (Modality.𝟘ᵐ-allowed 𝕄₁) →
   (∀ {p} → tr p ≡ Modality.𝟘 𝕄₂ ⇔ p ≡ Modality.𝟘 𝕄₁) ×
   (∀ {p} → tr-Σ p ≡ Modality.𝟘 𝕄₂ ⇔ p ≡ Modality.𝟘 𝕄₁)) →
  tr ω₁ ≡ ω₂ →
  Are-preserving-type-restrictions R₁ R₂ tr tr-Σ →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω₁ 𝕄₁ R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω₂ 𝕄₂ R₂)
    tr tr-Σ
Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
  {𝕄₁ = 𝕄₁} {𝕄₂ = 𝕄₂} {tr = tr} {tr-Σ = tr-Σ} {ω₁ = ω₁} {ω₂ = ω₂}
  m m-Σ tr-𝟘 tr-ω r = record
  { Unit-preserved    = Unit-preserved
  ; Prodrec-preserved = Prodrec-preserved
  ; ΠΣ-preserved      = λ {b = b} (bn , is-𝟘 , not-𝟘) →
      ΠΣ-preserved bn , lemma₁ b is-𝟘 , lemma₂ b not-𝟘
  }
  where
  module M₁ = Modality 𝕄₁
  module M₂ = Modality 𝕄₂
  open Are-preserving-type-restrictions r
  open Definition.Modality.Properties 𝕄₁
  open Is-morphism m
  open Is-Σ-morphism m-Σ

  tr-≡-𝟘-⇔′ : ∀ {p} → tr p ≡ M₂.𝟘 ⇔ p ≡ M₁.𝟘
  tr-≡-𝟘-⇔′ = Mode.𝟘ᵐ-allowed-elim 𝕄₁
    tr-≡-𝟘-⇔
    (λ not-ok → tr-𝟘 not-ok .proj₁)

  tr-Σ-≡-𝟘-⇔ : ∀ {p} → tr-Σ p ≡ M₂.𝟘 ⇔ p ≡ M₁.𝟘
  tr-Σ-≡-𝟘-⇔ = Mode.𝟘ᵐ-allowed-elim 𝕄₁
    (λ ok →
         (λ hyp → tr-Σ-≡-𝟘-→ (𝟘ᵐ-in-second-if-in-first ok) hyp .proj₂)
       , (λ { refl → tr-Σ-𝟘-≡ m ok }))
    (λ not-ok → tr-𝟘 not-ok .proj₂)

  lemma₁ :
    ∀ {p q} b →
    (p ≡ M₁.𝟘 → q ≡ M₁.𝟘) →
    tr-BinderMode tr tr-Σ b p ≡ M₂.𝟘 → tr q ≡ M₂.𝟘
  lemma₁ {p = p} {q = q} BMΠ hyp =
    tr p ≡ M₂.𝟘  →⟨ tr-≡-𝟘-⇔′ .proj₁ ⟩
    p ≡ M₁.𝟘     →⟨ hyp ⟩
    q ≡ M₁.𝟘     →⟨ tr-≡-𝟘-⇔′ .proj₂ ⟩
    tr q ≡ M₂.𝟘  □
  lemma₁ {p = p} {q = q} (BMΣ _) hyp =
    tr-Σ p ≡ M₂.𝟘  →⟨ tr-Σ-≡-𝟘-⇔ .proj₁ ⟩
    p ≡ M₁.𝟘       →⟨ hyp ⟩
    q ≡ M₁.𝟘       →⟨ tr-≡-𝟘-⇔′ .proj₂ ⟩
    tr q ≡ M₂.𝟘    □

  lemma₂ :
    ∀ {p q} b →
    (p ≢ M₁.𝟘 → q ≡ ω₁) →
    tr-BinderMode tr tr-Σ b p ≢ M₂.𝟘 → tr q ≡ ω₂
  lemma₂ {p = p} {q = q} BMΠ hyp =
    tr p ≢ M₂.𝟘  →⟨ _∘→ tr-≡-𝟘-⇔′ .proj₂ ⟩
    p ≢ M₁.𝟘     →⟨ hyp ⟩
    q ≡ ω₁       →⟨ (λ { refl → tr-ω }) ⟩
    tr q ≡ ω₂    □
  lemma₂ {p = p} {q = q} (BMΣ _) hyp =
    tr-Σ p ≢ M₂.𝟘  →⟨ _∘→ tr-Σ-≡-𝟘-⇔ .proj₂ ⟩
    p ≢ M₁.𝟘       →⟨ hyp ⟩
    q ≡ ω₁         →⟨ (λ { refl → tr-ω }) ⟩
    tr q ≡ ω₂      □

-- A variant of
-- Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω with
-- different assumptions.

Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω′ :
  ∀ {ω₁ ω₂} →
  Is-order-embedding 𝕄₁ 𝕄₂ tr →
  Is-Σ-morphism 𝕄₁ 𝕄₂ tr tr-Σ →
  (¬ T (Modality.𝟘ᵐ-allowed 𝕄₁) → ∀ {p} → tr-Σ p ≡ tr p) →
  tr ω₁ ≡ ω₂ →
  Are-preserving-type-restrictions R₁ R₂ tr tr-Σ →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω₁ 𝕄₁ R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω₂ 𝕄₂ R₂)
    tr tr-Σ
Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω′
  {𝕄₁ = 𝕄₁} {𝕄₂ = 𝕄₂} {tr = tr} {tr-Σ = tr-Σ} {ω₁ = ω₁} {ω₂ = ω₂}
  emb m tr-Σ≡tr tr-ω r = record
  { Unit-preserved    = Unit-preserved
  ; Prodrec-preserved = Prodrec-preserved
  ; ΠΣ-preserved      = λ {b = b} (bn , is-𝟘 , not-𝟘) →
      ΠΣ-preserved bn , lemma₂ b is-𝟘 , lemma₄ b not-𝟘
  }
  where
  module M₁ = Modality 𝕄₁
  module M₂ = Modality 𝕄₂
  open Are-preserving-type-restrictions r
  open Definition.Modality.Properties 𝕄₁
  open Is-order-embedding emb
  open Is-Σ-morphism m

  lemma₁ :
    ∀ {p q} →
    (p ≡ M₁.𝟘 → q ≡ M₁.𝟘) →
    tr p ≡ M₂.𝟘 → tr q ≡ M₂.𝟘
  lemma₁ {p = p} {q = q} hyp =
    case trivial-⊎-tr-𝟘 of λ where
      (inj₁ 𝟙≡𝟘) →
        tr p ≡ M₂.𝟘  ≡⟨ cong (λ p → tr p ≡ _) (≈-trivial 𝟙≡𝟘) ⟩→
        tr q ≡ M₂.𝟘  □
      (inj₂ tr-𝟘) →
        tr p ≡ M₂.𝟘     ≡⟨ cong (_ ≡_) (sym tr-𝟘) ⟩→
        tr p ≡ tr M₁.𝟘  →⟨ tr-injective ⟩
        p ≡ M₁.𝟘        →⟨ hyp ⟩
        q ≡ M₁.𝟘        →⟨ (λ { refl → tr-𝟘 }) ⟩
        tr q ≡ M₂.𝟘     □

  lemma₂ :
    ∀ {p q} b →
    (p ≡ M₁.𝟘 → q ≡ M₁.𝟘) →
    tr-BinderMode tr tr-Σ b p ≡ M₂.𝟘 → tr q ≡ M₂.𝟘
  lemma₂                 BMΠ     = lemma₁
  lemma₂ {p = p} {q = q} (BMΣ _) = λ hyp →
    Mode.𝟘ᵐ-allowed-elim 𝕄₁
      (λ ok →
         tr-Σ p ≡ M₂.𝟘  →⟨ (λ hyp → tr-Σ-≡-𝟘-→ (𝟘ᵐ-in-second-if-in-first ok) hyp .proj₂) ⟩
         p ≡ M₁.𝟘       →⟨ hyp ⟩
         q ≡ M₁.𝟘       →⟨ tr-≡-𝟘-⇔ ok .proj₂ ⟩
         tr q ≡ M₂.𝟘    □)
      (λ not-ok →
         tr-Σ p ≡ M₂.𝟘  ≡⟨ cong (_≡ _) (tr-Σ≡tr not-ok) ⟩→
         tr p ≡ M₂.𝟘    →⟨ lemma₁ hyp ⟩
         tr q ≡ M₂.𝟘    □)

  lemma₃ :
    ∀ {p q} →
    (p ≢ M₁.𝟘 → q ≡ ω₁) →
    tr p ≢ M₂.𝟘 → tr q ≡ ω₂
  lemma₃ {p = p} {q = q} hyp =
    case trivial-⊎-tr-𝟘 of λ where
      (inj₁ 𝟙≡𝟘) →
        tr p ≢ M₂.𝟘  →⟨ (λ _ → ≈-trivial 𝟙≡𝟘) ⟩
        q ≡ ω₁       →⟨ (λ { refl → tr-ω }) ⟩
        tr q ≡ ω₂    □
      (inj₂ tr-𝟘) →
        tr p ≢ M₂.𝟘     ≡⟨ cong (_ ≢_) (sym tr-𝟘) ⟩→
        tr p ≢ tr M₁.𝟘  →⟨ _∘→ cong tr ⟩
        p ≢ M₁.𝟘        →⟨ hyp ⟩
        q ≡ ω₁          →⟨ (λ { refl → tr-ω }) ⟩
        tr q ≡ ω₂       □

  lemma₄ :
    ∀ {p q} b →
    (p ≢ M₁.𝟘 → q ≡ ω₁) →
    tr-BinderMode tr tr-Σ b p ≢ M₂.𝟘 → tr q ≡ ω₂
  lemma₄                 BMΠ     = lemma₃
  lemma₄ {p = p} {q = q} (BMΣ Σ) = λ hyp →
    Mode.𝟘ᵐ-allowed-elim 𝕄₁
      (λ ok →
         tr-Σ p ≢ M₂.𝟘  →⟨ _∘→ (λ { refl → tr-Σ-𝟘-≡ tr-morphism ok }) ⟩
         p ≢ M₁.𝟘       →⟨ hyp ⟩
         q ≡ ω₁         →⟨ (λ { refl → tr-ω }) ⟩
         tr q ≡ ω₂      □)
      (λ not-ok →
         tr-Σ p ≢ M₂.𝟘  ≡⟨ cong (_≢ _) (tr-Σ≡tr not-ok) ⟩→
         tr p ≢ M₂.𝟘    →⟨ lemma₃ hyp ⟩
         tr q ≡ ω₂      □)

-- If the functions tr and tr-Σ reflect certain type restrictions,
-- then they also do this for certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω, given that certain assumptions hold.

Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ {ω₁ ω₂} →
  Is-morphism 𝕄₁ 𝕄₂ tr →
  Is-Σ-morphism 𝕄₁ 𝕄₂ tr tr-Σ →
  (¬ T (Modality.𝟘ᵐ-allowed 𝕄₁) →
   (∀ {p} → tr p ≡ Modality.𝟘 𝕄₂ ⇔ p ≡ Modality.𝟘 𝕄₁) ×
   (∀ {p} → tr-Σ p ≡ Modality.𝟘 𝕄₂ ⇔ p ≡ Modality.𝟘 𝕄₁)) →
  (∀ {p} → tr p ≡ ω₂ → p ≡ ω₁) →
  Are-reflecting-type-restrictions R₁ R₂ tr tr-Σ →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω₁ 𝕄₁ R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω₂ 𝕄₂ R₂)
    tr tr-Σ
Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
  {𝕄₁ = 𝕄₁} {𝕄₂ = 𝕄₂} {tr = tr} {tr-Σ = tr-Σ} {ω₁ = ω₁} {ω₂ = ω₂}
  m m-Σ tr-𝟘 tr-ω r = record
  { Unit-reflected    = Unit-reflected
  ; Prodrec-reflected = Prodrec-reflected
  ; ΠΣ-reflected      = λ {b = b} (bn , is-𝟘 , not-𝟘) →
      ΠΣ-reflected bn , lemma₁ b is-𝟘 , lemma₂ b not-𝟘
  }
  where
  module M₁ = Modality 𝕄₁
  module M₂ = Modality 𝕄₂
  open Are-reflecting-type-restrictions r
  open Definition.Modality.Properties 𝕄₁
  open Is-morphism m
  open Is-Σ-morphism m-Σ

  tr-≡-𝟘-⇔′ : ∀ {p} → tr p ≡ M₂.𝟘 ⇔ p ≡ M₁.𝟘
  tr-≡-𝟘-⇔′ = Mode.𝟘ᵐ-allowed-elim 𝕄₁
    tr-≡-𝟘-⇔
    (λ not-ok → tr-𝟘 not-ok .proj₁)

  tr-Σ-≡-𝟘-⇔ : ∀ {p} → tr-Σ p ≡ M₂.𝟘 ⇔ p ≡ M₁.𝟘
  tr-Σ-≡-𝟘-⇔ = Mode.𝟘ᵐ-allowed-elim 𝕄₁
    (λ ok →
         (λ hyp → tr-Σ-≡-𝟘-→ (𝟘ᵐ-in-second-if-in-first ok) hyp .proj₂)
       , (λ { refl → tr-Σ-𝟘-≡ m ok }))
    (λ not-ok → tr-𝟘 not-ok .proj₂)

  lemma₁ :
    ∀ {p q} b →
    (tr-BinderMode tr tr-Σ b p ≡ M₂.𝟘 → tr q ≡ M₂.𝟘) →
    p ≡ M₁.𝟘 → q ≡ M₁.𝟘
  lemma₁ {p = p} {q = q} BMΠ hyp =
    p ≡ M₁.𝟘     →⟨ tr-≡-𝟘-⇔′ .proj₂ ⟩
    tr p ≡ M₂.𝟘  →⟨ hyp ⟩
    tr q ≡ M₂.𝟘  →⟨ tr-≡-𝟘-⇔′ .proj₁ ⟩
    q ≡ M₁.𝟘     □
  lemma₁ {p = p} {q = q} (BMΣ _) hyp =
    p ≡ M₁.𝟘       →⟨ tr-Σ-≡-𝟘-⇔ .proj₂ ⟩
    tr-Σ p ≡ M₂.𝟘  →⟨ hyp ⟩
    tr q ≡ M₂.𝟘    →⟨ tr-≡-𝟘-⇔′ .proj₁ ⟩
    q ≡ M₁.𝟘       □

  lemma₂ :
    ∀ {p q} b →
    (tr-BinderMode tr tr-Σ b p ≢ M₂.𝟘 → tr q ≡ ω₂) →
    p ≢ M₁.𝟘 → q ≡ ω₁
  lemma₂ {p = p} {q = q} BMΠ hyp =
    p ≢ M₁.𝟘     →⟨ _∘→ tr-≡-𝟘-⇔′ .proj₁ ⟩
    tr p ≢ M₂.𝟘  →⟨ hyp ⟩
    tr q ≡ ω₂    →⟨ tr-ω ⟩
    q ≡ ω₁       □
  lemma₂ {p = p} {q = q} (BMΣ _) hyp =
    p ≢ M₁.𝟘       →⟨ _∘→ tr-Σ-≡-𝟘-⇔ .proj₁ ⟩
    tr-Σ p ≢ M₂.𝟘  →⟨ hyp ⟩
    tr q ≡ ω₂      →⟨ tr-ω ⟩
    q ≡ ω₁         □

-- A variant of
-- Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω with
-- different assumptions.

Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω′ :
  ∀ {ω₁ ω₂} →
  Is-order-embedding 𝕄₁ 𝕄₂ tr →
  Is-Σ-morphism 𝕄₁ 𝕄₂ tr tr-Σ →
  (¬ T (Modality.𝟘ᵐ-allowed 𝕄₁) → ∀ {p} → tr-Σ p ≡ tr p) →
  (∀ {p} → tr p ≡ ω₂ → p ≡ ω₁) →
  Are-reflecting-type-restrictions R₁ R₂ tr tr-Σ →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω₁ 𝕄₁ R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω₂ 𝕄₂ R₂)
    tr tr-Σ
Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω′
  {𝕄₁ = 𝕄₁} {𝕄₂ = 𝕄₂} {tr = tr} {tr-Σ = tr-Σ} {ω₁ = ω₁} {ω₂ = ω₂}
  emb m tr-Σ≡tr tr-ω r = record
  { Unit-reflected    = Unit-reflected
  ; Prodrec-reflected = Prodrec-reflected
  ; ΠΣ-reflected      = λ {b = b} (bn , is-𝟘 , not-𝟘) →
      ΠΣ-reflected bn , lemma₂ b is-𝟘 , lemma₄ b not-𝟘
  }
  where
  module M₁ = Modality 𝕄₁
  module M₂ = Modality 𝕄₂
  open Are-reflecting-type-restrictions r
  open Definition.Modality.Properties 𝕄₁
  open Is-order-embedding emb
  open Is-Σ-morphism m

  lemma₁ :
    ∀ {p q} →
    (tr p ≡ M₂.𝟘 → tr q ≡ M₂.𝟘) →
    p ≡ M₁.𝟘 → q ≡ M₁.𝟘
  lemma₁ {p = p} {q = q} hyp =
    case trivial-⊎-tr-𝟘 of λ where
      (inj₁ 𝟙≡𝟘) →
        p ≡ M₁.𝟘  →⟨ (λ _ → ≈-trivial 𝟙≡𝟘) ⟩
        q ≡ M₁.𝟘  □
      (inj₂ tr-𝟘) →
        p ≡ M₁.𝟘        →⟨ (λ { refl → tr-𝟘 }) ⟩
        tr p ≡ M₂.𝟘     →⟨ hyp ⟩
        tr q ≡ M₂.𝟘     ≡⟨ cong (_ ≡_) (sym tr-𝟘) ⟩→
        tr q ≡ tr M₁.𝟘  →⟨ tr-injective ⟩
        q ≡ M₁.𝟘        □

  lemma₂ :
    ∀ {p q} b →
    (tr-BinderMode tr tr-Σ b p ≡ M₂.𝟘 → tr q ≡ M₂.𝟘) →
    p ≡ M₁.𝟘 → q ≡ M₁.𝟘
  lemma₂                 BMΠ     = lemma₁
  lemma₂ {p = p} {q = q} (BMΣ _) = λ hyp →
    Mode.𝟘ᵐ-allowed-elim 𝕄₁
      (λ ok →
         p ≡ M₁.𝟘       →⟨ (λ { refl → tr-Σ-𝟘-≡ tr-morphism ok }) ⟩
         tr-Σ p ≡ M₂.𝟘  →⟨ hyp ⟩
         tr q ≡ M₂.𝟘    →⟨ tr-≡-𝟘-⇔ ok .proj₁ ⟩
         q ≡ M₁.𝟘       □)
      (λ not-ok → lemma₁ (
         tr p ≡ M₂.𝟘    ≡⟨ cong (_≡ _) (sym (tr-Σ≡tr not-ok)) ⟩→
         tr-Σ p ≡ M₂.𝟘  →⟨ hyp ⟩
         tr q ≡ M₂.𝟘    □))

  lemma₃ :
    ∀ {p q} →
    (tr p ≢ M₂.𝟘 → tr q ≡ ω₂) →
    p ≢ M₁.𝟘 → q ≡ ω₁
  lemma₃ {p = p} {q = q} hyp =
    case trivial-⊎-tr-𝟘 of λ where
      (inj₁ 𝟙≡𝟘) →
        p ≢ M₁.𝟘  →⟨ (λ _ → ≈-trivial 𝟙≡𝟘) ⟩
        q ≡ ω₁    □
      (inj₂ tr-𝟘) →
        p ≢ M₁.𝟘        →⟨ _∘→ tr-injective ⟩
        tr p ≢ tr M₁.𝟘  ≡⟨ cong (_ ≢_) tr-𝟘 ⟩→
        tr p ≢ M₂.𝟘     →⟨ hyp ⟩
        tr q ≡ ω₂       →⟨ tr-ω ⟩
        q ≡ ω₁          □

  lemma₄ :
    ∀ {p q} b →
    (tr-BinderMode tr tr-Σ b p ≢ M₂.𝟘 → tr q ≡ ω₂) →
    p ≢ M₁.𝟘 → q ≡ ω₁
  lemma₄                 BMΠ     = lemma₃
  lemma₄ {p = p} {q = q} (BMΣ _) = λ hyp →
    Mode.𝟘ᵐ-allowed-elim 𝕄₁
      (λ ok →
         p ≢ M₁.𝟘       →⟨ _∘→ (λ hyp → tr-Σ-≡-𝟘-→ (𝟘ᵐ-in-second-if-in-first ok) hyp .proj₂) ⟩
         tr-Σ p ≢ M₂.𝟘  →⟨ hyp ⟩
         tr q ≡ ω₂      →⟨ tr-ω ⟩
         q ≡ ω₁          □)
      (λ not-ok → lemma₃ (
         tr p ≢ M₂.𝟘    ≡⟨ cong (_≢ _) (sym (tr-Σ≡tr not-ok)) ⟩→
         tr-Σ p ≢ M₂.𝟘  →⟨ hyp ⟩
         tr q ≡ ω₂      □))

-- If the functions tr and tr-Σ preserve certain type restrictions,
-- then they also do this for certain type restrictions obtained using
-- no-erased-matches, given that a certain assumption holds.

Are-preserving-type-restrictions-no-erased-matches :
  ∀ 𝕄₁ 𝕄₂ →
  (Modality.𝟙 𝕄₂ ≢ Modality.𝟘 𝕄₂ →
   Modality.𝟙 𝕄₁ ≢ Modality.𝟘 𝕄₁ ×
   (∀ {p} → tr p ≡ Modality.𝟘 𝕄₂ → p ≡ Modality.𝟘 𝕄₁) ⊎
   (∀ {p} → tr p ≢ Modality.𝟘 𝕄₂)) →
  Are-preserving-type-restrictions R₁ R₂ tr tr-Σ →
  Are-preserving-type-restrictions
    (no-erased-matches 𝕄₁ R₁)
    (no-erased-matches 𝕄₂ R₂)
    tr tr-Σ
Are-preserving-type-restrictions-no-erased-matches
  {tr = tr} 𝕄₁ 𝕄₂ hyp r = record
  { Unit-preserved    = Unit-preserved
  ; ΠΣ-preserved      = ΠΣ-preserved
  ; Prodrec-preserved = λ {r = r} (p , ≢𝟘) →
        Prodrec-preserved p
      , (λ 𝟙≢𝟘 → case hyp 𝟙≢𝟘 of λ where
           (inj₁ (𝟙≢𝟘 , tr-≡-𝟘-→)) →
             tr r ≡ M₂.𝟘  →⟨ tr-≡-𝟘-→ ⟩
             r ≡ M₁.𝟘     →⟨ ≢𝟘 𝟙≢𝟘 ⟩
             ⊥            □
           (inj₂ ≢𝟘) →
             tr r ≡ M₂.𝟘  →⟨ ≢𝟘 ⟩
             ⊥            □)
  }
  where
  module M₁ = Modality 𝕄₁
  module M₂ = Modality 𝕄₂
  open Are-preserving-type-restrictions r

-- If the functions tr and tr-Σ reflect certain type restrictions,
-- then they also do this for certain type restrictions obtained using
-- no-erased-matches, given that a certain assumption holds.

Are-reflecting-type-restrictions-no-erased-matches :
  ∀ 𝕄₁ 𝕄₂ →
  (Modality.𝟙 𝕄₁ ≢ Modality.𝟘 𝕄₁ →
   Modality.𝟙 𝕄₂ ≢ Modality.𝟘 𝕄₂ ×
   (∀ {p} → p ≡ Modality.𝟘 𝕄₁ → tr p ≡ Modality.𝟘 𝕄₂)) →
  Are-reflecting-type-restrictions R₁ R₂ tr tr-Σ →
  Are-reflecting-type-restrictions
    (no-erased-matches 𝕄₁ R₁)
    (no-erased-matches 𝕄₂ R₂)
    tr tr-Σ
Are-reflecting-type-restrictions-no-erased-matches
  {tr = tr} 𝕄₁ 𝕄₂ hyp r = record
  { Unit-reflected    = Unit-reflected
  ; ΠΣ-reflected      = ΠΣ-reflected
  ; Prodrec-reflected = λ {r = r} (p , ≢𝟘) →
        Prodrec-reflected p
      , (λ 𝟙≢𝟘 →
           r ≡ M₁.𝟘     →⟨ hyp 𝟙≢𝟘 .proj₂ ⟩
           tr r ≡ M₂.𝟘  →⟨ ≢𝟘 (hyp 𝟙≢𝟘 .proj₁) ⟩
           ⊥            □)
  }
  where
  module M₁ = Modality 𝕄₁
  module M₂ = Modality 𝕄₂
  open Are-reflecting-type-restrictions r

------------------------------------------------------------------------
-- Some lemmas related to equal-binder-quantities and concrete
-- translation functions

-- The functions erasure→zero-one-many and erasure→zero-one-many-Σ do
-- not preserve certain type restrictions obtained using
-- equal-binder-quantities.

¬-erasure→zero-one-many-Σ-preserves-equal-binder-quantities :
  ¬ Are-preserving-type-restrictions
      (equal-binder-quantities no-type-restrictions)
      (equal-binder-quantities R)
      erasure→zero-one-many erasure→zero-one-many-Σ
¬-erasure→zero-one-many-Σ-preserves-equal-binder-quantities r =
  case ΠΣ-preserved {b = BMΣ Σₚ} {p = ω} (_ , refl) .proj₂ of λ ()
  where
  open Are-preserving-type-restrictions r

-- The functions affine→linear-or-affine and affine→linear-or-affine-Σ
-- do not preserve certain type restrictions obtained using
-- equal-binder-quantities.

¬-affine→linear-or-affine-Σ-preserves-equal-binder-quantities :
  ¬ Are-preserving-type-restrictions
      (equal-binder-quantities no-type-restrictions)
      (equal-binder-quantities R)
      affine→linear-or-affine affine→linear-or-affine-Σ
¬-affine→linear-or-affine-Σ-preserves-equal-binder-quantities r =
  case ΠΣ-preserved {b = BMΣ Σₚ} {p = 𝟙} (_ , refl) .proj₂ of λ ()
  where
  open Are-preserving-type-restrictions r

------------------------------------------------------------------------
-- Some lemmas related to second-ΠΣ-quantities-𝟘-or-ω and concrete
-- translation functions

-- If the function unit→erasure preserves certain type restrictions,
-- then it also does this for certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

unit→erasure-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  Are-preserving-type-restrictions
    R₁ R₂ unit→erasure unit→erasure →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω tt UnitModality R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω (ErasureModality rs) R₂)
    unit→erasure unit→erasure
unit→erasure-preserves-second-ΠΣ-quantities-𝟘-or-ω {rs = rs} =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω′
    {𝕄₂ = ErasureModality rs}
    unit⇨erasure
    (Is-morphism→Is-Σ-morphism $
     Is-order-embedding.tr-morphism unit⇨erasure)
    (λ _ → refl)
    refl

-- If the function unit→erasure reflects certain type restrictions,
-- then it also does this for certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

unit→erasure-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  Are-reflecting-type-restrictions
    R₁ R₂ unit→erasure unit→erasure →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω tt UnitModality R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω (ErasureModality rs) R₂)
    unit→erasure unit→erasure
unit→erasure-reflects-second-ΠΣ-quantities-𝟘-or-ω {rs = rs} =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω′
    {𝕄₂ = ErasureModality rs}
    unit⇨erasure
    (Is-morphism→Is-Σ-morphism $
     Is-order-embedding.tr-morphism unit⇨erasure)
    (λ _ → refl)
    (λ _ → refl)

-- If the function erasure→unit preserves certain type restrictions,
-- then it also does this for certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

erasure→unit-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  Are-preserving-type-restrictions
    R₁ R₂ erasure→unit erasure→unit →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (ErasureModality rs) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω tt UnitModality R₂)
    erasure→unit erasure→unit
erasure→unit-preserves-second-ΠΣ-quantities-𝟘-or-ω r =
  record
    { Unit-preserved    = Unit-preserved
    ; Prodrec-preserved = Prodrec-preserved
    ; ΠΣ-preserved      = λ (b , _) →
        ΠΣ-preserved b , (λ _ → refl) , (λ _ → refl)
    }
  where
  open Are-preserving-type-restrictions r

-- The function erasure→unit does not reflect certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

¬-erasure→unit-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ¬ Are-reflecting-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω ω (ErasureModality rs) R₁)
      (second-ΠΣ-quantities-𝟘-or-ω tt
         UnitModality no-type-restrictions)
      erasure→unit erasure→unit
¬-erasure→unit-reflects-second-ΠΣ-quantities-𝟘-or-ω r =
  case
    ΠΣ-reflected {b = BMΠ} {p = 𝟘} {q = ω}
      (_ , (λ _ → refl) , (λ _ → refl))
  of
    λ (_ , eq , _) →
  case eq refl of λ ()
  where
  open Are-reflecting-type-restrictions r

-- If the function erasure→zero-one-many preserves certain type
-- restrictions, then the function preserves certain type restrictions
-- obtained using second-ΠΣ-quantities-𝟘-or-ω, given a certain
-- assumption.

erasure→zero-one-many-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Are-preserving-type-restrictions R₁ R₂
    erasure→zero-one-many erasure→zero-one-many →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (ErasureModality rs₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω (zero-one-many-greatest 𝟙≤𝟘 rs₂) R₂)
    erasure→zero-one-many erasure→zero-one-many
erasure→zero-one-many-preserves-second-ΠΣ-quantities-𝟘-or-ω eq =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω′
    m
    (Is-morphism→Is-Σ-morphism $ Is-order-embedding.tr-morphism m)
    (λ _ → refl)
    refl
  where
  m = erasure⇨zero-one-many eq

-- If the function erasure→zero-one-many reflects certain type
-- restrictions, then the function reflects certain type restrictions
-- obtained using second-ΠΣ-quantities-𝟘-or-ω, given a certain
-- assumption.

erasure→zero-one-many-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Are-reflecting-type-restrictions R₁ R₂
    erasure→zero-one-many erasure→zero-one-many →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (ErasureModality rs₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω (zero-one-many-greatest 𝟙≤𝟘 rs₂) R₂)
    erasure→zero-one-many erasure→zero-one-many
erasure→zero-one-many-reflects-second-ΠΣ-quantities-𝟘-or-ω eq =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω′
    m
    (Is-morphism→Is-Σ-morphism $ Is-order-embedding.tr-morphism m)
    (λ _ → refl)
    (λ where
       {p = ω} _ → refl)
  where
  m = erasure⇨zero-one-many eq

-- If the functions erasure→zero-one-many and erasure→zero-one-many-Σ
-- preserve certain type restrictions, then the functions preserve
-- certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω, given a certain assumption.

erasure→zero-one-many-Σ-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Are-preserving-type-restrictions R₁ R₂
    erasure→zero-one-many erasure→zero-one-many-Σ →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (ErasureModality rs₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω (zero-one-many-greatest 𝟙≤𝟘 rs₂) R₂)
    erasure→zero-one-many erasure→zero-one-many-Σ
erasure→zero-one-many-Σ-preserves-second-ΠΣ-quantities-𝟘-or-ω
 {rs₁ = rs₁} refl =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    {𝕄₁ = ErasureModality rs₁}
    (Is-order-embedding.tr-morphism $ erasure⇨zero-one-many refl)
    (Is-Σ-order-embedding.tr-Σ-morphism $ erasure⇨zero-one-many-Σ idᶠ)
    (λ _ →
         (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = ω} → (λ ()) , (λ ()))
       , (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = ω} → (λ ()) , (λ ())))
    refl

-- If the functions erasure→zero-one-many and erasure→zero-one-many-Σ
-- reflect certain type restrictions, then the functions reflect
-- certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω, given a certain assumption.

erasure→zero-one-many-Σ-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Are-reflecting-type-restrictions R₁ R₂
    erasure→zero-one-many erasure→zero-one-many-Σ →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (ErasureModality rs₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω (zero-one-many-greatest 𝟙≤𝟘 rs₂) R₂)
    erasure→zero-one-many erasure→zero-one-many-Σ
erasure→zero-one-many-Σ-reflects-second-ΠΣ-quantities-𝟘-or-ω
  {rs₁ = rs₁} refl =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    {𝕄₁ = ErasureModality rs₁}
    (Is-order-embedding.tr-morphism $ erasure⇨zero-one-many refl)
    (Is-Σ-order-embedding.tr-Σ-morphism $ erasure⇨zero-one-many-Σ idᶠ)
    (λ _ →
         (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = ω} → (λ ()) , (λ ()))
       , (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = ω} → (λ ()) , (λ ())))
    (λ where
       {p = ω} _ → refl)

-- If the function zero-one-many→erasure preserves certain type
-- restrictions, then the function also preserves certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω, given a
-- certain assumption.

zero-one-many→erasure-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Are-preserving-type-restrictions R₁ R₂
    zero-one-many→erasure zero-one-many→erasure →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (zero-one-many-greatest 𝟙≤𝟘 rs₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω (ErasureModality rs₂) R₂)
    zero-one-many→erasure zero-one-many→erasure
zero-one-many→erasure-preserves-second-ΠΣ-quantities-𝟘-or-ω eq =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    m
    (Is-morphism→Is-Σ-morphism m)
    (λ _ →
         (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙} → (λ ()) , (λ ())
            {p = ω} → (λ ()) , (λ ()))
       , (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙} → (λ ()) , (λ ())
            {p = ω} → (λ ()) , (λ ())))
    refl
  where
  m = zero-one-many⇨erasure eq

-- The function zero-one-many→erasure does not reflect certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

¬-zero-one-many→erasure-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ¬ Are-reflecting-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω ω (zero-one-many-greatest 𝟙≤𝟘 rs) R)
      (second-ΠΣ-quantities-𝟘-or-ω ω
         (ErasureModality (𝟘ᵐ-allowed-if ok)) no-type-restrictions)
      zero-one-many→erasure zero-one-many→erasure
¬-zero-one-many→erasure-reflects-second-ΠΣ-quantities-𝟘-or-ω r =
  case
    ΠΣ-reflected {b = BMΠ} {p = ω} {q = 𝟙}
      (_ , (λ ()) , (λ _ → refl))
  of
    λ (_ , _ , eq) →
  case eq (λ ()) of λ ()
  where
  open Are-reflecting-type-restrictions r

-- If the function linearity→linear-or-affine preserves certain type
-- restrictions, then the function preserves certain type restrictions
-- obtained using second-ΠΣ-quantities-𝟘-or-ω, given a certain
-- assumption.

linearity→linear-or-affine-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Are-preserving-type-restrictions R₁ R₂
    linearity→linear-or-affine linearity→linear-or-affine →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (linearityModality rs₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine rs₂) R₂)
    linearity→linear-or-affine linearity→linear-or-affine
linearity→linear-or-affine-preserves-second-ΠΣ-quantities-𝟘-or-ω eq =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω′
    m
    (Is-morphism→Is-Σ-morphism $ Is-order-embedding.tr-morphism m)
    (λ _ → refl)
    refl
  where
  m = linearity⇨linear-or-affine eq

-- If the function linearity→linear-or-affine reflects certain type
-- restrictions, then the function reflects certain type restrictions
-- obtained using second-ΠΣ-quantities-𝟘-or-ω, given a certain
-- assumption.

linearity→linear-or-affine-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Are-reflecting-type-restrictions R₁ R₂
    linearity→linear-or-affine linearity→linear-or-affine →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (linearityModality rs₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine rs₂) R₂)
    linearity→linear-or-affine linearity→linear-or-affine
linearity→linear-or-affine-reflects-second-ΠΣ-quantities-𝟘-or-ω eq =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω′
    m
    (Is-morphism→Is-Σ-morphism $ Is-order-embedding.tr-morphism m)
    (λ _ → refl)
    (λ where
       {p = ω} _ → refl)
  where
  m = linearity⇨linear-or-affine eq

-- If the function linear-or-affine→linearity preserves certain type
-- restrictions, then the function also preserves certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω, given a
-- certain assumption.

linear-or-affine→linearity-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Are-preserving-type-restrictions R₁ R₂
    linear-or-affine→linearity linear-or-affine→linearity →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine rs₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω (linearityModality rs₂) R₂)
    linear-or-affine→linearity linear-or-affine→linearity
linear-or-affine→linearity-preserves-second-ΠΣ-quantities-𝟘-or-ω eq =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    m
    (Is-morphism→Is-Σ-morphism m)
    (λ _ →
         (λ where
            {p = 𝟘}  → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙}  → (λ ()) , (λ ())
            {p = ≤𝟙} → (λ ()) , (λ ())
            {p = ≤ω} → (λ ()) , (λ ()))
       , (λ where
            {p = 𝟘}  → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙}  → (λ ()) , (λ ())
            {p = ≤𝟙} → (λ ()) , (λ ())
            {p = ≤ω} → (λ ()) , (λ ())))
    refl
  where
  m = linear-or-affine⇨linearity eq

-- The function linear-or-affine→linearity does not reflect certain
-- type restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

¬-linear-or-affine→linearity-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ¬ Are-reflecting-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine rs) R)
      (second-ΠΣ-quantities-𝟘-or-ω ω
         (linearityModality (𝟘ᵐ-allowed-if ok)) no-type-restrictions)
      linear-or-affine→linearity linear-or-affine→linearity
¬-linear-or-affine→linearity-reflects-second-ΠΣ-quantities-𝟘-or-ω r =
  case
    ΠΣ-reflected {b = BMΠ} {p = ≤ω} {q = ≤𝟙}
      (_ , (λ ()) , (λ _ → refl))
  of
    λ (_ , _ , eq) →
  case eq (λ ()) of λ ()
  where
  open Are-reflecting-type-restrictions r

-- If the function affine→linear-or-affine preserves certain type
-- restrictions, then the function preserves certain type restrictions
-- obtained using second-ΠΣ-quantities-𝟘-or-ω, given a certain
-- assumption.

affine→linear-or-affine-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Are-preserving-type-restrictions R₁ R₂
    affine→linear-or-affine affine→linear-or-affine →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality rs₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine rs₂) R₂)
    affine→linear-or-affine affine→linear-or-affine
affine→linear-or-affine-preserves-second-ΠΣ-quantities-𝟘-or-ω eq =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω′
    m
    (Is-morphism→Is-Σ-morphism $ Is-order-embedding.tr-morphism m)
    (λ _ → refl)
    refl
  where
  m = affine⇨linear-or-affine eq

-- If the function affine→linear-or-affine reflects certain type
-- restrictions, then the function reflects certain type restrictions
-- obtained using second-ΠΣ-quantities-𝟘-or-ω, given a certain
-- assumption.

affine→linear-or-affine-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Are-reflecting-type-restrictions R₁ R₂
    affine→linear-or-affine affine→linear-or-affine →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality rs₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine rs₂) R₂)
    affine→linear-or-affine affine→linear-or-affine
affine→linear-or-affine-reflects-second-ΠΣ-quantities-𝟘-or-ω eq =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω′
    m
    (Is-morphism→Is-Σ-morphism $ Is-order-embedding.tr-morphism m)
    (λ _ → refl)
    (λ where
       {p = ω} _ → refl)
  where
  m = affine⇨linear-or-affine eq

-- If the functions affine→linear-or-affine and
-- affine→linear-or-affine-Σ preserve certain type restrictions, then
-- the functions preserve certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω, given a certain assumption.

affine→linear-or-affine-Σ-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Are-preserving-type-restrictions R₁ R₂
    affine→linear-or-affine affine→linear-or-affine-Σ →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality rs₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine rs₂) R₂)
    affine→linear-or-affine affine→linear-or-affine-Σ
affine→linear-or-affine-Σ-preserves-second-ΠΣ-quantities-𝟘-or-ω
  {rs₁ = rs₁} refl =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    {𝕄₁ = affineModality rs₁}
    (Is-order-embedding.tr-morphism $ affine⇨linear-or-affine refl)
    (Is-Σ-order-embedding.tr-Σ-morphism $ affine⇨linear-or-affine-Σ idᶠ)
    (λ _ →
         (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙} → (λ ()) , (λ ())
            {p = ω} → (λ ()) , (λ ()))
       , (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙} → (λ ()) , (λ ())
            {p = ω} → (λ ()) , (λ ())))
    refl

-- If the functions affine→linear-or-affine and
-- affine→linear-or-affine-Σ reflect certain type restrictions, then
-- the functions reflect certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω, given a certain assumption.

affine→linear-or-affine-Σ-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Are-reflecting-type-restrictions R₁ R₂
    affine→linear-or-affine affine→linear-or-affine-Σ →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality rs₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine rs₂) R₂)
    affine→linear-or-affine affine→linear-or-affine-Σ
affine→linear-or-affine-Σ-reflects-second-ΠΣ-quantities-𝟘-or-ω
  {rs₁ = rs₁} refl =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    {𝕄₁ = affineModality rs₁}
    (Is-order-embedding.tr-morphism $ affine⇨linear-or-affine refl)
    (Is-Σ-order-embedding.tr-Σ-morphism $ affine⇨linear-or-affine-Σ idᶠ)
    (λ _ →
         (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙} → (λ ()) , (λ ())
            {p = ω} → (λ ()) , (λ ()))
       , (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙} → (λ ()) , (λ ())
            {p = ω} → (λ ()) , (λ ())))
    (λ where
       {p = ω} _ → refl)

-- If the function linear-or-affine→affine preserves certain type
-- restrictions, then the function also preserves certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω, given a
-- certain assumption.

linear-or-affine→affine-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Are-preserving-type-restrictions R₁ R₂
    linear-or-affine→affine linear-or-affine→affine →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine rs₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality rs₂) R₂)
    linear-or-affine→affine linear-or-affine→affine
linear-or-affine→affine-preserves-second-ΠΣ-quantities-𝟘-or-ω eq =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    m
    (Is-morphism→Is-Σ-morphism m)
    (λ _ →
         (λ where
            {p = 𝟘}  → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙}  → (λ ()) , (λ ())
            {p = ≤𝟙} → (λ ()) , (λ ())
            {p = ≤ω} → (λ ()) , (λ ()))
       , (λ where
            {p = 𝟘}  → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙}  → (λ ()) , (λ ())
            {p = ≤𝟙} → (λ ()) , (λ ())
            {p = ≤ω} → (λ ()) , (λ ())))
    refl
  where
  m = linear-or-affine⇨affine eq

-- If the function linear-or-affine→affine reflects certain type
-- restrictions, then the function also reflects certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω, given a
-- certain assumption.

linear-or-affine→affine-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Are-reflecting-type-restrictions R₁ R₂
    linear-or-affine→affine linear-or-affine→affine →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine rs₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality rs₂) R₂)
    linear-or-affine→affine linear-or-affine→affine
linear-or-affine→affine-reflects-second-ΠΣ-quantities-𝟘-or-ω eq =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    m
    (Is-morphism→Is-Σ-morphism m)
    (λ _ →
         (λ where
            {p = 𝟘}  → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙}  → (λ ()) , (λ ())
            {p = ≤𝟙} → (λ ()) , (λ ())
            {p = ≤ω} → (λ ()) , (λ ()))
       , (λ where
            {p = 𝟘}  → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙}  → (λ ()) , (λ ())
            {p = ≤𝟙} → (λ ()) , (λ ())
            {p = ≤ω} → (λ ()) , (λ ())))
    (λ where
       {p = ≤ω} _ → refl)
  where
  m = linear-or-affine⇨affine eq

-- If the function affine→linearity preserves certain type
-- restrictions, then the function preserves certain type restrictions
-- obtained using second-ΠΣ-quantities-𝟘-or-ω, given a certain
-- assumption.

affine→linearity-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Are-preserving-type-restrictions R₁ R₂
    affine→linearity affine→linearity →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality rs₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω (linearityModality rs₂) R₂)
    affine→linearity affine→linearity
affine→linearity-preserves-second-ΠΣ-quantities-𝟘-or-ω eq =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    m
    (Is-morphism→Is-Σ-morphism m)
    (λ _ →
         (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙} → (λ ()) , (λ ())
            {p = ω} → (λ ()) , (λ ()))
       , (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙} → (λ ()) , (λ ())
            {p = ω} → (λ ()) , (λ ())))
    refl
  where
  m = affine⇨linearity eq

-- The function affine→linearity does not reflect certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

¬-affine→linearity-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ¬ Are-reflecting-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality rs) R)
      (second-ΠΣ-quantities-𝟘-or-ω ω
         (linearityModality (𝟘ᵐ-allowed-if ok)) no-type-restrictions)
      affine→linearity affine→linearity
¬-affine→linearity-reflects-second-ΠΣ-quantities-𝟘-or-ω r =
  case
    ΠΣ-reflected {b = BMΠ} {p = ω} {q = 𝟙}
      (_ , (λ ()) , (λ _ → refl))
  of
    λ (_ , _ , eq) →
  case eq (λ ()) of λ ()
  where
  open Are-reflecting-type-restrictions r

-- If the functions affine→linearity and affine→linearity-Σ preserve
-- certain type restrictions, then the functions preserve certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω, given a
-- certain assumption.

affine→linearity-Σ-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Are-preserving-type-restrictions R₁ R₂
    affine→linearity affine→linearity-Σ →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality rs₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω (linearityModality rs₂) R₂)
    affine→linearity affine→linearity-Σ
affine→linearity-Σ-preserves-second-ΠΣ-quantities-𝟘-or-ω
  {rs₁ = rs₁} refl =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    {𝕄₁ = affineModality rs₁}
    (affine⇨linearity refl)
    (affine⇨linearity-Σ idᶠ)
    (λ _ →
         (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙} → (λ ()) , (λ ())
            {p = ω} → (λ ()) , (λ ()))
       , (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙} → (λ ()) , (λ ())
            {p = ω} → (λ ()) , (λ ())))
    refl

-- The functions affine→linearity and affine→linearity-Σ do not
-- reflect certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

¬-affine→linearity-Σ-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ¬ Are-reflecting-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality rs) R)
      (second-ΠΣ-quantities-𝟘-or-ω ω
         (linearityModality (𝟘ᵐ-allowed-if ok)) no-type-restrictions)
      affine→linearity affine→linearity-Σ
¬-affine→linearity-Σ-reflects-second-ΠΣ-quantities-𝟘-or-ω r =
  case
    ΠΣ-reflected {b = BMΠ} {p = ω} {q = 𝟙}
      (_ , (λ ()) , (λ _ → refl))
  of
    λ (_ , _ , eq) →
  case eq (λ ()) of λ ()
  where
  open Are-reflecting-type-restrictions r

-- If the function linearity→affine preserves certain type
-- restrictions, then the function also preserves certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω, given a
-- certain assumption.

linearity→affine-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Are-preserving-type-restrictions R₁ R₂
    linearity→affine linearity→affine →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (linearityModality rs₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality rs₂) R₂)
    linearity→affine linearity→affine
linearity→affine-preserves-second-ΠΣ-quantities-𝟘-or-ω eq =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    m
    (Is-morphism→Is-Σ-morphism m)
    (λ _ →
         (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙} → (λ ()) , (λ ())
            {p = ω} → (λ ()) , (λ ()))
       , (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙} → (λ ()) , (λ ())
            {p = ω} → (λ ()) , (λ ())))
    refl
  where
  m = linearity⇨affine eq

-- If the function linearity→affine reflects certain type
-- restrictions, then the function also reflects certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω, given a
-- certain assumption.

linearity→affine-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Are-reflecting-type-restrictions R₁ R₂
    linearity→affine linearity→affine →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (linearityModality rs₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality rs₂) R₂)
    linearity→affine linearity→affine
linearity→affine-reflects-second-ΠΣ-quantities-𝟘-or-ω eq =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    m
    (Is-morphism→Is-Σ-morphism m)
    (λ _ →
         (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙} → (λ ()) , (λ ())
            {p = ω} → (λ ()) , (λ ()))
       , (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙} → (λ ()) , (λ ())
            {p = ω} → (λ ()) , (λ ())))
    (λ where
       {p = ω} _ → refl)
  where
  m = linearity⇨affine eq

------------------------------------------------------------------------
-- Some lemmas related to no-erased-matches and concrete translation
-- functions

-- If the functions unit→erasure and tr preserve certain type
-- restrictions, then they also do this for certain type restrictions
-- obtained using no-erased-matches.

unit→erasure-preserves-no-erased-matches :
  Are-preserving-type-restrictions R₁ R₂ unit→erasure tr →
  Are-preserving-type-restrictions
    (no-erased-matches UnitModality R₁)
    (no-erased-matches (ErasureModality rs) R₂)
    unit→erasure tr
unit→erasure-preserves-no-erased-matches {rs = rs} =
  Are-preserving-type-restrictions-no-erased-matches
    UnitModality
    (ErasureModality rs)
    (λ _ → inj₂ (λ ()))

-- If the functions unit→erasure and tr reflect certain type
-- restrictions, then they also do this for certain type restrictions
-- obtained using no-erased-matches.

unit→erasure-reflects-no-erased-matches :
  Are-reflecting-type-restrictions R₁ R₂ unit→erasure tr →
  Are-reflecting-type-restrictions
    (no-erased-matches UnitModality R₁)
    (no-erased-matches (ErasureModality rs) R₂)
    unit→erasure tr
unit→erasure-reflects-no-erased-matches {rs = rs} =
  Are-reflecting-type-restrictions-no-erased-matches
    UnitModality
    (ErasureModality rs)
    (λ tt≢tt → ⊥-elim $ tt≢tt refl)

-- If the functions erasure→unit and tr preserve certain type
-- restrictions, then they also do this for certain type restrictions
-- obtained using no-erased-matches.

erasure→unit-preserves-no-erased-matches :
  Are-preserving-type-restrictions R₁ R₂ erasure→unit tr →
  Are-preserving-type-restrictions
    (no-erased-matches (ErasureModality rs) R₁)
    (no-erased-matches UnitModality R₂)
    erasure→unit tr
erasure→unit-preserves-no-erased-matches {rs = rs} =
  Are-preserving-type-restrictions-no-erased-matches
    (ErasureModality rs)
    UnitModality
    (λ tt≢tt → ⊥-elim $ tt≢tt refl)

-- The functions erasure→unit and tr do not reflect certain type
-- restrictions obtained using no-erased-matches.

¬-erasure→unit-reflects-no-erased-matches :
  ¬ Are-reflecting-type-restrictions
      (no-erased-matches (ErasureModality rs) R)
      (no-erased-matches UnitModality no-type-restrictions)
      erasure→unit tr
¬-erasure→unit-reflects-no-erased-matches r =
  Prodrec-reflected {r = 𝟘} {p = 𝟘} {q = 𝟘} (_ , idᶠ) .proj₂ (λ ()) refl
  where
  open Are-reflecting-type-restrictions r

-- If the functions erasure→zero-one-many and tr preserve certain type
-- restrictions, then they also do this for certain type restrictions
-- obtained using no-erased-matches.

erasure→zero-one-many-preserves-no-erased-matches :
  Are-preserving-type-restrictions R₁ R₂
    erasure→zero-one-many tr →
  Are-preserving-type-restrictions
    (no-erased-matches (ErasureModality rs₁) R₁)
    (no-erased-matches (zero-one-many-greatest 𝟙≤𝟘 rs₂) R₂)
    erasure→zero-one-many tr
erasure→zero-one-many-preserves-no-erased-matches
  {rs₁ = rs₁} {rs₂ = rs₂} =
  Are-preserving-type-restrictions-no-erased-matches
    (ErasureModality rs₁)
    (zero-one-many-greatest _ rs₂)
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions erasure→zero-one-many and tr reflect certain type
-- restrictions, then they also do this for certain type restrictions
-- obtained using no-erased-matches.

erasure→zero-one-many-reflects-no-erased-matches :
  Are-reflecting-type-restrictions R₁ R₂
    erasure→zero-one-many tr →
  Are-reflecting-type-restrictions
    (no-erased-matches (ErasureModality rs₁) R₁)
    (no-erased-matches (zero-one-many-greatest 𝟙≤𝟘 rs₂) R₂)
    erasure→zero-one-many tr
erasure→zero-one-many-reflects-no-erased-matches
  {rs₁ = rs₁} {rs₂ = rs₂} =
  Are-reflecting-type-restrictions-no-erased-matches
    (ErasureModality rs₁)
    (zero-one-many-greatest _ rs₂)
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))

-- If the functions zero-one-many→erasure and tr preserve certain type
-- restrictions, then they also do this for certain type restrictions
-- obtained using no-erased-matches.

zero-one-many→erasure-preserves-no-erased-matches :
  Are-preserving-type-restrictions R₁ R₂
    zero-one-many→erasure tr →
  Are-preserving-type-restrictions
    (no-erased-matches (zero-one-many-greatest 𝟙≤𝟘 rs₁) R₁)
    (no-erased-matches (ErasureModality rs₂) R₂)
    zero-one-many→erasure tr
zero-one-many→erasure-preserves-no-erased-matches
  {rs₁ = rs₁} {rs₂ = rs₂} =
  Are-preserving-type-restrictions-no-erased-matches
    (zero-one-many-greatest _ rs₁)
    (ErasureModality rs₂)
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions zero-one-many→erasure and tr reflect certain type
-- restrictions, then they also do this for certain type restrictions
-- obtained using no-erased-matches.

zero-one-many→erasure-reflects-no-erased-matches :
  Are-reflecting-type-restrictions R₁ R₂
    zero-one-many→erasure tr →
  Are-reflecting-type-restrictions
    (no-erased-matches (zero-one-many-greatest 𝟙≤𝟘 rs₁) R₁)
    (no-erased-matches (ErasureModality rs₂) R₂)
    zero-one-many→erasure tr
zero-one-many→erasure-reflects-no-erased-matches
  {rs₁ = rs₁} {rs₂ = rs₂} =
  Are-reflecting-type-restrictions-no-erased-matches
    (zero-one-many-greatest _ rs₁)
    (ErasureModality rs₂)
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))

-- If the functions linearity→linear-or-affine and tr preserve certain
-- type restrictions, then they also do this for certain type
-- restrictions obtained using no-erased-matches.

linearity→linear-or-affine-preserves-no-erased-matches :
  Are-preserving-type-restrictions R₁ R₂
    linearity→linear-or-affine tr →
  Are-preserving-type-restrictions
    (no-erased-matches (linearityModality rs₁) R₁)
    (no-erased-matches (linear-or-affine rs₂) R₂)
    linearity→linear-or-affine tr
linearity→linear-or-affine-preserves-no-erased-matches
  {rs₁ = rs₁} {rs₂ = rs₂} =
  Are-preserving-type-restrictions-no-erased-matches
    (linearityModality rs₁)
    (linear-or-affine rs₂)
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions linearity→linear-or-affine and tr reflect certain
-- type restrictions, then they also do this for certain type
-- restrictions obtained using no-erased-matches.

linearity→linear-or-affine-reflects-no-erased-matches :
  Are-reflecting-type-restrictions R₁ R₂
    linearity→linear-or-affine tr →
  Are-reflecting-type-restrictions
    (no-erased-matches (linearityModality rs₁) R₁)
    (no-erased-matches (linear-or-affine rs₂) R₂)
    linearity→linear-or-affine tr
linearity→linear-or-affine-reflects-no-erased-matches
  {rs₁ = rs₁} {rs₂ = rs₂} =
  Are-reflecting-type-restrictions-no-erased-matches
    (linearityModality rs₁)
    (linear-or-affine rs₂)
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))

-- If the functions linear-or-affine→linearity and tr preserve certain
-- type restrictions, then they also do this for certain type
-- restrictions obtained using no-erased-matches.

linear-or-affine→linearity-preserves-no-erased-matches :
  Are-preserving-type-restrictions R₁ R₂
    linear-or-affine→linearity tr →
  Are-preserving-type-restrictions
    (no-erased-matches (linear-or-affine rs₁) R₁)
    (no-erased-matches (linearityModality rs₂) R₂)
    linear-or-affine→linearity tr
linear-or-affine→linearity-preserves-no-erased-matches
  {rs₁ = rs₁} {rs₂ = rs₂} =
  Are-preserving-type-restrictions-no-erased-matches
    (linear-or-affine rs₁)
    (linearityModality rs₂)
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions linear-or-affine→linearity and tr reflect certain
-- type restrictions, then they also do this for certain type
-- restrictions obtained using no-erased-matches.

linear-or-affine→linearity-reflects-no-erased-matches :
  Are-reflecting-type-restrictions R₁ R₂
    linear-or-affine→linearity tr →
  Are-reflecting-type-restrictions
    (no-erased-matches (linear-or-affine rs₁) R₁)
    (no-erased-matches (linearityModality rs₂) R₂)
    linear-or-affine→linearity tr
linear-or-affine→linearity-reflects-no-erased-matches
  {rs₁ = rs₁} {rs₂ = rs₂} =
  Are-reflecting-type-restrictions-no-erased-matches
    (linear-or-affine rs₁)
    (linearityModality rs₂)
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))

-- If the functions affine→linear-or-affine and tr preserve certain
-- type restrictions, then they also do this for certain type
-- restrictions obtained using no-erased-matches.

affine→linear-or-affine-preserves-no-erased-matches :
  Are-preserving-type-restrictions R₁ R₂
    affine→linear-or-affine tr →
  Are-preserving-type-restrictions
    (no-erased-matches (affineModality rs₁) R₁)
    (no-erased-matches (linear-or-affine rs₂) R₂)
    affine→linear-or-affine tr
affine→linear-or-affine-preserves-no-erased-matches
  {rs₁ = rs₁} {rs₂ = rs₂} =
  Are-preserving-type-restrictions-no-erased-matches
    (affineModality rs₁)
    (linear-or-affine rs₂)
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions affine→linear-or-affine and tr reflect certain
-- type restrictions, then they also do this for certain type
-- restrictions obtained using no-erased-matches.

affine→linear-or-affine-reflects-no-erased-matches :
  Are-reflecting-type-restrictions R₁ R₂
    affine→linear-or-affine tr →
  Are-reflecting-type-restrictions
    (no-erased-matches (affineModality rs₁) R₁)
    (no-erased-matches (linear-or-affine rs₂) R₂)
    affine→linear-or-affine tr
affine→linear-or-affine-reflects-no-erased-matches
  {rs₁ = rs₁} {rs₂ = rs₂} =
  Are-reflecting-type-restrictions-no-erased-matches
    (affineModality rs₁)
    (linear-or-affine rs₂)
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))

-- If the functions linear-or-affine→affine and tr preserve certain
-- type restrictions, then they also do this for certain type
-- restrictions obtained using no-erased-matches.

linear-or-affine→affine-preserves-no-erased-matches :
  Are-preserving-type-restrictions R₁ R₂
    linear-or-affine→affine tr →
  Are-preserving-type-restrictions
    (no-erased-matches (linear-or-affine rs₁) R₁)
    (no-erased-matches (affineModality rs₂) R₂)
    linear-or-affine→affine tr
linear-or-affine→affine-preserves-no-erased-matches
  {rs₁ = rs₁} {rs₂ = rs₂} =
  Are-preserving-type-restrictions-no-erased-matches
    (linear-or-affine rs₁)
    (affineModality rs₂)
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions linear-or-affine→affine and tr reflect certain
-- type restrictions, then they also do this for certain type
-- restrictions obtained using no-erased-matches.

linear-or-affine→affine-reflects-no-erased-matches :
  Are-reflecting-type-restrictions R₁ R₂
    linear-or-affine→affine tr →
  Are-reflecting-type-restrictions
    (no-erased-matches (linear-or-affine rs₁) R₁)
    (no-erased-matches (affineModality rs₂) R₂)
    linear-or-affine→affine tr
linear-or-affine→affine-reflects-no-erased-matches
  {rs₁ = rs₁} {rs₂ = rs₂} =
  Are-reflecting-type-restrictions-no-erased-matches
    (linear-or-affine rs₁)
    (affineModality rs₂)
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))

-- If the functions affine→linearity and tr preserve certain type
-- restrictions, then they also do this for certain type restrictions
-- obtained using no-erased-matches.

affine→linearity-preserves-no-erased-matches :
  Are-preserving-type-restrictions R₁ R₂
    affine→linearity tr →
  Are-preserving-type-restrictions
    (no-erased-matches (affineModality rs₁) R₁)
    (no-erased-matches (linearityModality rs₂) R₂)
    affine→linearity tr
affine→linearity-preserves-no-erased-matches {rs₁ = rs₁} {rs₂ = rs₂} =
  Are-preserving-type-restrictions-no-erased-matches
    (affineModality rs₁)
    (linearityModality rs₂)
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions affine→linearity and tr reflect certain type
-- restrictions, then they also do this for certain type restrictions
-- obtained using no-erased-matches.

affine→linearity-reflects-no-erased-matches :
  Are-reflecting-type-restrictions R₁ R₂
    affine→linearity tr →
  Are-reflecting-type-restrictions
    (no-erased-matches (affineModality rs₁) R₁)
    (no-erased-matches (linearityModality rs₂) R₂)
    affine→linearity tr
affine→linearity-reflects-no-erased-matches {rs₁ = rs₁} {rs₂ = rs₂} =
  Are-reflecting-type-restrictions-no-erased-matches
    (affineModality rs₁)
    (linearityModality rs₂)
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))

-- If the functions linearity→affine and tr preserve certain type
-- restrictions, then they also do this for certain type restrictions
-- obtained using no-erased-matches.

linearity→affine-preserves-no-erased-matches :
  Are-preserving-type-restrictions R₁ R₂
    linearity→affine tr →
  Are-preserving-type-restrictions
    (no-erased-matches (linearityModality rs₁) R₁)
    (no-erased-matches (affineModality rs₂) R₂)
    linearity→affine tr
linearity→affine-preserves-no-erased-matches {rs₁ = rs₁} {rs₂ = rs₂} =
  Are-preserving-type-restrictions-no-erased-matches
    (linearityModality rs₁)
    (affineModality rs₂)
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions linearity→affine and tr reflect certain type
-- restrictions, then they also do this for certain type restrictions
-- obtained using no-erased-matches.

linearity→affine-reflects-no-erased-matches :
  Are-reflecting-type-restrictions R₁ R₂
    linearity→affine tr →
  Are-reflecting-type-restrictions
    (no-erased-matches (linearityModality rs₁) R₁)
    (no-erased-matches (affineModality rs₂) R₂)
    linearity→affine tr
linearity→affine-reflects-no-erased-matches {rs₁ = rs₁} {rs₂ = rs₂} =
  Are-reflecting-type-restrictions-no-erased-matches
    (linearityModality rs₁)
    (affineModality rs₂)
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))
