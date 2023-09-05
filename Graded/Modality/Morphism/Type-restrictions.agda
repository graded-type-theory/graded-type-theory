------------------------------------------------------------------------
-- Preserving/reflecting type restrictions
------------------------------------------------------------------------

module Graded.Modality.Morphism.Type-restrictions where

open import Tools.Bool
open import Tools.Function
open import Tools.Level
open import Tools.Nullary
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PropositionalEquality
open import Tools.Sum using (inj₁; inj₂)
open import Tools.Unit

open import Graded.Modality
open import Graded.Modality.Instances.Affine
  using (affineModality)
open import Graded.Modality.Instances.Erasure
  using (𝟘; ω)
open import Graded.Modality.Instances.Erasure.Modality
  using (ErasureModality)
open import Graded.Modality.Instances.Linear-or-affine
  using (𝟘; 𝟙; ≤𝟙; ≤ω; linear-or-affine)
open import Graded.Modality.Instances.Linearity
  using (linearityModality)
open import Graded.Modality.Instances.Unit using (UnitModality)
open import Graded.Modality.Instances.Zero-one-many
  using (𝟘; 𝟙; ω; zero-one-many-modality)
open import Graded.Modality.Morphism
import Graded.Modality.Properties
open import Graded.Restrictions

open import Graded.Mode as Mode hiding (module Mode)
open import Graded.Modality.Variant

open Modality-variant

open import Definition.Typed.Restrictions

open import Definition.Untyped.NotParametrised
open import Definition.Untyped.QuantityTranslation

private variable
  𝟙≤𝟘 ok                      : Bool
  R R₁ R₂ R₃                  : Type-restrictions _
  b                           : BinderMode
  M M₁ M₂                     : Set _
  𝕄₁ 𝕄₂                       : Modality _
  tr tr₁ tr₂ tr-Σ tr-Σ₁ tr-Σ₂ : M₁ → M₂
  p q                         : M

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
    -- If R₁.Unit-allowed holds, then R₂.Unit-allowed holds.
    Unit-preserved :
      R₁.Unit-allowed → R₂.Unit-allowed

    -- The functions tr and tr-Σ preserve the ΠΣ-allowed property in a
    -- certain way.
    ΠΣ-preserved :
      R₁.ΠΣ-allowed b p q →
      R₂.ΠΣ-allowed b (tr-BinderMode tr tr-Σ b p) (tr q)

-- The property of reflecting Type-restrictions.

record Are-reflecting-type-restrictions
         {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
         (R₁ : Type-restrictions M₁) (R₂ : Type-restrictions M₂)
         (tr tr-Σ : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  private
    module R₁ = Type-restrictions R₁
    module R₂ = Type-restrictions R₂

  field
    -- If R₂.Unit-allowed holds, then R₁.Unit-allowed holds.
    Unit-reflected :
      R₂.Unit-allowed → R₁.Unit-allowed

    -- The functions tr and tr-Σ reflect the ΠΣ-allowed property in a
    -- certain way.
    ΠΣ-reflected :
      R₂.ΠΣ-allowed b (tr-BinderMode tr tr-Σ b p) (tr q) →
      R₁.ΠΣ-allowed b p q

------------------------------------------------------------------------
-- Identity

-- For every value R of type Type-restrictions the identity function
-- preserves Type-restrictions for R and R.

Are-preserving-type-restrictions-id :
  Are-preserving-type-restrictions R R idᶠ idᶠ
Are-preserving-type-restrictions-id {R = R} = λ where
    .Unit-preserved           → idᶠ
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
    { Unit-preserved = R.Unit-preserved
    ; ΠΣ-preserved   = λ {b = b} → λ where
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
  { Unit-reflected = Unit-reflected
  ; ΠΣ-reflected   =
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
  { Unit-preserved = Unit-preserved
  ; ΠΣ-preserved   = λ where
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
  { Unit-reflected = Unit-reflected
  ; ΠΣ-reflected   = λ (b , eq) → ΠΣ-reflected b , tr-𝟘 eq
  }
  where
  open Are-reflecting-type-restrictions r

-- If the functions tr and tr-Σ preserve certain type restrictions,
-- then they also do this for certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω, given that certain assumptions hold.

Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ {ω₁ ω₂}
  (𝕄₁ : Modality M₁)
  (𝕄₂ : Modality M₂) →
  (Modality.𝟙 𝕄₁ ≢ Modality.𝟘 𝕄₁ →
   tr (Modality.𝟘 𝕄₁) ≡ Modality.𝟘 𝕄₂) →
  (∀ {p} → tr p ≡ ω₂ ⇔ p ≡ ω₁) →
  (∀ {p} → tr-Σ p ≡ ω₂ ⇔ p ≡ ω₁) →
  Are-preserving-type-restrictions R₁ R₂ tr tr-Σ →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω₁ 𝕄₁ R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω₂ 𝕄₂ R₂)
    tr tr-Σ
Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
  {tr = tr} {tr-Σ = tr-Σ} {ω₁ = ω₁} {ω₂ = ω₂}
  𝕄₁ 𝕄₂ tr-𝟘 tr-ω tr-Σ-ω r = record
  { Unit-preserved = Unit-preserved
  ; ΠΣ-preserved   = λ {b = b} (bn , is-𝟘 , not-𝟘) →
      ΠΣ-preserved bn , lemma₁ b is-𝟘 , lemma₃ b not-𝟘
  }
  where
  module M₁ = Modality 𝕄₁
  module M₂ = Modality 𝕄₂
  open Are-preserving-type-restrictions r
  open Graded.Modality.Properties 𝕄₁

  lemma₁ :
    ∀ {p q} b →
    (p ≡ ω₁ → q ≡ ω₁) →
    tr-BinderMode tr tr-Σ b p ≡ ω₂ → tr q ≡ ω₂
  lemma₁ {p = p} {q = q} BMΠ hyp =
    tr p ≡ ω₂  →⟨ tr-ω .proj₁ ⟩
    p ≡ ω₁     →⟨ hyp ⟩
    q ≡ ω₁     →⟨ tr-ω .proj₂ ⟩
    tr q ≡ ω₂  □
  lemma₁ {p = p} {q = q} (BMΣ _) hyp =
    tr-Σ p ≡ ω₂  →⟨ tr-Σ-ω .proj₁ ⟩
    p ≡ ω₁       →⟨ hyp ⟩
    q ≡ ω₁       →⟨ tr-ω .proj₂ ⟩
    tr q ≡ ω₂    □

  lemma₂ :
    ∀ {p q} →
    (p ≢ ω₁ → q ≡ M₁.𝟘) →
    p ≢ ω₁ → tr q ≡ M₂.𝟘
  lemma₂ {p = p} {q = q} hyp p≢ω₁ =
    case hyp p≢ω₁ of λ {
      refl →
    tr-𝟘 (≢→𝟙≢𝟘 p≢ω₁) }

  lemma₃ :
    ∀ {p q} b →
    (p ≢ ω₁ → q ≡ M₁.𝟘) →
    tr-BinderMode tr tr-Σ b p ≢ ω₂ → tr q ≡ M₂.𝟘
  lemma₃ {p = p} {q = q} BMΠ hyp =
    tr p ≢ ω₂    →⟨ _∘→ tr-ω .proj₂ ⟩
    p ≢ ω₁       →⟨ lemma₂ hyp ⟩
    tr q ≡ M₂.𝟘  □
  lemma₃ {p = p} {q = q} (BMΣ _) hyp =
    tr-Σ p ≢ ω₂  →⟨ _∘→ tr-Σ-ω .proj₂ ⟩
    p ≢ ω₁       →⟨ lemma₂ hyp ⟩
    tr q ≡ M₂.𝟘  □

-- If the functions tr and tr-Σ reflect certain type restrictions,
-- then they also do this for certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω, given that certain assumptions hold.

Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ {ω₁ ω₂}
  (𝕄₁ : Modality M₁)
  (𝕄₂ : Modality M₂) →
  (∀ {p} → tr p ≡ Modality.𝟘 𝕄₂ → p ≡ Modality.𝟘 𝕄₁) →
  (∀ {p} → tr p ≡ ω₂ ⇔ p ≡ ω₁) →
  (∀ {p} → tr-Σ p ≡ ω₂ ⇔ p ≡ ω₁) →
  Are-reflecting-type-restrictions R₁ R₂ tr tr-Σ →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω₁ 𝕄₁ R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω₂ 𝕄₂ R₂)
    tr tr-Σ
Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
  {tr = tr} {tr-Σ = tr-Σ} {ω₁ = ω₁} {ω₂ = ω₂}
  𝕄₁ 𝕄₂ tr-𝟘 tr-ω tr-Σ-ω r = record
  { Unit-reflected = Unit-reflected
  ; ΠΣ-reflected   = λ {b = b} (bn , is-𝟘 , not-𝟘) →
      ΠΣ-reflected bn , lemma₁ b is-𝟘 , lemma₂ b not-𝟘
  }
  where
  module M₁ = Modality 𝕄₁
  module M₂ = Modality 𝕄₂
  open Are-reflecting-type-restrictions r

  lemma₁ :
    ∀ {p q} b →
    (tr-BinderMode tr tr-Σ b p ≡ ω₂ → tr q ≡ ω₂) →
    p ≡ ω₁ → q ≡ ω₁
  lemma₁ {p = p} {q = q} BMΠ hyp =
    p ≡ ω₁     →⟨ tr-ω .proj₂ ⟩
    tr p ≡ ω₂  →⟨ hyp ⟩
    tr q ≡ ω₂  →⟨ tr-ω .proj₁ ⟩
    q ≡ ω₁     □
  lemma₁ {p = p} {q = q} (BMΣ _) hyp =
    p ≡ ω₁       →⟨ tr-Σ-ω .proj₂ ⟩
    tr-Σ p ≡ ω₂  →⟨ hyp ⟩
    tr q ≡ ω₂    →⟨ tr-ω .proj₁ ⟩
    q ≡ ω₁       □

  lemma₂ :
    ∀ {p q} b →
    (tr-BinderMode tr tr-Σ b p ≢ ω₂ → tr q ≡ M₂.𝟘) →
    p ≢ ω₁ → q ≡ M₁.𝟘
  lemma₂ {p = p} {q = q} BMΠ hyp =
    p ≢ ω₁       →⟨ _∘→ tr-ω .proj₁ ⟩
    tr p ≢ ω₂    →⟨ hyp ⟩
    tr q ≡ M₂.𝟘  →⟨ tr-𝟘 ⟩
    q ≡ M₁.𝟘     □
  lemma₂ {p = p} {q = q} (BMΣ _) hyp =
    p ≢ ω₁       →⟨ _∘→ tr-Σ-ω .proj₁ ⟩
    tr-Σ p ≢ ω₂  →⟨ hyp ⟩
    tr q ≡ M₂.𝟘  →⟨ tr-𝟘 ⟩
    q ≡ M₁.𝟘     □

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
  ∀ v₁ v₁-ok v₂ →
  Are-preserving-type-restrictions
    R₁ R₂ unit→erasure unit→erasure →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω tt (UnitModality v₁ v₁-ok) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω (ErasureModality v₂) R₂)
    unit→erasure unit→erasure
unit→erasure-preserves-second-ΠΣ-quantities-𝟘-or-ω v₁ v₁-ok v₂ =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    (UnitModality v₁ v₁-ok)
    (ErasureModality v₂)
    (λ tt≢tt → ⊥-elim (tt≢tt refl))
    ((λ _ → refl) , (λ _ → refl))
    ((λ _ → refl) , (λ _ → refl))

-- If the function unit→erasure reflects certain type restrictions,
-- then it also does this for certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

unit→erasure-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₁-ok v₂ →
  Are-reflecting-type-restrictions
    R₁ R₂ unit→erasure unit→erasure →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω tt (UnitModality v₁ v₁-ok) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω (ErasureModality v₂) R₂)
    unit→erasure unit→erasure
unit→erasure-reflects-second-ΠΣ-quantities-𝟘-or-ω v₁ v₁-ok v₂ =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    (UnitModality v₁ v₁-ok)
    (ErasureModality v₂)
    (λ ())
    ((λ _ → refl) , (λ _ → refl))
    ((λ _ → refl) , (λ _ → refl))

-- If the function erasure→unit preserves certain type restrictions,
-- then it also does this for certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

erasure→unit-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ v₂-ok →
  Are-preserving-type-restrictions
    R₁ R₂ erasure→unit erasure→unit →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (ErasureModality v₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω tt (UnitModality v₂ v₂-ok) R₂)
    erasure→unit erasure→unit
erasure→unit-preserves-second-ΠΣ-quantities-𝟘-or-ω _ _ _ r =
  record
    { Unit-preserved = Unit-preserved
    ; ΠΣ-preserved   = λ (b , _) →
        ΠΣ-preserved b , (λ _ → refl) , (λ _ → refl)
    }
  where
  open Are-preserving-type-restrictions r

-- The function erasure→unit does not reflect certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

¬-erasure→unit-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ v₂-ok →
  ¬ Are-reflecting-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω ω (ErasureModality v₁) R₁)
      (second-ΠΣ-quantities-𝟘-or-ω tt
         (UnitModality v₂ v₂-ok) no-type-restrictions)
      erasure→unit erasure→unit
¬-erasure→unit-reflects-second-ΠΣ-quantities-𝟘-or-ω _ _ _ r =
  case
    ΠΣ-reflected {b = BMΠ} {p = 𝟘} {q = ω}
      (_ , (λ _ → refl) , (λ _ → refl))
  of
    λ (_ , _ , eq) →
  case eq (λ ()) of λ ()
  where
  open Are-reflecting-type-restrictions r

-- If the function erasure→zero-one-many preserves certain type
-- restrictions, then the function preserves certain type restrictions
-- obtained using second-ΠΣ-quantities-𝟘-or-ω.

erasure→zero-one-many-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ v₂-ok →
  Are-preserving-type-restrictions R₁ R₂
    erasure→zero-one-many erasure→zero-one-many →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (ErasureModality v₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω
       (zero-one-many-modality 𝟙≤𝟘 v₂ v₂-ok) R₂)
    erasure→zero-one-many erasure→zero-one-many
erasure→zero-one-many-preserves-second-ΠΣ-quantities-𝟘-or-ω
  v₁ v₂ v₂-ok =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    (ErasureModality v₁)
    (zero-one-many-modality _ v₂ v₂-ok)
    (λ _ → refl)
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

-- If the function erasure→zero-one-many reflects certain type
-- restrictions, then the function reflects certain type restrictions
-- obtained using second-ΠΣ-quantities-𝟘-or-ω.

erasure→zero-one-many-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ v₂-ok →
  Are-reflecting-type-restrictions R₁ R₂
    erasure→zero-one-many erasure→zero-one-many →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (ErasureModality v₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω
       (zero-one-many-modality 𝟙≤𝟘 v₂ v₂-ok) R₂)
    erasure→zero-one-many erasure→zero-one-many
erasure→zero-one-many-reflects-second-ΠΣ-quantities-𝟘-or-ω v₁ v₂ v₂-ok =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    (ErasureModality v₁)
    (zero-one-many-modality _ v₂ v₂-ok)
    (λ where
       {p = 𝟘} _  → refl
       {p = ω} ())
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

-- The functions erasure→zero-one-many and erasure→zero-one-many-Σ do
-- not preserve certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

¬-erasure→zero-one-many-Σ-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ v₂-ok →
  ¬ Are-preserving-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω ω
         (ErasureModality v₁) no-type-restrictions)
      (second-ΠΣ-quantities-𝟘-or-ω ω
         (zero-one-many-modality 𝟙≤𝟘 v₂ v₂-ok) R₂)
      erasure→zero-one-many erasure→zero-one-many-Σ
¬-erasure→zero-one-many-Σ-preserves-second-ΠΣ-quantities-𝟘-or-ω
  _ _ _ r =
  case
    ΠΣ-preserved {b = BMΣ Σₚ} {p = ω} {q = ω}
      (_ , (λ _ → refl) , ⊥-elim ∘→ (_$ refl))
      .proj₂ .proj₂ (λ ())
  of λ ()
  where
  open Are-preserving-type-restrictions r

-- The functions erasure→zero-one-many and erasure→zero-one-many-Σ do
-- not reflect certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

¬-erasure→zero-one-many-Σ-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ v₂-ok →
  ¬ Are-reflecting-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω ω (ErasureModality v₁) R₁)
      (second-ΠΣ-quantities-𝟘-or-ω ω
         (zero-one-many-modality 𝟙≤𝟘 v₂ v₂-ok) no-type-restrictions)
      erasure→zero-one-many erasure→zero-one-many-Σ
¬-erasure→zero-one-many-Σ-reflects-second-ΠΣ-quantities-𝟘-or-ω _ _ _ r =
  case
    ΠΣ-reflected {b = BMΣ Σₚ} {p = ω} {q = 𝟘}
      (_ , (λ ()) , (λ _ → refl))
      .proj₂ .proj₁ refl
  of λ ()
  where
  open Are-reflecting-type-restrictions r

-- The function zero-one-many→erasure does not preserve certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

¬-zero-one-many→erasure-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₁-ok v₂ →
  ¬ Are-preserving-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω ω
         (zero-one-many-modality 𝟙≤𝟘 v₁ v₁-ok) no-type-restrictions)
      (second-ΠΣ-quantities-𝟘-or-ω ω (ErasureModality v₂) R₂)
      zero-one-many→erasure zero-one-many→erasure
¬-zero-one-many→erasure-preserves-second-ΠΣ-quantities-𝟘-or-ω _ _ _ r =
  case
    ΠΣ-preserved {b = BMΠ} {p = 𝟙} {q = 𝟘}
      (_ , (λ ()) , (λ _ → refl))
      .proj₂ .proj₁ refl
  of λ ()
  where
  open Are-preserving-type-restrictions r

-- The function zero-one-many→erasure does not reflect certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

¬-zero-one-many→erasure-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₁-ok v₂ →
  ¬ Are-reflecting-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω ω
         (zero-one-many-modality 𝟙≤𝟘 v₁ v₁-ok) R)
      (second-ΠΣ-quantities-𝟘-or-ω ω
         (ErasureModality v₂) no-type-restrictions)
      zero-one-many→erasure zero-one-many→erasure
¬-zero-one-many→erasure-reflects-second-ΠΣ-quantities-𝟘-or-ω _ _ _ r =
  case
    ΠΣ-reflected {b = BMΠ} {p = ω} {q = 𝟙}
      (_ , (λ _ → refl) , ⊥-elim ∘→ (_$ refl))
  of
    λ (_ , eq , _) →
  case eq refl of λ ()
  where
  open Are-reflecting-type-restrictions r

-- If the function linearity→linear-or-affine preserves certain type
-- restrictions, then the function preserves certain type restrictions
-- obtained using second-ΠΣ-quantities-𝟘-or-ω.

linearity→linear-or-affine-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₁-ok v₂ v₂-ok →
  Are-preserving-type-restrictions R₁ R₂
    linearity→linear-or-affine linearity→linear-or-affine →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (linearityModality v₁ v₁-ok) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine v₂ v₂-ok) R₂)
    linearity→linear-or-affine linearity→linear-or-affine
linearity→linear-or-affine-preserves-second-ΠΣ-quantities-𝟘-or-ω
  v₁ v₁-ok v₂ v₂-ok =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    (linearityModality v₁ v₁-ok)
    (linear-or-affine v₂ v₂-ok)
    (λ _ → refl)
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

-- If the function linearity→linear-or-affine reflects certain type
-- restrictions, then the function reflects certain type restrictions
-- obtained using second-ΠΣ-quantities-𝟘-or-ω.

linearity→linear-or-affine-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₁-ok v₂ v₂-ok →
  Are-reflecting-type-restrictions R₁ R₂
    linearity→linear-or-affine linearity→linear-or-affine →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (linearityModality v₁ v₁-ok) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine v₂ v₂-ok) R₂)
    linearity→linear-or-affine linearity→linear-or-affine
linearity→linear-or-affine-reflects-second-ΠΣ-quantities-𝟘-or-ω
  v₁ v₁-ok v₂ v₂-ok =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    (linearityModality v₁ v₁-ok)
    (linear-or-affine v₂ v₂-ok)
    (λ where
       {p = 𝟘} _  → refl
       {p = 𝟙} ()
       {p = ω} ())
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

-- The function linear-or-affine→linearity does not preserve certain
-- type restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

¬-linear-or-affine→linearity-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₁-ok v₂ v₂-ok →
  ¬ Are-preserving-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine v₁ v₁-ok)
         no-type-restrictions)
      (second-ΠΣ-quantities-𝟘-or-ω ω (linearityModality v₂ v₂-ok) R₂)
      linear-or-affine→linearity linear-or-affine→linearity
¬-linear-or-affine→linearity-preserves-second-ΠΣ-quantities-𝟘-or-ω
  _ _ _ _ r =
  case
    ΠΣ-preserved {b = BMΠ} {p = ≤𝟙} {q = 𝟘}
      (_ , (λ ()) , (λ _ → refl))
      .proj₂ .proj₁ refl
  of λ ()
  where
  open Are-preserving-type-restrictions r

-- The function linear-or-affine→linearity does not reflect certain
-- type restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

¬-linear-or-affine→linearity-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₁-ok v₂ v₂-ok →
  ¬ Are-reflecting-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine v₁ v₁-ok) R)
      (second-ΠΣ-quantities-𝟘-or-ω ω
         (linearityModality v₂ v₂-ok) no-type-restrictions)
      linear-or-affine→linearity linear-or-affine→linearity
¬-linear-or-affine→linearity-reflects-second-ΠΣ-quantities-𝟘-or-ω
  _ _ _ _ r =
  case
    ΠΣ-reflected {b = BMΠ} {p = ≤ω} {q = ≤𝟙}
      (_ , (λ _ → refl) , ⊥-elim ∘→ (_$ refl))
  of
    λ (_ , eq , _) →
  case eq refl of λ ()
  where
  open Are-reflecting-type-restrictions r

-- If the function affine→linear-or-affine preserves certain type
-- restrictions, then the function preserves certain type restrictions
-- obtained using second-ΠΣ-quantities-𝟘-or-ω.

affine→linear-or-affine-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ v₂-ok →
  Are-preserving-type-restrictions R₁ R₂
    affine→linear-or-affine affine→linear-or-affine →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality v₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine v₂ v₂-ok) R₂)
    affine→linear-or-affine affine→linear-or-affine
affine→linear-or-affine-preserves-second-ΠΣ-quantities-𝟘-or-ω
  v₁ v₂ v₂-ok =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    (affineModality v₁)
    (linear-or-affine v₂ v₂-ok)
    (λ _ → refl)
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

-- If the function affine→linear-or-affine reflects certain type
-- restrictions, then the function reflects certain type restrictions
-- obtained using second-ΠΣ-quantities-𝟘-or-ω.

affine→linear-or-affine-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ v₂-ok →
  Are-reflecting-type-restrictions R₁ R₂
    affine→linear-or-affine affine→linear-or-affine →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality v₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine v₂ v₂-ok) R₂)
    affine→linear-or-affine affine→linear-or-affine
affine→linear-or-affine-reflects-second-ΠΣ-quantities-𝟘-or-ω
  v₁ v₂ v₂-ok =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    (affineModality v₁)
    (linear-or-affine v₂ v₂-ok)
    (λ where
       {p = 𝟘} _  → refl
       {p = 𝟙} ()
       {p = ω} ())
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

-- If the functions affine→linear-or-affine and
-- affine→linear-or-affine-Σ preserve certain type restrictions, then
-- the functions preserve certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

affine→linear-or-affine-Σ-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ v₂-ok →
  Are-preserving-type-restrictions R₁ R₂
    affine→linear-or-affine affine→linear-or-affine-Σ →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality v₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine v₂ v₂-ok) R₂)
    affine→linear-or-affine affine→linear-or-affine-Σ
affine→linear-or-affine-Σ-preserves-second-ΠΣ-quantities-𝟘-or-ω
  v₁ v₂ v₂-ok =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    (affineModality v₁)
    (linear-or-affine v₂ v₂-ok)
    (λ _ → refl)
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

-- If the functions affine→linear-or-affine and
-- affine→linear-or-affine-Σ reflect certain type restrictions, then
-- the functions reflect certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

affine→linear-or-affine-Σ-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ v₂-ok →
  Are-reflecting-type-restrictions R₁ R₂
    affine→linear-or-affine affine→linear-or-affine-Σ →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality v₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine v₂ v₂-ok) R₂)
    affine→linear-or-affine affine→linear-or-affine-Σ
affine→linear-or-affine-Σ-reflects-second-ΠΣ-quantities-𝟘-or-ω
  v₁ v₂ v₂-ok =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    (affineModality v₁)
    (linear-or-affine v₂ v₂-ok)
    (λ where
       {p = 𝟘} _  → refl
       {p = 𝟙} ()
       {p = ω} ())
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

-- If the function linear-or-affine→affine preserves certain type
-- restrictions, then the function also preserves certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

linear-or-affine→affine-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₁-ok v₂ →
  Are-preserving-type-restrictions R₁ R₂
    linear-or-affine→affine linear-or-affine→affine →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine v₁ v₁-ok) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality v₂) R₂)
    linear-or-affine→affine linear-or-affine→affine
linear-or-affine→affine-preserves-second-ΠΣ-quantities-𝟘-or-ω
  v₁ v₁-ok v₂ =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    (linear-or-affine v₁ v₁-ok)
    (affineModality v₂)
    (λ _ → refl)
    (λ where
       {p = 𝟘}  → (λ ()) , (λ ())
       {p = 𝟙}  → (λ ()) , (λ ())
       {p = ≤𝟙} → (λ ()) , (λ ())
       {p = ≤ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘}  → (λ ()) , (λ ())
       {p = 𝟙}  → (λ ()) , (λ ())
       {p = ≤𝟙} → (λ ()) , (λ ())
       {p = ≤ω} → (λ _ → refl) , (λ _ → refl))

-- If the function linear-or-affine→affine reflects certain type
-- restrictions, then the function also reflects certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

linear-or-affine→affine-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₁-ok v₂ →
  Are-reflecting-type-restrictions R₁ R₂
    linear-or-affine→affine linear-or-affine→affine →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine v₁ v₁-ok) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality v₂) R₂)
    linear-or-affine→affine linear-or-affine→affine
linear-or-affine→affine-reflects-second-ΠΣ-quantities-𝟘-or-ω
  v₁ v₁-ok v₂ =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    (linear-or-affine v₁ v₁-ok)
    (affineModality v₂)
    (λ where
       {p = 𝟘}  _  → refl
       {p = 𝟙}  ()
       {p = ≤𝟙} ()
       {p = ≤ω} ())
    (λ where
       {p = 𝟘}  → (λ ()) , (λ ())
       {p = 𝟙}  → (λ ()) , (λ ())
       {p = ≤𝟙} → (λ ()) , (λ ())
       {p = ≤ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘}  → (λ ()) , (λ ())
       {p = 𝟙}  → (λ ()) , (λ ())
       {p = ≤𝟙} → (λ ()) , (λ ())
       {p = ≤ω} → (λ _ → refl) , (λ _ → refl))

-- The function affine→linearity does not preserve certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

¬-affine→linearity-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ v₂-ok →
  ¬ Are-preserving-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality v₁)
         no-type-restrictions)
      (second-ΠΣ-quantities-𝟘-or-ω ω (linearityModality v₂ v₂-ok) R₂)
      affine→linearity affine→linearity
¬-affine→linearity-preserves-second-ΠΣ-quantities-𝟘-or-ω _ _ _ r =
  case
    ΠΣ-preserved {b = BMΠ} {p = 𝟙} {q = 𝟘}
      (_ , (λ ()) , (λ _ → refl))
      .proj₂ .proj₁ refl
  of λ ()
  where
  open Are-preserving-type-restrictions r

-- The function affine→linearity does not reflect certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

¬-affine→linearity-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ v₂-ok →
  ¬ Are-reflecting-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality v₁) R)
      (second-ΠΣ-quantities-𝟘-or-ω ω
         (linearityModality v₂ v₂-ok) no-type-restrictions)
      affine→linearity affine→linearity
¬-affine→linearity-reflects-second-ΠΣ-quantities-𝟘-or-ω _ _ _ r =
  case
    ΠΣ-reflected {b = BMΠ} {p = ω} {q = 𝟙}
      (_ , (λ _ → refl) , ⊥-elim ∘→ (_$ refl))
  of
    λ (_ , eq , _) →
  case eq refl of λ ()
  where
  open Are-reflecting-type-restrictions r

-- The functions affine→linearity and affine→linearity-Σ do not
-- preserve certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

¬-affine→linearity-Σ-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ v₂-ok →
  ¬ Are-preserving-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality v₁)
         no-type-restrictions)
      (second-ΠΣ-quantities-𝟘-or-ω ω (linearityModality v₂ v₂-ok) R₂)
      affine→linearity affine→linearity-Σ
¬-affine→linearity-Σ-preserves-second-ΠΣ-quantities-𝟘-or-ω _ _ _ r =
  case
    ΠΣ-preserved {b = BMΠ} {p = 𝟙} {q = 𝟘}
      (_ , (λ ()) , (λ _ → refl))
      .proj₂ .proj₁ refl
  of λ ()
  where
  open Are-preserving-type-restrictions r

-- The functions affine→linearity and affine→linearity-Σ do not
-- reflect certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

¬-affine→linearity-Σ-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ v₂-ok →
  ¬ Are-reflecting-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality v₁) R)
      (second-ΠΣ-quantities-𝟘-or-ω ω
         (linearityModality v₂ v₂-ok) no-type-restrictions)
      affine→linearity affine→linearity-Σ
¬-affine→linearity-Σ-reflects-second-ΠΣ-quantities-𝟘-or-ω _ _ _ r =
  case
    ΠΣ-reflected {b = BMΠ} {p = ω} {q = 𝟙}
      (_ , (λ _ → refl) , ⊥-elim ∘→ (_$ refl))
  of
    λ (_ , eq , _) →
  case eq refl of λ ()
  where
  open Are-reflecting-type-restrictions r

-- If the function linearity→affine preserves certain type
-- restrictions, then the function also preserves certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

linearity→affine-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₁-ok v₂ →
  Are-preserving-type-restrictions R₁ R₂
    linearity→affine linearity→affine →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (linearityModality v₁ v₁-ok) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality v₂) R₂)
    linearity→affine linearity→affine
linearity→affine-preserves-second-ΠΣ-quantities-𝟘-or-ω v₁ v₁-ok v₂ =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    (linearityModality v₁ v₁-ok)
    (affineModality v₂)
    (λ _ → refl)
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

-- If the function linearity→affine reflects certain type
-- restrictions, then the function also reflects certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

linearity→affine-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₁-ok v₂ →
  Are-reflecting-type-restrictions R₁ R₂
    linearity→affine linearity→affine →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (linearityModality v₁ v₁-ok) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality v₂) R₂)
    linearity→affine linearity→affine
linearity→affine-reflects-second-ΠΣ-quantities-𝟘-or-ω v₁ v₁-ok v₂ =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    (linearityModality v₁ v₁-ok)
    (affineModality v₂)
    (λ where
       {p = 𝟘} _  → refl
       {p = 𝟙} ()
       {p = ω} ())
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
