------------------------------------------------------------------------
-- Lemmas related to
-- Are-preserving-type-restrictions/Are-reflecting-type-restrictions
-- and specific type restriction transformers (and
-- no-type-restrictions)
------------------------------------------------------------------------

module Graded.Modality.Morphism.Type-restrictions.Examples where

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Product as Σ
open import Tools.PropositionalEquality
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum as ⊎

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
open import Graded.Modality.Morphism.Examples
open import Graded.Modality.Morphism.Type-restrictions
import Graded.Modality.Properties
open import Graded.Mode
open import Graded.Restrictions

open import Definition.Typed.Restrictions

open import Definition.Untyped.NotParametrised
open import Definition.Untyped.QuantityTranslation

private variable
  b₁ b₂ 𝟙≤𝟘   : Bool
  R R₁ R₂     : Type-restrictions _
  s           : Strength
  M₁ M₂       : Set _
  Mode₁ Mode₂ : Set _
  𝕄₁ 𝕄₂       : Modality _
  𝐌₁ 𝐌₂     : IsMode _ _
  tr tr-Σ     : M₁ → M₂
  v₁-ok v₂-ok : ¬ _

------------------------------------------------------------------------
-- Preserving/reflecting no type restrictions

opaque

  -- The functions tr and tr-Σ preserve certain type restrictions
  -- obtained from no-type-restrictions, given a certain assumption.

  Are-preserving-type-restrictions-no-type-restrictions :
    (¬ Modality.Trivial 𝕄₁ → ¬ Modality.Trivial 𝕄₂) →
    Are-preserving-type-restrictions
      (no-type-restrictions 𝕄₁ 𝐌₁ b₁ b₂)
      (no-type-restrictions 𝕄₂ 𝐌₂ b₁ b₂)
      tr tr-Σ
  Are-preserving-type-restrictions-no-type-restrictions hyp = λ where
      .unfolding-mode-preserved      → refl
      .level-support-preserved       → level-type small≤small
      .Omega-plus-preserved          → _
      .Unitʷ-η-preserved ()
      .Unit-preserved                → _
      .ΠΣ-preserved                  → _
      .Opacity-preserved             → lift ∘→ Lift.lower
      .K-preserved                   → lift ∘→ Lift.lower
      .[]-cong-preserved             → hyp
      .Equality-reflection-preserved → lift ∘→ Lift.lower
    where
    open Are-preserving-type-restrictions

opaque

  -- The functions tr and tr-Σ reflect certain type restrictions
  -- obtained from no-type-restrictions, given a certain assumption.

  Are-reflecting-type-restrictions-no-type-restrictions :
    (Modality.Trivial 𝕄₂ ⊎ ¬ Modality.Trivial 𝕄₂ →
     Modality.Trivial 𝕄₁ ⊎ ¬ Modality.Trivial 𝕄₁) →
    Are-reflecting-type-restrictions
      (no-type-restrictions 𝕄₁ 𝐌₁ b₁ b₂)
      (no-type-restrictions 𝕄₂ 𝐌₂ b₁ b₂)
      tr tr-Σ
  Are-reflecting-type-restrictions-no-type-restrictions hyp = λ where
      .unfolding-mode-reflected      → refl
      .level-support-reflected       → level-type small≤small
      .Unitʷ-η-reflected ()
      .Unit-reflected                → _
      .ΠΣ-reflected                  → _
      .Opacity-reflected             → lift ∘→ Lift.lower
      .K-reflected                   → lift ∘→ Lift.lower
      .[]-cong-reflected             → ⊎.comm ∘→ hyp ∘→ ⊎.comm
      .Equality-reflection-reflected → lift ∘→ Lift.lower
    where
    open Are-reflecting-type-restrictions

------------------------------------------------------------------------
-- Preserving/reflecting certain type restrictions

-- If tr preserves type restrictions for R₁ and R₂, then it also does
-- this for equal-binder-quantities 𝕄₁ R₁ and
-- equal-binder-quantities 𝕄₂ R₂.

Are-preserving-type-restrictions-equal-binder-quantities :
  Are-preserving-type-restrictions R₁ R₂ tr tr →
  Are-preserving-type-restrictions
    (equal-binder-quantities 𝕄₁ 𝐌₁ R₁)
    (equal-binder-quantities 𝕄₂ 𝐌₂ R₂)
    tr tr
Are-preserving-type-restrictions-equal-binder-quantities {tr = tr} r =
  record
    { unfolding-mode-preserved = R.unfolding-mode-preserved
    ; level-support-preserved  = R.level-support-preserved
    ; Omega-plus-preserved     = R.Omega-plus-preserved
    ; Unitʷ-η-preserved        = R.Unitʷ-η-preserved
    ; Unit-preserved           = R.Unit-preserved
    ; ΠΣ-preserved             = λ {b = b} → λ where
        (bn , refl) →
            R.ΠΣ-preserved bn
          , tr-BinderMode-one-function _ _ refl b
    ; Opacity-preserved             = R.Opacity-preserved
    ; K-preserved                   = R.K-preserved
    ; []-cong-preserved             = R.[]-cong-preserved
    ; Equality-reflection-preserved = R.Equality-reflection-preserved
    }
  where
  module R = Are-preserving-type-restrictions r

-- If tr reflects type restrictions for R₁ and R₂, then it also does
-- this for equal-binder-quantities 𝕄₁ R₁ and
-- equal-binder-quantities 𝕄₂ R₂, assuming that the function is
-- injective.

Are-reflecting-type-restrictions-equal-binder-quantities :
  (∀ {p q} → tr p ≡ tr q → p ≡ q) →
  Are-reflecting-type-restrictions R₁ R₂ tr tr →
  Are-reflecting-type-restrictions
    (equal-binder-quantities 𝕄₁ 𝐌₁ R₁)
    (equal-binder-quantities 𝕄₂ 𝐌₂ R₂)
    tr tr
Are-reflecting-type-restrictions-equal-binder-quantities
  {tr = tr} inj r = record
  { unfolding-mode-reflected = unfolding-mode-reflected
  ; level-support-reflected  = level-support-reflected
  ; Unitʷ-η-reflected        = Unitʷ-η-reflected
  ; Unit-reflected           = Unit-reflected
  ; ΠΣ-reflected             =
      λ {b = b} {p = p} {q = q} (bn , eq) →
          ΠΣ-reflected bn
        , inj (
            tr p                     ≡˘⟨ tr-BinderMode-one-function _ _ refl b ⟩
            tr-BinderMode tr tr b p  ≡⟨ eq ⟩
            tr q                     ∎)
  ; Opacity-reflected             = Opacity-reflected
  ; K-reflected                   = K-reflected
  ; []-cong-reflected             = []-cong-reflected
  ; Equality-reflection-reflected = Equality-reflection-reflected
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
    (second-ΠΣ-quantities-𝟘 𝕄₁ 𝐌₁ R₁)
    (second-ΠΣ-quantities-𝟘 𝕄₂ 𝐌₂ R₂)
    tr tr-Σ
Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘 tr-𝟘 r = record
  { unfolding-mode-preserved = unfolding-mode-preserved
  ; level-support-preserved  = level-support-preserved
  ; Omega-plus-preserved     = Omega-plus-preserved
  ; Unitʷ-η-preserved        = Unitʷ-η-preserved
  ; Unit-preserved           = Unit-preserved
  ; ΠΣ-preserved             = λ where
      (b , refl) → ΠΣ-preserved b , tr-𝟘
  ; Opacity-preserved             = Opacity-preserved
  ; K-preserved                   = K-preserved
  ; []-cong-preserved             = []-cong-preserved
  ; Equality-reflection-preserved = Equality-reflection-preserved
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
    (second-ΠΣ-quantities-𝟘 𝕄₁ 𝐌₁ R₁)
    (second-ΠΣ-quantities-𝟘 𝕄₂ 𝐌₂ R₂)
    tr tr-Σ
Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘 tr-𝟘 r = record
  { unfolding-mode-reflected      = unfolding-mode-reflected
  ; level-support-reflected       = level-support-reflected
  ; Unitʷ-η-reflected             = Unitʷ-η-reflected
  ; Unit-reflected                = Unit-reflected
  ; ΠΣ-reflected                  = Σ.map ΠΣ-reflected tr-𝟘
  ; Opacity-reflected             = Opacity-reflected
  ; K-reflected                   = K-reflected
  ; []-cong-reflected             = []-cong-reflected
  ; Equality-reflection-reflected = Equality-reflection-reflected
  }
  where
  open Are-reflecting-type-restrictions r

-- If the functions tr and tr-Σ preserve certain type restrictions,
-- then they also do this for certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω, given that certain assumptions hold.

Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω :
  (Modality.𝟙 𝕄₁ ≢ Modality.𝟘 𝕄₁ →
   tr (Modality.𝟘 𝕄₁) ≡ Modality.𝟘 𝕄₂) →
  (∀ {p} → tr p ≡ Modality.ω 𝕄₂ ⇔ p ≡ Modality.ω 𝕄₁) →
  (∀ {p} → tr-Σ p ≡ Modality.ω 𝕄₂ ⇔ p ≡ Modality.ω 𝕄₁) →
  Are-preserving-type-restrictions R₁ R₂ tr tr-Σ →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ 𝐌₁ R₁)
    (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ 𝐌₂ R₂)
    tr tr-Σ
Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
  {𝕄₁} {tr} {𝕄₂} {tr-Σ} tr-𝟘 tr-ω tr-Σ-ω r = record
  { unfolding-mode-preserved = unfolding-mode-preserved
  ; level-support-preserved  = level-support-preserved
  ; Omega-plus-preserved     = Omega-plus-preserved
  ; Unitʷ-η-preserved        = Unitʷ-η-preserved
  ; Unit-preserved           = Unit-preserved
  ; ΠΣ-preserved             = λ {b = b} (bn , is-𝟘 , not-𝟘) →
      ΠΣ-preserved bn , lemma₁ b is-𝟘 , lemma₃ b not-𝟘
  ; Opacity-preserved             = Opacity-preserved
  ; K-preserved                   = K-preserved
  ; []-cong-preserved             = []-cong-preserved
  ; Equality-reflection-preserved = Equality-reflection-preserved
  }
  where
  module M₁ = Modality 𝕄₁
  module M₂ = Modality 𝕄₂
  open Are-preserving-type-restrictions r
  open Graded.Modality.Properties 𝕄₁

  lemma₁ :
    ∀ {p q} b →
    (p ≡ M₁.ω → q ≡ M₁.ω) →
    tr-BinderMode tr tr-Σ b p ≡ M₂.ω → tr q ≡ M₂.ω
  lemma₁ {p = p} {q = q} BMΠ hyp =
    tr p ≡ M₂.ω  →⟨ tr-ω .proj₁ ⟩
    p ≡ M₁.ω     →⟨ hyp ⟩
    q ≡ M₁.ω     →⟨ tr-ω .proj₂ ⟩
    tr q ≡ M₂.ω  □
  lemma₁ {p = p} {q = q} (BMΣ _) hyp =
    tr-Σ p ≡ M₂.ω  →⟨ tr-Σ-ω .proj₁ ⟩
    p ≡ M₁.ω       →⟨ hyp ⟩
    q ≡ M₁.ω       →⟨ tr-ω .proj₂ ⟩
    tr q ≡ M₂.ω    □

  lemma₂ :
    ∀ {p q} →
    (p ≢ M₁.ω → q ≡ M₁.𝟘) →
    p ≢ M₁.ω → tr q ≡ M₂.𝟘
  lemma₂ {p = p} {q = q} hyp p≢ω₁ =
    case hyp p≢ω₁ of λ {
      refl →
    tr-𝟘 (≢→non-trivial p≢ω₁) }

  lemma₃ :
    ∀ {p q} b →
    (p ≢ M₁.ω → q ≡ M₁.𝟘) →
    tr-BinderMode tr tr-Σ b p ≢ M₂.ω → tr q ≡ M₂.𝟘
  lemma₃ {p = p} {q = q} BMΠ hyp =
    tr p ≢ M₂.ω  →⟨ _∘→ tr-ω .proj₂ ⟩
    p ≢ M₁.ω     →⟨ lemma₂ hyp ⟩
    tr q ≡ M₂.𝟘  □
  lemma₃ {p = p} {q = q} (BMΣ _) hyp =
    tr-Σ p ≢ M₂.ω  →⟨ _∘→ tr-Σ-ω .proj₂ ⟩
    p ≢ M₁.ω       →⟨ lemma₂ hyp ⟩
    tr q ≡ M₂.𝟘    □

-- If the functions tr and tr-Σ reflect certain type restrictions,
-- then they also do this for certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω, given that certain assumptions hold.

Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω :
  (∀ {p} → tr p ≡ Modality.𝟘 𝕄₂ → p ≡ Modality.𝟘 𝕄₁) →
  (∀ {p} → tr p ≡ Modality.ω 𝕄₂ ⇔ p ≡ Modality.ω 𝕄₁) →
  (∀ {p} → tr-Σ p ≡ Modality.ω 𝕄₂ ⇔ p ≡ Modality.ω 𝕄₁) →
  Are-reflecting-type-restrictions R₁ R₂ tr tr-Σ →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ 𝐌₁ R₁)
    (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ 𝐌₂ R₂)
    tr tr-Σ
Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
  {tr} {𝕄₂} {𝕄₁} {tr-Σ} tr-𝟘 tr-ω tr-Σ-ω r = record
  { unfolding-mode-reflected = unfolding-mode-reflected
  ; level-support-reflected  = level-support-reflected
  ; Unitʷ-η-reflected        = Unitʷ-η-reflected
  ; Unit-reflected           = Unit-reflected
  ; ΠΣ-reflected             = λ {b = b} (bn , is-𝟘 , not-𝟘) →
      ΠΣ-reflected bn , lemma₁ b is-𝟘 , lemma₂ b not-𝟘
  ; Opacity-reflected             = Opacity-reflected
  ; K-reflected                   = K-reflected
  ; []-cong-reflected             = []-cong-reflected
  ; Equality-reflection-reflected = Equality-reflection-reflected
  }
  where
  module M₁ = Modality 𝕄₁
  module M₂ = Modality 𝕄₂
  open Are-reflecting-type-restrictions r

  lemma₁ :
    ∀ {p q} b →
    (tr-BinderMode tr tr-Σ b p ≡ M₂.ω → tr q ≡ M₂.ω) →
    p ≡ M₁.ω → q ≡ M₁.ω
  lemma₁ {p = p} {q = q} BMΠ hyp =
    p ≡ M₁.ω     →⟨ tr-ω .proj₂ ⟩
    tr p ≡ M₂.ω  →⟨ hyp ⟩
    tr q ≡ M₂.ω  →⟨ tr-ω .proj₁ ⟩
    q ≡ M₁.ω     □
  lemma₁ {p = p} {q = q} (BMΣ _) hyp =
    p ≡ M₁.ω       →⟨ tr-Σ-ω .proj₂ ⟩
    tr-Σ p ≡ M₂.ω  →⟨ hyp ⟩
    tr q ≡ M₂.ω    →⟨ tr-ω .proj₁ ⟩
    q ≡ M₁.ω       □

  lemma₂ :
    ∀ {p q} b →
    (tr-BinderMode tr tr-Σ b p ≢ M₂.ω → tr q ≡ M₂.𝟘) →
    p ≢ M₁.ω → q ≡ M₁.𝟘
  lemma₂ {p = p} {q = q} BMΠ hyp =
    p ≢ M₁.ω     →⟨ _∘→ tr-ω .proj₁ ⟩
    tr p ≢ M₂.ω  →⟨ hyp ⟩
    tr q ≡ M₂.𝟘  →⟨ tr-𝟘 ⟩
    q ≡ M₁.𝟘     □
  lemma₂ {p = p} {q = q} (BMΣ _) hyp =
    p ≢ M₁.ω       →⟨ _∘→ tr-Σ-ω .proj₁ ⟩
    tr-Σ p ≢ M₂.ω  →⟨ hyp ⟩
    tr q ≡ M₂.𝟘    →⟨ tr-𝟘 ⟩
    q ≡ M₁.𝟘       □

opaque

 -- If the functions tr and tr-Σ preserve certain type restrictions,
 -- then they do this also for certain type restrictions obtained
 -- using strong-types-restricted, given a certain assumption.

 Are-preserving-type-restrictions-strong-types-restricted :
   tr-Σ (Modality.𝟙 𝕄₁) ≡ Modality.𝟙 𝕄₂ →
   Are-preserving-type-restrictions R₁ R₂ tr tr-Σ →
   Are-preserving-type-restrictions
     (strong-types-restricted 𝕄₁ 𝐌₁ R₁)
     (strong-types-restricted 𝕄₂ 𝐌₂ R₂)
     tr tr-Σ
 Are-preserving-type-restrictions-strong-types-restricted hyp r = record
   { unfolding-mode-preserved =
       unfolding-mode-preserved
   ; level-support-preserved =
       level-support-preserved
   ; Omega-plus-preserved =
       Omega-plus-preserved
   ; Unitʷ-η-preserved =
       Unitʷ-η-preserved
   ; Unit-preserved =
       Σ.map Unit-preserved idᶠ
   ; ΠΣ-preserved =
       Σ.map ΠΣ-preserved λ where
         hyp′ refl → case hyp′ refl of λ where
           refl → hyp
   ; Opacity-preserved =
       Opacity-preserved
   ; K-preserved =
       K-preserved
   ; []-cong-preserved =
       Σ.map []-cong-preserved idᶠ
   ; Equality-reflection-preserved =
       Equality-reflection-preserved
   }
   where
   open Are-preserving-type-restrictions r

opaque

 -- If the functions tr and tr-Σ reflect certain type restrictions,
 -- then they do this also for certain type restrictions obtained
 -- using strong-types-restricted, given certain assumptions.

 Are-reflecting-type-restrictions-strong-types-restricted :
   (∀ {p} → tr-Σ p ≡ Modality.𝟙 𝕄₂ → p ≡ Modality.𝟙 𝕄₁) →
   (∀ {s} →
    Modality.Trivial 𝕄₂ →
    ¬ Type-restrictions.[]-cong-allowed R₁ s) →
   Are-reflecting-type-restrictions R₁ R₂ tr tr-Σ →
   Are-reflecting-type-restrictions
     (strong-types-restricted 𝕄₁ 𝐌₁ R₁)
     (strong-types-restricted 𝕄₂ 𝐌₂ R₂)
     tr tr-Σ
 Are-reflecting-type-restrictions-strong-types-restricted
   hyp₁ hyp₂ r = record
   { unfolding-mode-reflected =
       unfolding-mode-reflected
   ; level-support-reflected =
       level-support-reflected
   ; Unitʷ-η-reflected =
       Unitʷ-η-reflected
   ; Unit-reflected =
       Σ.map Unit-reflected idᶠ
   ; ΠΣ-reflected =
       Σ.map ΠΣ-reflected (λ { hyp refl → hyp₁ (hyp refl) })
   ; Opacity-reflected =
       Opacity-reflected
   ; K-reflected =
       K-reflected
   ; []-cong-reflected = λ {s = s} → λ where
       (inj₁ (ok₂ , s≢𝕤)) →
         case []-cong-reflected (inj₁ ok₂) of λ where
           (inj₁ ok₁)      → inj₁ (ok₁ , s≢𝕤)
           (inj₂ trivial₁) → inj₂ trivial₁
       (inj₂ trivial₂) →
         case []-cong-reflected {s = s} (inj₂ trivial₂) of λ where
           (inj₁ ok₁)      → ⊥-elim $ hyp₂ trivial₂ ok₁
           (inj₂ trivial₁) → inj₂ trivial₁
   ; Equality-reflection-reflected =
       Equality-reflection-reflected
   }
   where
   open Are-reflecting-type-restrictions r

opaque

 -- If the functions tr and tr-Σ preserve certain type restrictions,
 -- then they do this also for certain type restrictions obtained
 -- using no-strong-types.

 Are-preserving-type-restrictions-no-strong-types :
   Are-preserving-type-restrictions R₁ R₂ tr tr-Σ →
   Are-preserving-type-restrictions
     (no-strong-types 𝕄₁ 𝐌₁ R₁)
     (no-strong-types 𝕄₂ 𝐌₂ R₂)
     tr tr-Σ
 Are-preserving-type-restrictions-no-strong-types r = record
   { unfolding-mode-preserved =
       unfolding-mode-preserved
   ; level-support-preserved =
       level-support-preserved
   ; Omega-plus-preserved =
       Omega-plus-preserved
   ; Unitʷ-η-preserved =
       Unitʷ-η-preserved
   ; Unit-preserved =
       Σ.map Unit-preserved idᶠ
   ; ΠΣ-preserved =
       Σ.map ΠΣ-preserved (lift ∘→ Lift.lower)
   ; Opacity-preserved =
       Opacity-preserved
   ; K-preserved =
       K-preserved
   ; []-cong-preserved =
       Σ.map []-cong-preserved idᶠ
   ; Equality-reflection-preserved =
       Equality-reflection-preserved
   }
   where
   open Are-preserving-type-restrictions r

opaque

 -- If the functions tr and tr-Σ reflect certain type restrictions,
 -- then they do this also for certain type restrictions obtained
 -- using no-strong-types, given a certain assumption.

 Are-reflecting-type-restrictions-no-strong-types :
   (∀ {s} →
    Modality.Trivial 𝕄₂ →
    ¬ Type-restrictions.[]-cong-allowed R₁ s) →
   Are-reflecting-type-restrictions R₁ R₂ tr tr-Σ →
   Are-reflecting-type-restrictions
     (no-strong-types 𝕄₁ 𝐌₁ R₁)
     (no-strong-types 𝕄₂ 𝐌₂ R₂)
     tr tr-Σ
 Are-reflecting-type-restrictions-no-strong-types hyp r = record
   { unfolding-mode-reflected =
       unfolding-mode-reflected
   ; level-support-reflected =
       level-support-reflected
   ; Unitʷ-η-reflected =
       Unitʷ-η-reflected
   ; Unit-reflected =
       Σ.map Unit-reflected idᶠ
   ; ΠΣ-reflected =
       Σ.map ΠΣ-reflected (lift ∘→ Lift.lower)
   ; Opacity-reflected =
       Opacity-reflected
   ; K-reflected =
       K-reflected
   ; []-cong-reflected = λ {s = s} → λ where
       (inj₁ (ok₂ , s≢𝕤)) →
         case []-cong-reflected (inj₁ ok₂) of λ where
           (inj₁ ok₁)      → inj₁ (ok₁ , s≢𝕤)
           (inj₂ trivial₁) → inj₂ trivial₁
       (inj₂ trivial₂) →
         case []-cong-reflected {s = s} (inj₂ trivial₂) of λ where
           (inj₁ ok₁)      → ⊥-elim $ hyp trivial₂ ok₁
           (inj₂ trivial₁) → inj₂ trivial₁
   ; Equality-reflection-reflected =
       Equality-reflection-reflected
   }
   where
   open Are-reflecting-type-restrictions r

-- If the functions tr and tr-Σ preserve certain type restrictions,
-- then they do this also for certain type restrictions obtained using
-- no-erased-matches-TR.

Are-preserving-type-restrictions-no-erased-matches-TR :
  Are-preserving-type-restrictions R₁ R₂ tr tr-Σ →
  Are-preserving-type-restrictions
    (no-erased-matches-TR 𝕄₁ 𝐌₁ s R₁)
    (no-erased-matches-TR 𝕄₂ 𝐌₂ s R₂)
    tr tr-Σ
Are-preserving-type-restrictions-no-erased-matches-TR r = record
  { unfolding-mode-preserved      = unfolding-mode-preserved
  ; level-support-preserved       = level-support-preserved
  ; Omega-plus-preserved          = Omega-plus-preserved
  ; Unitʷ-η-preserved             = Unitʷ-η-preserved
  ; Unit-preserved                = Unit-preserved
  ; ΠΣ-preserved                  = ΠΣ-preserved
  ; Opacity-preserved             = Opacity-preserved
  ; K-preserved                   = K-preserved
  ; []-cong-preserved             = Σ.map []-cong-preserved idᶠ
  ; Equality-reflection-preserved = Equality-reflection-preserved
  }
  where
  open Are-preserving-type-restrictions r

-- If the functions tr and tr-Σ reflect certain type restrictions,
-- then they do this also for certain type restrictions obtained using
-- no-erased-matches-TR, given a certain assumption.

Are-reflecting-type-restrictions-no-erased-matches-TR :
  (∀ {s} →
   Modality.Trivial 𝕄₂ →
   ¬ Type-restrictions.[]-cong-allowed R₁ s) →
  Are-reflecting-type-restrictions R₁ R₂ tr tr-Σ →
  Are-reflecting-type-restrictions
    (no-erased-matches-TR 𝕄₁ 𝐌₁ s R₁)
    (no-erased-matches-TR 𝕄₂ 𝐌₂ s R₂)
    tr tr-Σ
Are-reflecting-type-restrictions-no-erased-matches-TR hyp r = record
  { unfolding-mode-reflected = unfolding-mode-reflected
  ; level-support-reflected  = level-support-reflected
  ; Unitʷ-η-reflected        = Unitʷ-η-reflected
  ; Unit-reflected           = Unit-reflected
  ; ΠΣ-reflected             = ΠΣ-reflected
  ; Opacity-reflected        = Opacity-reflected
  ; K-reflected              = K-reflected
  ; []-cong-reflected        = λ {s = s} → λ where
      (inj₁ (ok₂ , s≢)) →
        case []-cong-reflected (inj₁ ok₂) of λ where
          (inj₁ ok₁)      → inj₁ (ok₁ , s≢)
          (inj₂ trivial₁) → inj₂ trivial₁
      (inj₂ trivial₂) →
        case []-cong-reflected {s = s} (inj₂ trivial₂) of λ where
          (inj₁ ok₁)      → ⊥-elim $ hyp trivial₂ ok₁
          (inj₂ trivial₁) → inj₂ trivial₁
  ; Equality-reflection-reflected = Equality-reflection-reflected
  }
  where
  open Are-reflecting-type-restrictions r

opaque

  -- If the functions tr and tr-Σ preserve certain type restrictions,
  -- then they do this also for certain type restrictions obtained using
  -- []-cong-TR, given a certain assumption.

  Are-preserving-type-restrictions-[]-cong-TR :
    let module M₁ = Modality 𝕄₁
        module M₂ = Modality 𝕄₂
    in
    (¬ M₁.Trivial → ¬ M₂.Trivial × tr M₁.𝟘 ≡ M₂.𝟘 × tr-Σ M₁.𝟘 ≡ M₂.𝟘) →
    Are-preserving-type-restrictions R₁ R₂ tr tr-Σ →
    Are-preserving-type-restrictions
      ([]-cong-TR 𝕄₁ 𝐌₁ R₁)
      ([]-cong-TR 𝕄₂ 𝐌₂ R₂)
      tr tr-Σ
  Are-preserving-type-restrictions-[]-cong-TR hyp r = record
    { unfolding-mode-preserved =
        unfolding-mode-preserved
    ; level-support-preserved =
        level-support-preserved
    ; Omega-plus-preserved =
        Omega-plus-preserved
    ; Unitʷ-η-preserved =
        Unitʷ-η-preserved
    ; Unit-preserved =
        ⊎.map Unit-preserved (proj₁ ∘→ hyp)
    ; ΠΣ-preserved = λ {b = b} ok →
        case singleton b of λ where
          (BMΠ , refl) →
            ΠΣ-preserved ok
          (BMΣ s , refl) →
            ⊎.map
              ΠΣ-preserved
              (λ { (non-trivial , refl , refl) →
                   let non-trivial , tr-𝟘≡𝟘 , tr-Σ-𝟘≡𝟘 =
                         hyp non-trivial
                   in
                   non-trivial , tr-Σ-𝟘≡𝟘 , tr-𝟘≡𝟘 })
              ok
    ; Opacity-preserved =
        Opacity-preserved
    ; K-preserved =
        K-preserved
    ; []-cong-preserved =
        proj₁ ∘→ hyp
    ; Equality-reflection-preserved =
        Equality-reflection-preserved
    }
    where
    open Are-preserving-type-restrictions r

opaque

  -- If the functions tr and tr-Σ reflect certain type restrictions,
  -- then they do this also for certain type restrictions obtained using
  -- []-cong-TR, given a certain assumption.

  Are-reflecting-type-restrictions-[]-cong-TR :
    let module M₁ = Modality 𝕄₁
        module M₂ = Modality 𝕄₂
    in
    (¬ M₂.Trivial →
     ¬ M₁.Trivial ×
     (∀ p → tr p ≡ M₂.𝟘 → p ≡ M₁.𝟘) ×
     (∀ p → tr-Σ p ≡ M₂.𝟘 → p ≡ M₁.𝟘)) →
    Are-reflecting-type-restrictions R₁ R₂ tr tr-Σ →
    Are-reflecting-type-restrictions
      ([]-cong-TR 𝕄₁ 𝐌₁ R₁)
      ([]-cong-TR 𝕄₂ 𝐌₂ R₂)
      tr tr-Σ
  Are-reflecting-type-restrictions-[]-cong-TR {𝕄₁} hyp r = record
    { unfolding-mode-reflected =
        unfolding-mode-reflected
    ; level-support-reflected =
        level-support-reflected
    ; Unitʷ-η-reflected =
        Unitʷ-η-reflected
    ; Unit-reflected =
        ⊎.map Unit-reflected (proj₁ ∘→ hyp)
    ; ΠΣ-reflected =
        λ {b = b} ok →
        case singleton b of λ where
          (BMΠ , refl) →
            ΠΣ-reflected ok
          (BMΣ s , refl) →
            ⊎.map
              ΠΣ-reflected
              (λ (non-trivial , tr-Σ-p≡𝟘 , tr-q≡𝟘) →
                 let non-trivial , tr≡𝟘→≡𝟘 , tr-Σ≡𝟘→≡𝟘 =
                       hyp non-trivial
                 in
                 non-trivial , tr-Σ≡𝟘→≡𝟘 _ tr-Σ-p≡𝟘 , tr≡𝟘→≡𝟘 _ tr-q≡𝟘)
              ok
    ; Opacity-reflected =
        Opacity-reflected
    ; K-reflected =
        K-reflected
    ; []-cong-reflected = λ _ → case trivial? of λ where
        (yes trivial)    → inj₂ trivial
        (no non-trivial) → inj₁ non-trivial
    ; Equality-reflection-reflected =
        Equality-reflection-reflected
    }
    where
    open Graded.Modality.Properties 𝕄₁
    open Are-reflecting-type-restrictions r

opaque

  -- If the functions tr and tr-Σ preserve certain type restrictions,
  -- then they do this also for certain type restrictions obtained
  -- using no-[]-cong-TR.

  Are-preserving-type-restrictions-no-[]-cong-TR :
    Are-preserving-type-restrictions R₁ R₂ tr tr-Σ →
    Are-preserving-type-restrictions
      (no-[]-cong-TR 𝕄₁ 𝐌₁ R₁)
      (no-[]-cong-TR 𝕄₂ 𝐌₂ R₂)
      tr tr-Σ
  Are-preserving-type-restrictions-no-[]-cong-TR r = record
    { unfolding-mode-preserved      = unfolding-mode-preserved
    ; level-support-preserved       = level-support-preserved
    ; Omega-plus-preserved          = Omega-plus-preserved
    ; Unitʷ-η-preserved             = Unitʷ-η-preserved
    ; Unit-preserved                = Unit-preserved
    ; ΠΣ-preserved                  = ΠΣ-preserved
    ; Opacity-preserved             = Opacity-preserved
    ; K-preserved                   = K-preserved
    ; []-cong-preserved             = λ ()
    ; Equality-reflection-preserved = Equality-reflection-preserved
    }
    where
    open Are-preserving-type-restrictions r

opaque

  -- If the functions tr and tr-Σ reflect certain type restrictions,
  -- then they do this also for certain type restrictions obtained
  -- using no-[]-cong-TR, given a certain assumption.

  Are-reflecting-type-restrictions-no-[]-cong-TR :
    (∀ {s} →
     Modality.Trivial 𝕄₂ →
     ¬ Type-restrictions.[]-cong-allowed R₁ s) →
    Are-reflecting-type-restrictions R₁ R₂ tr tr-Σ →
    Are-reflecting-type-restrictions
      (no-[]-cong-TR 𝕄₁ 𝐌₁ R₁)
      (no-[]-cong-TR 𝕄₂ 𝐌₂ R₂)
      tr tr-Σ
  Are-reflecting-type-restrictions-no-[]-cong-TR hyp r = record
    { unfolding-mode-reflected = unfolding-mode-reflected
    ; level-support-reflected  = level-support-reflected
    ; Unitʷ-η-reflected        = Unitʷ-η-reflected
    ; Unit-reflected           = Unit-reflected
    ; ΠΣ-reflected             = ΠΣ-reflected
    ; Opacity-reflected        = Opacity-reflected
    ; K-reflected              = K-reflected
    ; []-cong-reflected        = λ {s = s} → λ where
        (inj₁ ())
        (inj₂ trivial) →
          case []-cong-reflected {s = s} (inj₂ trivial) of λ where
            (inj₁ ok)      → ⊥-elim $ hyp trivial ok
            (inj₂ trivial) → inj₂ trivial
    ; Equality-reflection-reflected = Equality-reflection-reflected
    }
    where
    open Are-reflecting-type-restrictions r

opaque

  -- If the functions tr and tr-Σ preserve certain type restrictions,
  -- then they do this also for certain type restrictions obtained
  -- using with-equality-reflection.

  Are-preserving-type-restrictions-with-equality-reflection :
    Are-preserving-type-restrictions R₁ R₂ tr tr-Σ →
    Are-preserving-type-restrictions
      (with-equality-reflection 𝕄₁ 𝐌₁ R₁)
      (with-equality-reflection 𝕄₂ 𝐌₂ R₂)
      tr tr-Σ
  Are-preserving-type-restrictions-with-equality-reflection r = record
    { unfolding-mode-preserved      = unfolding-mode-preserved
    ; level-support-preserved       = level-support-preserved
    ; Omega-plus-preserved          = Omega-plus-preserved
    ; Unitʷ-η-preserved             = Unitʷ-η-preserved
    ; Unit-preserved                = Unit-preserved
    ; ΠΣ-preserved                  = ΠΣ-preserved
    ; Opacity-preserved             = λ ()
    ; K-preserved                   = K-preserved
    ; []-cong-preserved             = []-cong-preserved
    ; Equality-reflection-preserved = _
    }
    where
    open Are-preserving-type-restrictions r

opaque

  -- If the functions tr and tr-Σ reflect certain type restrictions,
  -- then they do this also for certain type restrictions obtained
  -- using with-equality-reflection, given a certain assumption.

  Are-reflecting-type-restrictions-with-equality-reflection :
    (∀ {s} →
     Modality.Trivial 𝕄₂ →
     ¬ Type-restrictions.[]-cong-allowed R₁ s) →
    Are-reflecting-type-restrictions R₁ R₂ tr tr-Σ →
    Are-reflecting-type-restrictions
      (with-equality-reflection 𝕄₁ 𝐌₁ R₁)
      (with-equality-reflection 𝕄₂ 𝐌₂ R₂)
      tr tr-Σ
  Are-reflecting-type-restrictions-with-equality-reflection
    hyp r = record
    { unfolding-mode-reflected      = unfolding-mode-reflected
    ; level-support-reflected       = level-support-reflected
    ; Unitʷ-η-reflected             = Unitʷ-η-reflected
    ; Unit-reflected                = Unit-reflected
    ; ΠΣ-reflected                  = ΠΣ-reflected
    ; Opacity-reflected             = λ ()
    ; K-reflected                   = K-reflected
    ; []-cong-reflected             = []-cong-reflected
    ; Equality-reflection-reflected = _
    }
    where
    open Are-reflecting-type-restrictions r

------------------------------------------------------------------------
-- Some lemmas related to equal-binder-quantities and concrete
-- translation functions

-- The functions erasure→zero-one-many and erasure→zero-one-many-Σ do
-- not preserve certain type restrictions obtained using
-- equal-binder-quantities.

¬-erasure→zero-one-many-Σ-preserves-equal-binder-quantities :
  (R : Type-restrictions 𝕄₂) →
  ¬ Are-preserving-type-restrictions
      (equal-binder-quantities 𝕄₁ 𝐌₁ (no-type-restrictions 𝕄₁ 𝐌₁ b₁ b₂))
      (equal-binder-quantities 𝕄₂ 𝐌₂ R)
      erasure→zero-one-many erasure→zero-one-many-Σ
¬-erasure→zero-one-many-Σ-preserves-equal-binder-quantities _ r =
  case ΠΣ-preserved {b = BMΣ 𝕤} {p = ω} (_ , refl) .proj₂ of λ ()
  where
  open Are-preserving-type-restrictions r

-- The functions affine→linear-or-affine and affine→linear-or-affine-Σ
-- do not preserve certain type restrictions obtained using
-- equal-binder-quantities.

¬-affine→linear-or-affine-Σ-preserves-equal-binder-quantities :
  (R : Type-restrictions 𝕄₂) →
  ¬ Are-preserving-type-restrictions
      (equal-binder-quantities 𝕄₁ 𝐌₁ (no-type-restrictions 𝕄₁ 𝐌₁ b₁ b₂))
      (equal-binder-quantities 𝕄₂ 𝐌₂ R)
      affine→linear-or-affine affine→linear-or-affine-Σ
¬-affine→linear-or-affine-Σ-preserves-equal-binder-quantities _ r =
  case ΠΣ-preserved {b = BMΣ 𝕤} {p = 𝟙} (_ , refl) .proj₂ of λ ()
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
    (second-ΠΣ-quantities-𝟘-or-ω UnitModality 𝐌₁ R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ErasureModality 𝐌₂ R₂)
    unit→erasure unit→erasure
unit→erasure-preserves-second-ΠΣ-quantities-𝟘-or-ω {𝐌₁} {𝐌₂} =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    {𝐌₁ = 𝐌₁} {𝐌₂ = 𝐌₂}
    (λ tt≢tt → ⊥-elim (tt≢tt refl))
    ((λ _ → refl) , (λ _ → refl))
    ((λ _ → refl) , (λ _ → refl))

-- If the function unit→erasure reflects certain type restrictions,
-- then it also does this for certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

unit→erasure-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  Are-reflecting-type-restrictions
    R₁ R₂ unit→erasure unit→erasure →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω UnitModality 𝐌₁ R₁)
    (second-ΠΣ-quantities-𝟘-or-ω ErasureModality 𝐌₂ R₂)
    unit→erasure unit→erasure
unit→erasure-reflects-second-ΠΣ-quantities-𝟘-or-ω {𝐌₁} {𝐌₂} =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    {𝐌₁ = 𝐌₁} {𝐌₂ = 𝐌₂}
    (λ ())
    ((λ _ → refl) , (λ _ → refl))
    ((λ _ → refl) , (λ _ → refl))

-- If the function erasure→unit preserves certain type restrictions,
-- then it also does this for certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

erasure→unit-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  Are-preserving-type-restrictions
    R₁ R₂ erasure→unit erasure→unit →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ErasureModality 𝐌₁ R₁)
    (second-ΠΣ-quantities-𝟘-or-ω UnitModality 𝐌₂ R₂)
    erasure→unit erasure→unit
erasure→unit-preserves-second-ΠΣ-quantities-𝟘-or-ω r =
  record
    { unfolding-mode-preserved = unfolding-mode-preserved
    ; level-support-preserved  = level-support-preserved
    ; Omega-plus-preserved     = Omega-plus-preserved
    ; Unitʷ-η-preserved        = Unitʷ-η-preserved
    ; Unit-preserved           = Unit-preserved
    ; ΠΣ-preserved             = λ (b , _) →
        ΠΣ-preserved b , (λ _ → refl) , (λ _ → refl)
    ; Opacity-preserved             = Opacity-preserved
    ; K-preserved                   = K-preserved
    ; []-cong-preserved             = []-cong-preserved
    ; Equality-reflection-preserved = Equality-reflection-preserved
  }
  where
  open Are-preserving-type-restrictions r

-- The function erasure→unit does not reflect certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

¬-erasure→unit-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  let 𝕄₁ = ErasureModality
      𝕄₂ = UnitModality
  in
  (R₁ : Type-restrictions 𝕄₁) →
  ¬ Are-reflecting-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ 𝐌₁ R₁)
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ 𝐌₂ (no-type-restrictions 𝕄₂ 𝐌₂ b₁ b₂))
      erasure→unit erasure→unit
¬-erasure→unit-reflects-second-ΠΣ-quantities-𝟘-or-ω _ r =
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
  Are-preserving-type-restrictions R₁ R₂
    erasure→zero-one-many erasure→zero-one-many →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ErasureModality 𝐌₁ R₁)
    (second-ΠΣ-quantities-𝟘-or-ω (zero-one-many-modality 𝟙≤𝟘) 𝐌₂ R₂)
    erasure→zero-one-many erasure→zero-one-many
erasure→zero-one-many-preserves-second-ΠΣ-quantities-𝟘-or-ω {𝐌₁} {𝐌₂} =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    {𝐌₁ = 𝐌₁} {𝐌₂ = 𝐌₂}
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
  Are-reflecting-type-restrictions R₁ R₂
    erasure→zero-one-many erasure→zero-one-many →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ErasureModality 𝐌₁ R₁)
    (second-ΠΣ-quantities-𝟘-or-ω (zero-one-many-modality 𝟙≤𝟘) 𝐌₂ R₂)
    erasure→zero-one-many erasure→zero-one-many
erasure→zero-one-many-reflects-second-ΠΣ-quantities-𝟘-or-ω {𝐌₁} {𝐌₂} =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    {𝐌₁ = 𝐌₁} {𝐌₂ = 𝐌₂}
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
  let 𝕄₁ = ErasureModality
      𝕄₂ = zero-one-many-modality 𝟙≤𝟘
  in
  (R₂ : Type-restrictions 𝕄₂) →
  ¬ Are-preserving-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ 𝐌₁ (no-type-restrictions 𝕄₁ 𝐌₁ b₁ b₂))
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ 𝐌₂ R₂)
      erasure→zero-one-many erasure→zero-one-many-Σ
¬-erasure→zero-one-many-Σ-preserves-second-ΠΣ-quantities-𝟘-or-ω _ r =
  case
    ΠΣ-preserved {b = BMΣ 𝕤} {p = ω} {q = ω}
      (_ , (λ _ → refl) , ⊥-elim ∘→ (_$ refl))
      .proj₂ .proj₂ (λ ())
  of λ ()
  where
  open Are-preserving-type-restrictions r

-- The functions erasure→zero-one-many and erasure→zero-one-many-Σ do
-- not reflect certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

¬-erasure→zero-one-many-Σ-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  let 𝕄₁ = ErasureModality
      𝕄₂ = zero-one-many-modality 𝟙≤𝟘
  in
  (R₁ : Type-restrictions 𝕄₁) →
  ¬ Are-reflecting-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ 𝐌₁ R₁)
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ 𝐌₂ (no-type-restrictions 𝕄₂ 𝐌₂ b₁ b₂))
      erasure→zero-one-many erasure→zero-one-many-Σ
¬-erasure→zero-one-many-Σ-reflects-second-ΠΣ-quantities-𝟘-or-ω _ r =
  case
    ΠΣ-reflected {b = BMΣ 𝕤} {p = ω} {q = 𝟘}
      (_ , (λ ()) , (λ _ → refl))
      .proj₂ .proj₁ refl
  of λ ()
  where
  open Are-reflecting-type-restrictions r

-- The function zero-one-many→erasure does not preserve certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

¬-zero-one-many→erasure-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  let 𝕄₁ = zero-one-many-modality 𝟙≤𝟘
      𝕄₂ = ErasureModality
  in
  (R₂ : Type-restrictions 𝕄₂) →
  ¬ Are-preserving-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ 𝐌₁ (no-type-restrictions 𝕄₁ 𝐌₁ b₁ b₂))
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ 𝐌₂ R₂)
      zero-one-many→erasure zero-one-many→erasure
¬-zero-one-many→erasure-preserves-second-ΠΣ-quantities-𝟘-or-ω _ r =
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
  let 𝕄₁ = zero-one-many-modality 𝟙≤𝟘
      𝕄₂ = ErasureModality
  in
  (R₁ : Type-restrictions 𝕄₁) →
  ¬ Are-reflecting-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ 𝐌₁ R₁)
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ 𝐌₂ (no-type-restrictions 𝕄₂ 𝐌₂ b₁ b₂))
      zero-one-many→erasure zero-one-many→erasure
¬-zero-one-many→erasure-reflects-second-ΠΣ-quantities-𝟘-or-ω _ r =
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
  Are-preserving-type-restrictions R₁ R₂
    linearity→linear-or-affine linearity→linear-or-affine →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω linearityModality 𝐌₁ R₁)
    (second-ΠΣ-quantities-𝟘-or-ω linear-or-affine 𝐌₂ R₂)
    linearity→linear-or-affine linearity→linear-or-affine
linearity→linear-or-affine-preserves-second-ΠΣ-quantities-𝟘-or-ω {𝐌₁} {𝐌₂} =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    {𝐌₁ = 𝐌₁} {𝐌₂ = 𝐌₂}
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
  Are-reflecting-type-restrictions R₁ R₂
    linearity→linear-or-affine linearity→linear-or-affine →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω linearityModality 𝐌₁ R₁)
    (second-ΠΣ-quantities-𝟘-or-ω linear-or-affine 𝐌₂ R₂)
    linearity→linear-or-affine linearity→linear-or-affine
linearity→linear-or-affine-reflects-second-ΠΣ-quantities-𝟘-or-ω {𝐌₁} {𝐌₂} =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    {𝐌₁ = 𝐌₁} {𝐌₂ = 𝐌₂}
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
  let 𝕄₁ = linear-or-affine
      𝕄₂ = linearityModality
  in
  (R₂ : Type-restrictions 𝕄₂) →
  ¬ Are-preserving-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ 𝐌₁ (no-type-restrictions 𝕄₁ 𝐌₁ b₁ b₂))
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ 𝐌₂ R₂)
      linear-or-affine→linearity linear-or-affine→linearity
¬-linear-or-affine→linearity-preserves-second-ΠΣ-quantities-𝟘-or-ω _ r =
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
  let 𝕄₁ = linear-or-affine
      𝕄₂ = linearityModality
  in
  (R₁ : Type-restrictions 𝕄₁) →
  ¬ Are-reflecting-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ 𝐌₁ R₁)
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ 𝐌₂ (no-type-restrictions 𝕄₂ 𝐌₂ b₁ b₂))
      linear-or-affine→linearity linear-or-affine→linearity
¬-linear-or-affine→linearity-reflects-second-ΠΣ-quantities-𝟘-or-ω _ r =
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
  Are-preserving-type-restrictions R₁ R₂
    affine→linear-or-affine affine→linear-or-affine →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω affineModality 𝐌₁ R₁)
    (second-ΠΣ-quantities-𝟘-or-ω linear-or-affine 𝐌₂ R₂)
    affine→linear-or-affine affine→linear-or-affine
affine→linear-or-affine-preserves-second-ΠΣ-quantities-𝟘-or-ω {𝐌₁} {𝐌₂} =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    {𝐌₁ = 𝐌₁} {𝐌₂ = 𝐌₂}
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
  Are-reflecting-type-restrictions R₁ R₂
    affine→linear-or-affine affine→linear-or-affine →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω affineModality 𝐌₁ R₁)
    (second-ΠΣ-quantities-𝟘-or-ω linear-or-affine 𝐌₂ R₂)
    affine→linear-or-affine affine→linear-or-affine
affine→linear-or-affine-reflects-second-ΠΣ-quantities-𝟘-or-ω {𝐌₁} {𝐌₂} =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    {𝐌₁ = 𝐌₁} {𝐌₂ = 𝐌₂}
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
  Are-preserving-type-restrictions R₁ R₂
    affine→linear-or-affine affine→linear-or-affine-Σ →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω affineModality 𝐌₁ R₁)
    (second-ΠΣ-quantities-𝟘-or-ω linear-or-affine 𝐌₂ R₂)
    affine→linear-or-affine affine→linear-or-affine-Σ
affine→linear-or-affine-Σ-preserves-second-ΠΣ-quantities-𝟘-or-ω {𝐌₁} {𝐌₂} =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    {𝐌₁ = 𝐌₁} {𝐌₂ = 𝐌₂}
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
  Are-reflecting-type-restrictions R₁ R₂
    affine→linear-or-affine affine→linear-or-affine-Σ →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω affineModality 𝐌₁ R₁)
    (second-ΠΣ-quantities-𝟘-or-ω linear-or-affine 𝐌₂ R₂)
    affine→linear-or-affine affine→linear-or-affine-Σ
affine→linear-or-affine-Σ-reflects-second-ΠΣ-quantities-𝟘-or-ω {𝐌₁} {𝐌₂} =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    {𝐌₁ = 𝐌₁} {𝐌₂ = 𝐌₂}
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
  Are-preserving-type-restrictions R₁ R₂
    linear-or-affine→affine linear-or-affine→affine →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω linear-or-affine 𝐌₁ R₁)
    (second-ΠΣ-quantities-𝟘-or-ω affineModality 𝐌₂ R₂)
    linear-or-affine→affine linear-or-affine→affine
linear-or-affine→affine-preserves-second-ΠΣ-quantities-𝟘-or-ω {𝐌₁} {𝐌₂} =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    {𝐌₁ = 𝐌₁} {𝐌₂ = 𝐌₂}
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
  Are-reflecting-type-restrictions R₁ R₂
    linear-or-affine→affine linear-or-affine→affine →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω linear-or-affine 𝐌₁ R₁)
    (second-ΠΣ-quantities-𝟘-or-ω affineModality 𝐌₂ R₂)
    linear-or-affine→affine linear-or-affine→affine
linear-or-affine→affine-reflects-second-ΠΣ-quantities-𝟘-or-ω {𝐌₁} {𝐌₂} =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    {𝐌₁ = 𝐌₁} {𝐌₂ = 𝐌₂}
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
  let 𝕄₁ = affineModality
      𝕄₂ = linearityModality
  in
  (R₂ : Type-restrictions 𝕄₂) →
  ¬ Are-preserving-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ 𝐌₁ (no-type-restrictions 𝕄₁ 𝐌₁ b₁ b₂))
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ 𝐌₂ R₂)
      affine→linearity affine→linearity
¬-affine→linearity-preserves-second-ΠΣ-quantities-𝟘-or-ω _ r =
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
  let 𝕄₁ = affineModality
      𝕄₂ = linearityModality
  in
  (R₁ : Type-restrictions 𝕄₁) →
  ¬ Are-reflecting-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ 𝐌₁ R₁)
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ 𝐌₂ (no-type-restrictions 𝕄₂ 𝐌₂ b₁ b₂))
      affine→linearity affine→linearity
¬-affine→linearity-reflects-second-ΠΣ-quantities-𝟘-or-ω _ r =
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
  let 𝕄₁ = affineModality
      𝕄₂ = linearityModality
  in
  (R₂ : Type-restrictions 𝕄₂) →
  ¬ Are-preserving-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ 𝐌₁ (no-type-restrictions 𝕄₁ 𝐌₁ b₁ b₂))
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ 𝐌₂ R₂)
      affine→linearity affine→linearity-Σ
¬-affine→linearity-Σ-preserves-second-ΠΣ-quantities-𝟘-or-ω _ r =
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
  let 𝕄₁ = affineModality
      𝕄₂ = linearityModality
  in
  (R₁ : Type-restrictions 𝕄₁) →
  ¬ Are-reflecting-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ 𝐌₁ R₁)
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ 𝐌₂ (no-type-restrictions 𝕄₂ 𝐌₂ b₁ b₂))
      affine→linearity affine→linearity-Σ
¬-affine→linearity-Σ-reflects-second-ΠΣ-quantities-𝟘-or-ω _ r =
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
  Are-preserving-type-restrictions R₁ R₂
    linearity→affine linearity→affine →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω linearityModality 𝐌₁ R₁)
    (second-ΠΣ-quantities-𝟘-or-ω affineModality 𝐌₂ R₂)
    linearity→affine linearity→affine
linearity→affine-preserves-second-ΠΣ-quantities-𝟘-or-ω {𝐌₁} {𝐌₂} =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    {𝐌₁ = 𝐌₁} {𝐌₂ = 𝐌₂}
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
  Are-reflecting-type-restrictions R₁ R₂
    linearity→affine linearity→affine →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω linearityModality 𝐌₁ R₁)
    (second-ΠΣ-quantities-𝟘-or-ω affineModality 𝐌₂ R₂)
    linearity→affine linearity→affine
linearity→affine-reflects-second-ΠΣ-quantities-𝟘-or-ω {𝐌₁} {𝐌₂} =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    {𝐌₁ = 𝐌₁} {𝐌₂ = 𝐌₂}
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

------------------------------------------------------------------------
-- Some lemmas related to strong-types-restricted and concrete
-- translation functions

opaque

  -- If the function unit→erasure preserves certain type restrictions,
  -- then it also does this for certain type restrictions obtained
  -- using strong-types-restricted.

  unit→erasure-preserves-strong-types-restricted :
    Are-preserving-type-restrictions
      R₁ R₂ unit→erasure unit→erasure →
    Are-preserving-type-restrictions
      (strong-types-restricted UnitModality 𝐌₁ R₁)
      (strong-types-restricted ErasureModality 𝐌₂ R₂)
      unit→erasure unit→erasure
  unit→erasure-preserves-strong-types-restricted =
    Are-preserving-type-restrictions-strong-types-restricted refl

opaque

  -- If the function unit→erasure reflects certain type restrictions,
  -- then it also does this for certain type restrictions obtained
  -- using strong-types-restricted.

  unit→erasure-reflects-strong-types-restricted :
    Are-reflecting-type-restrictions
      R₁ R₂ unit→erasure unit→erasure →
    Are-reflecting-type-restrictions
      (strong-types-restricted UnitModality 𝐌₁ R₁)
      (strong-types-restricted ErasureModality 𝐌₂ R₂)
      unit→erasure unit→erasure
  unit→erasure-reflects-strong-types-restricted =
    Are-reflecting-type-restrictions-strong-types-restricted
      (λ _ → refl)
      (λ ())

opaque

  -- If the function erasure→unit preserves certain type restrictions,
  -- then it also does this for certain type restrictions obtained
  -- using strong-types-restricted.

  erasure→unit-preserves-strong-types-restricted :
    Are-preserving-type-restrictions
      R₁ R₂ erasure→unit erasure→unit →
    Are-preserving-type-restrictions
      (strong-types-restricted ErasureModality 𝐌₁ R₁)
      (strong-types-restricted UnitModality 𝐌₂ R₂)
      erasure→unit erasure→unit
  erasure→unit-preserves-strong-types-restricted =
    Are-preserving-type-restrictions-strong-types-restricted refl

opaque

  -- The function erasure→unit does not reflect certain type
  -- restrictions obtained using strong-types-restricted.

  ¬-erasure→unit-reflects-strong-types-restricted :
    let 𝕄₁ = ErasureModality
        𝕄₂ = UnitModality
    in
    (R₁ : Type-restrictions 𝕄₁) →
    ¬ Are-reflecting-type-restrictions
        (strong-types-restricted 𝕄₁ 𝐌₁ R₁)
        (strong-types-restricted 𝕄₂ 𝐌₂ (no-type-restrictions 𝕄₂ 𝐌₂ b₁ b₂))
        erasure→unit erasure→unit
  ¬-erasure→unit-reflects-strong-types-restricted _ r =
    case
      ΠΣ-reflected {b = BMΣ 𝕤} {p = 𝟘} {q = 𝟘} (_ , (λ _ → refl))
        .proj₂ refl
    of λ ()
    where
    open Are-reflecting-type-restrictions r

opaque

  -- The function erasure→zero-one-many does not preserve certain type
  -- restrictions obtained using strong-types-restricted.

  ¬-erasure→zero-one-many-preserves-strong-types-restricted :
    let 𝕄₁ = ErasureModality
        𝕄₂ = zero-one-many-modality 𝟙≤𝟘
    in
    (R₂ : Type-restrictions 𝕄₂) →
    ¬ Are-preserving-type-restrictions
        (strong-types-restricted 𝕄₁ 𝐌₁ (no-type-restrictions 𝕄₁ 𝐌₁ b₁ b₂))
        (strong-types-restricted 𝕄₂ 𝐌₂ R₂)
        erasure→zero-one-many erasure→zero-one-many
  ¬-erasure→zero-one-many-preserves-strong-types-restricted _ r =
    case
      ΠΣ-preserved {b = BMΣ 𝕤} {p = ω} {q = 𝟘} (_ , (λ _ → refl))
        .proj₂ refl
    of λ ()
    where
    open Are-preserving-type-restrictions r

opaque

  -- If the function erasure→zero-one-many reflects certain type
  -- restrictions, then the function reflects certain type
  -- restrictions obtained using strong-types-restricted.

  erasure→zero-one-many-reflects-strong-types-restricted :
    Are-reflecting-type-restrictions R₁ R₂
      erasure→zero-one-many erasure→zero-one-many →
    Are-reflecting-type-restrictions
      (strong-types-restricted ErasureModality 𝐌₁ R₁)
      (strong-types-restricted (zero-one-many-modality 𝟙≤𝟘) 𝐌₂ R₂)
      erasure→zero-one-many erasure→zero-one-many
  erasure→zero-one-many-reflects-strong-types-restricted =
    Are-reflecting-type-restrictions-strong-types-restricted
      (λ where
         {p = 𝟘} ()
         {p = ω} ())
      (λ ())

opaque

  -- If the functions erasure→zero-one-many and
  -- erasure→zero-one-many-Σ preserve certain type restrictions, then
  -- the functions preserve certain type restrictions obtained using
  -- strong-types-restricted.

  erasure→zero-one-many-Σ-preserves-strong-types-restricted :
    Are-preserving-type-restrictions R₁ R₂
      erasure→zero-one-many erasure→zero-one-many-Σ →
    Are-preserving-type-restrictions
      (strong-types-restricted ErasureModality 𝐌₁ R₁)
      (strong-types-restricted (zero-one-many-modality 𝟙≤𝟘) 𝐌₂ R₂)
      erasure→zero-one-many erasure→zero-one-many-Σ
  erasure→zero-one-many-Σ-preserves-strong-types-restricted =
    Are-preserving-type-restrictions-strong-types-restricted refl

opaque

  -- If the functions erasure→zero-one-many and
  -- erasure→zero-one-many-Σ reflect certain type restrictions, then
  -- the functions reflect certain type restrictions obtained using
  -- strong-types-restricted.

  erasure→zero-one-many-Σ-reflects-strong-types-restricted :
    Are-reflecting-type-restrictions R₁ R₂
      erasure→zero-one-many erasure→zero-one-many-Σ →
    Are-reflecting-type-restrictions
      (strong-types-restricted ErasureModality 𝐌₁ R₁)
      (strong-types-restricted (zero-one-many-modality 𝟙≤𝟘) 𝐌₂ R₂)
      erasure→zero-one-many erasure→zero-one-many-Σ
  erasure→zero-one-many-Σ-reflects-strong-types-restricted =
    Are-reflecting-type-restrictions-strong-types-restricted
      (λ where
         {p = ω} refl → refl
         {p = 𝟘} ())
      (λ ())

opaque

  -- If the function zero-one-many→erasure preserves certain type
  -- restrictions, then it also does this for certain type
  -- restrictions obtained using strong-types-restricted.

  zero-one-many→erasure-preserves-strong-types-restricted :
    Are-preserving-type-restrictions
      R₁ R₂ zero-one-many→erasure zero-one-many→erasure →
    Are-preserving-type-restrictions
      (strong-types-restricted (zero-one-many-modality 𝟙≤𝟘) 𝐌₁ R₁)
      (strong-types-restricted ErasureModality 𝐌₂ R₂)
      zero-one-many→erasure zero-one-many→erasure
  zero-one-many→erasure-preserves-strong-types-restricted =
    Are-preserving-type-restrictions-strong-types-restricted refl

opaque

  -- The function zero-one-many→erasure does not reflect certain type
  -- restrictions obtained using strong-types-restricted.

  ¬-zero-one-many→erasure-reflects-strong-types-restricted :
    let 𝕄₁ = zero-one-many-modality 𝟙≤𝟘
        𝕄₂ = ErasureModality
    in
    (R₁ : Type-restrictions 𝕄₁) →
    ¬ Are-reflecting-type-restrictions
        (strong-types-restricted 𝕄₁ 𝐌₁ R₁)
        (strong-types-restricted 𝕄₂ 𝐌₂ (no-type-restrictions 𝕄₂ 𝐌₂ b₁ b₂))
        zero-one-many→erasure zero-one-many→erasure
  ¬-zero-one-many→erasure-reflects-strong-types-restricted _ r =
    case
      ΠΣ-reflected {b = BMΣ 𝕤} {p = ω} {q = ω} (_ , (λ _ → refl))
        .proj₂ refl
    of λ ()
    where
    open Are-reflecting-type-restrictions r

opaque

  -- If the function linearity→linear-or-affine preserves certain type
  -- restrictions, then the function preserves certain type
  -- restrictions obtained using strong-types-restricted.

  linearity→linear-or-affine-preserves-strong-types-restricted :
    Are-preserving-type-restrictions R₁ R₂
      linearity→linear-or-affine linearity→linear-or-affine →
    Are-preserving-type-restrictions
      (strong-types-restricted linearityModality 𝐌₁ R₁)
      (strong-types-restricted linear-or-affine 𝐌₂ R₂)
      linearity→linear-or-affine linearity→linear-or-affine
  linearity→linear-or-affine-preserves-strong-types-restricted =
    Are-preserving-type-restrictions-strong-types-restricted refl

opaque

  -- If the function linearity→linear-or-affine reflects certain type
  -- restrictions, then the function reflects certain type
  -- restrictions obtained using strong-types-restricted.

  linearity→linear-or-affine-reflects-strong-types-restricted :
    Are-reflecting-type-restrictions R₁ R₂
      linearity→linear-or-affine linearity→linear-or-affine →
    Are-reflecting-type-restrictions
      (strong-types-restricted linearityModality 𝐌₁ R₁)
      (strong-types-restricted linear-or-affine 𝐌₂ R₂)
      linearity→linear-or-affine linearity→linear-or-affine
  linearity→linear-or-affine-reflects-strong-types-restricted =
    Are-reflecting-type-restrictions-strong-types-restricted
      (λ where
         {p = 𝟙} refl → refl
         {p = 𝟘} ()
         {p = ω} ())
      (λ ())

opaque

  -- If the function linearity→linear-or-affine preserves certain type
  -- restrictions, then the function preserves certain type
  -- restrictions obtained using strong-types-restricted.

  linear-or-affine→linearity-preserves-strong-types-restricted :
    Are-preserving-type-restrictions R₁ R₂
      linear-or-affine→linearity linear-or-affine→linearity →
    Are-preserving-type-restrictions
      (strong-types-restricted linear-or-affine 𝐌₁ R₁)
      (strong-types-restricted linearityModality 𝐌₂ R₂)
      linear-or-affine→linearity linear-or-affine→linearity
  linear-or-affine→linearity-preserves-strong-types-restricted =
    Are-preserving-type-restrictions-strong-types-restricted refl

opaque

  -- If the function linearity→linear-or-affine reflects certain type
  -- restrictions, then the function reflects certain type
  -- restrictions obtained using strong-types-restricted.

  linear-or-affine→linearity-reflects-strong-types-restricted :
    Are-reflecting-type-restrictions R₁ R₂
      linear-or-affine→linearity linear-or-affine→linearity →
    Are-reflecting-type-restrictions
      (strong-types-restricted linear-or-affine 𝐌₁ R₁)
      (strong-types-restricted linearityModality 𝐌₂ R₂)
      linear-or-affine→linearity linear-or-affine→linearity
  linear-or-affine→linearity-reflects-strong-types-restricted =
    Are-reflecting-type-restrictions-strong-types-restricted
      (λ where
         {p = 𝟙}  refl → refl
         {p = 𝟘}  ()
         {p = ≤𝟙} ()
         {p = ≤ω} ())
      (λ ())

opaque

  -- The function affine→linear-or-affine does not preserve certain
  -- type restrictions obtained using strong-types-restricted.

  ¬-affine→linear-or-affine-preserves-strong-types-restricted :
    let 𝕄₁ = affineModality
        𝕄₂ = linear-or-affine
    in
    (R₂ : Type-restrictions 𝕄₂) →
    ¬ Are-preserving-type-restrictions
        (strong-types-restricted 𝕄₁ 𝐌₁ (no-type-restrictions 𝕄₁ 𝐌₁ b₁ b₂))
        (strong-types-restricted 𝕄₂ 𝐌₂ R₂)
        affine→linear-or-affine affine→linear-or-affine
  ¬-affine→linear-or-affine-preserves-strong-types-restricted _ r =
    case
      ΠΣ-preserved {b = BMΣ 𝕤} {p = 𝟙} {q = 𝟙} (_ , (λ _ → refl))
        .proj₂ refl
    of λ ()
    where
    open Are-preserving-type-restrictions r

opaque

  -- If the function affine→linear-or-affine reflects certain type
  -- restrictions, then the function reflects certain type
  -- restrictions obtained using strong-types-restricted.

  affine→linear-or-affine-reflects-strong-types-restricted :
    Are-reflecting-type-restrictions R₁ R₂
      affine→linear-or-affine affine→linear-or-affine →
    Are-reflecting-type-restrictions
      (strong-types-restricted affineModality 𝐌₁ R₁)
      (strong-types-restricted linear-or-affine 𝐌₂ R₂)
      affine→linear-or-affine affine→linear-or-affine
  affine→linear-or-affine-reflects-strong-types-restricted =
    Are-reflecting-type-restrictions-strong-types-restricted
      (λ where
         {p = 𝟘} ()
         {p = 𝟙} ()
         {p = ω} ())
      (λ ())

opaque

  -- If the functions affine→linear-or-affine and
  -- affine→linear-or-affine-Σ preserve certain type restrictions,
  -- then the functions preserve certain type restrictions obtained
  -- using strong-types-restricted.

  affine→linear-or-affine-Σ-preserves-strong-types-restricted :
    Are-preserving-type-restrictions R₁ R₂
      affine→linear-or-affine affine→linear-or-affine-Σ →
    Are-preserving-type-restrictions
      (strong-types-restricted affineModality 𝐌₁ R₁)
      (strong-types-restricted linear-or-affine 𝐌₂ R₂)
      affine→linear-or-affine affine→linear-or-affine-Σ
  affine→linear-or-affine-Σ-preserves-strong-types-restricted =
    Are-preserving-type-restrictions-strong-types-restricted refl

opaque

  -- If the functions affine→linear-or-affine and
  -- affine→linear-or-affine-Σ reflect certain type restrictions, then
  -- the functions reflect certain type restrictions obtained using
  -- strong-types-restricted.

  affine→linear-or-affine-Σ-reflects-strong-types-restricted :
    Are-reflecting-type-restrictions R₁ R₂
      affine→linear-or-affine affine→linear-or-affine-Σ →
    Are-reflecting-type-restrictions
      (strong-types-restricted affineModality 𝐌₁ R₁)
      (strong-types-restricted linear-or-affine 𝐌₂ R₂)
      affine→linear-or-affine affine→linear-or-affine-Σ
  affine→linear-or-affine-Σ-reflects-strong-types-restricted =
    Are-reflecting-type-restrictions-strong-types-restricted
      (λ where
         {p = 𝟙} refl → refl
         {p = 𝟘} ()
         {p = ω} ())
      (λ ())

opaque

  -- If the function linear-or-affine→affine preserves certain type
  -- restrictions, then the function preserves certain type
  -- restrictions obtained using strong-types-restricted.

  linear-or-affine→affine-preserves-strong-types-restricted :
    Are-preserving-type-restrictions R₁ R₂
      linear-or-affine→affine linear-or-affine→affine →
    Are-preserving-type-restrictions
      (strong-types-restricted linear-or-affine 𝐌₁ R₁)
      (strong-types-restricted affineModality 𝐌₂ R₂)
      linear-or-affine→affine linear-or-affine→affine
  linear-or-affine→affine-preserves-strong-types-restricted =
    Are-preserving-type-restrictions-strong-types-restricted refl

opaque

  -- The function linear-or-affine→affine does not reflect certain
  -- type restrictions obtained using strong-types-restricted.

  ¬-linear-or-affine→affine-reflects-strong-types-restricted :
    let 𝕄₁ = linear-or-affine
        𝕄₂ = affineModality
    in
    (R₁ : Type-restrictions 𝕄₁) →
    ¬ Are-reflecting-type-restrictions
        (strong-types-restricted 𝕄₁ 𝐌₁ R₁)
        (strong-types-restricted 𝕄₂ 𝐌₂ (no-type-restrictions 𝕄₂ 𝐌₂ b₁ b₂))
        linear-or-affine→affine linear-or-affine→affine
  ¬-linear-or-affine→affine-reflects-strong-types-restricted _ r =
    case
      ΠΣ-reflected {b = BMΣ 𝕤} {p = ≤𝟙} {q = ≤𝟙} (_ , (λ _ → refl))
        .proj₂ refl
    of λ ()
    where
    open Are-reflecting-type-restrictions r

opaque

  -- The function affine→linearity does not preserve certain type
  -- restrictions obtained using strong-types-restricted.

  ¬-affine→linearity-preserves-strong-types-restricted :
    let 𝕄₁ = affineModality
        𝕄₂ = linearityModality
    in
    (R₂ : Type-restrictions 𝕄₂) →
    ¬ Are-preserving-type-restrictions
        (strong-types-restricted 𝕄₁ 𝐌₁ (no-type-restrictions 𝕄₁ 𝐌₁ b₁ b₂))
        (strong-types-restricted 𝕄₂ 𝐌₂ R₂)
        affine→linearity affine→linearity
  ¬-affine→linearity-preserves-strong-types-restricted _ r =
    case
      ΠΣ-preserved {b = BMΣ 𝕤} {p = 𝟙} {q = 𝟙} (_ , (λ _ → refl))
        .proj₂ refl
    of λ ()
    where
    open Are-preserving-type-restrictions r

opaque

  -- If the function affine→linearity reflects certain type
  -- restrictions, then the function reflects certain type
  -- restrictions obtained using strong-types-restricted.

  affine→linearity-reflects-strong-types-restricted :
    Are-reflecting-type-restrictions R₁ R₂
      affine→linearity affine→linearity →
    Are-reflecting-type-restrictions
      (strong-types-restricted affineModality 𝐌₁ R₁)
      (strong-types-restricted linearityModality 𝐌₂ R₂)
      affine→linearity affine→linearity
  affine→linearity-reflects-strong-types-restricted =
    Are-reflecting-type-restrictions-strong-types-restricted
      (λ where
         {p = 𝟘} ()
         {p = 𝟙} ()
         {p = ω} ())
      (λ ())

opaque

  -- If the functions affine→linearity and affine→linearity-Σ preserve
  -- certain type restrictions, then the functions preserve certain
  -- type restrictions obtained using strong-types-restricted.

  affine→linearity-Σ-preserves-strong-types-restricted :
    Are-preserving-type-restrictions R₁ R₂
      affine→linearity affine→linearity-Σ →
    Are-preserving-type-restrictions
      (strong-types-restricted affineModality 𝐌₁ R₁)
      (strong-types-restricted linearityModality 𝐌₂ R₂)
      affine→linearity affine→linearity-Σ
  affine→linearity-Σ-preserves-strong-types-restricted =
    Are-preserving-type-restrictions-strong-types-restricted refl

opaque

  -- If the functions affine→linearity and affine→linearity-Σ reflect
  -- certain type restrictions, then the functions reflect certain
  -- type restrictions obtained using strong-types-restricted.

  affine→linearity-Σ-reflects-strong-types-restricted :
    Are-reflecting-type-restrictions R₁ R₂
      affine→linearity affine→linearity-Σ →
    Are-reflecting-type-restrictions
      (strong-types-restricted affineModality 𝐌₁ R₁)
      (strong-types-restricted linearityModality 𝐌₂ R₂)
      affine→linearity affine→linearity-Σ
  affine→linearity-Σ-reflects-strong-types-restricted =
    Are-reflecting-type-restrictions-strong-types-restricted
      (λ where
         {p = 𝟙} refl → refl
         {p = 𝟘} ()
         {p = ω} ())
      (λ ())

opaque

  -- If the function linearity→affine preserves certain type
  -- restrictions, then the function preserves certain type
  -- restrictions obtained using strong-types-restricted.

  linearity→affine-preserves-strong-types-restricted :
    Are-preserving-type-restrictions R₁ R₂
      linearity→affine linearity→affine →
    Are-preserving-type-restrictions
      (strong-types-restricted linearityModality 𝐌₁ R₁)
      (strong-types-restricted affineModality 𝐌₂ R₂)
      linearity→affine linearity→affine
  linearity→affine-preserves-strong-types-restricted =
    Are-preserving-type-restrictions-strong-types-restricted refl

opaque

  -- If the function linearity→affine reflects certain type
  -- restrictions, then the function reflects certain type
  -- restrictions obtained using strong-types-restricted.

  linearity→affine-reflects-strong-types-restricted :
    Are-reflecting-type-restrictions R₁ R₂
      linearity→affine linearity→affine →
    Are-reflecting-type-restrictions
      (strong-types-restricted linearityModality 𝐌₁ R₁)
      (strong-types-restricted affineModality 𝐌₂ R₂)
      linearity→affine linearity→affine
  linearity→affine-reflects-strong-types-restricted =
    Are-reflecting-type-restrictions-strong-types-restricted
      (λ where
         {p = 𝟙} refl → refl
         {p = 𝟘} ()
         {p = ω} ())
      (λ ())
