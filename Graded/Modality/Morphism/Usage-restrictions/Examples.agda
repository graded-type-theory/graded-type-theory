------------------------------------------------------------------------
-- Lemmas related to
-- Are-preserving-usage-restrictions/Are-reflecting-usage-restrictions
-- and specific usage restriction transformers (at the time of writing
-- only one, no-erased-matches)
------------------------------------------------------------------------

module Graded.Modality.Morphism.Usage-restrictions.Examples where

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

open import Graded.Modality
open import Graded.Modality.Morphism.Examples
open import Graded.Modality.Morphism.Usage-restrictions
open import Graded.Modality.Instances.Affine
  using (affineModality)
open import Graded.Modality.Instances.Erasure
  using (𝟘)
open import Graded.Modality.Instances.Erasure.Modality
  using (ErasureModality)
open import Graded.Modality.Instances.Linear-or-affine
  using (𝟘; linear-or-affine)
open import Graded.Modality.Instances.Linearity
  using (linearityModality)
open import Graded.Modality.Instances.Unit using (UnitModality)
open import Graded.Modality.Instances.Zero-one-many
  using (𝟘; zero-one-many-modality)
open import Graded.Restrictions
open import Graded.Usage.Restrictions

private variable
  𝟙≤𝟘     : Bool
  R R₁ R₂ : Usage-restrictions _
  M₁ M₂   : Set _
  tr tr-Σ : M₁ → M₂

------------------------------------------------------------------------
-- Preserving/reflecting certain usage restrictions

-- If the functions tr and tr-Σ preserve certain usage restrictions,
-- then they also do this for certain usage restrictions obtained
-- using no-erased-matches, given that a certain assumption holds.

Are-preserving-usage-restrictions-no-erased-matches :
  ∀ 𝕄₁ 𝕄₂ →
  (Modality.𝟙 𝕄₂ ≢ Modality.𝟘 𝕄₂ →
   Modality.𝟙 𝕄₁ ≢ Modality.𝟘 𝕄₁ ×
   (∀ {p} → tr p ≡ Modality.𝟘 𝕄₂ → p ≡ Modality.𝟘 𝕄₁) ⊎
   (∀ {p} → tr p ≢ Modality.𝟘 𝕄₂)) →
  Are-preserving-usage-restrictions R₁ R₂ tr tr-Σ →
  Are-preserving-usage-restrictions
    (no-erased-matches 𝕄₁ R₁)
    (no-erased-matches 𝕄₂ R₂)
    tr tr-Σ
Are-preserving-usage-restrictions-no-erased-matches
  {tr = tr} 𝕄₁ 𝕄₂ hyp r = record
  { Prodrec-preserved = λ {r = r} (p , ≢𝟘) →
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
  open Are-preserving-usage-restrictions r

-- If the functions tr and tr-Σ reflect certain usage restrictions,
-- then they also do this for certain usage restrictions obtained
-- using no-erased-matches, given that a certain assumption holds.

Are-reflecting-usage-restrictions-no-erased-matches :
  ∀ 𝕄₁ 𝕄₂ →
  (Modality.𝟙 𝕄₁ ≢ Modality.𝟘 𝕄₁ →
   Modality.𝟙 𝕄₂ ≢ Modality.𝟘 𝕄₂ ×
   (∀ {p} → p ≡ Modality.𝟘 𝕄₁ → tr p ≡ Modality.𝟘 𝕄₂)) →
  Are-reflecting-usage-restrictions R₁ R₂ tr tr-Σ →
  Are-reflecting-usage-restrictions
    (no-erased-matches 𝕄₁ R₁)
    (no-erased-matches 𝕄₂ R₂)
    tr tr-Σ
Are-reflecting-usage-restrictions-no-erased-matches
  {tr = tr} 𝕄₁ 𝕄₂ hyp r = record
  { Prodrec-reflected = λ {r = r} (p , ≢𝟘) →
        Prodrec-reflected p
      , (λ 𝟙≢𝟘 →
           r ≡ M₁.𝟘     →⟨ hyp 𝟙≢𝟘 .proj₂ ⟩
           tr r ≡ M₂.𝟘  →⟨ ≢𝟘 (hyp 𝟙≢𝟘 .proj₁) ⟩
           ⊥            □)
  }
  where
  module M₁ = Modality 𝕄₁
  module M₂ = Modality 𝕄₂
  open Are-reflecting-usage-restrictions r

------------------------------------------------------------------------
-- Some lemmas related to no-erased-matches and concrete translation
-- functions

-- If the functions unit→erasure and tr preserve certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches.

unit→erasure-preserves-no-erased-matches :
  ∀ v₁ v₁-ok v₂ →
  Are-preserving-usage-restrictions R₁ R₂ unit→erasure tr →
  Are-preserving-usage-restrictions
    (no-erased-matches (UnitModality v₁ v₁-ok) R₁)
    (no-erased-matches (ErasureModality v₂) R₂)
    unit→erasure tr
unit→erasure-preserves-no-erased-matches v₁ v₁-ok v₂ =
  Are-preserving-usage-restrictions-no-erased-matches
    (UnitModality v₁ v₁-ok)
    (ErasureModality v₂)
    (λ _ → inj₂ (λ ()))

-- If the functions unit→erasure and tr reflect certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches.

unit→erasure-reflects-no-erased-matches :
  ∀ v₁ v₁-ok v₂ →
  Are-reflecting-usage-restrictions R₁ R₂ unit→erasure tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches (UnitModality v₁ v₁-ok) R₁)
    (no-erased-matches (ErasureModality v₂) R₂)
    unit→erasure tr
unit→erasure-reflects-no-erased-matches v₁ v₁-ok v₂ =
  Are-reflecting-usage-restrictions-no-erased-matches
    (UnitModality v₁ v₁-ok)
    (ErasureModality v₂)
    (λ tt≢tt → ⊥-elim $ tt≢tt refl)

-- If the functions erasure→unit and tr preserve certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches.

erasure→unit-preserves-no-erased-matches :
  ∀ v₁ v₂ v₂-ok →
  Are-preserving-usage-restrictions R₁ R₂ erasure→unit tr →
  Are-preserving-usage-restrictions
    (no-erased-matches (ErasureModality v₁) R₁)
    (no-erased-matches (UnitModality v₂ v₂-ok) R₂)
    erasure→unit tr
erasure→unit-preserves-no-erased-matches v₁ v₂ v₂-ok =
  Are-preserving-usage-restrictions-no-erased-matches
    (ErasureModality v₁)
    (UnitModality v₂ v₂-ok)
    (λ tt≢tt → ⊥-elim $ tt≢tt refl)

-- The functions erasure→unit and tr do not reflect certain usage
-- restrictions obtained using no-erased-matches.

¬-erasure→unit-reflects-no-erased-matches :
  ∀ v₁ v₂ v₂-ok →
  ¬ Are-reflecting-usage-restrictions
      (no-erased-matches (ErasureModality v₁) R)
      (no-erased-matches (UnitModality v₂ v₂-ok) no-usage-restrictions)
      erasure→unit tr
¬-erasure→unit-reflects-no-erased-matches _ _ _ r =
  Prodrec-reflected {r = 𝟘} {p = 𝟘} {q = 𝟘} (_ , idᶠ) .proj₂ (λ ()) refl
  where
  open Are-reflecting-usage-restrictions r

-- If the functions erasure→zero-one-many and tr preserve certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches.

erasure→zero-one-many-preserves-no-erased-matches :
  ∀ v₁ v₂ →
  Are-preserving-usage-restrictions R₁ R₂
    erasure→zero-one-many tr →
  Are-preserving-usage-restrictions
    (no-erased-matches (ErasureModality v₁) R₁)
    (no-erased-matches (zero-one-many-modality 𝟙≤𝟘 v₂) R₂)
    erasure→zero-one-many tr
erasure→zero-one-many-preserves-no-erased-matches v₁ v₂ =
  Are-preserving-usage-restrictions-no-erased-matches
    (ErasureModality v₁)
    (zero-one-many-modality _ v₂)
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions erasure→zero-one-many and tr reflect certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches.

erasure→zero-one-many-reflects-no-erased-matches :
  ∀ v₁ v₂ →
  Are-reflecting-usage-restrictions R₁ R₂
    erasure→zero-one-many tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches (ErasureModality v₁) R₁)
    (no-erased-matches (zero-one-many-modality 𝟙≤𝟘 v₂) R₂)
    erasure→zero-one-many tr
erasure→zero-one-many-reflects-no-erased-matches v₁ v₂ =
  Are-reflecting-usage-restrictions-no-erased-matches
    (ErasureModality v₁)
    (zero-one-many-modality _ v₂)
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))

-- If the functions zero-one-many→erasure and tr preserve certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches.

zero-one-many→erasure-preserves-no-erased-matches :
  ∀ v₁ v₂ →
  Are-preserving-usage-restrictions R₁ R₂
    zero-one-many→erasure tr →
  Are-preserving-usage-restrictions
    (no-erased-matches (zero-one-many-modality 𝟙≤𝟘 v₁) R₁)
    (no-erased-matches (ErasureModality v₂) R₂)
    zero-one-many→erasure tr
zero-one-many→erasure-preserves-no-erased-matches v₁ v₂ =
  Are-preserving-usage-restrictions-no-erased-matches
    (zero-one-many-modality _ v₁)
    (ErasureModality v₂)
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions zero-one-many→erasure and tr reflect certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches.

zero-one-many→erasure-reflects-no-erased-matches :
  ∀ v₁ v₂ →
  Are-reflecting-usage-restrictions R₁ R₂
    zero-one-many→erasure tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches (zero-one-many-modality 𝟙≤𝟘 v₁) R₁)
    (no-erased-matches (ErasureModality v₂) R₂)
    zero-one-many→erasure tr
zero-one-many→erasure-reflects-no-erased-matches v₁ v₂ =
  Are-reflecting-usage-restrictions-no-erased-matches
    (zero-one-many-modality _ v₁)
    (ErasureModality v₂)
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))

-- If the functions linearity→linear-or-affine and tr preserve certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches.

linearity→linear-or-affine-preserves-no-erased-matches :
  ∀ v₁ v₂ →
  Are-preserving-usage-restrictions R₁ R₂
    linearity→linear-or-affine tr →
  Are-preserving-usage-restrictions
    (no-erased-matches (linearityModality v₁) R₁)
    (no-erased-matches (linear-or-affine v₂) R₂)
    linearity→linear-or-affine tr
linearity→linear-or-affine-preserves-no-erased-matches v₁ v₂ =
  Are-preserving-usage-restrictions-no-erased-matches
    (linearityModality v₁)
    (linear-or-affine v₂)
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions linearity→linear-or-affine and tr reflect certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches.

linearity→linear-or-affine-reflects-no-erased-matches :
  ∀ v₁ v₂ →
  Are-reflecting-usage-restrictions R₁ R₂
    linearity→linear-or-affine tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches (linearityModality v₁) R₁)
    (no-erased-matches (linear-or-affine v₂) R₂)
    linearity→linear-or-affine tr
linearity→linear-or-affine-reflects-no-erased-matches v₁ v₂ =
  Are-reflecting-usage-restrictions-no-erased-matches
    (linearityModality v₁)
    (linear-or-affine v₂)
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))

-- If the functions linear-or-affine→linearity and tr preserve certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches.

linear-or-affine→linearity-preserves-no-erased-matches :
  ∀ v₁ v₂ →
  Are-preserving-usage-restrictions R₁ R₂
    linear-or-affine→linearity tr →
  Are-preserving-usage-restrictions
    (no-erased-matches (linear-or-affine v₁) R₁)
    (no-erased-matches (linearityModality v₂) R₂)
    linear-or-affine→linearity tr
linear-or-affine→linearity-preserves-no-erased-matches v₁ v₂ =
  Are-preserving-usage-restrictions-no-erased-matches
    (linear-or-affine v₁)
    (linearityModality v₂)
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions linear-or-affine→linearity and tr reflect certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches.

linear-or-affine→linearity-reflects-no-erased-matches :
  ∀ v₁ v₂ →
  Are-reflecting-usage-restrictions R₁ R₂
    linear-or-affine→linearity tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches (linear-or-affine v₁) R₁)
    (no-erased-matches (linearityModality v₂) R₂)
    linear-or-affine→linearity tr
linear-or-affine→linearity-reflects-no-erased-matches v₁ v₂ =
  Are-reflecting-usage-restrictions-no-erased-matches
    (linear-or-affine v₁)
    (linearityModality v₂)
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))

-- If the functions affine→linear-or-affine and tr preserve certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches.

affine→linear-or-affine-preserves-no-erased-matches :
  ∀ v₁ v₂ →
  Are-preserving-usage-restrictions R₁ R₂
    affine→linear-or-affine tr →
  Are-preserving-usage-restrictions
    (no-erased-matches (affineModality v₁) R₁)
    (no-erased-matches (linear-or-affine v₂) R₂)
    affine→linear-or-affine tr
affine→linear-or-affine-preserves-no-erased-matches v₁ v₂ =
  Are-preserving-usage-restrictions-no-erased-matches
    (affineModality v₁)
    (linear-or-affine v₂)
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions affine→linear-or-affine and tr reflect certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches.

affine→linear-or-affine-reflects-no-erased-matches :
  ∀ v₁ v₂ →
  Are-reflecting-usage-restrictions R₁ R₂
    affine→linear-or-affine tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches (affineModality v₁) R₁)
    (no-erased-matches (linear-or-affine v₂) R₂)
    affine→linear-or-affine tr
affine→linear-or-affine-reflects-no-erased-matches v₁ v₂ =
  Are-reflecting-usage-restrictions-no-erased-matches
    (affineModality v₁)
    (linear-or-affine v₂)
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))

-- If the functions linear-or-affine→affine and tr preserve certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches.

linear-or-affine→affine-preserves-no-erased-matches :
  ∀ v₁ v₂ →
  Are-preserving-usage-restrictions R₁ R₂
    linear-or-affine→affine tr →
  Are-preserving-usage-restrictions
    (no-erased-matches (linear-or-affine v₁) R₁)
    (no-erased-matches (affineModality v₂) R₂)
    linear-or-affine→affine tr
linear-or-affine→affine-preserves-no-erased-matches v₁ v₂ =
  Are-preserving-usage-restrictions-no-erased-matches
    (linear-or-affine v₁)
    (affineModality v₂)
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions linear-or-affine→affine and tr reflect certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches.

linear-or-affine→affine-reflects-no-erased-matches :
  ∀ v₁ v₂ →
  Are-reflecting-usage-restrictions R₁ R₂
    linear-or-affine→affine tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches (linear-or-affine v₁) R₁)
    (no-erased-matches (affineModality v₂) R₂)
    linear-or-affine→affine tr
linear-or-affine→affine-reflects-no-erased-matches v₁ v₂ =
  Are-reflecting-usage-restrictions-no-erased-matches
    (linear-or-affine v₁)
    (affineModality v₂)
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))

-- If the functions affine→linearity and tr preserve certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches.

affine→linearity-preserves-no-erased-matches :
  ∀ v₁ v₂ →
  Are-preserving-usage-restrictions R₁ R₂
    affine→linearity tr →
  Are-preserving-usage-restrictions
    (no-erased-matches (affineModality v₁) R₁)
    (no-erased-matches (linearityModality v₂) R₂)
    affine→linearity tr
affine→linearity-preserves-no-erased-matches v₁ v₂ =
  Are-preserving-usage-restrictions-no-erased-matches
    (affineModality v₁)
    (linearityModality v₂)
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions affine→linearity and tr reflect certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches.

affine→linearity-reflects-no-erased-matches :
  ∀ v₁ v₂ →
  Are-reflecting-usage-restrictions R₁ R₂
    affine→linearity tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches (affineModality v₁) R₁)
    (no-erased-matches (linearityModality v₂) R₂)
    affine→linearity tr
affine→linearity-reflects-no-erased-matches v₁ v₂ =
  Are-reflecting-usage-restrictions-no-erased-matches
    (affineModality v₁)
    (linearityModality v₂)
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))

-- If the functions linearity→affine and tr preserve certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches.

linearity→affine-preserves-no-erased-matches :
  ∀ v₁ v₂ →
  Are-preserving-usage-restrictions R₁ R₂
    linearity→affine tr →
  Are-preserving-usage-restrictions
    (no-erased-matches (linearityModality v₁) R₁)
    (no-erased-matches (affineModality v₂) R₂)
    linearity→affine tr
linearity→affine-preserves-no-erased-matches v₁ v₂ =
  Are-preserving-usage-restrictions-no-erased-matches
    (linearityModality v₁)
    (affineModality v₂)
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions linearity→affine and tr reflect certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches.

linearity→affine-reflects-no-erased-matches :
  ∀ v₁ v₂ →
  Are-reflecting-usage-restrictions R₁ R₂
    linearity→affine tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches (linearityModality v₁) R₁)
    (no-erased-matches (affineModality v₂) R₂)
    linearity→affine tr
linearity→affine-reflects-no-erased-matches v₁ v₂ =
  Are-reflecting-usage-restrictions-no-erased-matches
    (linearityModality v₁)
    (affineModality v₂)
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))
