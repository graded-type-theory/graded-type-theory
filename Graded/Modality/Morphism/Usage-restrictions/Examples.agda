------------------------------------------------------------------------
-- Lemmas related to
-- Are-preserving-usage-restrictions/Are-reflecting-usage-restrictions
-- and specific usage restriction transformers (at the time of writing
-- only one, no-erased-matches-UR)
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
open import Graded.Modality.Variant
open import Graded.Restrictions
open import Graded.Usage.Restrictions

private variable
  𝟙≤𝟘 ok  : Bool
  v₂      : Modality-variant _
  R R₁ R₂ : Usage-restrictions _
  A M₁ M₂ : Set _
  tr tr-Σ : M₁ → M₂
  v₂-ok   : A

------------------------------------------------------------------------
-- Preserving/reflecting certain usage restrictions

opaque

  -- If R₁ and R₂ have the same usage restrictions, then this applies
  -- also to no-erased-matches-UR 𝕄₁ R₁ and
  -- no-erased-matches-UR 𝕄₂ R₂.

  Same-usage-restrictions-no-erased-matches-UR :
    ∀ 𝕄₁ 𝕄₂ →
    Same-usage-restrictions R₁ R₂ →
    Same-usage-restrictions
      (no-erased-matches-UR 𝕄₁ R₁)
      (no-erased-matches-UR 𝕄₂ R₂)
  Same-usage-restrictions-no-erased-matches-UR _ _ s = record
    { Id-erased-preserved            = Id-erased-preserved
    ; Erased-matches-for-J-preserved = (λ ()) , (λ ())
    ; Erased-matches-for-K-preserved = (λ ()) , (λ ())
    }
    where
    open Same-usage-restrictions s

-- If the functions tr and tr-Σ preserve certain usage restrictions,
-- then they also do this for certain usage restrictions obtained
-- using no-erased-matches-UR, given that a certain assumption holds.

Are-preserving-usage-restrictions-no-erased-matches-UR :
  ∀ 𝕄₁ 𝕄₂ →
  (¬ Modality.Trivial 𝕄₂ →
   ¬ Modality.Trivial 𝕄₁ ×
   (∀ {p} → tr p ≡ Modality.𝟘 𝕄₂ → p ≡ Modality.𝟘 𝕄₁) ⊎
   (∀ {p} → tr p ≢ Modality.𝟘 𝕄₂)) →
  Are-preserving-usage-restrictions R₁ R₂ tr tr-Σ →
  Are-preserving-usage-restrictions
    (no-erased-matches-UR 𝕄₁ R₁)
    (no-erased-matches-UR 𝕄₂ R₂)
    tr tr-Σ
Are-preserving-usage-restrictions-no-erased-matches-UR
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
  ; Unitrec-preserved = λ {p = p} (P , ≢𝟘) →
        Unitrec-preserved P
      , λ 𝟙≢𝟘 → case hyp 𝟙≢𝟘 of λ where
         (inj₁ (𝟙≢𝟘 , tr-≡-𝟘-→)) →
           tr p ≡ M₂.𝟘  →⟨ tr-≡-𝟘-→ ⟩
           p ≡ M₁.𝟘     →⟨ ≢𝟘 𝟙≢𝟘 ⟩
           ⊥            □
         (inj₂ ≢𝟘) →
           tr p ≡ M₂.𝟘  →⟨ ≢𝟘 ⟩
           ⊥            □

  ; starˢ-sink-preserved = starˢ-sink-preserved
  ; same-usage-restrictions =
      Same-usage-restrictions-no-erased-matches-UR 𝕄₁ 𝕄₂
        same-usage-restrictions
  }
  where
  module M₁ = Modality 𝕄₁
  module M₂ = Modality 𝕄₂
  open Are-preserving-usage-restrictions r

-- If the functions tr and tr-Σ reflect certain usage restrictions,
-- then they also do this for certain usage restrictions obtained
-- using no-erased-matches-UR, given that a certain assumption holds.

Are-reflecting-usage-restrictions-no-erased-matches-UR :
  ∀ 𝕄₁ 𝕄₂ →
  (¬ Modality.Trivial 𝕄₁ →
   ¬ Modality.Trivial 𝕄₂ ×
   (∀ {p} → p ≡ Modality.𝟘 𝕄₁ → tr p ≡ Modality.𝟘 𝕄₂)) →
  Are-reflecting-usage-restrictions R₁ R₂ tr tr-Σ →
  Are-reflecting-usage-restrictions
    (no-erased-matches-UR 𝕄₁ R₁)
    (no-erased-matches-UR 𝕄₂ R₂)
    tr tr-Σ
Are-reflecting-usage-restrictions-no-erased-matches-UR
  {tr = tr} 𝕄₁ 𝕄₂ hyp r = record
  { Prodrec-reflected = λ {r = r} (p , ≢𝟘) →
        Prodrec-reflected p
      , (λ 𝟙≢𝟘 →
           r ≡ M₁.𝟘     →⟨ hyp 𝟙≢𝟘 .proj₂ ⟩
           tr r ≡ M₂.𝟘  →⟨ ≢𝟘 (hyp 𝟙≢𝟘 .proj₁) ⟩
           ⊥            □)
  ; Unitrec-reflected = λ {p = p} (P , ≢𝟘) →
        Unitrec-reflected P
      , λ 𝟙≢𝟘 →
          p ≡ M₁.𝟘     →⟨ hyp 𝟙≢𝟘 .proj₂ ⟩
          tr p ≡ M₂.𝟘  →⟨ ≢𝟘 (hyp 𝟙≢𝟘 .proj₁) ⟩
          ⊥            □

  ; starˢ-sink-reflected = starˢ-sink-reflected
  ; same-usage-restrictions =
      Same-usage-restrictions-no-erased-matches-UR 𝕄₁ 𝕄₂
        same-usage-restrictions
  }
  where
  module M₁ = Modality 𝕄₁
  module M₂ = Modality 𝕄₂
  open Are-reflecting-usage-restrictions r

------------------------------------------------------------------------
-- Some lemmas related to no-erased-matches-UR and concrete
-- translation functions

-- If the functions unit→erasure and tr preserve certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches-UR.

unit→erasure-preserves-no-erased-matches-UR :
  ∀ v₁ v₁-ok v₂ →
  Are-preserving-usage-restrictions R₁ R₂ unit→erasure tr →
  Are-preserving-usage-restrictions
    (no-erased-matches-UR (UnitModality v₁ v₁-ok) R₁)
    (no-erased-matches-UR (ErasureModality v₂) R₂)
    unit→erasure tr
unit→erasure-preserves-no-erased-matches-UR v₁ v₁-ok v₂ =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (UnitModality v₁ v₁-ok)
    (ErasureModality v₂)
    (λ _ → inj₂ (λ ()))

-- If the functions unit→erasure and tr reflect certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches-UR.

unit→erasure-reflects-no-erased-matches-UR :
  ∀ v₁ v₁-ok v₂ →
  Are-reflecting-usage-restrictions R₁ R₂ unit→erasure tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches-UR (UnitModality v₁ v₁-ok) R₁)
    (no-erased-matches-UR (ErasureModality v₂) R₂)
    unit→erasure tr
unit→erasure-reflects-no-erased-matches-UR v₁ v₁-ok v₂ =
  Are-reflecting-usage-restrictions-no-erased-matches-UR
    (UnitModality v₁ v₁-ok)
    (ErasureModality v₂)
    (λ tt≢tt → ⊥-elim $ tt≢tt refl)

-- If the functions erasure→unit and tr preserve certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches-UR.

erasure→unit-preserves-no-erased-matches-UR :
  ∀ v₁ v₂ v₂-ok →
  Are-preserving-usage-restrictions R₁ R₂ erasure→unit tr →
  Are-preserving-usage-restrictions
    (no-erased-matches-UR (ErasureModality v₁) R₁)
    (no-erased-matches-UR (UnitModality v₂ v₂-ok) R₂)
    erasure→unit tr
erasure→unit-preserves-no-erased-matches-UR v₁ v₂ v₂-ok =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (ErasureModality v₁)
    (UnitModality v₂ v₂-ok)
    (λ tt≢tt → ⊥-elim $ tt≢tt refl)

-- The functions erasure→unit and tr do not reflect certain usage
-- restrictions obtained using no-erased-matches-UR.

¬-erasure→unit-reflects-no-erased-matches-UR :
  ∀ v₁ R →
  let 𝕄₂ = UnitModality v₂ v₂-ok in
  ¬ Are-reflecting-usage-restrictions
      (no-erased-matches-UR (ErasureModality v₁) R)
      (no-erased-matches-UR 𝕄₂ (no-usage-restrictions 𝕄₂))
      erasure→unit tr
¬-erasure→unit-reflects-no-erased-matches-UR _ _ r =
  Prodrec-reflected {r = 𝟘} {p = 𝟘} {q = 𝟘} (_ , idᶠ) .proj₂ (λ ()) refl
  where
  open Are-reflecting-usage-restrictions r

-- If the functions erasure→zero-one-many and tr preserve certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches-UR.

erasure→zero-one-many-preserves-no-erased-matches-UR :
  ∀ v₁ v₂ →
  Are-preserving-usage-restrictions R₁ R₂
    erasure→zero-one-many tr →
  Are-preserving-usage-restrictions
    (no-erased-matches-UR (ErasureModality v₁) R₁)
    (no-erased-matches-UR (zero-one-many-modality 𝟙≤𝟘 v₂) R₂)
    erasure→zero-one-many tr
erasure→zero-one-many-preserves-no-erased-matches-UR v₁ v₂ =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (ErasureModality v₁)
    (zero-one-many-modality _ v₂)
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions erasure→zero-one-many and tr reflect certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches-UR.

erasure→zero-one-many-reflects-no-erased-matches-UR :
  ∀ v₁ v₂ →
  Are-reflecting-usage-restrictions R₁ R₂
    erasure→zero-one-many tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches-UR (ErasureModality v₁) R₁)
    (no-erased-matches-UR (zero-one-many-modality 𝟙≤𝟘 v₂) R₂)
    erasure→zero-one-many tr
erasure→zero-one-many-reflects-no-erased-matches-UR v₁ v₂ =
  Are-reflecting-usage-restrictions-no-erased-matches-UR
    (ErasureModality v₁)
    (zero-one-many-modality _ v₂)
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))

-- If the functions zero-one-many→erasure and tr preserve certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches-UR.

zero-one-many→erasure-preserves-no-erased-matches-UR :
  ∀ v₁ v₂ →
  Are-preserving-usage-restrictions R₁ R₂
    zero-one-many→erasure tr →
  Are-preserving-usage-restrictions
    (no-erased-matches-UR (zero-one-many-modality 𝟙≤𝟘 v₁) R₁)
    (no-erased-matches-UR (ErasureModality v₂) R₂)
    zero-one-many→erasure tr
zero-one-many→erasure-preserves-no-erased-matches-UR v₁ v₂ =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (zero-one-many-modality _ v₁)
    (ErasureModality v₂)
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions zero-one-many→erasure and tr reflect certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches-UR.

zero-one-many→erasure-reflects-no-erased-matches-UR :
  ∀ v₁ v₂ →
  Are-reflecting-usage-restrictions R₁ R₂
    zero-one-many→erasure tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches-UR (zero-one-many-modality 𝟙≤𝟘 v₁) R₁)
    (no-erased-matches-UR (ErasureModality v₂) R₂)
    zero-one-many→erasure tr
zero-one-many→erasure-reflects-no-erased-matches-UR v₁ v₂ =
  Are-reflecting-usage-restrictions-no-erased-matches-UR
    (zero-one-many-modality _ v₁)
    (ErasureModality v₂)
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))

-- If the functions linearity→linear-or-affine and tr preserve certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches-UR.

linearity→linear-or-affine-preserves-no-erased-matches-UR :
  ∀ v₁ v₂ →
  Are-preserving-usage-restrictions R₁ R₂
    linearity→linear-or-affine tr →
  Are-preserving-usage-restrictions
    (no-erased-matches-UR (linearityModality v₁) R₁)
    (no-erased-matches-UR (linear-or-affine v₂) R₂)
    linearity→linear-or-affine tr
linearity→linear-or-affine-preserves-no-erased-matches-UR v₁ v₂ =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (linearityModality v₁)
    (linear-or-affine v₂)
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions linearity→linear-or-affine and tr reflect certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches-UR.

linearity→linear-or-affine-reflects-no-erased-matches-UR :
  ∀ v₁ v₂ →
  Are-reflecting-usage-restrictions R₁ R₂
    linearity→linear-or-affine tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches-UR (linearityModality v₁) R₁)
    (no-erased-matches-UR (linear-or-affine v₂) R₂)
    linearity→linear-or-affine tr
linearity→linear-or-affine-reflects-no-erased-matches-UR v₁ v₂ =
  Are-reflecting-usage-restrictions-no-erased-matches-UR
    (linearityModality v₁)
    (linear-or-affine v₂)
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))

-- If the functions linear-or-affine→linearity and tr preserve certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches-UR.

linear-or-affine→linearity-preserves-no-erased-matches-UR :
  ∀ v₁ v₂ →
  Are-preserving-usage-restrictions R₁ R₂
    linear-or-affine→linearity tr →
  Are-preserving-usage-restrictions
    (no-erased-matches-UR (linear-or-affine v₁) R₁)
    (no-erased-matches-UR (linearityModality v₂) R₂)
    linear-or-affine→linearity tr
linear-or-affine→linearity-preserves-no-erased-matches-UR v₁ v₂ =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (linear-or-affine v₁)
    (linearityModality v₂)
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions linear-or-affine→linearity and tr reflect certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches-UR.

linear-or-affine→linearity-reflects-no-erased-matches-UR :
  ∀ v₁ v₂ →
  Are-reflecting-usage-restrictions R₁ R₂
    linear-or-affine→linearity tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches-UR (linear-or-affine v₁) R₁)
    (no-erased-matches-UR (linearityModality v₂) R₂)
    linear-or-affine→linearity tr
linear-or-affine→linearity-reflects-no-erased-matches-UR v₁ v₂ =
  Are-reflecting-usage-restrictions-no-erased-matches-UR
    (linear-or-affine v₁)
    (linearityModality v₂)
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))

-- If the functions affine→linear-or-affine and tr preserve certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches-UR.

affine→linear-or-affine-preserves-no-erased-matches-UR :
  ∀ v₁ v₂ →
  Are-preserving-usage-restrictions R₁ R₂
    affine→linear-or-affine tr →
  Are-preserving-usage-restrictions
    (no-erased-matches-UR (affineModality v₁) R₁)
    (no-erased-matches-UR (linear-or-affine v₂) R₂)
    affine→linear-or-affine tr
affine→linear-or-affine-preserves-no-erased-matches-UR v₁ v₂ =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (affineModality v₁)
    (linear-or-affine v₂)
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions affine→linear-or-affine and tr reflect certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches-UR.

affine→linear-or-affine-reflects-no-erased-matches-UR :
  ∀ v₁ v₂ →
  Are-reflecting-usage-restrictions R₁ R₂
    affine→linear-or-affine tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches-UR (affineModality v₁) R₁)
    (no-erased-matches-UR (linear-or-affine v₂) R₂)
    affine→linear-or-affine tr
affine→linear-or-affine-reflects-no-erased-matches-UR v₁ v₂ =
  Are-reflecting-usage-restrictions-no-erased-matches-UR
    (affineModality v₁)
    (linear-or-affine v₂)
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))

-- If the functions linear-or-affine→affine and tr preserve certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches-UR.

linear-or-affine→affine-preserves-no-erased-matches-UR :
  ∀ v₁ v₂ →
  Are-preserving-usage-restrictions R₁ R₂
    linear-or-affine→affine tr →
  Are-preserving-usage-restrictions
    (no-erased-matches-UR (linear-or-affine v₁) R₁)
    (no-erased-matches-UR (affineModality v₂) R₂)
    linear-or-affine→affine tr
linear-or-affine→affine-preserves-no-erased-matches-UR v₁ v₂ =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (linear-or-affine v₁)
    (affineModality v₂)
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions linear-or-affine→affine and tr reflect certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches-UR.

linear-or-affine→affine-reflects-no-erased-matches-UR :
  ∀ v₁ v₂ →
  Are-reflecting-usage-restrictions R₁ R₂
    linear-or-affine→affine tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches-UR (linear-or-affine v₁) R₁)
    (no-erased-matches-UR (affineModality v₂) R₂)
    linear-or-affine→affine tr
linear-or-affine→affine-reflects-no-erased-matches-UR v₁ v₂ =
  Are-reflecting-usage-restrictions-no-erased-matches-UR
    (linear-or-affine v₁)
    (affineModality v₂)
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))

-- If the functions affine→linearity and tr preserve certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches-UR.

affine→linearity-preserves-no-erased-matches-UR :
  ∀ v₁ v₂ →
  Are-preserving-usage-restrictions R₁ R₂
    affine→linearity tr →
  Are-preserving-usage-restrictions
    (no-erased-matches-UR (affineModality v₁) R₁)
    (no-erased-matches-UR (linearityModality v₂) R₂)
    affine→linearity tr
affine→linearity-preserves-no-erased-matches-UR v₁ v₂ =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (affineModality v₁)
    (linearityModality v₂)
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions affine→linearity and tr reflect certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches-UR.

affine→linearity-reflects-no-erased-matches-UR :
  ∀ v₁ v₂ →
  Are-reflecting-usage-restrictions R₁ R₂
    affine→linearity tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches-UR (affineModality v₁) R₁)
    (no-erased-matches-UR (linearityModality v₂) R₂)
    affine→linearity tr
affine→linearity-reflects-no-erased-matches-UR v₁ v₂ =
  Are-reflecting-usage-restrictions-no-erased-matches-UR
    (affineModality v₁)
    (linearityModality v₂)
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))

-- If the functions linearity→affine and tr preserve certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches-UR.

linearity→affine-preserves-no-erased-matches-UR :
  ∀ v₁ v₂ →
  Are-preserving-usage-restrictions R₁ R₂
    linearity→affine tr →
  Are-preserving-usage-restrictions
    (no-erased-matches-UR (linearityModality v₁) R₁)
    (no-erased-matches-UR (affineModality v₂) R₂)
    linearity→affine tr
linearity→affine-preserves-no-erased-matches-UR v₁ v₂ =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (linearityModality v₁)
    (affineModality v₂)
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions linearity→affine and tr reflect certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches-UR.

linearity→affine-reflects-no-erased-matches-UR :
  ∀ v₁ v₂ →
  Are-reflecting-usage-restrictions R₁ R₂
    linearity→affine tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches-UR (linearityModality v₁) R₁)
    (no-erased-matches-UR (affineModality v₂) R₂)
    linearity→affine tr
linearity→affine-reflects-no-erased-matches-UR v₁ v₂ =
  Are-reflecting-usage-restrictions-no-erased-matches-UR
    (linearityModality v₁)
    (affineModality v₂)
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))
