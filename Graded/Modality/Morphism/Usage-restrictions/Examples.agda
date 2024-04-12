------------------------------------------------------------------------
-- Lemmas related to
-- Are-preserving-usage-restrictions/Are-reflecting-usage-restrictions
-- and specific usage restriction transformers (and
-- no-usage-restrictions)
------------------------------------------------------------------------

module Graded.Modality.Morphism.Usage-restrictions.Examples where

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Product as Σ
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

open import Definition.Typed.Restrictions

open import Graded.Modality
open import Graded.Modality.Morphism.Examples
open import Graded.Modality.Morphism.Type-restrictions
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
open import Graded.Mode
open import Graded.Restrictions
open import Graded.Usage.Erased-matches
open import Graded.Usage.Restrictions

private variable
  b₁ b₂ 𝟙≤𝟘 ok : Bool
  v₁ v₂        : Modality-variant _
  R R₁ R₂      : Usage-restrictions _
  TR₁ TR₂      : Type-restrictions _
  A M₁ M₂      : Set _
  𝕄₁ 𝕄₂        : Modality _
  m₁ m₂        : Mode _
  tr tr-Σ      : M₁ → M₂
  v₁-ok v₂-ok  : A

------------------------------------------------------------------------
-- Preserving/reflecting no usage restrictions

opaque

  -- Common-properties holds for certain usage restrictions obtained
  -- from no-usage-restrictions, given that a certain assumption
  -- holds.

  Common-properties-no-usage-restrictions :
    (T (Modality.𝟘ᵐ-allowed 𝕄₁) → T (Modality.𝟘ᵐ-allowed 𝕄₂)) →
    Common-properties
      (no-usage-restrictions 𝕄₁ b₁ b₂)
      (no-usage-restrictions 𝕄₂ b₁ b₂)
  Common-properties-no-usage-restrictions hyp = λ where
      .𝟘ᵐ-preserved                   → hyp
      .starˢ-sink-preserved           → refl
      .Id-erased-preserved            → lift ∘→ Lift.lower
                                      , lift ∘→ Lift.lower
      .erased-matches-for-J-preserved → _
      .erased-matches-for-K-preserved → _
    where
    open Common-properties

opaque

  -- The functions tr and tr-Σ preserve certain usage restrictions
  -- obtained from no-usage-restrictions, given that a certain
  -- assumption holds.

  Are-preserving-usage-restrictions-no-usage-restrictions :
    (T (Modality.𝟘ᵐ-allowed 𝕄₁) → T (Modality.𝟘ᵐ-allowed 𝕄₂)) →
    Are-preserving-usage-restrictions
      (no-usage-restrictions 𝕄₁ b₁ b₂)
      (no-usage-restrictions 𝕄₂ b₁ b₂)
      tr tr-Σ
  Are-preserving-usage-restrictions-no-usage-restrictions hyp = λ where
      .common-properties  → Common-properties-no-usage-restrictions hyp
      .Prodrec-preserved  → _
      .Unitrec-preserved  → _
      .Emptyrec-preserved → _
    where
    open Are-preserving-usage-restrictions

opaque

  -- The functions tr and tr-Σ reflect certain usage restrictions
  -- obtained from no-usage-restrictions, given that certain
  -- assumptions hold.

  Are-reflecting-usage-restrictions-no-usage-restrictions :
    let module M₁ = Modality 𝕄₁
        module M₂ = Modality 𝕄₂
    in
    (T M₁.𝟘ᵐ-allowed → T M₂.𝟘ᵐ-allowed) →
    (T M₂.𝟘ᵐ-allowed ⊎ M₂.Trivial → T M₁.𝟘ᵐ-allowed ⊎ M₁.Trivial) →
    Are-reflecting-usage-restrictions
      (no-usage-restrictions 𝕄₁ b₁ b₂)
      (no-usage-restrictions 𝕄₂ b₁ b₂)
      tr tr-Σ
  Are-reflecting-usage-restrictions-no-usage-restrictions hyp₁ hyp₂ =
    λ where
      .common-properties →
        Common-properties-no-usage-restrictions hyp₁
      .𝟘ᵐ-reflected                   → hyp₂
      .Prodrec-reflected              → _
      .Unitrec-reflected              → _
      .Emptyrec-reflected             → _
      .erased-matches-for-J-reflected → _
      .erased-matches-for-K-reflected → _
    where
    open Are-reflecting-usage-restrictions

------------------------------------------------------------------------
-- Preserving/reflecting certain usage restrictions

opaque

  -- The function only-some-erased-matches preserves Common-properties
  -- in a certain way.

  Common-properties-only-some-erased-matches :
    Common-properties R₁ R₂ →
    Common-properties
      (only-some-erased-matches 𝕄₁ R₁)
      (only-some-erased-matches 𝕄₂ R₂)
  Common-properties-only-some-erased-matches cp = record
    { 𝟘ᵐ-preserved                   = 𝟘ᵐ-preserved
    ; starˢ-sink-preserved           = starˢ-sink-preserved
    ; Id-erased-preserved            = Id-erased-preserved
    ; erased-matches-for-J-preserved = λ where
        𝟙ᵐ → _
        𝟘ᵐ → erased-matches-for-J-preserved 𝟘ᵐ
    ; erased-matches-for-K-preserved = λ where
        𝟙ᵐ → _
        𝟘ᵐ → erased-matches-for-K-preserved 𝟘ᵐ
    }
    where
    open Common-properties cp

opaque

  -- If the functions tr and tr-Σ preserve certain usage restrictions,
  -- then they also do this for certain usage restrictions obtained
  -- using only-some-erased-matches, given that a certain assumption
  -- holds.

  Are-preserving-usage-restrictions-only-some-erased-matches :
    (¬ Modality.Trivial 𝕄₂ →
     ¬ Modality.Trivial 𝕄₁ ×
     (∀ {p} → tr p ≡ Modality.𝟘 𝕄₂ → p ≡ Modality.𝟘 𝕄₁) ⊎
     (∀ {p} → tr p ≢ Modality.𝟘 𝕄₂)) →
    Are-preserving-usage-restrictions R₁ R₂ tr tr-Σ →
    Are-preserving-usage-restrictions
      (only-some-erased-matches 𝕄₁ R₁)
      (only-some-erased-matches 𝕄₂ R₂)
      tr tr-Σ
  Are-preserving-usage-restrictions-only-some-erased-matches
    {𝕄₂} {𝕄₁} {tr} hyp r = record
    { common-properties =
        Common-properties-only-some-erased-matches common-properties
    ; Prodrec-preserved = λ {_ _} {r = r} m₁≈m₂ (p , ≢𝟘) →
          Prodrec-preserved m₁≈m₂ p
        , (λ 𝟙≢𝟘 ≡𝟙ᵐ → case hyp 𝟙≢𝟘 of λ where
             (inj₁ (𝟙≢𝟘 , tr-≡-𝟘-→)) →
               tr r ≡ M₂.𝟘  →⟨ tr-≡-𝟘-→ ⟩
               r ≡ M₁.𝟘     →⟨ ≢𝟘 𝟙≢𝟘 (≈ᵐ→≡𝟙ᵐ→≡𝟙ᵐ m₁≈m₂ ≡𝟙ᵐ) ⟩
               ⊥            □
             (inj₂ ≢𝟘) →
               tr r ≡ M₂.𝟘  →⟨ ≢𝟘 ⟩
               ⊥            □)
    ; Unitrec-preserved =
        Unitrec-preserved
    ; Emptyrec-preserved =
        Emptyrec-preserved
    }
    where
    module M₁ = Modality 𝕄₁
    module M₂ = Modality 𝕄₂
    open Are-preserving-usage-restrictions r

opaque

  -- If the functions tr and tr-Σ reflect certain usage restrictions,
  -- then they also do this for certain usage restrictions obtained
  -- using only-some-erased-matches, given that a certain assumption
  -- holds.

  Are-reflecting-usage-restrictions-only-some-erased-matches :
    (¬ Modality.Trivial 𝕄₁ →
     ¬ Modality.Trivial 𝕄₂ ×
     (∀ {p} → p ≡ Modality.𝟘 𝕄₁ → tr p ≡ Modality.𝟘 𝕄₂)) →
    Are-reflecting-usage-restrictions R₁ R₂ tr tr-Σ →
    Are-reflecting-usage-restrictions
      (only-some-erased-matches 𝕄₁ R₁)
      (only-some-erased-matches 𝕄₂ R₂)
      tr tr-Σ
  Are-reflecting-usage-restrictions-only-some-erased-matches
    {𝕄₁} {𝕄₂} {tr} hyp r = record
    { common-properties =
        Common-properties-only-some-erased-matches common-properties
    ; 𝟘ᵐ-reflected =
        𝟘ᵐ-reflected
    ; Prodrec-reflected = λ {_ _} {r = r} m₁≲m₂ (prodrec-ok , tr-r≢𝟘) →
          Prodrec-reflected m₁≲m₂ prodrec-ok
        , (λ non-trivial₁ m₁≡𝟙ᵐ →
             case m₁≲m₂ of λ where
               [ m₁≈m₂ ] →
                 r ≡ M₁.𝟘     →⟨ hyp non-trivial₁ .proj₂ ⟩
                 tr r ≡ M₂.𝟘  →⟨ tr-r≢𝟘 (hyp non-trivial₁ .proj₁) (≈ᵐ→≡𝟙ᵐ←≡𝟙ᵐ m₁≈m₂ m₁≡𝟙ᵐ) ⟩
                 ⊥            □
               (𝟙ᵐ≳𝟘ᵐ trivial₁) _ →
                 non-trivial₁ trivial₁)
    ; Unitrec-reflected =
        Unitrec-reflected
    ; Emptyrec-reflected =
        Emptyrec-reflected
    ; erased-matches-for-J-reflected = λ where
        𝟙ᵐ → _
        𝟘ᵐ → erased-matches-for-J-reflected 𝟘ᵐ
    ; erased-matches-for-K-reflected = λ where
        𝟙ᵐ → _
        𝟘ᵐ → erased-matches-for-K-reflected 𝟘ᵐ
    }
    where
    module M₁ = Modality 𝕄₁
    module M₂ = Modality 𝕄₂
    open Are-reflecting-usage-restrictions r

-- The function no-erased-matches-UR preserves Common-properties in
-- a certain way.

Common-properties-no-erased-matches-UR :
  ∀ TR₁ TR₂ →
  Common-properties R₁ R₂ →
  Common-properties
    (no-erased-matches-UR 𝕄₁ TR₁ R₁)
    (no-erased-matches-UR 𝕄₂ TR₂ R₂)
Common-properties-no-erased-matches-UR _ _ cp = record
  { 𝟘ᵐ-preserved                   = 𝟘ᵐ-preserved
  ; starˢ-sink-preserved           = starˢ-sink-preserved
  ; Id-erased-preserved            = Id-erased-preserved
  ; erased-matches-for-J-preserved = erased-matches-for-J-preserved
  ; erased-matches-for-K-preserved = erased-matches-for-K-preserved
  }
  where
  open Common-properties
         (Common-properties-only-some-erased-matches cp)

-- If the functions tr and tr-Σ preserve certain usage restrictions,
-- then they also do this for certain usage restrictions obtained
-- using no-erased-matches-UR, given that certain assumptions hold.

Are-preserving-usage-restrictions-no-erased-matches-UR :
  (¬ Modality.Trivial 𝕄₂ →
   ¬ Modality.Trivial 𝕄₁ ×
   (∀ {p} → tr p ≡ Modality.𝟘 𝕄₂ → p ≡ Modality.𝟘 𝕄₁) ⊎
   (∀ {p} → tr p ≢ Modality.𝟘 𝕄₂)) →
  Are-preserving-type-restrictions TR₁ TR₂ tr tr-Σ →
  Are-preserving-usage-restrictions R₁ R₂ tr tr-Σ →
  Are-preserving-usage-restrictions
    (no-erased-matches-UR 𝕄₁ TR₁ R₁)
    (no-erased-matches-UR 𝕄₂ TR₂ R₂)
    tr tr-Σ
Are-preserving-usage-restrictions-no-erased-matches-UR
  {𝕄₂} {𝕄₁} {tr} {TR₁} {TR₂} hyp tp up = record
  { common-properties =
      Common-properties-no-erased-matches-UR TR₁ TR₂
        UP.common-properties
  ; Prodrec-preserved =
      Are-preserving-usage-restrictions.Prodrec-preserved
        (Are-preserving-usage-restrictions-only-some-erased-matches
           hyp up)
  ; Unitrec-preserved = λ {_ _} {p = p} m₁≈m₂ (P , η) →
        UP.Unitrec-preserved m₁≈m₂ P
      , (λ 𝟙≢𝟘 ≡𝟙ᵐ → case hyp 𝟙≢𝟘 of λ where
           (inj₁ (𝟙≢𝟘 , tr-≡-𝟘-→)) →
             tr p ≡ M₂.𝟘  →⟨ tr-≡-𝟘-→ ⟩
             p ≡ M₁.𝟘     →⟨ η 𝟙≢𝟘 (≈ᵐ→≡𝟙ᵐ→≡𝟙ᵐ m₁≈m₂ ≡𝟙ᵐ) ⟩
             TR₁.Unitʷ-η  →⟨ TP.Unitʷ-η-preserved ⟩
             TR₂.Unitʷ-η  □
           (inj₂ ≢𝟘) →
             tr p ≡ M₂.𝟘  →⟨ ≢𝟘 ⟩
             ⊥            →⟨ ⊥-elim ⟩
             TR₂.Unitʷ-η  □)
  ; Emptyrec-preserved =
      UP.Emptyrec-preserved
  }
  where
  module UP  = Are-preserving-usage-restrictions up
  module TP  = Are-preserving-type-restrictions tp
  module M₁  = Modality 𝕄₁
  module M₂  = Modality 𝕄₂
  module TR₁ = Type-restrictions TR₁
  module TR₂ = Type-restrictions TR₂

-- If the functions tr and tr-Σ reflect certain usage restrictions,
-- then they also do this for certain usage restrictions obtained
-- using no-erased-matches-UR, given that certain assumptions hold.

Are-reflecting-usage-restrictions-no-erased-matches-UR :
  (¬ Modality.Trivial 𝕄₁ →
   ¬ Modality.Trivial 𝕄₂ ×
   (∀ {p} → p ≡ Modality.𝟘 𝕄₁ → tr p ≡ Modality.𝟘 𝕄₂)) →
  Are-reflecting-type-restrictions TR₁ TR₂ tr tr-Σ →
  Are-reflecting-usage-restrictions R₁ R₂ tr tr-Σ →
  Are-reflecting-usage-restrictions
    (no-erased-matches-UR 𝕄₁ TR₁ R₁)
    (no-erased-matches-UR 𝕄₂ TR₂ R₂)
    tr tr-Σ
Are-reflecting-usage-restrictions-no-erased-matches-UR
  {𝕄₁} {𝕄₂} {tr} {TR₁} {TR₂} hyp tp up = record
  { common-properties =
      Common-properties-no-erased-matches-UR TR₁ TR₂
        (Are-reflecting-usage-restrictions.common-properties up)
  ; 𝟘ᵐ-reflected =
      UR.𝟘ᵐ-reflected
  ; Prodrec-reflected =
      UR.Prodrec-reflected
  ; Unitrec-reflected = λ {_ _} {p = p} m₁≲m₂ (unitrec-ok , tr-p≢𝟘) →
        UR.Unitrec-reflected m₁≲m₂ unitrec-ok
      , (λ non-trivial₁ m₁≡𝟙ᵐ →
           case m₁≲m₂ of λ where
             [ m₁≈m₂ ] →
               p ≡ M₁.𝟘     →⟨ hyp non-trivial₁ .proj₂ ⟩
               tr p ≡ M₂.𝟘  →⟨ tr-p≢𝟘 (hyp non-trivial₁ .proj₁) (≈ᵐ→≡𝟙ᵐ←≡𝟙ᵐ m₁≈m₂ m₁≡𝟙ᵐ) ⟩
               TR₂.Unitʷ-η  →⟨ TR.Unitʷ-η-reflected ⟩
               TR₁.Unitʷ-η  □
             (𝟙ᵐ≳𝟘ᵐ trivial₁) _ →
               ⊥-elim (non-trivial₁ trivial₁))
  ; Emptyrec-reflected =
      UR.Emptyrec-reflected
  ; erased-matches-for-J-reflected =
      UR.erased-matches-for-J-reflected
  ; erased-matches-for-K-reflected =
      UR.erased-matches-for-K-reflected
  }
  where
  module UR =
    Are-reflecting-usage-restrictions
      (Are-reflecting-usage-restrictions-only-some-erased-matches
         hyp up)
  module TR  = Are-reflecting-type-restrictions tp
  module M₁  = Modality 𝕄₁
  module M₂  = Modality 𝕄₂
  module TR₁ = Type-restrictions TR₁
  module TR₂ = Type-restrictions TR₂

private opaque

  -- A lemma related to not-all-for-𝟙ᵐ.

  not-all-for-𝟙ᵐ-≤ᵉᵐ :
    (f₁ : Mode 𝕄₁ → Erased-matches)
    (f₂ : Mode 𝕄₂ → Erased-matches) →
    f₁ m₁ ≤ᵉᵐ f₂ m₂ →
    m₁ ≈ᵐ m₂ →
    not-all-for-𝟙ᵐ 𝕄₁ f₁ m₁ ≤ᵉᵐ not-all-for-𝟙ᵐ 𝕄₂ f₂ m₂
  not-all-for-𝟙ᵐ-≤ᵉᵐ _  _  hyp 𝟘ᵐ = hyp
  not-all-for-𝟙ᵐ-≤ᵉᵐ f₁ f₂ hyp 𝟙ᵐ with f₁ 𝟙ᵐ | f₂ 𝟙ᵐ
  … | none | _    = _
  … | some | some = _
  … | some | all  = _
  … | all  | none = ⊥-elim hyp
  … | all  | some = _
  … | all  | all  = _

opaque

  -- The function not-all-erased-matches-JK preserves
  -- Common-properties in a certain way.

  Common-properties-not-all-erased-matches-JK :
    Common-properties R₁ R₂ →
    Common-properties
      (not-all-erased-matches-JK 𝕄₁ R₁)
      (not-all-erased-matches-JK 𝕄₂ R₂)
  Common-properties-not-all-erased-matches-JK
    {R₁} {R₂} cp = record
    { 𝟘ᵐ-preserved                   = 𝟘ᵐ-preserved
    ; starˢ-sink-preserved           = starˢ-sink-preserved
    ; Id-erased-preserved            = Id-erased-preserved
    ; erased-matches-for-J-preserved = λ where
        𝟘ᵐ → erased-matches-for-J-preserved 𝟘ᵐ
        𝟙ᵐ →
          not-all-for-𝟙ᵐ-≤ᵉᵐ R₁.erased-matches-for-J
            R₂.erased-matches-for-J (erased-matches-for-J-preserved 𝟙ᵐ)
            𝟙ᵐ
    ; erased-matches-for-K-preserved = λ where
        𝟘ᵐ → erased-matches-for-K-preserved 𝟘ᵐ
        𝟙ᵐ →
          not-all-for-𝟙ᵐ-≤ᵉᵐ R₁.erased-matches-for-K
            R₂.erased-matches-for-K (erased-matches-for-K-preserved 𝟙ᵐ)
            𝟙ᵐ
    }
    where
    module R₁ = Usage-restrictions R₁
    module R₂ = Usage-restrictions R₂
    open Common-properties cp

opaque

  -- If the functions tr and tr-Σ preserve certain usage restrictions,
  -- then they also do this for certain usage restrictions obtained
  -- using not-all-erased-matches-JK.

  Are-preserving-usage-restrictions-not-all-erased-matches-JK :
    Are-preserving-usage-restrictions R₁ R₂ tr tr-Σ →
    Are-preserving-usage-restrictions
      (not-all-erased-matches-JK 𝕄₁ R₁)
      (not-all-erased-matches-JK 𝕄₂ R₂)
      tr tr-Σ
  Are-preserving-usage-restrictions-not-all-erased-matches-JK
    r = record
    { common-properties =
        Common-properties-not-all-erased-matches-JK common-properties
    ; Prodrec-preserved =
        Prodrec-preserved
    ; Unitrec-preserved =
        Unitrec-preserved
    ; Emptyrec-preserved =
        Emptyrec-preserved
    }
    where
    open Are-preserving-usage-restrictions r

opaque

  -- If the functions tr and tr-Σ reflect certain usage restrictions,
  -- then they also do this for certain usage restrictions obtained
  -- using not-all-erased-matches-JK.

  Are-reflecting-usage-restrictions-not-all-erased-matches-JK :
    Are-reflecting-usage-restrictions R₁ R₂ tr tr-Σ →
    Are-reflecting-usage-restrictions
      (not-all-erased-matches-JK 𝕄₁ R₁)
      (not-all-erased-matches-JK 𝕄₂ R₂)
      tr tr-Σ
  Are-reflecting-usage-restrictions-not-all-erased-matches-JK
    {𝕄₁} {R₁} {𝕄₂} {R₂} r = record
    { common-properties =
        Common-properties-not-all-erased-matches-JK common-properties
    ; 𝟘ᵐ-reflected =
        𝟘ᵐ-reflected
    ; Prodrec-reflected =
        Prodrec-reflected
    ; Unitrec-reflected =
        Unitrec-reflected
    ; Emptyrec-reflected =
        Emptyrec-reflected
    ; erased-matches-for-J-reflected = λ where
        𝟘ᵐ → erased-matches-for-J-reflected 𝟘ᵐ
        𝟙ᵐ →
          not-all-for-𝟙ᵐ-≤ᵉᵐ R₂.erased-matches-for-J
            R₁.erased-matches-for-J (erased-matches-for-J-reflected 𝟙ᵐ)
            𝟙ᵐ
    ; erased-matches-for-K-reflected = λ where
        𝟘ᵐ → erased-matches-for-K-reflected 𝟘ᵐ
        𝟙ᵐ →
          not-all-for-𝟙ᵐ-≤ᵉᵐ R₂.erased-matches-for-K
            R₁.erased-matches-for-K (erased-matches-for-K-reflected 𝟙ᵐ)
            𝟙ᵐ
    }
    where
    module M₁ = Modality 𝕄₁
    module M₂ = Modality 𝕄₂
    module R₁ = Usage-restrictions R₁
    module R₂ = Usage-restrictions R₂
    open Are-reflecting-usage-restrictions r

------------------------------------------------------------------------
-- Some lemmas related to only-some-erased-matches and concrete
-- translation functions

opaque

  -- If the functions unit→erasure and tr preserve certain usage
  -- restrictions, then they also do this for certain usage
  -- restrictions obtained using only-some-erased-matches.

  unit→erasure-preserves-only-some-erased-matches :
    Are-preserving-usage-restrictions R₁ R₂ unit→erasure tr →
    Are-preserving-usage-restrictions
      (only-some-erased-matches (UnitModality v₁ v₁-ok) R₁)
      (only-some-erased-matches (ErasureModality v₂) R₂)
      unit→erasure tr
  unit→erasure-preserves-only-some-erased-matches =
    Are-preserving-usage-restrictions-only-some-erased-matches
      (λ _ → inj₂ (λ ()))

opaque

  -- If the functions unit→erasure and tr reflect certain usage
  -- restrictions, then they also do this for certain usage
  -- restrictions obtained using only-some-erased-matches.

  unit→erasure-reflects-only-some-erased-matches :
    Are-reflecting-usage-restrictions R₁ R₂ unit→erasure tr →
    Are-reflecting-usage-restrictions
      (only-some-erased-matches (UnitModality v₁ v₁-ok) R₁)
      (only-some-erased-matches (ErasureModality v₂) R₂)
      unit→erasure tr
  unit→erasure-reflects-only-some-erased-matches =
    Are-reflecting-usage-restrictions-only-some-erased-matches
      (λ tt≢tt → ⊥-elim $ tt≢tt refl)

opaque

  -- If the functions erasure→unit and tr preserve certain usage
  -- restrictions, then they also do this for certain usage
  -- restrictions obtained using only-some-erased-matches.

  erasure→unit-preserves-only-some-erased-matches :
    Are-preserving-usage-restrictions R₁ R₂ erasure→unit tr →
    Are-preserving-usage-restrictions
      (only-some-erased-matches (ErasureModality v₁) R₁)
      (only-some-erased-matches (UnitModality v₂ v₂-ok) R₂)
      erasure→unit tr
  erasure→unit-preserves-only-some-erased-matches =
    Are-preserving-usage-restrictions-only-some-erased-matches
      (λ tt≢tt → ⊥-elim $ tt≢tt refl)

opaque

  -- The functions erasure→unit and tr do not reflect certain usage
  -- restrictions obtained using only-some-erased-matches.

  ¬-erasure→unit-reflects-only-some-erased-matches :
    ∀ R →
    let 𝕄₂ = UnitModality v₂ v₂-ok in
    ¬ Are-reflecting-usage-restrictions
        (only-some-erased-matches (ErasureModality v₁) R)
        (only-some-erased-matches 𝕄₂ (no-usage-restrictions 𝕄₂ b₁ b₂))
        erasure→unit tr
  ¬-erasure→unit-reflects-only-some-erased-matches _ r =
    Prodrec-reflected {p = 𝟘} {q = 𝟘} [ 𝟙ᵐ ] (_ , λ tt≢tt _ → tt≢tt)
      .proj₂ (λ ()) refl refl
    where
    open Are-reflecting-usage-restrictions r

opaque

  -- If the functions erasure→zero-one-many and tr preserve certain
  -- usage restrictions, then they also do this for certain usage
  -- restrictions obtained using only-some-erased-matches.

  erasure→zero-one-many-preserves-only-some-erased-matches :
    Are-preserving-usage-restrictions R₁ R₂
      erasure→zero-one-many tr →
    Are-preserving-usage-restrictions
      (only-some-erased-matches (ErasureModality v₁) R₁)
      (only-some-erased-matches (zero-one-many-modality 𝟙≤𝟘 v₂) R₂)
      erasure→zero-one-many tr
  erasure→zero-one-many-preserves-only-some-erased-matches =
    Are-preserving-usage-restrictions-only-some-erased-matches
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              {p = 𝟘} _ → refl)
         ))

opaque

  -- If the functions erasure→zero-one-many and tr reflect certain
  -- usage restrictions, then they also do this for certain usage
  -- restrictions obtained using only-some-erased-matches.

  erasure→zero-one-many-reflects-only-some-erased-matches :
    Are-reflecting-usage-restrictions R₁ R₂
      erasure→zero-one-many tr →
    Are-reflecting-usage-restrictions
      (only-some-erased-matches (ErasureModality v₁) R₁)
      (only-some-erased-matches (zero-one-many-modality 𝟙≤𝟘 v₂) R₂)
      erasure→zero-one-many tr
  erasure→zero-one-many-reflects-only-some-erased-matches =
    Are-reflecting-usage-restrictions-only-some-erased-matches
      (λ _ →
           (λ ())
         , (λ where
              {p = 𝟘} _ → refl))

opaque

  -- If the functions zero-one-many→erasure and tr preserve certain
  -- usage restrictions, then they also do this for certain usage
  -- restrictions obtained using only-some-erased-matches.

  zero-one-many→erasure-preserves-only-some-erased-matches :
    Are-preserving-usage-restrictions R₁ R₂
      zero-one-many→erasure tr →
    Are-preserving-usage-restrictions
      (only-some-erased-matches (zero-one-many-modality 𝟙≤𝟘 v₁) R₁)
      (only-some-erased-matches (ErasureModality v₂) R₂)
      zero-one-many→erasure tr
  zero-one-many→erasure-preserves-only-some-erased-matches =
    Are-preserving-usage-restrictions-only-some-erased-matches
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              {p = 𝟘} _ → refl)
         ))

opaque

  -- If the functions zero-one-many→erasure and tr reflect certain
  -- usage restrictions, then they also do this for certain usage
  -- restrictions obtained using only-some-erased-matches.

  zero-one-many→erasure-reflects-only-some-erased-matches :
    Are-reflecting-usage-restrictions R₁ R₂
      zero-one-many→erasure tr →
    Are-reflecting-usage-restrictions
      (only-some-erased-matches (zero-one-many-modality 𝟙≤𝟘 v₁) R₁)
      (only-some-erased-matches (ErasureModality v₂) R₂)
      zero-one-many→erasure tr
  zero-one-many→erasure-reflects-only-some-erased-matches =
    Are-reflecting-usage-restrictions-only-some-erased-matches
      (λ _ →
           (λ ())
         , (λ where
              {p = 𝟘} _ → refl))

opaque

  -- If the functions linearity→linear-or-affine and tr preserve
  -- certain usage restrictions, then they also do this for certain
  -- usage restrictions obtained using only-some-erased-matches.

  linearity→linear-or-affine-preserves-only-some-erased-matches :
    Are-preserving-usage-restrictions R₁ R₂
      linearity→linear-or-affine tr →
    Are-preserving-usage-restrictions
      (only-some-erased-matches (linearityModality v₁) R₁)
      (only-some-erased-matches (linear-or-affine v₂) R₂)
      linearity→linear-or-affine tr
  linearity→linear-or-affine-preserves-only-some-erased-matches =
    Are-preserving-usage-restrictions-only-some-erased-matches
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              {p = 𝟘} _ → refl)
         ))

opaque

  -- If the functions linearity→linear-or-affine and tr reflect
  -- certain usage restrictions, then they also do this for certain
  -- usage restrictions obtained using only-some-erased-matches.

  linearity→linear-or-affine-reflects-only-some-erased-matches :
    Are-reflecting-usage-restrictions R₁ R₂
      linearity→linear-or-affine tr →
    Are-reflecting-usage-restrictions
      (only-some-erased-matches (linearityModality v₁) R₁)
      (only-some-erased-matches (linear-or-affine v₂) R₂)
      linearity→linear-or-affine tr
  linearity→linear-or-affine-reflects-only-some-erased-matches =
    Are-reflecting-usage-restrictions-only-some-erased-matches
      (λ _ →
           (λ ())
         , (λ where
              {p = 𝟘} _ → refl))

opaque

  -- If the functions linear-or-affine→linearity and tr preserve
  -- certain usage restrictions, then they also do this for certain
  -- usage restrictions obtained using only-some-erased-matches.

  linear-or-affine→linearity-preserves-only-some-erased-matches :
    Are-preserving-usage-restrictions R₁ R₂
      linear-or-affine→linearity tr →
    Are-preserving-usage-restrictions
      (only-some-erased-matches (linear-or-affine v₁) R₁)
      (only-some-erased-matches (linearityModality v₂) R₂)
      linear-or-affine→linearity tr
  linear-or-affine→linearity-preserves-only-some-erased-matches =
    Are-preserving-usage-restrictions-only-some-erased-matches
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              {p = 𝟘} _ → refl)
         ))

opaque

  -- If the functions linear-or-affine→linearity and tr reflect
  -- certain usage restrictions, then they also do this for certain
  -- usage restrictions obtained using only-some-erased-matches.

  linear-or-affine→linearity-reflects-only-some-erased-matches :
    Are-reflecting-usage-restrictions R₁ R₂
      linear-or-affine→linearity tr →
    Are-reflecting-usage-restrictions
      (only-some-erased-matches (linear-or-affine v₁) R₁)
      (only-some-erased-matches (linearityModality v₂) R₂)
      linear-or-affine→linearity tr
  linear-or-affine→linearity-reflects-only-some-erased-matches =
    Are-reflecting-usage-restrictions-only-some-erased-matches
      (λ _ →
           (λ ())
         , (λ where
              {p = 𝟘} _ → refl))

opaque

  -- If the functions affine→linear-or-affine and tr preserve certain
  -- usage restrictions, then they also do this for certain usage
  -- restrictions obtained using only-some-erased-matches.

  affine→linear-or-affine-preserves-only-some-erased-matches :
    Are-preserving-usage-restrictions R₁ R₂
      affine→linear-or-affine tr →
    Are-preserving-usage-restrictions
      (only-some-erased-matches (affineModality v₁) R₁)
      (only-some-erased-matches (linear-or-affine v₂) R₂)
      affine→linear-or-affine tr
  affine→linear-or-affine-preserves-only-some-erased-matches =
    Are-preserving-usage-restrictions-only-some-erased-matches
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              {p = 𝟘} _ → refl)
         ))

opaque

  -- If the functions affine→linear-or-affine and tr reflect certain
  -- usage restrictions, then they also do this for certain usage
  -- restrictions obtained using only-some-erased-matches.

  affine→linear-or-affine-reflects-only-some-erased-matches :
    Are-reflecting-usage-restrictions R₁ R₂
      affine→linear-or-affine tr →
    Are-reflecting-usage-restrictions
      (only-some-erased-matches (affineModality v₁) R₁)
      (only-some-erased-matches (linear-or-affine v₂) R₂)
      affine→linear-or-affine tr
  affine→linear-or-affine-reflects-only-some-erased-matches =
    Are-reflecting-usage-restrictions-only-some-erased-matches
      (λ _ →
           (λ ())
         , (λ where
              {p = 𝟘} _ → refl))

opaque

  -- If the functions linear-or-affine→affine and tr preserve certain
  -- usage restrictions, then they also do this for certain usage
  -- restrictions obtained using only-some-erased-matches.

  linear-or-affine→affine-preserves-only-some-erased-matches :
    Are-preserving-usage-restrictions R₁ R₂
      linear-or-affine→affine tr →
    Are-preserving-usage-restrictions
      (only-some-erased-matches (linear-or-affine v₁) R₁)
      (only-some-erased-matches (affineModality v₂) R₂)
      linear-or-affine→affine tr
  linear-or-affine→affine-preserves-only-some-erased-matches =
    Are-preserving-usage-restrictions-only-some-erased-matches
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              {p = 𝟘} _ → refl)
         ))

opaque

  -- If the functions linear-or-affine→affine and tr reflect certain
  -- usage restrictions, then they also do this for certain usage
  -- restrictions obtained using only-some-erased-matches.

  linear-or-affine→affine-reflects-only-some-erased-matches :
    Are-reflecting-usage-restrictions R₁ R₂
      linear-or-affine→affine tr →
    Are-reflecting-usage-restrictions
      (only-some-erased-matches (linear-or-affine v₁) R₁)
      (only-some-erased-matches (affineModality v₂) R₂)
      linear-or-affine→affine tr
  linear-or-affine→affine-reflects-only-some-erased-matches =
    Are-reflecting-usage-restrictions-only-some-erased-matches
      (λ _ →
           (λ ())
         , (λ where
              {p = 𝟘} _ → refl))

opaque

  -- If the functions affine→linearity and tr preserve certain usage
  -- restrictions, then they also do this for certain usage
  -- restrictions obtained using only-some-erased-matches.

  affine→linearity-preserves-only-some-erased-matches :
    Are-preserving-usage-restrictions R₁ R₂
      affine→linearity tr →
    Are-preserving-usage-restrictions
      (only-some-erased-matches (affineModality v₁) R₁)
      (only-some-erased-matches (linearityModality v₂) R₂)
      affine→linearity tr
  affine→linearity-preserves-only-some-erased-matches =
    Are-preserving-usage-restrictions-only-some-erased-matches
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              {p = 𝟘} _ → refl)
         ))

opaque

  -- If the functions affine→linearity and tr reflect certain usage
  -- restrictions, then they also do this for certain usage
  -- restrictions obtained using only-some-erased-matches.

  affine→linearity-reflects-only-some-erased-matches :
    Are-reflecting-usage-restrictions R₁ R₂
      affine→linearity tr →
    Are-reflecting-usage-restrictions
      (only-some-erased-matches (affineModality v₁) R₁)
      (only-some-erased-matches (linearityModality v₂) R₂)
      affine→linearity tr
  affine→linearity-reflects-only-some-erased-matches =
    Are-reflecting-usage-restrictions-only-some-erased-matches
      (λ _ →
           (λ ())
         , (λ where
              {p = 𝟘} _ → refl))

opaque

  -- If the functions linearity→affine and tr preserve certain usage
  -- restrictions, then they also do this for certain usage
  -- restrictions obtained using only-some-erased-matches.

  linearity→affine-preserves-only-some-erased-matches :
    Are-preserving-usage-restrictions R₁ R₂
      linearity→affine tr →
    Are-preserving-usage-restrictions
      (only-some-erased-matches (linearityModality v₁) R₁)
      (only-some-erased-matches (affineModality v₂) R₂)
      linearity→affine tr
  linearity→affine-preserves-only-some-erased-matches =
    Are-preserving-usage-restrictions-only-some-erased-matches
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              {p = 𝟘} _ → refl)
         ))

opaque

  -- If the functions linearity→affine and tr reflect certain usage
  -- restrictions, then they also do this for certain usage
  -- restrictions obtained using only-some-erased-matches.

  linearity→affine-reflects-only-some-erased-matches :
    Are-reflecting-usage-restrictions R₁ R₂
      linearity→affine tr →
    Are-reflecting-usage-restrictions
      (only-some-erased-matches (linearityModality v₁) R₁)
      (only-some-erased-matches (affineModality v₂) R₂)
      linearity→affine tr
  linearity→affine-reflects-only-some-erased-matches =
    Are-reflecting-usage-restrictions-only-some-erased-matches
      (λ _ →
           (λ ())
         , (λ where
              {p = 𝟘} _ → refl))

------------------------------------------------------------------------
-- Some lemmas related to no-erased-matches-UR and concrete
-- translation functions

-- If the functions unit→erasure and tr preserve certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches-UR, given a certain assumption.

unit→erasure-preserves-no-erased-matches-UR :
  Are-preserving-type-restrictions TR₁ TR₂ unit→erasure tr →
  Are-preserving-usage-restrictions R₁ R₂ unit→erasure tr →
  Are-preserving-usage-restrictions
    (no-erased-matches-UR (UnitModality v₁ v₁-ok) TR₁ R₁)
    (no-erased-matches-UR (ErasureModality v₂) TR₂ R₂)
    unit→erasure tr
unit→erasure-preserves-no-erased-matches-UR =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (λ _ → inj₂ (λ ()))

-- If the functions unit→erasure and tr reflect certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches-UR, given a certain assumption.

unit→erasure-reflects-no-erased-matches-UR :
  Are-reflecting-type-restrictions TR₁ TR₂ unit→erasure tr →
  Are-reflecting-usage-restrictions R₁ R₂ unit→erasure tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches-UR (UnitModality v₁ v₁-ok) TR₁ R₁)
    (no-erased-matches-UR (ErasureModality v₂) TR₂ R₂)
    unit→erasure tr
unit→erasure-reflects-no-erased-matches-UR =
  Are-reflecting-usage-restrictions-no-erased-matches-UR
    (λ tt≢tt → ⊥-elim $ tt≢tt refl)

-- If the functions erasure→unit and tr preserve certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches-UR, given a certain assumption.

erasure→unit-preserves-no-erased-matches-UR :
  Are-preserving-type-restrictions TR₁ TR₂ erasure→unit tr →
  Are-preserving-usage-restrictions R₁ R₂ erasure→unit tr →
  Are-preserving-usage-restrictions
    (no-erased-matches-UR (ErasureModality v₁) TR₁ R₁)
    (no-erased-matches-UR (UnitModality v₂ v₂-ok) TR₂ R₂)
    erasure→unit tr
erasure→unit-preserves-no-erased-matches-UR =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (λ tt≢tt → ⊥-elim $ tt≢tt refl)

-- The functions erasure→unit and tr do not reflect certain usage
-- restrictions obtained using no-erased-matches-UR.

¬-erasure→unit-reflects-no-erased-matches-UR :
  ∀ TR₁ TR₂ R →
  let 𝕄₂ = UnitModality v₂ v₂-ok in
  ¬ Are-reflecting-usage-restrictions
      (no-erased-matches-UR (ErasureModality v₁) TR₁ R)
      (no-erased-matches-UR 𝕄₂ TR₂ (no-usage-restrictions 𝕄₂ b₁ b₂))
      erasure→unit tr
¬-erasure→unit-reflects-no-erased-matches-UR _ _ _ r =
  Prodrec-reflected {p = 𝟘} {q = 𝟘} [ 𝟙ᵐ ] (_ , λ tt≢tt _ → tt≢tt)
    .proj₂ (λ ()) refl refl
  where
  open Are-reflecting-usage-restrictions r

-- If the functions erasure→zero-one-many and tr preserve certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches-UR, given a certain
-- assumption.

erasure→zero-one-many-preserves-no-erased-matches-UR :
  Are-preserving-type-restrictions TR₁ TR₂ erasure→zero-one-many tr →
  Are-preserving-usage-restrictions R₁ R₂
    erasure→zero-one-many tr →
  Are-preserving-usage-restrictions
    (no-erased-matches-UR (ErasureModality v₁) TR₁ R₁)
    (no-erased-matches-UR (zero-one-many-modality 𝟙≤𝟘 v₂) TR₂ R₂)
    erasure→zero-one-many tr
erasure→zero-one-many-preserves-no-erased-matches-UR =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions erasure→zero-one-many and tr reflect certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches-UR, given a certain assumption.

erasure→zero-one-many-reflects-no-erased-matches-UR :
  Are-reflecting-type-restrictions TR₁ TR₂ erasure→zero-one-many tr →
  Are-reflecting-usage-restrictions R₁ R₂
    erasure→zero-one-many tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches-UR (ErasureModality v₁) TR₁ R₁)
    (no-erased-matches-UR (zero-one-many-modality 𝟙≤𝟘 v₂) TR₂ R₂)
    erasure→zero-one-many tr
erasure→zero-one-many-reflects-no-erased-matches-UR =
  Are-reflecting-usage-restrictions-no-erased-matches-UR
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))

-- If the functions zero-one-many→erasure and tr preserve certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches-UR, given a certain
-- assumption.

zero-one-many→erasure-preserves-no-erased-matches-UR :
  Are-preserving-type-restrictions TR₁ TR₂ zero-one-many→erasure tr →
  Are-preserving-usage-restrictions R₁ R₂
    zero-one-many→erasure tr →
  Are-preserving-usage-restrictions
    (no-erased-matches-UR (zero-one-many-modality 𝟙≤𝟘 v₁) TR₁ R₁)
    (no-erased-matches-UR (ErasureModality v₂) TR₂ R₂)
    zero-one-many→erasure tr
zero-one-many→erasure-preserves-no-erased-matches-UR =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions zero-one-many→erasure and tr reflect certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches-UR, given a certain assumption.

zero-one-many→erasure-reflects-no-erased-matches-UR :
  Are-reflecting-type-restrictions TR₁ TR₂ zero-one-many→erasure tr →
  Are-reflecting-usage-restrictions R₁ R₂
    zero-one-many→erasure tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches-UR (zero-one-many-modality 𝟙≤𝟘 v₁) TR₁ R₁)
    (no-erased-matches-UR (ErasureModality v₂) TR₂ R₂)
    zero-one-many→erasure tr
zero-one-many→erasure-reflects-no-erased-matches-UR =
  Are-reflecting-usage-restrictions-no-erased-matches-UR
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))

-- If the functions linearity→linear-or-affine and tr preserve certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches-UR, given a certain
-- assumption.

linearity→linear-or-affine-preserves-no-erased-matches-UR :
  Are-preserving-type-restrictions TR₁ TR₂
    linearity→linear-or-affine tr →
  Are-preserving-usage-restrictions R₁ R₂
    linearity→linear-or-affine tr →
  Are-preserving-usage-restrictions
    (no-erased-matches-UR (linearityModality v₁) TR₁ R₁)
    (no-erased-matches-UR (linear-or-affine v₂) TR₂ R₂)
    linearity→linear-or-affine tr
linearity→linear-or-affine-preserves-no-erased-matches-UR =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions linearity→linear-or-affine and tr reflect certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches-UR, given a certain
-- assumption.

linearity→linear-or-affine-reflects-no-erased-matches-UR :
  Are-reflecting-type-restrictions TR₁ TR₂
    linearity→linear-or-affine tr →
  Are-reflecting-usage-restrictions R₁ R₂
    linearity→linear-or-affine tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches-UR (linearityModality v₁) TR₁ R₁)
    (no-erased-matches-UR (linear-or-affine v₂) TR₂ R₂)
    linearity→linear-or-affine tr
linearity→linear-or-affine-reflects-no-erased-matches-UR =
  Are-reflecting-usage-restrictions-no-erased-matches-UR
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))

-- If the functions linear-or-affine→linearity and tr preserve certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches-UR, given a certain
-- assumption.

linear-or-affine→linearity-preserves-no-erased-matches-UR :
  Are-preserving-type-restrictions TR₁ TR₂
    linear-or-affine→linearity tr →
  Are-preserving-usage-restrictions R₁ R₂
    linear-or-affine→linearity tr →
  Are-preserving-usage-restrictions
    (no-erased-matches-UR (linear-or-affine v₁) TR₁ R₁)
    (no-erased-matches-UR (linearityModality v₂) TR₂ R₂)
    linear-or-affine→linearity tr
linear-or-affine→linearity-preserves-no-erased-matches-UR =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions linear-or-affine→linearity and tr reflect certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches-UR, given a certain
-- assumption.

linear-or-affine→linearity-reflects-no-erased-matches-UR :
  Are-reflecting-type-restrictions TR₁ TR₂
    linear-or-affine→linearity tr →
  Are-reflecting-usage-restrictions R₁ R₂
    linear-or-affine→linearity tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches-UR (linear-or-affine v₁) TR₁ R₁)
    (no-erased-matches-UR (linearityModality v₂) TR₂ R₂)
    linear-or-affine→linearity tr
linear-or-affine→linearity-reflects-no-erased-matches-UR =
  Are-reflecting-usage-restrictions-no-erased-matches-UR
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))

-- If the functions affine→linear-or-affine and tr preserve certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches-UR, given a certain
-- assumption.

affine→linear-or-affine-preserves-no-erased-matches-UR :
  Are-preserving-type-restrictions TR₁ TR₂ affine→linear-or-affine tr →
  Are-preserving-usage-restrictions R₁ R₂
    affine→linear-or-affine tr →
  Are-preserving-usage-restrictions
    (no-erased-matches-UR (affineModality v₁) TR₁ R₁)
    (no-erased-matches-UR (linear-or-affine v₂) TR₂ R₂)
    affine→linear-or-affine tr
affine→linear-or-affine-preserves-no-erased-matches-UR =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions affine→linear-or-affine and tr reflect certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches-UR, given a certain
-- assumption.

affine→linear-or-affine-reflects-no-erased-matches-UR :
  Are-reflecting-type-restrictions TR₁ TR₂ affine→linear-or-affine tr →
  Are-reflecting-usage-restrictions R₁ R₂
    affine→linear-or-affine tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches-UR (affineModality v₁) TR₁ R₁)
    (no-erased-matches-UR (linear-or-affine v₂) TR₂ R₂)
    affine→linear-or-affine tr
affine→linear-or-affine-reflects-no-erased-matches-UR =
  Are-reflecting-usage-restrictions-no-erased-matches-UR
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))

-- If the functions linear-or-affine→affine and tr preserve certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches-UR, given a certain
-- assumption.

linear-or-affine→affine-preserves-no-erased-matches-UR :
  Are-preserving-type-restrictions TR₁ TR₂ linear-or-affine→affine tr →
  Are-preserving-usage-restrictions R₁ R₂
    linear-or-affine→affine tr →
  Are-preserving-usage-restrictions
    (no-erased-matches-UR (linear-or-affine v₁) TR₁ R₁)
    (no-erased-matches-UR (affineModality v₂) TR₂ R₂)
    linear-or-affine→affine tr
linear-or-affine→affine-preserves-no-erased-matches-UR =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions linear-or-affine→affine and tr reflect certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches-UR, given a certain
-- assumption.

linear-or-affine→affine-reflects-no-erased-matches-UR :
  Are-reflecting-type-restrictions TR₁ TR₂ linear-or-affine→affine tr →
  Are-reflecting-usage-restrictions R₁ R₂
    linear-or-affine→affine tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches-UR (linear-or-affine v₁) TR₁ R₁)
    (no-erased-matches-UR (affineModality v₂) TR₂ R₂)
    linear-or-affine→affine tr
linear-or-affine→affine-reflects-no-erased-matches-UR =
  Are-reflecting-usage-restrictions-no-erased-matches-UR
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))

-- If the functions affine→linearity and tr preserve certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches-UR, given a certain assumption.

affine→linearity-preserves-no-erased-matches-UR :
  Are-preserving-type-restrictions TR₁ TR₂ affine→linearity tr →
  Are-preserving-usage-restrictions R₁ R₂
    affine→linearity tr →
  Are-preserving-usage-restrictions
    (no-erased-matches-UR (affineModality v₁) TR₁ R₁)
    (no-erased-matches-UR (linearityModality v₂) TR₂ R₂)
    affine→linearity tr
affine→linearity-preserves-no-erased-matches-UR =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions affine→linearity and tr reflect certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches-UR, given a certain assumption.

affine→linearity-reflects-no-erased-matches-UR :
  Are-reflecting-type-restrictions TR₁ TR₂ affine→linearity tr →
  Are-reflecting-usage-restrictions R₁ R₂
    affine→linearity tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches-UR (affineModality v₁) TR₁ R₁)
    (no-erased-matches-UR (linearityModality v₂) TR₂ R₂)
    affine→linearity tr
affine→linearity-reflects-no-erased-matches-UR =
  Are-reflecting-usage-restrictions-no-erased-matches-UR
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))

-- If the functions linearity→affine and tr preserve certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches-UR, given a certain assumption.

linearity→affine-preserves-no-erased-matches-UR :
  Are-preserving-type-restrictions TR₁ TR₂ linearity→affine tr →
  Are-preserving-usage-restrictions R₁ R₂
    linearity→affine tr →
  Are-preserving-usage-restrictions
    (no-erased-matches-UR (linearityModality v₁) TR₁ R₁)
    (no-erased-matches-UR (affineModality v₂) TR₂ R₂)
    linearity→affine tr
linearity→affine-preserves-no-erased-matches-UR =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _ → refl)
       ))

-- If the functions linearity→affine and tr reflect certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches-UR, given a certain assumption.

linearity→affine-reflects-no-erased-matches-UR :
  Are-reflecting-type-restrictions TR₁ TR₂ linearity→affine tr →
  Are-reflecting-usage-restrictions R₁ R₂
    linearity→affine tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches-UR (linearityModality v₁) TR₁ R₁)
    (no-erased-matches-UR (affineModality v₂) TR₂ R₂)
    linearity→affine tr
linearity→affine-reflects-no-erased-matches-UR =
  Are-reflecting-usage-restrictions-no-erased-matches-UR
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _ → refl))
