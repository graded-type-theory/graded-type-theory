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
open import Tools.Sum as ⊎ using (_⊎_; inj₁; inj₂)
import Tools.Reasoning.PartialOrder

open import Definition.Typed.Restrictions

open import Graded.Modality
open import Graded.Modality.Morphism
open import Graded.Modality.Morphism.Examples
open import Graded.Modality.Morphism.Type-restrictions
open import Graded.Modality.Morphism.Usage-restrictions
open import Graded.Modality.Instances.Affine
  using (Affine; affineModality)
open import Graded.Modality.Instances.Erasure
  using (Erasure; 𝟘; ω)
open import Graded.Modality.Instances.Erasure.Modality
  using (ErasureModality; erasure-has-well-behaved-zero)
open import Graded.Modality.Instances.Linear-or-affine
  using (Linear-or-affine; 𝟘; 𝟙; ≤𝟙; ≤ω; linear-or-affine;
         linear-or-affine-has-well-behaved-zero)
open import Graded.Modality.Instances.Linearity
  using (Linearity; linearityModality)
open import Graded.Modality.Instances.Unit using (UnitModality)
open import Graded.Modality.Instances.Zero-one-many
  using (Zero-one-many; 𝟘; 𝟙; ω; zero-one-many-modality;
         zero-one-many-has-well-behaved-zero)
open import Graded.Mode.Instances.Zero-one.Variant
open import Graded.Mode.Instances.Zero-one
open import Graded.Mode.Instances.Zero-one.QuantityTranslation.Primitive
import Graded.Modality.Properties
open import Graded.Restrictions.Zero-one
open import Graded.Usage.Erased-matches
open import Graded.Usage.Restrictions
open import Graded.Usage.Restrictions.Natrec

open Usage-restrictions

private variable
  b₁ b₂ 𝟙≤𝟘 ok : Bool
  v₁ v₂        : Mode-variant _
  R R₁ R₂      : Usage-restrictions _ _
  TR₁ TR₂      : Type-restrictions _
  A M₁ M₂      : Set _
  𝕄₁ 𝕄₂        : Modality _
  m₁ m₂        : Mode _
  tr tr-Σ      : M₁ → M₂
  v₁-ok v₂-ok  : A
  nm₁ nm₂      : Natrec-mode _

------------------------------------------------------------------------
-- Preserving/reflecting no usage restrictions

opaque

  -- Common-properties holds for certain usage restrictions obtained
  -- from no-usage-restrictions, given that a certain assumption
  -- holds.

  Common-properties-no-usage-restrictions :
    (T (Mode-variant.𝟘ᵐ-allowed v₁) → T (Mode-variant.𝟘ᵐ-allowed v₂)) →
    nm₁ ≈ⁿᵐ nm₂ →
    Common-properties
      (no-usage-restrictions 𝕄₁ v₁ nm₁ b₁ b₂)
      (no-usage-restrictions 𝕄₂ v₂ nm₂ b₁ b₂)
  Common-properties-no-usage-restrictions hyp nm₁≈nm₂ = λ where
      .𝟘ᵐ-preserved                   → hyp
      .natrec-mode-preserved          → nm₁≈nm₂
      .starˢ-sink-preserved           → refl
      .Id-erased-preserved            → lift ∘→ Lift.lower
                                      , lift ∘→ Lift.lower
      .erased-matches-for-J-preserved → _
      .erased-matches-for-K-preserved → _
    where
    open Common-properties

opaque

  -- The functions tr and tr-Σ preserve certain usage restrictions
  -- obtained from no-usage-restrictions, given that certain
  -- assumptions hold.

  Are-preserving-usage-restrictions-no-usage-restrictions :
    (T (Mode-variant.𝟘ᵐ-allowed v₁) → T (Mode-variant.𝟘ᵐ-allowed v₂)) →
    nm₁ ≈ⁿᵐ nm₂ →
    (⦃ has-nr₁ : Natrec-mode-has-nr _ nm₁ ⦄ →
     ⦃ has-nr₂ : Natrec-mode-has-nr _ nm₂ ⦄ →
     Is-nr-preserving-morphism 𝕄₁ 𝕄₂
       ⦃ has-nr₁ = Natrec-mode-Has-nr 𝕄₁ has-nr₁ ⦄
       ⦃ has-nr₂ = Natrec-mode-Has-nr 𝕄₂ has-nr₂ ⦄ tr) →
    (⦃ no-nr₁ : Natrec-mode-no-nr _ nm₁ ⦄ →
     ⦃ no-nr₂ : Natrec-mode-no-nr _ nm₂ ⦄ →
     Is-no-nr-preserving 𝕄₁ 𝕄₂ v₁ v₂) →
    (⦃ no-nr₁ : Natrec-mode-no-nr-glb _ nm₁ ⦄ →
     ⦃ no-nr₂ : Natrec-mode-no-nr-glb _ nm₂ ⦄ →
     Is-no-nr-glb-preserving-morphism 𝕄₁ 𝕄₂ tr) →
    Are-preserving-usage-restrictions
      (no-usage-restrictions 𝕄₁ v₁ nm₁ b₁ b₂)
      (no-usage-restrictions 𝕄₂ v₂ nm₂ b₁ b₂)
      tr tr-Σ
  Are-preserving-usage-restrictions-no-usage-restrictions
    hyp₁ nm₁≈nm₂ hyp₂ hyp₃ hyp₄ = λ where
      .common-properties  → Common-properties-no-usage-restrictions hyp₁ nm₁≈nm₂
      .nr-preserving → hyp₂
      .no-nr-preserving → hyp₃
      .no-nr-glb-preserving → hyp₄
      .Prodrec-preserved → _
      .Unitrec-preserved → _
      .Emptyrec-preserved → _
      .[]-cong-mode-preserved → _
    where
    open Are-preserving-usage-restrictions

opaque

  -- The functions tr and tr-Σ reflect certain usage restrictions
  -- obtained from no-usage-restrictions, given that certain
  -- assumptions hold.

  Are-reflecting-usage-restrictions-no-usage-restrictions :
    let module M₁ = Modality 𝕄₁
        module M₂ = Modality 𝕄₂
        module V₁ = Mode-variant v₁
        module V₂ = Mode-variant v₂
    in
    (T V₁.𝟘ᵐ-allowed → T V₂.𝟘ᵐ-allowed) →
    (T V₂.𝟘ᵐ-allowed ⊎ M₂.Trivial → T V₁.𝟘ᵐ-allowed ⊎ M₁.Trivial) →
    nm₁ ≈ⁿᵐ nm₂ →
    (⦃ has-nr₁ : Natrec-mode-has-nr _ nm₁ ⦄ →
     ⦃ has-nr₂ : Natrec-mode-has-nr _ nm₂ ⦄ →
     Is-nr-reflecting-morphism 𝕄₁ 𝕄₂
       ⦃ has-nr₁ = Natrec-mode-Has-nr 𝕄₁ has-nr₁ ⦄
       ⦃ has-nr₂ = Natrec-mode-Has-nr 𝕄₂ has-nr₂ ⦄ tr) →
    (⦃ no-nr₁ : Natrec-mode-no-nr _ nm₁ ⦄ →
     ⦃ no-nr₂ : Natrec-mode-no-nr _ nm₂ ⦄ →
     Is-no-nr-reflecting-morphism 𝕄₁ 𝕄₂ v₁ v₂ tr) →
    (⦃ no-nr₁ : Natrec-mode-no-nr-glb _ nm₁ ⦄ →
     ⦃ no-nr₂ : Natrec-mode-no-nr-glb _ nm₂ ⦄ →
     Is-no-nr-glb-reflecting-morphism 𝕄₁ 𝕄₂ tr) →
    Are-reflecting-usage-restrictions
      (no-usage-restrictions 𝕄₁ v₁ nm₁ b₁ b₂)
      (no-usage-restrictions 𝕄₂ v₂ nm₂ b₁ b₂)
      tr tr-Σ
  Are-reflecting-usage-restrictions-no-usage-restrictions
    hyp₁ hyp₂ nm₁≈nm₂ hyp₃ hyp₄ hyp₅ =
    λ where
      .common-properties →
        Common-properties-no-usage-restrictions hyp₁ nm₁≈nm₂
      .𝟘ᵐ-reflected                   → hyp₂
      .nr-reflected                   → hyp₃
      .no-nr-reflected                → hyp₄
      .no-nr-glb-reflected            → hyp₅
      .Prodrec-reflected              → _
      .Unitrec-reflected              → _
      .Emptyrec-reflected             → _
      .[]-cong-mode-reflected         → _
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
      (only-some-erased-matches 𝕄₁ v₁ R₁)
      (only-some-erased-matches 𝕄₂ v₂ R₂)
  Common-properties-only-some-erased-matches cp = record
    { 𝟘ᵐ-preserved                   = 𝟘ᵐ-preserved
    ; natrec-mode-preserved          = natrec-mode-preserved
    ; starˢ-sink-preserved           = starˢ-sink-preserved
    ; Id-erased-preserved            = Id-erased-preserved
    ; erased-matches-for-J-preserved = λ where
        𝟙ᵐ → _
        𝟘ᵐ → erased-matches-for-J-preserved 𝟘ᵐ?≈𝟘ᵐ?′
    ; erased-matches-for-K-preserved = λ where
        𝟙ᵐ → _
        𝟘ᵐ → erased-matches-for-K-preserved 𝟘ᵐ?≈𝟘ᵐ?′
    }
    where
    open Common-properties cp

opaque

  -- If the functions tr and tr-Σ preserve certain usage restrictions,
  -- then they also do this for certain usage restrictions obtained
  -- using only-some-erased-matches, given that certain assumptions
  -- hold.

  Are-preserving-usage-restrictions-only-some-erased-matches :
    (¬ Modality.Trivial 𝕄₂ →
     ¬ Modality.Trivial 𝕄₁ ×
     (∀ {p} → tr p ≡ Modality.𝟘 𝕄₂ → p ≡ Modality.𝟘 𝕄₁) ⊎
     (∀ {p} → tr p ≢ Modality.𝟘 𝕄₂)) →
    Are-preserving-usage-restrictions R₁ R₂ tr tr-Σ →
    Are-preserving-usage-restrictions
      (only-some-erased-matches 𝕄₁ v₁ R₁)
      (only-some-erased-matches 𝕄₂ v₂ R₂)
      tr tr-Σ
  Are-preserving-usage-restrictions-only-some-erased-matches
    {𝕄₂} {𝕄₁} {tr} hyp r = record
    { common-properties =
        Common-properties-only-some-erased-matches common-properties
    ; nr-preserving = nr-preserving
    ; no-nr-preserving = no-nr-preserving
    ; no-nr-glb-preserving = no-nr-glb-preserving
    ; Prodrec-preserved = λ {r = r} m₁≈m₂ (p , ≢𝟘) →
          Prodrec-preserved m₁≈m₂ p
        , (λ ≡𝟙ᵐ 𝟙≢𝟘 → case hyp 𝟙≢𝟘 of λ where
             (inj₁ (𝟙≢𝟘 , tr-≡-𝟘-→)) →
               tr r ≡ M₂.𝟘  →⟨ tr-≡-𝟘-→ ⟩
               r ≡ M₁.𝟘     →⟨ ≢𝟘 (≈ᵐ→≡𝟙ᵐ→≡𝟙ᵐ m₁≈m₂ ≡𝟙ᵐ) 𝟙≢𝟘 ⟩
               ⊥            □
             (inj₂ ≢𝟘) →
               tr r ≡ M₂.𝟘  →⟨ ≢𝟘 ⟩
               ⊥            □)
    ; Unitrec-preserved =
        Unitrec-preserved
    ; Emptyrec-preserved =
        Emptyrec-preserved
    ; []-cong-mode-preserved =
        []-cong-mode-preserved
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
      (only-some-erased-matches 𝕄₁ v₁ R₁)
      (only-some-erased-matches 𝕄₂ v₂ R₂)
      tr tr-Σ
  Are-reflecting-usage-restrictions-only-some-erased-matches
    {𝕄₁} {𝕄₂} {tr} hyp r = record
    { common-properties =
        Common-properties-only-some-erased-matches common-properties
    ; 𝟘ᵐ-reflected =
        𝟘ᵐ-reflected
    ; nr-reflected = nr-reflected
    ; no-nr-reflected = no-nr-reflected
    ; no-nr-glb-reflected = no-nr-glb-reflected
    ; Prodrec-reflected = λ {r = r} m₁≲m₂ (prodrec-ok , tr-r≢𝟘) →
          Prodrec-reflected m₁≲m₂ prodrec-ok
        , (λ m₁≡𝟙ᵐ non-trivial₁ →
             case m₁≲m₂ of λ where
               [ m₁≈m₂ ] →
                 r ≡ M₁.𝟘     →⟨ hyp non-trivial₁ .proj₂ ⟩
                 tr r ≡ M₂.𝟘  →⟨ tr-r≢𝟘 (≈ᵐ→≡𝟙ᵐ←≡𝟙ᵐ m₁≈m₂ m₁≡𝟙ᵐ) (hyp non-trivial₁ .proj₁) ⟩
                 ⊥            □
               (𝟙ᵐ≳𝟘ᵐ trivial₁) _ →
                 non-trivial₁ trivial₁)
    ; Unitrec-reflected =
        Unitrec-reflected
    ; Emptyrec-reflected =
        Emptyrec-reflected
    ; []-cong-mode-reflected =
        []-cong-mode-reflected
    ; erased-matches-for-J-reflected = λ where
        𝟙ᵐ → _
        𝟘ᵐ → erased-matches-for-J-reflected 𝟘ᵐ?≈𝟘ᵐ?′
    ; erased-matches-for-K-reflected = λ where
        𝟙ᵐ → _
        𝟘ᵐ → erased-matches-for-K-reflected 𝟘ᵐ?≈𝟘ᵐ?′
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
    (no-erased-matches-UR 𝕄₁ v₁ TR₁ R₁)
    (no-erased-matches-UR 𝕄₂ v₂ TR₂ R₂)
Common-properties-no-erased-matches-UR _ _ cp = record
  { 𝟘ᵐ-preserved                   = 𝟘ᵐ-preserved
  ; natrec-mode-preserved          = natrec-mode-preserved
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
    (no-erased-matches-UR 𝕄₁ v₁ TR₁ R₁)
    (no-erased-matches-UR 𝕄₂ v₂ TR₂ R₂)
    tr tr-Σ
Are-preserving-usage-restrictions-no-erased-matches-UR
  {𝕄₂} {𝕄₁} {tr} {TR₁} {TR₂} hyp tp up = record
  { common-properties =
      Common-properties-no-erased-matches-UR TR₁ TR₂
        UP.common-properties
  ; nr-preserving = UP.nr-preserving
  ; no-nr-preserving = UP.no-nr-preserving
  ; no-nr-glb-preserving = UP.no-nr-glb-preserving
  ; Prodrec-preserved =
      Are-preserving-usage-restrictions.Prodrec-preserved
        (Are-preserving-usage-restrictions-only-some-erased-matches
           hyp up)
  ; Unitrec-preserved = λ {p = p} m₁≈m₂ (P , η) →
        UP.Unitrec-preserved m₁≈m₂ P
      , (λ ≡𝟙ᵐ 𝟙≢𝟘 → case hyp 𝟙≢𝟘 of λ where
           (inj₁ (𝟙≢𝟘 , tr-≡-𝟘-→)) →
             tr p ≡ M₂.𝟘  →⟨ tr-≡-𝟘-→ ⟩
             p ≡ M₁.𝟘     →⟨ η (≈ᵐ→≡𝟙ᵐ→≡𝟙ᵐ m₁≈m₂ ≡𝟙ᵐ) 𝟙≢𝟘 ⟩
             TR₁.Unitʷ-η  →⟨ TP.Unitʷ-η-preserved ⟩
             TR₂.Unitʷ-η  □
           (inj₂ ≢𝟘) →
             tr p ≡ M₂.𝟘  →⟨ ≢𝟘 ⟩
             ⊥            →⟨ ⊥-elim ⟩
             TR₂.Unitʷ-η  □)
  ; Emptyrec-preserved =
      UP.Emptyrec-preserved
  ; []-cong-mode-preserved =
      UP.[]-cong-mode-preserved
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
    (no-erased-matches-UR 𝕄₁ v₁ TR₁ R₁)
    (no-erased-matches-UR 𝕄₂ v₂ TR₂ R₂)
    tr tr-Σ
Are-reflecting-usage-restrictions-no-erased-matches-UR
  {𝕄₁} {𝕄₂} {tr} {TR₁} {TR₂} hyp tp up = record
  { common-properties =
      Common-properties-no-erased-matches-UR TR₁ TR₂
        (Are-reflecting-usage-restrictions.common-properties up)
  ; 𝟘ᵐ-reflected =
      UR.𝟘ᵐ-reflected
  ; nr-reflected = UR.nr-reflected
  ; no-nr-reflected = UR.no-nr-reflected
  ; no-nr-glb-reflected = UR.no-nr-glb-reflected
  ; Prodrec-reflected =
      UR.Prodrec-reflected
  ; Unitrec-reflected = λ {p = p} m₁≲m₂ (unitrec-ok , tr-p≢𝟘) →
        UR.Unitrec-reflected m₁≲m₂ unitrec-ok
      , (λ m₁≡𝟙ᵐ non-trivial₁ →
           case m₁≲m₂ of λ where
             [ m₁≈m₂ ] →
               p ≡ M₁.𝟘     →⟨ hyp non-trivial₁ .proj₂ ⟩
               tr p ≡ M₂.𝟘  →⟨ tr-p≢𝟘 (≈ᵐ→≡𝟙ᵐ←≡𝟙ᵐ m₁≈m₂ m₁≡𝟙ᵐ) (hyp non-trivial₁ .proj₁) ⟩
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
  ; []-cong-mode-reflected =
      UR.[]-cong-mode-reflected
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
    (f₁ : Mode v₁ → Erased-matches)
    (f₂ : Mode v₂ → Erased-matches) →
    f₁ m₁ ≤ᵉᵐ f₂ m₂ →
    m₁ ≈ᵐ m₂ →
    not-all-for-𝟙ᵐ 𝕄₁ v₁ f₁ m₁ ≤ᵉᵐ not-all-for-𝟙ᵐ 𝕄₂ v₂ f₂ m₂
  not-all-for-𝟙ᵐ-≤ᵉᵐ _  _  hyp 𝟘ᵐ = hyp
  not-all-for-𝟙ᵐ-≤ᵉᵐ f₁ f₂ hyp 𝟙ᵐ with f₁ 𝟙ᵐ | f₂ 𝟙ᵐ
  … | none | _    = _
  … | some | none = ⊥-elim hyp
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
      (not-all-erased-matches-JK 𝕄₁ v₁ R₁)
      (not-all-erased-matches-JK 𝕄₂ v₂ R₂)
  Common-properties-not-all-erased-matches-JK
    {R₁} {R₂} cp = record
    { 𝟘ᵐ-preserved                   = 𝟘ᵐ-preserved
    ; natrec-mode-preserved          = natrec-mode-preserved
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
      (not-all-erased-matches-JK 𝕄₁ v₁ R₁)
      (not-all-erased-matches-JK 𝕄₂ v₂ R₂)
      tr tr-Σ
  Are-preserving-usage-restrictions-not-all-erased-matches-JK
    r = record
    { common-properties =
        Common-properties-not-all-erased-matches-JK common-properties
    ; nr-preserving = nr-preserving
    ; no-nr-preserving = no-nr-preserving
    ; no-nr-glb-preserving = no-nr-glb-preserving
    ; Prodrec-preserved =
        Prodrec-preserved
    ; Unitrec-preserved =
        Unitrec-preserved
    ; Emptyrec-preserved =
        Emptyrec-preserved
    ; []-cong-mode-preserved =
        []-cong-mode-preserved
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
      (not-all-erased-matches-JK 𝕄₁ v₁ R₁)
      (not-all-erased-matches-JK 𝕄₂ v₂ R₂)
      tr tr-Σ
  Are-reflecting-usage-restrictions-not-all-erased-matches-JK
    {𝕄₁} {R₁} {𝕄₂} {R₂} r = record
    { common-properties =
        Common-properties-not-all-erased-matches-JK common-properties
    ; 𝟘ᵐ-reflected =
        𝟘ᵐ-reflected
    ; nr-reflected = nr-reflected
    ; no-nr-reflected = no-nr-reflected
    ; no-nr-glb-reflected = no-nr-glb-reflected
    ; Prodrec-reflected =
        Prodrec-reflected
    ; Unitrec-reflected =
        Unitrec-reflected
    ; Emptyrec-reflected =
        Emptyrec-reflected
    ; []-cong-mode-reflected =
        []-cong-mode-reflected
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

opaque

  -- The function []-cong-UR preserves Common-properties in a certain
  -- way.

  Common-properties-[]-cong-UR :
    Common-properties R₁ R₂ →
    Common-properties
      ([]-cong-UR 𝕄₁ v₁ R₁)
      ([]-cong-UR 𝕄₂ v₂ R₂)
  Common-properties-[]-cong-UR cp = record
    { 𝟘ᵐ-preserved                   = 𝟘ᵐ-preserved
    ; natrec-mode-preserved          = natrec-mode-preserved
    ; starˢ-sink-preserved           = starˢ-sink-preserved
    ; Id-erased-preserved            = Id-erased-preserved
    ; erased-matches-for-J-preserved = _
    ; erased-matches-for-K-preserved = erased-matches-for-K-preserved
    }
    where
    open Common-properties cp

opaque

  -- If the functions tr and tr-Σ preserve certain usage restrictions,
  -- then they also do this for certain usage restrictions obtained
  -- using []-cong-UR, given a certain assumption.

  Are-preserving-usage-restrictions-[]-cong-UR :
    let module M₁ = Modality 𝕄₁
        module M₂ = Modality 𝕄₂
    in
    (M₂.Trivial → M₁.Trivial) →
    Are-preserving-usage-restrictions R₁ R₂ tr tr-Σ →
    Are-preserving-usage-restrictions
      ([]-cong-UR 𝕄₁ v₁ R₁)
      ([]-cong-UR 𝕄₂ v₂ R₂)
      tr tr-Σ
  Are-preserving-usage-restrictions-[]-cong-UR hyp r = record
    { common-properties =
        Common-properties-[]-cong-UR common-properties
    ; nr-preserving =
        nr-preserving
    ; no-nr-preserving =
        no-nr-preserving
    ; no-nr-glb-preserving =
        no-nr-glb-preserving
    ; Prodrec-preserved =
        Prodrec-preserved
    ; Unitrec-preserved =
        Unitrec-preserved
    ; Emptyrec-preserved =
        Emptyrec-preserved
    ; []-cong-mode-preserved = λ m₁≈m₂ →
        ⊎.map ([]-cong-mode-preserved m₁≈m₂) (_∘→ hyp)
    }
    where
    open Are-preserving-usage-restrictions r

opaque

  -- If the functions tr and tr-Σ reflect certain usage restrictions,
  -- then they also do this for certain usage restrictions obtained
  -- using []-cong-UR, given a certain assumption.

  Are-reflecting-usage-restrictions-[]-cong-UR :
    let module M₁ = Modality 𝕄₁
        module M₂ = Modality 𝕄₂
    in
    (M₁.Trivial → M₂.Trivial) →
    Are-reflecting-usage-restrictions R₁ R₂ tr tr-Σ →
    Are-reflecting-usage-restrictions
      ([]-cong-UR 𝕄₁ v₁ R₁)
      ([]-cong-UR 𝕄₂ v₂ R₂)
      tr tr-Σ
  Are-reflecting-usage-restrictions-[]-cong-UR {𝕄₂} hyp r = record
    { common-properties =
        Common-properties-[]-cong-UR common-properties
    ; 𝟘ᵐ-reflected =
        𝟘ᵐ-reflected
    ; nr-reflected =
        nr-reflected
    ; no-nr-reflected =
        no-nr-reflected
    ; no-nr-glb-reflected =
        no-nr-glb-reflected
    ; Prodrec-reflected =
        Prodrec-reflected
    ; Unitrec-reflected =
        Unitrec-reflected
    ; Emptyrec-reflected =
        Emptyrec-reflected
    ; []-cong-mode-reflected = λ where
        m₁≳m₂ (inj₁ ok) →
          inj₁ ([]-cong-mode-reflected m₁≳m₂ ok)
        m₁≳m₂ (inj₂ ¬trivial) →
          inj₂ (¬trivial ∘→ hyp)
    ; erased-matches-for-J-reflected =
        _
    ; erased-matches-for-K-reflected =
        erased-matches-for-K-reflected
    }
    where
    module M₂ = Modality 𝕄₂
    open Are-reflecting-usage-restrictions r

private opaque

  -- A lemma related to at-least-some.

  at-least-some-≤ᵉᵐ :
    (f₁ : Mode v₁ → Erased-matches)
    (f₂ : Mode v₂ → Erased-matches) →
    f₁ m₁ ≤ᵉᵐ f₂ m₂ → m₁ ≈ᵐ m₂ →
    at-least-some 𝕄₁ v₁ f₁ m₁ ≤ᵉᵐ at-least-some 𝕄₂ v₂ f₂ m₂
  at-least-some-≤ᵉᵐ {m₁} {m₂} f₁ f₂ hyp eq with f₁ m₁ | f₂ m₂
  … | none       | none       = _
  … | none       | some       = _
  … | none       | all        = _
  … | some       | none       = _
  … | all        | none       = hyp
  … | not-none _ | not-none _ = hyp

opaque

  -- The function no-[]-cong-UR preserves Common-properties in a
  -- certain way.

  Common-properties-no-[]-cong-UR :
    Common-properties R₁ R₂ →
    Common-properties
      (no-[]-cong-UR 𝕄₁ v₁ R₁)
      (no-[]-cong-UR 𝕄₂ v₂ R₂)
  Common-properties-no-[]-cong-UR {R₁} {R₂} cp = record
    { 𝟘ᵐ-preserved                   = 𝟘ᵐ-preserved
    ; natrec-mode-preserved          = natrec-mode-preserved
    ; starˢ-sink-preserved           = starˢ-sink-preserved
    ; Id-erased-preserved            = Id-erased-preserved
    ; erased-matches-for-J-preserved = λ m₁≈m₂ →
        at-least-some-≤ᵉᵐ R₁.erased-matches-for-J
          R₂.erased-matches-for-J (erased-matches-for-J-preserved m₁≈m₂)
          m₁≈m₂
    ; erased-matches-for-K-preserved = erased-matches-for-K-preserved
    }
    where
    module R₁ = Usage-restrictions R₁
    module R₂ = Usage-restrictions R₂
    open Common-properties cp

opaque

  -- If the functions tr and tr-Σ preserve certain usage restrictions,
  -- then they also do this for certain usage restrictions obtained
  -- using no-[]-cong-UR.

  Are-preserving-usage-restrictions-no-[]-cong-UR :
    Are-preserving-usage-restrictions R₁ R₂ tr tr-Σ →
    Are-preserving-usage-restrictions
      (no-[]-cong-UR 𝕄₁ v₁ R₁)
      (no-[]-cong-UR 𝕄₂ v₂ R₂)
      tr tr-Σ
  Are-preserving-usage-restrictions-no-[]-cong-UR r = record
    { common-properties =
        Common-properties-no-[]-cong-UR common-properties
    ; nr-preserving =
        nr-preserving
    ; no-nr-preserving =
        no-nr-preserving
    ; no-nr-glb-preserving =
        no-nr-glb-preserving
    ; Prodrec-preserved =
        Prodrec-preserved
    ; Unitrec-preserved =
        Unitrec-preserved
    ; Emptyrec-preserved =
        Emptyrec-preserved
    ; []-cong-mode-preserved =
        λ _ ()
    }
    where
    open Are-preserving-usage-restrictions r

opaque

  -- If the functions tr and tr-Σ reflect certain usage restrictions,
  -- then they also do this for certain usage restrictions obtained
  -- using no-[]-cong-UR, given a certain assumption.

  Are-reflecting-usage-restrictions-no-[]-cong-UR :
    let module M₁ = Modality 𝕄₁
        module M₂ = Modality 𝕄₂
        module V₂ = Mode-variant v₂
    in
    ¬ (M₁.Trivial × T V₂.𝟘ᵐ-allowed) →
    Are-reflecting-usage-restrictions R₁ R₂ tr tr-Σ →
    Are-reflecting-usage-restrictions
      (no-[]-cong-UR 𝕄₁ v₁ R₁)
      (no-[]-cong-UR 𝕄₂ v₂ R₂)
      tr tr-Σ
  Are-reflecting-usage-restrictions-no-[]-cong-UR
    {R₁} {R₂} hyp r = record
    { common-properties =
        Common-properties-no-[]-cong-UR common-properties
    ; 𝟘ᵐ-reflected =
        𝟘ᵐ-reflected
    ; nr-reflected = nr-reflected
    ; no-nr-reflected = no-nr-reflected
    ; no-nr-glb-reflected = no-nr-glb-reflected
    ; Prodrec-reflected =
        Prodrec-reflected
    ; Unitrec-reflected =
        Unitrec-reflected
    ; Emptyrec-reflected =
        Emptyrec-reflected
    ; []-cong-mode-reflected = λ where
        _ ()
    ; erased-matches-for-J-reflected = λ m₁≈m₂ →
        at-least-some-≤ᵉᵐ
          R₂.erased-matches-for-J R₁.erased-matches-for-J
          (erased-matches-for-J-reflected m₁≈m₂) (≈ᵐ-symmetric m₁≈m₂)
    ; erased-matches-for-K-reflected =
        erased-matches-for-K-reflected
    }
    where
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
      (only-some-erased-matches UnitModality v₁ R₁)
      (only-some-erased-matches ErasureModality v₂ R₂)
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
      (only-some-erased-matches UnitModality v₁ R₁)
      (only-some-erased-matches ErasureModality v₂ R₂)
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
      (only-some-erased-matches ErasureModality v₁ R₁)
      (only-some-erased-matches UnitModality v₂ R₂)
      erasure→unit tr
  erasure→unit-preserves-only-some-erased-matches =
    Are-preserving-usage-restrictions-only-some-erased-matches
      (λ tt≢tt → ⊥-elim $ tt≢tt refl)

opaque

  -- The functions erasure→unit and tr do not reflect certain usage
  -- restrictions obtained using only-some-erased-matches.

  ¬-erasure→unit-reflects-only-some-erased-matches :
    ∀ R →
    let 𝕄₂ = UnitModality in
    ¬ Are-reflecting-usage-restrictions
        (only-some-erased-matches ErasureModality v₁ R)
        (only-some-erased-matches 𝕄₂ v₂ (no-usage-restrictions 𝕄₂ v₂ nm₁ b₁ b₂))
        erasure→unit tr
  ¬-erasure→unit-reflects-only-some-erased-matches _ r =
    Prodrec-reflected {p = 𝟘} {q = 𝟘} [ 𝟙ᵐ ] (_ , (λ _ tt≢tt → tt≢tt))
      .proj₂ refl (λ ()) refl
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
      (only-some-erased-matches ErasureModality v₁ R₁)
      (only-some-erased-matches (zero-one-many-modality 𝟙≤𝟘) v₂ R₂)
      erasure→zero-one-many tr
  erasure→zero-one-many-preserves-only-some-erased-matches =
    Are-preserving-usage-restrictions-only-some-erased-matches
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              {p = 𝟘} _  → refl
              {p = ω} ())
         ))

opaque

  -- If the functions erasure→zero-one-many and tr reflect certain
  -- usage restrictions, then they also do this for certain usage
  -- restrictions obtained using only-some-erased-matches.

  erasure→zero-one-many-reflects-only-some-erased-matches :
    Are-reflecting-usage-restrictions R₁ R₂
      erasure→zero-one-many tr →
    Are-reflecting-usage-restrictions
      (only-some-erased-matches ErasureModality v₁ R₁)
      (only-some-erased-matches (zero-one-many-modality 𝟙≤𝟘) v₂ R₂)
      erasure→zero-one-many tr
  erasure→zero-one-many-reflects-only-some-erased-matches =
    Are-reflecting-usage-restrictions-only-some-erased-matches
      (λ _ →
           (λ ())
         , (λ where
              {p = 𝟘} _  → refl
              {p = ω} ()))

opaque

  -- If the functions zero-one-many→erasure and tr preserve certain
  -- usage restrictions, then they also do this for certain usage
  -- restrictions obtained using only-some-erased-matches.

  zero-one-many→erasure-preserves-only-some-erased-matches :
    Are-preserving-usage-restrictions R₁ R₂
      zero-one-many→erasure tr →
    Are-preserving-usage-restrictions
      (only-some-erased-matches (zero-one-many-modality 𝟙≤𝟘) v₁ R₁)
      (only-some-erased-matches (ErasureModality) v₂ R₂)
      zero-one-many→erasure tr
  zero-one-many→erasure-preserves-only-some-erased-matches =
    Are-preserving-usage-restrictions-only-some-erased-matches
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              {p = 𝟘} _  → refl
              {p = 𝟙} ()
              {p = ω} ())
         ))

opaque

  -- If the functions zero-one-many→erasure and tr reflect certain
  -- usage restrictions, then they also do this for certain usage
  -- restrictions obtained using only-some-erased-matches.

  zero-one-many→erasure-reflects-only-some-erased-matches :
    Are-reflecting-usage-restrictions R₁ R₂
      zero-one-many→erasure tr →
    Are-reflecting-usage-restrictions
      (only-some-erased-matches (zero-one-many-modality 𝟙≤𝟘) v₁ R₁)
      (only-some-erased-matches ErasureModality v₂ R₂)
      zero-one-many→erasure tr
  zero-one-many→erasure-reflects-only-some-erased-matches =
    Are-reflecting-usage-restrictions-only-some-erased-matches
      (λ _ →
           (λ ())
         , (λ where
              {p = 𝟘} _  → refl
              {p = 𝟙} ()
              {p = ω} ()))

opaque

  -- If the functions linearity→linear-or-affine and tr preserve
  -- certain usage restrictions, then they also do this for certain
  -- usage restrictions obtained using only-some-erased-matches.

  linearity→linear-or-affine-preserves-only-some-erased-matches :
    Are-preserving-usage-restrictions R₁ R₂
      linearity→linear-or-affine tr →
    Are-preserving-usage-restrictions
      (only-some-erased-matches linearityModality v₁ R₁)
      (only-some-erased-matches linear-or-affine v₂ R₂)
      linearity→linear-or-affine tr
  linearity→linear-or-affine-preserves-only-some-erased-matches =
    Are-preserving-usage-restrictions-only-some-erased-matches
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              {p = 𝟘} _  → refl
              {p = 𝟙} ()
              {p = ω} ())
         ))

opaque

  -- If the functions linearity→linear-or-affine and tr reflect
  -- certain usage restrictions, then they also do this for certain
  -- usage restrictions obtained using only-some-erased-matches.

  linearity→linear-or-affine-reflects-only-some-erased-matches :
    Are-reflecting-usage-restrictions R₁ R₂
      linearity→linear-or-affine tr →
    Are-reflecting-usage-restrictions
      (only-some-erased-matches linearityModality v₁ R₁)
      (only-some-erased-matches linear-or-affine v₂ R₂)
      linearity→linear-or-affine tr
  linearity→linear-or-affine-reflects-only-some-erased-matches =
    Are-reflecting-usage-restrictions-only-some-erased-matches
      (λ _ →
           (λ ())
         , (λ where
              {p = 𝟘} _  → refl
              {p = 𝟙} ()
              {p = ω} ()))

opaque

  -- If the functions linear-or-affine→linearity and tr preserve
  -- certain usage restrictions, then they also do this for certain
  -- usage restrictions obtained using only-some-erased-matches.

  linear-or-affine→linearity-preserves-only-some-erased-matches :
    Are-preserving-usage-restrictions R₁ R₂
      linear-or-affine→linearity tr →
    Are-preserving-usage-restrictions
      (only-some-erased-matches linear-or-affine v₁ R₁)
      (only-some-erased-matches linearityModality v₂ R₂)
      linear-or-affine→linearity tr
  linear-or-affine→linearity-preserves-only-some-erased-matches =
    Are-preserving-usage-restrictions-only-some-erased-matches
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              {p = 𝟘}  _  → refl
              {p = 𝟙}  ()
              {p = ≤𝟙} ()
              {p = ≤ω} ())
         ))

opaque

  -- If the functions linear-or-affine→linearity and tr reflect
  -- certain usage restrictions, then they also do this for certain
  -- usage restrictions obtained using only-some-erased-matches.

  linear-or-affine→linearity-reflects-only-some-erased-matches :
    Are-reflecting-usage-restrictions R₁ R₂
      linear-or-affine→linearity tr →
    Are-reflecting-usage-restrictions
      (only-some-erased-matches linear-or-affine v₁ R₁)
      (only-some-erased-matches linearityModality v₂ R₂)
      linear-or-affine→linearity tr
  linear-or-affine→linearity-reflects-only-some-erased-matches =
    Are-reflecting-usage-restrictions-only-some-erased-matches
      (λ _ →
           (λ ())
         , (λ where
              {p = 𝟘}  _  → refl
              {p = 𝟙}  ()
              {p = ≤𝟙} ()
              {p = ≤ω} ()))

opaque

  -- If the functions affine→linear-or-affine and tr preserve certain
  -- usage restrictions, then they also do this for certain usage
  -- restrictions obtained using only-some-erased-matches.

  affine→linear-or-affine-preserves-only-some-erased-matches :
    Are-preserving-usage-restrictions R₁ R₂
      affine→linear-or-affine tr →
    Are-preserving-usage-restrictions
      (only-some-erased-matches affineModality v₁ R₁)
      (only-some-erased-matches linear-or-affine v₂ R₂)
      affine→linear-or-affine tr
  affine→linear-or-affine-preserves-only-some-erased-matches =
    Are-preserving-usage-restrictions-only-some-erased-matches
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              {p = 𝟘} _  → refl
              {p = 𝟙} ()
              {p = ω} ())
         ))

opaque

  -- If the functions affine→linear-or-affine and tr reflect certain
  -- usage restrictions, then they also do this for certain usage
  -- restrictions obtained using only-some-erased-matches.

  affine→linear-or-affine-reflects-only-some-erased-matches :
    Are-reflecting-usage-restrictions R₁ R₂
      affine→linear-or-affine tr →
    Are-reflecting-usage-restrictions
      (only-some-erased-matches affineModality v₁ R₁)
      (only-some-erased-matches linear-or-affine v₂ R₂)
      affine→linear-or-affine tr
  affine→linear-or-affine-reflects-only-some-erased-matches =
    Are-reflecting-usage-restrictions-only-some-erased-matches
      (λ _ →
           (λ ())
         , (λ where
              {p = 𝟘} _  → refl
              {p = 𝟙} ()
              {p = ω} ()))

opaque

  -- If the functions linear-or-affine→affine and tr preserve certain
  -- usage restrictions, then they also do this for certain usage
  -- restrictions obtained using only-some-erased-matches.

  linear-or-affine→affine-preserves-only-some-erased-matches :
    Are-preserving-usage-restrictions R₁ R₂
      linear-or-affine→affine tr →
    Are-preserving-usage-restrictions
      (only-some-erased-matches linear-or-affine v₁ R₁)
      (only-some-erased-matches affineModality v₂ R₂)
      linear-or-affine→affine tr
  linear-or-affine→affine-preserves-only-some-erased-matches =
    Are-preserving-usage-restrictions-only-some-erased-matches
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              {p = 𝟘}  _  → refl
              {p = 𝟙}  ()
              {p = ≤𝟙} ()
              {p = ≤ω} ())
         ))

opaque

  -- If the functions linear-or-affine→affine and tr reflect certain
  -- usage restrictions, then they also do this for certain usage
  -- restrictions obtained using only-some-erased-matches.

  linear-or-affine→affine-reflects-only-some-erased-matches :
    Are-reflecting-usage-restrictions R₁ R₂
      linear-or-affine→affine tr →
    Are-reflecting-usage-restrictions
      (only-some-erased-matches linear-or-affine v₁ R₁)
      (only-some-erased-matches affineModality v₂ R₂)
      linear-or-affine→affine tr
  linear-or-affine→affine-reflects-only-some-erased-matches =
    Are-reflecting-usage-restrictions-only-some-erased-matches
      (λ _ →
           (λ ())
         , (λ where
              {p = 𝟘}  _  → refl
              {p = 𝟙}  ()
              {p = ≤𝟙} ()
              {p = ≤ω} ()))

opaque

  -- If the functions affine→linearity and tr preserve certain usage
  -- restrictions, then they also do this for certain usage
  -- restrictions obtained using only-some-erased-matches.

  affine→linearity-preserves-only-some-erased-matches :
    Are-preserving-usage-restrictions R₁ R₂
      affine→linearity tr →
    Are-preserving-usage-restrictions
      (only-some-erased-matches affineModality v₁ R₁)
      (only-some-erased-matches linearityModality v₂ R₂)
      affine→linearity tr
  affine→linearity-preserves-only-some-erased-matches =
    Are-preserving-usage-restrictions-only-some-erased-matches
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              {p = 𝟘} _  → refl
              {p = 𝟙} ()
              {p = ω} ())
         ))

opaque

  -- If the functions affine→linearity and tr reflect certain usage
  -- restrictions, then they also do this for certain usage
  -- restrictions obtained using only-some-erased-matches.

  affine→linearity-reflects-only-some-erased-matches :
    Are-reflecting-usage-restrictions R₁ R₂
      affine→linearity tr →
    Are-reflecting-usage-restrictions
      (only-some-erased-matches affineModality v₁ R₁)
      (only-some-erased-matches linearityModality v₂ R₂)
      affine→linearity tr
  affine→linearity-reflects-only-some-erased-matches =
    Are-reflecting-usage-restrictions-only-some-erased-matches
      (λ _ →
           (λ ())
         , (λ where
              {p = 𝟘} _  → refl
              {p = 𝟙} ()
              {p = ω} ()))

opaque

  -- If the functions linearity→affine and tr preserve certain usage
  -- restrictions, then they also do this for certain usage
  -- restrictions obtained using only-some-erased-matches.

  linearity→affine-preserves-only-some-erased-matches :
    Are-preserving-usage-restrictions R₁ R₂
      linearity→affine tr →
    Are-preserving-usage-restrictions
      (only-some-erased-matches linearityModality v₁ R₁)
      (only-some-erased-matches affineModality v₂ R₂)
      linearity→affine tr
  linearity→affine-preserves-only-some-erased-matches =
    Are-preserving-usage-restrictions-only-some-erased-matches
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              {p = 𝟘} _  → refl
              {p = 𝟙} ()
              {p = ω} ())
         ))

opaque

  -- If the functions linearity→affine and tr reflect certain usage
  -- restrictions, then they also do this for certain usage
  -- restrictions obtained using only-some-erased-matches.

  linearity→affine-reflects-only-some-erased-matches :
    Are-reflecting-usage-restrictions R₁ R₂
      linearity→affine tr →
    Are-reflecting-usage-restrictions
      (only-some-erased-matches linearityModality v₁ R₁)
      (only-some-erased-matches affineModality v₂ R₂)
      linearity→affine tr
  linearity→affine-reflects-only-some-erased-matches =
    Are-reflecting-usage-restrictions-only-some-erased-matches
      (λ _ →
           (λ ())
         , (λ where
              {p = 𝟘} _  → refl
              {p = 𝟙} ()
              {p = ω} ()))

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
    (no-erased-matches-UR UnitModality v₁ TR₁ R₁)
    (no-erased-matches-UR ErasureModality v₂ TR₂ R₂)
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
    (no-erased-matches-UR UnitModality v₁ TR₁ R₁)
    (no-erased-matches-UR ErasureModality v₂ TR₂ R₂)
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
    (no-erased-matches-UR ErasureModality v₁ TR₁ R₁)
    (no-erased-matches-UR UnitModality v₂ TR₂ R₂)
    erasure→unit tr
erasure→unit-preserves-no-erased-matches-UR =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (λ tt≢tt → ⊥-elim $ tt≢tt refl)

-- The functions erasure→unit and tr do not reflect certain usage
-- restrictions obtained using no-erased-matches-UR.

¬-erasure→unit-reflects-no-erased-matches-UR :
  ∀ TR₁ TR₂ R →
  let 𝕄₂ = UnitModality in
  ¬ Are-reflecting-usage-restrictions
      (no-erased-matches-UR ErasureModality v₁ TR₁ R)
      (no-erased-matches-UR 𝕄₂ v₂ TR₂ (no-usage-restrictions 𝕄₂ v₂ nm₂ b₁ b₂))
      erasure→unit tr
¬-erasure→unit-reflects-no-erased-matches-UR _ _ _ r =
  Prodrec-reflected {p = 𝟘} {q = 𝟘} [ 𝟙ᵐ ] (_ , λ _ tt≢tt → tt≢tt)
    .proj₂ refl (λ ()) refl
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
    (no-erased-matches-UR ErasureModality v₁ TR₁ R₁)
    (no-erased-matches-UR (zero-one-many-modality 𝟙≤𝟘) v₂ TR₂ R₂)
    erasure→zero-one-many tr
erasure→zero-one-many-preserves-no-erased-matches-UR =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _  → refl
            {p = ω} ())
       ))

-- If the functions erasure→zero-one-many and tr reflect certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches-UR, given a certain assumption.

erasure→zero-one-many-reflects-no-erased-matches-UR :
  Are-reflecting-type-restrictions TR₁ TR₂ erasure→zero-one-many tr →
  Are-reflecting-usage-restrictions R₁ R₂
    erasure→zero-one-many tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches-UR ErasureModality v₁ TR₁ R₁)
    (no-erased-matches-UR (zero-one-many-modality 𝟙≤𝟘) v₂ TR₂ R₂)
    erasure→zero-one-many tr
erasure→zero-one-many-reflects-no-erased-matches-UR =
  Are-reflecting-usage-restrictions-no-erased-matches-UR
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _  → refl
            {p = ω} ()))

-- If the functions zero-one-many→erasure and tr preserve certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches-UR, given a certain
-- assumption.

zero-one-many→erasure-preserves-no-erased-matches-UR :
  Are-preserving-type-restrictions TR₁ TR₂ zero-one-many→erasure tr →
  Are-preserving-usage-restrictions R₁ R₂
    zero-one-many→erasure tr →
  Are-preserving-usage-restrictions
    (no-erased-matches-UR (zero-one-many-modality 𝟙≤𝟘) v₁ TR₁ R₁)
    (no-erased-matches-UR ErasureModality v₂ TR₂ R₂)
    zero-one-many→erasure tr
zero-one-many→erasure-preserves-no-erased-matches-UR =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _  → refl
            {p = 𝟙} ()
            {p = ω} ())
       ))

-- If the functions zero-one-many→erasure and tr reflect certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches-UR, given a certain assumption.

zero-one-many→erasure-reflects-no-erased-matches-UR :
  Are-reflecting-type-restrictions TR₁ TR₂ zero-one-many→erasure tr →
  Are-reflecting-usage-restrictions R₁ R₂
    zero-one-many→erasure tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches-UR (zero-one-many-modality 𝟙≤𝟘) v₁ TR₁ R₁)
    (no-erased-matches-UR ErasureModality v₂ TR₂ R₂)
    zero-one-many→erasure tr
zero-one-many→erasure-reflects-no-erased-matches-UR =
  Are-reflecting-usage-restrictions-no-erased-matches-UR
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _  → refl
            {p = 𝟙} ()
            {p = ω} ()))

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
    (no-erased-matches-UR linearityModality v₁ TR₁ R₁)
    (no-erased-matches-UR linear-or-affine v₂ TR₂ R₂)
    linearity→linear-or-affine tr
linearity→linear-or-affine-preserves-no-erased-matches-UR =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _  → refl
            {p = 𝟙} ()
            {p = ω} ())
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
    (no-erased-matches-UR linearityModality v₁ TR₁ R₁)
    (no-erased-matches-UR linear-or-affine v₂ TR₂ R₂)
    linearity→linear-or-affine tr
linearity→linear-or-affine-reflects-no-erased-matches-UR =
  Are-reflecting-usage-restrictions-no-erased-matches-UR
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _  → refl
            {p = 𝟙} ()
            {p = ω} ()))

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
    (no-erased-matches-UR linear-or-affine v₁ TR₁ R₁)
    (no-erased-matches-UR linearityModality v₂ TR₂ R₂)
    linear-or-affine→linearity tr
linear-or-affine→linearity-preserves-no-erased-matches-UR =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘}  _  → refl
            {p = 𝟙}  ()
            {p = ≤𝟙} ()
            {p = ≤ω} ())
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
    (no-erased-matches-UR linear-or-affine v₁ TR₁ R₁)
    (no-erased-matches-UR linearityModality v₂ TR₂ R₂)
    linear-or-affine→linearity tr
linear-or-affine→linearity-reflects-no-erased-matches-UR =
  Are-reflecting-usage-restrictions-no-erased-matches-UR
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘}  _  → refl
            {p = 𝟙}  ()
            {p = ≤𝟙} ()
            {p = ≤ω} ()))

-- If the functions affine→linear-or-affine and tr preserve certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches-UR, given a certain
-- assumption.

affine→linear-or-affine-preserves-no-erased-matches-UR :
  Are-preserving-type-restrictions TR₁ TR₂ affine→linear-or-affine tr →
  Are-preserving-usage-restrictions R₁ R₂
    affine→linear-or-affine tr →
  Are-preserving-usage-restrictions
    (no-erased-matches-UR affineModality v₁ TR₁ R₁)
    (no-erased-matches-UR linear-or-affine v₂ TR₂ R₂)
    affine→linear-or-affine tr
affine→linear-or-affine-preserves-no-erased-matches-UR =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _  → refl
            {p = 𝟙} ()
            {p = ω} ())
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
    (no-erased-matches-UR affineModality v₁ TR₁ R₁)
    (no-erased-matches-UR linear-or-affine v₂ TR₂ R₂)
    affine→linear-or-affine tr
affine→linear-or-affine-reflects-no-erased-matches-UR =
  Are-reflecting-usage-restrictions-no-erased-matches-UR
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _  → refl
            {p = 𝟙} ()
            {p = ω} ()))

-- If the functions linear-or-affine→affine and tr preserve certain
-- usage restrictions, then they also do this for certain usage
-- restrictions obtained using no-erased-matches-UR, given a certain
-- assumption.

linear-or-affine→affine-preserves-no-erased-matches-UR :
  Are-preserving-type-restrictions TR₁ TR₂ linear-or-affine→affine tr →
  Are-preserving-usage-restrictions R₁ R₂
    linear-or-affine→affine tr →
  Are-preserving-usage-restrictions
    (no-erased-matches-UR linear-or-affine v₁ TR₁ R₁)
    (no-erased-matches-UR affineModality v₂ TR₂ R₂)
    linear-or-affine→affine tr
linear-or-affine→affine-preserves-no-erased-matches-UR =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘}  _  → refl
            {p = 𝟙}  ()
            {p = ≤𝟙} ()
            {p = ≤ω} ())
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
    (no-erased-matches-UR linear-or-affine v₁ TR₁ R₁)
    (no-erased-matches-UR affineModality v₂ TR₂ R₂)
    linear-or-affine→affine tr
linear-or-affine→affine-reflects-no-erased-matches-UR =
  Are-reflecting-usage-restrictions-no-erased-matches-UR
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘}  _  → refl
            {p = 𝟙}  ()
            {p = ≤𝟙} ()
            {p = ≤ω} ()))

-- If the functions affine→linearity and tr preserve certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches-UR, given a certain assumption.

affine→linearity-preserves-no-erased-matches-UR :
  Are-preserving-type-restrictions TR₁ TR₂ affine→linearity tr →
  Are-preserving-usage-restrictions R₁ R₂
    affine→linearity tr →
  Are-preserving-usage-restrictions
    (no-erased-matches-UR affineModality v₁ TR₁ R₁)
    (no-erased-matches-UR linearityModality v₂ TR₂ R₂)
    affine→linearity tr
affine→linearity-preserves-no-erased-matches-UR =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _  → refl
            {p = 𝟙} ()
            {p = ω} ())
       ))

-- If the functions affine→linearity and tr reflect certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches-UR, given a certain assumption.

affine→linearity-reflects-no-erased-matches-UR :
  Are-reflecting-type-restrictions TR₁ TR₂ affine→linearity tr →
  Are-reflecting-usage-restrictions R₁ R₂
    affine→linearity tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches-UR affineModality v₁ TR₁ R₁)
    (no-erased-matches-UR linearityModality v₂ TR₂ R₂)
    affine→linearity tr
affine→linearity-reflects-no-erased-matches-UR =
  Are-reflecting-usage-restrictions-no-erased-matches-UR
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _  → refl
            {p = 𝟙} ()
            {p = ω} ()))

-- If the functions linearity→affine and tr preserve certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches-UR, given a certain assumption.

linearity→affine-preserves-no-erased-matches-UR :
  Are-preserving-type-restrictions TR₁ TR₂ linearity→affine tr →
  Are-preserving-usage-restrictions R₁ R₂
    linearity→affine tr →
  Are-preserving-usage-restrictions
    (no-erased-matches-UR linearityModality v₁ TR₁ R₁)
    (no-erased-matches-UR affineModality v₂ TR₂ R₂)
    linearity→affine tr
linearity→affine-preserves-no-erased-matches-UR =
  Are-preserving-usage-restrictions-no-erased-matches-UR
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            {p = 𝟘} _  → refl
            {p = 𝟙} ()
            {p = ω} ())
       ))

-- If the functions linearity→affine and tr reflect certain usage
-- restrictions, then they also do this for certain usage restrictions
-- obtained using no-erased-matches-UR, given a certain assumption.

linearity→affine-reflects-no-erased-matches-UR :
  Are-reflecting-type-restrictions TR₁ TR₂ linearity→affine tr →
  Are-reflecting-usage-restrictions R₁ R₂
    linearity→affine tr →
  Are-reflecting-usage-restrictions
    (no-erased-matches-UR linearityModality v₁ TR₁ R₁)
    (no-erased-matches-UR affineModality v₂ TR₂ R₂)
    linearity→affine tr
linearity→affine-reflects-no-erased-matches-UR =
  Are-reflecting-usage-restrictions-no-erased-matches-UR
    (λ _ →
         (λ ())
       , (λ where
            {p = 𝟘} _  → refl
            {p = 𝟙} ()
            {p = ω} ()))


------------------------------------------------------------------------
-- Some lemmas related to Is-no-nr-preserving and concrete modalities

opaque

  -- no-nr preservation between Unit and Erasure

  unit⇒erasure-no-nr-preserving :
    Is-no-nr-preserving
      UnitModality ErasureModality
      v₁ v₂
  unit⇒erasure-no-nr-preserving = λ where
      .𝟘ᵐ-in-first-if-in-second _ → inj₂ refl
      .𝟘-well-behaved-in-first-if-in-second _ → inj₂ refl
    where
    open Is-no-nr-preserving

opaque

  -- no-nr preservation between Erasure and Zero-one-many

  erasure⇨zero-one-many-no-nr-preserving :
    (T (Mode-variant.𝟘ᵐ-allowed v₂) → T (Mode-variant.𝟘ᵐ-allowed v₁)) →
    Is-no-nr-preserving
      ErasureModality
      (zero-one-many-modality 𝟙≤𝟘)
      v₁ v₂
  erasure⇨zero-one-many-no-nr-preserving hyp = λ where
      .𝟘ᵐ-in-first-if-in-second ok →
        inj₁ (hyp ok)
      .𝟘-well-behaved-in-first-if-in-second ok →
        inj₁ erasure-has-well-behaved-zero
    where
    open Is-no-nr-preserving

opaque

  -- no-nr preservation between Zero-one-many and Erasure

  zero-one-many⇒erasure-no-nr-preserving :
    (T (Mode-variant.𝟘ᵐ-allowed v₂) → T (Mode-variant.𝟘ᵐ-allowed v₁)) →
    Is-no-nr-preserving
      (zero-one-many-modality 𝟙≤𝟘)
      ErasureModality
      v₁ v₂
  zero-one-many⇒erasure-no-nr-preserving {𝟙≤𝟘} hyp = λ where
      .𝟘ᵐ-in-first-if-in-second ok →
        inj₁ (hyp ok)
      .𝟘-well-behaved-in-first-if-in-second _ →
        inj₁ (zero-one-many-has-well-behaved-zero 𝟙≤𝟘)
    where
    open Is-no-nr-preserving

opaque

  -- no-nr preservation between Erasure and Linear types

  erasure⇒linearity-no-nr-preserving :
    (T (Mode-variant.𝟘ᵐ-allowed v₂) → T (Mode-variant.𝟘ᵐ-allowed v₁)) →
    Is-no-nr-preserving
      ErasureModality
      linearityModality
      v₁ v₂
  erasure⇒linearity-no-nr-preserving =
    erasure⇨zero-one-many-no-nr-preserving

opaque

  -- no-nr preservation between Erasure and Affine types

  erasure⇒affine-no-nr-preserving :
    (T (Mode-variant.𝟘ᵐ-allowed v₂) → T (Mode-variant.𝟘ᵐ-allowed v₁)) →
    Is-no-nr-preserving
      ErasureModality
      affineModality
      v₁ v₂
  erasure⇒affine-no-nr-preserving = erasure⇨zero-one-many-no-nr-preserving

opaque

  -- no-nr preservation between Linear types and Erasure

  linearity⇒erasure-no-nr-preserving :
    (T (Mode-variant.𝟘ᵐ-allowed v₂) → T (Mode-variant.𝟘ᵐ-allowed v₁)) →
    Is-no-nr-preserving
      linearityModality
      ErasureModality
      v₁ v₂
  linearity⇒erasure-no-nr-preserving = zero-one-many⇒erasure-no-nr-preserving

opaque

  -- no-nr preservation between Affine types and Erasure

  affine⇒erasure-no-nr-preserving :
    (T (Mode-variant.𝟘ᵐ-allowed v₂) → T (Mode-variant.𝟘ᵐ-allowed v₁)) →
    Is-no-nr-preserving
      affineModality
      ErasureModality
      v₁ v₂
  affine⇒erasure-no-nr-preserving = zero-one-many⇒erasure-no-nr-preserving

opaque

  -- no-nr preservation between Linear types and Linear or affine types

  linearity⇨linear-or-affine-no-nr-preserving :
    (T (Mode-variant.𝟘ᵐ-allowed v₂) → T (Mode-variant.𝟘ᵐ-allowed v₁)) →
    Is-no-nr-preserving
      linearityModality
      linear-or-affine
      v₁ v₂
  linearity⇨linear-or-affine-no-nr-preserving hyp = λ where
      .𝟘ᵐ-in-first-if-in-second ok →
        inj₁ (hyp ok)
      .𝟘-well-behaved-in-first-if-in-second _ →
        inj₁ (zero-one-many-has-well-behaved-zero false)
    where
    open Is-no-nr-preserving

opaque

  -- no-nr preservation between Linear or affine types and Linear types

  linear-or-affine⇨linearity-no-nr-preserving :
    (T (Mode-variant.𝟘ᵐ-allowed v₂) → T (Mode-variant.𝟘ᵐ-allowed v₁)) →
    Is-no-nr-preserving
      linear-or-affine
      linearityModality
      v₁ v₂
  linear-or-affine⇨linearity-no-nr-preserving hyp = λ where
      .𝟘ᵐ-in-first-if-in-second ok →
        inj₁ (hyp ok)
      .𝟘-well-behaved-in-first-if-in-second _ →
        inj₁ linear-or-affine-has-well-behaved-zero
    where
    open Is-no-nr-preserving

opaque

  -- no-nr preservation between Affine types and Linear or affine types

  affine⇨linear-or-affine-no-nr-preserving :
    (T (Mode-variant.𝟘ᵐ-allowed v₂) → T (Mode-variant.𝟘ᵐ-allowed v₁)) →
    Is-no-nr-preserving
      affineModality
      linear-or-affine
      v₁ v₂
  affine⇨linear-or-affine-no-nr-preserving hyp = λ where
      .𝟘ᵐ-in-first-if-in-second ok →
        inj₁ (hyp ok)
      .𝟘-well-behaved-in-first-if-in-second _ →
        inj₁ (zero-one-many-has-well-behaved-zero true)
    where
    open Is-no-nr-preserving

opaque

  -- no-nr preservation between Linear or affine types and Affine types

  linear-or-affine⇨affine-no-nr-preserving :
    (T (Mode-variant.𝟘ᵐ-allowed v₂) → T (Mode-variant.𝟘ᵐ-allowed v₁)) →
    Is-no-nr-preserving
      linear-or-affine
      affineModality
      v₁ v₂
  linear-or-affine⇨affine-no-nr-preserving hyp = λ where
      .𝟘ᵐ-in-first-if-in-second ok →
        inj₁ (hyp ok)
      .𝟘-well-behaved-in-first-if-in-second _ →
        inj₁ linear-or-affine-has-well-behaved-zero
    where
    open Is-no-nr-preserving

opaque

  -- no-nr preservation between Affine types and Linear types

  affine⇨linearity-no-nr-preserving :
    (T (Mode-variant.𝟘ᵐ-allowed v₂) → T (Mode-variant.𝟘ᵐ-allowed v₁)) →
    Is-no-nr-preserving
      affineModality
      linearityModality
      v₁ v₂
  affine⇨linearity-no-nr-preserving hyp = λ where
      .𝟘ᵐ-in-first-if-in-second ok →
        inj₁ (hyp ok)
      .𝟘-well-behaved-in-first-if-in-second _ →
        inj₁ (zero-one-many-has-well-behaved-zero true)
    where
    open Is-no-nr-preserving

opaque

  -- no-nr preservation between Linear types and Affine types

  linearity⇨affine-no-nr-preserving :
    (T (Mode-variant.𝟘ᵐ-allowed v₂) → T (Mode-variant.𝟘ᵐ-allowed v₁)) →
    Is-no-nr-preserving
      linearityModality
      affineModality
      v₁ v₂
  linearity⇨affine-no-nr-preserving hyp = λ where
      .𝟘ᵐ-in-first-if-in-second ok →
        inj₁ (hyp ok)
      .𝟘-well-behaved-in-first-if-in-second _ →
        inj₁ (zero-one-many-has-well-behaved-zero false)
    where
    open Is-no-nr-preserving

------------------------------------------------------------------------
-- Some lemmas related to Is-no-nr-reflecting-morphism and concrete
-- translation functions

opaque

  -- The property tr-≤-no-nr follows from other properties.

  →tr-≤-no-nr :
    ∀ {p q₁ q₂ q₃ q₄ r s} →
    (𝕄₁ : Modality M₁) (𝕄₂ : Modality M₂) →
    (v₁ : Mode-variant 𝕄₁) (v₂ : Mode-variant 𝕄₂) →
    let
      module M₁ = Modality 𝕄₁
      module M₂ = Modality 𝕄₂
    in
    (T (Mode-variant.𝟘ᵐ-allowed v₁) → T (Mode-variant.𝟘ᵐ-allowed v₂)) →
    (⦃ 𝟘-well-behaved :
         Has-well-behaved-zero M₁ M₁.semiring-with-meet ⦄ →
     Has-well-behaved-zero M₂ M₂.semiring-with-meet) →
    (tr : M₁ → M₂)
    (tr⁻¹ : M₂ → M₁) →
    (∀ p q → p M₂.≤ q → tr⁻¹ p M₁.≤ tr⁻¹ q) →
    (∀ p q → tr p M₂.≤ q → p M₁.≤ tr⁻¹ q) →
    (∀ p → tr (tr⁻¹ p) M₂.≤ p) →
    (∀ p q → tr⁻¹ (p M₂.+ q) M₁.≤ tr⁻¹ p M₁.+ tr⁻¹ q) →
    (∀ p q → tr⁻¹ (p M₂.∧ q) M₁.≤ tr⁻¹ p M₁.∧ tr⁻¹ q) →
    (∀ p q → tr⁻¹ (tr p M₂.· q) M₁.≤ p M₁.· tr⁻¹ q) →
    tr p M₂.≤ q₁ →
    q₁ M₂.≤ q₂ →
    (T (Mode-variant.𝟘ᵐ-allowed v₂) →
     q₁ M₂.≤ q₃) →
    (⦃ 𝟘-well-behaved : Has-well-behaved-zero M₂ M₂.semiring-with-meet ⦄ →
     q₁ M₂.≤ q₄) →
    q₁ M₂.≤ q₃ M₂.+ tr r M₂.· q₄ M₂.+ tr s M₂.· q₁ →
    ∃₄ λ q₁′ q₂′ q₃′ q₄′ →
       tr q₂′ M₂.≤ q₂ ×
       tr q₃′ M₂.≤ q₃ ×
       tr q₄′ M₂.≤ q₄ ×
       p M₁.≤ q₁′ ×
       q₁′ M₁.≤ q₂′ ×
       (T (Mode-variant.𝟘ᵐ-allowed v₁) →
        q₁′ M₁.≤ q₃′) ×
       (⦃ 𝟘-well-behaved :
            Has-well-behaved-zero M₁ M₁.semiring-with-meet ⦄ →
        q₁′ M₁.≤ q₄′) ×
       q₁′ M₁.≤ q₃′ M₁.+ r M₁.· q₄′ M₁.+ s M₁.· q₁′
  →tr-≤-no-nr
    {q₁ = q₁} {q₂ = q₂} {q₃ = q₃} {q₄ = q₄} {r = r} {s = s}
    𝕄₁ 𝕄₂ _ _ 𝟘ᵐ-in-second-if-in-first 𝟘-well-behaved-in-second-if-in-first
    tr tr⁻¹ tr⁻¹-monotone tr≤→≤tr⁻¹ tr-tr⁻¹≤ tr⁻¹-+ tr⁻¹-∧ tr⁻¹-·
    hyp₁ hyp₂ hyp₃ hyp₄ hyp₅ =
      tr⁻¹ q₁
    , tr⁻¹ q₂
    , tr⁻¹ q₃
    , tr⁻¹ q₄
    , tr-tr⁻¹≤ _
    , tr-tr⁻¹≤ _
    , tr-tr⁻¹≤ _
    , tr≤→≤tr⁻¹ _ _ hyp₁
    , tr⁻¹-monotone _ _ hyp₂
    , tr⁻¹-monotone _ _ ∘→ hyp₃ ∘→ 𝟘ᵐ-in-second-if-in-first
    , tr⁻¹-monotone _ _
        (hyp₄ ⦃ 𝟘-well-behaved = 𝟘-well-behaved-in-second-if-in-first ⦄)
    , (begin
         tr⁻¹ q₁                                                    ≤⟨ tr⁻¹-monotone _ _ hyp₅ ⟩
         tr⁻¹ (q₃ M₂.+ tr r M₂.· q₄ M₂.+ tr s M₂.· q₁)              ≤⟨ ≤-trans (tr⁻¹-+ _ _) $ +-monotoneʳ $ tr⁻¹-+ _ _ ⟩
         tr⁻¹ q₃ M₁.+ tr⁻¹ (tr r M₂.· q₄) M₁.+ tr⁻¹ (tr s M₂.· q₁)  ≤⟨ +-monotoneʳ $ +-monotone (tr⁻¹-· _ _) (tr⁻¹-· _ _) ⟩
         tr⁻¹ q₃ M₁.+ r M₁.· tr⁻¹ q₄ M₁.+ s M₁.· tr⁻¹ q₁            ∎)
    where
    module M₁ = Modality 𝕄₁
    module M₂ = Modality 𝕄₂
    open Graded.Modality.Properties 𝕄₁
    open Tools.Reasoning.PartialOrder ≤-poset

opaque

  -- The function unit→erasure is no-nr reflecting

  unit⇒erasure-no-nr-reflecting :
    Is-no-nr-reflecting-morphism
      UnitModality
      ErasureModality
      v₁ v₂
      unit→erasure
  unit⇒erasure-no-nr-reflecting = λ where
      .tr-≤-no-nr _ _ _ _ _ →
        _ , _ , _ , _ , refl , refl , refl , refl
          , refl , (λ _ → refl) , refl , refl
    where
    open Is-no-nr-reflecting-morphism

opaque

  -- The function erasure→zero-one-many is no-nr reflecting

  erasure⇨zero-one-many-no-nr-reflecting :
    (T (Mode-variant.𝟘ᵐ-allowed v₁) → T (Mode-variant.𝟘ᵐ-allowed v₂)) →
    Is-no-nr-reflecting-morphism
      ErasureModality
      (zero-one-many-modality 𝟙≤𝟘)
      v₁ v₂
      erasure→zero-one-many
  erasure⇨zero-one-many-no-nr-reflecting {v₁} {𝟙≤𝟘} {v₂} hyp = λ where
      .tr-≤-no-nr {r} {s} → →tr-≤-no-nr {r = r} {s = s}
        ErasureModality
        (zero-one-many-modality 𝟙≤𝟘) v₁ v₂
        hyp
        𝟘𝟙ω.zero-one-many-has-well-behaved-zero
        tr′ tr⁻¹ tr⁻¹-monotone tr≤→≤tr⁻¹ tr-tr⁻¹≤
        (λ p q → ≤-reflexive (tr⁻¹-+ p q))
        (λ p q → ≤-reflexive (tr⁻¹-∧ p q))
        λ p q → ≤-reflexive (tr⁻¹-· p q)
    where
    open Is-no-nr-reflecting-morphism
    module 𝟘𝟙ω = Graded.Modality.Instances.Zero-one-many 𝟙≤𝟘
    module E = Modality ErasureModality
    open Graded.Modality.Properties ErasureModality
    tr′ : Erasure → Zero-one-many 𝟙≤𝟘
    tr′ = erasure→zero-one-many
    tr⁻¹ : Zero-one-many 𝟙≤𝟘 → Erasure
    tr⁻¹ = zero-one-many→erasure
    tr⁻¹-monotone :
      ∀ p q → p 𝟘𝟙ω.≤ q →
      tr⁻¹ p E.≤ tr⁻¹ q
    tr⁻¹-monotone = λ where
      𝟘 𝟘 _     → refl
      𝟘 𝟙 𝟘≡𝟘∧𝟙 → ⊥-elim (𝟘𝟙ω.𝟘∧𝟙≢𝟘 (sym 𝟘≡𝟘∧𝟙))
      𝟙 𝟘 _     → refl
      𝟙 𝟙 _     → refl
      ω 𝟘 _     → refl
      ω 𝟙 _     → refl
      ω ω _     → refl
      𝟘 ω ()
      𝟙 ω ()
    tr≤→≤tr⁻¹ : ∀ p q → tr′ p 𝟘𝟙ω.≤ q → p E.≤ tr⁻¹ q
    tr≤→≤tr⁻¹ = λ where
      𝟘 𝟘 _     → refl
      𝟘 𝟙 𝟘≡𝟘∧𝟙 → ⊥-elim (𝟘𝟙ω.𝟘∧𝟙≢𝟘 (sym 𝟘≡𝟘∧𝟙))
      ω 𝟘 _     → refl
      ω 𝟙 _     → refl
      ω ω _     → refl
      𝟘 ω ()
    tr-tr⁻¹≤ : ∀ p → tr′ (tr⁻¹ p) 𝟘𝟙ω.≤ p
    tr-tr⁻¹≤ = λ where
      𝟘 → refl
      𝟙 → refl
      ω → refl
    tr⁻¹-𝟘∧𝟙 : tr⁻¹ 𝟘𝟙ω.𝟘∧𝟙 ≡ ω
    tr⁻¹-𝟘∧𝟙 = 𝟘𝟙ω.𝟘∧𝟙-elim
      (λ p → tr⁻¹ p ≡ ω)
      (λ _ → refl)
      (λ _ → refl)
    tr⁻¹-∧ : ∀ p q → tr⁻¹ (p 𝟘𝟙ω.∧ q) ≡ tr⁻¹ p E.∧ tr⁻¹ q
    tr⁻¹-∧ = λ where
      𝟘 𝟘 → refl
      𝟘 𝟙 → tr⁻¹-𝟘∧𝟙
      𝟘 ω → refl
      𝟙 𝟘 → tr⁻¹-𝟘∧𝟙
      𝟙 𝟙 → refl
      𝟙 ω → refl
      ω 𝟘 → refl
      ω 𝟙 → refl
      ω ω → refl
    tr⁻¹-+ : ∀ p q → tr⁻¹ (p 𝟘𝟙ω.+ q) ≡ tr⁻¹ p E.+ tr⁻¹ q
    tr⁻¹-+ = λ where
      𝟘 𝟘 → refl
      𝟘 𝟙 → refl
      𝟘 ω → refl
      𝟙 𝟘 → refl
      𝟙 𝟙 → refl
      𝟙 ω → refl
      ω 𝟘 → refl
      ω 𝟙 → refl
      ω ω → refl
    tr⁻¹-· : ∀ p q → tr⁻¹ (tr′ p 𝟘𝟙ω.· q) ≡ p E.· tr⁻¹ q
    tr⁻¹-· = λ where
      𝟘 𝟘 → refl
      𝟘 𝟙 → refl
      𝟘 ω → refl
      ω 𝟘 → refl
      ω 𝟙 → refl
      ω ω → refl

opaque

  -- The function erasure→zero-one-many is no-nr reflecting from an
  -- erasure modality to a linear types modality

  erasure⇒linearity-no-nr-reflecting :
    (T (Mode-variant.𝟘ᵐ-allowed v₁) → T (Mode-variant.𝟘ᵐ-allowed v₂)) →
    Is-no-nr-reflecting-morphism
      ErasureModality
      linearityModality
      v₁ v₂
      erasure→zero-one-many
  erasure⇒linearity-no-nr-reflecting = erasure⇨zero-one-many-no-nr-reflecting

opaque

  -- The function erasure→zero-one-many is no-nr reflecting from an
  -- erasure modality to a affinetypes modality

  erasure⇒affine-no-nr-reflecting :
    (T (Mode-variant.𝟘ᵐ-allowed v₁) → T (Mode-variant.𝟘ᵐ-allowed v₂)) →
    Is-no-nr-reflecting-morphism
      ErasureModality
      affineModality
      v₁ v₂
      erasure→zero-one-many
  erasure⇒affine-no-nr-reflecting = erasure⇨zero-one-many-no-nr-reflecting

opaque

  -- The function linearity→linear-or-affine is no-nr reflecting

  linearity⇨linear-or-affine-no-nr-reflecting :
    (T (Mode-variant.𝟘ᵐ-allowed v₁) → T (Mode-variant.𝟘ᵐ-allowed v₂)) →
    Is-no-nr-reflecting-morphism
      linearityModality
      linear-or-affine
      v₁ v₂
      linearity→linear-or-affine
  linearity⇨linear-or-affine-no-nr-reflecting {v₁} {v₂} hyp = λ where
      .tr-≤-no-nr {s} → tr-≤-no-nr′ s
    where
    open Is-no-nr-reflecting-morphism
    open Graded.Modality.Properties linearityModality
    module LA = Graded.Modality.Instances.Linear-or-affine
    module L = Graded.Modality.Instances.Linearity
    tr′ : Linearity → Linear-or-affine
    tr′ = linearity→linear-or-affine
    tr⁻¹ : Linear-or-affine → Linearity
    tr⁻¹ = linear-or-affine→linearity
    tr⁻¹-monotone : ∀ p q → p LA.≤ q → tr⁻¹ p L.≤ tr⁻¹ q
    tr⁻¹-monotone = λ where
      𝟘  𝟘  refl → refl
      𝟙  𝟙  refl → refl
      ≤𝟙 𝟘  refl → refl
      ≤𝟙 𝟙  refl → refl
      ≤𝟙 ≤𝟙 refl → refl
      ≤ω _  _    → refl
      𝟘  𝟙  ()
      𝟘  ≤𝟙 ()
      𝟘  ≤ω ()
      𝟙  𝟘  ()
      𝟙  ≤𝟙 ()
      𝟙  ≤ω ()
      ≤𝟙 ≤ω ()
    tr-tr⁻¹≤ : ∀ p → tr′ (tr⁻¹ p) LA.≤ p
    tr-tr⁻¹≤ = λ where
      𝟘  → refl
      𝟙  → refl
      ≤𝟙 → refl
      ≤ω → refl

    tr≤→≤tr⁻¹ : ∀ p q → tr′ p LA.≤ q → p L.≤ tr⁻¹ q
    tr≤→≤tr⁻¹ = λ where
      𝟘 𝟘 refl → refl
      𝟙 𝟙 refl → refl
      ω _ _    → refl
      𝟘 𝟙  ()
      𝟘 ≤𝟙 ()
      𝟘 ≤ω ()
      𝟙 𝟘  ()
      𝟙 ≤𝟙 ()
      𝟙 ≤ω ()

    tr⁻¹-∧ : ∀ p q → tr⁻¹ (p LA.∧ q) ≡ tr⁻¹ p L.∧ tr⁻¹ q
    tr⁻¹-∧ = λ where
      𝟘  𝟘  → refl
      𝟘  𝟙  → refl
      𝟘  ≤𝟙 → refl
      𝟘  ≤ω → refl
      𝟙  𝟘  → refl
      𝟙  𝟙  → refl
      𝟙  ≤𝟙 → refl
      𝟙  ≤ω → refl
      ≤𝟙 𝟘  → refl
      ≤𝟙 𝟙  → refl
      ≤𝟙 ≤𝟙 → refl
      ≤𝟙 ≤ω → refl
      ≤ω _  → refl

    tr⁻¹-+ : ∀ p q → tr⁻¹ (p LA.+ q) ≡ tr⁻¹ p L.+ tr⁻¹ q
    tr⁻¹-+ = λ where
      𝟘  𝟘  → refl
      𝟘  𝟙  → refl
      𝟘  ≤𝟙 → refl
      𝟘  ≤ω → refl
      𝟙  𝟘  → refl
      𝟙  𝟙  → refl
      𝟙  ≤𝟙 → refl
      𝟙  ≤ω → refl
      ≤𝟙 𝟘  → refl
      ≤𝟙 𝟙  → refl
      ≤𝟙 ≤𝟙 → refl
      ≤𝟙 ≤ω → refl
      ≤ω 𝟘  → refl
      ≤ω 𝟙  → refl
      ≤ω ≤𝟙 → refl
      ≤ω ≤ω → refl

    tr⁻¹-· : ∀ p q → tr⁻¹ (tr′ p LA.· q) ≡ p L.· tr⁻¹ q
    tr⁻¹-· = λ where
      𝟘 𝟘  → refl
      𝟘 𝟙  → refl
      𝟘 ≤𝟙 → refl
      𝟘 ≤ω → refl
      𝟙 𝟘  → refl
      𝟙 𝟙  → refl
      𝟙 ≤𝟙 → refl
      𝟙 ≤ω → refl
      ω 𝟘  → refl
      ω 𝟙  → refl
      ω ≤𝟙 → refl
      ω ≤ω → refl
    tr-≤-no-nr′ :
      ∀ {p q₁ q₂ q₃ q₄ r} s →
      tr′ p LA.≤ q₁ →
      q₁ LA.≤ q₂ →
      (T (Mode-variant.𝟘ᵐ-allowed v₂) →
       q₁ LA.≤ q₃) →
      (⦃ 𝟘-well-behaved :
           Has-well-behaved-zero Linear-or-affine
             LA.linear-or-affine-semiring-with-meet ⦄ →
       q₁ LA.≤ q₄) →
      q₁ LA.≤ q₃ LA.+ tr′ r LA.· q₄ LA.+ tr′ s LA.· q₁ →
      ∃₄ λ q₁′ q₂′ q₃′ q₄′ →
         tr′ q₂′ LA.≤ q₂ ×
         tr′ q₃′ LA.≤ q₃ ×
         tr′ q₄′ LA.≤ q₄ ×
         p L.≤ q₁′ ×
         q₁′ L.≤ q₂′ ×
         (T (Mode-variant.𝟘ᵐ-allowed v₁) →
          q₁′ L.≤ q₃′) ×
         (⦃ 𝟘-well-behaved :
              Has-well-behaved-zero Linearity
                (Modality.semiring-with-meet linearityModality) ⦄ →
          q₁′ L.≤ q₄′) ×
         q₁′ L.≤ q₃′ L.+ r L.· q₄′ L.+ s L.· q₁′
    tr-≤-no-nr′ s = →tr-≤-no-nr {s = s}
      linearityModality
      linear-or-affine
      v₁ v₂
      hyp
      LA.linear-or-affine-has-well-behaved-zero
      tr′
      tr⁻¹
      tr⁻¹-monotone
      tr≤→≤tr⁻¹
      tr-tr⁻¹≤
      (λ p q → ≤-reflexive (tr⁻¹-+ p q))
      (λ p q → ≤-reflexive (tr⁻¹-∧ p q))
      (λ p q → ≤-reflexive (tr⁻¹-· p q))

opaque

  -- The function affine→linear-or-affine is no-nr reflecting

  affine⇨linear-or-affine-no-nr-reflecting :
    (T (Mode-variant.𝟘ᵐ-allowed v₁) → T (Mode-variant.𝟘ᵐ-allowed v₂)) →
    Is-no-nr-reflecting-morphism
      affineModality
      linear-or-affine
      v₁ v₂
      affine→linear-or-affine
  affine⇨linear-or-affine-no-nr-reflecting {v₁} {v₂} hyp = λ where
      .tr-≤-no-nr {s} → tr-≤-no-nr′ s
    where
    open Is-no-nr-reflecting-morphism
    open Graded.Modality.Properties affineModality
    module LA = Graded.Modality.Instances.Linear-or-affine
    module A = Graded.Modality.Instances.Affine
    tr′ : Affine → Linear-or-affine
    tr′ = affine→linear-or-affine
    tr⁻¹ : Linear-or-affine → Affine
    tr⁻¹ = linear-or-affine→affine
    tr⁻¹-monotone : ∀ p q → p LA.≤ q → tr⁻¹ p A.≤ tr⁻¹ q
    tr⁻¹-monotone = λ where
      𝟘  𝟘  refl → refl
      𝟙  𝟙  refl → refl
      ≤𝟙 𝟘  refl → refl
      ≤𝟙 𝟙  refl → refl
      ≤𝟙 ≤𝟙 refl → refl
      ≤ω _  _    → refl
      𝟘  𝟙  ()
      𝟘  ≤𝟙 ()
      𝟘  ≤ω ()
      𝟙  𝟘  ()
      𝟙  ≤𝟙 ()
      𝟙  ≤ω ()
      ≤𝟙 ≤ω ()

    tr-tr⁻¹≤ : ∀ p → tr′ (tr⁻¹ p) LA.≤ p
    tr-tr⁻¹≤ = λ where
      𝟘  → refl
      𝟙  → refl
      ≤𝟙 → refl
      ≤ω → refl

    tr≤→≤tr⁻¹ : ∀ p q → tr′ p LA.≤ q → p A.≤ tr⁻¹ q
    tr≤→≤tr⁻¹ = λ where
      𝟘 𝟘  refl → refl
      𝟙 𝟘  refl → refl
      𝟙 𝟙  refl → refl
      𝟙 ≤𝟙 refl → refl
      ω _  _    → refl
      𝟘 𝟙  ()
      𝟘 ≤𝟙 ()
      𝟘 ≤ω ()
      𝟙 ≤ω ()

    tr⁻¹-∧ : ∀ p q → tr⁻¹ (p LA.∧ q) ≡ tr⁻¹ p A.∧ tr⁻¹ q
    tr⁻¹-∧ = λ where
      𝟘  𝟘  → refl
      𝟘  𝟙  → refl
      𝟘  ≤𝟙 → refl
      𝟘  ≤ω → refl
      𝟙  𝟘  → refl
      𝟙  𝟙  → refl
      𝟙  ≤𝟙 → refl
      𝟙  ≤ω → refl
      ≤𝟙 𝟘  → refl
      ≤𝟙 𝟙  → refl
      ≤𝟙 ≤𝟙 → refl
      ≤𝟙 ≤ω → refl
      ≤ω _  → refl

    tr⁻¹-+ : ∀ p q → tr⁻¹ (p LA.+ q) ≡ tr⁻¹ p A.+ tr⁻¹ q
    tr⁻¹-+ = λ where
      𝟘  𝟘  → refl
      𝟘  𝟙  → refl
      𝟘  ≤𝟙 → refl
      𝟘  ≤ω → refl
      𝟙  𝟘  → refl
      𝟙  𝟙  → refl
      𝟙  ≤𝟙 → refl
      𝟙  ≤ω → refl
      ≤𝟙 𝟘  → refl
      ≤𝟙 𝟙  → refl
      ≤𝟙 ≤𝟙 → refl
      ≤𝟙 ≤ω → refl
      ≤ω 𝟘  → refl
      ≤ω 𝟙  → refl
      ≤ω ≤𝟙 → refl
      ≤ω ≤ω → refl

    tr⁻¹-· : ∀ p q → tr⁻¹ (tr′ p LA.· q) ≡ p A.· tr⁻¹ q
    tr⁻¹-· = λ where
      𝟘 𝟘  → refl
      𝟘 𝟙  → refl
      𝟘 ≤𝟙 → refl
      𝟘 ≤ω → refl
      𝟙 𝟘  → refl
      𝟙 𝟙  → refl
      𝟙 ≤𝟙 → refl
      𝟙 ≤ω → refl
      ω 𝟘  → refl
      ω 𝟙  → refl
      ω ≤𝟙 → refl
      ω ≤ω → refl

    tr-≤-no-nr′ :
      ∀ {p q₁ q₂ q₃ q₄ r} s →
      tr′ p LA.≤ q₁ →
      q₁ LA.≤ q₂ →
      (T (Mode-variant.𝟘ᵐ-allowed v₂) →
       q₁ LA.≤ q₃) →
      (⦃ 𝟘-well-behaved :
           Has-well-behaved-zero Linear-or-affine
             LA.linear-or-affine-semiring-with-meet ⦄ →
       q₁ LA.≤ q₄) →
      q₁ LA.≤ q₃ LA.+ tr′ r LA.· q₄ LA.+ tr′ s LA.· q₁ →
      ∃₄ λ q₁′ q₂′ q₃′ q₄′ →
         tr′ q₂′ LA.≤ q₂ ×
         tr′ q₃′ LA.≤ q₃ ×
         tr′ q₄′ LA.≤ q₄ ×
         p A.≤ q₁′ ×
         q₁′ A.≤ q₂′ ×
         (T (Mode-variant.𝟘ᵐ-allowed v₁) →
          q₁′ A.≤ q₃′) ×
         (⦃ 𝟘-well-behaved :
              Has-well-behaved-zero Affine
                (Modality.semiring-with-meet affineModality) ⦄ →
          q₁′ A.≤ q₄′) ×
         q₁′ A.≤ q₃′ A.+ r A.· q₄′ A.+ s A.· q₁′
    tr-≤-no-nr′ s = →tr-≤-no-nr {s = s}
      affineModality
      linear-or-affine
      v₁ v₂
      hyp
      LA.linear-or-affine-has-well-behaved-zero
      tr′
      tr⁻¹
      tr⁻¹-monotone
      tr≤→≤tr⁻¹
      tr-tr⁻¹≤
      (λ p q → ≤-reflexive (tr⁻¹-+ p q))
      (λ p q → ≤-reflexive (tr⁻¹-∧ p q))
      (λ p q → ≤-reflexive (tr⁻¹-· p q))
