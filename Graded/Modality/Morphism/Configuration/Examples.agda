------------------------------------------------------------------------
-- Lemmas related to Is-Σ-morphism-C/Is-Σ-order-embedding-C and
-- specific configuration transformers (and no-restrictions)
------------------------------------------------------------------------

module Graded.Modality.Morphism.Configuration.Examples where

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Product as Σ
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum as ⊎ using (_⊎_; inj₁; inj₂)
import Tools.Reasoning.PartialOrder

open import Configuration-types
open import Configuration-types.Configuration.Zero-one
open import Configuration-types.Erased-matches
open import Configuration-types.Natrec
open import Configuration-types.Omega

open import Definition.Untyped.NotParametrised

open import Graded.Modality
open import Graded.Modality.Morphism
open import Graded.Modality.Morphism.Configuration
open import Graded.Modality.Morphism.Examples
open import Graded.Modality.Morphism.Type-configuration
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
         zero-one-many-has-well-behaved-zero;
         zero-one-many-has-omega)
import Graded.Modality.Morphism.Type-configuration.Examples as Ex
open import Graded.Mode.Instances.Zero-one.Variant
open import Graded.Mode.Instances.Zero-one
open import Graded.Mode.Instances.Zero-one.QuantityTranslation.Primitive
import Graded.Modality.Properties

open Configuration

private variable
  b₁ b₂ b₃ b₄ b₅ 𝟙≤𝟘 ok trp : Bool
  v₁ v₂                     : Mode-variant _
  C C₁ C₂                   : Configuration _
  A M₁ M₂                   : Set _
  𝕄₁ 𝕄₂                     : Modality _
  m₁ m₂                     : Mode _
  o₁ o₂                     : With-or-without-omega _
  tr tr-Σ                   : M₁ → M₂
  v₁-ok v₂-ok               : A
  nm₁ nm₂                   : Natrec-mode _

-- An instance used below

private instance
  zero-one-many-has-omega′ : Has-omega (Zero-one-many 𝟙≤𝟘) (zero-one-many-modality 𝟙≤𝟘)
  zero-one-many-has-omega′ = zero-one-many-has-omega _

  {-# OVERLAPPABLE zero-one-many-has-omega′ #-}

------------------------------------------------------------------------
-- Lemmas related to no-restrictions

private opaque

  -- A lemma used below.

  M-TC-no-restrictions :
    let module M₁ = Modality 𝕄₁
        module M₂ = Modality 𝕄₂
    in
    ∀ nm₁ nm₂ b₃ b₄ b₅ →
    (M₂.Trivial → M₁.Trivial) →
    (With-omega 𝕄₁ o₁ → T (Mode-variant.𝟘ᵐ-allowed v₁) →
     tr M₁.𝟘 ≡ M₂.𝟘) →
    ((ok₁ : With-omega 𝕄₁ o₁) (ok₂ : With-omega 𝕄₂ o₂) →
     tr (Has-omega.ω (With-omega→Has-omega _ ok₁)) ≡
     Has-omega.ω (With-omega→Has-omega _ ok₂)) →
    (With-omega 𝕄₁ o₁ → With-omega 𝕄₂ o₂) →
    (T (Mode-variant.𝟘ᵐ-allowed v₁) → T (Mode-variant.𝟘ᵐ-allowed v₂)) →
    Is-Σ-morphism-TC trp
      (no-restrictions 𝕄₁ v₁ o₁ nm₁ b₁ b₂ b₃ b₄ b₅ .Configuration.TC)
      (no-restrictions 𝕄₂ v₂ o₂ nm₂ b₁ b₂ b₃ b₄ b₅ .Configuration.TC)
      tr tr-Σ
  M-TC-no-restrictions _ _ _ _ _ hyp₁ hyp₂ hyp₃ hyp₄ hyp₅ = λ where
      .unfolding-mode-preserved      → refl
      .level-support-preserved       → level-type small≤small
      .Omega-plus-preserved          → _
      .Unitʷ-η-preserved ()
      .Unit-preserved                → _
      .ΠΣ-preserved                  → _
      .Opacity-preserved _           → lift ∘→ Lift.lower
      .K-preserved                   → lift ∘→ Lift.lower
      .[]-cong-preserved             → _∘→ hyp₁
      .Equality-reflection-preserved → lift ∘→ Lift.lower
      .Quot-preserved                →
        Σ.map
          (_∘→
             (Trivialᵐ′⇔Trivialᵐ _ .proj₂ ∘→
              ¬𝟘ᵐ-allowed→Trivialᵐ _ ∘→
              (_∘→ hyp₅) ∘→
              Trivialᵐ→¬𝟘ᵐ-allowed _ ∘→
              Trivialᵐ′⇔Trivialᵐ _ .proj₁))
          hyp₄
      .Quot-allowed→tr-𝟘≡𝟘 →
        uncurry (flip hyp₂) ∘→
        Σ.map
          (¬Trivialᵐ→𝟘ᵐ-allowed _ ∘→
           (_∘→ Trivialᵐ′⇔Trivialᵐ _ .proj₂))
          idᶠ
      .Omega-allowed-preserved          → hyp₄
      .omega-preserving ⦃ ok₁ ⦄ ⦃ ok₂ ⦄ → λ where
        .tr-ω → hyp₃ ok₁ ok₂
    where
    open Is-omega-preserving-morphism
    open Is-Σ-morphism-TC

opaque

  -- A lemma related to Is-Σ-morphism-C and no-restrictions.

  M-no-restrictions :
    let module M₁ = Modality 𝕄₁
        module M₂ = Modality 𝕄₂
    in
    (M₂.Trivial → M₁.Trivial) →
    (With-omega 𝕄₁ o₁ → T (Mode-variant.𝟘ᵐ-allowed v₁) →
     tr M₁.𝟘 ≡ M₂.𝟘) →
    ((ok₁ : With-omega 𝕄₁ o₁) (ok₂ : With-omega 𝕄₂ o₂) →
     tr (Has-omega.ω (With-omega→Has-omega _ ok₁)) ≡
     Has-omega.ω (With-omega→Has-omega _ ok₂)) →
    (With-omega 𝕄₁ o₁ → With-omega 𝕄₂ o₂) →
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
    Is-Σ-morphism-C trp
      (no-restrictions 𝕄₁ v₁ o₁ nm₁ b₁ b₂ b₃ b₄ b₅)
      (no-restrictions 𝕄₂ v₂ o₂ nm₂ b₁ b₂ b₃ b₄ b₅)
      tr tr-Σ
  M-no-restrictions
    {nm₁} {nm₂} {b₃} {b₄} {b₅}
    hyp₁ hyp₂ hyp₃ hyp₄ hyp₅ nm₁≈nm₂ hyp₆ hyp₇ hyp₈ = λ where
      .𝟘ᵐ-preserved → hyp₅
      .natrec-mode-preserved → nm₁≈nm₂
      .starˢ-sink-preserved → refl
      .Id-erased-preserved → lift ∘→ Lift.lower , lift ∘→ Lift.lower
      .erased-matches-for-J-preserved → _
      .erased-matches-for-K-preserved → _
      .Qrec-motive-erased-preserved →
        lift ∘→ Lift.lower , lift ∘→ Lift.lower
      .is-Σ-morphism-TC →
        M-TC-no-restrictions nm₁ nm₂ b₃ b₄ b₅ hyp₁ hyp₂ hyp₃ hyp₄ hyp₅
      .nr-preserving → hyp₆
      .no-nr-preserving → hyp₇
      .no-nr-glb-preserving → hyp₈
      .Prodrec-preserved → _
      .Unitrec-preserved → _
      .Emptyrec-preserved → _
      .[]-cong-mode-preserved _ → _∘→ hyp₁
    where
    open Is-omega-preserving-morphism
    open Is-Σ-morphism-C

opaque

  -- A lemma related to Is-Σ-order-embedding-C and no-restrictions.

  OE-no-restrictions :
    let module M₁ = Modality 𝕄₁
        module M₂ = Modality 𝕄₂
        module V₁ = Mode-variant v₁
        module V₂ = Mode-variant v₂
    in
    (M₂.Trivial → M₁.Trivial) →
    (With-omega 𝕄₁ o₁ → T V₁.𝟘ᵐ-allowed → tr M₁.𝟘 ≡ M₂.𝟘) →
    ((ok₁ : With-omega 𝕄₁ o₁) (ok₂ : With-omega 𝕄₂ o₂) →
     tr (Has-omega.ω (With-omega→Has-omega _ ok₁)) ≡
     Has-omega.ω (With-omega→Has-omega _ ok₂)) →
    With-omega 𝕄₁ o₁ ⇔ With-omega 𝕄₂ o₂ →
    (T V₁.𝟘ᵐ-allowed → T V₂.𝟘ᵐ-allowed) →
    (T V₂.𝟘ᵐ-allowed → T V₁.𝟘ᵐ-allowed ⊎ M₁.Trivial) →
    nm₁ ≈ⁿᵐ nm₂ →
    (⦃ has-nr₁ : Natrec-mode-has-nr _ nm₁ ⦄ →
     ⦃ has-nr₂ : Natrec-mode-has-nr _ nm₂ ⦄ →
     Is-nr-preserving-morphism 𝕄₁ 𝕄₂
       ⦃ has-nr₁ = Natrec-mode-Has-nr 𝕄₁ has-nr₁ ⦄
       ⦃ has-nr₂ = Natrec-mode-Has-nr 𝕄₂ has-nr₂ ⦄ tr ×
     Is-nr-reflecting-morphism 𝕄₁ 𝕄₂
       ⦃ has-nr₁ = Natrec-mode-Has-nr 𝕄₁ has-nr₁ ⦄
       ⦃ has-nr₂ = Natrec-mode-Has-nr 𝕄₂ has-nr₂ ⦄ tr) →
    (⦃ no-nr₁ : Natrec-mode-no-nr _ nm₁ ⦄ →
     ⦃ no-nr₂ : Natrec-mode-no-nr _ nm₂ ⦄ →
     Is-no-nr-preserving 𝕄₁ 𝕄₂ v₁ v₂ ×
     Is-no-nr-reflecting-morphism 𝕄₁ 𝕄₂ v₁ v₂ tr) →
    (⦃ no-nr₁ : Natrec-mode-no-nr-glb _ nm₁ ⦄ →
     ⦃ no-nr₂ : Natrec-mode-no-nr-glb _ nm₂ ⦄ →
     Is-no-nr-glb-preserving-morphism 𝕄₁ 𝕄₂ tr ×
     Is-no-nr-glb-reflecting-morphism 𝕄₁ 𝕄₂ tr) →
    Is-Σ-order-embedding-C trp
      (no-restrictions 𝕄₁ v₁ o₁ nm₁ b₁ b₂ b₃ b₄ b₅)
      (no-restrictions 𝕄₂ v₂ o₂ nm₂ b₁ b₂ b₃ b₄ b₅)
      tr tr-Σ
  OE-no-restrictions
    {𝕄₁} {nm₁} {nm₂} {b₃} {b₄} {b₅}
    hyp₁ hyp₂ hyp₃ hyp₄ hyp₅ hyp₆ nm₁≈nm₂ hyp₇ hyp₈ hyp₉ = λ where
      .is-Σ-morphism-C →
        M-no-restrictions hyp₁ hyp₂ hyp₃ (hyp₄ .proj₁) hyp₅ nm₁≈nm₂
          (hyp₇ .proj₁) (hyp₈ .proj₁) (hyp₉ .proj₁)
      .is-Σ-order-embedding-TC → λ where
        .is-Σ-morphism-TC →
          M-TC-no-restrictions nm₁ nm₂ b₃ b₄ b₅ hyp₁ hyp₂ hyp₃
            (hyp₄ .proj₁) hyp₅
        .unfolding-mode-reflected → refl
        .level-support-reflected → level-type small≤small
        .Unitʷ-η-reflected ()
        .Unit-reflected → _
        .ΠΣ-reflected → _
        .Opacity-reflected → lift ∘→ Lift.lower
        .K-reflected → lift ∘→ Lift.lower
        .[]-cong-reflected _ → case MP₁.trivial? of λ where
          (yes triv) → inj₂ triv
          (no not)   → inj₁ not
        .Equality-reflection-reflected → lift ∘→ Lift.lower
        .Quot-reflected →
          ⊎.[ (λ (not-triv , ok₁) →
                 ⊎.map
                   (λ ok₂ →
                      (_$ ok₂) ∘→
                      Trivialᵐ→¬𝟘ᵐ-allowed _ ∘→
                      Trivialᵐ′⇔Trivialᵐ _ .proj₁ ,
                      hyp₄ .proj₂ ok₁)
                   idᶠ
                   (hyp₆ $
                    ¬Trivialᵐ→𝟘ᵐ-allowed _ $
                    not-triv ∘→ Trivialᵐ′⇔Trivialᵐ _ .proj₂))
            , inj₂ ∘→ hyp₁
            ]
        .Omega-allowed-reflected →
          hyp₄ .proj₂
      .𝟘ᵐ-reflected →
        ⊎.[ hyp₆ , inj₂ ∘→ hyp₁ ]
      .nr-reflected →
        hyp₇ .proj₂
      .no-nr-reflected →
        hyp₈ .proj₂
      .no-nr-glb-reflected →
        hyp₉ .proj₂
      .Prodrec-reflected →
        _
      .Unitrec-reflected →
        _
      .Emptyrec-reflected →
        _
      .[]-cong-mode-reflected _ _ →
        case MP₁.trivial? of λ where
          (yes triv) → inj₂ triv
          (no not)   → inj₁ not
      .erased-matches-for-J-reflected →
        _
      .erased-matches-for-K-reflected →
        _
    where
    module MP₁ = Graded.Modality.Properties 𝕄₁
    open Is-Σ-morphism-TC
    open Is-Σ-order-embedding-TC
    open Is-Σ-order-embedding-C

------------------------------------------------------------------------
-- Lemmas related to certain configuration transformers

opaque

  -- A lemma related to Is-Σ-morphism-C and equal-binder-quantities.

  M-equal-binder-quantities :
    Is-Σ-morphism-C trp C₁ C₂ tr tr →
    Is-Σ-morphism-C trp
      (equal-binder-quantities 𝕄₁ v₁ C₁)
      (equal-binder-quantities 𝕄₂ v₂ C₂)
      tr tr
  M-equal-binder-quantities m = λ where
      .𝟘ᵐ-preserved                   → M.𝟘ᵐ-preserved
      .natrec-mode-preserved          → M.natrec-mode-preserved
      .starˢ-sink-preserved           → M.starˢ-sink-preserved
      .Id-erased-preserved            → M.Id-erased-preserved
      .erased-matches-for-J-preserved → M.erased-matches-for-J-preserved
      .erased-matches-for-K-preserved → M.erased-matches-for-K-preserved
      .Qrec-motive-erased-preserved   → M.Qrec-motive-erased-preserved
      .is-Σ-morphism-TC →
        Ex.M-equal-binder-quantities M.is-Σ-morphism-TC
      .nr-preserving          → M.nr-preserving
      .no-nr-preserving       → M.no-nr-preserving
      .no-nr-glb-preserving   → M.no-nr-glb-preserving
      .Prodrec-preserved      → M.Prodrec-preserved
      .Unitrec-preserved      → M.Unitrec-preserved
      .Emptyrec-preserved     → M.Emptyrec-preserved
      .[]-cong-mode-preserved → M.[]-cong-mode-preserved
    where
    module M = Is-Σ-morphism-C m
    open Is-Σ-morphism-C

opaque

  -- A lemma related to Is-Σ-order-embedding-TC and
  -- equal-binder-quantities.

  OE-equal-binder-quantities :
    (∀ {p q} → tr p ≡ tr q → p ≡ q) →
    Is-Σ-order-embedding-C trp C₁ C₂ tr tr →
    Is-Σ-order-embedding-C trp
      (equal-binder-quantities 𝕄₁ v₁ C₁)
      (equal-binder-quantities 𝕄₂ v₂ C₂)
      tr tr
  OE-equal-binder-quantities inj oe = λ where
      .is-Σ-morphism-C →
        M-equal-binder-quantities E.is-Σ-morphism-C
      .is-Σ-order-embedding-TC →
        Ex.OE-equal-binder-quantities inj E.is-Σ-order-embedding-TC
      .𝟘ᵐ-reflected                   → E.𝟘ᵐ-reflected
      .nr-reflected                   → E.nr-reflected
      .no-nr-reflected                → E.no-nr-reflected
      .no-nr-glb-reflected            → E.no-nr-glb-reflected
      .Prodrec-reflected              → E.Prodrec-reflected
      .Unitrec-reflected              → E.Unitrec-reflected
      .Emptyrec-reflected             → E.Emptyrec-reflected
      .[]-cong-mode-reflected         → E.[]-cong-mode-reflected
      .erased-matches-for-J-reflected → E.erased-matches-for-J-reflected
      .erased-matches-for-K-reflected → E.erased-matches-for-K-reflected
    where
    module E = Is-Σ-order-embedding-C oe
    open Is-Σ-order-embedding-C

opaque

  -- A lemma related to Is-Σ-morphism-C and second-ΠΣ-quantities-𝟘.

  M-second-ΠΣ-quantities-𝟘 :
    tr (Modality.𝟘 𝕄₁) ≡ Modality.𝟘 𝕄₂ →
    Is-Σ-morphism-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-morphism-C trp
      (second-ΠΣ-quantities-𝟘 𝕄₁ v₁ C₁)
      (second-ΠΣ-quantities-𝟘 𝕄₂ v₂ C₂)
      tr tr-Σ
  M-second-ΠΣ-quantities-𝟘 hyp m = λ where
      .𝟘ᵐ-preserved                   → M.𝟘ᵐ-preserved
      .natrec-mode-preserved          → M.natrec-mode-preserved
      .starˢ-sink-preserved           → M.starˢ-sink-preserved
      .Id-erased-preserved            → M.Id-erased-preserved
      .erased-matches-for-J-preserved → M.erased-matches-for-J-preserved
      .erased-matches-for-K-preserved → M.erased-matches-for-K-preserved
      .Qrec-motive-erased-preserved   → M.Qrec-motive-erased-preserved
      .is-Σ-morphism-TC →
        Ex.M-second-ΠΣ-quantities-𝟘 hyp M.is-Σ-morphism-TC
      .nr-preserving          → M.nr-preserving
      .no-nr-preserving       → M.no-nr-preserving
      .no-nr-glb-preserving   → M.no-nr-glb-preserving
      .Prodrec-preserved      → M.Prodrec-preserved
      .Unitrec-preserved      → M.Unitrec-preserved
      .Emptyrec-preserved     → M.Emptyrec-preserved
      .[]-cong-mode-preserved → M.[]-cong-mode-preserved
    where
    module M = Is-Σ-morphism-C m
    open Is-Σ-morphism-C

opaque

  -- A lemma related to Is-Σ-order-embedding-TC and
  -- second-ΠΣ-quantities-𝟘.

  OE-second-ΠΣ-quantities-𝟘 :
    (∀ p → p ≡ Modality.𝟘 𝕄₁ ⇔ tr p ≡ Modality.𝟘 𝕄₂) →
    Is-Σ-order-embedding-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-order-embedding-C trp
      (second-ΠΣ-quantities-𝟘 𝕄₁ v₁ C₁)
      (second-ΠΣ-quantities-𝟘 𝕄₂ v₂ C₂)
      tr tr-Σ
  OE-second-ΠΣ-quantities-𝟘 hyp oe = λ where
      .is-Σ-morphism-C →
        M-second-ΠΣ-quantities-𝟘 (hyp _ .proj₁ refl) E.is-Σ-morphism-C
      .is-Σ-order-embedding-TC →
        Ex.OE-second-ΠΣ-quantities-𝟘 hyp E.is-Σ-order-embedding-TC
      .𝟘ᵐ-reflected                   → E.𝟘ᵐ-reflected
      .nr-reflected                   → E.nr-reflected
      .no-nr-reflected                → E.no-nr-reflected
      .no-nr-glb-reflected            → E.no-nr-glb-reflected
      .Prodrec-reflected              → E.Prodrec-reflected
      .Unitrec-reflected              → E.Unitrec-reflected
      .Emptyrec-reflected             → E.Emptyrec-reflected
      .[]-cong-mode-reflected         → E.[]-cong-mode-reflected
      .erased-matches-for-J-reflected → E.erased-matches-for-J-reflected
      .erased-matches-for-K-reflected → E.erased-matches-for-K-reflected
    where
    module E = Is-Σ-order-embedding-C oe
    open Is-Σ-order-embedding-C

opaque

  -- A lemma related to Is-Σ-morphism-C and
  -- second-ΠΣ-quantities-𝟘-or-ω.

  M-second-ΠΣ-quantities-𝟘-or-ω :
    ⦃ has-ω₁ : Has-omega _ 𝕄₁ ⦄
    ⦃ has-ω₂ : Has-omega _ 𝕄₂ ⦄ →
    (¬ Modality.Trivial 𝕄₁ → tr (Modality.𝟘 𝕄₁) ≡ Modality.𝟘 𝕄₂) →
    (∀ p → tr p ≡ Has-omega.ω has-ω₂ ⇔ p ≡ Has-omega.ω has-ω₁) →
    (∀ p → tr-Σ p ≡ Has-omega.ω has-ω₂ ⇔ p ≡ Has-omega.ω has-ω₁) →
    Is-Σ-morphism-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-morphism-C trp
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ v₁ C₁)
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ v₂ C₂)
      tr tr-Σ
  M-second-ΠΣ-quantities-𝟘-or-ω hyp₁ hyp₂ hyp₃ m = λ where
      .𝟘ᵐ-preserved                   → M.𝟘ᵐ-preserved
      .natrec-mode-preserved          → M.natrec-mode-preserved
      .starˢ-sink-preserved           → M.starˢ-sink-preserved
      .Id-erased-preserved            → M.Id-erased-preserved
      .erased-matches-for-J-preserved → M.erased-matches-for-J-preserved
      .erased-matches-for-K-preserved → M.erased-matches-for-K-preserved
      .Qrec-motive-erased-preserved   → M.Qrec-motive-erased-preserved
      .is-Σ-morphism-TC →
        Ex.M-second-ΠΣ-quantities-𝟘-or-ω hyp₁ hyp₂ hyp₃
          M.is-Σ-morphism-TC
      .nr-preserving          → M.nr-preserving
      .no-nr-preserving       → M.no-nr-preserving
      .no-nr-glb-preserving   → M.no-nr-glb-preserving
      .Prodrec-preserved      → M.Prodrec-preserved
      .Unitrec-preserved      → M.Unitrec-preserved
      .Emptyrec-preserved     → M.Emptyrec-preserved
      .[]-cong-mode-preserved → M.[]-cong-mode-preserved
    where
    module M = Is-Σ-morphism-C m
    open Is-Σ-morphism-C

opaque

  -- A lemma related to Is-Σ-order-embedding-TC and
  -- second-ΠΣ-quantities-𝟘-or-ω.

  OE-second-ΠΣ-quantities-𝟘-or-ω :
    let module M₁ = Modality 𝕄₁
        module M₂ = Modality 𝕄₂
    in
    ⦃ has-ω₁ : Has-omega _ 𝕄₁ ⦄
    ⦃ has-ω₂ : Has-omega _ 𝕄₂ ⦄ →
    (¬ M₁.Trivial → tr M₁.𝟘 ≡ M₂.𝟘) →
    (∀ p → tr p ≡ M₂.𝟘 → p ≡ M₁.𝟘) →
    (∀ p → tr p ≡ Has-omega.ω has-ω₂ ⇔ p ≡ Has-omega.ω has-ω₁) →
    (∀ p → tr-Σ p ≡ Has-omega.ω has-ω₂ ⇔ p ≡ Has-omega.ω has-ω₁) →
    Is-Σ-order-embedding-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-order-embedding-C trp
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ v₁ C₁)
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ v₂ C₂)
      tr tr-Σ
  OE-second-ΠΣ-quantities-𝟘-or-ω hyp₁ hyp₂ hyp₃ hyp₄ oe = λ where
      .is-Σ-morphism-C →
        M-second-ΠΣ-quantities-𝟘-or-ω hyp₁ hyp₃ hyp₄ E.is-Σ-morphism-C
      .is-Σ-order-embedding-TC →
        Ex.OE-second-ΠΣ-quantities-𝟘-or-ω hyp₁ hyp₂ hyp₃ hyp₄
          E.is-Σ-order-embedding-TC
      .𝟘ᵐ-reflected                   → E.𝟘ᵐ-reflected
      .nr-reflected                   → E.nr-reflected
      .no-nr-reflected                → E.no-nr-reflected
      .no-nr-glb-reflected            → E.no-nr-glb-reflected
      .Prodrec-reflected              → E.Prodrec-reflected
      .Unitrec-reflected              → E.Unitrec-reflected
      .Emptyrec-reflected             → E.Emptyrec-reflected
      .[]-cong-mode-reflected         → E.[]-cong-mode-reflected
      .erased-matches-for-J-reflected → E.erased-matches-for-J-reflected
      .erased-matches-for-K-reflected → E.erased-matches-for-K-reflected
    where
    module E = Is-Σ-order-embedding-C oe
    open Is-Σ-order-embedding-C

opaque

  -- A lemma related to Is-Σ-morphism-C and strong-types-restricted.

  M-strong-types-restricted :
    tr-Σ (Modality.𝟙 𝕄₁) ≡ Modality.𝟙 𝕄₂ →
    Is-Σ-morphism-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-morphism-C trp
      (strong-types-restricted 𝕄₁ v₁ C₁)
      (strong-types-restricted 𝕄₂ v₂ C₂)
      tr tr-Σ
  M-strong-types-restricted hyp m = record
    { 𝟘ᵐ-preserved                   = 𝟘ᵐ-preserved
    ; natrec-mode-preserved          = natrec-mode-preserved
    ; starˢ-sink-preserved           = starˢ-sink-preserved
    ; Id-erased-preserved            = Id-erased-preserved
    ; erased-matches-for-J-preserved = erased-matches-for-J-preserved
    ; erased-matches-for-K-preserved = erased-matches-for-K-preserved
    ; Qrec-motive-erased-preserved   = Qrec-motive-erased-preserved
    ; is-Σ-morphism-TC =
        Ex.M-strong-types-restricted hyp is-Σ-morphism-TC
    ; nr-preserving          = nr-preserving
    ; no-nr-preserving       = no-nr-preserving
    ; no-nr-glb-preserving   = no-nr-glb-preserving
    ; Prodrec-preserved      = Prodrec-preserved
    ; Unitrec-preserved      = Unitrec-preserved
    ; Emptyrec-preserved     = Emptyrec-preserved
    ; []-cong-mode-preserved =
        λ m₁≈m₂ → Σ.map ([]-cong-mode-preserved m₁≈m₂) idᶠ
    }
    where
    open Is-Σ-morphism-C m

opaque

  -- A lemma related to Is-Σ-order-embedding-C and
  -- strong-types-restricted.

  OE-strong-types-restricted :
    (∀ p → p ≡ Modality.𝟙 𝕄₁ ⇔ tr-Σ p ≡ Modality.𝟙 𝕄₂) →
    (Modality.Trivial 𝕄₂ → Modality.Trivial 𝕄₁) →
    Is-Σ-order-embedding-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-order-embedding-C trp
      (strong-types-restricted 𝕄₁ v₁ C₁)
      (strong-types-restricted 𝕄₂ v₂ C₂)
      tr tr-Σ
  OE-strong-types-restricted {C₁} hyp₁ hyp₂ oe = record
    { is-Σ-morphism-C =
        M-strong-types-restricted (hyp₁ _ .proj₁ refl) is-Σ-morphism-C
    ; is-Σ-order-embedding-TC =
        Ex.OE-strong-types-restricted hyp₁
          (flip C₁.[]-cong→¬Trivial ∘→ hyp₂) is-Σ-order-embedding-TC
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
        _     (inj₂ triv)      → inj₂ (hyp₂ triv)
        m₁≳m₂ (inj₁ (ok , ≢𝕤)) →
          ⊎.map (_, ≢𝕤) idᶠ ([]-cong-mode-reflected m₁≳m₂ (inj₁ ok))
    ; erased-matches-for-J-reflected =
        erased-matches-for-J-reflected
    ; erased-matches-for-K-reflected =
        erased-matches-for-K-reflected
    }
    where
    module C₁ = Configuration C₁
    open Is-Σ-order-embedding-C oe

opaque

  -- A lemma related to Is-Σ-morphism-C and no-strong-types.

  M-no-strong-types :
    Is-Σ-morphism-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-morphism-C trp
      (no-strong-types 𝕄₁ v₁ C₁)
      (no-strong-types 𝕄₂ v₂ C₂)
      tr tr-Σ
  M-no-strong-types m = λ where
      .𝟘ᵐ-preserved                   → M.𝟘ᵐ-preserved
      .natrec-mode-preserved          → M.natrec-mode-preserved
      .starˢ-sink-preserved           → M.starˢ-sink-preserved
      .Id-erased-preserved            → M.Id-erased-preserved
      .erased-matches-for-J-preserved → M.erased-matches-for-J-preserved
      .erased-matches-for-K-preserved → M.erased-matches-for-K-preserved
      .Qrec-motive-erased-preserved   → M.Qrec-motive-erased-preserved
      .is-Σ-morphism-TC →
        Ex.M-no-strong-types M.is-Σ-morphism-TC
      .nr-preserving                → M.nr-preserving
      .no-nr-preserving             → M.no-nr-preserving
      .no-nr-glb-preserving         → M.no-nr-glb-preserving
      .Prodrec-preserved            → M.Prodrec-preserved
      .Unitrec-preserved            → M.Unitrec-preserved
      .Emptyrec-preserved           → M.Emptyrec-preserved
      .[]-cong-mode-preserved m₁≈m₂ →
        Σ.map (M.[]-cong-mode-preserved m₁≈m₂) idᶠ
    where
    module M = Is-Σ-morphism-C m
    open Is-Σ-morphism-C

opaque

  -- A lemma related to Is-Σ-order-embedding-TC and no-strong-types.

  OE-no-strong-types :
    (∀ {s} →
     Modality.Trivial 𝕄₂ →
     ¬ Configuration.[]-cong-allowed C₁ s) →
    Is-Σ-order-embedding-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-order-embedding-C trp
      (no-strong-types 𝕄₁ v₁ C₁)
      (no-strong-types 𝕄₂ v₂ C₂)
      tr tr-Σ
  OE-no-strong-types {C₁} hyp oe = λ where
      .is-Σ-morphism-C         → M-no-strong-types E.is-Σ-morphism-C
      .is-Σ-order-embedding-TC →
        Ex.OE-no-strong-types hyp E.is-Σ-order-embedding-TC
      .𝟘ᵐ-reflected                   → E.𝟘ᵐ-reflected
      .nr-reflected                   → E.nr-reflected
      .no-nr-reflected                → E.no-nr-reflected
      .no-nr-glb-reflected            → E.no-nr-glb-reflected
      .Prodrec-reflected              → E.Prodrec-reflected
      .Unitrec-reflected              → E.Unitrec-reflected
      .Emptyrec-reflected             → E.Emptyrec-reflected
      .[]-cong-mode-reflected {s}     → λ where
       m₁≳m₂ (inj₁ (ok₂ , s≢𝕤)) →
         case E.[]-cong-mode-reflected m₁≳m₂ (inj₁ ok₂) of λ where
           (inj₁ ok₁)      → inj₁ (ok₁ , s≢𝕤)
           (inj₂ trivial₁) → inj₂ trivial₁
       m₁≳m₂ (inj₂ trivial₂) →
         case E.[]-cong-mode-reflected {s = s} m₁≳m₂
                (inj₂ trivial₂) of λ where
           (inj₂ trivial₁) → inj₂ trivial₁
           (inj₁ ok₁)      →
             ⊥-elim $
             hyp trivial₂ (C₁.[]-cong-allowed-mode→[]-cong-allowed ok₁)
      .erased-matches-for-J-reflected → E.erased-matches-for-J-reflected
      .erased-matches-for-K-reflected → E.erased-matches-for-K-reflected
    where
    module C₁ = Configuration C₁
    module E  = Is-Σ-order-embedding-C oe
    open Is-Σ-order-embedding-C

opaque

  -- A lemma related to Is-Σ-morphism-C and _with-η-for-Unitʷ.

  M-with-η-for-Unitʷʳ :
    Is-Σ-morphism-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-morphism-C trp C₁ (_with-η-for-Unitʷ 𝕄₂ v₂ C₂) tr tr-Σ
  M-with-η-for-Unitʷʳ m = λ where
      .𝟘ᵐ-preserved                   → M.𝟘ᵐ-preserved
      .natrec-mode-preserved          → M.natrec-mode-preserved
      .starˢ-sink-preserved           → M.starˢ-sink-preserved
      .Id-erased-preserved            → M.Id-erased-preserved
      .erased-matches-for-J-preserved → M.erased-matches-for-J-preserved
      .erased-matches-for-K-preserved → M.erased-matches-for-K-preserved
      .Qrec-motive-erased-preserved   → M.Qrec-motive-erased-preserved
      .is-Σ-morphism-TC →
        Ex.M-with-η-for-Unitʷʳ M.is-Σ-morphism-TC
      .nr-preserving          → M.nr-preserving
      .no-nr-preserving       → M.no-nr-preserving
      .no-nr-glb-preserving   → M.no-nr-glb-preserving
      .Prodrec-preserved      → M.Prodrec-preserved
      .Unitrec-preserved      → M.Unitrec-preserved
      .Emptyrec-preserved     → M.Emptyrec-preserved
      .[]-cong-mode-preserved → M.[]-cong-mode-preserved
    where
    module M = Is-Σ-morphism-C m
    open Is-Σ-morphism-C

opaque

  -- A lemma related to Is-Σ-morphism-C and _with-η-for-Unitʷ.

  M-with-η-for-Unitʷ :
    Is-Σ-morphism-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-morphism-C trp
      (_with-η-for-Unitʷ 𝕄₁ v₁ C₁)
      (_with-η-for-Unitʷ 𝕄₂ v₂ C₂)
      tr tr-Σ
  M-with-η-for-Unitʷ m = λ where
      .𝟘ᵐ-preserved                   → M.𝟘ᵐ-preserved
      .natrec-mode-preserved          → M.natrec-mode-preserved
      .starˢ-sink-preserved           → M.starˢ-sink-preserved
      .Id-erased-preserved            → M.Id-erased-preserved
      .erased-matches-for-J-preserved → M.erased-matches-for-J-preserved
      .erased-matches-for-K-preserved → M.erased-matches-for-K-preserved
      .Qrec-motive-erased-preserved   → M.Qrec-motive-erased-preserved
      .is-Σ-morphism-TC →
        Ex.M-with-η-for-Unitʷ M.is-Σ-morphism-TC
      .nr-preserving          → M.nr-preserving
      .no-nr-preserving       → M.no-nr-preserving
      .no-nr-glb-preserving   → M.no-nr-glb-preserving
      .Prodrec-preserved      → M.Prodrec-preserved
      .Unitrec-preserved      → M.Unitrec-preserved
      .Emptyrec-preserved     → M.Emptyrec-preserved
      .[]-cong-mode-preserved → M.[]-cong-mode-preserved
    where
    module M = Is-Σ-morphism-C m
    open Is-Σ-morphism-C

opaque

  -- A lemma related to Is-Σ-order-embedding-TC and _with-η-for-Unitʷ.

  OE-with-η-for-Unitʷ :
    Is-Σ-order-embedding-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-order-embedding-C trp
      (_with-η-for-Unitʷ 𝕄₁ v₁ C₁)
      (_with-η-for-Unitʷ 𝕄₂ v₂ C₂)
      tr tr-Σ
  OE-with-η-for-Unitʷ oe = λ where
      .is-Σ-morphism-C         → M-with-η-for-Unitʷ E.is-Σ-morphism-C
      .is-Σ-order-embedding-TC →
        Ex.OE-with-η-for-Unitʷ E.is-Σ-order-embedding-TC
      .𝟘ᵐ-reflected                   → E.𝟘ᵐ-reflected
      .nr-reflected                   → E.nr-reflected
      .no-nr-reflected                → E.no-nr-reflected
      .no-nr-glb-reflected            → E.no-nr-glb-reflected
      .Prodrec-reflected              → E.Prodrec-reflected
      .Unitrec-reflected              → E.Unitrec-reflected
      .Emptyrec-reflected             → E.Emptyrec-reflected
      .[]-cong-mode-reflected         → E.[]-cong-mode-reflected
      .erased-matches-for-J-reflected → E.erased-matches-for-J-reflected
      .erased-matches-for-K-reflected → E.erased-matches-for-K-reflected
    where
    module E = Is-Σ-order-embedding-C oe
    open Is-Σ-order-embedding-C

opaque

  -- A lemma related to Is-Σ-morphism-C and with-equality-reflection.

  M-with-equality-reflectionʳ :
    Is-Σ-morphism-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-morphism-C true C₁
      (with-equality-reflection 𝕄₂ v₂ C₂)
      tr tr-Σ
  M-with-equality-reflectionʳ m = λ where
      .𝟘ᵐ-preserved                   → M.𝟘ᵐ-preserved
      .natrec-mode-preserved          → M.natrec-mode-preserved
      .starˢ-sink-preserved           → M.starˢ-sink-preserved
      .Id-erased-preserved            → M.Id-erased-preserved
      .erased-matches-for-J-preserved → M.erased-matches-for-J-preserved
      .erased-matches-for-K-preserved → M.erased-matches-for-K-preserved
      .Qrec-motive-erased-preserved   → M.Qrec-motive-erased-preserved
      .is-Σ-morphism-TC →
        Ex.M-with-equality-reflectionʳ M.is-Σ-morphism-TC
      .nr-preserving          → M.nr-preserving
      .no-nr-preserving       → M.no-nr-preserving
      .no-nr-glb-preserving   → M.no-nr-glb-preserving
      .Prodrec-preserved      → M.Prodrec-preserved
      .Unitrec-preserved      → M.Unitrec-preserved
      .Emptyrec-preserved     → M.Emptyrec-preserved
      .[]-cong-mode-preserved → M.[]-cong-mode-preserved
    where
    module M = Is-Σ-morphism-C m
    open Is-Σ-morphism-C

opaque

  -- A lemma related to Is-Σ-morphism-C and with-equality-reflection.

  M-with-equality-reflection :
    Is-Σ-morphism-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-morphism-C trp
      (with-equality-reflection 𝕄₁ v₁ C₁)
      (with-equality-reflection 𝕄₂ v₂ C₂)
      tr tr-Σ
  M-with-equality-reflection m = λ where
      .𝟘ᵐ-preserved                   → M.𝟘ᵐ-preserved
      .natrec-mode-preserved          → M.natrec-mode-preserved
      .starˢ-sink-preserved           → M.starˢ-sink-preserved
      .Id-erased-preserved            → M.Id-erased-preserved
      .erased-matches-for-J-preserved → M.erased-matches-for-J-preserved
      .erased-matches-for-K-preserved → M.erased-matches-for-K-preserved
      .Qrec-motive-erased-preserved   → M.Qrec-motive-erased-preserved
      .is-Σ-morphism-TC →
        Ex.M-with-equality-reflection M.is-Σ-morphism-TC
      .nr-preserving          → M.nr-preserving
      .no-nr-preserving       → M.no-nr-preserving
      .no-nr-glb-preserving   → M.no-nr-glb-preserving
      .Prodrec-preserved      → M.Prodrec-preserved
      .Unitrec-preserved      → M.Unitrec-preserved
      .Emptyrec-preserved     → M.Emptyrec-preserved
      .[]-cong-mode-preserved → M.[]-cong-mode-preserved
    where
    module M = Is-Σ-morphism-C m
    open Is-Σ-morphism-C

opaque

  -- A lemma related to Is-Σ-order-embedding-C and
  -- with-equality-reflection.

  OE-with-equality-reflection :
    (∀ {s} →
     Modality.Trivial 𝕄₂ →
     ¬ Configuration.[]-cong-allowed C₁ s) →
    Is-Σ-order-embedding-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-order-embedding-C trp
      (with-equality-reflection 𝕄₁ v₁ C₁)
      (with-equality-reflection 𝕄₂ v₂ C₂)
      tr tr-Σ
  OE-with-equality-reflection hyp oe = λ where
      .is-Σ-morphism-C →
        M-with-equality-reflection E.is-Σ-morphism-C
      .is-Σ-order-embedding-TC →
        Ex.OE-with-equality-reflection hyp E.is-Σ-order-embedding-TC
      .𝟘ᵐ-reflected                   → E.𝟘ᵐ-reflected
      .nr-reflected                   → E.nr-reflected
      .no-nr-reflected                → E.no-nr-reflected
      .no-nr-glb-reflected            → E.no-nr-glb-reflected
      .Prodrec-reflected              → E.Prodrec-reflected
      .Unitrec-reflected              → E.Unitrec-reflected
      .Emptyrec-reflected             → E.Emptyrec-reflected
      .[]-cong-mode-reflected         → E.[]-cong-mode-reflected
      .erased-matches-for-J-reflected → E.erased-matches-for-J-reflected
      .erased-matches-for-K-reflected → E.erased-matches-for-K-reflected
    where
    module E = Is-Σ-order-embedding-C oe
    open Is-Σ-order-embedding-C

opaque

  -- A lemma related to Is-Σ-morphism-C and no-quotients.

  M-no-quotients :
    Is-Σ-morphism-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-morphism-C trp
      (no-quotients 𝕄₁ v₁ C₁)
      (no-quotients 𝕄₂ v₂ C₂)
      tr tr-Σ
  M-no-quotients r = record
    { 𝟘ᵐ-preserved                   = 𝟘ᵐ-preserved
    ; natrec-mode-preserved          = natrec-mode-preserved
    ; starˢ-sink-preserved           = starˢ-sink-preserved
    ; Id-erased-preserved            = Id-erased-preserved
    ; erased-matches-for-J-preserved = erased-matches-for-J-preserved
    ; erased-matches-for-K-preserved = erased-matches-for-K-preserved
    ; Qrec-motive-erased-preserved   = Qrec-motive-erased-preserved
    ; is-Σ-morphism-TC =
        Ex.M-no-quotients is-Σ-morphism-TC
    ; nr-preserving          = nr-preserving
    ; no-nr-preserving       = no-nr-preserving
    ; no-nr-glb-preserving   = no-nr-glb-preserving
    ; Prodrec-preserved      = Prodrec-preserved
    ; Unitrec-preserved      = Unitrec-preserved
    ; Emptyrec-preserved     = Emptyrec-preserved
    ; []-cong-mode-preserved = []-cong-mode-preserved
    }
    where
    open Is-Σ-morphism-C r

opaque

  -- A lemma related to Is-Σ-order-embedding-C and no-quotients.

  OE-no-quotients :
    (Modality.Trivial 𝕄₂ → Modality.Trivial 𝕄₁) →
    Is-Σ-order-embedding-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-order-embedding-C trp
      (no-quotients 𝕄₁ v₁ C₁)
      (no-quotients 𝕄₂ v₂ C₂)
      tr tr-Σ
  OE-no-quotients hyp r = record
    { is-Σ-morphism-C =
        M-no-quotients is-Σ-morphism-C
    ; is-Σ-order-embedding-TC =
        Ex.OE-no-quotients hyp is-Σ-order-embedding-TC
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
    ; []-cong-mode-reflected =
        []-cong-mode-reflected
    ; erased-matches-for-J-reflected =
        erased-matches-for-J-reflected
    ; erased-matches-for-K-reflected =
        erased-matches-for-K-reflected
    }
    where
    open Is-Σ-order-embedding-C r

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

private opaque

  -- A lemma used below.

  M-TC-not-all-erased-matches-JK :
    ⦃ has-ω₁ : Has-omega _ 𝕄₁ ⦄
    ⦃ has-ω₂ : Has-omega _ 𝕄₂ ⦄ →
    Is-omega-preserving-morphism 𝕄₁ 𝕄₂ tr →
    Is-Σ-morphism-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-morphism-TC trp
      (not-all-erased-matches-JK 𝕄₁ v₁ C₁ .Configuration.TC)
      (not-all-erased-matches-JK 𝕄₂ v₂ C₂ .Configuration.TC)
      tr tr-Σ
  M-TC-not-all-erased-matches-JK {C₁} {C₂} hyp m = λ where
      .unfolding-mode-preserved      → M.unfolding-mode-preserved
      .level-support-preserved       → M.level-support-preserved
      .Omega-plus-preserved          → M.Omega-plus-preserved
      .Unitʷ-η-preserved             → M.Unitʷ-η-preserved
      .Unit-preserved                → M.Unit-preserved
      .ΠΣ-preserved                  → M.ΠΣ-preserved
      .Opacity-preserved             → M.Opacity-preserved
      .K-preserved                   → M.K-preserved
      .[]-cong-preserved             → M.[]-cong-preserved
      .Equality-reflection-preserved → M.Equality-reflection-preserved
      .Quot-preserved                → M.Quot-preserved
      .Quot-allowed→tr-𝟘≡𝟘           → M.Quot-allowed→tr-𝟘≡𝟘
      .Omega-allowed-preserved _     →
        with-ω
      .omega-preserving ⦃ ok₁ ⦄ ⦃ ok₂ ⦄ →
        case Omega-allowed-propositional
               (not-all-erased-matches-JK _ _ C₁) ok₁
               with-ω of λ {
          refl →
        case Omega-allowed-propositional
               (not-all-erased-matches-JK _ _ C₂) ok₂
               with-ω of λ {
          refl →
        hyp }}
    where
    module M = Is-Σ-morphism-C m
    open Is-Σ-morphism-TC

opaque

  -- A lemma related to Is-Σ-morphism-C and not-all-erased-matches-JK.

  M-not-all-erased-matches-JK :
    ⦃ has-ω₁ : Has-omega _ 𝕄₁ ⦄
    ⦃ has-ω₂ : Has-omega _ 𝕄₂ ⦄ →
    Is-omega-preserving-morphism 𝕄₁ 𝕄₂ tr →
    Is-Σ-morphism-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-morphism-C trp
      (not-all-erased-matches-JK 𝕄₁ v₁ C₁)
      (not-all-erased-matches-JK 𝕄₂ v₂ C₂)
      tr tr-Σ
  M-not-all-erased-matches-JK {C₁} {C₂} hyp m = record
    { 𝟘ᵐ-preserved                   = 𝟘ᵐ-preserved
    ; natrec-mode-preserved          = natrec-mode-preserved
    ; starˢ-sink-preserved           = starˢ-sink-preserved
    ; Id-erased-preserved            = Id-erased-preserved
    ; erased-matches-for-J-preserved = λ where
        𝟘ᵐ → erased-matches-for-J-preserved 𝟘ᵐ
        𝟙ᵐ →
          not-all-for-𝟙ᵐ-≤ᵉᵐ C₁.erased-matches-for-J
            C₂.erased-matches-for-J (erased-matches-for-J-preserved 𝟙ᵐ)
            𝟙ᵐ
    ; erased-matches-for-K-preserved = λ where
        𝟘ᵐ → erased-matches-for-K-preserved 𝟘ᵐ
        𝟙ᵐ →
          not-all-for-𝟙ᵐ-≤ᵉᵐ C₁.erased-matches-for-K
            C₂.erased-matches-for-K (erased-matches-for-K-preserved 𝟙ᵐ)
            𝟙ᵐ
    ; Qrec-motive-erased-preserved = Qrec-motive-erased-preserved
    ; is-Σ-morphism-TC =
        M-TC-not-all-erased-matches-JK hyp m
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
    module C₁ = Configuration C₁
    module C₂ = Configuration C₂
    open Is-Σ-morphism-C m

opaque

  -- A lemma related to Is-Σ-order-embedding-C and
  -- not-all-erased-matches-JK.

  OE-not-all-erased-matches-JK :
    ⦃ has-ω₁ : Has-omega _ 𝕄₁ ⦄
    ⦃ has-ω₂ : Has-omega _ 𝕄₂ ⦄ →
    Is-omega-preserving-morphism 𝕄₁ 𝕄₂ tr →
    Is-Σ-order-embedding-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-order-embedding-C trp
      (not-all-erased-matches-JK 𝕄₁ v₁ C₁)
      (not-all-erased-matches-JK 𝕄₂ v₂ C₂)
      tr tr-Σ
  OE-not-all-erased-matches-JK {𝕄₁} {𝕄₂} {C₁} {C₂} hyp r = record
    { is-Σ-morphism-C =
        M-not-all-erased-matches-JK hyp is-Σ-morphism-C
    ; is-Σ-order-embedding-TC = record
        { is-Σ-morphism-TC              = M-TC-not-all-erased-matches-JK
                                            hyp is-Σ-morphism-C
        ; unfolding-mode-reflected      = unfolding-mode-reflected
        ; level-support-reflected       = level-support-reflected
        ; Unitʷ-η-reflected             = Unitʷ-η-reflected
        ; Unit-reflected                = Unit-reflected
        ; ΠΣ-reflected                  = ΠΣ-reflected
        ; Opacity-reflected             = Opacity-reflected
        ; K-reflected                   = K-reflected
        ; []-cong-reflected             = []-cong-reflected
        ; Equality-reflection-reflected = Equality-reflection-reflected
        ; Quot-reflected                = Quot-reflected
        ; Omega-allowed-reflected       = λ _ → with-ω
        }
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
          not-all-for-𝟙ᵐ-≤ᵉᵐ C₂.erased-matches-for-J
            C₁.erased-matches-for-J (erased-matches-for-J-reflected 𝟙ᵐ)
            𝟙ᵐ
    ; erased-matches-for-K-reflected = λ where
        𝟘ᵐ → erased-matches-for-K-reflected 𝟘ᵐ
        𝟙ᵐ →
          not-all-for-𝟙ᵐ-≤ᵉᵐ C₂.erased-matches-for-K
            C₁.erased-matches-for-K (erased-matches-for-K-reflected 𝟙ᵐ)
            𝟙ᵐ
    }
    where
    module M₁ = Modality 𝕄₁
    module M₂ = Modality 𝕄₂
    module C₁ = Configuration C₁
    module C₂ = Configuration C₂
    open Is-Σ-order-embedding-C r

private opaque

  -- A lemma used below.

  M-TC-only-some-erased-matches :
    ⦃ has-ω₁ : Has-omega _ 𝕄₁ ⦄
    ⦃ has-ω₂ : Has-omega _ 𝕄₂ ⦄ →
    Is-omega-preserving-morphism 𝕄₁ 𝕄₂ tr →
    Is-Σ-morphism-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-morphism-TC trp
      (only-some-erased-matches 𝕄₁ v₁ C₁ .Configuration.TC)
      (only-some-erased-matches 𝕄₂ v₂ C₂ .Configuration.TC)
      tr tr-Σ
  M-TC-only-some-erased-matches {C₁} {C₂} hyp m = λ where
      .unfolding-mode-preserved      → M.unfolding-mode-preserved
      .level-support-preserved       → M.level-support-preserved
      .Omega-plus-preserved          → M.Omega-plus-preserved
      .Unitʷ-η-preserved             → M.Unitʷ-η-preserved
      .Unit-preserved                → M.Unit-preserved
      .ΠΣ-preserved                  → M.ΠΣ-preserved
      .Opacity-preserved             → M.Opacity-preserved
      .K-preserved                   → M.K-preserved
      .[]-cong-preserved             → M.[]-cong-preserved
      .Equality-reflection-preserved → M.Equality-reflection-preserved
      .Quot-preserved                → M.Quot-preserved
      .Quot-allowed→tr-𝟘≡𝟘           → M.Quot-allowed→tr-𝟘≡𝟘
      .Omega-allowed-preserved _     →
        with-ω
      .omega-preserving ⦃ ok₁ ⦄ ⦃ ok₂ ⦄ →
        case Omega-allowed-propositional
               (not-all-erased-matches-JK _ _ C₁) ok₁
               with-ω of λ {
          refl →
        case Omega-allowed-propositional
               (not-all-erased-matches-JK _ _ C₂) ok₂
               with-ω of λ {
          refl →
        hyp }}
    where
    module M = Is-Σ-morphism-C m
    open Is-Σ-morphism-TC

opaque

  -- A lemma related to Is-Σ-morphism-C and only-some-erased-matches.

  M-only-some-erased-matches :
    ⦃ has-ω₁ : Has-omega _ 𝕄₁ ⦄
    ⦃ has-ω₂ : Has-omega _ 𝕄₂ ⦄ →
    (¬ Modality.Trivial 𝕄₂ →
     ¬ Modality.Trivial 𝕄₁ ×
     (∀ p → tr p ≡ Modality.𝟘 𝕄₂ → p ≡ Modality.𝟘 𝕄₁) ⊎
     (∀ p → tr p ≢ Modality.𝟘 𝕄₂)) →
    Is-omega-preserving-morphism 𝕄₁ 𝕄₂ tr →
    Is-Σ-morphism-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-morphism-C trp
      (only-some-erased-matches 𝕄₁ v₁ C₁)
      (only-some-erased-matches 𝕄₂ v₂ C₂)
      tr tr-Σ
  M-only-some-erased-matches
    {𝕄₁} {𝕄₂} {tr} {C₁} {C₂} hyp hyp′ r = record
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
    ; Qrec-motive-erased-preserved = Qrec-motive-erased-preserved
    ; is-Σ-morphism-TC             =
        M-TC-only-some-erased-matches hyp′ r
    ; nr-preserving        = nr-preserving
    ; no-nr-preserving     = no-nr-preserving
    ; no-nr-glb-preserving = no-nr-glb-preserving
    ; Prodrec-preserved    = λ {r = r} m₁≈m₂ (p , ≢𝟘) →
          Prodrec-preserved m₁≈m₂ p
        , (λ ≡𝟙ᵐ 𝟙≢𝟘 → case hyp 𝟙≢𝟘 of λ where
             (inj₁ (𝟙≢𝟘 , tr-≡-𝟘-→)) →
               tr r ≡ M₂.𝟘  →⟨ tr-≡-𝟘-→ _ ⟩
               r ≡ M₁.𝟘     →⟨ ≢𝟘 (≈ᵐ→≡𝟙ᵐ→≡𝟙ᵐ m₁≈m₂ ≡𝟙ᵐ) 𝟙≢𝟘 ⟩
               ⊥            □
             (inj₂ ≢𝟘) →
               tr r ≡ M₂.𝟘  →⟨ ≢𝟘 _ ⟩
               ⊥            □)
    ; Unitrec-preserved      = Unitrec-preserved
    ; Emptyrec-preserved     = Emptyrec-preserved
    ; []-cong-mode-preserved = λ m₁≈m₂ (ok , hyp) →
        []-cong-mode-preserved m₁≈m₂ ok ,
        (case m₁≈m₂ of λ where
           𝟘ᵐ → λ ()
           𝟙ᵐ → λ _ → hyp refl)
    }
    where
    module M₁ = Modality 𝕄₁
    module M₂ = Modality 𝕄₂
    open Is-Σ-morphism-C r

opaque

  -- A lemma related to Is-Σ-order-embedding-C and
  -- only-some-erased-matches.

  OE-only-some-erased-matches :
    let module M₁ = Modality 𝕄₁
        module M₂ = Modality 𝕄₂
    in
    ⦃ has-ω₁ : Has-omega _ 𝕄₁ ⦄
    ⦃ has-ω₂ : Has-omega _ 𝕄₂ ⦄ →
    (¬ M₁.Trivial →
     ¬ M₂.Trivial × (∀ {p} → p ≡ M₁.𝟘 → tr p ≡ M₂.𝟘)) →
    (¬ M₂.Trivial →
     ¬ M₁.Trivial × (∀ p → tr p ≡ M₂.𝟘 → p ≡ M₁.𝟘) ⊎
      (∀ p → tr p ≢ M₂.𝟘)) →
    Is-omega-preserving-morphism 𝕄₁ 𝕄₂ tr →
    Is-Σ-order-embedding-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-order-embedding-C trp
      (only-some-erased-matches 𝕄₁ v₁ C₁)
      (only-some-erased-matches 𝕄₂ v₂ C₂)
      tr tr-Σ
  OE-only-some-erased-matches
    {𝕄₁} {𝕄₂} {tr} {C₁} {C₂} hyp₁ hyp₂ hyp₃ r = record
    { is-Σ-morphism-C =
        M-only-some-erased-matches hyp₂ hyp₃ is-Σ-morphism-C
    ; is-Σ-order-embedding-TC = record
        { is-Σ-morphism-TC              = M-TC-only-some-erased-matches
                                            hyp₃ is-Σ-morphism-C
        ; unfolding-mode-reflected      = unfolding-mode-reflected
        ; level-support-reflected       = level-support-reflected
        ; Unitʷ-η-reflected             = Unitʷ-η-reflected
        ; Unit-reflected                = Unit-reflected
        ; ΠΣ-reflected                  = ΠΣ-reflected
        ; Opacity-reflected             = Opacity-reflected
        ; K-reflected                   = K-reflected
        ; []-cong-reflected             = []-cong-reflected
        ; Equality-reflection-reflected = Equality-reflection-reflected
        ; Quot-reflected                = Quot-reflected
        ; Omega-allowed-reflected       = λ _ → with-ω
        }
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
                 r ≡ M₁.𝟘     →⟨ hyp₁ non-trivial₁ .proj₂ ⟩
                 tr r ≡ M₂.𝟘  →⟨ tr-r≢𝟘 (≈ᵐ→≡𝟙ᵐ←≡𝟙ᵐ m₁≈m₂ m₁≡𝟙ᵐ) (hyp₁ non-trivial₁ .proj₁) ⟩
                 ⊥            □
               (𝟙ᵐ≳𝟘ᵐ trivial₁) _ →
                 non-trivial₁ trivial₁)
    ; Unitrec-reflected =
        Unitrec-reflected
    ; Emptyrec-reflected =
        Emptyrec-reflected
    ; []-cong-mode-reflected = λ m₁≳m₂ ok →
        case ok of λ where
          (inj₂ triv) →
            inj₂ (contrapositive→ MP₁.trivial? (proj₁ ∘→ hyp₁) triv)
          (inj₁ (ok , ≢𝟙ᵐ)) →
            case []-cong-mode-reflected m₁≳m₂ (inj₁ ok) of λ where
              (inj₂ triv) → inj₂ triv
              (inj₁ ok)   →
                case m₁≳m₂ of λ where
                  (𝟙ᵐ≳𝟘ᵐ triv) → inj₂ triv
                  [ 𝟘ᵐ ]       → inj₁ (ok , (λ ()))
                  [ 𝟙ᵐ ]       → ⊥-elim (≢𝟙ᵐ refl)
    ; erased-matches-for-J-reflected = λ where
        𝟙ᵐ → _
        𝟘ᵐ → erased-matches-for-J-reflected 𝟘ᵐ?≈𝟘ᵐ?′
    ; erased-matches-for-K-reflected = λ where
        𝟙ᵐ → _
        𝟘ᵐ → erased-matches-for-K-reflected 𝟘ᵐ?≈𝟘ᵐ?′
    }
    where
    module M₁  = Modality 𝕄₁
    module M₂  = Modality 𝕄₂
    module MP₁ = Graded.Modality.Properties 𝕄₁
    open Is-Σ-order-embedding-C r

opaque

  -- A lemma related to Is-Σ-morphism-C and no-erased-matches.

  M-no-erased-matches :
    ⦃ has-ω₁ : Has-omega _ 𝕄₁ ⦄
    ⦃ has-ω₂ : Has-omega _ 𝕄₂ ⦄ →
    (¬ Modality.Trivial 𝕄₂ →
     ¬ Modality.Trivial 𝕄₁ ×
     (∀ p → tr p ≡ Modality.𝟘 𝕄₂ → p ≡ Modality.𝟘 𝕄₁) ⊎
     (∀ p → tr p ≢ Modality.𝟘 𝕄₂)) →
    Is-omega-preserving-morphism 𝕄₁ 𝕄₂ tr →
    Is-Σ-morphism-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-morphism-C trp
      (no-erased-matches 𝕄₁ v₁ C₁)
      (no-erased-matches 𝕄₂ v₂ C₂)
      tr tr-Σ
  M-no-erased-matches {𝕄₁} {𝕄₂} {tr} {C₁} {C₂} hyp hyp′ m = record
    { 𝟘ᵐ-preserved                   = M.𝟘ᵐ-preserved
    ; natrec-mode-preserved          = M.natrec-mode-preserved
    ; starˢ-sink-preserved           = M.starˢ-sink-preserved
    ; Id-erased-preserved            = M.Id-erased-preserved
    ; erased-matches-for-J-preserved = M.erased-matches-for-J-preserved
    ; erased-matches-for-K-preserved = M.erased-matches-for-K-preserved
    ; Qrec-motive-erased-preserved   = M.Qrec-motive-erased-preserved
    ; is-Σ-morphism-TC               = M.is-Σ-morphism-TC
    ; nr-preserving                  = M.nr-preserving
    ; no-nr-preserving               = M.no-nr-preserving
    ; no-nr-glb-preserving           = M.no-nr-glb-preserving
    ; Prodrec-preserved              = M.Prodrec-preserved
    ; Unitrec-preserved              = λ {p = p} m₁≈m₂ (P , η) →
          M.Unitrec-preserved m₁≈m₂ P
        , (λ ≡𝟙ᵐ 𝟙≢𝟘 → case hyp 𝟙≢𝟘 of λ where
             (inj₁ (𝟙≢𝟘 , tr-≡-𝟘-→)) →
               tr p ≡ M₂.𝟘  →⟨ tr-≡-𝟘-→ _ ⟩
               p ≡ M₁.𝟘     →⟨ η (≈ᵐ→≡𝟙ᵐ→≡𝟙ᵐ m₁≈m₂ ≡𝟙ᵐ) 𝟙≢𝟘 ⟩
               C₁.Unitʷ-η   →⟨ M.Unitʷ-η-preserved ⟩
               C₂.Unitʷ-η   □
             (inj₂ ≢𝟘) →
               tr p ≡ M₂.𝟘  →⟨ ≢𝟘 _ ⟩
               ⊥            →⟨ ⊥-elim ⟩
               C₂.Unitʷ-η   □)
    ; Emptyrec-preserved     = M.Emptyrec-preserved
    ; []-cong-mode-preserved = M.[]-cong-mode-preserved
    }
    where
    module M  = Is-Σ-morphism-C (M-only-some-erased-matches hyp hyp′ m)
    module M₁ = Modality 𝕄₁
    module M₂ = Modality 𝕄₂
    module C₁ = Configuration C₁
    module C₂ = Configuration C₂

opaque

  -- A lemma related to Is-Σ-order-embedding-C and no-erased-matches.

  OE-no-erased-matches :
    let module M₁ = Modality 𝕄₁
        module M₂ = Modality 𝕄₂
    in
    ⦃ has-ω₁ : Has-omega _ 𝕄₁ ⦄
    ⦃ has-ω₂ : Has-omega _ 𝕄₂ ⦄ →
    (¬ M₁.Trivial →
     ¬ M₂.Trivial × (∀ {p} → p ≡ M₁.𝟘 → tr p ≡ M₂.𝟘)) →
    (¬ M₂.Trivial →
     ¬ M₁.Trivial × (∀ p → tr p ≡ M₂.𝟘 → p ≡ M₁.𝟘) ⊎
      (∀ p → tr p ≢ M₂.𝟘)) →
    Is-omega-preserving-morphism 𝕄₁ 𝕄₂ tr →
    Is-Σ-order-embedding-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-order-embedding-C trp
      (no-erased-matches 𝕄₁ v₁ C₁)
      (no-erased-matches 𝕄₂ v₂ C₂)
      tr tr-Σ
  OE-no-erased-matches
    {𝕄₁} {𝕄₂} {tr} {C₁} {C₂} hyp₁ hyp₂ hyp₃ oe = record
    { is-Σ-morphism-C =
        M-no-erased-matches hyp₂ hyp₃
          (Is-Σ-order-embedding-C.is-Σ-morphism-C oe)
    ; is-Σ-order-embedding-TC =
        C.is-Σ-order-embedding-TC
    ; 𝟘ᵐ-reflected =
        C.𝟘ᵐ-reflected
    ; nr-reflected = C.nr-reflected
    ; no-nr-reflected = C.no-nr-reflected
    ; no-nr-glb-reflected = C.no-nr-glb-reflected
    ; Prodrec-reflected =
        C.Prodrec-reflected
    ; Unitrec-reflected = λ {p = p} m₁≲m₂ (unitrec-ok , tr-p≢𝟘) →
          C.Unitrec-reflected m₁≲m₂ unitrec-ok
        , (λ m₁≡𝟙ᵐ non-trivial₁ →
             case m₁≲m₂ of λ where
               [ m₁≈m₂ ] →
                 p ≡ M₁.𝟘     →⟨ hyp₁ non-trivial₁ .proj₂ ⟩
                 tr p ≡ M₂.𝟘  →⟨ tr-p≢𝟘 (≈ᵐ→≡𝟙ᵐ←≡𝟙ᵐ m₁≈m₂ m₁≡𝟙ᵐ) (hyp₁ non-trivial₁ .proj₁) ⟩
                 C₂.Unitʷ-η   →⟨ C.Unitʷ-η-reflected ⟩
                 C₁.Unitʷ-η   □
               (𝟙ᵐ≳𝟘ᵐ trivial₁) _ →
                 ⊥-elim (non-trivial₁ trivial₁))
    ; Emptyrec-reflected =
        C.Emptyrec-reflected
    ; erased-matches-for-J-reflected =
        C.erased-matches-for-J-reflected
    ; erased-matches-for-K-reflected =
        C.erased-matches-for-K-reflected
    ; []-cong-mode-reflected =
        C.[]-cong-mode-reflected
    }
    where
    module C =
      Is-Σ-order-embedding-C
        (OE-only-some-erased-matches hyp₁ hyp₂ hyp₃ oe)
    module M₁  = Modality 𝕄₁
    module M₂  = Modality 𝕄₂
    module C₁  = Configuration C₁
    module C₂  = Configuration C₂

private opaque

  -- A lemma related to none-for-𝟙ᵐ.

  none-for-𝟙ᵐ-≤ᵉᵐ :
    {f₁ : Mode v₁ → Erased-matches}
    {f₂ : Mode v₂ → Erased-matches} →
    (m₁ ≈ᵐ m₂ → f₁ m₁ ≤ᵉᵐ f₂ m₂) →
    m₁ ≈ᵐ m₂ → none-for-𝟙ᵐ 𝕄₁ v₁ f₁ m₁ ≤ᵉᵐ none-for-𝟙ᵐ 𝕄₂ v₂ f₂ m₂
  none-for-𝟙ᵐ-≤ᵉᵐ hyp 𝟘ᵐ = hyp 𝟘ᵐ
  none-for-𝟙ᵐ-≤ᵉᵐ _   𝟙ᵐ = _

private opaque

  -- A lemma used below.

  M-TC-with-[]-cong :
    ⦃ has-ω₁ : Has-omega _ 𝕄₁ ⦄
    ⦃ has-ω₂ : Has-omega _ 𝕄₂ ⦄ →
    let module M₁ = Modality 𝕄₁
        module M₂ = Modality 𝕄₂
    in
    (¬ Modality.Trivial 𝕄₁ →
     ¬ Modality.Trivial 𝕄₂ ×
     tr M₁.𝟘 ≡ M₂.𝟘 ×
     tr-Σ M₁.𝟘 ≡ M₂.𝟘) →
    Is-omega-preserving-morphism 𝕄₁ 𝕄₂ tr →
    Is-Σ-morphism-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-morphism-TC trp
      (with-[]-cong 𝕄₁ v₁ C₁ .Configuration.TC)
      (with-[]-cong 𝕄₂ v₂ C₂ .Configuration.TC)
      tr tr-Σ
  M-TC-with-[]-cong {𝕄₁} {C₁} {C₂} hyp₁ hyp₂ m = λ where
      .unfolding-mode-preserved  → M.unfolding-mode-preserved
      .level-support-preserved   → M.level-support-preserved
      .Omega-plus-preserved      → M.Omega-plus-preserved
      .Unitʷ-η-preserved         → M.Unitʷ-η-preserved
      .Unit-preserved            →
        ⊎.map M.Unit-preserved (proj₁ ∘→ hyp₁)
      .ΠΣ-preserved {b = BMΠ}   ok → M.ΠΣ-preserved ok
      .ΠΣ-preserved {b = BMΣ s} ok →
        ⊎.map
          M.ΠΣ-preserved
          (λ { (non-trivial , refl , refl) →
               let non-trivial , tr-𝟘≡𝟘 , tr-Σ-𝟘≡𝟘 =
                     hyp₁ non-trivial
               in
               non-trivial , tr-Σ-𝟘≡𝟘 , tr-𝟘≡𝟘 })
          ok
      .Opacity-preserved → M.Opacity-preserved
      .K-preserved       → M.K-preserved
      .[]-cong-preserved →
        ⊎.map M.[]-cong-preserved (proj₁ ∘→ hyp₁)
      .Equality-reflection-preserved → M.Equality-reflection-preserved
      .Quot-preserved                → M.Quot-preserved
      .Quot-allowed→tr-𝟘≡𝟘           → M.Quot-allowed→tr-𝟘≡𝟘
      .Omega-allowed-preserved _     →
          with-ω
      .omega-preserving ⦃ ok₁ ⦄ ⦃ ok₂ ⦄ →
        case Omega-allowed-propositional
               (not-all-erased-matches-JK _ _ C₁) ok₁
               with-ω of λ {
          refl →
        case Omega-allowed-propositional
               (not-all-erased-matches-JK _ _ C₂) ok₂
               with-ω of λ {
          refl →
        hyp₂ }}
    where
    module M = Is-Σ-morphism-C m
    open Is-Σ-morphism-TC

opaque

  -- A lemma related to Is-Σ-morphism-C and with-[]-cong.

  M-with-[]-cong :
    ⦃ has-ω₁ : Has-omega _ 𝕄₁ ⦄
    ⦃ has-ω₂ : Has-omega _ 𝕄₂ ⦄ →
    let module M₁ = Modality 𝕄₁
        module M₂ = Modality 𝕄₂
    in
    (¬ Modality.Trivial 𝕄₁ →
     ¬ Modality.Trivial 𝕄₂ ×
     tr M₁.𝟘 ≡ M₂.𝟘 ×
     tr-Σ M₁.𝟘 ≡ M₂.𝟘) →
    Is-omega-preserving-morphism 𝕄₁ 𝕄₂ tr →
    Is-Σ-morphism-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-morphism-C trp
      (with-[]-cong 𝕄₁ v₁ C₁)
      (with-[]-cong 𝕄₂ v₂ C₂)
      tr tr-Σ
  M-with-[]-cong {𝕄₁} {C₁} {C₂} hyp hyp′ r = record
    { 𝟘ᵐ-preserved                   = 𝟘ᵐ-preserved
    ; natrec-mode-preserved          = natrec-mode-preserved
    ; starˢ-sink-preserved           = starˢ-sink-preserved
    ; Id-erased-preserved            = Id-erased-preserved
    ; erased-matches-for-J-preserved =
        none-for-𝟙ᵐ-≤ᵉᵐ erased-matches-for-J-preserved
    ; erased-matches-for-K-preserved = erased-matches-for-K-preserved
    ; Qrec-motive-erased-preserved   = Qrec-motive-erased-preserved
    ; is-Σ-morphism-TC               = M-TC-with-[]-cong hyp hyp′ r
    ; nr-preserving                  = nr-preserving
    ; no-nr-preserving               = no-nr-preserving
    ; no-nr-glb-preserving           = no-nr-glb-preserving
    ; Prodrec-preserved              = Prodrec-preserved
    ; Unitrec-preserved              = Unitrec-preserved
    ; Emptyrec-preserved             = Emptyrec-preserved
    ; []-cong-mode-preserved         = λ m₁≈m₂ →
        ⊎.map ([]-cong-mode-preserved m₁≈m₂)
          (_∘→ contrapositive→ MP₁.trivial? (proj₁ ∘→ hyp))
    }
    where
    module MP₁ = Graded.Modality.Properties 𝕄₁
    open Is-Σ-morphism-C r

opaque

  -- A lemma related to Is-Σ-order-embedding-C and with-[]-cong.

  OE-with-[]-cong :
    ⦃ has-ω₁ : Has-omega _ 𝕄₁ ⦄
    ⦃ has-ω₂ : Has-omega _ 𝕄₂ ⦄ →
    let module M₁ = Modality 𝕄₁
        module M₂ = Modality 𝕄₂
    in
    M₁.Trivial ⇔ M₂.Trivial →
    (¬ M₁.Trivial →
     (∀ p → p ≡ M₁.𝟘 ⇔ tr p ≡ M₂.𝟘) ×
     (∀ p → p ≡ M₁.𝟘 ⇔ tr-Σ p ≡ M₂.𝟘)) →
    Is-omega-preserving-morphism 𝕄₁ 𝕄₂ tr →
    Is-Σ-order-embedding-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-order-embedding-C trp
      (with-[]-cong 𝕄₁ v₁ C₁)
      (with-[]-cong 𝕄₂ v₂ C₂)
      tr tr-Σ
  OE-with-[]-cong {𝕄₁} {C₁} {C₂} hyp₁ hyp₂ hyp₃ r =
    let hyp₁₂ = λ non-triv →
                  non-triv ∘→ hyp₁ .proj₂ ,
                  let hyp₂₁ , hyp₂₂ = hyp₂ non-triv in
                  hyp₂₁ _ .proj₁ refl , hyp₂₂ _ .proj₁ refl
    in record
    { is-Σ-morphism-C =
        M-with-[]-cong hyp₁₂ hyp₃ is-Σ-morphism-C
    ; is-Σ-order-embedding-TC = record
        { is-Σ-morphism-TC =
            M-TC-with-[]-cong hyp₁₂ hyp₃ is-Σ-morphism-C
        ; unfolding-mode-reflected = unfolding-mode-reflected
        ; level-support-reflected  = level-support-reflected
        ; Unitʷ-η-reflected        = Unitʷ-η-reflected
        ; Unit-reflected           =
            ⊎.map Unit-reflected (_∘→ hyp₁ .proj₁)
        ; ΠΣ-reflected = λ {b = b} ok →
            case singleton b of λ where
              (BMΠ , refl) →
                ΠΣ-reflected ok
              (BMΣ s , refl) →
                ⊎.map
                  ΠΣ-reflected
                  (λ (non-triv , tr-Σ-p≡𝟘 , tr-q≡𝟘) →
                     let ≡𝟘⇔tr≡𝟘 , ≡𝟘⇔tr-Σ≡𝟘 =
                           hyp₂ (non-triv ∘→ hyp₁ .proj₁)
                     in
                     non-triv ∘→ hyp₁ .proj₁ ,
                     ≡𝟘⇔tr-Σ≡𝟘 _ .proj₂ tr-Σ-p≡𝟘 ,
                     ≡𝟘⇔tr≡𝟘 _ .proj₂ tr-q≡𝟘)
                  ok
        ; Opacity-reflected = Opacity-reflected
        ; K-reflected       = K-reflected
        ; []-cong-reflected = λ _ → case MP₁.trivial? of λ where
            (yes trivial)    → inj₂ trivial
            (no non-trivial) → inj₁ (inj₂ non-trivial)
        ; Equality-reflection-reflected = Equality-reflection-reflected
        ; Quot-reflected                = Quot-reflected
        ; Omega-allowed-reflected       = λ _ → with-ω
        }
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
    ; []-cong-mode-reflected = λ _ _ → case MP₁.trivial? of λ where
        (yes triv) → inj₂ triv
        (no not)   → inj₁ (inj₂ not)
    ; erased-matches-for-J-reflected =
        none-for-𝟙ᵐ-≤ᵉᵐ
          (erased-matches-for-J-reflected ∘→ ≈ᵐ-symmetric) ∘→
        ≈ᵐ-symmetric
    ; erased-matches-for-K-reflected =
        erased-matches-for-K-reflected
    }
    where
    module MP₁ = Graded.Modality.Properties 𝕄₁
    open Is-Σ-order-embedding-C r

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

  -- A lemma related to Is-Σ-morphism-C and no-[]-cong.

  M-no-[]-cong :
    Is-Σ-morphism-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-morphism-C trp
      (no-[]-cong 𝕄₁ v₁ C₁)
      (no-[]-cong 𝕄₂ v₂ C₂)
      tr tr-Σ
  M-no-[]-cong {C₁} {C₂} m = record
    { 𝟘ᵐ-preserved                   = 𝟘ᵐ-preserved
    ; natrec-mode-preserved          = natrec-mode-preserved
    ; starˢ-sink-preserved           = starˢ-sink-preserved
    ; Id-erased-preserved            = Id-erased-preserved
    ; erased-matches-for-J-preserved = λ m₁≈m₂ →
        at-least-some-≤ᵉᵐ C₁.erased-matches-for-J
          C₂.erased-matches-for-J (erased-matches-for-J-preserved m₁≈m₂)
          m₁≈m₂
    ; erased-matches-for-K-preserved = erased-matches-for-K-preserved
    ; Qrec-motive-erased-preserved   = Qrec-motive-erased-preserved
    ; is-Σ-morphism-TC               = Ex.M-no-[]-cong is-Σ-morphism-TC
    ; nr-preserving                  = nr-preserving
    ; no-nr-preserving               = no-nr-preserving
    ; no-nr-glb-preserving           = no-nr-glb-preserving
    ; Prodrec-preserved              = Prodrec-preserved
    ; Unitrec-preserved              = Unitrec-preserved
    ; Emptyrec-preserved             = Emptyrec-preserved
    ; []-cong-mode-preserved         = λ _ ()
    }
    where
    module C₁ = Configuration C₁
    module C₂ = Configuration C₂
    open Is-Σ-morphism-C m

opaque

  -- A lemma related to Is-Σ-order-embedding-C and no-[]-cong.

  OE-no-[]-cong :
    let module M₁ = Modality 𝕄₁
        module M₂ = Modality 𝕄₂
        module V₂ = Mode-variant v₂
        module C₁ = Configuration C₁
    in
    (M₂.Trivial → M₁.Trivial) →
    Is-Σ-order-embedding-C trp C₁ C₂ tr tr-Σ →
    Is-Σ-order-embedding-C trp
      (no-[]-cong 𝕄₁ v₁ C₁)
      (no-[]-cong 𝕄₂ v₂ C₂)
      tr tr-Σ
  OE-no-[]-cong {C₁} {C₂} hyp r = record
    { is-Σ-morphism-C =
        M-no-[]-cong is-Σ-morphism-C
    ; is-Σ-order-embedding-TC =
        Ex.OE-no-[]-cong (flip C₁.[]-cong→¬Trivial ∘→ hyp)
          is-Σ-order-embedding-TC
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
        _ (inj₁ ())
        _ (inj₂ triv) → inj₂ (hyp triv)
    ; erased-matches-for-J-reflected = λ m₁≈m₂ →
        at-least-some-≤ᵉᵐ
          C₂.erased-matches-for-J C₁.erased-matches-for-J
          (erased-matches-for-J-reflected m₁≈m₂) (≈ᵐ-symmetric m₁≈m₂)
    ; erased-matches-for-K-reflected =
        erased-matches-for-K-reflected
    }
    where
    module C₁ = Configuration C₁
    module C₂ = Configuration C₂
    open Is-Σ-order-embedding-C r

------------------------------------------------------------------------
-- Some lemmas related to only-some-erased-matches and concrete
-- translation functions

opaque

  -- A lemma related to Is-Σ-morphism-C and unit→erasure.

  M-only-some-erased-matches-unit→erasure :
    Is-Σ-morphism-C trp C₁ C₂ unit→erasure tr →
    Is-Σ-morphism-C trp
      (only-some-erased-matches UnitModality v₁ C₁)
      (only-some-erased-matches ErasureModality v₂ C₂)
      unit→erasure tr
  M-only-some-erased-matches-unit→erasure =
    M-only-some-erased-matches
      (λ _ → inj₂ (λ _ ())) unit⇨erasure-omega-preserving

opaque

  -- A lemma related to Is-Σ-order-embedding-C and unit→erasure.

  OE-only-some-erased-matches-unit→erasure :
    Is-Σ-order-embedding-C trp C₁ C₂ unit→erasure tr →
    Is-Σ-order-embedding-C trp
      (only-some-erased-matches UnitModality v₁ C₁)
      (only-some-erased-matches ErasureModality v₂ C₂)
      unit→erasure tr
  OE-only-some-erased-matches-unit→erasure =
    OE-only-some-erased-matches
      (λ tt≢tt → ⊥-elim $ tt≢tt refl) (λ _ → inj₂ (λ _ ()))
      unit⇨erasure-omega-preserving

opaque

  -- A lemma related to Is-Σ-morphism-C and erasure→unit.

  M-only-some-erased-matches-erasure→unit :
    Is-Σ-morphism-C trp C₁ C₂ erasure→unit tr →
    Is-Σ-morphism-C trp
      (only-some-erased-matches ErasureModality v₁ C₁)
      (only-some-erased-matches UnitModality v₂ C₂)
      erasure→unit tr
  M-only-some-erased-matches-erasure→unit =
    M-only-some-erased-matches
      (λ tt≢tt → ⊥-elim $ tt≢tt refl) erasure⇨unit-omega-preserving

opaque

  -- A lemma related to Is-Σ-order-embedding-C and erasure→unit.

  ¬-OE-only-some-erased-matches-erasure→unit :
    ∀ C →
    let 𝕄₂ = UnitModality in
    ¬ Is-Σ-order-embedding-C trp
        (only-some-erased-matches ErasureModality v₁ C)
        (only-some-erased-matches 𝕄₂ v₂
           (no-restrictions 𝕄₂ v₂ o₂ nm₁ b₁ b₂ b₃ b₄ b₅))
        erasure→unit tr
  ¬-OE-only-some-erased-matches-erasure→unit _ r =
    Prodrec-reflected {p = 𝟘} {q = 𝟘} [ 𝟙ᵐ ] (_ , (λ _ tt≢tt → tt≢tt))
      .proj₂ refl (λ ()) refl
    where
    open Is-Σ-order-embedding-C r

opaque

  -- A lemma related to Is-Σ-morphism-C and erasure→zero-one-many.

  M-only-some-erased-matches-erasure→zero-one-many :
    Is-Σ-morphism-C trp C₁ C₂ erasure→zero-one-many tr →
    Is-Σ-morphism-C trp
      (only-some-erased-matches ErasureModality v₁ C₁)
      (only-some-erased-matches (zero-one-many-modality 𝟙≤𝟘) v₂ C₂)
      erasure→zero-one-many tr
  M-only-some-erased-matches-erasure→zero-one-many =
    M-only-some-erased-matches
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              𝟘 _  → refl
              ω ())
         ))
      erasure⇨zero-one-many-omega-preserving

opaque

  -- A lemma related to Is-Σ-order-embedding-C and
  -- erasure→zero-one-many.

  OE-only-some-erased-matches-erasure→zero-one-many :
    Is-Σ-order-embedding-C trp C₁ C₂ erasure→zero-one-many tr →
    Is-Σ-order-embedding-C trp
      (only-some-erased-matches ErasureModality v₁ C₁)
      (only-some-erased-matches (zero-one-many-modality 𝟙≤𝟘) v₂ C₂)
      erasure→zero-one-many tr
  OE-only-some-erased-matches-erasure→zero-one-many =
    OE-only-some-erased-matches
      (λ _ → (λ ()) , (λ { refl → refl }))
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              𝟘 _  → refl
              ω ())
         ))
      erasure⇨zero-one-many-omega-preserving

opaque

  -- A lemma related to Is-Σ-morphism-C and zero-one-many→erasure.

  M-only-some-erased-matches-zero-one-many→erasure :
    Is-Σ-morphism-C trp C₁ C₂ zero-one-many→erasure tr →
    Is-Σ-morphism-C trp
      (only-some-erased-matches (zero-one-many-modality 𝟙≤𝟘) v₁ C₁)
      (only-some-erased-matches (ErasureModality) v₂ C₂)
      zero-one-many→erasure tr
  M-only-some-erased-matches-zero-one-many→erasure =
    M-only-some-erased-matches
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              𝟘 _  → refl
              𝟙 ()
              ω ())
         ))
      zero-one-many⇨erasure-omega-preserving

opaque

  -- A lemma related to Is-Σ-order-embedding-C and
  -- zero-one-many→erasure.

  OE-only-some-erased-matches-zero-one-many→erasure :
    Is-Σ-order-embedding-C trp C₁ C₂ zero-one-many→erasure tr →
    Is-Σ-order-embedding-C trp
      (only-some-erased-matches (zero-one-many-modality 𝟙≤𝟘) v₁ C₁)
      (only-some-erased-matches ErasureModality v₂ C₂)
      zero-one-many→erasure tr
  OE-only-some-erased-matches-zero-one-many→erasure =
    OE-only-some-erased-matches
      (λ _ → (λ ()) , (λ { refl → refl }))
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              𝟘 _  → refl
              𝟙 ()
              ω ())
         ))
      zero-one-many⇨erasure-omega-preserving

opaque

  -- A lemma related to Is-Σ-morphism-C and
  -- linearity→linear-or-affine.

  M-only-some-erased-matches-linearity→linear-or-affine :
    Is-Σ-morphism-C trp C₁ C₂ linearity→linear-or-affine tr →
    Is-Σ-morphism-C trp
      (only-some-erased-matches linearityModality v₁ C₁)
      (only-some-erased-matches linear-or-affine v₂ C₂)
      linearity→linear-or-affine tr
  M-only-some-erased-matches-linearity→linear-or-affine =
    M-only-some-erased-matches
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              𝟘 _  → refl
              𝟙 ()
              ω ())
         ))
      linearity⇨linear-or-affine-omega-preserving

opaque

  -- A lemma related to Is-Σ-order-embedding-C and
  -- linearity→linear-or-affine.

  OE-only-some-erased-matches-linearity→linear-or-affine :
    Is-Σ-order-embedding-C trp C₁ C₂ linearity→linear-or-affine tr →
    Is-Σ-order-embedding-C trp
      (only-some-erased-matches linearityModality v₁ C₁)
      (only-some-erased-matches linear-or-affine v₂ C₂)
      linearity→linear-or-affine tr
  OE-only-some-erased-matches-linearity→linear-or-affine =
    OE-only-some-erased-matches
      (λ _ → (λ ()) , (λ { refl → refl }))
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              𝟘 _  → refl
              𝟙 ()
              ω ())
         ))
      linearity⇨linear-or-affine-omega-preserving

opaque

  -- A lemma related to Is-Σ-morphism-C and
  -- linear-or-affine→linearity.

  M-only-some-erased-matches-linear-or-affine→linearity :
    Is-Σ-morphism-C trp C₁ C₂ linear-or-affine→linearity tr →
    Is-Σ-morphism-C trp
      (only-some-erased-matches linear-or-affine v₁ C₁)
      (only-some-erased-matches linearityModality v₂ C₂)
      linear-or-affine→linearity tr
  M-only-some-erased-matches-linear-or-affine→linearity =
    M-only-some-erased-matches
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              𝟘  _  → refl
              𝟙  ()
              ≤𝟙 ()
              ≤ω ())
         ))
      linear-or-affine⇨linearity-omega-preserving

opaque

  -- A lemma related to Is-Σ-order-embedding-C and
  -- linear-or-affine→linearity.

  OE-only-some-erased-matches-linear-or-affine→linearity :
    Is-Σ-order-embedding-C trp C₁ C₂ linear-or-affine→linearity tr →
    Is-Σ-order-embedding-C trp
      (only-some-erased-matches linear-or-affine v₁ C₁)
      (only-some-erased-matches linearityModality v₂ C₂)
      linear-or-affine→linearity tr
  OE-only-some-erased-matches-linear-or-affine→linearity =
    OE-only-some-erased-matches
      (λ _ → (λ ()) , (λ { refl → refl }))
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              𝟘  _  → refl
              𝟙  ()
              ≤𝟙 ()
              ≤ω ())
         ))
      linear-or-affine⇨linearity-omega-preserving

opaque

  -- A lemma related to Is-Σ-morphism-C and affine→linear-or-affine.

  M-only-some-erased-matches-affine→linear-or-affine :
    Is-Σ-morphism-C trp C₁ C₂ affine→linear-or-affine tr →
    Is-Σ-morphism-C trp
      (only-some-erased-matches affineModality v₁ C₁)
      (only-some-erased-matches linear-or-affine v₂ C₂)
      affine→linear-or-affine tr
  M-only-some-erased-matches-affine→linear-or-affine =
    M-only-some-erased-matches
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              𝟘 _  → refl
              𝟙 ()
              ω ())
         ))
      affine⇨linear-or-affine-omega-preserving

opaque

  -- A lemma related to Is-Σ-order-embedding-C and
  -- affine→linear-or-affine.

  OE-only-some-erased-matches-affine→linear-or-affine :
    Is-Σ-order-embedding-C trp C₁ C₂ affine→linear-or-affine tr →
    Is-Σ-order-embedding-C trp
      (only-some-erased-matches affineModality v₁ C₁)
      (only-some-erased-matches linear-or-affine v₂ C₂)
      affine→linear-or-affine tr
  OE-only-some-erased-matches-affine→linear-or-affine =
    OE-only-some-erased-matches
      (λ _ → (λ ()) , (λ { refl → refl }))
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              𝟘 _  → refl
              𝟙 ()
              ω ())
         ))
      affine⇨linear-or-affine-omega-preserving

opaque

  -- A lemma related to Is-Σ-morphism-C and linear-or-affine→affine.

  M-only-some-erased-matches-linear-or-affine→affine :
    Is-Σ-morphism-C trp C₁ C₂ linear-or-affine→affine tr →
    Is-Σ-morphism-C trp
      (only-some-erased-matches linear-or-affine v₁ C₁)
      (only-some-erased-matches affineModality v₂ C₂)
      linear-or-affine→affine tr
  M-only-some-erased-matches-linear-or-affine→affine =
    M-only-some-erased-matches
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              𝟘  _  → refl
              𝟙  ()
              ≤𝟙 ()
              ≤ω ())
         ))
      linear-or-affine⇨affine-omega-preserving

opaque

  -- A lemma related to Is-Σ-order-embedding-C and
  -- linear-or-affine→affine.

  OE-only-some-erased-matches-linear-or-affine→affine :
    Is-Σ-order-embedding-C trp C₁ C₂ linear-or-affine→affine tr →
    Is-Σ-order-embedding-C trp
      (only-some-erased-matches linear-or-affine v₁ C₁)
      (only-some-erased-matches affineModality v₂ C₂)
      linear-or-affine→affine tr
  OE-only-some-erased-matches-linear-or-affine→affine =
    OE-only-some-erased-matches
      (λ _ → (λ ()) , (λ { refl → refl }))
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              𝟘  _  → refl
              𝟙  ()
              ≤𝟙 ()
              ≤ω ())
         ))
      linear-or-affine⇨affine-omega-preserving

opaque

  -- A lemma related to Is-Σ-morphism-C and affine→linearity.

  M-only-some-erased-matches-affine→linearity :
    Is-Σ-morphism-C trp C₁ C₂ affine→linearity tr →
    Is-Σ-morphism-C trp
      (only-some-erased-matches affineModality v₁ C₁)
      (only-some-erased-matches linearityModality v₂ C₂)
      affine→linearity tr
  M-only-some-erased-matches-affine→linearity =
    M-only-some-erased-matches
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              𝟘 _  → refl
              𝟙 ()
              ω ())
         ))
      affine⇨linearity-omega-preserving

opaque

  -- A lemma related to Is-Σ-order-embedding-C and affine→linearity.

  OE-only-some-erased-matches-affine→linearity :
    Is-Σ-order-embedding-C trp C₁ C₂ affine→linearity tr →
    Is-Σ-order-embedding-C trp
      (only-some-erased-matches affineModality v₁ C₁)
      (only-some-erased-matches linearityModality v₂ C₂)
      affine→linearity tr
  OE-only-some-erased-matches-affine→linearity =
    OE-only-some-erased-matches
      (λ _ → (λ ()) , (λ { refl → refl }))
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              𝟘 _  → refl
              𝟙 ()
              ω ())
         ))
      affine⇨linearity-omega-preserving

opaque

  -- A lemma related to Is-Σ-morphism-C and linearity→affine.

  M-only-some-erased-matches-linearity→affine :
    Is-Σ-morphism-C trp C₁ C₂ linearity→affine tr →
    Is-Σ-morphism-C trp
      (only-some-erased-matches linearityModality v₁ C₁)
      (only-some-erased-matches affineModality v₂ C₂)
      linearity→affine tr
  M-only-some-erased-matches-linearity→affine =
    M-only-some-erased-matches
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              𝟘 _  → refl
              𝟙 ()
              ω ())
         ))
      linearity⇨affine-omega-preserving

opaque

  -- A lemma related to Is-Σ-order-embedding-C and linearity→affine.

  OE-only-some-erased-matches-linearity→affine :
    Is-Σ-order-embedding-C trp C₁ C₂ linearity→affine tr →
    Is-Σ-order-embedding-C trp
      (only-some-erased-matches linearityModality v₁ C₁)
      (only-some-erased-matches affineModality v₂ C₂)
      linearity→affine tr
  OE-only-some-erased-matches-linearity→affine =
    OE-only-some-erased-matches
      (λ _ → (λ ()) , (λ { refl → refl }))
      (λ _ → inj₁
         ( (λ ())
         , (λ where
              𝟘 _  → refl
              𝟙 ()
              ω ())
         ))
      linearity⇨affine-omega-preserving

------------------------------------------------------------------------
-- Some lemmas related to no-erased-matches and concrete translation
-- functions

-- A lemma related to Is-Σ-morphism-C and unit→erasure.

M-no-erased-matches-unit→erasure :
  Is-Σ-morphism-C trp C₁ C₂ unit→erasure tr →
  Is-Σ-morphism-C trp
    (no-erased-matches UnitModality v₁ C₁)
    (no-erased-matches ErasureModality v₂ C₂)
    unit→erasure tr
M-no-erased-matches-unit→erasure =
  M-no-erased-matches
    (λ _ → inj₂ (λ _ ()))
    unit⇨erasure-omega-preserving

-- A lemma related to Is-Σ-order-embedding-C and unit→erasure.

OE-no-erased-matches-unit→erasure :
  Is-Σ-order-embedding-C trp C₁ C₂ unit→erasure tr →
  Is-Σ-order-embedding-C trp
    (no-erased-matches UnitModality v₁ C₁)
    (no-erased-matches ErasureModality v₂ C₂)
    unit→erasure tr
OE-no-erased-matches-unit→erasure =
  OE-no-erased-matches
    (λ tt≢tt → ⊥-elim $ tt≢tt refl)
    (λ _ → inj₂ (λ _ ()))
    unit⇨erasure-omega-preserving

-- A lemma related to Is-Σ-morphism-C and erasure→unit.

M-no-erased-matches-erasure→unit :
  Is-Σ-morphism-C trp C₁ C₂ erasure→unit tr →
  Is-Σ-morphism-C trp
    (no-erased-matches ErasureModality v₁ C₁)
    (no-erased-matches UnitModality v₂ C₂)
    erasure→unit tr
M-no-erased-matches-erasure→unit =
  M-no-erased-matches
    (λ tt≢tt → ⊥-elim $ tt≢tt refl)
    erasure⇨unit-omega-preserving

-- A lemma related to Is-Σ-order-embedding-C and erasure→unit.

¬-OE-no-erased-matches-erasure→unit :
  ∀ C →
  let 𝕄₂ = UnitModality in
  ¬ Is-Σ-order-embedding-C trp
      (no-erased-matches ErasureModality v₁ C)
      (no-erased-matches 𝕄₂ v₂
         (no-restrictions 𝕄₂ v₂ o₂ nm₂ b₁ b₂ b₃ b₄ b₅))
      erasure→unit tr
¬-OE-no-erased-matches-erasure→unit _ r =
  Prodrec-reflected {p = 𝟘} {q = 𝟘} [ 𝟙ᵐ ] (_ , λ _ tt≢tt → tt≢tt)
    .proj₂ refl (λ ()) refl
  where
  open Is-Σ-order-embedding-C r

-- A lemma related to Is-Σ-morphism-C and erasure→zero-one-many.

M-no-erased-matches-erasure→zero-one-many :
  Is-Σ-morphism-C trp C₁ C₂ erasure→zero-one-many tr →
  Is-Σ-morphism-C trp
    (no-erased-matches ErasureModality v₁ C₁)
    (no-erased-matches (zero-one-many-modality 𝟙≤𝟘) v₂ C₂)
    erasure→zero-one-many tr
M-no-erased-matches-erasure→zero-one-many =
  M-no-erased-matches
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            𝟘 _  → refl
            ω ())
       ))
    erasure⇨zero-one-many-omega-preserving

-- A lemma related to Is-Σ-order-embedding-C and
-- erasure→zero-one-many.

OE-no-erased-matches-erasure→zero-one-many :
  Is-Σ-order-embedding-C trp C₁ C₂ erasure→zero-one-many tr →
  Is-Σ-order-embedding-C trp
    (no-erased-matches ErasureModality v₁ C₁)
    (no-erased-matches (zero-one-many-modality 𝟙≤𝟘) v₂ C₂)
    erasure→zero-one-many tr
OE-no-erased-matches-erasure→zero-one-many =
  OE-no-erased-matches
    (λ _ → (λ ()) , (λ { refl → refl }))
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            𝟘 _  → refl
            ω ())
       ))
    erasure⇨zero-one-many-omega-preserving

-- A lemma related to Is-Σ-morphism-C and zero-one-many→erasure.

M-no-erased-matches-zero-one-many→erasure :
  Is-Σ-morphism-C trp C₁ C₂ zero-one-many→erasure tr →
  Is-Σ-morphism-C trp
    (no-erased-matches (zero-one-many-modality 𝟙≤𝟘) v₁ C₁)
    (no-erased-matches ErasureModality v₂ C₂)
    zero-one-many→erasure tr
M-no-erased-matches-zero-one-many→erasure =
  M-no-erased-matches
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            𝟘 _  → refl
            𝟙 ()
            ω ())
       ))
    zero-one-many⇨erasure-omega-preserving

-- A lemma related to Is-Σ-order-embedding-C and
-- zero-one-many→erasure.

OE-no-erased-matches-zero-one-many→erasure :
  Is-Σ-order-embedding-C trp C₁ C₂ zero-one-many→erasure tr →
  Is-Σ-order-embedding-C trp
    (no-erased-matches (zero-one-many-modality 𝟙≤𝟘) v₁ C₁)
    (no-erased-matches ErasureModality v₂ C₂)
    zero-one-many→erasure tr
OE-no-erased-matches-zero-one-many→erasure =
  OE-no-erased-matches
    (λ _ → (λ ()) , (λ { refl → refl }))
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            𝟘 _  → refl
            𝟙 ()
            ω ())
       ))
    zero-one-many⇨erasure-omega-preserving

-- A lemma related to Is-Σ-morphism-C and linearity→linear-or-affine.

M-no-erased-matches-linearity→linear-or-affine :
  Is-Σ-morphism-C trp C₁ C₂ linearity→linear-or-affine tr →
  Is-Σ-morphism-C trp
    (no-erased-matches linearityModality v₁ C₁)
    (no-erased-matches linear-or-affine v₂ C₂)
    linearity→linear-or-affine tr
M-no-erased-matches-linearity→linear-or-affine =
  M-no-erased-matches
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            𝟘 _  → refl
            𝟙 ()
            ω ())
       ))
    linearity⇨linear-or-affine-omega-preserving

-- A lemma related to Is-Σ-order-embedding-C and
-- linearity→linear-or-affine.

OE-no-erased-matches-linearity→linear-or-affine :
  Is-Σ-order-embedding-C trp C₁ C₂ linearity→linear-or-affine tr →
  Is-Σ-order-embedding-C trp
    (no-erased-matches linearityModality v₁ C₁)
    (no-erased-matches linear-or-affine v₂ C₂)
    linearity→linear-or-affine tr
OE-no-erased-matches-linearity→linear-or-affine =
  OE-no-erased-matches
    (λ _ → (λ ()) , (λ { refl → refl }))
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            𝟘 _  → refl
            𝟙 ()
            ω ())
       ))
    linearity⇨linear-or-affine-omega-preserving

-- A lemma related to Is-Σ-morphism-C and linear-or-affine→linearity.

M-no-erased-matches-linear-or-affine→linearity :
  Is-Σ-morphism-C trp C₁ C₂ linear-or-affine→linearity tr →
  Is-Σ-morphism-C trp
    (no-erased-matches linear-or-affine v₁ C₁)
    (no-erased-matches linearityModality v₂ C₂)
    linear-or-affine→linearity tr
M-no-erased-matches-linear-or-affine→linearity =
  M-no-erased-matches
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            𝟘  _  → refl
            𝟙  ()
            ≤𝟙 ()
            ≤ω ())
       ))
    linear-or-affine⇨linearity-omega-preserving

-- A lemma related to Is-Σ-order-embedding-C and
-- linear-or-affine→linearity.

OE-no-erased-matches-linear-or-affine→linearity :
  Is-Σ-order-embedding-C trp C₁ C₂ linear-or-affine→linearity tr →
  Is-Σ-order-embedding-C trp
    (no-erased-matches linear-or-affine v₁ C₁)
    (no-erased-matches linearityModality v₂ C₂)
    linear-or-affine→linearity tr
OE-no-erased-matches-linear-or-affine→linearity =
  OE-no-erased-matches
    (λ _ → (λ ()) , (λ { refl → refl }))
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            𝟘  _  → refl
            𝟙  ()
            ≤𝟙 ()
            ≤ω ())
       ))
    linear-or-affine⇨linearity-omega-preserving

-- A lemma related to Is-Σ-morphism-C and affine→linear-or-affine.

M-no-erased-matches-affine→linear-or-affine :
  Is-Σ-morphism-C trp C₁ C₂ affine→linear-or-affine tr →
  Is-Σ-morphism-C trp
    (no-erased-matches affineModality v₁ C₁)
    (no-erased-matches linear-or-affine v₂ C₂)
    affine→linear-or-affine tr
M-no-erased-matches-affine→linear-or-affine =
  M-no-erased-matches
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            𝟘 _  → refl
            𝟙 ()
            ω ())
       ))
    affine⇨linear-or-affine-omega-preserving

-- A lemma related to Is-Σ-order-embedding-C and
-- affine→linear-or-affine.

OE-no-erased-matches-affine→linear-or-affine :
  Is-Σ-order-embedding-C trp C₁ C₂ affine→linear-or-affine tr →
  Is-Σ-order-embedding-C trp
    (no-erased-matches affineModality v₁ C₁)
    (no-erased-matches linear-or-affine v₂ C₂)
    affine→linear-or-affine tr
OE-no-erased-matches-affine→linear-or-affine =
  OE-no-erased-matches
    (λ _ → (λ ()) , (λ { refl → refl }))
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            𝟘 _  → refl
            𝟙 ()
            ω ())
       ))
    affine⇨linear-or-affine-omega-preserving

-- A lemma related to Is-Σ-morphism-C and linear-or-affine→affine.

M-no-erased-matches-linear-or-affine→affine :
  Is-Σ-morphism-C trp C₁ C₂ linear-or-affine→affine tr →
  Is-Σ-morphism-C trp
    (no-erased-matches linear-or-affine v₁ C₁)
    (no-erased-matches affineModality v₂ C₂)
    linear-or-affine→affine tr
M-no-erased-matches-linear-or-affine→affine =
  M-no-erased-matches
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            𝟘  _  → refl
            𝟙  ()
            ≤𝟙 ()
            ≤ω ())
       ))
    linear-or-affine⇨affine-omega-preserving

-- A lemma related to Is-Σ-order-embedding-C and
-- linear-or-affine→affine.

OE-no-erased-matches-linear-or-affine→affine :
  Is-Σ-order-embedding-C trp C₁ C₂ linear-or-affine→affine tr →
  Is-Σ-order-embedding-C trp
    (no-erased-matches linear-or-affine v₁ C₁)
    (no-erased-matches affineModality v₂ C₂)
    linear-or-affine→affine tr
OE-no-erased-matches-linear-or-affine→affine =
  OE-no-erased-matches
    (λ _ → (λ ()) , (λ { refl → refl }))
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            𝟘  _  → refl
            𝟙  ()
            ≤𝟙 ()
            ≤ω ())
       ))
    linear-or-affine⇨affine-omega-preserving

-- A lemma related to Is-Σ-morphism-C and affine→linearity.

M-no-erased-matches-affine→linearity :
  Is-Σ-morphism-C trp C₁ C₂ affine→linearity tr →
  Is-Σ-morphism-C trp
    (no-erased-matches affineModality v₁ C₁)
    (no-erased-matches linearityModality v₂ C₂)
    affine→linearity tr
M-no-erased-matches-affine→linearity =
  M-no-erased-matches
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            𝟘 _  → refl
            𝟙 ()
            ω ())
       ))
    affine⇨linearity-omega-preserving

-- A lemma related to Is-Σ-order-embedding-C and affine→linearity.

OE-no-erased-matches-affine→linearity :
  Is-Σ-order-embedding-C trp C₁ C₂ affine→linearity tr →
  Is-Σ-order-embedding-C trp
    (no-erased-matches affineModality v₁ C₁)
    (no-erased-matches linearityModality v₂ C₂)
    affine→linearity tr
OE-no-erased-matches-affine→linearity =
  OE-no-erased-matches
    (λ _ → (λ ()) , (λ { refl → refl }))
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            𝟘 _  → refl
            𝟙 ()
            ω ())
       ))
    affine⇨linearity-omega-preserving

-- A lemma related to Is-Σ-morphism-C and linearity→affine.

M-no-erased-matches-linearity→affine :
  Is-Σ-morphism-C trp C₁ C₂ linearity→affine tr →
  Is-Σ-morphism-C trp
    (no-erased-matches linearityModality v₁ C₁)
    (no-erased-matches affineModality v₂ C₂)
    linearity→affine tr
M-no-erased-matches-linearity→affine =
  M-no-erased-matches
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            𝟘 _  → refl
            𝟙 ()
            ω ())
       ))
    linearity⇨affine-omega-preserving

-- A lemma related to Is-Σ-order-embedding-C and linearity→affine.

OE-no-erased-matches-linearity→affine :
  Is-Σ-order-embedding-C trp C₁ C₂ linearity→affine tr →
  Is-Σ-order-embedding-C trp
    (no-erased-matches linearityModality v₁ C₁)
    (no-erased-matches affineModality v₂ C₂)
    linearity→affine tr
OE-no-erased-matches-linearity→affine =
  OE-no-erased-matches
    (λ _ → (λ ()) , (λ { refl → refl }))
    (λ _ → inj₁
       ( (λ ())
       , (λ where
            𝟘 _  → refl
            𝟙 ()
            ω ())
       ))
    linearity⇨affine-omega-preserving

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
         Has-well-behaved-zero M₁ 𝕄₁ ⦄ →
     Has-well-behaved-zero M₂ 𝕄₂) →
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
    (⦃ 𝟘-well-behaved : Has-well-behaved-zero M₂ 𝕄₂ ⦄ →
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
            Has-well-behaved-zero M₁ 𝕄₁ ⦄ →
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
             LA.linear-or-affine ⦄ →
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
              Has-well-behaved-zero Linearity linearityModality ⦄ →
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
             LA.linear-or-affine ⦄ →
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
              Has-well-behaved-zero Affine affineModality ⦄ →
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
