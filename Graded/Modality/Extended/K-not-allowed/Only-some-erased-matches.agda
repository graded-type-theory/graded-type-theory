------------------------------------------------------------------------
-- Some examples of extended modalities, along with some morphisms
-- between them
------------------------------------------------------------------------

-- The formalisation contains a number of parameters. These examples
-- show that it is possible to instantiate all of the parameters at
-- the same time.

module Graded.Modality.Extended.K-not-allowed.Only-some-erased-matches
  where

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum
open import Tools.Unit

open import Configuration-types
open import Configuration-types.Configuration.Zero-one
open import Configuration-types.Erased-matches
open import Configuration-types.Natrec
open import Configuration-types.Omega

import Definition.Typechecking.Decidable.Assumptions as TD
open import Definition.Untyped.NotParametrised
open import Definition.Untyped.Properties.NotParametrised

open import Graded.FullReduction.Assumptions
open import Graded.Modality
open import Graded.Modality.Extended
import Graded.Modality.Instances.Affine as A
import Graded.Modality.Instances.Erasure as E
import Graded.Modality.Instances.Erasure.Modality as EM
import Graded.Modality.Instances.Erasure.Properties as EP
import Graded.Modality.Instances.Linearity as L
import Graded.Modality.Instances.Linear-or-affine as LA
import Graded.Modality.Instances.Unit as U
open import Graded.Modality.Morphism
open import Graded.Modality.Morphism.Configuration
open import Graded.Modality.Morphism.Configuration.Examples
open import Graded.Modality.Morphism.Examples
open import Graded.Modality.Omega-instances
open import Graded.Mode.Instances.Zero-one.Variant
open import Graded.Mode.Instances.Zero-one
import Graded.Usage.Decidable.Assumptions as UD

private variable
  a : Level

------------------------------------------------------------------------
-- Extended modalities

-- The following extended modalities all satisfy the following
-- properties:
--
-- * The term former prodrec r is allowed when the mode is 𝟘ᵐ or r is
--   non-zero or the modality is trivial.
-- * There are no restrictions on unitrec or emptyrec.
-- * Strong unit types are not allowed to be used as sinks.
-- * Id-erased is not inhabited.
-- * Erased matches are not allowed for J and K when the mode is 𝟙ᵐ,
--   and all erased matches are allowed for J and K when the mode
--   is 𝟘ᵐ.
-- * Eta-equality is not allowed for weak types.
-- * Strong unit types are not allowed, but weak unit types are
--   allowed.
-- * Strong Σ-types are not allowed.
-- * Π-types and weak Σ-types are allowed exactly when the following
--   conditions are satisfied:
--   * Whenever the "first grades" are ω, then the second grades
--     are ω.
--   * Whenever the first grades are not ω, then the second grades
--     are 𝟘.
-- * The K rule is not allowed.
-- * []-cong is allowed exactly when the modality is non-trivial, the
--   strength is 𝕨, and the mode is not 𝟙ᵐ.
-- * Opaque definitions are allowed.
-- * Equality reflection is not allowed.
-- * Level is small.
-- * Omega-plus-allowed is inhabited.
-- * Quotients are not allowed and the motive of qrec is not treated
--   as erased.
-- * 𝟘ᵐ is allowed exactly when the modality is non-trivial.

All-properties-hold-for : Extended-modality a → Set a
All-properties-hold-for M =
  (∀ {m r p q} → Prodrec-allowed m r p q ⇔ (m ≢ 𝟙ᵐ ⊎ r ≢ 𝟘 ⊎ Trivial)) ×
  (∀ {m p q} → Unitrec-allowed m p q) ×
  (∀ {m p} → Emptyrec-allowed m p) ×
  ¬ Starˢ-sink ×
  ¬ Id-erased ×
  erased-matches-for-J 𝟙ᵐ ≡ none ×
  erased-matches-for-K 𝟙ᵐ ≡ none ×
  (∀ {m} → m ≢ 𝟙ᵐ → erased-matches-for-J m ≡ all) ×
  (∀ {m} → m ≢ 𝟙ᵐ → erased-matches-for-K m ≡ all) ×
  ¬ Unitʷ-η ×
  ¬ Unit-allowed 𝕤 ×
  Unit-allowed 𝕨 ×
  (∀ {b p q} →
   ΠΣ-allowed b p q ⇔
   (b ≢ BMΣ 𝕤 × (p ≡ ω → q ≡ ω) × (p ≢ ω → q ≡ 𝟘))) ×
  ¬ K-allowed ×
  (∀ {s} → []-cong-allowed s ⇔ (¬ Trivial × s ≡ 𝕨)) ×
  (∀ {s m} → []-cong-allowed-mode s m ⇔ (¬ Trivial × s ≡ 𝕨 × m ≢ 𝟙ᵐ)) ×
  Opacity-allowed ×
  ¬ Equality-reflection ×
  Level-is-small ×
  Omega-plus-allowed ×
  ¬ Quot-allowed ×
  ¬ Qrec-motive-erased ×
  (T 𝟘ᵐ-allowed ⇔ (¬ Trivial))
  where
  open Extended-modality M
  open Mode-variant MV

private

  -- Functions used to construct the modalities below.

  C′ :
    {M : Set} {𝕄 : Modality M}
    {v : Mode-variant 𝕄} →
    ⦃ ok : Has-omega M 𝕄 ⦄ →
    Has-nr M 𝕄 →
    Configuration (Zero-one-isMode v)
  C′ has-nr =
    only-some-erased-matches _ _ $
    no-quotients _ _ $
    no-strong-types _ _ $
    second-ΠΣ-quantities-𝟘-or-ω _ _ $
    no-restrictions _ _ with-ω (Nr ⦃ has-nr ⦄) false false false false
      false

  opaque

    Assumptions-C′ :
      {M : Set} {𝕄 : Modality M}
      {v : Mode-variant 𝕄} →
      {has-nr : Has-nr _ 𝕄} →
      ⦃ ok : Has-omega M 𝕄 ⦄ →
      Decidable (_≡_ {A = M}) →
      UD.Assumptions (C′ {𝕄 = 𝕄} {v = v} has-nr)
    Assumptions-C′ {has-nr} =
      Assumptions-only-some-erased-matches _ _ ∘→
      Assumptions-no-quotients _ _ ∘→
      Assumptions-no-strong-types _ _ ∘→
      Assumptions-second-ΠΣ-quantities-𝟘-or-ω _ _ ∘→
      Assumptions-no-restrictions _ _ {omega = with-ω}
        ⦃ Nr ⦃ Nr ⦃ has-nr ⦄ ⦄ ⦄

-- A trivial modality.

Trivial : Extended-modality lzero
Trivial = λ where
    .M   → ⊤
    .𝕄   → U.UnitModality
    .MV  → 𝟘ᵐ-Not-Allowed _
    .C   → C′ U.unit-has-nr
    .FA  → U.full-reduction-assumptions
    .DA  → Assumptions-C′ U._≟_
    .NR  → Nr ⦃ U.unit-has-nr ⦄
    .NO-NR-GLB → U.unit-supports-glb-for-nr
    .HAS-ω → U.unit-has-omega
    .NR₀ → U.nr-linearity-like-for-𝟘
    .NR₁ → U.nr-linearity-like-for-𝟙
    .SUB → U.unit-supports-subtraction
  where
  open Extended-modality

opaque

  -- The properties listed above all hold for Trivial.

  All-properties-hold-for-Trivial : All-properties-hold-for Trivial
  All-properties-hold-for-Trivial =
      ((λ _ → inj₂ (inj₂ refl)) , (λ _ → _ , (λ _ 𝟙≢𝟘 _ → 𝟙≢𝟘 refl)))
    , _
    , _
    , (λ ())
    , (λ ())
    , refl
    , refl
    , (λ where
         {m = 𝟙ᵐ}       → ⊥-elim ∘→ (_$ refl)
         {m = 𝟘ᵐ[ () ]})
    , (λ where
         {m = 𝟙ᵐ}       → ⊥-elim ∘→ (_$ refl)
         {m = 𝟘ᵐ[ () ]})
    , (λ ())
    , (_$ refl) ∘→ proj₂
    , (_ , (λ ()))
    , ( (λ ((_ , hyp₁) , hyp₂) → Lift.lower hyp₂ , hyp₁)
      , (λ (hyp₁ , hyp₂) → (_ , hyp₂) , lift hyp₁)
      )
    , (λ ())
    , (id⇔ ×-cong-⇔ ≢𝕤⇔≡𝕨)
    , (id⇔ ×-cong-⇔ (≢𝕤⇔≡𝕨 ×-cong-⇔ id⇔)) ∘⇔ sym⇔ Σ-assoc-⇔
    , lift (λ ())
    , (λ { (lift ()) })
    , Level-is-small⇔ .proj₂ refl
    , _
    , (λ ())
    , (λ ())
    , ((λ ()) , (_$ refl))
    where
    open Extended-modality Trivial

-- An erasure modality.

Erasure : Extended-modality lzero
Erasure = λ where
    .M       → E.Erasure
    .𝕄       → EM.ErasureModality
    .MV      → 𝟘ᵐ-Allowed _
    .C       → C′ EM.erasure-has-nr
    .FA      → EP.full-reduction-assumptions _
    .DA      → Assumptions-C′ E._≟_
    .NR      → Nr ⦃ EM.erasure-has-nr ⦄
    .NO-NR-GLB → EP.Erasure-supports-factoring-nr-rule
    .HAS-ω → EM.erasure-has-omega
    .NR₀ {z} → EP.nr-linearity-like-for-𝟘 {z = z}
    .NR₁ {z} → EP.nr-linearity-like-for-𝟙 {z = z}
    .SUB     → EP.supports-subtraction
  where
  open Extended-modality

opaque

  -- The properties listed above all hold for Erasure.

  All-properties-hold-for-Erasure : All-properties-hold-for Erasure
  All-properties-hold-for-Erasure =
      (λ where
         {m = 𝟘ᵐ} → (λ _ → inj₁ (λ ())) , (λ _ → _ , (λ ()))
         {m = 𝟙ᵐ} →
             (λ (_ , r≢𝟘) → inj₂ (inj₁ (r≢𝟘 refl (λ ()))))
           , (λ where
                (inj₁ 𝟙ᵐ≢𝟙ᵐ)      → ⊥-elim $ 𝟙ᵐ≢𝟙ᵐ refl
                (inj₂ (inj₁ r≢𝟘)) → _ , (λ _ _ → r≢𝟘)
                (inj₂ (inj₂ ()))))
    , _
    , _
    , (λ ())
    , (λ ())
    , refl
    , refl
    , (λ where
         {m = 𝟘ᵐ} _ → refl
         {m = 𝟙ᵐ}   → ⊥-elim ∘→ (_$ refl))
    , (λ where
         {m = 𝟘ᵐ} _ → refl
         {m = 𝟙ᵐ}   → ⊥-elim ∘→ (_$ refl))
    , (λ ())
    , (_$ refl) ∘→ proj₂
    , (_ , (λ ()))
    , ( (λ ((_ , hyp₁) , hyp₂) → Lift.lower hyp₂ , hyp₁)
      , (λ (hyp₁ , hyp₂) → (_ , hyp₂) , lift hyp₁)
      )
    , (λ ())
    , (id⇔ ×-cong-⇔ ≢𝕤⇔≡𝕨)
    , (id⇔ ×-cong-⇔ (≢𝕤⇔≡𝕨 ×-cong-⇔ id⇔)) ∘⇔ sym⇔ Σ-assoc-⇔
    , lift (λ ())
    , (λ { (lift ()) })
    , Level-is-small⇔ .proj₂ refl
    , _
    , (λ ())
    , (λ ())
    , ((λ _ ()) , _)
    where
    open Extended-modality Erasure

-- An affine types modality.

Affine-types : Extended-modality lzero
Affine-types = λ where
    .M           → A.Affine
    .𝕄           → A.affineModality
    .MV          → 𝟘ᵐ-Allowed _
    .C           → C″
    .FA          → FA′
    .DA          → Assumptions-C′ A._≟_
    .NR          → Nr ⦃ A.zero-one-many-has-nr ⦄
    .NO-NR-GLB   → A.zero-one-many-supports-glb-for-natrec
    .HAS-ω       → A.zero-one-many-has-omega
    .NR₀ {p}     → A.nr-linearity-like-for-𝟘 {p = p}
    .NR₁ {p} {z} → A.nr-linearity-like-for-𝟙 {p = p} {z = z}
    .SUB         → A.supports-subtraction
  where
  open Extended-modality

  C″ = C′ A.zero-one-many-has-nr

  opaque

    FA′ : Full-reduction-assumptions _ C″
    FA′ =
      A.full-reduction-assumptions
        (_ , (λ _ (_ , hyp) → case Lift.lower hyp refl of λ ()))

opaque

  -- The properties listed above all hold for Affine-types.

  All-properties-hold-for-Affine-types :
    All-properties-hold-for Affine-types
  All-properties-hold-for-Affine-types =
       (λ where
         {m = 𝟘ᵐ} → (λ _ → inj₁ (λ ())) , (λ _ → _ , (λ ()))
         {m = 𝟙ᵐ} →
             (λ (_ , r≢𝟘) → inj₂ (inj₁ (r≢𝟘 refl (λ ()))))
           , (λ where
                (inj₁ 𝟙ᵐ≢𝟙ᵐ)      → ⊥-elim $ 𝟙ᵐ≢𝟙ᵐ refl
                (inj₂ (inj₁ r≢𝟘)) → _ , (λ _ _ → r≢𝟘)
                (inj₂ (inj₂ ()))))
    , _
    , _
    , (λ ())
    , (λ ())
    , refl
    , refl
    , (λ where
         {m = 𝟘ᵐ} _ → refl
         {m = 𝟙ᵐ}   → ⊥-elim ∘→ (_$ refl))
    , (λ where
         {m = 𝟘ᵐ} _ → refl
         {m = 𝟙ᵐ}   → ⊥-elim ∘→ (_$ refl))
    , (λ ())
    , (_$ refl) ∘→ proj₂
    , (_ , (λ ()))
    , ( (λ ((_ , hyp₁) , hyp₂) → Lift.lower hyp₂ , hyp₁)
      , (λ (hyp₁ , hyp₂) → (_ , hyp₂) , lift hyp₁)
      )
    , (λ ())
    , (id⇔ ×-cong-⇔ ≢𝕤⇔≡𝕨)
    , (id⇔ ×-cong-⇔ (≢𝕤⇔≡𝕨 ×-cong-⇔ id⇔)) ∘⇔ sym⇔ Σ-assoc-⇔
    , lift (λ ())
    , (λ { (lift ()) })
    , Level-is-small⇔ .proj₂ refl
    , _
    , (λ ())
    , (λ ())
    , ((λ _ ()) , _)
    where
    open Extended-modality Affine-types

-- A linearity modality.

Linearity : Extended-modality lzero
Linearity = λ where
    .M           → L.Linearity
    .𝕄           → L.linearityModality
    .MV          → 𝟘ᵐ-Allowed _
    .C           → C″
    .FA          → FA′
    .DA          → Assumptions-C′ L._≟_
    .NR          → Nr ⦃ L.zero-one-many-has-nr ⦄
    .NO-NR-GLB   → L.zero-one-many-supports-glb-for-natrec
    .HAS-ω       → L.zero-one-many-has-omega
    .NR₀ {p}     → L.nr-linearity-like-for-𝟘 {p = p}
    .NR₁ {p} {z} → L.nr-linearity-like-for-𝟙 {p = p} {z = z}
    .SUB         → L.supports-subtraction
  where
  open Extended-modality

  C″ = C′ L.zero-one-many-has-nr

  opaque

    FA′ : Full-reduction-assumptions _ C″
    FA′ =
      L.full-reduction-assumptions
        ( (_$ refl) ∘→ proj₂
        , (λ _ ())
        , (λ _ (_ , hyp) → case Lift.lower hyp refl of λ ())
        , (λ _ (_ , hyp) → case Lift.lower hyp refl of λ ())
        )

opaque

  -- The properties listed above all hold for Linearity.

  All-properties-hold-for-Linearity :
    All-properties-hold-for Linearity
  All-properties-hold-for-Linearity =
      (λ where
         {m = 𝟘ᵐ} → (λ _ → inj₁ (λ ())) , (λ _ → _ , (λ ()))
         {m = 𝟙ᵐ} →
             (λ (_ , r≢𝟘) → inj₂ (inj₁ (r≢𝟘 refl (λ ()))))
           , (λ where
                (inj₁ 𝟙ᵐ≢𝟙ᵐ)      → ⊥-elim $ 𝟙ᵐ≢𝟙ᵐ refl
                (inj₂ (inj₁ r≢𝟘)) → _ , (λ _ _ → r≢𝟘)
                (inj₂ (inj₂ ()))))
    , _
    , _
    , (λ ())
    , (λ ())
    , refl
    , refl
    , (λ where
         {m = 𝟘ᵐ} _ → refl
         {m = 𝟙ᵐ}   → ⊥-elim ∘→ (_$ refl))
    , (λ where
         {m = 𝟘ᵐ} _ → refl
         {m = 𝟙ᵐ}   → ⊥-elim ∘→ (_$ refl))
    , (λ ())
    , (_$ refl) ∘→ proj₂
    , (_ , (λ ()))
    , ( (λ ((_ , hyp₁) , hyp₂) → Lift.lower hyp₂ , hyp₁)
      , (λ (hyp₁ , hyp₂) → (_ , hyp₂) , lift hyp₁)
      )
    , (λ ())
    , (id⇔ ×-cong-⇔ ≢𝕤⇔≡𝕨)
    , (id⇔ ×-cong-⇔ (≢𝕤⇔≡𝕨 ×-cong-⇔ id⇔)) ∘⇔ sym⇔ Σ-assoc-⇔
    , lift (λ ())
    , (λ { (lift ()) })
    , Level-is-small⇔ .proj₂ refl
    , _
    , (λ ())
    , (λ ())
    , ((λ _ ()) , _)
    where
    open Extended-modality Linearity

-- A linear or affine types modality.

Linear-or-affine-types : Extended-modality lzero
Linear-or-affine-types = λ where
    .M           → LA.Linear-or-affine
    .𝕄           → LA.linear-or-affine
    .MV          → 𝟘ᵐ-Allowed _
    .C           → C″
    .FA          → FA′
    .DA          → Assumptions-C′ LA._≟_
    .NR          → Nr ⦃ LA.linear-or-affine-has-nr ⦄
    .NO-NR-GLB   → LA.linear-or-affine-supports-glb-for-natrec
    .HAS-ω       → LA.linear-or-affine-has-omega
    .NR₀ {p}     → LA.nr-linearity-like-for-𝟘 {p = p}
    .NR₁ {p} {s} → LA.nr-linearity-like-for-𝟙 {p = p} {s = s}
    .SUB {r}     → LA.supports-subtraction {r = r}
  where
  open Extended-modality

  C″ = C′ LA.linear-or-affine-has-nr

  opaque

    FA′ : Full-reduction-assumptions _ C″
    FA′ =
      LA.full-reduction-assumptions
        ( (_$ refl) ∘→ proj₂
        , (λ _ ())
        , (λ _ (_ , hyp) → case Lift.lower hyp refl of λ ())
        , (λ _ (_ , hyp) → case Lift.lower hyp refl of λ ())
        , (λ _ (_ , hyp) → case Lift.lower hyp refl of λ ())
        )

opaque

  -- The properties listed above all hold for Linear-or-affine-types.

  All-properties-hold-for-Linear-or-affine-types :
    All-properties-hold-for Linear-or-affine-types
  All-properties-hold-for-Linear-or-affine-types =
      (λ where
         {m = 𝟘ᵐ} → (λ _ → inj₁ (λ ())) , (λ _ → _ , (λ ()))
         {m = 𝟙ᵐ} →
             (λ (_ , r≢𝟘) → inj₂ (inj₁ (r≢𝟘 refl (λ ()))))
           , (λ where
                (inj₁ 𝟙ᵐ≢𝟙ᵐ)      → ⊥-elim $ 𝟙ᵐ≢𝟙ᵐ refl
                (inj₂ (inj₁ r≢𝟘)) → _ , (λ _ _ → r≢𝟘)
                (inj₂ (inj₂ ()))))
    , _
    , _
    , (λ ())
    , (λ ())
    , refl
    , refl
    , (λ where
         {m = 𝟘ᵐ} _ → refl
         {m = 𝟙ᵐ}   → ⊥-elim ∘→ (_$ refl))
    , (λ where
         {m = 𝟘ᵐ} _ → refl
         {m = 𝟙ᵐ}   → ⊥-elim ∘→ (_$ refl))
    , (λ ())
    , (_$ refl) ∘→ proj₂
    , (_ , (λ ()))
    , ( (λ ((_ , hyp₁) , hyp₂) → Lift.lower hyp₂ , hyp₁)
      , (λ (hyp₁ , hyp₂) → (_ , hyp₂) , lift hyp₁)
      )
    , (λ ())
    , (id⇔ ×-cong-⇔ ≢𝕤⇔≡𝕨)
    , (id⇔ ×-cong-⇔ (≢𝕤⇔≡𝕨 ×-cong-⇔ id⇔)) ∘⇔ sym⇔ Σ-assoc-⇔
    , lift (λ ())
    , (λ { (lift ()) })
    , Level-is-small⇔ .proj₂ refl
    , _
    , (λ ())
    , (λ ())
    , ((λ _ ()) , _)
    where
    open Extended-modality Linear-or-affine-types

------------------------------------------------------------------------
-- Some morphisms between the modalities above

-- A morphism from Trivial to Erasure.

Trivial⇨Erasure : Trivial ⇨ Erasure
Trivial⇨Erasure = λ where
    ._⇨_.transparent →
      false
    ._⇨_.tr →
      tr
    ._⇨_.tr-Σ →
      tr
    ._⇨_.is-order-embedding →
      is-order-embedding
    ._⇨_.is-Σ-order-embedding →
      is-Σ-order-embedding
    ._⇨_.is-Σ-order-embedding-C →
      is-Σ-order-embedding-C
  where
  module E₁ = Extended-modality Trivial
  module E₂ = Extended-modality Erasure

  tr = unit→erasure

  opaque

    is-order-embedding : Is-order-embedding E₁.𝕄 E₂.𝕄 tr
    is-order-embedding =
      unit⇨erasure

    is-Σ-order-embedding : Is-Σ-order-embedding E₁.𝕄 E₂.𝕄 tr tr
    is-Σ-order-embedding =
      Is-order-embedding→Is-Σ-order-embedding is-order-embedding

    is-Σ-order-embedding-C :
      Is-Σ-order-embedding-C false E₁.C E₂.C tr tr
    is-Σ-order-embedding-C =
      OE-only-some-erased-matches (⊥-elim ∘→ (_$ refl))
        (λ _ → inj₂ (λ _ ())) unit⇨erasure-omega-preserving $
      OE-no-quotients (λ _ → refl) $
      OE-no-strong-types (λ ()) $
      OE-second-ΠΣ-quantities-𝟘-or-ω (⊥-elim ∘→ (_$ refl))
        (λ _ _ → refl) (λ _ → (λ _ → refl) , (λ _ → refl))
        (λ _ → (λ _ → refl) , (λ _ → refl)) $
      OE-no-restrictions (λ _ → refl) (λ _ ()) (λ { _ with-ω → refl })
        ((λ _ → with-ω) , (λ _ → with-ω)) _ (λ _ → inj₂ refl)
        (Nr ⦃ U.unit-has-nr ⦄ ⦃ EM.erasure-has-nr ⦄)
        (λ ⦃ has-nr₁ ⦄ ⦃ has-nr₂ ⦄ →
          case Nr-available-propositional _ has-nr₁
                 (Nr ⦃ U.unit-has-nr ⦄) of λ {
            refl →
          case Nr-available-propositional _ has-nr₂
                 (Nr ⦃ EM.erasure-has-nr ⦄) of λ {
            refl →
          unit⇒erasure-nr-preserving , unit⇒erasure-nr-reflecting }})
        (unit⇒erasure-no-nr-preserving , unit⇒erasure-no-nr-reflecting)
        (unit⇒erasure-no-nr-glb-preserving ,
         unit⇒erasure-no-nr-glb-reflecting)

-- A morphism from Erasure to Affine-types.

Erasure⇨Affine-types : Erasure ⇨ Affine-types
Erasure⇨Affine-types = λ where
    ._⇨_.transparent →
      false
    ._⇨_.tr →
      tr
    ._⇨_.tr-Σ →
      tr
    ._⇨_.is-order-embedding →
      is-order-embedding
    ._⇨_.is-Σ-order-embedding →
      is-Σ-order-embedding
    ._⇨_.is-Σ-order-embedding-C →
      is-Σ-order-embedding-C
  where
  module E₁ = Extended-modality Erasure
  module E₂ = Extended-modality Affine-types

  tr = erasure→zero-one-many

  opaque

    is-order-embedding : Is-order-embedding E₁.𝕄 E₂.𝕄 tr
    is-order-embedding =
      erasure⇨zero-one-many

    is-Σ-order-embedding : Is-Σ-order-embedding E₁.𝕄 E₂.𝕄 tr tr
    is-Σ-order-embedding =
      Is-order-embedding→Is-Σ-order-embedding is-order-embedding

    is-Σ-order-embedding-C :
      Is-Σ-order-embedding-C false E₁.C E₂.C tr tr
    is-Σ-order-embedding-C =
      OE-only-some-erased-matches (λ _ → (λ ()) , (λ { refl → refl }))
        (λ _ →
           inj₁ ( (λ ())
                , (λ where
                     E.𝟘 refl → refl
                     E.ω ())
                ))
        erasure⇨zero-one-many-omega-preserving $
      OE-no-quotients (λ ()) $
      OE-no-strong-types (λ ()) $
      OE-second-ΠΣ-quantities-𝟘-or-ω (λ _ → refl)
        (λ where
           E.𝟘 _  → refl
           E.ω ())
        (λ where
           E.𝟘 → (λ ()) , (λ ())
           E.ω → (λ _ → refl) , (λ _ → refl))
        (λ where
           E.𝟘 → (λ ()) , (λ ())
           E.ω → (λ _ → refl) , (λ _ → refl)) $
      OE-no-restrictions (λ ()) (λ _ _ → refl)
        (λ { with-ω with-ω → refl }) ((λ _ → with-ω) , (λ _ → with-ω)) _
        (λ _ → inj₁ _)
        (Nr ⦃ EM.erasure-has-nr ⦄ ⦃ A.zero-one-many-has-nr ⦄)
        (λ ⦃ has-nr₁ ⦄ ⦃ has-nr₂ ⦄ →
          case Nr-available-propositional _ has-nr₁
                 (Nr ⦃ EM.erasure-has-nr ⦄) of λ {
            refl →
          case Nr-available-propositional _ has-nr₂
                 (Nr ⦃ A.zero-one-many-has-nr ⦄) of λ {
            refl →
          erasure⇒affine-nr-preserving ,
          erasure⇒affine-nr-reflecting }})
        (erasure⇒affine-no-nr-preserving _ ,
         erasure⇒affine-no-nr-reflecting _)
        (λ ⦃ no-nr ⦄ →
           erasure⇒affine-no-nr-glb-preserving ,
           ⊥-elim (¬[Nr∧No-nr-glb] _ Nr no-nr))

-- A morphism from Erasure to Linearity.

Erasure⇨Linearity : Erasure ⇨ Linearity
Erasure⇨Linearity = λ where
    ._⇨_.transparent →
      false
    ._⇨_.tr →
      tr
    ._⇨_.tr-Σ →
      tr
    ._⇨_.is-order-embedding →
      is-order-embedding
    ._⇨_.is-Σ-order-embedding →
      is-Σ-order-embedding
    ._⇨_.is-Σ-order-embedding-C →
      is-Σ-order-embedding-C
  where
  module E₁ = Extended-modality Erasure
  module E₂ = Extended-modality Linearity

  tr = erasure→zero-one-many

  opaque

    is-order-embedding : Is-order-embedding E₁.𝕄 E₂.𝕄 tr
    is-order-embedding =
      erasure⇨zero-one-many

    is-Σ-order-embedding : Is-Σ-order-embedding E₁.𝕄 E₂.𝕄 tr tr
    is-Σ-order-embedding =
      Is-order-embedding→Is-Σ-order-embedding is-order-embedding

    is-Σ-order-embedding-C :
      Is-Σ-order-embedding-C false E₁.C E₂.C tr tr
    is-Σ-order-embedding-C =
      OE-only-some-erased-matches (λ _ → (λ ()) , (λ { refl → refl }))
        (λ _ →
           inj₁ ( (λ ())
                , (λ where
                     E.𝟘 refl → refl
                     E.ω ())
                ))
        erasure⇨zero-one-many-omega-preserving $
      OE-no-quotients (λ ()) $
      OE-no-strong-types (λ ()) $
      OE-second-ΠΣ-quantities-𝟘-or-ω (λ _ → refl)
        (λ where
           E.𝟘 _  → refl
           E.ω ())
        (λ where
           E.𝟘 → (λ ()) , (λ ())
           E.ω → (λ _ → refl) , (λ _ → refl))
        (λ where
           E.𝟘 → (λ ()) , (λ ())
           E.ω → (λ _ → refl) , (λ _ → refl)) $
      OE-no-restrictions (λ ()) (λ _ _ → refl)
        (λ { with-ω with-ω → refl }) ((λ _ → with-ω) , (λ _ → with-ω)) _
        (λ _ → inj₁ _)
        (Nr ⦃ EM.erasure-has-nr ⦄ ⦃ L.zero-one-many-has-nr ⦄)
        (λ ⦃ has-nr₁ ⦄ ⦃ has-nr₂ ⦄ →
          case Nr-available-propositional _ has-nr₁
                 (Nr ⦃ EM.erasure-has-nr ⦄) of λ {
            refl →
          case Nr-available-propositional _ has-nr₂
                 (Nr ⦃ L.zero-one-many-has-nr ⦄) of λ {
            refl →
          erasure⇒linearity-nr-preserving ,
          erasure⇒linearity-nr-reflecting }})
        (erasure⇒linearity-no-nr-preserving _ ,
         erasure⇒linearity-no-nr-reflecting _)
        (λ ⦃ no-nr ⦄ →
           erasure⇒linearity-no-nr-glb-preserving ,
           ⊥-elim (¬[Nr∧No-nr-glb] _ Nr no-nr))

-- A morphism from Affine-types to Linear-or-affine-types.

Affine-types⇨Linear-or-affine-types :
  Affine-types ⇨ Linear-or-affine-types
Affine-types⇨Linear-or-affine-types = λ where
    ._⇨_.transparent →
      false
    ._⇨_.tr →
      tr
    ._⇨_.tr-Σ →
      tr
    ._⇨_.is-order-embedding →
      is-order-embedding
    ._⇨_.is-Σ-order-embedding →
      is-Σ-order-embedding
    ._⇨_.is-Σ-order-embedding-C →
      is-Σ-order-embedding-C
  where
  module E₁ = Extended-modality Affine-types
  module E₂ = Extended-modality Linear-or-affine-types

  tr = affine→linear-or-affine

  opaque

    is-order-embedding : Is-order-embedding E₁.𝕄 E₂.𝕄 tr
    is-order-embedding =
      affine⇨linear-or-affine

    is-Σ-order-embedding : Is-Σ-order-embedding E₁.𝕄 E₂.𝕄 tr tr
    is-Σ-order-embedding =
      Is-order-embedding→Is-Σ-order-embedding is-order-embedding

    is-Σ-order-embedding-C :
      Is-Σ-order-embedding-C false E₁.C E₂.C tr tr
    is-Σ-order-embedding-C =
      OE-only-some-erased-matches (λ _ → (λ ()) , (λ { refl → refl }))
        (λ _ →
           inj₁ ( (λ ())
                , (λ where
                     A.𝟘 refl → refl
                     A.𝟙 ()
                     A.ω ())
                ))
        affine⇨linear-or-affine-omega-preserving $
      OE-no-quotients (λ ()) $
      OE-no-strong-types (λ ()) $
      OE-second-ΠΣ-quantities-𝟘-or-ω (λ _ → refl)
        (λ where
           A.𝟘 _  → refl
           A.𝟙 ()
           A.ω ())
        (λ where
           A.𝟘 → (λ ()) , (λ ())
           A.𝟙 → (λ ()) , (λ ())
           A.ω → (λ _ → refl) , (λ _ → refl))
        (λ where
           A.𝟘 → (λ ()) , (λ ())
           A.𝟙 → (λ ()) , (λ ())
           A.ω → (λ _ → refl) , (λ _ → refl)) $
      OE-no-restrictions (λ ()) (λ _ _ → refl)
        (λ { with-ω with-ω → refl }) ((λ _ → with-ω) , (λ _ → with-ω)) _
        (λ _ → inj₁ _)
        (Nr ⦃ A.zero-one-many-has-nr ⦄ ⦃ LA.linear-or-affine-has-nr ⦄)
        (λ ⦃ has-nr₁ ⦄ ⦃ has-nr₂ ⦄ →
          case Nr-available-propositional _ has-nr₁
                 (Nr ⦃ A.zero-one-many-has-nr ⦄) of λ {
            refl →
          case Nr-available-propositional _ has-nr₂
                 (Nr ⦃ LA.linear-or-affine-has-nr ⦄) of λ {
            refl →
          affine⇨linear-or-affine-nr-preserving ,
          affine⇨linear-or-affine-nr-reflecting }})
        (affine⇨linear-or-affine-no-nr-preserving _ ,
         affine⇨linear-or-affine-no-nr-reflecting _)
        (λ ⦃ no-nr ⦄ →
           affine⇨linear-or-affine-no-nr-glb-preserving ,
           ⊥-elim
             (¬[Nr∧No-nr-glb] _ (Nr ⦃ A.zero-one-many-has-nr ⦄) no-nr))

-- A morphism from Linearity to Linear-or-affine-types.

Linearity⇨Linear-or-affine-types :
  Linearity ⇨ Linear-or-affine-types
Linearity⇨Linear-or-affine-types = λ where
    ._⇨_.transparent →
      false
    ._⇨_.tr →
      tr
    ._⇨_.tr-Σ →
      tr
    ._⇨_.is-order-embedding →
      is-order-embedding
    ._⇨_.is-Σ-order-embedding →
      is-Σ-order-embedding
    ._⇨_.is-Σ-order-embedding-C →
      is-Σ-order-embedding-C
  where
  module E₁ = Extended-modality Linearity
  module E₂ = Extended-modality Linear-or-affine-types

  tr = linearity→linear-or-affine

  opaque

    is-order-embedding : Is-order-embedding E₁.𝕄 E₂.𝕄 tr
    is-order-embedding =
      linearity⇨linear-or-affine

    is-Σ-order-embedding : Is-Σ-order-embedding E₁.𝕄 E₂.𝕄 tr tr
    is-Σ-order-embedding =
      Is-order-embedding→Is-Σ-order-embedding is-order-embedding

    is-Σ-order-embedding-C :
      Is-Σ-order-embedding-C false E₁.C E₂.C tr tr
    is-Σ-order-embedding-C =
      OE-only-some-erased-matches (λ _ → (λ ()) , (λ { refl → refl }))
        (λ _ →
           inj₁ ( (λ ())
                , (λ where
                     L.𝟘 refl → refl
                     L.𝟙 ()
                     L.ω ())
                ))
        linearity⇨linear-or-affine-omega-preserving $
      OE-no-quotients (λ ()) $
      OE-no-strong-types (λ ()) $
      OE-second-ΠΣ-quantities-𝟘-or-ω (λ _ → refl)
        (λ where
           L.𝟘 _  → refl
           L.𝟙 ()
           L.ω ())
        (λ where
           L.𝟘 → (λ ()) , (λ ())
           L.𝟙 → (λ ()) , (λ ())
           L.ω → (λ _ → refl) , (λ _ → refl))
        (λ where
           L.𝟘 → (λ ()) , (λ ())
           L.𝟙 → (λ ()) , (λ ())
           L.ω → (λ _ → refl) , (λ _ → refl)) $
      OE-no-restrictions (λ ()) (λ _ _ → refl)
        (λ { with-ω with-ω → refl }) ((λ _ → with-ω) , (λ _ → with-ω)) _
        (λ _ → inj₁ _)
        (Nr ⦃ L.zero-one-many-has-nr ⦄ ⦃ LA.linear-or-affine-has-nr ⦄)
        (λ ⦃ has-nr₁ ⦄ ⦃ has-nr₂ ⦄ →
          case Nr-available-propositional _ has-nr₁
                 (Nr ⦃ L.zero-one-many-has-nr ⦄) of λ {
            refl →
          case Nr-available-propositional _ has-nr₂
                 (Nr ⦃ LA.linear-or-affine-has-nr ⦄) of λ {
            refl →
          linearity⇨linear-or-affine-nr-preserving ,
          linearity⇨linear-or-affine-nr-reflecting }})
        (linearity⇨linear-or-affine-no-nr-preserving _ ,
         linearity⇨linear-or-affine-no-nr-reflecting _)
        (λ ⦃ no-nr ⦄ →
           linearity⇨linear-or-affine-no-nr-glb-preserving ,
           ⊥-elim
             (¬[Nr∧No-nr-glb] _ (Nr ⦃ L.zero-one-many-has-nr ⦄) no-nr))
