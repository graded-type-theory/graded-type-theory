------------------------------------------------------------------------
-- Some examples of extended modalities, along with some morphisms
-- between them
------------------------------------------------------------------------

-- The formalisation contains a number of parameters. These examples
-- show that it is possible to instantiate all of the parameters at
-- the same time.

module Graded.Modality.Extended.K-allowed where

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum
open import Tools.Unit

import Definition.Typechecking.Decidable.Assumptions as TD
open import Definition.Typed.Restrictions
open import Definition.Untyped.NotParametrised

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
open import Graded.Modality.Morphism.Examples
open import Graded.Modality.Morphism.Type-restrictions
open import Graded.Modality.Morphism.Type-restrictions.Examples
open import Graded.Modality.Morphism.Usage-restrictions
open import Graded.Modality.Morphism.Usage-restrictions.Examples
open import Graded.Mode.Instances.Zero-one.Variant
open import Graded.Mode.Instances.Zero-one
open import Graded.Restrictions.Zero-one
import Graded.Usage.Decidable.Assumptions as UD
open import Graded.Usage.Erased-matches
open import Graded.Usage.Restrictions
open import Graded.Usage.Restrictions.Natrec

private variable
  a : Level

------------------------------------------------------------------------
-- Extended modalities

-- The following extended modalities all satisfy the following
-- properties:
--
-- * There are no restrictions on prodrec, unitrec or emptyrec.
-- * Strong unit types are not allowed to be used as sinks.
-- * Id-erased is not inhabited.
-- * All erased matches are allowed for J and K.
-- * Eta-equality is not allowed for weak types.
-- * Strong unit types are not allowed, but weak unit types are
--   allowed.
-- * There are no restrictions on Π-types or weak Σ-types.
-- * For strong Σ-types the "first grades" must be 𝟙, but there are no
--   other restrictions.
-- * The K rule is allowed.
-- * []-cong is not allowed for 𝕤.
-- * []-cong is allowed for 𝕨 exactly when the modality is non-trivial.
-- * Opaque definitions are allowed.
-- * Equality reflection is not allowed.
-- * 𝟘ᵐ is allowed exactly when the modality is non-trivial.

All-properties-hold-for : Extended-modality a → Set a
All-properties-hold-for M =
  (∀ {m r p q} → Prodrec-allowed m r p q) ×
  (∀ {m p q} → Unitrec-allowed m p q) ×
  (∀ {m p} → Emptyrec-allowed m p) ×
  ¬ Starˢ-sink ×
  ¬ Id-erased ×
  (∀ {m} → erased-matches-for-J m ≡ all) ×
  (∀ {m} → erased-matches-for-K m ≡ all) ×
  ¬ Unitʷ-η ×
  ¬ Unit-allowed 𝕤 ×
  Unit-allowed 𝕨 ×
  (∀ {b p q} → ΠΣ-allowed b p q ⇔ (b ≡ BMΣ 𝕤 → p ≡ 𝟙)) ×
  K-allowed ×
  ¬ []-cong-allowed 𝕤 ×
  ([]-cong-allowed 𝕨 ⇔ (¬ Trivial)) ×
  Opacity-allowed ×
  ¬ Equality-reflection ×
  (T 𝟘ᵐ-allowed ⇔ (¬ Trivial))
  where
  open Extended-modality M
  open Mode-variant MV

private

  -- Functions used to construct the modalities below.

  TR′ :
    {M : Set} {𝕄 : Modality M} →
    Mode-variant 𝕄 →
    Type-restrictions 𝕄
  TR′ v =
    strong-types-restricted _ v $
    no-type-restrictions _ v true false

  opaque

    Assumptions-TR′ :
      {M : Set} {𝕄 : Modality M}
      {v : Mode-variant 𝕄} →
      Decidable (_≡_ {A = M}) →
      TD.Assumptions (TR′ {𝕄 = 𝕄} v)
    Assumptions-TR′ {v} =
      Assumptions-strong-types-restricted _ _ ∘→
      Assumptions-no-type-restrictions _ v

  UR′ :
    {M : Set} {𝕄 : Modality M}
    {v : Mode-variant 𝕄} →
    Has-nr M (Modality.semiring-with-meet 𝕄) →
    Usage-restrictions 𝕄 (Zero-one-isMode v)
  UR′ has-nr = no-usage-restrictions _ _ (Nr ⦃ has-nr ⦄) false false

  opaque

    Assumptions-UR′ :
      {M : Set} {𝕄 : Modality M}
      {v : Mode-variant 𝕄} →
      {has-nr : Has-nr _ (Modality.semiring-with-meet 𝕄)} →
      Decidable (_≡_ {A = M}) →
      UD.Assumptions (UR′ {𝕄 = 𝕄} {v = v} has-nr)
    Assumptions-UR′ {has-nr} =
      Assumptions-no-usage-restrictions _ _ ⦃ Nr ⦃ Nr ⦃ has-nr ⦄ ⦄ ⦄

-- A trivial modality.

Trivial : Extended-modality lzero
Trivial = λ where
    .M   → ⊤
    .𝕄   → U.UnitModality
    .MV  → 𝟘ᵐ-Not-Allowed _
    .TR  → TR′ (𝟘ᵐ-Not-Allowed _)
    .UR  → UR′ U.unit-has-nr
    .FA  → U.full-reduction-assumptions
    .TA  → Assumptions-TR′ U._≟_
    .UA  → Assumptions-UR′ U._≟_
    .NR  → Nr ⦃ U.unit-has-nr ⦄
    .NO-NR-GLB → U.unit-supports-glb-for-nr
    .NR₀ → U.nr-linearity-like-for-𝟘
    .NR₁ → U.nr-linearity-like-for-𝟙
    .SUB → U.unit-supports-subtraction
  where
  open Extended-modality

opaque

  -- The properties listed above all hold for Trivial.

  All-properties-hold-for-Trivial : All-properties-hold-for Trivial
  All-properties-hold-for-Trivial =
      _
    , _
    , _
    , (λ ())
    , (λ ())
    , refl
    , refl
    , (λ ())
    , (_$ refl) ∘→ proj₂
    , (_ , (λ ()))
    , (proj₂ , (_ ,_))
    , _
    , (_$ refl) ∘→ proj₂
    , (proj₁ , (λ hyp → hyp , (λ ())))
    , lift (λ ())
    , (λ { (lift ()) })
    , ((λ ()) , (_$ refl))

-- An erasure modality.

Erasure : Extended-modality lzero
Erasure = λ where
    .M       → E.Erasure
    .𝕄       → EM.ErasureModality
    .MV      → 𝟘ᵐ-Allowed _
    .TR      → TR′ (𝟘ᵐ-Allowed _)
    .UR      → UR′ EM.erasure-has-nr
    .FA      → EP.full-reduction-assumptions _
    .TA      → Assumptions-TR′ E._≟_
    .UA      → Assumptions-UR′ E._≟_
    .NR      → Nr ⦃ EM.erasure-has-nr ⦄
    .NO-NR-GLB → EP.Erasure-supports-factoring-nr-rule
    .NR₀ {z} → EP.nr-linearity-like-for-𝟘 {z = z}
    .NR₁ {z} → EP.nr-linearity-like-for-𝟙 {z = z}
    .SUB     → EP.supports-subtraction
  where
  open Extended-modality

opaque

  -- The properties listed above all hold for Erasure.

  All-properties-hold-for-Erasure : All-properties-hold-for Erasure
  All-properties-hold-for-Erasure =
      _
    , _
    , _
    , (λ ())
    , (λ ())
    , refl
    , refl
    , (λ ())
    , (_$ refl) ∘→ proj₂
    , (_ , (λ ()))
    , (proj₂ , (_ ,_))
    , _
    , (_$ refl) ∘→ proj₂
    , (proj₁ , (λ hyp → hyp , (λ ())))
    , lift (λ ())
    , (λ { (lift ()) })
    , ((λ _ ()) , _)

-- An affine types modality.

Affine-types : Extended-modality lzero
Affine-types = λ where
    .M           → A.Affine
    .𝕄           → A.affineModality
    .MV          → 𝟘ᵐ-Allowed _
    .TR          → TR″
    .UR          → UR″
    .FA          → FA′
    .TA          → Assumptions-TR′ A._≟_
    .UA          → Assumptions-UR′ A._≟_
    .NR          → Nr ⦃ A.zero-one-many-has-nr ⦄
    .NO-NR-GLB   → A.zero-one-many-supports-glb-for-natrec
    .NR₀ {p}     → A.nr-linearity-like-for-𝟘 {p = p}
    .NR₁ {p} {z} → A.nr-linearity-like-for-𝟙 {p = p} {z = z}
    .SUB         → A.supports-subtraction
  where
  open Extended-modality

  TR″ = TR′ (𝟘ᵐ-Allowed _)
  UR″ = UR′ A.zero-one-many-has-nr

  opaque

    FA′ : Full-reduction-assumptions _ TR″ UR″
    FA′ =
      A.full-reduction-assumptions
        (_ , (λ _ (_ , hyp) → case hyp refl of λ ()))

opaque

  -- The properties listed above all hold for Affine-types.

  All-properties-hold-for-Affine-types :
    All-properties-hold-for Affine-types
  All-properties-hold-for-Affine-types =
      _
    , _
    , _
    , (λ ())
    , (λ ())
    , refl
    , refl
    , (λ ())
    , (_$ refl) ∘→ proj₂
    , (_ , (λ ()))
    , (proj₂ , (_ ,_))
    , _
    , (_$ refl) ∘→ proj₂
    , (proj₁ , (λ hyp → hyp , (λ ())))
    , lift (λ ())
    , (λ { (lift ()) })
    , ((λ _ ()) , _)

-- A linearity modality.

Linearity : Extended-modality lzero
Linearity = λ where
    .M           → L.Linearity
    .𝕄           → L.linearityModality
    .MV          → 𝟘ᵐ-Allowed _
    .TR          → TR″
    .UR          → UR″
    .FA          → FA′
    .TA          → Assumptions-TR′ L._≟_
    .UA          → Assumptions-UR′ L._≟_
    .NR          → Nr ⦃ L.zero-one-many-has-nr ⦄
    .NO-NR-GLB   → L.zero-one-many-supports-glb-for-natrec
    .NR₀ {p}     → L.nr-linearity-like-for-𝟘 {p = p}
    .NR₁ {p} {z} → L.nr-linearity-like-for-𝟙 {p = p} {z = z}
    .SUB         → L.supports-subtraction
  where
  open Extended-modality

  UR″ = UR′ L.zero-one-many-has-nr
  TR″ = TR′ (𝟘ᵐ-Allowed _)

  opaque

    FA′ : Full-reduction-assumptions _ TR″ UR″
    FA′ =
      L.full-reduction-assumptions
        ( (_$ refl) ∘→ proj₂
        , (λ _ ())
        , (λ _ (_ , hyp) → case hyp refl of λ ())
        , (λ _ (_ , hyp) → case hyp refl of λ ())
        )

opaque

  -- The properties listed above all hold for Linearity.

  All-properties-hold-for-Linearity :
    All-properties-hold-for Linearity
  All-properties-hold-for-Linearity =
      _
    , _
    , _
    , (λ ())
    , (λ ())
    , refl
    , refl
    , (λ ())
    , (_$ refl) ∘→ proj₂
    , (_ , (λ ()))
    , (proj₂ , (_ ,_))
    , _
    , (_$ refl) ∘→ proj₂
    , (proj₁ , (λ hyp → hyp , (λ ())))
    , lift (λ ())
    , (λ { (lift ()) })
    , ((λ _ ()) , _)

-- A linear or affine types modality.

Linear-or-affine-types : Extended-modality lzero
Linear-or-affine-types = λ where
    .M           → LA.Linear-or-affine
    .𝕄           → LA.linear-or-affine
    .MV          → 𝟘ᵐ-Allowed _
    .TR          → TR″
    .UR          → UR″
    .FA          → FA′
    .TA          → Assumptions-TR′ LA._≟_
    .UA          → Assumptions-UR′ LA._≟_
    .NR          → Nr ⦃ LA.linear-or-affine-has-nr ⦄
    .NO-NR-GLB   → LA.linear-or-affine-supports-glb-for-natrec
    .NR₀ {p}     → LA.nr-linearity-like-for-𝟘 {p = p}
    .NR₁ {p} {s} → LA.nr-linearity-like-for-𝟙 {p = p} {s = s}
    .SUB {r}     → LA.supports-subtraction {r = r}
  where
  open Extended-modality

  UR″ = UR′ LA.linear-or-affine-has-nr
  TR″ = TR′ (𝟘ᵐ-Allowed _)

  opaque

    FA′ : Full-reduction-assumptions _ TR″ UR″
    FA′ =
      LA.full-reduction-assumptions
        ( (_$ refl) ∘→ proj₂
        , (λ _ ())
        , (λ _ (_ , hyp) → case hyp refl of λ ())
        , (λ _ (_ , hyp) → case hyp refl of λ ())
        , (λ _ (_ , hyp) → case hyp refl of λ ())
        )

opaque

  -- The properties listed above all hold for Linear-or-affine-types.

  All-properties-hold-for-Linear-or-affine-types :
    All-properties-hold-for Linear-or-affine-types
  All-properties-hold-for-Linear-or-affine-types =
      _
    , _
    , _
    , (λ ())
    , (λ ())
    , refl
    , refl
    , (λ ())
    , (_$ refl) ∘→ proj₂
    , (_ , (λ ()))
    , (proj₂ , (_ ,_))
    , _
    , (_$ refl) ∘→ proj₂
    , (proj₁ , (λ hyp → hyp , (λ ())))
    , lift (λ ())
    , (λ { (lift ()) })
    , ((λ _ ()) , _)

------------------------------------------------------------------------
-- Some morphisms between the modalities above

-- A morphism from Trivial to Erasure.

Trivial⇨Erasure : Trivial ⇨ Erasure
Trivial⇨Erasure = λ where
    ._⇨_.tr →
      tr
    ._⇨_.tr-Σ →
      tr
    ._⇨_.is-order-embedding →
      is-order-embedding
    ._⇨_.is-Σ-order-embedding →
      is-Σ-order-embedding
    ._⇨_.are-preserving-type-restrictions →
      are-preserving-type-restrictions
    ._⇨_.are-reflecting-type-restrictions →
      are-reflecting-type-restrictions
    ._⇨_.are-preserving-usage-restrictions →
      are-preserving-usage-restrictions
    ._⇨_.are-reflecting-usage-restrictions →
      are-reflecting-usage-restrictions
  where
  module E₁ = Extended-modality Trivial
  module E₂ = Extended-modality Erasure

  tr = unit→erasure

  opaque
    unfolding

    is-order-embedding : Is-order-embedding E₁.𝕄 E₂.𝕄 tr
    is-order-embedding = unit⇨erasure

    is-Σ-order-embedding : Is-Σ-order-embedding E₁.𝕄 E₂.𝕄 tr tr
    is-Σ-order-embedding =
      Is-order-embedding→Is-Σ-order-embedding is-order-embedding

    are-preserving-type-restrictions :
      Are-preserving-type-restrictions E₁.TR E₂.TR tr tr
    are-preserving-type-restrictions =
      unit→erasure-preserves-strong-types-restricted $
      Are-preserving-type-restrictions-no-type-restrictions
        {𝐌₁ = Zero-one-isMode (𝟘ᵐ-Not-Allowed _)} {𝐌₂ = Zero-one-isMode (𝟘ᵐ-Allowed _)}
        (λ _ ())

    are-reflecting-type-restrictions :
      Are-reflecting-type-restrictions E₁.TR E₂.TR tr tr
    are-reflecting-type-restrictions =
      unit→erasure-reflects-strong-types-restricted $
      Are-reflecting-type-restrictions-no-type-restrictions
        {𝐌₁ = Zero-one-isMode (𝟘ᵐ-Not-Allowed _)} {𝐌₂ = Zero-one-isMode (𝟘ᵐ-Allowed _)}
        (λ _ → inj₁ refl)

    are-preserving-usage-restrictions :
      Are-preserving-usage-restrictions E₁.UR E₂.UR tr tr
    are-preserving-usage-restrictions =
      Are-preserving-usage-restrictions-no-usage-restrictions
        _ (Nr ⦃ U.unit-has-nr ⦄ ⦃ EM.erasure-has-nr ⦄)
        (λ ⦃ has-nr₁ ⦄ ⦃ has-nr₂ ⦄ →
          case Nr-available-propositional _ has-nr₁ (Nr ⦃ U.unit-has-nr ⦄) of λ {
            refl →
          case Nr-available-propositional _ has-nr₂ (Nr ⦃ EM.erasure-has-nr ⦄) of λ {
            refl →
          unit⇒erasure-nr-preserving }})
        unit⇒erasure-no-nr-preserving
        unit⇒erasure-no-nr-glb-preserving

    are-reflecting-usage-restrictions :
      Are-reflecting-usage-restrictions E₁.UR E₂.UR tr tr
    are-reflecting-usage-restrictions =
      Are-reflecting-usage-restrictions-no-usage-restrictions
        _ (λ _ → inj₂ refl) (Nr ⦃ U.unit-has-nr ⦄ ⦃ EM.erasure-has-nr ⦄)
        (λ ⦃ has-nr₁ ⦄ ⦃ has-nr₂ ⦄ →
          case Nr-available-propositional _ has-nr₁ (Nr ⦃ U.unit-has-nr ⦄) of λ {
            refl →
          case Nr-available-propositional _ has-nr₂ (Nr ⦃ EM.erasure-has-nr ⦄) of λ {
            refl →
          unit⇒erasure-nr-reflecting }})
        unit⇒erasure-no-nr-reflecting
        unit⇒erasure-no-nr-glb-reflecting

-- A morphism from Erasure to Affine-types.

Erasure⇨Affine-types : Erasure ⇨ Affine-types
Erasure⇨Affine-types = λ where
    ._⇨_.tr →
      tr
    ._⇨_.tr-Σ →
      tr-Σ
    ._⇨_.is-order-embedding →
      is-order-embedding
    ._⇨_.is-Σ-order-embedding →
      is-Σ-order-embedding
    ._⇨_.are-preserving-type-restrictions →
      are-preserving-type-restrictions
    ._⇨_.are-reflecting-type-restrictions →
      are-reflecting-type-restrictions
    ._⇨_.are-preserving-usage-restrictions →
      are-preserving-usage-restrictions
    ._⇨_.are-reflecting-usage-restrictions →
      are-reflecting-usage-restrictions
  where
  module E₁ = Extended-modality Erasure
  module E₂ = Extended-modality Affine-types

  tr   = erasure→zero-one-many
  tr-Σ = erasure→zero-one-many-Σ

  Nr≈Nr : _ ≈ⁿᵐ _
  Nr≈Nr = Nr ⦃ EM.erasure-has-nr ⦄ ⦃ A.zero-one-many-has-nr ⦄

  opaque

    is-order-embedding : Is-order-embedding E₁.𝕄 E₂.𝕄 tr
    is-order-embedding = erasure⇨zero-one-many

    is-Σ-order-embedding : Is-Σ-order-embedding E₁.𝕄 E₂.𝕄 tr tr-Σ
    is-Σ-order-embedding =
      erasure⇨zero-one-many-Σ

    are-preserving-type-restrictions :
      Are-preserving-type-restrictions E₁.TR E₂.TR tr tr-Σ
    are-preserving-type-restrictions =
      erasure→zero-one-many-Σ-preserves-strong-types-restricted $
      Are-preserving-type-restrictions-no-type-restrictions
      {𝐌₁ = Zero-one-isMode (𝟘ᵐ-Allowed _)} {𝐌₂ = Zero-one-isMode (𝟘ᵐ-Allowed _)}
      (λ _ ())

    are-reflecting-type-restrictions :
      Are-reflecting-type-restrictions E₁.TR E₂.TR tr tr-Σ
    are-reflecting-type-restrictions =
      erasure→zero-one-many-Σ-reflects-strong-types-restricted $
      Are-reflecting-type-restrictions-no-type-restrictions
        {𝐌₁ = Zero-one-isMode (𝟘ᵐ-Allowed _)} {𝐌₂ = Zero-one-isMode (𝟘ᵐ-Allowed _)}
        (λ _ → inj₂ (λ ()))

    are-preserving-usage-restrictions :
      Are-preserving-usage-restrictions E₁.UR E₂.UR tr tr-Σ
    are-preserving-usage-restrictions =
      Are-preserving-usage-restrictions-no-usage-restrictions _ Nr≈Nr
        (λ ⦃ has-nr₁ ⦄ ⦃ has-nr₂ ⦄ →
          case Nr-available-propositional _ has-nr₁ (Nr ⦃ EM.erasure-has-nr ⦄) of λ {
            refl →
          case Nr-available-propositional _ has-nr₂ (Nr ⦃ A.zero-one-many-has-nr ⦄) of λ {
            refl →
          erasure⇒affine-nr-preserving }})
        (erasure⇒affine-no-nr-preserving _)
        erasure⇒affine-no-nr-glb-preserving

    are-reflecting-usage-restrictions :
      Are-reflecting-usage-restrictions E₁.UR E₂.UR tr tr-Σ
    are-reflecting-usage-restrictions =
      Are-reflecting-usage-restrictions-no-usage-restrictions
        _ (λ _ → inj₁ _) Nr≈Nr
        (λ ⦃ has-nr₁ ⦄ ⦃ has-nr₂ ⦄ →
          case Nr-available-propositional _ has-nr₁ (Nr ⦃ EM.erasure-has-nr ⦄) of λ {
            refl →
          case Nr-available-propositional _ has-nr₂ (Nr ⦃ A.zero-one-many-has-nr ⦄) of λ {
            refl →
          erasure⇒affine-nr-reflecting }})
        (erasure⇒affine-no-nr-reflecting _)
        (λ ⦃ no-nr ⦄ → ⊥-elim (¬[Nr∧No-nr-glb] _ Nr no-nr))

-- A morphism from Erasure to Linearity.

Erasure⇨Linearity : Erasure ⇨ Linearity
Erasure⇨Linearity = λ where
    ._⇨_.tr →
      tr
    ._⇨_.tr-Σ →
      tr-Σ
    ._⇨_.is-order-embedding →
      is-order-embedding
    ._⇨_.is-Σ-order-embedding →
      is-Σ-order-embedding
    ._⇨_.are-preserving-type-restrictions →
      are-preserving-type-restrictions
    ._⇨_.are-reflecting-type-restrictions →
      are-reflecting-type-restrictions
    ._⇨_.are-preserving-usage-restrictions →
      are-preserving-usage-restrictions
    ._⇨_.are-reflecting-usage-restrictions →
      are-reflecting-usage-restrictions
  where
  module E₁ = Extended-modality Erasure
  module E₂ = Extended-modality Linearity

  tr   = erasure→zero-one-many
  tr-Σ = erasure→zero-one-many-Σ

  Nr≈Nr : _ ≈ⁿᵐ _
  Nr≈Nr = Nr ⦃ EM.erasure-has-nr ⦄ ⦃ L.zero-one-many-has-nr ⦄

  opaque

    is-order-embedding : Is-order-embedding E₁.𝕄 E₂.𝕄 tr
    is-order-embedding =
      erasure⇨zero-one-many

    is-Σ-order-embedding : Is-Σ-order-embedding E₁.𝕄 E₂.𝕄 tr tr-Σ
    is-Σ-order-embedding =
      erasure⇨zero-one-many-Σ

    are-preserving-type-restrictions :
      Are-preserving-type-restrictions E₁.TR E₂.TR tr tr-Σ
    are-preserving-type-restrictions =
      erasure→zero-one-many-Σ-preserves-strong-types-restricted $
      Are-preserving-type-restrictions-no-type-restrictions
      {𝐌₁ = Zero-one-isMode (𝟘ᵐ-Allowed _)} {𝐌₂ = Zero-one-isMode (𝟘ᵐ-Allowed _)}
      (λ _ ())

    are-reflecting-type-restrictions :
      Are-reflecting-type-restrictions E₁.TR E₂.TR tr tr-Σ
    are-reflecting-type-restrictions =
      erasure→zero-one-many-Σ-reflects-strong-types-restricted $
      Are-reflecting-type-restrictions-no-type-restrictions
        {𝐌₁ = Zero-one-isMode (𝟘ᵐ-Allowed _)} {𝐌₂ = Zero-one-isMode (𝟘ᵐ-Allowed _)}
        (λ _ → inj₂ (λ ()))

    are-preserving-usage-restrictions :
      Are-preserving-usage-restrictions E₁.UR E₂.UR tr tr-Σ
    are-preserving-usage-restrictions =
      Are-preserving-usage-restrictions-no-usage-restrictions _ Nr≈Nr
        (λ ⦃ has-nr₁ ⦄ ⦃ has-nr₂ ⦄ →
          case Nr-available-propositional _ has-nr₁ (Nr ⦃ EM.erasure-has-nr ⦄) of λ {
            refl →
          case Nr-available-propositional _ has-nr₂ (Nr ⦃ L.zero-one-many-has-nr ⦄) of λ {
            refl →
          erasure⇒linearity-nr-preserving }})
        (erasure⇒linearity-no-nr-preserving _)
        erasure⇒linearity-no-nr-glb-preserving

    are-reflecting-usage-restrictions :
      Are-reflecting-usage-restrictions E₁.UR E₂.UR tr tr-Σ
    are-reflecting-usage-restrictions =
      Are-reflecting-usage-restrictions-no-usage-restrictions
        _ (λ _ → inj₁ _) Nr≈Nr
        (λ ⦃ has-nr₁ ⦄ ⦃ has-nr₂ ⦄ →
          case Nr-available-propositional _ has-nr₁ (Nr ⦃ EM.erasure-has-nr ⦄) of λ {
            refl →
          case Nr-available-propositional _ has-nr₂ (Nr ⦃ L.zero-one-many-has-nr ⦄) of λ {
            refl →
          erasure⇒linearity-nr-reflecting }})
        (erasure⇒linearity-no-nr-reflecting _)
        (λ ⦃ no-nr ⦄ → ⊥-elim (¬[Nr∧No-nr-glb] _ Nr no-nr))

-- A morphism from Affine-types to Linear-or-affine-types.

Affine-types⇨Linear-or-affine-types :
  Affine-types ⇨ Linear-or-affine-types
Affine-types⇨Linear-or-affine-types = λ where
    ._⇨_.tr →
      tr
    ._⇨_.tr-Σ →
      tr-Σ
    ._⇨_.is-order-embedding →
      is-order-embedding
    ._⇨_.is-Σ-order-embedding →
      is-Σ-order-embedding
    ._⇨_.are-preserving-type-restrictions →
      are-preserving-type-restrictions
    ._⇨_.are-reflecting-type-restrictions →
      are-reflecting-type-restrictions
    ._⇨_.are-preserving-usage-restrictions →
      are-preserving-usage-restrictions
    ._⇨_.are-reflecting-usage-restrictions →
      are-reflecting-usage-restrictions
  where
  module E₁ = Extended-modality Affine-types
  module E₂ = Extended-modality Linear-or-affine-types

  tr   = affine→linear-or-affine
  tr-Σ = affine→linear-or-affine-Σ

  Nr≈Nr : _ ≈ⁿᵐ _
  Nr≈Nr = Nr ⦃ A.zero-one-many-has-nr ⦄ ⦃ LA.linear-or-affine-has-nr ⦄

  opaque

    is-order-embedding : Is-order-embedding E₁.𝕄 E₂.𝕄 tr
    is-order-embedding =
      affine⇨linear-or-affine

    is-Σ-order-embedding : Is-Σ-order-embedding E₁.𝕄 E₂.𝕄 tr tr-Σ
    is-Σ-order-embedding =
      affine⇨linear-or-affine-Σ

    are-preserving-type-restrictions :
      Are-preserving-type-restrictions E₁.TR E₂.TR tr tr-Σ
    are-preserving-type-restrictions =
      affine→linear-or-affine-Σ-preserves-strong-types-restricted $
      Are-preserving-type-restrictions-no-type-restrictions
      {𝐌₁ = Zero-one-isMode (𝟘ᵐ-Allowed _)} {𝐌₂ = Zero-one-isMode (𝟘ᵐ-Allowed _)}
      (λ _ ())

    are-reflecting-type-restrictions :
      Are-reflecting-type-restrictions E₁.TR E₂.TR tr tr-Σ
    are-reflecting-type-restrictions =
      affine→linear-or-affine-Σ-reflects-strong-types-restricted $
      Are-reflecting-type-restrictions-no-type-restrictions
        {𝐌₁ = Zero-one-isMode (𝟘ᵐ-Allowed _)} {𝐌₂ = Zero-one-isMode (𝟘ᵐ-Allowed _)}
        (λ _ → inj₂ (λ ()))

    are-preserving-usage-restrictions :
      Are-preserving-usage-restrictions E₁.UR E₂.UR tr tr-Σ
    are-preserving-usage-restrictions =
      Are-preserving-usage-restrictions-no-usage-restrictions _ Nr≈Nr
        (λ ⦃ has-nr₁ ⦄ ⦃ has-nr₂ ⦄ →
          case Nr-available-propositional _ has-nr₁ (Nr ⦃ A.zero-one-many-has-nr ⦄) of λ {
            refl →
          case Nr-available-propositional _ has-nr₂ (Nr ⦃ LA.linear-or-affine-has-nr ⦄) of λ {
            refl →
          affine⇨linear-or-affine-nr-preserving }})
        (affine⇨linear-or-affine-no-nr-preserving _)
        affine⇨linear-or-affine-no-nr-glb-preserving

    are-reflecting-usage-restrictions :
      Are-reflecting-usage-restrictions E₁.UR E₂.UR tr tr-Σ
    are-reflecting-usage-restrictions =
      Are-reflecting-usage-restrictions-no-usage-restrictions
        _ (λ _ → inj₁ _) Nr≈Nr
        (λ ⦃ has-nr₁ ⦄ ⦃ has-nr₂ ⦄ →
          case Nr-available-propositional _ has-nr₁ (Nr ⦃ A.zero-one-many-has-nr ⦄) of λ {
            refl →
          case Nr-available-propositional _ has-nr₂ (Nr ⦃ LA.linear-or-affine-has-nr ⦄) of λ {
            refl →
          affine⇨linear-or-affine-nr-reflecting }})
        (affine⇨linear-or-affine-no-nr-reflecting _)
        (λ ⦃ no-nr ⦄ → ⊥-elim (¬[Nr∧No-nr-glb] _ (Nr ⦃ A.zero-one-many-has-nr ⦄) no-nr))

-- A morphism from Linearity to Linear-or-affine-types.

Linearity⇨Linear-or-affine-types :
  Linearity ⇨ Linear-or-affine-types
Linearity⇨Linear-or-affine-types = λ where
    ._⇨_.tr →
      tr
    ._⇨_.tr-Σ →
      tr
    ._⇨_.is-order-embedding →
      is-order-embedding
    ._⇨_.is-Σ-order-embedding →
      is-Σ-order-embedding
    ._⇨_.are-preserving-type-restrictions →
      are-preserving-type-restrictions
    ._⇨_.are-reflecting-type-restrictions →
      are-reflecting-type-restrictions
    ._⇨_.are-preserving-usage-restrictions →
      are-preserving-usage-restrictions
    ._⇨_.are-reflecting-usage-restrictions →
      are-reflecting-usage-restrictions
  where
  module E₁ = Extended-modality Linearity
  module E₂ = Extended-modality Linear-or-affine-types

  tr = linearity→linear-or-affine

  Nr≈Nr : _ ≈ⁿᵐ _
  Nr≈Nr = Nr ⦃ L.zero-one-many-has-nr ⦄ ⦃ LA.linear-or-affine-has-nr ⦄

  opaque

    is-order-embedding : Is-order-embedding E₁.𝕄 E₂.𝕄 tr
    is-order-embedding =
      linearity⇨linear-or-affine

    is-Σ-order-embedding : Is-Σ-order-embedding E₁.𝕄 E₂.𝕄 tr tr
    is-Σ-order-embedding =
      Is-order-embedding→Is-Σ-order-embedding is-order-embedding

    are-preserving-type-restrictions :
      Are-preserving-type-restrictions E₁.TR E₂.TR tr tr
    are-preserving-type-restrictions =
      linearity→linear-or-affine-preserves-strong-types-restricted $
      Are-preserving-type-restrictions-no-type-restrictions
      {𝐌₁ = Zero-one-isMode (𝟘ᵐ-Allowed _)} {𝐌₂ = Zero-one-isMode (𝟘ᵐ-Allowed _)}
      (λ _ ())

    are-reflecting-type-restrictions :
      Are-reflecting-type-restrictions E₁.TR E₂.TR tr tr
    are-reflecting-type-restrictions =
      linearity→linear-or-affine-reflects-strong-types-restricted $
      Are-reflecting-type-restrictions-no-type-restrictions
        {𝐌₁ = Zero-one-isMode (𝟘ᵐ-Allowed _)} {𝐌₂ = Zero-one-isMode (𝟘ᵐ-Allowed _)}
        (λ _ → inj₂ (λ ()))

    are-preserving-usage-restrictions :
      Are-preserving-usage-restrictions E₁.UR E₂.UR tr tr
    are-preserving-usage-restrictions =
      Are-preserving-usage-restrictions-no-usage-restrictions _ Nr≈Nr
        (λ ⦃ has-nr₁ ⦄ ⦃ has-nr₂ ⦄ →
          case Nr-available-propositional _ has-nr₁ (Nr ⦃ L.zero-one-many-has-nr ⦄) of λ {
            refl →
          case Nr-available-propositional _ has-nr₂ (Nr ⦃ LA.linear-or-affine-has-nr ⦄) of λ {
            refl →
          linearity⇨linear-or-affine-nr-preserving }})
        (linearity⇨linear-or-affine-no-nr-preserving _)
        linearity⇨linear-or-affine-no-nr-glb-preserving

    are-reflecting-usage-restrictions :
      Are-reflecting-usage-restrictions E₁.UR E₂.UR tr tr
    are-reflecting-usage-restrictions =
      Are-reflecting-usage-restrictions-no-usage-restrictions
        _ (λ _ → inj₁ _) Nr≈Nr
        (λ ⦃ has-nr₁ ⦄ ⦃ has-nr₂ ⦄ →
          case Nr-available-propositional _ has-nr₁ (Nr ⦃ L.zero-one-many-has-nr ⦄) of λ {
            refl →
          case Nr-available-propositional _ has-nr₂ (Nr ⦃ LA.linear-or-affine-has-nr ⦄) of λ {
            refl →
          linearity⇨linear-or-affine-nr-reflecting }})
        (linearity⇨linear-or-affine-no-nr-reflecting _)
        (λ ⦃ no-nr ⦄ → ⊥-elim (¬[Nr∧No-nr-glb] _ (Nr ⦃ L.zero-one-many-has-nr ⦄) no-nr))
