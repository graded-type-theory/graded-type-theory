------------------------------------------------------------------------
-- Some examples of extended modalities, along with some morphisms
-- between them
------------------------------------------------------------------------

-- The formalisation contains a number of parameters. These examples
-- show that it is possible to instantiate all of the parameters at
-- the same time.

{-# OPTIONS --hidden-argument-puns #-}

module Graded.Modality.Extended.K-allowed where

open import Tools.Bool
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
open import Graded.Modality.Dedicated-nr
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
open import Graded.Modality.Variant lzero
open import Graded.Restrictions
import Graded.Usage.Decidable.Assumptions as UD
open import Graded.Usage.Erased-matches
open import Graded.Usage.Restrictions

private variable
  a : Level

------------------------------------------------------------------------
-- Extended modalities

-- The following extended modalities all satisfy the following
-- properties:
--
-- * There are no restrictions on prodrec, unitrec or emptyrec.
-- * The strong unit type is not allowed to be used as a sink.
-- * Id-erased is not inhabited.
-- * All erased matches are allowed for J and K.
-- * Strong unit types are not allowed, but weak unit types are
--   allowed.
-- * There are no restrictions on Π-types or weak Σ-types.
-- * For strong Σ-types the "first grades" must be 𝟙, but there are no
--   other restrictions.
-- * The K rule is allowed.
-- * []-cong is not allowed for 𝕤.
-- * []-cong is allowed for 𝕨 exactly when the modality is non-trivial.
-- * 𝟘ᵐ is allowed exactly when the modality is non-trivial.
-- * A dedicated nr function is available.

All-properties-hold-for : Extended-modality a → Set a
All-properties-hold-for M =
  (∀ {m r p q} → Prodrec-allowed m r p q) ×
  (∀ {m p q} → Unitrec-allowed m p q) ×
  (∀ {m p} → Emptyrec-allowed m p) ×
  ¬ Starˢ-sink ×
  ¬ Id-erased ×
  (∀ {m} → erased-matches-for-J m ≡ all) ×
  (∀ {m} → erased-matches-for-K m ≡ all) ×
  ¬ Unit-allowed 𝕤 ×
  Unit-allowed 𝕨 ×
  (∀ {b p q} → ΠΣ-allowed b p q ⇔ (b ≡ BMΣ 𝕤 → p ≡ 𝟙)) ×
  K-allowed ×
  ¬ []-cong-allowed 𝕤 ×
  ([]-cong-allowed 𝕨 ⇔ (¬ Trivial)) ×
  (T 𝟘ᵐ-allowed ⇔ (¬ Trivial)) ×
  Nr-available
  where
  open Extended-modality M

private

  -- Functions used to construct the modalities below.

  TR′ :
    {M : Set} {𝕄 : Modality M} →
    Type-restrictions 𝕄
  TR′ =
    strong-types-restricted _ $
    no-type-restrictions _ true

  opaque

    Assumptions-TR′ :
      {M : Set} {𝕄 : Modality M} →
      Decidable (_≡_ {A = M}) →
      TD.Assumptions (TR′ {𝕄 = 𝕄})
    Assumptions-TR′ =
      Assumptions-strong-types-restricted _ ∘→
      Assumptions-no-type-restrictions _

  UR′ :
    {M : Set} {𝕄 : Modality M} →
    Usage-restrictions 𝕄
  UR′ = no-usage-restrictions _ false false

  opaque

    Assumptions-UR′ :
      {M : Set} {𝕄 : Modality M} →
      {has-nr : T (Modality.nr-available 𝕄)} →
      Decidable (_≡_ {A = M}) →
      UD.Assumptions (UR′ {𝕄 = 𝕄})
    Assumptions-UR′ {has-nr} =
      Assumptions-no-usage-restrictions _
        ⦃ has-nr = dedicated-nr has-nr ⦄

-- A trivial modality.

Trivial : Extended-modality lzero
Trivial = λ where
    .M  → ⊤
    .𝕄  → U.UnitModality (nr-available-and-𝟘ᵐ-allowed-if false) (λ ())
    .TR → TR′
    .UR → UR′
    .FA → U.full-reduction-assumptions (λ ())
    .TA → Assumptions-TR′ U._≟_
    .UA → Assumptions-UR′ U._≟_
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
    , (_$ refl) ∘→ proj₂
    , (_ , (λ ()))
    , (proj₂ , (_ ,_))
    , _
    , (_$ refl) ∘→ proj₂
    , (proj₁ , (λ hyp → hyp , (λ ())))
    , ((λ ()) , (_$ refl))
    , _

-- An erasure modality.

Erasure : Extended-modality lzero
Erasure = λ where
    .M  → E.Erasure
    .𝕄  → EM.ErasureModality (nr-available-and-𝟘ᵐ-allowed-if true)
    .TR → TR′
    .UR → UR′
    .FA → EP.full-reduction-assumptions _ _
    .TA → Assumptions-TR′ E._≟_
    .UA → Assumptions-UR′ E._≟_
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
    , (_$ refl) ∘→ proj₂
    , (_ , (λ ()))
    , (proj₂ , (_ ,_))
    , _
    , (_$ refl) ∘→ proj₂
    , (proj₁ , (λ hyp → hyp , (λ ())))
    , ((λ _ ()) , _)
    , _

-- An affine types modality.

Affine-types : Extended-modality lzero
Affine-types = λ where
    .M  → A.Affine
    .𝕄  → 𝕄′
    .TR → TR′
    .UR → UR′
    .FA → FA′
    .TA → Assumptions-TR′ A._≟_
    .UA → Assumptions-UR′ A._≟_
  where
  open Extended-modality

  𝕄′ = A.affineModality (nr-available-and-𝟘ᵐ-allowed-if true)

  opaque

    FA′ : Full-reduction-assumptions {𝕄 = 𝕄′} TR′ UR′
    FA′ =
      A.full-reduction-assumptions _
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
    , (_$ refl) ∘→ proj₂
    , (_ , (λ ()))
    , (proj₂ , (_ ,_))
    , _
    , (_$ refl) ∘→ proj₂
    , (proj₁ , (λ hyp → hyp , (λ ())))
    , ((λ _ ()) , _)
    , _

-- A linearity modality.

Linearity : Extended-modality lzero
Linearity = λ where
    .M  → L.Linearity
    .𝕄  → 𝕄′
    .TR → TR′
    .UR → UR′
    .FA → FA′
    .TA → Assumptions-TR′ L._≟_
    .UA → Assumptions-UR′ L._≟_
  where
  open Extended-modality

  𝕄′ = L.linearityModality (nr-available-and-𝟘ᵐ-allowed-if true)

  opaque

    FA′ : Full-reduction-assumptions {𝕄 = 𝕄′} TR′ UR′
    FA′ =
      L.full-reduction-assumptions _
        ( inj₁ ((_$ refl) ∘→ proj₂)
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
    , (_$ refl) ∘→ proj₂
    , (_ , (λ ()))
    , (proj₂ , (_ ,_))
    , _
    , (_$ refl) ∘→ proj₂
    , (proj₁ , (λ hyp → hyp , (λ ())))
    , ((λ _ ()) , _)
    , _

-- A linear or affine types modality.

Linear-or-affine-types : Extended-modality lzero
Linear-or-affine-types = λ where
    .M  → LA.Linear-or-affine
    .𝕄  → 𝕄′
    .TR → TR′
    .UR → UR′
    .FA → FA′
    .TA → Assumptions-TR′ LA._≟_
    .UA → Assumptions-UR′ LA._≟_
  where
  open Extended-modality

  𝕄′ = LA.linear-or-affine (nr-available-and-𝟘ᵐ-allowed-if true)

  opaque

    FA′ : Full-reduction-assumptions {𝕄 = 𝕄′} TR′ UR′
    FA′ =
      LA.full-reduction-assumptions
        ( inj₁ ((_$ refl) ∘→ proj₂)
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
    , (_$ refl) ∘→ proj₂
    , (_ , (λ ()))
    , (proj₂ , (_ ,_))
    , _
    , (_$ refl) ∘→ proj₂
    , (proj₁ , (λ hyp → hyp , (λ ())))
    , ((λ _ ()) , _)
    , _

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

    is-order-embedding : Is-order-embedding E₁.𝕄 E₂.𝕄 tr
    is-order-embedding =
      unit⇨erasure ((λ _ → dedicated-nr _) , (λ _ → dedicated-nr _))

    is-Σ-order-embedding : Is-Σ-order-embedding E₁.𝕄 E₂.𝕄 tr tr
    is-Σ-order-embedding =
      Is-order-embedding→Is-Σ-order-embedding is-order-embedding

    are-preserving-type-restrictions :
      Are-preserving-type-restrictions E₁.TR E₂.TR tr tr
    are-preserving-type-restrictions =
      unit→erasure-preserves-strong-types-restricted $
      Are-preserving-type-restrictions-no-type-restrictions (λ _ ())

    are-reflecting-type-restrictions :
      Are-reflecting-type-restrictions E₁.TR E₂.TR tr tr
    are-reflecting-type-restrictions =
      unit→erasure-reflects-strong-types-restricted $
      Are-reflecting-type-restrictions-no-type-restrictions
        (λ _ → inj₁ refl)

    are-preserving-usage-restrictions :
      Are-preserving-usage-restrictions E₁.UR E₂.UR tr tr
    are-preserving-usage-restrictions =
      Are-preserving-usage-restrictions-no-usage-restrictions _

    are-reflecting-usage-restrictions :
      Are-reflecting-usage-restrictions E₁.UR E₂.UR tr tr
    are-reflecting-usage-restrictions =
      Are-reflecting-usage-restrictions-no-usage-restrictions
        _ (λ _ → inj₂ refl)

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

  opaque

    is-order-embedding : Is-order-embedding E₁.𝕄 E₂.𝕄 tr
    is-order-embedding =
      erasure⇨zero-one-many refl
        ((λ _ → dedicated-nr _) , (λ _ → dedicated-nr _))

    is-Σ-order-embedding : Is-Σ-order-embedding E₁.𝕄 E₂.𝕄 tr tr-Σ
    is-Σ-order-embedding =
      erasure⇨zero-one-many-Σ _

    are-preserving-type-restrictions :
      Are-preserving-type-restrictions E₁.TR E₂.TR tr tr-Σ
    are-preserving-type-restrictions =
      erasure→zero-one-many-Σ-preserves-strong-types-restricted $
      Are-preserving-type-restrictions-no-type-restrictions (λ _ ())

    are-reflecting-type-restrictions :
      Are-reflecting-type-restrictions E₁.TR E₂.TR tr tr-Σ
    are-reflecting-type-restrictions =
      erasure→zero-one-many-Σ-reflects-strong-types-restricted $
      Are-reflecting-type-restrictions-no-type-restrictions
        (λ _ → inj₂ (λ ()))

    are-preserving-usage-restrictions :
      Are-preserving-usage-restrictions E₁.UR E₂.UR tr tr-Σ
    are-preserving-usage-restrictions =
      Are-preserving-usage-restrictions-no-usage-restrictions _

    are-reflecting-usage-restrictions :
      Are-reflecting-usage-restrictions E₁.UR E₂.UR tr tr-Σ
    are-reflecting-usage-restrictions =
      Are-reflecting-usage-restrictions-no-usage-restrictions
        _ (λ _ → inj₁ _)

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

  opaque

    is-order-embedding : Is-order-embedding E₁.𝕄 E₂.𝕄 tr
    is-order-embedding =
      erasure⇨zero-one-many refl
        ((λ _ → dedicated-nr _) , (λ _ → dedicated-nr _))

    is-Σ-order-embedding : Is-Σ-order-embedding E₁.𝕄 E₂.𝕄 tr tr-Σ
    is-Σ-order-embedding =
      erasure⇨zero-one-many-Σ _

    are-preserving-type-restrictions :
      Are-preserving-type-restrictions E₁.TR E₂.TR tr tr-Σ
    are-preserving-type-restrictions =
      erasure→zero-one-many-Σ-preserves-strong-types-restricted $
      Are-preserving-type-restrictions-no-type-restrictions (λ _ ())

    are-reflecting-type-restrictions :
      Are-reflecting-type-restrictions E₁.TR E₂.TR tr tr-Σ
    are-reflecting-type-restrictions =
      erasure→zero-one-many-Σ-reflects-strong-types-restricted $
      Are-reflecting-type-restrictions-no-type-restrictions
        (λ _ → inj₂ (λ ()))

    are-preserving-usage-restrictions :
      Are-preserving-usage-restrictions E₁.UR E₂.UR tr tr-Σ
    are-preserving-usage-restrictions =
      Are-preserving-usage-restrictions-no-usage-restrictions _

    are-reflecting-usage-restrictions :
      Are-reflecting-usage-restrictions E₁.UR E₂.UR tr tr-Σ
    are-reflecting-usage-restrictions =
      Are-reflecting-usage-restrictions-no-usage-restrictions
        _ (λ _ → inj₁ _)

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

  opaque

    is-order-embedding : Is-order-embedding E₁.𝕄 E₂.𝕄 tr
    is-order-embedding =
      affine⇨linear-or-affine refl
        ((λ _ → dedicated-nr _) , (λ _ → dedicated-nr _))

    is-Σ-order-embedding : Is-Σ-order-embedding E₁.𝕄 E₂.𝕄 tr tr-Σ
    is-Σ-order-embedding =
      affine⇨linear-or-affine-Σ _

    are-preserving-type-restrictions :
      Are-preserving-type-restrictions E₁.TR E₂.TR tr tr-Σ
    are-preserving-type-restrictions =
      affine→linear-or-affine-Σ-preserves-strong-types-restricted $
      Are-preserving-type-restrictions-no-type-restrictions (λ _ ())

    are-reflecting-type-restrictions :
      Are-reflecting-type-restrictions E₁.TR E₂.TR tr tr-Σ
    are-reflecting-type-restrictions =
      affine→linear-or-affine-Σ-reflects-strong-types-restricted $
      Are-reflecting-type-restrictions-no-type-restrictions
        (λ _ → inj₂ (λ ()))

    are-preserving-usage-restrictions :
      Are-preserving-usage-restrictions E₁.UR E₂.UR tr tr-Σ
    are-preserving-usage-restrictions =
      Are-preserving-usage-restrictions-no-usage-restrictions _

    are-reflecting-usage-restrictions :
      Are-reflecting-usage-restrictions E₁.UR E₂.UR tr tr-Σ
    are-reflecting-usage-restrictions =
      Are-reflecting-usage-restrictions-no-usage-restrictions
        _ (λ _ → inj₁ _)

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

  opaque

    is-order-embedding : Is-order-embedding E₁.𝕄 E₂.𝕄 tr
    is-order-embedding =
      linearity⇨linear-or-affine refl
        ((λ _ → dedicated-nr _) , (λ _ → dedicated-nr _))

    is-Σ-order-embedding : Is-Σ-order-embedding E₁.𝕄 E₂.𝕄 tr tr
    is-Σ-order-embedding =
      Is-order-embedding→Is-Σ-order-embedding is-order-embedding

    are-preserving-type-restrictions :
      Are-preserving-type-restrictions E₁.TR E₂.TR tr tr
    are-preserving-type-restrictions =
      linearity→linear-or-affine-preserves-strong-types-restricted $
      Are-preserving-type-restrictions-no-type-restrictions (λ _ ())

    are-reflecting-type-restrictions :
      Are-reflecting-type-restrictions E₁.TR E₂.TR tr tr
    are-reflecting-type-restrictions =
      linearity→linear-or-affine-reflects-strong-types-restricted $
      Are-reflecting-type-restrictions-no-type-restrictions
        (λ _ → inj₂ (λ ()))

    are-preserving-usage-restrictions :
      Are-preserving-usage-restrictions E₁.UR E₂.UR tr tr
    are-preserving-usage-restrictions =
      Are-preserving-usage-restrictions-no-usage-restrictions _

    are-reflecting-usage-restrictions :
      Are-reflecting-usage-restrictions E₁.UR E₂.UR tr tr
    are-reflecting-usage-restrictions =
      Are-reflecting-usage-restrictions-no-usage-restrictions
        _ (λ _ → inj₁ _)
