------------------------------------------------------------------------
-- Some examples of extended modalities, along with some morphisms
-- between them
------------------------------------------------------------------------

-- The formalisation contains a number of parameters. These examples
-- show that it is possible to instantiate all of the parameters at
-- the same time.

module Graded.Modality.Extended.K-not-allowed.Erased-matches where

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum
open import Tools.Unit

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
open import Graded.Mode
open import Graded.Restrictions
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
-- * "Some" erased matches are allowed for J and K when the mode
--   is 𝟙ᵐ, and all erased matches are allowed for J and K when the
--   mode is 𝟘ᵐ.
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
  erased-matches-for-J 𝟙ᵐ ≡ some ×
  erased-matches-for-K 𝟙ᵐ ≡ some ×
  (∀ {m} → m ≢ 𝟙ᵐ → erased-matches-for-J m ≡ all) ×
  (∀ {m} → m ≢ 𝟙ᵐ → erased-matches-for-K m ≡ all) ×
  ¬ Unit-allowed 𝕤 ×
  Unit-allowed 𝕨 ×
  (∀ {b p q} →
   ΠΣ-allowed b p q ⇔
   (b ≢ BMΣ 𝕤 × (p ≡ ω → q ≡ ω) × (p ≢ ω → q ≡ 𝟘))) ×
  ¬ K-allowed ×
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
    no-erased-matches-TR _ 𝕤 $
    no-strong-types _ $
    second-ΠΣ-quantities-𝟘-or-ω _ $
    no-type-restrictions _ false

  UR′ :
    {M : Set} {𝕄 : Modality M} →
    Usage-restrictions 𝕄
  UR′ =
    not-all-erased-matches-JK _ $
    no-usage-restrictions _ false false

-- A trivial modality.

Trivial : Extended-modality lzero
Trivial = λ where
    .M  → ⊤
    .𝕄  → U.UnitModality (nr-available-and-𝟘ᵐ-allowed-if false) (λ ())
    .TR → TR′
    .UR → UR′
    .FA → U.full-reduction-assumptions (λ ())
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
    , (λ where
         {m = 𝟙ᵐ} → ⊥-elim ∘→ (_$ refl))
    , (λ where
         {m = 𝟙ᵐ} → ⊥-elim ∘→ (_$ refl))
    , (_$ refl) ∘→ proj₂
    , (_ , (λ ()))
    , ( (λ ((_ , hyp₁) , hyp₂) → Lift.lower hyp₂ , hyp₁)
      , (λ (hyp₁ , hyp₂) → (_ , hyp₂) , lift hyp₁)
      )
    , (λ ())
    , (_$ refl) ∘→ proj₂
    , (proj₁ ∘→ proj₁ , ⊥-elim ∘→ (_$ refl))
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
    , (λ where
         {m = 𝟘ᵐ} _ → refl
         {m = 𝟙ᵐ}   → ⊥-elim ∘→ (_$ refl))
    , (λ where
         {m = 𝟘ᵐ} _ → refl
         {m = 𝟙ᵐ}   → ⊥-elim ∘→ (_$ refl))
    , (_$ refl) ∘→ proj₂
    , (_ , (λ ()))
    , ( (λ ((_ , hyp₁) , hyp₂) → Lift.lower hyp₂ , hyp₁)
      , (λ (hyp₁ , hyp₂) → (_ , hyp₂) , lift hyp₁)
      )
    , (λ ())
    , (_$ refl) ∘→ proj₂
    , (proj₁ ∘→ proj₁ , (λ _ → ((λ ()) , (λ ())) , (λ ())))
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
  where
  open Extended-modality

  𝕄′ = A.affineModality (nr-available-and-𝟘ᵐ-allowed-if true)

  opaque

    FA′ : Full-reduction-assumptions {𝕄 = 𝕄′} TR′ UR′
    FA′ =
      A.full-reduction-assumptions _
        (_ , (λ _ (_ , hyp) → case Lift.lower hyp refl of λ ()))

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
    , (λ where
         {m = 𝟘ᵐ} _ → refl
         {m = 𝟙ᵐ}   → ⊥-elim ∘→ (_$ refl))
    , (λ where
         {m = 𝟘ᵐ} _ → refl
         {m = 𝟙ᵐ}   → ⊥-elim ∘→ (_$ refl))
    , (_$ refl) ∘→ proj₂
    , (_ , (λ ()))
    , ( (λ ((_ , hyp₁) , hyp₂) → Lift.lower hyp₂ , hyp₁)
      , (λ (hyp₁ , hyp₂) → (_ , hyp₂) , lift hyp₁)
      )
    , (λ ())
    , (_$ refl) ∘→ proj₂
    , (proj₁ ∘→ proj₁ , (λ _ → ((λ ()) , (λ ())) , (λ ())))
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
  where
  open Extended-modality

  𝕄′ = L.linearityModality (nr-available-and-𝟘ᵐ-allowed-if true)

  opaque

    FA′ : Full-reduction-assumptions {𝕄 = 𝕄′} TR′ UR′
    FA′ =
      L.full-reduction-assumptions _
        ( inj₁ ((_$ refl) ∘→ proj₂)
        , (λ _ (_ , hyp) → case Lift.lower hyp refl of λ ())
        , (λ _ (_ , hyp) → case Lift.lower hyp refl of λ ())
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
    , (λ where
         {m = 𝟘ᵐ} _ → refl
         {m = 𝟙ᵐ}   → ⊥-elim ∘→ (_$ refl))
    , (λ where
         {m = 𝟘ᵐ} _ → refl
         {m = 𝟙ᵐ}   → ⊥-elim ∘→ (_$ refl))
    , (_$ refl) ∘→ proj₂
    , (_ , (λ ()))
    , ( (λ ((_ , hyp₁) , hyp₂) → Lift.lower hyp₂ , hyp₁)
      , (λ (hyp₁ , hyp₂) → (_ , hyp₂) , lift hyp₁)
      )
    , (λ ())
    , (_$ refl) ∘→ proj₂
    , (proj₁ ∘→ proj₁ , (λ _ → ((λ ()) , (λ ())) , (λ ())))
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
  where
  open Extended-modality

  𝕄′ = LA.linear-or-affine (nr-available-and-𝟘ᵐ-allowed-if true)

  opaque

    FA′ : Full-reduction-assumptions {𝕄 = 𝕄′} TR′ UR′
    FA′ =
      LA.full-reduction-assumptions
        ( inj₁ ((_$ refl) ∘→ proj₂)
        , (λ _ (_ , hyp) → case Lift.lower hyp refl of λ ())
        , (λ _ (_ , hyp) → case Lift.lower hyp refl of λ ())
        , (λ _ (_ , hyp) → case Lift.lower hyp refl of λ ())
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
    , (λ where
         {m = 𝟘ᵐ} _ → refl
         {m = 𝟙ᵐ}   → ⊥-elim ∘→ (_$ refl))
    , (λ where
         {m = 𝟘ᵐ} _ → refl
         {m = 𝟙ᵐ}   → ⊥-elim ∘→ (_$ refl))
    , (_$ refl) ∘→ proj₂
    , (_ , (λ ()))
    , ( (λ ((_ , hyp₁) , hyp₂) → Lift.lower hyp₂ , hyp₁)
      , (λ (hyp₁ , hyp₂) → (_ , hyp₂) , lift hyp₁)
      )
    , (λ ())
    , (_$ refl) ∘→ proj₂
    , (proj₁ ∘→ proj₁ , (λ _ → ((λ ()) , (λ ())) , (λ ())))
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
      Are-preserving-type-restrictions-no-erased-matches-TR $
      Are-preserving-type-restrictions-no-strong-types $
      unit→erasure-preserves-second-ΠΣ-quantities-𝟘-or-ω $
      Are-preserving-type-restrictions-no-type-restrictions (λ _ ())

    are-reflecting-type-restrictions :
      Are-reflecting-type-restrictions E₁.TR E₂.TR tr tr
    are-reflecting-type-restrictions =
      Are-reflecting-type-restrictions-no-erased-matches-TR (λ ()) $
      Are-reflecting-type-restrictions-no-strong-types (λ ()) $
      unit→erasure-reflects-second-ΠΣ-quantities-𝟘-or-ω $
      Are-reflecting-type-restrictions-no-type-restrictions
        (λ _ → inj₁ refl)

    are-preserving-usage-restrictions :
      Are-preserving-usage-restrictions E₁.UR E₂.UR tr tr
    are-preserving-usage-restrictions =
      Are-preserving-usage-restrictions-not-all-erased-matches-JK $
      Are-preserving-usage-restrictions-no-usage-restrictions _

    are-reflecting-usage-restrictions :
      Are-reflecting-usage-restrictions E₁.UR E₂.UR tr tr
    are-reflecting-usage-restrictions =
      Are-reflecting-usage-restrictions-not-all-erased-matches-JK $
      Are-reflecting-usage-restrictions-no-usage-restrictions
        _ (λ _ → inj₂ refl)

-- A morphism from Erasure to Affine-types.

Erasure⇨Affine-types : Erasure ⇨ Affine-types
Erasure⇨Affine-types = λ where
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
  module E₁ = Extended-modality Erasure
  module E₂ = Extended-modality Affine-types

  tr = erasure→zero-one-many

  opaque

    is-order-embedding : Is-order-embedding E₁.𝕄 E₂.𝕄 tr
    is-order-embedding =
      erasure⇨zero-one-many refl
        ((λ _ → dedicated-nr _) , (λ _ → dedicated-nr _))

    is-Σ-order-embedding : Is-Σ-order-embedding E₁.𝕄 E₂.𝕄 tr tr
    is-Σ-order-embedding =
      Is-order-embedding→Is-Σ-order-embedding is-order-embedding

    are-preserving-type-restrictions :
      Are-preserving-type-restrictions E₁.TR E₂.TR tr tr
    are-preserving-type-restrictions =
      Are-preserving-type-restrictions-no-erased-matches-TR $
      Are-preserving-type-restrictions-no-strong-types $
      erasure→zero-one-many-preserves-second-ΠΣ-quantities-𝟘-or-ω $
      Are-preserving-type-restrictions-no-type-restrictions (λ _ ())

    are-reflecting-type-restrictions :
      Are-reflecting-type-restrictions E₁.TR E₂.TR tr tr
    are-reflecting-type-restrictions =
      Are-reflecting-type-restrictions-no-erased-matches-TR (λ ()) $
      Are-reflecting-type-restrictions-no-strong-types (λ ()) $
      erasure→zero-one-many-reflects-second-ΠΣ-quantities-𝟘-or-ω $
      Are-reflecting-type-restrictions-no-type-restrictions
        (λ _ → inj₂ (λ ()))

    are-preserving-usage-restrictions :
      Are-preserving-usage-restrictions E₁.UR E₂.UR tr tr
    are-preserving-usage-restrictions =
      Are-preserving-usage-restrictions-not-all-erased-matches-JK $
      Are-preserving-usage-restrictions-no-usage-restrictions _

    are-reflecting-usage-restrictions :
      Are-reflecting-usage-restrictions E₁.UR E₂.UR tr tr
    are-reflecting-usage-restrictions =
      Are-reflecting-usage-restrictions-not-all-erased-matches-JK $
      Are-reflecting-usage-restrictions-no-usage-restrictions
        _ (λ _ → inj₁ _)

-- A morphism from Erasure to Linearity.

Erasure⇨Linearity : Erasure ⇨ Linearity
Erasure⇨Linearity = λ where
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
  module E₁ = Extended-modality Erasure
  module E₂ = Extended-modality Linearity

  tr = erasure→zero-one-many

  opaque

    is-order-embedding : Is-order-embedding E₁.𝕄 E₂.𝕄 tr
    is-order-embedding =
      erasure⇨zero-one-many refl
        ((λ _ → dedicated-nr _) , (λ _ → dedicated-nr _))

    is-Σ-order-embedding : Is-Σ-order-embedding E₁.𝕄 E₂.𝕄 tr tr
    is-Σ-order-embedding =
      Is-order-embedding→Is-Σ-order-embedding is-order-embedding

    are-preserving-type-restrictions :
      Are-preserving-type-restrictions E₁.TR E₂.TR tr tr
    are-preserving-type-restrictions =
      Are-preserving-type-restrictions-no-erased-matches-TR $
      Are-preserving-type-restrictions-no-strong-types $
      erasure→zero-one-many-preserves-second-ΠΣ-quantities-𝟘-or-ω $
      Are-preserving-type-restrictions-no-type-restrictions (λ _ ())

    are-reflecting-type-restrictions :
      Are-reflecting-type-restrictions E₁.TR E₂.TR tr tr
    are-reflecting-type-restrictions =
      Are-reflecting-type-restrictions-no-erased-matches-TR (λ ()) $
      Are-reflecting-type-restrictions-no-strong-types (λ ()) $
      erasure→zero-one-many-reflects-second-ΠΣ-quantities-𝟘-or-ω $
      Are-reflecting-type-restrictions-no-type-restrictions
        (λ _ → inj₂ (λ ()))

    are-preserving-usage-restrictions :
      Are-preserving-usage-restrictions E₁.UR E₂.UR tr tr
    are-preserving-usage-restrictions =
      Are-preserving-usage-restrictions-not-all-erased-matches-JK $
      Are-preserving-usage-restrictions-no-usage-restrictions _

    are-reflecting-usage-restrictions :
      Are-reflecting-usage-restrictions E₁.UR E₂.UR tr tr
    are-reflecting-usage-restrictions =
      Are-reflecting-usage-restrictions-not-all-erased-matches-JK $
      Are-reflecting-usage-restrictions-no-usage-restrictions
        _ (λ _ → inj₁ _)

-- A morphism from Affine-types to Linear-or-affine-types.

Affine-types⇨Linear-or-affine-types :
  Affine-types ⇨ Linear-or-affine-types
Affine-types⇨Linear-or-affine-types = λ where
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
  module E₁ = Extended-modality Affine-types
  module E₂ = Extended-modality Linear-or-affine-types

  tr = affine→linear-or-affine

  opaque

    is-order-embedding : Is-order-embedding E₁.𝕄 E₂.𝕄 tr
    is-order-embedding =
      affine⇨linear-or-affine refl
        ((λ _ → dedicated-nr _) , (λ _ → dedicated-nr _))

    is-Σ-order-embedding : Is-Σ-order-embedding E₁.𝕄 E₂.𝕄 tr tr
    is-Σ-order-embedding =
      Is-order-embedding→Is-Σ-order-embedding is-order-embedding

    are-preserving-type-restrictions :
      Are-preserving-type-restrictions E₁.TR E₂.TR tr tr
    are-preserving-type-restrictions =
      Are-preserving-type-restrictions-no-erased-matches-TR $
      Are-preserving-type-restrictions-no-strong-types $
      affine→linear-or-affine-preserves-second-ΠΣ-quantities-𝟘-or-ω $
      Are-preserving-type-restrictions-no-type-restrictions (λ _ ())

    are-reflecting-type-restrictions :
      Are-reflecting-type-restrictions E₁.TR E₂.TR tr tr
    are-reflecting-type-restrictions =
      Are-reflecting-type-restrictions-no-erased-matches-TR (λ ()) $
      Are-reflecting-type-restrictions-no-strong-types (λ ()) $
      affine→linear-or-affine-reflects-second-ΠΣ-quantities-𝟘-or-ω $
      Are-reflecting-type-restrictions-no-type-restrictions
        (λ _ → inj₂ (λ ()))

    are-preserving-usage-restrictions :
      Are-preserving-usage-restrictions E₁.UR E₂.UR tr tr
    are-preserving-usage-restrictions =
      Are-preserving-usage-restrictions-not-all-erased-matches-JK $
      Are-preserving-usage-restrictions-no-usage-restrictions _

    are-reflecting-usage-restrictions :
      Are-reflecting-usage-restrictions E₁.UR E₂.UR tr tr
    are-reflecting-usage-restrictions =
      Are-reflecting-usage-restrictions-not-all-erased-matches-JK $
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
      Are-preserving-type-restrictions-no-erased-matches-TR $
      Are-preserving-type-restrictions-no-strong-types $
      linearity→linear-or-affine-preserves-second-ΠΣ-quantities-𝟘-or-ω $
      Are-preserving-type-restrictions-no-type-restrictions (λ _ ())

    are-reflecting-type-restrictions :
      Are-reflecting-type-restrictions E₁.TR E₂.TR tr tr
    are-reflecting-type-restrictions =
      Are-reflecting-type-restrictions-no-erased-matches-TR (λ ()) $
      Are-reflecting-type-restrictions-no-strong-types (λ ()) $
      linearity→linear-or-affine-reflects-second-ΠΣ-quantities-𝟘-or-ω $
      Are-reflecting-type-restrictions-no-type-restrictions
        (λ _ → inj₂ (λ ()))

    are-preserving-usage-restrictions :
      Are-preserving-usage-restrictions E₁.UR E₂.UR tr tr
    are-preserving-usage-restrictions =
      Are-preserving-usage-restrictions-not-all-erased-matches-JK $
      Are-preserving-usage-restrictions-no-usage-restrictions _

    are-reflecting-usage-restrictions :
      Are-reflecting-usage-restrictions E₁.UR E₂.UR tr tr
    are-reflecting-usage-restrictions =
      Are-reflecting-usage-restrictions-not-all-erased-matches-JK $
      Are-reflecting-usage-restrictions-no-usage-restrictions
        _ (λ _ → inj₁ _)
