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
open import Graded.Mode
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
-- * []-cong is not allowed.
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
  (∀ {s} → ¬ []-cong-allowed s) ×
  (T 𝟘ᵐ-allowed ⇔ (¬ Trivial))
  where
  open Extended-modality M

private

  -- Functions used to construct the modalities below.

  TR′ :
    {M : Set} {𝕄 : Modality M} →
    Type-restrictions 𝕄
  TR′ =
    no-erased-matches-TR _ 𝕤 $
    no-erased-matches-TR _ 𝕨 $
    no-strong-types _ $
    second-ΠΣ-quantities-𝟘-or-ω _ $
    no-type-restrictions _ false

  opaque

    Assumptions-TR′ :
      {M : Set} {𝕄 : Modality M} →
      Decidable (_≡_ {A = M}) →
      TD.Assumptions (TR′ {𝕄 = 𝕄})
    Assumptions-TR′ =
      Assumptions-no-erased-matches-TR _ ∘→
      Assumptions-no-erased-matches-TR _ ∘→
      Assumptions-no-strong-types _ ∘→
      Assumptions-second-ΠΣ-quantities-𝟘-or-ω _ ∘→
      Assumptions-no-type-restrictions _

  UR′ :
    {M : Set} {𝕄 : Modality M} →
    Usage-restrictions 𝕄
  UR′ =
    only-some-erased-matches _ $
    no-usage-restrictions _ false false

  opaque

    Assumptions-UR′ :
      {M : Set} {𝕄 : Modality M} →
      {has-nr : T (Modality.nr-available 𝕄)} →
      Decidable (_≡_ {A = M}) →
      UD.Assumptions (UR′ {𝕄 = 𝕄})
    Assumptions-UR′ {has-nr} =
      Assumptions-only-some-erased-matches _ ∘→
      Assumptions-no-usage-restrictions _
        ⦃ has-nr = dedicated-nr has-nr ⦄

-- A trivial modality.

Trivial : Extended-modality lzero
Trivial = λ where
    .M   → ⊤
    .𝕄   → U.UnitModality (nr-available-and-𝟘ᵐ-allowed-if false) (λ ())
    .TR  → TR′
    .UR  → UR′
    .FA  → U.full-reduction-assumptions (λ ())
    .TA  → Assumptions-TR′ U._≟_
    .UA  → Assumptions-UR′ U._≟_
    .NR  → _
    .NR₀ → U.nr-linearity-like-for-𝟘
    .NR₁ → U.nr-linearity-like-for-𝟙
  where
  open Extended-modality

opaque

  -- The properties listed above all hold for Trivial.

  All-properties-hold-for-Trivial : All-properties-hold-for Trivial
  All-properties-hold-for-Trivial =
      ((λ _ → inj₂ (inj₂ refl)) , (λ _ → _ , ⊥-elim ∘→ (_$ refl)))
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
    , (λ ())
    , (_$ refl) ∘→ proj₂
    , (_ , (λ ()))
    , ( (λ ((_ , hyp₁) , hyp₂) → Lift.lower hyp₂ , hyp₁)
      , (λ (hyp₁ , hyp₂) → (_ , hyp₂) , lift hyp₁)
      )
    , (λ ())
    , (λ where
         {s = 𝕤} → (_$ refl) ∘→ proj₂
         {s = 𝕨} → (_$ refl) ∘→ proj₂ ∘→ proj₁)
    , ((λ ()) , (_$ refl))

-- An erasure modality.

Erasure : Extended-modality lzero
Erasure = λ where
    .M       → E.Erasure
    .𝕄       → EM.ErasureModality var
    .TR      → TR′
    .UR      → UR′
    .FA      → EP.full-reduction-assumptions _ _
    .TA      → Assumptions-TR′ E._≟_
    .UA      → Assumptions-UR′ E._≟_
    .NR      → _
    .NR₀ {z} → EP.nr-linearity-like-for-𝟘 var {z = z}
    .NR₁ {z} → EP.nr-linearity-like-for-𝟙 var {z = z}
  where
  open Extended-modality

  var = nr-available-and-𝟘ᵐ-allowed-if true

opaque

  -- The properties listed above all hold for Erasure.

  All-properties-hold-for-Erasure : All-properties-hold-for Erasure
  All-properties-hold-for-Erasure =
      (λ where
         {m = 𝟘ᵐ} → (λ _ → inj₁ (λ ())) , (λ _ → _ , (λ _ ()))
         {m = 𝟙ᵐ} →
             (λ (_ , r≢𝟘) → inj₂ (inj₁ (r≢𝟘 (λ ()) refl)))
           , (λ where
                (inj₁ 𝟙ᵐ≢𝟙ᵐ)      → ⊥-elim $ 𝟙ᵐ≢𝟙ᵐ refl
                (inj₂ (inj₁ r≢𝟘)) → _ , (λ _ _ → r≢𝟘)))
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
    , (λ where
         {s = 𝕤} → (_$ refl) ∘→ proj₂
         {s = 𝕨} → (_$ refl) ∘→ proj₂ ∘→ proj₁)
    , ((λ _ ()) , _)

-- An affine types modality.

Affine-types : Extended-modality lzero
Affine-types = λ where
    .M           → A.Affine
    .𝕄           → 𝕄′
    .TR          → TR′
    .UR          → UR′
    .FA          → FA′
    .TA          → Assumptions-TR′ A._≟_
    .UA          → Assumptions-UR′ A._≟_
    .NR          → _
    .NR₀ {p}     → A.nr-linearity-like-for-𝟘 {p = p}
    .NR₁ {p} {z} → A.nr-linearity-like-for-𝟙 {p = p} {z = z}
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
      (λ where
         {m = 𝟘ᵐ} → (λ _ → inj₁ (λ ())) , (λ _ → _ , (λ _ ()))
         {m = 𝟙ᵐ} →
             (λ (_ , r≢𝟘) → inj₂ (inj₁ (r≢𝟘 (λ ()) refl)))
           , (λ where
                (inj₁ 𝟙ᵐ≢𝟙ᵐ)      → ⊥-elim $ 𝟙ᵐ≢𝟙ᵐ refl
                (inj₂ (inj₁ r≢𝟘)) → _ , (λ _ _ → r≢𝟘)))
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
    , (λ where
         {s = 𝕤} → (_$ refl) ∘→ proj₂
         {s = 𝕨} → (_$ refl) ∘→ proj₂ ∘→ proj₁)
    , ((λ _ ()) , _)

-- A linearity modality.

Linearity : Extended-modality lzero
Linearity = λ where
    .M           → L.Linearity
    .𝕄           → 𝕄′
    .TR          → TR′
    .UR          → UR′
    .FA          → FA′
    .TA          → Assumptions-TR′ L._≟_
    .UA          → Assumptions-UR′ L._≟_
    .NR          → _
    .NR₀ {p}     → L.nr-linearity-like-for-𝟘 {p = p}
    .NR₁ {p} {z} → L.nr-linearity-like-for-𝟙 {p = p} {z = z}
  where
  open Extended-modality

  𝕄′ = L.linearityModality (nr-available-and-𝟘ᵐ-allowed-if true)

  opaque

    FA′ : Full-reduction-assumptions {𝕄 = 𝕄′} TR′ UR′
    FA′ =
      L.full-reduction-assumptions _
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
         {m = 𝟘ᵐ} → (λ _ → inj₁ (λ ())) , (λ _ → _ , (λ _ ()))
         {m = 𝟙ᵐ} →
             (λ (_ , r≢𝟘) → inj₂ (inj₁ (r≢𝟘 (λ ()) refl)))
           , (λ where
                (inj₁ 𝟙ᵐ≢𝟙ᵐ)      → ⊥-elim $ 𝟙ᵐ≢𝟙ᵐ refl
                (inj₂ (inj₁ r≢𝟘)) → _ , (λ _ _ → r≢𝟘)))
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
    , (λ where
         {s = 𝕤} → (_$ refl) ∘→ proj₂
         {s = 𝕨} → (_$ refl) ∘→ proj₂ ∘→ proj₁)
    , ((λ _ ()) , _)

-- A linear or affine types modality.

Linear-or-affine-types : Extended-modality lzero
Linear-or-affine-types = λ where
    .M           → LA.Linear-or-affine
    .𝕄           → 𝕄′
    .TR          → TR′
    .UR          → UR′
    .FA          → FA′
    .TA          → Assumptions-TR′ LA._≟_
    .UA          → Assumptions-UR′ LA._≟_
    .NR          → _
    .NR₀ {p}     → LA.nr-linearity-like-for-𝟘 {p = p}
    .NR₁ {p} {s} → LA.nr-linearity-like-for-𝟙 {p = p} {s = s}
  where
  open Extended-modality

  𝕄′ = LA.linear-or-affine (nr-available-and-𝟘ᵐ-allowed-if true)

  opaque

    FA′ : Full-reduction-assumptions {𝕄 = 𝕄′} TR′ UR′
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
         {m = 𝟘ᵐ} → (λ _ → inj₁ (λ ())) , (λ _ → _ , (λ _ ()))
         {m = 𝟙ᵐ} →
             (λ (_ , r≢𝟘) → inj₂ (inj₁ (r≢𝟘 (λ ()) refl)))
           , (λ where
                (inj₁ 𝟙ᵐ≢𝟙ᵐ)      → ⊥-elim $ 𝟙ᵐ≢𝟙ᵐ refl
                (inj₂ (inj₁ r≢𝟘)) → _ , (λ _ _ → r≢𝟘)))
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
    , (λ where
         {s = 𝕤} → (_$ refl) ∘→ proj₂
         {s = 𝕨} → (_$ refl) ∘→ proj₂ ∘→ proj₁)
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
      Are-preserving-type-restrictions-no-erased-matches-TR $
      Are-preserving-type-restrictions-no-strong-types $
      unit→erasure-preserves-second-ΠΣ-quantities-𝟘-or-ω $
      Are-preserving-type-restrictions-no-type-restrictions (λ _ ())

    are-reflecting-type-restrictions :
      Are-reflecting-type-restrictions E₁.TR E₂.TR tr tr
    are-reflecting-type-restrictions =
      Are-reflecting-type-restrictions-no-erased-matches-TR (λ ()) $
      Are-reflecting-type-restrictions-no-erased-matches-TR (λ ()) $
      Are-reflecting-type-restrictions-no-strong-types (λ ()) $
      unit→erasure-reflects-second-ΠΣ-quantities-𝟘-or-ω $
      Are-reflecting-type-restrictions-no-type-restrictions
        (λ _ → inj₁ refl)

    are-preserving-usage-restrictions :
      Are-preserving-usage-restrictions E₁.UR E₂.UR tr tr
    are-preserving-usage-restrictions =
      Are-preserving-usage-restrictions-only-some-erased-matches
        (λ _ → inj₂ (λ ())) $
      Are-preserving-usage-restrictions-no-usage-restrictions _

    are-reflecting-usage-restrictions :
      Are-reflecting-usage-restrictions E₁.UR E₂.UR tr tr
    are-reflecting-usage-restrictions =
      Are-reflecting-usage-restrictions-only-some-erased-matches
        (⊥-elim ∘→ (_$ refl)) $
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
      Are-preserving-type-restrictions-no-erased-matches-TR $
      Are-preserving-type-restrictions-no-strong-types $
      erasure→zero-one-many-preserves-second-ΠΣ-quantities-𝟘-or-ω $
      Are-preserving-type-restrictions-no-type-restrictions (λ _ ())

    are-reflecting-type-restrictions :
      Are-reflecting-type-restrictions E₁.TR E₂.TR tr tr
    are-reflecting-type-restrictions =
      Are-reflecting-type-restrictions-no-erased-matches-TR (λ ()) $
      Are-reflecting-type-restrictions-no-erased-matches-TR (λ ()) $
      Are-reflecting-type-restrictions-no-strong-types (λ ()) $
      erasure→zero-one-many-reflects-second-ΠΣ-quantities-𝟘-or-ω $
      Are-reflecting-type-restrictions-no-type-restrictions
        (λ _ → inj₂ (λ ()))

    are-preserving-usage-restrictions :
      Are-preserving-usage-restrictions E₁.UR E₂.UR tr tr
    are-preserving-usage-restrictions =
      Are-preserving-usage-restrictions-only-some-erased-matches
        (λ _ → inj₁ ((λ ()) , (λ { {p = E.𝟘} refl → refl }))) $
      Are-preserving-usage-restrictions-no-usage-restrictions _

    are-reflecting-usage-restrictions :
      Are-reflecting-usage-restrictions E₁.UR E₂.UR tr tr
    are-reflecting-usage-restrictions =
      Are-reflecting-usage-restrictions-only-some-erased-matches
        (λ _ → (λ ()) , (λ { refl → refl })) $
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
      Are-preserving-type-restrictions-no-erased-matches-TR $
      Are-preserving-type-restrictions-no-strong-types $
      erasure→zero-one-many-preserves-second-ΠΣ-quantities-𝟘-or-ω $
      Are-preserving-type-restrictions-no-type-restrictions (λ _ ())

    are-reflecting-type-restrictions :
      Are-reflecting-type-restrictions E₁.TR E₂.TR tr tr
    are-reflecting-type-restrictions =
      Are-reflecting-type-restrictions-no-erased-matches-TR (λ ()) $
      Are-reflecting-type-restrictions-no-erased-matches-TR (λ ()) $
      Are-reflecting-type-restrictions-no-strong-types (λ ()) $
      erasure→zero-one-many-reflects-second-ΠΣ-quantities-𝟘-or-ω $
      Are-reflecting-type-restrictions-no-type-restrictions
        (λ _ → inj₂ (λ ()))

    are-preserving-usage-restrictions :
      Are-preserving-usage-restrictions E₁.UR E₂.UR tr tr
    are-preserving-usage-restrictions =
      Are-preserving-usage-restrictions-only-some-erased-matches
        (λ _ → inj₁ ((λ ()) , (λ { {p = E.𝟘} refl → refl }))) $
      Are-preserving-usage-restrictions-no-usage-restrictions _

    are-reflecting-usage-restrictions :
      Are-reflecting-usage-restrictions E₁.UR E₂.UR tr tr
    are-reflecting-usage-restrictions =
      Are-reflecting-usage-restrictions-only-some-erased-matches
        (λ _ → (λ ()) , (λ { refl → refl })) $
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
      Are-preserving-type-restrictions-no-erased-matches-TR $
      Are-preserving-type-restrictions-no-strong-types $
      affine→linear-or-affine-preserves-second-ΠΣ-quantities-𝟘-or-ω $
      Are-preserving-type-restrictions-no-type-restrictions (λ _ ())

    are-reflecting-type-restrictions :
      Are-reflecting-type-restrictions E₁.TR E₂.TR tr tr
    are-reflecting-type-restrictions =
      Are-reflecting-type-restrictions-no-erased-matches-TR (λ ()) $
      Are-reflecting-type-restrictions-no-erased-matches-TR (λ ()) $
      Are-reflecting-type-restrictions-no-strong-types (λ ()) $
      affine→linear-or-affine-reflects-second-ΠΣ-quantities-𝟘-or-ω $
      Are-reflecting-type-restrictions-no-type-restrictions
        (λ _ → inj₂ (λ ()))

    are-preserving-usage-restrictions :
      Are-preserving-usage-restrictions E₁.UR E₂.UR tr tr
    are-preserving-usage-restrictions =
      Are-preserving-usage-restrictions-only-some-erased-matches
        (λ _ → inj₁ ((λ ()) , (λ { {p = A.𝟘} refl → refl }))) $
      Are-preserving-usage-restrictions-no-usage-restrictions _

    are-reflecting-usage-restrictions :
      Are-reflecting-usage-restrictions E₁.UR E₂.UR tr tr
    are-reflecting-usage-restrictions =
      Are-reflecting-usage-restrictions-only-some-erased-matches
        (λ _ → (λ ()) , (λ { refl → refl })) $
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
      Are-preserving-type-restrictions-no-erased-matches-TR $
      Are-preserving-type-restrictions-no-strong-types $
      linearity→linear-or-affine-preserves-second-ΠΣ-quantities-𝟘-or-ω $
      Are-preserving-type-restrictions-no-type-restrictions (λ _ ())

    are-reflecting-type-restrictions :
      Are-reflecting-type-restrictions E₁.TR E₂.TR tr tr
    are-reflecting-type-restrictions =
      Are-reflecting-type-restrictions-no-erased-matches-TR (λ ()) $
      Are-reflecting-type-restrictions-no-erased-matches-TR (λ ()) $
      Are-reflecting-type-restrictions-no-strong-types (λ ()) $
      linearity→linear-or-affine-reflects-second-ΠΣ-quantities-𝟘-or-ω $
      Are-reflecting-type-restrictions-no-type-restrictions
        (λ _ → inj₂ (λ ()))

    are-preserving-usage-restrictions :
      Are-preserving-usage-restrictions E₁.UR E₂.UR tr tr
    are-preserving-usage-restrictions =
      Are-preserving-usage-restrictions-only-some-erased-matches
        (λ _ → inj₁ ((λ ()) , (λ { {p = L.𝟘} refl → refl }))) $
      Are-preserving-usage-restrictions-no-usage-restrictions _

    are-reflecting-usage-restrictions :
      Are-reflecting-usage-restrictions E₁.UR E₂.UR tr tr
    are-reflecting-usage-restrictions =
      Are-reflecting-usage-restrictions-only-some-erased-matches
        (λ _ → (λ ()) , (λ { refl → refl })) $
      Are-reflecting-usage-restrictions-no-usage-restrictions
        _ (λ _ → inj₁ _)
