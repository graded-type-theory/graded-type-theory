------------------------------------------------------------------------
-- An extended erasure modality
------------------------------------------------------------------------

-- The formalisation contains a number of parameters. This example
-- shows that it is possible to instantiate all of the parameters at
-- the same time.

module Graded.Modality.Extended.K-not-allowed.Some-erased-matches where

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
-- An extended modality

-- The following extended modality satisfies the following properties:
--
-- * There are no restrictions on prodrec, unitrec or emptyrec.
-- * Strong unit types are not allowed to be used as sinks.
-- * Id-erased is not inhabited.
-- * Some erased matches are allowed for J and K when the mode is 𝟙ᵐ,
--   and all erased matches are allowed for J and K when the mode
--   is 𝟘ᵐ.
-- * Eta-equality is not allowed for weak types.
-- * Strong and weak unit types are allowed.
-- * Π-types and strong and weak Σ-types are allowed exactly when the
--   following conditions are satisfied:
--   * Whenever the "first grades" are ω, then the second grades
--     are ω.
--   * Whenever the first grades are not ω, then the second grades
--     are 𝟘.
-- * The K rule is not allowed.
-- * []-cong is allowed.
-- * Opaque definitions are allowed.
-- * Equality reflection is not allowed.
-- * Level is small.
-- * Omega-plus-allowed is inhabited.
-- * Quotients are allowed. The motive of qrec is not treated as
--   erased.
-- * 𝟘ᵐ is allowed.

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
  ¬ Unitʷ-η ×
  (∀ {s} → Unit-allowed s) ×
  (∀ {b p q} → ΠΣ-allowed b p q ⇔ ((p ≡ ω → q ≡ ω) × (p ≢ ω → q ≡ 𝟘))) ×
  ¬ K-allowed ×
  (∀ {s} → []-cong-allowed s) ×
  (∀ {s m} → []-cong-allowed-mode s m) ×
  Opacity-allowed ×
  ¬ Equality-reflection ×
  Level-is-small ×
  Omega-plus-allowed ×
  Quot-allowed ×
  ¬ Qrec-motive-erased ×
  T 𝟘ᵐ-allowed
  where
  open Extended-modality M
  open Mode-variant MV

private

  -- Functions used to construct the modality below.

  C′ :
    {M : Set} {𝕄 : Modality M}
    {v : Mode-variant 𝕄} →
    ⦃ ok : Has-omega M 𝕄 ⦄ →
    Has-nr M 𝕄 →
    Configuration (Zero-one-isMode v)
  C′ has-nr =
    not-all-erased-matches-JK _ _ $
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
      Assumptions-not-all-erased-matches-JK _ _ ∘→
      Assumptions-second-ΠΣ-quantities-𝟘-or-ω _ _ ∘→
      Assumptions-no-restrictions _ _ {omega = with-ω}
        ⦃ Nr ⦃ Nr ⦃ has-nr ⦄ ⦄ ⦄

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
    .HAS-ω   → with-ω
    .NR₀ {z} → EP.nr-linearity-like-for-𝟘 {z = z}
    .NR₁ {z} → EP.nr-linearity-like-for-𝟙 {z = z}
    .SUB     → EP.supports-subtraction
  where
  open Extended-modality

opaque
  unfolding Trivialᵐ′ trivialᵐ? 𝟘ᵐ?

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
    , (λ ())
    , _
    , (proj₂ , (_ ,_))
    , (λ ())
    , (λ ())
    , (λ ())
    , lift (λ ())
    , Lift.lower
    , Level-is-small⇔ .proj₂ refl
    , _
    , ((λ ()) , with-ω)
    , (λ ())
    , _
    where
    open Extended-modality Erasure
