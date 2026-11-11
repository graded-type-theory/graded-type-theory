------------------------------------------------------------------------
-- Soundness of the extraction function in the presence of certain
-- kinds of erased matches
------------------------------------------------------------------------

open import Configuration-types
import Configuration-types.Configuration.Zero-one
import Configuration-types.Type-configuration as TC
import Definition.Typed
import Definition.Untyped
open import Graded.Modality
open import Graded.Mode.Instances.Zero-one.Variant
import Graded.Mode.Instances.Zero-one
import Graded.Usage
open import Tools.Nat

module Graded.Erasure.Consequences.Soundness.Erased-matches
  {a} {M : Set a}
  (open Definition.Untyped M)
  {𝕄 : Modality M}
  (open Modality 𝕄)
  {variant : Mode-variant 𝕄}
  (open Graded.Mode.Instances.Zero-one variant)
  (open Configuration-types.Configuration.Zero-one 𝕄 variant)
  (C : Configuration Zero-one-isMode)
  (open Graded.Usage C)
  (open Configuration C)
  {kᵈ k : Nat}
  -- A definition context.
  (∇ : DCon (Term 0) kᵈ)
  -- A context.
  (Δ : Con Term k)
  -- Every definition in glassify ∇ is well-resourced.
  (well-resourced : ▸[ 𝟙ᵐ ] (glassify ∇))
  -- If erased matches are allowed for emptyrec when the mode is 𝟙ᵐ,
  -- then glassify ∇ and Δ are consistent with respect to a variant of
  -- the type system for which η-equality is allowed for weak unit
  -- types.
  (consistent :
     let open Definition.Typed (TC._with-η-for-Unitʷ 𝕄 TC) in
     Emptyrec-allowed 𝟙ᵐ 𝟘 →
     Consistent (glassify ∇ » Δ))
  -- Certain erased matches are not allowed.
  (only-some-erased-matches : Only-some-erased-matches)
  -- Equality reflection is not allowed or Δ is empty.
  ⦃ ok : No-equality-reflection or-empty Δ ⦄
  -- The modality's zero is well-behaved.
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M 𝕄 ⦄
  where

open import Tools.Bool
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Sum

import Definition.Typed.QuantityTranslation
open import Definition.Untyped.QuantityTranslation.Identity M false

open import Graded.Context 𝕄
open import Graded.Context.QuantityTranslation.Identity 𝕄
open import Graded.Modality.Morphism
open import Graded.Modality.Morphism.Configuration
open import Graded.Modality.Morphism.Configuration.Examples
open import Graded.Mode.Instances.Zero-one.QuantityTranslation.Primitive
import Graded.Usage.QuantityTranslation

import Graded.Erasure.Consequences.Soundness
open import Graded.Erasure.Extraction 𝕄
open import Graded.Erasure.LogicalRelation.Fundamental.Assumptions C
import Graded.Erasure.SucRed
import Graded.Erasure.Target as T

private variable
  Γ   : Cons _ _
  A t : Term _
  s   : Strength
  l   : Universe-level

-- A variant of the configuration for which η-equality is allowed for
-- weak unit types.

C-η : Configuration Zero-one-isMode
C-η = C with-η-for-Unitʷ

-- C is used by default.

open Definition.Typed (C .Configuration.TC)
open Graded.Erasure.SucRed (C .Configuration.TC)

-- The modules T-η and SR-η use C-η.

private
  module T-η  = Definition.Typed (C-η .Configuration.TC)
  module SR-η = Graded.Erasure.SucRed (C-η .Configuration.TC)

private

  -- Some lemmas used below.

  id-morphism : Is-morphism 𝕄 𝕄 idᶠ
  id-morphism = Is-order-embedding.tr-morphism Is-order-embedding-id

  id-Σ-morphism-C : Is-Σ-morphism-C false C C-η idᶠ idᶠ
  id-Σ-morphism-C = M-with-η-for-Unitʷʳ Is-Σ-morphism-C-id

-- Some modules used below.

private
  module U-η = Graded.Usage C-η

  module QTT = Definition.Typed.QuantityTranslation
    TC (C-η .Configuration.TC) false idᶠ idᶠ id-morphism
    (Is-morphism→Is-Σ-morphism id-morphism)
    (id-Σ-morphism-C .Is-Σ-morphism-C.is-Σ-morphism-TC)

  module QTU = Graded.Usage.QuantityTranslation.Is-morphism
    C C-η false idᶠ idᶠ id-morphism
    (Is-morphism→Is-Σ-morphism id-morphism)
    Are-mode-respecting-morphisms-id id-Σ-morphism-C

  module Soundness-η =
    Graded.Erasure.Consequences.Soundness.Soundness C-η
      (λ where
         .Fundamental-assumptions⁻.well-resourced →
           subst (U-η.▸[_]_ _) (Not-transparent.tr-DCon-id idᶠ) $
           QTU.tr-▸-DCon (λ ()) well-resourced
         .Fundamental-assumptions⁻.consistent →
           consistent
         .Fundamental-assumptions⁻.closed-or-no-erased-matches →
           inj₁ $
           Configuration.Only-some-erased-matches→No-erased-matches
             C-η _ only-some-erased-matches
         .Fundamental-assumptions⁻.no-equality-reflection-or-empty →
           Type-configuration.No-equality-reflection-or-empty⇔
             (C-η .Configuration.TC) .proj₂ $
           No-equality-reflection-or-empty⇔ .proj₁ $
           ok)

opaque

  -- The relation _⊢_∷_ is contained in T-η._⊢_∷_.

  ⊢∷→⊢∷-η : Γ ⊢ t ∷ A → Γ T-η.⊢ t ∷ A
  ⊢∷→⊢∷-η ⊢t =
    subst₃ T-η._⊢_∷_ (Not-transparent.tr-Cons-id idᶠ) tr-Term-id
      tr-Term-id $
    QTT.tr-⊢∷ ⊢t

opaque

  -- Soundness of erasure for natural numbers.
  --
  -- Note that SR-η._⊢_⇒ˢ*_∷ℕ is used in the statement of this
  -- theorem. This reduction relation uses the rule unitrec-β-η rather
  -- than unitrec-subst and unitrec-β.

  soundness-ℕ :
    ∇ » Δ ⊢ t ∷ ℕ → 𝟘ᶜ ▸[ 𝟙ᵐ ] t →
    ∃ λ n →
    glassify ∇ » Δ SR-η.⊢ t ⇒ˢ* sucⁿ n ∷ℕ ×
    (∀ str → eraseDCon str ∇ ⊢ erase str t ⇒ˢ⟨ str ⟩* T.sucⁿ n)
  soundness-ℕ ⊢t ▸t =
    Soundness-η.soundness-ℕ (⊢∷→⊢∷-η ⊢t)
      (subst₃ (U-η._▸[_]_) tr-Conₘ-id refl tr-Term-id $
       QTU.tr-▸ ▸t)

opaque

  -- Soundness of erasure for unit types.
  --
  -- Note that T-η._⊢_⇒*_∷_ is used in the statement of this theorem.
  -- This reduction relation uses the rule unitrec-β-η rather than
  -- unitrec-subst and unitrec-β.

  soundness-Unit :
    ∇ » Δ ⊢ t ∷ Unit s → 𝟘ᶜ ▸[ 𝟙ᵐ ] t →
    glassify ∇ » Δ T-η.⊢ t ⇒* star s ∷ Unit s ×
    (∀ str → eraseDCon str ∇ T.⊢ erase str t ⇒* T.star)
  soundness-Unit ⊢t ▸t =
    Soundness-η.soundness-Unit (⊢∷→⊢∷-η ⊢t)
      (subst₃ (U-η._▸[_]_) tr-Conₘ-id refl tr-Term-id $
       QTU.tr-▸ ▸t)
