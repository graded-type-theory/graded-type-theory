------------------------------------------------------------------------
-- Some examples related to the "bad" affine types modality
------------------------------------------------------------------------

open import Tools.Level

open import Definition.Typed.Restrictions

import Graded.Modality.Dedicated-nr
import Graded.Modality.Instances.Affine
open import Graded.Modality.Variant lzero
open import Graded.Usage.Restrictions

module Graded.Modality.Instances.Affine.Bad
  -- The modality variant.
  (variant : Modality-variant)
  (open Graded.Modality.Instances.Affine variant)
  (open Graded.Modality.Dedicated-nr bad-affine-modality)
  (TR : Type-restrictions bad-affine-modality)
  (open Type-restrictions TR)
  (UR : Usage-restrictions bad-affine-modality)
  -- It is assumed that "Π 𝟙 , 𝟘" is allowed.
  (Π-𝟙-𝟘 : Π-allowed 𝟙 𝟘)
  -- There is a dedicated nr function.
  ⦃ has-nr : Dedicated-nr ⦄
  where

open import Tools.Function
import Tools.Reasoning.PartialOrder

open import Graded.Context bad-affine-modality
open import Graded.Context.Properties bad-affine-modality
open import Graded.Modality Affine
open import Graded.Modality.Instances.Examples TR Π-𝟙-𝟘
open import Graded.Mode bad-affine-modality
open import Graded.Usage bad-affine-modality UR

private
  module M = Modality bad-affine-modality

-- The term double is well-resourced (even though it can be given the
-- type Π 𝟙 , 𝟘 ▷ ℕ ▹ ℕ).

▸double : ε ▸[ 𝟙ᵐ ] double
▸double =
  lamₘ $
  natrecₘ var (sucₘ var) var $
  sub ℕₘ $ begin
    𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ M.·-zeroʳ _ ⟩
    𝟘ᶜ                ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- The term plus is well-resourced.

▸plus : ε ▸[ 𝟙ᵐ ] plus
▸plus =
  lamₘ $
  lamₘ $
  natrecₘ var (sucₘ var) var $
  sub ℕₘ $ begin
    𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ M.·-zeroʳ _ ⟩
    𝟘ᶜ                ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
