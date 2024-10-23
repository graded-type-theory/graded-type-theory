------------------------------------------------------------------------
-- Some examples related to the "bad" affine types modality
------------------------------------------------------------------------

open import Tools.Level

open import Definition.Typed.Restrictions

import Graded.Modality.Instances.Affine
open import Graded.Modality.Variant lzero
open import Graded.Usage.Restrictions

module Graded.Modality.Instances.Affine.Bad
  -- The modality variant.
  (variant : Modality-variant)
  (open Graded.Modality.Instances.Affine variant)
  (TR : Type-restrictions affineModality)
  (open Type-restrictions TR)
  (UR : Usage-restrictions affineModality)
  -- It is assumed that "Π 𝟙 , 𝟘" is allowed.
  (Π-𝟙-𝟘 : Π-allowed 𝟙 𝟘)
  where

open import Graded.Restrictions affineModality
open import Graded.Modality Affine
open import Graded.Usage.Restrictions.Natrec affineModality

private
  module M = Modality affineModality

  -- The "bad" nr function is used
  UR′ = nr-available-UR zero-one-many-greatest-star-nr UR
  open Usage-restrictions UR′
  instance
    has-nr : Has-nr M.semiring-with-meet
    has-nr = zero-one-many-greatest-star-nr
    nr-avail : Nr-available
    nr-avail = Natrec-mode-has-nr.Nr

open import Tools.Function
import Tools.Reasoning.PartialOrder

open import Graded.Context affineModality
open import Graded.Context.Properties affineModality
open import Graded.Modality Affine
open import Graded.Modality.Instances.Examples TR Π-𝟙-𝟘
open import Graded.Mode affineModality
open import Graded.Usage affineModality UR′

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
