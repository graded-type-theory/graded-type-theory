------------------------------------------------------------------------
-- Some examples related to the affine types modality with a "bad" nr
-- function.
------------------------------------------------------------------------

open import Tools.Level

import Graded.Modality.Instances.Affine
open import Graded.Modality.Variant lzero
open import Graded.Usage.Restrictions

module Graded.Modality.Instances.Affine.Examples.Bad.Nr
  -- The modality variant.
  (variant : Modality-variant)
  (open Graded.Modality.Instances.Affine variant)
  (UR : Usage-restrictions affineModality)
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
    has-nr : Nr-available
    has-nr = Natrec-mode-has-nr.Nr ⦃ zero-one-many-greatest-star-nr ⦄

open import Tools.Function
import Tools.Reasoning.PartialOrder

open import Graded.Context affineModality
open import Graded.Context.Properties affineModality
open import Graded.Mode affineModality
open import Graded.Usage affineModality UR′

open import Definition.Untyped.Nat affineModality

opaque

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

opaque

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
