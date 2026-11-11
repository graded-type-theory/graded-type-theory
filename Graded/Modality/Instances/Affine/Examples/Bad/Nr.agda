------------------------------------------------------------------------
-- Some examples related to the affine types modality with a "bad" nr
-- function.
------------------------------------------------------------------------

open import Configuration-types
open import Graded.Modality.Instances.Affine
import Graded.Mode.Instances.Zero-one
open import Graded.Mode.Instances.Zero-one.Variant affineModality

module Graded.Modality.Instances.Affine.Examples.Bad.Nr
  {variant : Mode-variant}
  (open Graded.Mode.Instances.Zero-one variant)
  (C : Configuration Zero-one-isMode)
  where

open import Configuration-types.Configuration.Zero-one
  affineModality variant
open import Configuration-types.Natrec affineModality

open import Graded.Modality Affine
open import Graded.Mode Mode affineModality

private
  module M = Modality affineModality

  -- The "bad" nr function is used
  C′ = nr-available zero-one-many-greatest-star-nr C
  open Configuration C′
  instance
    has-nr : Nr-available
    has-nr = Natrec-mode-has-nr.Nr ⦃ zero-one-many-greatest-star-nr ⦄

open import Tools.Function
import Tools.Reasoning.PartialOrder

open import Graded.Context affineModality
open import Graded.Context.Properties affineModality
open import Graded.Usage C′

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
