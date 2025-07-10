------------------------------------------------------------------------
-- Some examples related to an "affine types" modality without a
-- dedicated nr function
------------------------------------------------------------------------

open import Tools.Level

import Graded.Modality.Instances.Affine
open import Graded.Modality.Variant lzero
open import Graded.Usage.Restrictions

module Graded.Modality.Instances.Affine.Examples.Bad.No-nr
  -- The modality variant.
  (variant : Modality-variant)
  (open Graded.Modality.Instances.Affine variant)
  (UR : Usage-restrictions affineModality)
  (open Usage-restrictions UR)
  -- There is no dedicated nr function.
  ⦃ no-nr : Nr-not-available ⦄
  where

open import Tools.Function
import Tools.Reasoning.PartialOrder

open import Graded.Context affineModality
open import Graded.Context.Properties affineModality
open import Graded.Modality Affine
open import Graded.Mode affineModality
open import Graded.Usage affineModality UR

open import Definition.Untyped.Nat affineModality

private
  module M = Modality affineModality

opaque

  -- The term double is well-resourced (even though it can be given the
  -- type Π 𝟙 , 𝟘 ▷ ℕ ▹ ℕ).

  ▸double : ε ▸[ 𝟙ᵐ ] double
  ▸double =
    lamₘ $
    natrec-no-nrₘ var (sucₘ var) var
      (sub ℕₘ $ begin
         𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ M.·-zeroʳ _ ⟩
         𝟘ᶜ                ∎)
      ≤ᶜ-refl
      (λ _ → ≤ᶜ-refl)
      ≤ᶜ-refl
      ≤ᶜ-refl
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

opaque

  -- The term plus is well-resourced.

  ▸plus : ε ▸[ 𝟙ᵐ ] plus
  ▸plus =
    lamₘ $
    lamₘ $
    natrec-no-nrₘ var (sucₘ var) var
      (sub ℕₘ $ begin
         𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ M.·-zeroʳ _ ⟩
         𝟘ᶜ                ∎)
      ≤ᶜ-refl
      (λ _ → ≤ᶜ-refl)
      ≤ᶜ-refl
      ≤ᶜ-refl
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset
