------------------------------------------------------------------------
-- Some examples related to an "affine types" modality without a
-- dedicated nr function
------------------------------------------------------------------------

open import Graded.Modality.Instances.Affine
open import Graded.Usage.Restrictions
open import Graded.Mode
import Graded.Mode.Instances.Zero-one
open import Graded.Mode.Instances.Zero-one.Variant affineModality

module Graded.Modality.Instances.Affine.Examples.Bad.No-nr
  {variant : Mode-variant}
  (open Graded.Mode.Instances.Zero-one variant)
  (UR : Usage-restrictions affineModality Zero-one-isMode)
  (open Usage-restrictions UR)
  -- There is no dedicated nr function.
  ⦃ no-nr : Nr-not-available ⦄
  where

open import Tools.Function
import Tools.Reasoning.PartialOrder

open import Graded.Context affineModality
open import Graded.Context.Properties affineModality
open import Graded.Modality Affine
open import Graded.Usage UR

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
      (λ _ → ≤ᶜ-refl)
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
      (λ _ → ≤ᶜ-refl)
      ≤ᶜ-refl
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset
