------------------------------------------------------------------------
-- Some examples related to an "affine types" modality without a
-- dedicated nr function
------------------------------------------------------------------------

open import Tools.Level

open import Definition.Typed.Restrictions

import Graded.Modality.Dedicated-nr
import Graded.Modality.Instances.Affine
open import Graded.Modality.Variant lzero
open import Graded.Usage.Restrictions

module Graded.Modality.Instances.Affine.Bad.No-dedicated-nr
  -- The modality variant.
  (variant : Modality-variant)
  (open Graded.Modality.Instances.Affine variant)
  (open Graded.Modality.Dedicated-nr affineModality)
  (TR : Type-restrictions affineModality)
  (open Type-restrictions TR)
  (UR : Usage-restrictions Affine)
  -- It is assumed that "Π 𝟙 , 𝟘" is allowed.
  (Π-𝟙-𝟘 : Π-allowed 𝟙 𝟘)
  -- There is no dedicated nr function.
  ⦃ no-nr : No-dedicated-nr ⦄
  where

open import Tools.Function
import Tools.Reasoning.PartialOrder

open import Graded.Context affineModality
open import Graded.Context.Properties affineModality
open import Graded.Modality Affine
open import Graded.Modality.Instances.Examples TR Π-𝟙-𝟘
open import Graded.Mode affineModality
open import Graded.Usage affineModality UR

private
  module M = Modality affineModality

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
