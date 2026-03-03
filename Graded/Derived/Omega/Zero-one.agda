------------------------------------------------------------------------
-- Properties related to usage, ω and Ω for the Zero-one mode structure
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode.Instances.Zero-one.Variant
import Graded.Mode.Instances.Zero-one
open import Graded.Usage.Restrictions

module Graded.Derived.Omega.Zero-one
  {a} {M : Set a}
  {𝕄 : Modality M}
  {mode-variant : Mode-variant 𝕄}
  (open Graded.Mode.Instances.Zero-one mode-variant)
  (UR : Usage-restrictions 𝕄 Zero-one-isMode)
  where

open Modality 𝕄 hiding (ω)

open import Graded.Context 𝕄
import Graded.Derived.Omega UR as O
open import Graded.Usage UR

open import Definition.Untyped.Omega M

open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder

private variable
  n : Nat
  m : Mode
  p : M

opaque
  unfolding ω

  -- A usage lemma for ω.

  ▸ω :
    (m ≡ 𝟙ᵐ → p ≤ 𝟙 + p) →
    𝟘ᶜ ▸[ m ] ω {n = n} p
  ▸ω hyp = O.▸ω (hyp ∘→ ⌜⌝≢𝟘→≡𝟙ᵐ)

opaque
  unfolding Ω

  -- A usage lemma for Ω.

  ▸Ω :
    (m ≡ 𝟙ᵐ → p ≤ 𝟙 + p) →
    𝟘ᶜ ▸[ m ] Ω {n = n} p
  ▸Ω hyp = O.▸Ω (hyp ∘→ ⌜⌝≢𝟘→≡𝟙ᵐ)
