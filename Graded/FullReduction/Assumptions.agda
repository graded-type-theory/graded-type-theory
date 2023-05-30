------------------------------------------------------------------------
-- Assumptions used to state the theorems in
-- Definition.Modality.FullReduction
------------------------------------------------------------------------

open import Graded.Modality
open import Definition.Typed.Restrictions

module Graded.FullReduction.Assumptions
  {a} {M : Set a}
  (𝕄 : Modality M)
  (R : Type-restrictions M)
  where

open Modality 𝕄
open Type-restrictions R

open import Graded.Mode 𝕄

open import Tools.PropositionalEquality

private variable
  p q r : M

-- The theorems in Definition.Modality.FullReduction are proved under
-- the assumption that the following property holds.

record Full-reduction-assumptions : Set a where
  no-eta-equality
  field
    -- If the unit type (with η-equality) is used (in certain ways),
    -- then 𝟘 must be the largest quantity.
    ≤𝟘 : Unit-restriction → p ≤ 𝟘

    -- If a Σ-type with η-equality and the "first component quantity" p
    -- is used (in certain ways), then p ·_ must be increasing.
    ·-increasing : Σₚ-restriction p q → r ≤ p · r

    -- If a Σ-type with η-equality and the "first component quantity" p
    -- is used (in certain ways), and ⌞ p ⌟ is 𝟙ᵐ, then p ≤ 𝟙 must hold.
    ⌞⌟≡𝟙ᵐ→≤𝟙 : Σₚ-restriction p q → ⌞ p ⌟ ≡ 𝟙ᵐ → p ≤ 𝟙
