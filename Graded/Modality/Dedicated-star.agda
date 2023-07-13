------------------------------------------------------------------------
-- The types Dedicated-star and No-dedicated-star
------------------------------------------------------------------------

import Graded.Modality

module Graded.Modality.Dedicated-star
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  where

open Modality 𝕄

open import Tools.Empty
open import Tools.Nullary
open import Tools.PropositionalEquality

private variable
  A : Set _

------------------------------------------------------------------------
-- Dedicated-star

-- A wrapper type, intended to be used in the types of instance
-- arguments.

record Dedicated-star : Set a where
  constructor dedicated-star
  field
    star : ⊛-available

-- This wrapper type is propositional.

Dedicated-star-propositional : (p q : Dedicated-star) → p ≡ q
Dedicated-star-propositional (dedicated-star s₁) (dedicated-star s₂) =
  cong dedicated-star (⊛-available-propositional s₁ s₂)

------------------------------------------------------------------------
-- No-dedicated-star

-- A wrapper type, intended to be used in the types of instance
-- arguments.

record No-dedicated-star : Set a where
  constructor no-dedicated-star
  field
    no-star : ¬ ⊛-available

------------------------------------------------------------------------
-- Dedicated-star and No-dedicated-star are mutually exclusive

-- One cannot both have and not have a dedicated natrec-star operator.

not-star-and-no-star :
  ⦃ star : Dedicated-star ⦄ ⦃ no-star : No-dedicated-star ⦄ → ⊥
not-star-and-no-star
  ⦃ star = dedicated-star s ⦄ ⦃ no-star = no-dedicated-star ns ⦄ =
  ns s
