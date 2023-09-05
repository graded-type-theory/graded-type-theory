------------------------------------------------------------------------
-- The types Dedicated-nr and No-dedicated-nr
------------------------------------------------------------------------

import Graded.Modality

module Graded.Modality.Dedicated-nr
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  where

open Modality 𝕄

open import Tools.Empty
open import Tools.Function
open import Tools.Nullary
open import Tools.PropositionalEquality

private variable
  A : Set _

------------------------------------------------------------------------
-- Dedicated-nr

-- A wrapper type, intended to be used in the types of instance
-- arguments.

record Dedicated-nr : Set a where
  constructor dedicated-nr
  field
    nr : Nr-available

-- This wrapper type is propositional.

Dedicated-nr-propositional : (p q : Dedicated-nr) → p ≡ q
Dedicated-nr-propositional (dedicated-nr n₁) (dedicated-nr n₂) =
  cong dedicated-nr (Nr-available-propositional n₁ n₂)

------------------------------------------------------------------------
-- No-dedicated-nr

-- A wrapper type, intended to be used in the types of instance
-- arguments.

record No-dedicated-nr : Set a where
  constructor no-dedicated-nr
  field
    no-nr : ¬ Nr-available

------------------------------------------------------------------------
-- Some lemmas related to both Dedicated-nr and No-dedicated-nr

-- One cannot both have and not have a dedicated nr function.

not-nr-and-no-nr :
  ⦃ nr : Dedicated-nr ⦄ ⦃ no-nr : No-dedicated-nr ⦄ → ⊥
not-nr-and-no-nr
  ⦃ nr = dedicated-nr n ⦄ ⦃ no-nr = no-dedicated-nr nn ⦄ =
  nn n

-- The property of either having or not having a dedicated nr
-- function.

data Dedicated-nr? : Set a where
  does-have-nr     : ⦃ has-nr : Dedicated-nr ⦄ → Dedicated-nr?
  does-not-have-nr : ⦃ no-nr : No-dedicated-nr ⦄ → Dedicated-nr?

-- One either has or does not have a dedicated nr function.

dedicated-nr? : Dedicated-nr?
dedicated-nr? = case Nr-available-decided of λ where
  (yes has-nr) → does-have-nr ⦃ has-nr = dedicated-nr has-nr ⦄
  (no no-nr)   →
    does-not-have-nr ⦃ no-nr = no-dedicated-nr no-nr ⦄
