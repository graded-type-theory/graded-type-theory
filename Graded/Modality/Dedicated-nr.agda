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

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation

private variable
  A : Set _

------------------------------------------------------------------------
-- Dedicated-nr

-- A wrapper type, intended to be used in the types of instance
-- arguments.

record Dedicated-nr : Set a where
  no-eta-equality
  pattern
  constructor dedicated-nr
  field
    nr : T nr-available

-- This wrapper type is propositional.

Dedicated-nr-propositional : (p q : Dedicated-nr) → p ≡ q
Dedicated-nr-propositional (dedicated-nr _) (dedicated-nr _) =
  cong dedicated-nr T-propositional

opaque

  -- A characterisation lemma for Dedicated-nr.

  Dedicated-nr⇔ : Dedicated-nr ⇔ T nr-available
  Dedicated-nr⇔ = Dedicated-nr.nr , dedicated-nr

------------------------------------------------------------------------
-- No-dedicated-nr

-- A wrapper type, intended to be used in the types of instance
-- arguments.

record No-dedicated-nr : Set a where
  no-eta-equality
  pattern
  constructor no-dedicated-nr
  field
    no-nr′ : T (not nr-available)

  -- A dedicated nr function is not available.

  no-nr : ¬ T nr-available
  no-nr = T-not⇔¬-T .proj₁ no-nr′

-- This wrapper type is propositional.

No-dedicated-nr-propositional : (p q : No-dedicated-nr) → p ≡ q
No-dedicated-nr-propositional (no-dedicated-nr _) (no-dedicated-nr _) =
  cong no-dedicated-nr T-propositional

------------------------------------------------------------------------
-- Some lemmas related to both Dedicated-nr and No-dedicated-nr

-- One cannot both have and not have a dedicated nr function.

not-nr-and-no-nr :
  ⦃ nr : Dedicated-nr ⦄ ⦃ no-nr : No-dedicated-nr ⦄ → ⊥
not-nr-and-no-nr ⦃ nr = dedicated-nr n ⦄ ⦃ no-nr = no-dedicated-nr nn ⦄
  with nr-available
… | true  = nn
… | false = n

-- The property of either having or not having a dedicated nr
-- function.

data Dedicated-nr? : Set a where
  does-have-nr     : ⦃ has-nr : Dedicated-nr ⦄ → Dedicated-nr?
  does-not-have-nr : ⦃ no-nr : No-dedicated-nr ⦄ → Dedicated-nr?

-- One either has or does not have a dedicated nr function.

dedicated-nr? : Dedicated-nr?
dedicated-nr? with nr-available in eq
… | false =
  does-not-have-nr
    ⦃ no-nr = no-dedicated-nr (subst (T ∘→ not) (sym eq) _) ⦄
… | true  =
  does-have-nr ⦃ has-nr = dedicated-nr (subst T (sym eq) _) ⦄
