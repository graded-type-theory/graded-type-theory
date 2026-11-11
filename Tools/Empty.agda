------------------------------------------------------------------------
-- The empty type; also used as absurd proposition (``Falsity'').
------------------------------------------------------------------------

module Tools.Empty where

open import Data.Empty public

open import Tools.Relation
open import Tools.PropositionalEquality

private variable
  A B : Set _

-- The type ⊥ is a proposition.

⊥-propositional : Is-proposition ⊥
⊥-propositional {x = ()}

opaque

  -- If A is decided, then B → A follows from the contrapositive
  -- statement ¬ A → ¬ B.

  contrapositive→ : Dec A → (¬ A → ¬ B) → B → A
  contrapositive→ (yes x)  _   _ = x
  contrapositive→ (no not) hyp y = ⊥-elim (hyp not y)
