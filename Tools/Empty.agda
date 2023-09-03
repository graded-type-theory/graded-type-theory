------------------------------------------------------------------------
-- The empty type; also used as absurd proposition (``Falsity'').
------------------------------------------------------------------------

module Tools.Empty where

open import Data.Empty public

open import Tools.PropositionalEquality

-- The type ⊥ is a proposition.

⊥-propositional : Is-proposition ⊥
⊥-propositional {x = ()}
