------------------------------------------------------------------------
-- The booleans
------------------------------------------------------------------------

module Tools.Bool where

open import Data.Bool.Base
  using (Bool; true; false; not; _∧_; _∨_; if_then_else_; T)
  public

open import Tools.Function
open import Tools.Relation
open import Tools.Product
open import Tools.PropositionalEquality

private variable
  b : Bool

-- The function T is pointwise propositional.

T-propositional : {x y : T b} → x ≡ y
T-propositional {b = true} = refl

-- T (not b) is logically equivalent to ¬ T b.

T-not⇔¬-T : T (not b) ⇔ (¬ T b)
T-not⇔¬-T {b = false} = (λ { _ → idᶠ }) , _
T-not⇔¬-T {b = true}  = (λ ()) , (_$ _)
