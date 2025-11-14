------------------------------------------------------------------------
-- Universe levels
------------------------------------------------------------------------

module Tools.Level where

open import Agda.Primitive public using (lzero; lsuc; Level; _⊔_)
open import Relation.Nullary

ℓ₀ = lzero

open import Level public using (Lift; lift)

private variable
  b : Level
  A : Set _

-- If A is decided, then Lift b A is decided.

Lift? : Dec A → Dec (Lift b A)
Lift? (yes A) = yes (lift A)
Lift? (no ¬A) = no (λ { (lift A) → ¬A A })
