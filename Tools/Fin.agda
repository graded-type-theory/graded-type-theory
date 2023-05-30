------------------------------------------------------------------------
-- Finite sets
------------------------------------------------------------------------

module Tools.Fin where

open import Data.Fin.Properties using () renaming (_≟_ to _≟ⱽ_) public
open import Data.Fin.Base using (Fin) renaming (zero to x0 ; suc to _+1) public

open import Tools.Nat

private variable
  n : Nat

-- One.

x1 : Fin (2 + n)
x1 = x0 +1
