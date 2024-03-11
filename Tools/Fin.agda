------------------------------------------------------------------------
-- Finite sets
------------------------------------------------------------------------

module Tools.Fin where

open import Data.Fin.Properties public
  using (suc-injective) renaming (_≟_ to _≟ⱽ_)
open import Data.Fin.Base using (Fin) renaming (zero to x0 ; suc to _+1) public

open import Tools.Nat

private variable
  n : Nat

pattern _+2 x = x +1 +1

-- One.

x1 : Fin (2 + n)
x1 = x0 +1

-- Two.

x2 : Fin (3 + n)
x2 = x1 +1

-- Three.

x3 : Fin (4 + n)
x3 = x2 +1

-- Four.

x4 : Fin (5 + n)
x4 = x3 +1

-- Five.

x5 : Fin (6 + n)
x5 = x4 +1

-- Six.

x6 : Fin (7 + n)
x6 = x5 +1
