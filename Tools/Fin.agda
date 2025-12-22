------------------------------------------------------------------------
-- Finite sets
------------------------------------------------------------------------

module Tools.Fin where

open import Data.Fin.Properties public
  using (suc-injective) renaming (_≟_ to _≟ⱽ_)
open import Data.Fin.Base public
  using (Fin; toℕ; compare; Ordering)
  renaming (zero to x0; suc to _+1)
open Ordering public

open import Tools.Nat

private variable
  n : Nat

pattern _+2 x = x +1 +1

pattern x1  = x0  +1
pattern x2  = x1  +1
pattern x3  = x2  +1
pattern x4  = x3  +1
pattern x5  = x4  +1
pattern x6  = x5  +1
pattern x7  = x6  +1
pattern x8  = x7  +1
pattern x9  = x8  +1
pattern x10 = x9  +1
pattern x11 = x10 +1

pattern not-x1  = () +1
pattern not-x2  = () +1 +1
pattern not-x3  = () +1 +1 +1
pattern not-x4  = () +1 +1 +1 +1
pattern not-x5  = () +1 +1 +1 +1 +1
pattern not-x6  = () +1 +1 +1 +1 +1 +1
pattern not-x7  = () +1 +1 +1 +1 +1 +1 +1
pattern not-x8  = () +1 +1 +1 +1 +1 +1 +1 +1
pattern not-x9  = () +1 +1 +1 +1 +1 +1 +1 +1 +1
pattern not-x10 = () +1 +1 +1 +1 +1 +1 +1 +1 +1 +1
pattern not-x11 = () +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1
pattern not-x12 = () +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1
