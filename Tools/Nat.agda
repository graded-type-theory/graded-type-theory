-- The natural numbers.

module Tools.Nat where

-- We reexport Agda's built-in type of natural numbers.

open import Agda.Builtin.Nat using (Nat; _+_) public
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Nat.Show using (show) public

pattern 1+ n = suc n
