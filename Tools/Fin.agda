------------------------------------------------------------------------
-- Finite sets
------------------------------------------------------------------------

module Tools.Fin where

open import Data.Fin.Properties using () renaming (_≟_ to _≟ⱽ_) public
open import Data.Fin.Base using (Fin) renaming (zero to x0 ; suc to _+1) public
