------------------------------------------------------------------------
-- Vectors
------------------------------------------------------------------------

module Tools.Vec where

open import Data.Vec.Base public
  using (Vec; _∷_; tail; zipWith; replicate) renaming ([] to ε)
