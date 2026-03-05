------------------------------------------------------------------------
-- Vectors
------------------------------------------------------------------------

module Tools.Vec where

open import Data.Vec.Base public
  using (Vec; _∷_; _++_; tail; lookup; zipWith; replicate)
  renaming ([] to ε)
