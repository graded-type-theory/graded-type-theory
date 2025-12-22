------------------------------------------------------------------------
-- The Maybe type
------------------------------------------------------------------------

module Tools.Maybe where

open import Data.Maybe public
  using (Maybe; just; nothing; _<∣>_)
  renaming (map to infixl 3 _<$>_; ap to infixl 3 _⊛_)
open import Relation.Nullary.Decidable public
  using (dec⇒maybe)
