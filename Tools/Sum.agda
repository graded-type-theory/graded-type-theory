------------------------------------------------------------------------
-- Disjoint sum type; also used as logical disjunction.
------------------------------------------------------------------------

module Tools.Sum where

open import Data.Sum.Base public using (_⊎_; inj₁; inj₂; map; [_,_])
open import Relation.Nullary.Decidable public
  using (_⊎-dec_)

-- Idempotency.

idem : ∀ {a} {A : Set a} → A ⊎ A → A
idem (inj₁ x) = x
idem (inj₂ x) = x

-- Commutativity.

comm : ∀ {a b} {A : Set a} {B : Set b} → A ⊎ B → B ⊎ A
comm (inj₁ x) = inj₂ x
comm (inj₂ x) = inj₁ x
