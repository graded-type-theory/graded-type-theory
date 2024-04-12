------------------------------------------------------------------------
-- Disjoint sum type; also used as logical disjunction.
------------------------------------------------------------------------

module Tools.Sum where

open import Data.Sum.Base public using (_⊎_; inj₁; inj₂; map; [_,_])

-- Idempotency.

id : ∀ {a} {A : Set a} → A ⊎ A → A
id (inj₁ x) = x
id (inj₂ x) = x

-- Symmetry.

sym : ∀ {a b} {A : Set a} {B : Set b} → A ⊎ B → B ⊎ A
sym (inj₁ x) = inj₂ x
sym (inj₂ x) = inj₁ x
