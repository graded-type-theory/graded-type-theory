------------------------------------------------------------------------
-- "Extra" restrictions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Tools.Relation

module Definition.Modality.Restrictions {a ℓ} (M′ : Setoid a ℓ) where

open Setoid M′ renaming (Carrier to M)

open import Tools.Level
open import Tools.Unit

-- "Extra" restrictions related to usage.

record Restrictions : Set (lsuc (a ⊔ ℓ)) where
  field
    -- The prodrec constructor's quantity has to satisfy this
    -- predicate.
    Prodrec : (p : M) → Set (a ⊔ ℓ)

    -- The predicate Prodrec respects equivalence.
    Prodrec-resp : ∀ {p p′} → p ≈ p′ → Prodrec p → Prodrec p′

-- No restrictions.

no-restrictions : Restrictions
no-restrictions = record
  { Prodrec = λ _ → Lift _ ⊤
  }
