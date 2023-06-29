------------------------------------------------------------------------
-- Restrictions on typing derivations
------------------------------------------------------------------------

module Definition.Typed.Restrictions
  {a} (M : Set a)
  where

open import Definition.Untyped M

open import Tools.Function
open import Tools.Level
open import Tools.Unit

-- Restrictions on typing derivations.

record Type-restrictions : Set (lsuc a) where
  no-eta-equality
  field
    -- Unit types (with η-equality) are only allowed if the given
    -- predicate holds.
    Unit-allowed : Set a

    -- Restrictions imposed upon Π- and Σ-types.
    ΠΣ-allowed : BinderMode → (p q : M) → Set a

  -- Restrictions imposed upon Π-types.

  Π-allowed : M → M → Set a
  Π-allowed = ΠΣ-allowed BMΠ

  -- Restrictions imposed upon Σ-types.

  Σ-allowed : SigmaMode → M → M → Set a
  Σ-allowed = ΠΣ-allowed ∘→ BMΣ

  -- Restrictions imposed upon Σ-types with η-equality.

  Σₚ-allowed : M → M → Set a
  Σₚ-allowed = Σ-allowed Σₚ

  -- Restrictions imposed upon Σ-types without η-equality.

  Σᵣ-allowed : M → M → Set a
  Σᵣ-allowed = Σ-allowed Σᵣ

  -- A variant of ΠΣ-allowed for BindingType.

  BindingType-allowed : BindingType → Set a
  BindingType-allowed (BM b p q) = ΠΣ-allowed b p q

open Type-restrictions
