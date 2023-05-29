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
    -- Restrictions imposed upon unit types (with η-equality).
    Unit-restriction : Set a

    -- Restrictions imposed upon Π- and Σ-types.
    ΠΣ-restriction : BinderMode → (p q : M) → Set a

  -- Restrictions imposed upon Π-types.

  Π-restriction : M → M → Set a
  Π-restriction = ΠΣ-restriction BMΠ

  -- Restrictions imposed upon Σ-types.

  Σ-restriction : SigmaMode → M → M → Set a
  Σ-restriction = ΠΣ-restriction ∘→ BMΣ

  -- Restrictions imposed upon Σ-types with η-equality.

  Σₚ-restriction : M → M → Set a
  Σₚ-restriction = Σ-restriction Σₚ

  -- Restrictions imposed upon Σ-types without η-equality.

  Σᵣ-restriction : M → M → Set a
  Σᵣ-restriction = Σ-restriction Σᵣ

  -- A variant of ΠΣ-restriction for BindingType.

  BindingType-restriction : BindingType → Set a
  BindingType-restriction (BM b p q) = ΠΣ-restriction b p q

open Type-restrictions
