------------------------------------------------------------------------
-- Restrictions on typing derivations
------------------------------------------------------------------------

module Definition.Typed.Restrictions
  {a} (M : Set a)
  where

open import Definition.Untyped M

open import Tools.Level
open import Tools.Unit

-- Restrictions on typing derivations.

record Type-restrictions : Set (lsuc a) where
  no-eta-equality
  field
    -- Restrictions imposed upon unit types (with η-equality).
    Unit-restriction : Set a

    -- Restrictions imposed upon Σ-types with η-equality. The
    -- argument is the annotation of the Σ-type's first component.
    Σₚ-restriction : M → Set a

  -- Restrictions imposed upon Σ-types. No restrictions are imposed
  -- upon Σ-types without η-equality.

  Σ-restriction : SigmaMode → M → Set a
  Σ-restriction = λ where
    Σₚ → Σₚ-restriction
    Σᵣ → λ _ → Lift _ ⊤

  -- Restrictions imposed upon Π- and Σ-types. No restrictions are
  -- imposed upon Π-types or Σ-types without η-equality.

  ΠΣ-restriction : BinderMode → M → Set a
  ΠΣ-restriction = λ where
    BMΠ     → λ _ → Lift _ ⊤
    (BMΣ s) → Σ-restriction s

  -- A variant of ΠΣ-restriction for BindingType.

  BindingType-restriction : BindingType → Set a
  BindingType-restriction (BM b p _) = ΠΣ-restriction b p

open Type-restrictions

-- No restrictions.

no-restrictions : Type-restrictions
no-restrictions = λ where
  .Unit-restriction → Lift _ ⊤
  .Σₚ-restriction   → λ _ → Lift _ ⊤
