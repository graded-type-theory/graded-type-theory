------------------------------------------------------------------------
-- Derived typing rules
------------------------------------------------------------------------

open import Definition.Typed.Restrictions

module Definition.Typed.Consequences.DerivedRules
  {a} {M : Set a}
  (R : Type-restrictions M)
  where

open import Definition.Typed R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Properties R
open import Definition.Untyped M hiding (_∷_)

open import Definition.Typed.Consequences.DerivedRules.Nat R public
open import Definition.Typed.Consequences.DerivedRules.Pi R public
open import Definition.Typed.Consequences.DerivedRules.Pi-Sigma R public
open import Definition.Typed.Consequences.DerivedRules.Sigma R public

private variable
  Γ : Con Term _
  t : Term _

-- An η-rule for the Unit type.

Unit-η :
  Γ ⊢ t ∷ Unit →
  Γ ⊢ star ≡ t ∷ Unit
Unit-η ⊢t = η-unit
  (starⱼ (wfTerm ⊢t) (⊢∷Unit→Unit-allowed ⊢t))
  ⊢t
