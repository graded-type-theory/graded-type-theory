------------------------------------------------------------------------
-- Derived typing rules
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.DerivedRules
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Typed.Consequences.DerivedRules.Identity R public
open import Definition.Typed.Consequences.DerivedRules.Nat R public
open import Definition.Typed.Consequences.DerivedRules.Pi R public
open import Definition.Typed.Consequences.DerivedRules.Pi-Sigma R public
open import Definition.Typed.Consequences.DerivedRules.Sigma R public
open import Definition.Typed.Consequences.DerivedRules.Unit R public
