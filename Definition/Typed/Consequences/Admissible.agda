------------------------------------------------------------------------
-- Derived typing rules
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.Admissible
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Typed.Consequences.Admissible.Bool R public
open import Definition.Typed.Consequences.Admissible.Bool.OK R public
open import Definition.Typed.Consequences.Admissible.Empty R public
open import Definition.Typed.Consequences.Admissible.Identity R public
open import Definition.Typed.Consequences.Admissible.Lift R public
open import Definition.Typed.Consequences.Admissible.Nat R public
open import Definition.Typed.Consequences.Admissible.Pi R public
open import Definition.Typed.Consequences.Admissible.Sigma R public
open import Definition.Typed.Consequences.Admissible.Unit R public

module Erased-Bool where
  open import Definition.Typed.Consequences.Admissible.Bool.Erased R
    public
