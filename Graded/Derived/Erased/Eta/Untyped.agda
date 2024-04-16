------------------------------------------------------------------------
-- The type constructor Erased, defined using strong Σ and unit types
------------------------------------------------------------------------

open import Graded.Modality

module Graded.Derived.Erased.Eta.Untyped
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open Modality 𝕄

open import Definition.Untyped M

open import Tools.Nat

private variable
  n : Nat

-- The projection erased.

erased : Term n → Term n
erased t = fst 𝟘 t
