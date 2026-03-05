------------------------------------------------------------------------
-- The type constructor Unrestricted, defined using a strong Σ-type
------------------------------------------------------------------------

open import Graded.Modality

module Graded.Derived.Unrestricted.Eta.Untyped
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open Modality 𝕄

open import Definition.Untyped M

open import Tools.Nat

private variable
  n : Nat

opaque

  -- The type constructor Unrestricted.

  Unrestricted : Lvl n → Term n → Term n
  Unrestricted l A = Σˢ ω , ω ▷ A ▹ Lift (wk1 l) Unitˢ

opaque

  -- The constructor [_].

  [_] : Term n → Term n
  [ t ] = prodˢ ω t (lift starˢ)

opaque

  -- The projection unbox.

  unbox : Term n → Term n
  unbox t = fst ω t
