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

-- The type constructor Unrestricted.

Unrestricted : Term n → Term n
Unrestricted A = Σˢ ω , ω ▷ A ▹ Unitˢ zeroᵘ

-- The constructor [_].

[_] : Term n → Term n
[ t ] = prodˢ ω t (starˢ zeroᵘ)

-- The projection unbox.

unbox : Term n → Term n
unbox t = fst ω t
