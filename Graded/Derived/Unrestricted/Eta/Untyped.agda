------------------------------------------------------------------------
-- The type constructor Unrestricted, defined using a Σ-type with
-- η-equality
------------------------------------------------------------------------

open import Graded.Modality
open import Definition.Untyped.NotParametrised

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
Unrestricted A = Σₚ ω , ω ▷ A ▹ Unitˢ

-- The constructor [_].

[_] : Term n → Term n
[ t ] = prodₚ ω t starˢ

-- The projection unbox.

unbox : Term n → Term n
unbox t = fst ω t
