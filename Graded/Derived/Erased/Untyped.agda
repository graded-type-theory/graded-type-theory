------------------------------------------------------------------------
-- The type constructor Erased
------------------------------------------------------------------------

{-# OPTIONS --no-opaque #-}

open import Graded.Modality

module Graded.Derived.Erased.Untyped
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open Modality 𝕄

open import Definition.Untyped M

open import Tools.Nat

private variable
  n : Nat

-- The type constructor Erased.

Erased : Term n → Term n
Erased A = Σₚ 𝟘 , 𝟘 ▷ A ▹ Unit

-- The constructor [_].

[_] : Term n → Term n
[ t ] = prodₚ 𝟘 t star

-- The projection erased.

erased : Term n → Term n
erased t = fst 𝟘 t
