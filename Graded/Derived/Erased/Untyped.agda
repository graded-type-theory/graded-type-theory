------------------------------------------------------------------------
-- The type constructor Erased
--
-- See Graded.Derived.Erased.Eta.Untyped or
-- Graded.Derived.Erased.Eta.Untyped for the definition of the
-- projection "erased".
------------------------------------------------------------------------

open import Graded.Modality
open import Definition.Untyped.NotParametrised

module Graded.Derived.Erased.Untyped
  {a} {M : Set a}
  (𝕄 : Modality M)
  (s : SigmaMode)
  where

open Modality 𝕄

open import Definition.Untyped M

open import Tools.Nat

private variable
  n : Nat

-- The type constructor Erased.

Erased : Term n → Term n
Erased A = Σ⟨ s ⟩ 𝟘 , 𝟘 ▷ A ▹ Unit s

-- The constructor [_].

[_] : Term n → Term n
[ t ] = prod s 𝟘 t (star s)
