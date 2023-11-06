------------------------------------------------------------------------
-- The type constructor Erased, defined using Σ and Unit types without
-- η-equality.
------------------------------------------------------------------------

open import Graded.Modality

module Graded.Derived.Erased.NoEta.Untyped
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open Modality 𝕄

open import Definition.Untyped M
open import Definition.Untyped.Sigma M

open import Tools.Fin
open import Tools.Nat

open import Graded.Derived.Erased.Untyped 𝕄 Σᵣ public

private variable
  n : Nat

-- The "projection" erased.

erased : Term n → Term n → Term n
erased = fstᵣ 𝟘
  where
  open Fstᵣ-sndᵣ (𝟘 ∧ 𝟙) 𝟘
