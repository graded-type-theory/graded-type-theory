------------------------------------------------------------------------
-- The type constructor Erased, defined using weak Σ and unit types
------------------------------------------------------------------------

open import Graded.Modality

module Graded.Derived.Erased.NoEta.Untyped
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open Modality 𝕄

open import Definition.Untyped M
open import Definition.Untyped.Sigma 𝕄

open import Tools.Fin
open import Tools.Nat
open import Tools.PropositionalEquality

private variable
  n : Nat
  σ : Subst _ _

-- The "projection" erased.

erased : Term n → Term n → Term n
erased = fstʷ 𝟘

opaque

  -- A substitution lemma for erased.

  erased-[] :
    (A t : Term n) → erased A t [ σ ] ≡ erased (A [ σ ]) (t [ σ ])
  erased-[] = fstʷ-[]
