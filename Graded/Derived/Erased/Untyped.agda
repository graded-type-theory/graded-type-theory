------------------------------------------------------------------------
-- The type constructor Erased
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Graded.Modality
open import Definition.Untyped.NotParametrised

module Graded.Derived.Erased.Untyped
  {a} {M : Set a}
  (𝕄 : Modality M)
  (s : Strength)
  where

open Modality 𝕄

open import Definition.Untyped M as U

import Graded.Derived.Erased.Eta.Untyped 𝕄 as Eta
import Graded.Derived.Erased.NoEta.Untyped 𝕄 as NoEta

open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality

private variable
  n   : Nat
  A t : Term _
  σ   : Subst _ _

-- The type constructor Erased.

Erased : Term n → Term n
Erased A = Σ⟨ s ⟩ 𝟘 , 𝟘 ▷ A ▹ Unit s

-- The constructor [_].

[_] : Term n → Term n
[ t ] = prod s 𝟘 t (star s)

opaque

  -- The "projection" erased.

  erased : Term n → Term n → Term n
  erased A t = case s of λ where
    𝕤 → Eta.erased t
    𝕨 → NoEta.erased A t

opaque
  unfolding erased

  -- A substitution lemma for erased.

  erased-[] : erased A t U.[ σ ] ≡ erased (A U.[ σ ]) (t U.[ σ ])
  erased-[] {A} {t} = case singleton s of λ where
    (𝕤 , refl) → refl
    (𝕨 , refl) → NoEta.erased-[] A t
