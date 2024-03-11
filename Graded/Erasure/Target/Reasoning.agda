------------------------------------------------------------------------
-- "Equational" reasoning combinators for _⇒*_
------------------------------------------------------------------------

module Graded.Erasure.Target.Reasoning where

open import Graded.Erasure.Target
open import Graded.Erasure.Target.Properties

open import Tools.Function
open import Tools.Nat
open import Tools.PropositionalEquality as PE using (_≡_)

private variable
  n   : Nat
  u v : Term _

infix  -1 _∎⇒
infixr -2 step-⇒ step-⇒* step-≡ step-≡˘ _≡⟨⟩⇒_

-- A single step.

step-⇒ : ∀ t → u ⇒* v → t ⇒ u → t ⇒* v
step-⇒ _ = flip trans

syntax step-⇒ t u⇒v t⇒u = t ⇒⟨ t⇒u ⟩ u⇒v

{-# INLINE step-⇒ #-}

-- Multiple steps.

step-⇒* : ∀ t → u ⇒* v → t ⇒* u → t ⇒* v
step-⇒* _ = flip red*concat

syntax step-⇒* t u⇒v t⇒u = t ⇒*⟨ t⇒u ⟩ u⇒v

{-# INLINE step-⇒* #-}

-- A reasoning step that uses propositional equality.

step-≡ : ∀ t → u ⇒* v → t ≡ u → t ⇒* v
step-≡ _ u⇒v PE.refl = u⇒v

syntax step-≡ t u⇒v t≡u = t ≡⟨ t≡u ⟩⇒ u⇒v

-- A reasoning step that uses propositional equality, combined with
-- symmetry.

step-≡˘ : ∀ t → u ⇒* v → u ≡ t → t ⇒* v
step-≡˘ _ u⇒v PE.refl = u⇒v

syntax step-≡˘ t u⇒v u≡t = t ≡˘⟨ u≡t ⟩⇒ u⇒v

-- A reasoning step that uses (Agda's) definitional equality.

_≡⟨⟩⇒_ : ∀ t → t ⇒* u → t ⇒* u
_ ≡⟨⟩⇒ t⇒u = t⇒u

{-# INLINE _≡⟨⟩⇒_ #-}

-- Reflexivity.

_∎⇒ : (t : Term n) → t ⇒* t
_ ∎⇒ = refl

{-# INLINE _∎⇒ #-}
