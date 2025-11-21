------------------------------------------------------------------------
-- An admissible rule related to the natural number type
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Nat.Primitive
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M
open import Definition.Typed R

import Tools.PropositionalEquality as PE

private variable
  Γ : Cons _ _

opaque

  -- A variant of ℕⱼ.

  ⊢ℕ : ⊢ Γ → Γ ⊢ ℕ
  ⊢ℕ ⊢Γ = univ (ℕⱼ ⊢Γ)
