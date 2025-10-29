------------------------------------------------------------------------
-- Admissible rules related to U
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.U
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  where

open import Definition.Typed TR

open import Definition.Untyped M hiding (wk)

private variable
  Γ : Con Term _
  l : Term _

opaque

  -- A variant of Uⱼ.

  ⊢U : Γ ⊢ l ∷ Level → Γ ⊢ U l
  ⊢U ⊢l = univ (Uⱼ ⊢l)
