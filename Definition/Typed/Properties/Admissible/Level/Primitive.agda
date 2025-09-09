------------------------------------------------------------------------
-- Primitive admissible rules for Level
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Level.Primitive
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Properties.Well-formed R

open import Definition.Untyped M

private variable
  Γ     : Con Term _
  A B l : Term _

supᵘ-zeroʳⱼ
  : Γ ⊢ l ∷ Level
  → Γ ⊢ l supᵘ zeroᵘ ≡ l ∷ Level
supᵘ-zeroʳⱼ ⊢l = trans (supᵘ-comm ⊢l (zeroᵘⱼ (wfTerm ⊢l))) (supᵘ-zeroˡ ⊢l)
