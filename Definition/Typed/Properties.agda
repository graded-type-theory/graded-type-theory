------------------------------------------------------------------------
-- Properties of the typing and reduction relations
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M

open import Definition.Typed R

open import Tools.Fin
open import Tools.PropositionalEquality

open import Definition.Typed.Properties.Admissible R public
open import Definition.Typed.Properties.Reduction R public
open import Definition.Typed.Properties.Well-formed R public

private variable
  x   : Fin _
  Γ   : Con Term _
  A B : Term _

------------------------------------------------------------------------
-- A lemma related to _∷_∈_

opaque

  -- If x ∷ A ∈ Γ and x ∷ B ∈ Γ both hold, then A is equal to B.

  det∈ : x ∷ A ∈ Γ → x ∷ B ∈ Γ → A ≡ B
  det∈ here      here      = refl
  det∈ (there x) (there y) = cong wk1 (det∈ x y)
