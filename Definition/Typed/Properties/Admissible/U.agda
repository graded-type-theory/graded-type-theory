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
open import Definition.Typed.Inversion.Primitive TR
import Definition.Typed.Properties.Admissible.U.Primitive TR as UP
open import Definition.Typed.Properties.Well-formed TR
open import Definition.Typed.Well-formed TR

open import Definition.Untyped M

open UP public

private variable
  Γ : Cons _ _
  t : Term _

opaque

  -- A variant of Uⱼ.

  ⊢U′ : Γ ⊢ t ∷ Level → Γ ⊢ U (level t)
  ⊢U′ ⊢t =
    let ok = inversion-Level-⊢ (wf-⊢∷ ⊢t) in
    ⊢U (term ok ⊢t)
