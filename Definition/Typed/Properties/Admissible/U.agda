------------------------------------------------------------------------
-- Admissible rules related to U
------------------------------------------------------------------------

open import Configuration-types
open import Graded.Modality

module Definition.Typed.Properties.Admissible.U
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TC : Type-configuration 𝕄)
  where

open import Definition.Typed TC
open import Definition.Typed.Inversion.Primitive TC
import Definition.Typed.Properties.Admissible.U.Primitive TC as UP
open import Definition.Typed.Properties.Well-formed TC
open import Definition.Typed.Well-formed TC

open import Definition.Untyped M

open UP public

private variable
  Γ : Cons _ _
  t : Term _

opaque

  -- A variant of Uⱼ.

  ⊢U′ : Γ ⊢ t ∷ Level → Γ ⊢ U (level t)
  ⊢U′ ⊢t =
    let ok = inversion-Level-⊢ (wf-⊢ ⊢t) in
    ⊢U (term ok ⊢t)
