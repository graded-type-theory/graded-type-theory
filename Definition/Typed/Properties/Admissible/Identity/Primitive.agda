------------------------------------------------------------------------
-- Some admissible rules related to Id
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Identity.Primitive
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as Erased

open import Definition.Typed R
open import Definition.Typed.Inversion.Primitive R
open import Definition.Typed.Well-formed R

open import Tools.Product

private variable
  ∇       : DCon (Term 0) _
  Γ       : Con Term _
  A t u v : Term _
  s       : Strength

opaque

  -- A variant of Idⱼ.

  Idⱼ′ : ∇ » Γ ⊢ t ∷ A → ∇ » Γ ⊢ u ∷ A → ∇ » Γ ⊢ Id A t u
  Idⱼ′ ⊢t = Idⱼ (wf-⊢∷ ⊢t) ⊢t

opaque

  -- A variant of []-congⱼ.

  []-congⱼ′ :
    let open Erased s in
    []-cong-allowed s →
    ∇ » Γ ⊢ v ∷ Id A t u →
    ∇ » Γ ⊢ []-cong s A t u v ∷ Id (Erased A) ([ t ]) ([ u ])
  []-congⱼ′ ok ⊢v =
    let _ , ⊢t , ⊢u = inversion-Id (wf-⊢∷ ⊢v) in
    []-congⱼ (wf-⊢∷ ⊢t) ⊢t ⊢u ⊢v ok
