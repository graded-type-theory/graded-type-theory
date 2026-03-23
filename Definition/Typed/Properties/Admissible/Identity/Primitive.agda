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
  Γ       : Cons _ _
  A t u v : Term _
  l       : Lvl _
  s       : Strength

opaque

  -- A variant of Idⱼ.

  Idⱼ′ : Γ ⊢ t ∷ A → Γ ⊢ u ∷ A → Γ ⊢ Id A t u
  Idⱼ′ ⊢t = Idⱼ (wf-⊢ ⊢t) ⊢t

opaque

  -- A variant of []-congⱼ.

  []-congⱼ′ :
    let open Erased s in
    []-cong-allowed s →
    Γ ⊢ l ∷Level →
    Γ ⊢ v ∷ Id A t u →
    Γ ⊢ []-cong s l A t u v ∷ Id (Erased l A) ([ t ]) ([ u ])
  []-congⱼ′ ok ⊢l ⊢v =
    let ⊢A , ⊢t , ⊢u = inversion-Id (wf-⊢ ⊢v) in
    []-congⱼ ⊢l ⊢A ⊢t ⊢u ⊢v ok
