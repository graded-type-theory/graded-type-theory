------------------------------------------------------------------------
-- Admissible rules related to Erased
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.Admissible.Erased
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Consequences.Admissible.Sigma R

open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as Erased

open import Tools.Product

private variable
  Γ         : Cons _ _
  A l t₁ t₂ : Term _
  s         : Strength

opaque
  unfolding Erased.Erased Erased.[_]

  -- A kind of inverse of []-cong′.

  []-cong′⁻¹ :
    let open Erased s in
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Γ ⊢ [ t₁ ] ≡ [ t₂ ] ∷ Erased l A →
    Γ ⊢ t₁ ≡ t₂ ∷ A
  []-cong′⁻¹ [t₁]≡[t₂] =
    let _ , t₁≡t₂ , _ = prod-cong⁻¹ [t₁]≡[t₂] in
    t₁≡t₂
