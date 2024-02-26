------------------------------------------------------------------------
-- Derived rules related to the unit types
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.DerivedRules.Unit
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  where

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed TR
open import Definition.Typed.Consequences.DerivedRules.Identity TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Consequences.Syntactic TR
open import Definition.Typed.Properties TR
open import Definition.Untyped.Unit 𝕄

open import Tools.Function

private variable
  Γ : Con Term _
  t : Term _
  s : Strength
  p : M

opaque

  -- A definitional η-rule for the strong unit type.

  Unit-η-≡ :
    Γ ⊢ t ∷ Unitˢ →
    Γ ⊢ starˢ ≡ t ∷ Unitˢ
  Unit-η-≡ ⊢t = η-unit
    (starⱼ (wfTerm ⊢t) (⊢∷Unit→Unit-allowed ⊢t))
    ⊢t

opaque
  unfolding Unit-η

  -- A typing rule for Unit-η.

  ⊢Unit-η :
    Γ ⊢ t ∷ Unit s →
    Γ ⊢ Unit-η s p t ∷ Id (Unit s) (star s) t
  ⊢Unit-η {s = 𝕤} ⊢t =
    rflⱼ′ (Unit-η-≡ ⊢t)
  ⊢Unit-η {s = 𝕨} ⊢t =
    case syntacticTerm ⊢t of λ
      ⊢Unit →
    case wf ⊢Unit of λ
      ⊢Γ →
    case inversion-Unit ⊢Unit of λ
      ok →
    unitrecⱼ
      (Idⱼ (starⱼ (⊢→⊢∙ (Unitⱼ ⊢Γ ok)) ok) (var₀ ⊢Unit))
      ⊢t
      (rflⱼ (starⱼ ⊢Γ ok))
      ok
