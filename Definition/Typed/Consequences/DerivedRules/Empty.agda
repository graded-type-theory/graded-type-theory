------------------------------------------------------------------------
-- Derived rules related to the empty type
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.DerivedRules.Empty
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions TR

open import Definition.Untyped M hiding (wk)
open import Definition.Untyped.Properties M
open import Definition.Typed TR
open import Definition.Typed.Consequences.Syntactic TR
open import Definition.Typed.Weakening TR
open import Definition.Typed.Properties TR
open import Definition.Untyped.Empty 𝕄

open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  Γ               : Con Term _
  A A₁ A₂ t t₁ t₂ : Term _


opaque
  unfolding emptyrec-sink

  -- An equality rule for emptyrec-sink.

  emptyrec-sink-cong :
    Unitˢ-allowed → Π-allowed 𝟙 𝟘 →
    Γ ⊢ A₁ ≡ A₂ → Γ ⊢ t₁ ≡ t₂ ∷ Empty →
    Γ ⊢ emptyrec-sink A₁ t₁ ≡ emptyrec-sink A₂ t₂ ∷ A₁
  emptyrec-sink-cong ok₁ ok₂ A₁≡A₂ t₁≡t₂ =
    let ⊢Γ    = wfEq A₁≡A₂
        ⊢Unit = Unitⱼ ⊢Γ ok₁
    in
    PE.subst (_⊢_≡_∷_ _ _ _) (wk1-sgSubst _ _) $
    app-cong
      (emptyrec-cong (ΠΣ-cong (refl ⊢Unit) (wkEq₁ ⊢Unit A₁≡A₂) ok₂)
         t₁≡t₂)
      (refl (starⱼ ⊢Γ ok₁))

opaque

  -- A typing rule for emptyrec-sink

  emptyrec-sinkⱼ :
    Unitˢ-allowed → Π-allowed 𝟙 𝟘 →
    Γ ⊢ A → Γ ⊢ t ∷ Empty →
    Γ ⊢ emptyrec-sink A t ∷ A
  emptyrec-sinkⱼ ok₁ ok₂ ⊢A ⊢t =
    syntacticEqTerm (emptyrec-sink-cong ok₁ ok₂ (refl ⊢A) (refl ⊢t))
      .proj₂ .proj₁
