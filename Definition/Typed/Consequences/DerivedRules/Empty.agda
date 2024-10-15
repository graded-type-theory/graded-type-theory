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
open import Definition.Typed.Weakening TR
open import Definition.Typed.Properties TR
open import Definition.Untyped.Empty 𝕄

import Tools.PropositionalEquality as PE

private variable
  Γ   : Con Term _
  A t : Term _


opaque
  unfolding emptyrec-sink

  -- A typing rule for emptyrec-sink

  emptyrec-sinkⱼ : Γ ⊢ A → Γ ⊢ t ∷ Empty →
                   Unitˢ-allowed → Π-allowed 𝟙 𝟘 →
                   Γ ⊢ emptyrec-sink A t ∷ A
  emptyrec-sinkⱼ {A} {t} ⊢A ⊢t ok ok′ =
    let ⊢Γ = wf ⊢A
        ⊢Unit = Unitⱼ ⊢Γ ok
    in  PE.subst (_ ⊢ emptyrec-sink A t ∷_) (wk1-sgSubst A (starˢ 0))
            (emptyrecⱼ (ΠΣⱼ ⊢Unit (wk (step id) (⊢Γ ∙ ⊢Unit) ⊢A) ok′) ⊢t
          ∘ⱼ starⱼ ⊢Γ ok)
