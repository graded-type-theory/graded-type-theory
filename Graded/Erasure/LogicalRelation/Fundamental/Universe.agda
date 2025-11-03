------------------------------------------------------------------------
-- Validity for U
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality

module Graded.Erasure.LogicalRelation.Fundamental.Universe
  {a} {M : Set a}
  {𝕄 : Modality M}
  {R : Type-restrictions 𝕄}
  (as : Assumptions R)
  where

open import Definition.LogicalRelation.Substitution R
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Substitution R
open import Definition.Untyped M

open import Graded.Context 𝕄
open import Graded.Erasure.LogicalRelation as
open import Graded.Erasure.LogicalRelation.Hidden as
import Graded.Erasure.Target as T
open import Graded.Mode 𝕄

open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  Γ : Con Term _
  t : Term _
  γ : Conₘ _
  m : Mode

opaque

  -- Validity for U.

  Uʳ :
    Γ ⊢ t ∷Level →
    γ ▸ Γ ⊩ʳ U t ∷[ m ] U (sucᵘ t)
  Uʳ ⊢t =
    ▸⊩ʳ∷⇔ .proj₂ λ ⊩σ _ →
    ®∷→®∷◂ $
    ®∷U⇔ .proj₂
      ( ⊢sucᵘ (subst-⊢∷L ⊢t (escape-⊩ˢ∷ ⊩σ .proj₂))
      , U/Levelᵣ (λ { PE.refl → T.refl })
      )
