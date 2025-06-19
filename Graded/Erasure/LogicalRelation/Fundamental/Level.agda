------------------------------------------------------------------------
-- Validity for Level
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality

module Graded.Erasure.LogicalRelation.Fundamental.Level
  {a} {M : Set a}
  {𝕄 : Modality M}
  {R : Type-restrictions 𝕄}
  (as : Assumptions R)
  where

open import Definition.LogicalRelation.Substitution R
open import Definition.Typed R
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
  Γ   : Con Term _
  t u : Term _
  γ   : Conₘ _
  m   : Mode

opaque

  -- Validity for Level.

  Levelʳ :
    Γ ⊢ t ∷ Level →
    γ ▸ Γ ⊩ʳ Level ∷[ m ] U t
  Levelʳ ⊢t =
    ▸⊩ʳ∷⇔ .proj₂ λ ⊩σ _ →
    ®∷→®∷◂ $
    ®∷U⇔ .proj₂
      ( subst-⊢∷ ⊢t (escape-⊩ˢ∷ ⊩σ .proj₂)
      , U/Levelᵣ (λ { PE.refl → T.refl })
      )

opaque

  -- Validity for zeroᵘ.

  zeroᵘʳ :
    γ ▸ Γ ⊩ʳ zeroᵘ ∷[ m ] Level
  zeroᵘʳ =
    ▸⊩ʳ∷⇔ .proj₂ λ ⊩σ _ →
    ®∷→®∷◂ $
    ®∷Level⇔ .proj₂ (U/Levelᵣ (λ { PE.refl → T.refl }))

opaque

  -- Validity for sucᵘ.

  sucᵘʳ :
    γ ▸ Γ ⊩ʳ sucᵘ t ∷[ m ] Level
  sucᵘʳ =
    ▸⊩ʳ∷⇔ .proj₂ λ ⊩σ _ →
    ®∷→®∷◂ $
    ®∷Level⇔ .proj₂ (U/Levelᵣ (λ { PE.refl → T.refl }))

opaque

  -- Validity for _maxᵘ_.

  maxᵘʳ :
    γ ▸ Γ ⊩ʳ t maxᵘ u ∷[ m ] Level
  maxᵘʳ =
    ▸⊩ʳ∷⇔ .proj₂ λ ⊩σ _ →
    ®∷→®∷◂ $
    ®∷Level⇔ .proj₂ (U/Levelᵣ (λ { PE.refl → T.refl }))
