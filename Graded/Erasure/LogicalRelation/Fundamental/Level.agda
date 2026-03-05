------------------------------------------------------------------------
-- Validity for Level
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality
open import Graded.Mode.Instances.Zero-one.Variant

module Graded.Erasure.LogicalRelation.Fundamental.Level
  {a} {M : Set a}
  {𝕄 : Modality M}
  {R : Type-restrictions 𝕄}
  (variant : Mode-variant 𝕄)
  (as : Assumptions R)
  where

open Assumptions as
open Type-restrictions R

open import Definition.LogicalRelation.Substitution R
open import Definition.Typed R
open import Definition.Typed.Substitution R
open import Definition.Untyped M

open import Graded.Context 𝕄
open import Graded.Erasure.LogicalRelation as
open import Graded.Erasure.LogicalRelation.Hidden variant as
open import Graded.Mode.Instances.Zero-one variant
import Graded.Erasure.Target as T

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  n   : Nat
  Γ   : Con Term _
  t u : Term _
  l   : Lvl _
  γ   : Conₘ _
  m   : Mode

opaque

  -- Validity for Level.

  Levelʳ :
    ts » Γ ⊢ l ∷Level →
    γ ▸ Γ ⊩ʳ Level ∷[ m ∣ n ] U l
  Levelʳ ⊢l =
    ▸⊩ʳ∷⇔ .proj₂ λ ⊢σ _ →
    ®∷→®∷◂ $
    ®∷U⇔ .proj₂
      ( subst-⊢∷L ⊢l ⊢σ
      , U/Levelᵣ (λ { PE.refl → T.refl })
      )

opaque

  -- Validity for zeroᵘ.

  zeroᵘʳ :
    Level-allowed →
    γ ▸ Γ ⊩ʳ zeroᵘ ∷[ m ∣ n ] Level
  zeroᵘʳ ok =
    ▸⊩ʳ∷⇔ .proj₂ λ _ _ →
    ®∷→®∷◂ $
    ®∷Level⇔ .proj₂ (ok , U/Levelᵣ (λ { PE.refl → T.refl }))

opaque

  -- Validity for sucᵘ.

  sucᵘʳ :
    Level-allowed →
    γ ▸ Γ ⊩ʳ sucᵘ t ∷[ m ∣ n ] Level
  sucᵘʳ ok =
    ▸⊩ʳ∷⇔ .proj₂ λ _ _ →
    ®∷→®∷◂ $
    ®∷Level⇔ .proj₂ (ok , U/Levelᵣ (λ { PE.refl → T.refl }))

opaque

  -- Validity for _supᵘ_.

  supᵘʳ :
    Level-allowed →
    γ ▸ Γ ⊩ʳ t supᵘ u ∷[ m ∣ n ] Level
  supᵘʳ ok =
    ▸⊩ʳ∷⇔ .proj₂ λ _ _ →
    ®∷→®∷◂ $
    ®∷Level⇔ .proj₂ (ok , U/Levelᵣ (λ { PE.refl → T.refl }))
