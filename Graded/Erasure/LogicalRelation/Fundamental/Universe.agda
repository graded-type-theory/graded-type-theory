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

open import Definition.Untyped M

open import Graded.Context 𝕄
open import Graded.Erasure.LogicalRelation as
open import Graded.Erasure.LogicalRelation.Hidden as
import Graded.Erasure.Target as T
open import Graded.Mode 𝕄

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  Γ : Con Term _
  γ : Conₘ _
  m : Mode
  l : Universe-level

opaque

  -- Validity for U.

  Uʳ : γ ▸ Γ ⊩ʳ⟨ 2+ l ⟩ U l ∷[ m ] U (1+ l)
  Uʳ =
    ▸⊩ʳ∷⇔ .proj₂ λ _ _ →
    ®∷→®∷◂ (®∷U⇔ .proj₂ (≤ᵘ-refl , Uᵣ (λ { PE.refl → T.refl })))
