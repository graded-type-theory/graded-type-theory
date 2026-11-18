------------------------------------------------------------------------
-- Validity for U
------------------------------------------------------------------------

open import Configuration-types
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality
import Graded.Mode.Instances.Zero-one
open import Graded.Mode.Instances.Zero-one.Variant

module Graded.Erasure.LogicalRelation.Fundamental.Universe
  {a} {M : Set a}
  {𝕄 : Modality M}
  {variant : Mode-variant 𝕄}
  (open Graded.Mode.Instances.Zero-one variant)
  (C : Configuration Zero-one-isMode)
  (open Configuration C)
  (as : Assumptions TC)
  where

open Assumptions as

open import Definition.LogicalRelation.Substitution TC
open import Definition.Typed TC
open import Definition.Typed.Properties TC
open import Definition.Typed.Substitution TC
open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Graded.Context 𝕄
open import Graded.Erasure.LogicalRelation as
open import Graded.Erasure.LogicalRelation.Hidden C as
import Graded.Erasure.Target as T

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  n : Nat
  Γ : Con Term _
  l : Lvl _
  γ : Conₘ _
  m : Mode

opaque

  -- Validity for U.

  Uʳ :
    ts » Γ ⊢ l ∷Level →
    γ ▸ Γ ⊩ʳ U l ∷[ m ∣ n ] U (1ᵘ+ l)
  Uʳ {l} ⊢l =
    ▸⊩ʳ∷⇔ .proj₂ λ ⊢σ _ →
    PE.subst (flip (_®_∷_◂_ _ _) _) (PE.cong U (PE.sym (1ᵘ+-[] l))) $
    ®∷→®∷◂ $
    ®∷U⇔ .proj₂
      ( ⊢1ᵘ+ (subst-⊢ ⊢l ⊢σ)
      , U/Levelᵣ (λ { PE.refl → T.refl })
      )
