------------------------------------------------------------------------
-- Validity for U
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality
open import Graded.Mode.Instances.Zero-one.Variant

module Graded.Erasure.LogicalRelation.Fundamental.Universe
  {a} {M : Set a}
  {𝕄 : Modality M}
  {R : Type-restrictions 𝕄}
  (variant : Mode-variant 𝕄)
  (as : Assumptions R)
  where

open Assumptions as

open import Definition.LogicalRelation.Substitution R
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Substitution R
open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Graded.Context 𝕄
open import Graded.Erasure.LogicalRelation as
open import Graded.Erasure.LogicalRelation.Hidden variant as
import Graded.Erasure.Target as T
open import Graded.Mode.Instances.Zero-one variant

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
      ( ⊢1ᵘ+ (subst-⊢∷L ⊢l ⊢σ)
      , U/Levelᵣ (λ { PE.refl → T.refl })
      )
