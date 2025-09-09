------------------------------------------------------------------------
-- Some lemmas related to the logical relation and WHNFs
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.Whnf
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  ⦃ eqrel : EqRelSet R ⦄
  where

open EqRelSet eqrel
open Type-restrictions R

open import Definition.LogicalRelation R

open import Definition.Untyped M
open import Definition.Untyped.Whnf M type-variant

open import Tools.Product

private variable
  Γ   : Cons _ _
  t u : Term _

opaque

  -- If t and u satisfy [Natural]-prop Γ, then they are "Naturals".

  split :
    [Natural]-prop Γ t u →
    Natural Var-included (Γ .defs) t × Natural Var-included (Γ .defs) u
  split (sucᵣ _)                  = sucₙ , sucₙ
  split zeroᵣ                     = zeroₙ , zeroₙ
  split (ne (neNfₜ₌ t-ne u-ne _)) = ne t-ne , ne u-ne

opaque

  -- If t and u satisfy [Empty]-prop Γ, then they are neutral.

  esplit :
    [Empty]-prop Γ t u → Neutralₗ (Γ .defs) t × Neutralₗ (Γ .defs) u
  esplit (ne (neNfₜ₌ t-ne u-ne _)) = t-ne , u-ne
