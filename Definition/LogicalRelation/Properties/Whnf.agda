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
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Whnf M type-variant

open import Tools.Function
open import Tools.Product

private variable
  Γ     : Cons _ _
  t u A : Term _
  s     : Strength
  l     : Universe-level

opaque

  -- If t satisfies Natural-prop Γ, then t is a "Natural" (a specific
  -- kind of WHNF).

  natural : Natural-prop Γ t → Natural Var-included (Γ .defs) t
  natural (sucᵣ _)            = sucₙ
  natural zeroᵣ               = zeroₙ
  natural (ne (neNfₜ t-ne _)) = ne t-ne

opaque

  -- If t and u satisfy [Natural]-prop Γ, then they are "Naturals".

  split :
    [Natural]-prop Γ t u →
    Natural Var-included (Γ .defs) t × Natural Var-included (Γ .defs) u
  split (sucᵣ _)                  = sucₙ , sucₙ
  split zeroᵣ                     = zeroₙ , zeroₙ
  split (ne (neNfₜ₌ t-ne u-ne _)) = ne t-ne , ne u-ne

opaque

  -- If t satisfies Empty-prop Γ, then t is neutral.

  empty : Empty-prop Γ t → Neutralₗ (Γ .defs) t
  empty (ne (neNfₜ t-ne _)) = t-ne

opaque

  -- If t and u satisfy [Empty]-prop Γ, then they are neutral.

  esplit :
    [Empty]-prop Γ t u → Neutralₗ (Γ .defs) t × Neutralₗ (Γ .defs) u
  esplit (ne (neNfₜ₌ t-ne u-ne _)) = t-ne , u-ne

opaque

  -- If t satisfies Unit-prop Γ l s, then t is a WHNF.

  unit : Unit-prop Γ l s t → Whnf (Γ .defs) t
  unit starᵣ               = starₙ
  unit (ne (neNfₜ t-ne _)) = ne-whnf t-ne

opaque

  -- If t and u satisfy [Unitʷ]-prop Γ, then they are WHNFs.

  usplit : [Unitʷ]-prop Γ l t u → Whnf (Γ .defs) t × Whnf (Γ .defs) u
  usplit starᵣ                     = starₙ , starₙ
  usplit (ne (neNfₜ₌ t-ne u-ne _)) = ne-whnf t-ne , ne-whnf u-ne
