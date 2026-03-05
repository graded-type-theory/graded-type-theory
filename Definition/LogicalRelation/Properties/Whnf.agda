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

open import Definition.LogicalRelation R ⦃ eqrel ⦄

open import Definition.Typed R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Untyped.Whnf M type-variant

open import Tools.Product

private variable
  Γ   : Cons _ _
  t u : Term _

opaque

  -- If t satisfies neLevel-prop Γ, then it is a neutral level.

  nelevel : neLevel-prop Γ t → Neutralₗ (Γ .defs) t
  nelevel (supᵘˡᵣ x x₁) = supᵘˡₙ (nelevel x)
  nelevel (supᵘʳᵣ x x₁) = supᵘʳₙ (nelevel x₁)
  nelevel (ne (neNfₜ₌ neK _ _)) = ne⁻ neK

  -- If t satisfies Level-prop Γ, then it is a WHNF.

  Level-prop→Whnf : Level-prop Γ t → Whnf (Γ .defs) t
  Level-prop→Whnf (zeroᵘᵣ _)  = zeroᵘₙ
  Level-prop→Whnf (sucᵘᵣ _ _) = sucᵘₙ
  Level-prop→Whnf (neLvl ⊩t)  = ne-whnf (nelevel ⊩t)

opaque

  -- If t and u satisfy [neLevel]-prop Γ, then they are neutral levels.

  nelsplit :
    [neLevel]-prop Γ t u → Neutralₗ (Γ .defs) t × Neutralₗ (Γ .defs) u
  nelsplit (supᵘˡᵣ t≡u x) = let a , b = nelsplit t≡u in supᵘˡₙ a , supᵘˡₙ b
  nelsplit (supᵘʳᵣ x t≡u) = let a , b = nelsplit t≡u in supᵘʳₙ a , supᵘʳₙ b
  nelsplit (supᵘ-zeroʳᵣ [u]) = let a = nelevel [u] in supᵘˡₙ a , a
  nelsplit (supᵘ-assoc¹ᵣ x y z) = let a = nelevel x in supᵘˡₙ (supᵘˡₙ a) , supᵘˡₙ a
  nelsplit (supᵘ-assoc²ᵣ x y z) = let a = nelevel y in supᵘˡₙ (supᵘʳₙ a) , supᵘʳₙ (supᵘˡₙ a)
  nelsplit (supᵘ-assoc³ᵣ x y z) = let a = nelevel z in supᵘʳₙ a , supᵘʳₙ (supᵘʳₙ a)
  nelsplit (supᵘ-comm¹ᵣ x d y d′) = supᵘˡₙ (nelevel x) , supᵘˡₙ (nelevel y)
  nelsplit (supᵘ-comm²ᵣ x d y) = let u = nelevel y in supᵘʳₙ u , supᵘˡₙ u
  nelsplit (supᵘ-idemᵣ x y) = let n = nelevel x in supᵘˡₙ n , n
  nelsplit (ne (neNfₜ₌ neK neM _)) = ne⁻ neK , ne⁻ neM

  -- If t and u satisfy [Level]-prop Γ, then they are WHNFs.

  lsplit : [Level]-prop Γ t u → Whnf (Γ .defs) t × Whnf (Γ .defs) u
  lsplit (zeroᵘᵣ _) = zeroᵘₙ , zeroᵘₙ
  lsplit (sucᵘᵣ _ _) = sucᵘₙ , sucᵘₙ
  lsplit (supᵘ-subᵣ x _) =
    let a = nelevel x in
    ne-whnf (supᵘˡₙ a) , sucᵘₙ
  lsplit (neLvl x) = let a , b = nelsplit x in ne-whnf a , ne-whnf b
  lsplit (sym u≡t) = let a , b = lsplit u≡t in b , a
  lsplit (trans t≡u u≡v) = let a , _ = lsplit t≡u; _ , b = lsplit u≡v in a , b

opaque

  -- If t and u satisfy [Natural]-prop Γ, then they are "Naturals".

  split :
    [Natural]-prop Γ t u →
    Natural Var-included (Γ .defs) t × Natural Var-included (Γ .defs) u
  split (sucᵣ _)                  = sucₙ , sucₙ
  split zeroᵣ                     = zeroₙ , zeroₙ
  split (ne (neNfₜ₌ t-ne u-ne _)) = ne (ne⁻ t-ne) , ne (ne⁻ u-ne)

opaque

  -- If t and u satisfy [Empty]-prop Γ, then they are neutral.

  esplit :
    [Empty]-prop Γ t u → Neutralₗ (Γ .defs) t × Neutralₗ (Γ .defs) u
  esplit (ne (neNfₜ₌ t-ne u-ne _)) = ne⁻ t-ne , ne⁻ u-ne

opaque

  -- If t and u satisfy [Unit]-prop′ Γ, then they are WHNFs.

  usplit :
    ∀ {s} → [Unit]-prop′ Γ s t u → Whnf (Γ .defs) t × Whnf (Γ .defs) u
  usplit starᵣ                 = starₙ , starₙ
  usplit (ne (neNfₜ₌ t-ne u-ne _)) = ne! t-ne , ne! u-ne
