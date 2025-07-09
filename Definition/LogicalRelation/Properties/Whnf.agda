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

open import Tools.Product

private variable
  Γ   : Con Term _
  t u : Term _

opaque

  -- If t satisfies neLevel-prop Γ, then it is a neutral level.

  nelevel : neLevel-prop Γ t → Neutralˡ t
  nelevel (supᵘˡᵣ x x₁) = supᵘˡₙ (nelevel x)
  nelevel (supᵘʳᵣ x x₁) = supᵘʳₙ (nelevel x₁)
  nelevel (ne (neNfₜ₌ _ neK neM k≡m)) = ne neK

  -- If t satisfies Level-prop Γ, then it is a WHNF.

  level : Level-prop Γ t → Whnf t
  level zeroᵘᵣ = zeroᵘₙ
  level (sucᵘᵣ x) = sucᵘₙ
  level (neLvl x) = ne (nelevel x)

opaque

  -- If t and u satisfy [neLevel]-prop Γ, then they are neutral levels.

  nelsplit : [neLevel]-prop Γ t u → Neutralˡ t × Neutralˡ u
  nelsplit (supᵘˡᵣ t≡u x) = let a , b = nelsplit t≡u in supᵘˡₙ a , supᵘˡₙ b
  nelsplit (supᵘʳᵣ x t≡u) = let a , b = nelsplit t≡u in supᵘʳₙ a , supᵘʳₙ b
  nelsplit (supᵘ-zeroʳᵣ [u]) = let a = nelevel [u] in supᵘˡₙ a , a
  nelsplit (supᵘ-assoc¹ᵣ x y z) = let a = nelevel x in supᵘˡₙ (supᵘˡₙ a) , supᵘˡₙ a
  nelsplit (supᵘ-assoc²ᵣ x y z) = let a = nelevel y in supᵘˡₙ (supᵘʳₙ a) , supᵘʳₙ (supᵘˡₙ a)
  nelsplit (supᵘ-assoc³ᵣ x y z) = let a = nelevel z in supᵘʳₙ a , supᵘʳₙ (supᵘʳₙ a)
  nelsplit (supᵘ-comm¹ᵣ x d y d′) = supᵘˡₙ (nelevel x) , supᵘˡₙ (nelevel y)
  nelsplit (supᵘ-comm²ᵣ x d y) = let u = nelevel y in supᵘʳₙ u , supᵘˡₙ u
  nelsplit (supᵘ-idemᵣ x y) = let n = nelevel x in supᵘˡₙ n , n
  nelsplit (ne (neNfₜ₌ _ neK neM _)) = ne neK , ne neM

  -- If t and u satisfy [Level]-prop Γ, then they are WHNFs.

  lsplit : [Level]-prop Γ t u → Whnf t × Whnf u
  lsplit zeroᵘᵣ = zeroᵘₙ , zeroᵘₙ
  lsplit (sucᵘᵣ x) = sucᵘₙ , sucᵘₙ
  lsplit (supᵘ-subᵣ x _) = let a = nelevel x in ne (supᵘˡₙ a) , sucᵘₙ
  lsplit (neLvl x) = let a , b = nelsplit x in ne a , ne b
  lsplit (sym u≡t) = let a , b = lsplit u≡t in b , a
  lsplit (trans t≡u u≡v) = let a , _ = lsplit t≡u; _ , b = lsplit u≡v in a , b

opaque

  -- If t and u satisfy [Natural]-prop Γ, then they are "Naturals".

  split : [Natural]-prop Γ t u → Natural t × Natural u
  split (sucᵣ _)                    = sucₙ , sucₙ
  split zeroᵣ                       = zeroₙ , zeroₙ
  split (ne (neNfₜ₌ _ t-ne u-ne _)) = ne t-ne , ne u-ne

opaque

  -- If t and u satisfy [Empty]-prop Γ, then they are neutral terms.

  esplit : [Empty]-prop Γ t u → Neutral t × Neutral u
  esplit (ne (neNfₜ₌ _ t-ne u-ne _)) = t-ne , u-ne

opaque

  -- If t and u satisfy [Unit]-prop′ Γ, then they are WHNFs.

  usplit : ∀ {s} → [Unit]-prop′ Γ s t u → Whnf t × Whnf u
  usplit starᵣ                 = starₙ , starₙ
  usplit (ne (neNfₜ₌ _ t-ne u-ne _)) = ne! t-ne , ne! u-ne
