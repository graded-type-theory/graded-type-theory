------------------------------------------------------------------------
-- Some basic properties of the logical relation for neutrals and levels.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.Primitive
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet eqrel
open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Typed R
open import Definition.Typed.Properties.Reduction R
open import Definition.Typed.Properties.Well-formed R
open import Definition.LogicalRelation R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties.Whnf R ⦃ eqrel ⦄

open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    A B t u : Term _
    Γ : Con Term n

-- Transitivity for neutrals in WHNF and levels

transEqTermNe : ∀ {n n′ n″ A}
              → Γ ⊩neNf n  ≡ n′ ∷ A
              → Γ ⊩neNf n′ ≡ n″ ∷ A
              → Γ ⊩neNf n  ≡ n″ ∷ A
transEqTermNe (neNfₜ₌ inc neK neM k≡m) (neNfₜ₌ _ neK₁ neM₁ k≡m₁) =
  neNfₜ₌ inc neK neM₁ (~-trans k≡m k≡m₁)

mutual
  transEqTermLevel : ∀ {n n′ n″}
                   → Γ ⊩Level n  ≡ n′ ∷Level
                   → Γ ⊩Level n′ ≡ n″ ∷Level
                   → Γ ⊩Level n  ≡ n″ ∷Level
  transEqTermLevel (Levelₜ₌ k _ d d′ prop) (Levelₜ₌ _ k″ d₁ d″ prop₁)
    with whrDet*Term (d₁ , proj₁ (lsplit prop₁)) (d′ , proj₂ (lsplit prop))
  ... | PE.refl = Levelₜ₌ k k″ d d″ (transLevel-prop prop prop₁)

  transLevel-prop : ∀ {k k′ k″}
                    → [Level]-prop Γ k k′
                    → [Level]-prop Γ k′ k″
                    → [Level]-prop Γ k k″
  transLevel-prop zeroᵘᵣ zeroᵘᵣ = zeroᵘᵣ
  transLevel-prop (sucᵘᵣ x) (sucᵘᵣ x₁) = sucᵘᵣ (transEqTermLevel x x₁)
  transLevel-prop (neLvl x₂) (neLvl x₅) = neLvl (trans x₂ x₅)
  transLevel-prop zeroᵘᵣ (neLvl n) = case nelsplit n .proj₁ of λ { (ne ()) }
  transLevel-prop (sucᵘᵣ _) (neLvl n) = case nelsplit n .proj₁ of λ { (ne ()) }
  transLevel-prop (neLvl n) zeroᵘᵣ = case nelsplit n .proj₂ of λ { (ne ()) }
  transLevel-prop (neLvl n) (sucᵘᵣ _) = case nelsplit n .proj₂ of λ { (ne ()) }

-- Symmetry for neutrals in WHNF and levels

symNeutralTerm : ∀ {t u A}
               → Γ ⊩neNf t ≡ u ∷ A
               → Γ ⊩neNf u ≡ t ∷ A
symNeutralTerm (neNfₜ₌ inc neK neM k≡m) = neNfₜ₌ inc neM neK (~-sym k≡m)

mutual
  symLevel-prop : ∀ {k k′}
                → [Level]-prop Γ k k′
                → [Level]-prop Γ k′ k
  symLevel-prop zeroᵘᵣ = zeroᵘᵣ
  symLevel-prop (sucᵘᵣ x) = sucᵘᵣ (symLevel x)
  symLevel-prop (neLvl x) = neLvl (sym x)

  symLevel : ∀ {k k′}
           → Γ ⊩Level k ≡ k′ ∷Level
           → Γ ⊩Level k′ ≡ k ∷Level
  symLevel (Levelₜ₌ k k′ d d′ prop) =
    Levelₜ₌ k′ k d′ d (symLevel-prop prop)

-- Well-formedness for neutrals in WHNF and levels

wf-neNf : Γ ⊩neNf t ≡ u ∷ A → Γ ⊩neNf t ≡ t ∷ A × Γ ⊩neNf u ≡ u ∷ A
wf-neNf t≡u = transEqTermNe t≡u (symNeutralTerm t≡u) , transEqTermNe (symNeutralTerm t≡u) t≡u

wf-neLevel-prop : neLevel-prop Γ t → ⊢ Γ
wf-neLevel-prop (maxᵘˡᵣ x₁ x₂) = wf-neLevel-prop x₁
wf-neLevel-prop (maxᵘʳᵣ x₁ x₂) = wf-neLevel-prop x₂
wf-neLevel-prop (ne (neNfₜ₌ _ neK neM k≡m)) = wfEqTerm (≅ₜ-eq (~-to-≅ₜ k≡m))

mutual
  wf-Level-eq : Γ ⊩Level t ≡ u ∷Level → Γ ⊩Level t ∷Level × Γ ⊩Level u ∷Level
  wf-Level-eq (Levelₜ₌ k k′ d d′ prop) =
    let x , y = wf-[Level]-prop prop
    in Levelₜ k d x , Levelₜ k′ d′ y

  wf-[Level]-prop : [Level]-prop Γ t u → Level-prop Γ t × Level-prop Γ u
  wf-[Level]-prop zeroᵘᵣ = zeroᵘᵣ , zeroᵘᵣ
  wf-[Level]-prop (sucᵘᵣ x) = let a , b = wf-Level-eq x in sucᵘᵣ a , sucᵘᵣ b
  wf-[Level]-prop (neLvl t≡u) = let [t] , [u] = wf-[neLevel]-prop t≡u in neLvl [t] , neLvl [u]

  wf-[neLevel]-prop : [neLevel]-prop Γ t u → neLevel-prop Γ t × neLevel-prop Γ u
  wf-[neLevel]-prop (maxᵘˡᵣ k₁≡k₁′ k₂≡k₂′) =
    let [k₁] , [k₁′] = wf-[neLevel]-prop k₁≡k₁′
        [k₂] , [k₂′] = wf-Level-eq k₂≡k₂′
    in maxᵘˡᵣ [k₁] [k₂] , maxᵘˡᵣ [k₁′] [k₂′]
  wf-[neLevel]-prop (maxᵘʳᵣ k₁≡k₁′ k₂≡k₂′) =
    let [k₁] , [k₁′] = wf-Level-eq k₁≡k₁′
        [k₂] , [k₂′] = wf-[neLevel]-prop k₂≡k₂′
    in maxᵘʳᵣ [k₁] [k₂] , maxᵘʳᵣ [k₁′] [k₂′]
  wf-[neLevel]-prop (maxᵘ-zeroʳˡᵣ k≡k) =
    let [k] = wf-[neLevel]-prop k≡k .proj₁
    in maxᵘˡᵣ [k] (Levelₜ _ (id (zeroᵘⱼ (wf-neLevel-prop [k]))) zeroᵘᵣ) , [k]
  wf-[neLevel]-prop (ne x) =
    let a , b = wf-neNf x
    in ne a , ne b
  wf-[neLevel]-prop (sym u≡t) =
    let [u] , [t] = wf-[neLevel]-prop u≡t
    in [t] , [u]
  wf-[neLevel]-prop (trans x y) =
    let [t] , _ = wf-[neLevel]-prop x
        _ , [u] = wf-[neLevel]-prop y
    in [t] , [u]
