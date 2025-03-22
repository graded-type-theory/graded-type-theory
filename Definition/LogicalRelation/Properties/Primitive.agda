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
open import Definition.Typed.Properties.Reduction R
open import Definition.LogicalRelation R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties.Whnf R

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
  transEqTermSne : ∀ {n n′ n″}
                   → Γ ⊩sne n  ≡ n′
                   → Γ ⊩sne n′ ≡ n″
                   → Γ ⊩sne n  ≡ n″
  transEqTermSne (sneₜ₌ ne-n _ prop) (sneₜ₌ _ ne-n″ prop′) =
    sneₜ₌ ne-n ne-n″ (transSne-prop prop prop′)

  transEqTermLevel : ∀ {n n′ n″}
                   → Γ ⊩Level n  ≡ n′ ∷Level
                   → Γ ⊩Level n′ ≡ n″ ∷Level
                   → Γ ⊩Level n  ≡ n″ ∷Level
  transEqTermLevel (Levelₜ₌ k _ d d′ prop) (Levelₜ₌ _ k″ d₁ d″ prop₁)
    with whrDet*Term (d₁ , proj₁ (lsplit prop₁)) (d′ , proj₂ (lsplit prop))
  ... | PE.refl = Levelₜ₌ k k″ d d″ (transLevel-prop prop prop₁)

  transSne-prop : ∀ {k k′ k″}
                    → [sne]-prop Γ k k′
                    → [sne]-prop Γ k′ k″
                    → [sne]-prop Γ k k″
  transSne-prop (maxᵘᵣ x y) (maxᵘᵣ z w) = maxᵘᵣ (transEqTermLevel x z) (transEqTermLevel y w)
  transSne-prop (ne x)      (ne y)      = ne (transEqTermNe x y)
  transSne-prop (maxᵘᵣ x y) (ne (neNfₜ₌ _ () _ _))
  transSne-prop (ne (neNfₜ₌ _ _ () _)) (maxᵘᵣ y z)

  transLevel-prop : ∀ {k k′ k″}
                    → [Level]-prop Γ k k′
                    → [Level]-prop Γ k′ k″
                    → [Level]-prop Γ k k″
  transLevel-prop zeroᵘᵣ y = y
  transLevel-prop (sucᵘᵣ x) (sucᵘᵣ y) = sucᵘᵣ (transEqTermLevel x y)
  transLevel-prop (ne x) (ne y) = ne (transEqTermSne x y)
  transLevel-prop (sucᵘᵣ x) (ne (sneₜ₌ (ne ()) _ _))
  transLevel-prop (ne (sneₜ₌ _ (ne ()) _)) zeroᵘᵣ
  transLevel-prop (ne (sneₜ₌ _ (ne ()) _)) (sucᵘᵣ y)

-- Symmetry for neutrals in WHNF and levels

symNeutralTerm : ∀ {t u A}
               → Γ ⊩neNf t ≡ u ∷ A
               → Γ ⊩neNf u ≡ t ∷ A
symNeutralTerm (neNfₜ₌ inc neK neM k≡m) = neNfₜ₌ inc neM neK (~-sym k≡m)

mutual
  symSne-prop : ∀ {k k′}
                → [sne]-prop Γ k k′
                → [sne]-prop Γ k′ k
  symSne-prop (maxᵘᵣ x y) = maxᵘᵣ (symLevel x) (symLevel y)
  symSne-prop (ne x) = ne (symNeutralTerm x)

  symLevel-prop : ∀ {k k′}
                → [Level]-prop Γ k k′
                → [Level]-prop Γ k′ k
  symLevel-prop zeroᵘᵣ = zeroᵘᵣ
  symLevel-prop (sucᵘᵣ x) = sucᵘᵣ (symLevel x)
  symLevel-prop (ne n) = ne (symSne n)

  symSne : ∀ {k k′}
         → Γ ⊩sne k ≡ k′
         → Γ ⊩sne k′ ≡ k
  symSne (sneₜ₌ a b prop) = sneₜ₌ b a (symSne-prop prop)

  symLevel : ∀ {k k′}
           → Γ ⊩Level k ≡ k′ ∷Level
           → Γ ⊩Level k′ ≡ k ∷Level
  symLevel (Levelₜ₌ k k′ d d′ prop) =
    Levelₜ₌ k′ k d′ d (symLevel-prop prop)

-- Well-formedness for levels

wf-⊩Level : Γ ⊩Level t ≡ u ∷Level → Γ ⊩Level t ∷Level × Γ ⊩Level u ∷Level
wf-⊩Level t≡u =
    transEqTermLevel t≡u (symLevel t≡u)
  , transEqTermLevel (symLevel t≡u) t≡u
