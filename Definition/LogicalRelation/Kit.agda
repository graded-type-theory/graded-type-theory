------------------------------------------------------------------------
-- Helper functions for working with kit of the Logical Relation
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Kit
  {a} {Mod : Set a}
  {𝕄 : Modality Mod}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped Mod as U hiding (K)
open import Definition.Untyped.Neutral Mod type-variant
open import Definition.Typed.Properties R
open import Definition.Typed R
open import Definition.Typed.Weakening R
open import Definition.LogicalRelation R

open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat using
  (Nat; 1+; _<′_; ≤′-step; ≤′-refl; _⊔_; _≤′_;
    <⇒<′; s≤s; ≤′⇒≤; ≤⇒≤′; ≤⇒pred≤; m≤n⇒m≤n⊔o′;
    m≤n⇒m≤o⊔n′; ≤→<s)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Unit

private
  variable
    p q : Mod
    ℓ l n : Nat
    Γ Δ : Con Term ℓ
    t t′ u u′ : Term _
    ρ : Wk _ _
    s : Strength

emb-⊩ : {l′ l : TypeLevel} {Γ : Con Term ℓ} {A : Term ℓ} → l′ < l → Γ ⊩⟨ l′ ⟩ A → Γ ⊩⟨ l ⟩ A
emb-⊩ p A = emb p (lemma p A)
  where
  lemma : {l′ l : TypeLevel} {Γ : Con Term ℓ} {A : Term ℓ} → (p : l′ < l) → Γ ⊩⟨ l′ ⟩ A → LogRelKit._⊩_ (kit′ p) Γ A
  lemma ≤′-refl A = A
  lemma (≤′-step p) A = lemma p A

emb-⊩≤ : {l′ l : TypeLevel} {Γ : Con Term ℓ} {A : Term ℓ} → l′ ≤ l → Γ ⊩⟨ l′ ⟩ A → Γ ⊩⟨ l ⟩ A
emb-⊩≤ ≤′-refl A = A
emb-⊩≤ (≤′-step p) A = emb (≤→<s p) (lemma (≤→<s p) A)
  where
  lemma : {l′ l : TypeLevel} {Γ : Con Term ℓ} {A : Term ℓ} → (p : l′ < l) → Γ ⊩⟨ l′ ⟩ A → LogRelKit._⊩_ (kit′ p) Γ A
  lemma ≤′-refl A = A
  lemma (≤′-step p) A = lemma p A

opaque

  -- If l′<l : l′ < l, then kit l′ is equal to kit′ l′<l.

  kit≡kit′ : ∀ {l′} (l′<l : l′ < l) → kit l′ PE.≡ kit′ l′<l
  kit≡kit′ ≤′-refl = PE.refl
  kit≡kit′ (≤′-step p) = kit≡kit′ p

opaque
  kitIneq : {Γ : Con Term n} {t : Term n} {l l' l'' : TypeLevel} (p : l < l')
    → (q : l < l'') → LogRelKit._⊩_ (kit′ p) Γ t → LogRelKit._⊩_ (kit′ q) Γ t
  kitIneq  ≤′-refl ≤′-refl t = t
  kitIneq p (≤′-step q) t = kitIneq p q t
  kitIneq (≤′-step p) q t = kitIneq p q t

opaque
  unfolding kitIneq

  kitIneqEq : {Γ : Con Term n} {t u : Term n} {l l' l'' : TypeLevel} (p : l < l')
      → (q : l < l'') ([t] : LogRelKit._⊩_ (kit′ p) Γ t) → LogRelKit._⊩_≡_/_ (kit′ p) Γ t u [t]
      → LogRelKit._⊩_≡_/_ (kit′ q) Γ t u (kitIneq p q [t])
  kitIneqEq ≤′-refl ≤′-refl [t] eq = eq
  kitIneqEq (≤′-step p) ≤′-refl [t] eq = kitIneqEq p ≤′-refl [t] eq
  kitIneqEq ≤′-refl (≤′-step q) [t] eq = kitIneqEq ≤′-refl q [t] eq
  kitIneqEq (≤′-step p) (≤′-step q) [t] eq = kitIneqEq (≤′-step p) q [t] eq

kitToLogRel : {l′ l : TypeLevel} {Γ : Con Term n} {A : Term n}
              → (p : l′ < l) → LogRelKit._⊩_ (kit′ p) Γ A  → Γ ⊩⟨ l′ ⟩ A
kitToLogRel ≤′-refl A = A
kitToLogRel (≤′-step p) A = kitToLogRel p A
