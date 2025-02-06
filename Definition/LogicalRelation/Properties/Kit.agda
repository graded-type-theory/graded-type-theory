------------------------------------------------------------------------
-- Some definitions related to kit and kit′
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.Kit
  {a} {Mod : Set a}
  {𝕄 : Modality Mod}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped Mod as U hiding (K)
open import Definition.Untyped.Properties Mod
open import Definition.LogicalRelation R

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  l l₁ l₂ n : Nat
  Γ         : Con Term _
  A B       : Term _

-- A variant of _⊩⟨_⟩_.

infix 4 _⊩<⟨_⟩_

_⊩<⟨_⟩_ : Con Term n → l₁ <ᵘ l₂ → Term n → Set a
Γ ⊩<⟨ p ⟩ A = LogRelKit._⊩_ (kit′ p) Γ A

-- A variant of _⊩⟨_⟩_≡_/_.

infix 4 _⊩<⟨_⟩_≡_/_

_⊩<⟨_⟩_≡_/_ :
  (Γ : Con Term n) (p : l₁ <ᵘ l₂) (A _ : Term n) → Γ ⊩<⟨ p ⟩ A → Set a
Γ ⊩<⟨ p ⟩ A ≡ B / ⊩A = LogRelKit._⊩_≡_/_ (kit′ p) Γ A B ⊩A

-- If p : l₁ <ᵘ l₂, then Γ ⊩<⟨ p ⟩ A is logically equivalent to
-- Γ ⊩⟨ l₁ ⟩ A.

⊩<⇔⊩ : (p : l₁ <ᵘ l₂) → Γ ⊩<⟨ p ⟩ A ⇔ Γ ⊩⟨ l₁ ⟩ A
⊩<⇔⊩ ≤ᵘ-refl     = id⇔
⊩<⇔⊩ (≤ᵘ-step p) = ⊩<⇔⊩ p

-- If p : l₁ <ᵘ l₂ and ⊩A : Γ ⊩<⟨ p ⟩ A, then Γ ⊩<⟨ p ⟩ A ≡ B / ⊩A is
-- logically equivalent to Γ ⊩⟨ l₁ ⟩ A ≡ B / ⊩<⇔⊩ p .proj₁ ⊩A.

⊩<≡⇔⊩≡ :
  (p : l₁ <ᵘ l₂) {⊩A : Γ ⊩<⟨ p ⟩ A} →
  Γ ⊩<⟨ p ⟩ A ≡ B / ⊩A ⇔ Γ ⊩⟨ l₁ ⟩ A ≡ B / ⊩<⇔⊩ p .proj₁ ⊩A
⊩<≡⇔⊩≡ ≤ᵘ-refl     = id⇔
⊩<≡⇔⊩≡ (≤ᵘ-step p) = ⊩<≡⇔⊩≡ p

-- A variant of ⊩<≡⇔⊩≡.

⊩<≡⇔⊩≡′ :
  (p : l₁ <ᵘ l₂) {⊩A : Γ ⊩⟨ l₁ ⟩ A} →
  Γ ⊩<⟨ p ⟩ A ≡ B / ⊩<⇔⊩ p .proj₂ ⊩A ⇔ Γ ⊩⟨ l₁ ⟩ A ≡ B / ⊩A
⊩<≡⇔⊩≡′ ≤ᵘ-refl     = id⇔
⊩<≡⇔⊩≡′ (≤ᵘ-step p) = ⊩<≡⇔⊩≡′ p

-- If l₁ <ᵘ l₂, then Γ ⊩⟨ l₁ ⟩ A is contained in Γ ⊩⟨ l₂ ⟩ A.

emb-<-⊩ : l₁ <ᵘ l₂ → Γ ⊩⟨ l₁ ⟩ A → Γ ⊩⟨ l₂ ⟩ A
emb-<-⊩ p = emb p ∘→ ⊩<⇔⊩ p .proj₂

opaque

  -- If l₁ ≤ᵘ l₂, then Γ ⊩⟨ l₁ ⟩ A is contained in Γ ⊩⟨ l₂ ⟩ A.

  emb-≤-⊩ : l₁ ≤ᵘ l₂ → Γ ⊩⟨ l₁ ⟩ A → Γ ⊩⟨ l₂ ⟩ A
  emb-≤-⊩ ≤ᵘ-refl     = idᶠ
  emb-≤-⊩ (≤ᵘ-step p) = emb (1+≤ᵘ1+ p) ∘→ ⊩<⇔⊩ (1+≤ᵘ1+ p) .proj₂

opaque

  -- If p : l₁ <ᵘ l₂, then kit l₁ is equal to kit′ p.

  kit≡kit′ : (p : l₁ <ᵘ l₂) → kit l₁ PE.≡ kit′ p
  kit≡kit′ ≤ᵘ-refl     = PE.refl
  kit≡kit′ (≤ᵘ-step p) = kit≡kit′ p

opaque

  -- Irrelevance for _⊩<⟨_⟩_.

  irrelevance-⊩< :
    (p : l <ᵘ l₁) (q : l <ᵘ l₂) → Γ ⊩<⟨ p ⟩ A → Γ ⊩<⟨ q ⟩ A
  irrelevance-⊩<  ≤ᵘ-refl    ≤ᵘ-refl     = idᶠ
  irrelevance-⊩< p           (≤ᵘ-step q) = irrelevance-⊩< p q
  irrelevance-⊩< (≤ᵘ-step p) q           = irrelevance-⊩< p q

opaque
  unfolding irrelevance-⊩<

  -- One form of irrelevance for _⊩<⟨_⟩_≡_/_.

  irrelevance-⊩<≡ :
    (p : l <ᵘ l₁) (q : l <ᵘ l₂) {⊩A : Γ ⊩<⟨ p ⟩ A} →
    Γ ⊩<⟨ p ⟩ A ≡ B / ⊩A →
    Γ ⊩<⟨ q ⟩ A ≡ B / irrelevance-⊩< p q ⊩A
  irrelevance-⊩<≡ ≤ᵘ-refl     ≤ᵘ-refl     = idᶠ
  irrelevance-⊩<≡ (≤ᵘ-step p) ≤ᵘ-refl     = irrelevance-⊩<≡ p ≤ᵘ-refl
  irrelevance-⊩<≡ ≤ᵘ-refl     (≤ᵘ-step q) = irrelevance-⊩<≡ ≤ᵘ-refl q
  irrelevance-⊩<≡ (≤ᵘ-step p) (≤ᵘ-step q) =
    irrelevance-⊩<≡ (≤ᵘ-step p) q
