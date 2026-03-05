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
open import Definition.LogicalRelation R ⦃ eqrel ⦄

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  m n           : Nat
  l l₁ l₂ k₁ k₂ : Universe-level
  Γ             : Cons _ _
  A B t u       : Term _

-- A variant of _⊩⟨_⟩_.

infix 4 _⊩<⟨_⟩_

_⊩<⟨_⟩_ : Cons m n → l₁ <ᵘ l₂ → Term n → Set a
Γ ⊩<⟨ p ⟩ A = LogRelKit._⊩_ (kit′ p) Γ A

-- A variant of _⊩⟨_⟩_≡_/_.

infix 4 _⊩<⟨_⟩_≡_/_

_⊩<⟨_⟩_≡_/_ :
  (Γ : Cons m n) (p : l₁ <ᵘ l₂) (A _ : Term n) → Γ ⊩<⟨ p ⟩ A → Set a
Γ ⊩<⟨ p ⟩ A ≡ B / ⊩A = LogRelKit._⊩_≡_/_ (kit′ p) Γ A B ⊩A

-- A variant of _⊩⟨_⟩_∷_/_.

infix 4 _⊩<⟨_⟩_∷_/_

_⊩<⟨_⟩_∷_/_ :
  (Γ : Cons m n) (p : l₁ <ᵘ l₂) (t A : Term n) → Γ ⊩<⟨ p ⟩ A → Set a
Γ ⊩<⟨ p ⟩ t ∷ A / ⊩A = LogRelKit._⊩_∷_/_ (kit′ p) Γ t A ⊩A

-- A variant of _⊩⟨_⟩_≡_∷_/_.

infix 4 _⊩<⟨_⟩_≡_∷_/_

_⊩<⟨_⟩_≡_∷_/_ :
  (Γ : Cons m n) (p : l₁ <ᵘ l₂) (t u : Term n) (A : Term n) →
  Γ ⊩<⟨ p ⟩ A → Set a
Γ ⊩<⟨ p ⟩ t ≡ u ∷ A / ⊩A = LogRelKit._⊩_≡_∷_/_ (kit′ p) Γ t u A ⊩A

-- If p : l₁ <ᵘ l₂, then Γ ⊩<⟨ p ⟩ A is logically equivalent to
-- Γ ⊩⟨ l₁ ⟩ A.

⊩<⇔⊩ : (p : l₁ <ᵘ l₂) → Γ ⊩<⟨ p ⟩ A ⇔ Γ ⊩⟨ l₁ ⟩ A
⊩<⇔⊩ (0ᵘ+<ᵘ0ᵘ+ ≤′-refl)     = id⇔
⊩<⇔⊩ (0ᵘ+<ᵘ0ᵘ+ (≤′-step p)) = ⊩<⇔⊩ (0ᵘ+<ᵘ0ᵘ+ p)
⊩<⇔⊩ 0ᵘ+<ᵘωᵘ+               = id⇔
⊩<⇔⊩ (ωᵘ+<ᵘωᵘ+ ≤′-refl)     = id⇔
⊩<⇔⊩ (ωᵘ+<ᵘωᵘ+ (≤′-step p)) = ⊩<⇔⊩ (ωᵘ+<ᵘωᵘ+ p)
⊩<⇔⊩ 0ᵘ+<ᵘωᵘ·2              = id⇔
⊩<⇔⊩ ωᵘ+<ᵘωᵘ·2              = id⇔

-- If p : l₁ <ᵘ l₂ and ⊩A : Γ ⊩<⟨ p ⟩ A, then Γ ⊩<⟨ p ⟩ A ≡ B / ⊩A is
-- logically equivalent to Γ ⊩⟨ l₁ ⟩ A ≡ B / ⊩<⇔⊩ p .proj₁ ⊩A.

⊩<≡⇔⊩≡ :
  (p : l₁ <ᵘ l₂) {⊩A : Γ ⊩<⟨ p ⟩ A} →
  Γ ⊩<⟨ p ⟩ A ≡ B / ⊩A ⇔ Γ ⊩⟨ l₁ ⟩ A ≡ B / ⊩<⇔⊩ p .proj₁ ⊩A
⊩<≡⇔⊩≡ (0ᵘ+<ᵘ0ᵘ+ ≤′-refl)     = id⇔
⊩<≡⇔⊩≡ (0ᵘ+<ᵘ0ᵘ+ (≤′-step p)) = ⊩<≡⇔⊩≡ (0ᵘ+<ᵘ0ᵘ+ p)
⊩<≡⇔⊩≡ 0ᵘ+<ᵘωᵘ+               = id⇔
⊩<≡⇔⊩≡ (ωᵘ+<ᵘωᵘ+ ≤′-refl)     = id⇔
⊩<≡⇔⊩≡ (ωᵘ+<ᵘωᵘ+ (≤′-step p)) = ⊩<≡⇔⊩≡ (ωᵘ+<ᵘωᵘ+ p)
⊩<≡⇔⊩≡ 0ᵘ+<ᵘωᵘ·2              = id⇔
⊩<≡⇔⊩≡ ωᵘ+<ᵘωᵘ·2              = id⇔

-- A variant of ⊩<≡⇔⊩≡.

⊩<≡⇔⊩≡′ :
  (p : l₁ <ᵘ l₂) {⊩A : Γ ⊩⟨ l₁ ⟩ A} →
  Γ ⊩<⟨ p ⟩ A ≡ B / ⊩<⇔⊩ p .proj₂ ⊩A ⇔ Γ ⊩⟨ l₁ ⟩ A ≡ B / ⊩A
⊩<≡⇔⊩≡′ (0ᵘ+<ᵘ0ᵘ+ ≤′-refl)     = id⇔
⊩<≡⇔⊩≡′ (0ᵘ+<ᵘ0ᵘ+ (≤′-step p)) = ⊩<≡⇔⊩≡′ (0ᵘ+<ᵘ0ᵘ+ p)
⊩<≡⇔⊩≡′ 0ᵘ+<ᵘωᵘ+               = id⇔
⊩<≡⇔⊩≡′ (ωᵘ+<ᵘωᵘ+ ≤′-refl)     = id⇔
⊩<≡⇔⊩≡′ (ωᵘ+<ᵘωᵘ+ (≤′-step p)) = ⊩<≡⇔⊩≡′ (ωᵘ+<ᵘωᵘ+ p)
⊩<≡⇔⊩≡′ 0ᵘ+<ᵘωᵘ·2              = id⇔
⊩<≡⇔⊩≡′ ωᵘ+<ᵘωᵘ·2              = id⇔

-- If p : l₁ <ᵘ l₂ and ⊩A : Γ ⊩<⟨ p ⟩ A, then Γ ⊩<⟨ p ⟩ t ∷ A / ⊩A is
-- logically equivalent to Γ ⊩⟨ l₁ ⟩ t ∷ A / ⊩<⇔⊩ p .proj₁ ⊩A.

⊩<∷⇔⊩∷ :
  (p : l₁ <ᵘ l₂) {⊩A : Γ ⊩<⟨ p ⟩ A} →
  Γ ⊩<⟨ p ⟩ t ∷ A / ⊩A ⇔ Γ ⊩⟨ l₁ ⟩ t ∷ A / ⊩<⇔⊩ p .proj₁ ⊩A
⊩<∷⇔⊩∷ (0ᵘ+<ᵘ0ᵘ+ ≤′-refl)     = id⇔
⊩<∷⇔⊩∷ (0ᵘ+<ᵘ0ᵘ+ (≤′-step p)) = ⊩<∷⇔⊩∷ (0ᵘ+<ᵘ0ᵘ+ p)
⊩<∷⇔⊩∷ 0ᵘ+<ᵘωᵘ+               = id⇔
⊩<∷⇔⊩∷ (ωᵘ+<ᵘωᵘ+ ≤′-refl)     = id⇔
⊩<∷⇔⊩∷ (ωᵘ+<ᵘωᵘ+ (≤′-step p)) = ⊩<∷⇔⊩∷ (ωᵘ+<ᵘωᵘ+ p)
⊩<∷⇔⊩∷ 0ᵘ+<ᵘωᵘ·2              = id⇔
⊩<∷⇔⊩∷ ωᵘ+<ᵘωᵘ·2              = id⇔

-- A variant of ⊩<∷⇔⊩∷.

⊩<∷⇔⊩∷′ :
  (p : l₁ <ᵘ l₂) {⊩A : Γ ⊩⟨ l₁ ⟩ A} →
  Γ ⊩<⟨ p ⟩ t ∷ A / ⊩<⇔⊩ p .proj₂ ⊩A ⇔ Γ ⊩⟨ l₁ ⟩ t ∷ A / ⊩A
⊩<∷⇔⊩∷′ (0ᵘ+<ᵘ0ᵘ+ ≤′-refl)     = id⇔
⊩<∷⇔⊩∷′ (0ᵘ+<ᵘ0ᵘ+ (≤′-step p)) = ⊩<∷⇔⊩∷′ (0ᵘ+<ᵘ0ᵘ+ p)
⊩<∷⇔⊩∷′ 0ᵘ+<ᵘωᵘ+               = id⇔
⊩<∷⇔⊩∷′ (ωᵘ+<ᵘωᵘ+ ≤′-refl)     = id⇔
⊩<∷⇔⊩∷′ (ωᵘ+<ᵘωᵘ+ (≤′-step p)) = ⊩<∷⇔⊩∷′ (ωᵘ+<ᵘωᵘ+ p)
⊩<∷⇔⊩∷′ 0ᵘ+<ᵘωᵘ·2              = id⇔
⊩<∷⇔⊩∷′ ωᵘ+<ᵘωᵘ·2              = id⇔

-- If p : l₁ <ᵘ l₂ and ⊩A : Γ ⊩<⟨ p ⟩ A, then Γ ⊩<⟨ p ⟩ t ≡ u ∷ A / ⊩A is
-- logically equivalent to Γ ⊩⟨ l₁ ⟩ t ≡ u ∷ A / ⊩<⇔⊩ p .proj₁ ⊩A.

⊩<≡∷⇔⊩≡∷ :
  (p : l₁ <ᵘ l₂) {⊩A : Γ ⊩<⟨ p ⟩ A} →
  Γ ⊩<⟨ p ⟩ t ≡ u ∷ A / ⊩A ⇔ Γ ⊩⟨ l₁ ⟩ t ≡ u ∷ A / ⊩<⇔⊩ p .proj₁ ⊩A
⊩<≡∷⇔⊩≡∷ (0ᵘ+<ᵘ0ᵘ+ ≤′-refl)     = id⇔
⊩<≡∷⇔⊩≡∷ (0ᵘ+<ᵘ0ᵘ+ (≤′-step p)) = ⊩<≡∷⇔⊩≡∷ (0ᵘ+<ᵘ0ᵘ+ p)
⊩<≡∷⇔⊩≡∷ 0ᵘ+<ᵘωᵘ+               = id⇔
⊩<≡∷⇔⊩≡∷ (ωᵘ+<ᵘωᵘ+ ≤′-refl)     = id⇔
⊩<≡∷⇔⊩≡∷ (ωᵘ+<ᵘωᵘ+ (≤′-step p)) = ⊩<≡∷⇔⊩≡∷ (ωᵘ+<ᵘωᵘ+ p)
⊩<≡∷⇔⊩≡∷ 0ᵘ+<ᵘωᵘ·2              = id⇔
⊩<≡∷⇔⊩≡∷ ωᵘ+<ᵘωᵘ·2              = id⇔

-- A variant of ⊩<≡∷⇔⊩≡∷.

⊩<≡∷⇔⊩≡∷′ :
  (p : l₁ <ᵘ l₂) {⊩A : Γ ⊩⟨ l₁ ⟩ A} →
  Γ ⊩<⟨ p ⟩ t ≡ u ∷ A / ⊩<⇔⊩ p .proj₂ ⊩A ⇔ Γ ⊩⟨ l₁ ⟩ t ≡ u ∷ A / ⊩A
⊩<≡∷⇔⊩≡∷′ (0ᵘ+<ᵘ0ᵘ+ ≤′-refl)     = id⇔
⊩<≡∷⇔⊩≡∷′ (0ᵘ+<ᵘ0ᵘ+ (≤′-step p)) = ⊩<≡∷⇔⊩≡∷′ (0ᵘ+<ᵘ0ᵘ+ p)
⊩<≡∷⇔⊩≡∷′ 0ᵘ+<ᵘωᵘ+               = id⇔
⊩<≡∷⇔⊩≡∷′ (ωᵘ+<ᵘωᵘ+ ≤′-refl)     = id⇔
⊩<≡∷⇔⊩≡∷′ (ωᵘ+<ᵘωᵘ+ (≤′-step p)) = ⊩<≡∷⇔⊩≡∷′ (ωᵘ+<ᵘωᵘ+ p)
⊩<≡∷⇔⊩≡∷′ 0ᵘ+<ᵘωᵘ·2              = id⇔
⊩<≡∷⇔⊩≡∷′ ωᵘ+<ᵘωᵘ·2              = id⇔

opaque

  -- If p : l₁ <ᵘ l₂, then kit l₁ is equal to kit′ p.

  kit≡kit′ : (p : l₁ <ᵘ l₂) → kit l₁ PE.≡ kit′ p
  kit≡kit′ (0ᵘ+<ᵘ0ᵘ+ ≤′-refl)     = PE.refl
  kit≡kit′ (0ᵘ+<ᵘ0ᵘ+ (≤′-step p)) = kit≡kit′ (0ᵘ+<ᵘ0ᵘ+ p)
  kit≡kit′ 0ᵘ+<ᵘωᵘ+               = PE.refl
  kit≡kit′ (ωᵘ+<ᵘωᵘ+ ≤′-refl)     = PE.refl
  kit≡kit′ (ωᵘ+<ᵘωᵘ+ (≤′-step p)) = kit≡kit′ (ωᵘ+<ᵘωᵘ+ p)
  kit≡kit′ 0ᵘ+<ᵘωᵘ·2              = PE.refl
  kit≡kit′ ωᵘ+<ᵘωᵘ·2              = PE.refl

opaque

  -- Irrelevance for _⊩<⟨_⟩_.

  irrelevance-⊩< :
    (eq : k₁ PE.≡ k₂) (p : k₁ <ᵘ l₁) (q : k₂ <ᵘ l₂) → Γ ⊩<⟨ p ⟩ A → Γ ⊩<⟨ q ⟩ A
  irrelevance-⊩< PE.refl p q = ⊩<⇔⊩ q .proj₂ ∘→ ⊩<⇔⊩ p .proj₁

opaque
  unfolding irrelevance-⊩<

  -- One form of irrelevance for _⊩<⟨_⟩_≡_/_.

  irrelevance-⊩<≡ :
    ∀ {Γ : Cons m n} (eq : k₁ PE.≡ k₂) (p : k₁ <ᵘ l₁) (q : k₂ <ᵘ l₂)
      {⊩A : Γ ⊩<⟨ p ⟩ A} →
    Γ ⊩<⟨ p ⟩ A ≡ B / ⊩A →
    Γ ⊩<⟨ q ⟩ A ≡ B / irrelevance-⊩< eq p q ⊩A
  irrelevance-⊩<≡ PE.refl p q = ⊩<≡⇔⊩≡′ q .proj₂ ∘→ ⊩<≡⇔⊩≡ p .proj₁
