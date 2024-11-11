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
open import Definition.Untyped.Neutral Mod type-variant
open import Definition.Untyped.Properties Mod
open import Definition.Typed.Properties R
open import Definition.Typed R
open import Definition.Typed.Weakening R
open import Definition.LogicalRelation R {{eqrel}}

open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum
open import Tools.Unit

private variable
  n : Nat
  k₁ k₂ l l₁ l₂ : Universe-level
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

infix 4 _⊩<⟨_⟩_∷_/_

_⊩<⟨_⟩_∷_/_ :
  (Γ : Con Term n) (p : l₁ <ᵘ l₂) (t A : Term n) → Γ ⊩<⟨ p ⟩ A → Set a
Γ ⊩<⟨ p ⟩ t ∷ A / ⊩A = LogRelKit._⊩_∷_/_ (kit′ p) Γ t A ⊩A

infix 4 _⊩<⟨_⟩_≡_∷_/_

_⊩<⟨_⟩_≡_∷_/_ :
  (Γ : Con Term n) (p : l₁ <ᵘ l₂) (t u : Term n) (A : Term n) → Γ ⊩<⟨ p ⟩ A → Set a
Γ ⊩<⟨ p ⟩ t ≡ u ∷ A / ⊩A = LogRelKit._⊩_≡_∷_/_ (kit′ p) Γ t u A ⊩A

-- If p : l₁ <ᵘ l₂, then Γ ⊩<⟨ p ⟩ A is logically equivalent to
-- Γ ⊩⟨ l₁ ⟩ A.

⊩<⇔⊩ : (p : l₁ <ᵘ l₂) → Γ ⊩<⟨ p ⟩ A ⇔ Γ ⊩⟨ l₁ ⟩ A
⊩<⇔⊩ (<ᵘ-nat ≤′-refl) = id⇔
⊩<⇔⊩ (<ᵘ-nat (≤′-step p)) = ⊩<⇔⊩ (<ᵘ-nat p)
⊩<⇔⊩ <ᵘ-ω = id⇔

-- If p : l₁ <ᵘ l₂ and ⊩A : Γ ⊩<⟨ p ⟩ A, then Γ ⊩<⟨ p ⟩ A ≡ B / ⊩A is
-- logically equivalent to Γ ⊩⟨ l₁ ⟩ A ≡ B / ⊩<⇔⊩ p .proj₁ ⊩A.

⊩<≡⇔⊩≡ :
  (p : l₁ <ᵘ l₂) {⊩A : Γ ⊩<⟨ p ⟩ A} →
  Γ ⊩<⟨ p ⟩ A ≡ B / ⊩A ⇔ Γ ⊩⟨ l₁ ⟩ A ≡ B / ⊩<⇔⊩ p .proj₁ ⊩A
⊩<≡⇔⊩≡ (<ᵘ-nat ≤′-refl) = id⇔
⊩<≡⇔⊩≡ (<ᵘ-nat (≤′-step p)) = ⊩<≡⇔⊩≡ (<ᵘ-nat p)
⊩<≡⇔⊩≡ <ᵘ-ω = id⇔

-- A variant of ⊩<≡⇔⊩≡.

⊩<≡⇔⊩≡′ :
  (p : l₁ <ᵘ l₂) {⊩A : Γ ⊩⟨ l₁ ⟩ A} →
  Γ ⊩<⟨ p ⟩ A ≡ B / ⊩<⇔⊩ p .proj₂ ⊩A ⇔ Γ ⊩⟨ l₁ ⟩ A ≡ B / ⊩A
⊩<≡⇔⊩≡′ (<ᵘ-nat ≤′-refl) = id⇔
⊩<≡⇔⊩≡′ (<ᵘ-nat (≤′-step p)) = ⊩<≡⇔⊩≡′ (<ᵘ-nat p)
⊩<≡⇔⊩≡′ <ᵘ-ω = id⇔

⊩<∷⇔⊩∷ :
  ∀ (p : l₁ <ᵘ l₂) {⊩A : Γ ⊩<⟨ p ⟩ A} {t} →
  Γ ⊩<⟨ p ⟩ t ∷ A / ⊩A ⇔ Γ ⊩⟨ l₁ ⟩ t ∷ A / ⊩<⇔⊩ p .proj₁ ⊩A
⊩<∷⇔⊩∷ (<ᵘ-nat ≤′-refl)     = id⇔
⊩<∷⇔⊩∷ (<ᵘ-nat (≤′-step p))     = ⊩<∷⇔⊩∷ (<ᵘ-nat p)
⊩<∷⇔⊩∷ <ᵘ-ω = id⇔

⊩<∷⇔⊩∷′ :
  ∀ (p : l₁ <ᵘ l₂) {⊩A : Γ ⊩⟨ l₁ ⟩ A} {t} →
  Γ ⊩<⟨ p ⟩ t ∷ A / ⊩<⇔⊩ p .proj₂ ⊩A ⇔ Γ ⊩⟨ l₁ ⟩ t ∷ A / ⊩A
⊩<∷⇔⊩∷′ (<ᵘ-nat ≤′-refl) = id⇔
⊩<∷⇔⊩∷′ (<ᵘ-nat (≤′-step p)) = ⊩<∷⇔⊩∷′ (<ᵘ-nat p)
⊩<∷⇔⊩∷′ <ᵘ-ω = id⇔

⊩<≡∷⇔⊩≡∷ :
  ∀ (p : l₁ <ᵘ l₂) {⊩A : Γ ⊩<⟨ p ⟩ A} {t u} →
  Γ ⊩<⟨ p ⟩ t ≡ u ∷ A / ⊩A ⇔ Γ ⊩⟨ l₁ ⟩ t ≡ u ∷ A / ⊩<⇔⊩ p .proj₁ ⊩A
⊩<≡∷⇔⊩≡∷ (<ᵘ-nat ≤′-refl) = id⇔
⊩<≡∷⇔⊩≡∷ (<ᵘ-nat (≤′-step p)) = ⊩<≡∷⇔⊩≡∷ (<ᵘ-nat p)
⊩<≡∷⇔⊩≡∷ <ᵘ-ω = id⇔

⊩<≡∷⇔⊩≡∷′ :
  ∀ (p : l₁ <ᵘ l₂) {⊩A : Γ ⊩⟨ l₁ ⟩ A} {t u} →
  Γ ⊩<⟨ p ⟩ t ≡ u ∷ A / ⊩<⇔⊩ p .proj₂ ⊩A ⇔ Γ ⊩⟨ l₁ ⟩ t ≡ u ∷ A / ⊩A
⊩<≡∷⇔⊩≡∷′ (<ᵘ-nat ≤′-refl) = id⇔
⊩<≡∷⇔⊩≡∷′ (<ᵘ-nat (≤′-step p)) = ⊩<≡∷⇔⊩≡∷′ (<ᵘ-nat p)
⊩<≡∷⇔⊩≡∷′ <ᵘ-ω = id⇔

-- If l₁ <ᵘ l₂, then Γ ⊩⟨ l₁ ⟩ A is contained in Γ ⊩⟨ l₂ ⟩ A.

emb-<-⊩ : l₁ <ᵘ l₂ → Γ ⊩⟨ l₁ ⟩ A → Γ ⊩⟨ l₂ ⟩ A
emb-<-⊩ p = emb p ∘→ ⊩<⇔⊩ p .proj₂

opaque

  -- If l₁ ≤ᵘ l₂, then Γ ⊩⟨ l₁ ⟩ A is contained in Γ ⊩⟨ l₂ ⟩ A.

  emb-≤-⊩ : l₁ ≤ᵘ l₂ → Γ ⊩⟨ l₁ ⟩ A → Γ ⊩⟨ l₂ ⟩ A
  emb-≤-⊩ p with ≤ᵘ→<ᵘ⊎≡ p
  ... | inj₁ l₁<l₂ = emb-<-⊩ l₁<l₂
  ... | inj₂ PE.refl = idᶠ

opaque

  -- If p : l₁ <ᵘ l₂, then kit l₁ is equal to kit′ p.

  kit≡kit′ : (p : l₁ <ᵘ l₂) → kit l₁ PE.≡ kit′ p
  kit≡kit′ (<ᵘ-nat ≤′-refl) = PE.refl
  kit≡kit′ (<ᵘ-nat (≤′-step p)) = kit≡kit′ (<ᵘ-nat p)
  kit≡kit′ <ᵘ-ω = PE.refl

opaque

  -- Irrelevance for _⊩<⟨_⟩_.

  irrelevance-⊩< :
    (eq : k₁ PE.≡ k₂) (p : k₁ <ᵘ l₁) (q : k₂ <ᵘ l₂) → Γ ⊩<⟨ p ⟩ A → Γ ⊩<⟨ q ⟩ A
  irrelevance-⊩< PE.refl p q = ⊩<⇔⊩ q .proj₂ ∘→ ⊩<⇔⊩ p .proj₁

opaque
  unfolding irrelevance-⊩<

  -- One form of irrelevance for _⊩<⟨_⟩_≡_/_.

  irrelevance-⊩<≡ :
    ∀ {Γ : Con Term n} (eq : k₁ PE.≡ k₂) (p : k₁ <ᵘ l₁) (q : k₂ <ᵘ l₂) {⊩A : Γ ⊩<⟨ p ⟩ A} →
    Γ ⊩<⟨ p ⟩ A ≡ B / ⊩A →
    Γ ⊩<⟨ q ⟩ A ≡ B / irrelevance-⊩< eq p q ⊩A
  irrelevance-⊩<≡ {B} PE.refl p q {⊩A} =
    ⊩<≡⇔⊩≡′ {B = B} q .proj₂ ∘→ ⊩<≡⇔⊩≡ {B = B} p {⊩A} .proj₁
