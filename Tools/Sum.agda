-- Disjoint sum type; also used as logical disjunction.

module Tools.Sum where

open import Tools.Level

data _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

-- Idempotency.

id : ∀ {a} {A : Set a} → A ⊎ A → A
id (inj₁ x) = x
id (inj₂ x) = x

-- Symmetry.

sym : ∀ {a b} {A : Set a} {B : Set b} → A ⊎ B → B ⊎ A
sym (inj₁ x) = inj₂ x
sym (inj₂ x) = inj₁ x

-- Eliminator

cases : ∀ {A B C : Set} → A ⊎ B → (A → C) → (B → C) → C
cases (inj₁ x) f g = f x
cases (inj₂ x) f g = g x
