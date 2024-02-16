------------------------------------------------------------------------
-- Martin-Löf identity type without the K axiom
-- (we do not assume uniqueness of identity proofs).
------------------------------------------------------------------------

module Tools.PropositionalEquality where

-- We reexport Agda's builtin equality type.

open import Tools.Level
open import Tools.Product
open import Tools.Relation

import Relation.Binary.PropositionalEquality as Eq
open Eq using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂;
   isEquivalence; setoid)
  public

private variable
  a                                   : Level
  A B C D E F G                       : Set _
  a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ f₁ f₂ : A

-- Non-dependent congruence rules.

cong₃ : ∀ {ℓ} {A B C D : Set ℓ} {a a′ b b′ c c′}
        (f : A → B → C → D) → a ≡ a′ → b ≡ b′ → c ≡ c′
      → f a b c ≡ f a′ b′ c′
cong₃ f refl refl refl = refl

cong₄ : ∀ {ℓ} {A B C D E : Set ℓ} {a a′ b b′ c c′ d d′}
        (f : A → B → C → D → E) → a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′
      → f a b c d ≡ f a′ b′ c′ d′
cong₄ f refl refl refl refl = refl

cong₅ :
  (f : A → B → C → D → E → F) →
  a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → d₁ ≡ d₂ → e₁ ≡ e₂ →
  f a₁ b₁ c₁ d₁ e₁ ≡ f a₂ b₂ c₂ d₂ e₂
cong₅ f refl refl refl refl refl = refl

cong₆ :
  (f : A → B → C → D → E → F → G) →
  a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → d₁ ≡ d₂ → e₁ ≡ e₂ → f₁ ≡ f₂ →
  f a₁ b₁ c₁ d₁ e₁ f₁ ≡ f a₂ b₂ c₂ d₂ e₂ f₂
cong₆ f refl refl refl refl refl refl = refl

-- Substitution (type-cast).

-- Three substitutions simultaneously.

subst₃ : ∀ {ℓ ℓ′ ℓ″ ℓ‴} {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″} {a a′ b b′ c c′} (F : A → B → C → Set ℓ‴)
       → a ≡ a′ → b ≡ b′ → c ≡ c′ → F a b c → F a′ b′ c′
subst₃ F refl refl refl f = f

-- The property of being a proposition.

Is-proposition : Set a → Set a
Is-proposition A = {x y : A} → x ≡ y

-- The property of being a set.

Is-set : Set a → Set a
Is-set A = {x y : A} → Is-proposition (x ≡ y)

-- If A is inhabited, then a corresponding "singleton type" is
-- inhabited.

singleton : (x : A) → ∃ λ (y : A) → x ≡ y
singleton x = x , refl
