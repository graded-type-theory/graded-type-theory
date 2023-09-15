------------------------------------------------------------------------
-- Martin-Löf identity type without the K axiom
-- (we do not assume uniqueness of identity proofs).
------------------------------------------------------------------------

module Tools.PropositionalEquality where

-- We reexport Agda's builtin equality type.

open import Tools.Relation

import Relation.Binary.PropositionalEquality as Eq
open Eq using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂;
   isEquivalence; setoid)
  public

-- Non-dependent congruence rules.

cong₃ : ∀ {ℓ} {A B C D : Set ℓ} {a a′ b b′ c c′}
        (f : A → B → C → D) → a ≡ a′ → b ≡ b′ → c ≡ c′
      → f a b c ≡ f a′ b′ c′
cong₃ f refl refl refl = refl

cong₄ : ∀ {ℓ} {A B C D E : Set ℓ} {a a′ b b′ c c′ d d′}
        (f : A → B → C → D → E) → a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′
      → f a b c d ≡ f a′ b′ c′ d′
cong₄ f refl refl refl refl = refl

-- Substitution (type-cast).

-- Three substitutions simultaneously.

subst₃ : ∀ {ℓ ℓ′ ℓ″ ℓ‴} {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″} {a a′ b b′ c c′} (F : A → B → C → Set ℓ‴)
       → a ≡ a′ → b ≡ b′ → c ≡ c′ → F a b c → F a′ b′ c′
subst₃ F refl refl refl f = f
