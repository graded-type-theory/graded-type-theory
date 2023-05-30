------------------------------------------------------------------------
-- Extended reduction relations allowing reduction under suc.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions

module Graded.Erasure.SucRed
  {a} {M : Set a}
  (R : Type-restrictions M)
  where

open import Tools.Nat

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed R
open import Definition.Typed.Properties R

import Graded.Erasure.Target as T


private
  variable
    n : Nat
    Γ : Con Term n
    t t′ u : Term n
    v v′ w : T.Term n

-- Extended reduction relation for natural numbers.
-- Allows reduction under suc

data _⊢_⇒ˢ_∷ℕ (Γ : Con Term n) : (t u : Term n) → Set a where
  whred : Γ ⊢ t ⇒ u ∷ ℕ → Γ ⊢ t ⇒ˢ u ∷ℕ
  sucred : Γ ⊢ t ⇒ˢ u ∷ℕ → Γ ⊢ suc t ⇒ˢ suc u ∷ℕ

-- Extended reduction relation closure for natural numbers.
-- Allows reduction under suc

data _⊢_⇒ˢ*_∷ℕ (Γ : Con Term n) : (t u : Term n) → Set a where
  id : Γ ⊢ t ∷ ℕ → Γ ⊢ t ⇒ˢ* t ∷ℕ
  _⇨ˢ_ : Γ ⊢ t ⇒ˢ t′ ∷ℕ → Γ ⊢ t′ ⇒ˢ* u ∷ℕ → Γ ⊢ t ⇒ˢ* u ∷ℕ

⇒ˢ*∷ℕ-trans : Γ ⊢ t ⇒ˢ* t′ ∷ℕ → Γ ⊢ t′ ⇒ˢ* u ∷ℕ → Γ ⊢ t ⇒ˢ* u ∷ℕ
⇒ˢ*∷ℕ-trans (id x) d′ = d′
⇒ˢ*∷ℕ-trans (x ⇨ˢ d) d′ = x ⇨ˢ ⇒ˢ*∷ℕ-trans d d′

whred* : Γ ⊢ t ⇒* u ∷ ℕ → Γ ⊢ t ⇒ˢ* u ∷ℕ
whred* (id x) = id x
whred* (x ⇨ d) = whred x ⇨ˢ whred* d

sucred* : Γ ⊢ t ⇒ˢ* u ∷ℕ → Γ ⊢ suc t ⇒ˢ* suc u ∷ℕ
sucred* (id x) = id (sucⱼ x)
sucred* (x ⇨ˢ d) = (sucred x) ⇨ˢ (sucred* d)

subsetTermˢ : Γ ⊢ t ⇒ˢ u ∷ℕ → Γ ⊢ t ≡ u ∷ ℕ
subsetTermˢ (whred x) = subsetTerm x
subsetTermˢ (sucred d) = suc-cong (subsetTermˢ d)

subset*Termˢ : Γ ⊢ t ⇒ˢ* u ∷ℕ → Γ ⊢ t ≡ u ∷ ℕ
subset*Termˢ (id x) = refl x
subset*Termˢ (x ⇨ˢ d) = trans (subsetTermˢ x) (subset*Termˢ d)

-- Extended reduction relation for the target language
-- Allows reduction under suc

data _⇒ˢ_ : (v w : T.Term n) → Set where
  whred : v T.⇒ w → v ⇒ˢ w
  sucred : v ⇒ˢ w → T.suc v ⇒ˢ T.suc w

-- Extended reduction relation closure for the target language
-- Allows reduction under suc

data _⇒ˢ*_ : (v w : T.Term n) → Set where
  refl : v ⇒ˢ* v
  trans : v ⇒ˢ v′ → v′ ⇒ˢ* w → v ⇒ˢ* w

⇒ˢ*-trans : v ⇒ˢ* v′ → v′ ⇒ˢ* w → v ⇒ˢ* w
⇒ˢ*-trans refl d′ = d′
⇒ˢ*-trans (trans d d₁) d′ = trans d (⇒ˢ*-trans d₁ d′)

whred*′ : v T.⇒* w → v ⇒ˢ* w
whred*′ T.refl = refl
whred*′ (T.trans x d) = trans (whred x) (whred*′ d)

sucred*′ : v ⇒ˢ* w → T.suc v ⇒ˢ* T.suc w
sucred*′ refl = refl
sucred*′ (trans x d) = trans (sucred x) (sucred*′ d)
