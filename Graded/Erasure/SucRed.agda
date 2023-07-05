------------------------------------------------------------------------
-- Extended reduction relations allowing reduction under suc.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions

module Graded.Erasure.SucRed
  {a} {M : Set a}
  (R : Type-restrictions M)
  where

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Nullary
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Unit

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed R
open import Definition.Typed.Consequences.Consistency R
open import Definition.Typed.Properties R

import Graded.Erasure.Target as T


private
  variable
    n : Nat
    Γ : Con Term n
    t t′ u : Term n
    v v′ w w′ : T.Term n

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

-- If t reduces to u according to _⊢_⇒ˢ_∷ℕ, and u is definitionally
-- equal to zero, then t reduces to u.

⇒ˢ∷ℕ≡zero→⇒ : Γ ⊢ t ⇒ˢ u ∷ℕ → Γ ⊢ u ≡ zero ∷ ℕ → Γ ⊢ t ⇒ u ∷ ℕ
⇒ˢ∷ℕ≡zero→⇒ (whred t⇒u) _        = t⇒u
⇒ˢ∷ℕ≡zero→⇒ (sucred _)  suc≡zero = ⊥-elim (zero≢suc (sym suc≡zero))

-- If t reduces to u according to _⊢_⇒ˢ*_∷ℕ, and u is definitionally
-- equal to zero, then t reduces to u.

⇒ˢ*∷ℕ≡zero→⇒* : Γ ⊢ t ⇒ˢ* u ∷ℕ → Γ ⊢ u ≡ zero ∷ ℕ → Γ ⊢ t ⇒* u ∷ ℕ
⇒ˢ*∷ℕ≡zero→⇒* (id ⊢t)       _   = id ⊢t
⇒ˢ*∷ℕ≡zero→⇒* (t⇒v ⇨ˢ v⇒*u) u≡0 =
  ⇒ˢ∷ℕ≡zero→⇒ t⇒v (trans (subset*Termˢ v⇒*u) u≡0) ⇨
  ⇒ˢ*∷ℕ≡zero→⇒* v⇒*u u≡0

-- If t reduces to zero according to _⊢_⇒ˢ_∷ℕ, then t reduces to zero.

⇒ˢzero∷ℕ→⇒zero : Γ ⊢ t ⇒ˢ zero ∷ℕ → Γ ⊢ t ⇒ zero ∷ ℕ
⇒ˢzero∷ℕ→⇒zero t⇒ =
  ⇒ˢ∷ℕ≡zero→⇒ t⇒ (refl (zeroⱼ (wfEqTerm (subsetTermˢ t⇒))))

-- If t reduces to zero according to _⊢_⇒ˢ*_∷ℕ, then t reduces to
-- zero.

⇒ˢ*zero∷ℕ→⇒*zero : Γ ⊢ t ⇒ˢ* zero ∷ℕ → Γ ⊢ t ⇒* zero ∷ ℕ
⇒ˢ*zero∷ℕ→⇒*zero t⇒ =
  ⇒ˢ*∷ℕ≡zero→⇒* t⇒ (refl (zeroⱼ (wfEqTerm (subset*Termˢ t⇒))))

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

-- Is-suc v is inhabited if v is of the form "T.suc something".

Is-suc : T.Term n → Set
Is-suc = λ where
  (T.suc _) → ⊤
  _         → ⊥

-- A view of a term as either "T.suc something" or not
-- "T.suc something".

data Suc-view : T.Term n → Set where
  is-suc     : Suc-view (T.suc v)
  not-is-suc : ¬ Is-suc v → Suc-view v

-- The view is total.

suc-view : (v : T.Term n) → Suc-view v
suc-view = λ where
  (T.suc _)        → is-suc
  (T.var _)        → not-is-suc (λ ())
  (T.lam _)        → not-is-suc (λ ())
  (_ T.∘ _)        → not-is-suc (λ ())
  (T.prod _ _)     → not-is-suc (λ ())
  (T.fst _)        → not-is-suc (λ ())
  (T.snd _)        → not-is-suc (λ ())
  (T.prodrec _ _)  → not-is-suc (λ ())
  T.zero           → not-is-suc (λ ())
  (T.natrec _ _ _) → not-is-suc (λ ())
  T.star           → not-is-suc (λ ())
  T.↯              → not-is-suc (λ ())

-- If v reduces to w and v is of the form "T.suc something", then w is
-- of the form "T.suc something".

suc⇒*suc : v T.⇒* w → Is-suc v → Is-suc w
suc⇒*suc         T.refl         is-suc-v = is-suc-v
suc⇒*suc {v = v} (T.trans v⇒ _) is-suc-v =
  case suc-view v of λ where
    is-suc                    → case v⇒ of λ ()
    (not-is-suc not-is-suc-v) → ⊥-elim (not-is-suc-v is-suc-v)

-- If v reduces to w according to _⇒ˢ_, and w is not of the form
-- "T.suc something", then v reduces to w.

⇒ˢ≢suc→⇒ : v ⇒ˢ w → ¬ Is-suc w → v T.⇒ w
⇒ˢ≢suc→⇒ (whred v⇒w) _       = v⇒w
⇒ˢ≢suc→⇒ (sucred _)  not-suc = ⊥-elim (not-suc _)

-- If v reduces to w according to _⇒ˢ*_, and w is not of the form
-- "T.suc something", then v reduces to w.

⇒ˢ*≢suc→⇒* : v ⇒ˢ* w → ¬ Is-suc w → v T.⇒* w
⇒ˢ*≢suc→⇒* refl               _       = T.refl
⇒ˢ*≢suc→⇒* (trans v⇒v′ v′⇒*w) not-suc =
  T.trans (⇒ˢ≢suc→⇒ v⇒v′ (not-suc ∘→ suc⇒*suc v′⇒*w′)) v′⇒*w′
  where
  v′⇒*w′ = ⇒ˢ*≢suc→⇒* v′⇒*w not-suc

-- If v reduces to T.zero according to _⇒ˢ_, then v reduces to T.zero.

⇒ˢzero→⇒zero : v ⇒ˢ T.zero → v T.⇒ T.zero
⇒ˢzero→⇒zero = flip ⇒ˢ≢suc→⇒ (λ ())

-- If v reduces to T.zero according to _⇒ˢ*_, then v reduces to T.zero.

⇒ˢ*zero→⇒*zero : v ⇒ˢ* T.zero → v T.⇒* T.zero
⇒ˢ*zero→⇒*zero = flip ⇒ˢ*≢suc→⇒* (λ ())

-- If v reduces to T.suc w according to _⇒ˢ_, then v reduces to
-- T.suc something.

⇒ˢsuc→⇒*suc : v ⇒ˢ T.suc w → ∃ λ w → v T.⇒* T.suc w
⇒ˢsuc→⇒*suc (whred v⇒)  = _ , T.trans v⇒ T.refl
⇒ˢsuc→⇒*suc (sucred v⇒) = _ , T.refl

-- If v reduces to T.suc w according to _⇒ˢ*_, then v reduces to
-- T.suc something.

⇒ˢ*suc→⇒*suc : v ⇒ˢ* T.suc w → ∃ λ w → v T.⇒* T.suc w
⇒ˢ*suc→⇒*suc = λ where
  refl →
    _ , T.refl
  (trans {v′ = v′} v⇒v′ v′⇒*suc) → case suc-view v′ of λ where
    is-suc               → ⇒ˢsuc→⇒*suc v⇒v′
    (not-is-suc not-suc) →
      case ⇒ˢ*suc→⇒*suc v′⇒*suc of λ {
        (_ , v′⇒*suc) →
      _ , T.trans (⇒ˢ≢suc→⇒ v⇒v′ not-suc) v′⇒*suc }
