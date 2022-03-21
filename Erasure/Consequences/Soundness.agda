{-# OPTIONS --without-K --safe #-}
open import Definition.Modality.Erasure

open import Definition.Typed.EqualityRelation


module Erasure.Consequences.Soundness {{eqrel : EqRelSet Erasure′}} where
open EqRelSet {{...}}

open import Definition.Untyped Erasure hiding (_∷_)
open import Definition.Typed Erasure′
open import Definition.Typed.Properties Erasure′
open import Definition.LogicalRelation Erasure′
open import Definition.Modality.Context ErasureModality
open import Definition.Modality.Usage ErasureModality

import Erasure.Target as T
open import Erasure.Extraction
open import Erasure.LogicalRelation
open import Erasure.LogicalRelation.Fundamental
open import Erasure.LogicalRelation.Irrelevance

open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality

private
  variable
    n : Nat
    t t′ u F : Term n
    G : Term (1+ n)
    v v′ w : T.Term n

-- WH reduction soundness of natural numbers

-- Canonical representation of natural numbers

sucᵏ : (k : Nat) → Term n
sucᵏ 0      = zero
sucᵏ (1+ n) = suc (sucᵏ n)

sucᵏ′ : (k : Nat) → T.Term n
sucᵏ′ 0      = T.zero
sucᵏ′ (1+ n) = T.suc (sucᵏ′ n)

-- Weak head representation of natural numbers

data WHℕ : (n : Nat) → Term 0 → Set where
  zeroʷ : ε ⊢ t ⇒* zero ∷ ℕ → WHℕ 0 t
  sucʷ  : ε ⊢ t ⇒* suc t′ ∷ ℕ → WHℕ n t′ → WHℕ (1+ n) t

data WHℕ′ : (n : Nat) → T.Term 0 → Set where
  zeroʷ : v T.⇒* T.zero → WHℕ′ 0 v
  sucʷ  : v T.⇒* T.suc v′ → WHℕ′ n v′ → WHℕ′ (1+ n) v


-- Weak head representations are equivalent to canonical representations
-- when reductions are allowed under the head of suc

data _⇓_ : (t t′ : Term 0) → Set where
  whred : ε ⊢ t ⇒ t′ ∷ ℕ → t ⇓ t′
  sucred : t ⇓ t′ → suc t ⇓ suc t′

data _⇓*_ : (t t′ : Term 0) → Set where
  id : ε ⊢ t ∷ ℕ → t ⇓* t
  _⇩_ : t ⇓ t′ → t′ ⇓* u → t ⇓* u

whred* : ε ⊢ t ⇒* t′ ∷ ℕ → t ⇓* t′
whred* (id x) = id x
whred* (x ⇨ x₁) = (whred x) ⇩ (whred* x₁)

sucred* : t ⇓* t′ → suc t ⇓* suc t′
sucred* (id x) = id (sucⱼ x)
sucred* (x ⇩ x₁) = sucred x ⇩ sucred* x₁

_⇩*_ : t ⇓* t′ → t′ ⇓* u → t ⇓* u
id ⊢t ⇩* t⇓u = t⇓u
(t⇓t′ ⇩ t′⇓t″) ⇩* t″⇓u = t⇓t′ ⇩ (t′⇓t″ ⇩* t″⇓u)

data _↓_ : (v v′ : T.Term 0) → Set where
  whred : v T.⇒ v′ → v ↓ v′
  sucred : v ↓ v′ → T.suc v ↓ T.suc v′

data _↓*_ : (v v′ : T.Term 0) → Set where
  id : v ↓* v
  _⇩_ : v ↓ v′ → v′ ↓* w → v ↓* w

whred*′ : v T.⇒* v′ → v ↓* v′
whred*′ T.refl = id
whred*′ (T.trans x x₁) = whred x ⇩ whred*′ x₁

sucred*′ : v ↓* v′ → T.suc v ↓* T.suc v′
sucred*′ id = id
sucred*′ (x ⇩ x₁) = sucred x ⇩ sucred*′ x₁

_⇩′*_ : v ↓* v′ → v′ ↓* w → v ↓* w
id ⇩′* v⇩w = v⇩w
(v⇩v′ ⇩ v′⇩v″) ⇩′* v″⇩w = v⇩v′ ⇩ (v′⇩v″ ⇩′* v″⇩w)

-- If WHℕ n t then t ⇓ sucᵏ n

WHℕ-canon : WHℕ n t → t ⇓* sucᵏ n
WHℕ-canon (zeroʷ x) = whred* x
WHℕ-canon (sucʷ x x₁) = (whred* x) ⇩* sucred* (WHℕ-canon x₁)

-- If WHℕ′ n v then v ⇓′ sucᵏ′ v

WHℕ′-canon : WHℕ′ n v → v ↓* sucᵏ′ n
WHℕ′-canon (zeroʷ x) = whred*′ x
WHℕ′-canon (sucʷ x x₁) = whred*′ x ⇩′* (sucred*′ (WHℕ′-canon x₁))


-- Helper lemma for WH reduction soundness of zero
-- If t ® v ∷ℕ  and t ⇒* zero then v ⇒* zero

soundness-zero′ : t ® v ∷ℕ → ε ⊢ t ⇒* zero ∷ ℕ → v T.⇒* T.zero
soundness-zero′ (zeroᵣ t⇒zero′ v⇒zero) t⇒zero = v⇒zero
soundness-zero′ (sucᵣ t⇒suc v⇒suc t®v) t⇒zero with whrDet*Term (t⇒zero , zeroₙ) (t⇒suc , sucₙ)
... | ()

-- WH reduction soundness of zero
-- If t ⇒* zero and ε ▸ t then erase t ⇒* zero

soundness-zero : ε ⊢ t ⇒* zero ∷ ℕ → ε ▸ t → erase t T.⇒* T.zero
soundness-zero t⇒zero γ▸t =
  let ⊢t = redFirst*Term t⇒zero
      [ℕ] , t®t′ = fundamental′ ⊢t γ▸t
      t®t″ = irrelevanceTerm {l′ = ¹} [ℕ] (ℕᵣ ([ ℕⱼ ε , ℕⱼ ε , id (ℕⱼ ε) ])) t®t′
  in  soundness-zero′ t®t″ t⇒zero

-- Helper lemma for WH reduction soundness of suc
-- If t ® v ∷ℕ  and t ⇒* suc t′ then v ⇒* suc v′ and t′ ® v′ ∷ℕ for some v′

soundness-suc′ : t ® v ∷ℕ → ε ⊢ t ⇒* suc t′ ∷ ℕ → ∃ λ v′ → v T.⇒* T.suc v′ × t′ ® v′ ∷ℕ
soundness-suc′ (zeroᵣ t⇒zero v⇒zero) t⇒suc
  with whrDet*Term (t⇒zero , zeroₙ) (t⇒suc , sucₙ)
... | ()
soundness-suc′ (sucᵣ {v′ = v′} t⇒suc′ v⇒suc t®v) t⇒suc
  with whrDet*Term (t⇒suc , sucₙ) (t⇒suc′ , sucₙ)
... | refl = v′ , (v⇒suc , t®v)

-- WH reduction soundness of suc
-- If t ⇒* suc t′ and ε ▸ t then erase t ⇒* suc v′ and t′ ® v′ ∷ℕ for some v′

soundness-suc : ε ⊢ t ⇒* suc t′ ∷ ℕ → ε ▸ t → ∃ λ v′ → erase t T.⇒* T.suc v′ × t′ ® v′ ∷ℕ
soundness-suc t⇒suc γ▸t =
  let ⊢t = redFirst*Term t⇒suc
      [ℕ] , t®t′ = fundamental′ ⊢t γ▸t
      t®t″ = irrelevanceTerm {l′ = ¹} [ℕ] (ℕᵣ ([ ℕⱼ ε , ℕⱼ ε , id (ℕⱼ ε) ])) t®t′
  in  soundness-suc′ t®t″ t⇒suc


-- Helper lemma for WH reduction soundness of natural numbers
-- If t ® v ∷ℕ and WHℕ n t then WHℕ′ n v

soundness-ℕ′ : t ® v ∷ℕ → WHℕ n t → WHℕ′ n v
soundness-ℕ′ t®v (zeroʷ x) = zeroʷ (soundness-zero′ t®v x)
soundness-ℕ′ t®v (sucʷ x whn) =
  let v′ , v⇒suc , t®v′ = soundness-suc′ t®v x
  in  sucʷ v⇒suc (soundness-ℕ′ t®v′ whn)

-- WH reduction soundness of natural numbers
-- If t ® v ∷ℕ and WHℕ n t then WHℕ′ n v

soundness-ℕ : ε ⊢ t ∷ ℕ → ε ▸ t → WHℕ n t → WHℕ′ n (erase t)
soundness-ℕ ⊢t γ▸t whn =
  let [ℕ] , t®t′ = fundamental′ ⊢t γ▸t
      t®t″ = irrelevanceTerm {l′ = ¹} [ℕ] (ℕᵣ ([ ℕⱼ ε , ℕⱼ ε , id (ℕⱼ ε) ])) t®t′
  in  soundness-ℕ′ t®t″ whn


-- Helper lemma for WH reduction soundness of unit

soundness-star′ : t ® v ∷Unit → v T.⇒* T.star
soundness-star′ (starᵣ _ v⇒star) = v⇒star

-- WH reduction soundness of unit

soundness-star : ε ⊢ t ⇒* star ∷ Unit → ε ▸ t → erase t T.⇒* T.star
soundness-star t⇒star γ▸t =
  let ⊢t = redFirst*Term t⇒star
      [⊤] , t®t′ = fundamental′ ⊢t γ▸t
      t®t″ = irrelevanceTerm {l′ = ¹} [⊤] (Unitᵣ ([ Unitⱼ ε , Unitⱼ ε , id (Unitⱼ ε) ])) t®t′
  in  soundness-star′ t®t″
