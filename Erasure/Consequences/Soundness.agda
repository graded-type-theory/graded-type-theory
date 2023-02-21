open import Definition.Modality.Instances.Erasure
open import Definition.Modality.Restrictions
open import Definition.Typed.EqualityRelation

module Erasure.Consequences.Soundness
  (restrictions : Restrictions Erasure)
  {{eqrel : EqRelSet Erasure}}
  where

open EqRelSet {{...}}

open import Definition.Untyped Erasure hiding (_∷_)
open import Definition.Typed Erasure
open import Definition.Typed.Properties Erasure
open import Definition.LogicalRelation Erasure

open import Definition.Modality.Instances.Erasure.Modality restrictions
open import Definition.Modality.Context ErasureModality
open import Definition.Modality.Usage ErasureModality
open import Definition.Mode ErasureModality

import Erasure.Target as T
open import Erasure.Extraction
open import Erasure.SucRed Erasure
open import Erasure.LogicalRelation restrictions
open import Erasure.LogicalRelation.Fundamental restrictions
open import Erasure.LogicalRelation.Irrelevance restrictions

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

-- If WHℕ n t then t ⇓ sucᵏ n

WHℕ-canon : WHℕ n t → ε ⊢ t ⇒ˢ* sucᵏ n ∷ℕ
WHℕ-canon (zeroʷ x) = whred* x
WHℕ-canon (sucʷ x x₁) = ⇒ˢ*∷ℕ-trans (whred* x) (sucred* (WHℕ-canon x₁))

-- If WHℕ′ n v then v ⇓′ sucᵏ′ v

WHℕ′-canon : WHℕ′ n v → v ⇒ˢ* sucᵏ′ n
WHℕ′-canon (zeroʷ x) = whred*′ x
WHℕ′-canon (sucʷ x x₁) = ⇒ˢ*-trans (whred*′ x) (sucred*′ (WHℕ′-canon x₁))

-- Helper lemma for WH reduction soundness of zero
-- If t ® v ∷ℕ  and t ⇒* zero then v ⇒* zero

soundness-zero′ : t ® v ∷ℕ → ε ⊢ t ⇒* zero ∷ ℕ → v T.⇒* T.zero
soundness-zero′ (zeroᵣ t⇒zero′ v⇒zero) t⇒zero = v⇒zero
soundness-zero′ (sucᵣ t⇒suc v⇒suc t®v) t⇒zero
  with whrDet*Term (t⇒zero , zeroₙ) (t⇒suc , sucₙ)
... | ()

-- WH reduction soundness of zero
-- If t ⇒* zero and ε ▸ t then erase t ⇒* zero

soundness-zero :
  ε ⊢ t ⇒* zero ∷ ℕ → ε ▸[ 𝟙ᵐ ] t → erase t T.⇒* T.zero
soundness-zero t⇒zero γ▸t =
  let ⊢t = redFirst*Term t⇒zero
      [ℕ] , t®t′ = fundamental′ ⊢t γ▸t
      t®t″ = irrelevanceTerm {l′ = ¹} [ℕ] (ℕᵣ (idRed:*: (ℕⱼ ε))) t®t′
  in  soundness-zero′ t®t″ t⇒zero

-- Helper lemma for WH reduction soundness of suc
-- If t ® v ∷ℕ  and t ⇒* suc t′ then v ⇒* suc v′ and t′ ® v′ ∷ℕ for some v′

soundness-suc′ : t ® v ∷ℕ → ε ⊢ t ⇒* suc t′ ∷ ℕ
               → ∃ λ v′ → v T.⇒* T.suc v′ × t′ ® v′ ∷ℕ
soundness-suc′ (zeroᵣ t⇒zero v⇒zero) t⇒suc
  with whrDet*Term (t⇒zero , zeroₙ) (t⇒suc , sucₙ)
... | ()
soundness-suc′ (sucᵣ {v′ = v′} t⇒suc′ v⇒suc t®v) t⇒suc
  with whrDet*Term (t⇒suc , sucₙ) (t⇒suc′ , sucₙ)
... | refl = v′ , (v⇒suc , t®v)

-- WH reduction soundness of suc
-- If t ⇒* suc t′ and ε ▸ t then erase t ⇒* suc v′ and t′ ® v′ ∷ℕ for some v′

soundness-suc : ε ⊢ t ⇒* suc t′ ∷ ℕ → ε ▸[ 𝟙ᵐ ] t
              → ∃ λ v′ → erase t T.⇒* T.suc v′ × t′ ® v′ ∷ℕ
soundness-suc t⇒suc γ▸t =
  let ⊢t = redFirst*Term t⇒suc
      [ℕ] , t®t′ = fundamental′ ⊢t γ▸t
      t®t″ = irrelevanceTerm {l′ = ¹} [ℕ] (ℕᵣ (idRed:*: (ℕⱼ ε))) t®t′
  in  soundness-suc′ t®t″ t⇒suc


-- Helper lemma for WH reduction soundness of natural numbers
-- If t ® v ∷ℕ and WHℕ n t then WHℕ′ n v

soundness-ℕ′ : t ® v ∷ℕ → WHℕ n t → WHℕ′ n v
soundness-ℕ′ t®v (zeroʷ x) = zeroʷ (soundness-zero′ t®v x)
soundness-ℕ′ t®v (sucʷ x whn) =
  let v′ , v⇒suc , t®v′ = soundness-suc′ t®v x
  in  sucʷ v⇒suc (soundness-ℕ′ t®v′ whn)

-- WH reduction soundness of natural numbers
-- If ε ⊢ t ∷ ℕ and ε ▸ t and WHℕ n t then WHℕ′ n (erase t)

soundness-ℕ : ε ⊢ t ∷ ℕ → ε ▸[ 𝟙ᵐ ] t → WHℕ n t → WHℕ′ n (erase t)
soundness-ℕ ⊢t γ▸t whn =
  let [ℕ] , t®t′ = fundamental′ ⊢t γ▸t
      t®t″ = irrelevanceTerm {l′ = ¹} [ℕ] (ℕᵣ (idRed:*: (ℕⱼ ε))) t®t′
  in  soundness-ℕ′ t®t″ whn

-- Helper lemma for existensial WH reduction soundness of natural numbers
-- If t ® v ∷ℕ then ∃ n such that WHℕ n t and WHℕ′ n v

soundness-ℕ-∃′ : t ® v ∷ℕ → ∃ λ n → WHℕ n t × WHℕ′ n v
soundness-ℕ-∃′ (zeroᵣ x x₁) = 0 , zeroʷ x , zeroʷ x₁
soundness-ℕ-∃′ (sucᵣ x x₁ t®v) with soundness-ℕ-∃′ t®v
... | n , y , y₁ = 1+ n , sucʷ x y , sucʷ x₁ y₁

-- Existensial WH reduction soundness for natural numbers
-- If ε ⊢ t ∷ ℕ and ε ▸ t then ∃ n such that WHℕ n t and WHℕ′ n (erase t)

soundness-ℕ-∃ :
  ε ⊢ t ∷ ℕ → ε ▸[ 𝟙ᵐ ] t → ∃ λ n → WHℕ n t × WHℕ′ n (erase t)
soundness-ℕ-∃ ⊢t ▸t =
  let [ℕ] , t®v = fundamental′ ⊢t ▸t
  in  soundness-ℕ-∃′ (irrelevanceTerm {l′ = ¹} [ℕ] (ℕᵣ (idRed:*: (ℕⱼ ε))) t®v)

-- Helper lemma for WH reduction soundness of unit

soundness-star′ : t ® v ∷Unit → v T.⇒* T.star
soundness-star′ (starᵣ _ v⇒star) = v⇒star

-- WH reduction soundness of unit

soundness-star :
  ε ⊢ t ⇒* star ∷ Unit → ε ▸[ 𝟙ᵐ ] t → erase t T.⇒* T.star
soundness-star t⇒star γ▸t =
  let ⊢t = redFirst*Term t⇒star
      [⊤] , t®t′ = fundamental′ ⊢t γ▸t
      t®t″ = irrelevanceTerm {l′ = ¹} [⊤] (Unitᵣ (idRed:*: (Unitⱼ ε))) t®t′
  in  soundness-star′ t®t″
