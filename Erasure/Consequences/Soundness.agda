{-# OPTIONS --without-K --safe #-}

open import Definition.Modality.Instances.Erasure
open import Definition.Typed.EqualityRelation

module Erasure.Consequences.Soundness
  (Prodrec : Erasure → Set) {{eqrel : EqRelSet Erasure′}} where
open EqRelSet {{...}}

open import Definition.Untyped Erasure hiding (_∷_)
open import Definition.Typed Erasure′
open import Definition.Typed.Properties Erasure′
open import Definition.LogicalRelation Erasure′

open import Definition.Modality.Instances.Erasure.Modality Prodrec
open import Definition.Modality.Context ErasureModality
open import Definition.Modality.Usage ErasureModality

import Erasure.Target as T
open import Erasure.Extraction
open import Erasure.SucRed Erasure′
open import Erasure.LogicalRelation Prodrec
open import Erasure.LogicalRelation.Fundamental Prodrec
open import Erasure.LogicalRelation.Irrelevance Prodrec

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

-- Helper lemma for WH reduction soundness of zero
-- If t ® v ∷ℕ  and t ⇒* zero then v ⇒* zero

soundness-zero′ : t ® v ∷ℕ → ε ⊢ t ⇒* zero ∷ ℕ → v T.⇒* T.zero
soundness-zero′ (zeroᵣ t⇒zero′ v⇒zero) t⇒zero = v⇒zero
soundness-zero′ (sucᵣ t⇒suc v⇒suc t®v) t⇒zero
  with whrDet*Term (t⇒zero , zeroₙ) (t⇒suc , sucₙ)
... | ()

-- WH reduction soundness of zero
-- If t ⇒* zero and ε ▸ t then erase t ⇒* zero

soundness-zero : ε ⊢ t ⇒* zero ∷ ℕ → ε ▸ t → erase t T.⇒* T.zero
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

soundness-suc : ε ⊢ t ⇒* suc t′ ∷ ℕ → ε ▸ t
              → ∃ λ v′ → erase t T.⇒* T.suc v′ × t′ ® v′ ∷ℕ
soundness-suc t⇒suc γ▸t =
  let ⊢t = redFirst*Term t⇒suc
      [ℕ] , t®t′ = fundamental′ ⊢t γ▸t
      t®t″ = irrelevanceTerm {l′ = ¹} [ℕ] (ℕᵣ (idRed:*: (ℕⱼ ε))) t®t′
  in  soundness-suc′ t®t″ t⇒suc

-- Helper lemma for soundness of natural numbers

soundness-ℕ′ : t ® v ∷ℕ → ∃ λ n → ε ⊢ t ⇒ˢ* sucᵏ n ∷ℕ × v ⇒ˢ* sucᵏ′ n
soundness-ℕ′ (zeroᵣ x x₁) = 0 , whred* x , whred*′ x₁
soundness-ℕ′ (sucᵣ x x₁ t®v) =
  let n , d , d′ = soundness-ℕ′ t®v
  in  1+ n , ⇒ˢ*∷ℕ-trans (whred* x) (sucred* d)
           , ⇒ˢ*-trans (whred*′ x₁) (sucred*′ d′)

-- Soundness for erasure of natural numbers
-- Closed, well-typed terms reduce to numerals

soundness-ℕ : ε ⊢ t ∷ ℕ → ε ▸ t
            → ∃ λ n → ε ⊢ t ⇒ˢ* sucᵏ n ∷ℕ × erase t ⇒ˢ* sucᵏ′ n
soundness-ℕ ⊢t ε▸t =
  let [ℕ] , t®v = fundamental′ ⊢t ε▸t
  in  soundness-ℕ′ (irrelevanceTerm {l′ = ¹} [ℕ] (ℕᵣ (idRed:*: (ℕⱼ ε))) t®v)

-- Helper lemma for WH reduction soundness of unit

soundness-star′ : t ® v ∷Unit → v T.⇒* T.star
soundness-star′ (starᵣ _ v⇒star) = v⇒star

-- WH reduction soundness of unit

soundness-star : ε ⊢ t ⇒* star ∷ Unit → ε ▸ t → erase t T.⇒* T.star
soundness-star t⇒star γ▸t =
  let ⊢t = redFirst*Term t⇒star
      [⊤] , t®t′ = fundamental′ ⊢t γ▸t
      t®t″ = irrelevanceTerm {l′ = ¹} [⊤] (Unitᵣ (idRed:*: (Unitⱼ ε))) t®t′
  in  soundness-star′ t®t″
