{-# OPTIONS --without-K  #-}
open import Definition.Modality.Erasure

open import Definition.Typed.EqualityRelation


module Erasure.LogicalRelation.Soundness {{eqrel : EqRelSet Erasure}} where
open EqRelSet {{...}}

open import Definition.Untyped Erasure hiding (_∷_)
open import Definition.Untyped.Properties Erasure
open import Definition.Typed Erasure
open import Definition.Typed.Properties Erasure
open import Definition.Typed.Consequences.Syntactic Erasure
open import Definition.Typed.Consequences.Inversion Erasure
open import Definition.LogicalRelation Erasure
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
    t t′ F : Term n
    G : Term (1+ n)
    v v′ : T.Term n

-- WH reduction soundness of natural numbers


-- Helper lemma for WH reduction soundness of zero
-- If t ® v ∷ℕ  and t ⇒* zero then v ⇒* zero

soundness-zero′ : t ® v ∷ℕ → ε ⊢ t ⇒* zero ∷ ℕ → v T.⇒* T.zero
soundness-zero′ (zeroᵣ t⇒zero′ v⇒zero ) t⇒zero = v⇒zero
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


soundness-star′ : t ® v ∷Unit → v T.⇒* T.star
soundness-star′ (starᵣ _ v⇒star) = v⇒star

soundness-star : ε ⊢ t ⇒* star ∷ Unit → ε ▸ t → erase t T.⇒* T.star
soundness-star t⇒star γ▸t =
  let ⊢t = redFirst*Term t⇒star
      [⊤] , t®t′ = fundamental′ ⊢t γ▸t
      t®t″ = irrelevanceTerm {l′ = ¹} [⊤] (Unitᵣ ([ Unitⱼ ε , Unitⱼ ε , id (Unitⱼ ε) ])) t®t′
  in  soundness-star′ t®t″
