------------------------------------------------------------------------
-- Soundness of the extraction function.
------------------------------------------------------------------------

open import Definition.Modality
open import Definition.Modality.Restrictions.Definitions
  using (No-erased-matches)
open import Definition.Typed.EqualityRelation
import Definition.Untyped as U hiding (_∷_)
import Definition.Typed as T′
open import Tools.PropositionalEquality
open import Tools.Sum

module Erasure.Consequences.Soundness
  {a k} {M : Set a} (𝕄 : Modality M)
  (open U M) (open T′ M) (open Modality 𝕄)
  {Δ : Con Term k} (⊢Δ : ⊢ Δ)
  (𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet)
  (consistent : ∀ {t} → Δ ⊢ t ∷ Empty → ⊥)
  -- Erased matches are not allowed unless the context
  -- is empty
  (no-erased-matches : No-erased-matches 𝕄 ⊎ k ≡ 0)
  {{eqrel : EqRelSet M}}
  where

open EqRelSet {{...}}

open import Definition.Typed.Properties M
open import Definition.LogicalRelation M

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Usage 𝕄
open import Definition.Modality.Properties.Has-well-behaved-zero
  semiring-with-meet-and-star 𝟘-well-behaved
open import Definition.Mode 𝕄

import Erasure.Target as T
open import Erasure.Extraction 𝕄 is-𝟘?
open import Erasure.SucRed M
open import Erasure.LogicalRelation 𝕄 ⊢Δ is-𝟘?
open import Erasure.LogicalRelation.Fundamental 𝕄 ⊢Δ 𝟘-well-behaved
                                                consistent no-erased-matches
open import Erasure.LogicalRelation.Irrelevance 𝕄 ⊢Δ is-𝟘?
open import Erasure.LogicalRelation.Subsumption 𝕄 ⊢Δ is-𝟘?

open import Tools.Nat
open import Tools.Product


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

soundness-zero′ : t ® v ∷ℕ → Δ ⊢ t ⇒* zero ∷ ℕ → v T.⇒* T.zero
soundness-zero′ (zeroᵣ t⇒zero′ v⇒zero) t⇒zero = v⇒zero
soundness-zero′ (sucᵣ t⇒suc v⇒suc t®v) t⇒zero
  with whrDet*Term (t⇒zero , zeroₙ) (t⇒suc , sucₙ)
... | ()

-- WH reduction soundness of zero
-- If t ⇒* zero and 𝟘ᶜ ▸ t then erase t ⇒* zero

soundness-zero :
  Δ ⊢ t ⇒* zero ∷ ℕ → 𝟘ᶜ ▸[ 𝟙ᵐ ] t → erase t T.⇒* T.zero
soundness-zero t⇒zero 𝟘▸t =
  let ⊢t = redFirst*Term t⇒zero
      [ℕ] , t®t′ = fundamentalErased ⊢t 𝟘▸t
      t®t″ = irrelevanceTerm {l′ = ¹} [ℕ] (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))) (t®t′ ◀≢𝟘 𝟙≉𝟘)
  in  soundness-zero′ t®t″ t⇒zero

-- Helper lemma for WH reduction soundness of suc
-- If t ® v ∷ℕ  and t ⇒* suc t′ then v ⇒* suc v′ and t′ ® v′ ∷ℕ for some v′

soundness-suc′ : t ® v ∷ℕ → Δ ⊢ t ⇒* suc t′ ∷ ℕ
               → ∃ λ v′ → v T.⇒* T.suc v′ × t′ ® v′ ∷ℕ
soundness-suc′ (zeroᵣ t⇒zero v⇒zero) t⇒suc
  with whrDet*Term (t⇒zero , zeroₙ) (t⇒suc , sucₙ)
... | ()
soundness-suc′ (sucᵣ {v′ = v′} t⇒suc′ v⇒suc t®v) t⇒suc
  with whrDet*Term (t⇒suc , sucₙ) (t⇒suc′ , sucₙ)
... | refl = v′ , (v⇒suc , t®v)

-- WH reduction soundness of suc
-- If t ⇒* suc t′ and 𝟘ᶜ ▸ t then erase t ⇒* suc v′ and t′ ® v′ ∷ℕ for some v′

soundness-suc : Δ ⊢ t ⇒* suc t′ ∷ ℕ → 𝟘ᶜ ▸[ 𝟙ᵐ ] t
              → ∃ λ v′ → erase t T.⇒* T.suc v′ × t′ ® v′ ∷ℕ
soundness-suc t⇒suc 𝟘▸t =
  let ⊢t = redFirst*Term t⇒suc
      [ℕ] , t®t′ = fundamentalErased ⊢t 𝟘▸t
      t®t″ = irrelevanceTerm {l′ = ¹} [ℕ] (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))) (t®t′ ◀≢𝟘 𝟙≉𝟘)
  in  soundness-suc′ t®t″ t⇒suc

-- Helper lemma for soundness of natural numbers

soundness-ℕ′ : t ® v ∷ℕ → ∃ λ n → Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ × v ⇒ˢ* sucᵏ′ n
soundness-ℕ′ (zeroᵣ x x₁) = 0 , whred* x , whred*′ x₁
soundness-ℕ′ (sucᵣ x x₁ t®v) =
  let n , d , d′ = soundness-ℕ′ t®v
  in  1+ n , ⇒ˢ*∷ℕ-trans (whred* x) (sucred* d)
           , ⇒ˢ*-trans (whred*′ x₁) (sucred*′ d′)

-- Soundness for erasure of natural numbers
-- Closed, well-typed terms reduce to numerals

soundness-ℕ : Δ ⊢ t ∷ ℕ → 𝟘ᶜ ▸[ 𝟙ᵐ ] t
            → ∃ λ n → Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ × erase t ⇒ˢ* sucᵏ′ n
soundness-ℕ ⊢t 𝟘▸t =
  let [ℕ] , t®v = fundamentalErased ⊢t 𝟘▸t
  in  soundness-ℕ′ (irrelevanceTerm {l′ = ¹} [ℕ] (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))) (t®v ◀≢𝟘 𝟙≉𝟘))

-- Helper lemma for WH reduction soundness of unit

soundness-star′ : t ® v ∷Unit → v T.⇒* T.star
soundness-star′ (starᵣ _ v⇒star) = v⇒star

-- WH reduction soundness of unit

soundness-star :
  Δ ⊢ t ⇒* star ∷ Unit → 𝟘ᶜ ▸[ 𝟙ᵐ ] t → erase t T.⇒* T.star
soundness-star t⇒star γ▸t =
  let ⊢t = redFirst*Term t⇒star
      [⊤] , t®t′ = fundamentalErased ⊢t γ▸t
      t®t″ = irrelevanceTerm {l′ = ¹} [⊤] (Unitᵣ (idRed:*: (Unitⱼ ⊢Δ))) (t®t′ ◀≢𝟘 𝟙≉𝟘)
  in  soundness-star′ t®t″
