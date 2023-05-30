------------------------------------------------------------------------
-- Soundness of the extraction function.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Restrictions
  using (No-erased-matches)
open import Graded.Usage.Restrictions
open import Definition.Typed.EqualityRelation
import Definition.Untyped hiding (_∷_)
open import Definition.Typed.Restrictions
import Definition.Typed
open import Tools.Empty
open import Tools.PropositionalEquality
open import Tools.Sum

module Graded.Erasure.Consequences.Soundness
  {a k} {M : Set a}
  (open Definition.Untyped M)
  (𝕄 : Modality M)
  (open Modality 𝕄)
  (TR : Type-restrictions M)
  (open Definition.Typed TR)
  (UR : Usage-restrictions M)
  {Δ : Con Term k} (⊢Δ : ⊢ Δ)
  (𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet)
  (consistent : ∀ {t} → Δ ⊢ t ∷ Empty → ⊥)
  -- Erased matches are not allowed unless the context
  -- is empty
  (no-erased-matches : No-erased-matches 𝕄 UR ⊎ k ≡ 0)
  {{eqrel : EqRelSet TR}}
  where

open EqRelSet {{...}}

open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Consequences.Syntactic TR
open import Definition.Typed.Properties TR
open import Definition.LogicalRelation TR

open import Graded.Context 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Modality.Properties.Has-well-behaved-zero
  semiring-with-meet-and-star 𝟘-well-behaved
open import Graded.Mode 𝕄

import Graded.Erasure.Target as T
open import Graded.Erasure.Extraction 𝕄 is-𝟘?
open import Graded.Erasure.SucRed TR
open import Graded.Erasure.LogicalRelation 𝕄 TR ⊢Δ is-𝟘?
open import Graded.Erasure.LogicalRelation.Fundamental
  𝕄 TR UR ⊢Δ 𝟘-well-behaved consistent no-erased-matches
open import Graded.Erasure.LogicalRelation.Irrelevance 𝕄 TR ⊢Δ is-𝟘?
open import Graded.Erasure.LogicalRelation.Subsumption 𝕄 TR ⊢Δ is-𝟘?

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
-- Well-typed terms of the natural number type reduce to numerals
-- if erased matches are disallowed or the term is closed.

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
      ok = ⊢∷Unit→Unit-restriction ⊢t
      t®t″ = irrelevanceTerm {l′ = ¹}
               [⊤] (Unitᵣ (Unitₜ (idRed:*: (Unitⱼ ⊢Δ ok)) ok))
               (t®t′ ◀≢𝟘 𝟙≉𝟘)
  in  soundness-star′ t®t″
