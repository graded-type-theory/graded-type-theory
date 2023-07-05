------------------------------------------------------------------------
-- Soundness of the extraction function.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Restrictions
  using (No-erased-matches)
open import Graded.Usage.Restrictions
open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Tools.Empty
open import Tools.PropositionalEquality
open import Tools.Sum

module Graded.Erasure.Consequences.Soundness
  {a} {M : Set a}
  (𝕄 : Modality M)
  (open Modality 𝕄)
  (TR : Type-restrictions M)
  (UR : Usage-restrictions M)
  (𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet)
  {{eqrel : EqRelSet TR}}
  where

open EqRelSet {{...}}
open Type-restrictions TR
open Usage-restrictions UR

open import Definition.Untyped M hiding (_∷_)

open import Definition.Typed TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Consequences.Substitution TR
open import Definition.Typed.Consequences.Syntactic TR
import Definition.Typed.Consequences.Canonicity TR as TC
open import Definition.Typed.Properties TR
open import Definition.LogicalRelation TR

open import Graded.Context 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄 using (≤-reflexive)
open import Graded.Modality.Properties.Has-well-behaved-zero
  semiring-with-meet-and-star 𝟘-well-behaved
open import Graded.Mode 𝕄

import Graded.Erasure.Target as T
open import Graded.Erasure.Extraction 𝕄 is-𝟘?
open import Graded.Erasure.SucRed TR
import Graded.Erasure.LogicalRelation 𝕄 TR is-𝟘? as LR
import Graded.Erasure.LogicalRelation.Fundamental
  𝕄 TR UR 𝟘-well-behaved as LRF
import Graded.Erasure.LogicalRelation.Irrelevance 𝕄 TR is-𝟘? as LRI
import Graded.Erasure.LogicalRelation.Subsumption 𝕄 TR is-𝟘? as LRS

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Nullary
open import Tools.Product
import Tools.Reasoning.PartialOrder
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    t t′ u F : Term n
    G : Term (1+ n)
    v v′ w : T.Term n
    p : M

-- WH reduction soundness of natural numbers

-- Canonical representation of natural numbers

sucᵏ : (k : Nat) → Term n
sucᵏ 0      = zero
sucᵏ (1+ n) = suc (sucᵏ n)

sucᵏ′ : (k : Nat) → T.Term n
sucᵏ′ 0      = T.zero
sucᵏ′ (1+ n) = T.suc (sucᵏ′ n)

-- The following results make use of some assumptions.

module Soundness
  {k : Nat}
  {Δ : Con Term k}
  -- Erased matches are not allowed unless the context is empty.
  (no-erased-matches : No-erased-matches 𝕄 UR ⊎ k ≡ 0)
  (⊢Δ : ⊢ Δ)
  (consistent : ∀ {t} → Δ ⊢ t ∷ Empty → ⊥)
  where

  open LR ⊢Δ
  open LRF.Fundamental no-erased-matches ⊢Δ consistent
  open LRI ⊢Δ
  open LRS ⊢Δ

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
        t®t″ = irrelevanceTerm {l′ = ¹} [ℕ] (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))) (t®t′ ◀≢𝟘 𝟙≢𝟘)
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
        t®t″ = irrelevanceTerm {l′ = ¹} [ℕ] (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))) (t®t′ ◀≢𝟘 𝟙≢𝟘)
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
    in  soundness-ℕ′ (irrelevanceTerm {l′ = ¹} [ℕ] (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))) (t®v ◀≢𝟘 𝟙≢𝟘))

  -- A variant of soundness-ℕ which only considers the source
  -- language.

  soundness-ℕ-only-source :
    Δ ⊢ t ∷ ℕ → 𝟘ᶜ ▸[ 𝟙ᵐ ] t →
    ∃ λ n → Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ
  soundness-ℕ-only-source ⊢t ▸t =
    case soundness-ℕ ⊢t ▸t of λ {
      (n , t⇒ˢ*n , _) →
    n , t⇒ˢ*n }

  -- Helper lemma for WH reduction soundness of unit

  soundness-star′ : t ® v ∷Unit → v T.⇒* T.star
  soundness-star′ (starᵣ _ v⇒star) = v⇒star

  -- WH reduction soundness of unit

  soundness-star :
    Δ ⊢ t ⇒* star ∷ Unit → 𝟘ᶜ ▸[ 𝟙ᵐ ] t → erase t T.⇒* T.star
  soundness-star t⇒star γ▸t =
    let ⊢t = redFirst*Term t⇒star
        [⊤] , t®t′ = fundamentalErased ⊢t γ▸t
        ok = ⊢∷Unit→Unit-allowed ⊢t
        t®t″ = irrelevanceTerm {l′ = ¹}
                 [⊤] (Unitᵣ (Unitₜ (idRed:*: (Unitⱼ ⊢Δ ok)) ok))
                 (t®t′ ◀≢𝟘 𝟙≢𝟘)
    in  soundness-star′ t®t″

-- If Prodrec-allowed 𝟘 p 𝟘 holds for some p (which means that certain
-- kinds of erased matches are allowed), and if additionally
-- Σᵣ-allowed p 𝟘 holds, then there is a counterexample to
-- soundness-ℕ-only-source without the assumption "erased matches are
-- not allowed unless the context is empty".

soundness-ℕ-only-source-counterexample :
  Prodrec-allowed 𝟘 p 𝟘 →
  Σᵣ-allowed p 𝟘 →
  let Γ = ε ∙ (Σᵣ p , 𝟘 ▷ ℕ ▹ ℕ)
      t = prodrec 𝟘 p 𝟘 ℕ (var x0) zero
  in
  ⊢ Γ ×
  (∀ {u} → Γ ⊢ u ∷ Empty → ⊥) ×
  Γ ⊢ t ∷ ℕ ×
  𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
  ¬ ∃ λ n → Γ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ
soundness-ℕ-only-source-counterexample {p = p} P-ok Σᵣ-ok =
    wfTerm ⊢prodrec
  , (λ ⊢t → TC.¬Empty $
            substTerm ⊢t (prodⱼ ε⊢ℕ εℕ⊢ℕ (zeroⱼ ε) (zeroⱼ ε) Σᵣ-ok))
  , ⊢prodrec
  , sub
      (prodrecₘ var
         (sub zeroₘ $
          let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
            𝟘ᶜ ∙ 𝟙 · 𝟘 · p ∙ 𝟙 · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-congˡ (·-zeroˡ _) ∙ PE.refl ⟩
            𝟘ᶜ ∙ 𝟙 · 𝟘 ∙ 𝟙 · 𝟘      ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩
            𝟘ᶜ                      ∎)
         (sub ℕₘ $
          let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
            𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
            𝟘ᶜ                ∎)
         P-ok)
      (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
         𝟘ᶜ                           ≈˘⟨ +ᶜ-identityʳ _ ⟩
         𝟘ᶜ +ᶜ 𝟘ᶜ                     ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
         𝟘 ·ᶜ (𝟘ᶜ ∙ ⌜ ⌞ 𝟘 ⌟ ⌝) +ᶜ 𝟘ᶜ  ∎)
  , λ where
      (0    , whred d ⇨ˢ _) → whnfRedTerm d (ne (prodrecₙ (var _)))
      (1+ _ , whred d ⇨ˢ _) → whnfRedTerm d (ne (prodrecₙ (var _)))
  where
  ε⊢ℕ = ℕⱼ ε
  ⊢εℕ = ε ∙ ε⊢ℕ
  εℕ⊢ℕ = ℕⱼ ⊢εℕ
  ε⊢Σ = ΠΣⱼ ε⊢ℕ εℕ⊢ℕ Σᵣ-ok
  ⊢εΣ = ε ∙ ε⊢Σ
  εΣ⊢ℕ = ℕⱼ ⊢εΣ
  ⊢εΣℕ = ⊢εΣ ∙ εΣ⊢ℕ
  εΣℕ⊢ℕ = ℕⱼ ⊢εΣℕ
  εΣ⊢Σ = ΠΣⱼ εΣ⊢ℕ εΣℕ⊢ℕ Σᵣ-ok
  ⊢εΣΣ = ⊢εΣ ∙ εΣ⊢Σ
  εΣΣ⊢ℕ = ℕⱼ ⊢εΣΣ
  ⊢εΣℕℕ = ⊢εΣℕ ∙ εΣℕ⊢ℕ
  ⊢prodrec =
    prodrecⱼ {r = 𝟘} εΣ⊢ℕ εΣℕ⊢ℕ εΣΣ⊢ℕ (var ⊢εΣ here) (zeroⱼ ⊢εΣℕℕ) Σᵣ-ok
