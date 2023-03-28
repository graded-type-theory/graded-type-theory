{-# OPTIONS --without-K --safe #-}

open import Definition.Modality.Instances.Erasure
open import Definition.Typed.EqualityRelation
open import Definition.Untyped Erasure hiding (_∷_)
open import Definition.Typed Erasure
open import Tools.Empty

module Erasure.LogicalRelation.Fundamental.Counterexample
  {{eqrel : EqRelSet Erasure}}
  where

open EqRelSet {{...}}

open import Definition.Modality.Restrictions Erasure

open import Definition.Modality.Instances.Erasure.Modality
  no-restrictions

open import Definition.Modality.Context ErasureModality
open import Definition.Modality.Usage ErasureModality
open import Definition.Mode ErasureModality

open import Definition.Typed.Properties Erasure

open import Definition.LogicalRelation Erasure
open import Definition.LogicalRelation.Substitution Erasure
open import Definition.LogicalRelation.Substitution.Properties Erasure
import Definition.LogicalRelation.Substitution.Irrelevance Erasure as IS

Δ : Con Term 1
Δ = ε ∙ (Σᵣ ω , 𝟘 ▷ ℕ ▹ ℕ)

⊢Δ : ⊢ Δ
⊢Δ = ε ∙ (ΠΣⱼ (ℕⱼ ε) ▹ (ℕⱼ (ε ∙ ℕⱼ ε)))

import Erasure.Target as T
open import Erasure.LogicalRelation ⊢Δ no-restrictions
open import Erasure.LogicalRelation.Irrelevance ⊢Δ no-restrictions
open import Erasure.LogicalRelation.Subsumption ⊢Δ no-restrictions

open import Tools.Fin
open import Tools.Product
open import Tools.Unit

-- The fundamental lemma does not hold if erased matching is allowed

cEx″ : ∀ {v} → prodrec 𝟘 ω 𝟘 ℕ (var x0) zero ® v ∷ℕ → ⊥
cEx″ (zeroᵣ x x₁) with whnfRed*Term x (ne (prodrecₙ (var x0)))
... | ()
cEx″ (sucᵣ x x₁ t®v) with whnfRed*Term x (ne (prodrecₙ (var x0)))
... | ()

cEx′ :
  ([Δ] : ⊩ᵛ Δ)
  ([A] : Δ ⊩ᵛ⟨ ¹ ⟩ ℕ / [Δ]) →
  ε ∙ 𝟘 ▸ Δ ⊩ʳ⟨ ¹ ⟩ prodrec 𝟘 ω 𝟘 ℕ (var x0) zero
    ∷[ 𝟙ᵐ ] ℕ / [Δ] / [A] →
  ⊥
cEx′ [Δ] [A] ⊩ʳpr =
  let [σ]′ = idSubstS [Δ]
      ⊢Δ′ = soundContext [Δ]
      [σ] = IS.irrelevanceSubst [Δ] [Δ] ⊢Δ′ ⊢Δ [σ]′
      σ®σ′ = erasedSubst {l = ¹} {σ′ = T.idSubst} [Δ] [σ]
      pr®pr = ⊩ʳpr [σ] σ®σ′
      [σA] = proj₁ (unwrap [A] ⊢Δ [σ])
      [ℕ] = ℕᵣ {l = ¹} (idRed:*: (ℕⱼ ⊢Δ))
      pr®pr′ = irrelevanceTerm [σA] [ℕ] pr®pr
  in  cEx″ pr®pr′

cEx : ∃ λ n
    → ∃₄ λ (t A : Term n) (Γ : Con Term n) (γ : Conₘ n)
    → Γ ⊢ t ∷ A
    × γ ▸[ 𝟙ᵐ ] t
    × ((∃₂ λ ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ]) →
        γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷[ 𝟙ᵐ ] A / [Γ] / [A]) →
       ⊥)
cEx = _
    , prodrec 𝟘 ω 𝟘 ℕ (var x0) zero , ℕ , ε ∙ (Σᵣ ω , 𝟘 ▷ ℕ ▹ ℕ)
    , ε ∙ 𝟘
    , prodrecⱼ Δ⊢ℕ Δℕ⊢ℕ ΔΣ⊢ℕ (var ⊢Δ here) (zeroⱼ ⊢Δℕℕ)
    , prodrecₘ var zeroₘ ℕₘ _
    , λ {([Γ] , [A] , ⊩ʳpr) → cEx′ [Γ] [A] ⊩ʳpr}
    where
    Δ⊢ℕ = ℕⱼ ⊢Δ
    ⊢Δℕ = ⊢Δ ∙ Δ⊢ℕ
    Δℕ⊢ℕ = ℕⱼ ⊢Δℕ
    Δ⊢Σ = ΠΣⱼ Δ⊢ℕ ▹ Δℕ⊢ℕ
    ⊢ΔΣ = ⊢Δ ∙ Δ⊢Σ
    ΔΣ⊢ℕ = ℕⱼ ⊢ΔΣ
    ⊢Δℕℕ = ⊢Δ ∙ Δ⊢ℕ ∙ Δℕ⊢ℕ
