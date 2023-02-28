{-# OPTIONS --without-K --safe #-}

open import Definition.Modality.Instances.Erasure
open import Definition.Typed.EqualityRelation
open import Definition.Untyped Erasure hiding (_∷_)
open import Definition.Typed Erasure′

module Erasure.LogicalRelation.Fundamental.Nat {k} {Δ : Con Term k} (⊢Δ : ⊢ Δ)
                                               (Prodrec : Erasure → Set)
                                               {{eqrel : EqRelSet Erasure′}} where
open EqRelSet {{...}}

open import Erasure.Extraction
open import Erasure.LogicalRelation ⊢Δ Prodrec
open import Erasure.LogicalRelation.Irrelevance ⊢Δ Prodrec
import Erasure.Target as T

open import Definition.Typed.Consequences.Substitution Erasure′

open import Definition.LogicalRelation Erasure′
open import Definition.LogicalRelation.Fundamental Erasure′
open import Definition.LogicalRelation.Substitution Erasure′
open import Definition.LogicalRelation.Substitution.Properties Erasure′
open import Definition.LogicalRelation.Substitution.Introductions.Universe Erasure′
open import Definition.LogicalRelation.Substitution.Introductions.Nat Erasure′

open import Definition.Modality.Instances.Erasure.Modality Prodrec
open import Definition.Modality.Context ErasureModality

open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    γ : Conₘ n
    Γ : Con Term n
    t : Term n

ℕʳ : ⊢ Γ
   → ∃ λ ([Γ] : ⊩ᵛ Γ)
   → ∃ λ ([U] : Γ ⊩ᵛ⟨ ¹ ⟩ U / [Γ])
   → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ ℕ ∷ U / [Γ] / [U]
ℕʳ ⊢Γ =
  let [Γ] = valid ⊢Γ
      [U] = Uᵛ [Γ]
  in  [Γ] , [U] , λ [σ] x → Uᵣ (ℕⱼ ⊢Δ)

zeroʳ : ∀ {l} → ⊢ Γ
      → ∃ λ ([Γ] : ⊩ᵛ Γ)
      → ∃ λ ([ℕ] : Γ ⊩ᵛ⟨ l ⟩ ℕ / [Γ])
      → γ ▸ Γ ⊩ʳ⟨ l ⟩ zero ∷ ℕ / [Γ] / [ℕ]
zeroʳ ⊢Γ =
  let [Γ] = valid ⊢Γ
      [ℕ] = ℕᵛ [Γ]
  in  [Γ] , [ℕ] , λ [σ] x → zeroᵣ (id (zeroⱼ ⊢Δ)) T.refl

sucʳ : ∀ {l}
     → ([Γ] : ⊩ᵛ Γ)
       ([ℕ] : Γ ⊩ᵛ⟨ l ⟩ ℕ / [Γ])
       (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷ ℕ / [Γ] / [ℕ])
     → Γ ⊢ t ∷ ℕ
     → γ ▸ Γ ⊩ʳ⟨ l ⟩ suc t ∷ ℕ / [Γ] / [ℕ]
sucʳ {Γ = Γ} {γ = γ} {t = t} {l = l} [Γ] [ℕ] ⊩ʳt Γ⊢t:ℕ {σ = σ} {σ′ = σ′} [σ] σ®σ′ =
  let [ℕ]′ = ℕᵛ {l = l} [Γ]
      ⊢t:ℕ = substitutionTerm Γ⊢t:ℕ (wellformedSubst [Γ] ⊢Δ [σ]) ⊢Δ
      t®v = ⊩ʳt [σ] σ®σ′
      t®v∷ℕ = irrelevanceTerm (proj₁ (unwrap [ℕ] ⊢Δ [σ])) (proj₁ (unwrap [ℕ]′ ⊢Δ [σ])) t®v
      suct®sucv : suc (subst σ t) ®⟨ _ ⟩ T.suc (T.subst σ′ (erase t)) ∷ ℕ / proj₁ (unwrap [ℕ]′ ⊢Δ [σ])
      suct®sucv = sucᵣ (id (sucⱼ ⊢t:ℕ)) T.refl t®v∷ℕ
  in  irrelevanceTerm (proj₁ (unwrap [ℕ]′ ⊢Δ [σ])) (proj₁ (unwrap [ℕ] ⊢Δ [σ])) suct®sucv
