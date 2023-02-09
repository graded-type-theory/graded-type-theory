{-# OPTIONS --without-K --safe #-}

open import Definition.Modality.Instances.Erasure
open import Definition.Modality.Restrictions
open import Definition.Typed.EqualityRelation

module Erasure.LogicalRelation.Fundamental.Unit
  (restrictions : Restrictions Erasure′)
  {{eqrel : EqRelSet Erasure′}}
  where

open EqRelSet {{...}}

open import Erasure.LogicalRelation restrictions
import Erasure.Target as T

open import Definition.Untyped Erasure
open import Definition.Typed Erasure′

open import Definition.LogicalRelation Erasure′
open import Definition.LogicalRelation.Fundamental Erasure′
open import Definition.LogicalRelation.Substitution Erasure′
open import Definition.LogicalRelation.Substitution.Introductions.Universe Erasure′
open import Definition.LogicalRelation.Substitution.Introductions.Unit Erasure′

open import Definition.Modality.Instances.Erasure.Modality restrictions
open import Definition.Modality.Context ErasureModality

open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    γ : Conₘ n
    Γ : Con Term n

Unitʳ : ⊢ Γ
      → ∃ λ ([Γ] : ⊩ᵛ Γ)
      → ∃ λ ([U] : Γ ⊩ᵛ⟨ ¹ ⟩ U / [Γ])
      → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ Unit ∷ U / [Γ] / [U]
Unitʳ ⊢Γ =
  let [Γ] = valid ⊢Γ
      [U] = Uᵛ [Γ]
  in  [Γ] , [U] , λ [σ] x → Uᵣ (Unitⱼ ε)

starʳ : ∀ {l} → ⊢ Γ
      → ∃ λ ([Γ] : ⊩ᵛ Γ)
      → ∃ λ ([Unit] : Γ ⊩ᵛ⟨ l ⟩ Unit / [Γ])
      → γ ▸ Γ ⊩ʳ⟨ l ⟩ star ∷ Unit / [Γ] / [Unit]
starʳ ⊢Γ =
  let [Γ] = valid ⊢Γ
      [Unit] = Unitᵛ [Γ]
  in  [Γ] , [Unit] , λ [σ] x → starᵣ (starⱼ ε) T.refl
