open import Definition.Modality.Instances.Erasure
open import Definition.Modality.Restrictions
open import Definition.Typed.EqualityRelation
open import Definition.Typed Erasure
open import Definition.Untyped Erasure

module Erasure.LogicalRelation.Fundamental.Unit
  {k} {Δ : Con Term k} (⊢Δ : ⊢ Δ)
  (restrictions : Restrictions Erasure)
  {{eqrel : EqRelSet Erasure}}
  where

open EqRelSet {{...}}

open import Erasure.LogicalRelation ⊢Δ restrictions
open import Erasure.LogicalRelation.Subsumption ⊢Δ restrictions
import Erasure.Target as T

open import Definition.LogicalRelation Erasure
open import Definition.LogicalRelation.Fundamental Erasure
open import Definition.LogicalRelation.Substitution Erasure
open import Definition.LogicalRelation.Substitution.Introductions.Universe Erasure
open import Definition.LogicalRelation.Substitution.Introductions.Unit Erasure

open import Definition.Modality.Instances.Erasure.Modality restrictions
open import Definition.Modality.Context ErasureModality
open import Definition.Mode ErasureModality

open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    γ : Conₘ n
    Γ : Con Term n
    m : Mode

Unitʳ : ⊢ Γ
      → ∃ λ ([Γ] : ⊩ᵛ Γ)
      → ∃ λ ([U] : Γ ⊩ᵛ⟨ ¹ ⟩ U / [Γ])
      → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ Unit ∷[ m ] U / [Γ] / [U]
Unitʳ ⊢Γ =
  [Γ] , [U] , subsumptionMode Unit [U] (λ _ _ → Uᵣ (Unitⱼ ⊢Δ))
  where
  [Γ] = valid ⊢Γ
  [U] = Uᵛ [Γ]

starʳ : ∀ {l} → ⊢ Γ
      → ∃ λ ([Γ] : ⊩ᵛ Γ)
      → ∃ λ ([Unit] : Γ ⊩ᵛ⟨ l ⟩ Unit / [Γ])
      → γ ▸ Γ ⊩ʳ⟨ l ⟩ star ∷[ m ] Unit / [Γ] / [Unit]
starʳ ⊢Γ =
    [Γ] , [Unit]
  , subsumptionMode star [Unit] (λ _ _ → starᵣ (starⱼ ⊢Δ) T.refl)
  where
  [Γ]    = valid ⊢Γ
  [Unit] = Unitᵛ [Γ]
