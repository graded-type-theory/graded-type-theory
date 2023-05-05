open import Definition.Modality
open import Definition.Typed.EqualityRelation
import Definition.Typed as T′
import Definition.Untyped as U
open import Tools.Nullary
open import Tools.PropositionalEquality

module Erasure.LogicalRelation.Fundamental.Unit
  {a k} {M : Set a} (𝕄 : Modality M)
  (open U M) (open T′ M) (open Modality 𝕄)
  {Δ : Con Term k} (⊢Δ : ⊢ Δ)
  (is-𝟘? : (p : M) → Dec (p ≡ 𝟘))
  {{eqrel : EqRelSet M}}
  where

open EqRelSet {{...}}

open import Erasure.LogicalRelation 𝕄 ⊢Δ is-𝟘?
open import Erasure.LogicalRelation.Subsumption 𝕄 ⊢Δ is-𝟘?
import Erasure.Target as T

open import Definition.LogicalRelation M
open import Definition.LogicalRelation.Fundamental M
open import Definition.LogicalRelation.Substitution M
open import Definition.LogicalRelation.Substitution.Introductions.Universe M
open import Definition.LogicalRelation.Substitution.Introductions.Unit M

open import Definition.Modality.Context 𝕄
open import Definition.Mode 𝕄

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
Unitʳ {m = m} ⊢Γ =
  [Γ] , [U] , λ _ _ → Uᵣ (Unitⱼ ⊢Δ) ◀ ⌜ m ⌝
  where
  [Γ] = valid ⊢Γ
  [U] = Uᵛ [Γ]

starʳ : ∀ {l} → ⊢ Γ
      → ∃ λ ([Γ] : ⊩ᵛ Γ)
      → ∃ λ ([Unit] : Γ ⊩ᵛ⟨ l ⟩ Unit / [Γ])
      → γ ▸ Γ ⊩ʳ⟨ l ⟩ star ∷[ m ] Unit / [Γ] / [Unit]
starʳ {m = m} ⊢Γ =
    [Γ] , [Unit]
  , λ _ _ → starᵣ (starⱼ ⊢Δ) T.refl ◀ ⌜ m ⌝
  where
  [Γ]    = valid ⊢Γ
  [Unit] = Unitᵛ [Γ]
