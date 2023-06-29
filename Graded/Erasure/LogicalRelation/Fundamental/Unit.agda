------------------------------------------------------------------------
-- Graded.Erasure validity of the unit type.
------------------------------------------------------------------------

open import Graded.Modality
open import Definition.Typed.EqualityRelation
import Definition.Typed
open import Definition.Typed.Restrictions
import Definition.Untyped
open import Tools.Nullary
open import Tools.PropositionalEquality

module Graded.Erasure.LogicalRelation.Fundamental.Unit
  {a k} {M : Set a}
  (open Definition.Untyped M)
  (𝕄 : Modality M)
  (open Modality 𝕄)
  (R : Type-restrictions M)
  (open Definition.Typed R)
  (is-𝟘? : (p : M) → Dec (p ≡ 𝟘))
  {{eqrel : EqRelSet R}}
  {Δ : Con Term k} (⊢Δ : ⊢ Δ)
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Graded.Erasure.LogicalRelation 𝕄 R is-𝟘? ⊢Δ
open import Graded.Erasure.LogicalRelation.Subsumption 𝕄 R is-𝟘? ⊢Δ
import Graded.Erasure.Target as T

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Fundamental R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Introductions.Universe R
open import Definition.LogicalRelation.Substitution.Introductions.Unit R

open import Graded.Context 𝕄
open import Graded.Mode 𝕄

open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    γ : Conₘ n
    Γ : Con Term n
    m : Mode

Unitʳ : ⊢ Γ
      → Unit-allowed
      → ∃ λ ([Γ] : ⊩ᵛ Γ)
      → ∃ λ ([U] : Γ ⊩ᵛ⟨ ¹ ⟩ U / [Γ])
      → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ Unit ∷[ m ] U / [Γ] / [U]
Unitʳ {m = m} ⊢Γ ok =
  [Γ] , [U] , λ _ _ → Uᵣ (Unitⱼ ⊢Δ ok) ◀ ⌜ m ⌝
  where
  [Γ] = valid ⊢Γ
  [U] = Uᵛ [Γ]

starʳ : ∀ {l}
      → ⊢ Γ
      → Unit-allowed
      → ∃ λ ([Γ] : ⊩ᵛ Γ)
      → ∃ λ ([Unit] : Γ ⊩ᵛ⟨ l ⟩ Unit / [Γ])
      → γ ▸ Γ ⊩ʳ⟨ l ⟩ star ∷[ m ] Unit / [Γ] / [Unit]
starʳ {m = m} ⊢Γ ok =
    [Γ] , [Unit]
  , λ _ _ → starᵣ (starⱼ ⊢Δ ok) T.refl ◀ ⌜ m ⌝
  where
  [Γ]    = valid ⊢Γ
  [Unit] = Unitᵛ [Γ] ok
