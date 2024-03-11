------------------------------------------------------------------------
-- Graded.Erasure validity of the empty type.
------------------------------------------------------------------------

import Definition.Typed
open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality
open import Tools.PropositionalEquality
open import Tools.Relation

module Graded.Erasure.LogicalRelation.Fundamental.Empty
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  (is-𝟘? : (p : M) → Dec (p ≡ 𝟘))
  {R : Type-restrictions 𝕄}
  (open Definition.Typed R)
  (as : Assumptions R)
  (open Assumptions as)
  (consistent : Consistent Δ)
  where

open import Graded.Erasure.LogicalRelation is-𝟘? as
open import Graded.Erasure.LogicalRelation.Subsumption is-𝟘? as
import Graded.Erasure.Target as T

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Fundamental R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Irrelevance R
open import Definition.LogicalRelation.Substitution.Introductions.Universe R
open import Definition.LogicalRelation.Substitution.Introductions.Empty R
open import Definition.Untyped M hiding (_∷_)

open import Graded.Context 𝕄
open import Graded.Mode 𝕄

open import Tools.Empty
open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    γ : Conₘ n
    Γ : Con Term n
    t A : Term n
    v : T.Term n
    m : Mode

Emptyʳ : ⊢ Γ
      → ∃ λ ([Γ] : ⊩ᵛ Γ)
      → ∃ λ ([U] : Γ ⊩ᵛ⟨ ¹ ⟩ U / [Γ])
      → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ Empty ∷[ m ] U / [Γ] / [U]
Emptyʳ {m = m} ⊢Γ =
  [Γ] , [U] , λ _ _ → Uᵣ ◀ ⌜ m ⌝
  where
  [Γ] = valid ⊢Γ
  [U] = Uᵛ [Γ]

emptyrecʳ′ : ∀ {l p} → ([Γ] : ⊩ᵛ Γ)
          → ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
          → ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Empty / [Γ] / Emptyᵛ [Γ])
          → γ ▸ Γ ⊩ʳ⟨ l ⟩ emptyrec p A t ∷[ m ] A / [Γ] / [A]
emptyrecʳ′ [Γ] [A] [t] [σ] σ®σ′ with proj₁ ([t] ⊢Δ [σ])
... | Emptyₜ n d n≡n (ne (neNfₜ neK ⊢k k≡k)) =
  ⊥-elim (consistent _ ⊢k)


emptyrecʳ : ∀ {l p} → ([Γ] : ⊩ᵛ Γ)
          → ([Empty] : Γ ⊩ᵛ⟨ l ⟩ Empty / [Γ])
          → ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
          → ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Empty / [Γ] / [Empty])
          → γ ▸ Γ ⊩ʳ⟨ l ⟩ emptyrec p A t ∷[ m ] A / [Γ] / [A]
emptyrecʳ {A = A} {t = t} {l = l} {p} [Γ] [Empty] [A] [t] [σ] σ®σ′ =
  let [Empty]′ = Emptyᵛ {l = l} [Γ]
      [t]′ = irrelevanceTerm {A = Empty} {t = t} [Γ] [Γ] [Empty] [Empty]′ [t]
  in  emptyrecʳ′ {A = A} {t = t} {p = p} [Γ] [A] [t]′ [σ] σ®σ′
