open import Definition.Modality
open import Definition.Typed.EqualityRelation
import Definition.Typed as T′
import Definition.Untyped as U hiding (_∷_)
open import Tools.Nullary
open import Tools.PropositionalEquality

module Erasure.LogicalRelation.Fundamental.Empty
  {a k} {M : Set a} (𝕄 : Modality M)
  (open U M) (open T′ M) (open Modality 𝕄)
  {Δ : Con Term k} (⊢Δ : ⊢ Δ)
  (is-𝟘? : (p : M) → Dec (p ≡ 𝟘))
  (consistent : ∀ {t} → Δ ⊢ t ∷ Empty → ⊥)
  {{eqrel : EqRelSet M}}
  where

open EqRelSet {{...}}

open import Erasure.LogicalRelation 𝕄 ⊢Δ is-𝟘?
open import Erasure.LogicalRelation.Subsumption 𝕄 ⊢Δ is-𝟘?
import Erasure.Target as T

open import Definition.LogicalRelation M
open import Definition.LogicalRelation.Fundamental M
open import Definition.LogicalRelation.Substitution M
open import Definition.LogicalRelation.Substitution.Irrelevance M
open import Definition.LogicalRelation.Substitution.Introductions.Universe M
open import Definition.LogicalRelation.Substitution.Introductions.Empty M

open import Definition.Modality.Context 𝕄
open import Definition.Mode 𝕄

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
  [Γ] , [U] , λ _ _ → Uᵣ (Emptyⱼ ⊢Δ) ◀ ⌜ m ⌝
  where
  [Γ] = valid ⊢Γ
  [U] = Uᵛ [Γ]

Emptyrecʳ′ : ∀ {l p} → ([Γ] : ⊩ᵛ Γ)
          → ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
          → ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Empty / [Γ] / Emptyᵛ [Γ])
          → γ ▸ Γ ⊩ʳ⟨ l ⟩ Emptyrec p A t ∷[ m ] A / [Γ] / [A]
Emptyrecʳ′ [Γ] [A] [t] [σ] σ®σ′ with proj₁ ([t] ⊢Δ [σ])
... | Emptyₜ n d n≡n (ne (neNfₜ neK ⊢k k≡k)) = ⊥-elim (consistent ⊢k)


Emptyrecʳ : ∀ {l p} → ([Γ] : ⊩ᵛ Γ)
          → ([Empty] : Γ ⊩ᵛ⟨ l ⟩ Empty / [Γ])
          → ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
          → ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Empty / [Γ] / [Empty])
          → γ ▸ Γ ⊩ʳ⟨ l ⟩ Emptyrec p A t ∷[ m ] A / [Γ] / [A]
Emptyrecʳ {A = A} {t = t} {l = l} {p} [Γ] [Empty] [A] [t] [σ] σ®σ′ =
  let [Empty]′ = Emptyᵛ {l = l} [Γ]
      [t]′ = irrelevanceTerm {A = Empty} {t = t} [Γ] [Γ] [Empty] [Empty]′ [t]
  in  Emptyrecʳ′ {A = A} {t = t} {p = p} [Γ] [A] [t]′ [σ] σ®σ′
