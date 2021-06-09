{-# OPTIONS --without-K #-}
open import Definition.Modality.Erasure

open import Definition.Typed.EqualityRelation


module Erasure.LogicalRelation.Fundamental.Empty {{eqrel : EqRelSet Erasure}} where
open EqRelSet {{...}}

open import Erasure.LogicalRelation
open import Erasure.LogicalRelation.Properties
import Erasure.Target as T

open import Definition.Untyped Erasure
open import Definition.Untyped.Properties Erasure
open import Definition.Typed Erasure

open import Definition.LogicalRelation Erasure
open import Definition.LogicalRelation.Fundamental Erasure
open import Definition.LogicalRelation.Substitution Erasure
open import Definition.LogicalRelation.Substitution.Irrelevance Erasure
open import Definition.LogicalRelation.Substitution.Introductions.Universe Erasure
open import Definition.LogicalRelation.Substitution.Introductions.Empty Erasure

open import Definition.Modality.Context ErasureModality

open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality

private
  variable
    n : Nat
    γ : Conₘ n
    Γ : Con Term n
    t A : Term n
    v : T.Term n

Emptyʳ : ⊢ Γ
      → ∃ λ ([Γ] : ⊩ᵛ Γ)
      → ∃ λ ([U] : Γ ⊩ᵛ⟨ ¹ ⟩ U / [Γ])
      → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ Empty ∷ U / [Γ] / [U]
Emptyʳ ⊢Γ =
  let [Γ] = valid ⊢Γ
      [U] = Uᵛ [Γ]
  in  [Γ] , [U] , λ [σ] x → Uᵣ (Emptyⱼ ε)


Emptyrecʳ′ : ∀ {l p} → ([Γ] : ⊩ᵛ Γ)
          → ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
          → ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Empty / [Γ] / Emptyᵛ [Γ])
          → γ ▸ Γ ⊩ʳ⟨ l ⟩ Emptyrec p A t ∷ A / [Γ] / [A]
Emptyrecʳ′ [Γ] [A] [t] [σ] σ®σ′ with proj₁ ([t] ε [σ])
... | Emptyₜ n d n≡n (ne (neNfₜ neK ⊢k k≡k)) = ⊥-elim (noClosedNe neK)


Emptyrecʳ : ∀ {l p} → ([Γ] : ⊩ᵛ Γ)
          → ([Empty] : Γ ⊩ᵛ⟨ l ⟩ Empty / [Γ])
          → ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
          → ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Empty / [Γ] / [Empty])
          → γ ▸ Γ ⊩ʳ⟨ l ⟩ Emptyrec p A t ∷ A / [Γ] / [A]
Emptyrecʳ {A = A} {t = t} {l = l} {p} [Γ] [Empty] [A] [t] [σ] σ®σ′ =
  let [Empty]′ = Emptyᵛ {l = l} [Γ]
      [t]′ = irrelevanceTerm {A = Empty} {t = t} [Γ] [Γ] [Empty] [Empty]′ [t]
  in  Emptyrecʳ′ {A = A} {t = t} {p = p} [Γ] [A] [t]′ [σ] σ®σ′
