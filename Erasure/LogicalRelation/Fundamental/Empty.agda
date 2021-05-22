{-# OPTIONS --without-K #-}
open import Definition.Modality.Erasure

open import Definition.Typed.EqualityRelation


module Erasure.LogicalRelation.Fundamental.Empty {{eqrel : EqRelSet Erasure}} where
open EqRelSet {{...}}

open import Erasure.LogicalRelation
open import Erasure.LogicalRelation.Irrelevance
import Erasure.Target as T

open import Definition.Untyped Erasure
open import Definition.Typed Erasure

open import Definition.LogicalRelation Erasure
open import Definition.LogicalRelation.Fundamental Erasure
open import Definition.LogicalRelation.Substitution Erasure
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
  in  [Γ] , [U] , λ [σ] x → Uᵣ (Emptyⱼ ε) T.refl

Emptyrecʳ′ : ∀ {l} → ([Empty] : ε ⊩⟨ l ⟩ Empty) → t ®⟨ l ⟩ v ∷ Empty / [Empty] → ⊥
Emptyrecʳ′ [Empty] t®v with irrelevanceTerm [Empty] (Emptyᵣ ([ Emptyⱼ ε , Emptyⱼ ε , id (Emptyⱼ ε) ])) t®v
... | ()

Emptyrecʳ : ∀ {l p} → ([Γ] : ⊩ᵛ Γ) → ([Empty] : Γ ⊩ᵛ⟨ l ⟩ Empty / [Γ])
          → (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷ Empty / [Γ] / [Empty])
          → ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
          → γ ▸ Γ ⊩ʳ⟨ l ⟩ Emptyrec p A t ∷ A / [Γ] / [A]
Emptyrecʳ [Γ] [Empty] ⊩ʳt [A] [σ] σ®σ′ =
  let t®v:Empty = ⊩ʳt [σ] σ®σ′
  in  ⊥-elim (Emptyrecʳ′ (proj₁ ([Empty] ε [σ])) t®v:Empty)
