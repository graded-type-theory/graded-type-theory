{-# OPTIONS --without-K --safe #-}

open import Tools.Relation

module Definition.Typed.Consequences.Consistency {a ℓ} (M′ : Setoid a ℓ) where

open Setoid M′ using () renaming (Carrier to M)

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed M′
open import Definition.Typed.Properties M′
open import Definition.Typed.EqRelInstance M′
open import Definition.LogicalRelation M′
open import Definition.LogicalRelation.Irrelevance M′
open import Definition.LogicalRelation.ShapeView M′
open import Definition.LogicalRelation.Fundamental.Reducibility M′

open import Tools.Empty
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    t : Term n

zero≢suc′ : ∀ {l} ([ℕ] : Γ ⊩⟨ l ⟩ℕ ℕ)
           → Γ ⊩⟨ l ⟩ zero ≡ suc t ∷ ℕ / ℕ-intr [ℕ] → ⊥
zero≢suc′ (noemb x) (ℕₜ₌ .(suc _) .(suc _) d d′ k≡k′ (sucᵣ x₁))
  with whnfRed*Term (redₜ d) zeroₙ
... | ()
zero≢suc′ (noemb x) (ℕₜ₌ .zero .zero d d′ k≡k′ zeroᵣ)
  with (PE.sym (whnfRed*Term (redₜ d′) sucₙ))
... | ()
zero≢suc′ (noemb x) (ℕₜ₌ k k′ d d′ k≡k′ (ne (neNfₜ₌ neK neM k≡m))) =
  zero≢ne neK (whnfRed*Term (redₜ d) zeroₙ)
zero≢suc′ (emb 0<1 [ℕ]) n = zero≢suc′ [ℕ] n

-- Zero cannot be judgmentally equal to suc t.
zero≢suc : Γ ⊢ zero ≡ suc t ∷ ℕ → ⊥
zero≢suc 0≡s =
  let [ℕ] , [0≡s] = reducibleEqTerm 0≡s
  in  zero≢suc′ (ℕ-elim [ℕ]) (irrelevanceEqTerm [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [0≡s])

zero≢one : Γ ⊢ zero ≡ suc zero ∷ ℕ → ⊥
zero≢one = zero≢suc
