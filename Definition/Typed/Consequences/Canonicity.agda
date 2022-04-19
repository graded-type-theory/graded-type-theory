{-# OPTIONS --without-K --safe #-}

module Definition.Typed.Consequences.Canonicity (M : Set) where

open import Definition.Untyped M hiding (_∷_)

open import Definition.Typed M
open import Definition.Typed.Weakening M
open import Definition.Typed.Properties M
open import Definition.Typed.EqRelInstance M
open import Definition.LogicalRelation M
open import Definition.LogicalRelation.Irrelevance M
open import Definition.LogicalRelation.ShapeView M
open import Definition.LogicalRelation.Fundamental.Reducibility M
open import Definition.Typed.Consequences.Inversion M
open import Definition.Typed.Consequences.Inequality M

open import Tools.Empty
open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat

-- Turns a natural number into its term representation
sucᵏ : Nat → Term n
sucᵏ 0 = zero
sucᵏ (1+ n) = suc (sucᵏ n)

-- Helper function for canonicity for reducible natural properties
canonicity″ : ∀ {t}
              → Natural-prop ε t
              → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ
canonicity″ (sucᵣ (ℕₜ n₁ d n≡n prop)) =
  let a , b = canonicity″ prop
  in  1+ a , suc-cong (trans (subset*Term (redₜ d)) b)
canonicity″ zeroᵣ = 0 , refl (zeroⱼ ε)
canonicity″ (ne (neNfₜ neK ⊢k k≡k)) = ⊥-elim (noNe ⊢k neK)

-- Helper function for canonicity for specific reducible natural numbers
canonicity′ : ∀ {t l}
             → ([ℕ] : ε ⊩⟨ l ⟩ℕ ℕ)
             → ε ⊩⟨ l ⟩ t ∷ ℕ / ℕ-intr [ℕ]
             → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ
canonicity′ (noemb [ℕ]) (ℕₜ n d n≡n prop) =
  let a , b = canonicity″ prop
  in  a , trans (subset*Term (redₜ d)) b
canonicity′ (emb 0<1 [ℕ]) [t] = canonicity′ [ℕ] [t]

-- Canonicity of natural numbers
canonicity : ∀ {t} → ε ⊢ t ∷ ℕ → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ
canonicity ⊢t with reducibleTerm ⊢t
canonicity ⊢t | [ℕ] , [t] =
  canonicity′ (ℕ-elim [ℕ]) (irrelevanceTerm [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [t])

-- Canonicity for Empty

¬Empty′ : ∀ {n} → ε ⊩Empty n ∷Empty → ⊥
¬Empty′ (Emptyₜ n _ n≡n (ne (neNfₜ neN ⊢n _))) =
  noNe ⊢n neN

¬Empty : ∀ {n} → ε ⊢ n ∷ Empty → ⊥
¬Empty {n} ⊢n =
  let [Empty] , [n] = reducibleTerm ⊢n
      [Empty]′ = Emptyᵣ {l = ¹} ([ Emptyⱼ ε , Emptyⱼ ε , id (Emptyⱼ ε) ])
      [n]′ = irrelevanceTerm [Empty] [Empty]′ [n]

  in ¬Empty′ [n]′
