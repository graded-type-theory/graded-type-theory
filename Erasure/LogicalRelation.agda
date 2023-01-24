{-# OPTIONS --without-K  --safe #-}

open import Definition.Modality.Instances.Erasure
open import Definition.Typed.EqualityRelation

module Erasure.LogicalRelation (Prodrec : Erasure → Set)
                               {{eqrel : EqRelSet Erasure′}} where
open EqRelSet {{...}}

open import Definition.Modality.Instances.Erasure.Modality Prodrec
open import Definition.LogicalRelation Erasure′
open import Definition.LogicalRelation.Substitution Erasure′
open import Definition.Modality.Context ErasureModality
open import Definition.Untyped Erasure as U hiding (_∷_; _∘_)
open import Definition.Typed Erasure′
open import Definition.Typed.Weakening Erasure′

open import Erasure.Target as T hiding (_⇒*_)
open import Erasure.Extraction

open import Tools.Level
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Unit


private
  variable
    m n : Nat
    t′ : U.Term 0
    v′ : T.Term 0

-- Logical relation for erasure for base types

data _®_∷U (t : U.Term 0) (v : T.Term 0) : Set where
  Uᵣ : ε ⊢ t ∷ U → t ® v ∷U

data _®_∷ℕ (t : U.Term 0) (v : T.Term 0) : Set where
  zeroᵣ : ε ⊢ t ⇒* U.zero ∷ ℕ → v T.⇒* T.zero → t ® v ∷ℕ
  sucᵣ : ε ⊢ t ⇒* U.suc t′ ∷ ℕ → v T.⇒* T.suc v′ → t′ ® v′ ∷ℕ → t ® v ∷ℕ

data _®_∷Empty (t : U.Term 0) (v : T.Term 0) : Set where

data _®_∷Unit (t : U.Term 0) (v : T.Term 0) : Set where
  starᵣ : ε ⊢ t ∷ Unit → v T.⇒* T.star → t ® v ∷Unit

-- Logical relation for erasure

_®⟨_⟩_∷_/_ : (t : U.Term 0) (l : TypeLevel) (v : T.Term 0)
             (A : U.Term 0) ([A] : ε ⊩⟨ l ⟩ A) → Set
t ®⟨ l ⟩ v ∷ A / Uᵣ x     = t ® v ∷U
t ®⟨ l ⟩ v ∷ A / ℕᵣ x     = t ® v ∷ℕ
t ®⟨ l ⟩ v ∷ A / Emptyᵣ x = t ® v ∷Empty
t ®⟨ l ⟩ v ∷ A / Unitᵣ x  = t ® v ∷Unit
t ®⟨ l ⟩ v ∷ A / ne′ K D neK K≡K = PE.⊥

-- Ordinary Π:
t ®⟨ l ⟩ v ∷ A / Bᵣ′ (BΠ ω q) F G D ⊢F ⊢G A≡A [F] [G] G-ext =
  ∀ {a w} → ([a] : ε ⊩⟨ l ⟩ a ∷ U.wk id F / [F] id ε)
          → a ®⟨ l ⟩ w ∷ U.wk id F / [F] id ε
          → (t ∘⟨ ω ⟩ a) ®⟨ l ⟩ v ∘ w ∷ U.wk (lift id) G U.[ a ] / [G] id ε [a]

-- Erased Π:
t ®⟨ l ⟩ v ∷ A / Bᵣ′ (BΠ 𝟘 q) F G D ⊢F ⊢G A≡A [F] [G] G-ext =
  ∀ {a} → ([a] : ε ⊩⟨ l ⟩ a ∷ U.wk id F / [F] id ε)
        → (t ∘⟨ 𝟘 ⟩ a) ®⟨ l ⟩ v ∘ undefined ∷ U.wk (lift id) G U.[ a ] / [G] id ε [a]

-- Σ:
t ®⟨ l ⟩ v ∷ A / Bᵣ′ (BΣ m q) F G D ⊢F ⊢G A≡A [F] [G] G-ext =
  ∃₄ λ t₁ t₂ v₁ v₂
     → ε ⊢ t ⇒* U.prod m t₁ t₂ ∷ Σ⟨ m ⟩ q ▷ F ▹ G
     × v T.⇒* T.prod v₁ v₂
     × Σ (ε ⊩⟨ l ⟩ t₁ ∷ U.wk id F / [F] id ε) λ [t₁]
     → t₁ ®⟨ l ⟩ v₁ ∷ U.wk id F / [F] id ε
     × (t₂ ®⟨ l ⟩ v₂ ∷ U.wk (lift id) G U.[ t₁ ] / [G] id ε [t₁])

-- Subsumption:
t ®⟨ ¹ ⟩ v ∷ A / emb 0<1 [A] = t ®⟨ ⁰ ⟩ v ∷ A / [A]


-- Logical relation for terms of quantified type
_®⟨_⟩_∷_◂_/_ : (t : U.Term 0) (l : TypeLevel) (v : T.Term 0)
               (A : U.Term 0) (p : Erasure) ([A] : ε ⊩⟨ l ⟩ A) → Set
t ®⟨ l ⟩ v ∷ A ◂ 𝟘 / [A] = ⊤
t ®⟨ l ⟩ v ∷ A ◂ ω / [A] = t ®⟨ l ⟩ v ∷ A / [A]

-- Logical relation for substitutions

_®⟨_⟩_∷_◂_/_/_ : (σₜ : U.Subst 0 n) (l : TypeLevel) (σᵥ : T.Subst 0 n) (Γ : Con U.Term n)
                 (γ : Conₘ n) ([Γ] : ⊩ᵛ Γ) ([σ] : ε ⊩ˢ σₜ ∷ Γ / [Γ] / ε) → Set
σₜ ®⟨ l ⟩ σᵥ ∷ ε ◂ ε / ε / (lift tt) = ⊤
σₜ ®⟨ l ⟩ σᵥ ∷ Γ ∙ A ◂ γ ∙ p / _∙_ {l = l₁} [Γ] [A] / ([σ] , [σA]) =
  ((U.tail σₜ) ®⟨ l ⟩ (T.tail σᵥ) ∷ Γ ◂ γ / [Γ] / [σ]) ×
  ((U.head σₜ) ®⟨ l₁ ⟩ (T.head σᵥ) ∷ (U.subst (U.tail σₜ) A) ◂ p / proj₁ (unwrap [A] ε [σ]))

-- Validity of erasure

_▸_⊩ʳ⟨_⟩_∷_/_/_ : (γ : Conₘ n) (Γ : Con U.Term n) (l : TypeLevel)
                   (t A : U.Term n) ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ]) → Set
γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷ A / [Γ] / [A] =
  ∀ {σ σ′} → ([σ] : ε ⊩ˢ σ ∷ Γ / [Γ] / ε)
           → σ ®⟨ l ⟩ σ′ ∷ Γ ◂ γ / [Γ] / [σ]
           → U.subst σ t ®⟨ l ⟩ T.subst σ′ (erase t) ∷ U.subst σ A / proj₁ (unwrap [A] ε [σ])
