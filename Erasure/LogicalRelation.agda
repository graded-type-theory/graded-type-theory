{-# OPTIONS --without-K --safe #-}
open import Definition.Modality.Erasure

open import Definition.Typed.EqualityRelation


module Erasure.LogicalRelation {{eqrel : EqRelSet Erasure}} where
open EqRelSet {{...}}

open import Definition.LogicalRelation Erasure
open import Definition.Untyped Erasure as U hiding (_∷_)
open import Definition.Untyped.Properties Erasure using (noClosedNe)
open import Definition.Typed Erasure --using (_⊢_∷_ ; _⊢_⇒*_∷_) --as Ty
open import Definition.Typed.Weakening Erasure

open import Erasure.Target as T hiding (_⇒*_)
open import Erasure.Extraction

open import Tools.Product


private
  variable
    t′ : U.Term 0
    v′ : T.Term 0

-- Logical relation for erasure for base types

data _®_∷U (t : U.Term 0) (v : T.Term 0) : Set where
  Uᵣ : ε ⊢ t ∷ U → v T.⇒* undefined → t ® v ∷U

data _®_∷ℕ (t : U.Term 0) (v : T.Term 0) : Set where
  zeroᵣ : ε ⊢ t ⇒* U.zero ∷ ℕ → v T.⇒* T.zero → t ® v ∷ℕ
  sucᵣ : ε ⊢ t ⇒* U.suc t′ ∷ ℕ → v T.⇒* T.suc v′ → t′ ® v′ ∷ℕ → t ® v ∷ℕ

data _®_∷Empty (t : U.Term 0) (v : T.Term 0) : Set where
  Emptyᵣ : ε ⊢ t ∷ Empty → v T.⇒* undefined → t ® v ∷Empty

data _®_∷Unit (t : U.Term 0) (v : T.Term 0) : Set where
  starᵣ : ε ⊢ t ⇒* U.star ∷ Unit → v T.⇒* T.star → t ® v ∷Unit

-- Logical relation for erasure

_®⟨_⟩_∷_/_ : (t : U.Term 0) (l : TypeLevel) (v : T.Term 0)
             (A : U.Term 0) ([A] : ε ⊩⟨ l ⟩ A) → Set
t ®⟨ l ⟩ v ∷ U / Uᵣ x     = t ® v ∷U
t ®⟨ l ⟩ v ∷ A / ℕᵣ x     = t ® v ∷ℕ
t ®⟨ l ⟩ v ∷ A / Emptyᵣ x = t ® v ∷Empty
t ®⟨ l ⟩ v ∷ A / Unitᵣ x  = t ® v ∷Unit
t ®⟨ l ⟩ v ∷ A / ne′ K D neK K≡K with noClosedNe neK
... | ()
t ®⟨ l ⟩ v ∷ A / Bᵣ′ (BΠ ω q) F G D ⊢F ⊢G A≡A [F] [G] G-ext =
  ∀ {a w} → ([a] : ε ⊩⟨ l ⟩ a ∷ U.wk id F / [F] id ε)
          → a ®⟨ l ⟩ w ∷ U.wk id F / [F] id ε
          → (t ∘ ω ▷ a) ®⟨ l ⟩ v ∘ w ∷ U.wk (lift id) G U.[ a ] / [G] id ε [a]
t ®⟨ l ⟩ v ∷ A / Bᵣ′ (BΠ 𝟘 q) F G D ⊢F ⊢G A≡A [F] [G] G-ext =
  ∀ {a} → ([a] : ε ⊩⟨ l ⟩ a ∷ U.wk id F / [F] id ε)
        → (t ∘ 𝟘 ▷ a) ®⟨ l ⟩ v ∘ undefined ∷ U.wk (lift id) G U.[ a ] / [G] id ε [a]
t ®⟨ l ⟩ v ∷ A / Bᵣ′ (BΣ q) F G D ⊢F ⊢G A≡A [F] [G] G-ext =
  ∀ {t₁ t₂ v₁ v₂} → ([t₁] : ε ⊩⟨ l ⟩ t₁ ∷ U.wk id F / [F] id ε)
                  → ([t₂] : ε ⊩⟨ l ⟩ t₂ ∷ U.wk (lift id) G U.[ t₁ ] / [G] id ε [t₁])
                  → ε ⊢ t ⇒* U.prod t₁ t₂ ∷ Σ q ▷ F ▹ G
                  × v T.⇒* T.prod v₁ v₂
                  × t₁ ®⟨ l ⟩ v₁ ∷ U.wk id F / [F] id ε
                  × t₂ ®⟨ l ⟩ v₂ ∷ U.wk (lift id) G U.[ t₁ ] / [G] id ε [t₁]
t ®⟨ ¹ ⟩ v ∷ A / emb 0<1 [A] = t ®⟨ ⁰ ⟩ v ∷ A / [A]
