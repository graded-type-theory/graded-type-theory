{-# OPTIONS --without-K  #-}
open import Definition.Modality.Erasure

open import Definition.Typed.EqualityRelation


module Erasure.LogicalRelation {{eqrel : EqRelSet Erasure}} where
open EqRelSet {{...}}

open import Definition.LogicalRelation Erasure
open import Definition.LogicalRelation.Substitution Erasure
open import Definition.Untyped Erasure as U hiding (_∷_)
open import Definition.Untyped.Properties Erasure using (noClosedNe)
open import Definition.Typed Erasure --using (_⊢_∷_ ; _⊢_⇒*_∷_) --as Ty
open import Definition.Typed.Weakening Erasure

open import Erasure.Target as T hiding (_⇒*_)
open import Erasure.Extraction

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
  Uᵣ : ε ⊢ t ∷ U → v T.⇒* undefined → t ® v ∷U

data _®_∷ℕ (t : U.Term 0) (v : T.Term 0) : Set where
  zeroᵣ : ε ⊢ t ⇒* U.zero ∷ ℕ → v T.⇒* T.zero → t ® v ∷ℕ
  sucᵣ : ε ⊢ t ⇒* U.suc t′ ∷ ℕ → v T.⇒* T.suc v′ → t′ ® v′ ∷ℕ → t ® v ∷ℕ

data _®_∷Empty (t : U.Term 0) (v : T.Term 0) : Set where

data _®_∷Unit (t : U.Term 0) (v : T.Term 0) : Set where
  starᵣ : ε ⊢ t ∷ Unit → v T.⇒* T.star → t ® v ∷Unit

-- Logical relation for erasure

_®⟨_⟩_∷_/_ : (t : U.Term 0) (l : TypeLevel) (v : T.Term 0)
             (A : U.Term 0) ([A] : ε ⊩⟨ l ⟩ A) → Set
t ®⟨ l ⟩ v ∷ U / Uᵣ x     = t ® v ∷U
t ®⟨ l ⟩ v ∷ A / ℕᵣ x     = t ® v ∷ℕ
t ®⟨ l ⟩ v ∷ A / Emptyᵣ x = t ® v ∷Empty
t ®⟨ l ⟩ v ∷ A / Unitᵣ x  = t ® v ∷Unit
t ®⟨ l ⟩ v ∷ A / ne′ K D neK K≡K with noClosedNe neK
... | ()

-- Ordinary Π:
t ®⟨ l ⟩ v ∷ A / Bᵣ′ (BΠ ω q) F G D ⊢F ⊢G A≡A [F] [G] G-ext =
  ∀ {a w} → ([a] : ε ⊩⟨ l ⟩ a ∷ U.wk id F / [F] id ε)
          → a ®⟨ l ⟩ w ∷ U.wk id F / [F] id ε
          → (t ∘ ω ▷ a) ®⟨ l ⟩ v ∘ w ∷ U.wk (lift id) G U.[ a ] / [G] id ε [a]

-- Erased Π:
t ®⟨ l ⟩ v ∷ A / Bᵣ′ (BΠ 𝟘 q) F G D ⊢F ⊢G A≡A [F] [G] G-ext =
  ∀ {a} → ([a] : ε ⊩⟨ l ⟩ a ∷ U.wk id F / [F] id ε)
        → (t ∘ 𝟘 ▷ a) ®⟨ l ⟩ v ∘ undefined ∷ U.wk (lift id) G U.[ a ] / [G] id ε [a]

-- Σ: (with reduction to whnf)
-- t ®⟨ l ⟩ v ∷ A / Bᵣ′ (BΣ q) F G D ⊢F ⊢G A≡A [F] [G] G-ext =
--   ∀ {t₁ t₂ v₁ v₂} → ([t₁] : ε ⊩⟨ l ⟩ t₁ ∷ U.wk id F / [F] id ε)
--                   → ([t₂] : ε ⊩⟨ l ⟩ t₂ ∷ U.wk (lift id) G U.[ t₁ ] / [G] id ε [t₁])
--                   → ε ⊢ t ⇒* U.prod t₁ t₂ ∷ Σ q ▷ F ▹ G
--                   × v T.⇒* T.prod v₁ v₂
--                   × t₁ ®⟨ l ⟩ v₁ ∷ U.wk id F / [F] id ε
--                   × t₂ ®⟨ l ⟩ v₂ ∷ U.wk (lift id) G U.[ t₁ ] / [G] id ε [t₁]

-- -- Alternative Σ using projections
t ®⟨ l ⟩ v ∷ A / Bᵣ′ (BΣ q) F G D ⊢F ⊢G A≡A [F] [G] G-ext =
  let t₁ = U.fst t
      t₂ = U.snd t
      v₁ = T.fst v
      v₂ = T.snd v
  in ([t₁] : ε ⊩⟨ l ⟩ t₁ ∷ U.wk id F / [F] id ε)
   → t₁ ®⟨ l ⟩ v₁ ∷ U.wk id F / [F] id ε
   × t₂ ®⟨ l ⟩ v₂ ∷ U.wk (lift id) G U.[ t₁ ] / [G] id ε [t₁]

-- Subsumption:
t ®⟨ ¹ ⟩ v ∷ A / emb 0<1 [A] = t ®⟨ ⁰ ⟩ v ∷ A / [A]


-- Logical relation for contexts

data _⊩_®⟨_⟩_/_ : (Γ : Con U.Term n) (σₜₛ : U.Subst 0 n) (l : TypeLevel)
                  (σᵥₛ : T.Subst 0 n) ([Γ] : ⊩ᵛ Γ) → Set where
     ε   : ∀ {l} → ε ⊩ U.idSubst ®⟨ l ⟩ T.idSubst / ε
     _∙_ : ∀ {Γ : Con U.Term n} {t A : U.Term n} {v : T.Term n} {l : TypeLevel}
             {σₜₛ : U.Subst 0 n} {σᵥₛ : T.Subst 0 n} {[Γ] : ⊩ᵛ Γ}
             {[σₜₛ] :  ε ⊩ˢ σₜₛ ∷ Γ / [Γ] / ε} {[A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ]}
         → Γ ⊩ σₜₛ ®⟨ l ⟩ σᵥₛ / [Γ]
         → U.subst σₜₛ t ®⟨ l ⟩ T.subst σᵥₛ v ∷ U.subst σₜₛ A / proj₁ ([A] ε [σₜₛ])
         → (Γ ∙ A) ⊩ (U.consSubst σₜₛ (U.subst σₜₛ t)) ®⟨ l ⟩ (T.consSubst σᵥₛ (T.subst σᵥₛ v)) / [Γ] ∙ [A]
