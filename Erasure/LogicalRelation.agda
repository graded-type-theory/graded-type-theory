open import Definition.Modality.Instances.Erasure
open import Definition.Modality.Restrictions
open import Definition.Typed.EqualityRelation
open import Definition.Untyped Erasure as U hiding (_∷_; _∘_)
open import Definition.Typed Erasure

module Erasure.LogicalRelation
  {k} {Δ : Con Term k} (⊢Δ : ⊢ Δ)
  (restrictions : Restrictions Erasure)
  {{eqrel : EqRelSet Erasure}}
  where

open EqRelSet {{...}}

open import Definition.Modality.Instances.Erasure.Modality restrictions
open import Definition.LogicalRelation Erasure
open import Definition.LogicalRelation.Substitution Erasure
open import Definition.Modality.Context ErasureModality
open import Definition.Mode ErasureModality
open import Definition.Typed.Weakening Erasure

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
    t′ : U.Term n
    v′ : T.Term n

-- Logical relation for erasure for base types

data _®_∷U (t : U.Term k) (v : T.Term k) : Set where
  Uᵣ : Δ ⊢ t ∷ U → t ® v ∷U

data _®_∷ℕ (t : U.Term k) (v : T.Term k) : Set where
  zeroᵣ : Δ ⊢ t ⇒* U.zero ∷ ℕ → v T.⇒* T.zero → t ® v ∷ℕ
  sucᵣ : Δ ⊢ t ⇒* U.suc t′ ∷ ℕ → v T.⇒* T.suc v′ → t′ ® v′ ∷ℕ → t ® v ∷ℕ

data _®_∷Empty (t : U.Term k) (v : T.Term k) : Set where

data _®_∷Unit (t : U.Term k) (v : T.Term k) : Set where
  starᵣ : Δ ⊢ t ∷ Unit → v T.⇒* T.star → t ® v ∷Unit

mutual

  -- Logical relation for erasure

  _®⟨_⟩_∷_/_ : (t : U.Term k) (l : TypeLevel) (v : T.Term k)
               (A : U.Term k) ([A] : Δ ⊩⟨ l ⟩ A) → Set
  t ®⟨ l ⟩ v ∷ A / Uᵣ x     = t ® v ∷U
  t ®⟨ l ⟩ v ∷ A / ℕᵣ x     = t ® v ∷ℕ
  t ®⟨ l ⟩ v ∷ A / Emptyᵣ x = t ® v ∷Empty
  t ®⟨ l ⟩ v ∷ A / Unitᵣ x  = t ® v ∷Unit
  t ®⟨ l ⟩ v ∷ A / ne′ K D neK K≡K = PE.⊥

  -- Ordinary Π:
  t ®⟨ l ⟩ v ∷ A / Bᵣ′ (BΠ ω q) F G D ⊢F ⊢G A≡A [F] [G] G-ext =
    ∀ {a w} →
    ([a] : Δ ⊩⟨ l ⟩ a ∷ U.wk id F / [F] id ⊢Δ) →
    a ®⟨ l ⟩ w ∷ U.wk id F / [F] id ⊢Δ →
    (t ∘⟨ ω ⟩ a) ®⟨ l ⟩ v ∘ w ∷ U.wk (lift id) G U.[ a ] / [G] id ⊢Δ [a]

  -- Erased Π:
  t ®⟨ l ⟩ v ∷ A / Bᵣ′ (BΠ 𝟘 q) F G D ⊢F ⊢G A≡A [F] [G] G-ext =
    ∀ {a} →
    ([a] : Δ ⊩⟨ l ⟩ a ∷ U.wk id F / [F] id ⊢Δ) →
    (t ∘⟨ 𝟘 ⟩ a) ®⟨ l ⟩ v ∘ ↯ ∷ U.wk (lift id) G U.[ a ] /
      [G] id ⊢Δ [a]

  -- Σ:
  t ®⟨ l ⟩ v ∷ A / Bᵣ′ (BΣ m p q) F G D ⊢F ⊢G A≡A [F] [G] G-ext =
    ∃₂ λ t₁ t₂ →
    Δ ⊢ t ⇒* U.prod m p t₁ t₂ ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G ×
    Σ (Δ ⊩⟨ l ⟩ t₁ ∷ U.wk id F / [F] id ⊢Δ) λ [t₁] →
    ∃ λ v₂ →
    t₂ ®⟨ l ⟩ v₂ ∷ U.wk (lift id) G U.[ t₁ ] / [G] id ⊢Δ [t₁] ×
    Σ-® l F ([F] id ⊢Δ) t₁ v v₂ p

  -- Subsumption:
  t ®⟨ ¹ ⟩ v ∷ A / emb 0<1 [A] = t ®⟨ ⁰ ⟩ v ∷ A / [A]

  -- Extra data for Σ-types, depending on whether the first component
  -- is erased or not.

  Σ-® :
    (l : TypeLevel) (F : U.Term k) →
    Δ ⊩⟨ l ⟩ U.wk id F →
    U.Term k → T.Term k → T.Term k → Erasure → Set
  Σ-® _ _ _   _  v v₂ 𝟘 = v T.⇒* v₂
  Σ-® l F [F] t₁ v v₂ ω =
    ∃ λ v₁ →
    v T.⇒* T.prod v₁ v₂ ×
    t₁ ®⟨ l ⟩ v₁ ∷ U.wk id F / [F]


-- Logical relation for terms of quantified type
_®⟨_⟩_∷_◂_/_ : (t : U.Term k) (l : TypeLevel) (v : T.Term k)
               (A : U.Term k) (p : Erasure) ([A] : Δ ⊩⟨ l ⟩ A) → Set
t ®⟨ l ⟩ v ∷ A ◂ 𝟘 / [A] = ⊤
t ®⟨ l ⟩ v ∷ A ◂ ω / [A] = t ®⟨ l ⟩ v ∷ A / [A]

-- Logical relation for substitutions

_®⟨_⟩_∷[_]_◂_/_/_ :
  (σₜ : U.Subst k n) (l : TypeLevel)
  (σᵥ : T.Subst k n) (m : Mode) (Γ : Con U.Term n) (γ : Conₘ n)
  ([Γ] : ⊩ᵛ Γ) ([σ] : Δ ⊩ˢ σₜ ∷ Γ / [Γ] / ⊢Δ) → Set
σₜ ®⟨ l ⟩ σᵥ ∷[ _ ] ε ◂ ε / ε / (lift tt) = ⊤
σₜ ®⟨ l ⟩ σᵥ ∷[ m ] Γ ∙ A ◂ γ ∙ p / _∙_ {l = l₁} [Γ] [A] / ([σ] , [σA]) =
  ((U.tail σₜ) ®⟨ l ⟩ (T.tail σᵥ) ∷[ m ] Γ ◂ γ / [Γ] / [σ]) ×
  ((U.head σₜ) ®⟨ l₁ ⟩ (T.head σᵥ) ∷ (U.subst (U.tail σₜ) A)
  ◂ ⌜ m ⌝ · p / proj₁ (unwrap [A] ⊢Δ [σ]))

-- Validity of erasure

_▸_⊩ʳ⟨_⟩_∷[_]_/_/_ :
  (γ : Conₘ n) (Γ : Con U.Term n) (l : TypeLevel)
  (t : U.Term n) (m : Mode) (A : U.Term n)
  ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ]) → Set
γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] A / [Γ] / [A] =
  ∀ {σ σ′} →
  ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) →
  σ ®⟨ l ⟩ σ′ ∷[ m ] Γ ◂ γ / [Γ] / [σ] →
  U.subst σ t ®⟨ l ⟩ T.subst σ′ (erase t) ∷ U.subst σ A ◂ ⌜ m ⌝ /
  proj₁ (unwrap [A] ⊢Δ [σ])

-- A different view of the extra data for Σ-types.

data Σ-®′
  (l : TypeLevel) (F : U.Term k)
  ([F] : Δ ⊩⟨ l ⟩ U.wk id F)
  (t₁ : U.Term k) (v v₂ : T.Term k) : Erasure → Set where
  𝟘 : v T.⇒* v₂ → Σ-®′ l F [F] t₁ v v₂ 𝟘
  ω : ∀ v₁ → v T.⇒* T.prod v₁ v₂ → t₁ ®⟨ l ⟩ v₁ ∷ U.wk id F / [F] →
      Σ-®′ l F [F] t₁ v v₂ ω

-- A function that provides a different view of the extra data for
-- Σ-types.

Σ-®-view :
  ∀ {l F} {[F] : Δ ⊩⟨ l ⟩ U.wk id F} {t₁ v v₂ p} →
  Σ-® l F [F] t₁ v v₂ p →
  Σ-®′ l F [F] t₁ v v₂ p
Σ-®-view {p = 𝟘} v⇒*v₂                   = 𝟘 v⇒*v₂
Σ-®-view {p = ω} (v₁ , v⇒*v₁,v₂ , t₁®v₁) = ω v₁ v⇒*v₁,v₂ t₁®v₁
