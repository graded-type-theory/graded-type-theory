------------------------------------------------------------------------
-- Irrelevance lemmata for the logical relation
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Definition.Typed.EqualityRelation
import Definition.Typed
open import Definition.Typed.Restrictions
import Definition.Untyped
open import Graded.Modality
import Tools.PropositionalEquality as PE
open import Tools.Relation

module Graded.Erasure.LogicalRelation.Irrelevance
  {a} {M : Set a}
  (open Definition.Untyped M)
  {𝕄 : Modality M}
  (open Modality 𝕄)
  (R : Type-restrictions 𝕄)
  (open Definition.Typed R)
  (is-𝟘? : (p : M) → Dec (p PE.≡ 𝟘))
  {{eqrel : EqRelSet R}}
  {k} {Δ : Con Term k} (⊢Δ : ⊢ Δ)
  where

open EqRelSet {{...}}

open import Graded.Erasure.LogicalRelation R is-𝟘? ⊢Δ

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.ShapeView R
import Definition.LogicalRelation.Irrelevance R as I
open import Definition.LogicalRelation.Substitution R
import Definition.LogicalRelation.Substitution.Irrelevance R as IS

open import Definition.Typed.Weakening R hiding (wk)
open import Definition.Typed.Properties R

open import Graded.Context 𝕄
open import Graded.Mode 𝕄

open import Tools.Function
open import Tools.Level
open import Tools.Nat
open import Tools.Product
open import Tools.Unit

private
  variable
    n : Nat
    Γ : Con Term n
    A A′ t : Term n
    γ : Conₘ n
    p : M
    m : Mode

-- Irrelevance of logical relation for erasure using a ShapeView

irrelevanceTermSV : ∀ {l l′ t v A}
                  → ([A] : Δ ⊩⟨ l ⟩ A)
                    ([A]′ : Δ ⊩⟨ l′ ⟩ A)
                  → t ®⟨ l ⟩ v ∷ A / [A]
                  → ShapeView Δ l l′ A A [A] [A]′
                  → t ®⟨ l′ ⟩ v ∷ A / [A]′
irrelevanceTermSV .(Uᵣ UA) .(Uᵣ UB) t®v (Uᵥ UA UB) = t®v
irrelevanceTermSV .(ℕᵣ ℕA) .(ℕᵣ ℕB) t®v (ℕᵥ ℕA ℕB) = t®v
irrelevanceTermSV
  .(Unitᵣ UnitA) .(Unitᵣ UnitB) t®v (Unitᵥ UnitA UnitB) =
  t®v
irrelevanceTermSV
  [A] [A]′ t®v
  (Bᵥ (BΠ p q) (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
     (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
       with B-PE-injectivity BΠ! BΠ! (whrDet* (red D , ΠΣₙ) (red D₁ , ΠΣₙ))
... | PE.refl , PE.refl , _
       with is-𝟘? p
... | (yes p≡𝟘) = λ [a]′ →
  let [a] = I.irrelevanceTerm ([F]₁ id ⊢Δ) ([F] id ⊢Δ) [a]′
      t®v′ = t®v [a]
      SV′ = goodCasesRefl ([G] id ⊢Δ [a]) ([G]₁ id ⊢Δ [a]′)
  in  irrelevanceTermSV ([G] id ⊢Δ [a]) ([G]₁ id ⊢Δ [a]′) t®v′ SV′
... | (no p≢𝟘) = λ [a]′ a®w′ →
  let [a] = I.irrelevanceTerm ([F]₁ id ⊢Δ) ([F] id ⊢Δ) [a]′
      SV = goodCasesRefl ([F]₁ id ⊢Δ) ([F] id ⊢Δ)
      a®w = irrelevanceTermSV ([F]₁ id ⊢Δ) ([F] id ⊢Δ) a®w′ SV
      t®v′ = t®v [a] a®w
      SV′ = goodCasesRefl ([G] id ⊢Δ [a]) ([G]₁ id ⊢Δ [a]′)
  in  irrelevanceTermSV ([G] id ⊢Δ [a]) ([G]₁ id ⊢Δ [a]′) t®v′ SV′
irrelevanceTermSV {v = v}
  [A] [A]′ (t₁ , t₂ , t⇒t′ , [t₁] , v₂ , t₂®v₂ , extra)
  (Bᵥ (BΣ _ p _) (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
     (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
  with B-PE-injectivity BΣ! BΣ! (whrDet* (red D , ΠΣₙ) (red D₁ , ΠΣₙ))
... | PE.refl , PE.refl , _ =
  let [F]′ = [F] id ⊢Δ
      [F]₁′ = [F]₁ id ⊢Δ
      [t₁]′ = I.irrelevanceTerm [F]′ [F]₁′ [t₁]
      [Gt₁] = [G] id ⊢Δ [t₁]
      [Gt₁]₁ = [G]₁ id ⊢Δ [t₁]′
      t₂®v₂′ = irrelevanceTermSV [Gt₁] [Gt₁]₁ t₂®v₂
                 (goodCasesRefl [Gt₁] [Gt₁]₁)
  in  t₁ , t₂ , t⇒t′ , [t₁]′ , v₂ , t₂®v₂′
      , Σ-®-elim (λ _ → Σ-® _ _ [F]₁′ t₁ v v₂ p) extra
                 Σ-®-intro-𝟘
                 λ v₁ v⇒p t₁®v₁ p≢𝟘 →
                   Σ-®-intro-ω v₁ v⇒p (irrelevanceTermSV [F]′ [F]₁′ t₁®v₁
                               (goodCasesRefl [F]′ [F]₁′)) p≢𝟘
irrelevanceTermSV _ _ t®v (Idᵥ ⊩A ⊩B) =
  case whrDet* (red (_⊩ₗId_.⇒*Id ⊩A) , Idₙ)
         (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) of λ {
    PE.refl →
  t®v }
irrelevanceTermSV (emb 0<1 [A]) [A]′ t®v (emb⁰¹ SV) =
  irrelevanceTermSV [A] [A]′ t®v SV
irrelevanceTermSV [A] (emb 0<1 [A]′) t®v (emb¹⁰ SV) =
  irrelevanceTermSV [A] [A]′ t®v SV
-- Impossible cases
irrelevanceTermSV _ _ () (Emptyᵥ _ _)
irrelevanceTermSV _ _ () (ne _ _)

-- Irrelevance of logical relation for erasure

irrelevanceTerm : ∀ {l l′ t v A}
                → ([A] : Δ ⊩⟨ l ⟩ A)
                  ([A]′ : Δ ⊩⟨ l′ ⟩ A)
                → t ®⟨ l ⟩ v ∷ A / [A]
                → t ®⟨ l′ ⟩ v ∷ A / [A]′
irrelevanceTerm [A] [A]′ t®v =
  irrelevanceTermSV [A] [A]′ t®v (goodCasesRefl [A] [A]′)

-- Irrelevance of logical relation for erasure with propositionally equal types

irrelevanceTerm′ : ∀ {l l′ t v A}
                 → A PE.≡ A′
                 → ([A] : Δ ⊩⟨ l ⟩ A)
                 → ([A]′ : Δ ⊩⟨ l′ ⟩ A′)
                 → t ®⟨ l ⟩ v ∷ A / [A]
                 → t ®⟨ l′ ⟩ v ∷ A′ / [A]′
irrelevanceTerm′ PE.refl [A] [A]′ t®v = irrelevanceTerm [A] [A]′ t®v

-- Irrelevance of quantified logical relation for erasure

irrelevanceQuant : ∀ {l l′ t v A} p
                 → ([A] : Δ ⊩⟨ l ⟩ A)
                 → ([A]′ : Δ ⊩⟨ l′ ⟩ A)
                 → t ®⟨ l ⟩ v ∷ A ◂ p / [A]
                 → t ®⟨ l′ ⟩ v ∷ A ◂ p / [A]′
irrelevanceQuant p [A] [A]′ t®v with is-𝟘? p
... | yes PE.refl = lift tt
... | no p≢𝟘 = irrelevanceTerm [A] [A]′ t®v

irrelevanceQuant′ : ∀ {l l′ t v A A′} p
                  → A PE.≡ A′
                  → ([A] : Δ ⊩⟨ l ⟩ A)
                  → ([A]′ : Δ ⊩⟨ l′ ⟩ A′)
                  → t ®⟨ l ⟩ v ∷ A ◂ p / [A]
                  → t ®⟨ l′ ⟩ v ∷ A′ ◂ p / [A]′
irrelevanceQuant′ p PE.refl = irrelevanceQuant p


-- Irrelevance of related substitutions

irrelevanceSubst : ∀ {σ σ′}
                 → ([Γ] [Γ]′ : ⊩ᵛ Γ)
                   ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
                   ([σ]′ : Δ ⊩ˢ σ ∷ Γ / [Γ]′ / ⊢Δ)
                   (σ®σ′ : σ ® σ′ ∷[ m ] Γ ◂ γ / [Γ] / [σ])
                 → (σ ® σ′ ∷[ m ] Γ ◂ γ / [Γ]′ / [σ]′)
irrelevanceSubst {Γ = ε} {γ = ε} ε ε (lift tt) (lift tt) (lift tt) = lift tt
irrelevanceSubst {Γ = Γ ∙ A} {m = m} {γ = γ ∙ p}
                 ([Γ] ∙ [A]) ([Γ]′ ∙ [A]′) ([tailσ] , b) ([tailσ]′ , d) (σ®σ , t®v) =
  let σ®σ′ = irrelevanceSubst [Γ] [Γ]′ [tailσ] [tailσ]′ σ®σ
      [σA] = proj₁ (unwrap [A] ⊢Δ [tailσ])
      t®v′ = irrelevanceQuant (⌜ m ⌝ · _)
               (proj₁ (unwrap [A] ⊢Δ [tailσ]))
               (proj₁ (unwrap [A]′ ⊢Δ [tailσ]′))
               t®v
  in  σ®σ′ , t®v′

-- Irrelevance of erasure validity

irrelevance : ∀ {l l′}
            → ([Γ] [Γ]′ : ⊩ᵛ Γ)
              ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
              ([A]′ : Γ ⊩ᵛ⟨ l′ ⟩ A / [Γ]′)
              (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] A / [Γ] / [A])
            → (γ ▸ Γ ⊩ʳ⟨ l′ ⟩ t ∷[ m ] A / [Γ]′ / [A]′)
irrelevance {m} [Γ] [Γ]′ [A] [A]′ ⊩ʳt [σ]′ σ®σ′ =
  let [σ] = IS.irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ]′
      σ®σ = irrelevanceSubst [Γ]′ [Γ] [σ]′ [σ] σ®σ′
      t®v = ⊩ʳt [σ] σ®σ
  in  irrelevanceQuant ⌜ m ⌝
        (proj₁ (unwrap [A] ⊢Δ [σ]))
        (proj₁ (unwrap [A]′ ⊢Δ [σ]′))
        t®v
