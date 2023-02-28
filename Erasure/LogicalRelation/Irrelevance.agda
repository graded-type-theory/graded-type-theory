{-# OPTIONS --without-K --safe #-}

open import Definition.Modality.Instances.Erasure
open import Definition.Typed.EqualityRelation
open import Definition.Typed Erasure′
open import Definition.Untyped Erasure

module Erasure.LogicalRelation.Irrelevance {k} {Δ : Con Term k} (⊢Δ : ⊢ Δ)
                                           (Prodrec : Erasure → Set)
                                           {{eqrel : EqRelSet Erasure′}} where
open EqRelSet {{...}}

open import Definition.Modality.Instances.Erasure.Modality Prodrec
open import Erasure.LogicalRelation ⊢Δ Prodrec

open import Definition.LogicalRelation Erasure′
open import Definition.LogicalRelation.ShapeView Erasure′
open import Definition.LogicalRelation.Substitution Erasure′
import Definition.LogicalRelation.Irrelevance Erasure′ as I
import Definition.LogicalRelation.Substitution.Irrelevance Erasure′ as IS

import Definition.Untyped.BindingType Erasure′ as BT
open import Definition.Typed.Weakening Erasure′
open import Definition.Typed.Properties Erasure′

open import Definition.Modality.Context ErasureModality

open import Tools.Level
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Unit

private
  variable
    n : Nat
    Γ : Con Term n
    A A′ t : Term n
    γ : Conₘ n
    p : Erasure

-- Irrelevance of logical relation for erasure using a ShapreView

irrelevanceTermSV : ∀ {l l′ t v A}
                  → ([A] : Δ ⊩⟨ l ⟩ A)
                    ([A]′ : Δ ⊩⟨ l′ ⟩ A)
                  → t ®⟨ l ⟩ v ∷ A / [A]
                  → ShapeView Δ l l′ A A [A] [A]′
                  → t ®⟨ l′ ⟩ v ∷ A / [A]′
irrelevanceTermSV .(Uᵣ UA) .(Uᵣ UB) t®v (Uᵥ UA UB) = t®v
irrelevanceTermSV .(ℕᵣ ℕA) .(ℕᵣ ℕB) t®v (ℕᵥ ℕA ℕB) = t®v
irrelevanceTermSV .(Unitᵣ UnitA) .(Unitᵣ UnitB) t®v (Unitᵥ UnitA UnitB) = t®v
irrelevanceTermSV [A] [A]′ t®v (Bᵥ (BΠ 𝟘 q) BΠ! (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                               (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) (BT.Π≋Π PE.refl PE.refl)) [a]′
                               with whrDet* (red D , Πₙ) (red D₁ , Πₙ)
... | Π≡Π′ with B-PE-injectivity (BΠ 𝟘 q) (BΠ 𝟘 q) Π≡Π′
... | PE.refl , PE.refl , _ =
  let [a] = I.irrelevanceTerm ([F]₁ id ⊢Δ) ([F] id ⊢Δ) [a]′
      t®v′ = t®v [a]
      SV′ = goodCasesRefl ([G] id ⊢Δ [a]) ([G]₁ id ⊢Δ [a]′)
  in  irrelevanceTermSV ([G] id ⊢Δ [a]) ([G]₁ id ⊢Δ [a]′) t®v′ SV′
irrelevanceTermSV [A] [A]′ t®v (Bᵥ (BΠ ω q) BΠ! (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                               (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) (BT.Π≋Π PE.refl PE.refl)) [a]′ a®w′
                               with whrDet* (red D , Πₙ) (red D₁ , Πₙ)
... | Π≡Π′ with B-PE-injectivity (BΠ ω q) (BΠ ω q) Π≡Π′
... | PE.refl , PE.refl , _ =
  let [a] = I.irrelevanceTerm ([F]₁ id ⊢Δ) ([F] id ⊢Δ) [a]′
      SV = goodCasesRefl ([F]₁ id ⊢Δ) ([F] id ⊢Δ)
      a®w = irrelevanceTermSV ([F]₁ id ⊢Δ) ([F] id ⊢Δ) a®w′ SV
      t®v′ = t®v [a] a®w
      SV′ = goodCasesRefl ([G] id ⊢Δ [a]) ([G]₁ id ⊢Δ [a]′)
      in  irrelevanceTermSV ([G] id ⊢Δ [a]) ([G]₁ id ⊢Δ [a]′) t®v′ SV′
irrelevanceTermSV [A] [A]′ (t₁ , t₂ , v₁ , v₂ , t⇒t′ , v⇒v′ , [t₁] , t₁®v₁ , t₂®v₂)
                  (Bᵥ (BΣ q m) BΣ! (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                      (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) (BT.Σ≋Σ PE.refl))
                  with whrDet* (red D , Σₙ) (red D₁ , Σₙ)
... | Σ≡Σ′ with B-PE-injectivity (BΣ q m) (BΣ q m) Σ≡Σ′
... | PE.refl , PE.refl , _ =
  let [F]′ = [F] id ⊢Δ
      [F]₁′ = [F]₁ id ⊢Δ
      [t₁]′ = I.irrelevanceTerm [F]′ [F]₁′ [t₁]
      [Gt₁] = [G] id ⊢Δ [t₁]
      [Gt₁]₁ = [G]₁ id ⊢Δ [t₁]′
      t₁®v₁′ = irrelevanceTermSV [F]′ [F]₁′ t₁®v₁ (goodCasesRefl [F]′ [F]₁′)
      t₂®v₂′ = irrelevanceTermSV [Gt₁] [Gt₁]₁ t₂®v₂ (goodCasesRefl [Gt₁] [Gt₁]₁)
  in  t₁ , t₂ , v₁ , v₂ , t⇒t′ , v⇒v′ , [t₁]′ , t₁®v₁′ , t₂®v₂′
irrelevanceTermSV (emb 0<1 [A]) [A]′ t®v (emb⁰¹ SV) = irrelevanceTermSV [A] [A]′ t®v SV
irrelevanceTermSV [A] (emb 0<1 [A]′) t®v (emb¹⁰ SV) = irrelevanceTermSV [A] [A]′ t®v SV
-- Impossible cases
irrelevanceTermSV .(Emptyᵣ EmptyA) .(Emptyᵣ EmptyB) () (Emptyᵥ EmptyA EmptyB)
irrelevanceTermSV .(ne neA) .(ne neB) () (ne neA neB)
irrelevanceTermSV _ _ t®v (Bᵥ BΣ! BΠ! BA BB ())
irrelevanceTermSV _ _ t®v (Bᵥ BΠ! BΣ! BA BB ())

-- Irrelevance of logical relation for erasure

irrelevanceTerm : ∀ {l l′ t v A}
                → ([A] : Δ ⊩⟨ l ⟩ A)
                  ([A]′ : Δ ⊩⟨ l′ ⟩ A)
                → t ®⟨ l ⟩ v ∷ A / [A]
                → t ®⟨ l′ ⟩ v ∷ A / [A]′
irrelevanceTerm [A] [A]′ t®v = irrelevanceTermSV [A] [A]′ t®v (goodCasesRefl [A] [A]′)

-- Irrelevance of logical relation for erasure with propositionally equal types

irrelevanceTerm′ : ∀ {l l′ t v A}
                 → A PE.≡ A′
                 → ([A] : Δ ⊩⟨ l ⟩ A)
                 → ([A]′ : Δ ⊩⟨ l′ ⟩ A′)
                 → t ®⟨ l ⟩ v ∷ A / [A]
                 → t ®⟨ l′ ⟩ v ∷ A′ / [A]′
irrelevanceTerm′ PE.refl [A] [A]′ t®v = irrelevanceTerm [A] [A]′ t®v

-- Irrelevance of quantified logical relation for erasure

irrelevanceQuant : ∀ {l l′ t v A}
                 → ([A] : Δ ⊩⟨ l ⟩ A)
                 → ([A]′ : Δ ⊩⟨ l′ ⟩ A)
                 → t ®⟨ l ⟩ v ∷ A ◂ p / [A]
                 → t ®⟨ l′ ⟩ v ∷ A ◂ p / [A]′
irrelevanceQuant {𝟘} [A] [A]′ t®v = tt
irrelevanceQuant {ω} [A] [A]′ t®v = irrelevanceTerm [A] [A]′ t®v

-- Irrelevance of related substitutions

irrelevanceSubst : ∀ {σ σ′ l}
                 → ([Γ] [Γ]′ : ⊩ᵛ Γ)
                   ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
                   ([σ]′ : Δ ⊩ˢ σ ∷ Γ / [Γ]′ / ⊢Δ)
                   (σ®σ′ : σ ®⟨ l ⟩ σ′ ∷ Γ ◂ γ / [Γ] / [σ])
                 → (σ ®⟨ l ⟩ σ′ ∷ Γ ◂ γ / [Γ]′ / [σ]′)
irrelevanceSubst {Γ = ε} {γ = ε} ε ε (lift tt) (lift tt) tt = tt
irrelevanceSubst {Γ = Γ ∙ A} {γ = γ ∙ p} {l = l}
                 ([Γ] ∙ [A]) ([Γ]′ ∙ [A]′) ([tailσ] , b) ([tailσ]′ , d) (σ®σ , t®v) =
  let σ®σ′ = irrelevanceSubst {l = l} [Γ] [Γ]′ [tailσ] [tailσ]′ σ®σ
      [σA] = proj₁ (unwrap [A] ⊢Δ [tailσ])
      t®v′ = irrelevanceQuant {p = p} (proj₁ (unwrap [A] ⊢Δ [tailσ]))
                              (proj₁ (unwrap [A]′ ⊢Δ [tailσ]′)) t®v
  in  σ®σ′ , t®v′

-- Irrelevance of erasure validity

irrelevance : ∀ {l l′}
            → ([Γ] [Γ]′ : ⊩ᵛ Γ)
              ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
              ([A]′ : Γ ⊩ᵛ⟨ l′ ⟩ A / [Γ]′)
              (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷ A / [Γ] / [A])
            → (γ ▸ Γ ⊩ʳ⟨ l′ ⟩ t ∷ A / [Γ]′ / [A]′)
irrelevance {l = l} [Γ] [Γ]′ [A] [A]′ ⊩ʳt [σ]′ σ®σ′ =
  let [σ] = IS.irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ]′
      σ®σ = irrelevanceSubst {l = l} [Γ]′ [Γ] [σ]′ [σ] σ®σ′
      t®v = ⊩ʳt [σ] σ®σ
  in  irrelevanceTerm (proj₁ (unwrap [A] ⊢Δ [σ])) (proj₁ (unwrap [A]′ ⊢Δ [σ]′)) t®v
