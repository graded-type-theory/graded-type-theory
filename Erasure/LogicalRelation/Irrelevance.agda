{-# OPTIONS --without-K --safe #-}
open import Definition.Modality.Erasure

open import Definition.Typed.EqualityRelation


module Erasure.LogicalRelation.Irrelevance {{eqrel : EqRelSet Erasure′}} where
open EqRelSet {{...}}

open import Erasure.LogicalRelation

open import Definition.LogicalRelation Erasure′
open import Definition.LogicalRelation.ShapeView Erasure′
import Definition.LogicalRelation.Irrelevance Erasure′ as I
open import Definition.LogicalRelation.Substitution Erasure′
import Definition.LogicalRelation.Substitution.Irrelevance Erasure′ as IS

open import Definition.Untyped Erasure
open import Definition.Untyped.Properties Erasure
import Definition.Untyped.BindingType Erasure′ as BT

open import Definition.Typed Erasure′
open import Definition.Typed.Weakening Erasure′
open import Definition.Typed.Properties Erasure′

open import Definition.Modality.Context ErasureModality

open import Tools.Empty
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
                  → ([A] : ε ⊩⟨ l ⟩ A)
                    ([A]′ : ε ⊩⟨ l′ ⟩ A)
                  → t ®⟨ l ⟩ v ∷ A / [A]
                  → ShapeView ε l l′ A A [A] [A]′
                  → t ®⟨ l′ ⟩ v ∷ A / [A]′
irrelevanceTermSV .(Uᵣ UA) .(Uᵣ UB) t®v (Uᵥ UA UB) = t®v
irrelevanceTermSV .(ℕᵣ ℕA) .(ℕᵣ ℕB) t®v (ℕᵥ ℕA ℕB) = t®v
irrelevanceTermSV .(Unitᵣ UnitA) .(Unitᵣ UnitB) t®v (Unitᵥ UnitA UnitB) = t®v
irrelevanceTermSV [A] [A]′ t®v (ne (ne K D neK K≡K) neB) = ⊥-elim (noClosedNe neK)
irrelevanceTermSV [A] [A]′ t®v (Bᵥ (BΠ 𝟘 q) BΠ! (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                               (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) (BT.Π≋Π PE.refl PE.refl)) [a]′
                               with whrDet* (red D , Πₙ) (red D₁ , Πₙ)
... | Π≡Π′ with B-PE-injectivity (BΠ 𝟘 q) (BΠ 𝟘 q) Π≡Π′
... | PE.refl , PE.refl , _ =
  let [a] = I.irrelevanceTerm ([F]₁ id ε) ([F] id ε) [a]′
      t®v′ = t®v [a]
      SV′ = goodCasesRefl ([G] id ε [a]) ([G]₁ id ε [a]′)
  in  irrelevanceTermSV ([G] id ε [a]) ([G]₁ id ε [a]′) t®v′ SV′
irrelevanceTermSV [A] [A]′ t®v (Bᵥ (BΠ ω q) BΠ! (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                               (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) (BT.Π≋Π PE.refl PE.refl)) [a]′ a®w′
                               with whrDet* (red D , Πₙ) (red D₁ , Πₙ)
... | Π≡Π′ with B-PE-injectivity (BΠ ω q) (BΠ ω q) Π≡Π′
... | PE.refl , PE.refl , _ =
  let [a] = I.irrelevanceTerm ([F]₁ id ε) ([F] id ε) [a]′
      SV = goodCasesRefl ([F]₁ id ε) ([F] id ε)
      a®w = irrelevanceTermSV ([F]₁ id ε) ([F] id ε) a®w′ SV
      t®v′ = t®v [a] a®w
      SV′ = goodCasesRefl ([G] id ε [a]) ([G]₁ id ε [a]′)
      in  irrelevanceTermSV ([G] id ε [a]) ([G]₁ id ε [a]′) t®v′ SV′
irrelevanceTermSV [A] [A]′ t®v (Bᵥ (BΣ q) BΣ! (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                  (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) (BT.Σ≋Σ PE.refl)) [t₁]′
                           with whrDet* (red D , Σₙ) (red D₁ , Σₙ)
... | Σ≡Σ′ with B-PE-injectivity (BΣ q) (BΣ q) Σ≡Σ′
... | PE.refl , PE.refl , _ =
    let [t₁] = I.irrelevanceTerm ([F]₁ id ε) ([F] id ε) [t₁]′
        t₁®v₁ , t₂®v₂ = t®v [t₁]
        SV  = goodCasesRefl ([F] id ε) ([F]₁ id ε)
        SV′ = goodCasesRefl ([G] id ε [t₁]) ([G]₁ id ε [t₁]′)
        t₁®v₁′ = irrelevanceTermSV ([F] id ε) ([F]₁ id ε) t₁®v₁ SV
        t₂®v₂′ = irrelevanceTermSV ([G] id ε [t₁]) ([G]₁ id ε [t₁]′) t₂®v₂ SV′
    in  t₁®v₁′  , t₂®v₂′
irrelevanceTermSV (emb 0<1 [A]) [A]′ t®v (emb⁰¹ SV) = irrelevanceTermSV [A] [A]′ t®v SV
irrelevanceTermSV [A] (emb 0<1 [A]′) t®v (emb¹⁰ SV) = irrelevanceTermSV [A] [A]′ t®v SV

-- Irrelevance of logical relation for erasure

irrelevanceTerm : ∀ {l l′ t v A}
                → ([A] : ε ⊩⟨ l ⟩ A)
                  ([A]′ : ε ⊩⟨ l′ ⟩ A)
                → t ®⟨ l ⟩ v ∷ A / [A]
                → t ®⟨ l′ ⟩ v ∷ A / [A]′
irrelevanceTerm [A] [A]′ t®v = irrelevanceTermSV [A] [A]′ t®v (goodCasesRefl [A] [A]′)

-- Irrelevance of logical relation for erasure with propositionally equal types

irrelevanceTerm′ : ∀ {l l′ t v A}
                 → A PE.≡ A′
                 → ([A] : ε ⊩⟨ l ⟩ A)
                 → ([A]′ : ε ⊩⟨ l′ ⟩ A′)
                 → t ®⟨ l ⟩ v ∷ A / [A]
                 → t ®⟨ l′ ⟩ v ∷ A′ / [A]′
irrelevanceTerm′ PE.refl [A] [A]′ t®v = irrelevanceTerm [A] [A]′ t®v

-- Irrelevance of quantified logical relation for erasure

irrelevanceQuant : ∀ {l l′ t v A}
                 → ([A] : ε ⊩⟨ l ⟩ A)
                 → ([A]′ : ε ⊩⟨ l′ ⟩ A)
                 → t ®⟨ l ⟩ v ∷ A ◂ p / [A]
                 → t ®⟨ l′ ⟩ v ∷ A ◂ p / [A]′
irrelevanceQuant {𝟘} [A] [A]′ t®v = tt
irrelevanceQuant {ω} [A] [A]′ t®v = irrelevanceTerm [A] [A]′ t®v

-- Irrelevance of related substitutions

irrelevanceSubst : ∀ {σ σ′ l}
                 → ([Γ] [Γ]′ : ⊩ᵛ Γ)
                   ([σ] : ε ⊩ˢ σ ∷ Γ / [Γ] / ε)
                   ([σ]′ : ε ⊩ˢ σ ∷ Γ / [Γ]′ / ε)
                   (σ®σ′ : σ ®⟨ l ⟩ σ′ ∷ Γ ◂ γ / [Γ] / [σ])
                 → (σ ®⟨ l ⟩ σ′ ∷ Γ ◂ γ / [Γ]′ / [σ]′)
irrelevanceSubst {Γ = ε} {γ = ε} ε ε (lift tt) (lift tt) tt = tt
irrelevanceSubst {Γ = Γ ∙ A} {γ = γ ∙ p} {l = l}
                 ([Γ] ∙ [A]) ([Γ]′ ∙ [A]′) ([tailσ] , b) ([tailσ]′ , d) (σ®σ , t®v) =
  let σ®σ′ = irrelevanceSubst {l = l} [Γ] [Γ]′ [tailσ] [tailσ]′ σ®σ
      [σA] = proj₁ ([A] ε [tailσ])
      t®v′ = irrelevanceQuant {p = p} (proj₁ ([A] ε [tailσ])) (proj₁ ([A]′ ε [tailσ]′)) t®v
  in  σ®σ′ , t®v′

-- Irrelevance of erasure validity

irrelevance : ∀ {l l′} → ([Γ] [Γ]′ : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ]) ([A]′ : Γ ⊩ᵛ⟨ l′ ⟩ A / [Γ]′)
              (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷ A / [Γ] / [A]) → (γ ▸ Γ ⊩ʳ⟨ l′ ⟩ t ∷ A / [Γ]′ / [A]′)
irrelevance {l = l} [Γ] [Γ]′ [A] [A]′ ⊩ʳt [σ]′ σ®σ′ =
  let [σ] = IS.irrelevanceSubst [Γ]′ [Γ] ε ε [σ]′
      σ®σ = irrelevanceSubst {l = l} [Γ]′ [Γ] [σ]′ [σ] σ®σ′
      t®v = ⊩ʳt [σ] σ®σ
  in  irrelevanceTerm (proj₁ ([A] ε [σ])) (proj₁ ([A]′ ε [σ]′)) t®v
