open import Definition.Typed.EqualityRelation
import Definition.Typed as T
import Definition.Untyped as U
open import Definition.Modality
open import Tools.Nullary
import Tools.PropositionalEquality as PE

module Erasure.LogicalRelation.Irrelevance
  {a k} {M : Set a} (𝕄 : Modality M)
  (open U M) (open T M) (open Modality 𝕄)
  {Δ : Con Term k} (⊢Δ : ⊢ Δ)
  (is-𝟘? : (p : M) → Dec (p PE.≡ 𝟘))
  {{eqrel : EqRelSet M}}
  where

open EqRelSet {{...}}

open import Erasure.LogicalRelation 𝕄 ⊢Δ is-𝟘?

open import Definition.LogicalRelation M
open import Definition.LogicalRelation.ShapeView M
import Definition.LogicalRelation.Irrelevance M as I
open import Definition.LogicalRelation.Substitution M
import Definition.LogicalRelation.Substitution.Irrelevance M as IS

import Definition.Untyped.BindingType M as BT

open import Definition.Typed.Weakening M hiding (wk)
open import Definition.Typed.Properties M

open import Definition.Modality.Context 𝕄
open import Definition.Mode 𝕄

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
  (Bᵥ (BΠ p q) BΠ! (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
     (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
     (BT.Π≋Π PE.refl PE.refl))
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
  (Bᵥ (BΣ _ p _) BΣ! (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
     (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
     (BT.Σ≋Σ PE.refl))
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
irrelevanceTermSV (emb 0<1 [A]) [A]′ t®v (emb⁰¹ SV) =
  irrelevanceTermSV [A] [A]′ t®v SV
irrelevanceTermSV [A] (emb 0<1 [A]′) t®v (emb¹⁰ SV) =
  irrelevanceTermSV [A] [A]′ t®v SV
-- Impossible cases
irrelevanceTermSV _ _ () (Emptyᵥ _ _)
irrelevanceTermSV _ _ () (ne _ _)
irrelevanceTermSV _ _ _ (Bᵥ BΣ! BΠ! _ _ ())
irrelevanceTermSV _ _ _ (Bᵥ BΠ! BΣ! _ _ ())

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

irrelevanceSubst : ∀ {σ σ′ l}
                 → ([Γ] [Γ]′ : ⊩ᵛ Γ)
                   ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
                   ([σ]′ : Δ ⊩ˢ σ ∷ Γ / [Γ]′ / ⊢Δ)
                   (σ®σ′ : σ ®⟨ l ⟩ σ′ ∷[ m ] Γ ◂ γ / [Γ] / [σ])
                 → (σ ®⟨ l ⟩ σ′ ∷[ m ] Γ ◂ γ / [Γ]′ / [σ]′)
irrelevanceSubst {Γ = ε} {γ = ε} ε ε (lift tt) (lift tt) (lift tt) = lift tt
irrelevanceSubst {Γ = Γ ∙ A} {m = m} {γ = γ ∙ p} {l = l}
                 ([Γ] ∙ [A]) ([Γ]′ ∙ [A]′) ([tailσ] , b) ([tailσ]′ , d) (σ®σ , t®v) =
  let σ®σ′ = irrelevanceSubst {l = l} [Γ] [Γ]′ [tailσ] [tailσ]′ σ®σ
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
irrelevance {m = m} {l = l} [Γ] [Γ]′ [A] [A]′ ⊩ʳt [σ]′ σ®σ′ =
  let [σ] = IS.irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ]′
      σ®σ = irrelevanceSubst {l = l} [Γ]′ [Γ] [σ]′ [σ] σ®σ′
      t®v = ⊩ʳt [σ] σ®σ
  in  irrelevanceQuant ⌜ m ⌝
        (proj₁ (unwrap [A] ⊢Δ [σ]))
        (proj₁ (unwrap [A]′ ⊢Δ [σ]′))
        t®v
