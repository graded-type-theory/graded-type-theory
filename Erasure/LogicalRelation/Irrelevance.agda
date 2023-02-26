open import Definition.Modality.Instances.Erasure
open import Definition.Modality.Restrictions
open import Definition.Typed.EqualityRelation

module Erasure.LogicalRelation.Irrelevance
  (restrictions : Restrictions Erasure)
  {{eqrel : EqRelSet Erasure}}
  where

open EqRelSet {{...}}

open import Definition.Modality.Instances.Erasure.Modality restrictions
open import Erasure.LogicalRelation restrictions

open import Definition.LogicalRelation Erasure
open import Definition.LogicalRelation.ShapeView Erasure
import Definition.LogicalRelation.Irrelevance Erasure as I
open import Definition.LogicalRelation.Substitution Erasure
import Definition.LogicalRelation.Substitution.Irrelevance Erasure as IS

open import Definition.Untyped Erasure
import Definition.Untyped.BindingType Erasure as BT

open import Definition.Typed Erasure
open import Definition.Typed.Weakening Erasure
open import Definition.Typed.Properties Erasure

open import Definition.Modality.Context ErasureModality
open import Definition.Mode ErasureModality

open import Tools.Function
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
    m : Mode

-- Irrelevance of logical relation for erasure using a ShapreView

irrelevanceTermSV : ∀ {l l′ t v A} p
                  → ([A] : ε ⊩⟨ l ⟩ A)
                    ([A]′ : ε ⊩⟨ l′ ⟩ A)
                  → t ®⟨ l ⟩ v ∷ A ◂ p / [A]
                  → ShapeView ε l l′ A A [A] [A]′
                  → t ®⟨ l′ ⟩ v ∷ A ◂ p / [A]′
irrelevanceTermSV 𝟘 = _
irrelevanceTermSV ω .(Uᵣ UA) .(Uᵣ UB) t®v (Uᵥ UA UB) = t®v
irrelevanceTermSV ω .(ℕᵣ ℕA) .(ℕᵣ ℕB) t®v (ℕᵥ ℕA ℕB) = t®v
irrelevanceTermSV
  ω .(Unitᵣ UnitA) .(Unitᵣ UnitB) t®v (Unitᵥ UnitA UnitB) =
  t®v
irrelevanceTermSV
  ω [A] [A]′ t®v
  (Bᵥ (BΠ 𝟘 q) BΠ! (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
     (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
     (BT.Π≋Π PE.refl PE.refl))
  [a]′
  with whrDet* (red D , ΠΣₙ) (red D₁ , ΠΣₙ)
... | Π≡Π′ with B-PE-injectivity (BΠ 𝟘 q) (BΠ 𝟘 q) Π≡Π′
... | PE.refl , PE.refl , _ =
  let [a] = I.irrelevanceTerm ([F]₁ id ε) ([F] id ε) [a]′
      t®v′ = t®v [a]
      SV′ = goodCasesRefl ([G] id ε [a]) ([G]₁ id ε [a]′)
  in  irrelevanceTermSV _ ([G] id ε [a]) ([G]₁ id ε [a]′) t®v′ SV′
irrelevanceTermSV
  ω [A] [A]′ t®v
  (Bᵥ (BΠ ω q) BΠ! (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
     (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
     (BT.Π≋Π PE.refl PE.refl))
  [a]′ a®w′
  with whrDet* (red D , ΠΣₙ) (red D₁ , ΠΣₙ)
... | Π≡Π′ with B-PE-injectivity (BΠ ω q) (BΠ ω q) Π≡Π′
... | PE.refl , PE.refl , _ =
  let [a] = I.irrelevanceTerm ([F]₁ id ε) ([F] id ε) [a]′
      SV = goodCasesRefl ([F]₁ id ε) ([F] id ε)
      a®w = irrelevanceTermSV _ ([F]₁ id ε) ([F] id ε) a®w′ SV
      t®v′ = t®v [a] a®w
      SV′ = goodCasesRefl ([G] id ε [a]) ([G]₁ id ε [a]′)
      in  irrelevanceTermSV _ ([G] id ε [a]) ([G]₁ id ε [a]′) t®v′ SV′
irrelevanceTermSV
  ω [A] [A]′ (t₁ , t₂ , t⇒t′ , [t₁] , v₂ , t₂®v₂ , extra)
  (Bᵥ (BΣ _ p _) BΣ! (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
     (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
     (BT.Σ≋Σ PE.refl))
  with whrDet* (red D , ΠΣₙ) (red D₁ , ΠΣₙ)
... | Σ≡Σ′ with B-PE-injectivity BΣ! BΣ! Σ≡Σ′
... | PE.refl , PE.refl , _ =
  let [F]′ = [F] id ε
      [F]₁′ = [F]₁ id ε
      [t₁]′ = I.irrelevanceTerm [F]′ [F]₁′ [t₁]
      [Gt₁] = [G] id ε [t₁]
      [Gt₁]₁ = [G]₁ id ε [t₁]′
      t₂®v₂′ = irrelevanceTermSV _ [Gt₁] [Gt₁]₁ t₂®v₂
                 (goodCasesRefl [Gt₁] [Gt₁]₁)
  in  t₁ , t₂ , t⇒t′ , [t₁]′ , v₂ , t₂®v₂′ ,
      (case Σ-®-view extra of λ where
         (𝟘 v⇒v′)          → v⇒v′
         (ω v₁ v⇒v′ t₁®v₁) →
           let t₁®v₁′ = irrelevanceTermSV p [F]′ [F]₁′ t₁®v₁
                          (goodCasesRefl [F]′ [F]₁′)
           in v₁ , v⇒v′ , t₁®v₁′)
irrelevanceTermSV ω (emb 0<1 [A]) [A]′ t®v (emb⁰¹ SV) =
  irrelevanceTermSV _ [A] [A]′ t®v SV
irrelevanceTermSV ω [A] (emb 0<1 [A]′) t®v (emb¹⁰ SV) =
  irrelevanceTermSV _ [A] [A]′ t®v SV
-- Impossible cases
irrelevanceTermSV ω _ _ () (Emptyᵥ _ _)
irrelevanceTermSV ω _ _ () (ne _ _)
irrelevanceTermSV ω _ _ _ (Bᵥ BΣ! BΠ! _ _ ())
irrelevanceTermSV ω _ _ _ (Bᵥ BΠ! BΣ! _ _ ())

-- Irrelevance of quantified logical relation for erasure

irrelevanceQuant : ∀ {l l′ t v A} p
                 → ([A] : ε ⊩⟨ l ⟩ A)
                 → ([A]′ : ε ⊩⟨ l′ ⟩ A)
                 → t ®⟨ l ⟩ v ∷ A ◂ p / [A]
                 → t ®⟨ l′ ⟩ v ∷ A ◂ p / [A]′
irrelevanceQuant p [A] [A]′ t®v =
  irrelevanceTermSV p [A] [A]′ t®v (goodCasesRefl [A] [A]′)

-- Irrelevance of logical relation for erasure

irrelevanceTerm : ∀ {l l′ t v A}
                → ([A] : ε ⊩⟨ l ⟩ A)
                  ([A]′ : ε ⊩⟨ l′ ⟩ A)
                → t ®⟨ l ⟩ v ∷ A / [A]
                → t ®⟨ l′ ⟩ v ∷ A / [A]′
irrelevanceTerm = irrelevanceQuant ω

-- Irrelevance of logical relation for erasure with propositionally equal types

irrelevanceTerm′ : ∀ {l l′ t v A}
                 → A PE.≡ A′
                 → ([A] : ε ⊩⟨ l ⟩ A)
                 → ([A]′ : ε ⊩⟨ l′ ⟩ A′)
                 → t ®⟨ l ⟩ v ∷ A / [A]
                 → t ®⟨ l′ ⟩ v ∷ A′ / [A]′
irrelevanceTerm′ PE.refl [A] [A]′ t®v = irrelevanceTerm [A] [A]′ t®v

-- Irrelevance of related substitutions

irrelevanceSubst : ∀ {σ σ′ l}
                 → ([Γ] [Γ]′ : ⊩ᵛ Γ)
                   ([σ] : ε ⊩ˢ σ ∷ Γ / [Γ] / ε)
                   ([σ]′ : ε ⊩ˢ σ ∷ Γ / [Γ]′ / ε)
                   (σ®σ′ : σ ®⟨ l ⟩ σ′ ∷[ m ] Γ ◂ γ / [Γ] / [σ])
                 → (σ ®⟨ l ⟩ σ′ ∷[ m ] Γ ◂ γ / [Γ]′ / [σ]′)
irrelevanceSubst {Γ = ε} {γ = ε} ε ε (lift tt) (lift tt) tt = tt
irrelevanceSubst {Γ = Γ ∙ A} {m = m} {γ = γ ∙ p} {l = l}
                 ([Γ] ∙ [A]) ([Γ]′ ∙ [A]′) ([tailσ] , b) ([tailσ]′ , d) (σ®σ , t®v) =
  let σ®σ′ = irrelevanceSubst {l = l} [Γ] [Γ]′ [tailσ] [tailσ]′ σ®σ
      [σA] = proj₁ (unwrap [A] ε [tailσ])
      t®v′ = irrelevanceQuant (⌜ m ⌝ · _)
               (proj₁ (unwrap [A] ε [tailσ]))
               (proj₁ (unwrap [A]′ ε [tailσ]′))
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
  let [σ] = IS.irrelevanceSubst [Γ]′ [Γ] ε ε [σ]′
      σ®σ = irrelevanceSubst {l = l} [Γ]′ [Γ] [σ]′ [σ] σ®σ′
      t®v = ⊩ʳt [σ] σ®σ
  in  irrelevanceQuant ⌜ m ⌝
        (proj₁ (unwrap [A] ε [σ]))
        (proj₁ (unwrap [A]′ ε [σ]′))
        t®v
