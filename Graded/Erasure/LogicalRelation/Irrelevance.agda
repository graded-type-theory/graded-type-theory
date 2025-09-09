------------------------------------------------------------------------
-- Irrelevance lemmata for the logical relation
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality

module Graded.Erasure.LogicalRelation.Irrelevance
  {a} {M : Set a}
  {𝕄 : Modality M}
  {R : Type-restrictions 𝕄}
  (as : Assumptions R)
  where

open Assumptions as
open Modality 𝕄
open Type-restrictions R

open import Graded.Erasure.LogicalRelation as

open import Definition.LogicalRelation.Simplified R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Type R
open import Definition.Typed.Weakening.Definition R

open import Definition.Untyped M
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation

private
  variable
    n : Nat
    A′ : Term n

private opaque

  -- Irrelevance of logical relation for erasure using a ShapeView

  irrelevanceTermSV : ∀ {t v A}
                    → {[A] : ts » Δ ⊨ A}
                      {[A]′ : ts » Δ ⊨ A}
                    → t ® v ∷ A / [A]
                    → ShapeView (ts » Δ) A A [A] [A]′
                    → t ® v ∷ A / [A]′
  irrelevanceTermSV t®v (Uᵥ UA UA′) = t®v
  irrelevanceTermSV t®v (ℕᵥ ℕA ℕA′) = t®v
  irrelevanceTermSV t®v (Emptyᵥ EmptyA EmptyA′) = t®v
  irrelevanceTermSV {A} t®v
    (Unitᵥ {s} (Unitᵣ l A⇒*Unit₁) (Unitᵣ l′ A⇒*Unit₂)) =
    case Unit-injectivity
           (Unit s l  ≡˘⟨ subset* A⇒*Unit₁ ⟩⊢
            A         ≡⟨ subset* A⇒*Unit₂ ⟩⊢∎
            Unit s l′ ∎) of λ {
      (_ , PE.refl) →
    t®v }
  irrelevanceTermSV t®v (ne neA neA′) = t®v
  irrelevanceTermSV
    t®v
    (Bᵥ BMΠ p q (Bᵣ F G D [F] [G])
      (Bᵣ F₁ G₁ D₁ [F]₁ [G]₁))
       with B-PE-injectivity BΠ! BΠ! (whrDet* (D , ΠΣₙ) (D₁ , ΠΣₙ))
  ... | PE.refl , PE.refl , _
         with is-𝟘? p
  ... | (yes p≡𝟘) = t®v .proj₁ , λ ⊢a →
    irrelevanceTermSV (t®v .proj₂ ⊢a)
      (goodCasesRefl ([G] ⊢a) ([G]₁ ⊢a))
  ... | (no p≢𝟘) = t®v .proj₁ , λ ⊢a a®w′ →
    let a®w = irrelevanceTermSV a®w′ (goodCasesRefl [F]₁ [F])
    in  irrelevanceTermSV (t®v .proj₂ ⊢a a®w)
          (goodCasesRefl ([G] ⊢a) ([G]₁ ⊢a))
  irrelevanceTermSV {v = v}
    (t₁ , t₂ , t⇒t′ , ⊢t₁ , v₂ , t₂®v₂ , extra)
    (Bᵥ (BMΣ _) p _ (Bᵣ F G D [F] [G])
       (Bᵣ F₁ G₁ D₁ [F]₁ [G]₁))
    with B-PE-injectivity BΣ! BΣ! (whrDet* (D , ΠΣₙ) (D₁ , ΠΣₙ))
  ... | PE.refl , PE.refl , _ =
    t₁ , t₂ , t⇒t′ , ⊢t₁ , v₂
       , irrelevanceTermSV t₂®v₂
           (goodCasesRefl ([G] ⊢t₁) ([G]₁ ⊢t₁))
       , Σ-®-elim (λ _ → Σ-® _ [F]₁ t₁ v v₂ p) extra Σ-®-intro-𝟘
           λ v₁ v⇒p t₁®v₁ p≢𝟘 →
             Σ-®-intro-ω v₁ v⇒p
               (irrelevanceTermSV t₁®v₁
                 (goodCasesRefl [F] [F]₁))
               p≢𝟘
  irrelevanceTermSV t®v (Idᵥ ⊨A@record{} ⊨B) =
    case whrDet* (_⊨Id_.⇒*Id ⊨A , Idₙ) (_⊨Id_.⇒*Id ⊨B , Idₙ) of λ {
      PE.refl →
    t®v }

opaque

  -- Irrelevance of logical relation for erasure

  irrelevanceTerm : ∀ {t v A}
                  → ([A] : ts » Δ ⊨ A)
                    ([A]′ : ts » Δ ⊨ A)
                  → t ® v ∷ A / [A]
                  → t ® v ∷ A / [A]′
  irrelevanceTerm [A] [A]′ t®v =
    irrelevanceTermSV t®v (goodCasesRefl [A] [A]′)

opaque

  -- Irrelevance of logical relation for erasure with propositionally equal types

  irrelevanceTerm′ : ∀ {t v A}
                   → A PE.≡ A′
                   → ([A] : ts » Δ ⊨ A)
                   → ([A]′ : ts » Δ ⊨ A′)
                   → t ® v ∷ A / [A]
                   → t ® v ∷ A′ / [A]′
  irrelevanceTerm′ PE.refl [A] [A]′ t®v = irrelevanceTerm [A] [A]′ t®v
