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

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.ShapeView R
import Definition.LogicalRelation.Irrelevance R as I

open import Definition.Typed R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Weakening R hiding (wk)
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Type R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Unit

private
  variable
    n : Nat
    A′ : Term n

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
  {l} {l′} {A}
  _ _ t®v (Unitᵥ {s} (Unitₜ A⇒*Unit₁ _) (Unitₜ A⇒*Unit₂ _)) =
  case Unit-injectivity
         (Unit s l  ≡˘⟨ subset* A⇒*Unit₁ ⟩⊢
          A         ≡⟨ subset* A⇒*Unit₂ ⟩⊢∎
          Unit s l′ ∎) of λ {
    (_ , PE.refl) →
  t®v }
irrelevanceTermSV
  [A] [A]′ t®v
  (Bᵥ (BΠ p q) (Bᵣ F G D A≡A [F] [G] G-ext _)
     (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
       with B-PE-injectivity BΠ! BΠ! (whrDet* (D , ΠΣₙ) (D₁ , ΠΣₙ))
... | PE.refl , PE.refl , _
       with is-𝟘? p
... | (yes p≡𝟘) = t®v .proj₁ , λ [a]′ →
  let [a] = I.irrelevanceTerm ([F]₁ (idʷ ⊢Δ)) ([F] (idʷ ⊢Δ)) [a]′
      t®v′ = t®v .proj₂ [a]
      SV′ = goodCasesRefl ([G] (idʷ ⊢Δ) [a]) ([G]₁ (idʷ ⊢Δ) [a]′)
  in  irrelevanceTermSV ([G] (idʷ ⊢Δ) [a]) ([G]₁ (idʷ ⊢Δ) [a]′) t®v′ SV′
... | (no p≢𝟘) = t®v .proj₁ , λ [a]′ a®w′ →
  let [a] = I.irrelevanceTerm ([F]₁ (idʷ ⊢Δ)) ([F] (idʷ ⊢Δ)) [a]′
      SV = goodCasesRefl ([F]₁ (idʷ ⊢Δ)) ([F] (idʷ ⊢Δ))
      a®w = irrelevanceTermSV ([F]₁ (idʷ ⊢Δ)) ([F] (idʷ ⊢Δ)) a®w′ SV
      t®v′ = t®v .proj₂ [a] a®w
      SV′ = goodCasesRefl ([G] (idʷ ⊢Δ) [a]) ([G]₁ (idʷ ⊢Δ) [a]′)
  in  irrelevanceTermSV ([G] (idʷ ⊢Δ) [a]) ([G]₁ (idʷ ⊢Δ) [a]′) t®v′ SV′
irrelevanceTermSV {v = v}
  [A] [A]′ (t₁ , t₂ , t⇒t′ , [t₁] , v₂ , t₂®v₂ , extra)
  (Bᵥ (BΣ _ p _) (Bᵣ F G D A≡A [F] [G] G-ext _)
     (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
  with B-PE-injectivity BΣ! BΣ! (whrDet* (D , ΠΣₙ) (D₁ , ΠΣₙ))
... | PE.refl , PE.refl , _ =
  let [F]′ = [F] (idʷ ⊢Δ)
      [F]₁′ = [F]₁ (idʷ ⊢Δ)
      [t₁]′ = I.irrelevanceTerm [F]′ [F]₁′ [t₁]
      [Gt₁] = [G] (idʷ ⊢Δ) [t₁]
      [Gt₁]₁ = [G]₁ (idʷ ⊢Δ) [t₁]′
      t₂®v₂′ = irrelevanceTermSV [Gt₁] [Gt₁]₁ t₂®v₂
                 (goodCasesRefl [Gt₁] [Gt₁]₁)
  in  t₁ , t₂ , t⇒t′ , [t₁]′ , v₂ , t₂®v₂′
      , Σ-®-elim (λ _ → Σ-® _ _ [F]₁′ t₁ v v₂ p) extra
                 Σ-®-intro-𝟘
                 λ v₁ v⇒p t₁®v₁ p≢𝟘 →
                   Σ-®-intro-ω v₁ v⇒p (irrelevanceTermSV [F]′ [F]₁′ t₁®v₁
                               (goodCasesRefl [F]′ [F]₁′)) p≢𝟘
irrelevanceTermSV _ _ t®v (Idᵥ ⊩A@record{} ⊩B) =
  case whrDet* (_⊩ₗId_.⇒*Id ⊩A , Idₙ) (_⊩ₗId_.⇒*Id ⊩B , Idₙ) of λ {
    PE.refl →
  t®v }
irrelevanceTermSV _ _ t®v (embᵥ₁ ≤ᵘ-refl A≡B) =
  irrelevanceTermSV _ _ t®v A≡B
irrelevanceTermSV _ _ t®v (embᵥ₁ (≤ᵘ-step p) A≡B) =
  irrelevanceTermSV _ _ t®v (embᵥ₁ p A≡B)
irrelevanceTermSV _ _ t®v (embᵥ₂ ≤ᵘ-refl A≡B) =
  irrelevanceTermSV _ _ t®v A≡B
irrelevanceTermSV _ _ t®v (embᵥ₂ (≤ᵘ-step p) A≡B) =
  irrelevanceTermSV _ _ t®v (embᵥ₂ p A≡B)
-- Impossible cases
irrelevanceTermSV _ _ () (Emptyᵥ _ _)
irrelevanceTermSV _ _ () (ne record{} _)

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
