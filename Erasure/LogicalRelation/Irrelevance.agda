{-# OPTIONS --without-K --allow-unsolved-metas  #-}
open import Definition.Modality.Erasure

open import Definition.Typed.EqualityRelation


module Erasure.LogicalRelation.Irrelevance {{eqrel : EqRelSet Erasure}} where
open EqRelSet {{...}}

open import Erasure.LogicalRelation

open import Definition.LogicalRelation Erasure
open import Definition.LogicalRelation.ShapeView Erasure
import Definition.LogicalRelation.Irrelevance Erasure as I
open import Definition.LogicalRelation.Properties.MaybeEmb Erasure
open import Definition.LogicalRelation.Properties.Escape Erasure
open import Definition.LogicalRelation.Properties.Conversion Erasure
open import Definition.LogicalRelation.Substitution Erasure
import Definition.LogicalRelation.Substitution.Irrelevance Erasure as IS

open import Definition.Untyped Erasure
open import Definition.Untyped.Properties Erasure
open import Definition.Typed Erasure
open import Definition.Typed.Consequences.Injectivity Erasure
open import Definition.Typed.Reduction Erasure
open import Definition.Typed.Weakening Erasure
open import Definition.Typed.Properties Erasure
open import Definition.Modality.Context ErasureModality

open import Tools.Empty
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

irrelevanceTermSV : ∀ {l l′ t v A} → ([A] : ε ⊩⟨ l ⟩ A) ([A]′ : ε ⊩⟨ l′ ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A]
                 → ShapeView ε l l′ A A [A] [A]′ → t ®⟨ l′ ⟩ v ∷ A / [A]′
irrelevanceTermSV .(Uᵣ UA) .(Uᵣ UB) t®v (Uᵥ UA UB) = t®v
irrelevanceTermSV .(ℕᵣ ℕA) .(ℕᵣ ℕB) t®v (ℕᵥ ℕA ℕB) = t®v
irrelevanceTermSV .(Unitᵣ UnitA) .(Unitᵣ UnitB) t®v (Unitᵥ UnitA UnitB) = t®v
irrelevanceTermSV [A] [A]′ t®v (ne (ne K D neK K≡K) neB) = ⊥-elim (noClosedNe neK)
irrelevanceTermSV [A] [A]′ t®v (Bᵥ (BΠ 𝟘 q) (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                               (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)) [a]′
                               with whrDet* (red D , Πₙ) (red D₁ , Πₙ)
... | Π≡Π′ with B-PE-injectivity (BΠ 𝟘 q) (BΠ 𝟘 q) Π≡Π′
... | PE.refl , PE.refl , _ =
  let [a] = I.irrelevanceTerm ([F]₁ id ε) ([F] id ε) [a]′
      t®v′ = t®v [a]
      SV′ = goodCasesRefl ([G] id ε [a]) ([G]₁ id ε [a]′)
  in  irrelevanceTermSV ([G] id ε [a]) ([G]₁ id ε [a]′) t®v′ SV′
irrelevanceTermSV [A] [A]′ t®v (Bᵥ (BΠ ω q) (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                               (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)) [a]′ a®w′
                               with whrDet* (red D , Πₙ) (red D₁ , Πₙ)
... | Π≡Π′ with B-PE-injectivity (BΠ ω q) (BΠ ω q) Π≡Π′
... | PE.refl , PE.refl , _ =
  let [a] = I.irrelevanceTerm ([F]₁ id ε) ([F] id ε) [a]′
      SV = goodCasesRefl ([F]₁ id ε) ([F] id ε)
      a®w = irrelevanceTermSV ([F]₁ id ε) ([F] id ε) a®w′ SV
      t®v′ = t®v [a] a®w
      SV′ = goodCasesRefl ([G] id ε [a]) ([G]₁ id ε [a]′)
      in  irrelevanceTermSV ([G] id ε [a]) ([G]₁ id ε [a]′) t®v′ SV′
irrelevanceTermSV [A] [A]′ t®v (Bᵥ (BΣ q) (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                               (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)) [t₁]′
                               with whrDet* (red D , Σₙ) (red D₁ , Σₙ)
... | Σ≡Σ′ with B-PE-injectivity (BΣ q) (BΣ q) Σ≡Σ′
... | PE.refl , PE.refl , _ =
  let [t₁] = I.irrelevanceTerm ([F]₁ id ε) ([F] id ε) [t₁]′
      t₁®v₁  , t₂®v₂ = t®v [t₁]
      SV = goodCasesRefl ([F] id ε) ([F]₁ id ε)
      SV′ = goodCasesRefl ([G] id ε [t₁]) ([G]₁ id ε [t₁]′)
  in  irrelevanceTermSV ([F] id ε) ([F]₁ id ε) t₁®v₁ SV
    , irrelevanceTermSV ([G] id ε [t₁]) ([G]₁ id ε [t₁]′) t₂®v₂ SV′
irrelevanceTermSV (emb 0<1 [A]) [A]′ t®v (emb⁰¹ SV) = irrelevanceTermSV [A] [A]′ t®v SV
irrelevanceTermSV [A] (emb 0<1 [A]′) t®v (emb¹⁰ SV) = irrelevanceTermSV [A] [A]′ t®v SV

irrelevanceTerm : ∀ {l t v A} → ([A] [A]′ : ε ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A]
                → t ®⟨ l ⟩ v ∷ A / [A]′
irrelevanceTerm [A] [A]′ t®v = irrelevanceTermSV [A] [A]′ t®v (goodCasesRefl [A] [A]′)


irrelevanceTerm′ : ∀ {l t v A} → A PE.≡ A′ → ([A] : ε ⊩⟨ l ⟩ A)
                 → ([A]′ : ε ⊩⟨ l ⟩ A′) → t ®⟨ l ⟩ v ∷ A / [A]
                 → t ®⟨ l ⟩ v ∷ A′ / [A]′
irrelevanceTerm′ PE.refl [A] [A]′ t®v = irrelevanceTerm [A] [A]′ t®v

convTermSV : ∀ {l l′ A B t v} → ([A] : ε ⊩⟨ l ⟩ A) → ([B] : ε ⊩⟨ l′ ⟩ B) → ε ⊩⟨ l ⟩ A ≡ B / [A]
          → ShapeView ε l l′ A B [A] [B] → t ®⟨ l ⟩ v ∷ A / [A] → t ®⟨ l′ ⟩ v ∷ B / [B]
convTermSV .(Uᵣ UA) .(Uᵣ UB) A≡B (Uᵥ UA UB) t®v = t®v
convTermSV .(ℕᵣ ℕA) .(ℕᵣ ℕB) A≡B (ℕᵥ ℕA ℕB) t®v = t®v
convTermSV .(Unitᵣ UnitA) .(Unitᵣ UnitB) A≡B (Unitᵥ UnitA UnitB) t®v = t®v
convTermSV .(ne′ K D neK K≡K) .(ne neB) A≡B (ne (ne K D neK K≡K) neB) t®v = ⊥-elim (noClosedNe neK)
convTermSV [A] _ A≡B (Bᵥ (BΠ 𝟘 q) (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                           (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)) t®v [a]′ =
  let [a] = convTerm₁ ([F]₁ id ε) ([F] id ε) {!!} [a]′
      t®v′ = t®v [a]
      SV = goodCases ([G] id ε [a]) ([G]₁ id ε [a]′) {!!}
  in  convTermSV ([G] id ε [a]) ([G]₁ id ε [a]′) {!!} SV t®v′
  -- irrelevanceTermSV ([G] id ε [a]) ([G]₁ id ε [a]′) t®v′ SV′
convTermSV (Bᵣ (BΠ ω q) BA) .(Bᵣ (BΠ ω q) BB) A≡B (Bᵥ (BΠ ω q) BA BB) t®v = {!!}
convTermSV (Bᵣ (BΣ p) BA) .(Bᵣ (BΣ p) BB) A≡B (Bᵥ (BΣ p) BA BB) t®v = {!!}
convTermSV (emb 0<1 [A]) [B] A≡B (emb⁰¹ SV) t®v = convTermSV [A] [B] A≡B SV t®v
convTermSV [A] (emb 0<1 [B]) A≡B (emb¹⁰ SV) t®v = convTermSV [A] [B] A≡B SV t®v

convTerm : ∀ {l A B t v} → ([A] : ε ⊩⟨ l ⟩ A) → ([B] : ε ⊩⟨ l ⟩ B) → ε ⊩⟨ l ⟩ A ≡ B / [A]
         → t ®⟨ l ⟩ v ∷ A / [A] → t ®⟨ l ⟩ v ∷ B / [B]
convTerm [A] [B] A≡B t®v = convTermSV [A] [B] A≡B {!(goodCases [A] [B] A≡B)!} t®v

-- irrelevanceTerm″ : ∀ {l t v A} → A ≡ A′
--                  → ([A] : ε ⊩⟨ l ⟩ A)
--                  → t ®⟨ l ⟩ v ∷ A / [A]
--                  → ∃ λ ([A]′ : ε ⊩⟨ l ⟩ A′)
--                  → t ®⟨ l ⟩ v ∷ A′ / [A]′
-- irrelevanceTerm″ eq [A] t®v =
--   let [A]′ = I.irrelevance′ eq [A]
--   in  [A]′ , irrelevanceTerm′ eq [A] [A]′ t®v

irrelevanceQuant : ∀ {l t v A} → ([A] [A]′ : ε ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A ◂ p / [A]
                 → t ®⟨ l ⟩ v ∷ A ◂ p / [A]′
irrelevanceQuant {𝟘} [A] [A]′ t®v = tt
irrelevanceQuant {ω} [A] [A]′ t®v = irrelevanceTerm [A] [A]′ t®v

irrelevanceSubst : ∀ {σ σ′ l} → ([Γ] [Γ]′ : ⊩ᵛ Γ) ([σ] : ε ⊩ˢ σ ∷ Γ / [Γ] / ε)
                           ([σ]′ : ε ⊩ˢ σ ∷ Γ / [Γ]′ / ε)
                           (σ®σ′ : σ ®⟨ l ⟩ σ′ ∷ Γ ◂ γ / [Γ] / [σ])
                         → (σ ®⟨ l ⟩ σ′ ∷ Γ ◂ γ / [Γ]′ / [σ]′)
irrelevanceSubst {Γ = ε} {γ = ε} ε ε tt tt tt = tt
irrelevanceSubst {Γ = Γ ∙ A} {γ = γ ∙ p} {l = l}
                 ([Γ] ∙ [A]) ([Γ]′ ∙ [A]′) ([tailσ] , b) ([tailσ]′ , d) (σ®σ , t®v) =
  let σ®σ′ = irrelevanceSubst [Γ] [Γ]′ [tailσ] [tailσ]′ σ®σ
      [σA] = proj₁ ([A] ε [tailσ])
      t®v′ = irrelevanceQuant {!!} (proj₁ ([A]′ ε [tailσ]′)) t®v
  in  σ®σ′ , t®v′

irrelevance : ∀ {l} → ([Γ] [Γ]′ : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ]) ([A]′ : Γ ⊩ᵛ⟨ l ⟩ A / [Γ]′)
              (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷ A / [Γ] / [A]) → (γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷ A / [Γ]′ / [A]′)
irrelevance [Γ] [Γ]′ [A] [A]′ ⊩ʳt [σ]′ σ®σ′ =
  let [σ] = IS.irrelevanceSubst [Γ]′ [Γ] ε ε [σ]′
      σ®σ = irrelevanceSubst [Γ]′ [Γ] [σ]′ [σ] σ®σ′
      t®v = ⊩ʳt [σ] σ®σ
  in  irrelevanceTerm (proj₁ ([A] ε [σ])) (proj₁ ([A]′ ε [σ]′)) t®v
