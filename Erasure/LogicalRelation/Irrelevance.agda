{-# OPTIONS --without-K --allow-unsolved-metas  #-}
open import Definition.Modality.Erasure

open import Definition.Typed.EqualityRelation


module Erasure.LogicalRelation.Irrelevance {{eqrel : EqRelSet Erasure}} where
open EqRelSet {{...}}

open import Erasure.LogicalRelation

open import Definition.LogicalRelation Erasure
import Definition.LogicalRelation.Irrelevance Erasure as I
open import Definition.LogicalRelation.Properties.MaybeEmb Erasure
open import Definition.LogicalRelation.Substitution Erasure
import Definition.LogicalRelation.Substitution.Irrelevance Erasure as IS

open import Definition.Untyped Erasure
open import Definition.Untyped.Properties Erasure
open import Definition.Typed Erasure
open import Definition.Typed.Weakening Erasure
open import Definition.Typed.Properties Erasure
open import Definition.Modality.Context ErasureModality

open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Unit

private
  variable
    n : Nat
    Γ : Con Term n
    A A′ t : Term n
    γ : Conₘ n
    p : Erasure

irrelevanceTerm : ∀ {l t v A} → ([A] [A]′ : ε ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A]
                → t ®⟨ l ⟩ v ∷ A / [A]′

-- Equal cases

irrelevanceTerm (Uᵣ x) (Uᵣ x₁) t®v = t®v
irrelevanceTerm (ℕᵣ x) (ℕᵣ x₁) t®v = t®v
irrelevanceTerm (Unitᵣ D) (Unitᵣ D′) t®v = t®v
irrelevanceTerm (Bᵣ′ (BΠ 𝟘 q) F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                (Bᵣ′ (BΠ p′ q′) F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′) t®v
                with whrDet* (red D , Πₙ) (red D′ , Πₙ)
... | Π≡Π′ with B-PE-injectivity (BΠ 𝟘 q) (BΠ p′ q′) Π≡Π′
... | refl , refl , refl = λ [a]′ →
  let [a] = I.irrelevanceTerm ([F]′ id ε) ([F] id ε) [a]′
      t®v′ = t®v [a]
  in  irrelevanceTerm ([G] id ε [a]) ([G]′ id ε [a]′) t®v′
irrelevanceTerm (Bᵣ′ (BΠ ω q) F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                (Bᵣ′ (BΠ p′ q′) F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′) t®v
                with whrDet* (red D , Πₙ) (red D′ , Πₙ)
... | Π≡Π′ with B-PE-injectivity (BΠ ω q) (BΠ p′ q′) Π≡Π′
... | refl , refl , refl = λ [a]′ a®w′ →
  let [a] = I.irrelevanceTerm ([F]′ id ε) ([F] id ε) [a]′
      a®w = irrelevanceTerm ([F]′ id ε) ([F] id ε) a®w′
      t®v′ = t®v [a] a®w
  in  irrelevanceTerm ([G] id ε [a]) ([G]′ id ε [a]′) t®v′
irrelevanceTerm (Bᵣ′ (BΣ q) F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                (Bᵣ′ (BΣ q′) F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′) t®v
                with whrDet* (red D , Σₙ) (red D′ , Σₙ)
... | Σ≡Σ′ with B-PE-injectivity (BΣ q) (BΣ q′) Σ≡Σ′
... | refl , refl , refl = λ [t₁]′ →
  let [t₁] = I.irrelevanceTerm ([F]′ id ε) ([F] id ε) [t₁]′
      t₁®v₁  , t₂®v₂ = t®v [t₁]
  in  irrelevanceTerm ([F] id ε) ([F]′ id ε) t₁®v₁
    , irrelevanceTerm ([G] id ε [t₁]) ([G]′ id ε [t₁]′) t₂®v₂

-- Neutral cases

irrelevanceTerm [A] (ne′ K D neK K≡K) t®v with noClosedNe neK
... | ()
irrelevanceTerm (ne′ K D neK K≡K) [A]′ t®v with noClosedNe neK
... | ()

-- Embedding cases

irrelevanceTerm [A] (emb 1<0 [A]′) t®v = {!!}
irrelevanceTerm (emb 1<0 [A]) [A]′ t®v = {![A]!}

-- Refutable cases

irrelevanceTerm (Uᵣ x) (ℕᵣ D) t®v with whnfRed* (red D) Uₙ
... | ()
irrelevanceTerm (Uᵣ x) (Emptyᵣ D) t®v with whnfRed* (red D) Uₙ
... | ()
irrelevanceTerm (Uᵣ x) (Unitᵣ D) t®v with whnfRed* (red D) Uₙ
... | ()
irrelevanceTerm (Uᵣ x) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) t®v =
  ⊥-elim (U≢B W (whnfRed* (red D) Uₙ))


irrelevanceTerm (ℕᵣ D) (Uᵣ x₁) t®v with whnfRed* (red D) Uₙ
... | ()
irrelevanceTerm (ℕᵣ D) (Emptyᵣ D′) t®v with whrDet* (red D , ℕₙ) (red D′ , Emptyₙ)
... | ()
irrelevanceTerm (ℕᵣ D) (Unitᵣ D′) t®v with whrDet* (red D , ℕₙ) (red D′ , Unitₙ)
... | ()
irrelevanceTerm (ℕᵣ D) (Bᵣ′ W F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) t®v =
  ⊥-elim (ℕ≢B W (whrDet* (red D , ℕₙ) (red D′ , ⟦ W ⟧ₙ)))


irrelevanceTerm (Unitᵣ D) (Uᵣ D′) t®v with whnfRed* (red D) Uₙ
... | ()
irrelevanceTerm (Unitᵣ D) (ℕᵣ D′) t®v with whrDet* (red D , Unitₙ) (red D′ , ℕₙ)
... | ()
irrelevanceTerm (Unitᵣ D) (Emptyᵣ D′) t®v with whrDet* (red D , Unitₙ) (red D′ , Emptyₙ)
... | ()
irrelevanceTerm (Unitᵣ D) (Bᵣ′ W F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) t®v =
  ⊥-elim (Unit≢B W (whrDet* (red D , Unitₙ) (red D′ , ⟦ W ⟧ₙ)))


irrelevanceTerm (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ D′) t®v
  = ⊥-elim (U≢B W (whnfRed* (red D) Uₙ))
irrelevanceTerm (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ D′) t®v
  = ⊥-elim (ℕ≢B W (whrDet* (red D′ , ℕₙ) (red D , ⟦ W ⟧ₙ)))
irrelevanceTerm (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ D′) t®v
  = ⊥-elim (Empty≢B W (whrDet* (red D′ , Emptyₙ) (red D , ⟦ W ⟧ₙ)))
irrelevanceTerm (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Unitᵣ D′) t®v
  = ⊥-elim (Unit≢B W (whrDet* (red D′ , Unitₙ) (red D , ⟦ W ⟧ₙ)))

irrelevanceTerm (Bᵣ′ (BΠ p q) F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                (Bᵣ′ (BΣ q′) F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′) t®v
                with whrDet* (red D , Πₙ) (red D′ , Σₙ)
... | ()
irrelevanceTerm (Bᵣ′ (BΣ q′) F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                (Bᵣ′ (BΠ p q) F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′) t®v
                with whrDet* (red D , Σₙ) (red D′ , Πₙ)
... | ()


irrelevanceTerm′ : ∀ {l t v A} → A ≡ A′ → ([A] : ε ⊩⟨ l ⟩ A)
                 → ([A]′ : ε ⊩⟨ l ⟩ A′) → t ®⟨ l ⟩ v ∷ A / [A]
                 → t ®⟨ l ⟩ v ∷ A′ / [A]′
irrelevanceTerm′ refl [A] [A]′ t®v = irrelevanceTerm [A] [A]′ t®v

irrelevanceTerm″ : ∀ {l t v A} → A ≡ A′
                 → ([A] : ε ⊩⟨ l ⟩ A)
                 → t ®⟨ l ⟩ v ∷ A / [A]
                 → ∃ λ ([A]′ : ε ⊩⟨ l ⟩ A′)
                 → t ®⟨ l ⟩ v ∷ A′ / [A]′
irrelevanceTerm″ eq [A] t®v =
  let [A]′ = I.irrelevance′ eq [A]
  in  [A]′ , irrelevanceTerm′ eq [A] [A]′ t®v

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
