{-# OPTIONS --without-K --safe #-}
open import Definition.Modality.Erasure

open import Definition.Typed.EqualityRelation


module Erasure.LogicalRelation.Conversion {{eqrel : EqRelSet Erasure′}} where
open EqRelSet {{...}}

open import Erasure.LogicalRelation
import Erasure.Target as T

open import Definition.LogicalRelation Erasure′
open import Definition.LogicalRelation.Irrelevance Erasure′
open import Definition.LogicalRelation.Fundamental.Reducibility Erasure′
open import Definition.LogicalRelation.ShapeView Erasure′
open import Definition.LogicalRelation.Properties.Conversion Erasure′
open import Definition.LogicalRelation.Properties.Escape Erasure′
open import Definition.LogicalRelation.Properties.Symmetry Erasure′
open import Definition.LogicalRelation.Substitution Erasure′
open import Definition.LogicalRelation.Substitution.Properties Erasure′
import Definition.LogicalRelation.Substitution.Irrelevance Erasure′ as IS

open import Definition.Untyped Erasure
open import Definition.Untyped.Properties Erasure
import Definition.Untyped.BindingType Erasure′ as BT

open import Definition.Typed Erasure′
open import Definition.Typed.Consequences.Injectivity Erasure′
open import Definition.Typed.Consequences.Substitution Erasure′
open import Definition.Typed.Reduction Erasure′
open import Definition.Typed.RedSteps Erasure′
open import Definition.Typed.Weakening Erasure′

open import Tools.Empty
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    A B t : Term n
    v : T.Term n

-- Conversion of logical relation for erasure using ShapeView
-- If t ® v ∷ A and ε ⊩ A ≡ B then t ® v ∷ B

convTermʳ′ : ∀ {l l′}
           → ([A] : ε ⊩⟨ l ⟩ A)
             ([B] : ε ⊩⟨ l′ ⟩ B)
           → ε ⊢ A ≡ B
           → ShapeView ε l l′ A B [A] [B]
           → t ®⟨ l ⟩ v ∷ A / [A]
           → t ®⟨ l′ ⟩ v ∷ B / [B]
convTermʳ′ _ _ A≡B (Uᵥ UA UB) t®v = t®v
convTermʳ′ _ _ A≡B (ℕᵥ ℕA ℕB) t®v = t®v
convTermʳ′ _ _ A≡B (Unitᵥ UnitA UnitB) t®v = t®v
convTermʳ′ [A] [B] A≡B (Bᵥ (BΠ 𝟘 q) BΠ! (Bᵣ F G [ _ , _ , A⇒Π ] ⊢F ⊢G A≡A [F] [G] G-ext)
           (Bᵣ F₁ G₁ [ _ , _ , B⇒Π₁ ] ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) (BT.Π≋Π PE.refl PE.refl)) t®v [a]′ =
  let Π≡Π₁ = reduction′ A⇒Π B⇒Π₁ Πₙ Πₙ A≡B
      F≡F₁ , G≡G₁ , _ , _ = injectivity Π≡Π₁
      [F₁]′ , [F]′ , [F₁≡F]′ = reducibleEq (sym F≡F₁)
      [F₁≡F] = irrelevanceEq″ (PE.sym (wk-id F₁)) (PE.sym (wk-id F))
                              [F₁]′ ([F]₁ id ε) [F₁≡F]′
      [a] = convTerm₁ ([F]₁ id ε) ([F] id ε) [F₁≡F] [a]′
      G≡G₁′ = wkEq (lift id) (ε ∙ escape ([F] id ε)) G≡G₁
      G[a]≡G₁[a] = substTypeEq G≡G₁′ (refl (escapeTerm ([F] id ε) [a]))
      [Ga]′ , [G₁a]′ , [Ga≡G₁a]′ = reducibleEq G[a]≡G₁[a]
      [Ga≡G₁a] = irrelevanceEq [Ga]′ ([G] id ε [a]) [Ga≡G₁a]′
      t®v′ = t®v [a]
      SV = goodCases ([G] id ε [a]) ([G]₁ id ε [a]′) [Ga≡G₁a]
  in  convTermʳ′ ([G] id ε [a]) ([G]₁ id ε [a]′) G[a]≡G₁[a] SV t®v′
convTermʳ′ [A] [B] A≡B (Bᵥ (BΠ ω q) BΠ! (Bᵣ F G [ _ , _ , A⇒Π ] ⊢F ⊢G A≡A [F] [G] G-ext)
           (Bᵣ F₁ G₁ [ _ , _ , B⇒Π₁ ] ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) (BT.Π≋Π PE.refl PE.refl)) t®v [a]′ a®w′ =
  let Π≡Π₁ = reduction′ A⇒Π B⇒Π₁ Πₙ Πₙ A≡B
      F≡F₁ , G≡G₁ , _ , _ = injectivity Π≡Π₁
      [F₁]′ , [F]′ , [F₁≡F]′ = reducibleEq (sym F≡F₁)
      [F₁≡F] = irrelevanceEq″ (PE.sym (wk-id F₁)) (PE.sym (wk-id F))
                              [F₁]′ ([F]₁ id ε) [F₁≡F]′
      [a] = convTerm₁ ([F]₁ id ε) ([F] id ε) [F₁≡F] [a]′
      G≡G₁′ = wkEq (lift id) (ε ∙ escape ([F] id ε)) G≡G₁
      G[a]≡G₁[a] = substTypeEq G≡G₁′ (refl (escapeTerm ([F] id ε) [a]))
      [Ga]′ , [G₁a]′ , [Ga≡G₁a]′ = reducibleEq G[a]≡G₁[a]
      [Ga≡G₁a] = irrelevanceEq [Ga]′ ([G] id ε [a]) [Ga≡G₁a]′
      SV = goodCases ([F]₁ id ε) ([F] id ε) [F₁≡F]
      F₁≡F = PE.subst₂ (ε ⊢_≡_) (PE.sym (wk-id F₁)) (PE.sym (wk-id F)) (sym F≡F₁)
      a®w = convTermʳ′ ([F]₁ id ε) ([F] id ε) F₁≡F SV a®w′
      t®v′ = t®v [a] a®w
      SV′ = goodCases ([G] id ε [a]) ([G]₁ id ε [a]′) [Ga≡G₁a]
  in  convTermʳ′ ([G] id ε [a]) ([G]₁ id ε [a]′) G[a]≡G₁[a] SV′ t®v′
convTermʳ′ [A] [B] A≡B (Bᵥ (BΣ q m) BΣ! (Bᵣ F G [ _ , _ , A⇒Σ ] ⊢F ⊢G A≡A [F] [G] G-ext)
           (Bᵣ F₁ G₁ [ _ , _ , B⇒Σ₁ ] ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) (BT.Σ≋Σ PE.refl))
           (t₁ , t₂ , v₁ , v₂ , t⇒t′ , v⇒v′ , [t₁] , t₁®v₁ , t₂®v₂) =
  let Σ≡Σ₁ = reduction′ A⇒Σ B⇒Σ₁ Σₙ Σₙ A≡B
      F≡F₁ , G≡G₁ , _ = Σ-injectivity Σ≡Σ₁
      [F]′ , [F₁]′ , [F≡F₁]′ = reducibleEq F≡F₁
      [F≡F₁] = irrelevanceEq″ (PE.sym (wk-id F)) (PE.sym (wk-id F₁))
                              [F]′ ([F] id ε) [F≡F₁]′
      F≡F₁′ = PE.subst₂ (ε ⊢_≡_) (PE.sym (wk-id F)) (PE.sym (wk-id F₁)) F≡F₁
      [t₁]′ = convTerm₁ ([F] id ε) ([F]₁ id ε) [F≡F₁] [t₁]
      G≡G₁′ = wkEq (lift id) (ε ∙ escape ([F] id ε)) G≡G₁
      G[t₁]≡G₁[t₁] = substTypeEq G≡G₁′ (refl (escapeTerm ([F] id ε) [t₁]))
      [Gt₁]′ , [G₁t₁]′ , [Gt₁≡G₁t₁]′ = reducibleEq G[t₁]≡G₁[t₁]
      [Gt₁≡G₁t₁] = irrelevanceEq [Gt₁]′ ([G] id ε [t₁]) [Gt₁≡G₁t₁]′
      t⇒t″ = conv* t⇒t′ Σ≡Σ₁
      SV₁ = goodCases ([F] id ε) ([F]₁ id ε) [F≡F₁]
      SV₂ = goodCases ([G] id ε [t₁]) ([G]₁ id ε [t₁]′) [Gt₁≡G₁t₁]
      t₁®v₁′ = convTermʳ′ ([F] id ε) ([F]₁ id ε) F≡F₁′ SV₁ t₁®v₁
      t₂®v₂′ = convTermʳ′ ([G] id ε [t₁]) ([G]₁ id ε [t₁]′) G[t₁]≡G₁[t₁] SV₂ t₂®v₂
  in  t₁ , t₂ , v₁ , v₂ , t⇒t″ , v⇒v′ , [t₁]′ , t₁®v₁′ , t₂®v₂′
convTermʳ′ (emb 0<1 [A]) [B] A≡B (emb⁰¹ SV) t®v = convTermʳ′ [A] [B] A≡B SV t®v
convTermʳ′ [A] (emb 0<1 [B]) A≡B (emb¹⁰ SV) t®v = convTermʳ′ [A] [B] A≡B SV t®v

-- Conversion of logical relation for erasure
-- If t ® v ∷ A and ε ⊢ A ≡ B then t ® v ∷ B

convTermʳ : ∀ {l l′ A B t v}
          → ([A] : ε ⊩⟨ l ⟩ A)
            ([B] : ε ⊩⟨ l′ ⟩ B)
          → ε ⊢ A ≡ B
          → t ®⟨ l ⟩ v ∷ A / [A]
          → t ®⟨ l′ ⟩ v ∷ B / [B]
convTermʳ [A] [B] A≡B t®v =
  let [A]′ , [B]′ , [A≡B]′ = reducibleEq A≡B
      [A≡B] = irrelevanceEq [A]′ [A] [A≡B]′
  in convTermʳ′ [A] [B] A≡B (goodCases [A] [B] [A≡B]) t®v

-- Conversion of erasure validity
-- If γ ▸ Γ ⊩ʳ t ∷ A and Γ ⊩ᵛ A ≡ B then γ ▸ Γ ⊩ʳ t ∷ B

convʳ : ∀ {l l′ A B t γ}
      → ([Γ] : ⊩ᵛ Γ)
        ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
        ([B] : Γ ⊩ᵛ⟨ l′ ⟩ B / [Γ])
        (A≡B : Γ ⊢ A ≡ B)
        (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷ A / [Γ] / [A])
      → (γ ▸ Γ ⊩ʳ⟨ l′ ⟩ t ∷ B / [Γ] / [B])
convʳ {A = A} {B = B} [Γ] [A] [B] A≡B ⊩ʳt [σ] σ®σ′ =
  let t®v = ⊩ʳt [σ] σ®σ′
      [σA] = proj₁ ([A] ε [σ])
      [σB] = proj₁ ([B] ε [σ])
      σA≡σB = substitutionEq A≡B (wellformedSubstEq [Γ] ε [σ] (reflSubst [Γ] ε [σ])) ε
  in  convTermʳ [σA] [σB] σA≡σB t®v
