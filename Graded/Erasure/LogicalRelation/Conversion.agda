------------------------------------------------------------------------
-- Type conversion lemmata for the logical relation
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
import Definition.Typed
open import Definition.Typed.Restrictions
import Definition.Untyped
open import Graded.Modality
open import Tools.Nullary
import Tools.PropositionalEquality as PE

module Graded.Erasure.LogicalRelation.Conversion
  {a k} {M : Set a}
  (open Definition.Untyped M)
  (𝕄 : Modality M)
  (open Modality 𝕄)
  (R : Type-restrictions M)
  (open Definition.Typed R)
  {Δ : Con Term k} (⊢Δ : ⊢ Δ)
  (is-𝟘? : (p : M) → Dec (p PE.≡ 𝟘))
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}

open import Graded.Erasure.LogicalRelation 𝕄 R ⊢Δ is-𝟘?
import Graded.Erasure.Target as T

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Fundamental.Reducibility R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Properties.Conversion R
open import Definition.LogicalRelation.Properties.Escape R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Properties R
import Definition.LogicalRelation.Substitution.Irrelevance R as IS
open import Graded.Mode 𝕄
open import Definition.Untyped.Properties M

open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Reduction R
open import Definition.Typed.RedSteps R
open import Definition.Typed.Weakening R hiding (wk)

open import Tools.Level
open import Tools.Nat
open import Tools.Product
open import Tools.Unit

private
  variable
    n : Nat
    Γ : Con Term n
    A B t : Term n
    v : T.Term n
    p : M
    m : Mode

-- Conversion of logical relation for erasure using ShapeView
-- If t ® v ∷ A and Δ ⊩ A ≡ B then t ® v ∷ B

convTermʳ′ : ∀ {l l′}
           → ([A] : Δ ⊩⟨ l ⟩ A)
             ([B] : Δ ⊩⟨ l′ ⟩ B)
           → Δ ⊢ A ≡ B
           → ShapeView Δ l l′ A B [A] [B]
           → t ®⟨ l ⟩ v ∷ A / [A]
           → t ®⟨ l′ ⟩ v ∷ B / [B]
convTermʳ′ _ _ A≡B (Uᵥ UA UB) t®v = t®v
convTermʳ′ _ _ A≡B (ℕᵥ ℕA ℕB) t®v = t®v
convTermʳ′ _ _ A≡B (Unitᵥ UnitA UnitB) t®v = t®v
convTermʳ′
  [A] [B] A≡B
  (Bᵥ (BΠ p q) (Bᵣ F G [ _ , _ , A⇒Π ] ⊢F ⊢G A≡A [F] [G] G-ext _)
     (Bᵣ F₁ G₁ [ _ , _ , B⇒Π₁ ] ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
  t®v
     with is-𝟘? p
... | yes PE.refl = λ [a]′ →
  let Π≡Π₁ = reduction′ A⇒Π B⇒Π₁ ΠΣₙ ΠΣₙ A≡B
      F≡F₁ , G≡G₁ , _ , _ = injectivity Π≡Π₁
      [F₁]′ , [F]′ , [F₁≡F]′ = reducibleEq (sym F≡F₁)
      [F₁≡F] = irrelevanceEq″ (PE.sym (wk-id F₁)) (PE.sym (wk-id F))
                              [F₁]′ ([F]₁ id ⊢Δ) [F₁≡F]′
      [a] = convTerm₁ ([F]₁ id ⊢Δ) ([F] id ⊢Δ) [F₁≡F] [a]′
      G≡G₁′ = wkEq (lift id) (⊢Δ ∙ escape ([F] id ⊢Δ)) G≡G₁
      G[a]≡G₁[a] = substTypeEq G≡G₁′ (refl (escapeTerm ([F] id ⊢Δ) [a]))
      [Ga]′ , [G₁a]′ , [Ga≡G₁a]′ = reducibleEq G[a]≡G₁[a]
      [Ga≡G₁a] = irrelevanceEq [Ga]′ ([G] id ⊢Δ [a]) [Ga≡G₁a]′
      t®v′ = t®v [a]
      SV = goodCases ([G] id ⊢Δ [a]) ([G]₁ id ⊢Δ [a]′) [Ga≡G₁a]
  in  convTermʳ′ ([G] id ⊢Δ [a]) ([G]₁ id ⊢Δ [a]′) G[a]≡G₁[a] SV t®v′
... | no p≢𝟘 = λ [a]′ a®w′ →
  let Π≡Π₁ = reduction′ A⇒Π B⇒Π₁ ΠΣₙ ΠΣₙ A≡B
      F≡F₁ , G≡G₁ , _ , _ = injectivity Π≡Π₁
      [F₁]′ , [F]′ , [F₁≡F]′ = reducibleEq (sym F≡F₁)
      [F₁≡F] = irrelevanceEq″ (PE.sym (wk-id F₁)) (PE.sym (wk-id F))
                              [F₁]′ ([F]₁ id ⊢Δ) [F₁≡F]′
      [a] = convTerm₁ ([F]₁ id ⊢Δ) ([F] id ⊢Δ) [F₁≡F] [a]′
      G≡G₁′ = wkEq (lift id) (⊢Δ ∙ escape ([F] id ⊢Δ)) G≡G₁
      G[a]≡G₁[a] = substTypeEq G≡G₁′ (refl (escapeTerm ([F] id ⊢Δ) [a]))
      [Ga]′ , [G₁a]′ , [Ga≡G₁a]′ = reducibleEq G[a]≡G₁[a]
      [Ga≡G₁a] = irrelevanceEq [Ga]′ ([G] id ⊢Δ [a]) [Ga≡G₁a]′
      SV = goodCases ([F]₁ id ⊢Δ) ([F] id ⊢Δ) [F₁≡F]
      F₁≡F = PE.subst₂ (Δ ⊢_≡_) (PE.sym (wk-id F₁)) (PE.sym (wk-id F)) (sym F≡F₁)
      a®w = convTermʳ′ ([F]₁ id ⊢Δ) ([F] id ⊢Δ) F₁≡F SV a®w′
      t®v′ = t®v [a] a®w
      SV′ = goodCases ([G] id ⊢Δ [a]) ([G]₁ id ⊢Δ [a]′) [Ga≡G₁a]
  in  convTermʳ′ ([G] id ⊢Δ [a]) ([G]₁ id ⊢Δ [a]′) G[a]≡G₁[a] SV′ t®v′
convTermʳ′ {v = v}
  [A] [B] A≡B
  (Bᵥ (BΣ _ p _) (Bᵣ F G [ _ , _ , A⇒Σ ] ⊢F ⊢G A≡A [F] [G] G-ext _)
     (Bᵣ F₁ G₁ [ _ , _ , B⇒Σ₁ ] ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
  (t₁ , t₂ , t⇒t′ , [t₁] , v₂ , t₂®v₂ , extra) =
  let Σ≡Σ₁ = reduction′ A⇒Σ B⇒Σ₁ ΠΣₙ ΠΣₙ A≡B
      F≡F₁ , G≡G₁ , _ = Σ-injectivity Σ≡Σ₁
      [F]′ = [F] id ⊢Δ
      [F]₁′ = [F]₁ id ⊢Δ
      [F]″ , [F₁]″ , [F≡F₁]′ = reducibleEq F≡F₁
      [F≡F₁] = irrelevanceEq″ (PE.sym (wk-id F)) (PE.sym (wk-id F₁))
                              [F]″ [F]′ [F≡F₁]′
      F≡F₁′ = PE.subst₂ (Δ ⊢_≡_) (PE.sym (wk-id F)) (PE.sym (wk-id F₁)) F≡F₁
      [t₁]′ = convTerm₁ [F]′ [F]₁′ [F≡F₁] [t₁]
      G≡G₁′ = wkEq (lift id) (⊢Δ ∙ escape [F]′) G≡G₁
      G[t₁]≡G₁[t₁] = substTypeEq G≡G₁′ (refl (escapeTerm [F]′ [t₁]))
      [Gt₁] = [G] id ⊢Δ [t₁]
      [Gt₁]₁ = [G]₁ id ⊢Δ [t₁]′
      [Gt₁]′ , [G₁t₁]′ , [Gt₁≡G₁t₁]′ = reducibleEq G[t₁]≡G₁[t₁]
      [Gt₁≡G₁t₁] = irrelevanceEq [Gt₁]′ [Gt₁] [Gt₁≡G₁t₁]′
      t⇒t″ = conv* t⇒t′ Σ≡Σ₁
      SV₂ = goodCases [Gt₁] [Gt₁]₁ [Gt₁≡G₁t₁]
      t₂®v₂′ = convTermʳ′ [Gt₁] [Gt₁]₁ G[t₁]≡G₁[t₁] SV₂ t₂®v₂
      SV₁ = goodCases [F]′ [F]₁′ [F≡F₁]
      extra′ =
        Σ-®-elim (λ _ → Σ-® _ _ [F]₁′ t₁ v v₂ p) extra
                 Σ-®-intro-𝟘
                 λ v₁ v⇒p t₁®v₁ →
                   let t₁®v₁′ = convTermʳ′ [F]′ [F]₁′ F≡F₁′ SV₁ t₁®v₁
                   in  Σ-®-intro-ω v₁ v⇒p t₁®v₁′
  in  t₁ , t₂ , t⇒t″ , [t₁]′ , v₂ , t₂®v₂′ , extra′
convTermʳ′ (emb 0<1 [A]) [B] A≡B (emb⁰¹ SV) t®v =
  convTermʳ′ [A] [B] A≡B SV t®v
convTermʳ′ [A] (emb 0<1 [B]) A≡B (emb¹⁰ SV) t®v =
  convTermʳ′ [A] [B] A≡B SV t®v
-- Impossible cases
convTermʳ′ _ _ _ (Emptyᵥ _ _) ()
convTermʳ′ _ _ _ (ne _ _) ()

-- Conversion of logical relation for erasure
-- If t ® v ∷ A and Δ ⊢ A ≡ B then t ® v ∷ B

convTermʳ : ∀ {l l′ A B t v}
          → ([A] : Δ ⊩⟨ l ⟩ A)
            ([B] : Δ ⊩⟨ l′ ⟩ B)
          → Δ ⊢ A ≡ B
          → t ®⟨ l ⟩ v ∷ A / [A]
          → t ®⟨ l′ ⟩ v ∷ B / [B]
convTermʳ [A] [B] A≡B t®v =
  let [A]′ , [B]′ , [A≡B]′ = reducibleEq A≡B
      [A≡B] = irrelevanceEq [A]′ [A] [A≡B]′
  in convTermʳ′ [A] [B] A≡B (goodCases [A] [B] [A≡B]) t®v

convTermQuantʳ : ∀ {l l′ A B t v} p
               → ([A] : Δ ⊩⟨ l ⟩ A)
                 ([B] : Δ ⊩⟨ l′ ⟩ B)
               → Δ ⊢ A ≡ B
               → t ®⟨ l ⟩ v ∷ A ◂ p / [A]
               → t ®⟨ l′ ⟩ v ∷ B ◂ p / [B]
convTermQuantʳ p [A] [B] A≡B t®v with is-𝟘? p
... | yes PE.refl = lift tt
... | no p≢𝟘 = convTermʳ [A] [B] A≡B t®v

-- Conversion of erasure validity
-- If γ ▸ Γ ⊩ʳ t ∷ A and Γ ⊩ᵛ A ≡ B then γ ▸ Γ ⊩ʳ t ∷ B

convʳ : ∀ {l l′ A B t γ}
      → ([Γ] : ⊩ᵛ Γ)
        ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
        ([B] : Γ ⊩ᵛ⟨ l′ ⟩ B / [Γ])
        (A≡B : Γ ⊢ A ≡ B)
        (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] A / [Γ] / [A])
      → (γ ▸ Γ ⊩ʳ⟨ l′ ⟩ t ∷[ m ] B / [Γ] / [B])
convʳ {m = m} {A = A} {B = B} [Γ] [A] [B] A≡B ⊩ʳt [σ] σ®σ′ =
  let t®v = ⊩ʳt [σ] σ®σ′
      [σA] = proj₁ (unwrap [A] ⊢Δ [σ])
      [σB] = proj₁ (unwrap [B] ⊢Δ [σ])
      σA≡σB = substitutionEq A≡B (wellformedSubstEq [Γ] ⊢Δ [σ] (reflSubst [Γ] ⊢Δ [σ])) ⊢Δ
  in  convTermQuantʳ ⌜ m ⌝ [σA] [σB] σA≡σB t®v
