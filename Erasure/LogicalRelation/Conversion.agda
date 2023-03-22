open import Definition.Modality.Instances.Erasure
open import Definition.Modality.Restrictions
open import Definition.Typed.EqualityRelation
open import Definition.Untyped Erasure
open import Definition.Typed Erasure

module Erasure.LogicalRelation.Conversion
  {k} {Δ : Con Term k} (⊢Δ : ⊢ Δ)
  (restrictions : Restrictions Erasure)
  {{eqrel : EqRelSet Erasure}}
  where

open EqRelSet {{...}}

open import Erasure.LogicalRelation ⊢Δ restrictions
import Erasure.Target as T

open import Definition.LogicalRelation Erasure
open import Definition.LogicalRelation.Irrelevance Erasure
open import Definition.LogicalRelation.Fundamental.Reducibility Erasure
open import Definition.LogicalRelation.ShapeView Erasure
open import Definition.LogicalRelation.Properties.Conversion Erasure
open import Definition.LogicalRelation.Properties.Escape Erasure
open import Definition.LogicalRelation.Substitution Erasure
open import Definition.LogicalRelation.Substitution.Properties Erasure
import Definition.LogicalRelation.Substitution.Irrelevance Erasure as IS

open import Definition.Modality.Instances.Erasure.Modality restrictions
open import Definition.Mode ErasureModality
open import Definition.Untyped.Properties Erasure
import Definition.Untyped.BindingType Erasure as BT

open import Definition.Typed.Consequences.Injectivity Erasure
open import Definition.Typed.Consequences.Substitution Erasure
open import Definition.Typed.Reduction Erasure
open import Definition.Typed.RedSteps Erasure
open import Definition.Typed.Weakening Erasure

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    A B t : Term n
    v : T.Term n
    p : Erasure
    m : Mode

-- Conversion of logical relation for erasure using ShapeView
-- If t ® v ∷ A and Δ ⊩ A ≡ B then t ® v ∷ B

convTermʳ′ : ∀ {l l′} p
           → ([A] : Δ ⊩⟨ l ⟩ A)
             ([B] : Δ ⊩⟨ l′ ⟩ B)
           → Δ ⊢ A ≡ B
           → ShapeView Δ l l′ A B [A] [B]
           → t ®⟨ l ⟩ v ∷ A ◂ p / [A]
           → t ®⟨ l′ ⟩ v ∷ B ◂ p / [B]
convTermʳ′ 𝟘 = _
convTermʳ′ ω _ _ A≡B (Uᵥ UA UB) t®v = t®v
convTermʳ′ ω _ _ A≡B (ℕᵥ ℕA ℕB) t®v = t®v
convTermʳ′ ω _ _ A≡B (Unitᵥ UnitA UnitB) t®v = t®v
convTermʳ′
  ω [A] [B] A≡B
  (Bᵥ (BΠ 𝟘 q) BΠ! (Bᵣ F G [ _ , _ , A⇒Π ] ⊢F ⊢G A≡A [F] [G] G-ext)
     (Bᵣ F₁ G₁ [ _ , _ , B⇒Π₁ ] ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
     (BT.Π≋Π PE.refl PE.refl))
  t®v [a]′ =
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
  in  convTermʳ′ _ ([G] id ⊢Δ [a]) ([G]₁ id ⊢Δ [a]′) G[a]≡G₁[a] SV t®v′
convTermʳ′
  ω [A] [B] A≡B
  (Bᵥ (BΠ ω q) BΠ! (Bᵣ F G [ _ , _ , A⇒Π ] ⊢F ⊢G A≡A [F] [G] G-ext)
     (Bᵣ F₁ G₁ [ _ , _ , B⇒Π₁ ] ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
     (BT.Π≋Π PE.refl PE.refl))
  t®v [a]′ a®w′ =
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
      a®w = convTermʳ′ _ ([F]₁ id ⊢Δ) ([F] id ⊢Δ) F₁≡F SV a®w′
      t®v′ = t®v [a] a®w
      SV′ = goodCases ([G] id ⊢Δ [a]) ([G]₁ id ⊢Δ [a]′) [Ga≡G₁a]
  in  convTermʳ′ _ ([G] id ⊢Δ [a]) ([G]₁ id ⊢Δ [a]′) G[a]≡G₁[a] SV′ t®v′
convTermʳ′
  ω [A] [B] A≡B
  (Bᵥ (BΣ _ p _) BΣ! (Bᵣ F G [ _ , _ , A⇒Σ ] ⊢F ⊢G A≡A [F] [G] G-ext)
     (Bᵣ F₁ G₁ [ _ , _ , B⇒Σ₁ ] ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
     (BT.Σ≋Σ PE.refl))
  (t₁ , t₂ , t⇒t′ , [t₁] , v₂ , t₂®v₂ , extra) =
  let Σ≡Σ₁ = reduction′ A⇒Σ B⇒Σ₁ ΠΣₙ ΠΣₙ A≡B
      F≡F₁ , G≡G₁ , _ = Σ-injectivity Σ≡Σ₁
      [F]′ , [F₁]′ , [F≡F₁]′ = reducibleEq F≡F₁
      [F≡F₁] = irrelevanceEq″ (PE.sym (wk-id F)) (PE.sym (wk-id F₁))
                              [F]′ ([F] id ⊢Δ) [F≡F₁]′
      F≡F₁′ = PE.subst₂ (Δ ⊢_≡_) (PE.sym (wk-id F)) (PE.sym (wk-id F₁)) F≡F₁
      [t₁]′ = convTerm₁ ([F] id ⊢Δ) ([F]₁ id ⊢Δ) [F≡F₁] [t₁]
      G≡G₁′ = wkEq (lift id) (⊢Δ ∙ escape ([F] id ⊢Δ)) G≡G₁
      G[t₁]≡G₁[t₁] = substTypeEq G≡G₁′ (refl (escapeTerm ([F] id ⊢Δ) [t₁]))
      [Gt₁]′ , [G₁t₁]′ , [Gt₁≡G₁t₁]′ = reducibleEq G[t₁]≡G₁[t₁]
      [Gt₁≡G₁t₁] = irrelevanceEq [Gt₁]′ ([G] id ⊢Δ [t₁]) [Gt₁≡G₁t₁]′
      t⇒t″ = conv* t⇒t′ Σ≡Σ₁
      SV₂ = goodCases ([G] id ⊢Δ [t₁]) ([G]₁ id ⊢Δ [t₁]′) [Gt₁≡G₁t₁]
      t₂®v₂′ = convTermʳ′ _ ([G] id ⊢Δ [t₁]) ([G]₁ id ⊢Δ [t₁]′)
                 G[t₁]≡G₁[t₁] SV₂ t₂®v₂
  in  t₁ , t₂ , t⇒t″ , [t₁]′ , v₂ , t₂®v₂′ ,
      (case Σ-®-view extra of λ where
        (𝟘 v⇒v′)          → v⇒v′
        (ω v₁ v⇒v′ t₁®v₁) →
          let SV₁    = goodCases ([F] id ⊢Δ) ([F]₁ id ⊢Δ) [F≡F₁]
              t₁®v₁′ = convTermʳ′ p ([F] id ⊢Δ) ([F]₁ id ⊢Δ)
                         F≡F₁′ SV₁ t₁®v₁
          in v₁ , v⇒v′ , t₁®v₁′)
convTermʳ′ ω (emb 0<1 [A]) [B] A≡B (emb⁰¹ SV) t®v =
  convTermʳ′ _ [A] [B] A≡B SV t®v
convTermʳ′ ω [A] (emb 0<1 [B]) A≡B (emb¹⁰ SV) t®v =
  convTermʳ′ _ [A] [B] A≡B SV t®v
-- Impossible cases
convTermʳ′ ω _ _ _ (Emptyᵥ _ _) ()
convTermʳ′ ω _ _ _ (ne _ _) ()
convTermʳ′ ω _ _ _ (Bᵥ BΣ! BΠ! _ _ ())
convTermʳ′ ω _ _ _ (Bᵥ BΠ! BΣ! _ _ ())

-- Conversion of logical relation for erasure
-- If t ® v ∷ A and Δ ⊢ A ≡ B then t ® v ∷ B

convTermʳ : ∀ {l l′ A B t v} p
          → ([A] : Δ ⊩⟨ l ⟩ A)
            ([B] : Δ ⊩⟨ l′ ⟩ B)
          → Δ ⊢ A ≡ B
          → t ®⟨ l ⟩ v ∷ A ◂ p / [A]
          → t ®⟨ l′ ⟩ v ∷ B ◂ p / [B]
convTermʳ p [A] [B] A≡B t®v =
  let [A]′ , [B]′ , [A≡B]′ = reducibleEq A≡B
      [A≡B] = irrelevanceEq [A]′ [A] [A≡B]′
  in convTermʳ′ p [A] [B] A≡B (goodCases [A] [B] [A≡B]) t®v

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
  in  convTermʳ ⌜ m ⌝ [σA] [σB] σA≡σB t®v
