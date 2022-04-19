{-# OPTIONS --without-K --safe #-}

module Definition.Typed.Consequences.Injectivity (M : Set) where

open import Definition.Untyped M hiding (wk)
import Definition.Untyped M as U
open import Definition.Untyped.Properties M

open import Definition.Typed M
open import Definition.Typed.Weakening M
open import Definition.Typed.Properties M
open import Definition.Typed.EqRelInstance M
open import Definition.LogicalRelation M
open import Definition.LogicalRelation.Irrelevance M
open import Definition.LogicalRelation.ShapeView M
open import Definition.LogicalRelation.Properties M
open import Definition.LogicalRelation.Fundamental.Reducibility M

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    p p′ q q′ : M

-- Helper function of injectivity for specific reducible Π-types
injectivity′ : ∀ {F G H E l} W W′
               ([WFG] : Γ ⊩⟨ l ⟩B⟨ W ⟩ ⟦ W ⟧ F ▹ G)
             → Γ ⊩⟨ l ⟩ ⟦ W ⟧ F ▹ G ≡ ⟦ W′ ⟧ H ▹ E / B-intr W [WFG]
             → Γ ⊢ F ≡ H
             × Γ ∙ F ⊢ G ≡ E
             × (W PE.≡ W′)
injectivity′ W W′ (noemb (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  let F≡F₁ , G≡G₁ , _    = B-PE-injectivity W W (whnfRed* (red D) ⟦ W ⟧ₙ)
      H≡F′ , E≡G′ , W′≡W = B-PE-injectivity W′ W (whnfRed* D′ ⟦ W′ ⟧ₙ)
      ⊢Γ = wf ⊢F
      [F]₁ = [F] id ⊢Γ
      [F]′ = irrelevance′ (PE.trans (wk-id _) (PE.sym F≡F₁)) [F]₁
      [x∷F] = neuTerm ([F] (step id) (⊢Γ ∙ ⊢F)) (var x0) (var (⊢Γ ∙ ⊢F) here)
                      (refl (var (⊢Γ ∙ ⊢F) here))
      [G]₁ = [G] (step id) (⊢Γ ∙ ⊢F) [x∷F]
      [G]′ = PE.subst₂ (λ x y → _ ∙ y ⊩⟨ _ ⟩ x)
                       (PE.trans (wkSingleSubstId _) (PE.sym G≡G₁))
                       (PE.sym F≡F₁) [G]₁
      [F≡H]₁ = [F≡F′] id ⊢Γ
      [F≡H]′ = irrelevanceEq″ (PE.trans (wk-id _) (PE.sym F≡F₁))
                               (PE.trans (wk-id _) (PE.sym H≡F′))
                               [F]₁ [F]′ [F≡H]₁
      [G≡E]₁ = [G≡G′] (step id) (⊢Γ ∙ ⊢F) [x∷F]
      [G≡E]′ = irrelevanceEqLift″ (PE.trans (wkSingleSubstId _) (PE.sym G≡G₁))
                                   (PE.trans (wkSingleSubstId _) (PE.sym E≡G′))
                                   (PE.sym F≡F₁) [G]₁ [G]′ [G≡E]₁
  in escapeEq [F]′ [F≡H]′ , escapeEq [G]′ [G≡E]′ , PE.sym W′≡W
injectivity′ W W′ (emb 0<1 x) [WFG≡WHE] = injectivity′ W W′ x [WFG≡WHE]

-- Injectivity of W
B-injectivity : ∀ {F G H E} W W′ → Γ ⊢ ⟦ W ⟧ F ▹ G ≡ ⟦ W′ ⟧ H ▹ E → Γ ⊢ F ≡ H × Γ ∙ F ⊢ G ≡ E × W PE.≡ W′
B-injectivity W W′ ⊢WFG≡WHE =
  let [WFG] , _ , [WFG≡WHE] = reducibleEq ⊢WFG≡WHE
  in  injectivity′ W W′ (B-elim W [WFG])
                   (irrelevanceEq [WFG] (B-intr W (B-elim W [WFG])) [WFG≡WHE])

injectivity : ∀ {F G H E} → Γ ⊢ Π p , q ▷ F ▹ G ≡ Π p′ , q′ ▷ H ▹ E
            → Γ ⊢ F ≡ H × Γ ∙ F ⊢ G ≡ E × p PE.≡ p′ × q PE.≡ q′
injectivity x with B-injectivity BΠ! BΠ! x
... | F≡H , G≡E , PE.refl = F≡H , G≡E , PE.refl , PE.refl

Σ-injectivity : ∀ {m m′ F G H E} → Γ ⊢ Σ⟨ m ⟩ q ▷ F ▹ G ≡ Σ⟨ m′ ⟩ q′ ▷ H ▹ E → Γ ⊢ F ≡ H × Γ ∙ F ⊢ G ≡ E × q PE.≡ q′ × m PE.≡ m′
Σ-injectivity x with B-injectivity BΣ! BΣ! x
... | F≡H , G≡E , PE.refl = F≡H , G≡E , PE.refl , PE.refl
