module Definition.Typed.Consequences.Injectivity
  {a} (M : Set a) where

open import Definition.Untyped M hiding (wk; _∷_)
import Definition.Untyped M as U
import Definition.Untyped.BindingType M as BT
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
open import Tools.PropositionalEquality as PE using (_≈_)

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
             × W BT.≋ W′
injectivity′ W W′ (noemb (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (B₌ F′ G′ W″ D′ W≋W″ A≡B [F≡F′] [G≡G′]) =
  let F≡F₁ , G≡G₁ , _    = B-PE-injectivity W W (whnfRed* (red D) ⟦ W ⟧ₙ)
      H≡F′ , E≡G′ , W′≡W″ = B-PE-injectivity W′ W″ (whnfRed* D′ ⟦ W′ ⟧ₙ)
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
  in escapeEq [F]′ [F≡H]′ , escapeEq [G]′ [G≡E]′ , PE.subst (λ x → W BT.≋ x) (PE.sym W′≡W″) W≋W″
injectivity′ W W′ (emb 0<1 x) [WFG≡WHE] = injectivity′ W W′ x [WFG≡WHE]

-- Injectivity of W
B-injectivity : ∀ {F G H E} W W′ → Γ ⊢ ⟦ W ⟧ F ▹ G ≡ ⟦ W′ ⟧ H ▹ E → Γ ⊢ F ≡ H × Γ ∙ F ⊢ G ≡ E × W BT.≋ W′
B-injectivity W W′ ⊢WFG≡WHE =
  let [WFG] , _ , [WFG≡WHE] = reducibleEq ⊢WFG≡WHE
  in  injectivity′ W W′ (B-elim W [WFG])
                   (irrelevanceEq [WFG] (B-intr W (B-elim W [WFG])) [WFG≡WHE])

injectivity : ∀ {F G H E} → Γ ⊢ Π p , q ▷ F ▹ G ≡ Π p′ , q′ ▷ H ▹ E
            → Γ ⊢ F ≡ H × Γ ∙ F ⊢ G ≡ E × p ≈ p′ × q ≈ q′
injectivity x with B-injectivity BΠ! BΠ! x
... | F≡H , G≡E , BT.Π≋Π p≈p′ q≈q′ = F≡H , G≡E , p≈p′ , q≈q′

Σ-injectivity : ∀ {m m′ F G H E} → Γ ⊢ Σ⟨ m ⟩ q ▷ F ▹ G ≡ Σ⟨ m′ ⟩ q′ ▷ H ▹ E
              → Γ ⊢ F ≡ H × Γ ∙ F ⊢ G ≡ E × q ≈ q′ × m PE.≡ m′
Σ-injectivity x with B-injectivity BΣ! BΣ! x
... | F≡H , G≡E , BT.Σ≋Σ q≈q′ = F≡H , G≡E , q≈q′ , PE.refl

-- Injectivity of suc

suc-injectivity′ : ∀ {l t u A}
                 → ([ℕ] : Γ ⊩⟨ l ⟩ℕ A)
                 → Γ ⊩⟨ l ⟩ suc t ≡ suc u ∷ A / ℕ-intr [ℕ]
                 → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / ℕ-intr [ℕ]
suc-injectivity′ (noemb [ ⊢A , ⊢B , D ]) (ℕₜ₌ k k′ d d′ k≡k′ prop)
  with whnfRed*Term (redₜ d) sucₙ | whnfRed*Term (redₜ d′) sucₙ
suc-injectivity′ (noemb [ ⊢A , ⊢B , D ]) (ℕₜ₌ _ _ d d′ k≡k′ (sucᵣ x)) | PE.refl | PE.refl = x
suc-injectivity′ (emb 0<1 [ℕ]) x = suc-injectivity′ [ℕ] x

suc-injectivity : ∀ {t u}
                → Γ ⊢ suc t ≡ suc u ∷ ℕ
                → Γ ⊢ t ≡ u ∷ ℕ
suc-injectivity ⊢suct≡sucu =
  let [ℕ] , [suct≡sucu] = reducibleEqTerm ⊢suct≡sucu
      [ℕ]′ = ℕ-intr (ℕ-elim [ℕ])
      [suct≡sucu]′ = irrelevanceEqTerm [ℕ] [ℕ]′ [suct≡sucu]
      [t≡u] = suc-injectivity′ (ℕ-elim [ℕ]) [suct≡sucu]′
  in  escapeTermEq [ℕ]′ [t≡u]
