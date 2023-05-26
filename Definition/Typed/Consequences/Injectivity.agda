------------------------------------------------------------------------
-- Term constructors are injective.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions

module Definition.Typed.Consequences.Injectivity
  {a} {M : Set a}
  (R : Type-restrictions M)
  where

open import Definition.Untyped M hiding (wk; _∷_)
import Definition.Untyped M as U
open import Definition.Untyped.Properties M

open import Definition.Typed R
open import Definition.Typed.Weakening R
open import Definition.Typed.Properties R
open import Definition.Typed.EqRelInstance R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Fundamental.Reducibility R

open import Tools.Fin
open import Tools.Function
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
             × W PE.≡ W′
injectivity′
  W W′ (noemb (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _))
  (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  case B-PE-injectivity W W (whnfRed* (red D) ⟦ W ⟧ₙ) of λ {
    (PE.refl , PE.refl , _) →
  case B-PE-injectivity W′ W (whnfRed* D′ ⟦ W′ ⟧ₙ) of λ {
    (PE.refl , PE.refl , PE.refl) →
  let ⊢Γ = wf ⊢F
      [F]₁ = [F] id ⊢Γ
      [F]′ = irrelevance′ (wk-id _) [F]₁
      [x∷F] = neuTerm ([F] (step id) (⊢Γ ∙ ⊢F)) (var x0) (var (⊢Γ ∙ ⊢F) here)
                      (refl (var (⊢Γ ∙ ⊢F) here))
      [G]₁ = [G] (step id) (⊢Γ ∙ ⊢F) [x∷F]
      [G]′ = PE.subst (_ ∙ _ ⊩⟨ _ ⟩_) (wkSingleSubstId _) [G]₁
      [F≡H]₁ = [F≡F′] id ⊢Γ
      [F≡H]′ = irrelevanceEq″ (wk-id _) (wk-id _) [F]₁ [F]′ [F≡H]₁
      [G≡E]₁ = [G≡G′] (step id) (⊢Γ ∙ ⊢F) [x∷F]
      [G≡E]′ = irrelevanceEqLift″
                 (wkSingleSubstId _) (wkSingleSubstId _) PE.refl
                 [G]₁ [G]′ [G≡E]₁
  in escapeEq [F]′ [F≡H]′ , escapeEq [G]′ [G≡E]′ , PE.refl }}
injectivity′ W W′ (emb 0<1 x) [WFG≡WHE] = injectivity′ W W′ x [WFG≡WHE]

-- Injectivity of W
B-injectivity :
  ∀ {F G H E} W W′ →
  Γ ⊢ ⟦ W ⟧ F ▹ G ≡ ⟦ W′ ⟧ H ▹ E → Γ ⊢ F ≡ H × Γ ∙ F ⊢ G ≡ E × W PE.≡ W′
B-injectivity W W′ ⊢WFG≡WHE =
  let [WFG] , _ , [WFG≡WHE] = reducibleEq ⊢WFG≡WHE
  in  injectivity′ W W′ (B-elim W [WFG])
                   (irrelevanceEq [WFG] (B-intr W (B-elim W [WFG])) [WFG≡WHE])

injectivity : ∀ {F G H E} → Γ ⊢ Π p , q ▷ F ▹ G ≡ Π p′ , q′ ▷ H ▹ E
            → Γ ⊢ F ≡ H × Γ ∙ F ⊢ G ≡ E × p ≈ p′ × q ≈ q′
injectivity x with B-injectivity BΠ! BΠ! x
... | F≡H , G≡E , PE.refl = F≡H , G≡E , PE.refl , PE.refl

Σ-injectivity :
  ∀ {m m′ F G H E} →
  Γ ⊢ Σ⟨ m ⟩ p , q ▷ F ▹ G ≡ Σ⟨ m′ ⟩ p′ , q′ ▷ H ▹ E →
  Γ ⊢ F ≡ H × Γ ∙ F ⊢ G ≡ E × p ≈ p′ × q ≈ q′ × m PE.≡ m′
Σ-injectivity x with B-injectivity BΣ! BΣ! x
... | F≡H , G≡E , PE.refl =
  F≡H , G≡E , PE.refl , PE.refl , PE.refl

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
