------------------------------------------------------------------------
-- Term constructors are injective.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.Injectivity
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M hiding (wk)
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
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    A₁ A₂ F F′ G G′ t₁ t₂ u₁ u₂ : Term _
    p p′ q q′ : M
    b b′ : BinderMode
    l : TypeLevel
    s s′ : Strength

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
      [x∷F] = neuTerm ([F] (step id) (⊢Γ ∙ ⊢F)) (var x0) (var₀ ⊢F)
                (refl (var₀ ⊢F))
      [G]₁ = [G] (step id) (⊢Γ ∙ ⊢F) [x∷F]
      [G]′ = PE.subst (_ ∙ _ ⊩⟨ _ ⟩_) (wkSingleSubstId _) [G]₁
      [F≡H]₁ = [F≡F′] id ⊢Γ
      [F≡H]′ = irrelevanceEq″ (wk-id _) (wk-id _) [F]₁ [F]′ [F≡H]₁
      [G≡E]₁ = [G≡G′] (step id) (⊢Γ ∙ ⊢F) [x∷F]
      [G≡E]′ = irrelevanceEq″
                 (wkSingleSubstId _) (wkSingleSubstId _)
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
            → Γ ⊢ F ≡ H × Γ ∙ F ⊢ G ≡ E × p PE.≡ p′ × q PE.≡ q′
injectivity x with B-injectivity BΠ! BΠ! x
... | F≡H , G≡E , PE.refl = F≡H , G≡E , PE.refl , PE.refl

Σ-injectivity :
  ∀ {m m′ F G H E} →
  Γ ⊢ Σ⟨ m ⟩ p , q ▷ F ▹ G ≡ Σ⟨ m′ ⟩ p′ , q′ ▷ H ▹ E →
  Γ ⊢ F ≡ H × Γ ∙ F ⊢ G ≡ E × p PE.≡ p′ × q PE.≡ q′ × m PE.≡ m′
Σ-injectivity x with B-injectivity BΣ! BΣ! x
... | F≡H , G≡E , PE.refl =
  F≡H , G≡E , PE.refl , PE.refl , PE.refl

ΠΣ-injectivity :
  Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ≡ ΠΣ⟨ b′ ⟩ p′ , q′ ▷ F′ ▹ G′ →
  Γ ⊢ F ≡ F′ × Γ ∙ F ⊢ G ≡ G′ × p PE.≡ p′ × q PE.≡ q′ × b PE.≡ b′
ΠΣ-injectivity {b = BMΠ} {b′ = BMΠ} Π≡Π =
  case injectivity Π≡Π of λ {
    (F≡F′ , G≡G′ , p≡p′ , q≡q′) →
  F≡F′ , G≡G′ , p≡p′ , q≡q′ , PE.refl }
ΠΣ-injectivity {b = BMΣ _} {b′ = BMΣ _} Σ≡Σ =
  case Σ-injectivity Σ≡Σ of λ {
    (F≡F′ , G≡G′ , p≡p′ , q≡q′ , PE.refl) →
  F≡F′ , G≡G′ , p≡p′ , q≡q′ , PE.refl }
ΠΣ-injectivity {b = BMΠ} {b′ = BMΣ _} Π≡Σ =
  case B-injectivity (BΠ _ _) (BΣ _ _ _) Π≡Σ of λ {
    (_ , _ , ()) }
ΠΣ-injectivity {b = BMΣ _} {b′ = BMΠ} Σ≡Π =
  case B-injectivity (BΣ _ _ _) (BΠ _ _) Σ≡Π of λ {
    (_ , _ , ()) }

opaque

  -- Injectivity of Id.

  Id-injectivity :
    Γ ⊢ Id A₁ t₁ u₁ ≡ Id A₂ t₂ u₂ →
    (Γ ⊢ A₁ ≡ A₂) × Γ ⊢ t₁ ≡ t₂ ∷ A₁ × Γ ⊢ u₁ ≡ u₂ ∷ A₁
  Id-injectivity Id≡Id =
    case reducibleEq Id≡Id of λ {
      (⊩Id , _ , ⊩Id≡Id) →
    helper (Id-elim ⊩Id)
      (irrelevanceEq ⊩Id (Id-intr (Id-elim ⊩Id)) ⊩Id≡Id) }
    where
    helper :
      ∀ ⊩Id →
      Γ ⊩⟨ l ⟩ Id A₁ t₁ u₁ ≡ Id A₂ t₂ u₂ / Id-intr ⊩Id →
      (Γ ⊢ A₁ ≡ A₂) × Γ ⊢ t₁ ≡ t₂ ∷ A₁ × Γ ⊢ u₁ ≡ u₂ ∷ A₁
    helper (emb 0<1 ⊩Id) ⊩Id≡Id = helper ⊩Id ⊩Id≡Id
    helper (noemb ⊩Id)   ⊩Id≡Id =
      case whnfRed* (red (_⊩ₗId_.⇒*Id ⊩Id)) Idₙ of λ {
        PE.refl →
      case whnfRed* (red (_⊩ₗId_≡_/_.⇒*Id′ ⊩Id≡Id)) Idₙ of λ {
        PE.refl →
        escapeEq (_⊩ₗId_.⊩Ty ⊩Id) (_⊩ₗId_≡_/_.Ty≡Ty′ ⊩Id≡Id)
      , escapeTermEq (_⊩ₗId_.⊩Ty ⊩Id) (_⊩ₗId_≡_/_.lhs≡lhs′ ⊩Id≡Id)
      , escapeTermEq (_⊩ₗId_.⊩Ty ⊩Id) (_⊩ₗId_≡_/_.rhs≡rhs′ ⊩Id≡Id) }}

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

-- Injectivity of Unit

Unit-injectivity′ : ∀ {l}
                  → ([Unit] : Γ ⊩⟨ l ⟩Unit⟨ s ⟩ Unit s)
                  → Γ ⊩⟨ l ⟩ Unit s ≡ Unit s′ / Unit-intr [Unit]
                  → s PE.≡ s′
Unit-injectivity′ (noemb (Unitₜ ⇒*-Unit ok)) D
  with whnfRed* D Unitₙ
... | PE.refl = PE.refl
Unit-injectivity′ (emb 0<1 [Unit]) [Unit≡Unit] =
  Unit-injectivity′ [Unit] [Unit≡Unit]

Unit-injectivity : Γ ⊢ Unit s ≡ Unit s′
                 → s PE.≡ s′
Unit-injectivity x =
  let [Unit] , _ , [Unit≡Unit] = reducibleEq x
      [Unit]′ = Unit-intr (Unit-elim [Unit])
      [Unit≡Unit]′ = irrelevanceEq [Unit] [Unit]′ [Unit≡Unit]
  in  Unit-injectivity′ (Unit-elim [Unit]) [Unit≡Unit]′
