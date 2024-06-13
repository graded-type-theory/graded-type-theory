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

open Type-restrictions R

open import Definition.Untyped M hiding (wk)
import Definition.Untyped M as U
open import Definition.Untyped.Neutral M type-variant

open import Definition.Typed R
open import Definition.Typed.Weakening R
open import Definition.Typed.Properties R
open import Definition.Typed.EqRelInstance R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Fundamental.Reducibility R
open import Definition.LogicalRelation.Substitution.Introductions R

open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    A₁ A₂ B₁ B₂ t₁ t₂ u₁ u₂ : Term _
    p₁ p₂ q₁ q₂ : M
    b₁ b₂ : BinderMode
    l : TypeLevel
    s₁ s₂ : Strength

opaque

  -- A kind of injectivity for Π and Σ.

  ΠΣ-injectivity :
    Γ ⊢ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ →
    Γ ⊢ A₁ ≡ A₂ × Γ ∙ A₁ ⊢ B₁ ≡ B₂ ×
    p₁ PE.≡ p₂ × q₁ PE.≡ q₂ × b₁ PE.≡ b₂
  ΠΣ-injectivity ΠΣ≡ΠΣ =
    case ⊩ΠΣ≡ΠΣ→ $ reducible-⊩≡ ΠΣ≡ΠΣ of λ
      (_ , b₁≡b₂ , p₁≡p₂ , q₁≡q₂ , A₁≡A₂ , B₁≡B₂) →
    escape-⊩≡ A₁≡A₂ , escape-⊩≡ B₁≡B₂ , p₁≡p₂ , q₁≡q₂ , b₁≡b₂

opaque

  -- A kind of injectivity for Π.

  injectivity :
    Γ ⊢ Π p₁ , q₁ ▷ A₁ ▹ B₁ ≡ Π p₂ , q₂ ▷ A₂ ▹ B₂ →
    Γ ⊢ A₁ ≡ A₂ × Γ ∙ A₁ ⊢ B₁ ≡ B₂ × p₁ PE.≡ p₂ × q₁ PE.≡ q₂
  injectivity Π≡Π =
    case ΠΣ-injectivity Π≡Π of λ
      (A₁≡A₂ , B₁≡B₂ , p₁≡p₂ , q₁≡q₂ , _) →
    A₁≡A₂ , B₁≡B₂ , p₁≡p₂ , q₁≡q₂

opaque

  -- A kind of injectivity for Σ.

  Σ-injectivity :
    Γ ⊢ Σ⟨ s₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≡ Σ⟨ s₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ →
    Γ ⊢ A₁ ≡ A₂ × Γ ∙ A₁ ⊢ B₁ ≡ B₂ ×
    p₁ PE.≡ p₂ × q₁ PE.≡ q₂ × s₁ PE.≡ s₂
  Σ-injectivity Σ≡Σ =
    case ΠΣ-injectivity Σ≡Σ of λ {
      (A₁≡A₂ , B₁≡B₂ , p₁≡p₂ , q₁≡q₂ , PE.refl) →
    A₁≡A₂ , B₁≡B₂ , p₁≡p₂ , q₁≡q₂ , PE.refl }

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

opaque

  -- Injectivity of suc.

  suc-injectivity :
    Γ ⊢ suc t₁ ≡ suc t₂ ∷ ℕ →
    Γ ⊢ t₁ ≡ t₂ ∷ ℕ
  suc-injectivity {Γ} {t₁} {t₂} =
    Γ ⊢ suc t₁ ≡ suc t₂ ∷ ℕ       →⟨ reducible-⊩≡∷ ⟩
    Γ ⊩⟨ ¹ ⟩ suc t₁ ≡ suc t₂ ∷ ℕ  ⇔⟨ ⊩suc≡suc∷ℕ⇔ ⟩→
    Γ ⊩⟨ ¹ ⟩ t₁ ≡ t₂ ∷ ℕ          →⟨ escape-⊩≡∷ ⟩
    Γ ⊢ t₁ ≡ t₂ ∷ ℕ               □

opaque

  -- Injectivity of Unit.

  Unit-injectivity :
    Γ ⊢ Unit s₁ ≡ Unit s₂ →
    s₁ PE.≡ s₂
  Unit-injectivity {Γ} {s₁} {s₂} =
    Γ ⊢ Unit s₁ ≡ Unit s₂               →⟨ reducible-⊩≡ ⟩
    Γ ⊩⟨ ¹ ⟩ Unit s₁ ≡ Unit s₂          ⇔⟨ ⊩Unit≡Unit⇔ ⟩→
    ⊢ Γ × Unit-allowed s₁ × s₁ PE.≡ s₂  →⟨ proj₂ ∘→ proj₂ ⟩
    s₁ PE.≡ s₂                          □
