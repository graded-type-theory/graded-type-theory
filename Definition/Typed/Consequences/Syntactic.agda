------------------------------------------------------------------------
-- Syntactic validity of the typing and reduction relations.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.Syntactic
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Fundamental.Reducibility R
open import Definition.LogicalRelation.Hidden R

open import Definition.Untyped M hiding (wk)
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Weakening R
open import Definition.Typed.Consequences.Injectivity R

open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ

private
  variable
    n : Nat
    Γ : Con Term n
    A B t u : Term n
    p q : M

opaque

  -- If two types are equal, then they are well-formed.

  syntacticEq : Γ ⊢ A ≡ B → Γ ⊢ A × Γ ⊢ B
  syntacticEq {Γ} {A} {B} =
    Γ ⊢ A ≡ B                          →⟨ reducible-⊩≡ ⟩
    (∃ λ l → Γ ⊩⟨ l ⟩ A ≡ B)           →⟨ Σ.map idᶠ wf-⊩≡ ⟩
    (∃ λ l → Γ ⊩⟨ l ⟩ A × Γ ⊩⟨ l ⟩ B)  →⟨ Σ.map escape-⊩ escape-⊩ ∘→ proj₂ ⟩
    Γ ⊢ A × Γ ⊢ B                      □

opaque

  -- If a term is well-typed, then its type is well-formed.

  syntacticTerm : Γ ⊢ t ∷ A → Γ ⊢ A
  syntacticTerm {Γ} {t} {A} =
    Γ ⊢ t ∷ A                 →⟨ reducible-⊩∷ ⟩
    (∃ λ l → Γ ⊩⟨ l ⟩ t ∷ A)  →⟨ Σ.map idᶠ wf-⊩∷ ⟩
    (∃ λ l → Γ ⊩⟨ l ⟩ A)      →⟨ escape-⊩ ∘→ proj₂ ⟩
    Γ ⊢ A                     □

opaque

  -- If two terms are equal at a given type, then they have that type,
  -- and the type is well-formed.

  syntacticEqTerm : Γ ⊢ t ≡ u ∷ A → (Γ ⊢ A) × Γ ⊢ t ∷ A × Γ ⊢ u ∷ A
  syntacticEqTerm {Γ} {t} {u} {A} =
    Γ ⊢ t ≡ u ∷ A                              →⟨ reducible-⊩≡∷ ⟩
    (∃ λ l → Γ ⊩⟨ l ⟩ t ≡ u ∷ A)               →⟨ Σ.map idᶠ wf-⊩≡∷ ⟩
    (∃ λ l → Γ ⊩⟨ l ⟩ t ∷ A × Γ ⊩⟨ l ⟩ u ∷ A)  →⟨ (λ (_ , ⊩t , ⊩u) → escape-⊩ (wf-⊩∷ ⊩t) , escape-⊩∷ ⊩t , escape-⊩∷ ⊩u) ⟩
    (Γ ⊢ A) × Γ ⊢ t ∷ A × Γ ⊢ u ∷ A            □

-- Syntactic validity of type reductions.
syntacticRed : ∀ {A B} → Γ ⊢ A ⇒* B → Γ ⊢ A × Γ ⊢ B
syntacticRed D = syntacticEq (subset* D)

opaque

  -- The relation _⊢_⇒*_ is contained in _⊢_:⇒*:_.

  ⇒*→:⇒*: : Γ ⊢ A ⇒* B → Γ ⊢ A :⇒*: B
  ⇒*→:⇒*: A⇒*B =
    case syntacticRed A⇒*B of λ
      (⊢A , ⊢B) →
    [ ⊢A , ⊢B , A⇒*B ]

-- Syntactic validity of term reductions.
syntacticRedTerm : ∀ {t u A} → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ A × (Γ ⊢ t ∷ A × Γ ⊢ u ∷ A)
syntacticRedTerm d = syntacticEqTerm (subset*Term d)

opaque

  -- The relation _⊢_⇒*_∷_ is contained in _⊢_:⇒*:_∷_.

  ⇒*∷→:⇒*:∷ : Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t :⇒*: u ∷ A
  ⇒*∷→:⇒*:∷ t⇒*u =
    case syntacticRedTerm t⇒*u of λ
      (_ , ⊢t , ⊢u) →
    [ ⊢t , ⊢u , t⇒*u ]

-- Syntactic validity of Π-types.
syntacticΠ : ∀ {F G} → Γ ⊢ Π p , q ▷ F ▹ G → Γ ⊢ F × Γ ∙ F ⊢ G
syntacticΠ ΠFG with injectivity (refl ΠFG)
syntacticΠ ΠFG | F≡F , G≡G , _ = proj₁ (syntacticEq F≡F) , proj₁ (syntacticEq G≡G)

syntacticΣ : ∀ {m F G} → Γ ⊢ Σ⟨ m ⟩ p , q ▷ F ▹ G → Γ ⊢ F × Γ ∙ F ⊢ G
syntacticΣ ΣFG with Σ-injectivity (refl ΣFG)
syntacticΣ ΣFG | F≡F , G≡G , _ = proj₁ (syntacticEq F≡F) , proj₁ (syntacticEq G≡G)

-- Syntactic validity of context lookup

syntacticVar : ∀ {x A} → x ∷ A ∈ Γ → ⊢ Γ → Γ ⊢ A
syntacticVar here (_ ∙ ⊢A) = wk₁ ⊢A ⊢A
syntacticVar (there x) (⊢Γ ∙ ⊢B) = wk₁ ⊢B (syntacticVar x ⊢Γ)
