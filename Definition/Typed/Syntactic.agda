------------------------------------------------------------------------
-- Syntactic validity of the typing and reduction relations.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Syntactic
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.Typed.Inversion.Primitive R
open import Definition.Typed.Properties.Reduction R
import Definition.Typed.Well-formed R as W

open import Tools.Function
open import Tools.Product

open W public
  using ()
  renaming
    (wf-∷∈  to syntacticVar;
     wf-⊢∷  to syntacticTerm;
     wf-⊢≡  to syntacticEq;
     wf-⊢≡∷ to syntacticEqTerm)

private variable
  Γ       : Con Term _
  A B t u : Term _
  p q     : M
  s       : Strength

opaque

  -- A well-formedness lemma for _⊢_⇒*_.

  syntacticRed : Γ ⊢ A ⇒* B → Γ ⊢ A × Γ ⊢ B
  syntacticRed = syntacticEq ∘→ subset*

opaque

  -- The relation _⊢_⇒*_ is contained in _⊢_:⇒*:_.

  ⇒*→:⇒*: : Γ ⊢ A ⇒* B → Γ ⊢ A :⇒*: B
  ⇒*→:⇒*: A⇒*B =
    case syntacticRed A⇒*B of λ
      (⊢A , ⊢B) →
    [ ⊢A , ⊢B , A⇒*B ]

opaque

  -- A well-formedness lemma for _⊢_⇒*_∷_.

  syntacticRedTerm : Γ ⊢ t ⇒* u ∷ A → (Γ ⊢ A) × Γ ⊢ t ∷ A × Γ ⊢ u ∷ A
  syntacticRedTerm = syntacticEqTerm ∘→ subset*Term

opaque

  -- The relation _⊢_⇒*_∷_ is contained in _⊢_:⇒*:_∷_.

  ⇒*∷→:⇒*:∷ : Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t :⇒*: u ∷ A
  ⇒*∷→:⇒*:∷ t⇒*u =
    case syntacticRedTerm t⇒*u of λ
      (_ , ⊢t , ⊢u) →
    [ ⊢t , ⊢u , t⇒*u ]

opaque

  -- Syntactic validity of Π-types.

  syntacticΠ : Γ ⊢ Π p , q ▷ A ▹ B → Γ ⊢ A × Γ ∙ A ⊢ B
  syntacticΠ ⊢ΠAB =
    let (⊢A , _) , (⊢B , _) , _ = inversion-ΠΣ-⊢ ⊢ΠAB in
    ⊢A , ⊢B

opaque

  -- Syntactic validity of Σ-types.

  syntacticΣ : Γ ⊢ Σ⟨ s ⟩ p , q ▷ A ▹ B → Γ ⊢ A × Γ ∙ A ⊢ B
  syntacticΣ ⊢ΣAB =
    let (⊢A , _) , (⊢B , _) , _ = inversion-ΠΣ-⊢ ⊢ΣAB in
    ⊢A , ⊢B
