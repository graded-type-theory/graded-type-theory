------------------------------------------------------------------------
-- "Equational" reasoning combinators for _⊢_⇒*_∷_
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Reasoning.Reduction
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Typed R
open import Definition.Typed.Consequences.Reduction R
import Definition.Typed.Reasoning.Reduction.Primitive
open import Definition.Typed.RedSteps R
open import Definition.Untyped M hiding (_∷_)

import Tools.PropositionalEquality as PE

open Definition.Typed.Reasoning.Reduction.Primitive R public
  hiding (finally-⇒; finally-⇒≡; step-⇐; finally-⇐; finally-⇐≡)

private variable
  A t u v : Term _
  Γ       : Con Term _

------------------------------------------------------------------------
-- Combinators for left-to-right reductions

infix -1 finally-⇒ finally-⇒≡

opaque

  -- The reflexivity proof requires one to prove that the term is
  -- well-formed. In a non-empty chain of reasoning steps one can
  -- instead end with the following combinator.

  finally-⇒ : ∀ t u → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ⇒* u ∷ A
  finally-⇒ _ _ t⇒u = redMany t⇒u

  syntax finally-⇒ t u t⇒u = t ⇒⟨ t⇒u ⟩∎ u ∎

opaque

  -- A variant of finally-⇒ that makes it possible to end the chain of
  -- reasoning steps with a propositional equality, without the use of
  -- _∎⟨_⟩⇒.

  finally-⇒≡ : ∀ t → u PE.≡ v → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ⇒* v ∷ A
  finally-⇒≡ _ PE.refl t⇒u = redMany t⇒u

  syntax finally-⇒≡ t u≡v t⇒u = t ⇒⟨ t⇒u ⟩∎≡ u≡v

------------------------------------------------------------------------
-- Combinators for right-to-left reductions

infix  -1 finally-⇐
infixr -2 step-⇐ finally-⇐≡

opaque

  -- A single step.

  step-⇐ :
    ∀ v → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ u ⇒ v ∷ A → Γ ⊢ t ⇒* v ∷ A
  step-⇐ _ t⇒u u⇒v = t⇒u ⇨∷* redMany u⇒v

  syntax step-⇐ v t⇒u u⇒v = v ⇐⟨ u⇒v ⟩ t⇒u

opaque

  -- The reflexivity proof requires one to prove that the term is
  -- well-formed. In a non-empty chain of reasoning steps one can
  -- instead end with the following combinator.

  finally-⇐ : ∀ u t → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ⇒* u ∷ A
  finally-⇐ _ _ t⇒u = redMany t⇒u

  syntax finally-⇐ u t t⇒u = u ⇐⟨ t⇒u ⟩∎ t ∎

opaque

  -- A variant of finally-⇐ that makes it possible to end the chain of
  -- reasoning steps with a propositional equality, without the use of
  -- _∎⟨_⟩⇒.

  finally-⇐≡ : ∀ v → u PE.≡ t → Γ ⊢ v ⇒ u ∷ A → Γ ⊢ v ⇒* t ∷ A
  finally-⇐≡ _ PE.refl t⇒u = redMany t⇒u

  syntax finally-⇐≡ v u≡t v⇒u = v ⇐⟨ v⇒u ⟩∎≡ u≡t
