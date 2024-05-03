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
open import Definition.Untyped M hiding (_∷_)

import Tools.PropositionalEquality as PE

open Definition.Typed.Reasoning.Reduction.Primitive R public
  hiding (finally-⇒; finally-⇒≡)

private variable
  A u v : Term _
  Γ     : Con Term _

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
