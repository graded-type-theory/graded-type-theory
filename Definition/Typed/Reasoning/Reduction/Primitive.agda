------------------------------------------------------------------------
-- A variant of Definition.Typed.Reasoning.Reduction with fewer
-- dependencies
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Reasoning.Reduction.Primitive
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Typed R
open import Definition.Typed.RedSteps R
open import Definition.Untyped M hiding (_∷_)

open import Tools.Function
import Tools.PropositionalEquality as PE

private variable
  A B u v : Term _
  Γ       : Con Term _

infix  -1 _∎⟨_⟩⇒ finally-⇒* finally-⇒ finally-⇒*≡ finally-⇒≡
infixr -2 step-⇒ step-⇒* step-≡ step-≡˘ _≡⟨⟩⇒_
          step-⇒-conv step-⇒-≡ step-⇒*-conv step-⇒*-≡

-- A single step.

step-⇒ : ∀ t → Γ ⊢ u ⇒* v ∷ A → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ⇒* v ∷ A
step-⇒ _ = flip _⇨_

syntax step-⇒ t u⇒v t⇒u = t ⇒⟨ t⇒u ⟩ u⇒v

{-# INLINE step-⇒ #-}

-- Multiple steps.

step-⇒* : ∀ t → Γ ⊢ u ⇒* v ∷ A → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ⇒* v ∷ A
step-⇒* _ = flip _⇨∷*_

syntax step-⇒* t u⇒v t⇒u = t ⇒*⟨ t⇒u ⟩ u⇒v

{-# INLINE step-⇒* #-}

-- A reasoning step that uses propositional equality.

step-≡ : ∀ t → Γ ⊢ u ⇒* v ∷ A → t PE.≡ u → Γ ⊢ t ⇒* v ∷ A
step-≡ _ u⇒v PE.refl = u⇒v

syntax step-≡ t u⇒v t≡u = t ≡⟨ t≡u ⟩⇒ u⇒v

-- A reasoning step that uses propositional equality, combined with
-- symmetry.

step-≡˘ : ∀ t → Γ ⊢ u ⇒* v ∷ A → u PE.≡ t → Γ ⊢ t ⇒* v ∷ A
step-≡˘ _ u⇒v PE.refl = u⇒v

syntax step-≡˘ t u⇒v u≡t = t ≡˘⟨ u≡t ⟩⇒ u⇒v

-- A reasoning step that uses (Agda's) definitional equality.

_≡⟨⟩⇒_ : ∀ t → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ⇒* u ∷ A
_ ≡⟨⟩⇒ t⇒u = t⇒u

{-# INLINE _≡⟨⟩⇒_ #-}

opaque

  -- A reasoning step combined with conversion.

  step-⇒-conv :
    ∀ t → Γ ⊢ u ⇒* v ∷ B → Γ ⊢ t ⇒ u ∷ B → Γ ⊢ A ≡ B → Γ ⊢ t ⇒* v ∷ A
  step-⇒-conv _ u⇒v t⇒u A≡B = conv* (t⇒u ⇨ u⇒v) (sym A≡B)

  syntax step-⇒-conv t u⇒v t⇒u A≡B = t ⇒⟨ t⇒u ⟩ ⟨ A≡B ⟩ u⇒v

opaque

  -- A reasoning step combined with conversion using propositional
  -- equality.

  step-⇒-≡ :
    ∀ t → Γ ⊢ u ⇒* v ∷ B → Γ ⊢ t ⇒ u ∷ B → A PE.≡ B → Γ ⊢ t ⇒* v ∷ A
  step-⇒-≡ _ u⇒v t⇒u PE.refl = t⇒u ⇨ u⇒v

  syntax step-⇒-≡ t u⇒v t⇒u A≡B = t ⇒⟨ t⇒u ⟩ ≡⟨ A≡B ⟩ u⇒v

opaque

  -- A reasoning step combined with conversion.

  step-⇒*-conv :
    ∀ t → Γ ⊢ u ⇒* v ∷ B → Γ ⊢ t ⇒* u ∷ B → Γ ⊢ A ≡ B → Γ ⊢ t ⇒* v ∷ A
  step-⇒*-conv _ u⇒v t⇒u A≡B = conv* (t⇒u ⇨∷* u⇒v) (sym A≡B)

  syntax step-⇒*-conv t u⇒v t⇒u A≡B = t ⇒*⟨ t⇒u ⟩ ⟨ A≡B ⟩ u⇒v

opaque

  -- A reasoning step combined with conversion using propositional
  -- equality.

  step-⇒*-≡ :
    ∀ t → Γ ⊢ u ⇒* v ∷ B → Γ ⊢ t ⇒* u ∷ B → A PE.≡ B → Γ ⊢ t ⇒* v ∷ A
  step-⇒*-≡ _ u⇒v t⇒u PE.refl = t⇒u ⇨∷* u⇒v

  syntax step-⇒*-≡ t u⇒v t⇒u A≡B = t ⇒*⟨ t⇒u ⟩ ≡⟨ A≡B ⟩ u⇒v

-- Reflexivity.

_∎⟨_⟩⇒ : ∀ t → Γ ⊢ t ∷ A → Γ ⊢ t ⇒* t ∷ A
_ ∎⟨ ⊢t ⟩⇒ = id ⊢t

{-# INLINE _∎⟨_⟩⇒ #-}

-- The reflexivity proof requires one to prove that the term is
-- well-formed. In a non-empty chain of reasoning steps one can
-- instead end with the following combinator.

finally-⇒* : ∀ t u → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ⇒* u ∷ A
finally-⇒* _ _ t⇒u = t⇒u

syntax finally-⇒* t u t⇒u = t ⇒*⟨ t⇒u ⟩∎ u ∎

{-# INLINE finally-⇒* #-}

-- A variant of finally-⇒*.

finally-⇒ : ∀ t u → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ u ∷ A → Γ ⊢ t ⇒* u ∷ A
finally-⇒ _ _ t⇒u ⊢u = t⇒u ⇨ id ⊢u

syntax finally-⇒ t u t⇒u ⊢u = t ⇒⟨ t⇒u , ⊢u ⟩∎ u ∎

{-# INLINE finally-⇒ #-}

-- A variant of finally-⇒* that makes it possible to end the chain of
-- reasoning steps with a propositional equality, without the use of
-- _∎⟨_⟩⇒.

finally-⇒*≡ : ∀ t → u PE.≡ v → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ⇒* v ∷ A
finally-⇒*≡ _ PE.refl t⇒u = t⇒u

syntax finally-⇒*≡ t u≡v t⇒u = t ⇒*⟨ t⇒u ⟩∎≡ u≡v

-- A variant of finally-⇒*≡.

finally-⇒≡ : ∀ t → u PE.≡ v → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ u ∷ A → Γ ⊢ t ⇒* v ∷ A
finally-⇒≡ _ PE.refl = finally-⇒ _ _

syntax finally-⇒≡ t u≡v t⇒u = t ⇒⟨ t⇒u ⟩∎≡ u≡v
