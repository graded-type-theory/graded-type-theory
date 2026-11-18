------------------------------------------------------------------------
-- A variant of Definition.Typed.Reasoning.Term with fewer
-- dependencies
------------------------------------------------------------------------

open import Configuration-types
open import Graded.Modality

module Definition.Typed.Reasoning.Term.Primitive
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (TC : Type-configuration 𝕄)
  where

open import Definition.Typed TC
open import Definition.Untyped M

open import Tools.Function
import Tools.PropositionalEquality as PE

private variable
  A B t u v : Term _
  Γ         : Cons _ _

------------------------------------------------------------------------
-- Equational reasoning combinators

infix  -1 _∎⟨_⟩⊢ finally
infixr -2 step-≡ step-≡≡ step-≡˘≡ _≡⟨⟩⊢_ finally-≡

-- A regular reasoning step.

step-≡ : ∀ t → Γ ⊢ u ≡ v ∷ A → Γ ⊢ t ≡ u ∷ A → Γ ⊢ t ≡ v ∷ A
step-≡ _ = flip trans

syntax step-≡ t u≡v t≡u = t ≡⟨ t≡u ⟩⊢ u≡v

{-# INLINE step-≡ #-}

-- A reasoning step that uses propositional equality.

step-≡≡ : ∀ t → Γ ⊢ u ≡ v ∷ A → t PE.≡ u → Γ ⊢ t ≡ v ∷ A
step-≡≡ _ u≡v PE.refl = u≡v

syntax step-≡≡ t u≡v t≡u = t ≡⟨ t≡u ⟩⊢≡ u≡v

-- A reasoning step that uses propositional equality, combined with
-- symmetry.

step-≡˘≡ : ∀ t → Γ ⊢ u ≡ v ∷ A → u PE.≡ t → Γ ⊢ t ≡ v ∷ A
step-≡˘≡ _ u≡v PE.refl = u≡v

syntax step-≡˘≡ t u≡v u≡t = t ≡˘⟨ u≡t ⟩⊢≡ u≡v

-- A reasoning step that uses (Agda's) definitional equality.

_≡⟨⟩⊢_ : ∀ t → Γ ⊢ t ≡ u ∷ A → Γ ⊢ t ≡ u ∷ A
_ ≡⟨⟩⊢ t≡u = t≡u

{-# INLINE _≡⟨⟩⊢_ #-}

-- Reflexivity.

_∎⟨_⟩⊢ : ∀ t → Γ ⊢ t ∷ A → Γ ⊢ t ≡ t ∷ A
_ ∎⟨ ⊢t ⟩⊢ = refl ⊢t

{-# INLINE _∎⟨_⟩⊢ #-}

-- The reflexivity proof requires one to prove that the term is
-- well-typed. In a non-empty chain of reasoning steps one can instead
-- end with the following combinator.

finally : ∀ t u → Γ ⊢ t ≡ u ∷ A → Γ ⊢ t ≡ u ∷ A
finally _ _ t≡u = t≡u

syntax finally t u t≡u = t ≡⟨ t≡u ⟩⊢∎ u ∎

{-# INLINE finally #-}

-- A variant of finally that makes it possible to end the chain of
-- reasoning steps with a propositional equality, without the use of
-- _∎⟨_⟩⊢.

finally-≡ : ∀ t → u PE.≡ v → Γ ⊢ t ≡ u ∷ A → Γ ⊢ t ≡ v ∷ A
finally-≡ _ PE.refl t≡u = t≡u

syntax finally-≡ t u≡v t≡u = t ≡⟨ t≡u ⟩⊢∎≡ u≡v

------------------------------------------------------------------------
-- Equational reasoning combinators with explicit types

infix  -1 _∷_∎⟨_⟩⊢∷ finally-∷
infixr -2 step-∷≡ step-∷≡≡ step-∷≡˘≡ _∷_≡⟨⟩⊢∷_ finally-∷≡

-- A regular reasoning step.

step-∷≡ : ∀ t A → Γ ⊢ u ≡ v ∷ A → Γ ⊢ t ≡ u ∷ A → Γ ⊢ t ≡ v ∷ A
step-∷≡ _ _ = flip trans

syntax step-∷≡ t A u≡v t≡u = t ∷ A ≡⟨ t≡u ⟩⊢∷ u≡v

{-# INLINE step-∷≡ #-}

-- A reasoning step that uses propositional equality.

step-∷≡≡ : ∀ t A → Γ ⊢ u ≡ v ∷ A → t PE.≡ u → Γ ⊢ t ≡ v ∷ A
step-∷≡≡ _ _ u≡v PE.refl = u≡v

syntax step-∷≡≡ t A u≡v t≡u = t ∷ A ≡⟨ t≡u ⟩⊢∷≡ u≡v

-- A reasoning step that uses propositional equality, combined with
-- symmetry.

step-∷≡˘≡ : ∀ t A → Γ ⊢ u ≡ v ∷ A → u PE.≡ t → Γ ⊢ t ≡ v ∷ A
step-∷≡˘≡ _ _ u≡v PE.refl = u≡v

syntax step-∷≡˘≡ t A u≡v u≡t = t ∷ A ≡˘⟨ u≡t ⟩⊢∷≡ u≡v

-- A reasoning step that uses (Agda's) definitional equality.

_∷_≡⟨⟩⊢∷_ : ∀ t A → Γ ⊢ t ≡ u ∷ A → Γ ⊢ t ≡ u ∷ A
_ ∷ _ ≡⟨⟩⊢∷ t≡u = t≡u

{-# INLINE _∷_≡⟨⟩⊢∷_ #-}

-- Reflexivity.

_∷_∎⟨_⟩⊢∷ : ∀ t A → Γ ⊢ t ∷ A → Γ ⊢ t ≡ t ∷ A
_ ∷ _ ∎⟨ ⊢t ⟩⊢∷ = refl ⊢t

{-# INLINE _∷_∎⟨_⟩⊢∷ #-}

-- The reflexivity proof requires one to prove that the term is
-- well-typed. In a non-empty chain of reasoning steps one can instead
-- end with the following combinator.

finally-∷ : ∀ t A u → Γ ⊢ t ≡ u ∷ A → Γ ⊢ t ≡ u ∷ A
finally-∷ _ _ _ t≡u = t≡u

syntax finally-∷ t A u t≡u = t ∷ A ≡⟨ t≡u ⟩⊢∷∎ u ∎

{-# INLINE finally-∷ #-}

-- A variant of finally-∷ that makes it possible to end the chain of
-- reasoning steps with a propositional equality, without the use of
-- _∷_∎⟨_⟩⊢∷.

finally-∷≡ : ∀ t A → u PE.≡ v → Γ ⊢ t ≡ u ∷ A → Γ ⊢ t ≡ v ∷ A
finally-∷≡ _ _ PE.refl t≡u = t≡u

syntax finally-∷≡ t A u≡v t≡u = t ∷ A ≡⟨ t≡u ⟩⊢∷∎≡ u≡v

------------------------------------------------------------------------
-- Conversion combinators

infix -2 step-≡-conv step-≡-conv˘ step-≡-conv-≡ step-≡-conv-≡˘

-- Conversion.

step-≡-conv : Γ ⊢ t ≡ u ∷ B → Γ ⊢ A ≡ B → Γ ⊢ t ≡ u ∷ A
step-≡-conv t≡u A≡B = conv t≡u (sym A≡B)

syntax step-≡-conv t≡u A≡B = ⟨ A≡B ⟩≡ t≡u

{-# INLINE step-≡-conv #-}

-- Conversion.

step-≡-conv˘ : Γ ⊢ t ≡ u ∷ B → Γ ⊢ B ≡ A → Γ ⊢ t ≡ u ∷ A
step-≡-conv˘ t≡u B≡A = conv t≡u B≡A

syntax step-≡-conv˘ t≡u B≡A = ˘⟨ B≡A ⟩≡ t≡u

{-# INLINE step-≡-conv˘ #-}

-- Conversion using propositional equality.

step-≡-conv-≡ : Γ ⊢ t ≡ u ∷ B → A PE.≡ B → Γ ⊢ t ≡ u ∷ A
step-≡-conv-≡ t≡u PE.refl = t≡u

syntax step-≡-conv-≡ t≡u A≡B = ⟨ A≡B ⟩≡≡ t≡u

-- Conversion using propositional equality.

step-≡-conv-≡˘ : Γ ⊢ t ≡ u ∷ B → B PE.≡ A → Γ ⊢ t ≡ u ∷ A
step-≡-conv-≡˘ t≡u PE.refl = t≡u

syntax step-≡-conv-≡˘ t≡u B≡A = ˘⟨ B≡A ⟩≡≡ t≡u

------------------------------------------------------------------------
-- Conversion combinators with explicit types

infix -2 step-∷≡-conv step-∷≡-conv˘ step-∷≡-conv-≡ step-∷≡-conv-≡˘

-- Conversion.

step-∷≡-conv : ∀ A → Γ ⊢ t ≡ u ∷ B → Γ ⊢ A ≡ B → Γ ⊢ t ≡ u ∷ A
step-∷≡-conv _ = step-≡-conv

syntax step-∷≡-conv A t≡u A≡B = ∷ A ⟨ A≡B ⟩≡∷ t≡u

{-# INLINE step-∷≡-conv #-}

-- Conversion.

step-∷≡-conv˘ : ∀ A → Γ ⊢ t ≡ u ∷ B → Γ ⊢ B ≡ A → Γ ⊢ t ≡ u ∷ A
step-∷≡-conv˘ _ = step-≡-conv˘

syntax step-∷≡-conv˘ A t≡u B≡A = ∷ A ˘⟨ B≡A ⟩≡∷ t≡u

{-# INLINE step-∷≡-conv˘ #-}

-- Conversion using propositional equality.

step-∷≡-conv-≡ : ∀ A → Γ ⊢ t ≡ u ∷ B → A PE.≡ B → Γ ⊢ t ≡ u ∷ A
step-∷≡-conv-≡ _ t≡u PE.refl = t≡u

syntax step-∷≡-conv-≡ A t≡u A≡B = ∷ A ⟨ A≡B ⟩≡∷≡ t≡u

-- Conversion using propositional equality.

step-∷≡-conv-≡˘ : ∀ A → Γ ⊢ t ≡ u ∷ B → B PE.≡ A → Γ ⊢ t ≡ u ∷ A
step-∷≡-conv-≡˘ _ t≡u PE.refl = t≡u

syntax step-∷≡-conv-≡˘ A t≡u B≡A = ∷ A ˘⟨ B≡A ⟩≡∷≡ t≡u
