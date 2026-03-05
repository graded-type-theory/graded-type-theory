------------------------------------------------------------------------
-- Equational reasoning combinators for definitional equality of levels
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Reasoning.Level
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Typed R
open import Definition.Typed.Properties.Admissible.Level.Primitive R
open import Definition.Untyped M

open import Tools.Function
import Tools.PropositionalEquality as PE

private variable
  l l₁ l₂ l₃ : Lvl _
  Γ          : Cons _ _

infix  -1 _∎⟨_⟩⊢ finally finally-˘
infixr -2 step-≡ step-≡≡ step-≡˘≡ _≡⟨⟩⊢_ finally-≡ step-≡˘ finally-≡˘

-- A regular reasoning step.

step-≡ :
  ∀ l₁ → Γ ⊢ l₂ ≡ l₃ ∷Level → Γ ⊢ l₁ ≡ l₂ ∷Level → Γ ⊢ l₁ ≡ l₃ ∷Level
step-≡ _ = flip trans-⊢≡∷L

syntax step-≡ l₁ l₂≡l₃ l₁≡l₂ = l₁ ≡⟨ l₁≡l₂ ⟩⊢ l₂≡l₃

{-# INLINE step-≡ #-}

-- A reasoning step that uses propositional equality.

step-≡≡ : ∀ l₁ → Γ ⊢ l₂ ≡ l₃ ∷Level → l₁ PE.≡ l₂ → Γ ⊢ l₁ ≡ l₃ ∷Level
step-≡≡ _ l₂≡l₃ PE.refl = l₂≡l₃

syntax step-≡≡ l₁ l₂≡l₃ l₁≡l₂ = l₁ ≡⟨ l₁≡l₂ ⟩⊢≡ l₂≡l₃

-- A reasoning step combined with symmetry.

step-≡˘ :
  ∀ l₁ → Γ ⊢ l₂ ≡ l₃ ∷Level → Γ ⊢ l₂ ≡ l₁ ∷Level → Γ ⊢ l₁ ≡ l₃ ∷Level
step-≡˘ _ l₂≡l₃ l₂≡l₁ = trans-⊢≡∷L (sym-⊢≡∷L l₂≡l₁) l₂≡l₃

syntax step-≡˘ l₁ l₂≡l₃ l₂≡l₁ = l₁ ≡˘⟨ l₂≡l₁ ⟩⊢ l₂≡l₃

{-# INLINE step-≡˘ #-}

-- A reasoning step that uses propositional equality, combined with
-- symmetry.

step-≡˘≡ : ∀ l₁ → Γ ⊢ l₂ ≡ l₃ ∷Level → l₂ PE.≡ l₁ → Γ ⊢ l₁ ≡ l₃ ∷Level
step-≡˘≡ _ l₂≡l₃ PE.refl = l₂≡l₃

syntax step-≡˘≡ l₁ l₂≡l₃ l₂≡l₁ = l₁ ≡˘⟨ l₂≡l₁ ⟩⊢≡ l₂≡l₃

-- A reasoning step that uses (Agda's) definitional equality.

_≡⟨⟩⊢_ : ∀ l₁ → Γ ⊢ l₁ ≡ l₂ ∷Level → Γ ⊢ l₁ ≡ l₂ ∷Level
_ ≡⟨⟩⊢ l₁≡l₂ = l₁≡l₂

{-# INLINE _≡⟨⟩⊢_ #-}

-- Reflexivity.

_∎⟨_⟩⊢ : ∀ l → Γ ⊢ l ∷Level → Γ ⊢ l ≡ l ∷Level
_ ∎⟨ ⊢l ⟩⊢ = refl-⊢≡∷L ⊢l

{-# INLINE _∎⟨_⟩⊢ #-}

-- The reflexivity proof requires one to prove that the term is
-- well-typed. In a non-empty chain of reasoning steps one can instead
-- end with the following combinator.

finally : ∀ l₁ l₂ → Γ ⊢ l₁ ≡ l₂ ∷Level → Γ ⊢ l₁ ≡ l₂ ∷Level
finally _ _ l₁≡l₂ = l₁≡l₂

syntax finally l₁ l₂ l₁≡l₂ = l₁ ≡⟨ l₁≡l₂ ⟩⊢∎ l₂ ∎

{-# INLINE finally #-}

-- A variant of finally that makes it possible to end the chain of
-- reasoning steps with a propositional equality, without the use of
-- _∎⟨_⟩⊢.

finally-≡ : ∀ l₁ → l₂ PE.≡ l₃ → Γ ⊢ l₁ ≡ l₂ ∷Level → Γ ⊢ l₁ ≡ l₃ ∷Level
finally-≡ _ PE.refl l₁≡l₂ = l₁≡l₂

syntax finally-≡ l₁ l₂≡l₃ l₁≡l₂ = l₁ ≡⟨ l₁≡l₂ ⟩⊢∎≡ l₂≡l₃

-- A combinator that combines finally and symmetry.

finally-˘ : ∀ l₁ l₂ → Γ ⊢ l₂ ≡ l₁ ∷Level → Γ ⊢ l₁ ≡ l₂ ∷Level
finally-˘ _ _ l₁≡l₂ = sym-⊢≡∷L l₁≡l₂

syntax finally-˘ l₁ l₂ l₂≡l₁ = l₁ ≡˘⟨ l₂≡l₁ ⟩⊢∎ l₂ ∎

{-# INLINE finally-˘ #-}

-- A variant of finally-≡.

finally-≡˘ : ∀ l₁ → l₂ PE.≡ l₃ → Γ ⊢ l₂ ≡ l₁ ∷Level → Γ ⊢ l₁ ≡ l₃ ∷Level
finally-≡˘ _ PE.refl l₂≡l₁ = sym-⊢≡∷L l₂≡l₁

syntax finally-≡˘ l₁ l₂≡l₃ l₂≡l₁ = l₁ ≡˘⟨ l₂≡l₁ ⟩⊢∎≡ l₂≡l₃
