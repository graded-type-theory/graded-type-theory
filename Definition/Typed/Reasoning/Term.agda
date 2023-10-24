------------------------------------------------------------------------
-- Equational reasoning combinators for definitional equality of terms
------------------------------------------------------------------------

open import Definition.Typed.Restrictions

module Definition.Typed.Reasoning.Term
  {ℓ} {M : Set ℓ}
  (R : Type-restrictions M)
  where

open import Definition.Typed R
open import Definition.Untyped M hiding (_∷_)

open import Tools.Function
import Tools.PropositionalEquality as PE

private variable
  A B u v : Term _
  Γ       : Con Term _

infix  -1 _∎⟨_⟩⊢ finally finally-˘ finally-≡
infixr -2 step-≡ step-≡˘ step-≡≡ step-≡˘≡ _≡⟨⟩⊢_ step-≡-conv step-≡-≡

-- A regular reasoning step.

step-≡ : ∀ t → Γ ⊢ u ≡ v ∷ A → Γ ⊢ t ≡ u ∷ A → Γ ⊢ t ≡ v ∷ A
step-≡ _ = flip trans

syntax step-≡ t u≡v t≡u = t ≡⟨ t≡u ⟩⊢ u≡v

{-# INLINE step-≡ #-}

-- A reasoning step combined with symmetry.

step-≡˘ : ∀ t → Γ ⊢ u ≡ v ∷ A → Γ ⊢ u ≡ t ∷ A → Γ ⊢ t ≡ v ∷ A
step-≡˘ _ u≡v u≡t = trans (sym u≡t) u≡v

syntax step-≡˘ t u≡v u≡t = t ≡˘⟨ u≡t ⟩⊢ u≡v

{-# INLINE step-≡˘ #-}

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

-- A reasoning step combined with conversion.

step-≡-conv :
  ∀ t → Γ ⊢ u ≡ v ∷ B → Γ ⊢ t ≡ u ∷ B → Γ ⊢ A ≡ B → Γ ⊢ t ≡ v ∷ A
step-≡-conv _ u≡v t≡u A≡B = conv (trans t≡u u≡v) (sym A≡B)

syntax step-≡-conv t u≡v t≡u A≡B = t ≡⟨ t≡u ⟩⊢ ⟨ A≡B ⟩ u≡v

{-# INLINE step-≡-conv #-}

-- A reasoning step combined with conversion using propositional
-- equality.

step-≡-≡ :
  ∀ t → Γ ⊢ u ≡ v ∷ B → Γ ⊢ t ≡ u ∷ A → A PE.≡ B → Γ ⊢ t ≡ v ∷ A
step-≡-≡ _ u≡v t≡u PE.refl = trans t≡u u≡v

syntax step-≡-≡ t u≡v t≡u A≡B = t ≡⟨ t≡u ⟩⊢ ≡⟨ A≡B ⟩ u≡v

{-# INLINE step-≡-conv #-}

-- Reflexivity.

_∎⟨_⟩⊢ : ∀ t → Γ ⊢ t ∷ A → Γ ⊢ t ≡ t ∷ A
_ ∎⟨ ⊢t ⟩⊢ = refl ⊢t

{-# INLINE _∎⟨_⟩⊢ #-}

-- The reflexivity proof requires one to prove that the term is
-- well-formed. In a non-empty chain of reasoning steps one can
-- instead end with the following combinator.

finally : ∀ t u → Γ ⊢ t ≡ u ∷ A → Γ ⊢ t ≡ u ∷ A
finally _ _ t≡u = t≡u

syntax finally t u t≡u = t ≡⟨ t≡u ⟩⊢∎ u ∎

{-# INLINE finally #-}

-- A combinator that combines finally and symmetry.

finally-˘ : ∀ t u → Γ ⊢ u ≡ t ∷ A → Γ ⊢ t ≡ u ∷ A
finally-˘ _ _ t≡u = sym t≡u

syntax finally-˘ t u u≡t = t ≡˘⟨ u≡t ⟩⊢∎ u ∎

{-# INLINE finally-˘ #-}

-- A variant of finally that makes it possible to end the chain of
-- reasoning steps with a propositional equality, without the use of
-- _∎⟨_⟩⊢.

finally-≡ : ∀ t → u PE.≡ v → Γ ⊢ t ≡ u ∷ A → Γ ⊢ t ≡ v ∷ A
finally-≡ _ PE.refl t≡u = t≡u

syntax finally-≡ t u≡v t≡u = t ≡⟨ t≡u ⟩⊢∎≡ u≡v
