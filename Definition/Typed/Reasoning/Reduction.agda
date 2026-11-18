------------------------------------------------------------------------
-- "Equational" reasoning combinators for _⊢_⇒*_∷_
------------------------------------------------------------------------

open import Configuration-types
open import Graded.Modality

module Definition.Typed.Reasoning.Reduction
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (TC : Type-configuration 𝕄)
  where

open import Definition.Typed TC
open import Definition.Typed.Properties.Reduction TC
open import Definition.Untyped M

open import Tools.Function
import Tools.PropositionalEquality as PE

private variable
  A B t u v : Term _
  Γ         : Cons _ _

------------------------------------------------------------------------
-- Combinators for left-to-right reductions

infix  -1 finally-⇒* finally-⇒
infixr -2 step-⇒ step-⇒* finally-⇒*≡ finally-⇒≡

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

-- The reflexivity proof requires one to prove that the term is
-- well-typed. In a non-empty chain of reasoning steps one can instead
-- end with the following combinator.

finally-⇒* : ∀ t u → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ⇒* u ∷ A
finally-⇒* _ _ t⇒u = t⇒u

syntax finally-⇒* t u t⇒u = t ⇒*⟨ t⇒u ⟩∎ u ∎

{-# INLINE finally-⇒* #-}

-- A variant of finally-⇒*.

finally-⇒ : ∀ t u → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ⇒* u ∷ A
finally-⇒ _ _ t⇒u = redMany t⇒u

syntax finally-⇒ t u t⇒u = t ⇒⟨ t⇒u ⟩∎ u ∎

{-# INLINE finally-⇒ #-}

-- A variant of finally-⇒* that makes it possible to end the chain of
-- reasoning steps with a propositional equality, without the use of
-- _∎⟨_⟩⇒.

finally-⇒*≡ : ∀ t → u PE.≡ v → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ⇒* v ∷ A
finally-⇒*≡ _ PE.refl t⇒u = t⇒u

syntax finally-⇒*≡ t u≡v t⇒u = t ⇒*⟨ t⇒u ⟩∎≡ u≡v

-- A variant of finally-⇒*≡.

finally-⇒≡ : ∀ t → u PE.≡ v → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ⇒* v ∷ A
finally-⇒≡ _ PE.refl = finally-⇒ _ _

syntax finally-⇒≡ t u≡v t⇒u = t ⇒⟨ t⇒u ⟩∎≡ u≡v

------------------------------------------------------------------------
-- Combinators for right-to-left reductions

infix  -1 finally-⇐* finally-⇐
infixr -2 step-⇐ step-⇐* finally-⇐*≡ finally-⇐≡

opaque

  -- A single step.

  step-⇐ :
    ∀ v → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ u ⇒ v ∷ A → Γ ⊢ t ⇒* v ∷ A
  step-⇐ _ t⇒u u⇒v = t⇒u ⇨∷* redMany u⇒v

  syntax step-⇐ v t⇒u u⇒v = v ⇐⟨ u⇒v ⟩ t⇒u

-- Multiple steps.

step-⇐* : ∀ v → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ u ⇒* v ∷ A → Γ ⊢ t ⇒* v ∷ A
step-⇐* _ = _⇨∷*_

syntax step-⇐* v t⇒u u⇒v = v ⇐*⟨ u⇒v ⟩ t⇒u

{-# INLINE step-⇐* #-}

-- The reflexivity proof requires one to prove that the term is
-- well-typed. In a non-empty chain of reasoning steps one can instead
-- end with the following combinator.

finally-⇐* : ∀ u t → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ⇒* u ∷ A
finally-⇐* _ _ t⇒u = t⇒u

syntax finally-⇐* u t t⇒u = u ⇐*⟨ t⇒u ⟩∎ t ∎

{-# INLINE finally-⇐* #-}

-- A variant of finally-⇐*.

finally-⇐ : ∀ u t → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ⇒* u ∷ A
finally-⇐ _ _ t⇒u = redMany t⇒u

syntax finally-⇐ u t t⇒u = u ⇐⟨ t⇒u ⟩∎ t ∎

{-# INLINE finally-⇐ #-}

-- A variant of finally-⇐* that makes it possible to end the chain of
-- reasoning steps with a propositional equality, without the use of
-- _∎⟨_⟩⇒.

finally-⇐*≡ : ∀ v → u PE.≡ t → Γ ⊢ v ⇒* u ∷ A → Γ ⊢ v ⇒* t ∷ A
finally-⇐*≡ _ PE.refl v⇒u = v⇒u

syntax finally-⇐*≡ v u≡t v⇒u = v ⇐*⟨ v⇒u ⟩∎≡ u≡t

-- A variant of finally-⇐*≡.

finally-⇐≡ : ∀ v → u PE.≡ t → Γ ⊢ v ⇒ u ∷ A → Γ ⊢ v ⇒* t ∷ A
finally-⇐≡ _ PE.refl = finally-⇐ _ _

syntax finally-⇐≡ v u≡t v⇒u = v ⇐⟨ v⇒u ⟩∎≡ u≡t

------------------------------------------------------------------------
-- Combinators for left-to-right or right-to-left reductions

infix  -1 _∎⟨_⟩⇒
infixr -2 step-≡ step-≡˘ _≡⟨⟩⇒_

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

-- Reflexivity.

_∎⟨_⟩⇒ : ∀ t → Γ ⊢ t ∷ A → Γ ⊢ t ⇒* t ∷ A
_ ∎⟨ ⊢t ⟩⇒ = id ⊢t

{-# INLINE _∎⟨_⟩⇒ #-}

------------------------------------------------------------------------
-- Combinators for left-to-right reductions with explicit types

infix -1
  finally-⇒*∷ finally-⇒∷
infixr -2
  step-⇒∷ step-⇒*∷ step-⇒*∷≡ step-⇒*∷≡˘ _∷_≡⟨⟩⇒∷_ finally-⇒*∷≡
  finally-⇒∷≡

-- A single step.

step-⇒∷ : ∀ t A → Γ ⊢ u ⇒* v ∷ A → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ⇒* v ∷ A
step-⇒∷ _ _ = flip _⇨_

syntax step-⇒∷ t A u⇒v t⇒u = t ∷ A ⇒⟨ t⇒u ⟩∷ u⇒v

{-# INLINE step-⇒∷ #-}

-- Multiple steps.

step-⇒*∷ : ∀ t A → Γ ⊢ u ⇒* v ∷ A → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ⇒* v ∷ A
step-⇒*∷ _ _ = flip _⇨∷*_

syntax step-⇒*∷ t A u⇒v t⇒u = t ∷ A ⇒*⟨ t⇒u ⟩∷ u⇒v

{-# INLINE step-⇒*∷ #-}

-- A reasoning step that uses propositional equality.

step-⇒*∷≡ : ∀ t A → Γ ⊢ u ⇒* v ∷ A → t PE.≡ u → Γ ⊢ t ⇒* v ∷ A
step-⇒*∷≡ _ _ u⇒v PE.refl = u⇒v

syntax step-⇒*∷≡ t A u⇒v t≡u = t ∷ A ≡⟨ t≡u ⟩⇒∷ u⇒v

-- A reasoning step that uses propositional equality, combined with
-- symmetry.

step-⇒*∷≡˘ : ∀ t A → Γ ⊢ u ⇒* v ∷ A → u PE.≡ t → Γ ⊢ t ⇒* v ∷ A
step-⇒*∷≡˘ _ _ u⇒v PE.refl = u⇒v

syntax step-⇒*∷≡˘ t A u⇒v u≡t = t ∷ A ≡˘⟨ u≡t ⟩⇒∷ u⇒v

-- A reasoning step that uses (Agda's) definitional equality.

_∷_≡⟨⟩⇒∷_ : ∀ t A → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ⇒* u ∷ A
_ ∷ _ ≡⟨⟩⇒∷ t⇒u = t⇒u

{-# INLINE _∷_≡⟨⟩⇒∷_ #-}

-- The reflexivity proof requires one to prove that the term is
-- well-typed. In a non-empty chain of reasoning steps one can instead
-- end with the following combinator.

finally-⇒*∷ : ∀ t A u → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ⇒* u ∷ A
finally-⇒*∷ _ _ _ t⇒u = t⇒u

syntax finally-⇒*∷ t A u t⇒u = t ∷ A ⇒*⟨ t⇒u ⟩∎∷ u ∎

{-# INLINE finally-⇒*∷ #-}

-- A variant of finally-⇒*∷.

finally-⇒∷ : ∀ t A u → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ⇒* u ∷ A
finally-⇒∷ _ _ _ t⇒u = redMany t⇒u

syntax finally-⇒∷ t A u t⇒u = t ∷ A ⇒⟨ t⇒u ⟩∎∷ u ∎

{-# INLINE finally-⇒∷ #-}

-- A variant of finally-⇒*∷ that makes it possible to end the chain of
-- reasoning steps with a propositional equality, without the use of
-- _∷_∎⟨_⟩⇒.

finally-⇒*∷≡ : ∀ t A → u PE.≡ v → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ⇒* v ∷ A
finally-⇒*∷≡ _ _ PE.refl t⇒u = t⇒u

syntax finally-⇒*∷≡ t A u≡v t⇒u = t ∷ A ⇒*⟨ t⇒u ⟩∎∷≡ u≡v

-- A variant of finally-⇒*∷≡.

finally-⇒∷≡ :
  ∀ t A → u PE.≡ v → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ⇒* v ∷ A
finally-⇒∷≡ _ _ PE.refl = finally-⇒ _ _

syntax finally-⇒∷≡ t A u≡v t⇒u = t ∷ A ⇒⟨ t⇒u ⟩∎∷≡ u≡v

------------------------------------------------------------------------
-- Combinators for right-to-left reductions with explicit types

infix -1
  finally-⇐*∷ finally-⇐∷
infixr -2
  step-⇐∷ step-⇐*∷ step-⇐*∷≡ step-⇐*∷≡˘ _∷_≡⟨⟩⇐∷_ finally-⇐*∷≡
  finally-⇐∷≡

opaque

  -- A single step.

  step-⇐∷ : ∀ v A → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ u ⇒ v ∷ A → Γ ⊢ t ⇒* v ∷ A
  step-⇐∷ _ _ t⇒u u⇒v = t⇒u ⇨∷* redMany u⇒v

  syntax step-⇐∷ v A t⇒u u⇒v = v ∷ A ⇐⟨ u⇒v ⟩∷ t⇒u

-- Multiple steps.

step-⇐*∷ : ∀ v A → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ u ⇒* v ∷ A → Γ ⊢ t ⇒* v ∷ A
step-⇐*∷ _ _ = _⇨∷*_

syntax step-⇐*∷ v A t⇒u u⇒v = v ∷ A ⇐*⟨ u⇒v ⟩∷ t⇒u

{-# INLINE step-⇐*∷ #-}

-- A reasoning step that uses propositional equality.

step-⇐*∷≡ : ∀ v A → Γ ⊢ t ⇒* u ∷ A → v PE.≡ u → Γ ⊢ t ⇒* v ∷ A
step-⇐*∷≡ _ _ t⇒u PE.refl = t⇒u

syntax step-⇐*∷≡ v A t⇒u v≡u = v ∷ A ≡⟨ v≡u ⟩⇐∷ t⇒u

-- A reasoning step that uses propositional equality, combined with
-- symmetry.

step-⇐*∷≡˘ : ∀ v A → Γ ⊢ t ⇒* u ∷ A → u PE.≡ v → Γ ⊢ t ⇒* v ∷ A
step-⇐*∷≡˘ _ _ t⇒u PE.refl = t⇒u

syntax step-⇐*∷≡˘ v A t⇒u u≡v = v ∷ A ≡˘⟨ u≡v ⟩⇐∷ t⇒u

-- A reasoning step that uses (Agda's) definitional equality.

_∷_≡⟨⟩⇐∷_ : ∀ u A → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ⇒* u ∷ A
_ ∷ _ ≡⟨⟩⇐∷ t⇒u = t⇒u

{-# INLINE _∷_≡⟨⟩⇐∷_ #-}

-- The reflexivity proof requires one to prove that the term is
-- well-typed. In a non-empty chain of reasoning steps one can instead
-- end with the following combinator.

finally-⇐*∷ : ∀ u A t → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ⇒* u ∷ A
finally-⇐*∷ _ _ _ t⇒u = t⇒u

syntax finally-⇐*∷ u A t t⇒u = u ∷ A ⇐*⟨ t⇒u ⟩∎∷ t ∎

{-# INLINE finally-⇐*∷ #-}

-- A variant of finally-⇐*∷.

finally-⇐∷ : ∀ u A t → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ⇒* u ∷ A
finally-⇐∷ _ _ _ t⇒u = redMany t⇒u

syntax finally-⇐∷ u A t t⇒u = u ∷ A ⇐⟨ t⇒u ⟩∎∷ t ∎

{-# INLINE finally-⇐∷ #-}

-- A variant of finally-⇐*∷ that makes it possible to end the chain of
-- reasoning steps with a propositional equality, without the use of
-- _∷_∎⟨_⟩⇒.

finally-⇐*∷≡ : ∀ v A → u PE.≡ t → Γ ⊢ u ⇒* v ∷ A → Γ ⊢ t ⇒* v ∷ A
finally-⇐*∷≡ _ _ PE.refl u⇒v = u⇒v

syntax finally-⇐*∷≡ v A u≡t u⇒v = v ∷ A ⇐*⟨ u⇒v ⟩∎∷≡ u≡t

-- A variant of finally-⇐*∷≡.

finally-⇐∷≡ : ∀ v A → u PE.≡ t → Γ ⊢ u ⇒ v ∷ A → Γ ⊢ t ⇒* v ∷ A
finally-⇐∷≡ _ _ PE.refl = finally-⇐ _ _

syntax finally-⇐∷≡ v A u≡t u⇒v = v ∷ A ⇐⟨ u⇒v ⟩∎∷≡ u≡t

------------------------------------------------------------------------
-- A combinator for left-to-right or right-to-left reductions with
-- explicit types

infix -1 _∷_∎⟨_⟩⇒

-- Reflexivity.

_∷_∎⟨_⟩⇒ : ∀ t A → Γ ⊢ t ∷ A → Γ ⊢ t ⇒* t ∷ A
_ ∷ _ ∎⟨ ⊢t ⟩⇒ = id ⊢t

{-# INLINE _∷_∎⟨_⟩⇒ #-}

------------------------------------------------------------------------
-- Conversion combinators

infix -2 step-⇒*-conv step-⇒*-conv˘ step-⇒*-conv-≡ step-⇒*-conv-≡˘

opaque

  -- Conversion.

  step-⇒*-conv : Γ ⊢ t ⇒* u ∷ B → Γ ⊢ A ≡ B → Γ ⊢ t ⇒* u ∷ A
  step-⇒*-conv t⇒u A≡B = conv* t⇒u (sym A≡B)

  syntax step-⇒*-conv t⇒u A≡B = ⟨ A≡B ⟩⇒ t⇒u

opaque

  -- Conversion.

  step-⇒*-conv˘ : Γ ⊢ t ⇒* u ∷ B → Γ ⊢ B ≡ A → Γ ⊢ t ⇒* u ∷ A
  step-⇒*-conv˘ t⇒u B≡A = conv* t⇒u B≡A

  syntax step-⇒*-conv˘ t⇒u B≡A = ˘⟨ B≡A ⟩⇒ t⇒u

-- Conversion using propositional equality.

step-⇒*-conv-≡ : Γ ⊢ t ⇒* u ∷ B → A PE.≡ B → Γ ⊢ t ⇒* u ∷ A
step-⇒*-conv-≡ t⇒u PE.refl = t⇒u

syntax step-⇒*-conv-≡ t⇒u A≡B = ⟨ A≡B ⟩⇒≡ t⇒u

-- Conversion using propositional equality.

step-⇒*-conv-≡˘ : Γ ⊢ t ⇒* u ∷ B → B PE.≡ A → Γ ⊢ t ⇒* u ∷ A
step-⇒*-conv-≡˘ t⇒u PE.refl = t⇒u

syntax step-⇒*-conv-≡˘ t⇒u B≡A = ˘⟨ B≡A ⟩⇒≡ t⇒u

------------------------------------------------------------------------
-- Conversion combinators for left-to-right reductions with explicit
-- types

infix -2 step-∷⇒*-conv step-∷⇒*-conv˘ step-∷⇒*-conv-≡ step-∷⇒*-conv-≡˘

-- Conversion.

step-∷⇒*-conv : ∀ A → Γ ⊢ t ⇒* u ∷ B → Γ ⊢ A ≡ B → Γ ⊢ t ⇒* u ∷ A
step-∷⇒*-conv _ = step-⇒*-conv

syntax step-∷⇒*-conv A t⇒u A≡B = ∷ A ⟨ A≡B ⟩⇒ t⇒u

{-# INLINE step-∷⇒*-conv #-}

-- Conversion.

step-∷⇒*-conv˘ : ∀ A → Γ ⊢ t ⇒* u ∷ B → Γ ⊢ B ≡ A → Γ ⊢ t ⇒* u ∷ A
step-∷⇒*-conv˘ _ = step-⇒*-conv˘

syntax step-∷⇒*-conv˘ A t⇒u B≡A = ∷ A ˘⟨ B≡A ⟩⇒ t⇒u

{-# INLINE step-∷⇒*-conv˘ #-}

-- Conversion using propositional equality.

step-∷⇒*-conv-≡ : ∀ A → Γ ⊢ t ⇒* u ∷ B → A PE.≡ B → Γ ⊢ t ⇒* u ∷ A
step-∷⇒*-conv-≡ _ t⇒u PE.refl = t⇒u

syntax step-∷⇒*-conv-≡ A t⇒u A≡B = ∷ A ⟨ A≡B ⟩⇒≡ t⇒u

-- Conversion using propositional equality.

step-∷⇒*-conv-≡˘ : ∀ A → Γ ⊢ t ⇒* u ∷ B → B PE.≡ A → Γ ⊢ t ⇒* u ∷ A
step-∷⇒*-conv-≡˘ _ t⇒u PE.refl = t⇒u

syntax step-∷⇒*-conv-≡˘ A t⇒u B≡A = ∷ A ˘⟨ B≡A ⟩⇒≡ t⇒u

------------------------------------------------------------------------
-- Conversion combinators for right-to-left reductions with explicit
-- types

infix -2 step-∷⇐*-conv step-∷⇐*-conv˘ step-∷⇐*-conv-≡ step-∷⇐*-conv-≡˘

-- Conversion.

step-∷⇐*-conv : ∀ A → Γ ⊢ t ⇒* u ∷ B → Γ ⊢ A ≡ B → Γ ⊢ t ⇒* u ∷ A
step-∷⇐*-conv _ = step-⇒*-conv

syntax step-∷⇐*-conv A t⇒u A≡B = ∷ A ⟨ A≡B ⟩⇐ t⇒u

{-# INLINE step-∷⇐*-conv #-}

-- Conversion.

step-∷⇐*-conv˘ : ∀ A → Γ ⊢ t ⇒* u ∷ B → Γ ⊢ B ≡ A → Γ ⊢ t ⇒* u ∷ A
step-∷⇐*-conv˘ _ = step-⇒*-conv˘

syntax step-∷⇐*-conv˘ A t⇒u B≡A = ∷ A ˘⟨ B≡A ⟩⇐ t⇒u

{-# INLINE step-∷⇐*-conv˘ #-}

-- Conversion using propositional equality.

step-∷⇐*-conv-≡ : ∀ A → Γ ⊢ t ⇒* u ∷ B → A PE.≡ B → Γ ⊢ t ⇒* u ∷ A
step-∷⇐*-conv-≡ _ t⇒u PE.refl = t⇒u

syntax step-∷⇐*-conv-≡ A t⇒u A≡B = ∷ A ⟨ A≡B ⟩⇐≡ t⇒u

-- Conversion using propositional equality.

step-∷⇐*-conv-≡˘ : ∀ A → Γ ⊢ t ⇒* u ∷ B → B PE.≡ A → Γ ⊢ t ⇒* u ∷ A
step-∷⇐*-conv-≡˘ _ t⇒u PE.refl = t⇒u

syntax step-∷⇐*-conv-≡˘ A t⇒u B≡A = ∷ A ˘⟨ B≡A ⟩⇐≡ t⇒u
