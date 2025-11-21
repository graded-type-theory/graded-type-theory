------------------------------------------------------------------------
-- Equational reasoning combinators for definitional equality of types
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Reasoning.Type
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Typed R
open import Definition.Typed.Properties.Reduction R
open import Definition.Untyped M

open import Tools.Function
import Tools.PropositionalEquality as PE

private variable
  B C l : Term _
  Γ     : Cons _ _

infix  -1 _∎⟨_⟩⊢ finally finally-˘
          finally-⇒ finally-⇒∷ finally-⇒* finally-⇒*∷
          finally-⇐ finally-⇐∷ finally-⇐* finally-⇐*∷
infixr -2 step-≡ step-≡˘ step-≡≡ step-≡˘≡ _≡⟨⟩⊢_ finally-≡ finally-≡˘
          step-≡⇒ step-≡⇒∷ step-≡⇒* step-≡⇒*∷
          step-≡⇐ step-≡⇐∷ step-≡⇐* step-≡⇐*∷
          finally-⇒≡ finally-⇒∷≡ finally-⇒*≡ finally-⇒*∷≡
          finally-⇐≡ finally-⇐∷≡ finally-⇐*≡ finally-⇐*∷≡

-- A regular reasoning step.
--
-- It can be easier for Agda to type-check typical equational
-- reasoning chains if the transitivity proof gets the equality
-- arguments in the opposite order, because then the B argument is
-- (perhaps more) known once the proof of Γ ⊢ A ≡ B is type-checked.
--
-- The idea behind this optimisation came up in discussions with Ulf
-- Norell.

step-≡ : ∀ A → Γ ⊢ B ≡ C → Γ ⊢ A ≡ B → Γ ⊢ A ≡ C
step-≡ _ = flip trans

syntax step-≡ A B≡C A≡B = A ≡⟨ A≡B ⟩⊢ B≡C

{-# INLINE step-≡ #-}

-- A reasoning step combined with symmetry.

step-≡˘ : ∀ A → Γ ⊢ B ≡ C → Γ ⊢ B ≡ A → Γ ⊢ A ≡ C
step-≡˘ _ B≡C B≡A = trans (sym B≡A) B≡C

syntax step-≡˘ A B≡C B≡A = A ≡˘⟨ B≡A ⟩⊢ B≡C

{-# INLINE step-≡˘ #-}

-- A reasoning step that uses propositional equality.

step-≡≡ : ∀ A → Γ ⊢ B ≡ C → A PE.≡ B → Γ ⊢ A ≡ C
step-≡≡ _ B≡C PE.refl = B≡C

syntax step-≡≡ A B≡C A≡B = A ≡⟨ A≡B ⟩⊢≡ B≡C

-- A reasoning step that uses propositional equality, combined with
-- symmetry.

step-≡˘≡ : ∀ A → Γ ⊢ B ≡ C → B PE.≡ A → Γ ⊢ A ≡ C
step-≡˘≡ _ B≡C PE.refl = B≡C

syntax step-≡˘≡ A B≡C B≡A = A ≡˘⟨ B≡A ⟩⊢≡ B≡C

-- A reasoning step that uses (Agda's) definitional equality.

_≡⟨⟩⊢_ : ∀ A → Γ ⊢ A ≡ B → Γ ⊢ A ≡ B
_ ≡⟨⟩⊢ A≡B = A≡B

{-# INLINE _≡⟨⟩⊢_ #-}

-- Reflexivity.

_∎⟨_⟩⊢ : ∀ A → Γ ⊢ A → Γ ⊢ A ≡ A
_ ∎⟨ ⊢A ⟩⊢ = refl ⊢A

{-# INLINE _∎⟨_⟩⊢ #-}

-- The reflexivity proof requires one to prove that the type is
-- well-formed. In a non-empty chain of reasoning steps one can
-- instead end with the following combinator.

finally : ∀ A B → Γ ⊢ A ≡ B → Γ ⊢ A ≡ B
finally _ _ A≡B = A≡B

syntax finally A B A≡B = A ≡⟨ A≡B ⟩⊢∎ B ∎

{-# INLINE finally #-}

-- A combinator that combines finally and symmetry.

finally-˘ : ∀ A B → Γ ⊢ B ≡ A → Γ ⊢ A ≡ B
finally-˘ _ _ A≡B = sym A≡B

syntax finally-˘ A B B≡A = A ≡˘⟨ B≡A ⟩⊢∎ B ∎

{-# INLINE finally-˘ #-}

-- A variant of finally that makes it possible to end the chain of
-- reasoning steps with a propositional equality, without the use of
-- _∎⟨_⟩⊢.

finally-≡ : ∀ A → B PE.≡ C → Γ ⊢ A ≡ B → Γ ⊢ A ≡ C
finally-≡ _ PE.refl A≡B = A≡B

syntax finally-≡ A B≡C A≡B = A ≡⟨ A≡B ⟩⊢∎≡ B≡C

-- A variant of finally-≡.

finally-≡˘ : ∀ A → B PE.≡ C → Γ ⊢ B ≡ A → Γ ⊢ A ≡ C
finally-≡˘ _ PE.refl B≡A = sym B≡A

syntax finally-≡˘ A B≡C B≡A = A ≡˘⟨ B≡A ⟩⊢∎≡ B≡C

opaque

  -- A reduction step.

  step-≡⇒ : ∀ A → Γ ⊢ B ≡ C → Γ ⊢ A ⇒ B → Γ ⊢ A ≡ C
  step-≡⇒ _ B≡C A⇒B = trans (subset A⇒B) B≡C

  syntax step-≡⇒ A B≡C A⇒B = A ⇒⟨ A⇒B ⟩⊢ B≡C

opaque

  -- A reduction step.

  step-≡⇒∷ : ∀ A → Γ ⊢ B ≡ C → Γ ⊢ A ⇒ B ∷ U l → Γ ⊢ A ≡ C
  step-≡⇒∷ _ B≡C A⇒B = step-≡⇒ _ B≡C (univ A⇒B)

  syntax step-≡⇒∷ A B≡C A⇒B = A ⇒⟨ A⇒B ⟩⊢∷ B≡C

opaque

  -- Multiple reduction steps.

  step-≡⇒* : ∀ A → Γ ⊢ B ≡ C → Γ ⊢ A ⇒* B → Γ ⊢ A ≡ C
  step-≡⇒* _ B≡C A⇒*B = trans (subset* A⇒*B) B≡C

  syntax step-≡⇒* A B≡C A⇒*B = A ⇒*⟨ A⇒*B ⟩⊢ B≡C

opaque

  -- Multiple reduction steps.

  step-≡⇒*∷ : ∀ A → Γ ⊢ B ≡ C → Γ ⊢ A ⇒* B ∷ U l → Γ ⊢ A ≡ C
  step-≡⇒*∷ _ B≡C A⇒*B = step-≡⇒* _ B≡C (univ* A⇒*B)

  syntax step-≡⇒*∷ A B≡C A⇒*B = A ⇒*⟨ A⇒*B ⟩⊢∷ B≡C

opaque

  -- A reduction step, "backwards".

  step-≡⇐ : ∀ A → Γ ⊢ B ≡ C → Γ ⊢ B ⇒ A → Γ ⊢ A ≡ C
  step-≡⇐ _ B≡C A⇐B = trans (sym (subset A⇐B)) B≡C

  syntax step-≡⇐ A B≡C A⇐B = A ⇐⟨ A⇐B ⟩⊢ B≡C

opaque

  -- A reduction step, "backwards".

  step-≡⇐∷ : ∀ A → Γ ⊢ B ≡ C → Γ ⊢ B ⇒ A ∷ U l → Γ ⊢ A ≡ C
  step-≡⇐∷ _ B≡C A⇐B = step-≡⇐ _ B≡C (univ A⇐B)

  syntax step-≡⇐∷ A B≡C A⇐B = A ⇐⟨ A⇐B ⟩⊢∷ B≡C

opaque

  -- Multiple reduction steps, "backwards".

  step-≡⇐* : ∀ A → Γ ⊢ B ≡ C → Γ ⊢ B ⇒* A → Γ ⊢ A ≡ C
  step-≡⇐* _ B≡C A⇐*B = trans (sym (subset* A⇐*B)) B≡C

  syntax step-≡⇐* A B≡C A⇐*B = A ⇐*⟨ A⇐*B ⟩⊢ B≡C

opaque

  -- Multiple reduction steps, "backwards".

  step-≡⇐*∷ : ∀ A → Γ ⊢ B ≡ C → Γ ⊢ B ⇒* A ∷ U l → Γ ⊢ A ≡ C
  step-≡⇐*∷ _ B≡C A⇐*B = step-≡⇐* _ B≡C (univ* A⇐*B)

  syntax step-≡⇐*∷ A B≡C A⇐*B = A ⇐*⟨ A⇐*B ⟩⊢∷ B≡C

-- A variant of finally for reductions.

finally-⇒ : ∀ A B → Γ ⊢ A ⇒ B → Γ ⊢ A ≡ B
finally-⇒ _ _ A⇒B = subset A⇒B

syntax finally-⇒ A B A⇒B = A ⇒⟨ A⇒B ⟩⊢∎ B ∎

{-# INLINE finally-⇒ #-}

-- A variant of finally for reductions.

finally-⇒∷ : ∀ A B → Γ ⊢ A ⇒ B ∷ U l → Γ ⊢ A ≡ B
finally-⇒∷ _ _ A⇒B = subset (univ A⇒B)

syntax finally-⇒∷ A B A⇒B = A ⇒⟨ A⇒B ⟩⊢∷∎ B ∎

{-# INLINE finally-⇒∷ #-}

-- A variant of finally for reductions.

finally-⇒* : ∀ A B → Γ ⊢ A ⇒* B → Γ ⊢ A ≡ B
finally-⇒* _ _ A⇒*B = subset* A⇒*B

syntax finally-⇒* A B A⇒*B = A ⇒*⟨ A⇒*B ⟩⊢∎ B ∎

{-# INLINE finally-⇒* #-}

opaque

  -- A variant of finally for reductions.

  finally-⇒*∷ : ∀ A B → Γ ⊢ A ⇒* B ∷ U l → Γ ⊢ A ≡ B
  finally-⇒*∷ _ _ A⇒*B = subset* (univ* A⇒*B)

  syntax finally-⇒*∷ A B A⇒*B = A ⇒*⟨ A⇒*B ⟩⊢∷∎ B ∎

opaque

  -- A variant of finally for reductions.

  finally-⇐ : ∀ A B → Γ ⊢ B ⇒ A → Γ ⊢ A ≡ B
  finally-⇐ _ _ A⇐B = sym (subset A⇐B)

  syntax finally-⇐ A B A⇐B = A ⇐⟨ A⇐B ⟩⊢∎ B ∎

opaque

  -- A variant of finally for reductions.

  finally-⇐∷ : ∀ A B → Γ ⊢ B ⇒ A ∷ U l → Γ ⊢ A ≡ B
  finally-⇐∷ _ _ A⇐B = finally-⇐ _ _ (univ A⇐B)

  syntax finally-⇐∷ A B A⇐B = A ⇐⟨ A⇐B ⟩⊢∷∎ B ∎

opaque

  -- A variant of finally for reductions.

  finally-⇐* : ∀ A B → Γ ⊢ B ⇒* A → Γ ⊢ A ≡ B
  finally-⇐* _ _ A⇐*B = sym (subset* A⇐*B)

  syntax finally-⇐* A B A⇐*B = A ⇐*⟨ A⇐*B ⟩⊢∎ B ∎

opaque

  -- A variant of finally for reductions.

  finally-⇐*∷ : ∀ A B → Γ ⊢ B ⇒* A ∷ U l → Γ ⊢ A ≡ B
  finally-⇐*∷ _ _ A⇐*B = finally-⇐* _ _ (univ* A⇐*B)

  syntax finally-⇐*∷ A B A⇐*B = A ⇐*⟨ A⇐*B ⟩⊢∷∎ B ∎

-- A variant of finally-≡ for reductions.

finally-⇒≡ : ∀ A → B PE.≡ C → Γ ⊢ A ⇒ B → Γ ⊢ A ≡ C
finally-⇒≡ _ PE.refl A⇒B = subset A⇒B

syntax finally-⇒≡ A B≡C A⇒B = A ⇒⟨ A⇒B ⟩⊢∎≡ B≡C

opaque

  -- A variant of finally-≡ for reductions.

  finally-⇒∷≡ : ∀ A → B PE.≡ C → Γ ⊢ A ⇒ B ∷ U l → Γ ⊢ A ≡ C
  finally-⇒∷≡ _ B≡C A⇒B = finally-⇒≡ _ B≡C (univ A⇒B)

  syntax finally-⇒∷≡ A B≡C A⇒B = A ⇒⟨ A⇒B ⟩⊢∷∎≡ B≡C

-- A variant of finally-≡ for reductions.

finally-⇒*≡ : ∀ A → B PE.≡ C → Γ ⊢ A ⇒* B → Γ ⊢ A ≡ C
finally-⇒*≡ _ PE.refl A⇒*B = subset* A⇒*B

syntax finally-⇒*≡ A B≡C A⇒*B = A ⇒*⟨ A⇒*B ⟩⊢∎≡ B≡C

opaque

  -- A variant of finally-≡ for reductions.

  finally-⇒*∷≡ : ∀ A → B PE.≡ C → Γ ⊢ A ⇒* B ∷ U l → Γ ⊢ A ≡ C
  finally-⇒*∷≡ _ PE.refl A⇒*∷B = subset* (univ* A⇒*∷B)

  syntax finally-⇒*∷≡ A B≡C A⇒*B = A ⇒*⟨ A⇒*B ⟩⊢∷∎≡ B≡C

opaque

  -- A variant of finally-≡ for reductions.

  finally-⇐≡ : ∀ A → B PE.≡ C → Γ ⊢ B ⇒ A → Γ ⊢ A ≡ C
  finally-⇐≡ _ PE.refl A⇐B = sym (subset A⇐B)

  syntax finally-⇐≡ A B≡C A⇐B = A ⇐⟨ A⇐B ⟩⊢∎≡ B≡C

opaque

  -- A variant of finally-≡ for reductions.

  finally-⇐∷≡ : ∀ A → B PE.≡ C → Γ ⊢ B ⇒ A ∷ U l → Γ ⊢ A ≡ C
  finally-⇐∷≡ _ B≡C A⇐B = finally-⇐≡ _ B≡C (univ A⇐B)

  syntax finally-⇐∷≡ A B≡C A⇐B = A ⇐⟨ A⇐B ⟩⊢∷∎≡ B≡C

opaque

  -- A variant of finally-≡ for reductions.

  finally-⇐*≡ : ∀ A → B PE.≡ C → Γ ⊢ B ⇒* A → Γ ⊢ A ≡ C
  finally-⇐*≡ _ PE.refl A⇐*B = sym (subset* A⇐*B)

  syntax finally-⇐*≡ A B≡C A⇐*B = A ⇐*⟨ A⇐*B ⟩⊢∎≡ B≡C

opaque

  -- A variant of finally-≡ for reductions.

  finally-⇐*∷≡ : ∀ A → B PE.≡ C → Γ ⊢ B ⇒* A ∷ U l → Γ ⊢ A ≡ C
  finally-⇐*∷≡ _ B≡C A⇐*B = finally-⇐*≡ _ B≡C (univ* A⇐*B)

  syntax finally-⇐*∷≡ A B≡C A⇐*B = A ⇐*⟨ A⇐*B ⟩⊢∷∎≡ B≡C
