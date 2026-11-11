------------------------------------------------------------------------
-- Equational reasoning combinators for definitional equality of terms
------------------------------------------------------------------------

open import Configuration-types
open import Graded.Modality

module Definition.Typed.Reasoning.Term
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (TC : Type-configuration 𝕄)
  where

open import Definition.Typed TC
open import Definition.Typed.Properties.Admissible.Equality TC
open import Definition.Typed.Properties.Reduction TC
open import Definition.Untyped M

import Tools.PropositionalEquality as PE

open import Definition.Typed.Reasoning.Term.Primitive TC public

private variable
  A B t u v : Term _
  Γ         : Cons _ _

------------------------------------------------------------------------
-- Equational reasoning combinators

infix  -1 finally-˘ finally-⇒ finally-⇒* finally-⇐ finally-⇐*
infixr -2 step-≡˘ step-≡⇒ step-≡⇒* step-≡⇐ step-≡⇐* finally-≡˘

-- A reasoning step combined with symmetry.

step-≡˘ : ∀ t → Γ ⊢ u ≡ v ∷ A → Γ ⊢ u ≡ t ∷ A → Γ ⊢ t ≡ v ∷ A
step-≡˘ _ u≡v u≡t = trans (sym′ u≡t) u≡v

syntax step-≡˘ t u≡v u≡t = t ≡˘⟨ u≡t ⟩⊢ u≡v

{-# INLINE step-≡˘ #-}

opaque

  -- A reduction step.

  step-≡⇒ : ∀ t → Γ ⊢ u ≡ v ∷ A → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ≡ v ∷ A
  step-≡⇒ _ u≡v t⇒u = trans (subsetTerm t⇒u) u≡v

  syntax step-≡⇒ t u≡v t⇒u = t ⇒⟨ t⇒u ⟩⊢ u≡v

opaque

  -- Multiple reduction steps.

  step-≡⇒* : ∀ t → Γ ⊢ u ≡ v ∷ A → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ≡ v ∷ A
  step-≡⇒* _ u≡v t⇒*u = trans (subset*Term t⇒*u) u≡v

  syntax step-≡⇒* t u≡v t⇒*u = t ⇒*⟨ t⇒*u ⟩⊢ u≡v

opaque

  -- A reduction step, "backwards".

  step-≡⇐ : ∀ t → Γ ⊢ u ≡ v ∷ A → Γ ⊢ u ⇒ t ∷ A → Γ ⊢ t ≡ v ∷ A
  step-≡⇐ _ u≡v t⇐u = trans (sym′ (subsetTerm t⇐u)) u≡v

  syntax step-≡⇐ t u≡v t⇐u = t ⇐⟨ t⇐u ⟩⊢ u≡v

opaque

  -- Multiple reduction steps, "backwards".

  step-≡⇐* : ∀ t → Γ ⊢ u ≡ v ∷ A → Γ ⊢ u ⇒* t ∷ A → Γ ⊢ t ≡ v ∷ A
  step-≡⇐* _ u≡v t⇐*u = trans (sym′ (subset*Term t⇐*u)) u≡v

  syntax step-≡⇐* t u≡v t⇐*u = t ⇐*⟨ t⇐*u ⟩⊢ u≡v

-- A combinator that combines finally and symmetry.

finally-˘ : ∀ t u → Γ ⊢ u ≡ t ∷ A → Γ ⊢ t ≡ u ∷ A
finally-˘ _ _ t≡u = sym′ t≡u

syntax finally-˘ t u u≡t = t ≡˘⟨ u≡t ⟩⊢∎ u ∎

{-# INLINE finally-˘ #-}

opaque

  -- A variant of finally for reductions.

  finally-⇒ : ∀ t u → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ≡ u ∷ A
  finally-⇒ _ _ t⇒u = subsetTerm t⇒u

  syntax finally-⇒ t u t⇒u = t ⇒⟨ t⇒u ⟩⊢∎ u ∎

opaque

  -- A variant of finally for reductions.

  finally-⇒* : ∀ t u → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ≡ u ∷ A
  finally-⇒* _ _ t⇒*u = subset*Term t⇒*u

  syntax finally-⇒* t u t⇒*u = t ⇒*⟨ t⇒*u ⟩⊢∎ u ∎

opaque

  -- A variant of finally for reductions.

  finally-⇐ : ∀ t u → Γ ⊢ u ⇒ t ∷ A → Γ ⊢ t ≡ u ∷ A
  finally-⇐ _ _ t⇐u = sym′ (subsetTerm t⇐u)

  syntax finally-⇐ t u t⇐u = t ⇐⟨ t⇐u ⟩⊢∎ u ∎

opaque

  -- A variant of finally for reductions.

  finally-⇐* : ∀ t u → Γ ⊢ u ⇒* t ∷ A → Γ ⊢ t ≡ u ∷ A
  finally-⇐* _ _ t⇐*u = sym′ (subset*Term t⇐*u)

  syntax finally-⇐* t u t⇐*u = t ⇐*⟨ t⇐*u ⟩⊢∎ u ∎

-- A variant of finally-≡.

finally-≡˘ : ∀ t → u PE.≡ v → Γ ⊢ u ≡ t ∷ A → Γ ⊢ t ≡ v ∷ A
finally-≡˘ _ PE.refl u≡t = sym′ u≡t

syntax finally-≡˘ t u≡v u≡t = t ≡˘⟨ u≡t ⟩⊢∎≡ u≡v

------------------------------------------------------------------------
-- Equational reasoning combinators with explicit types

infix  -1 finally-∷˘ finally-∷⇒ finally-∷⇒* finally-∷⇐ finally-∷⇐*
infixr -2 step-∷≡˘ step-∷≡⇒ step-∷≡⇒* step-∷≡⇐ step-∷≡⇐* finally-∷≡˘

-- A reasoning step combined with symmetry.

step-∷≡˘ : ∀ t A → Γ ⊢ u ≡ v ∷ A → Γ ⊢ u ≡ t ∷ A → Γ ⊢ t ≡ v ∷ A
step-∷≡˘ _ _ u≡v u≡t = trans (sym′ u≡t) u≡v

syntax step-∷≡˘ t A u≡v u≡t = t ∷ A ≡˘⟨ u≡t ⟩⊢∷ u≡v

{-# INLINE step-∷≡˘ #-}

opaque

  -- A reduction step.

  step-∷≡⇒ : ∀ t A → Γ ⊢ u ≡ v ∷ A → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ≡ v ∷ A
  step-∷≡⇒ _ _ = step-≡⇒ _

  syntax step-∷≡⇒ t A u≡v t⇒u = t ∷ A ⇒⟨ t⇒u ⟩⊢∷ u≡v

opaque

  -- Multiple reduction steps.

  step-∷≡⇒* : ∀ t A → Γ ⊢ u ≡ v ∷ A → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ≡ v ∷ A
  step-∷≡⇒* _ _ = step-≡⇒* _

  syntax step-∷≡⇒* t A u≡v t⇒*u = t ∷ A ⇒*⟨ t⇒*u ⟩⊢∷ u≡v

opaque

  -- A reduction step, "backwards".

  step-∷≡⇐ : ∀ t A → Γ ⊢ u ≡ v ∷ A → Γ ⊢ u ⇒ t ∷ A → Γ ⊢ t ≡ v ∷ A
  step-∷≡⇐ _ _ = step-≡⇐ _

  syntax step-∷≡⇐ t A u≡v t⇐u = t ∷ A ⇐⟨ t⇐u ⟩⊢∷ u≡v

opaque

  -- Multiple reduction steps, "backwards".

  step-∷≡⇐* : ∀ t A → Γ ⊢ u ≡ v ∷ A → Γ ⊢ u ⇒* t ∷ A → Γ ⊢ t ≡ v ∷ A
  step-∷≡⇐* _ _ = step-≡⇐* _

  syntax step-∷≡⇐* t A u≡v t⇐*u = t ∷ A ⇐*⟨ t⇐*u ⟩⊢∷ u≡v

-- A combinator that combines finally-∷ and symmetry.

finally-∷˘ : ∀ t A u → Γ ⊢ u ≡ t ∷ A → Γ ⊢ t ≡ u ∷ A
finally-∷˘ _ _ _ t≡u = sym′ t≡u

syntax finally-∷˘ t A u u≡t = t ∷ A ≡˘⟨ u≡t ⟩⊢∷∎ u ∎

{-# INLINE finally-∷˘ #-}

opaque

  -- A variant of finally-∷ for reductions.

  finally-∷⇒ : ∀ t A u → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ≡ u ∷ A
  finally-∷⇒ _ _ = finally-⇒ _

  syntax finally-∷⇒ t A u t⇒u = t ∷ A ⇒⟨ t⇒u ⟩⊢∷∎ u ∎

opaque

  -- A variant of finally-∷ for reductions.

  finally-∷⇒* : ∀ t A u → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ≡ u ∷ A
  finally-∷⇒* _ _ = finally-⇒* _

  syntax finally-∷⇒* t A u t⇒*u = t ∷ A ⇒*⟨ t⇒*u ⟩⊢∷∎ u ∎

opaque

  -- A variant of finally-∷ for reductions.

  finally-∷⇐ : ∀ t A u → Γ ⊢ u ⇒ t ∷ A → Γ ⊢ t ≡ u ∷ A
  finally-∷⇐ _ _ = finally-⇐ _

  syntax finally-∷⇐ t A u t⇐u = t ∷ A ⇐⟨ t⇐u ⟩⊢∷∎ u ∎

opaque

  -- A variant of finally-∷ for reductions.

  finally-∷⇐* : ∀ t A u → Γ ⊢ u ⇒* t ∷ A → Γ ⊢ t ≡ u ∷ A
  finally-∷⇐* _ _ = finally-⇐* _

  syntax finally-∷⇐* t A u t⇐*u = t ∷ A ⇐*⟨ t⇐*u ⟩⊢∷∎ u ∎

-- A variant of finally-∷≡.

finally-∷≡˘ : ∀ t A → u PE.≡ v → Γ ⊢ u ≡ t ∷ A → Γ ⊢ t ≡ v ∷ A
finally-∷≡˘ _ _ PE.refl u≡t = sym′ u≡t

syntax finally-∷≡˘ t A u≡v u≡t = t ∷ A ≡˘⟨ u≡t ⟩⊢∷∎≡ u≡v
