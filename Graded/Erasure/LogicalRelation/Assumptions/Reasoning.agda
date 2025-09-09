------------------------------------------------------------------------
-- "Equational" reasoning combinators for _⇛_∷_
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Definition.Untyped
import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality

module Graded.Erasure.LogicalRelation.Assumptions.Reasoning
  {a} {M : Set a}
  (open Definition.Untyped M)
  {𝕄 : Modality M}
  {R : Type-restrictions 𝕄}
  (open Graded.Erasure.LogicalRelation.Assumptions R)
  {m n} {Δ : Cons m n}
  {_⇛_∷_ : Term n → Term n → Term n → Set a}
  (is-reduction-relation : Is-reduction-relation Δ _⇛_∷_)
  where

open Is-reduction-relation is-reduction-relation

open import Definition.Typed R
open import Definition.Typed.Properties.Reduction R

open import Tools.Function
import Tools.PropositionalEquality as PE

private variable
  A B t u v : Term _

------------------------------------------------------------------------
-- Combinators for left-to-right reductions

infix  -1 finally-⇛ finally-⇒* finally-⇒
infixr -2 step-⇛ step-⇒* step-⇒ finally-⇛≡ finally-⇒*≡ finally-⇒≡

opaque

  -- A form of transitivity.

  step-⇛ : ∀ t → u ⇛ v ∷ A → t ⇛ u ∷ A → t ⇛ v ∷ A
  step-⇛ _ = flip trans-⇛

  syntax step-⇛ t u⇛v t⇛u = t ⇛⟨ t⇛u ⟩ u⇛v

opaque

  -- Multiple reduction steps.

  step-⇒* : ∀ t → u ⇛ v ∷ A → Δ ⊢ t ⇒* u ∷ A → t ⇛ v ∷ A
  step-⇒* _ u⇛v t⇒*u = trans-⇛ (⇒*→⇛ t⇒*u) u⇛v

  syntax step-⇒* t u⇒v t⇒u = t ⇒*⟨ t⇒u ⟩⇛ u⇒v

opaque

  -- A single reduction step.

  step-⇒ : ∀ t → u ⇛ v ∷ A → Δ ⊢ t ⇒ u ∷ A → t ⇛ v ∷ A
  step-⇒ _ u⇛v t⇒u = step-⇒* _ u⇛v (redMany t⇒u)

  syntax step-⇒ t u⇒v t⇒u = t ⇒⟨ t⇒u ⟩⇛ u⇒v

-- A combinator that can be used as the last one in a chain of
-- reasoning steps.

finally-⇛ : ∀ t u → t ⇛ u ∷ A → t ⇛ u ∷ A
finally-⇛ _ _ t⇛u = t⇛u

syntax finally-⇛ t u t⇛u = t ⇛⟨ t⇛u ⟩∎ u ∎

{-# INLINE finally-⇛ #-}

opaque

  -- A variant of finally-⇛.

  finally-⇒ : ∀ t u → Δ ⊢ t ⇒ u ∷ A → t ⇛ u ∷ A
  finally-⇒ _ _ t⇒u = ⇒*→⇛ (redMany t⇒u)

  syntax finally-⇒ t u t⇒u = t ⇒⟨ t⇒u ⟩∎⇛ u ∎

opaque

  -- A variant of finally-⇛.

  finally-⇒* : ∀ t u → Δ ⊢ t ⇒* u ∷ A → t ⇛ u ∷ A
  finally-⇒* _ _ t⇒u = ⇒*→⇛ t⇒u

  syntax finally-⇒* t u t⇒u = t ⇒*⟨ t⇒u ⟩∎⇛ u ∎

-- A variant of finally-⇛ that makes it possible to end the chain of
-- reasoning steps with a propositional equality, without the use of
-- _∎⟨_⟩⇛.

finally-⇛≡ : ∀ t → u PE.≡ v → t ⇛ u ∷ A → t ⇛ v ∷ A
finally-⇛≡ _ PE.refl t⇛u = t⇛u

syntax finally-⇛≡ t u≡v t⇛u = t ⇛⟨ t⇛u ⟩∎≡ u≡v

opaque

  -- A variant of finally-⇛≡.

  finally-⇒*≡ : ∀ t → u PE.≡ v → Δ ⊢ t ⇒* u ∷ A → t ⇛ v ∷ A
  finally-⇒*≡ _ PE.refl = finally-⇒* _ _

  syntax finally-⇒*≡ t u≡v t⇒u = t ⇒*⟨ t⇒u ⟩∎≡⇛ u≡v

opaque

  -- A variant of finally-⇛≡.

  finally-⇒≡ : ∀ t → u PE.≡ v → Δ ⊢ t ⇒ u ∷ A → t ⇛ v ∷ A
  finally-⇒≡ _ PE.refl = finally-⇒ _ _

  syntax finally-⇒≡ t u≡v t⇒u = t ⇒⟨ t⇒u ⟩∎≡⇛ u≡v

------------------------------------------------------------------------
-- Combinators for right-to-left reductions

infix  -1 finally-⇚ finally-⇐* finally-⇐
infixr -2 step-⇚ step-⇐* step-⇐ finally-⇚≡ finally-⇐*≡ finally-⇐≡

opaque

  -- A form of transitivity.

  step-⇚ : ∀ t → t ⇛ u ∷ A → u ⇛ v ∷ A → t ⇛ v ∷ A
  step-⇚ _ = trans-⇛

  syntax step-⇚ v t⇛u u⇛v = v ⇚⟨ u⇛v ⟩ t⇛u

opaque

  -- Multiple steps.

  step-⇐* : ∀ v → t ⇛ u ∷ A → Δ ⊢ u ⇒* v ∷ A → t ⇛ v ∷ A
  step-⇐* _ t⇛u u⇒v = trans-⇛ t⇛u (⇒*→⇛ u⇒v)

  syntax step-⇐* v t⇛u u⇒v = v ⇐*⟨ u⇒v ⟩⇚ t⇛u

opaque

  -- A single step.

  step-⇐ : ∀ v → t ⇛ u ∷ A → Δ ⊢ u ⇒ v ∷ A → t ⇛ v ∷ A
  step-⇐ _ t⇛u u⇒v = step-⇐* _ t⇛u (redMany u⇒v)

  syntax step-⇐ v t⇛u u⇒v = v ⇐⟨ u⇒v ⟩⇚ t⇛u

-- A combinator that can be used as the last one in a chain of
-- reasoning steps.

finally-⇚ : ∀ u t → t ⇛ u ∷ A → t ⇛ u ∷ A
finally-⇚ _ _ t⇛u = t⇛u

syntax finally-⇚ u t t⇛u = u ⇚⟨ t⇛u ⟩∎ t ∎

{-# INLINE finally-⇚ #-}

opaque

  -- A variant of finally-⇚.

  finally-⇐* : ∀ u t → Δ ⊢ t ⇒* u ∷ A → t ⇛ u ∷ A
  finally-⇐* _ _ = finally-⇒* _ _

  syntax finally-⇐* u t t⇒u = u ⇐*⟨ t⇒u ⟩∎⇚ t ∎

  {-# INLINE finally-⇐* #-}

opaque

  -- A variant of finally-⇐*.

  finally-⇐ : ∀ u t → Δ ⊢ t ⇒ u ∷ A → t ⇛ u ∷ A
  finally-⇐ _ _ = finally-⇒ _ _

  syntax finally-⇐ u t t⇒u = u ⇐⟨ t⇒u ⟩∎⇚ t ∎

  {-# INLINE finally-⇐ #-}

-- A variant of finally-⇐* that makes it possible to end the chain of
-- reasoning steps with a propositional equality, without the use of
-- _∎⟨_⟩⇛.

finally-⇚≡ : ∀ v → u PE.≡ t → u ⇛ v ∷ A → t ⇛ v ∷ A
finally-⇚≡ _ PE.refl u⇛v = u⇛v

syntax finally-⇚≡ v u≡t u⇛v = v ⇚⟨ u⇛v ⟩∎≡ u≡t

opaque

  -- A variant of finally-⇚≡.

  finally-⇐*≡ : ∀ v → u PE.≡ t → Δ ⊢ u ⇒* v ∷ A → t ⇛ v ∷ A
  finally-⇐*≡ _ PE.refl = finally-⇐* _ _

  syntax finally-⇐*≡ v u≡t u⇒v = v ⇐*⟨ u⇒v ⟩∎≡⇚ u≡t

opaque

  -- A variant of finally-⇚≡.

  finally-⇐≡ : ∀ v → u PE.≡ t → Δ ⊢ u ⇒ v ∷ A → t ⇛ v ∷ A
  finally-⇐≡ _ PE.refl = finally-⇐ _ _

  syntax finally-⇐≡ v u≡t u⇒v = v ⇐⟨ u⇒v ⟩∎≡⇚ u≡t

------------------------------------------------------------------------
-- Combinators for left-to-right or right-to-left reductions

infix  -1 _∎⟨_⟩⇛
infixr -2 step-≡ step-≡˘ _≡⟨⟩⇛_

-- A reasoning step that uses propositional equality.

step-≡ : ∀ t → u ⇛ v ∷ A → t PE.≡ u → t ⇛ v ∷ A
step-≡ _ u⇛v PE.refl = u⇛v

syntax step-≡ t u⇛v t≡u = t ≡⟨ t≡u ⟩⇛ u⇛v

-- A reasoning step that uses propositional equality, combined with
-- symmetry.

step-≡˘ : ∀ t → u ⇛ v ∷ A → u PE.≡ t → t ⇛ v ∷ A
step-≡˘ _ u⇛v PE.refl = u⇛v

syntax step-≡˘ t u⇛v u≡t = t ≡˘⟨ u≡t ⟩⇛ u⇛v

-- A reasoning step that uses (Agda's) definitional equality.

_≡⟨⟩⇛_ : ∀ t → t ⇛ u ∷ A → t ⇛ u ∷ A
_ ≡⟨⟩⇛ t⇛u = t⇛u

{-# INLINE _≡⟨⟩⇛_ #-}

-- Reflexivity.

_∎⟨_⟩⇛ : ∀ t → Δ ⊢ t ∷ A → t ⇛ t ∷ A
_ ∎⟨ ⊢t ⟩⇛ = ⇒*→⇛ (id ⊢t)

{-# INLINE _∎⟨_⟩⇛ #-}

------------------------------------------------------------------------
-- Combinators for left-to-right reductions with explicit types

infix  -1 finally-⇛∷ finally-⇒*∷ finally-⇒∷
infixr -2 step-⇛∷ step-⇒*∷ step-⇒∷ step-⇛∷≡ step-⇛∷≡˘ _∷_≡⟨⟩⇛∷_
          finally-⇛≡∷ finally-⇒*≡∷ finally-⇒≡∷

opaque

  -- A form of transitivity.

  step-⇛∷ : ∀ t A → u ⇛ v ∷ A → t ⇛ u ∷ A → t ⇛ v ∷ A
  step-⇛∷ _ _ = step-⇛ _

  syntax step-⇛∷ t A u⇛v t⇛u = t ∷ A ⇛⟨ t⇛u ⟩∷ u⇛v

opaque

  -- Multiple reduction steps.

  step-⇒*∷ : ∀ t A → u ⇛ v ∷ A → Δ ⊢ t ⇒* u ∷ A → t ⇛ v ∷ A
  step-⇒*∷ _ _ = step-⇒* _

  syntax step-⇒*∷ t A u⇒v t⇒u = t ∷ A ⇒*⟨ t⇒u ⟩⇛∷ u⇒v

opaque

  -- A single reduction step.

  step-⇒∷ : ∀ t A → u ⇛ v ∷ A → Δ ⊢ t ⇒ u ∷ A → t ⇛ v ∷ A
  step-⇒∷ _ _ = step-⇒ _

  syntax step-⇒∷ t A u⇒v t⇒u = t ∷ A ⇒⟨ t⇒u ⟩⇛∷ u⇒v

-- A reasoning step that uses propositional equality.

step-⇛∷≡ : ∀ t A → u ⇛ v ∷ A → t PE.≡ u → t ⇛ v ∷ A
step-⇛∷≡ _ _ u⇛v PE.refl = u⇛v

syntax step-⇛∷≡ t A u⇛v t≡u = t ∷ A ≡⟨ t≡u ⟩⇛∷ u⇛v

-- A reasoning step that uses propositional equality, combined with
-- symmetry.

step-⇛∷≡˘ : ∀ t A → u ⇛ v ∷ A → u PE.≡ t → t ⇛ v ∷ A
step-⇛∷≡˘ _ _ u⇛v PE.refl = u⇛v

syntax step-⇛∷≡˘ t A u⇛v u≡t = t ∷ A ≡˘⟨ u≡t ⟩⇛∷ u⇛v

-- A reasoning step that uses (Agda's) definitional equality.

_∷_≡⟨⟩⇛∷_ : ∀ t A → t ⇛ u ∷ A → t ⇛ u ∷ A
_ ∷ _ ≡⟨⟩⇛∷ t⇛u = t⇛u

{-# INLINE _∷_≡⟨⟩⇛∷_ #-}

-- A combinator that can be used as the last one in a chain of
-- reasoning steps.

finally-⇛∷ : ∀ t A u → t ⇛ u ∷ A → t ⇛ u ∷ A
finally-⇛∷ _ _ _ t⇛u = t⇛u

syntax finally-⇛∷ t A u t⇛u = t ∷ A ⇛⟨ t⇛u ⟩∎∷ u ∎

{-# INLINE finally-⇛∷ #-}

opaque

  -- A variant of finally-⇛∷.

  finally-⇒∷ : ∀ t A u → Δ ⊢ t ⇒ u ∷ A → t ⇛ u ∷ A
  finally-⇒∷ _ _ _ = finally-⇒ _ _

  syntax finally-⇒∷ t A u t⇒u = t ∷ A ⇒⟨ t⇒u ⟩∎⇛∷ u ∎

opaque

  -- A variant of finally-⇛∷.

  finally-⇒*∷ : ∀ t A u → Δ ⊢ t ⇒* u ∷ A → t ⇛ u ∷ A
  finally-⇒*∷ _ _ = finally-⇒* _

  syntax finally-⇒*∷ t A u t⇒u = t ∷ A ⇒*⟨ t⇒u ⟩∎⇛∷ u ∎

-- A variant of finally-⇛ that makes it possible to end the chain of
-- reasoning steps with a propositional equality, without the use of
-- _∷_∎⟨_⟩⇛.

finally-⇛≡∷ : ∀ t A → u PE.≡ v → t ⇛ u ∷ A → t ⇛ v ∷ A
finally-⇛≡∷ _ _ PE.refl t⇛u = t⇛u

syntax finally-⇛≡∷ t A u≡v t⇛u = t ∷ A ⇛⟨ t⇛u ⟩∎∷≡ u≡v

opaque

  -- A variant of finally-⇛≡∷.

  finally-⇒*≡∷ : ∀ t A → u PE.≡ v → Δ ⊢ t ⇒* u ∷ A → t ⇛ v ∷ A
  finally-⇒*≡∷ _ _ = finally-⇒*≡ _

  syntax finally-⇒*≡∷ t A u≡v t⇒u = t ∷ A ⇒*⟨ t⇒u ⟩∎⇛∷≡ u≡v

opaque

  -- A variant of finally-⇛≡∷.

  finally-⇒≡∷ : ∀ t A → u PE.≡ v → Δ ⊢ t ⇒ u ∷ A → t ⇛ v ∷ A
  finally-⇒≡∷ _ _ = finally-⇒≡ _

  syntax finally-⇒≡∷ t A u≡v t⇒u = t ∷ A ⇒⟨ t⇒u ⟩∎⇛∷≡ u≡v

------------------------------------------------------------------------
-- Combinators for right-to-left reductions with explicit types

infix  -1 finally-⇚∷ finally-⇐*∷ finally-⇐∷
infixr -2 step-⇚∷ step-⇐*∷ step-⇐∷ step-⇚∷≡ step-⇚∷≡˘ _∷_≡⟨⟩⇚∷_
          finally-⇚≡∷ finally-⇐*≡∷ finally-⇐≡∷

opaque

  -- A form of transitivity.

  step-⇚∷ : ∀ t A → t ⇛ u ∷ A → u ⇛ v ∷ A → t ⇛ v ∷ A
  step-⇚∷ _ _ = step-⇚ _

  syntax step-⇚∷ v A t⇛u u⇛v = v ∷ A ⇚⟨ u⇛v ⟩∷ t⇛u

opaque

  -- Multiple steps.

  step-⇐*∷ : ∀ v A → t ⇛ u ∷ A → Δ ⊢ u ⇒* v ∷ A → t ⇛ v ∷ A
  step-⇐*∷ _ _ = step-⇐* _

  syntax step-⇐*∷ v A t⇛u u⇒v = v ∷ A ⇐*⟨ u⇒v ⟩⇚∷ t⇛u

opaque

  -- A single step.

  step-⇐∷ : ∀ v A → t ⇛ u ∷ A → Δ ⊢ u ⇒ v ∷ A → t ⇛ v ∷ A
  step-⇐∷ _ _ = step-⇐ _

  syntax step-⇐∷ v A t⇛u u⇒v = v ∷ A ⇐⟨ u⇒v ⟩⇚∷ t⇛u

-- A reasoning step that uses propositional equality.

step-⇚∷≡ : ∀ v A → t ⇛ u ∷ A → v PE.≡ u → t ⇛ v ∷ A
step-⇚∷≡ _ _ t⇛u PE.refl = t⇛u

syntax step-⇚∷≡ v A t⇛u v≡u = v ∷ A ≡⟨ v≡u ⟩⇚∷ t⇛u

-- A reasoning step that uses propositional equality, combined with
-- symmetry.

step-⇚∷≡˘ : ∀ v A → t ⇛ u ∷ A → u PE.≡ v → t ⇛ v ∷ A
step-⇚∷≡˘ _ _ t⇛u PE.refl = t⇛u

syntax step-⇚∷≡˘ v A t⇒u u≡v = v ∷ A ≡˘⟨ u≡v ⟩⇚∷ t⇒u

-- A reasoning step that uses (Agda's) definitional equality.

_∷_≡⟨⟩⇚∷_ : ∀ u A → t ⇛ u ∷ A → t ⇛ u ∷ A
_ ∷ _ ≡⟨⟩⇚∷ t⇛u = t⇛u

{-# INLINE _∷_≡⟨⟩⇚∷_ #-}

-- A combinator that can be used as the last one in a chain of
-- reasoning steps.

finally-⇚∷ : ∀ u A t → t ⇛ u ∷ A → t ⇛ u ∷ A
finally-⇚∷ _ _ _ t⇛u = t⇛u

syntax finally-⇚∷ u A t t⇛u = u ∷ A ⇚⟨ t⇛u ⟩∎∷ t ∎

{-# INLINE finally-⇚∷ #-}

opaque

  -- A variant of finally-⇚∷.

  finally-⇐*∷ : ∀ u A t → Δ ⊢ t ⇒* u ∷ A → t ⇛ u ∷ A
  finally-⇐*∷ _ _ _ = finally-⇐* _ _

  syntax finally-⇐*∷ u A t t⇒u = u ∷ A ⇐*⟨ t⇒u ⟩∎⇚∷ t ∎

  {-# INLINE finally-⇐*∷ #-}

opaque

  -- A variant of finally-⇐*∷.

  finally-⇐∷ : ∀ u A t → Δ ⊢ t ⇒ u ∷ A → t ⇛ u ∷ A
  finally-⇐∷ _ _ _ = finally-⇐ _ _

  syntax finally-⇐∷ u A t t⇒u = u ∷ A ⇐⟨ t⇒u ⟩∎⇚∷ t ∎

  {-# INLINE finally-⇐∷ #-}

-- A variant of finally-⇐* that makes it possible to end the chain of
-- reasoning steps with a propositional equality, without the use of
-- _∷_∎⟨_⟩⇛.

finally-⇚≡∷ : ∀ v A → u PE.≡ t → u ⇛ v ∷ A → t ⇛ v ∷ A
finally-⇚≡∷ _ _ PE.refl u⇛v = u⇛v

syntax finally-⇚≡∷ v A u≡t u⇛v = v ∷ A ⇚⟨ u⇛v ⟩∎∷≡ u≡t

opaque

  -- A variant of finally-⇚≡∷.

  finally-⇐*≡∷ : ∀ v A → u PE.≡ t → Δ ⊢ u ⇒* v ∷ A → t ⇛ v ∷ A
  finally-⇐*≡∷ _ _ = finally-⇐*≡ _

  syntax finally-⇐*≡∷ v A u≡t u⇒v = v ∷ A ⇐*⟨ u⇒v ⟩∎⇚∷≡ u≡t

opaque

  -- A variant of finally-⇚≡∷.

  finally-⇐≡∷ : ∀ v A → u PE.≡ t → Δ ⊢ u ⇒ v ∷ A → t ⇛ v ∷ A
  finally-⇐≡∷ _ _ = finally-⇐≡ _

  syntax finally-⇐≡∷ v A u≡t u⇒v = v ∷ A ⇐⟨ u⇒v ⟩∎⇚∷≡ u≡t

------------------------------------------------------------------------
-- A combinator for left-to-right or right-to-left reductions with
-- explicit types

infix -1 _∷_∎⟨_⟩⇛

-- Reflexivity.

_∷_∎⟨_⟩⇛ : ∀ t A → Δ ⊢ t ∷ A → t ⇛ t ∷ A
_ ∷ _ ∎⟨ ⊢t ⟩⇛ = ⇒*→⇛ (id ⊢t)

{-# INLINE _∷_∎⟨_⟩⇛ #-}

------------------------------------------------------------------------
-- Conversion combinators

infix -2 step-⇛-conv step-⇛-conv˘ step-⇛-conv-≡ step-⇛-conv-≡˘

opaque

  -- Conversion.

  step-⇛-conv : t ⇛ u ∷ B → Δ ⊢ A ≡ B → t ⇛ u ∷ A
  step-⇛-conv t⇛u A≡B = conv-⇛ t⇛u (sym A≡B)

  syntax step-⇛-conv t⇛u A≡B = ⟨ A≡B ⟩⇛ t⇛u

opaque

  -- Conversion.

  step-⇛-conv˘ : t ⇛ u ∷ B → Δ ⊢ B ≡ A → t ⇛ u ∷ A
  step-⇛-conv˘ t⇛u B≡A = conv-⇛ t⇛u B≡A

  syntax step-⇛-conv˘ t⇛u B≡A = ˘⟨ B≡A ⟩⇛ t⇛u

-- Conversion using propositional equality.

step-⇛-conv-≡ : t ⇛ u ∷ B → A PE.≡ B → t ⇛ u ∷ A
step-⇛-conv-≡ t⇛u PE.refl = t⇛u

syntax step-⇛-conv-≡ t⇛u A≡B = ⟨ A≡B ⟩⇛≡ t⇛u

-- Conversion using propositional equality.

step-⇛-conv-≡˘ : t ⇛ u ∷ B → B PE.≡ A → t ⇛ u ∷ A
step-⇛-conv-≡˘ t⇛u PE.refl = t⇛u

syntax step-⇛-conv-≡˘ t⇛u B≡A = ˘⟨ B≡A ⟩⇛≡ t⇛u

------------------------------------------------------------------------
-- Conversion combinators for left-to-right reductions with explicit
-- types

infix -2 step-∷⇛-conv step-∷⇛-conv˘ step-∷⇛-conv-≡ step-∷⇛-conv-≡˘

opaque

  -- Conversion.

  step-∷⇛-conv : ∀ A → t ⇛ u ∷ B → Δ ⊢ A ≡ B → t ⇛ u ∷ A
  step-∷⇛-conv _ = step-⇛-conv

  syntax step-∷⇛-conv A t⇛u A≡B = ∷ A ⟨ A≡B ⟩⇛ t⇛u

opaque

  -- Conversion.

  step-∷⇛-conv˘ : ∀ A → t ⇛ u ∷ B → Δ ⊢ B ≡ A → t ⇛ u ∷ A
  step-∷⇛-conv˘ _ = step-⇛-conv˘

  syntax step-∷⇛-conv˘ A t⇛u B≡A = ∷ A ˘⟨ B≡A ⟩⇛ t⇛u

-- Conversion using propositional equality.

step-∷⇛-conv-≡ : ∀ A → t ⇛ u ∷ B → A PE.≡ B → t ⇛ u ∷ A
step-∷⇛-conv-≡ _ t⇛u PE.refl = t⇛u

syntax step-∷⇛-conv-≡ A t⇛u A≡B = ∷ A ⟨ A≡B ⟩⇛≡ t⇛u

-- Conversion using propositional equality.

step-∷⇛-conv-≡˘ : ∀ A → t ⇛ u ∷ B → B PE.≡ A → t ⇛ u ∷ A
step-∷⇛-conv-≡˘ _ t⇛u PE.refl = t⇛u

syntax step-∷⇛-conv-≡˘ A t⇛u B≡A = ∷ A ˘⟨ B≡A ⟩⇛≡ t⇛u

------------------------------------------------------------------------
-- Conversion combinators for right-to-left reductions with explicit
-- types

infix -2 step-∷⇚-conv step-∷⇚-conv˘ step-∷⇚-conv-≡ step-∷⇚-conv-≡˘

opaque

  -- Conversion.

  step-∷⇚-conv : ∀ A → t ⇛ u ∷ B → Δ ⊢ A ≡ B → t ⇛ u ∷ A
  step-∷⇚-conv _ = step-⇛-conv

  syntax step-∷⇚-conv A t⇛u A≡B = ∷ A ⟨ A≡B ⟩⇚ t⇛u

opaque

  -- Conversion.

  step-∷⇚-conv˘ : ∀ A → t ⇛ u ∷ B → Δ ⊢ B ≡ A → t ⇛ u ∷ A
  step-∷⇚-conv˘ _ = step-⇛-conv˘

  syntax step-∷⇚-conv˘ A t⇛u B≡A = ∷ A ˘⟨ B≡A ⟩⇚ t⇛u

-- Conversion using propositional equality.

step-∷⇚-conv-≡ : ∀ A → t ⇛ u ∷ B → A PE.≡ B → t ⇛ u ∷ A
step-∷⇚-conv-≡ _ t⇛u PE.refl = t⇛u

syntax step-∷⇚-conv-≡ A t⇛u A≡B = ∷ A ⟨ A≡B ⟩⇚≡ t⇛u

-- Conversion using propositional equality.

step-∷⇚-conv-≡˘ : ∀ A → t ⇛ u ∷ B → B PE.≡ A → t ⇛ u ∷ A
step-∷⇚-conv-≡˘ _ t⇛u PE.refl = t⇛u

syntax step-∷⇚-conv-≡˘ A t⇛u B≡A = ∷ A ˘⟨ B≡A ⟩⇚≡ t⇛u
