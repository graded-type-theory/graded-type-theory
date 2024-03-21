------------------------------------------------------------------------
-- Assumptions used to prove decidability of type-checking (for
-- certain contexts, types and terms)
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typechecking.Decidable.Assumptions
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Tools.PropositionalEquality
open import Tools.Relation

record Assumptions : Set a where
  infix 10 _≟_
  field
    -- Equality is assumed to be decidable for M.
    _≟_ : Decidable (_≡_ {A = M})

    -- It is decidable whether the Unit types are allowed.
    Unit-allowed? : ∀ s → Dec (Unit-allowed s)

    -- ΠΣ-allowed is pointwise decidable.
    ΠΣ-allowed? : ∀ b p q → Dec (ΠΣ-allowed b p q)

    -- It is decidable whether the K rule is allowed.
    K-allowed? : Dec K-allowed

    -- It is decidable whether []-cong is allowed for a given
    -- strength.
    []-cong-allowed? : ∀ s → Dec ([]-cong-allowed s)
