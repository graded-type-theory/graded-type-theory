------------------------------------------------------------------------
-- Decidability of type and term equality.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Tools.Relation
import Tools.PropositionalEquality as PE

module Definition.Typed.Decidable.Equality
  {a} {M : Set a}
  (R : Type-restrictions M)
  (_≟_ : Decidable (PE._≡_ {A = M}))
  where


open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed R
open import Definition.Conversion.Decidable R _≟_
open import Definition.Conversion.Soundness R
open import Definition.Conversion.Consequences.Completeness R

open import Tools.Nat

private
  variable
    n : Nat
    Γ : Con Term n

-- Decidability of conversion of well-formed types
decEq : ∀ {A B} → Γ ⊢ A → Γ ⊢ B → Dec (Γ ⊢ A ≡ B)
decEq ⊢A ⊢B = map soundnessConv↑ completeEq
                  (decConv↑ (completeEq (refl ⊢A))
                            (completeEq (refl ⊢B)))

-- Decidability of conversion of well-formed terms
decEqTerm : ∀ {t u A} → Γ ⊢ t ∷ A → Γ ⊢ u ∷ A → Dec (Γ ⊢ t ≡ u ∷ A)
decEqTerm ⊢t ⊢u = map soundnessConv↑Term completeEqTerm
                      (decConv↑Term (completeEqTerm (refl ⊢t))
                                    (completeEqTerm (refl ⊢u)))
