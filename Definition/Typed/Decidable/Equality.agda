------------------------------------------------------------------------
-- Decidability of type and term equality (in the absence of equality
-- reflection)
------------------------------------------------------------------------

open import Configuration-types
open import Graded.Modality
open import Tools.Relation
import Tools.PropositionalEquality as PE

module Definition.Typed.Decidable.Equality
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TC : Type-configuration 𝕄)
  (open Type-configuration TC)
  (_≟_ : Decidable (PE._≡_ {A = M}))
  ⦃ no-equality-reflection : No-equality-reflection ⦄
  where


open import Definition.Untyped M
open import Definition.Typed TC
open import Definition.Conversion.Decidable TC _≟_
open import Definition.Conversion.Soundness TC
open import Definition.Conversion.Consequences.Completeness TC

open import Tools.Nat

private
  variable
    m n : Nat
    Γ : Cons m n

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
