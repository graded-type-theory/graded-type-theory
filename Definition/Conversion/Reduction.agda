------------------------------------------------------------------------
-- Weak head expansion of algorithmic equality.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Conversion.Reduction
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.RedSteps R
open import Definition.Conversion R

open import Tools.Nat

private
  variable
    n : Nat
    Γ : Con Term n

-- Weak head expansion of algorithmic equality of types.
reductionConv↑ : ∀ {A A′ B B′}
               → Γ ⊢ A ⇒* A′
               → Γ ⊢ B ⇒* B′
               → Γ ⊢ A′ [conv↑] B′
               → Γ ⊢ A  [conv↑] B
reductionConv↑ A⇒* B⇒* ([↑] A″ B″ D D′ whnfA″ whnfB″ A″<>B″) =
  [↑] A″ B″ (A⇒* ⇨* D) (B⇒* ⇨* D′) whnfA″ whnfB″ A″<>B″

-- Weak head expansion of algorithmic equality of terms.
reductionConv↑Term : ∀ {t t′ u u′ A B}
                   → Γ ⊢ A ⇒* B
                   → Γ ⊢ t ⇒* t′ ∷ B
                   → Γ ⊢ u ⇒* u′ ∷ B
                   → Γ ⊢ t′ [conv↑] u′ ∷ B
                   → Γ ⊢ t  [conv↑] u  ∷ A
reductionConv↑Term A⇒* t⇒* u⇒* ([↑]ₜ B′ t″ u″ D d d′ whnfB′ whnft″ whnfu″ t″<>u″) =
  [↑]ₜ B′ t″ u″
       (A⇒* ⇨* D)
       ((conv* t⇒* (subset* D)) ⇨∷* d)
       ((conv* u⇒* (subset* D)) ⇨∷* d′)
       whnfB′ whnft″ whnfu″ t″<>u″
