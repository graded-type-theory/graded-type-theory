------------------------------------------------------------------------
-- Weak head expansion of algorithmic equality.
------------------------------------------------------------------------

open import Configuration-types
open import Graded.Modality

module Definition.Conversion.Reduction
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TC : Type-configuration 𝕄)
  where

open import Definition.Untyped M
open import Definition.Typed TC
open import Definition.Typed.Properties TC
open import Definition.Conversion TC

open import Tools.Nat
open import Tools.Product

private variable
  Γ : Cons _ _

-- Weak head expansion of algorithmic equality of types.
reductionConv↑ : ∀ {A A′ B B′}
               → Γ ⊢ A ⇒* A′
               → Γ ⊢ B ⇒* B′
               → Γ ⊢ A′ [conv↑] B′
               → Γ ⊢ A  [conv↑] B
reductionConv↑ A⇒* B⇒* ([↑] A″ B″ D D′ A″<>B″) =
  [↑] A″ B″ (⇒*→↘→↘ A⇒* D) (⇒*→↘→↘ B⇒* D′) A″<>B″

-- Weak head expansion of algorithmic equality of terms.
reductionConv↑Term : ∀ {t t′ u u′ A B}
                   → Γ ⊢ A ⇒* B
                   → Γ ⊢ t ⇒* t′ ∷ B
                   → Γ ⊢ u ⇒* u′ ∷ B
                   → Γ ⊢ t′ [conv↑] u′ ∷ B
                   → Γ ⊢ t  [conv↑] u  ∷ A
reductionConv↑Term A⇒* t⇒* u⇒* ([↑]ₜ B′ t″ u″ D@(D′ , _) d d′ t″<>u″) =
  [↑]ₜ B′ t″ u″
       (⇒*→↘→↘ A⇒* D)
       (⇒*∷→↘∷→↘∷ (conv* t⇒* (subset* D′)) d)
       (⇒*∷→↘∷→↘∷ (conv* u⇒* (subset* D′)) d′)
       t″<>u″
