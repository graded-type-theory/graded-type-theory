------------------------------------------------------------------------
-- A lemma related to definitional equality for variables
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Conversion.Consequences.Var
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Conversion R
open import Definition.Conversion.Consequences.Completeness R
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Untyped M hiding (_∷_)

open import Tools.Fin
open import Tools.Function
import Tools.PropositionalEquality as PE

private variable
  x   : Fin _
  Γ   : Con Term _
  A t : Term _

-- If A is a type without η-equality, then the only WHNF that a
-- variable x of type A is definitionally equal to is x.

var-only-equal-to-itself :
  No-η-equality A → Whnf t → Γ ⊢ var x ≡ t ∷ A → var x PE.≡ t
var-only-equal-to-itself =
  λ A-no-η t-whnf → [conv↑]∷-lemma A-no-η t-whnf ∘→ completeEqTerm
  where
  ~↑-lemma : Γ ⊢ var x ~ t ↑ A → var x PE.≡ t
  ~↑-lemma (var-refl _ PE.refl) = PE.refl

  ~↓-lemma : Γ ⊢ var x ~ t ↓ A → var x PE.≡ t
  ~↓-lemma x≡t = ~↑-lemma (_⊢_~_↓_.k~l x≡t)

  [conv↓]-lemma : Γ ⊢ var x [conv↓] A → var x PE.≡ A
  [conv↓]-lemma (ne x≡A) = ~↓-lemma x≡A

  [conv↓]∷-lemma :
    No-η-equality A → Whnf t → Γ ⊢ var x [conv↓] t ∷ A → var x PE.≡ t
  [conv↓]∷-lemma = λ where
    _        _ (univ _ _ x≡t)     → [conv↓]-lemma x≡t
    _        _ (Σᵣ-ins _ _ x≡t)   → ~↓-lemma x≡t
    _        _ (Empty-ins x≡t)    → ~↓-lemma x≡t
    _        _ (ℕ-ins x≡t)        → ~↓-lemma x≡t
    _        _ (Id-ins _ x≡t)     → ~↓-lemma x≡t
    _        _ (ne-ins _ _ _ x≡t) → ~↓-lemma x≡t
    (neₙ ()) _ (Unit-ins _)
    (neₙ ()) _ (η-eq _ _ _ _ _)
    (neₙ ()) _ (Σ-η _ _ _ _ _ _)
    (neₙ ()) _ (η-unit _ _ _ _)

  [conv↑]∷-lemma :
    No-η-equality A → Whnf t → Γ ⊢ var x [conv↑] t ∷ A → var x PE.≡ t
  [conv↑]∷-lemma A-no-η t-whnf x≡t =
    case whnfRed* D (No-η-equality→Whnf A-no-η) of λ {
      PE.refl →
    case whnfRed*Term d (ne (var _)) of λ {
      PE.refl →
    case whnfRed*Term d′ t-whnf of λ {
      PE.refl →
    [conv↓]∷-lemma A-no-η t-whnf t<>u }}}
    where
    open _⊢_[conv↑]_∷_ x≡t
