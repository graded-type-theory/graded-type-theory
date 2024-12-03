------------------------------------------------------------------------
-- Negative contexts (contexts containing only negative types).
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Application.NegativeAxioms.NegativeContext
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R
open import Application.NegativeAxioms.NegativeType R

open import Tools.Fin
open import Tools.Nat

private
  Ctx = Con Term
  variable
    m : Nat
    Γ : Ctx m
    A : Term m
    x : Fin m

-- Negative contexts
---------------------------------------------------------------------------

-- A context is negative if all of its type entries are negative.

data NegativeContext : Ctx m → Set a where
  ε   : NegativeContext ε
  _∙_ : NegativeContext Γ → NegativeType Γ A → NegativeContext (Γ ∙ A)

-- Lemma: Any entry in negative context is a negative type (needs weakening).

lookupNegative : ⊢ Γ → NegativeContext Γ → (x ∷ A ∈ Γ) → NegativeType Γ A
lookupNegative ε      _         ()
lookupNegative (∙ ⊢A) (nΓ ∙ nA) here
  = wkNeg (stepʷ id ⊢A) nA
lookupNegative (∙ ⊢A) (nΓ ∙ nA) (there h)
  = wkNeg (stepʷ id ⊢A) (lookupNegative (wf ⊢A) nΓ h)
