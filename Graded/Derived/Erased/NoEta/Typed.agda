------------------------------------------------------------------------
-- Some properties related to typing and the weak variant of Erased
------------------------------------------------------------------------

import Graded.Modality
open import Definition.Typed.Restrictions

module Graded.Derived.Erased.NoEta.Typed
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (R : Type-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Consequences.DerivedRules.Sigma R

open import Definition.Untyped M hiding (_[_])

open import Graded.Derived.Erased.NoEta.Untyped 𝕄
open import Graded.Derived.Erased.Untyped 𝕄 𝕨 hiding (erased)

open import Tools.Function
open import Tools.Product

private variable
  Γ       : Con Term _
  A B t u : Term _

-- A β-rule for Erased.

Erased-β :
  Erasedʷ-allowed →
  Γ ⊢ t ∷ A →
  Γ ⊢ erased A [ t ] ≡ t ∷ A
Erased-β (Unit-ok , Σ-ok) ⊢t =
  fstʷ-β-≡ (Unitⱼ ⊢ΓA Unit-ok) ⊢t (starⱼ ⊢Γ Unit-ok) Σ-ok
  where
  ⊢Γ = wfTerm ⊢t
  ⊢ΓA = ∙ syntacticTerm ⊢t

-- An elimination rule for Erased.

erasedⱼ : Γ ⊢ t ∷ Erased A → Γ ⊢ erased A t ∷ A
erasedⱼ ⊢t = fstʷⱼ ⊢t

-- A corresponding congruence rule.

erased-cong :
  Γ ⊢ A ≡ B → Γ ⊢ t ≡ u ∷ Erased A → Γ ⊢ erased A t ≡ erased B u ∷ A
erased-cong = fstʷ-cong
