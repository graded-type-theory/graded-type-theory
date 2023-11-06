------------------------------------------------------------------------
-- Some properties related to typing and Erased (without η-equality).
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
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Consequences.DerivedRules.Sigma R

open Fstᵣ-sndᵣ (𝟘 ∧ 𝟙) 𝟘

open import Definition.Untyped M hiding (_∷_; _[_])

open import Graded.Derived.Erased.NoEta.Untyped 𝕄

open import Tools.Function
open import Tools.Product

private variable
  Γ       : Con Term _
  A t u : Term _

-- Some lemmas that are proved under the assumption that Erased
-- without η-equality is allowed.

module _ (Erased-ok@(Unit-ok , Σ-ok) : Erased-allowed Σᵣ) where

  open import Graded.Derived.Erased.Typed R Erased-ok public

  -- A β-rule for Erased.

  Erased-β :
    Γ ⊢ t ∷ A →
    Γ ⊢ erased A [ t ] ≡ t ∷ A
  Erased-β ⊢t =
    fstᵣ-β-≡ (Unitⱼ ⊢ΓA Unit-ok) ⊢t (starⱼ ⊢Γ Unit-ok) Σ-ok
    where
    ⊢Γ = wfTerm ⊢t
    ⊢ΓA = ⊢Γ ∙ syntacticTerm ⊢t

-- An elimination rule for Erased.

erasedⱼ : Γ ⊢ t ∷ Erased A → Γ ⊢ erased A t ∷ A
erasedⱼ ⊢t = fstᵣⱼ ⊢t

-- A corresponding congruence rule.

erased-cong : Γ ⊢ t ≡ u ∷ Erased A → Γ ⊢ erased A t ≡ erased A u ∷ A
erased-cong t≡u =
  case syntacticEqTerm t≡u of λ {
    (⊢Erased , _ , _) →
  case syntacticΣ ⊢Erased of λ {
    (⊢A , ⊢Unit) →
  case inversion-Unit ⊢Unit of λ
    Unit-ok →
  fstᵣ-cong (refl ⊢A) (Unitⱼ (wf ⊢A ∙ ⊢A) Unit-ok) t≡u }}
