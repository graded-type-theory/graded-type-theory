------------------------------------------------------------------------
-- Some properties related to typing and Erased (with η-equality).
------------------------------------------------------------------------

import Graded.Modality
open import Definition.Typed.Restrictions
open import Tools.Product

module Graded.Derived.Erased.Eta.Typed
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (R : Type-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Syntactic R

open import Definition.Untyped M hiding (_∷_; _[_])

import Graded.Derived.Erased.Eta.Typed.Primitive R as P
open import Graded.Derived.Erased.Eta.Untyped 𝕄

open import Tools.Function

private variable
  Γ       : Con Term _
  A B t u : Term _

-- Some lemmas that are proved under the assumption that Erased
-- with η-equality is allowed.

module _ (Erased-ok@(Unit-ok , Σ-ok) : Erased-allowed Σₚ) where

  open import Graded.Derived.Erased.Typed R Erased-ok public

  private module P′ = P Erased-ok

  -- A β-rule for Erased.

  Erased-β :
    Γ ⊢ t ∷ A →
    Γ ⊢ erased [ t ] ≡ t ∷ A
  Erased-β ⊢t = P′.Erased-β ⊢A ⊢t
    where
    ⊢A = syntacticTerm ⊢t

-- An elimination rule for Erased.

erasedⱼ : Γ ⊢ t ∷ Erased A → Γ ⊢ erased t ∷ A
erasedⱼ ⊢t =
  case inversion-ΠΣ (syntacticTerm ⊢t) of λ {
    (⊢A , ⊢Unit , Σ-ok) →
  P.erasedⱼ (inversion-Unit ⊢Unit , Σ-ok) ⊢A ⊢t }

-- A corresponding congruence rule.

erased-cong : Γ ⊢ t ≡ u ∷ Erased A → Γ ⊢ erased t ≡ erased u ∷ A
erased-cong t≡u =
  case inversion-ΠΣ (syntacticEqTerm t≡u .proj₁) of λ {
    (⊢A , ⊢Unit , Σₚ-ok) →
  P.erased-cong (inversion-Unit ⊢Unit , Σₚ-ok) ⊢A t≡u }

-- An η-rule for Erased.

Erased-η :
  Γ ⊢ t ∷ Erased A →
  Γ ⊢ u ∷ Erased A →
  Γ ⊢ erased t ≡ erased u ∷ A →
  Γ ⊢ t ≡ u ∷ Erased A
Erased-η ⊢t =
  case inversion-ΠΣ (syntacticTerm ⊢t) of λ {
    (⊢A , ⊢Unit , Σₚ-ok) →
  P.Erased-η (inversion-Unit ⊢Unit , Σₚ-ok) ⊢A ⊢t }

-- An instance of the η-rule.

[erased] :
  Γ ⊢ t ∷ Erased A →
  Γ ⊢ [ erased t ] ≡ t ∷ Erased A
[erased] ⊢t =
  case inversion-ΠΣ (syntacticTerm ⊢t) of λ {
    (⊢A , ⊢Unit , Σₚ-ok) →
  P.[erased] (inversion-Unit ⊢Unit , Σₚ-ok) ⊢A ⊢t }
