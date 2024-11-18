------------------------------------------------------------------------
-- Some properties related to typing and the strong variant of Erased
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
open import Definition.Typed.Inversion R
open import Definition.Typed.Syntactic R

open import Definition.Untyped M hiding (_[_])
open import Definition.Untyped.Erased 𝕄 𝕤 hiding (erased)
open import Definition.Untyped.Erased.Eta 𝕄

import Graded.Derived.Erased.Eta.Typed.Primitive R as P

open import Tools.Function

private variable
  Γ       : Con Term _
  A B t u : Term _

-- A β-rule for Erased.

Erased-β :
  Erasedˢ-allowed →
  Γ ⊢ t ∷ A →
  Γ ⊢ erased [ t ] ≡ t ∷ A
Erased-β ok ⊢t = P.Erased-β ok ⊢A ⊢t
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
    (⊢A , ⊢Unit , Σˢ-ok) →
  P.erased-cong (inversion-Unit ⊢Unit , Σˢ-ok) ⊢A t≡u }

-- A definitional η-rule for Erased.

Erased-η-≡ :
  Γ ⊢ t ∷ Erased A →
  Γ ⊢ u ∷ Erased A →
  Γ ⊢ erased t ≡ erased u ∷ A →
  Γ ⊢ t ≡ u ∷ Erased A
Erased-η-≡ ⊢t =
  case inversion-ΠΣ (syntacticTerm ⊢t) of λ {
    (⊢A , ⊢Unit , Σˢ-ok) →
  P.Erased-η-≡ (inversion-Unit ⊢Unit , Σˢ-ok) ⊢A ⊢t }

-- An instance of the η-rule.

[erased] :
  Γ ⊢ t ∷ Erased A →
  Γ ⊢ [ erased t ] ≡ t ∷ Erased A
[erased] ⊢t =
  case inversion-ΠΣ (syntacticTerm ⊢t) of λ {
    (⊢A , ⊢Unit , Σˢ-ok) →
  P.[erased] (inversion-Unit ⊢Unit , Σˢ-ok) ⊢A ⊢t }
