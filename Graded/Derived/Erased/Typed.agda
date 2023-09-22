------------------------------------------------------------------------
-- Some properties related to typing and Erased
------------------------------------------------------------------------

import Graded.Modality
open import Definition.Typed.Restrictions
open import Tools.Product

module Graded.Derived.Erased.Typed
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (open Modality 𝕄)
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  -- Erased is assumed to be allowed.
  (Erased-ok@(Unit-ok , Σₚ-ok) : Erased-allowed)
  where

open import Definition.Typed R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Syntactic R

open import Definition.Untyped M hiding (_∷_; _[_])

import Graded.Derived.Erased.Typed.Primitive R Erased-ok as P
open import Graded.Derived.Erased.Untyped 𝕄

private variable
  Γ       : Con Term _
  A B t u : Term _

-- A formation rule for Erased.

Erasedⱼ : Γ ⊢ A → Γ ⊢ Erased A
Erasedⱼ = P.Erasedⱼ

-- A corresponding congruence rule.

Erased-cong :
  Γ ⊢ A ≡ B →
  Γ ⊢ Erased A ≡ Erased B
Erased-cong A≡B = P.Erased-cong ⊢A A≡B
  where
  ⊢A = syntacticEq A≡B .proj₁

-- An introduction rule for U.

Erasedⱼ-U : Γ ⊢ A ∷ U → Γ ⊢ Erased A ∷ U
Erasedⱼ-U ⊢A∷U = P.Erasedⱼ-U ⊢A ⊢A∷U
  where
  ⊢A = univ ⊢A∷U

-- A corresponding congruence rule.

Erased-cong-U :
  Γ ⊢ A ≡ B ∷ U →
  Γ ⊢ Erased A ≡ Erased B ∷ U
Erased-cong-U A≡B = P.Erased-cong-U ⊢A A≡B
  where
  ⊢A = univ (syntacticEqTerm A≡B .proj₂ .proj₁)

-- An introduction rule for Erased.

[]ⱼ : Γ ⊢ t ∷ A → Γ ⊢ [ t ] ∷ Erased A
[]ⱼ ⊢t = P.[]ⱼ ⊢A ⊢t
  where
  ⊢A = syntacticTerm ⊢t

-- A corresponding congruence rule.

[]-cong′ :
  Γ ⊢ t ≡ u ∷ A → Γ ⊢ [ t ] ≡ [ u ] ∷ Erased A
[]-cong′ t≡u = P.[]-cong′ ⊢A t≡u
  where
  ⊢A = syntacticEqTerm t≡u .proj₁

-- An elimination rule for Erased.

erasedⱼ : Γ ⊢ t ∷ Erased A → Γ ⊢ erased t ∷ A
erasedⱼ ⊢t = P.erasedⱼ ⊢A ⊢t
  where
  ⊢A = inversion-ΠΣ (syntacticTerm ⊢t) .proj₁

-- A corresponding congruence rule.

erased-cong : Γ ⊢ t ≡ u ∷ Erased A → Γ ⊢ erased t ≡ erased u ∷ A
erased-cong t≡u = P.erased-cong ⊢A t≡u
  where
  ⊢A = inversion-ΠΣ (syntacticEqTerm t≡u .proj₁) .proj₁

-- A β-rule for Erased.

Erased-β :
  Γ ⊢ t ∷ A →
  Γ ⊢ erased [ t ] ≡ t ∷ A
Erased-β ⊢t = P.Erased-β ⊢A ⊢t
  where
  ⊢A = syntacticTerm ⊢t

-- An η-rule for Erased.

Erased-η :
  Γ ⊢ t ∷ Erased A →
  Γ ⊢ u ∷ Erased A →
  Γ ⊢ erased t ≡ erased u ∷ A →
  Γ ⊢ t ≡ u ∷ Erased A
Erased-η ⊢t ⊢u t≡u = P.Erased-η ⊢A ⊢t ⊢u t≡u
  where
  ⊢A = syntacticEqTerm t≡u .proj₁

-- An instance of the η-rule.

[erased] :
  Γ ⊢ t ∷ Erased A →
  Γ ⊢ [ erased t ] ≡ t ∷ Erased A
[erased] ⊢t = P.[erased] ⊢A ⊢t
  where
  ⊢A = inversion-ΠΣ (syntacticTerm ⊢t) .proj₁
