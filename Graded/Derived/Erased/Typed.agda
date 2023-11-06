------------------------------------------------------------------------
-- Some properties related to typing and Erased that hold both with and
-- without η-equality.
------------------------------------------------------------------------

import Graded.Modality
open import Definition.Typed.Restrictions
open import Tools.Product

module Graded.Derived.Erased.Typed
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  -- The Erased type is assumed to be allowed.
  {s}
  (Erased-ok@(Unit-ok , Σ-ok) : Erased-allowed s)
  where

open Modality 𝕄

open import Definition.Typed R
open import Definition.Typed.Consequences.Syntactic R

open import Definition.Untyped M hiding (_∷_; _[_])

import Graded.Derived.Erased.Typed.Primitive R as P
open import Graded.Derived.Erased.Untyped 𝕄 s

private variable
  Γ       : Con Term _
  A B t u : Term _

private module P′ = P Erased-ok

-- A formation rule for Erased.

Erasedⱼ : Γ ⊢ A → Γ ⊢ Erased A
Erasedⱼ = P′.Erasedⱼ

-- A corresponding congruence rule.

Erased-cong :
  Γ ⊢ A ≡ B →
  Γ ⊢ Erased A ≡ Erased B
Erased-cong A≡B = P′.Erased-cong ⊢A A≡B
  where
  ⊢A = syntacticEq A≡B .proj₁

-- An introduction rule for U.

Erasedⱼ-U : Γ ⊢ A ∷ U → Γ ⊢ Erased A ∷ U
Erasedⱼ-U ⊢A∷U = P′.Erasedⱼ-U ⊢A ⊢A∷U
  where
  ⊢A = univ ⊢A∷U

-- A corresponding congruence rule.

Erased-cong-U :
  Γ ⊢ A ≡ B ∷ U →
  Γ ⊢ Erased A ≡ Erased B ∷ U
Erased-cong-U A≡B = P′.Erased-cong-U ⊢A A≡B
  where
  ⊢A = univ (syntacticEqTerm A≡B .proj₂ .proj₁)

-- An introduction rule for Erased.

[]ⱼ : Γ ⊢ t ∷ A → Γ ⊢ [ t ] ∷ Erased A
[]ⱼ ⊢t = P′.[]ⱼ ⊢A ⊢t
  where
  ⊢A = syntacticTerm ⊢t

-- A corresponding congruence rule.

[]-cong′ :
  Γ ⊢ t ≡ u ∷ A → Γ ⊢ [ t ] ≡ [ u ] ∷ Erased A
[]-cong′ t≡u = P′.[]-cong′ ⊢A t≡u
  where
  ⊢A = syntacticEqTerm t≡u .proj₁
