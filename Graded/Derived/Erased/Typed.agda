------------------------------------------------------------------------
-- Some properties related to typing and Erased that hold both with and
-- without η-equality.
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

import Graded.Modality
open import Definition.Typed.Restrictions
import Definition.Untyped hiding (_∷_; _[_])

module Graded.Derived.Erased.Typed
  {a} {M : Set a}
  (open Definition.Untyped M)
  (open Graded.Modality M)
  {𝕄 : Modality}
  (R : Type-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Consequences.Syntactic R

import Graded.Derived.Erased.Eta.Typed R as Eta
import Graded.Derived.Erased.NoEta.Typed R as NoEta
import Graded.Derived.Erased.Typed.Primitive R as P
import Graded.Derived.Erased.Untyped 𝕄 as Erased

open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  Γ       : Con Term _
  A B t u : Term _
  s       : Strength

-- Some lemmas that are proved under the assumption that Erased is
-- allowed.

module _ (Erased-ok : Erased-allowed s) where

  open Erased s

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

  opaque
    unfolding erased

    -- A β-rule for Erased.

    Erased-β :
      Γ ⊢ t ∷ A →
      Γ ⊢ erased A [ t ] ≡ t ∷ A
    Erased-β = case PE.singleton s of λ where
      (𝕤 , PE.refl) → Eta.Erased-β Erased-ok
      (𝕨 , PE.refl) → NoEta.Erased-β Erased-ok

module _ where

  open Erased

  opaque
    unfolding erased

    -- An elimination rule for Erased.

    erasedⱼ : Γ ⊢ t ∷ Erased s A → Γ ⊢ erased s A t ∷ A
    erasedⱼ {s} = case PE.singleton s of λ where
      (𝕤 , PE.refl) → Eta.erasedⱼ
      (𝕨 , PE.refl) → NoEta.erasedⱼ

  opaque
    unfolding erased

    -- A corresponding congruence rule.

    erased-cong :
      Γ ⊢ A ≡ B → Γ ⊢ t ≡ u ∷ Erased s A →
      Γ ⊢ erased s A t ≡ erased s B u ∷ A
    erased-cong {s} A≡B = case PE.singleton s of λ where
      (𝕤 , PE.refl) → Eta.erased-cong
      (𝕨 , PE.refl) → NoEta.erased-cong A≡B
