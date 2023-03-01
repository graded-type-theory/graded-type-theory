{-# OPTIONS --without-K --safe #-}

open import Tools.Relation

module Application.NegativeAxioms.NegativeContext {a ℓ} (M′ : Setoid a ℓ) where

open Setoid M′ using () renaming (Carrier to M)

open import Definition.Untyped M
open import Definition.Typed M′
open import Definition.Typed.Weakening M′
open import Application.NegativeAxioms.NegativeType M′

open import Tools.Fin
open import Tools.Level
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

data NegativeContext : Ctx m → Set (a ⊔ ℓ) where
  ε   : NegativeContext ε
  _∙_ : NegativeContext Γ → NegativeType Γ A → NegativeContext (Γ ∙ A)

-- Lemma: Any entry in negative context is a negative type (needs weakening).

lookupNegative : ⊢ Γ → NegativeContext Γ → (x ∷ A ∈ Γ) → NegativeType Γ A
lookupNegative ⊢Γ∙A            (nΓ ∙ nA) here
  = wkNeg (step id) ⊢Γ∙A nA
lookupNegative ⊢Γ∙A@(⊢Γ ∙ Γ⊢A) (nΓ ∙ nA) (there h)
  = wkNeg (step id) ⊢Γ∙A (lookupNegative ⊢Γ nΓ h)
