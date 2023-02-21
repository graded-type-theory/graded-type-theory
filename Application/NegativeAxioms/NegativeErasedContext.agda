open import Definition.Modality
open import Tools.Empty

module Application.NegativeAxioms.NegativeErasedContext
  {a} {M : Set a} (𝕄 : Modality M)
  (𝟘≰𝟙 : Modality._≤_ 𝕄 (Modality.𝟘 𝕄) (Modality.𝟙 𝕄) → ⊥) where

open Modality 𝕄

open import Definition.Untyped M
open import Definition.Typed M
open import Definition.Typed.Weakening M
open import Definition.Modality.Context 𝕄
open import Definition.Modality.Usage 𝕄
open import Application.NegativeAxioms.NegativeType M


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
    γ : Conₘ m
    p : M

-- Negative or Erased contexts
---------------------------------------------------------------------------

-- A context is negative or erased if all of its type entries are negative or erased.

data NegativeErasedContext : Ctx m → Conₘ m → Set a where
  ε   : NegativeErasedContext ε ε
  _∙_ : NegativeErasedContext Γ γ → NegativeType Γ A → NegativeErasedContext (Γ ∙ A) (γ ∙ p)
  _∙𝟘 : NegativeErasedContext Γ γ → NegativeErasedContext (Γ ∙ A) (γ ∙ 𝟘)

-- Lemma: Any entry in negative erased context is a negative type (needs weakening).

lookupNegative : ⊢ Γ → NegativeErasedContext Γ γ → (x ∷ A ∈ Γ) → (γ ⟨ x ⟩ ≤ 𝟙)
               → NegativeType Γ A
lookupNegative ⊢Γ∙A (nΓγ ∙ nA) here _ =
  wkNeg (step id) ⊢Γ∙A nA
lookupNegative ⊢Γ∙A@(⊢Γ ∙ Γ⊢A) (nΓγ ∙ nA) (there h) p≤𝟙 =
  wkNeg (step id) ⊢Γ∙A (lookupNegative ⊢Γ nΓγ h p≤𝟙)
lookupNegative ⊢Γ∙A (nΓγ ∙𝟘) here p≤𝟙 =
  ⊥-elim (𝟘≰𝟙 p≤𝟙)
lookupNegative ⊢Γ∙A@(⊢Γ ∙ Γ⊢A) (nΓγ ∙𝟘) (there h) p≤𝟙 =
  wkNeg (step id) ⊢Γ∙A (lookupNegative ⊢Γ nΓγ h p≤𝟙)
