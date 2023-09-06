------------------------------------------------------------------------
-- Contexts in which all types either are negative or erased.
------------------------------------------------------------------------

open import Graded.Modality
open import Definition.Typed.Restrictions
open import Tools.Nullary

module Application.NegativeOrErasedAxioms.NegativeOrErasedContext
  {a} {M : Set a}
  (𝕄 : Modality M)
  (open Modality 𝕄)
  (R : Type-restrictions M)
  where

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.Typed.Weakening R
open import Graded.Context 𝕄
open import Graded.Modality.Properties 𝕄
open import Application.NegativeOrErasedAxioms.NegativeOrErasedType 𝕄 R

open import Tools.Bool
open import Tools.Empty
open import Tools.Fin
open import Tools.Nat using (Nat)
open import Tools.PropositionalEquality as PE using (_≢_)

private
  Ctx = Con Term
  variable
    m : Nat
    Γ : Ctx m
    A : Term m
    x : Fin m
    γ δ : Conₘ m
    p : M

-- Negative or Erased contexts
---------------------------------------------------------------------------

-- A context is negative or erased if all of its type entries are negative or erased.

data NegativeErasedContext : Ctx m → Conₘ m → Set a where
  ε   : NegativeErasedContext ε ε
  _∙_ : NegativeErasedContext Γ γ → NegativeType Γ A → NegativeErasedContext (Γ ∙ A) (γ ∙ p)
  _∙𝟘 : NegativeErasedContext Γ γ → NegativeErasedContext (Γ ∙ A) (γ ∙ 𝟘)

-- In a negative erased context the entries with non-zero grades have
-- negative types.

lookupNegative :
  ⊢ Γ → NegativeErasedContext Γ γ → x ∷ A ∈ Γ → γ ⟨ x ⟩ ≢ 𝟘 →
  NegativeType Γ A
lookupNegative ⊢Γ∙A (nΓγ ∙ nA) here _ =
  wkNeg (step id) ⊢Γ∙A nA
lookupNegative ⊢Γ∙A@(⊢Γ ∙ Γ⊢A) (nΓγ ∙ nA) (there h) ≢𝟘 =
  wkNeg (step id) ⊢Γ∙A (lookupNegative ⊢Γ nΓγ h ≢𝟘)
lookupNegative ⊢Γ∙A (nΓγ ∙𝟘) here ≢𝟘 =
  ⊥-elim (≢𝟘 PE.refl)
lookupNegative ⊢Γ∙A@(⊢Γ ∙ Γ⊢A) (nΓγ ∙𝟘) (there h) ≢𝟘 =
  wkNeg (step id) ⊢Γ∙A (lookupNegative ⊢Γ nΓγ h ≢𝟘)

erasedContext : NegativeErasedContext Γ 𝟘ᶜ
erasedContext {Γ = ε} = ε
erasedContext {Γ = Γ ∙ A} = erasedContext ∙𝟘

-- If 𝟘ᵐ is allowed, then NegativeErasedContext is upwards closed in
-- its second argument.

NegativeErasedContext-upwards-closed :
  T 𝟘ᵐ-allowed →
  γ ≤ᶜ δ →
  NegativeErasedContext Γ γ →
  NegativeErasedContext Γ δ
NegativeErasedContext-upwards-closed
  {γ = ε} {δ = ε} _ ε ε =
  ε
NegativeErasedContext-upwards-closed
  {γ = _ ∙ _} {δ = _ ∙ _} ok (γ≤δ ∙ _) (neΓγ ∙ neg) =
  NegativeErasedContext-upwards-closed ok γ≤δ neΓγ ∙ neg
NegativeErasedContext-upwards-closed
  {γ = _ ∙ _} {δ = _ ∙ _} ok (γ≤δ ∙ 𝟘≤p) (neΓγ ∙𝟘) =
  PE.subst (λ p → NegativeErasedContext _ (_ ∙ p))
    (PE.sym (𝟘≮ ok 𝟘≤p))
    (NegativeErasedContext-upwards-closed ok γ≤δ neΓγ ∙𝟘)
