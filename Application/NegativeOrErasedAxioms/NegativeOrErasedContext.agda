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
  (𝟘≰𝟙 : ¬ 𝟘 ≤ 𝟙)
  (R : Type-restrictions M)
  where

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.Typed.Weakening R
open import Graded.Context 𝕄
open import Graded.Modality.Properties 𝕄 hiding (𝟘≰𝟙)
open import Application.NegativeOrErasedAxioms.NegativeOrErasedType 𝕄 R

open import Tools.Bool
open import Tools.Empty
open import Tools.Fin
open import Tools.Nat using (Nat)
import Tools.PropositionalEquality as PE

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
