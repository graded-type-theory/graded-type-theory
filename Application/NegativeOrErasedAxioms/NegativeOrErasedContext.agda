------------------------------------------------------------------------
-- Contexts in which all types either are negative or erased.
------------------------------------------------------------------------

import Graded.Modality
open import Definition.Typed.Restrictions

module Application.NegativeOrErasedAxioms.NegativeOrErasedContext
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (open Modality 𝕄)
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R
open import Definition.Typed.Weakening.Definition R
open import Graded.Context 𝕄
open import Graded.Modality.Properties 𝕄
open import Application.NegativeOrErasedAxioms.NegativeOrErasedType R

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.PropositionalEquality as PE using (_≡_; _≢_)

private variable
  α m n : Nat
  x     : Fin _
  ∇     : DCon (Term 0) _
  Γ     : Cons _ _
  A t   : Term _
  φ     : Unfolding _
  γ δ   : Conₘ _
  p     : M

-- Negative or Erased contexts
---------------------------------------------------------------------------

-- A definition context is negative if all of its opaque entries have
-- negative types.
--
-- It might make sense to add mode contexts for definitions, in which
-- case it might suffice to require opaque entries to have negative
-- types if the entries have mode 𝟙ᵐ.

data NegativeDefinitionContext : DCon (Term 0) n → Set a where
  ε  : NegativeDefinitionContext ε
  ∙ᵗ : NegativeDefinitionContext ∇ →
       NegativeDefinitionContext (∇ ∙⟨ tra ⟩[ t ∷ A ])
  ∙ᵒ : NegativeDefinitionContext ∇ →
       NegativeType (∇ » ε) A →
       NegativeDefinitionContext (∇ ∙⟨ opa φ ⟩[ t ∷ A ])

-- A pair consisting of a context pair and a usage context is
-- negative/erased if the definition context is negative and all the
-- variables are erased or have negative types.

data NegativeErasedContext : Cons m n → Conₘ n → Set a where
  ε   : NegativeDefinitionContext ∇ →
        NegativeErasedContext (∇ » ε) ε
  _∙_ : NegativeErasedContext Γ γ → NegativeType Γ A →
        NegativeErasedContext (Γ »∙ A) (γ ∙ p)
  _∙𝟘 : NegativeErasedContext Γ γ →
        NegativeErasedContext (Γ »∙ A) (γ ∙ 𝟘)

opaque

  -- If a context triple is negative/erased, then the triple's
  -- definition context is negative.

  negative-definition-context :
    NegativeErasedContext Γ γ → NegativeDefinitionContext (Γ .defs)
  negative-definition-context (ε ∇-neg) =
    ∇-neg
  negative-definition-context (Γ-neg ∙𝟘) =
    negative-definition-context Γ-neg
  negative-definition-context (Γ-neg ∙ _) =
    negative-definition-context Γ-neg

-- In a negative context the entries with non-zero grades have
-- negative types.

lookupNegative :
  ⊢ Γ → NegativeErasedContext Γ γ → x ∷ A ∈ Γ .vars → γ ⟨ x ⟩ ≢ 𝟘 →
  NegativeType Γ A
lookupNegative (ε _)  _          ()
lookupNegative (∙ ⊢A) (nΓγ ∙ nA) here _ =
  wkNeg (stepʷ id ⊢A) nA
lookupNegative (∙ ⊢A) (nΓγ ∙ nA) (there h) ≢𝟘 =
  wkNeg (stepʷ id ⊢A) (lookupNegative (wf ⊢A) nΓγ h ≢𝟘)
lookupNegative ⊢Γ∙A (nΓγ ∙𝟘) here ≢𝟘 =
  ⊥-elim (≢𝟘 PE.refl)
lookupNegative (∙ ⊢A) (nΓγ ∙𝟘) (there h) ≢𝟘 =
  wkNeg (stepʷ id ⊢A) (lookupNegative (wf ⊢A) nΓγ h ≢𝟘)

opaque

  -- If α points to an opaque definition with type A in a negative,
  -- well-formed definition context, then A is negative.

  lookupOpaqueNegative :
    α ↦⊘∷ A ∈ ∇ →
    » ∇ →
    NegativeDefinitionContext ∇ →
    NegativeType (∇ » ε) A
  lookupOpaqueNegative here (∙ᵒ⟨ ok ⟩[ ⊢t ∷ ⊢A ]) (∙ᵒ _ A-neg) =
    defn-wkNeg (stepᵒ₁ ok ⊢A ⊢t) A-neg
  lookupOpaqueNegative (there α↦) ∙ᵒ⟨ ok ⟩[ ⊢t ∷ ⊢A ] (∙ᵒ ∇-neg _) =
    defn-wkNeg (stepᵒ₁ ok ⊢A ⊢t)
      (lookupOpaqueNegative α↦ (defn-wf (wf ⊢A)) ∇-neg)
  lookupOpaqueNegative (there α↦) ∙ᵗ[ ⊢t ] (∙ᵗ ∇-neg) =
    defn-wkNeg (stepᵗ₁ ⊢t)
      (lookupOpaqueNegative α↦ (defn-wf (wfTerm ⊢t)) ∇-neg)

opaque

  -- If a context triple's definition context is negative, and the
  -- usage context is zero, then the triple is negative/erased.

  erasedContext :
    NegativeDefinitionContext (Γ .defs) →
    NegativeErasedContext Γ 𝟘ᶜ
  erasedContext {Γ = _ » ε}     ∇-neg = ε ∇-neg
  erasedContext {Γ = _ » _ ∙ _} ∇-neg = erasedContext ∇-neg ∙𝟘

-- If NegativeErasedContext Γ γ holds, then NegativeErasedContext Γ δ
-- holds if δ ⟨ x ⟩ is 𝟘 whenever γ ⟨ x ⟩ is 𝟘.

NegativeErasedContext-𝟘 :
  (∀ x → γ ⟨ x ⟩ ≡ 𝟘 → δ ⟨ x ⟩ ≡ 𝟘) →
  NegativeErasedContext Γ γ →
  NegativeErasedContext Γ δ
NegativeErasedContext-𝟘 {γ = ε} {δ = ε} _ (ε ∇-neg) =
  ε ∇-neg
NegativeErasedContext-𝟘 {γ = _ ∙ _} {δ = _ ∙ _} ok (neΓγ ∙ neg) =
  NegativeErasedContext-𝟘 (ok ∘→ _+1) neΓγ ∙ neg
NegativeErasedContext-𝟘
  {γ = _ ∙ _} {δ = _ ∙ _} ok (neΓγ ∙𝟘) =
  PE.subst (λ p → NegativeErasedContext _ (_ ∙ p))
    (PE.sym (ok x0 PE.refl))
    (NegativeErasedContext-𝟘 (ok ∘→ _+1) neΓγ ∙𝟘)

-- If semiring-with-meet has a well-behaved zero, then
-- NegativeErasedContext is upwards closed in its second argument.

NegativeErasedContext-upwards-closed :
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
  γ ≤ᶜ δ →
  NegativeErasedContext Γ γ →
  NegativeErasedContext Γ δ
NegativeErasedContext-upwards-closed
  {γ = ε} {δ = ε} ε (ε ∇-neg) =
  ε ∇-neg
NegativeErasedContext-upwards-closed
  {γ = _ ∙ _} {δ = _ ∙ _} (γ≤δ ∙ _) (neΓγ ∙ neg) =
  NegativeErasedContext-upwards-closed γ≤δ neΓγ ∙ neg
NegativeErasedContext-upwards-closed
  {γ = _ ∙ _} {δ = _ ∙ _} (γ≤δ ∙ 𝟘≤p) (neΓγ ∙𝟘) =
  PE.subst (λ p → NegativeErasedContext _ (_ ∙ p))
    (PE.sym (𝟘≮ 𝟘≤p))
    (NegativeErasedContext-upwards-closed γ≤δ neΓγ ∙𝟘)
