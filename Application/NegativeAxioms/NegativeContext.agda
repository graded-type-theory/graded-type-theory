------------------------------------------------------------------------
-- Negative contexts (contexts containing only negative types).
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Application.NegativeAxioms.NegativeContext
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R
open import Definition.Typed.Weakening.Definition R
open import Application.NegativeAxioms.NegativeType R

open import Tools.Fin
open import Tools.Nat

private variable
  α m n : Nat
  x     : Fin _
  ∇     : DCon (Term 0) _
  Γ     : Cons _ _
  A t   : Term _
  φ     : Unfolding _

-- Negative contexts
---------------------------------------------------------------------------

-- A definition context is negative if all of its opaque entries have
-- negative types.

data NegativeDefinitionContext : DCon (Term 0) n → Set a where
  ε  : NegativeDefinitionContext ε
  ∙ᵗ : NegativeDefinitionContext ∇ →
       NegativeDefinitionContext (∇ ∙⟨ tra ⟩[ t ∷ A ])
  ∙ᵒ : NegativeDefinitionContext ∇ →
       NegativeType (∇ » ε) A →
       NegativeDefinitionContext (∇ ∙⟨ opa φ ⟩[ t ∷ A ])

-- A context pair is negative if the definition context is negative
-- and all the types in the variable context are negative.

data NegativeContext : Cons m n → Set a where
  ε   : NegativeDefinitionContext ∇ →
        NegativeContext (∇ » ε)
  _∙_ : NegativeContext Γ → NegativeType Γ A →
        NegativeContext (Γ »∙ A)

opaque

  -- If a context pair is negative, then the pair's definition context
  -- is negative.

  negative-definition-context :
    NegativeContext Γ → NegativeDefinitionContext (Γ .defs)
  negative-definition-context (ε ∇-neg)   = ∇-neg
  negative-definition-context (Γ-neg ∙ _) =
    negative-definition-context Γ-neg

-- Lemma: Any entry in negative context is a negative type (needs weakening).

lookupNegative :
  ⊢ Γ → NegativeContext Γ → x ∷ A ∈ Γ .vars → NegativeType Γ A
lookupNegative (ε _)  _         ()
lookupNegative (∙ ⊢A) (nΓ ∙ nA) here
  = wkNeg (stepʷ id ⊢A) nA
lookupNegative (∙ ⊢A) (nΓ ∙ nA) (there h)
  = wkNeg (stepʷ id ⊢A) (lookupNegative (wf ⊢A) nΓ h)

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
      (lookupOpaqueNegative α↦ (defn-wf (wf ⊢t)) ∇-neg)
