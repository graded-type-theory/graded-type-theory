------------------------------------------------------------------------
-- Derived typing rules (at the time of writing just one)
------------------------------------------------------------------------

module Definition.Typed.Consequences.DerivedRules
  {a} (M : Set a) where

open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE

open import Definition.Typed M
open import Definition.Typed.Consequences.Syntactic M
open import Definition.Typed.Properties M
open import Definition.Typed.Weakening M
open import Definition.Untyped M hiding (_∷_; wk)
open import Definition.Untyped.Properties M

private variable
  Γ       : Con Term _
  A B t u : Term _
  p q     : M

-- Lambdas preserve definitional equality.

lam-cong :
  Γ ∙ A ⊢ t ≡ u ∷ B →
  Γ ⊢ lam p t ≡ lam p u ∷ Π p , q ▷ A ▹ B
lam-cong {B = B} t≡u = η-eq ⊢A (lamⱼ ⊢A ⊢t) (lamⱼ ⊢A ⊢u) $
  _⊢_≡_∷_.trans
    (PE.subst (_ ⊢ _ ≡ _ ∷_)
       (wkSingleSubstId _)
       (β-red A⊢A A∙A⊢B (wkTerm ρ ⊢∙A∙A ⊢t) (var ⊢∙A here)
          PE.refl)) $
  _⊢_≡_∷_.trans
    (PE.subst₂ (_ ⊢_≡_∷ _)
      (PE.sym (wkSingleSubstId _))
      (PE.sym (wkSingleSubstId _))
      t≡u) $
  _⊢_≡_∷_.sym $
  PE.subst (_ ⊢ _ ≡ _ ∷_)
    (wkSingleSubstId _)
    (β-red A⊢A A∙A⊢B (wkTerm ρ ⊢∙A∙A ⊢u) (var ⊢∙A here) PE.refl)
  where
  ρ     = lift (step id)
  ⊢t    = syntacticEqTerm t≡u .proj₂ .proj₁
  ⊢u    = syntacticEqTerm t≡u .proj₂ .proj₂
  ⊢B    = syntacticEqTerm t≡u .proj₁
  ⊢∙A   = wf ⊢B
  ⊢A    = case ⊢∙A of λ where
            (_ ∙ ⊢A) → ⊢A
  A⊢A   = wk (step id) ⊢∙A ⊢A
  ⊢∙A∙A = ⊢∙A ∙ A⊢A
  A∙A⊢B = wk (lift (step id)) ⊢∙A∙A ⊢B
