------------------------------------------------------------------------
-- Admissible rules related to Π
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Pi
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M

open import Definition.Typed R
open import Definition.Typed.Inversion.Primitive R
open import Definition.Typed.Properties.Reduction R
import Definition.Typed.Substitution.Primitive.Primitive R as S
open import Definition.Typed.Well-formed R

open import Tools.Fin
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  Γ          : Con Term _
  A B t t′ u : Term _
  p q        : M

opaque

  -- A variant of lamⱼ.

  lamⱼ′ :
    Π-allowed p q →
    Γ ∙ A ⊢ t ∷ B →
    Γ ⊢ lam p t ∷ Π p , q ▷ A ▹ B
  lamⱼ′ ok ⊢t = lamⱼ (wf-⊢∷ ⊢t) ⊢t ok

opaque

  -- Lambdas preserve definitional equality.

  lam-cong :
    Γ ∙ A ⊢ t ≡ u ∷ B →
    Π-allowed p q →
    Γ ⊢ lam p t ≡ lam p u ∷ Π p , q ▷ A ▹ B
  lam-cong t≡u =
    let ⊢B , ⊢t , ⊢u = wf-⊢≡∷ t≡u in
    S.lam-cong ⊢B ⊢t ⊢u t≡u

opaque

  -- A variant of η-eq.

  η-eq′ :
    Γ ⊢ t ∷ Π p , q ▷ A ▹ B →
    Γ ⊢ u ∷ Π p , q ▷ A ▹ B →
    Γ ∙ A ⊢ wk1 t ∘⟨ p ⟩ var x0 ≡ wk1 u ∘⟨ p ⟩ var x0 ∷ B →
    Γ ⊢ t ≡ u ∷ Π p , q ▷ A ▹ B
  η-eq′ ⊢t ⊢u t0≡u0 =
    let _ , ⊢B , ok = inversion-ΠΣ (wf-⊢∷ ⊢t) in
    η-eq ⊢B ⊢t ⊢u t0≡u0 ok

opaque

  -- A variant of the reduction rule β-red.

  β-red-⇒ :
    Γ ∙ A ⊢ t ∷ B →
    Γ ⊢ u ∷ A →
    Π-allowed p q →
    Γ ⊢ lam p t ∘⟨ p ⟩ u ⇒ t [ u ]₀ ∷ B [ u ]₀
  β-red-⇒ ⊢t ⊢u =
    β-red (wf-⊢∷ ⊢t) ⊢t ⊢u PE.refl

opaque

  -- A variant of the equality rule β-red.

  β-red-≡ :
    Γ ∙ A ⊢ t ∷ B →
    Γ ⊢ u ∷ A →
    Π-allowed p q →
    Γ ⊢ lam p t ∘⟨ p ⟩ u ≡ t [ u ]₀ ∷ B [ u ]₀
  β-red-≡ ⊢t ⊢u ok =
    subsetTerm (β-red-⇒ ⊢t ⊢u ok)

opaque

  -- A variant of app-subst for _⊢_⇒*_∷_.

  app-subst* :
    Γ ⊢ t ⇒* t′ ∷ Π p , q ▷ A ▹ B →
    Γ ⊢ u ∷ A →
    Γ ⊢ t ∘⟨ p ⟩ u ⇒* t′ ∘⟨ p ⟩ u ∷ B [ u ]₀
  app-subst* (id ⊢t)        ⊢u = id (⊢t ∘ⱼ ⊢u)
  app-subst* (t⇒t′ ⇨ t′⇒t″) ⊢u = app-subst t⇒t′ ⊢u ⇨ app-subst* t′⇒t″ ⊢u
