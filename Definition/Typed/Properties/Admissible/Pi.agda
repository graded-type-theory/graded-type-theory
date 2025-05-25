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
open import Definition.Untyped.Properties M

open import Definition.Typed R
open import Definition.Typed.Inversion.Primitive R
open import Definition.Typed.Properties.Reduction R
open import Definition.Typed.Reasoning.Reduction R
open import Definition.Typed.Substitution.Primitive R
import Definition.Typed.Substitution.Primitive.Primitive R as S
open import Definition.Typed.Well-formed R

open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private variable
  ∇                            : DCon (Term 0) _
  Γ                            : Con Term _
  A B C D E t t′ u u₁ u₂ u₃ u₄ : Term _
  p p₁ p₂ p₃ p₄ q q₁ q₂ q₃ q₄  : M

opaque

  -- A variant of lamⱼ.

  lamⱼ′ :
    Π-allowed p q →
    ∇ » Γ ∙ A ⊢ t ∷ B →
    ∇ » Γ ⊢ lam p t ∷ Π p , q ▷ A ▹ B
  lamⱼ′ ok ⊢t = lamⱼ (wf-⊢∷ ⊢t) ⊢t ok

opaque

  -- Lambdas preserve definitional equality.

  lam-cong :
    ∇ » Γ ∙ A ⊢ t ≡ u ∷ B →
    Π-allowed p q →
    ∇ » Γ ⊢ lam p t ≡ lam p u ∷ Π p , q ▷ A ▹ B
  lam-cong t≡u =
    let ⊢B , ⊢t , ⊢u = wf-⊢≡∷ t≡u in
    S.lam-cong ⊢B ⊢t ⊢u t≡u

opaque

  -- A variant of η-eq.

  η-eq′ :
    ∇ » Γ ⊢ t ∷ Π p , q ▷ A ▹ B →
    ∇ » Γ ⊢ u ∷ Π p , q ▷ A ▹ B →
    ∇ » Γ ∙ A ⊢ wk1 t ∘⟨ p ⟩ var x0 ≡ wk1 u ∘⟨ p ⟩ var x0 ∷ B →
    ∇ » Γ ⊢ t ≡ u ∷ Π p , q ▷ A ▹ B
  η-eq′ ⊢t ⊢u t0≡u0 =
    let _ , ⊢B , ok = inversion-ΠΣ (wf-⊢∷ ⊢t) in
    η-eq ⊢B ⊢t ⊢u t0≡u0 ok

opaque

  -- A variant of app-subst for _⊢_⇒*_∷_.

  app-subst* :
    ∇ » Γ ⊢ t ⇒* t′ ∷ Π p , q ▷ A ▹ B →
    ∇ » Γ ⊢ u ∷ A →
    ∇ » Γ ⊢ t ∘⟨ p ⟩ u ⇒* t′ ∘⟨ p ⟩ u ∷ B [ u ]₀
  app-subst* (id ⊢t)        ⊢u = id (⊢t ∘ⱼ ⊢u)
  app-subst* (t⇒t′ ⇨ t′⇒t″) ⊢u = app-subst t⇒t′ ⊢u ⇨ app-subst* t′⇒t″ ⊢u

opaque

  -- A variant of the reduction rule β-red.

  β-red-⇒ :
    ∇ » Γ ∙ A ⊢ t ∷ B →
    ∇ » Γ ⊢ u ∷ A →
    Π-allowed p q →
    ∇ » Γ ⊢ lam p t ∘⟨ p ⟩ u ⇒ t [ u ]₀ ∷ B [ u ]₀
  β-red-⇒ ⊢t ⊢u =
    β-red (wf-⊢∷ ⊢t) ⊢t ⊢u PE.refl

opaque

  -- A variant of the equality rule β-red.

  β-red-≡ :
    ∇ » Γ ∙ A ⊢ t ∷ B →
    ∇ » Γ ⊢ u ∷ A →
    Π-allowed p q →
    ∇ » Γ ⊢ lam p t ∘⟨ p ⟩ u ≡ t [ u ]₀ ∷ B [ u ]₀
  β-red-≡ ⊢t ⊢u ok =
    subsetTerm (β-red-⇒ ⊢t ⊢u ok)

opaque

  -- A variant of β-red-⇒.
  --
  -- See also Definition.Typed.Consequences.Admissible.Pi.β-red-⇒₂.

  β-red-⇒₂′ :
    Π-allowed p₁ q₁ →
    Π-allowed p₂ q₂ →
    ∇ » Γ ∙ A ∙ B ⊢ t ∷ C →
    ∇ » Γ ⊢ u₁ ∷ A →
    ∇ » Γ ⊢ u₂ ∷ B [ u₁ ]₀ →
    ∇ » Γ ⊢ lam p₁ (lam p₂ t) ∘⟨ p₁ ⟩ u₁ ∘⟨ p₂ ⟩ u₂ ⇒* t [ u₁ , u₂ ]₁₀ ∷
      C [ u₁ , u₂ ]₁₀
  β-red-⇒₂′ {p₁} {p₂} {t} {C} {u₁} {u₂} ok₁ ok₂ ⊢t ⊢u₁ ⊢u₂ =
    lam p₁ (lam p₂ t) ∘⟨ p₁ ⟩ u₁ ∘⟨ p₂ ⟩ u₂  ⇒⟨ PE.subst (_»_⊢_⇒_∷_ _ _ _ _) (singleSubstComp _ _ C) $
                                                app-subst (β-red-⇒ (lamⱼ′ ok₂ ⊢t) ⊢u₁ ok₁) ⊢u₂ ⟩
    lam p₂ (t [ sgSubst u₁ ⇑ ]) ∘⟨ p₂ ⟩ u₂   ⇒⟨ PE.subst (_»_⊢_⇒_∷_ _ _ _ _) (singleSubstComp _ _ C) $
                                                β-red-⇒ (subst-⊢∷-⇑ ⊢t (⊢ˢʷ∷-sgSubst ⊢u₁)) ⊢u₂ ok₂ ⟩∎≡
    t [ sgSubst u₁ ⇑ ] [ u₂ ]₀               ≡⟨ singleSubstComp _ _ t ⟩
    t [ u₁ , u₂ ]₁₀                          ∎

opaque

  -- A variant of β-red-⇒.
  --
  -- See also Definition.Typed.Consequences.Admissible.Pi.β-red-⇒₃.

  β-red-⇒₃′ :
    Π-allowed p₁ q₁ →
    Π-allowed p₂ q₂ →
    Π-allowed p₃ q₃ →
    ∇ » Γ ∙ A ∙ B ∙ C ⊢ t ∷ D →
    ∇ » Γ ⊢ u₁ ∷ A →
    ∇ » Γ ⊢ u₂ ∷ B [ u₁ ]₀ →
    ∇ » Γ ⊢ u₃ ∷ C [ u₁ , u₂ ]₁₀ →
    ∇ » Γ ⊢ lam p₁ (lam p₂ (lam p₃ t)) ∘⟨ p₁ ⟩ u₁ ∘⟨ p₂ ⟩ u₂ ∘⟨ p₃ ⟩ u₃ ⇒*
        t [ consSubst (consSubst (sgSubst u₁) u₂) u₃ ] ∷
        D [ consSubst (consSubst (sgSubst u₁) u₂) u₃ ]
  β-red-⇒₃′
    {p₁} {p₂} {p₃} {t} {D} {u₁} {u₂} {u₃}
    ok₁ ok₂ ok₃ ⊢t ⊢u₁ ⊢u₂ ⊢u₃ =
    lam p₁ (lam p₂ (lam p₃ t)) ∘⟨ p₁ ⟩ u₁ ∘⟨ p₂ ⟩ u₂ ∘⟨ p₃ ⟩ u₃  ⇒*⟨ PE.subst (_»_⊢_⇒*_∷_ _ _ _ _) (singleSubstComp _ _ D) $
                                                                     app-subst* (β-red-⇒₂′ ok₁ ok₂ (lamⱼ′ ok₃ ⊢t) ⊢u₁ ⊢u₂) ⊢u₃ ⟩
    lam p₃ (t [ consSubst (sgSubst u₁) u₂ ⇑ ]) ∘⟨ p₃ ⟩ u₃        ⇒⟨ PE.subst (_»_⊢_⇒_∷_ _ _ _ _) (singleSubstComp _ _ D) $
                                                                    β-red-⇒ (subst-⊢∷-⇑ ⊢t (→⊢ˢʷ∷∙ (⊢ˢʷ∷-sgSubst ⊢u₁) ⊢u₂)) ⊢u₃ ok₃ ⟩∎≡
    t [ consSubst (sgSubst u₁) u₂ ⇑ ] [ u₃ ]₀                    ≡⟨ singleSubstComp _ _ t ⟩
    t [ consSubst (consSubst (sgSubst u₁) u₂) u₃ ]               ∎

opaque

  -- A variant of β-red-⇒.
  --
  -- See also Definition.Typed.Consequences.Admissible.Pi.β-red-⇒₄.

  β-red-⇒₄′ :
    Π-allowed p₁ q₁ →
    Π-allowed p₂ q₂ →
    Π-allowed p₃ q₃ →
    Π-allowed p₄ q₄ →
    ∇ » Γ ∙ A ∙ B ∙ C ∙ D ⊢ t ∷ E →
    ∇ » Γ ⊢ u₁ ∷ A →
    ∇ » Γ ⊢ u₂ ∷ B [ u₁ ]₀ →
    ∇ » Γ ⊢ u₃ ∷ C [ u₁ , u₂ ]₁₀ →
    ∇ » Γ ⊢ u₄ ∷ D [ consSubst (consSubst (sgSubst u₁) u₂) u₃ ] →
    ∇ » Γ ⊢
      lam p₁ (lam p₂ (lam p₃ (lam p₄ t)))
        ∘⟨ p₁ ⟩ u₁ ∘⟨ p₂ ⟩ u₂ ∘⟨ p₃ ⟩ u₃ ∘⟨ p₄ ⟩ u₄ ⇒*
      t [ consSubst (consSubst (consSubst (sgSubst u₁) u₂) u₃) u₄ ] ∷
      E [ consSubst (consSubst (consSubst (sgSubst u₁) u₂) u₃) u₄ ]
  β-red-⇒₄′
    {p₁} {p₂} {p₃} {p₄} {t} {E} {u₁} {u₂} {u₃} {u₄}
    ok₁ ok₂ ok₃ ok₄ ⊢t ⊢u₁ ⊢u₂ ⊢u₃ ⊢u₄ =
    lam p₁ (lam p₂ (lam p₃ (lam p₄ t))) ∘⟨ p₁ ⟩ u₁ ∘⟨ p₂ ⟩ u₂ ∘⟨ p₃ ⟩ u₃
      ∘⟨ p₄ ⟩ u₄                                                          ⇒*⟨ PE.subst (_»_⊢_⇒*_∷_ _ _ _ _) (singleSubstComp _ _ E) $
                                                                              app-subst* (β-red-⇒₃′ ok₁ ok₂ ok₃ (lamⱼ′ ok₄ ⊢t) ⊢u₁ ⊢u₂ ⊢u₃) ⊢u₄ ⟩
    lam p₄ (t [ consSubst (consSubst (sgSubst u₁) u₂) u₃ ⇑ ]) ∘⟨ p₄ ⟩ u₄  ⇒⟨ PE.subst (_»_⊢_⇒_∷_ _ _ _ _) (singleSubstComp _ _ E) $
                                                                             β-red-⇒ (subst-⊢∷-⇑ ⊢t (→⊢ˢʷ∷∙ (→⊢ˢʷ∷∙ (⊢ˢʷ∷-sgSubst ⊢u₁) ⊢u₂) ⊢u₃))
                                                                               ⊢u₄ ok₄ ⟩∎≡
    t [ consSubst (consSubst (sgSubst u₁) u₂) u₃ ⇑ ] [ u₄ ]₀              ≡⟨ singleSubstComp _ _ t ⟩
    t [ consSubst (consSubst (consSubst (sgSubst u₁) u₂) u₃) u₄ ]         ∎
