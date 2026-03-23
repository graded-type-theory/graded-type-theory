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
open import Definition.Untyped.Allowed-literal R
open import Definition.Untyped.Lift M
open import Definition.Untyped.Pi M
open import Definition.Untyped.Pi-Sigma M
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sup R

open import Definition.Typed R
open import Definition.Typed.Inversion.Primitive R
open import Definition.Typed.Properties.Admissible.Equality R
open import Definition.Typed.Properties.Admissible.Level R
open import Definition.Typed.Properties.Admissible.Lift R
open import Definition.Typed.Properties.Admissible.Pi-Sigma R
open import Definition.Typed.Properties.Admissible.U R
open import Definition.Typed.Properties.Admissible.Var R
open import Definition.Typed.Properties.Reduction R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Reasoning.Reduction R
import Definition.Typed.Reasoning.Term R as TmR
import Definition.Typed.Reasoning.Type R as TyR
open import Definition.Typed.Substitution.Primitive R
import Definition.Typed.Substitution.Primitive.Primitive R as S
open import Definition.Typed.Weakening R as W
open import Definition.Typed.Well-formed R

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Sum

private variable
  n                                               : Nat
  ∇                                               : DCon _ _
  Δ                                               : Con _ _
  Γ                                               : Cons _ _
  A B C D E F a f g t t′ t₁ t₂ u u₁ u₂ u₃ u₄ u₅ v : Term _
  l l₁ l₂                                         : Lvl _
  p p′ p₁ p₂ p₃ p₄ p₅ q q₁ q₂ q₃ q₄ q₅            : M

opaque

  -- A variant of lamⱼ.

  lamⱼ′ :
    Π-allowed p q →
    Γ »∙ A ⊢ t ∷ B →
    Γ ⊢ lam p t ∷ Π p , q ▷ A ▹ B
  lamⱼ′ ok ⊢t = lamⱼ (wf-⊢∷ ⊢t) ⊢t ok

opaque

  -- Lambdas preserve definitional equality.

  lam-cong :
    Γ »∙ A ⊢ t ≡ u ∷ B →
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
    Γ »∙ A ⊢ wk1 t ∘⟨ p ⟩ var x0 ≡ wk1 u ∘⟨ p ⟩ var x0 ∷ B →
    Γ ⊢ t ≡ u ∷ Π p , q ▷ A ▹ B
  η-eq′ ⊢t ⊢u t0≡u0 =
    let _ , ⊢B , ok = inversion-ΠΣ (wf-⊢∷ ⊢t) in
    η-eq ⊢B ⊢t ⊢u t0≡u0 ok

opaque

  -- A variant of app-subst for _⊢_⇒*_∷_.

  app-subst* :
    Γ ⊢ t ⇒* t′ ∷ Π p , q ▷ A ▹ B →
    Γ ⊢ u ∷ A →
    Γ ⊢ t ∘⟨ p ⟩ u ⇒* t′ ∘⟨ p ⟩ u ∷ B [ u ]₀
  app-subst* (id ⊢t)        ⊢u = id (⊢t ∘ⱼ ⊢u)
  app-subst* (t⇒t′ ⇨ t′⇒t″) ⊢u = app-subst t⇒t′ ⊢u ⇨ app-subst* t′⇒t″ ⊢u

opaque

  -- A variant of the reduction rule β-red.

  β-red-⇒ :
    Γ »∙ A ⊢ t ∷ B →
    Γ ⊢ u ∷ A →
    Π-allowed p q →
    Γ ⊢ lam p t ∘⟨ p ⟩ u ⇒ t [ u ]₀ ∷ B [ u ]₀
  β-red-⇒ ⊢t ⊢u =
    β-red (wf-⊢∷ ⊢t) ⊢t ⊢u PE.refl

opaque

  -- A variant of the equality rule β-red.

  β-red-≡ :
    Γ »∙ A ⊢ t ∷ B →
    Γ ⊢ u ∷ A →
    Π-allowed p q →
    Γ ⊢ lam p t ∘⟨ p ⟩ u ≡ t [ u ]₀ ∷ B [ u ]₀
  β-red-≡ ⊢t ⊢u ok =
    subsetTerm (β-red-⇒ ⊢t ⊢u ok)

opaque

  -- A variant of β-red-⇒.
  --
  -- See also Definition.Typed.Consequences.Admissible.Pi.β-red-⇒₂.

  β-red-⇒₂′ :
    Π-allowed p₁ q₁ →
    Π-allowed p₂ q₂ →
    Γ »∙ A »∙ B ⊢ t ∷ C →
    Γ ⊢ u₁ ∷ A →
    Γ ⊢ u₂ ∷ B [ u₁ ]₀ →
    Γ ⊢ lam p₁ (lam p₂ t) ∘⟨ p₁ ⟩ u₁ ∘⟨ p₂ ⟩ u₂ ⇒* t [ u₁ , u₂ ]₁₀ ∷
      C [ u₁ , u₂ ]₁₀
  β-red-⇒₂′ {p₁} {p₂} {t} {C} {u₁} {u₂} ok₁ ok₂ ⊢t ⊢u₁ ⊢u₂ =
    lam p₁ (lam p₂ t) ∘⟨ p₁ ⟩ u₁ ∘⟨ p₂ ⟩ u₂  ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _) (singleSubstComp _ _ C) $
                                                app-subst (β-red-⇒ (lamⱼ′ ok₂ ⊢t) ⊢u₁ ok₁) ⊢u₂ ⟩
    lam p₂ (t [ sgSubst u₁ ⇑ ]) ∘⟨ p₂ ⟩ u₂   ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _) (singleSubstComp _ _ C) $
                                                β-red-⇒ (subst-⊢-⇑ ⊢t (⊢ˢʷ∷-sgSubst ⊢u₁)) ⊢u₂ ok₂ ⟩∎≡
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
    Γ »∙ A »∙ B »∙ C ⊢ t ∷ D →
    Γ ⊢ u₁ ∷ A →
    Γ ⊢ u₂ ∷ B [ u₁ ]₀ →
    Γ ⊢ u₃ ∷ C [ u₁ , u₂ ]₁₀ →
    Γ ⊢ lam p₁ (lam p₂ (lam p₃ t)) ∘⟨ p₁ ⟩ u₁ ∘⟨ p₂ ⟩ u₂ ∘⟨ p₃ ⟩ u₃ ⇒*
        t [ consSubst (consSubst (sgSubst u₁) u₂) u₃ ] ∷
        D [ consSubst (consSubst (sgSubst u₁) u₂) u₃ ]
  β-red-⇒₃′
    {p₁} {p₂} {p₃} {t} {D} {u₁} {u₂} {u₃}
    ok₁ ok₂ ok₃ ⊢t ⊢u₁ ⊢u₂ ⊢u₃ =
    lam p₁ (lam p₂ (lam p₃ t)) ∘⟨ p₁ ⟩ u₁ ∘⟨ p₂ ⟩ u₂ ∘⟨ p₃ ⟩ u₃  ⇒*⟨ PE.subst (_⊢_⇒*_∷_ _ _ _) (singleSubstComp _ _ D) $
                                                                     app-subst* (β-red-⇒₂′ ok₁ ok₂ (lamⱼ′ ok₃ ⊢t) ⊢u₁ ⊢u₂) ⊢u₃ ⟩
    lam p₃ (t [ consSubst (sgSubst u₁) u₂ ⇑ ]) ∘⟨ p₃ ⟩ u₃        ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _) (singleSubstComp _ _ D) $
                                                                    β-red-⇒ (subst-⊢-⇑ ⊢t (→⊢ˢʷ∷∙ (⊢ˢʷ∷-sgSubst ⊢u₁) ⊢u₂)) ⊢u₃ ok₃ ⟩∎≡
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
    Γ »∙ A »∙ B »∙ C »∙ D ⊢ t ∷ E →
    Γ ⊢ u₁ ∷ A →
    Γ ⊢ u₂ ∷ B [ u₁ ]₀ →
    Γ ⊢ u₃ ∷ C [ u₁ , u₂ ]₁₀ →
    Γ ⊢ u₄ ∷ D [ consSubst (consSubst (sgSubst u₁) u₂) u₃ ] →
    Γ ⊢
      lam p₁ (lam p₂ (lam p₃ (lam p₄ t)))
        ∘⟨ p₁ ⟩ u₁ ∘⟨ p₂ ⟩ u₂ ∘⟨ p₃ ⟩ u₃ ∘⟨ p₄ ⟩ u₄ ⇒*
      t [ consSubst (consSubst (consSubst (sgSubst u₁) u₂) u₃) u₄ ] ∷
      E [ consSubst (consSubst (consSubst (sgSubst u₁) u₂) u₃) u₄ ]
  β-red-⇒₄′
    {p₁} {p₂} {p₃} {p₄} {t} {E} {u₁} {u₂} {u₃} {u₄}
    ok₁ ok₂ ok₃ ok₄ ⊢t ⊢u₁ ⊢u₂ ⊢u₃ ⊢u₄ =
    lam p₁ (lam p₂ (lam p₃ (lam p₄ t))) ∘⟨ p₁ ⟩ u₁ ∘⟨ p₂ ⟩ u₂ ∘⟨ p₃ ⟩ u₃
      ∘⟨ p₄ ⟩ u₄                                                          ⇒*⟨ PE.subst (_⊢_⇒*_∷_ _ _ _) (singleSubstComp _ _ E) $
                                                                              app-subst* (β-red-⇒₃′ ok₁ ok₂ ok₃ (lamⱼ′ ok₄ ⊢t) ⊢u₁ ⊢u₂ ⊢u₃) ⊢u₄ ⟩
    lam p₄ (t [ consSubst (consSubst (sgSubst u₁) u₂) u₃ ⇑ ]) ∘⟨ p₄ ⟩ u₄  ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _) (singleSubstComp _ _ E) $
                                                                             β-red-⇒ (subst-⊢-⇑ ⊢t (→⊢ˢʷ∷∙ (→⊢ˢʷ∷∙ (⊢ˢʷ∷-sgSubst ⊢u₁) ⊢u₂) ⊢u₃))
                                                                               ⊢u₄ ok₄ ⟩∎≡
    t [ consSubst (consSubst (sgSubst u₁) u₂) u₃ ⇑ ] [ u₄ ]₀              ≡⟨ singleSubstComp _ _ t ⟩
    t [ consSubst (consSubst (consSubst (sgSubst u₁) u₂) u₃) u₄ ]         ∎

opaque

  -- A variant of β-red-⇒.
  --
  -- See also Definition.Typed.Consequences.Admissible.Pi.β-red-⇒₅.

  β-red-⇒₅′ :
    Π-allowed p₁ q₁ →
    Π-allowed p₂ q₂ →
    Π-allowed p₃ q₃ →
    Π-allowed p₄ q₄ →
    Π-allowed p₅ q₅ →
    Γ »∙ A »∙ B »∙ C »∙ D »∙ E ⊢ t ∷ F →
    Γ ⊢ u₁ ∷ A →
    Γ ⊢ u₂ ∷ B [ u₁ ]₀ →
    Γ ⊢ u₃ ∷ C [ u₁ , u₂ ]₁₀ →
    Γ ⊢ u₄ ∷ D [ consSubst (consSubst (sgSubst u₁) u₂) u₃ ] →
    Γ ⊢ u₅ ∷
      E [ consSubst (consSubst (consSubst (sgSubst u₁) u₂) u₃) u₄ ] →
    Γ ⊢
      lam p₁ (lam p₂ (lam p₃ (lam p₄ (lam p₅ t))))
        ∘⟨ p₁ ⟩ u₁ ∘⟨ p₂ ⟩ u₂ ∘⟨ p₃ ⟩ u₃ ∘⟨ p₄ ⟩ u₄ ∘⟨ p₅ ⟩ u₅ ⇒*
      t [ consSubst
            (consSubst (consSubst (consSubst (sgSubst u₁) u₂) u₃) u₄)
            u₅ ] ∷
      F [ consSubst
            (consSubst (consSubst (consSubst (sgSubst u₁) u₂) u₃) u₄)
            u₅ ]
  β-red-⇒₅′
    {p₁} {p₂} {p₃} {p₄} {p₅} {t} {F} {u₁} {u₂} {u₃} {u₄} {u₅}
    ok₁ ok₂ ok₃ ok₄ ok₅ ⊢t ⊢u₁ ⊢u₂ ⊢u₃ ⊢u₄ ⊢u₅ =
    lam p₁ (lam p₂ (lam p₃ (lam p₄ (lam p₅ t)))) ∘⟨ p₁ ⟩ u₁ ∘⟨ p₂ ⟩ u₂
      ∘⟨ p₃ ⟩ u₃ ∘⟨ p₄ ⟩ u₄ ∘⟨ p₅ ⟩ u₅                                    ⇒*⟨ PE.subst (_⊢_⇒*_∷_ _ _ _) (singleSubstComp _ _ F) $
                                                                              app-subst* (β-red-⇒₄′ ok₁ ok₂ ok₃ ok₄ (lamⱼ′ ok₅ ⊢t) ⊢u₁ ⊢u₂ ⊢u₃ ⊢u₄)
                                                                                ⊢u₅ ⟩
    lam p₅
      (t [ consSubst (consSubst (consSubst (sgSubst u₁) u₂) u₃) u₄ ⇑ ])
      ∘⟨ p₅ ⟩ u₅                                                          ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _) (singleSubstComp _ _ F) $
                                                                             β-red-⇒
                                                                               (subst-⊢-⇑ ⊢t $
                                                                                →⊢ˢʷ∷∙ (→⊢ˢʷ∷∙ (→⊢ˢʷ∷∙ (⊢ˢʷ∷-sgSubst ⊢u₁) ⊢u₂) ⊢u₃) ⊢u₄)
                                                                               ⊢u₅ ok₅ ⟩∎≡
    t [ consSubst (consSubst (consSubst (sgSubst u₁) u₂) u₃) u₄ ⇑ ]
      [ u₅ ]₀                                                             ≡⟨ singleSubstComp _ _ t ⟩

    t [ consSubst
          (consSubst (consSubst (consSubst (sgSubst u₁) u₂) u₃) u₄) u₅ ]  ∎

------------------------------------------------------------------------
-- Iterated Π-types

opaque
  unfolding Πs

  -- A typing rule for Πs.

  ⊢Πs :
    Π-allowed p q or-empty Δ →
    ∇ » Δ ⊢ A →
    ∇ » ε ⊢ Πs p q Δ A
  ⊢Πs {Δ = ε}     _                          ⊢A = ⊢A
  ⊢Πs {Δ = _ ∙ _} (possibly-nonempty ⦃ ok ⦄) ⊢A =
    ⊢Πs possibly-nonempty (ΠΣⱼ ⊢A ok)

opaque
  unfolding Πs

  -- An inversion lemma for Πs.

  inversion-Πs :
    ∇ » ε ⊢ Πs p q Δ A →
    ∇ » Δ ⊢ A
  inversion-Πs {Δ = ε}     ⊢A = ⊢A
  inversion-Πs {Δ = _ ∙ _} ⊢A =
    inversion-ΠΣ (inversion-Πs ⊢A) .proj₂ .proj₁

opaque
  unfolding Πs lams

  -- A typing rule for lams.

  ⊢lams :
    Π-allowed p q or-empty Δ →
    ∇ » Δ ⊢ t ∷ A →
    ∇ » ε ⊢ lams p Δ t ∷ Πs p q Δ A
  ⊢lams {Δ = ε}     _                          ⊢t = ⊢t
  ⊢lams {Δ = _ ∙ _} (possibly-nonempty ⦃ ok ⦄) ⊢t =
    ⊢lams possibly-nonempty (lamⱼ′ ok ⊢t)

opaque
  unfolding Πs apps

  -- A typing rule for apps.

  ⊢apps :
    Π-allowed p q or-empty Δ →
    ∇ » ε ⊢ t ∷ Πs p q Δ A →
    ∇ » Δ ⊢ apps p Δ t ∷ A
  ⊢apps {Δ = ε}     _                 ⊢t = ⊢t
  ⊢apps {Δ = _ ∙ _} possibly-nonempty ⊢t =
    let ⊢A , _ = inversion-ΠΣ (inversion-Πs (wf-⊢∷ ⊢t)) in
    PE.subst (_⊢_∷_ _ _) (wkSingleSubstId _) $
    wk₁ ⊢A (⊢apps possibly-nonempty ⊢t) ∘ⱼ var₀ ⊢A

------------------------------------------------------------------------
-- Some lemmas related to Πʰ

opaque
  unfolding ΠΣʰ lamʰ

  -- A typing rule for lamʰ.

  ⊢lamʰ :
    Π-allowed p q →
    Γ ⊢ l₁ ∷Level →
    Γ ⊢ l₂ ∷Level →
    Γ »∙ A ⊢ t ∷ B →
    Γ ⊢ lamʰ p t ∷ Πʰ p q l₁ l₂ A B
  ⊢lamʰ ok ⊢l₁ ⊢l₂ ⊢t =
    let ⊢A = ⊢∙→⊢ (wf ⊢t) in
    lamⱼ′ ok (liftⱼ′ (wk₁ (Liftⱼ ⊢l₂ ⊢A) ⊢l₁) (lower₀Term ⊢l₂ ⊢t))

opaque
  unfolding ΠΣʰ ∘ʰ

  -- An equality rule for ∘ʰ.

  app-congʰ :
    Γ »∙ A ⊢ B →
    Γ ⊢ t₁ ≡ t₂ ∷ Πʰ p q l₁ l₂ A B →
    Γ ⊢ u₁ ≡ u₂ ∷ A →
    Γ ⊢ ∘ʰ p t₁ u₁ ≡ ∘ʰ p t₂ u₂ ∷ B [ u₁ ]₀
  app-congʰ ⊢B t₁≡t₂ u₁≡u₂ =
    let ⊢A , ⊢u₁ , ⊢u₂ = wf-⊢≡∷ u₁≡u₂
        _ , ⊢l₂ , _    = inversion-ΠΣʰ-⊢ (wf-⊢≡∷ t₁≡t₂ .proj₁)
    in
    conv (lower-cong (app-cong t₁≡t₂ (lift-cong ⊢l₂ u₁≡u₂)))
      (lower₀[lift]₀ ⊢B ⊢u₁)

opaque

  -- A typing rule for ∘ʰ.

  ⊢∘ʰ :
    Γ »∙ A ⊢ B →
    Γ ⊢ t ∷ Πʰ p q l₁ l₂ A B →
    Γ ⊢ u ∷ A →
    Γ ⊢ ∘ʰ p t u ∷ B [ u ]₀
  ⊢∘ʰ ⊢B ⊢t ⊢u =
    wf-⊢≡∷ (app-congʰ ⊢B (refl ⊢t) (refl ⊢u)) .proj₂ .proj₁

opaque
  unfolding lamʰ ∘ʰ

  -- A β-rule for ∘ʰ and lamʰ.

  β-redʰ :
    Γ »∙ A ⊢ t ∷ B →
    Γ ⊢ u ∷ A →
    Π-allowed p q →
    Γ ⊢ ∘ʰ p (lamʰ p t) u ≡ t [ u ]₀ ∷ B [ u ]₀
  β-redʰ {t} {u} {p} ⊢t ⊢u ok =
    let ⊢0      = ⊢zeroᵘ (wf ⊢u)
        ⊢wk-l₁  = wk₁ (Liftⱼ ⊢0 (wf-⊢∷ ⊢u)) ⊢0
        ⊢lift-u = liftⱼ′ ⊢0 ⊢u
    in
    ∘ʰ p (lamʰ p t) u                              ≡⟨⟩⊢
    lower (lam p (lift (lower₀ t)) ∘⟨ p ⟩ lift u)  ≡⟨ lower-cong $
                                                      _⊢_≡_∷_.conv (β-red-≡ (liftⱼ′ ⊢wk-l₁ (lower₀Term ⊢0 ⊢t)) ⊢lift-u ok) $
                                                      Lift-cong (refl-⊢≡∷L (substLevel ⊢wk-l₁ ⊢lift-u)) (lower₀[lift]₀ (wf-⊢∷ ⊢t) ⊢u) ⟩⊢
    lower (lift (lower₀ t) [ lift u ]₀)            ≡⟨ lower-cong (lift-cong ⊢0 (lower₀[lift]₀∷ ⊢t ⊢u)) ⟩⊢
    lower (lift (t [ u ]₀))                        ⇒⟨ Lift-β⇒ (substTerm ⊢t ⊢u) ⟩⊢∎
    t [ u ]₀                                       ∎
    where
    open TmR

opaque
  unfolding ΠΣʰ ∘ʰ lower₀

  -- An η-rule for Πʰ.

  η-eqʰ :
    Γ ⊢ t ∷ Πʰ p q l₁ l₂ A B →
    Γ ⊢ u ∷ Πʰ p q l₁ l₂ A B →
    Γ »∙ A ⊢ ∘ʰ p (wk1 t) (var x0) ≡ ∘ʰ p (wk1 u) (var x0) ∷ B →
    Γ ⊢ t ≡ u ∷ Πʰ p q l₁ l₂ A B
  η-eqʰ {Γ} {t} {p} {q} {l₁} {l₂} {A} {B} {u} ⊢t ⊢u t≡u =
    let _ , ⊢l₂ , _ = inversion-ΠΣʰ-⊢ {B = B} (wf-⊢∷ ⊢t)
        ⊢B , _      = wf-⊢≡∷ t≡u
        ⊢Lift-A     = Liftⱼ ⊢l₂ (⊢∙→⊢ (wf ⊢B))
        ⊢0          = var₀ ⊢Lift-A

        lemma :
          Γ ⊢ v ∷ Πʰ p q l₁ l₂ A B →
          Γ »∙ Lift l₂ A ⊢ lower₀ (lower (wk1 v ∘⟨ p ⟩ lift (var x0))) ≡
            lower (wk1 v ∘⟨ p ⟩ var x0) ∷ lower₀ B
        lemma ⊢t =
          conv
            (lower-cong $
             app-cong
               (PE.subst₃ (_⊢_≡_∷_ _)
                  (PE.sym (wk1-[][]↑ 1)) PE.refl PE.refl
                  (refl (wk₁ ⊢Lift-A ⊢t)))
               (sym′ (Lift-η-swap ⊢0 (refl (lowerⱼ ⊢0)))))
            (PE.subst (_⊢_≡_ _ _) (wkSingleSubstId _) $
             substTypeEq
               (_⊢_≡_.refl $
                W.wk (liftʷ (step id) (wk₁ ⊢Lift-A ⊢Lift-A)) $
                lower₀Type ⊢l₂ ⊢B)
               (sym′ (Lift-η-swap ⊢0 (refl (lowerⱼ ⊢0)))))
    in
    η-eq′ ⊢t ⊢u $
    Lift-η′
      (PE.subst (_⊢_∷_ _ _) (wkSingleSubstId _) $
       wk₁ ⊢Lift-A ⊢t ∘ⱼ ⊢0)
      (PE.subst (_⊢_∷_ _ _) (wkSingleSubstId _) $
       wk₁ ⊢Lift-A ⊢u ∘ⱼ ⊢0)
      (lower (wk1 t ∘⟨ p ⟩ var x0)                  ≡˘⟨ lemma ⊢t ⟩⊢
       lower₀ (lower (wk1 t ∘⟨ p ⟩ lift (var x0)))  ≡⟨ lower₀TermEq ⊢l₂ t≡u ⟩⊢
       lower₀ (lower (wk1 u ∘⟨ p ⟩ lift (var x0)))  ≡⟨ lemma ⊢u ⟩⊢∎
       lower (wk1 u ∘⟨ p ⟩ var x0)                  ∎)
    where
    open TmR

------------------------------------------------------------------------
-- Some lemmas related to a type of a universe-polymorphic identity
-- function

opaque
  unfolding _supᵘₗ_

  -- A certain type of a certain universe-polymorphic identity
  -- function, expressed using lifting in a certain way (and using
  -- certain grades), lives in some universe, assuming that the
  -- context is well-formed, Level is small, Omega-plus-allowed holds,
  -- and certain forms of Π-types are allowed.

  a-type-of-id-has-a-type :
    Omega-plus-allowed →
    Level-is-small →
    Π-allowed p₁ q₁ →
    Π-allowed p₂ q₂ →
    Π-allowed p₃ q₃ →
    ⊢ Γ →
    let A =
          Π p₁ , q₁ ▷ Lift (ωᵘ+ 0) Level ▹
          Lift (ωᵘ+ 0)
            (Π p₂ , q₂ ▷ U (level (lower (var x0))) ▹
             Lift (level (sucᵘ (lower (var x1))))
               (Π p₃ , q₃ ▷ var x0 ▹ var x1))
        t = lam p₁ (lift (lam p₂ (lift (lam p₃ (var x0)))))
    in
    Γ ⊢ t ∷ A ×
    Γ ⊢ A ∷ U (ωᵘ+ 0)
  a-type-of-id-has-a-type ok-ω okᴸ ok₁ ok₂ ok₃ ⊢Γ =
    let ⊢ω     = literal (Allowed-literal-ωᵘ+-⇔ .proj₂ ok-ω) ⊢Γ
        ⊢Level = Liftⱼ′ ⊢ω (Levelⱼ ⊢Γ okᴸ)
        okᴸ    = Level-allowed⇔⊎ .proj₂ (inj₁ okᴸ)
        ⊢U     = Uⱼ (term okᴸ (lowerⱼ (var₀ (univ ⊢Level))))
        ⊢0     = var₀ (univ ⊢U)
        l      = level (lower (var x1))
        ⊢l     = term okᴸ (lowerⱼ (var₁ (univ ⊢U)))
    in
    (lamⱼ′ ok₁ $ liftⱼ′ (wk₁ (univ ⊢Level) ⊢ω) $
     lamⱼ′ ok₂ $ liftⱼ′ (⊢1ᵘ+ ⊢l) $
     lamⱼ′ ok₃ $ var₀ (univ ⊢0)) ,
    ΠΣⱼ′ ⊢Level
      (Liftⱼ′ (wk₁ (univ ⊢Level) ⊢ω) $
       ΠΣⱼ′ ⊢U
         (conv (Liftⱼ′ (⊢1ᵘ+ ⊢l) (ΠΣⱼ′ ⊢0 (var₁ (univ ⊢0)) ok₃))
            (U (l supᵘₗ 1ᵘ+ l)  ≡⟨ U-cong-⊢≡ (⊢≤ₗ∷L→⊢≡∷L (supᵘₗ-sub ⊢l)) ⟩⊢∎
             U (1ᵘ+ l)          ∎))
         ok₂)
      ok₁
    where
    open TyR

opaque

  -- A variant of a-type-of-id-has-a-type that is stated using Πʰ.

  a-type-of-id-has-a-type-Πʰ :
    Omega-plus-allowed →
    Level-is-small →
    Π-allowed p₁ q₁ →
    Π-allowed p₂ q₂ →
    Π-allowed p₃ q₃ →
    ⊢ Γ →
    let A =
          Πʰ p₁ q₁ (ωᵘ+ 0) (ωᵘ+ 0) Level $
          Πʰ p₂ q₂ (ωᵘ+ 0) (ωᵘ+ 0) (U (level (var x0))) $
          Π p₃ , q₃ ▷ var x0 ▹ var x1
        t = lamʰ p₁ (lamʰ p₂ (lam p₃ (var x0)))
    in
    Γ ⊢ t ∷ A ×
    Γ ⊢ A ∷ U (ωᵘ+ 0)
  a-type-of-id-has-a-type-Πʰ ok-ω okᴸ ok₁ ok₂ ok₃ ⊢Γ =
    let ⊢ω     = literal (Allowed-literal-ωᵘ+-⇔ .proj₂ ok-ω) ⊢Γ
        ⊢Level = Levelⱼ ⊢Γ okᴸ
        ⊢ω′    = wk₁ (univ ⊢Level) ⊢ω
        ⊢l     = term (Level-allowed⇔⊎ .proj₂ (inj₁ okᴸ))
                   (var₀ (univ ⊢Level))
        ⊢U     = Uⱼ ⊢l
        ⊢0     = var₀ (univ ⊢U)
    in
    (⊢lamʰ ok₁ ⊢ω ⊢ω $
     ⊢lamʰ ok₂ ⊢ω′ ⊢ω′ $
     lamⱼ′ ok₃ (var₀ (univ ⊢0))) ,
    (⊢ΠΣʰ∷-≤ₗ ok₁ (zeroᵘₗ≤ₗ ⊢ω) (refl-⊢≤ₗ∷L ⊢ω) ⊢Level $
     ⊢ΠΣʰ∷-≤ₗ ok₂ (level≤ₗωᵘ+ ok-ω (⊢1ᵘ+ ⊢l)) (level≤ₗωᵘ+ ok-ω ⊢l) ⊢U $
     ΠΣⱼ′ ⊢0 (var₁ (univ ⊢0)) ok₃)
