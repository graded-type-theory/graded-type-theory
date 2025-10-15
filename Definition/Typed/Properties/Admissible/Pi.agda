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
open import Definition.Untyped.Lift M
open import Definition.Untyped.Pi M
open import Definition.Untyped.Pi-Sigma M
open import Definition.Untyped.Properties M

open import Definition.Typed R
open import Definition.Typed.Inversion.Primitive R
open import Definition.Typed.Properties.Admissible.Equality R
open import Definition.Typed.Properties.Admissible.Lift R
open import Definition.Typed.Properties.Admissible.Pi-Sigma R
open import Definition.Typed.Properties.Reduction R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Reasoning.Reduction R
open import Definition.Typed.Reasoning.Term R
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

private variable
  n                                                : Nat
  Γ                                                : Con Term _
  A B C D E a f g l l₁ l₂ t t′ t₁ t₂ u u₁ u₂ u₃ u₄ : Term _
  p p′ p₁ p₂ p₃ p₄ q q₁ q₂ q₃ q₄                   : M

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

  -- A variant of β-red-⇒.
  --
  -- See also Definition.Typed.Consequences.Admissible.Pi.β-red-⇒₂.

  β-red-⇒₂′ :
    Π-allowed p₁ q₁ →
    Π-allowed p₂ q₂ →
    Γ ∙ A ∙ B ⊢ t ∷ C →
    Γ ⊢ u₁ ∷ A →
    Γ ⊢ u₂ ∷ B [ u₁ ]₀ →
    Γ ⊢ lam p₁ (lam p₂ t) ∘⟨ p₁ ⟩ u₁ ∘⟨ p₂ ⟩ u₂ ⇒* t [ u₁ , u₂ ]₁₀ ∷
      C [ u₁ , u₂ ]₁₀
  β-red-⇒₂′ {p₁} {p₂} {t} {C} {u₁} {u₂} ok₁ ok₂ ⊢t ⊢u₁ ⊢u₂ =
    lam p₁ (lam p₂ t) ∘⟨ p₁ ⟩ u₁ ∘⟨ p₂ ⟩ u₂  ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _) (singleSubstComp _ _ C) $
                                                app-subst (β-red-⇒ (lamⱼ′ ok₂ ⊢t) ⊢u₁ ok₁) ⊢u₂ ⟩
    lam p₂ (t [ sgSubst u₁ ⇑ ]) ∘⟨ p₂ ⟩ u₂   ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _) (singleSubstComp _ _ C) $
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
    Γ ∙ A ∙ B ∙ C ⊢ t ∷ D →
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
    Γ ∙ A ∙ B ∙ C ∙ D ⊢ t ∷ E →
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
                                                                             β-red-⇒ (subst-⊢∷-⇑ ⊢t (→⊢ˢʷ∷∙ (→⊢ˢʷ∷∙ (⊢ˢʷ∷-sgSubst ⊢u₁) ⊢u₂) ⊢u₃))
                                                                               ⊢u₄ ok₄ ⟩∎≡
    t [ consSubst (consSubst (sgSubst u₁) u₂) u₃ ⇑ ] [ u₄ ]₀              ≡⟨ singleSubstComp _ _ t ⟩
    t [ consSubst (consSubst (consSubst (sgSubst u₁) u₂) u₃) u₄ ]         ∎

------------------------------------------------------------------------
-- Heterogeneous variants of the typing rules for Π

opaque
  unfolding ΠΣʰ lamʰ

  -- A typing rule for lamʰ.

  lamʰⱼ′
    : Γ ⊢ l₁ ∷ Level
    → Γ ⊢ l₂ ∷ Level
    → Γ ∙ A ⊢ B
    → Γ ∙ A ⊢ t ∷ B
    → Π-allowed p q
    → Γ     ⊢ lamʰ p t ∷ Πʰ p q l₁ l₂ A B
  lamʰⱼ′ ⊢l₁ ⊢l₂ ⊢B ⊢t ok =
    let ⊢A = ⊢∙→⊢ (wf ⊢B)
    in lamⱼ′ ok (liftⱼ′ (wkTerm₁ (Liftⱼ ⊢l₂ ⊢A) ⊢l₁) (lower₀Term ⊢l₂ ⊢t))

opaque

  -- A variant of lamʰⱼ′.

  lamʰⱼ :
    Γ ⊢ l₁ ∷ Level →
    Γ ⊢ l₂ ∷ Level →
    Γ ∙ A ⊢ B ∷ U (wk1 l₂) →
    Γ ∙ A ⊢ t ∷ B →
    Π-allowed p q →
    Γ ⊢ lamʰ p t ∷ Πʰ p q l₁ l₂ A B
  lamʰⱼ ⊢l₁ ⊢l₂ ⊢B = lamʰⱼ′ ⊢l₁ ⊢l₂ (univ ⊢B)

opaque
  unfolding ΠΣʰ ∘ʰ

  -- A typing rule for ∘ʰ.

  ∘ʰⱼ′ :
    Γ ∙ A ⊢ B →
    Γ ⊢ t ∷ Πʰ p q l₁ l₂ A B →
    Γ ⊢ u ∷ A →
    Γ ⊢ ∘ʰ p l₂ t u ∷ B [ u ]₀
  ∘ʰⱼ′ ⊢B ⊢t ⊢u =
    let ⊢A          = wf-⊢∷ ⊢u
        _ , ⊢l₂ , _ = inversion-ΠΣʰ-⊢ (wf-⊢∷ ⊢t)
    in
    conv (lowerⱼ (⊢t ∘ⱼ liftⱼ ⊢l₂ ⊢A ⊢u)) (lower₀[lift]₀ ⊢B ⊢u)

opaque

  -- A variant of ∘ʰⱼ′.

  ∘ʰⱼ :
    Γ ∙ A ⊢ B ∷ U (wk1 l₂) →
    Γ ⊢ t ∷ Πʰ p q l₁ l₂ A B →
    Γ ⊢ u ∷ A →
    Γ ⊢ ∘ʰ p l₂ t u ∷ B [ u ]₀
  ∘ʰⱼ ⊢B = ∘ʰⱼ′ (univ ⊢B)

opaque
  unfolding ΠΣʰ ∘ʰ

  -- Heterogeneous application congruence

  app-congʰ′ :
    Γ ∙ A ⊢ B →
    Γ ⊢ t₁ ≡ t₂ ∷ Πʰ p q l₁ l₂ A B →
    Γ ⊢ u₁ ≡ u₂ ∷ A →
    Γ ⊢ ∘ʰ p l₂ t₁ u₁ ≡ ∘ʰ p l₂ t₂ u₂ ∷ B [ u₁ ]₀
  app-congʰ′ ⊢B t₁≡t₂ u₁≡u₂ =
    let ⊢A , ⊢u₁ , ⊢u₂ = wf-⊢≡∷ u₁≡u₂
        _ , ⊢l₂ , _    = inversion-ΠΣʰ-⊢ (wf-⊢≡∷ t₁≡t₂ .proj₁)
    in
    conv (lower-cong (app-cong t₁≡t₂ (lift-cong ⊢l₂ u₁≡u₂)))
      (lower₀[lift]₀ ⊢B ⊢u₁)

opaque

  -- A variant of app-congʰ′.

  app-congʰ :
    Γ ∙ A ⊢ B ∷ U (wk1 l₂) →
    Γ ⊢ t₁ ≡ t₂ ∷ Πʰ p q l₁ l₂ A B →
    Γ ⊢ u₁ ≡ u₂ ∷ A →
    Γ ⊢ ∘ʰ p l₂ t₁ u₁ ≡ ∘ʰ p l₂ t₂ u₂ ∷ B [ u₁ ]₀
  app-congʰ ⊢B = app-congʰ′ (univ ⊢B)

opaque
  unfolding lamʰ ∘ʰ

  -- Heterogeneous β-reduction

  β-redʰ′
    : Γ ⊢ l₁ ∷ Level
    → Γ ⊢ l₂ ∷ Level
    → Γ ∙ A ⊢ t ∷ B
    → Γ     ⊢ a ∷ A
    → p PE.≡ p′
    → Π-allowed p q
    → Γ     ⊢ ∘ʰ p′ l₂ (lamʰ p t) a ≡ t [ a ]₀ ∷ B [ a ]₀
  β-redʰ′ {l₁} {l₂} {A} {t} {B} {a} {p} ⊢l₁ ⊢l₂ ⊢t ⊢a PE.refl ok =
    let ⊢A = wf-⊢∷ ⊢a
        ⊢B = wf-⊢∷ ⊢t
        ⊢LiftA = Liftⱼ ⊢l₂ ⊢A
        ⊢wkl₁ = wkTerm₁ ⊢LiftA ⊢l₁
        ⊢lower₀B = lower₀Type ⊢l₂ ⊢B
        ⊢LiftB = Liftⱼ ⊢wkl₁ ⊢lower₀B
        ⊢lifta = liftⱼ′ ⊢l₂ ⊢a
        ⊢lower₀t = lower₀Term ⊢l₂ ⊢t
        ⊢liftlower₀t = liftⱼ′ ⊢wkl₁ ⊢lower₀t
    in
    ∘ʰ p l₂ (lamʰ p t) a ≡⟨⟩⊢
    lower (lam p (lift (lower₀ t)) ∘⟨ p ⟩ lift a)
      ≡⟨ lower-cong (conv
          (β-red ⊢LiftB ⊢liftlower₀t ⊢lifta PE.refl ok)
          (Lift-cong (refl (substTerm ⊢wkl₁ ⊢lifta)) (lower₀[lift]₀ ⊢B ⊢a))) ⟩⊢
    lower (lift (lower₀ t) [ lift a ]₀)
      ≡⟨ lower-cong (lift-cong ⊢l₁ (lower₀[lift]₀∷ ⊢t ⊢a)) ⟩⊢
    lower (lift (t [ a ]₀))
      ⇒⟨ Lift-β⇒ (substTerm ⊢t ⊢a) ⟩⊢∎
    t [ a ]₀
      ∎

opaque

  -- A variant of β-redʰ′.

  β-redʰ :
    Γ ⊢ l₁ ∷ Level →
    Γ ⊢ l₂ ∷ Level →
    Γ ∙ A ⊢ t ∷ B →
    Γ ⊢ u ∷ A →
    Π-allowed p q →
    Γ ⊢ ∘ʰ p l₂ (lamʰ p t) u ≡ t [ u ]₀ ∷ B [ u ]₀
  β-redʰ ⊢l₁ ⊢l₂ ⊢t ⊢u =
    β-redʰ′ ⊢l₁ ⊢l₂ ⊢t ⊢u PE.refl

opaque
  unfolding ΠΣʰ ∘ʰ lower₀

  -- Heterogeneous η-rule

  η-eqʰ′
    : Γ ⊢ l₁ ∷ Level
    → Γ ∙ A ⊢ B
    → Γ     ⊢ f ∷ Πʰ p q l₁ l₂ A B
    → Γ     ⊢ g ∷ Πʰ p q l₁ l₂ A B
    → Γ ∙ A ⊢ ∘ʰ p (wk1 l₂) (wk1 f) (var x0) ≡ ∘ʰ p (wk1 l₂) (wk1 g) (var x0) ∷ B
    → Γ     ⊢ f ≡ g ∷ Πʰ p q l₁ l₂ A B
  η-eqʰ′ {Γ} {l₁} {A} {B} {f} {p} {q} {l₂} {g} ⊢l₁ ⊢B ⊢f ⊢g f≡g =
    let _ , ⊢l₂ , _ , _ , ok = inversion-ΠΣʰ-⊢ {B = B} (wf-⊢∷ ⊢f)
        ⊢A = ⊢∙→⊢ (wf ⊢B)
        ⊢LiftA = Liftⱼ ⊢l₂ ⊢A
        ⊢x₀ = var (∙ ⊢LiftA) here
        lemma
          : ∀ {f}
          → Γ ⊢ f ∷ Πʰ p q l₁ l₂ A B
          → Γ ∙ Lift l₂ A ⊢ lower₀ (lower (wk1 f ∘⟨ p ⟩ lift (var x0)))
                          ≡ lower (wk1 f ∘⟨ p ⟩ var x0) ∷ lower₀ B
        lemma ⊢f =
          conv
            (lower-cong
              (app-cong
                (PE.subst₃ (_⊢_≡_∷_ _)
                  (PE.sym (wk1-[][]↑ 1)) PE.refl PE.refl
                  (refl (wkTerm₁ ⊢LiftA ⊢f)))
                (sym′ (Lift-η-swap ⊢x₀ (refl (lowerⱼ ⊢x₀))))))
            (PE.subst (_⊢_≡_ _ _) (wkSingleSubstId _)
              (substTypeEq
                (refl (W.wk
                  (liftʷ (step id) (wk₁ ⊢LiftA ⊢LiftA))
                  (lower₀Type ⊢l₂ ⊢B)))
                (sym′ (Lift-η-swap ⊢x₀ (refl (lowerⱼ ⊢x₀))))))
    in η-eq′ ⊢f ⊢g $ Lift-η′
        (PE.subst (_⊢_∷_ _ _) (wkSingleSubstId _) (wkTerm₁ ⊢LiftA ⊢f ∘ⱼ var (∙ ⊢LiftA) here))
        (PE.subst (_⊢_∷_ _ _) (wkSingleSubstId _) (wkTerm₁ ⊢LiftA ⊢g ∘ⱼ var (∙ ⊢LiftA) here))
        (lower (wk1 f ∘⟨ p ⟩ var x0)                 ≡˘⟨ lemma ⊢f ⟩⊢
         lower₀ (lower (wk1 f ∘⟨ p ⟩ lift (var x0))) ≡⟨ lower₀TermEq ⊢l₂ f≡g ⟩⊢
         lower₀ (lower (wk1 g ∘⟨ p ⟩ lift (var x0))) ≡⟨ lemma ⊢g ⟩⊢∎
         lower (wk1 g ∘⟨ p ⟩ var x0)                 ∎)

opaque

  -- A variant of η-eqʰ′

  η-eqʰ :
    Γ ⊢ l₁ ∷ Level →
    Γ ∙ A ⊢ B ∷ U (wk1 l₂) →
    Γ ⊢ t₁ ∷ Πʰ p q l₁ l₂ A B →
    Γ ⊢ t₂ ∷ Πʰ p q l₁ l₂ A B →
    Γ ∙ A ⊢ ∘ʰ p (wk1 l₂) (wk1 t₁) (var x0) ≡
      ∘ʰ p (wk1 l₂) (wk1 t₂) (var x0) ∷ B →
    Γ ⊢ t₁ ≡ t₂ ∷ Πʰ p q l₁ l₂ A B
  η-eqʰ ⊢l₁ ⊢B = η-eqʰ′ ⊢l₁ (univ ⊢B)
