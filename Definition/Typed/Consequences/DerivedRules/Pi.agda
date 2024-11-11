------------------------------------------------------------------------
-- Derived rules related to Π-types
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.DerivedRules.Pi
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Reduction R
open import Definition.Typed.RedSteps R
import Definition.Typed.Substitution R as S
open import Definition.Typed.Weakening R as W hiding (wk)

open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private variable
  Γ                                                   : Con _ _
  A B C D E t u u₁ u₂ u₃ u₄ v w                       : Term _
  p p′ p″ p₁ p₁′ p₂ p₂′ p₃ p₃′ p₄ p₄′ q q₁ q₂ q₃ q₄ r : M

------------------------------------------------------------------------
-- Simple variants of typing/equality/reduction rules

opaque

  -- A variant of the reduction rule β-red.

  β-red-⇒ :
    Γ ∙ A ⊢ t ∷ B →
    Γ ⊢ u ∷ A →
    Π-allowed p q →
    Γ ⊢ lam p t ∘⟨ p ⟩ u ⇒ t [ u ]₀ ∷ B [ u ]₀
  β-red-⇒ ⊢t ⊢u =
    β-red (syntacticTerm ⊢t) ⊢t ⊢u PE.refl

opaque

  -- A variant of the equality rule β-red.

  β-red-≡ :
    Γ ∙ A ⊢ t ∷ B →
    Γ ⊢ u ∷ A →
    Π-allowed p q →
    Γ ⊢ lam p t ∘⟨ p ⟩ u ≡ t [ u ]₀ ∷ B [ u ]₀
  β-red-≡ ⊢t ⊢u ok =
    subsetTerm (β-red-⇒ ⊢t ⊢u ok)

------------------------------------------------------------------------
-- Other derived rules

opaque

  -- Another variant of the reduction rule β-red.

  β-red-⇒₁ :
    Γ ⊢ lam p t ∷ Π p′ , q ▷ A ▹ B →
    Γ ⊢ u ∷ A →
    Γ ⊢ lam p t ∘⟨ p′ ⟩ u ⇒ t [ u ]₀ ∷ B [ u ]₀
  β-red-⇒₁ ⊢lam ⊢u =
    case inversion-lam-Π ⊢lam of λ {
      (⊢t , PE.refl , ok) →
    β-red-⇒ ⊢t ⊢u ok }

opaque

  -- Another variant of the equality rule β-red.

  β-red-≡₁ :
    Γ ⊢ lam p t ∷ Π p′ , q ▷ A ▹ B →
    Γ ⊢ u ∷ A →
    Γ ⊢ lam p t ∘⟨ p′ ⟩ u ≡ t [ u ]₀ ∷ B [ u ]₀
  β-red-≡₁ ⊢lam ⊢u =
    subsetTerm (β-red-⇒₁ ⊢lam ⊢u)

opaque

  -- A variant of β-red-⇒₁ for functions of two arguments.

  β-red-⇒₂ :
    Γ ⊢ lam p₁ (lam p₂ t) ∷ Π p₁′ , q₁ ▷ A ▹ Π p₂′ , q₂ ▷ B ▹ C →
    Γ ⊢ u ∷ A →
    Γ ⊢ v ∷ B [ u ]₀ →
    Γ ⊢ lam p₁ (lam p₂ t) ∘⟨ p₁′ ⟩ u ∘⟨ p₂′ ⟩ v ⇒* t [ u , v ]₁₀ ∷
      C [ u , v ]₁₀
  β-red-⇒₂ {p₁} {p₂} {t} {p₁′} {p₂′} {C} {u} {v} ⊢lam ⊢u ⊢v =
    case substitutionTerm (inversion-lam-Π ⊢lam .proj₁)
           (singleSubst ⊢u) (wfTerm ⊢u) of λ {
      ⊢lam′ →                                         ⟨ PE.sym $ singleSubstComp _ _ C ⟩⇒≡
    lam p₁ (lam p₂ t) ∘⟨ p₁′ ⟩ u ∘⟨ p₂′ ⟩ v          ⇒⟨ app-subst (β-red-⇒₁ ⊢lam ⊢u) ⊢v ⟩
    lam p₂ (t [ liftSubst (sgSubst u) ]) ∘⟨ p₂′ ⟩ v  ⇒⟨ β-red-⇒₁ ⊢lam′ ⊢v ⟩∎≡
    t [ liftSubst (sgSubst u) ] [ v ]₀               ≡⟨ singleSubstComp _ _ t ⟩
    t [ u , v ]₁₀                                    ∎ }

opaque

  -- A variant of β-red-⇒₁ for functions of three arguments.

  β-red-⇒₃ :
    Γ ⊢ lam p₁ (lam p₂ (lam p₃ t)) ∷
        Π p₁′ , q₁ ▷ A ▹ Π p₂′ , q₂ ▷ B ▹ Π p₃′ , q₃ ▷ C ▹ D →
    Γ ⊢ u ∷ A →
    Γ ⊢ v ∷ B [ u ]₀ →
    Γ ⊢ w ∷ C [ u , v ]₁₀ →
    Γ ⊢ lam p₁ (lam p₂ (lam p₃ t)) ∘⟨ p₁′ ⟩ u ∘⟨ p₂′ ⟩ v ∘⟨ p₃′ ⟩ w ⇒*
        t [ consSubst (consSubst (sgSubst u) v) w ] ∷
        D [ consSubst (consSubst (sgSubst u) v) w ]
  β-red-⇒₃
    {p₁} {p₂} {p₃} {t} {p₁′} {p₂′} {p₃′} {D} {u} {v} {w} ⊢lam ⊢u ⊢v ⊢w =
    case substitutionTerm
           (inversion-lam-Π (inversion-lam-Π ⊢lam .proj₁) .proj₁)
           (singleSubst ⊢u , ⊢v)
           (wfTerm ⊢u) of λ {
      ⊢lam′ →                                                        ⟨ PE.sym $ singleSubstComp _ _ D ⟩⇒≡
    lam p₁ (lam p₂ (lam p₃ t)) ∘⟨ p₁′ ⟩ u ∘⟨ p₂′ ⟩ v ∘⟨ p₃′ ⟩ w    ⇒*⟨ app-subst* (β-red-⇒₂ ⊢lam ⊢u ⊢v) ⊢w ⟩
    lam p₃ (t [ liftSubst (consSubst (sgSubst u) v) ]) ∘⟨ p₃′ ⟩ w  ⇒⟨ β-red-⇒₁ ⊢lam′ ⊢w ⟩∎≡
    t [ liftSubst (consSubst (sgSubst u) v) ] [ w ]₀               ≡⟨ singleSubstComp _ _ t ⟩
    t [ consSubst (consSubst (sgSubst u) v) w ]                    ∎ }

opaque

  -- A variant of β-red-⇒₁ for functions of four arguments.

  β-red-⇒₄ :
    Γ ⊢ lam p₁ (lam p₂ (lam p₃ (lam p₄ t))) ∷
        Π p₁′ , q₁ ▷ A ▹ Π p₂′ , q₂ ▷ B ▹ Π p₃′ , q₃ ▷ C ▹
        Π p₄′ , q₄ ▷ D ▹ E →
    Γ ⊢ u₁ ∷ A →
    Γ ⊢ u₂ ∷ B [ u₁ ]₀ →
    Γ ⊢ u₃ ∷ C [ u₁ , u₂ ]₁₀ →
    Γ ⊢ u₄ ∷ D [ consSubst (consSubst (sgSubst u₁) u₂) u₃ ] →
    Γ ⊢ lam p₁ (lam p₂ (lam p₃ (lam p₄ t)))
          ∘⟨ p₁′ ⟩ u₁ ∘⟨ p₂′ ⟩ u₂ ∘⟨ p₃′ ⟩ u₃ ∘⟨ p₄′ ⟩ u₄ ⇒*
        t [ consSubst (consSubst (consSubst (sgSubst u₁) u₂) u₃) u₄ ] ∷
        E [ consSubst (consSubst (consSubst (sgSubst u₁) u₂) u₃) u₄ ]
  β-red-⇒₄
    {p₁} {p₂} {p₃} {p₄} {t} {p₁′} {p₂′} {p₃′} {p₄′} {E}
    {u₁} {u₂} {u₃} {u₄} ⊢lam ⊢u₁ ⊢u₂ ⊢u₃ ⊢u₄ =
    case substitutionTerm
           (inversion-lam-Π
              (inversion-lam-Π (inversion-lam-Π ⊢lam .proj₁) .proj₁)
              .proj₁)
           ((singleSubst ⊢u₁ , ⊢u₂) , ⊢u₃)
           (wfTerm ⊢u₁) of λ {
      ⊢lam′ →                                                              ⟨ PE.sym $ singleSubstComp _ _ E ⟩⇒≡
    lam p₁ (lam p₂ (lam p₃ (lam p₄ t)))
      ∘⟨ p₁′ ⟩ u₁ ∘⟨ p₂′ ⟩ u₂ ∘⟨ p₃′ ⟩ u₃ ∘⟨ p₄′ ⟩ u₄                    ⇒*⟨ app-subst* (β-red-⇒₃ ⊢lam ⊢u₁ ⊢u₂ ⊢u₃) ⊢u₄ ⟩

    lam p₄ (t [ liftSubst (consSubst (consSubst (sgSubst u₁) u₂) u₃) ])
      ∘⟨ p₄′ ⟩ u₄                                                        ⇒⟨ β-red-⇒₁ ⊢lam′ ⊢u₄ ⟩∎≡

    t [ liftSubst (consSubst (consSubst (sgSubst u₁) u₂) u₃) ] [ u₄ ]₀   ≡⟨ singleSubstComp _ _ t ⟩

    t [ consSubst (consSubst (consSubst (sgSubst u₁) u₂) u₃) u₄ ]        ∎ }

opaque

  -- Lambdas preserve definitional equality.

  lam-cong :
    Γ ∙ A ⊢ t ≡ u ∷ B →
    Π-allowed p q →
    Γ ⊢ lam p t ≡ lam p u ∷ Π p , q ▷ A ▹ B
  lam-cong t≡u =
    let ⊢B , ⊢t , ⊢u = syntacticEqTerm t≡u in
    S.lam-cong ⊢B ⊢t ⊢u t≡u

opaque

  -- A reduction rule for weakened lambdas applied to variable zero.

  wk1-lam∘0⇒ :
    Γ ⊢ lam p t ∷ Π q , r ▷ A ▹ B →
    Γ ∙ A ⊢ wk1 (lam p t) ∘⟨ p ⟩ var x0 ⇒ t ∷ B
  wk1-lam∘0⇒ ⊢lam =
    case inversion-lam-Π ⊢lam of λ {
      (⊢t , PE.refl , ok) →
    case wfTerm ⊢t of λ {
      (∙ ⊢A) →
    PE.subst₂ (_⊢_⇒_∷_ _ _)
      (wkSingleSubstId _)
      (wkSingleSubstId _)
      (β-red-⇒
         (wkTerm (liftʷ (step id) (W.wk (stepʷ id ⊢A) ⊢A)) ⊢t)
         (var₀ ⊢A) ok) }}

opaque

  -- An equality rule for weakened lambdas applied to variable zero.

  wk1-lam∘0≡ :
    Γ ⊢ lam p t ∷ Π q , r ▷ A ▹ B →
    Γ ∙ A ⊢ wk1 (lam p t) ∘⟨ p ⟩ var x0 ≡ t ∷ B
  wk1-lam∘0≡ ⊢lam = subsetTerm (wk1-lam∘0⇒ ⊢lam)

opaque

  -- An inverse of uncurry lam-cong (up to logical equivalence).

  lam-cong⁻¹ :
    Γ ⊢ lam p t ≡ lam p u ∷ Π p , q ▷ A ▹ B →
    Γ ∙ A ⊢ t ≡ u ∷ B × Π-allowed p q
  lam-cong⁻¹ {Γ} {p} {t} {u} {q} {A} {B} lam-t≡lam-u =
    case syntacticEqTerm lam-t≡lam-u of λ {
      (⊢ΠAB , ⊢lam-t , ⊢lam-u) →
    case inversion-ΠΣ ⊢ΠAB .proj₁ of λ {
      ⊢A →                                                               $⟨ lam-t≡lam-u ⟩

    Γ ⊢ lam p t ≡ lam p u ∷ Π p , q ▷ A ▹ B                              →⟨ wkEqTerm₁ ⊢A ⟩

    Γ ∙ A ⊢ wk1 (lam p t) ≡ wk1 (lam p u) ∷ wk1 (Π p , q ▷ A ▹ B)        →⟨ flip app-cong (refl (var₀ ⊢A)) ⟩

    Γ ∙ A ⊢ wk1 (lam p t) ∘⟨ p ⟩ var x0 ≡ wk1 (lam p u) ∘⟨ p ⟩ var x0 ∷
      wk (lift (step id)) B [ var x0 ]₀                                  →⟨ PE.subst (_ ⊢ _ ≡ _ ∷_) (wkSingleSubstId _) ⟩

    Γ ∙ A ⊢ wk1 (lam p t) ∘⟨ p ⟩ var x0 ≡ wk1 (lam p u) ∘⟨ p ⟩ var x0 ∷
      B                                                                  →⟨ (λ hyp → trans
                                                                               (sym′ (wk1-lam∘0≡ ⊢lam-t))
                                                                               (trans hyp (wk1-lam∘0≡ ⊢lam-u))) ⟩

    Γ ∙ A ⊢ t ≡ u ∷ B                                                    →⟨ _, inversion-lam-Π ⊢lam-t .proj₂ .proj₂ ⟩

    Γ ∙ A ⊢ t ≡ u ∷ B × Π-allowed p q                                    □ }}

opaque

  -- An injectivity lemma for lam.

  lam-injective :
    Γ ⊢ lam p t ≡ lam p′ u ∷ Π p″ , q ▷ A ▹ B →
    p PE.≡ p′ × Γ ∙ A ⊢ t ≡ u ∷ B × Π-allowed p q × p′ PE.≡ p″
  lam-injective {Γ} {p} {t} {p′} {u} {p″} {q} {A} {B} lam-t≡lam-u =
    case syntacticEqTerm lam-t≡lam-u of λ {
      (_ , ⊢lam₁ , ⊢lam₂) →
    case inversion-lam-Π ⊢lam₁ of λ {
      (_ , PE.refl , _) →
    case inversion-lam-Π ⊢lam₂ of λ {
      (_ , PE.refl , _) →
    case lam-cong⁻¹ lam-t≡lam-u of λ {
      (t≡u , ok) →
    PE.refl , t≡u , ok , PE.refl }}}}

opaque

  -- An η-rule for Π-types.

  Π-η :
    Γ ⊢ t ∷ Π p , q ▷ A ▹ B →
    Γ ⊢ lam p (wk1 t ∘⟨ p ⟩ var x0) ≡ t ∷ Π p , q ▷ A ▹ B
  Π-η {Γ} {t} {p} {q} {A} {B} ⊢t =
    case inversion-ΠΣ (syntacticTerm ⊢t) of λ {
      (⊢A , _ , ok) →
    case                                                               $⟨ wkTerm₁ ⊢A ⊢t ∘ⱼ var₀ ⊢A ⟩
      Γ ∙ A ⊢ wk1 t ∘⟨ p ⟩ var x0 ∷ wk (lift (step id)) B [ var x0 ]₀  →⟨ PE.subst (_ ⊢ _ ∷_) (wkSingleSubstId _) ⟩
      Γ ∙ A ⊢ wk1 t ∘⟨ p ⟩ var x0 ∷ B                                  →⟨ lamⱼ′ ok ⟩
      Γ ⊢ lam p (wk1 t ∘⟨ p ⟩ var x0) ∷ Π p , q ▷ A ▹ B                □
    of λ {
      ⊢lam →
    η-eq′ ⊢lam ⊢t
      (                                                     $⟨ ⊢lam ⟩

       Γ ⊢ lam p (wk1 t ∘⟨ p ⟩ var x0) ∷ Π p , q ▷ A ▹ B    →⟨ wk1-lam∘0≡ ⟩

       Γ ∙ A ⊢
         wk1 (lam p (wk1 t ∘⟨ p ⟩ var x0)) ∘⟨ p ⟩ var x0 ≡
         wk1 t ∘⟨ p ⟩ var x0 ∷
         B                                                  □) }}
