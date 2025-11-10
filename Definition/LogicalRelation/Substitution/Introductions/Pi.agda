------------------------------------------------------------------------
-- Validity for Π-types
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Pi
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  ⦃ eqrel : EqRelSet R ⦄
  where

open EqRelSet eqrel
open Type-restrictions R

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
import Definition.LogicalRelation.Hidden.Restricted R as R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R
open import
  Definition.LogicalRelation.Substitution.Introductions.Pi-Sigma R
open import Definition.LogicalRelation.Substitution.Introductions.Var R
open import Definition.LogicalRelation.Weakening.Restricted R

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Reduction R
open import Definition.Typed.Reasoning.Term R
open import Definition.Typed.Stability R
open import Definition.Typed.Substitution R
open import Definition.Typed.Weakening R as W using (_∷ʷ_⊇_)
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private variable
  m n                 : Nat
  Γ Δ Η               : Con Term _
  A B t t₁ t₂ u u₁ u₂ : Term _
  ρ                   : Wk _ _
  σ σ₁ σ₂             : Subst _ _
  p q                 : M
  l l′ l″             : Universe-level

------------------------------------------------------------------------
-- Some characterisation lemmas

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷Π⇔ :
    {A : Term n} {B : Term (1+ n)} →
    Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ Π p , q ▷ A ▹ B ⇔
    (Γ ⊩⟨ l ⟩ Π p , q ▷ A ▹ B ×
     ∃₂ λ u₁ u₂ →
     Γ ⊢ t₁ ⇒* u₁ ∷ Π p , q ▷ A ▹ B ×
     Γ ⊢ t₂ ⇒* u₂ ∷ Π p , q ▷ A ▹ B ×
     Functionᵃ u₁ ×
     Functionᵃ u₂ ×
     Γ ⊢ u₁ ≅ u₂ ∷ Π p , q ▷ A ▹ B ×
     ∀ {m} {ρ : Wk m n} {Δ : Con Term m} {v₁ v₂} →
     ρ ∷ʷʳ Δ ⊇ Γ →
     Δ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ wk ρ A →
     Δ ⊩⟨ l ⟩ wk ρ u₁ ∘⟨ p ⟩ v₁ ≡ wk ρ u₂ ∘⟨ p ⟩ v₂ ∷
       wk (lift ρ) B [ v₁ ]₀)
  ⊩≡∷Π⇔ {n} {Γ} {l} {t₁} {t₂} {p} {q} {A} {B} =
      (λ (⊩Π , t₁≡t₂) →
         case B-view ⊩Π of λ {
           (Bᵣ (Bᵣ _ _ Π⇒*Π _ ⊩wk-A ⊩wk-B _ _)) →
         case t₁≡t₂ of λ
           (u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ , u₁-fun , u₂-fun , u₁≅u₂ , rest) →
         case B-PE-injectivity _ _ $ whnfRed* Π⇒*Π ΠΣₙ of λ {
           (PE.refl , PE.refl , _) →
         ⊩Π ,
         ((∃₂ λ u₁ u₂ →
          Γ ⊢ t₁ ⇒* u₁ ∷ Π p , q ▷ A ▹ B ×
          Γ ⊢ t₂ ⇒* u₂ ∷ Π p , q ▷ A ▹ B ×
          Functionᵃ u₁ ×
          Functionᵃ u₂ ×
          Γ ⊢ u₁ ≅ u₂ ∷ Π p , q ▷ A ▹ B ×
          ∀ {m} {ρ : Wk m n} {Δ : Con Term m} {v₁ v₂} →
          ρ ∷ʷʳ Δ ⊇ Γ →
          Δ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ wk ρ A →
          Δ ⊩⟨ l ⟩ wk ρ u₁ ∘⟨ p ⟩ v₁ ≡ wk ρ u₂ ∘⟨ p ⟩ v₂ ∷
            wk (lift ρ) B [ v₁ ]₀) ∋
         u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ , u₁-fun , u₂-fun , u₁≅u₂ ,
         λ ρ⊇ v₁≡v₂ →
           let ⊩v₁ , ⊩v₂ = wf-⊩≡∷ v₁≡v₂ in
           ⊩≡∷-intro (⊩wk-B ρ⊇ _) $
           rest ρ⊇ (⊩∷→⊩∷/ (⊩wk-A ρ⊇) ⊩v₁) (⊩∷→⊩∷/ (⊩wk-A ρ⊇) ⊩v₂)
             (⊩≡∷→⊩≡∷/ (⊩wk-A ρ⊇) v₁≡v₂)) }})
    , (λ (⊩Π , rest) →
         case B-view ⊩Π of λ {
           (Bᵣ ⊩Π′@(Bᵣ _ _ Π⇒*Π _ ⊩wk-A ⊩wk-B _ _)) →
         case rest of λ
           (u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ , u₁-fun , u₂-fun , u₁≅u₂ , rest) →
         case B-PE-injectivity _ _ $ whnfRed* Π⇒*Π ΠΣₙ of λ {
           (PE.refl , PE.refl , _) →
         Bᵣ _ ⊩Π′ ,
         (_ ⊩⟨ _ ⟩ _ ≡ _ ∷ _ / Bᵣ _ ⊩Π′ ∋
         u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ , u₁-fun , u₂-fun , u₁≅u₂ ,
         λ ρ⊇ ⊩v ⊩w v≡w →
           ⊩≡∷→⊩≡∷/ (⊩wk-B ρ⊇ ⊩v) $
           rest ρ⊇ $
           ⊩≡∷-intro (⊩wk-A ρ⊇) v≡w) }})

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷Π⇔ :
    {A : Term n} {B : Term (1+ n)} →
    Γ ⊩⟨ l ⟩ t ∷ Π p , q ▷ A ▹ B ⇔
    (Γ ⊩⟨ l ⟩ Π p , q ▷ A ▹ B ×
     ∃ λ u →
     Γ ⊢ t ⇒* u ∷ Π p , q ▷ A ▹ B ×
     Functionᵃ u ×
     Γ ⊢≅ u ∷ Π p , q ▷ A ▹ B ×
     ∀ {m} {ρ : Wk m n} {Δ : Con Term m} {v₁ v₂} →
     ρ ∷ʷʳ Δ ⊇ Γ →
     Δ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ wk ρ A →
     Δ ⊩⟨ l ⟩ wk ρ u ∘⟨ p ⟩ v₁ ≡ wk ρ u ∘⟨ p ⟩ v₂ ∷
       wk (lift ρ) B [ v₁ ]₀)
  ⊩∷Π⇔ {n} {Γ} {l} {t} {p} {q} {A} {B} =
    Γ ⊩⟨ l ⟩ t ∷ Π p , q ▷ A ▹ B                       ⇔⟨ ⊩∷⇔⊩≡∷ ⟩

    Γ ⊩⟨ l ⟩ t ≡ t ∷ Π p , q ▷ A ▹ B                   ⇔⟨ ⊩≡∷Π⇔ ⟩

    (Γ ⊩⟨ l ⟩ Π p , q ▷ A ▹ B ×
     ∃₂ λ u₁ u₂ →
     Γ ⊢ t ⇒* u₁ ∷ Π p , q ▷ A ▹ B ×
     Γ ⊢ t ⇒* u₂ ∷ Π p , q ▷ A ▹ B ×
     Functionᵃ u₁ ×
     Functionᵃ u₂ ×
     Γ ⊢ u₁ ≅ u₂ ∷ Π p , q ▷ A ▹ B ×
     ∀ {m} {ρ : Wk m n} {Δ : Con Term m} {v₁ v₂} →
     ρ ∷ʷʳ Δ ⊇ Γ →
     Δ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ wk ρ A →
     Δ ⊩⟨ l ⟩ wk ρ u₁ ∘⟨ p ⟩ v₁ ≡ wk ρ u₂ ∘⟨ p ⟩ v₂ ∷
       wk (lift ρ) B [ v₁ ]₀)                          ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                             ( (λ (_ , t⇒*u₁ , t⇒*u₂ , u₁-fun , u₂-fun , u₁≅u₂ , u₁∘≡u₂∘) →
                                                                  case whrDet*Term (t⇒*u₁ , Functionᵃ→Whnf u₁-fun)
                                                                         (t⇒*u₂ , Functionᵃ→Whnf u₂-fun) of λ {
                                                                    PE.refl →
                                                                  t⇒*u₁ , u₁-fun , u₁≅u₂ , u₁∘≡u₂∘ })
                                                             , (λ (t⇒*u , u-fun , ≅u , u∘≡u∘) →
                                                                  _ , t⇒*u , t⇒*u , u-fun , u-fun , ≅u , u∘≡u∘)
                                                             )) ⟩
    (Γ ⊩⟨ l ⟩ Π p , q ▷ A ▹ B ×
     ∃ λ u →
     Γ ⊢ t ⇒* u ∷ Π p , q ▷ A ▹ B ×
     Functionᵃ u ×
     Γ ⊢≅ u ∷ Π p , q ▷ A ▹ B ×
     ∀ {m} {ρ : Wk m n} {Δ : Con Term m} {v₁ v₂} →
     ρ ∷ʷʳ Δ ⊇ Γ →
     Δ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ wk ρ A →
     Δ ⊩⟨ l ⟩ wk ρ u ∘⟨ p ⟩ v₁ ≡ wk ρ u ∘⟨ p ⟩ v₂ ∷
       wk (lift ρ) B [ v₁ ]₀)                          □⇔

------------------------------------------------------------------------
-- Lambdas

opaque

  -- Reducibility of equality between applications of lam.

  ⊩lam≡lam :
    {σ₁ σ₂ : Subst m n} →
    Π-allowed p q →
    Γ ∙ A ⊢ t₁ ≡ t₂ ∷ B →
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ B →
    ⦃ inc : Neutrals-included or-empty Δ ⦄ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l ⟩ lam p t₁ [ σ₁ ] ≡ lam p t₂ [ σ₂ ] ∷
      (Π p , q ▷ A ▹ B) [ σ₁ ]
  ⊩lam≡lam
    {m} {p} {A} {t₁} {t₂} {B} {l} {Δ} {σ₁} {σ₂}
    ok ⊢t₁≡t₂ ⊩A t₁≡t₂ σ₁≡σ₂ =
    case wf-⊢≡∷ ⊢t₁≡t₂ of λ
      (⊢B , ⊢t₁ , ⊢t₂) →
    case ⊢∙→⊢ (wf ⊢B) of λ
      ⊢A →
    case escape-⊩ˢ≡∷ σ₁≡σ₂ of λ
      (⊢Δ , ⊢σ₁≡σ₂) →
    case wf-⊢ˢʷ≡∷ (⊢ˢʷ≡∷-⇑′ ⊢A ⊢σ₁≡σ₂) of λ
      (_ , ⊢σ₁⇑ , ⊢σ₂⇑) →
    case stability-⊢ˢʷ∷ˡ (refl-∙ (subst-⊢≡ (refl ⊢A) ⊢σ₁≡σ₂)) ⊢σ₂⇑ of λ
      ⊢σ₂⇑ →
    case wf-⊩ˢ≡∷ σ₁≡σ₂ of λ
      (⊩σ₁ , ⊩σ₂) →
    case wf-⊩ᵛ≡∷ t₁≡t₂ of λ
      (⊩t₁ , ⊩t₂) →
    case wf-⊩ᵛ∷ ⊩t₁ of λ
      ⊩B →
    case ⊩ᵛ→⊩ˢ∷→⊩[] ⊩A ⊩σ₁ of λ
      ⊩A[σ₁] →
    case R.escape-⊩ ⊩A[σ₁] of λ
      ⊢A[σ₁] →
    case wf-⊢≡∷ (subst-⊢≡∷ (lam-cong ⊢t₁≡t₂ ok) ⊢σ₁≡σ₂) of λ
      (_ , ⊢lam-t₁[σ₁] , ⊢lam-t₂[σ₂]) →
    case
      (∀ k (ρ : Wk k m) (Ε : Con Term k) v₁ v₂ →
       ρ ∷ʷʳ Ε ⊇ Δ →
       Ε ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ wk ρ (A [ σ₁ ]) →
       Ε ⊩⟨ l ⟩ wk ρ (lam p t₁ [ σ₁ ]) ∘⟨ p ⟩ v₁ ≡
         wk ρ (lam p t₂ [ σ₂ ]) ∘⟨ p ⟩ v₂ ∷
         wk (lift ρ) (B [ σ₁ ⇑ ]) [ v₁ ]₀) ∋
      (λ _ ρ _ v₁ v₂ ρʳ⊇ v₁≡v₂ →
         let instance
               inc = wk-Neutrals-included-or-empty← ρʳ⊇
             ρ⊇ = ∷ʷʳ⊇→∷ʷ⊇ ρʳ⊇
         in
         case W.wk ρ⊇ ⊢A[σ₁] of λ
           ⊢wk-ρ-A[σ₁] →
         case W.wk ρ⊇ $ R.escape-⊩ $ ⊩ᵛ→⊩ˢ∷→⊩[] ⊩A ⊩σ₂ of λ
           ⊢wk-ρ-A[σ₂] →
         case wf-⊩≡∷ v₁≡v₂ of λ
           (⊩v₁ , ⊩v₂) →
         case conv-⊩∷
                (wk-⊩≡ ρʳ⊇ $ R.⊩≡→ $
                 ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] (refl-⊩ᵛ≡ ⊩A) σ₁≡σ₂)
                ⊩v₂ of λ
           ⊩v₂ →
         case ⊩ˢ≡∷∙⇔ {σ₁ = consSubst _ _} {σ₂ = consSubst _ _} .proj₂
                ( ( _ , ⊩A
                  , PE.subst (R._⊩⟨_⟩_≡_∷_ _ _ _ _) (wk-subst A)
                      (R.→⊩≡∷ v₁≡v₂)
                  )
                , ⊩ˢ≡∷-•ₛ ρ⊇ σ₁≡σ₂
                ) of λ
           ρ•ₛσ₁,v₁≡ρ•ₛσ₂,v₂ →
         lam p (wk (lift ρ) (t₁ [ σ₁ ⇑ ])) ∘⟨ p ⟩ v₁  ⇒⟨ β-red (W.wk (W.liftʷʷ ρ⊇ ⊢wk-ρ-A[σ₁]) (subst-⊢ ⊢B ⊢σ₁⇑))
                                                           (W.wkTerm (W.liftʷʷ ρ⊇ ⊢wk-ρ-A[σ₁]) (subst-⊢∷ ⊢t₁ ⊢σ₁⇑))
                                                           (escape-⊩∷ ⊩v₁) PE.refl ok ⟩⊩∷
         wk (lift ρ) (t₁ [ σ₁ ⇑ ]) [ v₁ ]₀ ∷
           wk (lift ρ) (B [ σ₁ ⇑ ]) [ v₁ ]₀           ≡⟨ singleSubstWkComp _ _ t₁ ⟩⊩∷∷≡
                                                       ⟨ singleSubstWkComp _ _ B ⟩⊩∷≡
         t₁ [ consSubst (ρ •ₛ σ₁) v₁ ] ∷
           B [ consSubst (ρ •ₛ σ₁) v₁ ]               ≡⟨ R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t₁≡t₂ ρ•ₛσ₁,v₁≡ρ•ₛσ₂,v₂ ⟩⊩∷∷⇐*
                                                       ⟨ ≅-eq $ R.escape-⊩≡ $
                                                         ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] (refl-⊩ᵛ≡ ⊩B) ρ•ₛσ₁,v₁≡ρ•ₛσ₂,v₂ ⟩⇒
         t₂ [ consSubst (ρ •ₛ σ₂) v₂ ] ∷
           B [ consSubst (ρ •ₛ σ₂) v₂ ]               ≡˘⟨ singleSubstWkComp _ _ t₂ ⟩⇐∷
                                                       ˘⟨ singleSubstWkComp _ _ B ⟩⇒≡
         wk (lift ρ) (t₂ [ σ₂ ⇑ ]) [ v₂ ]₀ ∷
           wk (lift ρ) (B [ σ₂ ⇑ ]) [ v₂ ]₀           ⇐⟨ β-red (W.wk (W.liftʷʷ ρ⊇ (⊢wk-ρ-A[σ₂])) (subst-⊢ ⊢B ⊢σ₂⇑))
                                                           (W.wkTerm (W.liftʷʷ ρ⊇ (⊢wk-ρ-A[σ₂])) (subst-⊢∷ ⊢t₂ ⊢σ₂⇑))
                                                           (escape-⊩∷ ⊩v₂) PE.refl ok
                                                       ⟩∎∷
         lam p (wk (lift ρ) (t₂ [ σ₂ ⇑ ])) ∘⟨ p ⟩ v₂  ∎)
    of λ
      lemma →
    ⊩≡∷Π⇔ .proj₂
      ( R.⊩→ (⊩ᵛ→⊩ˢ∷→⊩[] (ΠΣᵛ (ΠΣⱼ ⊢B ok) ⊩A ⊩B) ⊩σ₁)
      , _ , _
      , id ⊢lam-t₁[σ₁]
      , id ⊢lam-t₂[σ₂]
      , lamₙ , lamₙ
      , with-inc-⊢≅∷ (subst-⊢≡∷ (lam-cong ⊢t₁≡t₂ ok) ⊢σ₁≡σ₂)
          (let instance
                 inc : Neutrals-included or-empty Η
                 inc = included
               step-id =
                 W.stepʷ W.id ⊢A[σ₁]
           in
           ≅-η-eq ⊢lam-t₁[σ₁] ⊢lam-t₂[σ₂] lamₙ lamₙ $
           escape-⊩≡∷ $
           PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (idWkLiftSubstLemma _ B) $
           lemma _ (step id) _ _ _ (∷ʷ⊇→∷ʷʳ⊇ step-id) $
           refl-⊩≡∷ $ ⊩var here $
           R.⊩→ $ R.wk-⊩ step-id ⊩A[σ₁])
      , lemma _ _ _ _ _
      )

opaque

  -- Validity of equality preservation for lam.

  lam-congᵛ :
    Π-allowed p q →
    Γ ∙ A ⊢ t₁ ≡ t₂ ∷ B →
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ B →
    Γ ⊩ᵛ⟨ l ⟩ lam p t₁ ≡ lam p t₂ ∷ Π p , q ▷ A ▹ B
  lam-congᵛ ok ⊢t₁≡t₂ ⊩A t₁≡t₂ =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( ΠΣᵛ (ΠΣⱼ (wf-⊢≡∷ ⊢t₁≡t₂ .proj₁) ok) ⊩A
          (wf-⊩ᵛ∷ $ wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁)
      , ⊩lam≡lam ok ⊢t₁≡t₂ ⊩A t₁≡t₂
      )

opaque

  -- Validity of lam.

  lamᵛ :
    Π-allowed p q →
    Γ ∙ A ⊢ t ∷ B →
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t ∷ B →
    Γ ⊩ᵛ⟨ l ⟩ lam p t ∷ Π p , q ▷ A ▹ B
  lamᵛ ok ⊢t ⊩A ⊩t =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    lam-congᵛ ok (refl ⊢t) ⊩A (refl-⊩ᵛ≡∷ ⊩t)

------------------------------------------------------------------------
-- Applications

opaque

  -- Reducibility of equality between applications.

  ⊩∘≡∘ :
    Γ ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ Π p , q ▷ A ▹ B →
    Γ ⊩ᵛ⟨ l′ ⟩ u₁ ≡ u₂ ∷ A →
    ⦃ inc : Neutrals-included or-empty Δ ⦄ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l ⟩ (t₁ ∘⟨ p ⟩ u₁) [ σ₁ ] ≡ (t₂ ∘⟨ p ⟩ u₂) [ σ₂ ] ∷
      B [ u₁ ]₀ [ σ₁ ]
  ⊩∘≡∘ {t₁} {t₂} {p} {B} {u₁} {u₂} {σ₁} {σ₂} t₁≡t₂ u₁≡u₂ σ₁≡σ₂ =
    case ⊩ᵛ≡∷⇔″ .proj₁ t₁≡t₂ of λ
      (⊩t₁ , _ , t₁[]≡t₂[]) →
    case wf-⊩ᵛ≡∷ u₁≡u₂ of λ
      (⊩u₁ , ⊩u₂) →
    case wf-⊩ˢ≡∷ σ₁≡σ₂ of λ
      (⊩σ₁ , ⊩σ₂) →
    case ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ u₁≡u₂ σ₁≡σ₂ of λ
      u₁[σ₁]≡u₂[σ₂] →
    case ⊩ᵛΠΣ→ (wf-⊩ᵛ∷ ⊩t₁) of λ
      (_ , ⊩A , ⊩B) →
    case ⊩≡∷Π⇔ .proj₁ $ R.⊩≡∷→ $ t₁[]≡t₂[] σ₁≡σ₂ of λ
      (_ , t₁′ , t₂′ , t₁[σ₁]⇒*t₁′ , t₂[σ₂]⇒*t₂′ , _ , _ , _ , rest) →
                           ∷ B [ u₁ ]₀ [ σ₁ ]             ⟨ singleSubstLift B _ ⟩⊩∷∷≡
    (t₁ ∘⟨ p ⟩ u₁) [ σ₁ ]  ∷ B [ σ₁ ⇑ ] [ u₁ [ σ₁ ] ]₀  ⇒*⟨ app-subst* t₁[σ₁]⇒*t₁′ $
                                                            R.escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u₁ ⊩σ₁ ⟩⊩∷∷
    t₁′ ∘⟨ p ⟩ (u₁ [ σ₁ ])                              ≡⟨ PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _)
                                                             (PE.cong₃ _∘⟨_⟩_ (wk-id _) PE.refl PE.refl)
                                                             (PE.cong₃ _∘⟨_⟩_ (wk-id _) PE.refl PE.refl)
                                                             (PE.cong₂ _[_]₀ (wk-lift-id (B [ _ ])) PE.refl) $
                                                           rest (id (escape-⊩ˢ∷ ⊩σ₁ .proj₁)) $
                                                           PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (PE.sym $ wk-id _) $
                                                           level-⊩≡∷ (R.⊩→ $ ⊩ᵛ→⊩ˢ∷→⊩[] ⊩A ⊩σ₁)
                                                             (R.⊩≡∷→ u₁[σ₁]≡u₂[σ₂]) ⟩⊩∷⇐*
                                                          ⟨ ≅-eq $ R.escape-⊩≡ $
                                                            ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀
                                                              (refl-⊩ᵛ≡ ⊩B) (refl-⊩ˢ≡∷ ⊩σ₁) u₁[σ₁]≡u₂[σ₂] ⟩⇒
    t₂′ ∘⟨ p ⟩ (u₂ [ σ₂ ]) ∷ B [ σ₁ ⇑ ] [ u₂ [ σ₂ ] ]₀  ⇐*⟨ app-subst* t₂[σ₂]⇒*t₂′ $
                                                            R.escape-⊩∷ $
                                                            R.conv-⊩∷ (R.sym-⊩≡ $ ⊩ᵛ⇔ .proj₁ ⊩A .proj₂ σ₁≡σ₂) $
                                                            ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u₂ ⊩σ₂ ⟩∎∷
    (t₂ ∘⟨ p ⟩ u₂) [ σ₂ ]                               ∎

opaque

  -- Validity of equality preservation for application.

  ∘-congᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ Π p , q ▷ A ▹ B →
    Γ ⊩ᵛ⟨ l′ ⟩ u₁ ≡ u₂ ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t₁ ∘⟨ p ⟩ u₁ ≡ t₂ ∘⟨ p ⟩ u₂ ∷ B [ u₁ ]₀
  ∘-congᵛ t₁≡t₂ u₁≡u₂ =
    case ⊩ᵛΠΣ→ $ wf-⊩ᵛ∷ $ wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁ of λ
      (_ , _ , ⊩B) →
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ ⊩B (wf-⊩ᵛ≡∷ u₁≡u₂ .proj₁)
      , ⊩∘≡∘ t₁≡t₂ u₁≡u₂
      )

opaque

  -- Validity of application.

  ∘ᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ Π p , q ▷ A ▹ B →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t ∘⟨ p ⟩ u ∷ B [ u ]₀
  ∘ᵛ ⊩t ⊩u =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    ∘-congᵛ (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ᵛ≡∷ ⊩u)

------------------------------------------------------------------------
-- Validity of some equality rules

opaque

  -- Validity of β-reduction.

  β-redᵛ :
    Π-allowed p q →
    Γ ∙ A ⊢ t ∷ B →
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t ∷ B →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ lam p t ∘⟨ p ⟩ u ≡ t [ u ]₀ ∷ B [ u ]₀
  β-redᵛ {t} {B} ok ⊢t ⊩t ⊩u =
    ⊩ᵛ∷-⇐
      (λ ⊩σ →
         PE.subst₂ (_⊢_⇒_∷_ _ _) (PE.sym $ singleSubstLift t _)
           (PE.sym $ singleSubstLift B _) $
         β-red-⇒ (subst-⊢∷-⇑ ⊢t (escape-⊩ˢ∷ ⊩σ .proj₂))
           (R.escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u ⊩σ) ok)
      (⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₀∷ ⊩t ⊩u)

private opaque

  -- A lemma used below.

  wk-[]∘≡ :
    (t : Term n) →
    wk ρ (t [ σ ]) ∘⟨ p ⟩ u PE.≡
    (wk1 t ∘⟨ p ⟩ var x0) [ consSubst (ρ •ₛ σ) u ]
  wk-[]∘≡ {ρ} {σ} {u} t =
    PE.cong (_∘⟨ _ ⟩ _)
      (wk ρ (t [ σ ])                  ≡⟨ wk-subst t ⟩
       t [ ρ •ₛ σ ]                    ≡˘⟨ wk1-sgSubst _ _ ⟩
       wk1 (t [ ρ •ₛ σ ]) [ u ]₀       ≡˘⟨ PE.cong _[ _ ] $ wk1-liftSubst t ⟩
       wk1 t [ (ρ •ₛ σ) ⇑ ] [ u ]₀     ≡⟨ singleSubstComp _ _ (wk1 t) ⟩
       wk1 t [ consSubst (ρ •ₛ σ) u ]  ∎)

opaque

  -- Validity of η-equality.

  η-eqᵛ :
    Γ ⊢ t₁ ∷ Π p , q ▷ A ▹ B →
    Γ ⊩ᵛ⟨ l ⟩ t₁ ∷ Π p , q ▷ A ▹ B →
    Γ ⊢ t₂ ∷ Π p , q ▷ A ▹ B →
    Γ ⊩ᵛ⟨ l′ ⟩ t₂ ∷ Π p , q ▷ A ▹ B →
    Γ ∙ A ⊢ wk1 t₁ ∘⟨ p ⟩ var x0 ≡ wk1 t₂ ∘⟨ p ⟩ var x0 ∷ B →
    Γ ∙ A ⊩ᵛ⟨ l″ ⟩ wk1 t₁ ∘⟨ p ⟩ var x0 ≡ wk1 t₂ ∘⟨ p ⟩ var x0 ∷ B →
    Γ ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ Π p , q ▷ A ▹ B
  η-eqᵛ
    {t₁} {p} {A} {B} {l} {t₂}
    ⊢t₁ ⊩t₁ ⊢t₂ ⊩t₂ ⊢wk1-t₁∘0≡wk1-t₂∘0 wk1-t₁∘0≡wk1-t₂∘0 =
    case wf-⊩ᵛ∷ ⊩t₁ of λ
      ⊩ΠAB →
    case ⊩ᵛΠΣ→ ⊩ΠAB of λ
      (_ , ⊩A , ⊩B) →
    ⊩ᵛ≡∷⇔′ʰ .proj₂
      ( ⊩t₁
      , level-⊩ᵛ∷ ⊩ΠAB ⊩t₂
      , λ {m = m} {Δ = Δ} {σ = σ} ⊩σ →
          case ⊩ᵛ→⊩ˢ∷→⊩[] ⊩A ⊩σ of λ
            ⊩A[σ] →
          case R.escape-⊩ ⊩A[σ] of λ
            ⊢A[σ] →
          case ⊩∷Π⇔ .proj₁ $ R.⊩∷→ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t₁ ⊩σ of λ
            (⊩ΠAB[σ] , u₁ , t₁[σ]⇒*u₁ , u₁-fun , _ , _) →
          case ⊩∷Π⇔ .proj₁ $ R.⊩∷→ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t₂ ⊩σ of λ
            (_ , u₂ , t₂[σ]⇒*u₂ , u₂-fun , _ , _) →
          case
            (∀ k (ρ : Wk k m) (Ε : Con Term k) v₁ v₂ →
             ρ ∷ʷʳ Ε ⊇ Δ →
             Ε ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ wk ρ (A [ σ ]) →
             Ε ⊩⟨ l ⟩ wk ρ u₁ ∘⟨ p ⟩ v₁ ≡ wk ρ u₂ ∘⟨ p ⟩ v₂ ∷
               wk (lift ρ) (B [ σ ⇑ ]) [ v₁ ]₀) ∋
            (λ _ ρ _ v₁ v₂ ρ⊇ v₁≡v₂ →
               let instance
                     inc = wk-Neutrals-included-or-empty← ρ⊇
                   ρ⊇ = ∷ʷʳ⊇→∷ʷ⊇ ρ⊇
               in
               case wf-⊩≡∷ v₁≡v₂ of λ
                 (⊩v₁ , ⊩v₂) →
               case R.⊩≡→ $
                    ⊩ᵛ⇔ .proj₁ ⊩B .proj₂ $
                    ⊩ˢ≡∷∙⇔ .proj₂
                      ( ( _ , ⊩A
                        , (R.→⊩≡∷ $
                           PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (wk-subst A)
                             v₁≡v₂)
                        )
                      , refl-⊩ˢ≡∷ (⊩ˢ∷-•ₛ ρ⊇ ⊩σ)
                      ) of λ
                 B[ρ•ₛσ,v₁]≡B[ρ•ₛσ,v₂] →

               wk ρ u₁ ∘⟨ p ⟩ v₁ ∷ wk (lift ρ) (B [ σ ⇑ ]) [ v₁ ]₀  ⇐*⟨ app-subst* (W.wkRed*Term ρ⊇ t₁[σ]⇒*u₁) (escape-⊩∷ ⊩v₁) ⟩⊩∷∷

               wk ρ (t₁ [ σ ]) ∘⟨ p ⟩ v₁                            ≡⟨ wk-[]∘≡ t₁ ⟩⊩∷≡
                                                                     ⟨ singleSubstWkComp _ _ B ⟩⊩∷≡
               (wk1 t₁ ∘⟨ p ⟩ var x0) [ consSubst (ρ •ₛ σ) v₁ ] ∷
                 B [ consSubst (ρ •ₛ σ) v₁ ]                        ≡⟨ level-⊩≡∷ (wf-⊩≡ B[ρ•ₛσ,v₁]≡B[ρ•ₛσ,v₂] .proj₁) $
                                                                       R.⊩≡∷→ $
                                                                       ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,]∷ wk1-t₁∘0≡wk1-t₂∘0
                                                                         (⊩ˢ≡∷-•ₛ ρ⊇ (refl-⊩ˢ≡∷ ⊩σ))
                                                                         (R.→⊩≡∷ $ PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (wk-subst A) v₁≡v₂) ⟩⊩∷∷⇒*
                                                                     ⟨ ≅-eq $ escape-⊩≡ B[ρ•ₛσ,v₁]≡B[ρ•ₛσ,v₂] ⟩⇒
               (wk1 t₂ ∘⟨ p ⟩ var x0) [ consSubst (ρ •ₛ σ) v₂ ] ∷
                 B [ consSubst (ρ •ₛ σ) v₂ ]                        ≡˘⟨ wk-[]∘≡ t₂ ⟩⇒∷
                                                                     ˘⟨ singleSubstWkComp _ _ B ⟩⇒≡
               wk ρ (t₂ [ σ ]) ∘⟨ p ⟩ v₂ ∷
                 wk (lift ρ) (B [ σ ⇑ ]) [ v₂ ]₀                    ⇒*⟨ app-subst* (W.wkRed*Term ρ⊇ t₂[σ]⇒*u₂) (escape-⊩∷ ⊩v₂) ⟩∎∷

               wk ρ u₂ ∘⟨ p ⟩ v₂                                    ∎)
          of λ
            lemma →
          ⊩≡∷Π⇔ .proj₂
            ( ⊩ΠAB[σ]
            , u₁ , u₂ , t₁[σ]⇒*u₁ , t₂[σ]⇒*u₂ , u₁-fun , u₂-fun
            , with-inc-⊢≅∷
                (u₁        ⇐*⟨ t₁[σ]⇒*u₁ ⟩⊢
                 t₁ [ σ ]  ≡⟨ subst-⊢≡∷ (η-eq′ ⊢t₁ ⊢t₂ ⊢wk1-t₁∘0≡wk1-t₂∘0)
                                (refl-⊢ˢʷ≡∷ $ escape-⊩ˢ∷ ⊩σ .proj₂) ⟩⊢
                 t₂ [ σ ]  ⇒*⟨ t₂[σ]⇒*u₂ ⟩⊢∎
                 u₂        ∎)
                (let instance
                       inc : Neutrals-included or-empty Η
                       inc = included
                     step-id =
                       ∷ʷ⊇→∷ʷʳ⊇ $ W.stepʷ W.id ⊢A[σ]
                 in
                 ≅-η-eq (wf-⊢≡∷ (subset*Term t₁[σ]⇒*u₁) .proj₂ .proj₂)
                   (wf-⊢≡∷ (subset*Term t₂[σ]⇒*u₂) .proj₂ .proj₂)
                   (Functionᵃ→ u₁-fun) (Functionᵃ→ u₂-fun)
                   (PE.subst (_⊢_≅_∷_ _ _ _)
                      (idWkLiftSubstLemma _ B) $
                    escape-⊩≡∷ $
                    lemma _ _ _ _ _ step-id $
                    refl-⊩≡∷ $
                    ⊩var here $
                    wk-⊩ step-id $ R.⊩→ ⦃ inc = inc ⦄ ⊩A[σ]))
            , lemma _ _ _ _ _
            )
      )
