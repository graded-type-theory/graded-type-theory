------------------------------------------------------------------------
-- Validity for unit types
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Unit
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Reduction R
open import Definition.Typed.Stability.Primitive R
open import Definition.Typed.Substitution.Primitive R
open import Definition.Typed.Well-formed R
open import Definition.LogicalRelation R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Hidden R ⦃ eqrel ⦄
import Definition.LogicalRelation.Hidden.Restricted R ⦃ eqrel ⦄ as R
open import Definition.LogicalRelation.Properties R ⦃ eqrel ⦄
open import Definition.LogicalRelation.ShapeView R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Substitution R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Substitution.Introductions.Level R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Substitution.Introductions.Universe R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Irrelevance R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Unary R ⦃ eqrel ⦄

open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum

private
  variable
    n : Nat
    Γ Δ : Con Term n
    σ σ₁ σ₂ : Subst _ _
    s s₁ s₂ : Strength
    l l′ l″ l‴ l₁ l₂ : Universe-level
    A A₁ A₂ k k₁ k₂ k′ t t₁ t₂ u u₁ u₂ : Term n
    p q : M

------------------------------------------------------------------------
-- Characterisation lemmas

opaque

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩Unit⇔ :
    Γ ⊩⟨ l ⟩ Unit s ⇔
    (⊢ Γ × Unit-allowed s)
  ⊩Unit⇔ =
      (λ ⊩Unit →
        case Unit-view ⊩Unit of λ {
          (Unitᵣ (Unitᵣ Unit⇒*Unit ok)) →
      wf (escape ⊩Unit) , ok })
    , (λ (⊢Γ , ok) →
         Unitᵣ′ (id (Unitⱼ ⊢Γ ok)) ok)

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩Unit≡⇔ :
    Γ ⊩⟨ l ⟩ Unit s ≡ A ⇔
    (Γ ⊢ A ⇒* Unit s ×
     Unit-allowed s)
  ⊩Unit≡⇔ {l} {s} {A} =
      (λ (⊩Unit , _ , Unit≡A) →
         case Unit-view ⊩Unit of λ {
           (Unitᵣ (Unitᵣ Unit⇒*Unit ok)) →
         case Unit≡A of λ
           (Unit₌ A⇒) →
        A⇒ , ok })
    , (λ (A⇒*Unit , ok) →
         sym-⊩≡
           (A       ⇒*⟨ A⇒*Unit ⟩⊩
            Unit s  ∎⟨ ⊩Unit⇔ .proj₂ (wf (redFirst* A⇒*Unit) , ok) ⟩⊩))

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩Unit≡Unit⇔ :
    Γ ⊩⟨ l ⟩ Unit s₁ ≡ Unit s₂ ⇔
    (⊢ Γ × Unit-allowed s₁ × s₁ PE.≡ s₂)
  ⊩Unit≡Unit⇔ {Γ} {l} {s₁} {s₂} =
    Γ ⊩⟨ l ⟩ Unit s₁ ≡ Unit s₂            ⇔⟨ ⊩Unit≡⇔ ⟩
    (Γ ⊢ Unit s₂ ⇒* Unit s₁ × Unit-allowed s₁) ⇔⟨ ((λ { (Unit⇒*Unit , ok) →
                                                     case Unit-PE-injectivity $ whnfRed* Unit⇒*Unit Unitₙ of λ {
                                                       PE.refl →
                                                     wf (redFirst* Unit⇒*Unit) , ok , PE.refl }})
                                                 , λ { (⊢Γ , ok , PE.refl) →
                                                       id (Unitⱼ ⊢Γ ok) , ok }) ⟩
    (⊢ Γ × Unit-allowed s₁ × s₁ PE.≡ s₂) □⇔

opaque
  unfolding _⊩⟨_⟩_≡_∷_ ⊩Unit⇔

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷Unit⇔ :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ Unit s ⇔
    (Unit-allowed s × Γ ⊩Unit⟨ s ⟩ t ≡ u ∷Unit)
  ⊩≡∷Unit⇔ =
      (λ (⊩Unit , t≡u) →
         case Unit-view ⊩Unit of λ {
            (Unitᵣ (Unitᵣ Unit⇒*Unit ok)) →
         ok , t≡u })
    , (λ (ok , t≡u@(Unitₜ₌ _ _ (d , _) _ _)) →
        ⊩Unit⇔ .proj₂ (wfTerm (redFirst*Term d) , ok) , t≡u)

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷Unit⇔ :
    Γ ⊩⟨ l ⟩ t ∷ Unit s ⇔
    (Unit-allowed s × Γ ⊩Unit⟨ s ⟩ t ∷Unit)
  ⊩∷Unit⇔ {Γ} {l} {t} {s} =
    Γ ⊩⟨ l ⟩ t ∷ Unit s                                   ⇔⟨ ⊩∷⇔⊩≡∷ ⟩
    Γ ⊩⟨ l ⟩ t ≡ t ∷ Unit s                               ⇔⟨ ⊩≡∷Unit⇔ ⟩
    (Unit-allowed s × Γ ⊩Unit⟨ s ⟩ t ≡ t ∷Unit)          ⇔˘⟨ (Σ-cong-⇔ λ _ → ⊩Unit∷Unit⇔⊩Unit≡∷Unit) ⟩
    (Unit-allowed s × Γ ⊩Unit⟨ s ⟩ t ∷Unit)              □⇔

------------------------------------------------------------------------
-- Unit

opaque

  -- If the type Unit s l is valid, then it is allowed (given a
  -- certain assumption).

  ⊩ᵛUnit→Unit-allowed :
    ⦃ inc : Neutrals-included or-empty Γ ⦄ →
    Γ ⊩ᵛ⟨ l ⟩ Unit s →
    Unit-allowed s
  ⊩ᵛUnit→Unit-allowed {Γ} {l} {s} =
    Γ ⊩ᵛ⟨ l ⟩ Unit s       →⟨ R.⊩→ ∘→ ⊩ᵛ→⊩ ⟩
    Γ ⊩⟨ l ⟩ Unit s        ⇔⟨ ⊩Unit⇔ ⟩→
    (⊢ Γ × Unit-allowed s) →⟨ proj₂ ⟩
    Unit-allowed s         □

opaque

  -- Reducibility for Unit.

  ⊩Unit :
    ⊢ Γ →
    Unit-allowed s →
    Γ ⊩⟨ 0ᵘ ⟩ Unit s
  ⊩Unit ⊢Γ ok = ⊩Unit⇔ .proj₂ (⊢Γ , ok)

opaque

  -- Validity for Unit, seen as a term former.

  Unitᵗᵛ :
    ⊩ᵛ Γ →
    Unit-allowed s →
    Γ ⊩ᵛ⟨ ωᵘ ⟩ Unit s ∷ U zeroᵘ
  Unitᵗᵛ ⊩Γ ok =
    ⊩ᵛ∷⇔ʰ .proj₂
      ( ⊩ᵛU (zeroᵘᵛ ⊩Γ)
      , λ σ₁≡σ₂ →
          let ⊢Δ , _ = escape-⊩ˢ≡∷ σ₁≡σ₂
          in Type→⊩≡∷U⇔ Unitₙ Unitₙ .proj₂
            ( ⊩zeroᵘ ⊢Δ , <ᵘ-ωᵘ
            , ⊩Unit≡Unit⇔ .proj₂ (⊢Δ , ok , PE.refl)
            , ≅ₜ-Unit-refl ⊢Δ ok
            )
      )

opaque

  -- Validity for Unit, seen as a type former.

  Unitᵛ :
    ⊩ᵛ Γ →
    Unit-allowed s →
    Γ ⊩ᵛ⟨ ωᵘ ⟩ Unit s
  Unitᵛ ⊩Γ ok = ⊩ᵛ∷U→⊩ᵛ (Unitᵗᵛ ⊩Γ ok)

------------------------------------------------------------------------
-- The constructor star

opaque

  -- Reducibility of equality preservation for star.

  ⊩star :
    ⊢ Γ →
    Unit-allowed s →
    Γ ⊩⟨ 0ᵘ ⟩ star s ∷ Unit s
  ⊩star {s} ⊢Γ ok =
    ⊩∷Unit⇔ .proj₂
      ( ok
      , Unitₜ _ (id (starⱼ ⊢Γ ok) , starₙ) (Unit-prop′→Unit-prop starᵣ))

opaque

  -- Validity of star.

  starᵛ :
    ⊩ᵛ Γ →
    Unit-allowed s →
    Γ ⊩ᵛ⟨ ωᵘ ⟩ star s ∷ Unit s
  starᵛ ⊩Γ ok =
    ⊩ᵛ∷⇔ʰ .proj₂
      ( Unitᵛ ⊩Γ ok
      , λ σ₁≡σ₂ →
          emb-⊩≡∷ ≤ᵘ-ωᵘ $ refl-⊩≡∷ (⊩star (escape-⊩ˢ≡∷ σ₁≡σ₂ .proj₁) ok)
      )

------------------------------------------------------------------------
-- The typing rule η-unit

opaque

  -- Reducibility of η-unit.

  ⊩η-unit :
    Γ ⊩⟨ l′ ⟩ t ∷ Unit s →
    Γ ⊩⟨ l″ ⟩ u ∷ Unit s →
    Unit-with-η s →
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ Unit s
  ⊩η-unit ⊩t ⊩u η =
    let
      (ok , Unitₜ _ t↘ _) = ⊩∷Unit⇔ .proj₁ ⊩t
      (_  , Unitₜ _ u↘ _) = ⊩∷Unit⇔ .proj₁ ⊩u
    in ⊩≡∷Unit⇔ .proj₂
      ( ok
      , Unitₜ₌ _ _ t↘ u↘ (Unitₜ₌ˢ η)
      )

opaque

  -- Validity of η-unit.

  η-unitᵛ :
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ Unit s →
    Γ ⊩ᵛ⟨ l″ ⟩ u ∷ Unit s →
    Unit-with-η s →
    Γ ⊩ᵛ⟨ l′ ⟩ t ≡ u ∷ Unit s
  η-unitᵛ ⊩t ⊩u η =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( wf-⊩ᵛ∷ ⊩t
      , λ σ₁≡σ₂ →
          ⊩η-unit
            (wf-⊩≡∷ (⊩ᵛ∷⇔ʰ .proj₁ ⊩t .proj₂ σ₁≡σ₂) .proj₁)
            (wf-⊩≡∷ (⊩ᵛ∷⇔ʰ .proj₁ ⊩u .proj₂ σ₁≡σ₂) .proj₂)
            η
      )

------------------------------------------------------------------------
-- The eliminator unitrec

opaque

  -- Reducibility of equality between applications of unitrec.

  ⊩unitrec≡unitrec :
    Γ ∙ Unitʷ ⊢ A₁ ≡ A₂ →
    Γ ∙ Unitʷ ⊩ᵛ⟨ l′ ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l″ ⟩ t₁ ≡ t₂ ∷ Unitʷ →
    Γ ⊩ᵛ⟨ l‴ ⟩ u₁ ≡ u₂ ∷ A₁ [ starʷ ]₀ →
    ⦃ inc : Neutrals-included or-empty Δ ⦄ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ unitrec p q A₁ t₁ u₁ [ σ₁ ] ≡
      unitrec p q A₂ t₂ u₂ [ σ₂ ] ∷ A₁ [ t₁ ]₀ [ σ₁ ]
  ⊩unitrec≡unitrec
    {A₁} {A₂} {l′} {t₁} {t₂} {u₁} {u₂} {Δ} {σ₁} {σ₂} {p} {q}
    ⊢A₁≡A₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ σ₁≡σ₂ =
    let
      ⊩Γ = wf-⊩ᵛ (wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁))
      (⊩A₁ , ⊩A₂) = wf-⊩ᵛ≡ A₁≡A₂
      (⊩t₁ , ⊩t₂ , t₁≡t₂) = ⊩ᵛ≡∷⇔″ .proj₁ t₁≡t₂
      (⊩u₁ , ⊩u₂ , u₁≡u₂) = ⊩ᵛ≡∷⇔″ .proj₁ u₁≡u₂
      (⊩σ₁ , ⊩σ₂) = wf-⊩ˢ≡∷ σ₁≡σ₂
      ⊩Unit = ⊩ᵛ∷⇔ .proj₁ ⊩t₁ .proj₁
      ⊢Unit = R.escape-⊩ $ ⊩ᵛ→⊩ˢ∷→⊩[] ⊩Unit ⊩σ₁
      A₁[σ₁⇑]≡A₂[σ₂⇑] = ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑]≡[⇑] A₁≡A₂ σ₁≡σ₂
    in
    case ⊩≡∷Unit⇔ .proj₁ (R.⊩≡∷⇔ .proj₁ (t₁≡t₂ σ₁≡σ₂)) of λ {
      (ok ,
       Unitₜ₌ t₁′ t₂′ (t₁[σ₁]⇒*t₁′ , _) (t₂[σ₂]⇒*t₂′ , _) prop) →
    let
      ⋆≡⋆ = refl-⊩ᵛ≡∷ (starᵛ ⊩Γ ok)
      A₁[⋆]₀[σ₁]≡A₂[⋆]₀[σ₂] =
        PE.subst₂ (_⊢_≡_ _) (substConsId {t = star!} A₁)
          (substConsId {t = star!} A₂) $
        ≅-eq $ R.escape-⊩≡ $
        ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,] A₁≡A₂ σ₁≡σ₂ $
        ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ ⋆≡⋆ σ₁≡σ₂
      (⊢A₁[σ₁⇑] , ⊢A₂[σ₂⇑]) =
          wf-⊢≡ $ subst-⊢≡ ⊢A₁≡A₂ $
            ⊢ˢʷ≡∷-⇑ (refl ⊢Unit) $ escape-⊩ˢ≡∷ σ₁≡σ₂ .proj₂
      ⊩t₁[σ₁] = ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t₁ ⊩σ₁
      ⊩t₂[σ₂] = ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t₂ ⊩σ₂
      ⊢t₂[σ₂] = R.escape-⊩∷ ⊩t₂[σ₂]
      ⊢u₁[σ₁] =
        R.escape-⊩∷ $
        PE.subst (R._⊩⟨_⟩_∷_ _ _ _) (singleSubstLift A₁ starʷ) $
        ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u₁ ⊩σ₁
      ⊢u₂[σ₂] =
        R.escape-⊩∷ $
        R.conv-⊩∷
          (⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ A₁≡A₂ (refl-⊩ˢ≡∷ ⊩σ₂)
            (⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ ⋆≡⋆ (refl-⊩ˢ≡∷ ⊩σ₂))) $
        PE.subst (R._⊩⟨_⟩_∷_ _ _ _) (singleSubstLift A₁ starʷ) $
        ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u₂ ⊩σ₂
    in case prop of λ where
      (Unitₜ₌ˢ η)  →
        case starᵛ (wf-⊩ᵛ ⊩Unit) ok of λ
          ⊩⋆ →
        unitrec p q A₁ t₁ u₁ [ σ₁ ] ∷ A₁ [ t₁ ]₀ [ σ₁ ]        ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift A₁ t₁) $
                                                                     unitrec-β-η ⊢A₁[σ₁⇑] (R.escape-⊩∷ ⊩t₁[σ₁]) ⊢u₁[σ₁] ok
                                                                     (Unit-with-η-𝕨→Unitʷ-η η) ⟩⊩∷∷
                                                                   ⟨ R.⊩≡⇔ .proj₁ $
                                                                     ⊩ᵛ≡→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[] (refl-⊩ᵛ≡ ⊩A₁)
                                                                       (⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (η-unitᵛ ⊩t₁ ⊩⋆ η) $
                                                                        refl-⊩ˢ≡∷ ⊩σ₁)
                                                                       (refl-⊩ˢ≡∷ ⊩σ₁) ⟩⊩∷
        u₁ [ σ₁ ]  ∷ A₁ [ starʷ ]₀ [ σ₁ ]                      ≡⟨ R.⊩≡∷⇔ .proj₁ (u₁≡u₂ σ₁≡σ₂) ⟩⊩∷∷⇐*
                                                                   ⟨ A₁[⋆]₀[σ₁]≡A₂[⋆]₀[σ₂] ⟩⇒
                   ∷ A₂ [ starʷ ]₀ [ σ₂ ]                       ⟨ singleSubstLift A₂ starʷ ⟩⇐≡
        u₂ [ σ₂ ]  ∷ A₂ [ σ₂ ⇑ ] [ starʷ [ σ₂ ] ]₀             ⇐⟨ conv
                                                                       (unitrec-β-η ⊢A₂[σ₂⇑] ⊢t₂[σ₂] ⊢u₂[σ₂] ok
                                                                          (Unit-with-η-𝕨→Unitʷ-η η))
                                                                       (≅-eq $ R.escape-⊩≡ $
                                                                        ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩A₂) (refl-⊩ˢ≡∷ ⊩σ₂) $
                                                                        ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (η-unitᵛ ⊩t₂ ⊩⋆ η) $
                                                                        refl-⊩ˢ≡∷ ⊩σ₂)
                                                                   ⟩∎∷
        unitrec p q A₂ t₂ u₂ [ σ₂ ]                            ∎

      (Unitₜ₌ʷ rest no-η) →
        let
          unitrec⇒*₁ =
            PE.subst (_⊢_⇒*_∷_ _ _ _) (PE.sym $ singleSubstLift A₁ t₁) $
            unitrec-subst* {p = p} {q = q} t₁[σ₁]⇒*t₁′ ⊢A₁[σ₁⇑] ⊢u₁[σ₁] no-η
          unitrec⇒*₂ =
            PE.subst (_⊢_⇒*_∷_ _ _ _) (PE.sym $ singleSubstLift A₂ t₂) $
            unitrec-subst* {p = p} {q = q} t₂[σ₂]⇒*t₂′ ⊢A₂[σ₂⇑] ⊢u₂[σ₂] no-η
          A₁[t₁]₀[σ₁]≡A₁[σ₁⇑][t₁′]₀ =
            PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (PE.sym $ singleSubstLift A₁ t₁) PE.refl $
            R.⊩≡→ $
            ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩A₁) (refl-⊩ˢ≡∷ ⊩σ₁)
              (R.→⊩≡∷ $ ⊩∷-⇒* t₁[σ₁]⇒*t₁′ $ R.⊩∷→ ⊩t₁[σ₁])
          ⊢A₂[t₂]₀[σ₂]≡A₂[σ₂⇑][t₂′]₀ =
            ≅-eq $ escape-⊩≡ $
            PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (PE.sym $ singleSubstLift A₂ t₂) PE.refl $
            R.⊩≡→ $
            ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩A₂) (refl-⊩ˢ≡∷ ⊩σ₂)
              (R.→⊩≡∷ $ ⊩∷-⇒* t₂[σ₂]⇒*t₂′ $ R.⊩∷→ ⊩t₂[σ₂])
        in case rest of λ where
          starᵣ →
            unitrec p q A₁ t₁       u₁ [ σ₁ ] ∷ A₁ [ t₁ ]₀ [ σ₁ ]         ⇒*⟨ unitrec⇒*₁ ⟩⊩∷∷
                                                                               ⟨ A₁[t₁]₀[σ₁]≡A₁[σ₁⇑][t₁′]₀ ⟩⊩∷
            unitrec p q (A₁ [ σ₁ ⇑ ]) starʷ (u₁ [ σ₁ ])
                                                 ∷ A₁ [ σ₁ ⇑ ] [ starʷ ]₀
                                                                             ⇒⟨ unitrec-β ⊢A₁[σ₁⇑] ⊢u₁[σ₁] ok no-η ⟩⊩∷∷
                                                                             ˘⟨ singleSubstLift A₁ starʷ ⟩⊩∷≡
            u₁ [ σ₁ ]                            ∷ A₁ [ starʷ ]₀ [ σ₁ ]   ≡⟨ R.⊩≡∷→ $ u₁≡u₂ σ₁≡σ₂ ⟩⊩∷∷⇐*
                                                                              ⟨ A₁[⋆]₀[σ₁]≡A₂[⋆]₀[σ₂] ⟩⇒
                                                 ∷ A₂ [ starʷ ]₀ [ σ₂ ]    ⟨ singleSubstLift A₂ starʷ ⟩⇐≡
            u₂ [ σ₂ ]                            ∷ A₂ [ σ₂ ⇑ ] [ starʷ [ σ₂ ] ]₀
                                                                             ⇐⟨ unitrec-β ⊢A₂[σ₂⇑] ⊢u₂[σ₂] ok no-η ⟩∷
                                                 ∷ A₂ [ σ₂ ⇑ ] [ starʷ ]₀ ˘⟨ ⊢A₂[t₂]₀[σ₂]≡A₂[σ₂⇑][t₂′]₀ ⟩⇒
            unitrec p q (A₂ [ σ₂ ⇑ ]) starʷ (u₂ [ σ₂ ])
                                                 ∷ A₂ [ t₂ ]₀ [ σ₂ ]         ⇐*⟨ unitrec⇒*₂ ⟩∎∷
            unitrec p q A₂ t₂        u₂ [ σ₂ ]                            ∎

          (ne (neNfₜ₌ inc t₁′-ne t₂′-ne t₁′~t₂′)) →
            Δ ⊩⟨ l′ ⟩
              unitrec p q (A₁ [ σ₁ ⇑ ]) (t₁ [ σ₁ ]) (u₁ [ σ₁ ]) ≡
              unitrec p q (A₂ [ σ₂ ⇑ ]) (t₂ [ σ₂ ]) (u₂ [ σ₂ ]) ∷
              A₁ [ t₁ ]₀ [ σ₁ ] ∋
            (unitrec p q A₁ t₁ u₁ [ σ₁ ]
               ∷ A₁ [ t₁ ]₀ [ σ₁ ]                                ⇒*⟨ unitrec⇒*₁ ⟩⊩∷∷
                                                                    ⟨ A₁[t₁]₀[σ₁]≡A₁[σ₁⇑][t₁′]₀ ⟩⊩∷
             unitrec p q (A₁ [ σ₁ ⇑ ]) t₁′ (u₁ [ σ₁ ])
               ∷ A₁ [ σ₁ ⇑ ] [ t₁′ ]₀                             ≡⟨ neutral-⊩≡∷ inc (wf-⊩≡ A₁[t₁]₀[σ₁]≡A₁[σ₁⇑][t₁′]₀ .proj₂)
                                                                       (unitrecₙ no-η t₁′-ne) (unitrecₙ no-η t₂′-ne)
                                                                       (~-unitrec
                                                                          (escape-⊩≡ $
                                                                           R.⊩≡→ ⦃ inc = included ⦃ inc = inc ⦄ ⦄ A₁[σ₁⇑]≡A₂[σ₂⇑])
                                                                          t₁′~t₂′
                                                                          (PE.subst (_⊢_≅_∷_ _ _ _) (singleSubstLift A₁ _) $
                                                                           escape-⊩≡∷ (R.⊩≡∷→ $ u₁≡u₂ σ₁≡σ₂))
                                                                          ok no-η) ⟩⊩∷∷⇐*
                                                                    ⟨ ≅-eq $ escape-⊩≡ $ R.⊩≡→ $
                                                                      ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ A₁≡A₂ σ₁≡σ₂ $ R.→⊩≡∷ $
                                                                      neutral-⊩≡∷ inc (R.⊩→ $ ⊩ᵛ→⊩ˢ∷→⊩[] ⊩Unit ⊩σ₁)
                                                                        t₁′-ne t₂′-ne t₁′~t₂′ ⟩⇒
               ∷ A₂ [ σ₂ ⇑ ] [ t₂′ ]₀                              ˘⟨ ⊢A₂[t₂]₀[σ₂]≡A₂[σ₂⇑][t₂′]₀ ⟩⇒

             unitrec p q (A₂ [ σ₂ ⇑ ]) t₂′ (u₂ [ σ₂ ])
               ∷ A₂ [ t₂ ]₀ [ σ₂ ]                                ⇐*⟨ unitrec⇒*₂ ⟩∎∷

             unitrec p q (A₂ [ σ₂ ⇑ ]) (t₂ [ σ₂ ]) (u₂ [ σ₂ ]) ∎) }

opaque

  -- Validity of equality between applications of unitrec.

  unitrec-congᵛ :
    Γ ∙ Unitʷ ⊢ A₁ ≡ A₂ →
    Γ ∙ Unitʷ ⊩ᵛ⟨ l′ ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l″ ⟩ t₁ ≡ t₂ ∷ Unitʷ →
    Γ ⊩ᵛ⟨ l‴ ⟩ u₁ ≡ u₂ ∷ A₁ [ starʷ ]₀ →
    Γ ⊩ᵛ⟨ l′ ⟩ unitrec p q A₁ t₁ u₁ ≡ unitrec p q A₂ t₂ u₂ ∷
      A₁ [ t₁ ]₀
  unitrec-congᵛ ⊢A₁≡A₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ (wf-⊩ᵛ≡ A₁≡A₂ .proj₁) (wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁)
      , ⊩unitrec≡unitrec ⊢A₁≡A₂ A₁≡A₂ t₁≡t₂ u₁≡u₂
      )

opaque

  -- Validity of unitrec.

  unitrecᵛ :
    Γ ∙ Unitʷ ⊢ A →
    Γ ∙ Unitʷ ⊩ᵛ⟨ l′ ⟩ A →
    Γ ⊩ᵛ⟨ l″ ⟩ t ∷ Unitʷ →
    Γ ⊩ᵛ⟨ l‴ ⟩ u ∷ A [ starʷ ]₀ →
    Γ ⊩ᵛ⟨ l′ ⟩ unitrec p q A t u ∷ A [ t ]₀
  unitrecᵛ ⊢A ⊩A ⊩t ⊩u =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    unitrec-congᵛ (refl ⊢A) (refl-⊩ᵛ≡ ⊩A) (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ᵛ≡∷ ⊩u)

opaque

  -- Validity of the unitrec β rule.

  unitrec-βᵛ :
    Γ ∙ Unitʷ ⊢ A →
    Γ ∙ Unitʷ ⊩ᵛ⟨ l″ ⟩ A →
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ A [ starʷ ]₀ →
    ¬ Unitʷ-η →
    Γ ⊩ᵛ⟨ l′ ⟩ unitrec p q A starʷ t ≡ t ∷ A [ starʷ ]₀
  unitrec-βᵛ {A} ⊢A ⊩A ⊩t no-η =
    let ⊢Unit = ⊢∙→⊢ (wf ⊢A) in
    ⊩ᵛ∷-⇐
      (λ ⊩σ →
         PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift A _) $
         unitrec-β
           (subst-⊢ ⊢A (⊢ˢʷ∷-⇑′ ⊢Unit (escape-⊩ˢ∷ ⊩σ .proj₂)))
           (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
            R.escape-⊩∷ (⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t ⊩σ))
           (inversion-Unit ⊢Unit) no-η)
      ⊩t

opaque

  -- Validity of the rule called unitrec-β-η.

  unitrec-β-ηᵛ :
    Γ ∙ Unitʷ ⊢ A →
    Γ ∙ Unitʷ ⊩ᵛ⟨ l′ ⟩ A →
    Γ ⊩ᵛ⟨ l″ ⟩ t ∷ Unitʷ →
    Γ ⊩ᵛ⟨ l‴ ⟩ u ∷ A [ starʷ ]₀ →
    Unitʷ-η →
    Γ ⊩ᵛ⟨ l′ ⟩ unitrec p q A t u ≡ u ∷ A [ t ]₀
  unitrec-β-ηᵛ {A} ⊢A ⊩A ⊩t ⊩u η =
    let ⊢Unit = ⊢∙→⊢ (wf ⊢A)
        ok    = inversion-Unit ⊢Unit
    in
    ⊩ᵛ∷-⇐
      (λ ⊩σ →
         PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift A _) $
         unitrec-β-η
           (subst-⊢ ⊢A (⊢ˢʷ∷-⇑′ ⊢Unit (escape-⊩ˢ∷ ⊩σ .proj₂)))
           (R.escape-⊩∷ (⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t ⊩σ))
           (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
            R.escape-⊩∷ (⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u ⊩σ))
           ok η)
      (conv-⊩ᵛ∷
         (⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀ (refl-⊩ᵛ≡ ⊩A) $
          η-unitᵛ (starᵛ (wf-⊩ᵛ (wf-⊩ᵛ∷ ⊩t)) ok) ⊩t (inj₂ η))
         ⊩u)
