------------------------------------------------------------------------
-- Validity of the unit type.
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
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Reduction.Primitive R
open import Definition.Typed.RedSteps R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Introductions.Universe R
open import Definition.LogicalRelation.Irrelevance R

open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ Δ : Con Term n
    σ σ₁ σ₂ : Subst _ _
    s : Strength
    l l′ l″ : TypeLevel
    A A₁ A₂ t t₁ t₂ u u₁ u₂ : Term n
    p q : M

------------------------------------------------------------------------
-- Characterisation lemmas

opaque

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩Unit⇔ :
    Γ ⊩⟨ l ⟩ Unit s ⇔
    (⊢ Γ × Unit-allowed s)
  ⊩Unit⇔ =
      (λ ⊩Unit → lemma (Unit-elim ⊩Unit))
    , (λ (⊢Γ , ok) →
         Unitᵣ $
         Unitₜ (idRed:*: (Unitⱼ ⊢Γ ok)) ok)
    where
    lemma :
      Γ ⊩⟨ l ⟩Unit⟨ s ⟩ Unit s →
      ⊢ Γ × Unit-allowed s
    lemma (emb 0<1 ⊩Unit)               = lemma ⊩Unit
    lemma (noemb (Unitₜ Unit⇒*Unit ok)) = wf (⊢A-red Unit⇒*Unit) , ok

opaque
  unfolding _⊩⟨_⟩_∷_ ⊩Unit⇔

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷Unit⇔ :
    Γ ⊩⟨ l ⟩ t ∷ Unit s ⇔
    (Unit-allowed s ×
     Γ ⊩Unit⟨ s ⟩ t ∷Unit)
  ⊩∷Unit⇔ =
      (λ (⊩Unit , ⊩t) →
         lemma (Unit-elim ⊩Unit)
           (irrelevanceTerm ⊩Unit (Unit-intr (Unit-elim ⊩Unit)) ⊩t))
    , (λ (ok , ⊩t@(Unitₜ _ t⇒*u _ _)) →
         ⊩Unit⇔ .proj₂ (wfTerm (⊢t-redₜ t⇒*u) , ok) , ⊩t)
    where
    lemma :
      (⊩Unit : Γ ⊩⟨ l ⟩Unit⟨ s ⟩ Unit s) →
      Γ ⊩⟨ l ⟩ t ∷ Unit s / Unit-intr ⊩Unit →
      Unit-allowed s ×
      Γ ⊩Unit⟨ s ⟩ t ∷Unit
    lemma (emb 0<1 ⊩Unit)      ⊩t = lemma ⊩Unit ⊩t
    lemma (noemb (Unitₜ _ ok)) ⊩t = ok , ⊩t

opaque
  unfolding _⊩⟨_⟩_≡_∷_ ⊩Unit⇔

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷Unit⇔ :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ Unit s ⇔
    (Unit-allowed s ×
     Γ ⊩Unit⟨ s ⟩ t ∷Unit ×
     Γ ⊩Unit⟨ s ⟩ u ∷Unit ×
     Γ ⊩Unit⟨ s ⟩ t ≡ u ∷Unit)
  ⊩≡∷Unit⇔ {s} =
      (λ (⊩Unit , ⊩t , ⊩u , t≡u) →
         lemma (Unit-elim ⊩Unit)
           (irrelevanceTerm ⊩Unit (Unit-intr (Unit-elim ⊩Unit)) ⊩t)
           (irrelevanceTerm ⊩Unit (Unit-intr (Unit-elim ⊩Unit)) ⊩u)
           (irrelevanceEqTerm ⊩Unit (Unit-intr (Unit-elim ⊩Unit)) t≡u))
    , (λ (ok , ⊩t , ⊩u , t≡u) →
         case (case PE.singleton s of λ where
                 (𝕤 , PE.refl) → wfTerm (_⊩Unitˢ_≡_∷Unit.⊢t t≡u)
                 (𝕨 , PE.refl) →
                   wfTerm (⊢t-redₜ (_⊩Unitʷ_≡_∷Unit.d t≡u))) of λ
           ⊢Γ →
         ⊩Unit⇔ .proj₂ (⊢Γ , ok) , ⊩t , ⊩u , t≡u)
    where
    lemma :
      (⊩Unit : Γ ⊩⟨ l ⟩Unit⟨ s ⟩ Unit s) →
      Γ ⊩⟨ l ⟩ t ∷ Unit s / Unit-intr ⊩Unit →
      Γ ⊩⟨ l ⟩ u ∷ Unit s / Unit-intr ⊩Unit →
      Γ ⊩⟨ l ⟩ t ≡ u ∷ Unit s / Unit-intr ⊩Unit →
      Unit-allowed s ×
      Γ ⊩Unit⟨ s ⟩ t ∷Unit ×
      Γ ⊩Unit⟨ s ⟩ u ∷Unit ×
      Γ ⊩Unit⟨ s ⟩ t ≡ u ∷Unit
    lemma (emb 0<1 ⊩Unit)      ⊩t ⊩u t≡u = lemma ⊩Unit ⊩t ⊩u t≡u
    lemma (noemb (Unitₜ _ ok)) ⊩t ⊩u t≡u = ok , ⊩t , ⊩u , t≡u

------------------------------------------------------------------------
-- Unit

opaque

  -- If the type Unit s is valid, then it is allowed.

  ⊩ᵛUnit→Unit-allowed :
    Γ ⊩ᵛ⟨ l ⟩ Unit s →
    Unit-allowed s
  ⊩ᵛUnit→Unit-allowed {Γ} {l} {s} =
    Γ ⊩ᵛ⟨ l ⟩ Unit s      →⟨ ⊩ᵛ→⊩ ⟩
    Γ ⊩⟨ l ⟩ Unit s       ⇔⟨ ⊩Unit⇔ ⟩→
    ⊢ Γ × Unit-allowed s  →⟨ proj₂ ⟩
    Unit-allowed s        □

opaque

  -- Reducibility for Unit.

  ⊩Unit :
    ⊢ Γ →
    Unit-allowed s →
    Γ ⊩⟨ l ⟩ Unit s
  ⊩Unit ⊢Γ ok = ⊩Unit⇔ .proj₂ (⊢Γ , ok)

opaque

  -- Validity for Unit, seen as a type former.

  Unitᵛ :
    ⊩ᵛ Γ →
    Unit-allowed s →
    Γ ⊩ᵛ⟨ l ⟩ Unit s
  Unitᵛ ⊩Γ ok =
    ⊩ᵛ⇔ .proj₂
      ( ⊩Γ
      , λ ⊩σ →
          case ⊩Unit (escape-⊩ˢ∷ ⊩σ .proj₁) ok of λ
            ⊩Unit →
          ⊩Unit , λ {σ′ = _} _ → refl-⊩≡ ⊩Unit
      )

opaque

  -- Validity for Unit, seen as a term former.

  Unitᵗᵛ :
    ⊩ᵛ Γ →
    Unit-allowed s →
    Γ ⊩ᵛ⟨ ¹ ⟩ Unit s ∷ U
  Unitᵗᵛ ⊩Γ ok =
    ⊩ᵛ∷⇔ .proj₂
      ( ⊩ᵛU ⊩Γ
      , λ ⊩σ →
          case escape-⊩ˢ∷ ⊩σ .proj₁ of λ
            ⊢Δ →
          case ⊩Unit ⊢Δ ok of λ
            ⊩Unit →
          case Unitⱼ ⊢Δ ok of λ
            ⊢Unit →
          case ≅ₜ-Unitrefl ⊢Δ ok of λ
            Unit≅Unit →
            Type→⊩∷U⇔ Unitₙ .proj₂
              ( (_ , 0<1 , ⊩Unit)
              , (⊢Unit , Unit≅Unit)
              )
          , λ _ →
              Type→⊩≡∷U⇔ Unitₙ Unitₙ .proj₂
                ( ⊢Unit , ⊢Unit , Unit≅Unit
                , (_ , 0<1 , refl-⊩≡ ⊩Unit)
                )
      )

------------------------------------------------------------------------
-- The constructor star

opaque

  -- Reducibility for star.

  ⊩star :
    ⊢ Γ →
    Unit-allowed s →
    Γ ⊩⟨ l ⟩ star s ∷ Unit s
  ⊩star ⊢Γ ok =
    ⊩∷Unit⇔ .proj₂
      ( ok
      , Unitₜ _ (idRedTerm:*: (starⱼ ⊢Γ ok)) (≅ₜ-starrefl ⊢Γ ok) starᵣ
      )

opaque

  -- Validity of star.

  starᵛ :
    ⊩ᵛ Γ →
    Unit-allowed s →
    Γ ⊩ᵛ⟨ l ⟩ star s ∷ Unit s
  starᵛ ⊩Γ ok =
    ⊩ᵛ∷⇔ .proj₂
      ( Unitᵛ ⊩Γ ok
      , λ ⊩σ →
          case ⊩star (escape-⊩ˢ∷ ⊩σ .proj₁) ok of λ
            ⊩star →
          ⊩star , λ {σ′ = _} _ → refl-⊩≡∷ ⊩star
      )

------------------------------------------------------------------------
-- The typing rule η-unit

opaque

  -- Validity of η-unit.

  η-unitᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ Unitˢ →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ Unitˢ →
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ Unitˢ
  η-unitᵛ ⊩t ⊩u =
    ⊩ᵛ≡∷⇔ .proj₂
      ( ⊩t
      , level-⊩ᵛ∷ (wf-⊩ᵛ∷ ⊩t) ⊩u
      , λ ⊩σ →
          case ⊩∷Unit⇔ .proj₁ (⊩ᵛ∷⇔′ .proj₁ ⊩t .proj₂ .proj₁ ⊩σ) of λ
            (ok , ⊩t@(Unitₜ _ t⇒*t′ _ _)) →
          case ⊩∷Unit⇔ .proj₁ (⊩ᵛ∷⇔′ .proj₁ ⊩u .proj₂ .proj₁ ⊩σ) of λ
            (_ , ⊩u@(Unitₜ _ u⇒*u′ _ _)) →
          ⊩≡∷Unit⇔ .proj₂
            (ok , ⊩t , ⊩u , Unitₜ₌ (⊢t-redₜ t⇒*t′) (⊢t-redₜ u⇒*u′))
      )

------------------------------------------------------------------------
-- The eliminator unitrec

private opaque

  -- A variant of unitrec-subst for _⊢_⇒*_∷_.

  unitrec-subst* :
    Γ ∙ Unitʷ ⊩ᵛ⟨ l ⟩ A →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ t₁ ∷ Unitʷ →
    Δ ⊢ t₁ ⇒* t₂ ∷ Unitʷ →
    Δ ⊢ u ∷ A [ σ ⇑ ] [ starʷ ]₀ →
    Δ ⊢ unitrec p q (A [ σ ⇑ ]) t₁ u ⇒* unitrec p q (A [ σ ⇑ ]) t₂ u ∷
      A [ σ ⇑ ] [ t₁ ]₀
  unitrec-subst* {l} {A} ⊩A ⊩σ ⊩t₁ t₁⇒*t₂ ⊢u =
    case ⊩ᵛUnit→Unit-allowed $ wf-∙-⊩ᵛ ⊩A .proj₂ of λ
      ok →
    case escape $ ⊩ᵛ→⊩ˢ∷→⊩[⇑] ⊩A ⊩σ of λ
      ⊢A[σ⇑] →
    case t₁⇒*t₂ of λ where
      (id ⊢t₁)         → id (unitrecⱼ ⊢A[σ⇑] ⊢t₁ ⊢u ok)
      (t₁⇒t₃ ⇨ t₃⇒*t₂) →
        case redFirst*Term t₃⇒*t₂ of λ
          ⊢t₃ →
        case ⊩∷-⇒* [ redFirstTerm t₁⇒t₃ , ⊢t₃ , t₁⇒t₃ ⇨ id ⊢t₃ ]
               ⊩t₁ of λ
          (⊩t₃ , t₁≡t₃) →
        unitrec-subst ⊢A[σ⇑] ⊢u t₁⇒t₃ ok ⇨
        conv* (unitrec-subst* ⊩A ⊩σ ⊩t₃ t₃⇒*t₂ ⊢u)
          (≅-eq $ escape-⊩≡ $
           ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩A) (refl-⊩ˢ≡∷ ⊩σ)
             (sym-⊩≡∷ t₁≡t₃))

opaque

  -- Reducibility of equality between applications of unitrec.

  ⊩unitrec≡unitrec :
    Γ ∙ Unitʷ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l′ ⟩ t₁ ≡ t₂ ∷ Unitʷ →
    Γ ⊩ᵛ⟨ l″ ⟩ u₁ ≡ u₂ ∷ A₁ [ starʷ ]₀ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l ⟩ unitrec p q A₁ t₁ u₁ [ σ₁ ] ≡ unitrec p q A₂ t₂ u₂ [ σ₂ ] ∷
      A₁ [ t₁ ]₀ [ σ₁ ]
  ⊩unitrec≡unitrec
    {l} {A₁} {A₂} {t₁} {t₂} {u₁} {u₂} {σ₁} {σ₂} {p} {q}
    A₁≡A₂ t₁≡t₂ u₁≡u₂ σ₁≡σ₂ =
    case wf-⊩ᵛ≡ A₁≡A₂ of λ
      (⊩A₁ , ⊩A₂) →
    case ⊩ᵛ≡∷⇔′ .proj₁ t₁≡t₂ of λ
      (⊩t₁ , ⊩t₂ , t₁≡t₂) →
    case ⊩ᵛ≡∷⇔′ .proj₁ u₁≡u₂ of λ
      (⊩u₁ , ⊩u₂ , u₁≡u₂) →
    case wf-⊩ˢ≡∷ σ₁≡σ₂ of λ
      (⊩σ₁ , ⊩σ₂) →
    case ⊩ᵛ∷⇔′ .proj₁ ⊩t₁ .proj₁ of λ
      ⊩Unit →
    case ⊩ᵛ∷⇔′ .proj₁ ⊩t₁ .proj₂ .proj₁ ⊩σ₁ of λ
      ⊩t₁[σ₁] →
    case ⊩ᵛ∷⇔′ .proj₁ ⊩t₂ .proj₂ .proj₁ ⊩σ₂ of λ
      ⊩t₂[σ₂] →
    case ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑]≡[⇑] A₁≡A₂ σ₁≡σ₂ of λ
      A₁[σ₁⇑]≡A₂[σ₂⇑] →
    case Σ.map escape escape (wf-⊩≡ A₁[σ₁⇑]≡A₂[σ₂⇑]) of λ
      (⊢A₁[σ₁⇑] , ⊢A₂[σ₂⇑]) →
    case refl-⊩≡∷ $
         ⊩star {l = l} (escape-⊩ˢ∷ ⊩σ₁ .proj₁) $
         ⊩ᵛUnit→Unit-allowed ⊩Unit of λ
      ⋆≡⋆ →
    case escape-⊩∷ $
         PE.subst (_⊩⟨_⟩_∷_ _ _ _) (singleSubstLift A₁ starʷ) $
         ⊩ᵛ∷⇔′ .proj₁ ⊩u₁ .proj₂ .proj₁ ⊩σ₁ of λ
      ⊢u₁[σ₁] →
    case escape-⊩∷ $
         conv-⊩∷
           (⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ A₁≡A₂ (refl-⊩ˢ≡∷ ⊩σ₂) ⋆≡⋆) $
         PE.subst (_⊩⟨_⟩_∷_ _ _ _) (singleSubstLift A₁ starʷ) $
         ⊩ᵛ∷⇔′ .proj₁ ⊩u₂ .proj₂ .proj₁ ⊩σ₂ of λ
      ⊢u₂[σ₂] →
    case ⊩≡∷Unit⇔ .proj₁ (t₁≡t₂ σ₁≡σ₂) of λ
      (ok , _ , _ ,
       Unitₜ₌ t₁′ t₂′ t₁[σ₁]⇒*t₁′@([ _ , ⊢t₁′ , _ ])
         t₂[σ₂]⇒*t₂′@([ _ , ⊢t₂′ , _ ]) _ rest) →
    case PE.subst (_⊢_⇒*_∷_ _ _ _) (PE.sym $ singleSubstLift A₁ t₁) $
         unitrec-subst* ⊩A₁ ⊩σ₁ ⊩t₁[σ₁] (redₜ t₁[σ₁]⇒*t₁′)
           ⊢u₁[σ₁] of λ
      unitrec⇒*₁ →
    case PE.subst (_⊢_⇒*_∷_ _ _ _) (PE.sym $ singleSubstLift A₂ t₂) $
         unitrec-subst* ⊩A₂ ⊩σ₂ ⊩t₂[σ₂] (redₜ t₂[σ₂]⇒*t₂′)
           ⊢u₂[σ₂] of λ
      unitrec⇒*₂ →
    case PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
           (PE.sym $ singleSubstLift A₁ t₁) PE.refl $
         ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩A₁) (refl-⊩ˢ≡∷ ⊩σ₁)
           (⊩∷-⇒* t₁[σ₁]⇒*t₁′ ⊩t₁[σ₁] .proj₂) of λ
      A₁[t₁]₀[σ₁]≡A₁[σ₁⇑][t₁′]₀ →
    case ≅-eq $ escape-⊩≡ $
         PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
           (PE.sym $ singleSubstLift A₂ t₂) PE.refl $
         ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩A₂) (refl-⊩ˢ≡∷ ⊩σ₂)
           (⊩∷-⇒* t₂[σ₂]⇒*t₂′ ⊩t₂[σ₂] .proj₂) of λ
      ⊢A₂[t₂]₀[σ₂]≡A₂[σ₂⇑][t₂′]₀ →
    case rest of λ where
      starᵣ →
        unitrec p q A₁ t₁    u₁ [ σ₁ ] ∷ A₁ [ t₁ ]₀ [ σ₁ ]       ⇒*⟨ unitrec⇒*₁ ⟩⊩∷∷
                                                                   ⟨ A₁[t₁]₀[σ₁]≡A₁[σ₁⇑][t₁′]₀ ⟩⊩∷
        unitrec p q A₁ starʷ u₁ [ σ₁ ] ∷ A₁ [ σ₁ ⇑ ] [ starʷ ]₀  ⇒⟨ unitrec-β ⊢A₁[σ₁⇑] ⊢u₁[σ₁] ok ⟩⊩∷∷
                                                                 ˘⟨ singleSubstLift A₁ starʷ ⟩⊩∷≡
        u₁ [ σ₁ ]                      ∷ A₁ [ starʷ ]₀ [ σ₁ ]    ≡⟨ u₁≡u₂ σ₁≡σ₂ ⟩⊩∷∷⇐*
                                                                  ⟨ PE.subst₂ (_⊢_≡_ _) (substConsId A₁) (substConsId A₂) $
                                                                    ≅-eq $ escape-⊩≡ $
                                                                    ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,] A₁≡A₂ σ₁≡σ₂ ⋆≡⋆ ⟩⇒
                                       ∷ A₂ [ starʷ ]₀ [ σ₂ ]     ⟨ singleSubstLift A₂ starʷ ⟩⇐≡
        u₂ [ σ₂ ]                      ∷ A₂ [ σ₂ ⇑ ] [ starʷ ]₀  ⇐⟨ unitrec-β ⊢A₂[σ₂⇑] ⊢u₂[σ₂] ok , ⊢u₂[σ₂] ⟩∷
                                                                 ˘⟨ ⊢A₂[t₂]₀[σ₂]≡A₂[σ₂⇑][t₂′]₀ ⟩⇒
        unitrec p q A₂ starʷ u₂ [ σ₂ ] ∷ A₂ [ t₂ ]₀ [ σ₂ ]       ⇐*⟨ unitrec⇒*₂ ⟩∎∷
        unitrec p q A₂ t₂    u₂ [ σ₂ ]                           ∎

      (ne (neNfₜ₌ t₁′-ne t₂′-ne t₁′~t₂′)) →
        case ≅-eq $ escape-⊩≡ $
             ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ A₁≡A₂ σ₁≡σ₂ $
             neutral-⊩≡∷ (⊩ᵛ⇔′ .proj₁ ⊩Unit .proj₂ .proj₁ ⊩σ₁)
               t₁′-ne t₂′-ne ⊢t₁′ ⊢t₂′ t₁′~t₂′ of λ
          ⊢A₁[σ₁⇑][t₁′]₀≡A₂[σ₂⇑][t₂′]₀ →
        unitrec p q (A₁ [ σ₁ ⇑ ]) (t₁ [ σ₁ ]) (u₁ [ σ₁ ])
          ∷ A₁ [ t₁ ]₀ [ σ₁ ]                              ⇒*⟨ unitrec⇒*₁ ⟩⊩∷∷
                                                             ⟨ A₁[t₁]₀[σ₁]≡A₁[σ₁⇑][t₁′]₀ ⟩⊩∷
        unitrec p q (A₁ [ σ₁ ⇑ ]) t₁′         (u₁ [ σ₁ ])
          ∷ A₁ [ σ₁ ⇑ ] [ t₁′ ]₀                           ≡⟨ neutral-⊩≡∷ (wf-⊩≡ A₁[t₁]₀[σ₁]≡A₁[σ₁⇑][t₁′]₀ .proj₂)
                                                                (unitrecₙ t₁′-ne) (unitrecₙ t₂′-ne)
                                                                (unitrecⱼ ⊢A₁[σ₁⇑] ⊢t₁′ ⊢u₁[σ₁] ok)
                                                                (conv (unitrecⱼ ⊢A₂[σ₂⇑] ⊢t₂′ ⊢u₂[σ₂] ok)
                                                                   (sym ⊢A₁[σ₁⇑][t₁′]₀≡A₂[σ₂⇑][t₂′]₀))
                                                                (~-unitrec (escape-⊩≡ A₁[σ₁⇑]≡A₂[σ₂⇑]) t₁′~t₂′
                                                                   (PE.subst (_⊢_≅_∷_ _ _ _) (singleSubstLift A₁ _) $
                                                                    escape-⊩≡∷ (u₁≡u₂ σ₁≡σ₂))
                                                                   ok) ⟩⊩∷∷⇐*
                                                             ⟨ ⊢A₁[σ₁⇑][t₁′]₀≡A₂[σ₂⇑][t₂′]₀ ⟩⇒
          ∷ A₂ [ σ₂ ⇑ ] [ t₂′ ]₀                            ˘⟨ ⊢A₂[t₂]₀[σ₂]≡A₂[σ₂⇑][t₂′]₀ ⟩⇒

        unitrec p q (A₂ [ σ₂ ⇑ ]) t₂′         (u₂ [ σ₂ ])
          ∷ A₂ [ t₂ ]₀ [ σ₂ ]                              ⇐*⟨ unitrec⇒*₂ ⟩∎∷

        unitrec p q (A₂ [ σ₂ ⇑ ]) (t₂ [ σ₂ ]) (u₂ [ σ₂ ])  ∎

opaque

  -- Reducibility for unitrec.

  ⊩unitrec :
    Γ ∙ Unitʷ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ Unitʷ →
    Γ ⊩ᵛ⟨ l″ ⟩ u ∷ A [ starʷ ]₀ →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l ⟩ unitrec p q A t u [ σ ] ∷ A [ t ]₀ [ σ ]
  ⊩unitrec ⊩A ⊩t ⊩u ⊩σ =
    wf-⊩≡∷
      (⊩unitrec≡unitrec (refl-⊩ᵛ≡ ⊩A) (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ᵛ≡∷ ⊩u)
         (refl-⊩ˢ≡∷ ⊩σ))
      .proj₁

opaque

  -- Validity of unitrec.

  unitrecᵛ :
    Γ ∙ Unitʷ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ Unitʷ →
    Γ ⊩ᵛ⟨ l″ ⟩ u ∷ A [ starʷ ]₀ →
    Γ ⊩ᵛ⟨ l ⟩ unitrec p q A t u ∷ A [ t ]₀
  unitrecᵛ ⊩A ⊩t ⊩u =
    ⊩ᵛ∷⇔′ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ ⊩A ⊩t
      , ⊩unitrec ⊩A ⊩t ⊩u
      , ⊩unitrec≡unitrec (refl-⊩ᵛ≡ ⊩A) (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ᵛ≡∷ ⊩u)
      )

opaque

  -- Validity of equality between applications of unitrec.

  unitrec-congᵛ :
    Γ ∙ Unitʷ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l′ ⟩ t₁ ≡ t₂ ∷ Unitʷ →
    Γ ⊩ᵛ⟨ l″ ⟩ u₁ ≡ u₂ ∷ A₁ [ starʷ ]₀ →
    Γ ⊩ᵛ⟨ l ⟩ unitrec p q A₁ t₁ u₁ ≡ unitrec p q A₂ t₂ u₂ ∷ A₁ [ t₁ ]₀
  unitrec-congᵛ A₁≡A₂ t₁≡t₂ u₁≡u₂ =
    case wf-⊩ᵛ≡ A₁≡A₂ of λ
      (⊩A₁ , ⊩A₂) →
    case wf-⊩ᵛ≡∷ t₁≡t₂ of λ
      (⊩t₁ , ⊩t₂) →
    case wf-⊩ᵛ≡∷ u₁≡u₂ of λ
      (⊩u₁ , ⊩u₂) →
    case wf-∙-⊩ᵛ ⊩A₁ of λ
      (_ , ⊩Unit) →
    ⊩ᵛ≡∷⇔′ .proj₂
      ( unitrecᵛ ⊩A₁ ⊩t₁ ⊩u₁
      , conv-⊩ᵛ∷ (sym-⊩ᵛ≡ $ ⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀ A₁≡A₂ t₁≡t₂)
          (unitrecᵛ ⊩A₂ ⊩t₂
             (conv-⊩ᵛ∷
                (⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀ A₁≡A₂ $ refl-⊩ᵛ≡∷ $
                 starᵛ {l = ⁰} (wf-⊩ᵛ ⊩Unit)
                   (⊩ᵛUnit→Unit-allowed ⊩Unit))
              ⊩u₂))
      , ⊩unitrec≡unitrec A₁≡A₂ t₁≡t₂ u₁≡u₂
      )

opaque

  -- Validity of the unitrec β rule.

  unitrec-βᵛ :
    Γ ∙ Unitʷ ⊩ᵛ⟨ l′ ⟩ A →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A [ starʷ ]₀ →
    Γ ⊩ᵛ⟨ l ⟩ unitrec p q A starʷ t ≡ t ∷ A [ starʷ ]₀
  unitrec-βᵛ {A} ⊩A ⊩t =
    ⊩ᵛ∷-⇐
      (λ ⊩σ →
         PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift A _) $
         unitrec-β
           (escape $ ⊩ᵛ→⊩ˢ∷→⊩[⇑] ⊩A ⊩σ)
           (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
            escape-⊩∷ (⊩ᵛ∷⇔′ .proj₁ ⊩t .proj₂ .proj₁ ⊩σ))
           (⊩ᵛUnit→Unit-allowed (wf-∙-⊩ᵛ ⊩A .proj₂)))
      ⊩t
      .proj₂
