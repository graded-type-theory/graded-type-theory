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
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Reduction R
open import Definition.Typed.Substitution.Primitive R
open import Definition.Typed.Weakening.Definition R
open import Definition.Typed.Well-formed R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
import Definition.LogicalRelation.Hidden.Restricted R as R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Introductions.Universe R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Unary R

open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum

private
  variable
    m n : Nat
    ∇ : DCon (Term 0) m
    Δ Η : Con Term n
    Γ : Cons m n
    σ σ₁ σ₂ : Subst _ _
    s s₁ s₂ : Strength
    l l′ l″ l‴ l₁ l₂ : Universe-level
    A A₁ A₂ t t₁ t₂ u u₁ u₂ : Term n
    p q : M

------------------------------------------------------------------------
-- Characterisation lemmas

opaque
  unfolding emb-⊩

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩Unit⇔ :
    Γ ⊩⟨ l′ ⟩ Unit s l ⇔
    (l ≤ᵘ l′ × ⊢ Γ × Unit-allowed s)
  ⊩Unit⇔ =
      (λ ⊩Unit →
        case Unit-view ⊩Unit of λ {
          (Unitᵣ (Unitᵣ l l≤ Unit⇒*Unit ok)) →
      case Unit-PE-injectivity $
           whnfRed* Unit⇒*Unit Unitₙ of λ {
        (_ , PE.refl) →
      l≤ , wfEq (subset* Unit⇒*Unit) , ok }})
    , (λ (l≤l′ , ⊢Γ , ok) →
         Unitᵣ′ _ l≤l′ (id (Unitⱼ ⊢Γ ok)) ok)

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩Unit≡⇔ :
    Γ ⊩⟨ l′ ⟩ Unit s l ≡ A ⇔
    (l ≤ᵘ l′ × ⊢ Γ × Unit-allowed s × Γ ⊩Unit⟨ l , s ⟩ Unit s l ≡ A)
  ⊩Unit≡⇔ {s} {l} {A} =
      (λ (⊩Unit , _ , A⇒*Unit) →
         case Unit-view ⊩Unit of λ {
           (Unitᵣ (Unitᵣ l l≤ Unit⇒*Unit ok)) →
         case wfEq (subset* Unit⇒*Unit) of λ
           ⊢Γ →
         case Unit-PE-injectivity $
              whnfRed* Unit⇒*Unit Unitₙ of λ {
           (_ , PE.refl) →
         l≤ , ⊢Γ , ok , A⇒*Unit }})
    , (λ (l≤l′ , ⊢Γ , ok , A⇒*Unit) →
         sym-⊩≡
           (A         ⇒*⟨ A⇒*Unit ⟩⊩
            Unit s l  ∎⟨ ⊩Unit⇔ .proj₂ (l≤l′ , ⊢Γ , ok) ⟩⊩))

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩Unit≡Unit⇔ :
    Γ ⊩⟨ l ⟩ Unit s₁ l₁ ≡ Unit s₂ l₂ ⇔
    (l₁ ≤ᵘ l × ⊢ Γ × Unit-allowed s₁ × s₁ PE.≡ s₂ × l₁ PE.≡ l₂)
  ⊩Unit≡Unit⇔ {Γ} {l} {s₁} {l₁} {s₂} {l₂} =
    Γ ⊩⟨ l ⟩ Unit s₁ l₁ ≡ Unit s₂ l₂                                ⇔⟨ ⊩Unit≡⇔ ⟩
    l₁ ≤ᵘ l × ⊢ Γ × Unit-allowed s₁ × Γ ⊢ Unit s₂ l₂ ⇒* Unit s₁ l₁  ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ ⊢Γ → Σ-cong-⇔ λ ok →
                                                                          Σ.map PE.sym PE.sym ∘→ Unit-PE-injectivity ∘→ flip whnfRed* Unitₙ
                                                                        , (λ { (PE.refl , PE.refl) → id (Unitⱼ ⊢Γ ok) }))
                                                                     ⟩
    l₁ ≤ᵘ l × ⊢ Γ × Unit-allowed s₁ × s₁ PE.≡ s₂ × l₁ PE.≡ l₂       □⇔

opaque
  unfolding _⊩⟨_⟩_≡_∷_ ⊩Unit⇔

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷Unit⇔ :
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ Unit s l ⇔
    (l ≤ᵘ l′ × Unit-allowed s × Γ ⊩Unit⟨ l , s ⟩ t ≡ u ∷Unit)
  ⊩≡∷Unit⇔ {s} =
      (λ (⊩Unit , t≡u) →
         case Unit-view ⊩Unit of λ {
            (Unitᵣ (Unitᵣ l l≤ Unit⇒*Unit ok)) →
         case Unit-PE-injectivity $
              whnfRed* Unit⇒*Unit Unitₙ of λ {
           (_ , PE.refl) →
         l≤ , ok , t≡u }})
    , (λ (l≤l′ , ok , t≡u) →
         let Unitₜ₌ _ _ (t⇒ , _) _ _ = t≡u
             ⊢Γ                      = wfTerm (redFirst*Term t⇒)
         in
         emb-⊩≡∷ l≤l′ $ ⊩Unit⇔ .proj₂ (≤ᵘ-refl , ⊢Γ , ok) , t≡u)

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷Unit⇔ :
    Γ ⊩⟨ l′ ⟩ t ∷ Unit s l ⇔
    (l ≤ᵘ l′ × Unit-allowed s × Γ ⊩Unit⟨ l , s ⟩ t ∷Unit)
  ⊩∷Unit⇔ {Γ} {l′} {t} {s} {l} =
    Γ ⊩⟨ l′ ⟩ t ∷ Unit s l                                   ⇔⟨ ⊩∷⇔⊩≡∷ ⟩
    Γ ⊩⟨ l′ ⟩ t ≡ t ∷ Unit s l                               ⇔⟨ ⊩≡∷Unit⇔ ⟩
    l ≤ᵘ l′ × Unit-allowed s × Γ ⊩Unit⟨ l , s ⟩ t ≡ t ∷Unit  ⇔˘⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → ⊩Unit∷Unit⇔⊩Unit≡∷Unit) ⟩
    l ≤ᵘ l′ × Unit-allowed s × Γ ⊩Unit⟨ l , s ⟩ t ∷Unit      □⇔

------------------------------------------------------------------------
-- Unit

opaque

  -- If the type Unit s l is valid, then it is allowed (given a
  -- certain assumption).

  ⊩ᵛUnit→Unit-allowed :
    ⦃ inc : Var-included or-empty (Γ .vars) ⦄ →
    Γ ⊩ᵛ⟨ l′ ⟩ Unit s l →
    Unit-allowed s
  ⊩ᵛUnit→Unit-allowed {Γ} {l′} {s} {l} =
    Γ ⊩ᵛ⟨ l′ ⟩ Unit s l             →⟨ R.⊩→ ∘→ ⊩ᵛ→⊩ ⟩
    Γ ⊩⟨ l′ ⟩ Unit s l              ⇔⟨ ⊩Unit⇔ ⟩→
    l ≤ᵘ l′ × ⊢ Γ × Unit-allowed s  →⟨ proj₂ ∘→ proj₂ ⟩
    Unit-allowed s                  □

opaque

  -- Reducibility for Unit.

  ⊩Unit :
    ⊢ Γ →
    Unit-allowed s →
    Γ ⊩⟨ l ⟩ Unit s l
  ⊩Unit ⊢Γ ok = ⊩Unit⇔ .proj₂ (≤ᵘ-refl , ⊢Γ , ok)

opaque

  -- Validity for Unit, seen as a type former.

  Unitᵛ :
    ⊩ᵛ Γ →
    Unit-allowed s →
    Γ ⊩ᵛ⟨ l ⟩ Unit s l
  Unitᵛ {Γ} {s} {l} ⊩Γ ok =
    ⊩ᵛ⇔ʰ .proj₂
      ( ⊩Γ
      , λ {_} {∇} ξ⊇ {_} {Δ} {σ₁} {σ₂} →
          ∇ » Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ .vars        →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ∇ »⊢ Δ                            →⟨ flip ⊩Unit ok ⟩
          (∇ » Δ ⊩⟨ l ⟩ Unit s l)           →⟨ refl-⊩≡ ⟩
          ∇ » Δ ⊩⟨ l ⟩ Unit s l ≡ Unit s l  □
      )

opaque

  -- Validity for Unit, seen as a term former.

  Unitᵗᵛ :
    ⊩ᵛ Γ →
    Unit-allowed s →
    Γ ⊩ᵛ⟨ 1+ l ⟩ Unit s l ∷ U l
  Unitᵗᵛ ⊩Γ ok =
    ⊩ᵛ∷⇔ʰ .proj₂
      ( ⊩ᵛU ⊩Γ
      , λ ξ⊇ σ₁≡σ₂ →
          case escape-⊩ˢ≡∷ σ₁≡σ₂ of λ
            (⊢Δ , _) →
          Type→⊩≡∷U⇔ Unitₙ Unitₙ .proj₂
            (≤ᵘ-refl , refl-⊩≡ (⊩Unit ⊢Δ ok) , ≅ₜ-Unitrefl ⊢Δ ok)
      )

------------------------------------------------------------------------
-- The constructor star

opaque

  -- Reducibility for star.

  ⊩star :
    ⊢ Γ →
    Unit-allowed s →
    Γ ⊩⟨ l ⟩ star s l ∷ Unit s l
  ⊩star ⊢Γ ok =
    ⊩∷Unit⇔ .proj₂
      ( ≤ᵘ-refl
      , ok
      , Unitₜ _ (id (starⱼ ⊢Γ ok) , starₙ) (Unit-prop′→Unit-prop starᵣ)
      )

opaque

  -- Validity of star.

  starᵛ :
    ⊩ᵛ Γ →
    Unit-allowed s →
    Γ ⊩ᵛ⟨ l ⟩ star s l ∷ Unit s l
  starᵛ {Γ} {s} {l} ⊩Γ ok =
    ⊩ᵛ∷⇔ʰ .proj₂
      ( Unitᵛ ⊩Γ ok
      , λ {_} {∇} ξ⊇ {_} {Δ} {σ₁} {σ₂} →
          ∇ » Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ .vars                   →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ∇ »⊢ Δ                                       →⟨ flip ⊩star ok ⟩
          ∇ » Δ ⊩⟨ l ⟩ star s l ∷ Unit s l             →⟨ refl-⊩≡∷ ⟩
          ∇ » Δ ⊩⟨ l ⟩ star s l ≡ star s l ∷ Unit s l  □
      )

------------------------------------------------------------------------
-- The typing rule η-unit

opaque

  -- Validity of η-unit.

  η-unitᵛ :
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ Unit s l →
    Γ ⊩ᵛ⟨ l″ ⟩ u ∷ Unit s l →
    Unit-with-η s →
    Γ ⊩ᵛ⟨ l′ ⟩ t ≡ u ∷ Unit s l
  η-unitᵛ ⊩t ⊩u η =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( wf-⊩ᵛ∷ ⊩t
      , λ ξ⊇ σ₁≡σ₂ →
          let ⊩t                             = defn-wk-⊩ᵛ∷ ξ⊇ ⊩t
              ⊩u                             = defn-wk-⊩ᵛ∷ ξ⊇ ⊩u
              ⊩σ₁ , ⊩σ₂                      = wf-⊩ˢ≡∷ σ₁≡σ₂
              l≤l′ , ok , Unitₜ _ t[σ₁]↘t′ _ =
                ⊩∷Unit⇔ .proj₁ $ R.⊩∷→ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t ⊩σ₁
              _ , _ , Unitₜ _ u[σ₂]↘u′ _ =
                ⊩∷Unit⇔ .proj₁ $ R.⊩∷→ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u ⊩σ₂
          in
          ⊩≡∷Unit⇔ .proj₂
            (l≤l′ , ok ,
             Unitₜ₌ _ _ t[σ₁]↘t′ u[σ₂]↘u′ (Unitₜ₌ˢ η))
      )

------------------------------------------------------------------------
-- The eliminator unitrec

opaque

  -- Reducibility of equality between applications of unitrec.

  ⊩unitrec≡unitrec :
    ∇ » Δ ∙ Unitʷ l ⊢ A₁ ≡ A₂ →
    ∇ » Δ ∙ Unitʷ l ⊩ᵛ⟨ l′ ⟩ A₁ ≡ A₂ →
    ∇ » Δ ⊩ᵛ⟨ l″ ⟩ t₁ ≡ t₂ ∷ Unitʷ l →
    ∇ » Δ ⊩ᵛ⟨ l‴ ⟩ u₁ ≡ u₂ ∷ A₁ [ starʷ l ]₀ →
    ⦃ inc : Var-included or-empty Η ⦄ →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ⊩⟨ l′ ⟩ unitrec l p q A₁ t₁ u₁ [ σ₁ ] ≡
      unitrec l p q A₂ t₂ u₂ [ σ₂ ] ∷ A₁ [ t₁ ]₀ [ σ₁ ]
  ⊩unitrec≡unitrec
    {∇} {l} {A₁} {A₂} {l′} {t₁} {t₂} {u₁} {u₂} {Η} {σ₁} {σ₂} {p} {q}
    ⊢A₁≡A₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ σ₁≡σ₂ =
    case wf-⊩ᵛ≡ A₁≡A₂ of λ
      (⊩A₁ , ⊩A₂) →
    case ⊩ᵛ≡∷⇔″ .proj₁ t₁≡t₂ of λ
      (⊩t₁ , ⊩t₂ , t₁≡t₂) →
    case ⊩ᵛ≡∷⇔″ .proj₁ u₁≡u₂ of λ
      (⊩u₁ , ⊩u₂ , u₁≡u₂) →
    case wf-⊩ˢ≡∷ σ₁≡σ₂ of λ
      (⊩σ₁ , ⊩σ₂) →
    case ⊩ᵛ∷⇔ .proj₁ ⊩t₁ .proj₁ of λ
      ⊩Unit →
    case ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t₁ ⊩σ₁ of λ
      ⊩t₁[σ₁] →
    case ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t₂ ⊩σ₂ of λ
      ⊩t₂[σ₂] →
    case ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑]≡[⇑] A₁≡A₂ σ₁≡σ₂ of λ
      A₁[σ₁⇑]≡A₂[σ₂⇑] →
    case R.escape-⊩ $ ⊩ᵛ→⊩ˢ∷→⊩[] ⊩Unit ⊩σ₁ of λ
      ⊢Unit →
    case subst-⊢≡ ⊢A₁≡A₂ $
         ⊢ˢʷ≡∷-⇑ (refl ⊢Unit) $ escape-⊩ˢ≡∷ σ₁≡σ₂ .proj₂ of λ
      ⊢A₁[σ₁⇑]≡⊢A₂[σ₂⇑] →
    case wf-⊢≡ ⊢A₁[σ₁⇑]≡⊢A₂[σ₂⇑] of λ
      (⊢A₁[σ₁⇑] , ⊢A₂[σ₂⇑]) →
    case (R.refl-⊩≡∷ $ R.→⊩∷ $
          ⊩star (escape-⊩ˢ∷ ⊩σ₁ .proj₁) $
          inversion-Unit ⊢Unit) of λ
      ⋆≡⋆ →
    case PE.subst₂ (_⊢_≡_ _) (substConsId {t = star!} A₁)
           (substConsId {t = star!} A₂) $
         ≅-eq $ R.escape-⊩≡ $
         ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,] A₁≡A₂ σ₁≡σ₂ ⋆≡⋆ of λ
      A₁[⋆]₀[σ₁]≡A₂[⋆]₀[σ₂] →
    case R.escape-⊩∷ $
         PE.subst (R._⊩⟨_⟩_∷_ _ _ _) (singleSubstLift A₁ (starʷ _)) $
         ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u₁ ⊩σ₁ of λ
      ⊢u₁[σ₁] →
    case R.escape-⊩∷ $
         R.conv-⊩∷
           (⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ A₁≡A₂ (refl-⊩ˢ≡∷ ⊩σ₂) ⋆≡⋆) $
         PE.subst (R._⊩⟨_⟩_∷_ _ _ _) (singleSubstLift A₁ (starʷ _)) $
         ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u₂ ⊩σ₂ of λ
      ⊢u₂[σ₂] →
    case ⊩≡∷Unit⇔ .proj₁ (R.⊩≡∷⇔ .proj₁ (t₁≡t₂ id σ₁≡σ₂)) of λ {
      (_ , ok ,
       Unitₜ₌ t₁′ t₂′ (t₁[σ₁]⇒*t₁′ , _) (t₂[σ₂]⇒*t₂′ , _) prop) →
    case prop of λ where
      (Unitₜ₌ˢ η)  →
        case starᵛ (wf-⊩ᵛ ⊩Unit) ok of λ
          ⊩⋆ →
        unitrec l p q A₁ t₁ u₁ [ σ₁ ] ∷ A₁ [ t₁ ]₀ [ σ₁ ]         ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift A₁ t₁) $
                                                                     unitrec-β-η ⊢A₁[σ₁⇑] (R.escape-⊩∷ ⊩t₁[σ₁]) ⊢u₁[σ₁] ok
                                                                       (Unit-with-η-𝕨→Unitʷ-η η) ⟩⊩∷∷
                                                                   ⟨ R.⊩≡⇔ .proj₁ $
                                                                     ⊩ᵛ≡→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[] (refl-⊩ᵛ≡ ⊩A₁)
                                                                       (⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (η-unitᵛ ⊩t₁ ⊩⋆ η) $
                                                                        refl-⊩ˢ≡∷ ⊩σ₁)
                                                                       (refl-⊩ˢ≡∷ ⊩σ₁) ⟩⊩∷
        u₁ [ σ₁ ]                     ∷ A₁ [ starʷ l ]₀ [ σ₁ ]    ≡⟨ R.⊩≡∷⇔ .proj₁ (u₁≡u₂ id σ₁≡σ₂) ⟩⊩∷∷⇐*
                                                                   ⟨ A₁[⋆]₀[σ₁]≡A₂[⋆]₀[σ₂] ⟩⇒
                                      ∷ A₂ [ starʷ l ]₀ [ σ₂ ]     ⟨ singleSubstLift A₂ (starʷ _) ⟩⇐≡
        u₂ [ σ₂ ]                     ∷ A₂ [ σ₂ ⇑ ] [ starʷ l ]₀  ⇐⟨ conv
                                                                       (unitrec-β-η ⊢A₂[σ₂⇑] (R.escape-⊩∷ ⊩t₂[σ₂]) ⊢u₂[σ₂] ok
                                                                          (Unit-with-η-𝕨→Unitʷ-η η))
                                                                       (≅-eq $ R.escape-⊩≡ $
                                                                        ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩A₂) (refl-⊩ˢ≡∷ ⊩σ₂) $
                                                                        ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (η-unitᵛ ⊩t₂ ⊩⋆ η) $
                                                                        refl-⊩ˢ≡∷ ⊩σ₂)
                                                                   ⟩∎∷
        unitrec l p q A₂ t₂ u₂ [ σ₂ ]                             ∎

      (Unitₜ₌ʷ rest no-η) →
        case PE.subst (_⊢_⇒*_∷_ _ _ _)
               (PE.sym $ singleSubstLift A₁ t₁) $
             unitrec-subst* {p = p} {q = q} t₁[σ₁]⇒*t₁′ ⊢A₁[σ₁⇑] ⊢u₁[σ₁]
               no-η of λ
          unitrec⇒*₁ →
        case PE.subst (_⊢_⇒*_∷_ _ _ _)
               (PE.sym $ singleSubstLift A₂ t₂) $
             unitrec-subst* {p = p} {q = q} t₂[σ₂]⇒*t₂′ ⊢A₂[σ₂⇑] ⊢u₂[σ₂]
               no-η of λ
          unitrec⇒*₂ →
        case PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
               (PE.sym $ singleSubstLift A₁ t₁) PE.refl $
             R.⊩≡→ $
             ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩A₁) (refl-⊩ˢ≡∷ ⊩σ₁)
               (R.→⊩≡∷ $ ⊩∷-⇒* t₁[σ₁]⇒*t₁′ $ R.⊩∷→ ⊩t₁[σ₁]) of λ
          A₁[t₁]₀[σ₁]≡A₁[σ₁⇑][t₁′]₀ →
        case ≅-eq $ escape-⊩≡ $
             PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
               (PE.sym $ singleSubstLift A₂ t₂) PE.refl $
             R.⊩≡→ $
             ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩A₂) (refl-⊩ˢ≡∷ ⊩σ₂)
               (R.→⊩≡∷ $ ⊩∷-⇒* t₂[σ₂]⇒*t₂′ $ R.⊩∷→ ⊩t₂[σ₂]) of λ
          ⊢A₂[t₂]₀[σ₂]≡A₂[σ₂⇑][t₂′]₀ →
        case rest of λ where
          starᵣ →
            unitrec l p q A₁ t₁        u₁ [ σ₁ ] ∷ A₁ [ t₁ ]₀ [ σ₁ ]         ⇒*⟨ unitrec⇒*₁ ⟩⊩∷∷
                                                                               ⟨ A₁[t₁]₀[σ₁]≡A₁[σ₁⇑][t₁′]₀ ⟩⊩∷
            unitrec l p q A₁ (starʷ l) u₁ [ σ₁ ] ∷ A₁ [ σ₁ ⇑ ] [ starʷ l ]₀  ⇒⟨ unitrec-β ⊢A₁[σ₁⇑] ⊢u₁[σ₁] ok no-η ⟩⊩∷∷
                                                                             ˘⟨ singleSubstLift A₁ (starʷ _) ⟩⊩∷≡
            u₁ [ σ₁ ]                            ∷ A₁ [ starʷ l ]₀ [ σ₁ ]    ≡⟨ R.⊩≡∷→ $ u₁≡u₂ id σ₁≡σ₂ ⟩⊩∷∷⇐*
                                                                              ⟨ A₁[⋆]₀[σ₁]≡A₂[⋆]₀[σ₂] ⟩⇒
                                                 ∷ A₂ [ starʷ l ]₀ [ σ₂ ]     ⟨ singleSubstLift A₂ (starʷ _) ⟩⇐≡
            u₂ [ σ₂ ]                            ∷ A₂ [ σ₂ ⇑ ] [ starʷ l ]₀  ⇐⟨ unitrec-β ⊢A₂[σ₂⇑] ⊢u₂[σ₂] ok no-η ⟩∷
                                                                             ˘⟨ ⊢A₂[t₂]₀[σ₂]≡A₂[σ₂⇑][t₂′]₀ ⟩⇒
            unitrec l p q A₂ (starʷ l) u₂ [ σ₂ ] ∷ A₂ [ t₂ ]₀ [ σ₂ ]         ⇐*⟨ unitrec⇒*₂ ⟩∎∷
            unitrec l p q A₂ t₂        u₂ [ σ₂ ]                             ∎

          (ne (neNfₜ₌ t₁′-ne t₂′-ne t₁′~t₂′)) →
            ∇ » Η ⊩⟨ l′ ⟩
              unitrec l p q (A₁ [ σ₁ ⇑ ]) (t₁ [ σ₁ ]) (u₁ [ σ₁ ]) ≡
              unitrec l p q (A₂ [ σ₂ ⇑ ]) (t₂ [ σ₂ ]) (u₂ [ σ₂ ]) ∷
              A₁ [ t₁ ]₀ [ σ₁ ] ∋
            (unitrec l p q (A₁ [ σ₁ ⇑ ]) (t₁ [ σ₁ ]) (u₁ [ σ₁ ])
               ∷ A₁ [ t₁ ]₀ [ σ₁ ]                                ⇒*⟨ unitrec⇒*₁ ⟩⊩∷∷
                                                                    ⟨ A₁[t₁]₀[σ₁]≡A₁[σ₁⇑][t₁′]₀ ⟩⊩∷
             unitrec l p q (A₁ [ σ₁ ⇑ ]) t₁′         (u₁ [ σ₁ ])
               ∷ A₁ [ σ₁ ⇑ ] [ t₁′ ]₀                             ≡⟨ neutral-⊩≡∷ (wf-⊩≡ A₁[t₁]₀[σ₁]≡A₁[σ₁⇑][t₁′]₀ .proj₂)
                                                                       (unitrecₙ no-η t₁′-ne) (unitrecₙ no-η t₂′-ne)
                                                                       (~-unitrec
                                                                          (with-inc-⊢≅ ⊢A₁[σ₁⇑]≡⊢A₂[σ₂⇑] $
                                                                           escape-⊩≡ $
                                                                           R.⊩≡→ ⦃ inc = included ⦄ A₁[σ₁⇑]≡A₂[σ₂⇑])
                                                                          t₁′~t₂′
                                                                          (PE.subst (_⊢_≅_∷_ _ _ _) (singleSubstLift A₁ _) $
                                                                           escape-⊩≡∷ (R.⊩≡∷→ $ u₁≡u₂ id σ₁≡σ₂))
                                                                          ok no-η) ⟩⊩∷∷⇐*
                                                                    ⟨ ≅-eq $ escape-⊩≡ $ R.⊩≡→ $
                                                                      ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ A₁≡A₂ σ₁≡σ₂ $ R.→⊩≡∷ $
                                                                      neutral-⊩≡∷ (R.⊩→ $ ⊩ᵛ→⊩ˢ∷→⊩[] ⊩Unit ⊩σ₁)
                                                                        t₁′-ne t₂′-ne t₁′~t₂′ ⟩⇒
               ∷ A₂ [ σ₂ ⇑ ] [ t₂′ ]₀                              ˘⟨ ⊢A₂[t₂]₀[σ₂]≡A₂[σ₂⇑][t₂′]₀ ⟩⇒

             unitrec l p q (A₂ [ σ₂ ⇑ ]) t₂′         (u₂ [ σ₂ ])
               ∷ A₂ [ t₂ ]₀ [ σ₂ ]                                ⇐*⟨ unitrec⇒*₂ ⟩∎∷

             unitrec l p q (A₂ [ σ₂ ⇑ ]) (t₂ [ σ₂ ]) (u₂ [ σ₂ ])  ∎) }

opaque

  -- Validity of equality between applications of unitrec.

  unitrec-congᵛ :
    Γ »∙ Unitʷ l ⊢ A₁ ≡ A₂ →
    Γ »∙ Unitʷ l ⊩ᵛ⟨ l′ ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l″ ⟩ t₁ ≡ t₂ ∷ Unitʷ l →
    Γ ⊩ᵛ⟨ l‴ ⟩ u₁ ≡ u₂ ∷ A₁ [ starʷ l ]₀ →
    Γ ⊩ᵛ⟨ l′ ⟩ unitrec l p q A₁ t₁ u₁ ≡ unitrec l p q A₂ t₂ u₂ ∷
      A₁ [ t₁ ]₀
  unitrec-congᵛ ⊢A₁≡A₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ (wf-⊩ᵛ≡ A₁≡A₂ .proj₁) (wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁)
      , λ ξ⊇ → ⊩unitrec≡unitrec (defn-wkEq ξ⊇ ⊢A₁≡A₂)
                                (defn-wk-⊩ᵛ≡ ξ⊇ A₁≡A₂)
                                (defn-wk-⊩ᵛ≡∷ ξ⊇ t₁≡t₂)
                                (defn-wk-⊩ᵛ≡∷ ξ⊇ u₁≡u₂)
      )

opaque

  -- Validity of unitrec.

  unitrecᵛ :
    Γ »∙ Unitʷ l ⊢ A →
    Γ »∙ Unitʷ l ⊩ᵛ⟨ l′ ⟩ A →
    Γ ⊩ᵛ⟨ l″ ⟩ t ∷ Unitʷ l →
    Γ ⊩ᵛ⟨ l‴ ⟩ u ∷ A [ starʷ l ]₀ →
    Γ ⊩ᵛ⟨ l′ ⟩ unitrec l p q A t u ∷ A [ t ]₀
  unitrecᵛ ⊢A ⊩A ⊩t ⊩u =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    unitrec-congᵛ (refl ⊢A) (refl-⊩ᵛ≡ ⊩A) (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ᵛ≡∷ ⊩u)

opaque

  -- Validity of the unitrec β rule.

  unitrec-βᵛ :
    Γ »∙ Unitʷ l ⊢ A →
    Γ »∙ Unitʷ l ⊩ᵛ⟨ l″ ⟩ A →
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ A [ starʷ l ]₀ →
    ¬ Unitʷ-η →
    Γ ⊩ᵛ⟨ l′ ⟩ unitrec l p q A (starʷ l) t ≡ t ∷ A [ starʷ l ]₀
  unitrec-βᵛ {A} ⊢A ⊩A ⊩t no-η =
    ⊩ᵛ∷-⇐
      (λ ξ⊇ ⊩σ →
         let ⊢A = defn-wk ξ⊇ ⊢A
             ⊢Unit = ⊢∙→⊢ (wf ⊢A)
             ⊩t = defn-wk-⊩ᵛ∷ ξ⊇ ⊩t
         in
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
    Γ »∙ Unitʷ l ⊢ A →
    Γ »∙ Unitʷ l ⊩ᵛ⟨ l′ ⟩ A →
    Γ ⊩ᵛ⟨ l″ ⟩ t ∷ Unitʷ l →
    Γ ⊩ᵛ⟨ l‴ ⟩ u ∷ A [ starʷ l ]₀ →
    Unitʷ-η →
    Γ ⊩ᵛ⟨ l′ ⟩ unitrec l p q A t u ≡ u ∷ A [ t ]₀
  unitrec-β-ηᵛ {A} ⊢A ⊩A ⊩t ⊩u η =
    let ⊢Unit = ⊢∙→⊢ (wf ⊢A)
        ok    = inversion-Unit ⊢Unit
    in
    ⊩ᵛ∷-⇐
      (λ ξ⊇ ⊩σ →
         let ⊢A = defn-wk ξ⊇ ⊢A
             ⊢Unit = defn-wk ξ⊇ ⊢Unit
             ⊩t = defn-wk-⊩ᵛ∷ ξ⊇ ⊩t
             ⊩u = defn-wk-⊩ᵛ∷ ξ⊇ ⊩u
         in
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
