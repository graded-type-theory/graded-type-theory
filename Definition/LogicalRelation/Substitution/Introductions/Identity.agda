------------------------------------------------------------------------
-- Validity for identity types
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Identity
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  ⦃ eqrel : EqRelSet R ⦄
  where

open EqRelSet eqrel
open Type-restrictions R

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R
import Definition.LogicalRelation.Substitution.Introductions.Erased R
  as Erased
open import
  Definition.LogicalRelation.Substitution.Introductions.Universe R
open import Definition.LogicalRelation.Substitution.Introductions.Var R
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Reduction.Primitive R
open import Definition.Typed.RedSteps R
open import Definition.Untyped M as U hiding (_[_])
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

import Graded.Derived.Erased.Typed.Primitive R as ETP
import Graded.Derived.Erased.Untyped

open import Tools.Fin using (x0)
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality

private variable
  Γ Δ                                             : Con Term _
  A A₁ A₂ B B₁ B₂ t t₁ t₂ u u₁ u₂ v v₁ v₂ w w₁ w₂ : Term _
  σ σ₁ σ₂                                         : Subst _ _
  l l′ l′₁ l′₂ l′₃ l′₄ l′₅ l″ l‴ l⁗               : TypeLevel
  n                                               : Nat
  p q                                             : M
  s                                               : Strength

private

  -- Some definitions used in proofs below.

  module E {s} (ok : []-cong-allowed s) where

    open Erased ([]-cong→Erased ok) public
      renaming ([]-congᵛ to []-congᵛ′)
    open ETP    ([]-cong→Erased ok) public
    open Graded.Derived.Erased.Untyped 𝕄 s public

------------------------------------------------------------------------
-- Some characterisation lemmas

opaque
  unfolding _⊩⟨_⟩_∷_

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩Id⇔ :
    Γ ⊩⟨ l ⟩ Id A t u ⇔
    (Γ ⊩⟨ l ⟩ t ∷ A × Γ ⊩⟨ l ⟩ u ∷ A)
  ⊩Id⇔ {A} {t} {u} =
      (λ ⊩Id → lemma (Id-elim ⊩Id))
    , (λ ((⊩A , ⊩t) , (⊩A′ , ⊩u)) →
         Idᵣ
           (Idᵣ A t u
              (idRed:*: (Idⱼ (escapeTerm ⊩A ⊩t) (escapeTerm ⊩A′ ⊩u))) ⊩A
              ⊩t (irrelevanceTerm ⊩A′ ⊩A ⊩u)))
    where
    lemma :
      Γ ⊩⟨ l ⟩Id Id A t u →
      Γ ⊩⟨ l ⟩ t ∷ A × Γ ⊩⟨ l ⟩ u ∷ A
    lemma (emb 0<1 ⊩Id) =
      case lemma ⊩Id of λ
        (⊩t , ⊩u) →
      emb-⊩∷ (emb 0<1) ⊩t , emb-⊩∷ (emb 0<1) ⊩u
    lemma (noemb ⊩Id) =
      case whnfRed* (red ⇒*Id) Idₙ of λ {
        PE.refl →
      (⊩Ty , ⊩lhs) , (⊩Ty , ⊩rhs) }
      where
      open _⊩ₗId_ ⊩Id

opaque

  -- A corollary.

  →⊩Id∷U :
    Γ ⊩⟨ l ⟩ A ∷ U →
    Γ ⊩⟨ l ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ u ∷ A →
    Γ ⊩⟨ l ⟩ Id A t u ∷ U
  →⊩Id∷U {Γ} {l} {A} {t} {u} ⊩A ⊩t ⊩u =                       $⟨ ⊩A , ⊩t , ⊩u ⟩
    Γ ⊩⟨ l ⟩ A ∷ U ×
    Γ ⊩⟨ l ⟩ t ∷ A ×
    Γ ⊩⟨ l ⟩ u ∷ A                                            →⟨ (λ (⊩A∷U , ⊩t , ⊩u) →
                                                                    case ⊩∷U⇔ .proj₁ ⊩A∷U of λ
                                                                      ((_ , l′<l , ⊩A) , _) →
                                                                      (_ , l′<l , level-⊩∷ ⊩A ⊩t , level-⊩∷ ⊩A ⊩u)
                                                                    , Idⱼ (escape-⊩∷ ⊩A∷U) (escape-⊩∷ ⊩t) (escape-⊩∷ ⊩u)
                                                                    , ≅ₜ-Id-cong (escape-⊩≡∷ (refl-⊩≡∷ ⊩A∷U))
                                                                        (escape-⊩≡∷ (refl-⊩≡∷ ⊩t)) (escape-⊩≡∷ (refl-⊩≡∷ ⊩u)))
                                                               ⟩
    ((∃ λ l′ → l′ < l × Γ ⊩⟨ l′ ⟩ t ∷ A × Γ ⊩⟨ l′ ⟩ u ∷ A) ×
     Γ ⊢ Id A t u ∷ U ×
     Γ ⊢ Id A t u ≅ Id A t u ∷ U)                             ⇔˘⟨ (Σ-cong-⇔ λ _ → id⇔ ×-cong-⇔ ⊩Id⇔) ×-cong-⇔ id⇔ ⟩→

    ((∃ λ l′ → l′ < l × Γ ⊩⟨ l′ ⟩ Id A t u) ×
     Γ ⊢ Id A t u ∷ U ×
     Γ ⊢ Id A t u ≅ Id A t u ∷ U)                             ⇔˘⟨ Type→⊩∷U⇔ Idₙ ⟩→

    Γ ⊩⟨ l ⟩ Id A t u ∷ U                                     □

-- A variant of ⊩Id∷-view.

data ⊩Id∷-view′
       (Γ : Con Term n) (l : TypeLevel) (A t u : Term n) :
       Term n → Set a where
  rflᵣ : Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
         ⊩Id∷-view′ Γ l A t u rfl
  ne   : Neutral v →
         Γ ⊢ v ~ v ∷ Id A t u →
         ⊩Id∷-view′ Γ l A t u v

opaque
  unfolding _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷Id⇔ :
    Γ ⊩⟨ l ⟩ v ∷ Id A t u ⇔
    (∃ λ w →
     Γ ⊢ v :⇒*: w ∷ Id A t u ×
     Γ ⊩⟨ l ⟩ t ∷ A ×
     Γ ⊩⟨ l ⟩ u ∷ A ×
     ⊩Id∷-view′ Γ l A t u w)
  ⊩∷Id⇔ =
      (λ (⊩Id , ⊩v) →
         lemma (Id-elim ⊩Id)
           (irrelevanceTerm ⊩Id (Id-intr (Id-elim ⊩Id)) ⊩v))
    , (λ (w , v⇒*w , (⊩A , ⊩t) , (⊩A′ , ⊩u) , rest) →
         case idRed:*: $ Idⱼ (escapeTerm ⊩A ⊩t) (escapeTerm ⊩A′ ⊩u) of λ
           Id⇒*Id →
           Idᵣ (Idᵣ _ _ _ Id⇒*Id ⊩A ⊩t (irrelevanceTerm ⊩A′ ⊩A ⊩u))
         , ( w , v⇒*w
           , (case rest of λ where
                (ne w-ne w~w)              → ne w-ne , w~w
                (rflᵣ (⊩A″ , _ , _ , t≡u)) →
                  rflₙ , irrelevanceEqTerm ⊩A″ ⊩A t≡u)
           ))
    where
    lemma :
      (⊩Id : Γ ⊩⟨ l ⟩Id Id A t u) →
      Γ ⊩⟨ l ⟩ v ∷ Id A t u / Id-intr ⊩Id →
      ∃ λ w →
      Γ ⊢ v :⇒*: w ∷ Id A t u ×
      Γ ⊩⟨ l ⟩ t ∷ A ×
      Γ ⊩⟨ l ⟩ u ∷ A ×
      ⊩Id∷-view′ Γ l A t u w
    lemma (emb 0<1 ⊩Id) ⊩v =
      case lemma ⊩Id ⊩v of λ
        (w , v⇒*w , ⊩t , ⊩u , rest) →
        w , v⇒*w , emb-⊩∷ (emb 0<1) ⊩t , emb-⊩∷ (emb 0<1) ⊩u
      , (case rest of λ where
           (rflᵣ t≡u)    → rflᵣ (emb-⊩≡∷ (emb 0<1) t≡u)
           (ne v-ne v~v) → ne v-ne v~v)
    lemma (noemb ⊩Id) ⊩v@(w , v⇒*w , _) =
      case whnfRed* (red ⇒*Id) Idₙ of λ {
        PE.refl →
        w , v⇒*w
      , (⊩Ty , ⊩lhs)
      , (⊩Ty , ⊩rhs)
      , (case ⊩Id∷-view-inhabited ⊩v of λ where
           (rflᵣ lhs≡rhs) → rflᵣ (⊩Ty , ⊩lhs , ⊩rhs , lhs≡rhs)
           (ne w-ne w~w)  → ne w-ne w~w) }
      where
      open _⊩ₗId_ ⊩Id

opaque

  -- A variant of ⊩∷Id⇔.

  Identity→⊩∷Id⇔ :
    Identity v →
    Γ ⊩⟨ l ⟩ v ∷ Id A t u ⇔
    (Γ ⊢ v ∷ Id A t u ×
     Γ ⊩⟨ l ⟩ t ∷ A ×
     Γ ⊩⟨ l ⟩ u ∷ A ×
     ⊩Id∷-view′ Γ l A t u v)
  Identity→⊩∷Id⇔ {v} {Γ} {l} {A} {t} {u} v-id =
    Γ ⊩⟨ l ⟩ v ∷ Id A t u       ⇔⟨ ⊩∷Id⇔ ⟩

    (∃ λ w →
     Γ ⊢ v :⇒*: w ∷ Id A t u ×
     Γ ⊩⟨ l ⟩ t ∷ A ×
     Γ ⊩⟨ l ⟩ u ∷ A ×
     ⊩Id∷-view′ Γ l A t u w)    ⇔⟨ (λ (_ , v⇒*w , ⊩t , ⊩u , rest) →
                                      case whnfRed*Term (redₜ v⇒*w) (identityWhnf v-id) of λ {
                                        PE.refl →
                                      ⊢t-redₜ v⇒*w , ⊩t , ⊩u , rest })
                                 , (λ (⊢v , ⊩t , ⊩u , rest) →
                                      _ , idRedTerm:*: ⊢v , ⊩t , ⊩u , rest)
                                 ⟩
    Γ ⊢ v ∷ Id A t u ×
    Γ ⊩⟨ l ⟩ t ∷ A ×
    Γ ⊩⟨ l ⟩ u ∷ A ×
    ⊩Id∷-view′ Γ l A t u v      □⇔

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩Id≡⇔ :
    Γ ⊩⟨ l ⟩ Id A t u ≡ B ⇔
    (Γ ⊩⟨ l ⟩ Id A t u ×
     ∃₃ λ A′ t′ u′ →
     (Γ ⊢ B :⇒*: Id A′ t′ u′) ×
     (Γ ⊩⟨ l ⟩ A ≡ A′) ×
     Γ ⊩⟨ l ⟩ t ≡ t′ ∷ A ×
     Γ ⊩⟨ l ⟩ u ≡ u′ ∷ A)
  ⊩Id≡⇔ =
      (λ (⊩Id , ⊩B , Id≡B) →
           ⊩Id
         , lemma₁ refl (Id-elim ⊩Id) ⊩B
             (irrelevanceEq ⊩Id (Id-intr (Id-elim ⊩Id)) Id≡B))
    , (λ (⊩Id , rest) →
         Id-intr (Id-elim ⊩Id) , lemma₂ refl (Id-elim ⊩Id) rest)
    where
    lemma₁ :
      l′ ≤ l →
      (⊩Id : Γ ⊩⟨ l′ ⟩Id Id A t u) →
      Γ ⊩⟨ l ⟩ B →
      Γ ⊩⟨ l′ ⟩ Id A t u ≡ B / Id-intr ⊩Id →
      ∃₃ λ A′ t′ u′ →
      (Γ ⊢ B :⇒*: Id A′ t′ u′) ×
      (Γ ⊩⟨ l ⟩ A ≡ A′) ×
      Γ ⊩⟨ l ⟩ t ≡ t′ ∷ A ×
      Γ ⊩⟨ l ⟩ u ≡ u′ ∷ A
    lemma₁ 1≤l (emb 0<1 ⊩Id) ⊩B Id≡A =
      lemma₁ (≤-trans (emb 0<1) 1≤l) ⊩Id ⊩B Id≡A
    lemma₁ l′≤l (noemb ⊩Id) ⊩B (Id₌ A′ t′ u′ ⇒*Id′ A≡A′ t≡t′ u≡u′ _ _) =
      case whnfRed* (red ⇒*Id) Idₙ of λ {
        PE.refl →
      case extractMaybeEmb′ (Id-elim (redSubst*′ ⇒*Id′ ⊩B .proj₁)) of λ
        (_ , l″≤l , Idᵣ _ _ _ ⇒*Id″ ⊩Ty″ ⊩lhs″ ⊩rhs″) →
      case whnfRed* (red ⇒*Id″) Idₙ of λ {
        PE.refl →
      case emb-≤-≡ A≡A′ of λ
        A≡A′ →
      let ⊩Ty′ = emb-≤-⊩ l′≤l ⊩Ty in
        A′ , t′ , u′ , ⇒*Id′
      , (⊩Ty′ , emb-≤-⊩ l″≤l ⊩Ty″ , A≡A′)
      , ( ⊩Ty′
        , emb-≤-∷ ⊩lhs
        , convTerm₂ ⊩Ty′ ⊩Ty″ A≡A′ ⊩lhs″
        , emb-≤-≡∷ t≡t′
        )
      , ( ⊩Ty′
        , emb-≤-∷ ⊩rhs
        , convTerm₂ ⊩Ty′ ⊩Ty″ A≡A′ ⊩rhs″
        , emb-≤-≡∷ u≡u′
        ) }}
      where
      open _⊩ₗId_ ⊩Id

    lemma₂ :
      l′ ≤ l →
      (⊩Id : Γ ⊩⟨ l′ ⟩Id Id A t u) →
      (∃₃ λ A′ t′ u′ →
       (Γ ⊢ B :⇒*: Id A′ t′ u′) ×
       (Γ ⊩⟨ l ⟩ A ≡ A′) ×
       Γ ⊩⟨ l ⟩ t ≡ t′ ∷ A ×
       Γ ⊩⟨ l ⟩ u ≡ u′ ∷ A) →
      (Γ ⊩⟨ l ⟩ B) × Γ ⊩⟨ l′ ⟩ Id A t u ≡ B / Id-intr ⊩Id
    lemma₂ 1≤l (emb 0<1 ⊩Id) rest =
      lemma₂ (≤-trans (emb 0<1) 1≤l) ⊩Id rest
    lemma₂
      _
      (noemb ⊩Id)
      ( A′ , t′ , u′ , B⇒*Id , (⊩A , ⊩A′ , A≡A′)
      , (⊩A″ , _ , ⊩t′ , t≡t′) , (⊩A‴ , _ , ⊩u′ , u≡u′)
      ) =
      case whnfRed* (red ⇒*Id) Idₙ of λ {
        PE.refl →
      case ≅-eq (escapeEq ⊩A A≡A′) of λ
        ⊢A≡A′ →
        redSubst* (red B⇒*Id)
          (Idᵣ
             (Idᵣ A′ t′ u′
                (idRed:*: $
                 Idⱼ (conv (escapeTerm ⊩A″ ⊩t′) ⊢A≡A′)
                   (conv (escapeTerm ⊩A‴ ⊩u′) ⊢A≡A′))
                ⊩A′
                (convTerm₁ ⊩A″ ⊩A′ (irrelevanceEq ⊩A ⊩A″ A≡A′) ⊩t′)
                (convTerm₁ ⊩A‴ ⊩A′ (irrelevanceEq ⊩A ⊩A‴ A≡A′) ⊩u′)))
          .proj₁
      , Id₌′ B⇒*Id (irrelevanceEq ⊩A ⊩Ty A≡A′)
          (irrelevanceEqTerm ⊩A″ ⊩Ty t≡t′)
          (irrelevanceEqTerm ⊩A‴ ⊩Ty u≡u′) }
      where
      open _⊩ₗId_ ⊩Id

opaque

  -- Another characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩Id≡Id⇔ :
    Γ ⊩⟨ l ⟩ Id A₁ t₁ u₁ ≡ Id A₂ t₂ u₂ ⇔
    ((Γ ⊩⟨ l ⟩ A₁ ≡ A₂) ×
     Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ A₁ ×
     Γ ⊩⟨ l ⟩ u₁ ≡ u₂ ∷ A₁)
  ⊩Id≡Id⇔ {Γ} {l} {A₁} {t₁} {u₁} {A₂} {t₂} {u₂} =
    (Γ ⊩⟨ l ⟩ Id A₁ t₁ u₁ ≡ Id A₂ t₂ u₂)   ⇔⟨ ⊩Id≡⇔ ⟩

    (Γ ⊩⟨ l ⟩ Id A₁ t₁ u₁ ×
     ∃₃ λ A′ t′ u′ →
     (Γ ⊢ Id A₂ t₂ u₂ :⇒*: Id A′ t′ u′) ×
     (Γ ⊩⟨ l ⟩ A₁ ≡ A′) ×
     Γ ⊩⟨ l ⟩ t₁ ≡ t′ ∷ A₁ ×
     Γ ⊩⟨ l ⟩ u₁ ≡ u′ ∷ A₁)                ⇔⟨ (λ (_ , _ , _ , _ , Id⇒*Id , A₁≡ , t₁≡ , u₁≡) →
                                                 case whnfRed* (red Id⇒*Id) Idₙ of λ {
                                                   PE.refl →
                                                 A₁≡ , t₁≡ , u₁≡ })
                                            , (λ (A₁≡A₂ , t₁≡t₂ , u₁≡u₂) →
                                                   ⊩Id⇔ .proj₂ (wf-⊩≡∷ t₁≡t₂ .proj₁ , wf-⊩≡∷ u₁≡u₂ .proj₁)
                                                 , _ , _ , _
                                                 , idRed:*:
                                                     (Idⱼ (escape-⊩∷ (conv-⊩∷ A₁≡A₂ (wf-⊩≡∷ t₁≡t₂ .proj₂)))
                                                        (escape-⊩∷ (conv-⊩∷ A₁≡A₂ (wf-⊩≡∷ u₁≡u₂ .proj₂))))
                                                 , A₁≡A₂ , t₁≡t₂ , u₁≡u₂)
                                            ⟩
    (Γ ⊩⟨ l ⟩ A₁ ≡ A₂) ×
    Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ A₁ ×
    Γ ⊩⟨ l ⟩ u₁ ≡ u₂ ∷ A₁                  □⇔

opaque

  -- A corollary.

  →⊩Id≡Id∷U :
    Γ ⊩⟨ l ⟩ A₁ ≡ A₂ ∷ U →
    Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊩⟨ l ⟩ u₁ ≡ u₂ ∷ A₁ →
    Γ ⊩⟨ l ⟩ Id A₁ t₁ u₁ ≡ Id A₂ t₂ u₂ ∷ U
  →⊩Id≡Id∷U {Γ} {l} {A₁} {A₂} {t₁} {t₂} {u₁} {u₂} A₁≡A₂∷U t₁≡t₂ u₁≡u₂ =
                                                                     $⟨ A₁≡A₂∷U , t₁≡t₂ , u₁≡u₂ ⟩
    Γ ⊩⟨ l ⟩ A₁ ≡ A₂ ∷ U ×
    Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ A₁ ×
    Γ ⊩⟨ l ⟩ u₁ ≡ u₂ ∷ A₁                                            →⟨ (λ (A₁≡A₂∷U , t₁≡t₂ , u₁≡u₂) →
                                                                           case ⊩≡∷U⇔ .proj₁ A₁≡A₂∷U of λ
                                                                             ((_ , l′<l , A₁≡A₂) , _) →
                                                                           case escape-⊩≡∷ A₁≡A₂∷U of λ
                                                                             A₁≅A₂∷U →
                                                                           case escape-⊩≡∷ t₁≡t₂ of λ
                                                                             t₁≅t₂ →
                                                                           case escape-⊩≡∷ u₁≡u₂ of λ
                                                                             u₁≅u₂ →
                                                                           case Σ.map escape-⊩∷ escape-⊩∷ $ wf-⊩≡∷ A₁≡A₂∷U of λ
                                                                             (⊢A₁∷U , ⊢A₂∷U) →
                                                                           case Σ.map escape-⊩∷ escape-⊩∷ $ wf-⊩≡∷ t₁≡t₂ of λ
                                                                             (⊢t₁ , ⊢t₂) →
                                                                           case Σ.map escape-⊩∷ escape-⊩∷ $ wf-⊩≡∷ u₁≡u₂ of λ
                                                                             (⊢u₁ , ⊢u₂) →
                                                                           case univ (≅ₜ-eq A₁≅A₂∷U) of λ
                                                                             ⊢A₁≡A₂ →
                                                                           case wf-⊩≡ A₁≡A₂ .proj₁ of λ
                                                                             ⊩A₁ →
                                                                             Idⱼ ⊢A₁∷U ⊢t₁ ⊢u₁
                                                                           , Idⱼ ⊢A₂∷U (conv ⊢t₂ ⊢A₁≡A₂) (conv ⊢u₂ ⊢A₁≡A₂)
                                                                           , ≅ₜ-Id-cong A₁≅A₂∷U t₁≅t₂ u₁≅u₂
                                                                           , _ , l′<l
                                                                           , A₁≡A₂ , level-⊩≡∷ ⊩A₁ t₁≡t₂ , level-⊩≡∷ ⊩A₁ u₁≡u₂) ⟩
    Γ ⊢ Id A₁ t₁ u₁ ∷ U ×
    Γ ⊢ Id A₂ t₂ u₂ ∷ U ×
    Γ ⊢ Id A₁ t₁ u₁ ≅ Id A₂ t₂ u₂ ∷ U ×
    (∃₂ λ l′ (l′<l : l′ < l) →
     (Γ ⊩⟨ l′ ⟩ A₁ ≡ A₂) ×
     Γ ⊩⟨ l′ ⟩ t₁ ≡ t₂ ∷ A₁ ×
     Γ ⊩⟨ l′ ⟩ u₁ ≡ u₂ ∷ A₁)                                         ⇔˘⟨ (id⇔ ×-cong-⇔ id⇔ ×-cong-⇔ id⇔ ×-cong-⇔
                                                                          Σ-cong-⇔ λ _ → id⇔ ×-cong-⇔ ⊩Id≡Id⇔) ⟩→
    Γ ⊢ Id A₁ t₁ u₁ ∷ U ×
    Γ ⊢ Id A₂ t₂ u₂ ∷ U ×
    Γ ⊢ Id A₁ t₁ u₁ ≅ Id A₂ t₂ u₂ ∷ U ×
    (∃₂ λ l′ (l′<l : l′ < l) → Γ ⊩⟨ l′ ⟩ Id A₁ t₁ u₁ ≡ Id A₂ t₂ u₂)  ⇔˘⟨ Type→⊩≡∷U⇔ Idₙ Idₙ ⟩→

    Γ ⊩⟨ l ⟩ Id A₁ t₁ u₁ ≡ Id A₂ t₂ u₂ ∷ U                           □

-- A variant of ⊩Id≡∷-view.

data ⊩Id≡∷-view′
       (Γ : Con Term n) (l : TypeLevel) (A t u : Term n) :
       Term n → Term n → Set a where
  rfl₌ : Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
         ⊩Id≡∷-view′ Γ l A t u rfl rfl
  ne   : Neutral v → Neutral w →
         Γ ⊢ v ~ w ∷ Id A t u →
         ⊩Id≡∷-view′ Γ l A t u v w

opaque
  unfolding _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷Id⇔ :
    Γ ⊩⟨ l ⟩ v ≡ w ∷ Id A t u ⇔
    (∃₂ λ v′ w′ →
     Γ ⊢ v :⇒*: v′ ∷ Id A t u ×
     Γ ⊢ w :⇒*: w′ ∷ Id A t u ×
     Γ ⊩⟨ l ⟩ t ∷ A ×
     Γ ⊩⟨ l ⟩ u ∷ A ×
     ⊩Id≡∷-view′ Γ l A t u v′ w′)
  ⊩≡∷Id⇔ =
      (λ (⊩Id , _ , _ , ⊩v) →
         lemma (Id-elim ⊩Id)
           (irrelevanceEqTerm ⊩Id (Id-intr (Id-elim ⊩Id)) ⊩v))
    , (λ (v′ , w′ , v⇒*v′ , w⇒*w′ , (⊩A , ⊩t) , (⊩A′ , ⊩u) , rest) →
         case idRed:*: $ Idⱼ (escapeTerm ⊩A ⊩t) (escapeTerm ⊩A′ ⊩u) of λ
           Id⇒*Id →
           Idᵣ (Idᵣ _ _ _ Id⇒*Id ⊩A ⊩t (irrelevanceTerm ⊩A′ ⊩A ⊩u))
         , (case rest of λ where
              (ne v′-ne w′-ne v′~w′) →
                  (v′ , v⇒*v′ , ne v′-ne , ~-trans v′~w′ (~-sym v′~w′))
                , (w′ , w⇒*w′ , ne w′-ne , ~-trans (~-sym v′~w′) v′~w′)
                , ( v′ , w′ , v⇒*v′ , w⇒*w′
                  , ne v′-ne , ne w′-ne , v′~w′
                  )
              (rfl₌ (⊩A″ , _ , _ , t≡u)) →
                case irrelevanceEqTerm ⊩A″ ⊩A t≡u of λ
                  t≡u →
                  (v′ , v⇒*v′ , rflₙ , t≡u)
                , (w′ , w⇒*w′ , rflₙ , t≡u)
                , (v′ , w′ , v⇒*v′ , w⇒*w′ , rflₙ , rflₙ , t≡u)))
    where
    lemma :
      (⊩Id : Γ ⊩⟨ l ⟩Id Id A t u) →
      Γ ⊩⟨ l ⟩ v ≡ w ∷ Id A t u / Id-intr ⊩Id →
      ∃₂ λ v′ w′ →
      Γ ⊢ v :⇒*: v′ ∷ Id A t u ×
      Γ ⊢ w :⇒*: w′ ∷ Id A t u ×
      Γ ⊩⟨ l ⟩ t ∷ A ×
      Γ ⊩⟨ l ⟩ u ∷ A ×
      ⊩Id≡∷-view′ Γ l A t u v′ w′
    lemma (emb 0<1 ⊩Id) v≡w =
      case lemma ⊩Id v≡w of λ
        (v′ , w′ , v⇒*v′ , w⇒*w′ , ⊩t , ⊩u , rest) →
        v′ , w′ , v⇒*v′ , w⇒*w′
      , emb-⊩∷ (emb 0<1) ⊩t , emb-⊩∷ (emb 0<1) ⊩u
      , (case rest of λ where
           (rfl₌ t≡u)             → rfl₌ (emb-⊩≡∷ (emb 0<1) t≡u)
           (ne v′-ne w′-ne v′~w′) → ne v′-ne w′-ne v′~w′)
    lemma (noemb ⊩Id) v≡w@(v′ , w′ , v⇒*v′ , w⇒*w′ , _) =
      case whnfRed* (red ⇒*Id) Idₙ of λ {
        PE.refl →
        v′ , w′ , v⇒*v′ , w⇒*w′
      , (⊩Ty , ⊩lhs)
      , (⊩Ty , ⊩rhs)
      , (case ⊩Id≡∷-view-inhabited ⊩Id v≡w of λ where
           (rfl₌ t≡u)             → rfl₌ (⊩Ty , ⊩lhs , ⊩rhs , t≡u)
           (ne v′-ne w′-ne v′~w′) → ne v′-ne w′-ne v′~w′) }
      where
      open _⊩ₗId_ ⊩Id

opaque

  -- A variant of ⊩≡∷Id⇔.

  Identity→⊩≡∷Id⇔ :
    Identity v → Identity w →
    Γ ⊩⟨ l ⟩ v ≡ w ∷ Id A t u ⇔
    (Γ ⊢ v ∷ Id A t u ×
     Γ ⊢ w ∷ Id A t u ×
     Γ ⊩⟨ l ⟩ t ∷ A ×
     Γ ⊩⟨ l ⟩ u ∷ A ×
     ⊩Id≡∷-view′ Γ l A t u v w)
  Identity→⊩≡∷Id⇔ {v} {w} {Γ} {l} {A} {t} {u} v-id w-id =
    Γ ⊩⟨ l ⟩ v ≡ w ∷ Id A t u      ⇔⟨ ⊩≡∷Id⇔ ⟩

    (∃₂ λ v′ w′ →
     Γ ⊢ v :⇒*: v′ ∷ Id A t u ×
     Γ ⊢ w :⇒*: w′ ∷ Id A t u ×
     Γ ⊩⟨ l ⟩ t ∷ A ×
     Γ ⊩⟨ l ⟩ u ∷ A ×
     ⊩Id≡∷-view′ Γ l A t u v′ w′)  ⇔⟨ (λ (_ , _ , v⇒*v′ , w⇒*w′ , ⊩t , ⊩u , rest) →
                                         case whnfRed*Term (redₜ v⇒*v′) (identityWhnf v-id) of λ {
                                           PE.refl →
                                         case whnfRed*Term (redₜ w⇒*w′) (identityWhnf w-id) of λ {
                                           PE.refl →
                                         ⊢t-redₜ v⇒*v′ , ⊢t-redₜ w⇒*w′ , ⊩t , ⊩u , rest }})
                                    , (λ (⊢v , ⊢w , ⊩t , ⊩u , rest) →
                                         _ , _ , idRedTerm:*: ⊢v , idRedTerm:*: ⊢w , ⊩t , ⊩u , rest)
                                    ⟩
    Γ ⊢ v ∷ Id A t u ×
    Γ ⊢ w ∷ Id A t u ×
    Γ ⊩⟨ l ⟩ t ∷ A ×
    Γ ⊩⟨ l ⟩ u ∷ A ×
    ⊩Id≡∷-view′ Γ l A t u v w      □⇔

opaque

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_.

  ⊩ᵛId⇔ :
    Γ ⊩ᵛ⟨ l ⟩ Id A t u ⇔
    (Γ ⊩ᵛ⟨ l ⟩ t ∷ A × Γ ⊩ᵛ⟨ l ⟩ u ∷ A)
  ⊩ᵛId⇔ {Γ} {l} {A} {t} {u} =
    (Γ ⊩ᵛ⟨ l ⟩ Id A t u)                                 ⇔⟨ ⊩ᵛ⇔′ ⟩

    ⊩ᵛ Γ ×
    (∀ {m Δ} {σ : Subst m _} →
     Δ ⊩ˢ σ ∷ Γ →
     Δ ⊩⟨ l ⟩ Id A t u U.[ σ ]) ×
    (∀ {m Δ} {σ₁ σ₂ : Subst m _} →
     Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
     Δ ⊩⟨ l ⟩ Id A t u U.[ σ₁ ] ≡ Id A t u U.[ σ₂ ])     ⇔⟨ id⇔
                                                              ×-cong-⇔
                                                            (implicit-Π-cong-⇔ λ _ → implicit-Π-cong-⇔ λ _ →
                                                             implicit-Π-cong-⇔ λ _ → Π-cong-⇔ λ _ →
                                                             ⊩Id⇔)
                                                              ×-cong-⇔
                                                            (implicit-Π-cong-⇔ λ _ → implicit-Π-cong-⇔ λ _ →
                                                             implicit-Π-cong-⇔ λ _ → implicit-Π-cong-⇔ λ _ →
                                                             Π-cong-⇔ λ _ →
                                                             ⊩Id≡Id⇔) ⟩
    ⊩ᵛ Γ ×
    (∀ {m Δ} {σ : Subst m _} →
     Δ ⊩ˢ σ ∷ Γ →
     Δ ⊩⟨ l ⟩ t U.[ σ ] ∷ A U.[ σ ] ×
     Δ ⊩⟨ l ⟩ u U.[ σ ] ∷ A U.[ σ ]) ×
    (∀ {m Δ} {σ₁ σ₂ : Subst m _} →
     Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
     (Δ ⊩⟨ l ⟩ A U.[ σ₁ ] ≡ A U.[ σ₂ ]) ×
     Δ ⊩⟨ l ⟩ t U.[ σ₁ ] ≡ t U.[ σ₂ ] ∷ A U.[ σ₁ ] ×
     Δ ⊩⟨ l ⟩ u U.[ σ₁ ] ≡ u U.[ σ₂ ] ∷ A U.[ σ₁ ])      ⇔⟨ (λ (⊩Γ , ⊩t×⊩u , A≡A×t≡t×u≡u) →
                                                               case ⊩ᵛ⇔′ .proj₂
                                                                      ( ⊩Γ
                                                                      , (λ ⊩σ → wf-⊩≡ (A≡A×t≡t×u≡u (refl-⊩ˢ≡∷ ⊩σ) .proj₁) .proj₁)
                                                                      , proj₁ ∘→ A≡A×t≡t×u≡u
                                                                      ) of λ
                                                                 ⊩A →
                                                                 ( ⊩A
                                                                 , (λ ⊩σ → ⊩t×⊩u ⊩σ .proj₁)
                                                                 , (λ σ₁≡σ₂ → A≡A×t≡t×u≡u σ₁≡σ₂ .proj₂ .proj₁)
                                                                 )
                                                               , ( ⊩A
                                                                 , (λ ⊩σ → ⊩t×⊩u ⊩σ .proj₂)
                                                                 , (λ σ₁≡σ₂ → A≡A×t≡t×u≡u σ₁≡σ₂ .proj₂ .proj₂)
                                                                 ))
                                                          , (λ ((⊩A , ⊩t , t≡t) , (_ , ⊩u , u≡u)) →
                                                                 wf-⊩ᵛ ⊩A
                                                               , (λ ⊩σ → ⊩t ⊩σ , ⊩u ⊩σ)
                                                               , (λ σ₁≡σ₂ →
                                                                      ⊩ᵛ⇔′ .proj₁ ⊩A .proj₂ .proj₂ σ₁≡σ₂
                                                                    , t≡t σ₁≡σ₂ , u≡u σ₁≡σ₂))
                                                          ⟩
    (Γ ⊩ᵛ⟨ l ⟩ A ×
     (∀ {m Δ} {σ : Subst m _} →
      Δ ⊩ˢ σ ∷ Γ →
      Δ ⊩⟨ l ⟩ t U.[ σ ] ∷ A U.[ σ ]) ×
     (∀ {m Δ} {σ₁ σ₂ : Subst m _} →
      Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
      Δ ⊩⟨ l ⟩ t U.[ σ₁ ] ≡ t U.[ σ₂ ] ∷ A U.[ σ₁ ])) ×
    (Γ ⊩ᵛ⟨ l ⟩ A ×
     (∀ {m Δ} {σ : Subst m _} →
      Δ ⊩ˢ σ ∷ Γ →
      Δ ⊩⟨ l ⟩ u U.[ σ ] ∷ A U.[ σ ]) ×
     (∀ {m Δ} {σ₁ σ₂ : Subst m _} →
      Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
      Δ ⊩⟨ l ⟩ u U.[ σ₁ ] ≡ u U.[ σ₂ ] ∷ A U.[ σ₁ ]))    ⇔˘⟨ ⊩ᵛ∷⇔′ ×-cong-⇔ ⊩ᵛ∷⇔′ ⟩

    Γ ⊩ᵛ⟨ l ⟩ t ∷ A × Γ ⊩ᵛ⟨ l ⟩ u ∷ A                    □⇔

------------------------------------------------------------------------
-- Id

opaque

  -- Validity of Id, seen as a type former.

  Idᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ Id A t u
  Idᵛ ⊩t ⊩u =
    case ⊩ᵛ∷⇔′ .proj₁ ⊩t of λ
      (⊩A , ⊩t , t≡t) →
    case ⊩ᵛ∷⇔′ .proj₁ (level-⊩ᵛ∷ ⊩A ⊩u) of λ
      (_ , ⊩u , u≡u) →
    case ⊩ᵛ⇔′ .proj₁ ⊩A of λ
      (⊩Γ , _ , A≡A) →
    ⊩ᵛ⇔′ .proj₂
      ( ⊩Γ
      , (λ ⊩σ → ⊩Id⇔ .proj₂ (⊩t ⊩σ , ⊩u ⊩σ))
      , (λ σ₁≡σ₂ → ⊩Id≡Id⇔ .proj₂ (A≡A σ₁≡σ₂ , t≡t σ₁≡σ₂ , u≡u σ₁≡σ₂))
      )

opaque

  -- Validity of Id, seen as a term former.

  Idᵗᵛ :
    Γ ⊩ᵛ⟨ l ⟩ A ∷ U →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ Id A t u ∷ U
  Idᵗᵛ ⊩A∷U ⊩t ⊩u =
    case ⊩ᵛ∷⇔′ .proj₁ ⊩A∷U of λ
      (⊩U , ⊩A∷U , A≡A∷U) →
    case ⊩ᵛ∷⇔′ .proj₁ ⊩t of λ
      (_ , ⊩t , t≡t) →
    case ⊩ᵛ∷⇔′ .proj₁ ⊩u of λ
      (_ , ⊩u , u≡u) →
    ⊩ᵛ∷⇔′ .proj₂
      ( ⊩U
      , (λ ⊩σ → →⊩Id∷U (⊩A∷U ⊩σ) (⊩t ⊩σ) (⊩u ⊩σ))
      , (λ σ₁≡σ₂ → →⊩Id≡Id∷U (A≡A∷U σ₁≡σ₂) (t≡t σ₁≡σ₂) (u≡u σ₁≡σ₂))
      )

opaque

  -- Validity of equality preservation for Id, seen as a type former.

  Id-congᵛ :
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l′ ⟩ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊩ᵛ⟨ l″ ⟩ u₁ ≡ u₂ ∷ A₁ →
    Γ ⊩ᵛ⟨ l ⟩ Id A₁ t₁ u₁ ≡ Id A₂ t₂ u₂
  Id-congᵛ A₁≡A₂ t₁≡t₂ u₁≡u₂ =
    case wf-⊩ᵛ≡ A₁≡A₂ of λ
      (⊩A₁ , _) →
    case ⊩ᵛ≡∷⇔ .proj₁ (level-⊩ᵛ≡∷ ⊩A₁ t₁≡t₂) of λ
      (⊩t₁ , ⊩t₂ , t₁≡t₂) →
    case ⊩ᵛ≡∷⇔ .proj₁ (level-⊩ᵛ≡∷ ⊩A₁ u₁≡u₂) of λ
      (⊩u₁ , ⊩u₂ , u₁≡u₂) →
    ⊩ᵛ≡⇔ .proj₂
      ( Idᵛ ⊩t₁ ⊩u₁
      , Idᵛ (conv-⊩ᵛ∷ A₁≡A₂ ⊩t₂) (conv-⊩ᵛ∷ A₁≡A₂ ⊩u₂)
      , λ ⊩σ →
          ⊩Id≡Id⇔ .proj₂
            (⊩ᵛ≡⇔ .proj₁ A₁≡A₂ .proj₂ .proj₂ ⊩σ , t₁≡t₂ ⊩σ , u₁≡u₂ ⊩σ)
      )

opaque

  -- Validity of equality preservation for Id, seen as a term former.

  Id-congᵗᵛ :
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ ∷ U →
    Γ ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊩ᵛ⟨ l ⟩ u₁ ≡ u₂ ∷ A₁ →
    Γ ⊩ᵛ⟨ l ⟩ Id A₁ t₁ u₁ ≡ Id A₂ t₂ u₂ ∷ U
  Id-congᵗᵛ A₁≡A₂∷U t₁≡t₂ u₁≡u₂ =
    case ⊩ᵛ≡∷U→⊩ᵛ≡ A₁≡A₂∷U of λ
      A₁≡A₂ →
    case ⊩ᵛ≡∷⇔ .proj₁ A₁≡A₂∷U of λ
      (⊩A₁∷U , ⊩A₂∷U , A₁≡A₂∷U) →
    case ⊩ᵛ≡∷⇔ .proj₁ t₁≡t₂ of λ
      (⊩t₁ , ⊩t₂ , t₁≡t₂) →
    case ⊩ᵛ≡∷⇔ .proj₁ u₁≡u₂ of λ
      (⊩u₁ , ⊩u₂ , u₁≡u₂) →
    ⊩ᵛ≡∷⇔ .proj₂
      ( Idᵗᵛ ⊩A₁∷U ⊩t₁ ⊩u₁
      , Idᵗᵛ ⊩A₂∷U (conv-⊩ᵛ∷ A₁≡A₂ ⊩t₂) (conv-⊩ᵛ∷ A₁≡A₂ ⊩u₂)
      , λ ⊩σ → →⊩Id≡Id∷U (A₁≡A₂∷U ⊩σ) (t₁≡t₂ ⊩σ) (u₁≡u₂ ⊩σ)
      )

------------------------------------------------------------------------
-- The term rfl

opaque

  -- Reducibility of reflexivity.

  ⊩rfl′ :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ rfl ∷ Id A t u
  ⊩rfl′ t≡u =
    case wf-⊩≡∷ t≡u of λ
      (⊩t , ⊩u) →
    case escape-⊩∷ ⊩t of λ
      ⊢t →
    Identity→⊩∷Id⇔ rflₙ .proj₂
      ( conv (rflⱼ ⊢t)
          (Id-cong (refl (escape (wf-⊩∷ ⊩t))) (refl ⊢t)
             (≅ₜ-eq (escape-⊩≡∷ t≡u)))
      , ⊩t , ⊩u , rflᵣ t≡u
      )

opaque

  -- Reducibility of reflexivity.

  ⊩rfl :
    Γ ⊩⟨ l ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ rfl ∷ Id A t t
  ⊩rfl ⊩t = ⊩rfl′ (refl-⊩≡∷ ⊩t)

opaque

  -- Reducibility of equality between rfl and rfl.

  ⊩rfl≡rfl :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ rfl ≡ rfl ∷ Id A t u
  ⊩rfl≡rfl t≡u =
    case wf-⊩≡∷ t≡u of λ
      (⊩t , ⊩u) →
    case escape-⊩∷ (⊩rfl′ t≡u) of λ
      ⊢rfl →
    Identity→⊩≡∷Id⇔ rflₙ rflₙ .proj₂
      (⊢rfl , ⊢rfl , ⊩t , ⊩u , rfl₌ t≡u)

opaque

  -- Validity of reflexivity.

  rflᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ rfl ∷ Id A t t
  rflᵛ ⊩t =
    case ⊩ᵛ∷⇔′ .proj₁ ⊩t of λ
      (_ , ⊩t′ , t≡t) →
    ⊩ᵛ∷⇔′ .proj₂
      ( Idᵛ ⊩t ⊩t
      , ⊩rfl ∘→ ⊩t′
      , ⊩rfl≡rfl ∘→ t≡t ∘→ refl-⊩ˢ≡∷ ∘→ proj₁ ∘→ wf-⊩ˢ≡∷
      )

opaque

  -- Validity of equality for rfl.

  rfl-congᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ rfl ≡ rfl ∷ Id A t t
  rfl-congᵛ ⊩t =
    case rflᵛ ⊩t of λ
      ⊩rfl →
    ⊩ᵛ≡∷⇔ .proj₂
      ( ⊩rfl , ⊩rfl
      , ⊩rfl≡rfl ∘→ ⊩ᵛ∷⇔′ .proj₁ ⊩t .proj₂ .proj₂ ∘→ refl-⊩ˢ≡∷
      )

------------------------------------------------------------------------
-- []-cong

opaque

  -- Reducibility of equality between applications of []-cong.

  ⊩[]-cong≡[]-cong :
    (ok : []-cong-allowed s) →
    let open E ok in
    Γ ⊩⟨ l ⟩ A₁ ≡ A₂ →
    Γ ⊩⟨ l′ ⟩ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊩⟨ l″ ⟩ u₁ ≡ u₂ ∷ A₁ →
    Γ ⊩⟨ l‴ ⟩ v₁ ≡ v₂ ∷ Id A₁ t₁ u₁ →
    Γ ⊩⟨ l ⟩ []-cong s A₁ t₁ u₁ v₁ ≡ []-cong s A₂ t₂ u₂ v₂ ∷
      Id (Erased A₁) [ t₁ ] [ u₁ ]
  ⊩[]-cong≡[]-cong
    {s} {A₁} {A₂} {t₁} {t₂} {u₁} {u₂} {v₁} {v₂}
    ok A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ =
    case escape-⊩≡ A₁≡A₂ of λ
      A₁≅A₂ →
    case wf-⊩≡ A₁≡A₂ of λ
      (⊩A₁ , ⊩A₂) →
    case escape ⊩A₁ of λ
      ⊢A₁ →
    case escape ⊩A₂ of λ
      ⊢A₂ →
    case level-⊩≡∷ ⊩A₁ t₁≡t₂ of λ
      t₁≡t₂ →
    case escape-⊩≡∷ t₁≡t₂ of λ
      t₁≅t₂ →
    case wf-⊩≡∷ t₁≡t₂ of λ
      (⊩t₁ , ⊩t₂) →
    case escape-⊩∷ ⊩t₁ of λ
      ⊢t₁ →
    case level-⊩≡∷ ⊩A₁ u₁≡u₂ of λ
      u₁≡u₂ →
    case escape-⊩≡∷ u₁≡u₂ of λ
      u₁≅u₂ →
    case wf-⊩≡∷ u₁≡u₂ of λ
      (⊩u₁ , ⊩u₂) →
    case escape-⊩∷ ⊩u₁ of λ
      ⊢u₁ →
    case level-⊩≡∷ (⊩Id⇔ .proj₂ (⊩t₁ , ⊩u₁)) v₁≡v₂ of λ
      v₁≡v₂ →
    case ≅-eq A₁≅A₂ of λ
      ⊢A₁≡A₂ →
    case ≅ₜ-eq t₁≅t₂ of λ
      ⊢t₁≡t₂ →
    case ≅ₜ-eq u₁≅u₂ of λ
      ⊢u₁≡u₂ →
    case conv (escape-⊩∷ ⊩t₂) ⊢A₁≡A₂ of λ
      ⊢t₂ →
    case conv (escape-⊩∷ ⊩u₂) ⊢A₁≡A₂ of λ
      ⊢u₂ →
    case Id-cong ⊢A₁≡A₂ ⊢t₁≡t₂ ⊢u₁≡u₂ of λ
      ⊢Id≡Id →
    case Id-cong (Erased-cong ⊢A₁ ⊢A₁≡A₂) ([]-cong′ ⊢A₁ ⊢t₁≡t₂)
           ([]-cong′ ⊢A₁ ⊢u₁≡u₂) of λ
      ⊢Id≡Id′ →
    case ⊩≡∷Id⇔ .proj₁ v₁≡v₂ of λ
      (v₁′ , v₂′ , [ _ , ⊢v₁′ , v₁⇒*v₁′ ] , [ _ , ⊢v₂′ , v₂⇒*v₂′ ] ,
       ⊩t , ⊩u , rest) →
    case []-cong-subst* ⊢A₁ ⊢t₁ ⊢u₁ v₁⇒*v₁′ ok of λ
      []-cong⇒*[]-cong₁ →
    case []-cong-subst* ⊢A₂ ⊢t₂ ⊢u₂ (conv* v₂⇒*v₂′ ⊢Id≡Id) ok of λ
      []-cong⇒*[]-cong₂ →
    case rest of λ where
      (rfl₌ t₁≡u₁) →
        case      ˘⟨ A₁≡A₂ ⟩⊩∷
             t₂  ≡˘⟨ t₁≡t₂ ⟩⊩∷
             t₁  ≡⟨ t₁≡u₁ ⟩⊩∷
             u₁  ≡⟨ u₁≡u₂ ⟩⊩∷∎
             u₂  ∎ of λ
          t₂≡u₂ →
        []-cong s A₁ t₁ u₁ v₁               ⇒*⟨ []-cong⇒*[]-cong₁ ⟩⊩∷
        []-cong s A₁ t₁ u₁ rfl              ⇒⟨ []-cong-β ⊢A₁ ⊢t₁ ⊢u₁ (≅ₜ-eq (escape-⊩≡∷ t₁≡u₁)) ok ⟩⊩∷
        rfl ∷ Id (Erased A₁) [ t₁ ] [ u₁ ]  ≡⟨ refl-⊩≡∷ (⊩rfl′ (⊩[]≡[] t₁≡u₁)) ⟩⊩∷∷⇐* (
                                             ⟨ ⊢Id≡Id′ ⟩⇒
        rfl ∷ Id (Erased A₂) [ t₂ ] [ u₂ ]  ⇐⟨ []-cong-β ⊢A₂ ⊢t₂ ⊢u₂ (≅ₜ-eq (escape-⊩≡∷ t₂≡u₂)) ok
                                             , escape-⊩∷ (⊩rfl′ (⊩[]≡[] t₂≡u₂))
                                             ⟩∷
        []-cong s A₂ t₂ u₂ rfl              ⇐*⟨ []-cong⇒*[]-cong₂ ⟩∎
        []-cong s A₂ t₂ u₂ v₂               ∎)

      (ne v₁′-ne v₂′-ne v₁′~v₂′) →
        []-cong s A₁ t₁ u₁ v₁                                  ⇒*⟨ []-cong⇒*[]-cong₁ ⟩⊩∷
        []-cong s A₁ t₁ u₁ v₁′ ∷ Id (Erased A₁) [ t₁ ] [ u₁ ]  ≡⟨ neutral-⊩≡∷ (⊩Id⇔ .proj₂ (⊩[] ⊩t₁ , ⊩[] ⊩u₁))
                                                                    ([]-congₙ v₁′-ne) ([]-congₙ v₂′-ne)
                                                                    ([]-congⱼ ⊢t₁ ⊢u₁ ⊢v₁′ ok)
                                                                    (conv ([]-congⱼ ⊢t₂ ⊢u₂ (conv ⊢v₂′ ⊢Id≡Id) ok)
                                                                       (sym ⊢Id≡Id′))
                                                                    (~-[]-cong A₁≅A₂ t₁≅t₂ u₁≅u₂ v₁′~v₂′ ok) ⟩⊩∷∷⇐* (
                                                                 ⟨ ⊢Id≡Id′ ⟩⇒
        []-cong s A₂ t₂ u₂ v₂′ ∷ Id (Erased A₂) [ t₂ ] [ u₂ ]  ⇐*⟨ []-cong⇒*[]-cong₂ ⟩∎∷
        []-cong s A₂ t₂ u₂ v₂                                  ∎)
    where
    open E ok

opaque

  -- Reducibility for []-cong.

  ⊩[]-cong :
    (ok : []-cong-allowed s) →
    let open E ok in
    Γ ⊩⟨ l ⟩ v ∷ Id A t u →
    Γ ⊩⟨ l ⟩ []-cong s A t u v ∷ Id (Erased A) [ t ] [ u ]
  ⊩[]-cong ok ⊩v =
    case ⊩∷Id⇔ .proj₁ ⊩v of λ
      (_ , _ , ⊩t , ⊩u , _) →
    wf-⊩≡∷
      (⊩[]-cong≡[]-cong ok (refl-⊩≡ (wf-⊩∷ ⊩t)) (refl-⊩≡∷ ⊩t)
         (refl-⊩≡∷ ⊩u) (refl-⊩≡∷ ⊩v))
      .proj₁

opaque

  -- Validity of []-cong.

  []-congᵛ :
    (ok : []-cong-allowed s) →
    let open E ok in
    Γ ⊩ᵛ⟨ l ⟩ v ∷ Id A t u →
    Γ ⊩ᵛ⟨ l ⟩ []-cong s A t u v ∷ Id (Erased A) [ t ] [ u ]
  []-congᵛ ok ⊩v =
    case ⊩ᵛ∷⇔′ .proj₁ ⊩v of λ
      (⊩Id , ⊩v , v≡v) →
    case ⊩ᵛId⇔ .proj₁ ⊩Id of λ
      (⊩t , ⊩u) →
    ⊩ᵛ∷⇔′ .proj₂
      ( Idᵛ ([]ᵛ ⊩t) ([]ᵛ ⊩u)
      , ⊩[]-cong ok ∘→ ⊩v
      , λ σ₁≡σ₂ →
          ⊩[]-cong≡[]-cong ok
            (⊩ᵛ⇔′ .proj₁ (wf-⊩ᵛ∷ ⊩t) .proj₂ .proj₂ σ₁≡σ₂)
            (⊩ᵛ∷⇔′ .proj₁ ⊩t .proj₂ .proj₂ σ₁≡σ₂)
            (⊩ᵛ∷⇔′ .proj₁ ⊩u .proj₂ .proj₂ σ₁≡σ₂) (v≡v σ₁≡σ₂)
      )
    where
    open E ok

opaque

  -- Validity of equality preservation for []-cong.

  []-cong-congᵛ :
    (ok : []-cong-allowed s) →
    let open E ok in
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l′ ⟩ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊩ᵛ⟨ l″ ⟩ u₁ ≡ u₂ ∷ A₁ →
    Γ ⊩ᵛ⟨ l‴ ⟩ v₁ ≡ v₂ ∷ Id A₁ t₁ u₁ →
    Γ ⊩ᵛ⟨ l ⟩ []-cong s A₁ t₁ u₁ v₁ ≡ []-cong s A₂ t₂ u₂ v₂ ∷
      Id (Erased A₁) [ t₁ ] [ u₁ ]
  []-cong-congᵛ ok A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ =
    case Id-congᵛ A₁≡A₂ t₁≡t₂ u₁≡u₂ of λ
      Id≡Id →
    case ⊩ᵛ≡∷⇔′ .proj₁ (level-⊩ᵛ≡∷ (wf-⊩ᵛ≡ Id≡Id .proj₁) v₁≡v₂) of λ
      (⊩v₁ , ⊩v₂ , v₁≡v₂) →
    ⊩ᵛ≡∷⇔′ .proj₂
      ( []-congᵛ ok ⊩v₁
      , conv-⊩ᵛ∷
          (sym-⊩ᵛ≡ $
           Id-congᵛ (Erased-congᵛ A₁≡A₂) ([]-congᵛ′ t₁≡t₂)
             ([]-congᵛ′ u₁≡u₂))
          ([]-congᵛ ok (conv-⊩ᵛ∷ Id≡Id ⊩v₂))
      , λ σ₁≡σ₂ →
          ⊩[]-cong≡[]-cong ok
            (⊩ᵛ≡⇔′ .proj₁ A₁≡A₂ .proj₂ .proj₂ σ₁≡σ₂)
            (⊩ᵛ≡∷⇔′ .proj₁ t₁≡t₂ .proj₂ .proj₂ σ₁≡σ₂)
            (⊩ᵛ≡∷⇔′ .proj₁ u₁≡u₂ .proj₂ .proj₂ σ₁≡σ₂) (v₁≡v₂ σ₁≡σ₂)
      )
    where
    open E ok

opaque

  -- Validity of the []-cong β rule.

  []-cong-βᵛ :
    (ok : []-cong-allowed s) →
    let open E ok in
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ []-cong s A t t rfl ≡ rfl ∷ Id (Erased A) [ t ] [ t ]
  []-cong-βᵛ {s} {t} {A} ok ⊩t =
    ⊩ᵛ∷-⇐
      (λ ⊩σ →
         case ⊩ᵛ∷⇔′ .proj₁ ⊩t .proj₂ .proj₁ ⊩σ of λ
           ⊩t[σ] →
         case escape-⊩∷ ⊩t[σ] of λ
           ⊢t[σ] →
         []-cong-β (escape (wf-⊩∷ ⊩t[σ])) ⊢t[σ] ⊢t[σ] (refl ⊢t[σ]) ok)
      (rflᵛ ([]ᵛ ⊩t))
      .proj₂
    where
    open E ok

------------------------------------------------------------------------
-- The K rule

private opaque

  -- A variant of K-subst for _⊢_⇒*_∷_.

  K-subst*′ :
    Γ ∙ Id A t t ⊩ᵛ⟨ l ⟩ B →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊢ u ∷ B U.[ σ ⇑ ] [ rfl ]₀ →
    Δ ⊢ v₁ ⇒* v₂ ∷ Id A t t U.[ σ ] →
    Δ ⊩⟨ l′ ⟩ v₂ ∷ Id A t t U.[ σ ] →
    K-allowed →
    Δ ⊢ K p (A U.[ σ ]) (t U.[ σ ]) (B U.[ σ ⇑ ]) u v₁ ⇒*
      K p (A U.[ σ ]) (t U.[ σ ]) (B U.[ σ ⇑ ]) u v₂ ∷
      B U.[ σ ⇑ ] [ v₁ ]₀
  K-subst*′ {A} {t} {B} {σ} {u} {v₁} {v₂} {p} ⊩B ⊩σ ⊢u v₁⇒*v₂ ⊩v₂ ok =
    case ⊩ᵛId⇔ .proj₁ $ wf-∙-⊩ᵛ ⊩B .proj₂ of λ
      (⊩t , _) →
    case ⊩ᵛ∷⇔′ .proj₁ ⊩t .proj₂ .proj₁ ⊩σ of λ
      ⊩t[σ] →
    case escape-⊩∷ ⊩t[σ] of λ
      ⊢t[σ] →
    case escape $ ⊩ᵛ→⊩ˢ∷→⊩[⇑] ⊩B ⊩σ of λ
      ⊢B[σ⇑] →
    case v₁⇒*v₂ of λ where
      (id ⊢v₁)                     → id (Kⱼ ⊢t[σ] ⊢B[σ⇑] ⊢u ⊢v₁ ok)
      (_⇨_ {t′ = v₃} v₁⇒v₃ v₃⇒*v₂) →
        case
          v₁  ⇒⟨ v₁⇒v₃ ⟩⊩∷
          v₃  ∎⟨ ⊩∷-⇐* v₃⇒*v₂ ⊩v₂ .proj₁ ⟩⊩∷
        of λ
          v₁≡v₃ →
        K p (A U.[ σ ]) (t U.[ σ ]) (B U.[ σ ⇑ ]) u v₁
          ∷ B U.[ σ ⇑ ] [ v₁ ]₀                         ⇒⟨ K-subst (escape (wf-⊩∷ ⊩t[σ])) ⊢t[σ] ⊢B[σ⇑] ⊢u v₁⇒v₃ ok ⟩∷
                                                         ⟨ ≅-eq $ escape-⊩≡ $
                                                           ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀
                                                             (refl-⊩ᵛ≡ ⊩B) (refl-⊩ˢ≡∷ ⊩σ) v₁≡v₃ ⟩⇒
        K p (A U.[ σ ]) (t U.[ σ ]) (B U.[ σ ⇑ ]) u v₃
          ∷ B U.[ σ ⇑ ] [ v₃ ]₀                         ⇒*⟨ K-subst*′ ⊩B ⊩σ ⊢u v₃⇒*v₂ ⊩v₂ ok ⟩∎∷

        K p (A U.[ σ ]) (t U.[ σ ]) (B U.[ σ ⇑ ]) u v₂  ∎

opaque

  -- A variant of K-subst for _⊢_⇒*_∷_.

  K-subst* :
    Γ ∙ Id A t t ⊩ᵛ⟨ l ⟩ B →
    Γ ⊢ u ∷ B [ rfl ]₀ →
    Γ ⊢ v₁ ⇒* v₂ ∷ Id A t t →
    Γ ⊩⟨ l′ ⟩ v₂ ∷ Id A t t →
    K-allowed →
    Γ ⊢ K p A t B u v₁ ⇒* K p A t B u v₂ ∷ B [ v₁ ]₀
  K-subst* {B} ⊩B ⊢u v₁⇒*v₂ ⊩v₂ ok =
    PE.subst₃ (_⊢_⇒*_∷_ _)
      (PE.cong₅ (K _) (subst-id _) (subst-id _) ([idSubst⇑ⁿ]≡ 1) PE.refl
         PE.refl)
      (PE.cong₅ (K _) (subst-id _) (subst-id _) ([idSubst⇑ⁿ]≡ 1) PE.refl
         PE.refl)
      lemma $
    K-subst*′ ⊩B (⊩ˢ∷-idSubst (wf-⊩ᵛ (wf-∙-⊩ᵛ ⊩B .proj₂)))
      (PE.subst (_⊢_∷_ _ _) (PE.sym lemma) ⊢u)
      (PE.subst (_⊢_⇒*_∷_ _ _ _) (PE.sym $ subst-id _) v₁⇒*v₂)
      (PE.subst (_⊩⟨_⟩_∷_ _ _ _) (PE.sym $ subst-id _) ⊩v₂) ok
    where
    lemma : B U.[ idSubst ⇑ ] [ t ]₀ PE.≡ B [ t ]₀
    lemma = PE.cong _[ _ ]₀ ([idSubst⇑ⁿ]≡ 1 {t = B})

opaque

  -- Reducibility of equality between applications of K.

  ⊩K≡K :
    K-allowed →
    Γ ⊩ᵛ⟨ l′ ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l″ ⟩ t₁ ≡ t₂ ∷ A₁ →
    Γ ∙ Id A₁ t₁ t₁ ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    Γ ⊩ᵛ⟨ l‴ ⟩ u₁ ≡ u₂ ∷ B₁ [ rfl ]₀ →
    Γ ⊩ᵛ⟨ l⁗ ⟩ v₁ ≡ v₂ ∷ Id A₁ t₁ t₁ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l ⟩ K p A₁ t₁ B₁ u₁ v₁ U.[ σ₁ ] ≡ K p A₂ t₂ B₂ u₂ v₂ U.[ σ₂ ] ∷
      B₁ [ v₁ ]₀ U.[ σ₁ ]
  ⊩K≡K
    {A₁} {A₂} {t₁} {t₂} {B₁} {B₂} {u₁} {u₂} {v₁} {v₂} {σ₁} {σ₂} {p}
    ok A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ σ₁≡σ₂ =

    -- Some definitions related to σ₁ and σ₂.
    case wf-⊩ˢ≡∷ σ₁≡σ₂ of λ
      (⊩σ₁ , ⊩σ₂) →

    -- Some definitions related to Id.
    case Id-congᵛ A₁≡A₂ t₁≡t₂ t₁≡t₂ of λ
      Id≡Id →
    case ⊩ᵛ≡⇔′ .proj₁ Id≡Id .proj₂ .proj₂ σ₁≡σ₂ of λ
      Id[σ₁]≡Id[σ₂] →
    case ≅-eq $ escape-⊩≡ Id[σ₁]≡Id[σ₂] of λ
      ⊢Id[σ₁]≡Id[σ₂] →

    -- Some definitions related to t₁ and t₂.
    case wf-⊩ᵛ≡∷ t₁≡t₂ of λ
      (⊩t₁ , ⊩t₂) →
    case conv-⊩ᵛ∷ A₁≡A₂ ⊩t₂ of λ
      ⊩t₂ →
    case escape-⊩∷ $ ⊩ᵛ∷⇔′ .proj₁ ⊩t₁ .proj₂ .proj₁ ⊩σ₁ of λ
      ⊢t₁[σ₁] →
    case escape-⊩∷ $ ⊩ᵛ∷⇔′ .proj₁ ⊩t₂ .proj₂ .proj₁ ⊩σ₂ of λ
      ⊢t₂[σ₂] →

    -- Some definitions related to B₁ and B₂.
    case wf-⊩ᵛ≡ B₁≡B₂ of λ
      (⊩B₁ , ⊩B₂) →
    case conv-∙-⊩ᵛ Id≡Id ⊩B₂ of λ
      ⊩B₂ →
    case escape $ ⊩ᵛ→⊩ˢ∷→⊩[⇑] ⊩B₁ ⊩σ₁ of λ
      ⊢B₁[σ₁⇑] →
    case escape $ ⊩ᵛ→⊩ˢ∷→⊩[⇑] ⊩B₂ ⊩σ₂ of λ
      ⊢B₂[σ₂⇑] →

    -- Some definitions related to u₁ and u₂.
    case wf-⊩ᵛ≡∷ u₁≡u₂ of λ
      (⊩u₁ , ⊩u₂) →
    case conv-⊩ᵛ∷ (⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀ B₁≡B₂ (refl-⊩ᵛ≡∷ (rflᵛ ⊩t₁)))
           ⊩u₂ of λ
      ⊩u₂ →
    case PE.subst (_⊢_∷_ _ _) (singleSubstLift B₁ _) $
         escape-⊩∷ $ ⊩ᵛ∷⇔′ .proj₁ ⊩u₁ .proj₂ .proj₁ ⊩σ₁ of λ
      ⊢u₁[σ₁] →
    case PE.subst (_⊢_∷_ _ _) (singleSubstLift B₂ _) $
         escape-⊩∷ $ ⊩ᵛ∷⇔′ .proj₁ ⊩u₂ .proj₂ .proj₁ ⊩σ₂ of λ
      ⊢u₂[σ₂] →
    case PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (singleSubstLift B₁ _) $
         ⊩ᵛ≡∷⇔′ .proj₁
           (level-⊩ᵛ≡∷ (⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ ⊩B₁ (rflᵛ ⊩t₁)) u₁≡u₂)
           .proj₂ .proj₂ σ₁≡σ₂ of λ
      u₁[σ₁]≡u₂[σ₂] →

    -- Some definitions related to v₁ and v₂.
    case wf-⊩ᵛ≡∷ v₁≡v₂ of λ
      (⊩v₁ , ⊩v₂) →
    case conv-⊩ᵛ∷ Id≡Id ⊩v₂ of λ
      ⊩v₂ →
    case ⊩ᵛ≡∷⇔′ .proj₁ v₁≡v₂ .proj₂ .proj₂ σ₁≡σ₂ of λ
      v₁[σ₁]≡v₂[σ₂] →
    case ⊩≡∷Id⇔ .proj₁ v₁[σ₁]≡v₂[σ₂] of λ
      (v₁′ , v₂′ , v₁[σ₁]⇒*v₁′@([ _ , ⊢v₁′ , _ ]) , v₂[σ₂]⇒*v₂′ ,
       _ , _ , rest) →
    case convRed:*: v₂[σ₂]⇒*v₂′ ⊢Id[σ₁]≡Id[σ₂] of λ
      v₂[σ₂]⇒*v₂′@([ _ , ⊢v₂′ , _ ]) →

    -- Some definitions related to v₁′ and v₂′.
    case ⊩∷-⇒* v₁[σ₁]⇒*v₁′ $ ⊩ᵛ∷⇔′ .proj₁ ⊩v₁ .proj₂ .proj₁ ⊩σ₁ of λ
      (⊩v₁′ , v₁[σ₁]≡v₁′) →
    case ⊩∷-⇒* v₂[σ₂]⇒*v₂′ $ ⊩ᵛ∷⇔′ .proj₁ ⊩v₂ .proj₂ .proj₁ ⊩σ₂ of λ
      (⊩v₂′ , v₂[σ₂]≡v₂′) →
    case ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ B₁≡B₂ σ₁≡σ₂
           (v₁′                                 ≡˘⟨ v₁[σ₁]≡v₁′ ⟩⊩∷
            v₁ U.[ σ₁ ] ∷ Id A₁ t₁ t₁ U.[ σ₁ ]  ≡⟨ v₁[σ₁]≡v₂[σ₂] ⟩⊩∷∷
                                                 ⟨ Id[σ₁]≡Id[σ₂] ⟩⊩∷
            v₂ U.[ σ₂ ] ∷ Id A₂ t₂ t₂ U.[ σ₂ ]  ≡⟨ v₂[σ₂]≡v₂′ ⟩⊩∷∎∷
            v₂′                                 ∎) of λ
      B₁[σ₁⇑][v₁′]₀≡B₂[σ₂⇑][v₂′]₀ →
    case ≅-eq $ escape-⊩≡ B₁[σ₁⇑][v₁′]₀≡B₂[σ₂⇑][v₂′]₀ of λ
      ⊢B₁[σ₁⇑][v₁′]₀≡B₂[σ₂⇑][v₂′]₀ →

    -- The two applications of K are equal if applications of K to v₁′
    -- and v₂′ are equal.
    case
      (λ hyp →
         K p (A₁ U.[ σ₁ ]) (t₁ U.[ σ₁ ]) (B₁ U.[ σ₁ ⇑ ]) (u₁ U.[ σ₁ ])
           (v₁ U.[ σ₁ ]) ∷ B₁ [ v₁ ]₀ U.[ σ₁ ]                          ≡⟨⟩⊩∷∷
                                                                         ⟨ singleSubstLift B₁ _ ⟩⊩∷≡
         _               ∷ B₁ U.[ σ₁ ⇑ ] [ v₁ U.[ σ₁ ] ]₀               ⇒*⟨ K-subst*′ ⊩B₁ ⊩σ₁ ⊢u₁[σ₁] (redₜ v₁[σ₁]⇒*v₁′) ⊩v₁′ ok ⟩⊩∷∷
                                                                          ⟨ ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀
                                                                              (refl-⊩ᵛ≡ ⊩B₁) (refl-⊩ˢ≡∷ ⊩σ₁) v₁[σ₁]≡v₁′ ⟩⊩∷
         K p (A₁ U.[ σ₁ ]) (t₁ U.[ σ₁ ]) (B₁ U.[ σ₁ ⇑ ]) (u₁ U.[ σ₁ ])
           v₁′ ∷ B₁ U.[ σ₁ ⇑ ] [ v₁′ ]₀                                 ≡⟨ hyp ⟩⊩∷∷⇐*
                                                                         ⟨ ⊢B₁[σ₁⇑][v₁′]₀≡B₂[σ₂⇑][v₂′]₀ ⟩⇒
               ∷ B₂ U.[ σ₂ ⇑ ] [ v₂′ ]₀                                 ˘⟨ ≅-eq $ escape-⊩≡ $
                                                                           ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀
                                                                             (refl-⊩ᵛ≡ ⊩B₂) (refl-⊩ˢ≡∷ ⊩σ₂) v₂[σ₂]≡v₂′ ⟩⇒
         K p (A₂ U.[ σ₂ ]) (t₂ U.[ σ₂ ]) (B₂ U.[ σ₂ ⇑ ]) (u₂ U.[ σ₂ ])
           v₂′ ∷ B₂ U.[ σ₂ ⇑ ] [ v₂ U.[ σ₂ ] ]₀                         ⇐*⟨ K-subst*′ ⊩B₂ ⊩σ₂ ⊢u₂[σ₂] (redₜ v₂[σ₂]⇒*v₂′) ⊩v₂′ ok ⟩∎∷

         K p (A₂ U.[ σ₂ ]) (t₂ U.[ σ₂ ]) (B₂ U.[ σ₂ ⇑ ]) (u₂ U.[ σ₂ ])
           (v₂ U.[ σ₂ ])                                                ∎)
    of λ
      lemma →

    case rest of λ where
      (rfl₌ _) →
        -- If v₁′ and v₂′ are both rfl, then one can conclude by using
        -- the β-rule for K and the fact that u₁ [σ₁] is equal to
        -- u₂ [σ₂].
        lemma
          (K p A₁ t₁ B₁ u₁ rfl U.[ σ₁ ]          ⇒⟨ K-β ⊢t₁[σ₁] ⊢B₁[σ₁⇑] ⊢u₁[σ₁] ok ⟩⊩∷
           u₁ U.[ σ₁ ] ∷ B₁ U.[ σ₁ ⇑ ] [ rfl ]₀  ≡⟨ u₁[σ₁]≡u₂[σ₂] ⟩⊩∷∷⇐*
                                                  ⟨ ⊢B₁[σ₁⇑][v₁′]₀≡B₂[σ₂⇑][v₂′]₀ ⟩⇒
           u₂ U.[ σ₂ ] ∷ B₂ U.[ σ₂ ⇑ ] [ rfl ]₀  ⇐⟨ K-β ⊢t₂[σ₂] ⊢B₂[σ₂⇑] ⊢u₂[σ₂] ok , ⊢u₂[σ₂] ⟩∎∷
           K p A₂ t₂ B₂ u₂ rfl U.[ σ₂ ]          ∎)

      (ne v₁′-ne v₂′-ne v₁′~v₂′) →
        -- If v₁′ and v₂′ are equal neutral terms, then one can
        -- conclude by using the fact that the applications of K to
        -- v₁′ and v₂′ are equal neutral terms.
        lemma $
        neutral-⊩≡∷
          (wf-⊩≡ B₁[σ₁⇑][v₁′]₀≡B₂[σ₂⇑][v₂′]₀ .proj₁) (Kₙ v₁′-ne)
          (Kₙ v₂′-ne) (Kⱼ ⊢t₁[σ₁] ⊢B₁[σ₁⇑] ⊢u₁[σ₁] ⊢v₁′ ok)
          (conv (Kⱼ ⊢t₂[σ₂] ⊢B₂[σ₂⇑] ⊢u₂[σ₂] ⊢v₂′ ok)
             (sym ⊢B₁[σ₁⇑][v₁′]₀≡B₂[σ₂⇑][v₂′]₀)) $
        ~-K (escape-⊩≡ $ ⊩ᵛ≡⇔′ .proj₁ A₁≡A₂ .proj₂ .proj₂ σ₁≡σ₂) ⊢t₁[σ₁]
          (escape-⊩≡∷ $ ⊩ᵛ≡∷⇔′ .proj₁ t₁≡t₂ .proj₂ .proj₂ σ₁≡σ₂)
          (escape-⊩≡ $ ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑]≡[⇑] B₁≡B₂ σ₁≡σ₂)
          (escape-⊩≡∷ u₁[σ₁]≡u₂[σ₂]) v₁′~v₂′ ok

opaque

  -- Reducibility for K.

  ⊩K :
    K-allowed →
    Γ ∙ Id A t t ⊩ᵛ⟨ l ⟩ B →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ B [ rfl ]₀ →
    Γ ⊩ᵛ⟨ l″ ⟩ v ∷ Id A t t →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l ⟩ K p A t B u v U.[ σ ] ∷ B [ v ]₀ U.[ σ ]
  ⊩K ok ⊩B ⊩u ⊩v ⊩σ =
    case ⊩ᵛId⇔ .proj₁ $ wf-⊩ᵛ∷ ⊩v of λ
      (⊩t , _) →
    case wf-⊩ᵛ∷ ⊩t of λ
      ⊩A →
    wf-⊩≡∷
      (⊩K≡K ok (refl-⊩ᵛ≡ ⊩A) (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ᵛ≡ ⊩B) (refl-⊩ᵛ≡∷ ⊩u)
         (refl-⊩ᵛ≡∷ ⊩v) (refl-⊩ˢ≡∷ ⊩σ))
      .proj₁

opaque

  -- Validity of K.

  Kᵛ :
    K-allowed →
    Γ ∙ Id A t t ⊩ᵛ⟨ l ⟩ B →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ B [ rfl ]₀ →
    Γ ⊩ᵛ⟨ l″ ⟩ v ∷ Id A t t →
    Γ ⊩ᵛ⟨ l ⟩ K p A t B u v ∷ B [ v ]₀
  Kᵛ ok ⊩B ⊩u ⊩v =
    case ⊩ᵛId⇔ .proj₁ $ wf-⊩ᵛ∷ ⊩v of λ
      (⊩t , _) →
    case wf-⊩ᵛ∷ ⊩t of λ
      ⊩A →
    ⊩ᵛ∷⇔′ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ ⊩B ⊩v
      , ⊩K ok ⊩B ⊩u ⊩v
      , ⊩K≡K ok (refl-⊩ᵛ≡ ⊩A) (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ᵛ≡ ⊩B)
          (refl-⊩ᵛ≡∷ ⊩u) (refl-⊩ᵛ≡∷ ⊩v)
      )

opaque

  -- Validity of equality preservation for K.

  K-congᵛ :
    K-allowed →
    Γ ⊩ᵛ⟨ l′ ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l″ ⟩ t₁ ≡ t₂ ∷ A₁ →
    Γ ∙ Id A₁ t₁ t₁ ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    Γ ⊩ᵛ⟨ l‴ ⟩ u₁ ≡ u₂ ∷ B₁ [ rfl ]₀ →
    Γ ⊩ᵛ⟨ l⁗ ⟩ v₁ ≡ v₂ ∷ Id A₁ t₁ t₁ →
    Γ ⊩ᵛ⟨ l ⟩ K p A₁ t₁ B₁ u₁ v₁ ≡ K p A₂ t₂ B₂ u₂ v₂ ∷ B₁ [ v₁ ]₀
  K-congᵛ ok A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ =
    case wf-⊩ᵛ≡∷ t₁≡t₂ of λ
      (⊩t₁ , _) →
    case wf-⊩ᵛ≡ B₁≡B₂ of λ
      (⊩B₁ , ⊩B₂) →
    case wf-⊩ᵛ≡∷ u₁≡u₂ of λ
      (⊩u₁ , ⊩u₂) →
    case wf-⊩ᵛ≡∷ v₁≡v₂ of λ
      (⊩v₁ , ⊩v₂) →
    case Id-congᵛ A₁≡A₂ t₁≡t₂ t₁≡t₂ of λ
      Id≡Id →
    ⊩ᵛ≡∷⇔′ .proj₂
      ( Kᵛ ok ⊩B₁ ⊩u₁ ⊩v₁
      , conv-⊩ᵛ∷ (sym-⊩ᵛ≡ (⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀ B₁≡B₂ v₁≡v₂))
          (Kᵛ ok (conv-∙-⊩ᵛ Id≡Id ⊩B₂)
             (conv-⊩ᵛ∷ (⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀ B₁≡B₂ (refl-⊩ᵛ≡∷ (rflᵛ ⊩t₁)))
                ⊩u₂)
             (conv-⊩ᵛ∷ Id≡Id ⊩v₂))
      , ⊩K≡K ok A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂
      )

opaque

  -- Validity of the K β rule.

  K-βᵛ :
    K-allowed →
    Γ ∙ Id A t t ⊩ᵛ⟨ l′ ⟩ B →
    Γ ⊩ᵛ⟨ l ⟩ u ∷ B [ rfl ]₀ →
    Γ ⊩ᵛ⟨ l ⟩ K p A t B u rfl ≡ u ∷ B [ rfl ]₀
  K-βᵛ {B} ok ⊩B ⊩u =
    case ⊩ᵛId⇔ .proj₁ $ wf-∙-⊩ᵛ ⊩B .proj₂ of λ
      (⊩t , _) →
    ⊩ᵛ∷-⇐
      (λ ⊩σ →
         PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift B _) $
         K-β (escape-⊩∷ $ ⊩ᵛ∷⇔′ .proj₁ ⊩t .proj₂ .proj₁ ⊩σ)
           (escape $ ⊩ᵛ→⊩ˢ∷→⊩[⇑] ⊩B ⊩σ)
           (PE.subst (_⊢_∷_ _ _) (singleSubstLift B _) $
            escape-⊩∷ $ ⊩ᵛ∷⇔′ .proj₁ ⊩u .proj₂ .proj₁ ⊩σ)
           ok)
      ⊩u
      .proj₂

------------------------------------------------------------------------
-- The J rule

private opaque

  -- A lemma used below.

  Id[]≡Id-wk1-0-[⇑][]₀ :
    ∀ A t →
    Id (A U.[ σ ]) (t U.[ σ ]) u PE.≡
    Id (wk1 A) (wk1 t) (var x0) U.[ σ ⇑ ] [ u ]₀
  Id[]≡Id-wk1-0-[⇑][]₀ {σ} {u} A t =
    Id (A U.[ σ ]) (t U.[ σ ]) u                            ≡⟨ ≡Id-wk1-wk1-0[]₀ ⟩
    Id (wk1 (A U.[ σ ]) [ u ]₀) (wk1 (t U.[ σ ]) [ u ]₀) u  ≡⟨⟩
    Id (wk1 (A U.[ σ ])) (wk1 (t U.[ σ ])) (var x0) [ u ]₀  ≡˘⟨ PE.cong _[ u ]₀ $ Id-wk1-wk1-0[⇑]≡ A t ⟩
    Id (wk1 A) (wk1 t) (var x0) U.[ σ ⇑ ] [ u ]₀            ∎
    where
    open Tools.Reasoning.PropositionalEquality

private opaque

  -- A variant of J-subst for _⊢_⇒*_∷_.

  J-subst*′ :
    Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊩ᵛ⟨ l ⟩ B →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊢ u ∷ B U.[ σ ⇑ ⇑ ] [ t U.[ σ ] , rfl ]₁₀ →
    Δ ⊩⟨ l′ ⟩ v ∷ A U.[ σ ] →
    Δ ⊢ w₁ ⇒* w₂ ∷ Id (A U.[ σ ]) (t U.[ σ ]) v →
    Δ ⊩⟨ l″ ⟩ w₂ ∷ Id (A U.[ σ ]) (t U.[ σ ]) v →
    Δ ⊢ J p q (A U.[ σ ]) (t U.[ σ ]) (B U.[ σ ⇑ ⇑ ]) u v w₁ ⇒*
      J p q (A U.[ σ ]) (t U.[ σ ]) (B U.[ σ ⇑ ⇑ ]) u v w₂ ∷
      B U.[ σ ⇑ ⇑ ] [ v , w₁ ]₁₀
  J-subst*′
    {A} {t} {B} {σ} {u} {v} {w₁} {w₂} {p} {q} ⊩B ⊩σ ⊢u ⊩v w₁⇒*w₂ ⊩w₂ =
    case ⊩Id⇔ .proj₁ (wf-⊩∷ ⊩w₂) .proj₁ of λ
      ⊩t[σ] →
    case escape-⊩∷ ⊩t[σ] of λ
      ⊢t[σ] →
    case escape (wf-⊩∷ ⊩t[σ]) of λ
      ⊢A[σ] →
    case escape-⊩∷ ⊩v of λ
      ⊢v →
    case escape $
         PE.subst₃ _⊩⟨_⟩_
           (PE.cong (_∙_ _) $
            PE.cong₃ Id (wk1-liftSubst A) (wk1-liftSubst t) PE.refl)
           PE.refl PE.refl $
         ⊩ᵛ→⊩ˢ∷→⊩[⇑⇑] ⊩B ⊩σ of λ
      ⊢B[σ⇑⇑] →
    case w₁⇒*w₂ of λ where
      (id ⊢w₁) →
        id (Jⱼ ⊢A[σ] ⊢t[σ] ⊢B[σ⇑⇑] ⊢u ⊢v ⊢w₁)
      (_⇨_ {t′ = w₃} w₁⇒w₃ w₃⇒*w₂) →
        case
          w₁  ⇒⟨ w₁⇒w₃ ⟩⊩∷
          w₃  ∎⟨ ⊩∷-⇐* w₃⇒*w₂ ⊩w₂ .proj₁ ⟩⊩∷
        of λ
          w₁≡w₃ →
        J p q (A U.[ σ ]) (t U.[ σ ]) (B U.[ σ ⇑ ⇑ ]) u v w₁
          ∷ B U.[ σ ⇑ ⇑ ] [ v , w₁ ]₁₀                        ⇒⟨ J-subst ⊢A[σ] ⊢t[σ] ⊢B[σ⇑⇑] ⊢u ⊢v w₁⇒w₃ ⟩∷
                                                               ⟨ ≅-eq $ escape-⊩≡ $
                                                                 ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀
                                                                   (refl-⊩ᵛ≡ ⊩B) (refl-⊩ˢ≡∷ ⊩σ) (refl-⊩≡∷ ⊩v)
                                                                   (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (Id[]≡Id-wk1-0-[⇑][]₀ A t) w₁≡w₃) ⟩⇒
        J p q (A U.[ σ ]) (t U.[ σ ]) (B U.[ σ ⇑ ⇑ ]) u v w₃
          ∷ B U.[ σ ⇑ ⇑ ] [ v , w₃ ]₁₀                        ⇒*⟨ J-subst*′ ⊩B ⊩σ ⊢u ⊩v w₃⇒*w₂ ⊩w₂ ⟩∎∷

        J p q (A U.[ σ ]) (t U.[ σ ]) (B U.[ σ ⇑ ⇑ ]) u v w₂  ∎

opaque

  -- A variant of J-subst for _⊢_⇒*_∷_.

  J-subst* :
    Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊩ᵛ⟨ l ⟩ B →
    Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
    Γ ⊩⟨ l′ ⟩ v ∷ A →
    Γ ⊢ w₁ ⇒* w₂ ∷ Id A t v →
    Γ ⊩⟨ l″ ⟩ w₂ ∷ Id A t v →
    Γ ⊢ J p q A t B u v w₁ ⇒* J p q A t B u v w₂ ∷ B [ v , w₁ ]₁₀
  J-subst* {B} ⊩B ⊢u ⊩v w₁⇒*w₂ ⊩w₂ =
    PE.subst₃ (_⊢_⇒*_∷_ _)
      (PE.cong₆ (J _ _) (subst-id _) (subst-id _) ([idSubst⇑ⁿ]≡ 2)
         PE.refl (subst-id _) PE.refl)
      (PE.cong₆ (J _ _) (subst-id _) (subst-id _) ([idSubst⇑ⁿ]≡ 2)
         PE.refl (subst-id _) PE.refl)
      lemma $
    J-subst*′ ⊩B
      (⊩ˢ∷-idSubst (wf-⊩ᵛ (wf-∙-⊩ᵛ (wf-∙-⊩ᵛ ⊩B .proj₂) .proj₂)))
      (PE.subst (_⊢_∷_ _ _) (PE.sym lemma) ⊢u)
      (PE.subst₂ (_⊩⟨_⟩_∷_ _ _) (PE.sym $ subst-id _)
         (PE.sym $ subst-id _) ⊩v)
      (PE.subst (_⊢_⇒*_∷_ _ _ _) (PE.sym $ subst-id _) w₁⇒*w₂)
      (PE.subst (_⊩⟨_⟩_∷_ _ _ _) (PE.sym $ subst-id _) ⊩w₂)
    where
    lemma :
      B U.[ idSubst ⇑ ⇑ ] [ t U.[ idSubst ] , u ]₁₀ PE.≡ B [ t , u ]₁₀
    lemma = PE.cong₂ _[_, _ ]₁₀ ([idSubst⇑ⁿ]≡ 2 {t = B}) (subst-id _)

opaque

  -- Reducibility of equality between applications of J.

  ⊩J≡J :
    Γ ⊩ᵛ⟨ l′₁ ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l′₂ ⟩ t₁ ≡ t₂ ∷ A₁ →
    Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    Γ ⊩ᵛ⟨ l′₃ ⟩ u₁ ≡ u₂ ∷ B₁ [ t₁ , rfl ]₁₀ →
    Γ ⊩ᵛ⟨ l′₄ ⟩ v₁ ≡ v₂ ∷ A₁ →
    Γ ⊩ᵛ⟨ l′₅ ⟩ w₁ ≡ w₂ ∷ Id A₁ t₁ v₁ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l ⟩ J p q A₁ t₁ B₁ u₁ v₁ w₁ U.[ σ₁ ] ≡
      J p q A₂ t₂ B₂ u₂ v₂ w₂ U.[ σ₂ ] ∷ B₁ [ v₁ , w₁ ]₁₀ U.[ σ₁ ]
  ⊩J≡J
    {A₁} {A₂} {t₁} {t₂} {B₁} {B₂} {u₁} {u₂} {v₁} {v₂} {w₁} {w₂} {σ₁}
    {σ₂} {p} {q} A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂ σ₁≡σ₂ =

    -- Some definitions related to σ₁ and σ₂.
    case wf-⊩ˢ≡∷ σ₁≡σ₂ of λ
      (⊩σ₁ , ⊩σ₂) →

    -- Some definitions related to A₁ and A₂.
    case wf-⊩ᵛ≡ A₁≡A₂ of λ
      (⊩A₁ , ⊩A₂) →
    case ⊩ᵛ≡⇔′ .proj₁ A₁≡A₂ .proj₂ .proj₂ σ₁≡σ₂ of λ
      A₁[σ₁]≡A₂[σ₂] →
    case escape $ ⊩ᵛ⇔′ .proj₁ ⊩A₁ .proj₂ .proj₁ ⊩σ₁ of λ
      ⊢A₁[σ₁] →
    case escape $ ⊩ᵛ⇔′ .proj₁ ⊩A₂ .proj₂ .proj₁ ⊩σ₂ of λ
      ⊢A₂[σ₂] →

    -- Some definitions related to t₁ and t₂.
    case ⊩ᵛ≡∷⇔′ .proj₁ t₁≡t₂ .proj₂ .proj₂ σ₁≡σ₂ of λ
      t₁[σ₁]≡t₂[σ₂] →
    case wf-⊩≡∷ t₁[σ₁]≡t₂[σ₂] of λ
      (⊩t₁[σ₁] , ⊩t₂[σ₂]) →
    case conv-⊩∷ A₁[σ₁]≡A₂[σ₂] ⊩t₂[σ₂] of λ
      ⊩t₂[σ₂] →
    case escape-⊩∷ ⊩t₁[σ₁] of λ
      ⊢t₁[σ₁] →
    case escape-⊩∷ ⊩t₂[σ₂] of λ
      ⊢t₂[σ₂] →
    case refl-⊩≡∷ $
         PE.subst (_⊩⟨_⟩_∷_ _ _ _) (Id[]≡Id-wk1-0-[⇑][]₀ A₁ t₁) $
         ⊩rfl ⊩t₁[σ₁] of λ
      rfl≡rfl →

    -- Some definitions related to Id.
    case Id-congᵛ A₁≡A₂ t₁≡t₂ v₁≡v₂ of λ
      Id-v₁≡Id-v₂ →
    case ⊩ᵛ≡⇔′ .proj₁ Id-v₁≡Id-v₂ .proj₂ .proj₂ σ₁≡σ₂ of λ
      Id-v₁[σ₁]≡Id-v₂[σ₂] →

    -- Some definitions related to B₁ and B₂.
    case wf-⊩ᵛ≡ B₁≡B₂ of λ
      (⊩B₁ , ⊩B₂) →
    case conv-∙∙-⊩ᵛ A₁≡A₂
           (Id-congᵛ (wk1-⊩ᵛ≡ ⊩A₁ A₁≡A₂) (wk1-⊩ᵛ≡∷ ⊩A₁ t₁≡t₂)
              (refl-⊩ᵛ≡∷ (varᵛ′ here (wk1-⊩ᵛ ⊩A₁ ⊩A₁))))
           ⊩B₂ of λ
      ⊩B₂ →
    case PE.subst₄ _⊩⟨_⟩_≡_ (PE.cong (_∙_ _) $ Id-wk1-wk1-0[⇑]≡ A₁ t₁)
           PE.refl PE.refl PE.refl $
         ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑] B₁≡B₂ σ₁≡σ₂ of λ
      B₁[σ₁⇑⇑]≡B₂[σ₂⇑⇑] →
    case escape $ wf-⊩≡ B₁[σ₁⇑⇑]≡B₂[σ₂⇑⇑] .proj₁ of λ
      ⊢B₁[σ₁⇑⇑] →
    case PE.subst₂ _⊢_
           (PE.cong (_∙_ _) $ Id-wk1-wk1-0[⇑]≡ A₂ t₂) PE.refl $
         escape $ ⊩ᵛ→⊩ˢ∷→⊩[⇑⇑] ⊩B₂ ⊩σ₂ of λ
      ⊢B₂[σ₂⇑⇑] →
    case ≅-eq $ escape-⊩≡ $
         ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀ B₁≡B₂ σ₁≡σ₂ t₁[σ₁]≡t₂[σ₂]
           rfl≡rfl of λ
      ⊢B₁[σ₁⇑⇑][t₁[σ₁],rfl]≡B₂[σ₂⇑⇑][t₂[σ₂],rfl] →

    -- Some definitions related to u₁ and u₂.
    case PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) ([,]-[]-commute B₁) $
         ⊩ᵛ≡∷⇔′ .proj₁ u₁≡u₂ .proj₂ .proj₂ σ₁≡σ₂ of λ
      u₁[σ₁]≡u₂[σ₂] →
    case escape-⊩∷ $ wf-⊩≡∷ u₁[σ₁]≡u₂[σ₂] .proj₁ of λ
      ⊢u₁[σ₁] →
    case _⊢_∷_.conv (escape-⊩∷ $ wf-⊩≡∷ u₁[σ₁]≡u₂[σ₂] .proj₂)
           ⊢B₁[σ₁⇑⇑][t₁[σ₁],rfl]≡B₂[σ₂⇑⇑][t₂[σ₂],rfl] of λ
      ⊢u₂[σ₂] →

    -- Some definitions related to v₁ and v₂.
    case ⊩ᵛ≡∷⇔′ .proj₁ v₁≡v₂ .proj₂ .proj₂ σ₁≡σ₂ of λ
      v₁[σ₁]≡v₂[σ₂] →
    case wf-⊩≡∷ v₁[σ₁]≡v₂[σ₂] of λ
      (⊩v₁[σ₁] , ⊩v₂[σ₂]) →
    case conv-⊩∷ A₁[σ₁]≡A₂[σ₂] ⊩v₂[σ₂] of λ
      ⊩v₂[σ₂] →
    case escape-⊩∷ ⊩v₁[σ₁] of λ
      ⊢v₁[σ₁] →
    case escape-⊩∷ ⊩v₂[σ₂] of λ
      ⊢v₂[σ₂] →

    -- Some definitions related to w₁ and w₂.
    case wf-⊩ᵛ≡∷ w₁≡w₂ of λ
      (⊩w₁ , ⊩w₂) →
    case conv-⊩ᵛ∷ Id-v₁≡Id-v₂ ⊩w₂ of λ
      ⊩w₂ →
    case ⊩ᵛ≡∷⇔′ .proj₁ w₁≡w₂ .proj₂ .proj₂ σ₁≡σ₂ of λ
      w₁[σ₁]≡w₂[σ₂] →
    case ⊩≡∷Id⇔ .proj₁ w₁[σ₁]≡w₂[σ₂] of λ
      (w₁′ , w₂′ , w₁⇒*w₁′@([ _ , ⊢w₁′ , _ ]) , w₂⇒*w₂′ , _ , _ ,
       rest) →
    case convRed:*: w₂⇒*w₂′ (≅-eq $ escape-⊩≡ Id-v₁[σ₁]≡Id-v₂[σ₂]) of λ
      w₂⇒*w₂′@([ _ , ⊢w₂′ , _ ]) →

    -- Some definitions related to w₁′ and w₂′.
    case ⊩∷-⇒* w₁⇒*w₁′ $ ⊩ᵛ∷⇔′ .proj₁ ⊩w₁ .proj₂ .proj₁ ⊩σ₁ of λ
      (⊩w₁′ , w₁[σ₁]≡w₁′) →
    case ⊩∷-⇒* w₂⇒*w₂′ $ ⊩ᵛ∷⇔′ .proj₁ ⊩w₂ .proj₂ .proj₁ ⊩σ₂ of λ
      (⊩w₂′ , w₂[σ₂]≡w₂′) →
    case
      w₁′ ∷ Id (wk1 A₁) (wk1 t₁) (var x0) U.[ σ₁ ⇑ ] [ v₁ U.[ σ₁ ] ]₀  ≡⟨⟩⊩∷∷
                                                                       ˘⟨ Id[]≡Id-wk1-0-[⇑][]₀ A₁ t₁ ⟩⊩∷≡
      _   ∷ Id A₁ t₁ v₁ U.[ σ₁ ]                                       ≡˘⟨ w₁[σ₁]≡w₁′ ⟩⊩∷∷
      w₁ U.[ σ₁ ] ∷ Id A₁ t₁ v₁ U.[ σ₁ ]                               ≡⟨ w₁[σ₁]≡w₂[σ₂] ⟩⊩∷∷
                                                                        ⟨ Id-v₁[σ₁]≡Id-v₂[σ₂] ⟩⊩∷
      w₂ U.[ σ₂ ] ∷ Id A₂ t₂ v₂ U.[ σ₂ ]                               ≡⟨ w₂[σ₂]≡w₂′ ⟩⊩∷∎∷
      w₂′                                                              ∎
    of λ
      w₁′≡w₂′ →
    case ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀ B₁≡B₂ σ₁≡σ₂ v₁[σ₁]≡v₂[σ₂]
           w₁′≡w₂′ of λ
      B₁[σ₁⇑⇑][v₁[σ₁],w₁′]≡B₂[σ₂⇑⇑][v₂[σ₂],w₂′] →
    case ≅-eq $ escape-⊩≡ B₁[σ₁⇑⇑][v₁[σ₁],w₁′]≡B₂[σ₂⇑⇑][v₂[σ₂],w₂′] of λ
      ⊢B₁[σ₁⇑⇑][v₁[σ₁],w₁′]≡B₂[σ₂⇑⇑][v₂[σ₂],w₂′] →

    -- The two applications of J are equal if applications of J to w₁′
    -- and w₂′ are equal.
    case
      (λ hyp →
         J p q (A₁ U.[ σ₁ ]) (t₁ U.[ σ₁ ]) (B₁ U.[ σ₁ ⇑ ⇑ ])
           (u₁ U.[ σ₁ ]) (v₁ U.[ σ₁ ]) (w₁ U.[ σ₁ ])
           ∷ B₁ [ v₁ , w₁ ]₁₀ U.[ σ₁ ]                        ≡⟨⟩⊩∷∷
                                                               ⟨ [,]-[]-commute B₁ ⟩⊩∷≡
         _ ∷ B₁ U.[ σ₁ ⇑ ⇑ ] [ v₁ U.[ σ₁ ] , w₁ U.[ σ₁ ] ]₁₀  ⇒*⟨ J-subst*′ ⊩B₁ ⊩σ₁ ⊢u₁[σ₁] ⊩v₁[σ₁] (redₜ w₁⇒*w₁′) ⊩w₁′ ⟩⊩∷∷
                                                                ⟨ ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀ (refl-⊩ᵛ≡ ⊩B₁)
                                                                    (refl-⊩ˢ≡∷ ⊩σ₁) (refl-⊩≡∷ ⊩v₁[σ₁])
                                                                    (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (Id[]≡Id-wk1-0-[⇑][]₀ A₁ t₁)
                                                                       w₁[σ₁]≡w₁′) ⟩⊩∷
         J p q (A₁ U.[ σ₁ ]) (t₁ U.[ σ₁ ]) (B₁ U.[ σ₁ ⇑ ⇑ ])
           (u₁ U.[ σ₁ ]) (v₁ U.[ σ₁ ]) w₁′
            ∷ B₁ U.[ σ₁ ⇑ ⇑ ] [ v₁ U.[ σ₁ ] , w₁′ ]₁₀         ≡⟨ hyp ⟩⊩∷∷⇐*
                                                               ⟨ ⊢B₁[σ₁⇑⇑][v₁[σ₁],w₁′]≡B₂[σ₂⇑⇑][v₂[σ₂],w₂′] ⟩⇒
            ∷ B₂ U.[ σ₂ ⇑ ⇑ ] [ v₂ U.[ σ₂ ] , w₂′ ]₁₀         ˘⟨ ≅-eq $ escape-⊩≡ $
                                                                 ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀ (refl-⊩ᵛ≡ ⊩B₂)
                                                                   (refl-⊩ˢ≡∷ ⊩σ₂) (refl-⊩≡∷ ⊩v₂[σ₂])
                                                                   (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (Id[]≡Id-wk1-0-[⇑][]₀ A₂ t₂)
                                                                      w₂[σ₂]≡w₂′) ⟩⇒
         J p q (A₂ U.[ σ₂ ]) (t₂ U.[ σ₂ ]) (B₂ U.[ σ₂ ⇑ ⇑ ])
           (u₂ U.[ σ₂ ]) (v₂ U.[ σ₂ ]) w₂′
           ∷ B₂ U.[ σ₂ ⇑ ⇑ ] [ v₂ U.[ σ₂ ] , w₂ U.[ σ₂ ] ]₁₀  ⇐*⟨ J-subst*′ ⊩B₂ ⊩σ₂ ⊢u₂[σ₂] ⊩v₂[σ₂] (redₜ w₂⇒*w₂′) ⊩w₂′ ⟩∎∷

         J p q (A₂ U.[ σ₂ ]) (t₂ U.[ σ₂ ]) (B₂ U.[ σ₂ ⇑ ⇑ ])
           (u₂ U.[ σ₂ ]) (v₂ U.[ σ₂ ]) (w₂ U.[ σ₂ ])          ∎)
    of λ
      lemma →

    case rest of λ where
      (rfl₌ t₁[σ₁]≡v₁[σ₁]) →
        -- If w₁′ and w₂′ are both rfl, then one can conclude by using
        -- the β-rule for J and the fact that u₁ [σ₁] is equal to
        -- u₂ [σ₂].
        case
          t₂ U.[ σ₂ ] ∷ A₂ U.[ σ₂ ]  ≡⟨⟩⊩∷∷
                                      ˘⟨ A₁[σ₁]≡A₂[σ₂] ⟩⊩∷
          _           ∷ A₁ U.[ σ₁ ]  ≡˘⟨ t₁[σ₁]≡t₂[σ₂] ⟩⊩∷∷
          t₁ U.[ σ₁ ]                ≡⟨ t₁[σ₁]≡v₁[σ₁] ⟩⊩∷
          v₁ U.[ σ₁ ]                ≡⟨ v₁[σ₁]≡v₂[σ₂] ⟩⊩∷∎
          v₂ U.[ σ₂ ]                ∎
        of λ
          t₂[σ₂]≡v₂[σ₂] →
        lemma
          (J p q A₁ t₁ B₁ u₁ v₁ rfl U.[ σ₁ ]
             ∷ B₁ U.[ σ₁ ⇑ ⇑ ] [ v₁ U.[ σ₁ ] , rfl ]₁₀            ≡⟨⟩⊩∷∷
                                                                   ⟨ ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀ (refl-⊩ᵛ≡ ⊩B₁)
                                                                       (refl-⊩ˢ≡∷ ⊩σ₁) (sym-⊩≡∷ t₁[σ₁]≡v₁[σ₁])
                                                                       (refl-⊩≡∷ $
                                                                        PE.subst (_⊩⟨_⟩_∷_ _ _ _) (Id[]≡Id-wk1-0-[⇑][]₀ A₁ t₁) ⊩w₁′) ⟩⊩∷
           _ ∷ B₁ U.[ σ₁ ⇑ ⇑ ] [ t₁ U.[ σ₁ ] , rfl ]₁₀            ⇒⟨ J-β ⊢A₁[σ₁] ⊢t₁[σ₁] ⊢v₁[σ₁] (≅ₜ-eq (escape-⊩≡∷ t₁[σ₁]≡v₁[σ₁])) ⊢B₁[σ₁⇑⇑]
                                                                       (≅-eq $ escape-⊩≡ $
                                                                        ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀ (refl-⊩ᵛ≡ ⊩B₁)
                                                                          (refl-⊩ˢ≡∷ ⊩σ₁) t₁[σ₁]≡v₁[σ₁] rfl≡rfl)
                                                                       ⊢u₁[σ₁] ⟩⊩∷∷
           u₁ U.[ σ₁ ] ∷ B₁ U.[ σ₁ ⇑ ⇑ ] [ t₁ U.[ σ₁ ] , rfl ]₁₀  ≡⟨ u₁[σ₁]≡u₂[σ₂] ⟩⊩∷∷⇐*
                                                                   ⟨ ⊢B₁[σ₁⇑⇑][t₁[σ₁],rfl]≡B₂[σ₂⇑⇑][t₂[σ₂],rfl] ⟩⇒
           u₂ U.[ σ₂ ] ∷ B₂ U.[ σ₂ ⇑ ⇑ ] [ t₂ U.[ σ₂ ] , rfl ]₁₀  ⇐⟨ J-β ⊢A₂[σ₂] ⊢t₂[σ₂] ⊢v₂[σ₂] (≅ₜ-eq (escape-⊩≡∷ t₂[σ₂]≡v₂[σ₂])) ⊢B₂[σ₂⇑⇑]
                                                                       (≅-eq $ escape-⊩≡ $
                                                                        ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀ (refl-⊩ᵛ≡ ⊩B₂)
                                                                          (refl-⊩ˢ≡∷ ⊩σ₂) t₂[σ₂]≡v₂[σ₂]
                                                                          (refl-⊩≡∷ $
                                                                           PE.subst (_⊩⟨_⟩_∷_ _ _ _) (Id[]≡Id-wk1-0-[⇑][]₀ A₂ t₂) $
                                                                           ⊩rfl ⊩t₂[σ₂]))
                                                                       ⊢u₂[σ₂]
                                                                   , ⊢u₂[σ₂]
                                                                   ⟩∎∷
           J p q A₂ t₂ B₂ u₂ v₂ rfl U.[ σ₂ ]                      ∎)

      (ne w₁′-ne w₂′-ne w₁′~w₂′) →
        -- If w₁′ and w₂′ are equal neutral terms, then one can
        -- conclude by using the fact that the applications of J to
        -- w₁′ and w₂′ are equal neutral terms.
        lemma $
        neutral-⊩≡∷
          (wf-⊩≡ B₁[σ₁⇑⇑][v₁[σ₁],w₁′]≡B₂[σ₂⇑⇑][v₂[σ₂],w₂′] .proj₁)
          (Jₙ w₁′-ne) (Jₙ w₂′-ne)
          (Jⱼ ⊢A₁[σ₁] ⊢t₁[σ₁] ⊢B₁[σ₁⇑⇑] ⊢u₁[σ₁] ⊢v₁[σ₁] ⊢w₁′)
          (conv (Jⱼ ⊢A₂[σ₂] ⊢t₂[σ₂] ⊢B₂[σ₂⇑⇑] ⊢u₂[σ₂] ⊢v₂[σ₂] ⊢w₂′)
             (sym ⊢B₁[σ₁⇑⇑][v₁[σ₁],w₁′]≡B₂[σ₂⇑⇑][v₂[σ₂],w₂′]))
          (~-J ⊢A₁[σ₁] (escape-⊩≡ A₁[σ₁]≡A₂[σ₂]) ⊢t₁[σ₁]
             (escape-⊩≡∷ t₁[σ₁]≡t₂[σ₂]) (escape-⊩≡ B₁[σ₁⇑⇑]≡B₂[σ₂⇑⇑])
             (escape-⊩≡∷ u₁[σ₁]≡u₂[σ₂]) (escape-⊩≡∷ v₁[σ₁]≡v₂[σ₂])
             w₁′~w₂′)

opaque

  -- Reducibility for J.

  ⊩J :
    Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊩ᵛ⟨ l ⟩ B →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ B [ t , rfl ]₁₀ →
    Γ ⊩ᵛ⟨ l″ ⟩ w ∷ Id A t v →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l ⟩ J p q A t B u v w U.[ σ ] ∷ B [ v , w ]₁₀ U.[ σ ]
  ⊩J ⊩B ⊩u ⊩w ⊩σ =
    case ⊩ᵛId⇔ .proj₁ $ wf-⊩ᵛ∷ ⊩w of λ
      (⊩t , ⊩v) →
    case wf-⊩ᵛ∷ ⊩t of λ
      ⊩A →
    wf-⊩≡∷
      (⊩J≡J (refl-⊩ᵛ≡ ⊩A) (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ᵛ≡ ⊩B) (refl-⊩ᵛ≡∷ ⊩u)
         (refl-⊩ᵛ≡∷ ⊩v) (refl-⊩ᵛ≡∷ ⊩w) (refl-⊩ˢ≡∷ ⊩σ))
      .proj₁

opaque

  -- Validity of J.

  Jᵛ :
    Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊩ᵛ⟨ l ⟩ B →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ B [ t , rfl ]₁₀ →
    Γ ⊩ᵛ⟨ l″ ⟩ w ∷ Id A t v →
    Γ ⊩ᵛ⟨ l ⟩ J p q A t B u v w ∷ B [ v , w ]₁₀
  Jᵛ ⊩B ⊩u ⊩w =
    case ⊩ᵛId⇔ .proj₁ (wf-⊩ᵛ∷ ⊩w) of λ
      (⊩t , ⊩v) →
    ⊩ᵛ∷⇔′ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀ ⊩B ⊩v
          (PE.subst (_⊩ᵛ⟨_⟩_∷_ _ _ _) ≡Id-wk1-wk1-0[]₀ ⊩w)
      , ⊩J ⊩B ⊩u ⊩w
      , ⊩J≡J (refl-⊩ᵛ≡ (wf-⊩ᵛ∷ ⊩t)) (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ᵛ≡ ⊩B)
          (refl-⊩ᵛ≡∷ ⊩u) (refl-⊩ᵛ≡∷ ⊩v) (refl-⊩ᵛ≡∷ ⊩w)
      )

opaque

  -- Validity of equality preservation for J.

  J-congᵛ :
    Γ ⊩ᵛ⟨ l′₁ ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l′₂ ⟩ t₁ ≡ t₂ ∷ A₁ →
    Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    Γ ⊩ᵛ⟨ l′₃ ⟩ u₁ ≡ u₂ ∷ B₁ [ t₁ , rfl ]₁₀ →
    Γ ⊩ᵛ⟨ l′₄ ⟩ v₁ ≡ v₂ ∷ A₁ →
    Γ ⊩ᵛ⟨ l′₅ ⟩ w₁ ≡ w₂ ∷ Id A₁ t₁ v₁ →
    Γ ⊩ᵛ⟨ l ⟩ J p q A₁ t₁ B₁ u₁ v₁ w₁ ≡ J p q A₂ t₂ B₂ u₂ v₂ w₂ ∷
      B₁ [ v₁ , w₁ ]₁₀
  J-congᵛ A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂ =
    case wf-⊩ᵛ≡ A₁≡A₂ of λ
      (⊩A₁ , _) →
    case wf-⊩ᵛ≡ B₁≡B₂ of λ
      (⊩B₁ , ⊩B₂) →
    case wf-⊩ᵛ≡∷ u₁≡u₂ of λ
      (⊩u₁ , ⊩u₂) →
    case wf-⊩ᵛ≡∷ w₁≡w₂ of λ
      (⊩w₁ , ⊩w₂) →
    ⊩ᵛ≡∷⇔′ .proj₂
      ( Jᵛ ⊩B₁ ⊩u₁ ⊩w₁
      , conv-⊩ᵛ∷
          (sym-⊩ᵛ≡ $
           ⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ[]₁₀≡[]₁₀ B₁≡B₂ v₁≡v₂ $
           PE.subst (_⊩ᵛ⟨_⟩_≡_∷_ _ _ _ _) ≡Id-wk1-wk1-0[]₀ w₁≡w₂)
          (Jᵛ
             (conv-∙∙-⊩ᵛ A₁≡A₂
                (Id-congᵛ (wk1-⊩ᵛ≡ ⊩A₁ A₁≡A₂) (wk1-⊩ᵛ≡∷ ⊩A₁ t₁≡t₂)
                   (refl-⊩ᵛ≡∷ (varᵛ′ here (wk1-⊩ᵛ ⊩A₁ ⊩A₁))))
                ⊩B₂)
             (conv-⊩ᵛ∷
                (⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ[]₁₀≡[]₁₀ B₁≡B₂ t₁≡t₂ $
                 refl-⊩ᵛ≡∷ $
                 PE.subst (_⊩ᵛ⟨_⟩_∷_ _ _ _) ≡Id-wk1-wk1-0[]₀ $
                 rflᵛ (wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁))
                ⊩u₂)
             (conv-⊩ᵛ∷ (Id-congᵛ A₁≡A₂ t₁≡t₂ v₁≡v₂) ⊩w₂))
      , ⊩J≡J A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂
      )

opaque

  -- Validity of the J β rule.

  J-βᵛ :
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ A →
    Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊩ᵛ⟨ l″ ⟩ B →
    Γ ⊩ᵛ⟨ l ⟩ u ∷ B [ t , rfl ]₁₀ →
    Γ ⊩ᵛ⟨ l ⟩ J p q A t B u t rfl ≡ u ∷ B [ t , rfl ]₁₀
  J-βᵛ {t} {A} {B} ⊩t ⊩B ⊩u =
    ⊩ᵛ∷-⇐
      (λ {_ _} {σ = σ} ⊩σ →
         case ⊩ᵛ∷⇔′ .proj₁ ⊩t .proj₂ .proj₁ ⊩σ of λ
           ⊩t[σ] →
         case escape-⊩∷ ⊩t[σ] of λ
           ⊢t[σ] →
         PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ [,]-[]-commute B) $
         J-β (escape (wf-⊩∷ ⊩t[σ])) ⊢t[σ] ⊢t[σ] (refl ⊢t[σ])
           (PE.subst₂ _⊢_
              (PE.cong (_∙_ _) $ Id-wk1-wk1-0[⇑]≡ A t) PE.refl $
            escape $ ⊩ᵛ→⊩ˢ∷→⊩[⇑⇑] ⊩B ⊩σ)
           (_⊢_≡_.refl $ escape $
            ⊩ᵛ→⊩ˢ∷→⊩∷→⊩[⇑⇑][]₁₀ ⊩B ⊩σ ⊩t[σ] $
            PE.subst (_⊩⟨_⟩_∷_ _ _ _) (Id[]≡Id-wk1-0-[⇑][]₀ A t) $
            ⊩rfl ⊩t[σ])
           (PE.subst (_⊢_∷_ _ _) ([,]-[]-commute B) $
            escape-⊩∷ $ ⊩ᵛ∷⇔′ .proj₁ ⊩u .proj₂ .proj₁ ⊩σ))
      ⊩u
      .proj₂
