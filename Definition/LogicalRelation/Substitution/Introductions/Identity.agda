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
import Definition.LogicalRelation.Hidden.Restricted R as R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R
import Definition.LogicalRelation.Substitution.Introductions.Erased R
  as Erased
open import
  Definition.LogicalRelation.Substitution.Introductions.Level R
open import
  Definition.LogicalRelation.Substitution.Introductions.Universe R
open import Definition.LogicalRelation.Substitution.Introductions.Var R
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Reduction R
open import Definition.Typed.Stability R
open import Definition.Typed.Substitution R
open import Definition.Typed.Weakening R
open import Definition.Typed.Well-formed R
open import Definition.Untyped M as U hiding (_[_])
import Definition.Untyped.Erased
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Tools.Empty
open import Tools.Fin using (x0)
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality

private variable
  Γ Δ                                       : Con Term _
  A A₁ A₂ B B₁ B₂
    k k₁ k₂ t t₁ t₂ u u₁ u₂ v v₁ v₂ w w₁ w₂ : Term _
  σ σ₁ σ₂                                   : Subst _ _
  l l′ l′₁ l′₂ l′₃ l′₄ l′₅ l″ l‴ l⁗         : Universe-level
  n                                         : Nat
  p q                                       : M
  s                                         : Strength

private

  -- Some definitions used in proofs below.

  module E {s} (ok : []-cong-allowed s) where

    open Definition.Untyped.Erased 𝕄 s public
    open Erased ([]-cong→Erased ok) public
      renaming ([]-congᵛ to []-congᵛ′)

------------------------------------------------------------------------
-- Some characterisation lemmas

opaque
  unfolding _⊩⟨_⟩_∷_

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩Id⇔ :
    Γ ⊩⟨ l ⟩ Id A t u ⇔
    (Γ ⊩⟨ l ⟩ t ∷ A × Γ ⊩⟨ l ⟩ u ∷ A)
  ⊩Id⇔ {A} {t} {u} =
      (λ ⊩Id →
        case Id-view ⊩Id of λ {
          (Idᵣ ⊩Id@record{}) →
        let open _⊩ₗId_ ⊩Id in
        case whnfRed* ⇒*Id Idₙ of λ {
          PE.refl →
        (⊩Ty , ⊩lhs) , (⊩Ty , ⊩rhs) }})
    , (λ ((⊩A , ⊩t) , (⊩A′ , ⊩u)) →
         Idᵣ
           (Idᵣ A t u
              (_⊢_⇒*_.id $
               Idⱼ (escape ⊩A) (escapeTerm ⊩A ⊩t) (escapeTerm ⊩A′ ⊩u))
              ⊩A
              ⊩t (irrelevanceTerm ⊩A′ ⊩A ⊩u)))

opaque

  -- A corollary.

  →⊩Id∷U :
    Γ ⊩⟨ l′ ⟩ A ∷ U k →
    Γ ⊩⟨ l″ ⟩ t ∷ A →
    Γ ⊩⟨ l‴ ⟩ u ∷ A →
    Γ ⊩⟨ l′ ⟩ Id A t u ∷ U k
  →⊩Id∷U {Γ} {l′} {A} {k} {l″} {t} {l‴} {u} ⊩A ⊩t ⊩u =
                                                   $⟨ ⊩A , ⊩t , ⊩u ⟩
    Γ ⊩⟨ l′ ⟩ A ∷ U k ×
    Γ ⊩⟨ l″ ⟩ t ∷ A ×
    Γ ⊩⟨ l‴ ⟩ u ∷ A                                →⟨ (λ (⊩A∷U , ⊩t , ⊩u) →
                                                         let [k] , k< , ⊩A , _ = ⊩∷U⇔ .proj₁ ⊩A∷U in
                                                           [k] , k<
                                                         , (level-⊩∷ ⊩A ⊩t , level-⊩∷ ⊩A ⊩u)
                                                         , ≅ₜ-Id-cong (escape-⊩≡∷ (refl-⊩≡∷ ⊩A∷U))
                                                             (escape-⊩≡∷ (refl-⊩≡∷ ⊩t)) (escape-⊩≡∷ (refl-⊩≡∷ ⊩u)))
                                                   ⟩
    (∃ λ [k] → ↑ᵘ [k] <ᵘ l′ × (Γ ⊩⟨ ↑ᵘ [k] ⟩ t ∷ A × Γ ⊩⟨ ↑ᵘ [k] ⟩ u ∷ A) ×
    Γ ⊢≅ Id A t u ∷ U k)                           ⇔˘⟨ (Σ-cong-⇔ λ _ → id⇔ ×-cong-⇔ ⊩Id⇔ ×-cong-⇔ id⇔) ⟩→

    (∃ λ [k] → ↑ᵘ [k] <ᵘ l′ × (Γ ⊩⟨ ↑ᵘ [k] ⟩ Id A t u) ×
    Γ ⊢≅ Id A t u ∷ U k)                           ⇔˘⟨ Type→⊩∷U⇔ Idₙ ⟩→

    Γ ⊩⟨ l′ ⟩ Id A t u ∷ U k                       □

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_≡_∷_ wf-⊩≡∷

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩Id≡⇔ :
    Γ ⊩⟨ l ⟩ Id A t u ≡ B ⇔
    (Γ ⊩⟨ l ⟩ Id A t u ×
     ∃₃ λ A′ t′ u′ →
     (Γ ⊢ B ⇒* Id A′ t′ u′) ×
     (Γ ⊩⟨ l ⟩ A ≡ A′) ×
     Γ ⊩⟨ l ⟩ t ≡ t′ ∷ A ×
     Γ ⊩⟨ l ⟩ u ≡ u′ ∷ A)
  ⊩Id≡⇔ =
      (λ (⊩Id , ⊩B , Id≡B) →
        case Id-view ⊩Id of λ {
          (Idᵣ ⊩Id@record{}) →
        let open _⊩ₗId_ ⊩Id in
        case Id≡B of λ
          (Id₌ A′ t′ u′ ⇒*Id′ A≡A′ t≡t′ u≡u′ _ _) →
        case whnfRed* ⇒*Id Idₙ of λ {
          PE.refl →
        case Id-elim (redSubst*′ ⇒*Id′ ⊩B .proj₁) of λ {
          (Idᵣ _ _ _ ⇒*Id″ ⊩Ty″ _ _) →
        case whnfRed* ⇒*Id″ Idₙ of λ {
          PE.refl →
          Idᵣ ⊩Id
        , A′ , t′ , u′ , ⇒*Id′
        , (⊩Ty , ⊩Ty″ , A≡A′)
        , (⊩Ty , t≡t′)
        , (⊩Ty , u≡u′) }}}})
    , (λ (⊩Id , rest) →
        case Id-view ⊩Id of λ {
          (Idᵣ ⊩Id@record{}) →
        let open _⊩ₗId_ ⊩Id in
        let A′ , t′ , u′ , B⇒*Id , (⊩A , ⊩A′ , A≡A′) ,
              t≡t′′@(⊩A″ , t≡t′) , u≡u′′@(⊩A‴ , u≡u′) =
              rest
        in
        case whnfRed* ⇒*Id Idₙ of λ {
          PE.refl →
        let ⊢A≡A′         = ≅-eq (escapeEq ⊩A A≡A′)
            _ , (_ , ⊩t′) = wf-⊩≡∷ t≡t′′
            _ , (_ , ⊩u′) = wf-⊩≡∷ u≡u′′
        in
          Idᵣ ⊩Id
        , redSubst* B⇒*Id
            (Idᵣ
              (Idᵣ A′ t′ u′
                  (_⊢_⇒*_.id $
                  Idⱼ (escape ⊩A′) (conv (escapeTerm ⊩A″ ⊩t′) ⊢A≡A′)
                    (conv (escapeTerm ⊩A‴ ⊩u′) ⊢A≡A′))
                  ⊩A′
                  (convTerm₁ ⊩A″ ⊩A′ (irrelevanceEq ⊩A ⊩A″ A≡A′) ⊩t′)
                  (convTerm₁ ⊩A‴ ⊩A′ (irrelevanceEq ⊩A ⊩A‴ A≡A′) ⊩u′)))
            .proj₁
        , Id₌′ B⇒*Id (irrelevanceEq ⊩A ⊩Ty A≡A′)
            (irrelevanceEqTerm ⊩A″ ⊩Ty t≡t′)
            (irrelevanceEqTerm ⊩A‴ ⊩Ty u≡u′) }})

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
     (Γ ⊢ Id A₂ t₂ u₂ ⇒* Id A′ t′ u′) ×
     (Γ ⊩⟨ l ⟩ A₁ ≡ A′) ×
     Γ ⊩⟨ l ⟩ t₁ ≡ t′ ∷ A₁ ×
     Γ ⊩⟨ l ⟩ u₁ ≡ u′ ∷ A₁)              ⇔⟨ (λ (_ , _ , _ , _ , Id⇒*Id , A₁≡ , t₁≡ , u₁≡) →
                                               case whnfRed* Id⇒*Id Idₙ of λ {
                                                 PE.refl →
                                               A₁≡ , t₁≡ , u₁≡ })
                                          , (λ (A₁≡A₂ , t₁≡t₂ , u₁≡u₂) →
                                                 ⊩Id⇔ .proj₂ (wf-⊩≡∷ t₁≡t₂ .proj₁ , wf-⊩≡∷ u₁≡u₂ .proj₁)
                                               , _ , _ , _
                                               , id
                                                   (Idⱼ (escape-⊩ (wf-⊩≡ A₁≡A₂ .proj₂))
                                                      (escape-⊩∷ (conv-⊩∷ A₁≡A₂ (wf-⊩≡∷ t₁≡t₂ .proj₂)))
                                                      (escape-⊩∷ (conv-⊩∷ A₁≡A₂ (wf-⊩≡∷ u₁≡u₂ .proj₂))))
                                               , A₁≡A₂ , t₁≡t₂ , u₁≡u₂)
                                          ⟩
    (Γ ⊩⟨ l ⟩ A₁ ≡ A₂) ×
    Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ A₁ ×
    Γ ⊩⟨ l ⟩ u₁ ≡ u₂ ∷ A₁                □⇔

opaque

  -- A corollary.

  →⊩Id≡Id∷U :
    Γ ⊩⟨ l′ ⟩ A₁ ≡ A₂ ∷ U k →
    Γ ⊩⟨ l″ ⟩ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊩⟨ l‴ ⟩ u₁ ≡ u₂ ∷ A₁ →
    Γ ⊩⟨ l′ ⟩ Id A₁ t₁ u₁ ≡ Id A₂ t₂ u₂ ∷ U k
  →⊩Id≡Id∷U {Γ} {l′} {A₁} {A₂} {k} {l″} {t₁} {t₂} {l‴} {u₁} {u₂} A₁≡A₂∷U t₁≡t₂ u₁≡u₂ =
                                                                     $⟨ A₁≡A₂∷U , t₁≡t₂ , u₁≡u₂ ⟩
    Γ ⊩⟨ l′ ⟩ A₁ ≡ A₂ ∷ U k ×
    Γ ⊩⟨ l″ ⟩ t₁ ≡ t₂ ∷ A₁ ×
    Γ ⊩⟨ l‴ ⟩ u₁ ≡ u₂ ∷ A₁                                           →⟨ (λ (A₁≡A₂∷U , t₁≡t₂ , u₁≡u₂) →
                                                                           case ⊩≡∷U⇔ .proj₁ A₁≡A₂∷U of λ
                                                                             ([k] , k<l , A₁≡A₂ , _) →
                                                                           case escape-⊩≡∷ A₁≡A₂∷U of λ
                                                                             A₁≅A₂∷U →
                                                                           case escape-⊩≡∷ t₁≡t₂ of λ
                                                                             t₁≅t₂ →
                                                                           case escape-⊩≡∷ u₁≡u₂ of λ
                                                                             u₁≅u₂ →
                                                                           case Σ.map escape-⊩∷ escape-⊩∷ $ wf-⊩≡∷ A₁≡A₂∷U of λ
                                                                             (⊢A₁∷U , ⊢A₂∷U) →
                                                                           case wf-⊩≡ A₁≡A₂ .proj₁ of λ
                                                                             ⊩A₁ →
                                                                             [k] , k<l
                                                                           , (A₁≡A₂ , level-⊩≡∷ ⊩A₁ t₁≡t₂ , level-⊩≡∷ ⊩A₁ u₁≡u₂)
                                                                           , ≅ₜ-Id-cong A₁≅A₂∷U t₁≅t₂ u₁≅u₂) ⟩
    (∃ λ [k] → ↑ᵘ [k] <ᵘ l′ ×
    ((Γ ⊩⟨ ↑ᵘ [k] ⟩ A₁ ≡ A₂) ×
     Γ ⊩⟨ ↑ᵘ [k] ⟩ t₁ ≡ t₂ ∷ A₁ ×
     Γ ⊩⟨ ↑ᵘ [k] ⟩ u₁ ≡ u₂ ∷ A₁) ×
    Γ ⊢ Id A₁ t₁ u₁ ≅ Id A₂ t₂ u₂ ∷ U k)                             ⇔˘⟨ (Σ-cong-⇔ λ _ → id⇔ ×-cong-⇔
                                                                          ⊩Id≡Id⇔ ×-cong-⇔ id⇔) ⟩→
    (∃ λ [k] → ↑ᵘ [k] <ᵘ l′ ×
    (Γ ⊩⟨ ↑ᵘ [k] ⟩ Id A₁ t₁ u₁ ≡ Id A₂ t₂ u₂) ×
    Γ ⊢ Id A₁ t₁ u₁ ≅ Id A₂ t₂ u₂ ∷ U k)                             ⇔˘⟨ Type→⊩≡∷U⇔ Idₙ Idₙ ⟩→


    Γ ⊩⟨ l′ ⟩ Id A₁ t₁ u₁ ≡ Id A₂ t₂ u₂ ∷ U k                        □

-- A variant of ⊩Id≡∷-view.

data ⊩Id≡∷-view′
       (Γ : Con Term n) (l : Universe-level) (A t u : Term n) :
       Term n → Term n → Set a where
  rfl₌ : Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
         ⊩Id≡∷-view′ Γ l A t u rfl rfl
  ne   : Neutrals-included →
         Neutral v → Neutral w →
         Γ ⊢ v ~ w ∷ Id A t u →
         ⊩Id≡∷-view′ Γ l A t u v w

opaque

  -- If ⊩Id≡∷-view′ Γ l A t u v w holds, then Identity v and
  -- Identity w both hold.

  ⊩Id≡∷-view′→Identity :
    ⊩Id≡∷-view′ Γ l A t u v w →
    Identity v × Identity w
  ⊩Id≡∷-view′→Identity (rfl₌ _)           = rflₙ , rflₙ
  ⊩Id≡∷-view′→Identity (ne _ v-ne w-ne _) = ne v-ne , ne w-ne

opaque
  unfolding _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷Id⇔ :
    Γ ⊩⟨ l ⟩ v ≡ w ∷ Id A t u ⇔
    (∃₂ λ v′ w′ →
     Γ ⊢ v ⇒* v′ ∷ Id A t u ×
     Γ ⊢ w ⇒* w′ ∷ Id A t u ×
     Γ ⊩⟨ l ⟩ t ∷ A ×
     Γ ⊩⟨ l ⟩ u ∷ A ×
     ⊩Id≡∷-view′ Γ l A t u v′ w′)
  ⊩≡∷Id⇔ =
      (λ (⊩Id , v≡w) →
        case Id-view ⊩Id of λ {
          (Idᵣ ⊩Id@record{}) →
        let open _⊩ₗId_ ⊩Id in
        let v′ , w′ , v⇒*v′ , w⇒*w′ , _ = v≡w in
        case whnfRed* ⇒*Id Idₙ of λ {
          PE.refl →
          v′ , w′ , v⇒*v′ , w⇒*w′
        , (⊩Ty , ⊩lhs)
        , (⊩Ty , ⊩rhs)
        , (case ⊩Id≡∷-view-inhabited ⊩Id v≡w of λ where
            (rfl₌ t≡u)                 → rfl₌ (⊩Ty , t≡u)
            (ne inc v′-ne w′-ne v′~w′) → ne inc v′-ne w′-ne v′~w′) }})
    , (λ (v′ , w′ , v⇒*v′ , w⇒*w′ , (⊩A , ⊩t) , (⊩A′ , ⊩u) , rest) →
         let Id⇒*Id =
               _⊢_⇒*_.id $
               Idⱼ (escape ⊩A) (escapeTerm ⊩A ⊩t)
                 (escapeTerm ⊩A′ ⊩u)
         in
           Idᵣ (Idᵣ _ _ _ Id⇒*Id ⊩A ⊩t (irrelevanceTerm ⊩A′ ⊩A ⊩u))
         , (case rest of λ where
              (ne inc v′-ne w′-ne v′~w′) →
                v′ , w′ , v⇒*v′ , w⇒*w′ ,
                ne v′-ne , ne w′-ne , inc , v′~w′
              (rfl₌ (⊩A″ , t≡u)) →
                v′ , w′ , v⇒*v′ , w⇒*w′ , rflₙ , rflₙ ,
                irrelevanceEqTerm ⊩A″ ⊩A t≡u))

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
     Γ ⊢ v ⇒* v′ ∷ Id A t u ×
     Γ ⊢ w ⇒* w′ ∷ Id A t u ×
     Γ ⊩⟨ l ⟩ t ∷ A ×
     Γ ⊩⟨ l ⟩ u ∷ A ×
     ⊩Id≡∷-view′ Γ l A t u v′ w′)  ⇔⟨ (λ (_ , _ , v⇒*v′ , w⇒*w′ , ⊩t , ⊩u , rest) →
                                         case whnfRed*Term v⇒*v′ (identityWhnf v-id) of λ {
                                           PE.refl →
                                         case whnfRed*Term w⇒*w′ (identityWhnf w-id) of λ {
                                           PE.refl →
                                         redFirst*Term v⇒*v′ , redFirst*Term w⇒*w′ ,
                                         ⊩t , ⊩u , rest }})
                                    , (λ (⊢v , ⊢w , ⊩t , ⊩u , rest) →
                                         _ , _ , id ⊢v , id ⊢w , ⊩t , ⊩u , rest)
                                    ⟩
    Γ ⊢ v ∷ Id A t u ×
    Γ ⊢ w ∷ Id A t u ×
    Γ ⊩⟨ l ⟩ t ∷ A ×
    Γ ⊩⟨ l ⟩ u ∷ A ×
    ⊩Id≡∷-view′ Γ l A t u v w      □⇔

-- A variant of ⊩Id∷-view.

data ⊩Id∷-view′
       (Γ : Con Term n) (l : Universe-level) (A t u : Term n) :
       Term n → Set a where
  rflᵣ : Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
         ⊩Id∷-view′ Γ l A t u rfl
  ne   : Neutrals-included →
         Neutral v →
         Γ ⊢~ v ∷ Id A t u →
         ⊩Id∷-view′ Γ l A t u v

opaque

  -- ⊩Id∷-view′ is pointwise logically equivalent to the diagonal of
  -- ⊩Id≡∷-view′.

  ⊩Id∷-view′⇔⊩Id≡∷-view′ :
    ⊩Id∷-view′ Γ l A t u v ⇔ ⊩Id≡∷-view′ Γ l A t u v v
  ⊩Id∷-view′⇔⊩Id≡∷-view′ =
      (λ where
         (rflᵣ t≡u)       → rfl₌ t≡u
         (ne inc v-ne ~v) → ne inc v-ne v-ne ~v)
    , (λ where
         (rfl₌ t≡u)         → rflᵣ t≡u
         (ne inc v-ne _ ~v) → ne inc v-ne ~v)

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷Id⇔ :
    Γ ⊩⟨ l ⟩ v ∷ Id A t u ⇔
    (∃ λ w →
     Γ ⊢ v ⇒* w ∷ Id A t u ×
     Γ ⊩⟨ l ⟩ t ∷ A ×
     Γ ⊩⟨ l ⟩ u ∷ A ×
     ⊩Id∷-view′ Γ l A t u w)
  ⊩∷Id⇔ {Γ} {l} {v} {A} {t} {u} =
    Γ ⊩⟨ l ⟩ v ∷ Id A t u          ⇔⟨ ⊩∷⇔⊩≡∷ ⟩

    Γ ⊩⟨ l ⟩ v ≡ v ∷ Id A t u      ⇔⟨ ⊩≡∷Id⇔ ⟩

    (∃₂ λ v′ v″ →
     Γ ⊢ v ⇒* v′ ∷ Id A t u ×
     Γ ⊢ v ⇒* v″ ∷ Id A t u ×
     Γ ⊩⟨ l ⟩ t ∷ A ×
     Γ ⊩⟨ l ⟩ u ∷ A ×
     ⊩Id≡∷-view′ Γ l A t u v′ v″)  ⇔⟨ (λ (_ , _ , v⇒*v′ , v⇒*v″ , ⊩t , ⊩u , rest) →
                                         let v′-id , v″-id = ⊩Id≡∷-view′→Identity rest in
                                         case whrDet*Term (v⇒*v′ , identityWhnf v′-id)
                                                (v⇒*v″ , identityWhnf v″-id) of λ {
                                           PE.refl →
                                         _ , v⇒*v′ , ⊩t , ⊩u ,
                                         ⊩Id∷-view′⇔⊩Id≡∷-view′ .proj₂ rest })
                                    , (λ (_ , v⇒*w , ⊩t , ⊩u , rest) →
                                         _ , _ , v⇒*w , v⇒*w , ⊩t , ⊩u ,
                                         ⊩Id∷-view′⇔⊩Id≡∷-view′ .proj₁ rest)
                                    ⟩
    (∃ λ w →
     Γ ⊢ v ⇒* w ∷ Id A t u ×
     Γ ⊩⟨ l ⟩ t ∷ A ×
     Γ ⊩⟨ l ⟩ u ∷ A ×
     ⊩Id∷-view′ Γ l A t u w)       □⇔

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
    Γ ⊩⟨ l ⟩ v ∷ Id A t u     ⇔⟨ ⊩∷Id⇔ ⟩

    (∃ λ w →
     Γ ⊢ v ⇒* w ∷ Id A t u ×
     Γ ⊩⟨ l ⟩ t ∷ A ×
     Γ ⊩⟨ l ⟩ u ∷ A ×
     ⊩Id∷-view′ Γ l A t u w)  ⇔⟨ (λ (_ , v⇒*w , ⊩t , ⊩u , rest) →
                                    case whnfRed*Term v⇒*w (identityWhnf v-id) of λ {
                                      PE.refl →
                                    redFirst*Term v⇒*w , ⊩t , ⊩u , rest })
                               , (λ (⊢v , ⊩t , ⊩u , rest) →
                                    _ , id ⊢v , ⊩t , ⊩u , rest)
                               ⟩
    Γ ⊢ v ∷ Id A t u ×
    Γ ⊩⟨ l ⟩ t ∷ A ×
    Γ ⊩⟨ l ⟩ u ∷ A ×
    ⊩Id∷-view′ Γ l A t u v    □⇔

opaque

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_.

  ⊩ᵛId⇔ :
    Γ ⊩ᵛ⟨ l ⟩ Id A t u ⇔
    (Γ ⊩ᵛ⟨ l ⟩ t ∷ A × Γ ⊩ᵛ⟨ l ⟩ u ∷ A)
  ⊩ᵛId⇔ {Γ} {l} {A} {t} {u} =
    (Γ ⊩ᵛ⟨ l ⟩ Id A t u)                                 ⇔⟨ ⊩ᵛ⇔ʰ ⟩

    ⊩ᵛ Γ ×
    (∀ {m Δ} {σ₁ σ₂ : Subst m _}
       ⦃ inc : Neutrals-included or-empty Δ ⦄ →
     Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
     Δ ⊩⟨ l ⟩ Id A t u U.[ σ₁ ] ≡ Id A t u U.[ σ₂ ])     ⇔⟨ id⇔
                                                              ×-cong-⇔
                                                            (implicit-Π-cong-⇔ λ _ → implicit-Π-cong-⇔ λ _ →
                                                             implicit-Π-cong-⇔ λ _ → implicit-Π-cong-⇔ λ _ →
                                                             instance-Π-cong-⇔ $ Π-cong-⇔ λ _ →
                                                             ⊩Id≡Id⇔) ⟩
    ⊩ᵛ Γ ×
    (∀ {m Δ} {σ₁ σ₂ : Subst m _} →
       ⦃ inc : Neutrals-included or-empty Δ ⦄ →
     Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
     (Δ ⊩⟨ l ⟩ A U.[ σ₁ ] ≡ A U.[ σ₂ ]) ×
     Δ ⊩⟨ l ⟩ t U.[ σ₁ ] ≡ t U.[ σ₂ ] ∷ A U.[ σ₁ ] ×
     Δ ⊩⟨ l ⟩ u U.[ σ₁ ] ≡ u U.[ σ₂ ] ∷ A U.[ σ₁ ])      ⇔⟨ (λ (⊩Γ , A≡A×t≡t×u≡u) →
                                                               let ⊩A = ⊩ᵛ⇔ʰ .proj₂ (⊩Γ , proj₁ ∘→ A≡A×t≡t×u≡u) in
                                                                 ( ⊩A
                                                                 , λ σ₁≡σ₂ → A≡A×t≡t×u≡u σ₁≡σ₂ .proj₂ .proj₁
                                                                 )
                                                               , ( ⊩A
                                                                 , λ σ₁≡σ₂ → A≡A×t≡t×u≡u σ₁≡σ₂ .proj₂ .proj₂
                                                                 ))
                                                          , (λ ((⊩A , t≡t) , (_ , u≡u)) →
                                                                 wf-⊩ᵛ ⊩A
                                                               , (λ σ₁≡σ₂ →
                                                                      ⊩ᵛ⇔ʰ .proj₁ ⊩A .proj₂ σ₁≡σ₂
                                                                    , t≡t σ₁≡σ₂ , u≡u σ₁≡σ₂))
                                                          ⟩
    (Γ ⊩ᵛ⟨ l ⟩ A ×
     (∀ {m Δ} {σ₁ σ₂ : Subst m _}
        ⦃ inc : Neutrals-included or-empty Δ ⦄ →
      Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
      Δ ⊩⟨ l ⟩ t U.[ σ₁ ] ≡ t U.[ σ₂ ] ∷ A U.[ σ₁ ])) ×
    (Γ ⊩ᵛ⟨ l ⟩ A ×
     (∀ {m Δ} {σ₁ σ₂ : Subst m _}
        ⦃ inc : Neutrals-included or-empty Δ ⦄ →
      Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
      Δ ⊩⟨ l ⟩ u U.[ σ₁ ] ≡ u U.[ σ₂ ] ∷ A U.[ σ₁ ]))    ⇔˘⟨ ⊩ᵛ∷⇔ʰ ×-cong-⇔ ⊩ᵛ∷⇔ʰ ⟩

    Γ ⊩ᵛ⟨ l ⟩ t ∷ A × Γ ⊩ᵛ⟨ l ⟩ u ∷ A                    □⇔

------------------------------------------------------------------------
-- Id

opaque

  -- Validity of equality preservation for Id, seen as a type former.

  Id-congᵛ :
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l′ ⟩ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊩ᵛ⟨ l″ ⟩ u₁ ≡ u₂ ∷ A₁ →
    Γ ⊩ᵛ⟨ l ⟩ Id A₁ t₁ u₁ ≡ Id A₂ t₂ u₂
  Id-congᵛ A₁≡A₂ t₁≡t₂ u₁≡u₂ =
    let ⊩A₁ , _ , A₁≡A₂ = ⊩ᵛ≡⇔″ .proj₁ A₁≡A₂ in
    ⊩ᵛ≡⇔ʰ .proj₂
      ( wf-⊩ᵛ ⊩A₁
      , λ σ₁≡σ₂ →
          ⊩Id≡Id⇔ .proj₂
            ( R.⊩≡→ (A₁≡A₂ σ₁≡σ₂)
            , R.⊩≡∷→
                (⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (level-⊩ᵛ≡∷ ⊩A₁ t₁≡t₂) σ₁≡σ₂)
            , R.⊩≡∷→
                (⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (level-⊩ᵛ≡∷ ⊩A₁ u₁≡u₂) σ₁≡σ₂)
            )
      )

opaque

  -- Validity of Id, seen as a type former.

  Idᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ Id A t u
  Idᵛ ⊩t ⊩u =
    ⊩ᵛ⇔⊩ᵛ≡ .proj₂ $
    Id-congᵛ (refl-⊩ᵛ≡ $ wf-⊩ᵛ∷ ⊩t) (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ᵛ≡∷ ⊩u)

opaque

  -- Validity of equality preservation for Id, seen as a term former.

  Id-congᵗᵛ :
    Γ ⊩ᵛ⟨ l′ ⟩ A₁ ≡ A₂ ∷ U k →
    Γ ⊩ᵛ⟨ l″ ⟩ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊩ᵛ⟨ l‴ ⟩ u₁ ≡ u₂ ∷ A₁ →
    Γ ⊩ᵛ⟨ l′ ⟩ Id A₁ t₁ u₁ ≡ Id A₂ t₂ u₂ ∷ U k
  Id-congᵗᵛ A₁≡A₂∷U t₁≡t₂ u₁≡u₂ =
    let ⊩U , A₁≡A₂∷U = ⊩ᵛ≡∷⇔ʰ .proj₁ A₁≡A₂∷U in
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( ⊩U
      , λ σ₁≡σ₂ →
          →⊩Id≡Id∷U (A₁≡A₂∷U σ₁≡σ₂)
            (R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t₁≡t₂ σ₁≡σ₂)
            (R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ u₁≡u₂ σ₁≡σ₂)
      )

opaque

  -- Validity of Id, seen as a term former.

  Idᵗᵛ :
    Γ ⊩ᵛ⟨ l′ ⟩ A ∷ U k →
    Γ ⊩ᵛ⟨ l″ ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l‴ ⟩ u ∷ A →
    Γ ⊩ᵛ⟨ l′ ⟩ Id A t u ∷ U k
  Idᵗᵛ ⊩A∷U ⊩t ⊩u =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    Id-congᵗᵛ (refl-⊩ᵛ≡∷ ⊩A∷U) (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ᵛ≡∷ ⊩u)

------------------------------------------------------------------------
-- The term rfl

opaque

  -- Reducibility of reflexivity.

  ⊩rfl′ :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ rfl ∷ Id A t u
  ⊩rfl′ t≡u =
    let ⊩t , ⊩u = wf-⊩≡∷ t≡u
        ⊢t      = escape-⊩∷ ⊩t
    in
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
    let ⊩t , ⊩u = wf-⊩≡∷ t≡u
        ⊢rfl    = escape-⊩∷ (⊩rfl′ t≡u)
    in
    Identity→⊩≡∷Id⇔ rflₙ rflₙ .proj₂
      (⊢rfl , ⊢rfl , ⊩t , ⊩u , rfl₌ t≡u)

opaque

  -- Validity of equality for rfl.

  rfl-congᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ rfl ≡ rfl ∷ Id A t t
  rfl-congᵛ ⊩t =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( Idᵛ ⊩t ⊩t
      , ⊩rfl≡rfl ∘→ ⊩ᵛ∷⇔ʰ .proj₁ ⊩t .proj₂ ∘→
        refl-⊩ˢ≡∷ ∘→ proj₁ ∘→ wf-⊩ˢ≡∷
      )

opaque

  -- Validity of reflexivity.

  rflᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ rfl ∷ Id A t t
  rflᵛ = ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ ∘→ rfl-congᵛ

------------------------------------------------------------------------
-- Equality reflection

opaque

  -- Validity of equality reflection.

  equality-reflectionᵛ :
    Equality-reflection →
    Γ ⊩ᵛ⟨ l ⟩ v ∷ Id A t u →
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A
  equality-reflectionᵛ ok ⊩v =
    let ⊩Id , v≡v = ⊩ᵛ∷⇔ʰ .proj₁ ⊩v
        ⊩t , ⊩u   = ⊩ᵛId⇔ .proj₁ ⊩Id
    in
    ⊩ᵛ≡∷⇔′ʰ .proj₂
      ( ⊩t
      , ⊩u
      , λ ⊩σ →
          case ⊩≡∷Id⇔ .proj₁ $ v≡v $ refl-⊩ˢ≡∷ ⊩σ of λ
            (_ , _ , _ , _ , _ , _ , rest) →
          case rest of λ where
            (rfl₌ t[σ]≡u[σ]) → t[σ]≡u[σ]
            (ne inc _ _ _)   →
              ⊥-elim $
              Equality-reflection-allowed→¬Neutrals-included ok inc
      )

------------------------------------------------------------------------
-- []-cong

opaque

  -- Reducibility of equality between applications of []-cong.

  ⊩[]-cong≡[]-cong :
    (ok : []-cong-allowed s) →
    let open E ok in
    Γ ⊩Level k₁ ≡ k₂ ∷Level →
    Γ ⊩⟨ l ⟩ A₁ ≡ A₂ →
    Γ ⊩⟨ l′ ⟩ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊩⟨ l″ ⟩ u₁ ≡ u₂ ∷ A₁ →
    Γ ⊩⟨ l‴ ⟩ v₁ ≡ v₂ ∷ Id A₁ t₁ u₁ →
    Γ ⊩⟨ l ⟩ []-cong s k₁ A₁ t₁ u₁ v₁ ≡ []-cong s k₂ A₂ t₂ u₂ v₂ ∷
      Id (Erased k₁ A₁) [ t₁ ] [ u₁ ]
  ⊩[]-cong≡[]-cong
    {s} {k₁} {k₂} {A₁} {A₂} {t₁} {t₂} {u₁} {u₂} {v₁} {v₂}
    ok k₁≡k₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ =
    let ⊩k₁ , _   = wf-Level-eq k₁≡k₂
        k₁≅k₂     = escapeLevelEq k₁≡k₂
        ⊩A₁ , _   = wf-⊩≡ A₁≡A₂
        A₁≅A₂     = escape-⊩≡ A₁≡A₂
        t₁≡t₂     = level-⊩≡∷ ⊩A₁ t₁≡t₂
        t₁≅t₂     = escape-⊩≡∷ t₁≡t₂
        ⊩t₁ , _   = wf-⊩≡∷ t₁≡t₂
        u₁≡u₂     = level-⊩≡∷ ⊩A₁ u₁≡u₂
        u₁≅u₂     = escape-⊩≡∷ u₁≡u₂
        ⊩u₁ , _   = wf-⊩≡∷ u₁≡u₂
        v₁≡v₂     = level-⊩≡∷ (⊩Id⇔ .proj₂ (⊩t₁ , ⊩u₁)) v₁≡v₂
        ⊢k₁≡k₂    = ⊢≅∷L→⊢≡∷L k₁≅k₂
        ⊢k₁ , ⊢k₂ = wf-⊢≡∷L ⊢k₁≡k₂
        ⊢A₁≡A₂    = ≅-eq A₁≅A₂
        ⊢t₁≡t₂    = ≅ₜ-eq t₁≅t₂
        ⊢u₁≡u₂    = ≅ₜ-eq u₁≅u₂
        ⊢Id≡Id    =
          let ok = []-cong→Erased ok in
          Id-cong (Erased-cong ok ⊢k₁≡k₂ ⊢A₁≡A₂)
            ([]-cong′ ok ⊢k₁ ⊢t₁≡t₂) ([]-cong′ ok ⊢k₁ ⊢u₁≡u₂)
    in
    case ⊩≡∷Id⇔ .proj₁ v₁≡v₂ of λ
      (v₁′ , v₂′ , v₁⇒*v₁′ , v₂⇒*v₂′ , ⊩t , ⊩u , rest) →
    let []-cong⇒*[]-cong₁ = []-cong-subst* ⊢k₁ v₁⇒*v₁′ ok
        []-cong⇒*[]-cong₂ =
          []-cong-subst* ⊢k₂
            (conv* v₂⇒*v₂′ (Id-cong ⊢A₁≡A₂ ⊢t₁≡t₂ ⊢u₁≡u₂)) ok
    in
    case rest of λ where
      (rfl₌ t₁≡u₁) →
        let t₂≡u₂ =
                   ˘⟨ A₁≡A₂ ⟩⊩∷
              t₂  ≡˘⟨ t₁≡t₂ ⟩⊩∷
              t₁  ≡⟨ t₁≡u₁ ⟩⊩∷
              u₁  ≡⟨ u₁≡u₂ ⟩⊩∷∎
              u₂  ∎
        in
        []-cong s k₁ A₁ t₁ u₁ v₁               ⇒*⟨ []-cong⇒*[]-cong₁ ⟩⊩∷
        []-cong s k₁ A₁ t₁ u₁ rfl              ⇒⟨ []-cong-β ⊢k₁ (≅ₜ-eq (escape-⊩≡∷ t₁≡u₁)) ok ⟩⊩∷
        rfl ∷ Id (Erased k₁ A₁) [ t₁ ] [ u₁ ]  ≡⟨ refl-⊩≡∷ (⊩rfl′ (⊩[]≡[] ⊩k₁ t₁≡u₁)) ⟩⊩∷∷⇐*
                                                ⟨ ⊢Id≡Id ⟩⇒
        rfl ∷ Id (Erased k₂ A₂) [ t₂ ] [ u₂ ]  ⇐⟨ []-cong-β ⊢k₂ (≅ₜ-eq (escape-⊩≡∷ t₂≡u₂)) ok ⟩∷
        []-cong s k₂ A₂ t₂ u₂ rfl              ⇐*⟨ []-cong⇒*[]-cong₂ ⟩∎
        []-cong s k₂ A₂ t₂ u₂ v₂               ∎

      (ne inc v₁′-ne v₂′-ne v₁′~v₂′) →
        []-cong s k₁ A₁ t₁ u₁ v₁                                     ⇒*⟨ []-cong⇒*[]-cong₁ ⟩⊩∷
        []-cong s k₁ A₁ t₁ u₁ v₁′ ∷ Id (Erased k₁ A₁) [ t₁ ] [ u₁ ]  ≡⟨ neutral-⊩≡∷ inc (⊩Id⇔ .proj₂ (⊩[] ⊩k₁ ⊩t₁ , ⊩[] ⊩k₁ ⊩u₁))
                                                                          ([]-congₙ v₁′-ne) ([]-congₙ v₂′-ne)
                                                                          (~-[]-cong k₁≅k₂ A₁≅A₂ t₁≅t₂ u₁≅u₂ v₁′~v₂′ ok) ⟩⊩∷∷⇐*
                                                                       ⟨ ⊢Id≡Id ⟩⇒
        []-cong s k₂ A₂ t₂ u₂ v₂′ ∷ Id (Erased k₂ A₂) [ t₂ ] [ u₂ ]  ⇐*⟨ []-cong⇒*[]-cong₂ ⟩∎∷
        []-cong s k₂ A₂ t₂ u₂ v₂                                     ∎
    where
    open E ok

opaque

  -- Reducibility for []-cong.

  ⊩[]-cong :
    (ok : []-cong-allowed s) →
    let open E ok in
    Γ ⊩Level k ∷Level →
    Γ ⊩⟨ l ⟩ v ∷ Id A t u →
    Γ ⊩⟨ l ⟩ []-cong s k A t u v ∷ Id (Erased k A) [ t ] [ u ]
  ⊩[]-cong ok ⊩k ⊩v =
    let _ , _ , ⊩t , ⊩u , _ = ⊩∷Id⇔ .proj₁ ⊩v in
    ⊩∷⇔⊩≡∷ .proj₂ $
    ⊩[]-cong≡[]-cong ok (reflLevel ⊩k) (refl-⊩≡ (wf-⊩∷ ⊩t))
      (refl-⊩≡∷ ⊩t) (refl-⊩≡∷ ⊩u) (refl-⊩≡∷ ⊩v)

opaque

  -- Validity of equality preservation for []-cong.

  []-cong-congᵛ :
    (ok : []-cong-allowed s) →
    let open E ok in
    Γ ⊩ᵛ⟨ l′ ⟩ k₁ ≡ k₂ ∷Level →
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l″ ⟩ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊩ᵛ⟨ l‴ ⟩ u₁ ≡ u₂ ∷ A₁ →
    Γ ⊩ᵛ⟨ l⁗ ⟩ v₁ ≡ v₂ ∷ Id A₁ t₁ u₁ →
    Γ ⊩ᵛ⟨ l ⟩ []-cong s k₁ A₁ t₁ u₁ v₁ ≡ []-cong s k₂ A₂ t₂ u₂ v₂ ∷
      Id (Erased k₁ A₁) [ t₁ ] [ u₁ ]
  []-cong-congᵛ ok k₁≡k₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ =
    let ⊩k₁ , _ = wf-⊩ᵛ≡∷L k₁≡k₂ in
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( wf-⊩ᵛ≡
          (Id-congᵛ (Erased-congᵛ k₁≡k₂ A₁≡A₂)
             ([]-congᵛ′ ⊩k₁ t₁≡t₂) ([]-congᵛ′ ⊩k₁ u₁≡u₂))
          .proj₁
      , λ σ₁≡σ₂ →
          PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) Id-Erased-[] $
          ⊩[]-cong≡[]-cong ok (⊩ᵛ≡∷L→⊩ˢ≡∷→⊩[]≡[]∷L k₁≡k₂ σ₁≡σ₂)
            (R.⊩≡→ $ ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] A₁≡A₂ σ₁≡σ₂)
            (R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t₁≡t₂ σ₁≡σ₂)
            (R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ u₁≡u₂ σ₁≡σ₂)
            (R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ v₁≡v₂ σ₁≡σ₂)
      )
    where
    open E ok

opaque

  -- Validity of []-cong.

  []-congᵛ :
    (ok : []-cong-allowed s) →
    let open E ok in
    Γ ⊩ᵛ⟨ l′ ⟩ k ∷Level →
    Γ ⊩ᵛ⟨ l ⟩ v ∷ Id A t u →
    Γ ⊩ᵛ⟨ l ⟩ []-cong s k A t u v ∷ Id (Erased k A) [ t ] [ u ]
  []-congᵛ ok ⊩k ⊩v =
    let ⊩t , ⊩u = ⊩ᵛId⇔ .proj₁ $ wf-⊩ᵛ∷ ⊩v in
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    []-cong-congᵛ ok (refl-⊩ᵛ≡∷L ⊩k) (refl-⊩ᵛ≡ (wf-⊩ᵛ∷ ⊩t))
      (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ᵛ≡∷ ⊩u) (refl-⊩ᵛ≡∷ ⊩v)

opaque

  -- Validity of the []-cong β rule.

  []-cong-βᵛ :
    (ok : []-cong-allowed s) →
    let open E ok in
    Γ ⊩ᵛ⟨ l′ ⟩ k ∷Level →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ []-cong s k A t t rfl ≡ rfl ∷ Id (Erased k A) [ t ] [ t ]
  []-cong-βᵛ ok ⊩k ⊩t =
    ⊩ᵛ∷-⇐
      (λ ⊩σ →
         PE.subst (_⊢_⇒_∷_ _ _ _) Id-Erased-[] $
         let ⊢k[σ] = escapeLevel $ ⊩ᵛ∷L→⊩ˢ∷→⊩[]∷L ⊩k ⊩σ
             ⊢t[σ] = R.escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t ⊩σ
         in
         []-cong-β ⊢k[σ] (refl ⊢t[σ]) ok)
      (rflᵛ ([]ᵛ ⊩k ⊩t))
    where
    open E ok

------------------------------------------------------------------------
-- The K rule

opaque

  -- Reducibility of equality between applications of K.

  ⊩K≡K :
    K-allowed →
    Γ ⊩ᵛ⟨ l′ ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l″ ⟩ t₁ ≡ t₂ ∷ A₁ →
    Γ ∙ Id A₁ t₁ t₁ ⊢ B₁ ≡ B₂ →
    Γ ∙ Id A₁ t₁ t₁ ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    Γ ⊩ᵛ⟨ l‴ ⟩ u₁ ≡ u₂ ∷ B₁ [ rfl ]₀ →
    Γ ⊩ᵛ⟨ l⁗ ⟩ v₁ ≡ v₂ ∷ Id A₁ t₁ t₁ →
    ⦃ inc : Neutrals-included or-empty Δ ⦄ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l ⟩ K p A₁ t₁ B₁ u₁ v₁ U.[ σ₁ ] ≡ K p A₂ t₂ B₂ u₂ v₂ U.[ σ₂ ] ∷
      B₁ [ v₁ ]₀ U.[ σ₁ ]
  ⊩K≡K
    {A₁} {A₂} {t₁} {t₂} {B₁} {B₂} {u₁} {u₂} {v₁} {v₂} {σ₁} {σ₂} {p}
    ok A₁≡A₂ t₁≡t₂ ⊢B₁≡B₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ σ₁≡σ₂ =
    let -- Some definitions related to σ₁ and σ₂.
        ⊩σ₁ , ⊩σ₂ = wf-⊩ˢ≡∷ σ₁≡σ₂

        -- Some definitions related to Id.
        Id≡Id          = Id-congᵛ A₁≡A₂ t₁≡t₂ t₁≡t₂
        Id[σ₁]≡Id[σ₂]  = R.⊩≡→ $ ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] Id≡Id σ₁≡σ₂
        ⊢Id[σ₁]≡Id[σ₂] = ≅-eq $ escape-⊩≡ Id[σ₁]≡Id[σ₂]

        -- Some definitions related to t₁ and t₂.
        ⊩t₁ , _       = wf-⊩ᵛ≡∷ t₁≡t₂
        t₁[σ₁]≡t₂[σ₂] =
          ≅ₜ-eq $ R.escape-⊩≡∷ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t₁≡t₂ σ₁≡σ₂

        -- Some definitions related to B₁ and B₂.
        ⊩B₁ , ⊩B₂           = wf-⊩ᵛ≡ B₁≡B₂
        ⊩B₂                 = conv-∙-⊩ᵛ Id≡Id ⊩B₂
        ⊢B₁[σ₁⇑] , ⊢B₂[σ₂⇑] =
          wf-⊢≡ $ subst-⊢≡-⇑ ⊢B₁≡B₂ $ escape-⊩ˢ≡∷ σ₁≡σ₂ .proj₂
        ⊢B₂[σ₂⇑] =
          stability
            (refl-∙ $
             Id-cong
               (≅-eq $ R.escape-⊩≡ $ ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] A₁≡A₂ σ₁≡σ₂)
               t₁[σ₁]≡t₂[σ₂] t₁[σ₁]≡t₂[σ₂])
            ⊢B₂[σ₂⇑]

        -- Some definitions related to u₁ and u₂.
        ⊩u₁ , ⊩u₂ = wf-⊩ᵛ≡∷ u₁≡u₂
        ⊩u₂       = conv-⊩ᵛ∷
                      (⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀ B₁≡B₂ (refl-⊩ᵛ≡∷ (rflᵛ ⊩t₁)))
                      ⊩u₂
        ⊢u₁[σ₁]   =
          PE.subst (_⊢_∷_ _ _) (singleSubstLift B₁ _) $
          R.escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u₁ ⊩σ₁
        ⊢u₂[σ₂] =
          PE.subst (_⊢_∷_ _ _) (singleSubstLift B₂ _) $
          R.escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u₂ ⊩σ₂
        u₁[σ₁]≡u₂[σ₂] =
          PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (singleSubstLift B₁ _) $
          R.⊩≡∷→ $
          ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷
            (level-⊩ᵛ≡∷ (⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ ⊩B₁ (rflᵛ ⊩t₁)) u₁≡u₂) σ₁≡σ₂

        -- Some definitions related to v₁ and v₂.
        ⊩v₁ , ⊩v₂ = wf-⊩ᵛ≡∷ v₁≡v₂
        ⊩v₂       = conv-⊩ᵛ∷ Id≡Id ⊩v₂
        v₁[σ₁]≡v₂[σ₂] = R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ v₁≡v₂ σ₁≡σ₂
    in
    case ⊩≡∷Id⇔ .proj₁ v₁[σ₁]≡v₂[σ₂] of λ
      (v₁′ , v₂′ , v₁[σ₁]⇒*v₁′ , v₂[σ₂]⇒*v₂′ , _ , _ , rest) →
    let v₂[σ₂]⇒*v₂′ = conv* v₂[σ₂]⇒*v₂′ ⊢Id[σ₁]≡Id[σ₂]

        -- Some definitions related to v₁′ and v₂′.
        v₁[σ₁]≡v₁′ =
          ⊩∷-⇒* v₁[σ₁]⇒*v₁′ $ R.⊩∷→ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩v₁ ⊩σ₁
        v₂[σ₂]≡v₂′ =
          ⊩∷-⇒* v₂[σ₂]⇒*v₂′ $ R.⊩∷→ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩v₂ ⊩σ₂
        B₁[σ₁⇑][v₁′]₀≡B₂[σ₂⇑][v₂′]₀ =
          R.⊩≡→ $ ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ B₁≡B₂ σ₁≡σ₂ $
          R.→⊩≡∷
            (v₁′                                 ≡˘⟨ v₁[σ₁]≡v₁′ ⟩⊩∷
             v₁ U.[ σ₁ ] ∷ Id A₁ t₁ t₁ U.[ σ₁ ]  ≡⟨ v₁[σ₁]≡v₂[σ₂] ⟩⊩∷∷
                                                  ⟨ Id[σ₁]≡Id[σ₂] ⟩⊩∷
             v₂ U.[ σ₂ ] ∷ Id A₂ t₂ t₂ U.[ σ₂ ]  ≡⟨ v₂[σ₂]≡v₂′ ⟩⊩∷∎∷
             v₂′                                 ∎)
        ⊢B₁[σ₁⇑][v₁′]₀≡B₂[σ₂⇑][v₂′]₀ =
          ≅-eq $ escape-⊩≡ B₁[σ₁⇑][v₁′]₀≡B₂[σ₂⇑][v₂′]₀

        -- The two applications of K are equal if applications of K to
        -- v₁′ and v₂′ are equal.
        lemma = λ hyp →
          K p (A₁ U.[ σ₁ ]) (t₁ U.[ σ₁ ]) (B₁ U.[ σ₁ ⇑ ]) (u₁ U.[ σ₁ ])
            (v₁ U.[ σ₁ ]) ∷ B₁ [ v₁ ]₀ U.[ σ₁ ]                          ≡⟨⟩⊩∷∷
                                                                          ⟨ singleSubstLift B₁ _ ⟩⊩∷≡
          _               ∷ B₁ U.[ σ₁ ⇑ ] [ v₁ U.[ σ₁ ] ]₀               ⇒*⟨ K-subst* ⊢B₁[σ₁⇑] ⊢u₁[σ₁] v₁[σ₁]⇒*v₁′ ok ⟩⊩∷∷
                                                                           ⟨ R.⊩≡→ $
                                                                             ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀
                                                                               (refl-⊩ᵛ≡ ⊩B₁) (refl-⊩ˢ≡∷ ⊩σ₁) (R.→⊩≡∷ v₁[σ₁]≡v₁′) ⟩⊩∷
          K p (A₁ U.[ σ₁ ]) (t₁ U.[ σ₁ ]) (B₁ U.[ σ₁ ⇑ ]) (u₁ U.[ σ₁ ])
            v₁′ ∷ B₁ U.[ σ₁ ⇑ ] [ v₁′ ]₀                                 ≡⟨ hyp ⟩⊩∷∷⇐*
                                                                          ⟨ ⊢B₁[σ₁⇑][v₁′]₀≡B₂[σ₂⇑][v₂′]₀ ⟩⇒
                ∷ B₂ U.[ σ₂ ⇑ ] [ v₂′ ]₀                                 ˘⟨ ≅-eq $ escape-⊩≡ $ R.⊩≡→ $
                                                                            ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀
                                                                              (refl-⊩ᵛ≡ ⊩B₂) (refl-⊩ˢ≡∷ ⊩σ₂) (R.→⊩≡∷ v₂[σ₂]≡v₂′) ⟩⇒
          K p (A₂ U.[ σ₂ ]) (t₂ U.[ σ₂ ]) (B₂ U.[ σ₂ ⇑ ]) (u₂ U.[ σ₂ ])
            v₂′ ∷ B₂ U.[ σ₂ ⇑ ] [ v₂ U.[ σ₂ ] ]₀                         ⇐*⟨ K-subst* ⊢B₂[σ₂⇑] ⊢u₂[σ₂] v₂[σ₂]⇒*v₂′ ok ⟩∎∷
          K p (A₂ U.[ σ₂ ]) (t₂ U.[ σ₂ ]) (B₂ U.[ σ₂ ⇑ ]) (u₂ U.[ σ₂ ])
            (v₂ U.[ σ₂ ])                                                ∎
    in
    case rest of λ where
      (rfl₌ _) →
        -- If v₁′ and v₂′ are both rfl, then one can conclude by using
        -- the β-rule for K and the fact that u₁ [σ₁] is equal to
        -- u₂ [σ₂].
        lemma
          (K p A₁ t₁ B₁ u₁ rfl U.[ σ₁ ]          ⇒⟨ K-β ⊢B₁[σ₁⇑] ⊢u₁[σ₁] ok ⟩⊩∷
           u₁ U.[ σ₁ ] ∷ B₁ U.[ σ₁ ⇑ ] [ rfl ]₀  ≡⟨ u₁[σ₁]≡u₂[σ₂] ⟩⊩∷∷⇐*
                                                  ⟨ ⊢B₁[σ₁⇑][v₁′]₀≡B₂[σ₂⇑][v₂′]₀ ⟩⇒
           u₂ U.[ σ₂ ] ∷ B₂ U.[ σ₂ ⇑ ] [ rfl ]₀  ⇐⟨ K-β ⊢B₂[σ₂⇑] ⊢u₂[σ₂] ok ⟩∎∷
           K p A₂ t₂ B₂ u₂ rfl U.[ σ₂ ]          ∎)

      (ne inc v₁′-ne v₂′-ne v₁′~v₂′) →
        -- If v₁′ and v₂′ are equal neutral terms, then one can
        -- conclude by using the fact that the applications of K to
        -- v₁′ and v₂′ are equal neutral terms.
        lemma $
        neutral-⊩≡∷ inc
          (wf-⊩≡ B₁[σ₁⇑][v₁′]₀≡B₂[σ₂⇑][v₂′]₀ .proj₁)
          (Kₙ v₁′-ne) (Kₙ v₂′-ne) $
        ~-K (R.escape-⊩≡ $ ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] A₁≡A₂ σ₁≡σ₂)
          (R.escape-⊩≡∷ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t₁≡t₂ σ₁≡σ₂)
          (R.escape-⊩≡ ⦃ inc = included ⦃ inc = inc ⦄ ⦄ $
           ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑]≡[⇑] B₁≡B₂ σ₁≡σ₂)
          (escape-⊩≡∷ u₁[σ₁]≡u₂[σ₂]) v₁′~v₂′ ok

opaque

  -- Validity of equality preservation for K.

  K-congᵛ :
    K-allowed →
    Γ ⊩ᵛ⟨ l′ ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l″ ⟩ t₁ ≡ t₂ ∷ A₁ →
    Γ ∙ Id A₁ t₁ t₁ ⊢ B₁ ≡ B₂ →
    Γ ∙ Id A₁ t₁ t₁ ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    Γ ⊩ᵛ⟨ l‴ ⟩ u₁ ≡ u₂ ∷ B₁ [ rfl ]₀ →
    Γ ⊩ᵛ⟨ l⁗ ⟩ v₁ ≡ v₂ ∷ Id A₁ t₁ t₁ →
    Γ ⊩ᵛ⟨ l ⟩ K p A₁ t₁ B₁ u₁ v₁ ≡ K p A₂ t₂ B₂ u₂ v₂ ∷ B₁ [ v₁ ]₀
  K-congᵛ ok A₁≡A₂ t₁≡t₂ ⊢B₁≡B₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ (wf-⊩ᵛ≡ B₁≡B₂ .proj₁) (wf-⊩ᵛ≡∷ v₁≡v₂ .proj₁)
      , ⊩K≡K ok A₁≡A₂ t₁≡t₂ ⊢B₁≡B₂ B₁≡B₂ u₁≡u₂ v₁≡v₂
      )

opaque

  -- Validity of K.

  Kᵛ :
    K-allowed →
    Γ ∙ Id A t t ⊢ B →
    Γ ∙ Id A t t ⊩ᵛ⟨ l ⟩ B →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ B [ rfl ]₀ →
    Γ ⊩ᵛ⟨ l″ ⟩ v ∷ Id A t t →
    Γ ⊩ᵛ⟨ l ⟩ K p A t B u v ∷ B [ v ]₀
  Kᵛ ok ⊢B ⊩B ⊩u ⊩v =
    let ⊩t , _ = ⊩ᵛId⇔ .proj₁ $ wf-⊩ᵛ∷ ⊩v
        ⊩A     = wf-⊩ᵛ∷ ⊩t
    in
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    K-congᵛ ok (refl-⊩ᵛ≡ ⊩A) (refl-⊩ᵛ≡∷ ⊩t) (refl ⊢B) (refl-⊩ᵛ≡ ⊩B)
      (refl-⊩ᵛ≡∷ ⊩u) (refl-⊩ᵛ≡∷ ⊩v)

opaque

  -- Validity of the K β rule.

  K-βᵛ :
    K-allowed →
    Γ ∙ Id A t t ⊢ B →
    Γ ⊩ᵛ⟨ l ⟩ u ∷ B [ rfl ]₀ →
    Γ ⊩ᵛ⟨ l ⟩ K p A t B u rfl ≡ u ∷ B [ rfl ]₀
  K-βᵛ {B} ok ⊢B ⊩u =
    ⊩ᵛ∷-⇐
      (λ ⊩σ →
         PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift B _) $
         K-β
           (subst-⊢-⇑ ⊢B (escape-⊩ˢ∷ ⊩σ .proj₂))
           (PE.subst (_⊢_∷_ _ _) (singleSubstLift B _) $
            R.escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u ⊩σ)
           ok)
      ⊩u

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

opaque

  -- Reducibility of equality between applications of J.

  ⊩J≡J :
    Γ ⊩ᵛ⟨ l′₁ ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l′₂ ⟩ t₁ ≡ t₂ ∷ A₁ →
    Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ ≡ B₂ →
    Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    Γ ⊩ᵛ⟨ l′₃ ⟩ u₁ ≡ u₂ ∷ B₁ [ t₁ , rfl ]₁₀ →
    Γ ⊩ᵛ⟨ l′₄ ⟩ v₁ ≡ v₂ ∷ A₁ →
    Γ ⊩ᵛ⟨ l′₅ ⟩ w₁ ≡ w₂ ∷ Id A₁ t₁ v₁ →
    ⦃ inc : Neutrals-included or-empty Δ ⦄ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l ⟩ J p q A₁ t₁ B₁ u₁ v₁ w₁ U.[ σ₁ ] ≡
      J p q A₂ t₂ B₂ u₂ v₂ w₂ U.[ σ₂ ] ∷ B₁ [ v₁ , w₁ ]₁₀ U.[ σ₁ ]
  ⊩J≡J
    {A₁} {A₂} {t₁} {t₂} {B₁} {B₂} {u₁} {u₂} {v₁} {v₂} {w₁} {w₂} {σ₁}
    {σ₂} {p} {q} A₁≡A₂ t₁≡t₂ ⊢B₁≡B₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂ σ₁≡σ₂ =


    let -- Some definitions related to σ₁ and σ₂.
        ⊩σ₁ , ⊩σ₂   = wf-⊩ˢ≡∷ σ₁≡σ₂
        _ , ⊢σ₁≡σ₂  = escape-⊩ˢ≡∷ σ₁≡σ₂
        _ , _ , ⊢σ₂ = wf-⊢ˢʷ≡∷ ⊢σ₁≡σ₂

        -- Some definitions related to A₁ and A₂.
        ⊩A₁ , _        = wf-⊩ᵛ≡ A₁≡A₂
        A₁[σ₁]≡A₂[σ₂]  = R.⊩≡→ $ ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] A₁≡A₂ σ₁≡σ₂
        A₁[σ₁]≅A₂[σ₂]  = escape-⊩≡ A₁[σ₁]≡A₂[σ₂]
        ⊢A₁[σ₁]≡A₂[σ₂] = ≅-eq A₁[σ₁]≅A₂[σ₂]
        ⊢A₁[σ₁] , _    = wf-⊢≡ ⊢A₁[σ₁]≡A₂[σ₂]

        -- Some definitions related to t₁ and t₂.
        t₁[σ₁]≡t₂[σ₂]     = R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t₁≡t₂ σ₁≡σ₂
        ⊩t₁[σ₁] , ⊩t₂[σ₂] = wf-⊩≡∷ t₁[σ₁]≡t₂[σ₂]
        ⊩t₂[σ₂]           = conv-⊩∷ A₁[σ₁]≡A₂[σ₂] ⊩t₂[σ₂]
        rfl≡rfl           =
          R.refl-⊩≡∷ $ R.→⊩∷ $
          PE.subst (_⊩⟨_⟩_∷_ _ _ _) (Id[]≡Id-wk1-0-[⇑][]₀ A₁ t₁) $
          ⊩rfl ⊩t₁[σ₁]

        -- Some definitions related to Id.
        Id-v₁≡Id-v₂         = Id-congᵛ A₁≡A₂ t₁≡t₂ v₁≡v₂
        Id-v₁[σ₁]≡Id-v₂[σ₂] = R.⊩≡→ $ ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] Id-v₁≡Id-v₂ σ₁≡σ₂

        -- Some definitions related to B₁ and B₂.
        ⊩B₁ , ⊩B₂ = wf-⊩ᵛ≡ B₁≡B₂
        ⊩B₂       =
          conv-∙∙-⊩ᵛ A₁≡A₂
            (Id-congᵛ (wk1-⊩ᵛ≡ ⊩A₁ A₁≡A₂) (wk1-⊩ᵛ≡∷ ⊩A₁ t₁≡t₂)
               (refl-⊩ᵛ≡∷ (varᵛ′ here (wk1-⊩ᵛ ⊩A₁ ⊩A₁))))
            ⊩B₂
        ⊢B₁[σ₁⇑⇑][t₁[σ₁],rfl]≡B₂[σ₂⇑⇑][t₂[σ₂],rfl] =
          ≅-eq $ R.escape-⊩≡ $
          ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀ B₁≡B₂ σ₁≡σ₂
            (R.→⊩≡∷ t₁[σ₁]≡t₂[σ₂]) rfl≡rfl
        ⊢B₁[σ₁⇑²] , ⊢B₁[σ₂⇑²] =
          wf-⊢≡ $
          PE.subst₃ _⊢_≡_
            (PE.cong (_∙_ _) $ Id-wk1-wk1-0[⇑]≡ A₁ t₁) PE.refl PE.refl $
          subst-⊢≡-⇑ ⊢B₁≡B₂ ⊢σ₁≡σ₂
        ⊢B₂[σ₂⇑²] =
          stability
            (refl-∙ ⊢A₁[σ₁]≡A₂[σ₂] ∙
             Id-cong (wkEq₁ ⊢A₁[σ₁] ⊢A₁[σ₁]≡A₂[σ₂])
               (wkEqTerm₁ ⊢A₁[σ₁] (≅ₜ-eq $ escape-⊩≡∷ t₁[σ₁]≡t₂[σ₂]))
               (refl (var₀ ⊢A₁[σ₁])))
            ⊢B₁[σ₂⇑²]

        -- Some definitions related to u₁ and u₂.
        u₁[σ₁]≡u₂[σ₂] =
          PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) ([,]-[]-commute B₁) $
          R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ u₁≡u₂ σ₁≡σ₂
        ⊢u₁[σ₁] =
          escape-⊩∷ $ wf-⊩≡∷ u₁[σ₁]≡u₂[σ₂] .proj₁
        ⊢u₂[σ₂] =
          _⊢_∷_.conv (escape-⊩∷ $ wf-⊩≡∷ u₁[σ₁]≡u₂[σ₂] .proj₂)
            ⊢B₁[σ₁⇑⇑][t₁[σ₁],rfl]≡B₂[σ₂⇑⇑][t₂[σ₂],rfl]

        -- Some definitions related to v₁ and v₂.
        v₁[σ₁]≡v₂[σ₂]     = R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ v₁≡v₂ σ₁≡σ₂
        ⊩v₁[σ₁] , ⊩v₂[σ₂] = wf-⊩≡∷ v₁[σ₁]≡v₂[σ₂]
        ⊩v₂[σ₂]           = conv-⊩∷ A₁[σ₁]≡A₂[σ₂] ⊩v₂[σ₂]

        -- Some definitions related to w₁ and w₂.
        ⊩w₁ , ⊩w₂     = wf-⊩ᵛ≡∷ w₁≡w₂
        ⊩w₂           = conv-⊩ᵛ∷ Id-v₁≡Id-v₂ ⊩w₂
        w₁[σ₁]≡w₂[σ₂] = R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ w₁≡w₂ σ₁≡σ₂
    in
    case ⊩≡∷Id⇔ .proj₁ w₁[σ₁]≡w₂[σ₂] of λ
      (w₁′ , w₂′ , w₁⇒*w₁′ , w₂⇒*w₂′ , _ , _ , rest) →
    let w₂⇒*w₂′ = conv* w₂⇒*w₂′ (≅-eq $ escape-⊩≡ Id-v₁[σ₁]≡Id-v₂[σ₂])

        -- Some definitions related to w₁′ and w₂′.
        w₁[σ₁]≡w₁′ = ⊩∷-⇒* w₁⇒*w₁′ $ R.⊩∷→ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩w₁ ⊩σ₁
        w₂[σ₂]≡w₂′ = ⊩∷-⇒* w₂⇒*w₂′ $ R.⊩∷→ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩w₂ ⊩σ₂
        w₁′≡w₂′    =
          w₁′ ∷
            Id (wk1 A₁) (wk1 t₁) (var x0) U.[ σ₁ ⇑ ] [ v₁ U.[ σ₁ ] ]₀  ≡⟨⟩⊩∷∷
                                                                       ˘⟨ Id[]≡Id-wk1-0-[⇑][]₀ A₁ t₁ ⟩⊩∷≡
          _   ∷ Id A₁ t₁ v₁ U.[ σ₁ ]                                   ≡˘⟨ w₁[σ₁]≡w₁′ ⟩⊩∷∷

          w₁ U.[ σ₁ ] ∷ Id A₁ t₁ v₁ U.[ σ₁ ]                           ≡⟨ w₁[σ₁]≡w₂[σ₂] ⟩⊩∷∷
                                                                        ⟨ Id-v₁[σ₁]≡Id-v₂[σ₂] ⟩⊩∷
          w₂ U.[ σ₂ ] ∷ Id A₂ t₂ v₂ U.[ σ₂ ]                           ≡⟨ w₂[σ₂]≡w₂′ ⟩⊩∷∎∷

          w₂′                                                          ∎
        B₁[σ₁⇑⇑][v₁[σ₁],w₁′]≡B₂[σ₂⇑⇑][v₂[σ₂],w₂′] =
          R.⊩≡→ $
          ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀ B₁≡B₂ σ₁≡σ₂
            (R.→⊩≡∷ v₁[σ₁]≡v₂[σ₂]) (R.→⊩≡∷ w₁′≡w₂′)

        -- The two applications of J are equal if applications of J to
        -- w₁′ and w₂′ are equal.
        lemma = λ hyp →
          J p q (A₁ U.[ σ₁ ]) (t₁ U.[ σ₁ ]) (B₁ U.[ σ₁ ⇑ ⇑ ])
            (u₁ U.[ σ₁ ]) (v₁ U.[ σ₁ ]) (w₁ U.[ σ₁ ])
            ∷ B₁ [ v₁ , w₁ ]₁₀ U.[ σ₁ ]                        ≡⟨⟩⊩∷∷
                                                                ⟨ [,]-[]-commute B₁ ⟩⊩∷≡
          _ ∷ B₁ U.[ σ₁ ⇑ ⇑ ] [ v₁ U.[ σ₁ ] , w₁ U.[ σ₁ ] ]₁₀  ⇒*⟨ J-subst* ⊢B₁[σ₁⇑²] ⊢u₁[σ₁] w₁⇒*w₁′ ⟩⊩∷∷
                                                                 ⟨ R.⊩≡→ $
                                                                   ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀ (refl-⊩ᵛ≡ ⊩B₁)
                                                                     (refl-⊩ˢ≡∷ ⊩σ₁) (R.→⊩≡∷ $ refl-⊩≡∷ ⊩v₁[σ₁])
                                                                     (R.→⊩≡∷ $
                                                                      PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (Id[]≡Id-wk1-0-[⇑][]₀ A₁ t₁)
                                                                        w₁[σ₁]≡w₁′) ⟩⊩∷
          J p q (A₁ U.[ σ₁ ]) (t₁ U.[ σ₁ ]) (B₁ U.[ σ₁ ⇑ ⇑ ])
            (u₁ U.[ σ₁ ]) (v₁ U.[ σ₁ ]) w₁′
             ∷ B₁ U.[ σ₁ ⇑ ⇑ ] [ v₁ U.[ σ₁ ] , w₁′ ]₁₀         ≡⟨ hyp ⟩⊩∷∷⇐*
                                                                ⟨ ≅-eq $ escape-⊩≡ B₁[σ₁⇑⇑][v₁[σ₁],w₁′]≡B₂[σ₂⇑⇑][v₂[σ₂],w₂′] ⟩⇒
             ∷ B₂ U.[ σ₂ ⇑ ⇑ ] [ v₂ U.[ σ₂ ] , w₂′ ]₁₀         ˘⟨ ≅-eq $ R.escape-⊩≡ $
                                                                  ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀ (refl-⊩ᵛ≡ ⊩B₂)
                                                                    (refl-⊩ˢ≡∷ ⊩σ₂) (R.→⊩≡∷ $ refl-⊩≡∷ ⊩v₂[σ₂])
                                                                    (R.→⊩≡∷ $
                                                                     PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (Id[]≡Id-wk1-0-[⇑][]₀ A₂ t₂)
                                                                       w₂[σ₂]≡w₂′) ⟩⇒
          J p q (A₂ U.[ σ₂ ]) (t₂ U.[ σ₂ ]) (B₂ U.[ σ₂ ⇑ ⇑ ])
            (u₂ U.[ σ₂ ]) (v₂ U.[ σ₂ ]) w₂′
            ∷ B₂ U.[ σ₂ ⇑ ⇑ ] [ v₂ U.[ σ₂ ] , w₂ U.[ σ₂ ] ]₁₀  ⇐*⟨ J-subst* ⊢B₂[σ₂⇑²] ⊢u₂[σ₂] w₂⇒*w₂′ ⟩∎∷
          J p q (A₂ U.[ σ₂ ]) (t₂ U.[ σ₂ ]) (B₂ U.[ σ₂ ⇑ ⇑ ])
            (u₂ U.[ σ₂ ]) (v₂ U.[ σ₂ ]) (w₂ U.[ σ₂ ])          ∎
    in
    case rest of λ where
      (rfl₌ t₁[σ₁]≡v₁[σ₁]) →
        -- If w₁′ and w₂′ are both rfl, then one can conclude by using
        -- the β-rule for J and the fact that u₁ [σ₁] is equal to
        -- u₂ [σ₂].
        let t₂[σ₂]≡v₂[σ₂] =
              t₂ U.[ σ₂ ] ∷ A₂ U.[ σ₂ ]  ≡⟨⟩⊩∷∷
                                          ˘⟨ A₁[σ₁]≡A₂[σ₂] ⟩⊩∷
              _           ∷ A₁ U.[ σ₁ ]  ≡˘⟨ t₁[σ₁]≡t₂[σ₂] ⟩⊩∷∷
              t₁ U.[ σ₁ ]                ≡⟨ t₁[σ₁]≡v₁[σ₁] ⟩⊩∷
              v₁ U.[ σ₁ ]                ≡⟨ v₁[σ₁]≡v₂[σ₂] ⟩⊩∷∎
              v₂ U.[ σ₂ ]                ∎
        in
        lemma
          (J p q A₁ t₁ B₁ u₁ v₁ rfl U.[ σ₁ ]
             ∷ B₁ U.[ σ₁ ⇑ ⇑ ] [ v₁ U.[ σ₁ ] , rfl ]₁₀            ≡⟨⟩⊩∷∷
                                                                   ⟨ R.⊩≡→ $
                                                                     ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀ (refl-⊩ᵛ≡ ⊩B₁)
                                                                       (refl-⊩ˢ≡∷ ⊩σ₁) (R.→⊩≡∷ $ sym-⊩≡∷ t₁[σ₁]≡v₁[σ₁])
                                                                       (R.→⊩≡∷ $ refl-⊩≡∷ $
                                                                        PE.subst (_⊩⟨_⟩_∷_ _ _ _) (Id[]≡Id-wk1-0-[⇑][]₀ A₁ t₁) $
                                                                        wf-⊩≡∷ w₁[σ₁]≡w₁′ .proj₂) ⟩⊩∷
           _ ∷ B₁ U.[ σ₁ ⇑ ⇑ ] [ t₁ U.[ σ₁ ] , rfl ]₁₀            ⇒⟨ J-β-⇒ (≅ₜ-eq (escape-⊩≡∷ t₁[σ₁]≡v₁[σ₁])) ⊢B₁[σ₁⇑²] ⊢u₁[σ₁] ⟩⊩∷∷

           u₁ U.[ σ₁ ] ∷ B₁ U.[ σ₁ ⇑ ⇑ ] [ t₁ U.[ σ₁ ] , rfl ]₁₀  ≡⟨ u₁[σ₁]≡u₂[σ₂] ⟩⊩∷∷⇐*
                                                                   ⟨ ⊢B₁[σ₁⇑⇑][t₁[σ₁],rfl]≡B₂[σ₂⇑⇑][t₂[σ₂],rfl] ⟩⇒
           u₂ U.[ σ₂ ] ∷ B₂ U.[ σ₂ ⇑ ⇑ ] [ t₂ U.[ σ₂ ] , rfl ]₁₀  ⇐⟨ J-β-⇒ (≅ₜ-eq (escape-⊩≡∷ t₂[σ₂]≡v₂[σ₂])) ⊢B₂[σ₂⇑²] ⊢u₂[σ₂] ⟩∎∷

           J p q A₂ t₂ B₂ u₂ v₂ rfl U.[ σ₂ ]                      ∎)

      (ne inc w₁′-ne w₂′-ne w₁′~w₂′) →
        -- If w₁′ and w₂′ are equal neutral terms, then one can
        -- conclude by using the fact that the applications of J to
        -- w₁′ and w₂′ are equal neutral terms.
        lemma $
        neutral-⊩≡∷ inc
          (wf-⊩≡ B₁[σ₁⇑⇑][v₁[σ₁],w₁′]≡B₂[σ₂⇑⇑][v₂[σ₂],w₂′] .proj₁)
          (Jₙ w₁′-ne) (Jₙ w₂′-ne)
          (~-J A₁[σ₁]≅A₂[σ₂] (escape-⊩∷ ⊩t₁[σ₁])
             (escape-⊩≡∷ t₁[σ₁]≡t₂[σ₂])
             (PE.subst₃ _⊢_≅_ (PE.cong (_∙_ _) $ Id-wk1-wk1-0[⇑]≡ A₁ t₁)
                PE.refl PE.refl $
              R.escape-⊩≡ ⦃ inc = included ⦃ inc = inc ⦄ ⦄ $
              ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑] B₁≡B₂ σ₁≡σ₂)
             (escape-⊩≡∷ u₁[σ₁]≡u₂[σ₂])
             (escape-⊩≡∷ v₁[σ₁]≡v₂[σ₂]) w₁′~w₂′)

opaque

  -- Validity of equality preservation for J.

  J-congᵛ :
    Γ ⊩ᵛ⟨ l′₁ ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l′₂ ⟩ t₁ ≡ t₂ ∷ A₁ →
    Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ ≡ B₂ →
    Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    Γ ⊩ᵛ⟨ l′₃ ⟩ u₁ ≡ u₂ ∷ B₁ [ t₁ , rfl ]₁₀ →
    Γ ⊩ᵛ⟨ l′₄ ⟩ v₁ ≡ v₂ ∷ A₁ →
    Γ ⊩ᵛ⟨ l′₅ ⟩ w₁ ≡ w₂ ∷ Id A₁ t₁ v₁ →
    Γ ⊩ᵛ⟨ l ⟩ J p q A₁ t₁ B₁ u₁ v₁ w₁ ≡ J p q A₂ t₂ B₂ u₂ v₂ w₂ ∷
      B₁ [ v₁ , w₁ ]₁₀
  J-congᵛ A₁≡A₂ t₁≡t₂ ⊢B₁≡B₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂ =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀ (wf-⊩ᵛ≡ B₁≡B₂ .proj₁) (wf-⊩ᵛ≡∷ v₁≡v₂ .proj₁)
          (PE.subst (_⊩ᵛ⟨_⟩_∷_ _ _ _) ≡Id-wk1-wk1-0[]₀ $
           wf-⊩ᵛ≡∷ w₁≡w₂ .proj₁)
      , ⊩J≡J A₁≡A₂ t₁≡t₂ ⊢B₁≡B₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂
      )

opaque

  -- Validity of J.

  Jᵛ :
    Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
    Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊩ᵛ⟨ l ⟩ B →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ B [ t , rfl ]₁₀ →
    Γ ⊩ᵛ⟨ l″ ⟩ w ∷ Id A t v →
    Γ ⊩ᵛ⟨ l ⟩ J p q A t B u v w ∷ B [ v , w ]₁₀
  Jᵛ ⊢B ⊩B ⊩u ⊩w =
    case ⊩ᵛId⇔ .proj₁ (wf-⊩ᵛ∷ ⊩w) of λ
      (⊩t , ⊩v) →
    case wf-⊩ᵛ∷ ⊩t of λ
      ⊩A →
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    J-congᵛ (refl-⊩ᵛ≡ ⊩A) (refl-⊩ᵛ≡∷ ⊩t) (refl ⊢B) (refl-⊩ᵛ≡ ⊩B)
      (refl-⊩ᵛ≡∷ ⊩u) (refl-⊩ᵛ≡∷ ⊩v) (refl-⊩ᵛ≡∷ ⊩w)

opaque

  -- Validity of the J β rule.

  J-βᵛ :
    Γ ⊢ t ∷ A →
    Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
    Γ ⊩ᵛ⟨ l ⟩ u ∷ B [ t , rfl ]₁₀ →
    Γ ⊩ᵛ⟨ l ⟩ J p q A t B u t rfl ≡ u ∷ B [ t , rfl ]₁₀
  J-βᵛ {t} {A} {B} ⊢t ⊢B ⊩u =
    ⊩ᵛ∷-⇐
      (λ {_ _} {σ = σ} ⊩σ →
         let _ , ⊢σ = escape-⊩ˢ∷ ⊩σ in
         PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ [,]-[]-commute B) $
         J-β-⇒ (refl $ subst-⊢∷ ⊢t ⊢σ)
           (PE.subst₂ _⊢_
              (PE.cong (_∙_ _) $ Id-wk1-wk1-0[⇑]≡ A t) PE.refl $
            subst-⊢-⇑ ⊢B ⊢σ)
           (PE.subst (_⊢_∷_ _ _) ([,]-[]-commute B) $
            R.escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u ⊩σ))
      ⊩u
