------------------------------------------------------------------------
-- Validity of the universe type.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Universe
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Untyped M
open import Definition.Untyped.Properties M
open import Definition.Untyped.Neutral M type-variant
open import Definition.LogicalRelation R {{eqrel}}
open import Definition.LogicalRelation.Hidden R {{eqrel}}
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R {{eqrel}}
open import Definition.LogicalRelation.Substitution.Introductions.Level R {{eqrel}}

open import Tools.Function
open import Tools.Nat as N using (Nat; 1+; 2+)
open import Tools.Product as Σ
open import Tools.Empty
import Tools.PropositionalEquality as PE

private
  variable
    n    : Nat
    Γ    : Con Term n
    A B t u : Term n
    l l′ : Universe-level
    k    : LogRelKit

------------------------------------------------------------------------
-- Some characterisation lemmas

private

  -- A lemma used below.

  U⇒*U→≡ : Γ ⊢ U t :⇒*: U u → t PE.≡ u
  U⇒*U→≡ {Γ} {t} {u} =
    Γ ⊢ U t :⇒*: U u →⟨ red ⟩
    Γ ⊢ U t ⇒* U u   →⟨ flip whnfRed* Uₙ ⟩
    U t PE.≡ U u     →⟨ (λ { PE.refl → PE.refl }) ⟩
    t PE.≡ u         □

opaque

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩U⇔ :
    Γ ⊩⟨ l ⟩ U t ⇔
    Σ (Γ ⊩Level t ∷Level) λ [t] → reflect-level [t] <ᵘ l
  ⊩U⇔ =
      lemma ∘→ U-elim
    , λ ([t] , t<l) → Uᵣ′ _ [t] t<l (idRed:*: (Uⱼ (escapeLevel [t])))
    where
    lemma :
      Γ ⊩⟨ l ⟩U U t →
      Σ (Γ ⊩Level t ∷Level) λ [t] → reflect-level [t] <ᵘ l
    lemma (noemb (Uᵣ k [k] k<l U⇒*U@([ ⊢U , _ , _ ]))) =
      case U⇒*U→≡ U⇒*U of λ {
        PE.refl → [k] , k<l }
    lemma (emb ≤ᵘ-refl     ⊩U) = Σ.map idᶠ ≤ᵘ-step (lemma ⊩U)
    lemma (emb (≤ᵘ-step p) ⊩U) = Σ.map idᶠ ≤ᵘ-step (lemma (emb p ⊩U))

opaque
  unfolding _⊩⟨_⟩_∷_

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷U⇔ :
    Γ ⊩⟨ l ⟩ A ∷ U t ⇔
    Σ (Γ ⊩Level t ∷Level) λ [t] → reflect-level [t] <ᵘ l × Γ ⊩⟨ reflect-level [t] ⟩ A ×
    ∃ λ B → Γ ⊢ A :⇒*: B ∷ U t × Type B × Γ ⊢ B ≅ B ∷ U t
  ⊩∷U⇔ =
      (λ (⊩U , ⊩A) →
         lemma (U-elim ⊩U) (irrelevanceTerm ⊩U (U-intr (U-elim ⊩U)) ⊩A))
    , (λ ([t] , t<l , ⊩A , _ , A⇒*B , B-type , B≅B) →
          Uᵣ′ _ [t] t<l (idRed:*: (Uⱼ (escapeLevel [t])))
          , Uₜ _ A⇒*B B-type B≅B (⊩<⇔⊩ t<l .proj₂ ⊩A))
    where
    lemma :
      (⊩U : Γ ⊩⟨ l ⟩U U t) →
      Γ ⊩⟨ l ⟩ A ∷ U t / U-intr ⊩U →
      Σ (Γ ⊩Level t ∷Level) λ [t] → reflect-level [t] <ᵘ l × Γ ⊩⟨ reflect-level [t] ⟩ A ×
      ∃ λ B → Γ ⊢ A :⇒*: B ∷ U t × Type B × Γ ⊢ B ≅ B ∷ U t
    lemma (noemb (Uᵣ k [k] k<l U⇒*U)) (Uₜ _ A⇒*B B-type B≅B ⊩A) =
      case U⇒*U→≡ U⇒*U of λ where
        PE.refl → [k] , k<l , ⊩<⇔⊩ k<l .proj₁ ⊩A , _ , A⇒*B , B-type , B≅B
    lemma (emb ≤ᵘ-refl     ⊩U) = Σ.map idᶠ (Σ.map ≤ᵘ-step idᶠ) ∘→ lemma ⊩U
    lemma (emb (≤ᵘ-step p) ⊩U) = Σ.map idᶠ (Σ.map ≤ᵘ-step idᶠ) ∘→ lemma (emb p ⊩U)

opaque

  -- A variant of ⊩∷U⇔.

  Type→⊩∷U⇔ :
    Type A →
    Γ ⊩⟨ l ⟩ A ∷ U t ⇔
    Σ (Γ ⊩Level t ∷Level) λ [t] → reflect-level [t] <ᵘ l × (Γ ⊩⟨ reflect-level [t] ⟩ A) ×
     Γ ⊢ A ∷ U t ×
     Γ ⊢ A ≅ A ∷ U t
  Type→⊩∷U⇔ {A} {Γ} {l} {t} A-type =
    Γ ⊩⟨ l ⟩ A ∷ U t                                        ⇔⟨ ⊩∷U⇔ ⟩
    (∃ λ [t] → reflect-level [t] <ᵘ l × (Γ ⊩⟨ reflect-level [t] ⟩ A) ×
     ∃ λ B → Γ ⊢ A :⇒*: B ∷ U t × Type B × Γ ⊢ B ≅ B ∷ U t) ⇔⟨
      Σ-cong-⇔ (λ [t] → id⇔ ×-cong-⇔ id⇔ ×-cong-⇔
        ((λ (_ , A⇒*B , _ , B≅B) → case whnfRed*Term (redₜ A⇒*B) (typeWhnf A-type) of λ where
          PE.refl → ⊢t-redₜ A⇒*B , B≅B)
        , λ (⊢A , A≅A) → _ , idRedTerm:*: ⊢A , A-type , A≅A)) ⟩
    (∃ λ [t] → reflect-level [t] <ᵘ l × (Γ ⊩⟨ reflect-level [t] ⟩ A) × Γ ⊢ A ∷ U t × Γ ⊢ A ≅ A ∷ U t) □⇔

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩U≡⇔ :
    Γ ⊩⟨ l ⟩ U t ≡ A ⇔
    Σ (Γ ⊩Level t ∷Level) λ [t] → reflect-level [t] <ᵘ l ×
    ∃ λ u → Γ ⊢ A :⇒*: U u × Γ ⊩Level t ≡ u ∷Level × Γ ⊩⟨ l ⟩ A
  ⊩U≡⇔ {Γ} {t} {A} =
      (λ (⊩U , ⊩A , U≡A) →
        Σ.map idᶠ (Σ.map idᶠ (Σ.map idᶠ (Σ.map idᶠ (_, ⊩A)))) $
        lemma (U-elim ⊩U) (irrelevanceEq ⊩U (U-intr (U-elim ⊩U)) U≡A))
      , λ ([t] , t<l , u , A⇒*U@([ _ , ⊢U , _ ]) , t≡u , ⊩A) →
        Uᵣ′ _ [t] t<l (idRed:*: (Uⱼ (escapeLevel [t])))
        , ⊩A
        , U₌ u A⇒*U t≡u
    where
    lemma :
      (⊩U : Γ ⊩⟨ l ⟩U U t) →
      Γ ⊩⟨ l ⟩ U t ≡ A / U-intr ⊩U →
      Σ (Γ ⊩Level t ∷Level) λ [t] → reflect-level [t] <ᵘ l × ∃ λ u → Γ ⊢ A :⇒*: U u × Γ ⊩Level t ≡ u ∷Level
    lemma (noemb (Uᵣ k [k] k< U⇒*U)) (U₌ k′ D k≡k′) =
      case U⇒*U→≡ U⇒*U of λ {
        PE.refl → [k] , k< , k′ , D , k≡k′ }
    lemma (emb ≤ᵘ-refl ⊩U) A≡U =
      Σ.map idᶠ (Σ.map ≤ᵘ-step idᶠ) (lemma ⊩U A≡U)
    lemma (emb (≤ᵘ-step p) ⊩U) A≡U =
      Σ.map idᶠ (Σ.map ≤ᵘ-step idᶠ) (lemma (emb p ⊩U) A≡U)

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷U⇔ :
    Γ ⊩⟨ l ⟩ A ≡ B ∷ U t ⇔
    Σ (Γ ⊩Level t ∷Level) λ [t] → reflect-level [t] <ᵘ l × Γ ⊩⟨ reflect-level [t] ⟩ A ≡ B ×
     ∃₂ λ A′ B′ →
     Γ ⊢ A :⇒*: A′ ∷ U t ×
     Γ ⊢ B :⇒*: B′ ∷ U t ×
     Type A′ ×
     Type B′ ×
     Γ ⊢ A′ ≅ B′ ∷ U t
  ⊩≡∷U⇔ =
      (λ (⊩U , _ , _ , A≡B) →
          lemma (U-elim ⊩U)
            (irrelevanceEqTerm ⊩U (U-intr (U-elim ⊩U)) A≡B))
    , (λ ([t] , t<l , (⊩A , ⊩B , A≡B) , _ , _ ,
          A⇒*A′ , B⇒*B′ , A′-type , B′-type , A′≅B′) →
         let ⊩A = ⊩<⇔⊩ t<l .proj₂ ⊩A
             ⊩B = ⊩<⇔⊩ t<l .proj₂ ⊩B
         in
           Uᵣ′ _ [t] t<l (idRed:*: (Uⱼ (escapeLevel [t])))
         , Uₜ _ A⇒*A′ A′-type (≅ₜ-trans A′≅B′ (≅ₜ-sym A′≅B′)) ⊩A
         , Uₜ _ B⇒*B′ B′-type (≅ₜ-trans (≅ₜ-sym A′≅B′) A′≅B′) ⊩B
         , Uₜ₌ _ _ A⇒*A′ B⇒*B′ A′-type B′-type A′≅B′ ⊩A ⊩B
             (⊩<≡⇔⊩≡′ t<l .proj₂ A≡B))
    where
    lemma :
      (⊩U : Γ ⊩⟨ l ⟩U U t) →
      Γ ⊩⟨ l ⟩ A ≡ B ∷ U t / U-intr ⊩U →
      Σ (Γ ⊩Level t ∷Level) λ [t] → reflect-level [t] <ᵘ l × Γ ⊩⟨ reflect-level [t] ⟩ A ≡ B ×
      ∃₂ λ A′ B′ →
      Γ ⊢ A :⇒*: A′ ∷ U t ×
      Γ ⊢ B :⇒*: B′ ∷ U t ×
      Type A′ ×
      Type B′ ×
      Γ ⊢ A′ ≅ B′ ∷ U t
    lemma
      (noemb (Uᵣ k [k] k<l U⇒*U))
      (Uₜ₌ _ _ A⇒*A′ B⇒*B′ A′-type B′-type A′≅B′ ⊩A ⊩B A≡B) =
        case U⇒*U→≡ U⇒*U of λ where
          PE.refl →
              [k] , k<l
            , (⊩<⇔⊩ k<l .proj₁ ⊩A , ⊩<⇔⊩ k<l .proj₁ ⊩B , ⊩<≡⇔⊩≡ k<l .proj₁ A≡B)
            , _ , _ , A⇒*A′ , B⇒*B′ , A′-type , B′-type , A′≅B′
    lemma (emb ≤ᵘ-refl     ⊩U) = Σ.map idᶠ (Σ.map ≤ᵘ-step idᶠ) ∘→ lemma ⊩U
    lemma (emb (≤ᵘ-step p) ⊩U) = Σ.map idᶠ (Σ.map ≤ᵘ-step idᶠ) ∘→ lemma (emb p ⊩U)

opaque

  -- A variant of ⊩≡∷U⇔.

  Type→⊩≡∷U⇔ :
    Type A →
    Type B →
    Γ ⊩⟨ l ⟩ A ≡ B ∷ U t ⇔
    Σ (Γ ⊩Level t ∷Level) λ [t] → reflect-level [t] <ᵘ l × (Γ ⊩⟨ reflect-level [t] ⟩ A ≡ B) ×
     Γ ⊢ A ∷ U t ×
     Γ ⊢ B ∷ U t ×
     Γ ⊢ A ≅ B ∷ U t
  Type→⊩≡∷U⇔ {A} {B} {Γ} {l} {t} A-type B-type =
    Γ ⊩⟨ l ⟩ A ≡ B ∷ U t          ⇔⟨ ⊩≡∷U⇔ ⟩
    (Σ (Γ ⊩Level t ∷Level) λ [t] → reflect-level [t] <ᵘ l × Γ ⊩⟨ reflect-level [t] ⟩ A ≡ B ×
     ∃₂ λ A′ B′ →
     Γ ⊢ A :⇒*: A′ ∷ U t ×
     Γ ⊢ B :⇒*: B′ ∷ U t ×
     Type A′ ×
     Type B′ ×
     Γ ⊢ A′ ≅ B′ ∷ U t)
      ⇔⟨ Σ-cong-⇔ (λ [t] → id⇔ ×-cong-⇔ id⇔ ×-cong-⇔
        ( (λ (A′ , B′ , A⇒*A′ , B⇒*B′ , _ , _ , A′≅B′) →
          case whnfRed*Term (redₜ A⇒*A′) (typeWhnf A-type) of λ {
            PE.refl →
          case whnfRed*Term (redₜ B⇒*B′) (typeWhnf B-type) of λ {
            PE.refl →
          ⊢t-redₜ A⇒*A′ , ⊢t-redₜ B⇒*B′ , A′≅B′ } })
        , λ (⊢A , ⊢B , A≅B) →
          _ , _ , idRedTerm:*: ⊢A , idRedTerm:*: ⊢B , A-type , B-type , A≅B)) ⟩
    (Σ (Γ ⊩Level t ∷Level) λ [t] → reflect-level [t] <ᵘ l × (Γ ⊩⟨ reflect-level [t] ⟩ A ≡ B) ×
     Γ ⊢ A ∷ U t ×
     Γ ⊢ B ∷ U t ×
     Γ ⊢ A ≅ B ∷ U t) □⇔

------------------------------------------------------------------------
-- Validity

opaque

  -- Validity of U.

  ⊩ᵛU : (⊩t : Γ ⊩ᵛ⟨ l ⟩ t ∷ Level) → Γ ⊩ᵛ⟨ 1+ (reflect-level (⊩∷Level⇔ .proj₁ (⊩ᵛ∷→⊩∷ ⊩t))) ⟩ U t
  ⊩ᵛU {Γ} {t} ⊩t =
    ⊩ᵛ⇔ .proj₂
      ( wf-⊩ᵛ (wf-⊩ᵛ∷ ⊩t)
      , λ {_} {Δ} {σ₁} {σ₂} →
          λ σ₁≡σ₂ →
            let (⊩t[σ₁] , ⊩t[σ₂] , ⊩t≡) = ⊩≡∷Level⇔ .proj₁ (⊩ᵛ∷⇔ .proj₁ ⊩t .proj₂ σ₁≡σ₂)
                ⊢Δ = escape-⊩ˢ≡∷ σ₁≡σ₂ .proj₁
            in
              ⊩U≡⇔ .proj₂ $
                ⊩t[σ₁]
              , {!    !}
              , t [ σ₂ ]
              , idRed:*: (Uⱼ (escapeLevel ⊩t[σ₂]))
              , ⊩t≡
              , ⊩U⇔ .proj₂ (⊩t[σ₂] , {!   !})
      )

opaque

  -- Validity of U, seen as a term former.

  ⊩ᵛU∷U : (⊩t : Γ ⊩ᵛ⟨ l ⟩ t ∷ Level) → Γ ⊩ᵛ⟨ 2+ (reflect-level (⊩∷Level⇔ .proj₁ (⊩ᵛ∷→⊩∷ ⊩t))) ⟩ U t ∷ U (sucᵘ t)
  ⊩ᵛU∷U {Γ} {t} ⊩t =
    ⊩ᵛ∷⇔ .proj₂
      ( {!    !}
      , λ {_} {Δ} {σ₁} {σ₂} →
          -- Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ                                         →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩

          -- ⊢ Δ                                                      →⟨ (λ ⊢Δ → ≤ᵘ-refl , ⊩U⇔ .proj₂ (≤ᵘ-refl , ⊢Δ) , Uⱼ ⊢Δ , ≅-Urefl ⊢Δ) ⟩

          -- 1+ l <ᵘ 2+ l × (Δ ⊩⟨ 1+ l ⟩ U l) × Δ ⊢ U l ∷ U (1+ l) ×
          -- Δ ⊢ U l ≅ U l ∷ U (1+ l)                                 →⟨ Type→⊩∷U⇔ Uₙ .proj₂ ⟩

          -- Δ ⊩⟨ 2+ l ⟩ U l ∷ U (1+ l)                               →⟨ refl-⊩≡∷ ⟩

          -- Δ ⊩⟨ 2+ l ⟩ U l ≡ U l ∷ U (1+ l)                         □
          λ σ₁≡σ₂ →
            let ⊩t[σ₁]≡t[σ₂] = ⊩ᵛ∷⇔ .proj₁ ⊩t .proj₂ σ₁≡σ₂
                (⊩t[σ₁] , ⊩t[σ₂] , ⊩t≡) = ⊩≡∷Level⇔ .proj₁ ⊩t[σ₁]≡t[σ₂]
            in
              Type→⊩≡∷U⇔ Uₙ Uₙ .proj₂ $
                {! ⊩t[σ₁]≡t[σ₂]  !}
              , {!   !}
              , ⊩U≡⇔ .proj₂
                ( ⊩t[σ₁]
                , {!   !}
                , t [ σ₂ ]
                , idRed:*: (Uⱼ (escapeLevel ⊩t[σ₂]))
                , ⊩t≡
                , ⊩U⇔ .proj₂ (⊩t[σ₂] , {!   !})
                )
              , Uⱼ (escapeLevel ⊩t[σ₁])
              , conv (Uⱼ (escapeLevel ⊩t[σ₂])) (U-cong (sucᵘ-cong (sym (≅ₜ-eq (escapeLevelEq ⊩t≡)))))
              , ≅ₜ-U-cong (escapeLevelEq ⊩t≡)
      )

opaque

  -- Validity of one of the typing rules called univ.

  ⊩ᵛ∷U→⊩ᵛ :
    Γ ⊩ᵛ⟨ l ⟩ A ∷ U t →
    Γ ⊩ᵛ⟨ l ⟩ A
  ⊩ᵛ∷U→⊩ᵛ ⊩A∷U =
    case ⊩ᵛ∷⇔ .proj₁ ⊩A∷U of λ
      (⊩U , A≡A∷U) →
    ⊩ᵛ⇔ .proj₂
      ( wf-⊩ᵛ ⊩U
      , λ σ₁≡σ₂ →
        let ([t] , t<l , A≡A , _) = ⊩≡∷U⇔ .proj₁ (A≡A∷U σ₁≡σ₂) in
        emb-⊩≡ (<ᵘ→≤ᵘ t<l) A≡A
      )

opaque

  -- Validity of another of the typing rules called univ.

  ⊩ᵛ≡∷U→⊩ᵛ≡ :
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B ∷ U t →
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B
  ⊩ᵛ≡∷U→⊩ᵛ≡ A≡B∷U =
    case ⊩ᵛ≡∷⇔ .proj₁ A≡B∷U of λ
      (⊩U , A≡B∷U) →
    ⊩ᵛ≡⇔ .proj₂
      ( wf-⊩ᵛ ⊩U
      , λ σ₁≡σ₂ →
        let ([t] , t<l , A≡B , _) = ⊩≡∷U⇔ .proj₁ (A≡B∷U σ₁≡σ₂) in
        emb-⊩≡ (<ᵘ→≤ᵘ t<l) A≡B
      )
