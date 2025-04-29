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
open import Definition.Typed.Well-formed R
open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.LogicalRelation R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Hidden R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Irrelevance R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties R ⦃ eqrel ⦄
open import Definition.LogicalRelation.ShapeView R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Substitution R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Substitution.Introductions.Level R ⦃ eqrel ⦄

open import Tools.Function
open import Tools.Nat using (Nat; 1+; 2+)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE

private
  variable
    n    : Nat
    Γ    : Con Term n
    A B t t′ u u′ : Term n
    l l′ : Universe-level
    k    : LogRelKit

------------------------------------------------------------------------
-- Some characterisation lemmas

private

  -- A lemma used below.

  U⇒*U→≡ : Γ ⊢ U t ⇒* U t′ → t PE.≡ t′
  U⇒*U→≡ {Γ} {t} {t′} =
    Γ ⊢ U t ⇒* U t′  →⟨ flip whnfRed* Uₙ ⟩
    U t PE.≡ U t′    →⟨ (λ { PE.refl → PE.refl }) ⟩
    t PE.≡ t′        □

opaque

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩U⇔ :
    Γ ⊩⟨ l ⟩ U t ⇔
    (∃ λ (⊩t : Γ ⊩Level t ∷Level) → ↑ᵘ ⊩t <ᵘ l)
  ⊩U⇔ =
      (λ ⊩U →
        case U-view ⊩U of λ {
          (Uᵣ (Uᵣ _ _ t<l U⇒*U)) →
        case U⇒*U→≡ U⇒*U of λ {
          PE.refl →
        _ , t<l }})
    , (λ (⊩t , t<l) →
        Uᵣ (Uᵣ _ ⊩t t<l (id (Uⱼ (escapeLevel ⊩t)))))

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩U≡⇔ :
    Γ ⊩⟨ l ⟩ U t ≡ A ⇔
    (∃ λ ([t] : Γ ⊩Level t ∷Level) → ↑ᵘ [t] <ᵘ l × ∃ λ u → Γ ⊢ A ⇒* U u × Γ ⊩Level t ≡ u ∷Level)
  ⊩U≡⇔ {l} =
      (λ (⊩U , _ , U≡A) →
        case U-view ⊩U of λ {
          (Uᵣ (Uᵣ _ [t] t<l U⇒*U)) →
        case U≡A of λ
          (U₌ _ A⇒*U t≡u) →
        case U⇒*U→≡ U⇒*U of λ {
          PE.refl →
        [t] , t<l , _ , A⇒*U , t≡u }})
    , (λ ([t] , t<l , u , A⇒*U , t≡u) →
         let [u] = wf-Level-eq t≡u .proj₂ in
           Uᵣ (Uᵣ _ [t] t<l (id (Uⱼ (escapeLevel [t]))))
         , wf-⊩≡ (⊩-⇐* A⇒*U (⊩U⇔ .proj₂ ([u] , PE.subst (_<ᵘ l) (↑ᵘ-cong t≡u) t<l))) .proj₁
         , U₌ _ A⇒*U t≡u)

opaque

  ⊩U≡U⇔ :
    Γ ⊩⟨ l ⟩ U t ≡ U u ⇔
    (∃ λ (t≡u : Γ ⊩Level t ≡ u ∷Level) → ↑ᵘ wf-Level-eq t≡u .proj₁ <ᵘ l)
  ⊩U≡U⇔ {Γ} {l} {t} {u} =
    Γ ⊩⟨ l ⟩ U t ≡ U u                                                           ⇔⟨ ⊩U≡⇔ ⟩
    (∃ λ [t] → ↑ᵘ [t] <ᵘ l × ∃ λ u′ → Γ ⊢ U u ⇒* U u′ × Γ ⊩Level t ≡ u′ ∷Level)  ⇔⟨ (λ ([t] , t<l , u′ , U⇒*U , t≡u′) →
                                                                                      case U⇒*U→≡ U⇒*U of λ {
                                                                                        PE.refl →
                                                                                      t≡u′ , PE.subst (_<ᵘ l) ↑ᵘ-irrelevance t<l })
                                                                                    , (λ (t≡u , t<l) →
                                                                                        wf-Level-eq t≡u .proj₁
                                                                                      , PE.subst (_<ᵘ l) ↑ᵘ-irrelevance t<l
                                                                                      , u , id (Uⱼ (escapeLevel (wf-Level-eq t≡u .proj₂)))
                                                                                      , t≡u) ⟩
    (∃ λ t≡u → ↑ᵘ wf-Level-eq t≡u .proj₁ <ᵘ l)                                   □⇔

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷U⇔ :
    Γ ⊩⟨ l ⟩ A ≡ B ∷ U t ⇔
    (∃ λ ([t] : Γ ⊩Level t ∷Level) → ↑ᵘ [t] <ᵘ l ×
     Γ ⊩⟨ ↑ᵘ [t] ⟩ A ≡ B ×
     ∃₂ λ A′ B′ →
     Γ ⊢ A ⇒* A′ ∷ U t ×
     Γ ⊢ B ⇒* B′ ∷ U t ×
     Type A′ ×
     Type B′ ×
     Γ ⊢ A′ ≅ B′ ∷ U t)
  ⊩≡∷U⇔ =
      (λ (⊩U , A≡B) →
        case U-view ⊩U of λ {
          (Uᵣ (Uᵣ _ [t] t<l U⇒*U)) →
        case A≡B of λ
          (Uₜ₌ _ _ A⇒*A′ B⇒*B′ A′-type B′-type A′≅B′ ⊩A ⊩B A≡B) →
        case U⇒*U→≡ U⇒*U of λ {
          PE.refl →
          [t] , t<l
        , ( ⊩<⇔⊩ t<l .proj₁ ⊩A
          , ⊩<⇔⊩ t<l .proj₁ ⊩B
          , ⊩<≡⇔⊩≡ t<l .proj₁ A≡B
          )
        , _ , _ , A⇒*A′ , B⇒*B′ , A′-type , B′-type , A′≅B′ }})
    , (λ ([t] , t<l , (⊩A , ⊩B , A≡B) , _ , _ ,
          A⇒*A′ , B⇒*B′ , A′-type , B′-type , A′≅B′) →
         let ⊩A = ⊩<⇔⊩ t<l .proj₂ ⊩A
             ⊩B = ⊩<⇔⊩ t<l .proj₂ ⊩B
         in
           Uᵣ (Uᵣ _ [t] t<l (id (Uⱼ (escapeLevel [t]))))
         , Uₜ₌ _ _ A⇒*A′ B⇒*B′ A′-type B′-type A′≅B′ ⊩A ⊩B
             (⊩<≡⇔⊩≡′ t<l .proj₂ A≡B))

opaque

  -- A variant of ⊩≡∷U⇔.

  Type→⊩≡∷U⇔ :
    Type A →
    Type B →
    Γ ⊩⟨ l ⟩ A ≡ B ∷ U t ⇔
    (∃ λ ([t] : Γ ⊩Level t ∷Level) → ↑ᵘ [t] <ᵘ l ×
     (Γ ⊩⟨ ↑ᵘ [t] ⟩ A ≡ B) × Γ ⊢ A ≅ B ∷ U t)
  Type→⊩≡∷U⇔ {A} {B} {Γ} {l} {t} A-type B-type =
    Γ ⊩⟨ l ⟩ A ≡ B ∷ U t           ⇔⟨ ⊩≡∷U⇔ ⟩
    (∃ λ [t] → ↑ᵘ [t] <ᵘ l × (Γ ⊩⟨ ↑ᵘ [t] ⟩ A ≡ B) ×
    (∃₂ λ A′ B′ →
     Γ ⊢ A ⇒* A′ ∷ U t ×
     Γ ⊢ B ⇒* B′ ∷ U t ×
     Type A′ ×
     Type B′ ×
     Γ ⊢ A′ ≅ B′ ∷ U t))           ⇔⟨ (λ ([t] , t<l , A≡B , A′ , B′ , DA , DB , A′-type , B′-type , A′≅B′) →
                                         case whnfRed*Term DA (typeWhnf A-type) of λ {
                                           PE.refl →
                                         case whnfRed*Term DB (typeWhnf B-type) of λ {
                                           PE.refl →
                                         ([t] , t<l , A≡B , A′≅B′)}})
                                    , (λ ([t] , t<l , A≡B , A≅B) →
                                         let _ , ⊢A , ⊢B = wf-⊢≡∷ (≅ₜ-eq A≅B) in
                                           [t] , t<l , A≡B , _ , _ , id ⊢A , id ⊢B
                                         , A-type , B-type , A≅B) ⟩
    (∃ λ [t] → ↑ᵘ [t] <ᵘ l × (Γ ⊩⟨ ↑ᵘ [t] ⟩ A ≡ B) ×
    Γ ⊢ A ≅ B ∷ U t)               □⇔

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷U⇔ :
    Γ ⊩⟨ l ⟩ A ∷ U t ⇔
    (∃ λ ([t] : Γ ⊩Level t ∷Level) → ↑ᵘ [t] <ᵘ l ×
     Γ ⊩⟨ ↑ᵘ [t] ⟩ A ×
     ∃ λ B → Γ ⊢ A ⇒* B ∷ U t × Type B × Γ ⊢≅ B ∷ U t)
  ⊩∷U⇔ {Γ} {l} {A} {t} =
    Γ ⊩⟨ l ⟩ A ∷ U t                                      ⇔⟨ ⊩∷⇔⊩≡∷ ⟩

    Γ ⊩⟨ l ⟩ A ≡ A ∷ U t                                  ⇔⟨ ⊩≡∷U⇔ ⟩

    (∃ λ [t] → ↑ᵘ [t] <ᵘ l × Γ ⊩⟨ ↑ᵘ [t] ⟩ A ≡ A ×
     ∃₂ λ A′ A″ →
     Γ ⊢ A ⇒* A′ ∷ U t ×
     Γ ⊢ A ⇒* A″ ∷ U t ×
     Type A′ ×
     Type A″ ×
     Γ ⊢ A′ ≅ A″ ∷ U t)                                   ⇔⟨ (Σ-cong-⇔ λ _ → id⇔ ×-cong-⇔ sym⇔ ⊩⇔⊩≡ ×-cong-⇔
                                                                ( (λ (_ , _ , A⇒*A′ , _ , A′-type , _ , A′≅A″) →
                                                                     _ , A⇒*A′ , A′-type , wf-⊢≅∷ A′≅A″ .proj₁)
                                                                , (λ (_ , A⇒*B , B-type , ≅B) →
                                                                     _ , _ , A⇒*B , A⇒*B , B-type , B-type , ≅B)
                                                                )) ⟩
    (∃ λ [t] → ↑ᵘ [t] <ᵘ l × Γ ⊩⟨ ↑ᵘ [t] ⟩ A ×
     ∃ λ B → Γ ⊢ A ⇒* B ∷ U t × Type B × Γ ⊢≅ B ∷ U t)    □⇔

opaque

  -- A variant of ⊩∷U⇔.

  Type→⊩∷U⇔ :
    Type A →
    Γ ⊩⟨ l ⟩ A ∷ U t ⇔
    (∃ λ ([t] : Γ ⊩Level t ∷Level) → ↑ᵘ [t] <ᵘ l ×
     (Γ ⊩⟨ ↑ᵘ [t] ⟩ A) × Γ ⊢≅ A ∷ U t)
  Type→⊩∷U⇔ {A} {Γ} {l} {t} A-type =
    Γ ⊩⟨ l ⟩ A ∷ U t                                      ⇔⟨ ⊩∷U⇔ ⟩

    (∃ λ [t] → ↑ᵘ [t] <ᵘ l × (Γ ⊩⟨ ↑ᵘ [t] ⟩ A) ×
    (∃ λ B → Γ ⊢ A ⇒* B ∷ U t × Type B × Γ ⊢≅ B ∷ U t))   ⇔⟨ (Σ-cong-⇔ λ _ → id⇔
                                                               ×-cong-⇔
                                                             id⇔
                                                               ×-cong-⇔
                                                             ( (λ (_ , A⇒*B , _ , B≅B) →
                                                                 case whnfRed*Term A⇒*B (typeWhnf A-type) of λ {
                                                                   PE.refl →
                                                                 B≅B })
                                                             , (λ ≅A → _ , id (wf-⊢≡∷ (≅ₜ-eq ≅A) .proj₂ .proj₁) , A-type , ≅A)
                                                             ))
                                                           ⟩

    (∃ λ [t] → ↑ᵘ [t] <ᵘ l ×
     (Γ ⊩⟨ ↑ᵘ [t] ⟩ A) × Γ ⊢≅ A ∷ U t)                    □⇔

------------------------------------------------------------------------
-- Validity

opaque

  -- Validity of U.

  ⊩ᵛU : Γ ⊩ᵛ⟨ l ⟩ t ∷ Level → Γ ⊩ᵛ⟨ ωᵘ ⟩ U t
  ⊩ᵛU ⊩t =
    ⊩ᵛ⇔ʰ .proj₂
      ( wf-⊩ᵛ (wf-⊩ᵛ∷ ⊩t)
      , λ σ₁≡σ₂ →
          let t[σ₁]≡t[σ₂] = ⊩≡∷Level⇔ .proj₁ (⊩ᵛ∷⇔ʰ .proj₁ ⊩t .proj₂ σ₁≡σ₂)
              ⊩t[σ₁] , ⊩t[σ₂] = wf-Level-eq t[σ₁]≡t[σ₂]
          in ⊩U≡⇔ .proj₂
            ( ⊩t[σ₁] , <ᵘ-ωᵘ
            , _ , id (Uⱼ (escapeLevel ⊩t[σ₂]))
            , t[σ₁]≡t[σ₂]
            )
      )

opaque

  -- Validity of equality preservation for U, seen as a term former.

  ⊩ᵛU≡U∷U : Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ Level → Γ ⊩ᵛ⟨ ωᵘ ⟩ U t ≡ U u ∷ U (sucᵘ t)
  ⊩ᵛU≡U∷U t≡u =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( ⊩ᵛU (sucᵘᵛ (wf-⊩ᵛ≡∷ t≡u .proj₁))
      , λ σ₁≡σ₂ →
          let t[σ₁]≡u[σ₂] = ⊩≡∷Level⇔ .proj₁ (⊩ᵛ≡∷⇔ʰ .proj₁ t≡u .proj₂ σ₁≡σ₂)
              ⊩t[σ₁] , ⊩u[σ₂] = wf-Level-eq t[σ₁]≡u[σ₂]
          in Type→⊩≡∷U⇔ Uₙ Uₙ .proj₂
            ( ⊩sucᵘ ⊩t[σ₁] , <ᵘ-ωᵘ
            , ⊩U≡U⇔ .proj₂ (t[σ₁]≡u[σ₂] , <ᵘ-sucᵘ)
            , ≅ₜ-U-cong (escapeLevelEq t[σ₁]≡u[σ₂])
            )
      )

opaque

  -- Validity of U, seen as a term former.

  ⊩ᵛU∷U : Γ ⊩ᵛ⟨ l ⟩ t ∷ Level → Γ ⊩ᵛ⟨ ωᵘ ⟩ U t ∷ U (sucᵘ t)
  ⊩ᵛU∷U = ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ ∘→ ⊩ᵛU≡U∷U ∘→ ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁

opaque

  -- Validity of one of the typing rules called univ.

  ⊩ᵛ≡∷U→⊩ᵛ≡ :
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B ∷ U t →
    Γ ⊩ᵛ⟨ ωᵘ ⟩ A ≡ B
  ⊩ᵛ≡∷U→⊩ᵛ≡ A≡B∷U =
    case ⊩ᵛ≡∷⇔ʰ .proj₁ A≡B∷U of λ
      (⊩U , A≡B∷U) →
    ⊩ᵛ≡⇔ʰ .proj₂
      ( wf-⊩ᵛ ⊩U
      , λ σ₁≡σ₂ →
          case ⊩≡∷U⇔ .proj₁ (A≡B∷U σ₁≡σ₂) of λ
            ([t] , t<l , A[σ₁]≡A[σ₂] , _) →
          emb-⊩≡ ≤ᵘ-ωᵘ A[σ₁]≡A[σ₂]
      )

opaque

  -- Validity of another of the typing rules called univ.

  ⊩ᵛ∷U→⊩ᵛ :
    Γ ⊩ᵛ⟨ l ⟩ A ∷ U t →
    Γ ⊩ᵛ⟨ ωᵘ ⟩ A
  ⊩ᵛ∷U→⊩ᵛ = ⊩ᵛ⇔⊩ᵛ≡ .proj₂ ∘→ ⊩ᵛ≡∷U→⊩ᵛ≡ ∘→ ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁

opaque

  -- Validity of equality preservation for U, seen as a type former.

  ⊩ᵛU≡U : Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ Level → Γ ⊩ᵛ⟨ ωᵘ ⟩ U t ≡ U u
  ⊩ᵛU≡U = ⊩ᵛ≡∷U→⊩ᵛ≡ ∘→ ⊩ᵛU≡U∷U

------------------------------------------------------------------------
-- Validity of Level

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩Level≡Level∷U⇔ : Γ ⊩⟨ ωᵘ ⟩ Level ≡ Level ∷ U zeroᵘ ⇔ ⊢ Γ
  ⊩Level≡Level∷U⇔ =
      (λ Level≡Level →
         case ⊩≡∷U⇔ .proj₁ Level≡Level of λ
           (_ , _ , _ , _ , _ , Level⇒* , _) →
         wfEqTerm (subset*Term Level⇒*))
    , (λ ⊢Γ →
         case id (Levelⱼ ⊢Γ) of λ
           Level⇒*Level →
         ⊩≡∷U⇔ .proj₂
           ( ⊩zeroᵘ ⊢Γ , <ᵘ-ωᵘ , ⊩Level≡⇔ .proj₂ (id (Levelⱼ ⊢Γ))
           , (_ , _ , Level⇒*Level , Level⇒*Level , Levelₙ , Levelₙ , ≅ₜ-Levelrefl ⊢Γ)
           ))

opaque

  -- Validity of Level, seen as a term former.

  Levelᵗᵛ : ⊩ᵛ Γ → Γ ⊩ᵛ⟨ ωᵘ ⟩ Level ∷ U zeroᵘ
  Levelᵗᵛ {Γ} ⊩Γ =
    ⊩ᵛ∷⇔ʰ .proj₂
      ( ⊩ᵛU (zeroᵘᵛ ⊩Γ)
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ                   →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ⊢ Δ                                ⇔˘⟨ ⊩Level≡Level∷U⇔ ⟩→
          Δ ⊩⟨ ωᵘ ⟩ Level ≡ Level ∷ U zeroᵘ  □
      )
