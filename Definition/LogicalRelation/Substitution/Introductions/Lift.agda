------------------------------------------------------------------------
-- Validity for lifted types
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Lift
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Allowed-literal R
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sup R
open import Definition.Untyped.Whnf M type-variant
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
    Γ Δ : Cons _ _
    σ σ₁ σ₂ : Subst _ _
    s s₁ s₂ : Strength
    ℓ ℓ′ ℓ″ ℓ‴ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Universe-level
    A A₁ A₂ A′ B t t₁ t₂ u u₁ u₂ : Term n
    l l₀ l₁ l₂ : Lvl _
    p q : M

------------------------------------------------------------------------
-- Characterisation lemmas

opaque

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩Lift⇔ :
    Γ ⊩⟨ ℓ ⟩ Lift l A ⇔
    (Γ ⊩Level l ∷Level × Γ ⊩⟨ ℓ ⟩ A)
  ⊩Lift⇔ =
      (λ ⊩Lift →
        case Lift-view ⊩Lift of λ {
          (Liftᵣ (Liftᵣ Lift⇒*Lift [l] [A])) →
      case Lift-PE-injectivity $
           whnfRed* Lift⇒*Lift Liftₙ of λ {
        (PE.refl , PE.refl) →
      [l] , [A] }})
    , (λ ([l] , [A]) →
         Liftᵣ′ (id (Liftⱼ (escapeLevel [l]) (escape [A]))) [l] [A])

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩Lift≡⇔ :
    Γ ⊩⟨ ℓ ⟩ Lift l A ≡ B ⇔
    (∃₂ λ l′ A′ →
     (Γ ⊢ B ⇒* Lift l′ A′) ×
     Γ ⊩Level l ≡ l′ ∷Level ×
     Γ ⊩⟨ ℓ ⟩ A ≡ A′)
  ⊩Lift≡⇔ {l} {A} {B} =
      (λ (⊩Lift , [B] , Lift≡A) →
         case Lift-view ⊩Lift of λ {
           (Liftᵣ (Liftᵣ Lift⇒*Lift [l] [A])) →
         case Lift-PE-injectivity $
              whnfRed* Lift⇒*Lift Liftₙ of λ {
           (PE.refl , PE.refl) →
         case Lift≡A of λ
           (Lift₌ D′ l≡l′ A≡A′) →
         let _ , [F′] = ⊩Lift⇔ .proj₁ (wf-⊩≡ (⊩-⇒* D′ [B]) .proj₂)
         in _ , _ , D′ , l≡l′ , (_ , [F′] , A≡A′) }})
    , (λ (l′ , A′ , D , l≡l′ , ([A] , [A′] , A≡A′)) →
         let [l] , [l′] = wf-Level-eq l≡l′
             ⊢LA , ⊢LB = wf-⊢ (≅-eq (≅-Lift-cong (escapeLevelEq l≡l′) (escapeEq [A] A≡A′)))
             Liftl≡Liftl′
              = Liftᵣ′ (id ⊢LA) [l] [A]
              , Liftᵣ′ (id ⊢LB) [l′] [A′]
              , Lift₌ (id ⊢LB) l≡l′ A≡A′
         in sym-⊩≡
           (B          ⇒*⟨ D ⟩⊩
            Lift l′ A′ ≡˘⟨ Liftl≡Liftl′ ⟩⊩
            Lift l A   ∎⟨ ⊩Lift⇔ .proj₂ ([l] , [A]) ⟩⊩))

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩Lift≡Lift⇔ :
    Γ ⊩⟨ ℓ ⟩ Lift l₁ A₁ ≡ Lift l₂ A₂ ⇔
    (Γ ⊩Level l₁ ≡ l₂ ∷Level ×
     Γ ⊩⟨ ℓ ⟩ A₁ ≡ A₂)
  ⊩Lift≡Lift⇔ =
    ((λ (_ , _ , Lift⇒*Lift , l₁≡l₂ , A₁≡A₂) →
        case whnfRed* Lift⇒*Lift Liftₙ of λ {
          PE.refl →
        l₁≡l₂ , A₁≡A₂ }) ,
     (λ (l₁≡l₂ , A₁≡A₂) →
        let _ , [l₂] = wf-Level-eq l₁≡l₂
            _ , [A₂] = wf-⊩≡ A₁≡A₂
        in
        _ , _ , id (Liftⱼ (escapeLevel [l₂]) (escape [A₂])) , l₁≡l₂ ,
        A₁≡A₂))
    ∘⇔ ⊩Lift≡⇔

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷Lift⇔ :
    Γ ⊩⟨ ℓ ⟩ t ≡ u ∷ Lift l A ⇔
    ((Γ ⊩⟨ ℓ ⟩ Lift l A) ×
     ∃₂ λ t′ u′ →
     Γ ⊢ t ↘ t′ ∷ Lift l A ×
     Γ ⊢ u ↘ u′ ∷ Lift l A ×
     Γ ⊩⟨ ℓ ⟩ lower t′ ≡ lower u′ ∷ A)
  ⊩≡∷Lift⇔ {t} {u} =
      (λ ([Lift] , t≡u) →
        case Lift-view [Lift] of λ {
          (Liftᵣ (Liftᵣ Lift⇒*Lift [k] [A])) →
        case Lift-PE-injectivity $
             whnfRed* Lift⇒*Lift Liftₙ of λ {
          (PE.refl , PE.refl) →
        case t≡u of λ
          (Liftₜ₌ t′ u′ t↘ u↘ t≡u) →
        let [t≡u] = ⊩≡∷-intro [A] t≡u
        in ⊩Lift⇔ .proj₂ ([k] , [A]) , t′ , u′ , t↘ , u↘ , ⊩≡∷-intro [A] t≡u }})
    , λ ([Lift] , _ , _ , t↘ , u↘ , t≡u) →
      let [k] , [A] = ⊩Lift⇔ .proj₁ [Lift]
      in Liftᵣ′ (id (Liftⱼ (escapeLevel [k]) (escape [A]))) [k] [A] , _ , _ , t↘ , u↘ , ⊩≡∷→⊩≡∷/ [A] t≡u

------------------------------------------------------------------------
-- Lift

opaque

  -- Reducibility of equality between applications of Lift, seen as a
  -- term former.

  ⊩Lift≡Lift∷ :
    Γ ⊩Level l₀ ∷Level →
    Γ ⊩Level l₁ ≡ l₂ ∷Level →
    Γ ⊩⟨ ℓ ⟩ A₁ ≡ A₂ ∷ U l₀ →
    Γ ⊩⟨ ωᵘ·2 ⟩ Lift l₁ A₁ ≡ Lift l₂ A₂ ∷ U (l₀ supᵘₗ l₁)
  ⊩Lift≡Lift∷ ⊩k k₁≡k₂ A₁≡A₂ =
    Type→⊩≡∷U⇔ Liftₙ Liftₙ .proj₂
      ( ⊩supᵘₗ ⊩k (wf-Level-eq k₁≡k₂ .proj₁)
      , ↑ᵘ<ᵘωᵘ·2
      , ⊩Lift≡Lift⇔ .proj₂
          ( k₁≡k₂
          , emb-⊩≡ ≤ᵘ-supᵘₗʳ (⊩≡∷U⇔ .proj₁ A₁≡A₂ .proj₂ .proj₂ .proj₁)
          )
      , ≅ₜ-Lift-cong (escapeLevelEq k₁≡k₂) (escape-⊩≡∷ A₁≡A₂)
      )

opaque

  -- Validity of equality preservation for Lift, seen as a term former.

  Lift-congᵗᵛ :
    Γ ⊩ᵛ⟨ ℓ ⟩ l₀ ∷Level →
    Γ ⊩ᵛ⟨ ℓ′ ⟩ l₁ ≡ l₂ ∷Level →
    Γ ⊩ᵛ⟨ ℓ″ ⟩ A₁ ≡ A₂ ∷ U l₀ →
    Γ ⊩ᵛ⟨ ωᵘ·2 ⟩ Lift l₁ A₁ ≡ Lift l₂ A₂ ∷ U (l₀ supᵘₗ l₁)
  Lift-congᵗᵛ ⊩l₀ l₁≡l₂ A₁≡A₂ =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( ⊩ᵛU (supᵘₗᵛ ⊩l₀ (wf-⊩ᵛ≡∷L l₁≡l₂ .proj₁))
      , λ ∇′⊇∇ σ₁≡σ₂ →
          let ⊩l₀[σ₁] =
                ⊩ᵛ∷L→⊩ˢ∷→⊩[]∷L (defn-wk-⊩ᵛ∷L ∇′⊇∇ ⊩l₀)
                  (wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₁)
          in
          PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _)
            (PE.cong U $ PE.sym $
             supᵘₗ-[]′ λ not-ok _ →
             Allowed-literal→Level-literal (escape-⊩ᵛ∷L′ not-ok ⊩l₀) ,
             Allowed-literal→Level-literal
               (escape-⊩ᵛ≡∷L′ not-ok l₁≡l₂ .proj₁)) $
          ⊩Lift≡Lift∷ ⊩l₀[σ₁]
            (⊩ᵛ≡∷L→⊩ˢ≡∷→⊩[]≡[]∷L (defn-wk-⊩ᵛ≡∷L ∇′⊇∇ l₁≡l₂) σ₁≡σ₂)
            (R.⊩≡∷→ (⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ∇′⊇∇ A₁≡A₂) σ₁≡σ₂))
      )

opaque

  -- Validity of equality preservation for Lift, seen as a type former.

  Lift-congᵛ :
    Γ ⊩ᵛ⟨ ℓ′ ⟩ l₁ ≡ l₂ ∷Level →
    Γ ⊩ᵛ⟨ ℓ″ ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ ℓ″ ⟩ Lift l₁ A₁ ≡ Lift l₂ A₂
  Lift-congᵛ l₁≡l₂ A₁≡A₂ =
    ⊩ᵛ≡⇔ʰ .proj₂
      ( wf-⊩ᵛ (wf-⊩ᵛ≡ A₁≡A₂ .proj₁)
      , λ ∇′⊇∇ σ₁≡σ₂ →
          ⊩Lift≡Lift⇔ .proj₂
            ( ⊩ᵛ≡∷L→⊩ˢ≡∷→⊩[]≡[]∷L (defn-wk-⊩ᵛ≡∷L ∇′⊇∇ l₁≡l₂) σ₁≡σ₂
            , R.⊩≡→ (⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] (defn-wk-⊩ᵛ≡ ∇′⊇∇ A₁≡A₂) σ₁≡σ₂)
            )
      )

opaque

  -- Validity for Lift, seen as a term former.

  Liftᵗᵛ :
    Γ ⊩ᵛ⟨ ℓ ⟩ l₁ ∷Level →
    Γ ⊩ᵛ⟨ ℓ′ ⟩ l₂ ∷Level →
    Γ ⊩ᵛ⟨ ℓ″ ⟩ A ∷ U l₁ →
    Γ ⊩ᵛ⟨ ωᵘ·2 ⟩ Lift l₂ A ∷ U (l₁ supᵘₗ l₂)
  Liftᵗᵛ ⊩l₁ ⊩l₂ ⊩A = ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂
    (Lift-congᵗᵛ ⊩l₁ (refl-⊩ᵛ≡∷L ⊩l₂) (refl-⊩ᵛ≡∷ ⊩A))

opaque

  -- Validity for Lift, seen as a type former.

  Liftᵛ :
    Γ ⊩ᵛ⟨ ℓ′ ⟩ l ∷Level →
    Γ ⊩ᵛ⟨ ℓ″ ⟩ A →
    Γ ⊩ᵛ⟨ ℓ″ ⟩ Lift l A
  Liftᵛ ⊩l ⊩A =
    ⊩ᵛ⇔⊩ᵛ≡ .proj₂ (Lift-congᵛ (refl-⊩ᵛ≡∷L ⊩l) (refl-⊩ᵛ≡ ⊩A))

opaque

  ⊩ᵛLift→ :
    Γ ⊩ᵛ⟨ ℓ ⟩ Lift l A →
    Γ ⊩ᵛ⟨ ℓ ⟩ A
  ⊩ᵛLift→ ⊩Lift =
    case ⊩ᵛ⇔ʰ .proj₁ ⊩Lift of λ
      (⊩Γ , Lift≡Lift) →
    ⊩ᵛ⇔ʰ .proj₂
      ( ⊩Γ
      , λ ∇′⊇∇ σ₁≡σ₂ →
        let _ , A[σ₁]≡A[σ₂] = ⊩Lift≡Lift⇔ .proj₁ (Lift≡Lift ∇′⊇∇ σ₁≡σ₂)
        in A[σ₁]≡A[σ₂]
      )

------------------------------------------------------------------------
-- The constructor lift

opaque

  -- Reducibility of equality between applications of lift.

  ⊩lift≡lift :
    Γ ⊩Level l ∷Level →
    Γ ⊩⟨ ℓ ⟩ A →
    Γ ⊩⟨ ℓ′ ⟩ t₁ ≡ t₂ ∷ A →
    Γ ⊩⟨ ℓ ⟩ lift t₁ ≡ lift t₂ ∷ Lift l A
  ⊩lift≡lift {t₁} {t₂} ⊩l ⊩A t₁≡t₂ =
    let ⊢l             = escapeLevel ⊩l
        ⊢A , ⊢t₁ , ⊢t₂ = wf-⊢ (≅ₜ-eq (escape-⊩≡∷ t₁≡t₂))
    in
    ⊩≡∷Lift⇔ .proj₂
      ( ⊩Lift⇔ .proj₂ (⊩l , ⊩A)
      , _ , _
      , (id (liftⱼ′ ⊢l ⊢t₁) , liftₙ)
      , (id (liftⱼ′ ⊢l ⊢t₂) , liftₙ)
      , (lower (lift t₁)  ⇒⟨ Lift-β ⊢A ⊢t₁ ⟩⊩∷
         t₁               ≡⟨ level-⊩≡∷ ⊩A t₁≡t₂ ⟩⊩∷⇐*
         t₂               ⇐⟨ Lift-β ⊢A ⊢t₂ ⟩∎
         lower (lift t₂)  ∎)
      )


opaque

  -- Reducibility for lift.

  ⊩lift :
    Γ ⊩Level l ∷Level →
    Γ ⊩⟨ ℓ ⟩ A →
    Γ ⊩⟨ ℓ′ ⟩ t ∷ A →
    Γ ⊩⟨ ℓ ⟩ lift t ∷ Lift l A
  ⊩lift ⊩l ⊩A =
    ⊩∷⇔⊩≡∷ .proj₂ ∘→ ⊩lift≡lift ⊩l ⊩A ∘→ ⊩∷⇔⊩≡∷ .proj₁

opaque

  -- Validity of lift.

  liftᵛ :
    Γ ⊩ᵛ⟨ ℓ′ ⟩ l ∷Level →
    Γ ⊩ᵛ⟨ ℓ ⟩ A →
    Γ ⊩ᵛ⟨ ℓ″ ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ ℓ ⟩ lift t ∷ Lift l A
  liftᵛ ⊩l ⊩A ⊩t =
    ⊩ᵛ∷⇔ʰ .proj₂
      ( Liftᵛ ⊩l ⊩A
      , λ ∇′⊇∇ σ₁≡σ₂ →
          let ⊩σ₁ , _ = wf-⊩ˢ≡∷ σ₁≡σ₂ in
          ⊩lift≡lift (⊩ᵛ∷L→⊩ˢ∷→⊩[]∷L (defn-wk-⊩ᵛ∷L ∇′⊇∇ ⊩l) ⊩σ₁)
            (R.⊩→ $ ⊩ᵛ→⊩ˢ∷→⊩[] (defn-wk-⊩ᵛ ∇′⊇∇ ⊩A) ⊩σ₁)
            (R.⊩≡∷→ $
             ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (refl-⊩ᵛ≡∷ (defn-wk-⊩ᵛ∷ ∇′⊇∇ ⊩t)) σ₁≡σ₂)
      )

------------------------------------------------------------------------
-- The eliminator lower

opaque

  -- Reducibility of equality between applications of lower.

  ⊩lower≡lower :
    Γ ⊩⟨ ℓ ⟩ t₁ ≡ t₂ ∷ Lift l A →
    Γ ⊩⟨ ℓ ⟩ lower t₁ ≡ lower t₂ ∷ A
  ⊩lower≡lower {t₁} {t₂} t₁≡t₂ =
    case ⊩≡∷Lift⇔ .proj₁ t₁≡t₂ of λ
      (_ , u₁ , u₂ , (t₁⇒*u₁ , _) , (t₂⇒*u₂ , _) , lower-u₁≡lower-u₂) →
    lower t₁  ⇒*⟨ lower-subst* t₁⇒*u₁ ⟩⊩∷
    lower u₁  ≡⟨ lower-u₁≡lower-u₂ ⟩⊩∷⇐*
    lower u₂  ⇐*⟨ lower-subst* t₂⇒*u₂ ⟩∎
    lower t₂  ∎

opaque

  -- Validity of lower-cong.

  lower-congᵛ :
    Γ ⊩ᵛ⟨ ℓ ⟩ t ≡ u ∷ Lift l A →
    Γ ⊩ᵛ⟨ ℓ ⟩ lower t ≡ lower u ∷ A
  lower-congᵛ t≡u = ⊩ᵛ≡∷⇔ʰ .proj₂
    ( ⊩ᵛLift→ (wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t≡u .proj₁))
    , λ ∇′⊇∇ σ₁≡σ₂ →
      ⊩lower≡lower
        (R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ∇′⊇∇ t≡u) σ₁≡σ₂)
    )

opaque

  -- Validity of lower.

  lowerᵛ :
    Γ ⊩ᵛ⟨ ℓ ⟩ t ∷ Lift l A →
    Γ ⊩ᵛ⟨ ℓ ⟩ lower t ∷ A
  lowerᵛ ⊩t = ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ (lower-congᵛ (refl-⊩ᵛ≡∷ ⊩t))

------------------------------------------------------------------------
-- The β rule

opaque

  -- Reducibility for Lift-β.

  ⊩Lift-β :
    Γ ⊢ A →
    Γ ⊩⟨ ℓ ⟩ t ∷ A →
    Γ ⊩⟨ ℓ ⟩ lower (lift t) ≡ t ∷ A
  ⊩Lift-β {t} ⊢A ⊩t =
    case escape-⊩∷ ⊩t of λ
      ⊢t →
    ⊩∷-⇐*
      (lower (lift t)  ⇒⟨ Lift-β ⊢A ⊢t ⟩
       t               ∎⟨ ⊢t ⟩⇒)
      ⊩t

opaque

  -- Validity of Lift-β.

  Lift-βᵛ :
    Γ ⊩ᵛ⟨ ℓ′ ⟩ A →
    Γ ⊩ᵛ⟨ ℓ″ ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ ℓ″ ⟩ lower (lift t) ≡ t ∷ A
  Lift-βᵛ ⊩A ⊩t =
    ⊩ᵛ∷-⇐
      (λ ∇′⊇∇ ⊩σ →
        let _ , ⊢σ = escape-⊩ˢ∷ ⊩σ in
        Lift-β
          (R.escape-⊩ $ ⊩ᵛ→⊩ˢ∷→⊩[] (defn-wk-⊩ᵛ ∇′⊇∇ ⊩A) ⊩σ)
          (R.escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ (defn-wk-⊩ᵛ∷ ∇′⊇∇ ⊩t) ⊩σ))
      ⊩t

------------------------------------------------------------------------
-- The η rule

opaque

  -- Reducibility of Lift-η.

  ⊩Lift-η :
    Γ ⊩⟨ ℓ₂ ⟩ t ∷ Lift l A →
    Γ ⊩⟨ ℓ₃ ⟩ u ∷ Lift l A →
    Γ ⊩⟨ ℓ₄ ⟩ lower t ≡ lower u ∷ A →
    Γ ⊩⟨ ℓ₂ ⟩ t ≡ u ∷ Lift l A
  ⊩Lift-η {t} {u} ⊩t ⊩u lowert≡loweru =
    let ⊩Lift , t′ , _ , t↘ , _ , t≡t = ⊩≡∷Lift⇔ .proj₁ (refl-⊩≡∷ ⊩t)
        _ , u′ , _ , u↘ , _ , u≡u = ⊩≡∷Lift⇔ .proj₁ (refl-⊩≡∷ ⊩u)
        _ , ⊩A = ⊩Lift⇔ .proj₁ ⊩Lift
    in ⊩≡∷Lift⇔ .proj₂
      ( ⊩Lift
      , _ , _
      , t↘
      , u↘
      , (lower t′ ⇐*⟨ lower-subst* (t↘ .proj₁) ⟩⊩∷
         lower t  ≡⟨ level-⊩≡∷ ⊩A lowert≡loweru ⟩⊩∷⇒*
         lower u  ⇒*⟨ lower-subst* (u↘ .proj₁) ⟩∎
         lower u′ ∎))

opaque

  -- Validity of Lift-η.

  Lift-ηᵛ :
    Γ ⊩ᵛ⟨ ℓ₂ ⟩ l ∷Level →
    Γ ⊩ᵛ⟨ ℓ₃ ⟩ A →
    Γ ⊩ᵛ⟨ ℓ₄ ⟩ t ∷ Lift l A →
    Γ ⊩ᵛ⟨ ℓ₅ ⟩ u ∷ Lift l A →
    Γ ⊩ᵛ⟨ ℓ₆ ⟩ lower t ≡ lower u ∷ A →
    Γ ⊩ᵛ⟨ ωᵘ·2 ⟩ t ≡ u ∷ Lift l A
  Lift-ηᵛ ⊩l ⊩A ⊩t ⊩u lowert≡loweru =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( emb-⊩ᵛ ≤ᵘωᵘ·2 (Liftᵛ ⊩l ⊩A)
      , λ ∇′⊇∇ σ₁≡σ₂ →
        let ⊩σ₁ , ⊩σ₂ = wf-⊩ˢ≡∷ σ₁≡σ₂
            u[σ₁]≡u[σ₂] =
              R.⊩≡∷→ $
              ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (refl-⊩ᵛ≡∷ (defn-wk-⊩ᵛ∷ ∇′⊇∇ ⊩u)) σ₁≡σ₂
        in
        emb-⊩≡∷ ≤ᵘωᵘ·2 $
        ⊩Lift-η
          (R.⊩∷→ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ (defn-wk-⊩ᵛ∷ ∇′⊇∇ ⊩t) ⊩σ₁)
          (wf-⊩≡∷ u[σ₁]≡u[σ₂] .proj₂)
          (R.⊩≡∷→ $
           ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ∇′⊇∇ lowert≡loweru) σ₁≡σ₂)
      )
