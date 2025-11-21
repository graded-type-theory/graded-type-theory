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
    l l′ l″ l‴ l₁ l₂ l₃ l₄ l₅ l₆ : Universe-level
    A A₁ A₂ A′ B k k₁ k₂ k′ t t₁ t₂ u u₁ u₂ : Term n
    p q : M

------------------------------------------------------------------------
-- Characterisation lemmas

opaque

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩Lift⇔ :
    Γ ⊩⟨ l ⟩ Lift k A ⇔
    (Γ ⊩Level k ∷Level × Γ ⊩⟨ l ⟩ A)
  ⊩Lift⇔ =
      (λ ⊩Lift →
        case Lift-view ⊩Lift of λ {
          (Liftᵣ (Liftᵣ Lift⇒*Lift [k] [A])) →
      case Lift-PE-injectivity $
           whnfRed* Lift⇒*Lift Liftₙ of λ {
        (PE.refl , PE.refl) →
      [k] , [A] }})
    , (λ ([k] , [A]) →
         Liftᵣ′ (id (Liftⱼ (escapeLevel [k]) (escape [A]))) [k] [A])

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩Lift≡⇔ :
    Γ ⊩⟨ l ⟩ Lift k A ≡ B ⇔
    (∃₂ λ k′ A′ →
     (Γ ⊢ B ⇒* Lift k′ A′) ×
     Γ ⊩Level k ≡ k′ ∷Level ×
     Γ ⊩⟨ l ⟩ A ≡ A′)
  ⊩Lift≡⇔ {l} {k} {A} {B} =
      (λ (⊩Lift , [B] , Lift≡A) →
         case Lift-view ⊩Lift of λ {
           (Liftᵣ (Liftᵣ Lift⇒*Lift [k] [A])) →
         case Lift-PE-injectivity $
              whnfRed* Lift⇒*Lift Liftₙ of λ {
           (PE.refl , PE.refl) →
         case Lift≡A of λ
           (Lift₌ D′ k≡k′ A≡A′) →
         let _ , [F′] = ⊩Lift⇔ .proj₁ (wf-⊩≡ (⊩-⇒* D′ [B]) .proj₂)
         in _ , _ , D′ , k≡k′ , (_ , [F′] , A≡A′) }})
    , (λ (k′ , A′ , D , k≡k′ , ([A] , [A′] , A≡A′)) →
         let [k] , [k′] = wf-Level-eq k≡k′
             ⊢LA , ⊢LB = wf-⊢≡ (≅-eq (≅-Lift-cong (escapeLevelEq k≡k′) (escapeEq [A] A≡A′)))
             Liftk≡Liftk′
              = Liftᵣ′ (id ⊢LA) [k] [A]
              , Liftᵣ′ (id ⊢LB) [k′] [A′]
              , Lift₌ (id ⊢LB) k≡k′ A≡A′
         in sym-⊩≡
           (B          ⇒*⟨ D ⟩⊩
            Lift k′ A′ ≡˘⟨ Liftk≡Liftk′ ⟩⊩
            Lift k A   ∎⟨ ⊩Lift⇔ .proj₂ ([k] , [A]) ⟩⊩))

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩Lift≡Lift⇔ :
    Γ ⊩⟨ l ⟩ Lift k A ≡ Lift k′ A′ ⇔
    (Γ ⊩Level k ≡ k′ ∷Level ×
     Γ ⊩⟨ l ⟩ A ≡ A′)
  ⊩Lift≡Lift⇔ =
    ( (λ (_ , _ , Lift⇒*Lift , k≡k′ , A≡A′) →
      case whnfRed* Lift⇒*Lift Liftₙ of λ {
        PE.refl →
      k≡k′ , A≡A′ })
    , λ (k≡k′ , A≡A′) →
      let [k] , [k′] = wf-Level-eq k≡k′
          [A] , [A′] = wf-⊩≡ A≡A′
      in _ , _ , id (Liftⱼ (escapeLevel [k′]) (escape [A′])) , k≡k′ , A≡A′)
    ∘⇔ ⊩Lift≡⇔

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷Lift⇔ :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ Lift k A ⇔
    ((Γ ⊩⟨ l ⟩ Lift k A) ×
     ∃₂ λ t′ u′ →
     Γ ⊢ t ↘ t′ ∷ Lift k A ×
     Γ ⊢ u ↘ u′ ∷ Lift k A ×
     Γ ⊩⟨ l ⟩ lower t′ ≡ lower u′ ∷ A)
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
    Γ ⊩Level k ∷Level →
    Γ ⊩Level k₁ ≡ k₂ ∷Level →
    Γ ⊩⟨ l ⟩ A₁ ≡ A₂ ∷ U k →
    Γ ⊩⟨ ωᵘ ⟩ Lift k₁ A₁ ≡ Lift k₂ A₂ ∷ U (k supᵘₗ k₁)
  ⊩Lift≡Lift∷ ⊩k k₁≡k₂ A₁≡A₂ =
    Type→⊩≡∷U⇔ Liftₙ Liftₙ .proj₂
      ( ⊩supᵘₗ ⊩k (wf-Level-eq k₁≡k₂ .proj₁)
      , <ᵘ-ωᵘ
      , ⊩Lift≡Lift⇔ .proj₂
          ( k₁≡k₂
          , emb-⊩≡ ≤ᵘ-supᵘₗʳ (⊩≡∷U⇔ .proj₁ A₁≡A₂ .proj₂ .proj₂ .proj₁)
          )
      , ≅ₜ-Lift-cong (escapeLevelEq k₁≡k₂) (escape-⊩≡∷ A₁≡A₂)
      )

opaque

  -- Validity of equality preservation for Lift, seen as a term former.

  Lift-congᵗᵛ :
    Γ ⊩ᵛ⟨ l ⟩ k₁ ∷Level →
    Γ ⊩ᵛ⟨ l′ ⟩ k ≡ k′ ∷Level →
    Γ ⊩ᵛ⟨ l″ ⟩ A ≡ A′ ∷ U k₁ →
    Γ ⊩ᵛ⟨ ωᵘ ⟩ Lift k A ≡ Lift k′ A′ ∷ U (k₁ supᵘₗ k)
  Lift-congᵗᵛ ⊩k₁ k≡k′ A≡A′ =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( ⊩ᵛU (supᵘₗᵛ ⊩k₁ (wf-⊩ᵛ≡∷L k≡k′ .proj₁))
      , λ ∇′⊇∇ σ₁≡σ₂ →
          let ⊩k₁[σ₁] =
                ⊩ᵛ∷L→⊩ˢ∷→⊩[]∷L (defn-wk-⊩ᵛ∷L ∇′⊇∇ ⊩k₁)
                  (wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₁)
          in
          PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _)
            (PE.cong U $ PE.sym $
             supᵘₗ-[]′ λ not-ok →
             escape-⊩ᵛ∷L′ not-ok ⊩k₁ ,
             escape-⊩ᵛ≡∷L′ not-ok k≡k′ .proj₁) $
          ⊩Lift≡Lift∷ ⊩k₁[σ₁]
            (⊩ᵛ≡∷L→⊩ˢ≡∷→⊩[]≡[]∷L (defn-wk-⊩ᵛ≡∷L ∇′⊇∇ k≡k′) σ₁≡σ₂)
            (R.⊩≡∷→ (⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ∇′⊇∇ A≡A′) σ₁≡σ₂))
      )

opaque

  -- Validity of equality preservation for Lift, seen as a type former.

  Lift-congᵛ :
    Γ ⊩ᵛ⟨ l′ ⟩ k ≡ k′ ∷Level →
    Γ ⊩ᵛ⟨ l″ ⟩ A ≡ A′ →
    Γ ⊩ᵛ⟨ l″ ⟩ Lift k A ≡ Lift k′ A′
  Lift-congᵛ k≡k′ A≡A′ =
    ⊩ᵛ≡⇔ʰ .proj₂
      ( wf-⊩ᵛ (wf-⊩ᵛ≡ A≡A′ .proj₁)
      , λ ∇′⊇∇ σ₁≡σ₂ →
          let k[σ₁]≡k′[σ₂] =
                ⊩ᵛ≡∷L→⊩ˢ≡∷→⊩[]≡[]∷L (defn-wk-⊩ᵛ≡∷L ∇′⊇∇ k≡k′) σ₁≡σ₂
              A[σ₁]≡A′[σ₂] =
                R.⊩≡→ $ ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] (defn-wk-⊩ᵛ≡ ∇′⊇∇ A≡A′) σ₁≡σ₂
              ⊢A[σ₁] , ⊢A′[σ₂] = wf-⊢≡ (≅-eq (escape-⊩≡ A[σ₁]≡A′[σ₂]))
          in ⊩Lift≡Lift⇔ .proj₂
            ( k[σ₁]≡k′[σ₂]
            , A[σ₁]≡A′[σ₂]
            )
      )

opaque

  -- Validity for Lift, seen as a term former.

  Liftᵗᵛ :
    Γ ⊩ᵛ⟨ l ⟩ k₁ ∷Level →
    Γ ⊩ᵛ⟨ l′ ⟩ k ∷Level →
    Γ ⊩ᵛ⟨ l″ ⟩ A ∷ U k₁ →
    Γ ⊩ᵛ⟨ ωᵘ ⟩ Lift k A ∷ U (k₁ supᵘₗ k)
  Liftᵗᵛ ⊩k₁ ⊩k ⊩A = ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂
    (Lift-congᵗᵛ ⊩k₁ (refl-⊩ᵛ≡∷L ⊩k) (refl-⊩ᵛ≡∷ ⊩A))

opaque

  -- Validity for Lift, seen as a type former.

  Liftᵛ :
    Γ ⊩ᵛ⟨ l′ ⟩ k ∷Level →
    Γ ⊩ᵛ⟨ l″ ⟩ A →
    Γ ⊩ᵛ⟨ l″ ⟩ Lift k A
  Liftᵛ ⊩k ⊩A = ⊩ᵛ⇔⊩ᵛ≡ .proj₂
    (Lift-congᵛ (refl-⊩ᵛ≡∷L ⊩k) (refl-⊩ᵛ≡ ⊩A))

opaque

  ⊩ᵛLift→ :
    Γ ⊩ᵛ⟨ l ⟩ Lift k A →
    Γ ⊩ᵛ⟨ l ⟩ A
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
    Γ ⊩Level k ∷Level →
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩⟨ l′ ⟩ t₁ ≡ t₂ ∷ A →
    Γ ⊩⟨ l ⟩ lift t₁ ≡ lift t₂ ∷ Lift k A
  ⊩lift≡lift {t₁} {t₂} ⊩k ⊩A t₁≡t₂ =
    let ⊢k             = escapeLevel ⊩k
        ⊢A , ⊢t₁ , ⊢t₂ = wf-⊢≡∷ (≅ₜ-eq (escape-⊩≡∷ t₁≡t₂))
    in
    ⊩≡∷Lift⇔ .proj₂
      ( ⊩Lift⇔ .proj₂ (⊩k , ⊩A)
      , _ , _
      , (id (liftⱼ′ ⊢k ⊢t₁) , liftₙ)
      , (id (liftⱼ′ ⊢k ⊢t₂) , liftₙ)
      , (lower (lift t₁)  ⇒⟨ Lift-β ⊢A ⊢t₁ ⟩⊩∷
         t₁               ≡⟨ level-⊩≡∷ ⊩A t₁≡t₂ ⟩⊩∷⇐*
         t₂               ⇐⟨ Lift-β ⊢A ⊢t₂ ⟩∎
         lower (lift t₂)  ∎)
      )


opaque

  -- Reducibility for lift.

  ⊩lift :
    Γ ⊩Level k ∷Level →
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩⟨ l′ ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ lift t ∷ Lift k A
  ⊩lift ⊩k ⊩A =
    ⊩∷⇔⊩≡∷ .proj₂ ∘→ ⊩lift≡lift ⊩k ⊩A ∘→ ⊩∷⇔⊩≡∷ .proj₁

opaque

  -- Validity of lift.

  liftᵛ :
    Γ ⊩ᵛ⟨ l′ ⟩ k₂ ∷Level →
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊩ᵛ⟨ l″ ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ lift t ∷ Lift k₂ A
  liftᵛ ⊩k₂ ⊩A ⊩t =
    ⊩ᵛ∷⇔ʰ .proj₂
      ( Liftᵛ ⊩k₂ ⊩A
      , λ ∇′⊇∇ σ₁≡σ₂ →
          let ⊩σ₁ , _ = wf-⊩ˢ≡∷ σ₁≡σ₂ in
          ⊩lift≡lift (⊩ᵛ∷L→⊩ˢ∷→⊩[]∷L (defn-wk-⊩ᵛ∷L ∇′⊇∇ ⊩k₂) ⊩σ₁)
            (R.⊩→ $ ⊩ᵛ→⊩ˢ∷→⊩[] (defn-wk-⊩ᵛ ∇′⊇∇ ⊩A) ⊩σ₁)
            (R.⊩≡∷→ $
             ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (refl-⊩ᵛ≡∷ (defn-wk-⊩ᵛ∷ ∇′⊇∇ ⊩t)) σ₁≡σ₂)
      )

------------------------------------------------------------------------
-- The eliminator lower

opaque

  -- Reducibility of equality between applications of lower.

  ⊩lower≡lower :
    Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ Lift k A →
    Γ ⊩⟨ l ⟩ lower t₁ ≡ lower t₂ ∷ A
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
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ Lift k A →
    Γ ⊩ᵛ⟨ l ⟩ lower t ≡ lower u ∷ A
  lower-congᵛ t≡u = ⊩ᵛ≡∷⇔ʰ .proj₂
    ( ⊩ᵛLift→ (wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t≡u .proj₁))
    , λ ∇′⊇∇ σ₁≡σ₂ →
      ⊩lower≡lower
        (R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ∇′⊇∇ t≡u) σ₁≡σ₂)
    )

opaque

  -- Validity of lower.

  lowerᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ Lift k A →
    Γ ⊩ᵛ⟨ l ⟩ lower t ∷ A
  lowerᵛ ⊩t = ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ (lower-congᵛ (refl-⊩ᵛ≡∷ ⊩t))

------------------------------------------------------------------------
-- The β rule

opaque

  -- Reducibility for Lift-β.

  ⊩Lift-β :
    Γ ⊢ A →
    Γ ⊩⟨ l ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ lower (lift t) ≡ t ∷ A
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
    Γ ⊩ᵛ⟨ l′ ⟩ A →
    Γ ⊩ᵛ⟨ l″ ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l″ ⟩ lower (lift t) ≡ t ∷ A
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
    Γ ⊩Level k₂ ∷Level →
    Γ ⊩⟨ l₁ ⟩ A →
    Γ ⊩⟨ l₂ ⟩ t ∷ Lift k₂ A →
    Γ ⊩⟨ l₃ ⟩ u ∷ Lift k₂ A →
    Γ ⊩⟨ l₄ ⟩ lower t ≡ lower u ∷ A →
    Γ ⊩⟨ l₂ ⟩ t ≡ u ∷ Lift k₂ A
  ⊩Lift-η {t} {u} ⊩k₂ ⊩A∷U ⊩t ⊩u lowert≡loweru =
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
    Γ ⊩ᵛ⟨ l₂ ⟩ k₂ ∷Level →
    Γ ⊩ᵛ⟨ l₃ ⟩ A →
    Γ ⊩ᵛ⟨ l₄ ⟩ t ∷ Lift k₂ A →
    Γ ⊩ᵛ⟨ l₅ ⟩ u ∷ Lift k₂ A →
    Γ ⊩ᵛ⟨ l₆ ⟩ lower t ≡ lower u ∷ A →
    Γ ⊩ᵛ⟨ ωᵘ ⟩ t ≡ u ∷ Lift k₂ A
  Lift-ηᵛ ⊩k₂ ⊩A ⊩t ⊩u lowert≡loweru =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( emb-⊩ᵛ ≤ᵘ-ωᵘ (Liftᵛ ⊩k₂ ⊩A)
      , λ ∇′⊇∇ σ₁≡σ₂ →
        let ⊩σ₁ , ⊩σ₂ = wf-⊩ˢ≡∷ σ₁≡σ₂
            u[σ₁]≡u[σ₂] =
              R.⊩≡∷→ $
              ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (refl-⊩ᵛ≡∷ (defn-wk-⊩ᵛ∷ ∇′⊇∇ ⊩u)) σ₁≡σ₂
        in
        emb-⊩≡∷ ≤ᵘ-ωᵘ $
        ⊩Lift-η
          (⊩ᵛ∷L→⊩ˢ∷→⊩[]∷L (defn-wk-⊩ᵛ∷L ∇′⊇∇ ⊩k₂) ⊩σ₁)
          (R.⊩→ $ ⊩ᵛ→⊩ˢ∷→⊩[] (defn-wk-⊩ᵛ ∇′⊇∇ ⊩A) ⊩σ₁)
          (R.⊩∷→ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ (defn-wk-⊩ᵛ∷ ∇′⊇∇ ⊩t) ⊩σ₁)
          (wf-⊩≡∷ u[σ₁]≡u[σ₂] .proj₂)
          (R.⊩≡∷→ $
           ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ∇′⊇∇ lowert≡loweru) σ₁≡σ₂)
      )
