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
    Γ ⊩⟨ l ⟩ Unit s k ⇔
    (∃ λ ([k] : Γ ⊩Level k ∷Level) → ↑ᵘ [k] ≤ᵘ l × Unit-allowed s)
  ⊩Unit⇔ =
      (λ ⊩Unit →
        case Unit-view ⊩Unit of λ {
          (Unitᵣ (Unitᵣ k [k] k≤ Unit⇒*Unit ok)) →
      case Unit-PE-injectivity $
           whnfRed* Unit⇒*Unit Unitₙ of λ {
        (_ , PE.refl) →
      [k] , k≤ , ok }})
    , (λ ([k] , k≤ , ok) →
         Unitᵣ′ _ [k] k≤ (id (Unitⱼ (escapeLevel [k]) ok)) ok)

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩Unit≡⇔ :
    Γ ⊩⟨ l ⟩ Unit s k ≡ A ⇔
    (∃ λ ([k] : Γ ⊩Level k ∷Level) → ↑ᵘ [k] ≤ᵘ l ×
     Unit-allowed s × Γ ⊩Unit⟨ s ⟩ Unit s k ≡ A / k)
  ⊩Unit≡⇔ {l} {s} {k} {A} =
      (λ (⊩Unit , _ , Unit≡A) →
         case Unit-view ⊩Unit of λ {
           (Unitᵣ (Unitᵣ k [k] k≤ Unit⇒*Unit ok)) →
         case Unit-PE-injectivity $
              whnfRed* Unit⇒*Unit Unitₙ of λ {
           (_ , PE.refl) →
        [k] , k≤ , ok , Unit≡A }})
    , (λ ([k] , k≤ , ok , Unit₌ k′ A⇒*Unit k≡k′) →
         let [k′] = wf-⊩Level k≡k′ .proj₂
             ⊢Unitk = Unitⱼ (escapeLevel [k]) ok
             ⊢Unitk′ = Unitⱼ (escapeLevel [k′]) ok
             Unitk≡Unitk′
               = Unitᵣ′ _ [k] k≤ (id ⊢Unitk) ok
               , Unitᵣ′ _ [k′] (PE.subst (_≤ᵘ l) (↑ᵘ-cong k≡k′) k≤) (id ⊢Unitk′) ok
               , Unit₌ _ (id ⊢Unitk′) k≡k′
         in sym-⊩≡
           (A         ⇒*⟨ A⇒*Unit ⟩⊩
            Unit s k′ ≡˘⟨ Unitk≡Unitk′ ⟩⊩
            Unit s k  ∎⟨ ⊩Unit⇔ .proj₂ ([k] , k≤ , ok) ⟩⊩))

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩Unit≡Unit⇔ :
    Γ ⊩⟨ l ⟩ Unit s₁ k ≡ Unit s₂ k′ ⇔
    (∃ λ (k≡k′ : Γ ⊩Level k ≡ k′ ∷Level) → ↑ᵘ k≡k′ ≤ᵘ l ×
     Unit-allowed s₁ × s₁ PE.≡ s₂)
  ⊩Unit≡Unit⇔ {Γ} {l} {s₁} {k} {s₂} {k′} =
    Γ ⊩⟨ l ⟩ Unit s₁ k ≡ Unit s₂ k′                                 ⇔⟨ ⊩Unit≡⇔ ⟩
    (∃ λ [k] → ↑ᵘ [k] ≤ᵘ l × Unit-allowed s₁ ×
     Γ ⊩Unit⟨ s₁ ⟩ Unit s₁ k ≡ Unit s₂ k′ / k)                      ⇔⟨ ((λ { ([k] , k≤ , ok , Unit₌ _ Unit⇒*Unit k≡k′) →
                                                                          case Unit-PE-injectivity $ whnfRed* Unit⇒*Unit Unitₙ of λ {
                                                                            (PE.refl , PE.refl) →
                                                                          k≡k′ , PE.subst (_≤ᵘ l) ↑ᵘ-irrelevance k≤ , ok , PE.refl }})
                                                                      , λ { (k≡k′ , k≤ , ok , PE.refl) →
                                                                            wf-⊩Level k≡k′ .proj₁
                                                                          , PE.subst (_≤ᵘ l) ↑ᵘ-irrelevance k≤
                                                                          , ok
                                                                          , Unit₌ _ (id (Unitⱼ (escapeLevel (wf-⊩Level k≡k′ .proj₂)) ok)) k≡k′ }) ⟩
    (∃ λ k≡k′ → ↑ᵘ k≡k′ ≤ᵘ l × Unit-allowed s₁ × s₁ PE.≡ s₂)        □⇔

opaque
  unfolding _⊩⟨_⟩_≡_∷_ ⊩Unit⇔

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷Unit⇔ :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ Unit s k ⇔
    (∃ λ ([k] : Γ ⊩Level k ∷Level) → ↑ᵘ [k] ≤ᵘ l ×
     Unit-allowed s × Γ ⊩Unit⟨ s ⟩ t ≡ u ∷Unit/ k)
  ⊩≡∷Unit⇔ =
      (λ (⊩Unit , t≡u) →
         case Unit-view ⊩Unit of λ {
            (Unitᵣ (Unitᵣ k [k] k≤ Unit⇒*Unit ok)) →
         case Unit-PE-injectivity $
              whnfRed* Unit⇒*Unit Unitₙ of λ {
           (_ , PE.refl) →
         [k] , k≤ , ok , t≡u }})
    , (λ ([k] , k≤ , ok , t≡u) →
        ⊩Unit⇔ .proj₂ ([k] , k≤ , ok) , t≡u)

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷Unit⇔ :
    Γ ⊩⟨ l ⟩ t ∷ Unit s k ⇔
    (∃ λ ([k] : Γ ⊩Level k ∷Level) → ↑ᵘ [k] ≤ᵘ l ×
     Unit-allowed s × Γ ⊩Unit⟨ s ⟩ t ∷Unit/ k)
  ⊩∷Unit⇔ {Γ} {l} {t} {s} {k} =
    Γ ⊩⟨ l ⟩ t ∷ Unit s k                                   ⇔⟨ ⊩∷⇔⊩≡∷ ⟩
    Γ ⊩⟨ l ⟩ t ≡ t ∷ Unit s k                               ⇔⟨ ⊩≡∷Unit⇔ ⟩
    (∃ λ [k] → ↑ᵘ [k] ≤ᵘ l ×
     Unit-allowed s × Γ ⊩Unit⟨ s ⟩ t ≡ t ∷Unit/ k)          ⇔˘⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                                 Σ-cong-⇔ λ _ → ⊩Unit∷Unit⇔⊩Unit≡∷Unit) ⟩
    (∃ λ [k] → ↑ᵘ [k] ≤ᵘ l ×
     Unit-allowed s × Γ ⊩Unit⟨ s ⟩ t ∷Unit/ k)              □⇔

------------------------------------------------------------------------
-- Unit

opaque

  -- If the type Unit s l is valid, then it is allowed (given a
  -- certain assumption).

  ⊩ᵛUnit→Unit-allowed :
    ⦃ inc : Neutrals-included or-empty Γ ⦄ →
    Γ ⊩ᵛ⟨ l ⟩ Unit s k →
    Unit-allowed s
  ⊩ᵛUnit→Unit-allowed {Γ} {l} {s} {k} =
    Γ ⊩ᵛ⟨ l ⟩ Unit s k                        →⟨ R.⊩→ ∘→ ⊩ᵛ→⊩ ⟩
    Γ ⊩⟨ l ⟩ Unit s k                         ⇔⟨ ⊩Unit⇔ ⟩→
    (∃ λ [k] → ↑ᵘ [k] ≤ᵘ l × Unit-allowed s)  →⟨ proj₂ ∘→ proj₂ ⟩
    Unit-allowed s                            □

opaque

  -- Reducibility for Unit.

  ⊩Unit :
    ([k] : Γ ⊩Level k ∷Level) →
    Unit-allowed s →
    Γ ⊩⟨ ↑ᵘ [k] ⟩ Unit s k
  ⊩Unit [k] ok = ⊩Unit⇔ .proj₂ ([k] , ≤ᵘ-refl , ok)

opaque

  -- Validity for equality preservation for Unit, seen as a term former.

  Unit-congᵗᵛ :
    Γ ⊩ᵛ⟨ l ⟩ k ≡ k′ ∷ Level →
    Unit-allowed s →
    Γ ⊩ᵛ⟨ ωᵘ ⟩ Unit s k ≡ Unit s k′ ∷ U k
  Unit-congᵗᵛ k≡k′ ok =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( ⊩ᵛU (wf-⊩ᵛ≡∷ k≡k′ .proj₁)
      , λ σ₁≡σ₂ →
          let k[σ₁]≡k′[σ₂] = ⊩≡∷Level⇔ .proj₁ $ R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ k≡k′ σ₁≡σ₂
              ⊩k[σ₁] , ⊩k[σ₂] = wf-⊩Level k[σ₁]≡k′[σ₂]
          in Type→⊩≡∷U⇔ Unitₙ Unitₙ .proj₂
            ( ⊩k[σ₁] , <ᵘ-ωᵘ
            , ⊩Unit≡Unit⇔ .proj₂
              ( k[σ₁]≡k′[σ₂]
              , PE.subst (↑ᵘ k[σ₁]≡k′[σ₂] ≤ᵘ_) ↑ᵘ-irrelevance ≤ᵘ-refl
              , ok
              , PE.refl
              )
            , ≅ₜ-Unit-cong (escapeLevelEq k[σ₁]≡k′[σ₂]) ok
            )
      )

opaque

  -- Validity for equality preservation for Unit, seen as a type former.

  Unit-congᵛ :
    Γ ⊩ᵛ⟨ l ⟩ k ≡ k′ ∷ Level →
    Unit-allowed s →
    Γ ⊩ᵛ⟨ ωᵘ ⟩ Unit s k ≡ Unit s k′
  Unit-congᵛ k≡k′ ok = ⊩ᵛ≡∷U→⊩ᵛ≡ (Unit-congᵗᵛ k≡k′ ok)

opaque

  -- Validity for Unit, seen as a type former.

  Unitᵛ :
    Γ ⊩ᵛ⟨ l ⟩ k ∷ Level →
    Unit-allowed s →
    Γ ⊩ᵛ⟨ ωᵘ ⟩ Unit s k
  Unitᵛ ⊩k ok = ⊩ᵛ⇔⊩ᵛ≡ .proj₂ (Unit-congᵛ (⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁ ⊩k) ok)

opaque

  -- Validity for Unit, seen as a term former.

  Unitᵗᵛ :
    Γ ⊩ᵛ⟨ l ⟩ k ∷ Level →
    Unit-allowed s →
    Γ ⊩ᵛ⟨ ωᵘ ⟩ Unit s k ∷ U k
  Unitᵗᵛ ⊩k ok = ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ (Unit-congᵗᵛ (⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁ ⊩k) ok)

------------------------------------------------------------------------
-- The constructor star

opaque

  -- Reducibility of equality preservation for star.

  ⊩star≡star :
    (k≡k′ : Γ ⊩Level k ≡ k′ ∷Level) →
    Unit-allowed s →
    Γ ⊩⟨ ↑ᵘ k≡k′ ⟩ star s k ≡ star s k′ ∷ Unit s k
  ⊩star≡star {s} k≡k′ ok =
    let ⊩k , ⊩k′ = wf-⊩Level k≡k′
        Unit≡Unit = Unit-cong (≅ₜ-eq (escapeLevelEq k≡k′)) ok
    in ⊩≡∷Unit⇔ .proj₂
      ( ⊩k
      , PE.subst (_≤ᵘ ↑ᵘ k≡k′) ↑ᵘ-irrelevance ≤ᵘ-refl
      , ok
      , Unitₜ₌ _ _
          (id (starⱼ (escapeLevel ⊩k) ok) , starₙ)
          (id (conv (starⱼ (escapeLevel ⊩k′) ok) (sym Unit≡Unit)) , starₙ)
          ([Unit]-prop′→[Unit]-prop (starᵣ ⊩k k≡k′))
      )

opaque

  -- Reducibility for star.

  ⊩star :
    (⊩k : Γ ⊩Level k ∷Level) →
    Unit-allowed s →
    Γ ⊩⟨ ↑ᵘ ⊩k ⟩ star s k ∷ Unit s k
  ⊩star ⊩k ok = ⊩∷⇔⊩≡∷ .proj₂ (⊩star≡star ⊩k ok)

opaque

  -- Validity of equality preservation for star.

  star-congᵛ :
    Γ ⊩ᵛ⟨ l ⟩ k ≡ k′ ∷ Level →
    Unit-allowed s →
    Γ ⊩ᵛ⟨ ωᵘ ⟩ star s k ≡ star s k′ ∷ Unit s k
  star-congᵛ k≡k′ ok =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( Unitᵛ (wf-⊩ᵛ≡∷ k≡k′ .proj₁) ok
      , λ σ₁≡σ₂ →
          emb-⊩≡∷ ≤ᵘ-ωᵘ $ ⊩star≡star
            (⊩≡∷Level⇔ .proj₁ $ R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ k≡k′ σ₁≡σ₂)
            ok
      )

opaque

  -- Validity of star.

  starᵛ :
    Γ ⊩ᵛ⟨ l ⟩ k ∷ Level →
    Unit-allowed s →
    Γ ⊩ᵛ⟨ ωᵘ ⟩ star s k ∷ Unit s k
  starᵛ ⊩k ok = ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ (star-congᵛ (⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁ ⊩k) ok)

------------------------------------------------------------------------
-- The typing rule η-unit

opaque

  -- Reducibility of η-unit.

  ⊩η-unit :
    Γ ⊩⟨ l′ ⟩ t ∷ Unit s k →
    Γ ⊩⟨ l″ ⟩ u ∷ Unit s k →
    Unit-with-η s →
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ Unit s k
  ⊩η-unit ⊩t ⊩u η =
    let
      ([k] , k≤ , ok , Unitₜ _ t↘ _) = ⊩∷Unit⇔ .proj₁ ⊩t
      (_   , _  , _  , Unitₜ _ u↘ _) = ⊩∷Unit⇔ .proj₁ ⊩u
    in ⊩≡∷Unit⇔ .proj₂
      ( [k] , k≤ , ok
      , Unitₜ₌ _ _ t↘ u↘ (Unitₜ₌ˢ η)
      )

opaque

  -- Validity of η-unit.

  η-unitᵛ :
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ Unit s k →
    Γ ⊩ᵛ⟨ l″ ⟩ u ∷ Unit s k →
    Unit-with-η s →
    Γ ⊩ᵛ⟨ l′ ⟩ t ≡ u ∷ Unit s k
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
    Γ ∙ Unitʷ k₁ ⊢ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l ⟩ k₁ ≡ k₂ ∷ Level →
    Γ ∙ Unitʷ k₁ ⊩ᵛ⟨ l′ ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l″ ⟩ t₁ ≡ t₂ ∷ Unitʷ k₁ →
    Γ ⊩ᵛ⟨ l‴ ⟩ u₁ ≡ u₂ ∷ A₁ [ starʷ k₁ ]₀ →
    ⦃ inc : Neutrals-included or-empty Δ ⦄ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ unitrec p q k₁ A₁ t₁ u₁ [ σ₁ ] ≡
      unitrec p q k₂ A₂ t₂ u₂ [ σ₂ ] ∷ A₁ [ t₁ ]₀ [ σ₁ ]
  ⊩unitrec≡unitrec
    {k₁} {A₁} {A₂} {l} {k₂} {l′} {t₁} {t₂} {u₁} {u₂} {Δ} {σ₁} {σ₂} {p} {q}
    ⊢A₁≡A₂ k₁≡k₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ σ₁≡σ₂ =
    let
      k₁[σ₁]≡k₂[σ₂] = ⊩≡∷Level⇔ .proj₁ $ R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ k₁≡k₂ σ₁≡σ₂
      k₁[σ₁]≡k₁[σ₂] =
        ⊩≡∷Level⇔ .proj₁ $ R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷
        (⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁ $ wf-⊩ᵛ≡∷ k₁≡k₂ .proj₁) σ₁≡σ₂
      (⊩k₁[σ₁] , ⊩k₂[σ₂]) = wf-⊩Level k₁[σ₁]≡k₂[σ₂]
      ⊢k₁[σ₁] = escapeLevel ⊩k₁[σ₁]
      ⊢k₂[σ₂] = escapeLevel ⊩k₂[σ₂]
      (⊩A₁ , Unit₁⊩A₂) = wf-⊩ᵛ≡ A₁≡A₂
      (⊩t₁ , ⊩t₂∷Unit₁ , t₁≡t₂) = ⊩ᵛ≡∷⇔″ .proj₁ t₁≡t₂
      (⊩u₁ , ⊩u₂ , u₁≡u₂) = ⊩ᵛ≡∷⇔″ .proj₁ u₁≡u₂
      (⊩σ₁ , ⊩σ₂) = wf-⊩ˢ≡∷ σ₁≡σ₂
      ⊩Unit = ⊩ᵛ∷⇔ .proj₁ ⊩t₁ .proj₁
      A₁[σ₁⇑]≡A₂[σ₂⇑] = ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑]≡[⇑] A₁≡A₂ σ₁≡σ₂
    in
    case ⊩≡∷Unit⇔ .proj₁ (R.⊩≡∷⇔ .proj₁ (t₁≡t₂ σ₁≡σ₂)) of λ {
      (_ , _ , ok ,
       Unitₜ₌ t₁′ t₂′ (t₁[σ₁]⇒*t₁′ , _) (t₂[σ₂]⇒*t₂′∷Unit₁ , _) prop) →
    let
      Unit₁≡Unit₂ = Unit-congᵛ k₁≡k₂ ok
      Unit₁[]≡Unit₂[] = Unit-cong (≅ₜ-eq (escapeLevelEq k₁[σ₁]≡k₂[σ₂])) ok
      Unit₁[]≡Unit₁[] = Unit-cong (≅ₜ-eq (escapeLevelEq k₁[σ₁]≡k₁[σ₂])) ok
      ⋆₁≡⋆₂ = star-congᵛ k₁≡k₂ ok
      (⊩⋆₁ , ⊩⋆₂∷Unit₁) = wf-⊩ᵛ≡∷ ⋆₁≡⋆₂
      ⊩⋆₂ = conv-⊩ᵛ∷ Unit₁≡Unit₂ ⊩⋆₂∷Unit₁
      A₁[⋆₁]₀[σ₁]≡A₂[⋆₂]₀[σ₂] =
        PE.subst₂ (_⊢_≡_ _) (substConsId {t = star!} A₁)
          (substConsId {t = star!} A₂) $
        ≅-eq $ R.escape-⊩≡ $
        ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,] A₁≡A₂ σ₁≡σ₂ $
        ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ ⋆₁≡⋆₂ σ₁≡σ₂
      ⊩A₂ = conv-∙-⊩ᵛ Unit₁≡Unit₂ Unit₁⊩A₂
      ⊢A₁[]≡A₂[] =
        subst-⊢≡ ⊢A₁≡A₂ $
        ⊢ˢʷ≡∷-⇑ Unit₁[]≡Unit₁[] $ escape-⊩ˢ≡∷ σ₁≡σ₂ .proj₂
      (⊢A₁[σ₁⇑] , Unit₁⊢A₂[σ₂⇑]) = wf-⊢≡ ⊢A₁[]≡A₂[]
      ⊢A₂[σ₂⇑] = stability-⊢ refl-∙⟨ (wf-⊢≡ Unit₁[]≡Unit₂[] .proj₂) ∣ Unit₁[]≡Unit₂[] ⟩ Unit₁⊢A₂[σ₂⇑]
      ⊩t₂ = conv-⊩ᵛ∷ (Unit-congᵛ k₁≡k₂ ok) ⊩t₂∷Unit₁
      ⊩t₁[σ₁] = ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t₁ ⊩σ₁
      ⊩t₂[σ₂] = ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t₂ ⊩σ₂
      ⊢t₂[σ₂] = R.escape-⊩∷ ⊩t₂[σ₂]
      t₂[σ₂]⇒*t₂′ = conv* t₂[σ₂]⇒*t₂′∷Unit₁ Unit₁[]≡Unit₂[]
      ⊢u₁[σ₁] =
        R.escape-⊩∷ $
        PE.subst (R._⊩⟨_⟩_∷_ _ _ _) (singleSubstLift A₁ (starʷ _)) $
        ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u₁ ⊩σ₁
      ⊢u₂[σ₂] =
        R.escape-⊩∷ $
        R.conv-⊩∷
          (⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ A₁≡A₂ (refl-⊩ˢ≡∷ ⊩σ₂)
            (⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ ⋆₁≡⋆₂ (refl-⊩ˢ≡∷ ⊩σ₂))) $
        PE.subst (R._⊩⟨_⟩_∷_ _ _ _) (singleSubstLift A₁ (starʷ _)) $
        ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u₂ ⊩σ₂
    in case prop of λ where
      (Unitₜ₌ˢ η)  →
        unitrec p q k₁ A₁ t₁ u₁ [ σ₁ ] ∷ A₁ [ t₁ ]₀ [ σ₁ ]        ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift A₁ t₁) $
                                                                     unitrec-β-η ⊢k₁[σ₁] ⊢A₁[σ₁⇑] (R.escape-⊩∷ ⊩t₁[σ₁]) ⊢u₁[σ₁] ok
                                                                     (Unit-with-η-𝕨→Unitʷ-η η) ⟩⊩∷∷
                                                                   ⟨ R.⊩≡⇔ .proj₁ $
                                                                     ⊩ᵛ≡→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[] (refl-⊩ᵛ≡ ⊩A₁)
                                                                       (⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (η-unitᵛ ⊩t₁ ⊩⋆₁ η) $
                                                                        refl-⊩ˢ≡∷ ⊩σ₁)
                                                                       (refl-⊩ˢ≡∷ ⊩σ₁) ⟩⊩∷
        u₁ [ σ₁ ]  ∷ A₁ [ starʷ k₁ ]₀ [ σ₁ ]                      ≡⟨ R.⊩≡∷⇔ .proj₁ (u₁≡u₂ σ₁≡σ₂) ⟩⊩∷∷⇐*
                                                                   ⟨ A₁[⋆₁]₀[σ₁]≡A₂[⋆₂]₀[σ₂] ⟩⇒
                   ∷ A₂ [ starʷ k₂ ]₀ [ σ₂ ]                       ⟨ singleSubstLift A₂ (starʷ _) ⟩⇐≡
        u₂ [ σ₂ ]  ∷ A₂ [ σ₂ ⇑ ] [ starʷ k₂ [ σ₂ ] ]₀             ⇐⟨ conv
                                                                       (unitrec-β-η ⊢k₂[σ₂] ⊢A₂[σ₂⇑] ⊢t₂[σ₂] ⊢u₂[σ₂] ok
                                                                          (Unit-with-η-𝕨→Unitʷ-η η))
                                                                       (≅-eq $ R.escape-⊩≡ $
                                                                        ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩A₂) (refl-⊩ˢ≡∷ ⊩σ₂) $
                                                                        ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (η-unitᵛ ⊩t₂ ⊩⋆₂ η) $
                                                                        refl-⊩ˢ≡∷ ⊩σ₂)
                                                                   ⟩∎∷
        unitrec p q k₂ A₂ t₂ u₂ [ σ₂ ]                            ∎

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
          (starᵣ {k′} {k″} k₁≡k′ k′≡k″) →
            let
              k₂≡k″ =
                transEqTermLevel
                  (symLevel k₁[σ₁]≡k₂[σ₂])
                  (transEqTermLevel k₁≡k′ k′≡k″)
              ⊢k₁≡k′ = ≅ₜ-eq $ escapeLevelEq k₁≡k′
              ⊢k₂≡k″ = ≅ₜ-eq $ escapeLevelEq k₂≡k″
              A₁[σ₁⇑][⋆₁]₀≡A₁[σ₁⇑][⋆′]₀ =
                R.⊩≡→ $ ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩A₁) (refl-⊩ˢ≡∷ ⊩σ₁)
                  (R.→⊩≡∷ $ ⊩star≡star k₁≡k′ ok)
              A₂[σ₂⇑][⋆₂]₀≡A₂[σ₂⇑][⋆″]₀ =
                R.⊩≡→ $ ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩A₂) (refl-⊩ˢ≡∷ ⊩σ₂)
                  (R.→⊩≡∷ $ ⊩star≡star k₂≡k″ ok)
            in
            unitrec p q k₁ A₁ t₁       u₁ [ σ₁ ] ∷ A₁ [ t₁ ]₀ [ σ₁ ]         ⇒*⟨ unitrec⇒*₁ ⟩⊩∷∷
                                                                               ⟨ A₁[t₁]₀[σ₁]≡A₁[σ₁⇑][t₁′]₀ ⟩⊩∷
                                                 ∷ A₁ [ σ₁ ⇑ ] [ starʷ k′ ]₀ ˘⟨ A₁[σ₁⇑][⋆₁]₀≡A₁[σ₁⇑][⋆′]₀ ⟩⊩∷∷
            unitrec p q (k₁ [ σ₁ ]) (A₁ [ σ₁ ⇑ ]) (starʷ k′) (u₁ [ σ₁ ])
                                                 ∷ A₁ [ σ₁ ⇑ ] [ starʷ k₁ [ σ₁ ] ]₀
                                                                             ⇒⟨ unitrec-β ⊢k₁[σ₁] ⊢k₁≡k′ ⊢A₁[σ₁⇑] ⊢u₁[σ₁] ok no-η ⟩⊩∷∷
                                                                             ˘⟨ singleSubstLift A₁ (starʷ _) ⟩⊩∷≡
            u₁ [ σ₁ ]                            ∷ A₁ [ starʷ k₁ ]₀ [ σ₁ ]   ≡⟨ R.⊩≡∷→ $ u₁≡u₂ σ₁≡σ₂ ⟩⊩∷∷⇐*
                                                                              ⟨ A₁[⋆₁]₀[σ₁]≡A₂[⋆₂]₀[σ₂] ⟩⇒
                                                 ∷ A₂ [ starʷ k₂ ]₀ [ σ₂ ]    ⟨ singleSubstLift A₂ (starʷ _) ⟩⇐≡
            u₂ [ σ₂ ]                            ∷ A₂ [ σ₂ ⇑ ] [ starʷ k₂ [ σ₂ ] ]₀
                                                                             ⇐⟨ unitrec-β ⊢k₂[σ₂] ⊢k₂≡k″ ⊢A₂[σ₂⇑] ⊢u₂[σ₂] ok no-η ⟩∷
                                                                              ⟨ ≅-eq $ escape-⊩≡ A₂[σ₂⇑][⋆₂]₀≡A₂[σ₂⇑][⋆″]₀ ⟩⇒
                                                 ∷ A₂ [ σ₂ ⇑ ] [ starʷ k″ ]₀ ˘⟨ ⊢A₂[t₂]₀[σ₂]≡A₂[σ₂⇑][t₂′]₀ ⟩⇒
            unitrec p q (k₂ [ σ₂ ]) (A₂ [ σ₂ ⇑ ]) (starʷ k″) (u₂ [ σ₂ ])
                                                 ∷ A₂ [ t₂ ]₀ [ σ₂ ]         ⇐*⟨ unitrec⇒*₂ ⟩∎∷
            unitrec p q k₂ A₂ t₂        u₂ [ σ₂ ]                            ∎

          (ne (neNfₜ₌ inc t₁′-ne t₂′-ne t₁′~t₂′)) →
            Δ ⊩⟨ l′ ⟩
              unitrec p q (k₁ [ σ₁ ]) (A₁ [ σ₁ ⇑ ]) (t₁ [ σ₁ ]) (u₁ [ σ₁ ]) ≡
              unitrec p q (k₂ [ σ₂ ]) (A₂ [ σ₂ ⇑ ]) (t₂ [ σ₂ ]) (u₂ [ σ₂ ]) ∷
              A₁ [ t₁ ]₀ [ σ₁ ] ∋
            (unitrec p q k₁ A₁ t₁ u₁ [ σ₁ ]
               ∷ A₁ [ t₁ ]₀ [ σ₁ ]                                ⇒*⟨ unitrec⇒*₁ ⟩⊩∷∷
                                                                    ⟨ A₁[t₁]₀[σ₁]≡A₁[σ₁⇑][t₁′]₀ ⟩⊩∷
             unitrec p q (k₁ [ σ₁ ]) (A₁ [ σ₁ ⇑ ]) t₁′ (u₁ [ σ₁ ])
               ∷ A₁ [ σ₁ ⇑ ] [ t₁′ ]₀                             ≡⟨ neutral-⊩≡∷ inc (wf-⊩≡ A₁[t₁]₀[σ₁]≡A₁[σ₁⇑][t₁′]₀ .proj₂)
                                                                       (unitrecₙ no-η t₁′-ne) (unitrecₙ no-η t₂′-ne)
                                                                       (~-unitrec ⊢k₁[σ₁] ⊢k₂[σ₂]
                                                                          (≅ₜ-eq $ escapeLevelEq k₁[σ₁]≡k₂[σ₂])
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

             unitrec p q (k₂ [ σ₂ ]) (A₂ [ σ₂ ⇑ ]) t₂′ (u₂ [ σ₂ ])
               ∷ A₂ [ t₂ ]₀ [ σ₂ ]                                ⇐*⟨ unitrec⇒*₂ ⟩∎∷

             unitrec p q (k₂ [ σ₂ ]) (A₂ [ σ₂ ⇑ ]) (t₂ [ σ₂ ]) (u₂ [ σ₂ ]) ∎) }

opaque

  -- Validity of equality between applications of unitrec.

  unitrec-congᵛ :
    Γ ∙ Unitʷ k₁ ⊢ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l ⟩ k₁ ≡ k₂ ∷ Level →
    Γ ∙ Unitʷ k₁ ⊩ᵛ⟨ l′ ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l″ ⟩ t₁ ≡ t₂ ∷ Unitʷ k₁ →
    Γ ⊩ᵛ⟨ l‴ ⟩ u₁ ≡ u₂ ∷ A₁ [ starʷ k₁ ]₀ →
    Γ ⊩ᵛ⟨ l′ ⟩ unitrec p q k₁ A₁ t₁ u₁ ≡ unitrec p q k₂ A₂ t₂ u₂ ∷
      A₁ [ t₁ ]₀
  unitrec-congᵛ ⊢A₁≡A₂ k₁≡k₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ (wf-⊩ᵛ≡ A₁≡A₂ .proj₁) (wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁)
      , ⊩unitrec≡unitrec ⊢A₁≡A₂ k₁≡k₂ A₁≡A₂ t₁≡t₂ u₁≡u₂
      )

opaque

  -- Validity of unitrec.

  unitrecᵛ :
    Γ ∙ Unitʷ k ⊢ A →
    Γ ⊩ᵛ⟨ l ⟩ k ∷ Level →
    Γ ∙ Unitʷ k ⊩ᵛ⟨ l′ ⟩ A →
    Γ ⊩ᵛ⟨ l″ ⟩ t ∷ Unitʷ k →
    Γ ⊩ᵛ⟨ l‴ ⟩ u ∷ A [ starʷ k ]₀ →
    Γ ⊩ᵛ⟨ l′ ⟩ unitrec p q k A t u ∷ A [ t ]₀
  unitrecᵛ ⊢A ⊩k ⊩A ⊩t ⊩u =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    unitrec-congᵛ (refl ⊢A) (refl-⊩ᵛ≡∷ ⊩k) (refl-⊩ᵛ≡ ⊩A) (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ᵛ≡∷ ⊩u)

opaque

  -- Validity of the unitrec β rule.

  unitrec-βᵛ :
    Γ ∙ Unitʷ k ⊢ A →
    Γ ⊩ᵛ⟨ l ⟩ k ∷ Level →
    Γ ∙ Unitʷ k ⊩ᵛ⟨ l″ ⟩ A →
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ A [ starʷ k ]₀ →
    ¬ Unitʷ-η →
    Γ ⊩ᵛ⟨ l′ ⟩ unitrec p q k A (starʷ k) t ≡ t ∷ A [ starʷ k ]₀
  unitrec-βᵛ {A} ⊢A ⊩k ⊩A ⊩t no-η =
    let ⊢Unit = ⊢∙→⊢ (wf ⊢A) in
    ⊩ᵛ∷-⇐
      (λ ⊩σ →
         let ⊢k[σ] = R.escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩k ⊩σ in
         PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift A _) $
         unitrec-β
           ⊢k[σ] (refl ⊢k[σ])
           (subst-⊢ ⊢A (⊢ˢʷ∷-⇑′ ⊢Unit (escape-⊩ˢ∷ ⊩σ .proj₂)))
           (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
            R.escape-⊩∷ (⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t ⊩σ))
           (inversion-Unit-allowed ⊢Unit) no-η)
      ⊩t

opaque

  -- Validity of the rule called unitrec-β-η.

  unitrec-β-ηᵛ :
    Γ ∙ Unitʷ k ⊢ A →
    Γ ⊩ᵛ⟨ l ⟩ k ∷ Level →
    Γ ∙ Unitʷ k ⊩ᵛ⟨ l′ ⟩ A →
    Γ ⊩ᵛ⟨ l″ ⟩ t ∷ Unitʷ k →
    Γ ⊩ᵛ⟨ l‴ ⟩ u ∷ A [ starʷ k ]₀ →
    Unitʷ-η →
    Γ ⊩ᵛ⟨ l′ ⟩ unitrec p q k A t u ≡ u ∷ A [ t ]₀
  unitrec-β-ηᵛ {A} ⊢A ⊩k ⊩A ⊩t ⊩u η =
    let ⊢Unit = ⊢∙→⊢ (wf ⊢A)
        ok    = inversion-Unit-allowed ⊢Unit
    in
    ⊩ᵛ∷-⇐
      (λ ⊩σ →
         PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift A _) $
         unitrec-β-η
           (R.escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩k ⊩σ)
           (subst-⊢ ⊢A (⊢ˢʷ∷-⇑′ ⊢Unit (escape-⊩ˢ∷ ⊩σ .proj₂)))
           (R.escape-⊩∷ (⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t ⊩σ))
           (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
            R.escape-⊩∷ (⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u ⊩σ))
           ok η)
      (conv-⊩ᵛ∷
         (⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀ (refl-⊩ᵛ≡ ⊩A) $
          η-unitᵛ (starᵛ ⊩k ok) ⊩t (inj₂ η))
         ⊩u)
