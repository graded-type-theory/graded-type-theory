------------------------------------------------------------------------
-- Validity for levels
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Level
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  ⦃ eqrel : EqRelSet R ⦄
  where

open EqRelSet eqrel
open Type-restrictions R

open import Definition.LogicalRelation R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Hidden R ⦃ eqrel ⦄
import Definition.LogicalRelation.Hidden.Restricted R ⦃ eqrel ⦄ as R
open import Definition.LogicalRelation.Irrelevance R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties R ⦃ eqrel ⦄
open import Definition.LogicalRelation.ShapeView R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Substitution R ⦃ eqrel ⦄

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Reduction R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ
open import Tools.Sum
import Tools.PropositionalEquality as PE

private variable
  Γ Δ                               : Con Term _
  A A₁ A₂ B t t₁ t₂ u u₁ u₂ v v₁ v₂ : Term _
  σ₁ σ₂                             : Subst _ _
  l l′ l″ l‴                        : Universe-level

------------------------------------------------------------------------
-- Characterisation lemmas

opaque

  -- A characterisation lemma for _⊩⟨_⟩ Level

  ⊩Level⇔ : Γ ⊩⟨ l ⟩ Level ⇔ ⊢ Γ
  ⊩Level⇔ =
      (λ ⊩Level →
        case Level-view ⊩Level of λ {
          (Levelᵣ Level⇒*Level) →
        wfEq (subset* Level⇒*Level) })
    , (λ ⊢Γ → Levelᵣ (id (Levelⱼ ⊢Γ)))

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩ Level ≡_

  ⊩Level≡⇔ : Γ ⊩⟨ l ⟩ Level ≡ A ⇔ Γ ⊩Level Level ≡ A
  ⊩Level≡⇔ =
      (λ (⊩Level , _ , Level≡A) →
         case Level-view ⊩Level of λ {
           (Levelᵣ _) →
         Level≡A })
    , (λ Level≡A →
         case id (Levelⱼ (wfEq (subset* Level≡A))) of λ
           Level⇒*Level →
         let ⊩Level = Levelᵣ Level⇒*Level in
           ⊩Level
         , (redSubst* Level≡A ⊩Level) .proj₁
         , Level≡A)

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷ Level

  ⊩≡∷Level⇔ : Γ ⊩⟨ l ⟩ t ≡ u ∷ Level ⇔ Γ ⊩Level t ≡ u ∷Level
  ⊩≡∷Level⇔ =
      (λ (⊩Level , t≡u) →
         case Level-view ⊩Level of λ {
           (Levelᵣ _) →
         t≡u })
    , (λ t≡u →
          Levelᵣ (id (Levelⱼ (wfTerm (escapeLevel (wf-Level-eq t≡u .proj₁)))))
         , t≡u)

opaque

  ⊩Level∷Level⇔ : Γ ⊩Level t ∷Level ⇔ Γ ⊩Level t ≡ t ∷Level
  ⊩Level∷Level⇔ = reflLevel , proj₁ ∘→ wf-Level-eq

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷ Level

  ⊩∷Level⇔ : Γ ⊩⟨ l ⟩ t ∷ Level ⇔ Γ ⊩Level t ∷Level
  ⊩∷Level⇔ {Γ} {l} {t} =
    Γ ⊩⟨ l ⟩ t ∷ Level      ⇔⟨ ⊩∷⇔⊩≡∷ ⟩
    Γ ⊩⟨ l ⟩ t ≡ t ∷ Level  ⇔⟨ ⊩≡∷Level⇔ ⟩
    Γ ⊩Level t ≡ t ∷Level   ⇔˘⟨ ⊩Level∷Level⇔ ⟩
    Γ ⊩Level t ∷Level       □⇔

opaque

  ⊩zeroᵘ : ⊢ Γ → Γ ⊩Level zeroᵘ ∷Level
  ⊩zeroᵘ ⊢Γ =
    Levelₜ _ (id (zeroᵘⱼ ⊢Γ)) zeroᵘᵣ

  -- A characterisation lemma for _⊩⟨_⟩ zeroᵘ ∷ Level

  ⊩zeroᵘ∷Level⇔ : Γ ⊩⟨ l ⟩ zeroᵘ ∷ Level ⇔ ⊢ Γ
  ⊩zeroᵘ∷Level⇔ =
      wfTerm ∘→ escape-⊩∷
    , ⊩∷Level⇔ .proj₂ ∘→ ⊩zeroᵘ

opaque

  -- A characterisation lemma for _⊩⟨_⟩ zeroᵘ ≡ zeroᵘ ∷ Level

  ⊩zeroᵘ≡zeroᵘ∷Level⇔ : Γ ⊩⟨ l ⟩ zeroᵘ ≡ zeroᵘ ∷ Level ⇔ ⊢ Γ
  ⊩zeroᵘ≡zeroᵘ∷Level⇔ {Γ} {l} =
    Γ ⊩⟨ l ⟩ zeroᵘ ≡ zeroᵘ ∷ Level  ⇔˘⟨ ⊩∷⇔⊩≡∷ ⟩
    Γ ⊩⟨ l ⟩ zeroᵘ ∷ Level          ⇔⟨ ⊩zeroᵘ∷Level⇔ ⟩
    ⊢ Γ                             □⇔

opaque

  ⊩sucᵘ≡sucᵘ⇔ :
    Γ ⊩Level sucᵘ t ≡ sucᵘ u ∷Level ⇔
    Γ ⊩Level t ≡ u ∷Level
  ⊩sucᵘ≡sucᵘ⇔ {Γ} {t} {u} = lemma₁ , ⊩sucᵘ≡sucᵘ
    where
    lemma₀ : ∀ {t u} → [Level]-prop Γ (sucᵘ t) (sucᵘ u) → Γ ⊩Level t ≡ u ∷Level
    lemma₀ (sucᵘᵣ t≡u) = t≡u
    lemma₀ (neLvl x₂) = case nelsplit x₂ .proj₁ of λ { (ne ()) }

    lemma₁ : Γ ⊩Level sucᵘ t ≡ sucᵘ u ∷Level → Γ ⊩Level t ≡ u ∷Level
    lemma₁ (Levelₜ₌ _ _ sucᵘ-t⇒*t′ sucᵘ-u⇒*u′ t′≡u′) =
      case whnfRed*Term sucᵘ-t⇒*t′ sucᵘₙ of λ {
        PE.refl →
      case whnfRed*Term sucᵘ-u⇒*u′ sucᵘₙ of λ {
        PE.refl →
      lemma₀ t′≡u′}}

  -- A characterisation lemma for _⊩⟨_⟩ sucᵘ _ ≡ sucᵘ _ ∷ Level

  ⊩sucᵘ≡sucᵘ∷Level⇔ :
    Γ ⊩⟨ l ⟩ sucᵘ t ≡ sucᵘ u ∷ Level ⇔
    Γ ⊩⟨ l ⟩ t ≡ u ∷ Level
  ⊩sucᵘ≡sucᵘ∷Level⇔ {Γ} {l} {t} {u} =
    Γ ⊩⟨ l ⟩ sucᵘ t ≡ sucᵘ u ∷ Level  ⇔⟨ ⊩≡∷Level⇔ ⟩
    Γ ⊩Level sucᵘ t ≡ sucᵘ u ∷Level   ⇔⟨ ⊩sucᵘ≡sucᵘ⇔ ⟩
    Γ ⊩Level t ≡ u ∷Level             ⇔˘⟨ ⊩≡∷Level⇔ ⟩
    Γ ⊩⟨ l ⟩ t ≡ u ∷ Level            □⇔

opaque

  -- A characterisation lemma for _⊩⟨_⟩ sucᵘ _ ∷ Level

  ⊩sucᵘ∷Level⇔ :
    Γ ⊩⟨ l ⟩ sucᵘ t ∷ Level ⇔
    Γ ⊩⟨ l ⟩ t ∷ Level
  ⊩sucᵘ∷Level⇔ {Γ} {l} {t} =
    Γ ⊩⟨ l ⟩ sucᵘ t ∷ Level           ⇔⟨ ⊩∷⇔⊩≡∷ ⟩
    Γ ⊩⟨ l ⟩ sucᵘ t ≡ sucᵘ t ∷ Level  ⇔⟨ ⊩sucᵘ≡sucᵘ∷Level⇔ ⟩
    Γ ⊩⟨ l ⟩ t ≡ t ∷ Level            ⇔˘⟨ ⊩∷⇔⊩≡∷ ⟩
    Γ ⊩⟨ l ⟩ t ∷ Level                □⇔

opaque

  0≡t : ∀ {t} → [Level]-prop Γ zeroᵘ t → t PE.≡ zeroᵘ
  0≡t zeroᵘᵣ = PE.refl
  0≡t (neLvl n) = case nelsplit n .proj₁ of λ { (ne ()) }

  -- A characterisation lemma for _⊩⟨_⟩ zeroᵘ ≡ sucᵘ _ ∷ Level

  ⊩zeroᵘ≡sucᵘ∷Level⇔ : Γ ⊩⟨ l ⟩ zeroᵘ ≡ sucᵘ t ∷ Level ⇔ ⊥
  ⊩zeroᵘ≡sucᵘ∷Level⇔ =
      (λ zeroᵘ≡sucᵘ →
         case ⊩≡∷Level⇔ .proj₁ zeroᵘ≡sucᵘ of λ {
           (Levelₜ₌ _ _ zeroᵘ⇒* sucᵘ⇒* rest) →
         case whnfRed*Term zeroᵘ⇒* zeroᵘₙ of λ {
           PE.refl →
         case whnfRed*Term sucᵘ⇒* sucᵘₙ of λ {
           PE.refl →
         sucᵘ≢zeroᵘ (0≡t rest) }}})
    , ⊥-elim

------------------------------------------------------------------------
-- Level

opaque

  -- Validity of Level, seen as a type former.

  Levelᵛ : ⊩ᵛ Γ → Γ ⊩ᵛ⟨ l ⟩ Level
  Levelᵛ {Γ} {l} ⊩Γ =
    ⊩ᵛ⇔ʰ .proj₂
      ( ⊩Γ
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ          →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ⊢ Δ                       →⟨ Levelⱼ ⟩
          (Δ ⊢ Level)               →⟨ id ⟩
          Δ ⊢ Level ⇒* Level        ⇔˘⟨ ⊩Level≡⇔ ⟩→
          Δ ⊩⟨ l ⟩ Level ≡ Level    □
      )

------------------------------------------------------------------------
-- The constructors zeroᵘ and sucᵘ

opaque

  -- Reducibility of zeroᵘ.

  ⊩zeroᵘ∷Level :
    ⊢ Γ →
    Γ ⊩⟨ 0ᵘ ⟩ zeroᵘ ∷ Level
  ⊩zeroᵘ∷Level = ⊩zeroᵘ∷Level⇔ .proj₂

opaque

  -- Validity of zeroᵘ.

  zeroᵘᵛ :
    ⊩ᵛ Γ →
    Γ ⊩ᵛ⟨ 0ᵘ ⟩ zeroᵘ ∷ Level
  zeroᵘᵛ {Γ} ⊩Γ =
    ⊩ᵛ∷⇔ʰ .proj₂
      ( Levelᵛ ⊩Γ
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ                 →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ⊢ Δ                              ⇔˘⟨ ⊩zeroᵘ≡zeroᵘ∷Level⇔ ⟩→
          Δ ⊩⟨ 0ᵘ ⟩ zeroᵘ ≡ zeroᵘ ∷ Level  □
      )

opaque

  -- Reducibility of sucᵘ.

  ⊩sucᵘ∷Level :
    Γ ⊩⟨ l ⟩ t ∷ Level →
    Γ ⊩⟨ l ⟩ sucᵘ t ∷ Level
  ⊩sucᵘ∷Level = ⊩sucᵘ∷Level⇔ .proj₂

opaque

  -- Reducibility of equality between applications of sucᵘ.

  ⊩sucᵘ≡sucᵘ∷Level :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ Level →
    Γ ⊩⟨ l ⟩ sucᵘ t ≡ sucᵘ u ∷ Level
  ⊩sucᵘ≡sucᵘ∷Level = ⊩sucᵘ≡sucᵘ∷Level⇔ .proj₂

opaque

  -- Validity of equality preservation for sucᵘ.

  sucᵘ-congᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ Level →
    Γ ⊩ᵛ⟨ l ⟩ sucᵘ t ≡ sucᵘ u ∷ Level
  sucᵘ-congᵛ t≡u =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( Levelᵛ (wf-⊩ᵛ $ wf-⊩ᵛ∷ $ wf-⊩ᵛ≡∷ t≡u .proj₁)
      , ⊩sucᵘ≡sucᵘ∷Level ∘→ R.⊩≡∷→ ∘→ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t≡u
      )

opaque

  -- Validity of sucᵘ.

  sucᵘᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ l ⟩ sucᵘ t ∷ Level
  sucᵘᵛ ⊩t =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $ sucᵘ-congᵛ (refl-⊩ᵛ≡∷ ⊩t)

------------------------------------------------------------------------
-- The operator maxᵘ

opaque

  -- Reducibility of equality preservation for maxᵘ.

  ⊩maxᵘ≡maxᵘ∷Level :
    Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ Level →
    Γ ⊩⟨ l′ ⟩ u₁ ≡ u₂ ∷ Level →
    Γ ⊩⟨ l ⟩ t₁ maxᵘ u₁ ≡ t₂ maxᵘ u₂ ∷ Level
  ⊩maxᵘ≡maxᵘ∷Level t₁≡t₂ u₁≡u₂ =
    ⊩≡∷Level⇔ .proj₂ $ ⊩maxᵘ≡maxᵘ
      (⊩≡∷Level⇔ .proj₁ t₁≡t₂)
      (⊩≡∷Level⇔ .proj₁ u₁≡u₂)

opaque

  -- Validity of equality preservation for maxᵘ.

  maxᵘ-congᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ Level →
    Γ ⊩ᵛ⟨ l′ ⟩ u₁ ≡ u₂ ∷ Level →
    Γ ⊩ᵛ⟨ l ⟩ t₁ maxᵘ u₁ ≡ t₂ maxᵘ u₂ ∷ Level
  maxᵘ-congᵛ t₁≡t₂ u₁≡u₂ =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁)
      , λ σ₁≡σ₂ → ⊩maxᵘ≡maxᵘ∷Level
          (R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t₁≡t₂ σ₁≡σ₂)
          (R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ u₁≡u₂ σ₁≡σ₂)
      )

opaque

  -- Validity of maxᵘ.

  maxᵘᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ Level →
    Γ ⊩ᵛ⟨ l ⟩ t maxᵘ u ∷ Level
  maxᵘᵛ ⊩t ⊩u = ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    maxᵘ-congᵛ (⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁ ⊩t) (⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁ ⊩u)

opaque

  -- Reducibility of maxᵘ-zeroˡ.

  ⊩maxᵘ-zeroˡ :
    Γ ⊩⟨ l ⟩ t ∷ Level →
    Γ ⊩⟨ l ⟩ zeroᵘ maxᵘ t ≡ t ∷ Level
  ⊩maxᵘ-zeroˡ ⊩t = ⊩∷-⇐* (redMany (maxᵘ-zeroˡ (escape-⊩∷ ⊩t))) ⊩t

opaque

  -- Validity of maxᵘ-zeroˡ.

  maxᵘ-zeroˡᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ l ⟩ zeroᵘ maxᵘ t ≡ t ∷ Level
  maxᵘ-zeroˡᵛ ⊩t =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( wf-⊩ᵛ∷ ⊩t
      , λ σ₁≡σ₂ →
          let t[σ₁]≡t[σ₂] = ⊩ᵛ∷⇔ʰ .proj₁ ⊩t .proj₂ σ₁≡σ₂
          in trans-⊩≡∷ (⊩maxᵘ-zeroˡ (wf-⊩≡∷ t[σ₁]≡t[σ₂] .proj₁)) t[σ₁]≡t[σ₂]
      )

opaque

  -- Reducibility of maxᵘ-zeroʳ.

  ⊩maxᵘ-zeroʳ∷Level :
    Γ ⊩⟨ l ⟩ t ∷ Level →
    Γ ⊩⟨ l ⟩ t maxᵘ zeroᵘ ≡ t ∷ Level
  ⊩maxᵘ-zeroʳ∷Level ⊩t = ⊩≡∷Level⇔ .proj₂ $
    ⊩maxᵘ-zeroʳ (⊩∷Level⇔ .proj₁ ⊩t)

opaque

  -- Validity of maxᵘ-zeroʳ.

  maxᵘ-zeroʳᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ l ⟩ t maxᵘ zeroᵘ ≡ t ∷ Level
  maxᵘ-zeroʳᵛ ⊩t =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( wf-⊩ᵛ∷ ⊩t
      , λ σ₁≡σ₂ →
          let t[σ₁]≡t[σ₂] = ⊩ᵛ∷⇔ʰ .proj₁ ⊩t .proj₂ σ₁≡σ₂
              ⊩t[σ₁] , ⊩t[σ₂] = wf-⊩≡∷ t[σ₁]≡t[σ₂]
          in trans-⊩≡∷ (⊩maxᵘ-zeroʳ∷Level ⊩t[σ₁]) t[σ₁]≡t[σ₂]
      )

opaque

  -- Reducibility of maxᵘ-sucᵘ.

  ⊩maxᵘ-sucᵘ :
    Γ ⊩⟨ l ⟩ t ∷ Level →
    Γ ⊩⟨ l′ ⟩ u ∷ Level →
    Γ ⊩⟨ l ⟩ sucᵘ t maxᵘ sucᵘ u ≡ sucᵘ (t maxᵘ u) ∷ Level
  ⊩maxᵘ-sucᵘ ⊩t ⊩u = ⊩∷-⇐*
    (redMany (maxᵘ-sucᵘ (escape-⊩∷ ⊩t) (escape-⊩∷ ⊩u)))
    (⊩sucᵘ∷Level $ ⊩∷⇔⊩≡∷ .proj₂ $
      ⊩maxᵘ≡maxᵘ∷Level (refl-⊩≡∷ ⊩t) (refl-⊩≡∷ ⊩u))

opaque

  -- Validity of maxᵘ-sucᵘ.

  maxᵘ-sucᵘᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ Level →
    Γ ⊩ᵛ⟨ l ⟩ sucᵘ t maxᵘ sucᵘ u ≡ sucᵘ (t maxᵘ u) ∷ Level
  maxᵘ-sucᵘᵛ ⊩t ⊩u =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( wf-⊩ᵛ∷ ⊩t
      , λ σ₁≡σ₂ →
          let t[σ₁]≡t[σ₂] = ⊩ᵛ∷⇔ʰ .proj₁ ⊩t .proj₂ σ₁≡σ₂
              u[σ₁]≡u[σ₂] = ⊩ᵛ∷⇔ʰ .proj₁ ⊩u .proj₂ σ₁≡σ₂
              ⊩t[σ₁] , ⊩t[σ₂] = wf-⊩≡∷ t[σ₁]≡t[σ₂]
              ⊩u[σ₁] , ⊩u[σ₂] = wf-⊩≡∷ u[σ₁]≡u[σ₂]
          in trans-⊩≡∷
            (⊩maxᵘ-sucᵘ ⊩t[σ₁] ⊩u[σ₁])
            (⊩sucᵘ≡sucᵘ∷Level $ ⊩maxᵘ≡maxᵘ∷Level t[σ₁]≡t[σ₂] u[σ₁]≡u[σ₂])
      )

opaque

  ⊩maxᵘ-assoc∷Level :
    Γ ⊩⟨ l ⟩ t ∷ Level →
    Γ ⊩⟨ l′ ⟩ u ∷ Level →
    Γ ⊩⟨ l″ ⟩ v ∷ Level →
    Γ ⊩⟨ l ⟩ (t maxᵘ u) maxᵘ v ≡ t maxᵘ (u maxᵘ v) ∷ Level
  ⊩maxᵘ-assoc∷Level ⊩t ⊩u ⊩v = ⊩≡∷Level⇔ .proj₂ $
    ⊩maxᵘ-assoc (⊩∷Level⇔ .proj₁ ⊩t) (⊩∷Level⇔ .proj₁ ⊩u) (⊩∷Level⇔ .proj₁ ⊩v)

  maxᵘ-assocᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ Level →
    Γ ⊩ᵛ⟨ l″ ⟩ v ∷ Level →
    Γ ⊩ᵛ⟨ l ⟩ (t maxᵘ u) maxᵘ v ≡ t maxᵘ (u maxᵘ v) ∷ Level
  maxᵘ-assocᵛ ⊩t ⊩u ⊩v =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( wf-⊩ᵛ∷ ⊩t
      , λ σ₁≡σ₂ →
          let t[σ₁]≡t[σ₂] = ⊩ᵛ∷⇔ʰ .proj₁ ⊩t .proj₂ σ₁≡σ₂
              u[σ₁]≡u[σ₂] = ⊩ᵛ∷⇔ʰ .proj₁ ⊩u .proj₂ σ₁≡σ₂
              v[σ₁]≡v[σ₂] = ⊩ᵛ∷⇔ʰ .proj₁ ⊩v .proj₂ σ₁≡σ₂
              ⊩t[σ₁] , ⊩t[σ₂] = wf-⊩≡∷ t[σ₁]≡t[σ₂]
              ⊩u[σ₁] , ⊩u[σ₂] = wf-⊩≡∷ u[σ₁]≡u[σ₂]
              ⊩v[σ₁] , ⊩v[σ₂] = wf-⊩≡∷ v[σ₁]≡v[σ₂]
          in trans-⊩≡∷
            (⊩maxᵘ-assoc∷Level ⊩t[σ₁] ⊩u[σ₁] ⊩v[σ₁])
            (⊩maxᵘ≡maxᵘ∷Level t[σ₁]≡t[σ₂] (⊩maxᵘ≡maxᵘ∷Level u[σ₁]≡u[σ₂] v[σ₁]≡v[σ₂]))
      )

opaque

  ⊩maxᵘ-comm∷Level :
    Γ ⊩⟨ l ⟩ t ∷ Level →
    Γ ⊩⟨ l′ ⟩ u ∷ Level →
    Γ ⊩⟨ l ⟩ t maxᵘ u ≡ u maxᵘ t ∷ Level
  ⊩maxᵘ-comm∷Level ⊩t ⊩u = ⊩≡∷Level⇔ .proj₂ $
    ⊩maxᵘ-comm (⊩∷Level⇔ .proj₁ ⊩t) (⊩∷Level⇔ .proj₁ ⊩u)

  maxᵘ-commᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ Level →
    Γ ⊩ᵛ⟨ l ⟩ t maxᵘ u ≡ u maxᵘ t ∷ Level
  maxᵘ-commᵛ ⊩t ⊩u =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( wf-⊩ᵛ∷ ⊩t
      , λ σ₁≡σ₂ →
          let t[σ₁]≡t[σ₂] = ⊩ᵛ∷⇔ʰ .proj₁ ⊩t .proj₂ σ₁≡σ₂
              u[σ₁]≡u[σ₂] = ⊩ᵛ∷⇔ʰ .proj₁ ⊩u .proj₂ σ₁≡σ₂
              ⊩t[σ₁] , ⊩t[σ₂] = wf-⊩≡∷ t[σ₁]≡t[σ₂]
              ⊩u[σ₁] , ⊩u[σ₂] = wf-⊩≡∷ u[σ₁]≡u[σ₂]
          in trans-⊩≡∷
            (⊩maxᵘ≡maxᵘ∷Level t[σ₁]≡t[σ₂] u[σ₁]≡u[σ₂])
            (⊩maxᵘ-comm∷Level ⊩t[σ₂] ⊩u[σ₂])
      )

------------------------------------------------------------------------
-- Level reflection

opaque
  unfolding ↑ᵘ′_

  -- Level reflection sends zeroᵘ to 0ᵘ.

  ↑ᵘ-zeroᵘ : ([0] : Γ ⊩Level zeroᵘ ∷Level) → ↑ᵘ [0] PE.≡ 0ᵘ
  ↑ᵘ-zeroᵘ [0] = PE.cong 0ᵘ+_ (↑ᵘ′-zeroᵘ [0])

  -- zeroᵘ is the smallest level.

  zeroᵘ-≤ᵘ : {[0] : Γ ⊩Level zeroᵘ ∷Level} → ↑ᵘ [0] ≤ᵘ l
  zeroᵘ-≤ᵘ {l} {[0]} = PE.subst (_≤ᵘ l) (PE.sym (↑ᵘ-zeroᵘ [0])) 0≤ᵘ

opaque
  unfolding ↑ᵘ′_

  -- Level reflection sends sucᵘ to 1+.

  ↑ᵘ′-sucᵘ
    : ∀ {t} ([t] : Γ ⊩Level t ∷Level) ([t+1] : Γ ⊩Level sucᵘ t ∷Level)
    → ↑ᵘ′ [t+1] PE.≡ 1+ (↑ᵘ′ [t])
  ↑ᵘ′-sucᵘ [t] (Levelₜ _ t+1⇒ prop′) with whnfRed*Term t+1⇒ sucᵘₙ
  ↑ᵘ′-sucᵘ [t] [t+1]@(Levelₜ _ t+1⇒ (sucᵘᵣ [t]′)) | PE.refl
    = PE.cong 1+ (↑ᵘ′-irrelevance [t]′ [t])
  ↑ᵘ′-sucᵘ [t] (Levelₜ _ t+1⇒ (neLvl x₁)) | PE.refl = case nelevel x₁ of λ { (ne ()) }

  -- sucᵘ is inflationary.

  <′-sucᵘ
    : ∀ {t} ([t] : Γ ⊩Level t ∷Level) ([t+1] : Γ ⊩Level sucᵘ t ∷Level)
    → ↑ᵘ′ [t] <′ ↑ᵘ′ [t+1]
  <′-sucᵘ [t] [t+1] = PE.subst (↑ᵘ′ [t] <′_) (PE.sym (↑ᵘ′-sucᵘ [t] [t+1])) ≤′-refl

  <ᵘ-sucᵘ
    : ∀ {t} {[t] : Γ ⊩Level t ∷Level} {[t+1] : Γ ⊩Level sucᵘ t ∷Level}
    → ↑ᵘ [t] <ᵘ ↑ᵘ [t+1]
  <ᵘ-sucᵘ {[t]} {[t+1]} = <ᵘ-nat (<′-sucᵘ [t] [t+1])

-- t maxᵘ u is an upper bound of t and u.

opaque

  ≤ᵘ-maxᵘʳ :
    {⊩t : Γ ⊩Level t ∷Level} →
    {⊩u : Γ ⊩Level u ∷Level} →
    ↑ᵘ ⊩t ≤ᵘ ↑ᵘ ⊩maxᵘ ⊩t ⊩u
  ≤ᵘ-maxᵘʳ {⊩t} {⊩u} = PE.subst (↑ᵘ ⊩t ≤ᵘ_) (PE.sym $ ↑ᵘ-maxᵘ ⊩t ⊩u) ≤ᵘ⊔ᵘʳ

opaque

  ≤ᵘ-maxᵘˡ :
    {⊩t : Γ ⊩Level t ∷Level} →
    {⊩u : Γ ⊩Level u ∷Level} →
    ↑ᵘ ⊩u ≤ᵘ ↑ᵘ ⊩maxᵘ ⊩t ⊩u
  ≤ᵘ-maxᵘˡ {⊩t} {⊩u} = PE.subst (↑ᵘ ⊩u ≤ᵘ_) (PE.sym $ ↑ᵘ-maxᵘ ⊩t ⊩u) ≤ᵘ⊔ᵘˡ
