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
open import Definition.LogicalRelation.Properties R ⦃ eqrel ⦄
open import Definition.LogicalRelation.ShapeView R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Substitution R ⦃ eqrel ⦄

open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Tools.Empty
open import Tools.Function
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Relation

private variable
  Γ Δ                               : Con Term _
  A A₁ A₂ B t t₁ t₂ u u₁ u₂ v v₁ v₂ : Term _
  σ σ₁ σ₂                           : Subst _ _
  l l′ l″ l‴                        : Universe-level

------------------------------------------------------------------------
-- Characterisation lemmas

opaque

  -- A characterisation lemma for _⊩⟨_⟩ Level

  ⊩Level⇔ :
    Γ ⊩⟨ l ⟩ Level ⇔
    (Level-allowed × ⊢ Γ)
  ⊩Level⇔ =
      (λ ⊩Level →
        case Level-view ⊩Level of λ {
          (Levelᵣ Level⇒*Level) →
        let ⊢Level = redFirst* Level⇒*Level in
        inversion-Level-⊢ ⊢Level , wf ⊢Level })
    , (λ (ok , ⊢Γ) → Levelᵣ (id (Levelⱼ′ ok ⊢Γ)))

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
         let ok           = inversion-Level-⊢
                              (wf-⊢≡ (subset* Level≡A) .proj₂)
             Level⇒*Level = id (Levelⱼ′ ok (wfEq (subset* Level≡A)))
             ⊩Level       = Levelᵣ Level⇒*Level in
           ⊩Level
         , (redSubst* Level≡A ⊩Level) .proj₁
         , Level≡A)

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷ Level

  ⊩≡∷Level⇔ :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ Level ⇔
    (Level-allowed × Γ ⊩Level t ≡ u ∷Level)
  ⊩≡∷Level⇔ =
      (λ (⊩Level , t≡u) →
         case Level-view ⊩Level of λ {
           (Levelᵣ Level⇒*Level) →
         inversion-Level-⊢ (redFirst* Level⇒*Level) , t≡u })
    , (λ (ok , t≡u) →
          Levelᵣ
            (id $
             Levelⱼ′ ok $ wfTerm $ ⊢∷Level→⊢∷Level ok $
             escapeLevel (wf-Level-eq t≡u .proj₁))
         , t≡u)

opaque

  ⊩Level∷Level⇔ : Γ ⊩Level t ∷Level ⇔ Γ ⊩Level t ≡ t ∷Level
  ⊩Level∷Level⇔ = reflLevel , proj₁ ∘→ wf-Level-eq

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷ Level

  ⊩∷Level⇔ :
    Γ ⊩⟨ l ⟩ t ∷ Level ⇔
    (Level-allowed × Γ ⊩Level t ∷Level)
  ⊩∷Level⇔ {Γ} {l} {t} =
    Γ ⊩⟨ l ⟩ t ∷ Level                     ⇔⟨ ⊩∷⇔⊩≡∷ ⟩
    Γ ⊩⟨ l ⟩ t ≡ t ∷ Level                 ⇔⟨ ⊩≡∷Level⇔ ⟩
    Level-allowed × Γ ⊩Level t ≡ t ∷Level  ⇔˘⟨ id⇔ ×-cong-⇔ ⊩Level∷Level⇔ ⟩
    Level-allowed × Γ ⊩Level t ∷Level      □⇔

opaque

  -- A characterisation lemma for _⊩⟨_⟩ zeroᵘ ∷ Level

  ⊩zeroᵘ∷Level⇔ :
    Γ ⊩⟨ l ⟩ zeroᵘ ∷ Level ⇔
    (Level-allowed × ⊢ Γ)
  ⊩zeroᵘ∷Level⇔ {Γ} {l} =
    Γ ⊩⟨ l ⟩ zeroᵘ ∷ Level                 ⇔⟨ ⊩∷Level⇔ ⟩
    Level-allowed × Γ ⊩Level zeroᵘ ∷Level  ⇔⟨ (Σ-cong-⇔ λ ok →
                                               wfTerm ∘→ ⊢∷Level→⊢∷Level ok ∘→ escapeLevel ,
                                               ⊩zeroᵘ) ⟩
    Level-allowed × ⊢ Γ                    □⇔

opaque

  -- A characterisation lemma for _⊩⟨_⟩ zeroᵘ ≡ zeroᵘ ∷ Level

  ⊩zeroᵘ≡zeroᵘ∷Level⇔ :
    Γ ⊩⟨ l ⟩ zeroᵘ ≡ zeroᵘ ∷ Level ⇔
    (Level-allowed × ⊢ Γ)
  ⊩zeroᵘ≡zeroᵘ∷Level⇔ {Γ} {l} =
    Γ ⊩⟨ l ⟩ zeroᵘ ≡ zeroᵘ ∷ Level  ⇔˘⟨ ⊩∷⇔⊩≡∷ ⟩
    Γ ⊩⟨ l ⟩ zeroᵘ ∷ Level          ⇔⟨ ⊩zeroᵘ∷Level⇔ ⟩
    Level-allowed × ⊢ Γ             □⇔

opaque

  -- A characterisation lemma for _⊩⟨_⟩ sucᵘ _ ≡ sucᵘ _ ∷ Level

  ⊩sucᵘ≡sucᵘ∷Level :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ Level →
    Γ ⊩⟨ l ⟩ sucᵘ t ≡ sucᵘ u ∷ Level
  ⊩sucᵘ≡sucᵘ∷Level {Γ} {l} {t} {u} =
    Γ ⊩⟨ l ⟩ t ≡ u ∷ Level                           ⇔⟨ ⊩≡∷Level⇔ ⟩→
    Level-allowed × Γ ⊩Level t ≡ u ∷Level            →⟨ Σ.map idᶠ ⊩sucᵘ≡sucᵘ ⟩
    Level-allowed × Γ ⊩Level sucᵘ t ≡ sucᵘ u ∷Level  ⇔˘⟨ ⊩≡∷Level⇔ ⟩→
    Γ ⊩⟨ l ⟩ sucᵘ t ≡ sucᵘ u ∷ Level                 □

opaque

  -- A characterisation lemma for _⊩⟨_⟩ sucᵘ _ ∷ Level

  ⊩sucᵘ∷Level :
    Γ ⊩⟨ l ⟩ t ∷ Level →
    Γ ⊩⟨ l ⟩ sucᵘ t ∷ Level
  ⊩sucᵘ∷Level{Γ} {l} {t} =
    Γ ⊩⟨ l ⟩ t ∷ Level                ⇔⟨ ⊩∷⇔⊩≡∷ ⟩→
    Γ ⊩⟨ l ⟩ t ≡ t ∷ Level            →⟨ ⊩sucᵘ≡sucᵘ∷Level ⟩
    Γ ⊩⟨ l ⟩ sucᵘ t ≡ sucᵘ t ∷ Level  ⇔˘⟨ ⊩∷⇔⊩≡∷ ⟩→
    Γ ⊩⟨ l ⟩ sucᵘ t ∷ Level           □

------------------------------------------------------------------------
-- Some lemmas related to _⊩ᵛ⟨_⟩_∷Level or _⊩ᵛ⟨_⟩_≡_∷Level

opaque

  -- Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷Level implies Γ ⊩Level t ≡ u ∷Level (assuming
  -- that Γ is empty or Neutrals-included holds).

  ⊩ᵛ≡∷L→⊩≡∷L :
    ⦃ inc : Neutrals-included or-empty Γ ⦄ →
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷Level → Γ ⊩Level t ≡ u ∷Level
  ⊩ᵛ≡∷L→⊩≡∷L (term ok t≡u) =
    ⊩≡∷Level⇔ .proj₁ (R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩≡∷ t≡u) .proj₂
  ⊩ᵛ≡∷L→⊩≡∷L (literal! not-ok t-lit) =
    literal! not-ok t-lit

opaque

  -- Γ ⊩ᵛ⟨ l ⟩ t ∷Level implies Γ ⊩Level t ∷Level (assuming that Γ is
  -- empty or Neutrals-included holds).

  ⊩ᵛ∷L→⊩∷L :
    ⦃ inc : Neutrals-included or-empty Γ ⦄ →
    Γ ⊩ᵛ⟨ l ⟩ t ∷Level → Γ ⊩Level t ∷Level
  ⊩ᵛ∷L→⊩∷L {Γ} {l} {t} =
    Γ ⊩ᵛ⟨ l ⟩ t ∷Level      ⇔⟨ ⊩ᵛ∷L⇔⊩ᵛ≡∷L ⟩→
    Γ ⊩ᵛ⟨ l ⟩ t ≡ t ∷Level  →⟨ ⊩ᵛ≡∷L→⊩≡∷L ⟩
    Γ ⊩Level t ≡ t ∷Level   ⇔˘⟨ ⊩Level∷Level⇔ ⟩→
    Γ ⊩Level t ∷Level       □

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷Level.

  ⊩ᵛ≡∷L→⊩ˢ≡∷→⊩[]≡[]∷L :
    ⦃ inc : Neutrals-included or-empty Δ ⦄ →
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷Level →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩Level t [ σ₁ ] ≡ u [ σ₂ ] ∷Level
  ⊩ᵛ≡∷L→⊩ˢ≡∷→⊩[]≡[]∷L (term ok t≡u) σ₁≡σ₂ =
    ⊩≡∷Level⇔ .proj₁ (⊩ᵛ≡∷⇔ʰ .proj₁ t≡u .proj₂ σ₁≡σ₂) .proj₂
  ⊩ᵛ≡∷L→⊩ˢ≡∷→⊩[]≡[]∷L (literal! not-ok t-lit) _ =
    literal not-ok (Level-literal-[] t-lit) (Level-literal→[]≡[] t-lit)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷Level.

  ⊩ᵛ∷L→⊩ˢ∷→⊩[]∷L :
    ⦃ inc : Neutrals-included or-empty Δ ⦄ →
    Γ ⊩ᵛ⟨ l ⟩ t ∷Level →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩Level t [ σ ] ∷Level
  ⊩ᵛ∷L→⊩ˢ∷→⊩[]∷L ⊩t =
    ⊩Level∷Level⇔ .proj₂ ∘→
    ⊩ᵛ≡∷L→⊩ˢ≡∷→⊩[]≡[]∷L (refl-⊩ᵛ≡∷L ⊩t) ∘→
    refl-⊩ˢ≡∷

------------------------------------------------------------------------
-- Level

opaque

  -- Validity of Level, seen as a type former.

  Levelᵛ : Level-allowed → ⊩ᵛ Γ → Γ ⊩ᵛ⟨ l ⟩ Level
  Levelᵛ {Γ} {l} ok ⊩Γ =
    ⊩ᵛ⇔ʰ .proj₂
      ( ⊩Γ
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ          →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ⊢ Δ                       →⟨ Levelⱼ′ ok ⟩
          (Δ ⊢ Level)               →⟨ id ⟩
          Δ ⊢ Level ⇒* Level        ⇔˘⟨ ⊩Level≡⇔ ⟩→
          Δ ⊩⟨ l ⟩ Level ≡ Level    □
      )

-- The validity of Level seen as a term former is defined in
-- Definition.LogicalRelation.Substitution.Introductions.Universe
-- to avoid cyclic module dependencies.

------------------------------------------------------------------------
-- The constructors zeroᵘ and sucᵘ

opaque

  -- Reducibility of zeroᵘ.

  ⊩zeroᵘ∷Level :
    Level-allowed →
    ⊢ Γ →
    Γ ⊩⟨ 0ᵘ ⟩ zeroᵘ ∷ Level
  ⊩zeroᵘ∷Level = curry (⊩zeroᵘ∷Level⇔ .proj₂)

opaque

  -- Validity of zeroᵘ.

  zeroᵘᵛ′ :
    ⊩ᵛ Γ →
    Γ ⊩ᵛ⟨ 0ᵘ ⟩ zeroᵘ ∷Level
  zeroᵘᵛ′ {Γ} ⊩Γ =
    case Level-allowed? of λ where
      (yes ok) →
        term-⊩ᵛ∷L ok $
        ⊩ᵛ∷⇔ʰ .proj₂
          ( Levelᵛ ok ⊩Γ
          , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
              Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ                 →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
              ⊢ Δ                              →⟨ curry (⊩zeroᵘ≡zeroᵘ∷Level⇔ .proj₂) ok ⟩
              Δ ⊩⟨ 0ᵘ ⟩ zeroᵘ ≡ zeroᵘ ∷ Level  □
          )
      (no not-ok) →
        literal-⊩ᵛ∷L not-ok zeroᵘ

opaque

  -- Validity of zeroᵘ.

  zeroᵘᵛ :
    Level-allowed →
    ⊩ᵛ Γ →
    Γ ⊩ᵛ⟨ 0ᵘ ⟩ zeroᵘ ∷ Level
  zeroᵘᵛ ok ⊩Γ =
    ⊩ᵛ∷L⇔ ok .proj₁ (zeroᵘᵛ′ ⊩Γ)

opaque

  -- Validity of equality preservation for sucᵘ.

  sucᵘ-congᵛ′ :
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷Level →
    Γ ⊩ᵛ⟨ l ⟩ sucᵘ t ≡ sucᵘ u ∷Level
  sucᵘ-congᵛ′ (term ok t≡u) =
    term ok $
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( Levelᵛ ok (wf-⊩ᵛ $ wf-⊩ᵛ∷ $ wf-⊩ᵛ≡∷ t≡u .proj₁)
      , ⊩sucᵘ≡sucᵘ∷Level ∘→ R.⊩≡∷→ ∘→ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t≡u
      )
  sucᵘ-congᵛ′ (literal! not-ok t-lit) =
    literal! not-ok (sucᵘ t-lit)

opaque

  -- Validity of equality preservation for sucᵘ.

  sucᵘ-congᵛ :
    Level-allowed →
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ Level →
    Γ ⊩ᵛ⟨ l ⟩ sucᵘ t ≡ sucᵘ u ∷ Level
  sucᵘ-congᵛ ok = ⊩ᵛ≡∷L⇔ ok .proj₁ ∘→ sucᵘ-congᵛ′ ∘→ ⊩ᵛ≡∷L⇔ ok .proj₂

opaque

  -- Validity of sucᵘ.

  sucᵘᵛ′ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷Level →
    Γ ⊩ᵛ⟨ l ⟩ sucᵘ t ∷Level
  sucᵘᵛ′ = ⊩ᵛ∷L⇔⊩ᵛ≡∷L .proj₂ ∘→ sucᵘ-congᵛ′ ∘→ ⊩ᵛ∷L⇔⊩ᵛ≡∷L .proj₁

opaque

  -- Validity of sucᵘ.

  sucᵘᵛ :
    Level-allowed →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ l ⟩ sucᵘ t ∷ Level
  sucᵘᵛ ok ⊩t =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $ sucᵘ-congᵛ ok (refl-⊩ᵛ≡∷ ⊩t)

------------------------------------------------------------------------
-- The operator supᵘ

opaque

  -- Reducibility of equality preservation for supᵘ.

  ⊩supᵘ≡supᵘ∷Level :
    Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ Level →
    Γ ⊩⟨ l′ ⟩ u₁ ≡ u₂ ∷ Level →
    Γ ⊩⟨ l ⟩ t₁ supᵘ u₁ ≡ t₂ supᵘ u₂ ∷ Level
  ⊩supᵘ≡supᵘ∷Level t₁≡t₂ u₁≡u₂ =
    let ok , t₁≡t₂ = ⊩≡∷Level⇔ .proj₁ t₁≡t₂
        _  , u₁≡u₂ = ⊩≡∷Level⇔ .proj₁ u₁≡u₂
    in
    ⊩≡∷Level⇔ .proj₂ (ok , ⊩supᵘ≡supᵘ ok t₁≡t₂ u₁≡u₂)

opaque

  -- Validity of equality preservation for supᵘ.

  supᵘ-congᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ Level →
    Γ ⊩ᵛ⟨ l′ ⟩ u₁ ≡ u₂ ∷ Level →
    Γ ⊩ᵛ⟨ l ⟩ t₁ supᵘ u₁ ≡ t₂ supᵘ u₂ ∷ Level
  supᵘ-congᵛ t₁≡t₂ u₁≡u₂ =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁)
      , λ σ₁≡σ₂ → ⊩supᵘ≡supᵘ∷Level
          (R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t₁≡t₂ σ₁≡σ₂)
          (R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ u₁≡u₂ σ₁≡σ₂)
      )

opaque

  -- Validity of supᵘ.

  supᵘᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ Level →
    Γ ⊩ᵛ⟨ l ⟩ t supᵘ u ∷ Level
  supᵘᵛ ⊩t ⊩u = ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    supᵘ-congᵛ (⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁ ⊩t) (⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁ ⊩u)

opaque

  -- Validity for _supᵘₗ_.

  supᵘₗᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷Level →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷Level →
    Γ ⊩ᵛ⟨ l ⟩ t supᵘₗ u ∷Level
  supᵘₗᵛ ⊩t ⊩u =
    case ⊩ᵛ∷L⇔⊩ᵛ≡∷L .proj₁ ⊩t of λ where
      (term ok ⊩t) →
        PE.subst (_⊩ᵛ⟨_⟩_∷Level _ _) (PE.sym $ supᵘₗ≡supᵘ ok) $
        term-⊩ᵛ∷L ok $
        supᵘᵛ (⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ ⊩t) (⊩ᵛ∷L⇔ ok .proj₁ ⊩u)
      (literal not-ok t-lit _) →
        case ⊩ᵛ∷L⇔⊩ᵛ≡∷L .proj₁ ⊩u of λ where
          (literal _ u-lit _) →
            literal-⊩ᵛ∷L not-ok $
            Level-literal-supᵘₗ⇔ not-ok .proj₂ (t-lit , u-lit)
          (term ok _) →
            ⊥-elim (not-ok ok)

opaque

  -- Reducibility of supᵘ-zeroˡ.

  ⊩supᵘ-zeroˡ :
    Γ ⊩⟨ l ⟩ t ∷ Level →
    Γ ⊩⟨ l ⟩ zeroᵘ supᵘ t ≡ t ∷ Level
  ⊩supᵘ-zeroˡ ⊩t = ⊩∷-⇐* (redMany (supᵘ-zeroˡ (escape-⊩∷ ⊩t))) ⊩t

opaque

  -- Validity of supᵘ-zeroˡ.

  supᵘ-zeroˡᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ l ⟩ zeroᵘ supᵘ t ≡ t ∷ Level
  supᵘ-zeroˡᵛ ⊩t =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( wf-⊩ᵛ∷ ⊩t
      , λ σ₁≡σ₂ →
          let t[σ₁]≡t[σ₂] = ⊩ᵛ∷⇔ʰ .proj₁ ⊩t .proj₂ σ₁≡σ₂
          in trans-⊩≡∷ (⊩supᵘ-zeroˡ (wf-⊩≡∷ t[σ₁]≡t[σ₂] .proj₁)) t[σ₁]≡t[σ₂]
      )

opaque

  -- Reducibility of supᵘ-sucᵘ.

  ⊩supᵘ-sucᵘ :
    Γ ⊩⟨ l ⟩ t ∷ Level →
    Γ ⊩⟨ l′ ⟩ u ∷ Level →
    Γ ⊩⟨ l ⟩ sucᵘ t supᵘ sucᵘ u ≡ sucᵘ (t supᵘ u) ∷ Level
  ⊩supᵘ-sucᵘ ⊩t ⊩u = ⊩∷-⇐*
    (redMany (supᵘ-sucᵘ (escape-⊩∷ ⊩t) (escape-⊩∷ ⊩u)))
    (⊩sucᵘ∷Level $ ⊩∷⇔⊩≡∷ .proj₂ $
      ⊩supᵘ≡supᵘ∷Level (refl-⊩≡∷ ⊩t) (refl-⊩≡∷ ⊩u))

opaque

  -- Validity of supᵘ-sucᵘ.

  supᵘ-sucᵘᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ Level →
    Γ ⊩ᵛ⟨ l ⟩ sucᵘ t supᵘ sucᵘ u ≡ sucᵘ (t supᵘ u) ∷ Level
  supᵘ-sucᵘᵛ ⊩t ⊩u =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( wf-⊩ᵛ∷ ⊩t
      , λ σ₁≡σ₂ →
          let t[σ₁]≡t[σ₂] = ⊩ᵛ∷⇔ʰ .proj₁ ⊩t .proj₂ σ₁≡σ₂
              u[σ₁]≡u[σ₂] = ⊩ᵛ∷⇔ʰ .proj₁ ⊩u .proj₂ σ₁≡σ₂
              ⊩t[σ₁] , ⊩t[σ₂] = wf-⊩≡∷ t[σ₁]≡t[σ₂]
              ⊩u[σ₁] , ⊩u[σ₂] = wf-⊩≡∷ u[σ₁]≡u[σ₂]
          in trans-⊩≡∷
            (⊩supᵘ-sucᵘ ⊩t[σ₁] ⊩u[σ₁])
            (⊩sucᵘ≡sucᵘ∷Level $ ⊩supᵘ≡supᵘ∷Level t[σ₁]≡t[σ₂] u[σ₁]≡u[σ₂])
      )

opaque

  -- Reducibility of supᵘ-assoc.

  ⊩supᵘ-assoc∷Level :
    Γ ⊩⟨ l ⟩ t ∷ Level →
    Γ ⊩⟨ l′ ⟩ u ∷ Level →
    Γ ⊩⟨ l″ ⟩ v ∷ Level →
    Γ ⊩⟨ l ⟩ (t supᵘ u) supᵘ v ≡ t supᵘ (u supᵘ v) ∷ Level
  ⊩supᵘ-assoc∷Level ⊩t ⊩u ⊩v =
    let ok , ⊩t = ⊩∷Level⇔ .proj₁ ⊩t
        _  , ⊩u = ⊩∷Level⇔ .proj₁ ⊩u
        _  , ⊩v = ⊩∷Level⇔ .proj₁ ⊩v
    in
    ⊩≡∷Level⇔ .proj₂ (ok , ⊩supᵘ-assoc ok ⊩t ⊩u ⊩v)

opaque

  -- Validity of supᵘ-assoc.

  supᵘ-assocᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ Level →
    Γ ⊩ᵛ⟨ l″ ⟩ v ∷ Level →
    Γ ⊩ᵛ⟨ l ⟩ (t supᵘ u) supᵘ v ≡ t supᵘ (u supᵘ v) ∷ Level
  supᵘ-assocᵛ ⊩t ⊩u ⊩v =
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
            (⊩supᵘ-assoc∷Level ⊩t[σ₁] ⊩u[σ₁] ⊩v[σ₁])
            (⊩supᵘ≡supᵘ∷Level t[σ₁]≡t[σ₂] (⊩supᵘ≡supᵘ∷Level u[σ₁]≡u[σ₂] v[σ₁]≡v[σ₂]))
      )

opaque

  -- Reducibility of supᵘ-comm.

  ⊩supᵘ-comm∷Level :
    Γ ⊩⟨ l ⟩ t ∷ Level →
    Γ ⊩⟨ l′ ⟩ u ∷ Level →
    Γ ⊩⟨ l ⟩ t supᵘ u ≡ u supᵘ t ∷ Level
  ⊩supᵘ-comm∷Level ⊩t ⊩u =
    let ok , ⊩t = ⊩∷Level⇔ .proj₁ ⊩t
        _  , ⊩u = ⊩∷Level⇔ .proj₁ ⊩u
    in
    ⊩≡∷Level⇔ .proj₂ (ok , ⊩supᵘ-comm ok ⊩t ⊩u)

opaque

  -- Validity of supᵘ-comm.

  supᵘ-commᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ Level →
    Γ ⊩ᵛ⟨ l ⟩ t supᵘ u ≡ u supᵘ t ∷ Level
  supᵘ-commᵛ ⊩t ⊩u =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( wf-⊩ᵛ∷ ⊩t
      , λ σ₁≡σ₂ →
          let t[σ₁]≡t[σ₂] = ⊩ᵛ∷⇔ʰ .proj₁ ⊩t .proj₂ σ₁≡σ₂
              u[σ₁]≡u[σ₂] = ⊩ᵛ∷⇔ʰ .proj₁ ⊩u .proj₂ σ₁≡σ₂
              ⊩t[σ₁] , ⊩t[σ₂] = wf-⊩≡∷ t[σ₁]≡t[σ₂]
              ⊩u[σ₁] , ⊩u[σ₂] = wf-⊩≡∷ u[σ₁]≡u[σ₂]
          in trans-⊩≡∷
            (⊩supᵘ≡supᵘ∷Level t[σ₁]≡t[σ₂] u[σ₁]≡u[σ₂])
            (⊩supᵘ-comm∷Level ⊩t[σ₂] ⊩u[σ₂])
      )

opaque

  -- Reducibility of supᵘ-idem.

  ⊩supᵘ-idem∷Level :
    Γ ⊩⟨ l ⟩ t ∷ Level →
    Γ ⊩⟨ l ⟩ t supᵘ t ≡ t ∷ Level
  ⊩supᵘ-idem∷Level ⊩t =
    let ok , ⊩t = ⊩∷Level⇔ .proj₁ ⊩t in
    ⊩≡∷Level⇔ .proj₂ (ok , ⊩supᵘ-idem ok ⊩t)

opaque

  -- Validity of supᵘ-idem.

  supᵘ-idemᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ l ⟩ t supᵘ t ≡ t ∷ Level
  supᵘ-idemᵛ ⊩t =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( wf-⊩ᵛ∷ ⊩t
      , λ σ₁≡σ₂ →
          let t[σ₁]≡t[σ₂] = ⊩ᵛ∷⇔ʰ .proj₁ ⊩t .proj₂ σ₁≡σ₂
              ⊩t[σ₁] , ⊩t[σ₂] = wf-⊩≡∷ t[σ₁]≡t[σ₂]
          in trans-⊩≡∷ (⊩supᵘ-idem∷Level ⊩t[σ₁]) t[σ₁]≡t[σ₂]
      )

opaque

  -- Reducibility of supᵘ-sub.

  ⊩supᵘ-sub∷Level :
    Γ ⊩⟨ l ⟩ t ∷ Level →
    Γ ⊩⟨ l ⟩ t supᵘ sucᵘ t ≡ sucᵘ t ∷ Level
  ⊩supᵘ-sub∷Level ⊩t =
    let ok , ⊩t = ⊩∷Level⇔ .proj₁ ⊩t in
    ⊩≡∷Level⇔ .proj₂ (ok , ⊩supᵘ-sub ok ⊩t)

opaque

  -- Validity of supᵘ-sub.

  supᵘ-subᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ l ⟩ t supᵘ sucᵘ t ≡ sucᵘ t ∷ Level
  supᵘ-subᵛ ⊩t =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( wf-⊩ᵛ∷ ⊩t
      , λ σ₁≡σ₂ →
          let t[σ₁]≡t[σ₂] = ⊩ᵛ∷⇔ʰ .proj₁ ⊩t .proj₂ σ₁≡σ₂
              ⊩t[σ₁] , ⊩t[σ₂] = wf-⊩≡∷ t[σ₁]≡t[σ₂]
          in trans-⊩≡∷ (⊩supᵘ-sub∷Level ⊩t[σ₁]) (⊩sucᵘ≡sucᵘ∷Level t[σ₁]≡t[σ₂])
      )
