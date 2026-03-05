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
open import Definition.Typed.Substitution R
open import Definition.Typed.Weakening.Definition R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Allowed-literal R
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sup R

open import Tools.Empty
open import Tools.Function
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Relation

private variable
  ∇                                 : DCon _ _
  Δ Η                               : Con _ _
  Γ                                 : Cons _ _
  A A₁ A₂ B t t₁ t₂ u u₁ u₂ v v₁ v₂ : Term _
  l l₁ l₂                           : Lvl _
  σ σ₁ σ₂                           : Subst _ _
  ℓ ℓ′ ℓ″ ℓ‴                        : Universe-level

------------------------------------------------------------------------
-- Characterisation lemmas

opaque

  -- A characterisation lemma for _⊩⟨_⟩ Level

  ⊩Level⇔ :
    Γ ⊩⟨ ℓ ⟩ Level ⇔
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

  ⊩Level≡⇔ : Γ ⊩⟨ ℓ ⟩ Level ≡ A ⇔ Γ ⊩Level Level ≡ A
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
    Γ ⊩⟨ ℓ ⟩ t ≡ u ∷ Level ⇔
    (Level-allowed × Γ ⊩Level level t ≡ level u ∷Level)
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

  ⊩Level∷Level⇔ : Γ ⊩Level l ∷Level ⇔ Γ ⊩Level l ≡ l ∷Level
  ⊩Level∷Level⇔ = reflLevel , proj₁ ∘→ wf-Level-eq

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷ Level

  ⊩∷Level⇔ :
    Γ ⊩⟨ ℓ ⟩ t ∷ Level ⇔
    (Level-allowed × Γ ⊩Level level t ∷Level)
  ⊩∷Level⇔ {Γ} {ℓ} {t} =
    Γ ⊩⟨ ℓ ⟩ t ∷ Level                                 ⇔⟨ ⊩∷⇔⊩≡∷ ⟩
    Γ ⊩⟨ ℓ ⟩ t ≡ t ∷ Level                             ⇔⟨ ⊩≡∷Level⇔ ⟩
    Level-allowed × Γ ⊩Level level t ≡ level t ∷Level  ⇔˘⟨ id⇔ ×-cong-⇔ ⊩Level∷Level⇔ ⟩
    Level-allowed × Γ ⊩Level level t ∷Level            □⇔

opaque

  -- A characterisation lemma for _⊩⟨_⟩ zeroᵘ ∷ Level

  ⊩zeroᵘ∷Level⇔ :
    Γ ⊩⟨ ℓ ⟩ zeroᵘ ∷ Level ⇔
    (Level-allowed × ⊢ Γ)
  ⊩zeroᵘ∷Level⇔ {Γ} {ℓ} =
    Γ ⊩⟨ ℓ ⟩ zeroᵘ ∷ Level                  ⇔⟨ ⊩∷Level⇔ ⟩
    Level-allowed × Γ ⊩Level zeroᵘₗ ∷Level  ⇔⟨ (Σ-cong-⇔ λ ok →
                                                wfTerm ∘→ ⊢∷Level→⊢∷Level ok ∘→ escapeLevel ,
                                                ⊩zeroᵘ) ⟩
    Level-allowed × ⊢ Γ                     □⇔

opaque

  -- A characterisation lemma for _⊩⟨_⟩ zeroᵘ ≡ zeroᵘ ∷ Level

  ⊩zeroᵘ≡zeroᵘ∷Level⇔ :
    Γ ⊩⟨ ℓ ⟩ zeroᵘ ≡ zeroᵘ ∷ Level ⇔
    (Level-allowed × ⊢ Γ)
  ⊩zeroᵘ≡zeroᵘ∷Level⇔ {Γ} {ℓ} =
    Γ ⊩⟨ ℓ ⟩ zeroᵘ ≡ zeroᵘ ∷ Level  ⇔˘⟨ ⊩∷⇔⊩≡∷ ⟩
    Γ ⊩⟨ ℓ ⟩ zeroᵘ ∷ Level          ⇔⟨ ⊩zeroᵘ∷Level⇔ ⟩
    Level-allowed × ⊢ Γ             □⇔

opaque

  -- A characterisation lemma for _⊩⟨_⟩ sucᵘ _ ≡ sucᵘ _ ∷ Level

  ⊩sucᵘ≡sucᵘ∷Level :
    Γ ⊩⟨ ℓ ⟩ t ≡ u ∷ Level →
    Γ ⊩⟨ ℓ ⟩ sucᵘ t ≡ sucᵘ u ∷ Level
  ⊩sucᵘ≡sucᵘ∷Level {Γ} {ℓ} {t} {u} =
    Γ ⊩⟨ ℓ ⟩ t ≡ u ∷ Level                                           ⇔⟨ ⊩≡∷Level⇔ ⟩→
    Level-allowed × Γ ⊩Level level t ≡ level  u ∷Level               →⟨ Σ.map idᶠ ⊩1ᵘ+≡1ᵘ+ ⟩
    Level-allowed × Γ ⊩Level level (sucᵘ t) ≡ level (sucᵘ u) ∷Level  ⇔˘⟨ ⊩≡∷Level⇔ ⟩→
    Γ ⊩⟨ ℓ ⟩ sucᵘ t ≡ sucᵘ u ∷ Level                                 □

opaque

  -- A characterisation lemma for _⊩⟨_⟩ sucᵘ _ ∷ Level

  ⊩sucᵘ∷Level :
    Γ ⊩⟨ ℓ ⟩ t ∷ Level →
    Γ ⊩⟨ ℓ ⟩ sucᵘ t ∷ Level
  ⊩sucᵘ∷Level{Γ} {ℓ} {t} =
    Γ ⊩⟨ ℓ ⟩ t ∷ Level                ⇔⟨ ⊩∷⇔⊩≡∷ ⟩→
    Γ ⊩⟨ ℓ ⟩ t ≡ t ∷ Level            →⟨ ⊩sucᵘ≡sucᵘ∷Level ⟩
    Γ ⊩⟨ ℓ ⟩ sucᵘ t ≡ sucᵘ t ∷ Level  ⇔˘⟨ ⊩∷⇔⊩≡∷ ⟩→
    Γ ⊩⟨ ℓ ⟩ sucᵘ t ∷ Level           □

------------------------------------------------------------------------
-- Some lemmas related to _⊩ᵛ⟨_⟩_∷Level or _⊩ᵛ⟨_⟩_≡_∷Level

opaque

  -- Γ ⊩ᵛ⟨ l ⟩ l₁ ≡ l₂ ∷Level implies Γ ⊩Level l₁ ≡ l₂ ∷Level
  -- (assuming that the variable context is empty or Var-included
  -- holds).

  ⊩ᵛ≡∷L→⊩≡∷L :
    ⦃ inc : Var-included or-empty (Γ .vars) ⦄ →
    Γ ⊩ᵛ⟨ ℓ ⟩ l₁ ≡ l₂ ∷Level → Γ ⊩Level l₁ ≡ l₂ ∷Level
  ⊩ᵛ≡∷L→⊩≡∷L (term ok t≡u) =
    ⊩≡∷Level⇔ .proj₁ (R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩≡∷ t≡u) .proj₂
  ⊩ᵛ≡∷L→⊩≡∷L (literal! ok ⊩Γ) =
    literal! ok (escape-⊩ᵛ′ ⊩Γ)

opaque

  -- Γ ⊩ᵛ⟨ l ⟩ l ∷Level implies Γ ⊩Level l ∷Level (assuming that the
  -- variable context is empty or Var-included holds).

  ⊩ᵛ∷L→⊩∷L :
    ⦃ inc : Var-included or-empty (Γ .vars) ⦄ →
    Γ ⊩ᵛ⟨ ℓ ⟩ l ∷Level → Γ ⊩Level l ∷Level
  ⊩ᵛ∷L→⊩∷L {Γ} {ℓ} {l} =
    Γ ⊩ᵛ⟨ ℓ ⟩ l ∷Level      ⇔⟨ ⊩ᵛ∷L⇔⊩ᵛ≡∷L ⟩→
    Γ ⊩ᵛ⟨ ℓ ⟩ l ≡ l ∷Level  →⟨ ⊩ᵛ≡∷L→⊩≡∷L ⟩
    Γ ⊩Level l ≡ l ∷Level   ⇔˘⟨ ⊩Level∷Level⇔ ⟩→
    Γ ⊩Level l ∷Level       □

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷Level.

  ⊩ᵛ≡∷L→⊩ˢ≡∷→⊩[]≡[]∷L :
    ⦃ inc : Var-included or-empty Η ⦄ →
    ∇ » Δ ⊩ᵛ⟨ ℓ ⟩ l₁ ≡ l₂ ∷Level →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ⊩Level l₁ [ σ₁ ] ≡ l₂ [ σ₂ ] ∷Level
  ⊩ᵛ≡∷L→⊩ˢ≡∷→⊩[]≡[]∷L (term ok t₁≡t₂) σ₁≡σ₂ =
    ⊩≡∷Level⇔ .proj₁ (⊩ᵛ≡∷⇔ʰ .proj₁ t₁≡t₂ .proj₂ id⊇ σ₁≡σ₂) .proj₂
  ⊩ᵛ≡∷L→⊩ˢ≡∷→⊩[]≡[]∷L (literal! ok _) σ₁≡σ₂ =
    literal (Allowed-literal-[] ok) (escape-⊩ˢ≡∷ σ₁≡σ₂ .proj₁)
      (Level-literal→[]≡[] (Allowed-literal→Level-literal ok))

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷Level.

  ⊩ᵛ∷L→⊩ˢ∷→⊩[]∷L :
    ⦃ inc : Var-included or-empty Η ⦄ →
    ∇ » Δ ⊩ᵛ⟨ ℓ ⟩ l ∷Level →
    ∇ » Η ⊩ˢ σ ∷ Δ →
    ∇ » Η ⊩Level l [ σ ] ∷Level
  ⊩ᵛ∷L→⊩ˢ∷→⊩[]∷L ⊩l =
    ⊩Level∷Level⇔ .proj₂ ∘→
    ⊩ᵛ≡∷L→⊩ˢ≡∷→⊩[]≡[]∷L (refl-⊩ᵛ≡∷L ⊩l) ∘→
    refl-⊩ˢ≡∷

------------------------------------------------------------------------
-- Level

opaque

  -- Validity of Level, seen as a type former.

  Levelᵛ : Level-allowed → ⊩ᵛ Γ → Γ ⊩ᵛ⟨ ℓ ⟩ Level
  Levelᵛ {Γ} {ℓ} ok ⊩Γ =
    ⊩ᵛ⇔ʰ .proj₂
      ( ⊩Γ
      , λ {_} {∇′ = ∇} _ {_} {Η = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          ∇ » Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ .vars    →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ∇ »⊢ Δ                        →⟨ Levelⱼ′ ok ⟩
          (∇ » Δ ⊢ Level)               →⟨ id ⟩
          ∇ » Δ ⊢ Level ⇒* Level        ⇔˘⟨ ⊩Level≡⇔ ⟩→
          ∇ » Δ ⊩⟨ ℓ ⟩ Level ≡ Level    □
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

  -- Validity of zeroᵘₗ.

  zeroᵘᵛ′ :
    ⊩ᵛ Γ →
    Γ ⊩ᵛ⟨ 0ᵘ ⟩ zeroᵘₗ ∷Level
  zeroᵘᵛ′ {Γ} ⊩Γ =
    case Level-allowed? of λ where
      (yes ok) →
        term-⊩ᵛ∷L ok $
        ⊩ᵛ∷⇔ʰ .proj₂
          ( Levelᵛ ok ⊩Γ
          , λ {_} {∇′ = ∇} _ {_} {Η = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
              ∇ » Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ .vars           →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
              ∇ »⊢ Δ                               →⟨ curry (⊩zeroᵘ≡zeroᵘ∷Level⇔ .proj₂) ok ⟩
              ∇ » Δ ⊩⟨ 0ᵘ ⟩ zeroᵘ ≡ zeroᵘ ∷ Level  □
          )
      (no not-ok) →
        literal-⊩ᵛ∷L (Allowed-literal-level-⇔ .proj₂ (zeroᵘ , not-ok))
          ⊩Γ

opaque

  -- Validity of zeroᵘ.

  zeroᵘᵛ :
    Level-allowed →
    ⊩ᵛ Γ →
    Γ ⊩ᵛ⟨ 0ᵘ ⟩ zeroᵘ ∷ Level
  zeroᵘᵛ ok ⊩Γ =
    ⊩ᵛ∷L⇔ ok .proj₁ (zeroᵘᵛ′ ⊩Γ)

opaque

  -- Validity of equality preservation for 1ᵘ+.

  1ᵘ+-congᵛ :
    Γ ⊩ᵛ⟨ ℓ ⟩ l₁ ≡ l₂ ∷Level →
    Γ ⊩ᵛ⟨ ℓ ⟩ 1ᵘ+ l₁ ≡ 1ᵘ+ l₂ ∷Level
  1ᵘ+-congᵛ (term ok t₁≡t₂) =
    term ok $
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( Levelᵛ ok (wf-⊩ᵛ $ wf-⊩ᵛ∷ $ wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁)
      , λ ∇′⊇∇ →
          ⊩sucᵘ≡sucᵘ∷Level ∘→ R.⊩≡∷→ ∘→
          ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ∇′⊇∇ t₁≡t₂)
      )
  1ᵘ+-congᵛ (literal! ok ⊩Γ) =
    literal! (Allowed-literal-1ᵘ+-⇔ .proj₂ ok) ⊩Γ

opaque

  -- Validity of equality preservation for sucᵘ.

  sucᵘ-congᵛ :
    Level-allowed →
    Γ ⊩ᵛ⟨ ℓ ⟩ t ≡ u ∷ Level →
    Γ ⊩ᵛ⟨ ℓ ⟩ sucᵘ t ≡ sucᵘ u ∷ Level
  sucᵘ-congᵛ ok = ⊩ᵛ≡∷L⇔ ok .proj₁ ∘→ 1ᵘ+-congᵛ ∘→ ⊩ᵛ≡∷L⇔ ok .proj₂

opaque

  -- Validity of 1ᵘ+.

  1ᵘ+ᵛ :
    Γ ⊩ᵛ⟨ ℓ ⟩ l ∷Level →
    Γ ⊩ᵛ⟨ ℓ ⟩ 1ᵘ+ l ∷Level
  1ᵘ+ᵛ = ⊩ᵛ∷L⇔⊩ᵛ≡∷L .proj₂ ∘→ 1ᵘ+-congᵛ ∘→ ⊩ᵛ∷L⇔⊩ᵛ≡∷L .proj₁

opaque

  -- Validity of sucᵘ.

  sucᵘᵛ :
    Level-allowed →
    Γ ⊩ᵛ⟨ ℓ ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ ℓ ⟩ sucᵘ t ∷ Level
  sucᵘᵛ ok ⊩t =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $ sucᵘ-congᵛ ok (refl-⊩ᵛ≡∷ ⊩t)

------------------------------------------------------------------------
-- The operator supᵘ

opaque

  -- Reducibility of equality preservation for supᵘ.

  ⊩supᵘ≡supᵘ∷Level :
    Γ ⊩⟨ ℓ ⟩ t₁ ≡ t₂ ∷ Level →
    Γ ⊩⟨ ℓ′ ⟩ u₁ ≡ u₂ ∷ Level →
    Γ ⊩⟨ ℓ ⟩ t₁ supᵘ u₁ ≡ t₂ supᵘ u₂ ∷ Level
  ⊩supᵘ≡supᵘ∷Level t₁≡t₂ u₁≡u₂ =
    let ok , t₁≡t₂ = ⊩≡∷Level⇔ .proj₁ t₁≡t₂
        _  , u₁≡u₂ = ⊩≡∷Level⇔ .proj₁ u₁≡u₂
    in
    ⊩≡∷Level⇔ .proj₂ (ok , ⊩supᵘ≡supᵘ ok t₁≡t₂ u₁≡u₂)

opaque

  -- Validity of equality preservation for supᵘ.

  supᵘ-congᵛ :
    Γ ⊩ᵛ⟨ ℓ ⟩ t₁ ≡ t₂ ∷ Level →
    Γ ⊩ᵛ⟨ ℓ′ ⟩ u₁ ≡ u₂ ∷ Level →
    Γ ⊩ᵛ⟨ ℓ ⟩ t₁ supᵘ u₁ ≡ t₂ supᵘ u₂ ∷ Level
  supᵘ-congᵛ t₁≡t₂ u₁≡u₂ =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁)
      , λ ∇′⊇∇ σ₁≡σ₂ → ⊩supᵘ≡supᵘ∷Level
          (R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ∇′⊇∇ t₁≡t₂) σ₁≡σ₂)
          (R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ∇′⊇∇ u₁≡u₂) σ₁≡σ₂)
      )

opaque

  -- Validity of supᵘ.

  supᵘᵛ :
    Γ ⊩ᵛ⟨ ℓ ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ ℓ′ ⟩ u ∷ Level →
    Γ ⊩ᵛ⟨ ℓ ⟩ t supᵘ u ∷ Level
  supᵘᵛ ⊩t ⊩u = ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    supᵘ-congᵛ (⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁ ⊩t) (⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁ ⊩u)

opaque
  unfolding _supᵘₗ_

  -- Validity for _supᵘₗ_.

  supᵘₗᵛ :
    Γ ⊩ᵛ⟨ ℓ ⟩ l₁ ∷Level →
    Γ ⊩ᵛ⟨ ℓ′ ⟩ l₂ ∷Level →
    Γ ⊩ᵛ⟨ ℓ ⟩ l₁ supᵘₗ l₂ ∷Level
  supᵘₗᵛ ⊩l₁ ⊩l₂
    with ⊩ᵛ∷L⇔⊩ᵛ≡∷L .proj₁ ⊩l₁ | ⊩ᵛ∷L⇔⊩ᵛ≡∷L .proj₁ ⊩l₂
  … | term ok ⊩l₁ | term _ ⊩l₂ =
    PE.subst (_⊩ᵛ⟨_⟩_∷Level _ _) (PE.sym $ supᵘₗ≡supᵘ ok) $
    term-⊩ᵛ∷L ok $
    supᵘᵛ (⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ ⊩l₁) (⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ ⊩l₂)
  … | term ok₁ _ | literal ok₂ ⊩Γ _ =
    case Allowed-literal→Infinite ok₁ ok₂ of λ {
      ωᵘ+ →
    literal-⊩ᵛ∷L (Allowed-literal-ωᵘ+-→-Allowed-literal-ωᵘ+ ok₂)
      ⊩Γ }
  … | literal ok₁ ⊩Γ _ | term ok₂ _ =
    case Allowed-literal→Infinite ok₂ ok₁ of λ {
      ωᵘ+ →
    literal-⊩ᵛ∷L (Allowed-literal-ωᵘ+-→-Allowed-literal-ωᵘ+ ok₁) ⊩Γ }
  … | literal ok₁ ⊩Γ _ | literal ok₂ _ _ =
    literal-⊩ᵛ∷L (Allowed-literal-supᵘₗ ok₁ ok₂) ⊩Γ

opaque

  -- Reducibility of supᵘ-zeroˡ.

  ⊩supᵘ-zeroˡ :
    Γ ⊩⟨ ℓ ⟩ t ∷ Level →
    Γ ⊩⟨ ℓ ⟩ zeroᵘ supᵘ t ≡ t ∷ Level
  ⊩supᵘ-zeroˡ ⊩t = ⊩∷-⇐* (redMany (supᵘ-zeroˡ (escape-⊩∷ ⊩t))) ⊩t

opaque

  -- Validity of supᵘ-zeroˡ.

  supᵘ-zeroˡᵛ :
    Γ ⊩ᵛ⟨ ℓ ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ ℓ ⟩ zeroᵘ supᵘ t ≡ t ∷ Level
  supᵘ-zeroˡᵛ ⊩t =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( wf-⊩ᵛ∷ ⊩t
      , λ ∇′⊇∇ σ₁≡σ₂ →
          let t[σ₁]≡t[σ₂] = ⊩ᵛ∷⇔ʰ .proj₁ ⊩t .proj₂ ∇′⊇∇ σ₁≡σ₂ in
          trans-⊩≡∷ (⊩supᵘ-zeroˡ (wf-⊩≡∷ t[σ₁]≡t[σ₂] .proj₁))
            t[σ₁]≡t[σ₂]
      )

opaque

  -- Reducibility of supᵘ-sucᵘ.

  ⊩supᵘ-sucᵘ :
    Γ ⊩⟨ ℓ ⟩ t ∷ Level →
    Γ ⊩⟨ ℓ′ ⟩ u ∷ Level →
    Γ ⊩⟨ ℓ ⟩ sucᵘ t supᵘ sucᵘ u ≡ sucᵘ (t supᵘ u) ∷ Level
  ⊩supᵘ-sucᵘ ⊩t ⊩u =
    let ok , ⊩t = ⊩∷Level⇔ .proj₁ ⊩t
        _  , ⊩u = ⊩∷Level⇔ .proj₁ ⊩u
    in
    ⊩≡∷Level⇔ .proj₂ (ok , ⊩sucᵘ-supᵘ-sucᵘ≡sucᵘ-supᵘ ok ⊩t ⊩u)

opaque

  -- Validity of supᵘ-sucᵘ.

  supᵘ-sucᵘᵛ :
    Γ ⊩ᵛ⟨ ℓ ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ ℓ′ ⟩ u ∷ Level →
    Γ ⊩ᵛ⟨ ℓ ⟩ sucᵘ t supᵘ sucᵘ u ≡ sucᵘ (t supᵘ u) ∷ Level
  supᵘ-sucᵘᵛ ⊩t ⊩u =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( wf-⊩ᵛ∷ ⊩t
      , λ ∇′⊇∇ σ₁≡σ₂ →
          let t[σ₁]≡t[σ₂] = ⊩ᵛ∷⇔ʰ .proj₁ ⊩t .proj₂ ∇′⊇∇ σ₁≡σ₂
              u[σ₁]≡u[σ₂] = ⊩ᵛ∷⇔ʰ .proj₁ ⊩u .proj₂ ∇′⊇∇ σ₁≡σ₂
              ⊩t[σ₁] , ⊩t[σ₂] = wf-⊩≡∷ t[σ₁]≡t[σ₂]
              ⊩u[σ₁] , ⊩u[σ₂] = wf-⊩≡∷ u[σ₁]≡u[σ₂]
          in trans-⊩≡∷
            (⊩supᵘ-sucᵘ ⊩t[σ₁] ⊩u[σ₁])
            (⊩sucᵘ≡sucᵘ∷Level $ ⊩supᵘ≡supᵘ∷Level t[σ₁]≡t[σ₂] u[σ₁]≡u[σ₂])
      )

opaque

  -- Reducibility of supᵘ-assoc.

  ⊩supᵘ-assoc∷Level :
    Γ ⊩⟨ ℓ ⟩ t ∷ Level →
    Γ ⊩⟨ ℓ′ ⟩ u ∷ Level →
    Γ ⊩⟨ ℓ″ ⟩ v ∷ Level →
    Γ ⊩⟨ ℓ ⟩ (t supᵘ u) supᵘ v ≡ t supᵘ (u supᵘ v) ∷ Level
  ⊩supᵘ-assoc∷Level ⊩t ⊩u ⊩v =
    let ok , ⊩t = ⊩∷Level⇔ .proj₁ ⊩t
        _  , ⊩u = ⊩∷Level⇔ .proj₁ ⊩u
        _  , ⊩v = ⊩∷Level⇔ .proj₁ ⊩v
    in
    ⊩≡∷Level⇔ .proj₂ (ok , ⊩supᵘ-assoc ok ⊩t ⊩u ⊩v)

opaque

  -- Validity of supᵘ-assoc.

  supᵘ-assocᵛ :
    Γ ⊩ᵛ⟨ ℓ ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ ℓ′ ⟩ u ∷ Level →
    Γ ⊩ᵛ⟨ ℓ″ ⟩ v ∷ Level →
    Γ ⊩ᵛ⟨ ℓ ⟩ (t supᵘ u) supᵘ v ≡ t supᵘ (u supᵘ v) ∷ Level
  supᵘ-assocᵛ ⊩t ⊩u ⊩v =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( wf-⊩ᵛ∷ ⊩t
      , λ ∇′⊇∇ σ₁≡σ₂ →
          let t[σ₁]≡t[σ₂] = ⊩ᵛ∷⇔ʰ .proj₁ ⊩t .proj₂ ∇′⊇∇ σ₁≡σ₂
              u[σ₁]≡u[σ₂] = ⊩ᵛ∷⇔ʰ .proj₁ ⊩u .proj₂ ∇′⊇∇ σ₁≡σ₂
              v[σ₁]≡v[σ₂] = ⊩ᵛ∷⇔ʰ .proj₁ ⊩v .proj₂ ∇′⊇∇ σ₁≡σ₂
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
    Γ ⊩⟨ ℓ ⟩ t ∷ Level →
    Γ ⊩⟨ ℓ′ ⟩ u ∷ Level →
    Γ ⊩⟨ ℓ ⟩ t supᵘ u ≡ u supᵘ t ∷ Level
  ⊩supᵘ-comm∷Level ⊩t ⊩u =
    let ok , ⊩t = ⊩∷Level⇔ .proj₁ ⊩t
        _  , ⊩u = ⊩∷Level⇔ .proj₁ ⊩u
    in
    ⊩≡∷Level⇔ .proj₂ (ok , ⊩supᵘ-comm ok ⊩t ⊩u)

opaque

  -- Validity of supᵘ-comm.

  supᵘ-commᵛ :
    Γ ⊩ᵛ⟨ ℓ ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ ℓ′ ⟩ u ∷ Level →
    Γ ⊩ᵛ⟨ ℓ ⟩ t supᵘ u ≡ u supᵘ t ∷ Level
  supᵘ-commᵛ ⊩t ⊩u =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( wf-⊩ᵛ∷ ⊩t
      , λ ∇′⊇∇ σ₁≡σ₂ →
          let t[σ₁]≡t[σ₂] = ⊩ᵛ∷⇔ʰ .proj₁ ⊩t .proj₂ ∇′⊇∇ σ₁≡σ₂
              u[σ₁]≡u[σ₂] = ⊩ᵛ∷⇔ʰ .proj₁ ⊩u .proj₂ ∇′⊇∇ σ₁≡σ₂
              ⊩t[σ₁] , ⊩t[σ₂] = wf-⊩≡∷ t[σ₁]≡t[σ₂]
              ⊩u[σ₁] , ⊩u[σ₂] = wf-⊩≡∷ u[σ₁]≡u[σ₂]
          in trans-⊩≡∷
            (⊩supᵘ≡supᵘ∷Level t[σ₁]≡t[σ₂] u[σ₁]≡u[σ₂])
            (⊩supᵘ-comm∷Level ⊩t[σ₂] ⊩u[σ₂])
      )

opaque

  -- Reducibility of supᵘ-idem.

  ⊩supᵘ-idem∷Level :
    Γ ⊩⟨ ℓ ⟩ t ∷ Level →
    Γ ⊩⟨ ℓ ⟩ t supᵘ t ≡ t ∷ Level
  ⊩supᵘ-idem∷Level ⊩t =
    let ok , ⊩t = ⊩∷Level⇔ .proj₁ ⊩t in
    ⊩≡∷Level⇔ .proj₂ (ok , ⊩supᵘ-idem ok ⊩t)

opaque

  -- Validity of supᵘ-idem.

  supᵘ-idemᵛ :
    Γ ⊩ᵛ⟨ ℓ ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ ℓ ⟩ t supᵘ t ≡ t ∷ Level
  supᵘ-idemᵛ ⊩t =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( wf-⊩ᵛ∷ ⊩t
      , λ ∇′⊇∇ σ₁≡σ₂ →
          let t[σ₁]≡t[σ₂] = ⊩ᵛ∷⇔ʰ .proj₁ ⊩t .proj₂ ∇′⊇∇ σ₁≡σ₂
              ⊩t[σ₁] , ⊩t[σ₂] = wf-⊩≡∷ t[σ₁]≡t[σ₂]
          in trans-⊩≡∷ (⊩supᵘ-idem∷Level ⊩t[σ₁]) t[σ₁]≡t[σ₂]
      )

opaque

  -- Reducibility of supᵘ-sub.

  ⊩supᵘ-sub∷Level :
    Γ ⊩⟨ ℓ ⟩ t ∷ Level →
    Γ ⊩⟨ ℓ ⟩ t supᵘ sucᵘ t ≡ sucᵘ t ∷ Level
  ⊩supᵘ-sub∷Level ⊩t =
    let ok , ⊩t = ⊩∷Level⇔ .proj₁ ⊩t in
    ⊩≡∷Level⇔ .proj₂ (ok , ⊩supᵘ-sub ok ⊩t)

opaque

  -- Validity of supᵘ-sub.

  supᵘ-subᵛ :
    Γ ⊩ᵛ⟨ ℓ ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ ℓ ⟩ t supᵘ sucᵘ t ≡ sucᵘ t ∷ Level
  supᵘ-subᵛ ⊩t =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( wf-⊩ᵛ∷ ⊩t
      , λ ∇′⊇∇ σ₁≡σ₂ →
          let t[σ₁]≡t[σ₂] = ⊩ᵛ∷⇔ʰ .proj₁ ⊩t .proj₂ ∇′⊇∇ σ₁≡σ₂
              ⊩t[σ₁] , ⊩t[σ₂] = wf-⊩≡∷ t[σ₁]≡t[σ₂]
          in trans-⊩≡∷ (⊩supᵘ-sub∷Level ⊩t[σ₁]) (⊩sucᵘ≡sucᵘ∷Level t[σ₁]≡t[σ₂])
      )
