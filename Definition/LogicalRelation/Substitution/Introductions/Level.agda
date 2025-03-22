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
          Levelᵣ (id (Levelⱼ (wfTerm (escapeLevel (wf-⊩Level t≡u .proj₁)))))
         , t≡u)

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷ Level

  ⊩∷Level⇔ : Γ ⊩⟨ l ⟩ t ∷ Level ⇔ Γ ⊩Level t ∷Level
  ⊩∷Level⇔ {Γ} {l} {t} =
    Γ ⊩⟨ l ⟩ t ∷ Level      ⇔⟨ ⊩∷⇔⊩≡∷ ⟩
    Γ ⊩⟨ l ⟩ t ≡ t ∷ Level  ⇔⟨ ⊩≡∷Level⇔ ⟩
    Γ ⊩Level t ≡ t ∷Level   ⇔⟨ id⇔ ⟩
    Γ ⊩Level t ∷Level       □⇔

opaque

  ⊩zeroᵘ : ⊢ Γ → Γ ⊩Level zeroᵘ ∷Level
  ⊩zeroᵘ ⊢Γ =
    Levelₜ₌ _ _ (id (zeroᵘⱼ ⊢Γ)) (id (zeroᵘⱼ ⊢Γ)) zeroᵘᵣ

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

  ⊩sucᵘ≡sucᵘ : Γ ⊩Level t ≡ u ∷Level → Γ ⊩Level sucᵘ t ≡ sucᵘ u ∷Level
  ⊩sucᵘ≡sucᵘ t≡u@(Levelₜ₌ _ _ t⇒*t′ u⇒*u′ t′≡u′) =
    let t′-ok , u′-ok = lsplit t′≡u′ in
    Levelₜ₌ _ _
      (id (sucᵘⱼ (redFirst*Term t⇒*t′)))
      (id (sucᵘⱼ (redFirst*Term u⇒*u′)))
      (sucᵘᵣ t≡u)

  ⊩sucᵘ : Γ ⊩Level t ∷Level → Γ ⊩Level sucᵘ t ∷Level
  ⊩sucᵘ = ⊩sucᵘ≡sucᵘ

  ⊩sucᵘ≡sucᵘ⇔ :
    Γ ⊩Level sucᵘ t ≡ sucᵘ u ∷Level ⇔
    Γ ⊩Level t ≡ u ∷Level
  ⊩sucᵘ≡sucᵘ⇔ {Γ} {t} {u} = lemma₁ , ⊩sucᵘ≡sucᵘ
    where
    lemma₀ : [Level]-prop Γ (sucᵘ t) (sucᵘ u) → Γ ⊩Level t ≡ u ∷Level
    lemma₀ (sucᵘᵣ t≡u)             = t≡u
    lemma₀ (ne (sneₜ₌ (ne ()) _ _))

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
         case rest of λ where
           (ne (sneₜ₌ (ne ()) _ _)) }}})
    , ⊥-elim

opaque

  private
    lemma
      : [Level]-prop Γ t u
      → t PE.≡ zeroᵘ × u PE.≡ zeroᵘ
      ⊎   (∀ {t′} → Semineutral t′ → Semineutral (t′ maxᵘ t))
        × (∀ {t′} → Semineutral t′ → Semineutral (t′ maxᵘ u))
    lemma zeroᵘᵣ = inj₁ (PE.refl , PE.refl)
    lemma (sucᵘᵣ x) = inj₂ (maxᵘₙ₂ , maxᵘₙ₂)
    lemma (ne (sneₜ₌ n₁ n₂ _)) = inj₂ ((λ n → maxᵘₙ₁ n n₁) , λ n → maxᵘₙ₁ n n₂)

  -- An introduction lemma for _⊩Level _ maxᵘ _ ≡ _ maxᵘ _ ∷Level

  ⊩maxᵘ≡maxᵘ :
    Γ ⊩Level t₁ ≡ t₂ ∷Level →
    Γ ⊩Level u₁ ≡ u₂ ∷Level →
    Γ ⊩Level t₁ maxᵘ u₁ ≡ t₂ maxᵘ u₂ ∷Level
  ⊩maxᵘ≡maxᵘ {t₁} {t₂} {u₁} {u₂}
    t₁≡t₂@(Levelₜ₌ t₁′ t₂′ t₁⇒ t₂⇒ propt)
    u₁≡u₂@(Levelₜ₌ u₁′ u₂′ u₁⇒ u₂⇒ propu)
    =
    let ⊩t₁ , ⊩t₂ = wf-⊩Level t₁≡t₂
        ⊩u₁ , ⊩u₂ = wf-⊩Level u₁≡u₂
        ⊢t₁ = escapeLevel ⊩t₁
        ⊢t₂ = escapeLevel ⊩t₂
        ⊢u₁ = escapeLevel ⊩u₁
        ⊢u₂ = escapeLevel ⊩u₂
        _ , ⊢u₁′ , ⊢u₂′ = wf-⊢≡∷ (≅ₜ-eq (escapeLevel-prop (wfTerm ⊢t₁) propu))
    in case propt of λ where
        zeroᵘᵣ → Levelₜ₌ u₁′ u₂′
          (t₁    maxᵘ u₁  ⇒*⟨ maxᵘ-substˡ* t₁⇒ ⊢u₁ ⟩
           zeroᵘ maxᵘ u₁  ⇒⟨ maxᵘ-zeroˡ ⊢u₁ ⟩
                      u₁  ⇒*⟨ u₁⇒ ⟩∎
                      u₁′ ∎)
          (t₂    maxᵘ u₂  ⇒*⟨ maxᵘ-substˡ* t₂⇒ ⊢u₂ ⟩
           zeroᵘ maxᵘ u₂  ⇒⟨ maxᵘ-zeroˡ ⊢u₂ ⟩
                      u₂  ⇒*⟨ u₂⇒ ⟩∎
                      u₂′ ∎)
          propu
        (sucᵘᵣ {k = t₁′} {k′ = t₂′} t₁′≡t₂′) →
          let ⊩t₁′ , ⊩t₂′ = wf-⊩Level t₁′≡t₂′
              ⊢t₁′ = escapeLevel ⊩t₁′
              ⊢t₂′ = escapeLevel ⊩t₂′
          in case propu of λ where
            zeroᵘᵣ → Levelₜ₌ (sucᵘ t₁′) (sucᵘ t₂′)
              (t₁       maxᵘ u₁    ⇒*⟨ maxᵘ-substˡ* t₁⇒ ⊢u₁ ⟩
               sucᵘ t₁′ maxᵘ u₁    ⇒*⟨ maxᵘ-substʳ* (sucᵘⱼ ⊢t₁′) u₁⇒ sucᵘₙ sucᵘ≢zeroᵘ ⟩
               sucᵘ t₁′ maxᵘ zeroᵘ ⇒⟨ maxᵘ-zeroʳ (sucᵘⱼ ⊢t₁′) sucᵘₙ sucᵘ≢zeroᵘ ⟩∎
               sucᵘ t₁′            ∎)
              (t₂       maxᵘ u₂    ⇒*⟨ maxᵘ-substˡ* t₂⇒ ⊢u₂ ⟩
               sucᵘ t₂′ maxᵘ u₂    ⇒*⟨ maxᵘ-substʳ* (sucᵘⱼ ⊢t₂′) u₂⇒ sucᵘₙ sucᵘ≢zeroᵘ ⟩
               sucᵘ t₂′ maxᵘ zeroᵘ ⇒⟨ maxᵘ-zeroʳ (sucᵘⱼ ⊢t₂′) sucᵘₙ sucᵘ≢zeroᵘ ⟩∎
               sucᵘ t₂′            ∎)
              (sucᵘᵣ t₁′≡t₂′)
            (sucᵘᵣ {k = u₁′} {k′ = u₂′} u₁′≡u₂′) →
              let ⊩u₁′ , ⊩u₂′ = wf-⊩Level u₁′≡u₂′
                  ⊢u₁′ = escapeLevel ⊩u₁′
                  ⊢u₂′ = escapeLevel ⊩u₂′
              in Levelₜ₌ (sucᵘ (t₁′ maxᵘ u₁′)) (sucᵘ (t₂′ maxᵘ u₂′))
                (t₁       maxᵘ u₁       ⇒*⟨ maxᵘ-substˡ* t₁⇒ ⊢u₁ ⟩
                 sucᵘ t₁′ maxᵘ u₁       ⇒*⟨ maxᵘ-substʳ* (sucᵘⱼ ⊢t₁′) u₁⇒ sucᵘₙ sucᵘ≢zeroᵘ ⟩
                 sucᵘ t₁′ maxᵘ sucᵘ u₁′ ⇒⟨ maxᵘ-sucᵘ ⊢t₁′ ⊢u₁′ ⟩∎
                 sucᵘ (t₁′ maxᵘ u₁′)    ∎)
                (t₂       maxᵘ u₂       ⇒*⟨ maxᵘ-substˡ* t₂⇒ ⊢u₂ ⟩
                 sucᵘ t₂′ maxᵘ u₂       ⇒*⟨ maxᵘ-substʳ* (sucᵘⱼ ⊢t₂′) u₂⇒ sucᵘₙ sucᵘ≢zeroᵘ ⟩
                 sucᵘ t₂′ maxᵘ sucᵘ u₂′ ⇒⟨ maxᵘ-sucᵘ ⊢t₂′ ⊢u₂′ ⟩∎
                 sucᵘ (t₂′ maxᵘ u₂′)    ∎)
                (sucᵘᵣ (⊩maxᵘ≡maxᵘ t₁′≡t₂′ u₁′≡u₂′))
            (ne u₁′≡u₂′@(sneₜ₌ n₁ n₂ prop)) →
              Levelₜ₌ (sucᵘ t₁′ maxᵘ u₁′) (sucᵘ t₂′ maxᵘ u₂′)
                (t₁       maxᵘ u₁  ⇒*⟨ maxᵘ-substˡ* t₁⇒ ⊢u₁ ⟩
                 sucᵘ t₁′ maxᵘ u₁  ⇒*⟨ maxᵘ-substʳ* (sucᵘⱼ ⊢t₁′) u₁⇒ sucᵘₙ sucᵘ≢zeroᵘ ⟩∎
                 sucᵘ t₁′ maxᵘ u₁′ ∎)
                (t₂       maxᵘ u₂  ⇒*⟨ maxᵘ-substˡ* t₂⇒ ⊢u₂ ⟩
                 sucᵘ t₂′ maxᵘ u₂  ⇒*⟨ maxᵘ-substʳ* (sucᵘⱼ ⊢t₂′) u₂⇒ sucᵘₙ sucᵘ≢zeroᵘ ⟩∎
                 sucᵘ t₂′ maxᵘ u₂′ ∎)
                (ne (sneₜ₌ (maxᵘₙ₃ n₁) (maxᵘₙ₃ n₂)
                  (maxᵘᵣ
                    (⊩sucᵘ≡sucᵘ t₁′≡t₂′)
                    (Levelₜ₌ _ _ (id ⊢u₁′) (id ⊢u₂′) propu))))
        (ne t₁′≡t₂′@(sneₜ₌ n₁ n₂ prop)) →
          let t₁′~t₂′ = ≅ₜ-eq $ escapeSneEq t₁′≡t₂′
              _ , ⊢t₁′ , ⊢t₂′ = wf-⊢≡∷ t₁′~t₂′
          in case lemma propu of λ where
            (inj₁ (PE.refl , PE.refl)) →
              Levelₜ₌ t₁′ t₂′
                (t₁  maxᵘ u₁    ⇒*⟨ maxᵘ-substˡ* t₁⇒ ⊢u₁ ⟩
                 t₁′ maxᵘ u₁    ⇒*⟨ maxᵘ-substʳ* ⊢t₁′ u₁⇒ (ne n₁) (zeroᵘ≢ne n₁ ∘→ PE.sym) ⟩
                 t₁′ maxᵘ zeroᵘ ⇒⟨ maxᵘ-zeroʳ ⊢t₁′ (ne n₁) (zeroᵘ≢ne n₁ ∘→ PE.sym) ⟩∎
                 t₁′            ∎)
                (t₂  maxᵘ u₂    ⇒*⟨ maxᵘ-substˡ* t₂⇒ ⊢u₂ ⟩
                 t₂′ maxᵘ u₂    ⇒*⟨ maxᵘ-substʳ* ⊢t₂′ u₂⇒ (ne n₂) (zeroᵘ≢ne n₂ ∘→ PE.sym) ⟩
                 t₂′ maxᵘ zeroᵘ ⇒⟨ maxᵘ-zeroʳ ⊢t₂′ (ne n₂) (zeroᵘ≢ne n₂ ∘→ PE.sym) ⟩∎
                 t₂′            ∎)
              (ne t₁′≡t₂′)
            (inj₂ (n₁′ , n₂′)) →
              Levelₜ₌ (t₁′ maxᵘ u₁′) (t₂′ maxᵘ u₂′)
                (t₁  maxᵘ u₁  ⇒*⟨ maxᵘ-substˡ* t₁⇒ ⊢u₁ ⟩
                 t₁′ maxᵘ u₁  ⇒*⟨ maxᵘ-substʳ* ⊢t₁′ u₁⇒ (ne n₁) (zeroᵘ≢ne n₁ ∘→ PE.sym) ⟩∎
                 t₁′ maxᵘ u₁′ ∎)
                (t₂  maxᵘ u₂  ⇒*⟨ maxᵘ-substˡ* t₂⇒ ⊢u₂ ⟩
                 t₂′ maxᵘ u₂  ⇒*⟨ maxᵘ-substʳ* ⊢t₂′ u₂⇒ (ne n₂) (zeroᵘ≢ne n₂ ∘→ PE.sym) ⟩∎
                 t₂′ maxᵘ u₂′ ∎)
                (ne (sneₜ₌ (n₁′ n₁) (n₂′ n₂)
                  (maxᵘᵣ
                    (Levelₜ₌ _ _ (id ⊢t₁′) (id ⊢t₂′) propt)
                    (Levelₜ₌ _ _ (id ⊢u₁′) (id ⊢u₂′) propu))))

opaque

  -- An introduction lemma for _⊩Level _ maxᵘ _ ∷Level

  ⊩maxᵘ :
    Γ ⊩Level t ∷Level →
    Γ ⊩Level u ∷Level →
    Γ ⊩Level t maxᵘ u ∷Level
  ⊩maxᵘ ⊩t ⊩u = ⊩maxᵘ≡maxᵘ ⊩t ⊩u

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

  private
    maxᵘ-zeroʳ′ : ⊢ Γ → [Level]-prop Γ t u → Γ ⊢ t maxᵘ zeroᵘ ⇒ t ∷ Level
    maxᵘ-zeroʳ′ ⊢Γ zeroᵘᵣ = maxᵘ-zeroˡ (zeroᵘⱼ ⊢Γ)
    maxᵘ-zeroʳ′ ⊢Γ (sucᵘᵣ x) = maxᵘ-zeroʳ
      (sucᵘⱼ (escapeLevel (wf-⊩Level x .proj₁)))
      sucᵘₙ sucᵘ≢zeroᵘ
    maxᵘ-zeroʳ′ ⊢Γ (ne x@(sneₜ₌ n₁ n₂ _)) = maxᵘ-zeroʳ
      (wf-⊢≡∷ (≅ₜ-eq (escapeSneEq x)) .proj₂ .proj₁)
      (ne n₁)
      (zeroᵘ≢ne n₁ ∘→ PE.sym)

  ⊩maxᵘ-zeroʳ :
    Γ ⊩Level t ∷Level →
    Γ ⊩Level t maxᵘ zeroᵘ ≡ t ∷Level
  ⊩maxᵘ-zeroʳ {t} (Levelₜ₌ k k′ t⇒ t⇒′ prop) =
    let ⊢Γ = wfEqTerm (subset*Term t⇒)
    in Levelₜ₌ k k′
      (t maxᵘ zeroᵘ ⇒*⟨ maxᵘ-substˡ* t⇒ (zeroᵘⱼ ⊢Γ) ⟩
       k maxᵘ zeroᵘ ⇒⟨ maxᵘ-zeroʳ′ ⊢Γ prop ⟩∎
       k ∎)
      t⇒′
      prop

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

------------------------------------------------------------------------
-- Level reflection

opaque
  unfolding ↑ᵘ′_

  -- Level reflection sends zeroᵘ to 0ᵘ.

  ↑ᵘ′-zeroᵘ : ([0] : Γ ⊩Level zeroᵘ ≡ t ∷Level) → ↑ᵘ′ [0] PE.≡ 0
  ↑ᵘ′-zeroᵘ (Levelₜ₌ _ _ 0⇒ _ prop) with whnfRed*Term 0⇒ zeroᵘₙ
  ↑ᵘ′-zeroᵘ (Levelₜ₌ _ _ 0⇒ _ zeroᵘᵣ) | PE.refl = PE.refl
  ↑ᵘ′-zeroᵘ (Levelₜ₌ _ _ 0⇒ _ (ne (sneₜ₌ (ne ()) _ _))) | PE.refl

  ↑ᵘ-zeroᵘ : ([0] : Γ ⊩Level zeroᵘ ≡ t ∷Level) → ↑ᵘ [0] PE.≡ 0ᵘ
  ↑ᵘ-zeroᵘ [0] = PE.cong 0ᵘ+_ (↑ᵘ′-zeroᵘ [0])

  -- zeroᵘ is the smallest level.

  zeroᵘ-≤ᵘ : {[0] : Γ ⊩Level zeroᵘ ≡ t ∷Level} → ↑ᵘ [0] ≤ᵘ l
  zeroᵘ-≤ᵘ {l} {[0]} = PE.subst (_≤ᵘ l) (PE.sym (↑ᵘ-zeroᵘ [0])) 0≤ᵘ

opaque
  unfolding ↑ᵘ′_

  -- Level reflection sends sucᵘ to 1+.

  ↑ᵘ′-sucᵘ
    : ∀ {t u v} ([t] : Γ ⊩Level t ≡ u ∷Level) ([t+1] : Γ ⊩Level sucᵘ t ≡ v ∷Level)
    → ↑ᵘ′ [t+1] PE.≡ 1+ (↑ᵘ′ [t])
  ↑ᵘ′-sucᵘ [t] (Levelₜ₌ _ _ t+1⇒ _ prop′) with whnfRed*Term t+1⇒ sucᵘₙ
  ↑ᵘ′-sucᵘ [t] (Levelₜ₌ _ _ t+1⇒ _ (ne (sneₜ₌ (ne ()) _ _))) | PE.refl
  ↑ᵘ′-sucᵘ [t] [t+1]@(Levelₜ₌ _ _ t+1⇒ _ (sucᵘᵣ [t]′)) | PE.refl
    = PE.cong 1+ (↑ᵘ′-irrelevance [t]′ [t])

  -- sucᵘ is inflationary.

  <′-sucᵘ
    : ∀ {t u v} ([t] : Γ ⊩Level t ≡ u ∷Level) ([t+1] : Γ ⊩Level sucᵘ t ≡ v ∷Level)
    → ↑ᵘ′ [t] <′ ↑ᵘ′ [t+1]
  <′-sucᵘ [t] [t+1] = PE.subst (↑ᵘ′ [t] <′_) (PE.sym (↑ᵘ′-sucᵘ [t] [t+1])) ≤′-refl

  <ᵘ-sucᵘ
    : ∀ {t u v} {[t] : Γ ⊩Level t ≡ u ∷Level} {[t+1] : Γ ⊩Level sucᵘ t ≡ v ∷Level}
    → ↑ᵘ [t] <ᵘ ↑ᵘ [t+1]
  <ᵘ-sucᵘ {[t]} {[t+1]} = <ᵘ-nat (<′-sucᵘ [t] [t+1])

opaque
  unfolding ↑ᵘ′_ ⊩sucᵘ≡sucᵘ ⊩maxᵘ≡maxᵘ ⊩maxᵘ

  -- Level reflection sends maxᵘ to ⊔ᵘ.

  ↑ᵘ′-maxᵘ≡maxᵘ :
    (t₁≡t₂ : Γ ⊩Level t₁ ≡ t₂ ∷Level) →
    (u₁≡u₂ : Γ ⊩Level u₁ ≡ u₂ ∷Level) →
    ↑ᵘ′ ⊩maxᵘ≡maxᵘ t₁≡t₂ u₁≡u₂ PE.≡ ↑ᵘ′ t₁≡t₂ ⊔ ↑ᵘ′ u₁≡u₂
  ↑ᵘ′-maxᵘ≡maxᵘ (Levelₜ₌ t₁′ t₂′ t₁⇒ t₂⇒ zeroᵘᵣ) (Levelₜ₌ u₁′ u₂′ u₁⇒ u₂⇒ propu) = PE.refl
  ↑ᵘ′-maxᵘ≡maxᵘ (Levelₜ₌ t₁′ t₂′ t₁⇒ t₂⇒ (sucᵘᵣ x)) (Levelₜ₌ u₁′ u₂′ u₁⇒ u₂⇒ zeroᵘᵣ) = PE.refl
  ↑ᵘ′-maxᵘ≡maxᵘ (Levelₜ₌ t₁′ t₂′ t₁⇒ t₂⇒ (sucᵘᵣ t₁′≡t₂′)) (Levelₜ₌ u₁′ u₂′ u₁⇒ u₂⇒ (sucᵘᵣ u₁′≡u₂′)) = PE.cong 1+ (↑ᵘ′-maxᵘ≡maxᵘ t₁′≡t₂′ u₁′≡u₂′)
  ↑ᵘ′-maxᵘ≡maxᵘ (Levelₜ₌ t₁′ t₂′ t₁⇒ t₂⇒ (sucᵘᵣ x@record{})) (Levelₜ₌ u₁′ u₂′ u₁⇒ u₂⇒ (ne record{})) = PE.refl
  ↑ᵘ′-maxᵘ≡maxᵘ (Levelₜ₌ t₁′ t₂′ t₁⇒ t₂⇒ (ne record{})) (Levelₜ₌ u₁′ u₂′ u₁⇒ u₂⇒ zeroᵘᵣ) = PE.sym (⊔-identityʳ _)
  ↑ᵘ′-maxᵘ≡maxᵘ (Levelₜ₌ t₁′ t₂′ t₁⇒ t₂⇒ (ne record{})) (Levelₜ₌ u₁′ u₂′ u₁⇒ u₂⇒ (sucᵘᵣ x)) = PE.refl
  ↑ᵘ′-maxᵘ≡maxᵘ (Levelₜ₌ t₁′ t₂′ t₁⇒ t₂⇒ (ne record{})) (Levelₜ₌ u₁′ u₂′ u₁⇒ u₂⇒ (ne record{})) = PE.refl

  ↑ᵘ-maxᵘ≡maxᵘ :
    (t₁≡t₂ : Γ ⊩Level t₁ ≡ t₂ ∷Level) →
    (u₁≡u₂ : Γ ⊩Level u₁ ≡ u₂ ∷Level) →
    ↑ᵘ ⊩maxᵘ≡maxᵘ t₁≡t₂ u₁≡u₂ PE.≡ ↑ᵘ t₁≡t₂ ⊔ᵘ ↑ᵘ u₁≡u₂
  ↑ᵘ-maxᵘ≡maxᵘ t₁≡t₂ u₁≡u₂ = PE.cong 0ᵘ+_ (↑ᵘ′-maxᵘ≡maxᵘ t₁≡t₂ u₁≡u₂)

  ↑ᵘ-maxᵘ :
    (⊩t : Γ ⊩Level t ∷Level) →
    (⊩u : Γ ⊩Level u ∷Level) →
    ↑ᵘ ⊩maxᵘ ⊩t ⊩u PE.≡ ↑ᵘ ⊩t ⊔ᵘ ↑ᵘ ⊩u
  ↑ᵘ-maxᵘ ⊩t ⊩u = ↑ᵘ-maxᵘ≡maxᵘ ⊩t ⊩u

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
