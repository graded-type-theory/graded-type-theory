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

open import Definition.LogicalRelation R {{eqrel}}
open import Definition.LogicalRelation.Hidden R {{eqrel}}
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R

open import Definition.Typed R
open import Definition.Typed.Properties R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M
open import Definition.Untyped.Properties M

open import Tools.Empty
open import Tools.Function
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality

private variable
  Γ Δ                               : Con Term _
  A A₁ A₂ B t t₁ t₂ u u₁ u₂ v v₁ v₂ : Term _
  σ₁ σ₂                             : Subst _ _
  l l′ l″ l‴                        : Universe-level
  p q r                             : M

-- mutual
--   reflect-level-subst
--     : ∀ {n m} {Γ : Con Term n} {Δ : Con Term m} {σ : Subst m n} {t : Term n}
--     → (⊩t : Γ ⊩Level t ∷Level)
--     → (⊩t[σ] : Δ ⊩Level t [ σ ] ∷Level)
--     → reflect-level ⊩t ≤ᵘ reflect-level ⊩t[σ]
--   reflect-level-subst {σ} (Levelₜ k [ _ , _ , t⇒k ] k≡k (ne x)) (Levelₜ k′ [ _ , _ , t[σ]⇒k′ ] k′≡k′ prop′) =
--     0≤ᵘ
--   reflect-level-subst {σ} (Levelₜ k [ _ , _ , t⇒k ] k≡k zeroᵘᵣ) (Levelₜ k′ [ _ , _ , t[σ]⇒k′ ] k′≡k′ prop′) =
--     0≤ᵘ
--   reflect-level-subst {σ} (Levelₜ k [ _ , _ , t⇒k ] k≡k (sucᵘᵣ x)) (Levelₜ k′ [ _ , _ , t[σ]⇒k′ ] k′≡k′ (sucᵘᵣ y)) =
--     1+≤ᵘ1+ {!   !}
--   reflect-level-subst {σ} (Levelₜ k [ _ , _ , t⇒k ] k≡k (sucᵘᵣ x)) (Levelₜ k′ [ _ , _ , t[σ]⇒k′ ] k′≡k′ zeroᵘᵣ) =
--     ⊥-elim {!   !}
--   reflect-level-subst {σ} (Levelₜ k [ _ , _ , t⇒k ] k≡k (sucᵘᵣ x)) (Levelₜ k′ [ _ , _ , t[σ]⇒k′ ] k′≡k′ (ne y)) =
--     ⊥-elim {!    !}

  -- reflect-level-prop-subst
  --   : ∀ {n m} {Γ : Con Term n} {Δ : Con Term m} {σ : Subst m n} {t : Term n}
  --   → (⊩t : Level-prop Γ t)
  --   → (⊩t[σ] : Level-prop Δ (t [ σ ]))
  --   → reflect-level-prop ⊩t ≤ᵘ reflect-level-prop ⊩t[σ]
  -- reflect-level-prop-subst ⊩t ⊩t[σ] = {!   !}

------------------------------------------------------------------------
-- Characterisation lemmas

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩Level≡⇔ : Γ ⊩⟨ l ⟩ Level ≡ A ⇔ Γ ⊩Level Level ≡ A
  ⊩Level≡⇔ =
      (λ (⊩Level , _ , Level≡A) →
         lemma (Level-elim ⊩Level)
           ((irrelevanceEq ⊩Level) (Level-intr (Level-elim ⊩Level)) Level≡A))
    , (λ Level≡A →
         case idRed:*: (Levelⱼ (wfEq (subset* Level≡A))) of λ
           Level⇒*Level →
         let ⊩Level = Levelᵣ Level⇒*Level in
           ⊩Level
         , (redSubst* Level≡A ⊩Level) .proj₁
         , Level≡A)
    where
    lemma :
      (⊩A : Γ ⊩⟨ l ⟩Level A) →
      Γ ⊩⟨ l ⟩ A ≡ B / Level-intr ⊩A →
      Γ ⊩Level A ≡ B
    lemma (noemb _)    A≡B = A≡B
    lemma (emb ≤ᵘ-refl ⊩A) A≡B = lemma ⊩A A≡B
    lemma (emb (≤ᵘ-step s) ⊩A) A≡B = lemma (emb s ⊩A) A≡B

opaque
  unfolding _⊩⟨_⟩_∷_

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷Level⇔ : Γ ⊩⟨ l ⟩ t ∷ Level ⇔ Γ ⊩Level t ∷Level
  ⊩∷Level⇔ =
      (λ (⊩Level , ⊩t) →
         lemma (Level-elim ⊩Level)
           ((irrelevanceTerm ⊩Level) (Level-intr (Level-elim ⊩Level)) ⊩t))
    , (λ ⊩t →
         Levelᵣ (idRed:*: (Levelⱼ (wfTerm (⊢t-redₜ (_⊩Level_∷Level.d ⊩t))))) , ⊩t)
    where
    lemma :
      (⊩A : Γ ⊩⟨ l ⟩Level A) →
      Γ ⊩⟨ l ⟩ t ∷ A / Level-intr ⊩A →
      Γ ⊩Level t ∷Level
    lemma (noemb _)    ⊩t = ⊩t
    lemma (emb ≤ᵘ-refl ⊩A) ⊩t = lemma ⊩A ⊩t
    lemma (emb (≤ᵘ-step s) ⊩A) ⊩t = lemma (emb s ⊩A) ⊩t

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷Level⇔ :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ Level ⇔
    (Γ ⊩Level t ∷Level × Γ ⊩Level u ∷Level × Γ ⊩Level t ≡ u ∷Level)
  ⊩≡∷Level⇔ =
      (λ (⊩Level , ⊩t , ⊩u , t≡u) →
         lemma (Level-elim ⊩Level)
           ((irrelevanceTerm ⊩Level) (Level-intr (Level-elim ⊩Level)) ⊩t)
           ((irrelevanceTerm ⊩Level) (Level-intr (Level-elim ⊩Level)) ⊩u)
           ((irrelevanceEqTerm ⊩Level) (Level-intr (Level-elim ⊩Level)) t≡u))
    , (λ (⊩t , ⊩u , t≡u) →
         Levelᵣ (idRed:*: (Levelⱼ (wfTerm (⊢t-redₜ (_⊩Level_≡_∷Level.d t≡u)))))
       , ⊩t , ⊩u , t≡u)
    where
    lemma :
      (⊩A : Γ ⊩⟨ l ⟩Level A) →
      Γ ⊩⟨ l ⟩ t ∷ A / Level-intr ⊩A →
      Γ ⊩⟨ l ⟩ u ∷ A / Level-intr ⊩A →
      Γ ⊩⟨ l ⟩ t ≡ u ∷ A / Level-intr ⊩A →
      Γ ⊩Level t ∷Level × Γ ⊩Level u ∷Level × Γ ⊩Level t ≡ u ∷Level
    lemma (noemb _)    ⊩t ⊩u t≡u = ⊩t , ⊩u , t≡u
    lemma (emb ≤ᵘ-refl ⊩A) ⊩t ⊩u t≡u = lemma ⊩A ⊩t ⊩u t≡u
    lemma (emb (≤ᵘ-step s) ⊩A) ⊩t ⊩u t≡u = lemma (emb s ⊩A) ⊩t ⊩u t≡u

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩zeroᵘ∷Level⇔ : Γ ⊩⟨ l ⟩ zeroᵘ ∷ Level ⇔ ⊢ Γ
  ⊩zeroᵘ∷Level⇔ =
      wfTerm ∘→ escape-⊩∷
    , (λ ⊢Γ →
         ⊩∷Level⇔ .proj₂ $
         Levelₜ _ (idRedTerm:*: (zeroᵘⱼ ⊢Γ)) (≅ₜ-zeroᵘrefl ⊢Γ) zeroᵘᵣ)

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩zeroᵘ≡zeroᵘ∷Level⇔ : Γ ⊩⟨ l ⟩ zeroᵘ ≡ zeroᵘ ∷ Level ⇔ ⊢ Γ
  ⊩zeroᵘ≡zeroᵘ∷Level⇔ {Γ} {l} =
    Γ ⊩⟨ l ⟩ zeroᵘ ≡ zeroᵘ ∷ Level  ⇔⟨ proj₁ ∘→ wf-⊩≡∷ , refl-⊩≡∷ ⟩
    Γ ⊩⟨ l ⟩ zeroᵘ ∷ Level         ⇔⟨ ⊩zeroᵘ∷Level⇔ ⟩
    ⊢ Γ                       □⇔

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩sucᵘ∷Level⇔ :
    Γ ⊩⟨ l ⟩ sucᵘ t ∷ Level ⇔
    Γ ⊩⟨ l ⟩ t ∷ Level
  ⊩sucᵘ∷Level⇔ {Γ} {l} {t} =
    Γ ⊩⟨ l ⟩ sucᵘ t ∷ Level  ⇔⟨ ⊩∷Level⇔ ⟩
    Γ ⊩Level sucᵘ t ∷Level       ⇔⟨ (λ { (Levelₜ _ sucᵘ-t⇒*u _ u-ok) →
                                case whnfRed*Term (redₜ sucᵘ-t⇒*u) sucᵘₙ of λ {
                                  PE.refl →
                                lemma u-ok }})
                         , (λ ⊩t@(Levelₜ _ [ ⊢t , _ , t⇒*u ] u≅u u-ok) →
                              let t↘u = t⇒*u , level u-ok in
                              Levelₜ _ (idRedTerm:*: (sucᵘⱼ ⊢t))
                                (≅ₜ-sucᵘ-cong $
                                 ≅ₜ-red (id (Levelⱼ (wfTerm ⊢t)) , Levelₙ) t↘u t↘u u≅u)
                                (sucᵘᵣ ⊩t))
                         ⟩
    Γ ⊩Level t ∷Level           ⇔˘⟨ ⊩∷Level⇔ ⟩
    Γ ⊩⟨ l ⟩ t ∷ Level      □⇔
    where
    lemma : Level-prop Γ (sucᵘ t) → Γ ⊩Level t ∷Level
    lemma (sucᵘᵣ ⊩t)           = ⊩t
    lemma (ne (neNfₜ () _ _))

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩sucᵘ≡sucᵘ∷Level⇔ :
    Γ ⊩⟨ l ⟩ sucᵘ t ≡ sucᵘ u ∷ Level ⇔
    Γ ⊩⟨ l ⟩ t ≡ u ∷ Level
  ⊩sucᵘ≡sucᵘ∷Level⇔ {Γ} {l} {t} {u} =
    Γ ⊩⟨ l ⟩ sucᵘ t ≡ sucᵘ u ∷ Level                             ⇔⟨ ⊩≡∷Level⇔ ⟩
    Γ ⊩Level sucᵘ t ∷Level × Γ ⊩Level sucᵘ u ∷Level × Γ ⊩Level sucᵘ t ≡ sucᵘ u ∷Level  ⇔⟨ ⊩∷Level⇔ {l = l} ∘⇔ ⊩sucᵘ∷Level⇔ ∘⇔ sym⇔ ⊩∷Level⇔
                                                                ×-cong-⇔
                                                              ⊩∷Level⇔ {l = l} ∘⇔ ⊩sucᵘ∷Level⇔ ∘⇔ sym⇔ ⊩∷Level⇔
                                                                ×-cong-⇔
                                                              (lemma₁ , lemma₂) ⟩
    Γ ⊩Level t ∷Level × Γ ⊩Level u ∷Level × Γ ⊩Level t ≡ u ∷Level                  ⇔˘⟨ ⊩≡∷Level⇔ ⟩
    Γ ⊩⟨ l ⟩ t ≡ u ∷ Level                                     □⇔
    where
    lemma₀ : [Level]-prop Γ (sucᵘ t) (sucᵘ u) → Γ ⊩Level t ≡ u ∷Level
    lemma₀ (sucᵘᵣ t≡u)           = t≡u
    lemma₀ (ne (neNfₜ₌ () _ _))

    lemma₁ : Γ ⊩Level sucᵘ t ≡ sucᵘ u ∷Level → Γ ⊩Level t ≡ u ∷Level
    lemma₁ (Levelₜ₌ _ _ sucᵘ-t⇒*t′ sucᵘ-u⇒*u′ _ t′≡u′) =
      case whnfRed*Term (redₜ sucᵘ-t⇒*t′) sucᵘₙ of λ {
        PE.refl →
      case whnfRed*Term (redₜ sucᵘ-u⇒*u′) sucᵘₙ of λ {
        PE.refl →
      lemma₀ t′≡u′}}

    lemma₂ : Γ ⊩Level t ≡ u ∷Level → Γ ⊩Level sucᵘ t ≡ sucᵘ u ∷Level
    lemma₂
      t≡u@(Levelₜ₌ _ _ [ ⊢t , _ , t⇒*t′ ] [ ⊢u , _ , u⇒*u′ ] t′≅u′ t′≡u′) =
      let t′-ok , u′-ok = lsplit t′≡u′ in
      Levelₜ₌ _ _ (idRedTerm:*: (sucᵘⱼ ⊢t)) (idRedTerm:*: (sucᵘⱼ ⊢u))
        (≅ₜ-sucᵘ-cong $
         ≅ₜ-red (id (Levelⱼ (wfTerm ⊢t)) , Levelₙ) (t⇒*t′ , t′-ok)
           (u⇒*u′ , u′-ok) t′≅u′)
        (sucᵘᵣ t≡u)

------------------------------------------------------------------------
-- Level

opaque

  -- Validity of Level, seen as a type former.

  Levelᵛ : ⊩ᵛ Γ → Γ ⊩ᵛ Level
  Levelᵛ {Γ} ⊩Γ =
    ⊩ᵛ-const-intro
      ( ⊩Γ
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ  →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ⊢ Δ               →⟨ Levelⱼ ⟩
          (Δ ⊢ Level)           →⟨ id ⟩
          Δ ⊢ Level ⇒* Level        ⇔˘⟨ ⊩Level≡⇔ ⟩→
          Δ ⊩⟨ 0 ⟩ Level ≡ Level    □
      )


opaque

  ⊩Level-zeroᵘ : ⊢ Γ → Γ ⊩Level zeroᵘ ∷Level
  ⊩Level-zeroᵘ ⊢Γ = Levelₜ zeroᵘ (idRedTerm:*: (zeroᵘⱼ ⊢Γ)) (≅ₜ-zeroᵘrefl ⊢Γ) zeroᵘᵣ

  reflect-level-zero : (⊢Γ : ⊢ Γ) → reflect-level (⊩Level-zeroᵘ ⊢Γ) PE.≡ 0
  reflect-level-zero ⊢Γ = PE.refl

  zeroᵘ≤ᵘ : (⊢Γ : ⊢ Γ) → reflect-level (⊩Level-zeroᵘ ⊢Γ) ≤ᵘ l
  zeroᵘ≤ᵘ {l} ⊢Γ = PE.subst (_≤ᵘ l) (PE.sym (reflect-level-zero ⊢Γ)) 0≤ᵘ

  ⊩zeroᵘ : ⊢ Γ → Γ ⊩⟨ l ⟩ zeroᵘ ∷ Level
  ⊩zeroᵘ = ⊩zeroᵘ∷Level⇔ .proj₂

  zeroᵘᵛ : ⊩ᵛ Γ → Γ ⊩ᵛ zeroᵘ ∷ Level
  zeroᵘᵛ {Γ} ⊩Γ =
    ⊩ᵛ∷-const-intro
      ( Levelᵛ ⊩Γ
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ          →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ⊢ Δ                       ⇔˘⟨ ⊩zeroᵘ≡zeroᵘ∷Level⇔ ⟩→
          Δ ⊩⟨ 0 ⟩ zeroᵘ ≡ zeroᵘ ∷ Level  □
      )

opaque

  sucᵘ-congᵛ : Γ ⊩ᵛ t ≡ u ∷ Level → Γ ⊩ᵛ sucᵘ t ≡ sucᵘ u ∷ Level
  sucᵘ-congᵛ t≡u = ⊩ᵛ≡∷⇔ .proj₂
    ( Levelᵛ (wf-⊩ᵛ $ wf-⊩ᵛ∷ $ wf-⊩ᵛ≡∷ t≡u .proj₁)
    , Σ.map idᶠ (⊩sucᵘ≡sucᵘ∷Level⇔ .proj₂) ∘→ ⊩ᵛ≡∷⇔ .proj₁ t≡u .proj₂)

opaque

  -- Validity of sucᵘ.

  sucᵘᵛ :
    Γ ⊩ᵛ t ∷ Level →
    Γ ⊩ᵛ sucᵘ t ∷ Level
  sucᵘᵛ ⊩t =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    sucᵘ-congᵛ (refl-⊩ᵛ≡∷ ⊩t)
