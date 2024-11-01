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
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R

open import Definition.Typed R
open import Definition.Typed.Properties R

open import Definition.Untyped M
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

mutual
  reflect-level-subst
    : ∀ {n m} {Γ : Con Term n} {Δ : Con Term m} {σ : Subst m n} {t : Term n}
    → (⊩t : Γ ⊩Level t ∷Level)
    → (⊩t[σ] : Δ ⊩Level t [ σ ] ∷Level)
    → reflect-level ⊩t ≤ᵘ reflect-level ⊩t[σ]
  reflect-level-subst {σ} (Levelₜ k [ _ , _ , t⇒k ] k≡k (ne x)) (Levelₜ k′ [ _ , _ , t[σ]⇒k′ ] k′≡k′ prop′) =
    0≤ᵘ
  reflect-level-subst {σ} (Levelₜ k [ _ , _ , t⇒k ] k≡k zeroᵘᵣ) (Levelₜ k′ [ _ , _ , t[σ]⇒k′ ] k′≡k′ prop′) =
    0≤ᵘ
  reflect-level-subst {σ} (Levelₜ k [ _ , _ , t⇒k ] k≡k (sucᵘᵣ x)) (Levelₜ k′ [ _ , _ , t[σ]⇒k′ ] k′≡k′ (sucᵘᵣ y)) =
    1+≤ᵘ1+ {!   !}
  reflect-level-subst {σ} (Levelₜ k [ _ , _ , t⇒k ] k≡k (sucᵘᵣ x)) (Levelₜ k′ [ _ , _ , t[σ]⇒k′ ] k′≡k′ zeroᵘᵣ) =
    ⊥-elim {!   !}
  reflect-level-subst {σ} (Levelₜ k [ _ , _ , t⇒k ] k≡k (sucᵘᵣ x)) (Levelₜ k′ [ _ , _ , t[σ]⇒k′ ] k′≡k′ (ne y)) =
    ⊥-elim {!    !}

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

------------------------------------------------------------------------
-- Level

opaque

  -- Validity of Level, seen as a type former.

  Levelᵛ : ⊩ᵛ Γ → Γ ⊩ᵛ⟨ l ⟩ Level
  Levelᵛ {Γ} {l} ⊩Γ =
    ⊩ᵛ⇔ .proj₂
      ( ⊩Γ
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ  →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ⊢ Δ               →⟨ Levelⱼ ⟩
          (Δ ⊢ Level)           →⟨ id ⟩
          Δ ⊢ Level ⇒* Level        ⇔˘⟨ ⊩Level≡⇔ ⟩→
          Δ ⊩⟨ l ⟩ Level ≡ Level    □
      )


opaque

  ⊩Level-zeroᵘ : ⊢ Γ → Γ ⊩Level zeroᵘ ∷Level
  ⊩Level-zeroᵘ ⊢Γ = Levelₜ zeroᵘ (idRedTerm:*: (zeroᵘⱼ ⊢Γ)) (≅ₜ-zeroᵘrefl ⊢Γ) zeroᵘᵣ

  ⊩zeroᵘ : ⊢ Γ → Γ ⊩⟨ l ⟩ zeroᵘ ∷ Level
  ⊩zeroᵘ = ⊩zeroᵘ∷Level⇔ .proj₂

  zeroᵘᵛ : ⊩ᵛ Γ → Γ ⊩ᵛ⟨ l ⟩ zeroᵘ ∷ Level
  zeroᵘᵛ {Γ} {l} ⊩Γ =
    ⊩ᵛ∷⇔ .proj₂
      ( Levelᵛ ⊩Γ
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ          →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ⊢ Δ                       ⇔˘⟨ ⊩zeroᵘ≡zeroᵘ∷Level⇔ ⟩→
          Δ ⊩⟨ l ⟩ zeroᵘ ≡ zeroᵘ ∷ Level  □
      )
