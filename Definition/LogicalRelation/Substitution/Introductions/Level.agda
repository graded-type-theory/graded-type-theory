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

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Introductions.Var R

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Reduction.Primitive R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Tools.Empty
open import Tools.Fin
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
