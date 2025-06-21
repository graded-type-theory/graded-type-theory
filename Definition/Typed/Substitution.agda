------------------------------------------------------------------------
-- Substitution lemmas
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Substitution
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Typed R
open import Definition.Typed.Properties.Admissible.Identity R
open import Definition.Typed.Properties.Admissible.Pi R
open import Definition.Typed.Properties.Admissible.Sigma R
import Definition.Typed.Substitution.Primitive R as P

open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Tools.Function
import Tools.PropositionalEquality as PE

open P public

private variable
  Γ Δ     : Con Term _
  A B t u : Term _
  σ       : Subst _ _

opaque

  -- A substitution lemma for _⊢_⇒_∷_.

  subst-⊢⇒∷ :
    Γ ⊢ t ⇒ u ∷ A →
    Δ ⊢ˢʷ σ ∷ Γ →
    Δ ⊢ t [ σ ] ⇒ u [ σ ] ∷ A [ σ ]
  subst-⊢⇒∷ (conv t⇒u B≡A) ⊢σ =
    conv (subst-⊢⇒∷ t⇒u ⊢σ) (subst-⊢≡ B≡A (refl-⊢ˢʷ≡∷ ⊢σ))
  subst-⊢⇒∷ (maxᵘ-zeroˡ ⊢l) ⊢σ =
    maxᵘ-zeroˡ (subst-⊢∷ ⊢l ⊢σ)
  subst-⊢⇒∷ (maxᵘ-zeroʳ ⊢l) ⊢σ =
    maxᵘ-zeroʳ (subst-⊢∷ ⊢l ⊢σ)
  subst-⊢⇒∷ (maxᵘ-sucᵘ ⊢l ⊢u) ⊢σ =
    maxᵘ-sucᵘ (subst-⊢∷ ⊢l ⊢σ) (subst-⊢∷ ⊢u ⊢σ)
  subst-⊢⇒∷ (maxᵘ-substˡ l⇒l′ ⊢u) ⊢σ =
    maxᵘ-substˡ (subst-⊢⇒∷ l⇒l′ ⊢σ) (subst-⊢∷ ⊢u ⊢σ)
  subst-⊢⇒∷ (maxᵘ-substʳ ⊢l u⇒u′) ⊢σ =
    maxᵘ-substʳ (subst-⊢∷ ⊢l ⊢σ) (subst-⊢⇒∷ u⇒u′ ⊢σ)
  subst-⊢⇒∷ (lower-subst x) ⊢σ =
    lower-subst (subst-⊢⇒∷ x ⊢σ)
  subst-⊢⇒∷ (Lift-β x x₁ x₂) ⊢σ =
    Lift-β (subst-⊢∷ x ⊢σ) (subst-⊢ x₁ ⊢σ) (subst-⊢∷ x₂ ⊢σ)
  subst-⊢⇒∷ (app-subst {G = B} t⇒u ⊢v) ⊢σ =
    PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym (singleSubstLift B _))
      (app-subst (subst-⊢⇒∷ t⇒u ⊢σ) (subst-⊢∷ ⊢v ⊢σ))
  subst-⊢⇒∷ (β-red {G = B} {t} ⊢B ⊢t ⊢u PE.refl ok) ⊢σ =
    PE.subst₂ (_⊢_⇒_∷_ _ _)
      (PE.sym (singleSubstLift t _))
      (PE.sym (singleSubstLift B _)) $
    β-red-⇒ (subst-⊢∷-⇑ ⊢t ⊢σ) (subst-⊢∷ ⊢u ⊢σ) ok
  subst-⊢⇒∷ (fst-subst _ t⇒u) ⊢σ =
    fst-subst′ (subst-⊢⇒∷ t⇒u ⊢σ)
  subst-⊢⇒∷ (snd-subst {G = B} _ t⇒u) ⊢σ =
    PE.subst (_ ⊢ _ ⇒ _ ∷_)
      (PE.sym (singleSubstLift B _)) $
    snd-subst′ (subst-⊢⇒∷ t⇒u ⊢σ)
  subst-⊢⇒∷ (Σ-β₁ {G = B} ⊢B ⊢t ⊢u eq ok) ⊢σ =
    Σ-β₁ (subst-⊢-⇑ ⊢B ⊢σ) (subst-⊢∷ ⊢t ⊢σ)
      (PE.subst (_⊢_∷_ _ _) (singleSubstLift B _) (subst-⊢∷ ⊢u ⊢σ))
      eq ok
  subst-⊢⇒∷ (Σ-β₂ {G = B} ⊢B ⊢t ⊢u eq ok) ⊢σ =
    PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift B _) $
    Σ-β₂ (subst-⊢-⇑ ⊢B ⊢σ) (subst-⊢∷ ⊢t ⊢σ)
      (PE.subst (_⊢_∷_ _ _) (singleSubstLift B _) (subst-⊢∷ ⊢u ⊢σ))
      eq ok
  subst-⊢⇒∷ (prodrec-subst {A = C} ⊢C ⊢u t₁⇒t₂ _) ⊢σ =
    PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift C _)
      (prodrec-subst′ (subst-⊢-⇑ ⊢C ⊢σ)
        (PE.subst (_ ⊢ _ ∷_) (subst-β-prodrec C _) $
         subst-⊢∷-⇑ ⊢u ⊢σ)
        (subst-⊢⇒∷ t₁⇒t₂ ⊢σ))
  subst-⊢⇒∷
    (prodrec-β {G = B} {A = C} {u = v} ⊢C ⊢t ⊢u ⊢v PE.refl _) ⊢σ =
    PE.subst₂ (_⊢_⇒_∷_ _ _)
      (PE.sym $ [,]-[]-commute v)
      (PE.sym $ singleSubstLift C _) $
    prodrec-β-⇒ (subst-⊢-⇑ ⊢C ⊢σ) (subst-⊢∷ ⊢t ⊢σ)
      (PE.subst (_⊢_∷_ _ _) (singleSubstLift B _) $
       subst-⊢∷ ⊢u ⊢σ)
      (PE.subst (_⊢_∷_ _ _) (subst-β-prodrec C _) $
       subst-⊢∷-⇑ ⊢v ⊢σ)
  subst-⊢⇒∷ (natrec-subst {A} ⊢t ⊢u v₁⇒v₂) ⊢σ =
    PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift A _) $
    natrec-subst
      (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) (subst-⊢∷ ⊢t ⊢σ))
      (PE.subst (_⊢_∷_ _ _) (natrecSucCase _ A) $
       subst-⊢∷-⇑ ⊢u ⊢σ)
      (subst-⊢⇒∷ v₁⇒v₂ ⊢σ)
  subst-⊢⇒∷ (natrec-zero {A} ⊢t ⊢u) ⊢σ =
    PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift A _) $
    natrec-zero
      (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) (subst-⊢∷ ⊢t ⊢σ))
      (PE.subst (_⊢_∷_ _ _) (natrecSucCase _ A) $
       subst-⊢∷-⇑ ⊢u ⊢σ)
  subst-⊢⇒∷ (natrec-suc {A} {s = u} ⊢t ⊢u ⊢v) ⊢σ =
    PE.subst₂ (_⊢_⇒_∷_ _ _)
      (PE.sym $ [,]-[]-commute u)
      (PE.sym $ singleSubstLift A _) $
    natrec-suc
      (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) (subst-⊢∷ ⊢t ⊢σ))
      (PE.subst (_⊢_∷_ _ _) (natrecSucCase _ A) $
       subst-⊢∷-⇑ ⊢u ⊢σ)
      (subst-⊢∷ ⊢v ⊢σ)
  subst-⊢⇒∷ (emptyrec-subst ⊢A t₁⇒t₂) ⊢σ =
    emptyrec-subst (subst-⊢ ⊢A ⊢σ) (subst-⊢⇒∷ t₁⇒t₂ ⊢σ)
  subst-⊢⇒∷ (unitrec-subst {A} ⊢l ⊢A ⊢u t₁⇒t₂ ok no-η) ⊢σ =
    PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift A _) $
    unitrec-subst (subst-⊢∷ ⊢l ⊢σ) (subst-⊢-⇑ ⊢A ⊢σ)
      (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) (subst-⊢∷ ⊢u ⊢σ))
      (subst-⊢⇒∷ t₁⇒t₂ ⊢σ) ok no-η
  subst-⊢⇒∷ (unitrec-β {A} ⊢l₁ l₁≡l₂ ⊢A ⊢t ok no-η) ⊢σ =
    PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift A _) $
    unitrec-β (subst-⊢∷ ⊢l₁ ⊢σ) (subst-⊢≡∷ l₁≡l₂ (refl-⊢ˢʷ≡∷ ⊢σ)) (subst-⊢-⇑ ⊢A ⊢σ)
      (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) (subst-⊢∷ ⊢t ⊢σ)) ok
      no-η
  subst-⊢⇒∷ (unitrec-β-η {A} ⊢l ⊢A ⊢t ⊢u ok η) ⊢σ =
    PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift A _) $
    unitrec-β-η (subst-⊢∷ ⊢l ⊢σ) (subst-⊢-⇑ ⊢A ⊢σ) (subst-⊢∷ ⊢t ⊢σ)
      (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) (subst-⊢∷ ⊢u ⊢σ)) ok η
  subst-⊢⇒∷ (J-subst {t} {A} {B} ⊢t ⊢B ⊢u ⊢v w₁⇒w₂) ⊢σ =
    PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ [,]-[]-commute B) $
    J-subst (subst-⊢∷ ⊢t ⊢σ)
      (PE.subst (flip _⊢_ _)
         (PE.cong (_∙_ _) $
          PE.cong₃ Id (wk1-liftSubst A) (wk1-liftSubst t) PE.refl) $
       subst-⊢-⇑ ⊢B ⊢σ)
      (PE.subst (_⊢_∷_ _ _) ([,]-[]-commute B) (subst-⊢∷ ⊢u ⊢σ))
      (subst-⊢∷ ⊢v ⊢σ) (subst-⊢⇒∷ w₁⇒w₂ ⊢σ)
  subst-⊢⇒∷ (K-subst {B} ⊢B ⊢u v₁⇒v₂ ok) ⊢σ =
    PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift B _) $
    K-subst (subst-⊢-⇑ ⊢B ⊢σ)
      (PE.subst (_⊢_∷_ _ _) (singleSubstLift B _) (subst-⊢∷ ⊢u ⊢σ))
      (subst-⊢⇒∷ v₁⇒v₂ ⊢σ) ok
  subst-⊢⇒∷ ([]-cong-subst _ _ _ v₁⇒v₂ ok) ⊢σ =
    []-cong-subst′ (subst-⊢⇒∷ v₁⇒v₂ ⊢σ) ok
  subst-⊢⇒∷ (J-β {t} {A} {B} _ _ t≡t′ ⊢B _ ⊢u) ⊢σ =
    PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ [,]-[]-commute B) $
    J-β-⇒ (subst-⊢≡∷ t≡t′ (refl-⊢ˢʷ≡∷ ⊢σ))
      (PE.subst (flip _⊢_ _)
         (PE.cong (_∙_ _) $
          PE.cong₃ Id (wk1-liftSubst A) (wk1-liftSubst t) PE.refl) $
       subst-⊢-⇑ ⊢B ⊢σ)
      (PE.subst (_⊢_∷_ _ _) ([,]-[]-commute B) (subst-⊢∷ ⊢u ⊢σ))
  subst-⊢⇒∷ (K-β {B} ⊢B ⊢u ok) ⊢σ =
    PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift B _) $
    K-β (subst-⊢-⇑ ⊢B ⊢σ)
      (PE.subst (_⊢_∷_ _ _) (singleSubstLift B _) (subst-⊢∷ ⊢u ⊢σ)) ok
  subst-⊢⇒∷ ([]-cong-β _ _ _ t≡t′ ok) ⊢σ =
    []-cong-β-⇒ (subst-⊢≡∷ t≡t′ (refl-⊢ˢʷ≡∷ ⊢σ)) ok

opaque

  -- A substitution lemma for _⊢_⇒*_∷_.

  subst-⊢⇒*∷ :
    Γ ⊢ t ⇒* u ∷ A →
    Δ ⊢ˢʷ σ ∷ Γ →
    Δ ⊢ t [ σ ] ⇒* u [ σ ] ∷ A [ σ ]
  subst-⊢⇒*∷ (id ⊢t)      ⊢σ = id (subst-⊢∷ ⊢t ⊢σ)
  subst-⊢⇒*∷ (t⇒u ⇨ u⇒*v) ⊢σ = subst-⊢⇒∷ t⇒u ⊢σ ⇨ subst-⊢⇒*∷ u⇒*v ⊢σ

opaque

  -- A substitution lemma for _⊢_⇒_.

  subst-⊢⇒ :
    Γ ⊢ A ⇒ B →
    Δ ⊢ˢʷ σ ∷ Γ →
    Δ ⊢ A [ σ ] ⇒ B [ σ ]
  subst-⊢⇒ (univ A⇒B) ⊢σ =
    univ (subst-⊢⇒∷ A⇒B ⊢σ)

opaque

  -- A substitution lemma for _⊢_⇒*_.

  subst-⊢⇒* :
    Γ ⊢ A ⇒* B →
    Δ ⊢ˢʷ σ ∷ Γ →
    Δ ⊢ A [ σ ] ⇒* B [ σ ]
  subst-⊢⇒* (id ⊢A)      ⊢σ = id (subst-⊢ ⊢A ⊢σ)
  subst-⊢⇒* (A⇒B ⇨ B⇒*C) ⊢σ = subst-⊢⇒ A⇒B ⊢σ ⇨ subst-⊢⇒* B⇒*C ⊢σ
