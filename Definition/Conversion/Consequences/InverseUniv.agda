------------------------------------------------------------------------
-- Type equalities are also term equalities (in the absence of
-- equality reflection)
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Conversion.Consequences.InverseUniv
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  ⦃ no-equality-reflection : No-equality-reflection ⦄
  where

open import Definition.Conversion.Soundness R
open import Definition.Conversion.Consequences.Completeness R
open import Definition.Untyped M
open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Stability R
open import Definition.Typed.Syntactic R

open import Tools.Function
open import Tools.Sum using (_⊎_; inj₁; inj₂)
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  Γ           : Cons _ _
  A B l l₁ l₂ : Term _

opaque

  -- Terms can only "belong" to a single universe.

  universe-level-unique :
    Γ ⊢ A ∷ U l₁ → Γ ⊢ A ∷ U l₂ → Γ ⊢ l₁ ≡ l₂ ∷Level
  universe-level-unique ⊢A₁ ⊢A₂ =
    soundnessConv↑-U ⊢A₁ ⊢A₂ (completeEq (refl (univ ⊢A₁))) .proj₂

opaque

  -- If A or B is a term of type U l, then Γ ⊢ A ≡ B implies
  -- Γ ⊢ A ≡ B ∷ U l.

  inverseUnivEq′ :
    Γ ⊢ A ∷ U l ⊎ Γ ⊢ B ∷ U l →
    Γ ⊢ A ≡ B →
    Γ ⊢ A ≡ B ∷ U l
  inverseUnivEq′ (inj₁ ⊢A) (univ A≡B) =
    conv A≡B
      (U-cong-⊢≡ $
       universe-level-unique (syntacticEqTerm A≡B .proj₂ .proj₁) ⊢A)
  inverseUnivEq′ (inj₂ ⊢B) (univ A≡B) =
    conv A≡B
      (U-cong-⊢≡ $
       universe-level-unique (syntacticEqTerm A≡B .proj₂ .proj₂) ⊢B)
  inverseUnivEq′ (inj₁ ⊢A) (refl _) =
    refl ⊢A
  inverseUnivEq′ (inj₂ ⊢A) (refl _) =
    refl ⊢A
  inverseUnivEq′ (inj₁ ⊢A) (sym B≡A) =
    sym′ (inverseUnivEq′ (inj₂ ⊢A) B≡A)
  inverseUnivEq′ (inj₂ ⊢B) (sym B≡A) =
    sym′ (inverseUnivEq′ (inj₁ ⊢B) B≡A)
  inverseUnivEq′ (inj₁ ⊢A) (trans A≡C C≡B) =
    case inverseUnivEq′ (inj₁ ⊢A) A≡C of λ
      A≡C →
    case syntacticEqTerm A≡C of λ
      (_ , _ , ⊢C) →
    trans A≡C (inverseUnivEq′ (inj₁ ⊢C) C≡B)
  inverseUnivEq′ (inj₂ ⊢B) (trans A≡C C≡B) =
    case inverseUnivEq′ (inj₂ ⊢B) C≡B of λ
      C≡B →
    case syntacticEqTerm C≡B of λ
      (_ , ⊢C , _) →
    trans (inverseUnivEq′ (inj₂ ⊢C) A≡C) C≡B
  inverseUnivEq′ (inj₁ ⊢A) (U-cong l₁≡l₂) =
    conv (U-cong l₁≡l₂) (sym (inversion-U ⊢A))
  inverseUnivEq′ (inj₂ ⊢B) (U-cong l₁≡l₂) =
    conv (U-cong l₁≡l₂) (trans (U-cong (sucᵘ-cong l₁≡l₂)) (sym (inversion-U ⊢B)))
  inverseUnivEq′ (inj₁ ⊢A) (Lift-cong l₁≡l₂ A≡B) =
    let _ , ⊢l₂ , ⊢A , U≡U = inversion-Lift∷ ⊢A
    in conv
        (Lift-cong′ l₁≡l₂ (inverseUnivEq′ (inj₁ ⊢A) A≡B))
        (sym U≡U)
  inverseUnivEq′ (inj₂ ⊢B) (Lift-cong l₁≡l₂ A≡B) =
    let _ , ⊢l₂ , ⊢A , U≡U = inversion-Lift∷ ⊢B
        ⊢k                 = inversion-U-Level (syntacticTerm ⊢A)
    in conv
        (Lift-cong′ l₁≡l₂ (inverseUnivEq′ (inj₂ ⊢A) A≡B))
        (trans (U-cong-⊢≡ (supᵘₗ-cong (refl-⊢≡∷L ⊢k) l₁≡l₂)) (sym U≡U))
  inverseUnivEq′ (inj₁ ⊢ΠΣ) (ΠΣ-cong A₁≡A₂ B₁≡B₂ ok) =
    case inversion-ΠΣ-U ⊢ΠΣ of λ
      (_ , _ , ⊢A₁∷U , ⊢B₁∷U , U≡U , _) →
    conv
      (ΠΣ-cong′ (inverseUnivEq′ (inj₁ ⊢A₁∷U) A₁≡A₂)
         (inverseUnivEq′ (inj₁ ⊢B₁∷U) B₁≡B₂) ok)
      (sym U≡U)
  inverseUnivEq′ (inj₂ ⊢ΠΣ) (ΠΣ-cong A₁≡A₂ B₁≡B₂ ok) =
    case inversion-ΠΣ-U ⊢ΠΣ of λ
      (_ , _ , ⊢A₂∷U , ⊢B₂∷U , U≡U , _) →
    conv
      (ΠΣ-cong′ (inverseUnivEq′ (inj₂ ⊢A₂∷U) A₁≡A₂)
         (inverseUnivEq′
            (inj₂ $ stabilityTerm (refl-∙ (sym A₁≡A₂)) ⊢B₂∷U) B₁≡B₂) ok)
      (sym U≡U)
  inverseUnivEq′ (inj₁ ⊢Id) (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    case inversion-Id-U ⊢Id of λ
      (_ , ⊢A₁∷U , _ , _ , U≡U) →
    conv (Id-cong (inverseUnivEq′ (inj₁ ⊢A₁∷U) A₁≡A₂) t₁≡t₂ u₁≡u₂)
      (sym U≡U)
  inverseUnivEq′ (inj₂ ⊢Id) (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    case inversion-Id-U ⊢Id of λ
      (_ , ⊢A₂∷U , _ , _ , U≡U) →
    conv (Id-cong (inverseUnivEq′ (inj₂ ⊢A₂∷U) A₁≡A₂) t₁≡t₂ u₁≡u₂)
      (sym U≡U)

opaque

  -- If A is a term of type U l, then Γ ⊢ A ≡ B implies
  -- Γ ⊢ A ≡ B ∷ U l.

  inverseUnivEq : Γ ⊢ A ∷ U l → Γ ⊢ A ≡ B → Γ ⊢ A ≡ B ∷ U l
  inverseUnivEq = inverseUnivEq′ ∘→ inj₁

opaque

  -- If A has type U l and reduces to B, then A reduces to B at type
  -- U l.

  inverseUnivRed* : Γ ⊢ A ∷ U l → Γ ⊢ A ⇒* B → Γ ⊢ A ⇒* B ∷ U l
  inverseUnivRed* ⊢A (id _)            = id ⊢A
  inverseUnivRed* ⊢A (univ A⇒C ⇨ C⇒*B) =
    let l≡l′ = universe-level-unique (redFirstTerm A⇒C) ⊢A
        U≡U  = U-cong-⊢≡ l≡l′
    in
    conv A⇒C U≡U ⇨
    inverseUnivRed*
      (conv (syntacticRedTerm (redMany A⇒C) .proj₂ .proj₂) U≡U) C⇒*B
