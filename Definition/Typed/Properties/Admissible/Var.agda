------------------------------------------------------------------------
-- Some admissible typing rules related to variables
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Var
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Typed R

open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.PropositionalEquality

private variable
  Γ           : Cons _ _
  A B C D E F : Term _

opaque

  -- A typing rule for variable 0.

  var₀ :
    Γ ⊢ A →
    Γ »∙ A ⊢ var x0 ∷ wk1 A
  var₀ ⊢A = var (∙ ⊢A) here

opaque

  -- A typing rule for variable 1.

  var₁ :
    Γ »∙ A ⊢ B →
    Γ »∙ A »∙ B ⊢ var x1 ∷ wk[ 2 ] A
  var₁ ⊢B = var (∙ ⊢B) (there here)

opaque

  -- A typing rule for variable 1.

  var₁′ :
    Γ »∙ A ⊢ B →
    Γ »∙ A »∙ B ⊢ var x1 ∷ wk[ 2 ]′ A
  var₁′ = subst (_⊢_∷_ _ _) wk[]≡wk[]′ ∘→ var₁

opaque

  -- A typing rule for variable 2.

  var₂ :
    Γ »∙ A »∙ B ⊢ C →
    Γ »∙ A »∙ B »∙ C ⊢ var x2 ∷ wk[ 3 ] A
  var₂ ⊢C = var (∙ ⊢C) (there (there here))

opaque

  -- A typing rule for variable 2.

  var₂′ :
    Γ »∙ A »∙ B ⊢ C →
    Γ »∙ A »∙ B »∙ C ⊢ var x2 ∷ wk[ 3 ]′ A
  var₂′ = subst (_⊢_∷_ _ _) wk[]≡wk[]′ ∘→ var₂

opaque

  -- A typing rule for variable 3.

  var₃ :
    Γ »∙ A »∙ B »∙ C ⊢ D →
    Γ »∙ A »∙ B »∙ C »∙ D ⊢ var x3 ∷ wk[ 4 ] A
  var₃ ⊢D = var (∙ ⊢D) (there (there (there here)))

opaque

  -- A typing rule for variable 3.

  var₃′ :
    Γ »∙ A »∙ B »∙ C ⊢ D →
    Γ »∙ A »∙ B »∙ C »∙ D ⊢ var x3 ∷ wk[ 4 ]′ A
  var₃′ = subst (_⊢_∷_ _ _) wk[]≡wk[]′ ∘→ var₃

opaque

  -- A typing rule for variable 4.

  var₄ :
    Γ »∙ A »∙ B »∙ C »∙ D ⊢ E →
    Γ »∙ A »∙ B »∙ C »∙ D »∙ E ⊢ var x4 ∷ wk[ 5 ] A
  var₄ ⊢E = var (∙ ⊢E) (there (there (there (there here))))

opaque

  -- A typing rule for variable 4.

  var₄′ :
    Γ »∙ A »∙ B »∙ C »∙ D ⊢ E →
    Γ »∙ A »∙ B »∙ C »∙ D »∙ E ⊢ var x4 ∷ wk[ 5 ]′ A
  var₄′ = subst (_⊢_∷_ _ _) wk[]≡wk[]′ ∘→ var₄

opaque

  -- A typing rule for variable 5.

  var₅ :
    Γ »∙ A »∙ B »∙ C »∙ D »∙ E ⊢ F →
    Γ »∙ A »∙ B »∙ C »∙ D »∙ E »∙ F ⊢ var x5 ∷ wk[ 6 ] A
  var₅ ⊢F = var (∙ ⊢F) (there (there (there (there (there here)))))

opaque

  -- A typing rule for variable 5.

  var₅′ :
    Γ »∙ A »∙ B »∙ C »∙ D »∙ E ⊢ F →
    Γ »∙ A »∙ B »∙ C »∙ D »∙ E »∙ F ⊢ var x5 ∷ wk[ 6 ]′ A
  var₅′ = subst (_⊢_∷_ _ _) wk[]≡wk[]′ ∘→ var₅
