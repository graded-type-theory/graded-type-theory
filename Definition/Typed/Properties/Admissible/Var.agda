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

open import Tools.Fin

private variable
  ∇           : DCon (Term 0) _
  Γ           : Con Term _
  A B C D E F : Term _

opaque

  -- A typing rule for variable 0.

  var₀ : ∇ » Γ ⊢ A → ∇ » Γ ∙ A ⊢ var x0 ∷ wk1 A
  var₀ ⊢A = var (∙ ⊢A) here

opaque

  -- A typing rule for variable 1.

  var₁ : ∇ » Γ ∙ A ⊢ B → ∇ » Γ ∙ A ∙ B ⊢ var x1 ∷ wk1 (wk1 A)
  var₁ ⊢B = var (∙ ⊢B) (there here)

opaque

  -- A typing rule for variable 2.

  var₂ : ∇ » Γ ∙ A ∙ B ⊢ C → ∇ » Γ ∙ A ∙ B ∙ C ⊢ var x2 ∷ wk1 (wk1 (wk1 A))
  var₂ ⊢C = var (∙ ⊢C) (there (there here))

opaque

  -- A typing rule for variable 3.

  var₃ :
    ∇ » Γ ∙ A ∙ B ∙ C ⊢ D →
    ∇ » Γ ∙ A ∙ B ∙ C ∙ D ⊢ var x3 ∷ wk1 (wk1 (wk1 (wk1 A)))
  var₃ ⊢D = var (∙ ⊢D) (there (there (there here)))

opaque

  -- A typing rule for variable 4.

  var₄ :
    ∇ » Γ ∙ A ∙ B ∙ C ∙ D ⊢ E →
    ∇ » Γ ∙ A ∙ B ∙ C ∙ D ∙ E ⊢ var x4 ∷ wk1 (wk1 (wk1 (wk1 (wk1 A))))
  var₄ ⊢E = var (∙ ⊢E) (there (there (there (there here))))

opaque

  -- A typing rule for variable 5.

  var₅ :
    ∇ » Γ ∙ A ∙ B ∙ C ∙ D ∙ E ⊢ F →
    ∇ » Γ ∙ A ∙ B ∙ C ∙ D ∙ E ∙ F ⊢ var x5 ∷
      wk1 (wk1 (wk1 (wk1 (wk1 (wk1 A)))))
  var₅ ⊢F = var (∙ ⊢F) (there (there (there (there (there here)))))
