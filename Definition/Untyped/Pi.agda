------------------------------------------------------------------------
-- Some definitions related to Π-types
------------------------------------------------------------------------

-- Typing rules for the terms given in this module can be found in
-- Definition.Typed.Properties.Admissible.Pi.

module Definition.Untyped.Pi {a} (M : Set a) where

open import Definition.Untyped M

open import Tools.Fin
open import Tools.Nat

private variable
  n : Nat

opaque

  -- Iterated Π-types.

  Πs : M → M → Con Term n → Term n → Term 0
  Πs p q ε       B = B
  Πs p q (Γ ∙ A) B = Πs p q Γ (Π p , q ▷ A ▹ B)

opaque

  -- Iterated lambdas.

  lams : M → Con Term n → Term n → Term 0
  lams p ε       t = t
  lams p (Γ ∙ _) t = lams p Γ (lam p t)

opaque

  -- Iterated applications.

  apps : M → Con Term n → Term 0 → Term n
  apps p ε       t = t
  apps p (Γ ∙ _) t = wk1 (apps p Γ t) ∘⟨ p ⟩ var x0
