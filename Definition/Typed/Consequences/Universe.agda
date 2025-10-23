------------------------------------------------------------------------
-- Some results about universes
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.Universe
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Definition.Typed R
open import Definition.Typed.Consequences.Inequality R
open import Definition.Typed.Inversion R
open import Definition.Typed.Substitution R
open import Definition.Typed.Consequences.Injectivity R

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Relation

private
  variable
    n       : Nat
    A t u v : Term _
    Γ       : Con _ _
    p q     : M

opaque

  -- No type-in-type: U t is not an element of itself (assuming no
  -- equality reflection).

  ¬U∷U :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    ¬ Γ ⊢ U t ∷ U t
  ¬U∷U U∷U =
    t≢sucᵘt (U-injectivity (inversion-U U∷U))

opaque

  -- Certain types do not live in any universe (assuming no equality
  -- reflection).

  ¬ΠU∷U :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    ¬ Γ ⊢ Π p , q ▷ Level ▹ U (var x0) ∷ U t
  ¬ΠU∷U ΠU∷U =
    case inversion-ΠΣ-U ΠU∷U of λ
      (l , ⊢l , _ , x , y , z) →
    ¬U∷U (PE.subst (_⊢_∷_ _ _) (wk1-sgSubst _ _) (substTerm x ⊢l))
