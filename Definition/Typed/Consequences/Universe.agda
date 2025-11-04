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
open import Definition.Typed.Properties R
open import Definition.Typed.Substitution R
open import Definition.Typed.Consequences.Injectivity R

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Relation

private variable
  l   : Term _
  Γ   : Con _ _
  p q : M

opaque

  -- It is not the case that U l has type U l (assuming that the
  -- context is empty or equality reflection is disallowed).

  ¬U∷U :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    ¬ Γ ⊢ U l ∷ U l
  ¬U∷U U∷U =
    t≢sucᵘt (U-injectivity (inversion-U U∷U))

opaque

  -- Type-in-type for arbitrary well-formed levels does not hold in a
  -- well-formed context Γ (assuming that Γ is empty or equality
  -- reflection is disallowed): it is not the case that, given a
  -- well-formed level l, U l has type U l.

  no-type-in-type :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    ⊢ Γ →
    ¬ (∀ {l} → Γ ⊢ l ∷ Level → Γ ⊢ U l ∷ U l)
  no-type-in-type ⊢Γ U∷U =
    ¬U∷U (U∷U (zeroᵘⱼ ⊢Γ))

opaque

  -- For any context Γ there is a type that
  --
  -- * is well-formed if Γ is and a certain form of Π-type is allowed,
  --
  -- * does not have a type, and
  --
  -- * consequently does not live in any universe
  --
  -- (assuming that Γ is empty or equality reflection is not allowed).

  ¬ΠU∷U :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    let A = Π p , q ▷ Level ▹ U (var x0) in
    (Π-allowed p q → ⊢ Γ → Γ ⊢ A) ×
    (¬ ∃ λ B → Γ ⊢ A ∷ B) ×
    (¬ ∃ λ l → Γ ⊢ A ∷ U l)
  ¬ΠU∷U =
    let ¬⊢∷ = λ (_ , ⊢A) →
          let _ , ⊢l , _ , ⊢U , _ , _ = inversion-ΠΣ-U ⊢A in
          ¬U∷U $
          PE.subst (_⊢_∷_ _ _) (wk1-sgSubst _ _) (substTerm ⊢U ⊢l)
    in
    (λ ok ⊢Γ → ΠΣⱼ (⊢U (var₀ (Levelⱼ′ ⊢Γ))) ok) ,
    ¬⊢∷ ,
    ¬⊢∷ ∘→ Σ.map _ idᶠ
