------------------------------------------------------------------------
-- A non-terminating term
------------------------------------------------------------------------

module Graded.Erasure.Target.Non-terminating where

open import Definition.Untyped.NotParametrised

open import Graded.Erasure.Target
open import Graded.Erasure.Target.Properties

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation

private variable
  n   : Nat
  x   : Fin _
  t v : Term _
  s   : Strictness
  ρ   : Wk _ _
  σ   : Subst _ _

opaque

  -- A non-terminating term (which uses applications with the given
  -- strictness).

  loop : Strictness → Term n
  loop s = ω ∘⟨ s ⟩ ω
    where
    ω : Term n
    ω = lam (var x0 ∘⟨ s ⟩ var x0)

opaque
  unfolding loop

  -- The term loop s reduces in one step to itself.

  loop⇒loop : (Term n ∋ loop s) ⇒ loop s
  loop⇒loop = β-red (Value→Value⟨⟩ lam)

opaque

  -- The term loop s only reduces to terms that can reduce further.

  loop-reduces-forever : loop s ⇒* t → ∃ λ u → t ⇒ u
  loop-reduces-forever refl =
    _ , loop⇒loop
  loop-reduces-forever (trans nt⇒t t⇒*u)
    rewrite sym $ redDet _ loop⇒loop nt⇒t =
    loop-reduces-forever t⇒*u

opaque

  -- The term loop s does not reduce to a value.

  ¬loop⇒* : Value v → ¬ loop s ⇒* v
  ¬loop⇒* {v} {s} v-val =
    loop s ⇒* v        →⟨ loop-reduces-forever ⟩
    (∃ λ v′ → v ⇒ v′)  →⟨ Value→¬⇒ v-val ∘→ proj₂ ⟩
    ⊥                  □

opaque
  unfolding loop

  -- The term loop s is closed.

  loop-closed : ¬ HasX x (loop s)
  loop-closed (∘ₓˡ (lamₓ (∘ₓˡ ())))
  loop-closed (∘ₓˡ (lamₓ (∘ₓʳ ())))
  loop-closed (∘ₓʳ (lamₓ (∘ₓˡ ())))
  loop-closed (∘ₓʳ (lamₓ (∘ₓʳ ())))

opaque
  unfolding loop

  -- The result of weakening loop s is loop s.

  wk-loop : wk ρ (loop s) ≡ loop s
  wk-loop = refl

opaque
  unfolding loop

  -- The result of applying a substitution to loop s is loop s.

  loop-[] : loop s [ σ ] ≡ loop s
  loop-[] = refl
