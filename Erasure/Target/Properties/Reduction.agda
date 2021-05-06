{-# OPTIONS --without-K --safe #-}
module Erasure.Target.Properties.Reduction where

open import Erasure.Target --renaming (refl to ⇒*-refl; trans to ⇒*-trans)

open import Tools.Nat
import Tools.PropositionalEquality as PE


private
  variable
    n : Nat
    t t′ u : Term n

-- Reduction properties

-- Concatenation of reduction closure

red*concat : t ⇒* t′ → t′ ⇒* u → t ⇒* u
red*concat refl t′⇒*u = t′⇒*u
red*concat (trans x t⇒*t′) t′⇒*u = trans x (red*concat t⇒*t′ t′⇒*u)

-- Closure of substitution reductions

app-subst* : t ⇒* t′ → (t ∘ u) ⇒* (t′ ∘ u)
app-subst* refl = refl
app-subst* (trans x t⇒*t′) = trans (app-subst x) (app-subst* t⇒*t′)

fst-subst* : t ⇒* t′ → fst t ⇒* fst t′
fst-subst* refl = refl
fst-subst* (trans x t⇒*t′) = trans (fst-subst x) (fst-subst* t⇒*t′)

snd-subst* : t ⇒* t′ → snd t ⇒* snd t′
snd-subst* refl = refl
snd-subst* (trans x t⇒*t′) = trans (snd-subst x) (snd-subst* t⇒*t′)
