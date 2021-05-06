{-# OPTIONS --without-K --safe #-}
module Erasure.Target.Properties.Reduction where

open import Erasure.Target --renaming (refl to ⇒*-refl; trans to ⇒*-trans)

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Sum


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



-- Reduction is deterministic
-- If a ⇒ b and a ⇒ c then b ≡ c

redDet : (a : Term n) {b c : Term n} → a ⇒ b → a ⇒ c → b PE.≡ c
redDet (var x) () a⇒c
redDet (lam a) () a⇒c
redDet (a ∘ a₁) (app-subst a⇒b) (app-subst a⇒c) = PE.cong₂ _∘_ (redDet a a⇒b a⇒c) PE.refl
redDet (.(lam _) ∘ a) β-red β-red = PE.refl
redDet zero () a⇒c
redDet (suc a) () a⇒c
redDet (natrec a a₁ a₂) (natrec-subst a⇒b) (natrec-subst a⇒c) = PE.cong (natrec a a₁) (redDet a₂ a⇒b a⇒c)
redDet (natrec a a₁ .zero) natrec-zero natrec-zero = PE.refl
redDet (natrec a a₁ .(suc _)) natrec-suc natrec-suc = PE.refl
redDet (prod a a₁) () a⇒c
redDet (fst a) (fst-subst a⇒b) (fst-subst a⇒c) = PE.cong fst (redDet a a⇒b a⇒c)
redDet (fst .(prod _ _)) Σ-β₁ Σ-β₁ = PE.refl
redDet (snd a) (snd-subst a⇒b) (snd-subst a⇒c) = PE.cong snd (redDet a a⇒b a⇒c)
redDet (snd .(prod _ _)) Σ-β₂ Σ-β₂ = PE.refl
redDet (prodrec a a₁) (prodrec-subst a⇒b) (prodrec-subst a⇒c) = PE.cong (λ z → prodrec z a₁) (redDet a a⇒b a⇒c)
redDet (prodrec .(prod _ _) a) prodrec-β prodrec-β = PE.refl
redDet star () a⇒c
redDet undefined () a⇒c

-- Reduction closure is deterministic
-- If a ⇒* b and a ⇒* c then b ⇒* c or c ⇒* b

red*Det : {a b c : Term n} → a ⇒* b → a ⇒* c → (b ⇒* c) ⊎ (c ⇒* b)
red*Det refl refl = inj₁ refl
red*Det refl (trans x a⇒c) = inj₁ (trans x a⇒c)
red*Det (trans x a⇒b) refl = inj₂ (trans x a⇒b)
red*Det {a = a} (trans x a⇒b) (trans x₁ a⇒c) rewrite redDet a x x₁ = red*Det a⇒b a⇒c
