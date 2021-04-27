{-# OPTIONS --without-K --safe #-}

module Definition.Target where

open import Tools.Fin
open import Tools.Nat

infixl 25 _[_]
infixl 25 _[_,_]
infix 10 _⇒_

private
  variable
    m n : Nat

-- Terms of the target language:
-- A lambda calculus extended with natural numbers, products and unit

data Term : Nat → Set where
  var       : (x : Fin n) → Term n
  lam       : (t : Term (1+ n)) → Term n
  _∘_       : (t u : Term n) → Term n
  zero      : Term n
  suc       : (t : Term n) → Term n
  natrec    : (z : Term m) (s : Term (1+ (1+ m))) (n : Term m) → Term m
  prod      : (t u : Term n) → Term n
  fst       : (t : Term n) → Term n
  snd       : (t : Term n) → Term n
  prodrec   : (t : Term n) (u : Term (1+ (1+ n))) → Term n
  star      : Term n
  undefined : Term n

private
  variable
    s t t′ u z : Term n

-- Weakenings in the same style as the source language

data Wk : (m n : Nat) → Set where
  id   : Wk n n
  step : (ρ : Wk m n) → Wk (1+ m) n
  lift : (ρ : Wk m n) → Wk (1+ m) (1+ n)

-- Weakening of variables

wkVar : (ρ : Wk m n) → (x : Fin n) → Fin m
wkVar id x = x
wkVar (step ρ) x = (wkVar ρ x) +1
wkVar (lift ρ) x0 = x0
wkVar (lift ρ) (x +1) = (wkVar ρ x) +1

-- Weakening of terms

wk : (ρ : Wk m n) → (t : Term n) → Term m
wk ρ (var x) = var (wkVar ρ x)
wk ρ (lam t) = lam (wk (lift ρ) t)
wk ρ (t ∘ u) = wk ρ t ∘ wk ρ t
wk ρ zero = zero
wk ρ (suc t) = suc (wk ρ t)
wk ρ (natrec z s n) = natrec (wk ρ z) (wk (lift (lift ρ)) s) (wk ρ n)
wk ρ (prod t u) = prod (wk ρ t) (wk ρ u)
wk ρ (fst t) = fst (wk ρ t)
wk ρ (snd t) = snd (wk ρ t)
wk ρ (prodrec t u) = prodrec (wk ρ t) (wk (lift (lift ρ)) u)
wk ρ star = star
wk ρ undefined = undefined

-- Shift all variables in a term up by one

wk1 : Term n → Term (1+ n)
wk1 = wk (step id)

-- Substitutions are finite maps from variables to terms

Subst : (m n : Nat) → Set
Subst m n = Fin n → Term m

-- Identity substitution

idSubst : Subst n n
idSubst = var

-- Substitution with indices shifted up by one

wk1Subst : Subst m n → Subst (1+ m) n
wk1Subst σ x = wk1 (σ x)

-- Lifted substitution

liftSubst : (σ : Subst m n) → Subst (1+ m) (1+ n)
liftSubst σ x0 = var x0
liftSubst σ (x +1) = wk1Subst σ x

-- Extend a substitution σ with a term t, substituting x0 with t
-- and remaining variables by σ.

consSubst : (σ : Subst m n) → (t : Term m) → Subst m (1+ n)
consSubst σ t x0 = t
consSubst σ t (x +1) = σ x

-- Apply a substitution to a term

subst : (σ : Subst m n) → (t : Term n) → Term m
subst σ (var x) = σ x
subst σ (lam t) = lam (subst (liftSubst σ) t)
subst σ (t ∘ u) = subst σ t ∘ subst σ u
subst σ zero = zero
subst σ (suc t) = suc (subst σ t)
subst σ (natrec z s n) = natrec (subst σ z) (subst (liftSubst (liftSubst σ)) s) (subst σ n)
subst σ (prod t u) = prod (subst σ t) (subst σ u)
subst σ (fst t) = fst (subst σ t)
subst σ (snd t) = snd (subst σ t)
subst σ (prodrec t u) = prodrec (subst σ t) (subst (liftSubst (liftSubst σ)) u)
subst σ star = star
subst σ undefined = undefined

-- Substitute the first variable of a term with an other term.

_[_] : (t : Term (1+ n)) → (s : Term n) → Term n
t [ u ] = subst (consSubst idSubst u) t

-- Substitute the first two variables of a term with other terms.

_[_,_] : (t : Term (1+ (1+ n))) → (u v : Term n) → Term n
t [ u , v ] = subst (consSubst (consSubst idSubst u) v) t

-- Strengthening of terms.
-- Strengthenings are constructed similarily to weakenings.

data Str : (m n : Nat) → Set where
  id   : Str n n                     -- The identity strengthening
  step : Str m n → Str m (1+ n)      -- Removes x0 by substituting it with undefined and shifting remaining indices down
  lift : Str m n → Str (1+ m) (1+ n) -- Lifts a strengthening ρ by leaving x0 intact and applying ρ to all other

-- Strengthening of variables

strVar : Str m n → Fin n → Term m
strVar id x = var x
strVar (step ρ) x0 = undefined
strVar (step ρ) (_+1 x) = strVar ρ x
strVar (lift ρ) x0 = var x0
strVar (lift ρ) (x +1) = wk1 (strVar ρ x)

-- Strengthening of terms

str : Str m n → Term n → Term m
str ρ t = subst (strVar ρ) t


-- Single-step reduction relation

data _⇒_ : (t u : Term n) → Set where
  app-subst       : t ⇒ t′ → t ∘ u ⇒ t′ ∘ u
  β-red           : (lam t) ∘ u ⇒ t [ u ]
  fst-subst       : t ⇒ t′ → fst t ⇒ fst t′
  snd-subst       : t ⇒ t′ → snd t ⇒ snd t′
  Σ-β₁            : fst (prod t u) ⇒ t
  Σ-β₂            : snd (prod t u) ⇒ u
  prodrec-subst   : t ⇒ t′ → prodrec t u ⇒ prodrec t′ u
  prodrec-β       : prodrec (prod t t′) u ⇒ u [ t , t′ ]
  natrec-subst    : t ⇒ t′ → natrec z s t ⇒ natrec z s t′
  natrec-zero     : natrec z s zero ⇒ z
  natrec-suc      : natrec z s (suc t) ⇒ s [ t , natrec z s t ]

-- Reflexive transitive closure of reduction relation

data _⇒*_ : (t u : Term n) → Set where
  refl : t ⇒* t
  trans : t ⇒ t′ → t′ ⇒* u → t ⇒* u
