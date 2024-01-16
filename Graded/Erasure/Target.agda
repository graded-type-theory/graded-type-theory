------------------------------------------------------------------------
-- The untyped target language.
------------------------------------------------------------------------

module Graded.Erasure.Target where

open import Tools.Fin
open import Tools.Nat
import Tools.PropositionalEquality as PE

infixl 30 _∘_
infixl 25 _[_]
infixl 25 _[_,_]
infixl 25 _[_]₀
infix 10 _⇒_

private
  variable
    ℓ m n : Nat

-- Terms of the target language:
-- A lambda calculus extended with natural numbers, products, unit
-- and an undefined value.

data Term : Nat → Set where
  var     : (x : Fin n) → Term n
  lam     : (t : Term (1+ n)) → Term n
  _∘_     : (t u : Term n) → Term n
  prod    : (t u : Term n) → Term n
  fst     : (t : Term n) → Term n
  snd     : (t : Term n) → Term n
  prodrec : (t : Term n) (u : Term (2+ n)) → Term n
  zero    : Term n
  suc     : (t : Term n) → Term n
  natrec  : (z : Term m) (s : Term (2+ m)) (n : Term m) → Term m
  star    : Term n
  unitrec : (t u : Term n) → Term n
  rfl     : Term n
  ↯       : Term n

private
  variable
    s t t′ u z : Term n

-- Does a term contain a variable?

data HasX (x : Fin n) : (t : Term n) → Set where
  varₓ : HasX x (var x)
  lamₓ : HasX (x +1) t → HasX x (lam t)
  ∘ₓˡ : HasX x t → HasX x (t ∘ u)
  ∘ₓʳ : HasX x u → HasX x (t ∘ u)
  sucₓ : HasX x t → HasX x (suc t)
  natrecₓᶻ : HasX x z → HasX x (natrec z s t)
  natrecₓˢ : HasX (x +2) s → HasX x (natrec z s t)
  natrecₓⁿ : HasX x t → HasX x (natrec z s t)
  prodₓˡ : HasX x t → HasX x (prod t u)
  prodₓʳ : HasX x u → HasX x (prod t u)
  fstₓ : HasX x t → HasX x (fst t)
  sndₓ : HasX x t → HasX x (snd t)
  prodrecₓˡ : HasX x t → HasX x (prodrec t u)
  prodrecₓʳ : HasX (x +2) u → HasX x (prodrec t u)
  unitrecₓˡ : HasX x t → HasX x (unitrec t u)
  unitrecₓʳ : HasX x u → HasX x (unitrec t u)

-- Weakenings in the same style as the source language

data Wk : (m n : Nat) → Set where
  id   : Wk n n
  step : (ρ : Wk m n) → Wk (1+ m) n
  lift : (ρ : Wk m n) → Wk (1+ m) (1+ n)

-- Composition of weakenings

_•_ : (ρ : Wk m n) → (ρ′ : Wk n ℓ) → Wk m ℓ
id • ρ′ = ρ′
step ρ • ρ′ = step (ρ • ρ′)
lift ρ • id = lift ρ
lift ρ • step ρ′ = step (ρ • ρ′)
lift ρ • lift ρ′ = lift (ρ • ρ′)

liftn : (ρ : Wk ℓ m) → (n : Nat) → Wk (n + ℓ) (n + m)
liftn ρ 0 = ρ
liftn ρ (1+ n) = lift (liftn ρ n)

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
wk ρ (t ∘ u) = wk ρ t ∘ wk ρ u
wk ρ zero = zero
wk ρ (suc t) = suc (wk ρ t)
wk ρ (natrec z s n) = natrec (wk ρ z) (wk (lift (lift ρ)) s) (wk ρ n)
wk ρ (prod t u) = prod (wk ρ t) (wk ρ u)
wk ρ (fst t) = fst (wk ρ t)
wk ρ (snd t) = snd (wk ρ t)
wk ρ (prodrec t u) = prodrec (wk ρ t) (wk (lift (lift ρ)) u)
wk ρ star = star
wk ρ (unitrec t u) = unitrec (wk ρ t) (wk ρ u)
wk _ rfl = rfl
wk ρ ↯ = ↯

-- Shift all variables in a term up by one

wk1 : Term n → Term (1+ n)
wk1 = wk (step id)

-- Substitutions are finite maps from variables to terms

Subst : (m n : Nat) → Set
Subst m n = Fin n → Term m

-- Extract the substitution of the first variable.
--
-- If Γ ⊢ σ : Δ∙A  then Γ ⊢ head σ : subst σ A.

head : Subst m (1+ n) → Term m
head σ = σ x0

-- Remove the first variable instance of a substitution
-- and shift the rest to accommodate.
--
-- If Γ ⊢ σ : Δ∙A then Γ ⊢ tail σ : Δ.

tail : Subst m (1+ n) → Subst m n
tail σ x = σ (x +1)

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

liftSubstn : (σ : Subst ℓ m) → (n : Nat) → Subst (n + ℓ) (n + m)
liftSubstn σ 0 = σ
liftSubstn σ (1+ n) = liftSubst (liftSubstn σ n)


-- Extend a substitution σ with a term t, substituting x0 with t
-- and remaining variables by σ.

consSubst : (σ : Subst m n) → (t : Term m) → Subst m (1+ n)
consSubst σ t x0 = t
consSubst σ t (x +1) = σ x

sgSubst : (t : Term n) → Subst n (1+ n)
sgSubst = consSubst idSubst

toSubst : (ρ : Wk m n) → Subst m n
toSubst ρ x = var (wkVar ρ x)

-- Apply a substitution to a term

_[_] : (t : Term n) → (σ : Subst m n) → Term m
var x        [ σ ] = σ x
lam t        [ σ ] = lam (t [ liftSubst σ ])
(t ∘ u)      [ σ ] = (t [ σ ]) ∘ (u [ σ ])
prod t u     [ σ ] = prod (t [ σ ]) (u [ σ ])
fst t        [ σ ] = fst (t [ σ ])
snd t        [ σ ] = snd (t [ σ ])
prodrec t u  [ σ ] = prodrec (t [ σ ]) (u [ liftSubstn σ 2 ])
zero         [ σ ] = zero
suc t        [ σ ] = suc (t [ σ ])
natrec z s n [ σ ] = natrec (z [ σ ]) (s [ liftSubstn σ 2 ]) (n [ σ ])
star         [ σ ] = star
unitrec t u  [ σ ] = unitrec (t [ σ ]) (u [ σ ])
rfl          [ _ ] = rfl
↯            [ σ ] = ↯

-- Compose two substitutions.

_ₛ•ₛ_ : Subst ℓ m → Subst m n → Subst ℓ n
_ₛ•ₛ_ σ σ′ x = (σ′ x) [ σ ]

-- Composition of weakening and substitution.

_•ₛ_ : Wk ℓ m → Subst m n → Subst ℓ n
_•ₛ_ ρ σ x = wk ρ (σ x)

_ₛ•_ : Subst ℓ m → Wk m n → Subst ℓ n
_ₛ•_ σ ρ x = σ (wkVar ρ x)


-- Substitute the first variable of a term with an other term.

_[_]₀ : (t : Term (1+ n)) → (s : Term n) → Term n
t [ u ]₀ = t [ sgSubst u ]

-- Substitute the first two variables of a term with other terms.

_[_,_] : (t : Term (2+ n)) → (u v : Term n) → Term n
t [ u , v ] = t [ consSubst (sgSubst u) v ]


-- Single-step reduction relation

data _⇒_ : (t u : Term n) → Set where
  app-subst       : t ⇒ t′ → t ∘ u ⇒ t′ ∘ u
  β-red           : (lam t) ∘ u ⇒ t [ u ]₀
  fst-subst       : t ⇒ t′ → fst t ⇒ fst t′
  snd-subst       : t ⇒ t′ → snd t ⇒ snd t′
  Σ-β₁            : fst (prod t u) ⇒ t
  Σ-β₂            : snd (prod t u) ⇒ u
  prodrec-subst   : t ⇒ t′ → prodrec t u ⇒ prodrec t′ u
  prodrec-β       : prodrec (prod t t′) u ⇒ u [ t , t′ ]
  natrec-subst    : t ⇒ t′ → natrec z s t ⇒ natrec z s t′
  natrec-zero     : natrec z s zero ⇒ z
  natrec-suc      : natrec z s (suc t) ⇒ s [ t , natrec z s t ]
  unitrec-subst   : t ⇒ t′ → unitrec t u ⇒ unitrec t′ u
  unitrec-β       : unitrec star u ⇒ u

-- Reflexive transitive closure of reduction relation

data _⇒*_ : (t u : Term n) → Set where
  refl : t ⇒* t
  trans : t ⇒ t′ → t′ ⇒* u → t ⇒* u
