{-# OPTIONS --without-K --safe #-}
module Erasure.Target.Properties.Weakening where

open import Erasure.Target renaming (refl to ⇒*-refl; trans to ⇒*-trans)

open import Tools.Fin
open import Tools.Nat
open import Tools.PropositionalEquality hiding (subst)
open import Tools.Reasoning.PropositionalEquality

private
  variable
    ℓ m n : Nat
    ρ ρ′ : Wk m n

-- Weakening properties

-- Two weakenings ρ and ρ′ are extensionally equal if they agree on
-- all arguments when interpreted as functions mapping variables to
-- variables.  Formally, they are considered equal iff
--
--   (∀ x → wkVar ρ x ≡ wkVar ρ′ x)
--
-- Intensional (propositional) equality would be too fine.  For
-- instance,
--
--   lift id : Γ∙A ≤ Γ∙A
--
-- is extensionally equal to
--
--   id : Γ∙A ≤ Γ∙A
--
-- but syntactically different.

-- "lift" preserves equality of weakenings.  Or:
-- If two weakenings are equal under wkVar, then they are equal when lifted.

wkVar-lift : (∀ x → wkVar ρ x ≡ wkVar ρ′ x)
           → (∀ x → wkVar (lift ρ) x ≡ wkVar (lift ρ′) x)
wkVar-lift eq x0     = refl
wkVar-lift eq (x +1) = cong _+1 (eq x)


-- Extensionally equal weakenings, if applied to a term,
-- yield the same weakened term.  Or:
-- If two weakenings are equal under wkVar, then they are equal under wk.

mutual
  wkVar-to-wk : (∀ x → wkVar ρ x ≡ wkVar ρ′ x)
              → ∀ (t : Term n) → wk ρ t ≡ wk ρ′ t
  wkVar-to-wk eq (var x) = cong var (eq x)
  wkVar-to-wk eq (lam t) = cong lam (wkVar-to-wk (wkVar-lift eq) t)
  wkVar-to-wk eq (t ∘ u) = cong₂ _∘_ (wkVar-to-wk eq t) (wkVar-to-wk eq u)
  wkVar-to-wk eq zero = refl
  wkVar-to-wk eq (suc t) = cong suc (wkVar-to-wk eq t)
  wkVar-to-wk eq (natrec z s n) = cong₃ natrec (wkVar-to-wk eq z) (wkVar-to-wk (wkVar-lift (wkVar-lift eq)) s) (wkVar-to-wk eq n)
  wkVar-to-wk eq (prod t u) = cong₂ prod (wkVar-to-wk eq t) (wkVar-to-wk eq u)
  wkVar-to-wk eq (fst t) = cong fst (wkVar-to-wk eq t)
  wkVar-to-wk eq (snd t) = cong snd (wkVar-to-wk eq t)
  wkVar-to-wk eq (prodrec t u) = cong₂ prodrec (wkVar-to-wk eq t) (wkVar-to-wk (wkVar-lift (wkVar-lift eq)) u)
  wkVar-to-wk eq star = refl
  wkVar-to-wk eq undefined = refl


-- lift id  is extensionally equal to  id.

wkVar-lift-id : (x : Fin (1+ n)) → wkVar (lift id) x ≡ wkVar id x
wkVar-lift-id x0     = refl
wkVar-lift-id (x +1) = refl

wkVar-lifts-id : (n : Nat) (x : Fin (n + m)) → wkVar (liftn id n) x ≡ wkVar id x
wkVar-lifts-id 0 x           = refl
wkVar-lifts-id (1+ n) x0     = refl
wkVar-lifts-id (1+ n) (x +1) = cong _+1 (wkVar-lifts-id n x)

-- id is the identity renaming.

wkVar-id : (x : Fin n) → wkVar id x ≡ x
wkVar-id x = refl

mutual
  wk-id : (t : Term n) → wk id t ≡ t
  wk-id (var x) = refl
  wk-id (lam t) = cong lam (trans (wkVar-to-wk wkVar-lift-id t) (wk-id t))
  wk-id (t ∘ u) = cong₂ _∘_ (wk-id t) (wk-id u)
  wk-id zero = refl
  wk-id (suc t) = cong suc (wk-id t)
  wk-id (natrec z s n) = cong₃ natrec (wk-id z) (trans (wkVar-to-wk (wkVar-lifts-id 2) s) (wk-id s)) (wk-id n)
  wk-id (prod t u) = cong₂ prod (wk-id t) (wk-id u)
  wk-id (fst t) = cong fst (wk-id t)
  wk-id (snd t) = cong snd (wk-id t)
  wk-id (prodrec t u) = cong₂ prodrec (wk-id t) (trans (wkVar-to-wk (wkVar-lifts-id 2) u) (wk-id u))
  wk-id star = refl
  wk-id undefined = refl

-- lift id  is also the identity renaming.

wk-lift-id : (t : Term (1+ n)) → wk (lift id) t ≡ t
wk-lift-id t = trans (wkVar-to-wk wkVar-lift-id t) (wk-id t)

-- The composition of weakenings is correct...
--
-- ...as action on variables.

wkVar-comp : (ρ : Wk m ℓ) (ρ′ : Wk ℓ n) (x : Fin n) → wkVar ρ (wkVar ρ′ x) ≡ wkVar (ρ • ρ′) x
wkVar-comp id       ρ′        x      = refl
wkVar-comp (step ρ) ρ′        x      = cong _+1 (wkVar-comp ρ ρ′ x)
wkVar-comp (lift ρ) id        x      = refl
wkVar-comp (lift ρ) (step ρ′) x      = cong _+1 (wkVar-comp ρ ρ′ x)
wkVar-comp (lift ρ) (lift ρ′) x0     = refl
wkVar-comp (lift ρ) (lift ρ′) (x +1) = cong _+1 (wkVar-comp ρ ρ′ x)

wkVar-comps : ∀ k → (ρ : Wk m ℓ) (ρ′ : Wk ℓ n) (x : Fin (k + n))
            → wkVar (liftn ρ k • liftn ρ′ k) x
            ≡ wkVar (liftn (ρ • ρ′) k) x
wkVar-comps 0      ρ ρ′ x      = refl
wkVar-comps (1+ n) ρ ρ′ x0     = refl
wkVar-comps (1+ n) ρ ρ′ (x +1) = cong _+1 (wkVar-comps n ρ ρ′ x)

-- ... as action on terms.

mutual
  wk-comp : (ρ : Wk m ℓ) (ρ′ : Wk ℓ n) (t : Term n) → wk ρ (wk ρ′ t) ≡ wk (ρ • ρ′) t
  wk-comp ρ ρ′ (var x) = cong var (wkVar-comp ρ ρ′ x)
  wk-comp ρ ρ′ (lam t) = cong lam (wk-comp (lift ρ) (lift ρ′) t)
  wk-comp ρ ρ′ (t ∘ u) = cong₂ _∘_ (wk-comp ρ ρ′ t) (wk-comp ρ ρ′ u)
  wk-comp ρ ρ′ zero = refl
  wk-comp ρ ρ′ (suc t) = cong suc (wk-comp ρ ρ′ t)
  wk-comp ρ ρ′ (natrec z s n) = cong₃ natrec (wk-comp ρ ρ′ z) (wk-comp (lift (lift ρ)) (lift (lift ρ′)) s) (wk-comp ρ ρ′ n)
  wk-comp ρ ρ′ (prod t u) = cong₂ prod (wk-comp ρ ρ′ t) (wk-comp ρ ρ′ u)
  wk-comp ρ ρ′ (fst t) = cong fst (wk-comp ρ ρ′ t)
  wk-comp ρ ρ′ (snd t) = cong snd (wk-comp ρ ρ′ t)
  wk-comp ρ ρ′ (prodrec t u) = cong₂ prodrec (wk-comp ρ ρ′ t) (wk-comp (lift (lift ρ)) (lift (lift ρ′)) u)
  wk-comp ρ ρ′ star = refl
  wk-comp ρ ρ′ undefined = refl



-- The following lemmata are variations on the equality
--
--   wk1 ∘ ρ = lift ρ ∘ wk1.
--
-- Typing:  Γ∙A ≤ Γ ≤ Δ  <==>  Γ∙A ≤ Δ∙A ≤ Δ.

lift-step-comp : (ρ : Wk m n) → step id • ρ ≡ lift ρ • step id
lift-step-comp id       = refl
lift-step-comp (step ρ) = cong step (lift-step-comp ρ)
lift-step-comp (lift ρ) = refl

wk1-wk : (ρ : Wk m n) (t : Term n) → wk1 (wk ρ t) ≡ wk (step ρ) t
wk1-wk ρ t = wk-comp (step id) ρ t

lift-wk1 : (ρ : Wk m n) (t : Term n) → wk (lift ρ) (wk1 t) ≡ wk (step ρ) t
lift-wk1 pr A = trans (wk-comp (lift pr) (step id) A)
                      (sym (cong (λ x → wk x A) (lift-step-comp pr)))

wk1-wk≡lift-wk1 : (ρ : Wk m n) (t : Term n) → wk1 (wk ρ t) ≡ wk (lift ρ) (wk1 t)
wk1-wk≡lift-wk1 ρ t = trans (wk1-wk ρ t) (sym (lift-wk1 ρ t))
