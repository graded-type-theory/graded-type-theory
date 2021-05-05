{-# OPTIONS --without-K --safe #-}
module Erasure.Target.Properties where

open import Erasure.Target hiding (refl; trans)

open import Tools.Fin
open import Tools.Nat
open import Tools.PropositionalEquality hiding (subst)
open import Tools.Reasoning.PropositionalEquality

private
  variable
    ℓ m n : Nat
    ρ ρ′ : Wk m n
    σ σ′ : Subst m n

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

-- Substitution properties.

-- Two substitutions σ and σ′ are equal if they are pointwise equal,
-- i.e., agree on all variables.
--
--   ∀ x →  σ x ≡ σ′ x

-- If  σ = σ′  then  lift σ = lift σ′.

substVar-lift : (∀ x → σ x ≡ σ′ x) → ∀ x → liftSubst σ x ≡ liftSubst σ′ x

substVar-lift eq x0     = refl
substVar-lift eq (x +1) = cong wk1 (eq x)

substVar-lifts : (∀ x → σ x ≡ σ′ x) → ∀ n x → liftSubstn σ n x ≡ liftSubstn σ′ n x

substVar-lifts eq 0 x           = eq x
substVar-lifts eq (1+ n) x0     = refl
substVar-lifts eq (1+ n) (x +1) = cong wk1 (substVar-lifts eq n x)

-- If  σ = σ′  then  subst σ t = subst σ′ t.

mutual
  substVar-to-subst : ((x : Fin n) → σ x ≡ σ′ x)
                    → (t : Term n) → subst σ t ≡ subst σ′ t
  substVar-to-subst eq (var x) = eq x
  substVar-to-subst eq (lam t) = cong lam (substVar-to-subst (substVar-lift eq) t)
  substVar-to-subst eq (t ∘ u) = cong₂ _∘_ (substVar-to-subst eq t) (substVar-to-subst eq u)
  substVar-to-subst eq zero = refl
  substVar-to-subst eq (suc t) = cong suc (substVar-to-subst eq t)
  substVar-to-subst eq (natrec z s n) = cong₃ natrec (substVar-to-subst eq z) (substVar-to-subst (substVar-lifts eq 2) s) (substVar-to-subst eq n)
  substVar-to-subst eq (prod t u) = cong₂ prod (substVar-to-subst eq t) (substVar-to-subst eq u)
  substVar-to-subst eq (fst t) = cong fst (substVar-to-subst eq t)
  substVar-to-subst eq (snd t) = cong snd (substVar-to-subst eq t)
  substVar-to-subst eq (prodrec t u) = cong₂ prodrec (substVar-to-subst eq t) (substVar-to-subst (substVar-lifts eq 2) u)
  substVar-to-subst eq star = refl
  substVar-to-subst eq undefined = refl


-- lift id = id  (as substitutions)

subst-lift-id : (x : Fin (1+ n)) → (liftSubst idSubst) x ≡ idSubst x
subst-lift-id x0     = refl
subst-lift-id (x +1) = refl

subst-lifts-id : (n : Nat) → (x : Fin (n + m)) → (liftSubstn idSubst n) x ≡ idSubst x
subst-lifts-id 0 x = refl
subst-lifts-id (1+ n) x0 = refl
subst-lifts-id (1+ n) (x +1) = cong wk1 (subst-lifts-id n x)

-- Identity substitution.

mutual
  subst-id : (t : Term n) → subst idSubst t ≡ t
  subst-id (var x) = refl
  subst-id (lam t) = cong lam (trans (substVar-to-subst subst-lift-id t) (subst-id t))
  subst-id (t ∘ u) = cong₂ _∘_ (subst-id t) (subst-id u)
  subst-id zero = refl
  subst-id (suc t) = cong suc (subst-id t)
  subst-id (natrec z s n) = cong₃ natrec (subst-id z) (trans (substVar-to-subst (subst-lifts-id 2) s) (subst-id s)) (subst-id n)
  subst-id (prod t u) = cong₂ prod (subst-id t) (subst-id u)
  subst-id (fst t) = cong fst (subst-id t)
  subst-id (snd t) = cong snd (subst-id t)
  subst-id (prodrec t u) = cong₂ prodrec (subst-id t) (trans (substVar-to-subst (subst-lifts-id 2) u) (subst-id u))
  subst-id star = refl
  subst-id undefined = refl


-- Correctness of composition of weakening and substitution.

-- Composition of liftings is lifting of the composition.
-- lift ρ •ₛ lift σ = lift (ρ •ₛ σ)

subst-lift-•ₛ : ∀ t
              → subst (lift ρ •ₛ liftSubst σ) t
              ≡ subst (liftSubst (ρ •ₛ σ)) t
subst-lift-•ₛ =
  substVar-to-subst (λ { x0 → refl ; (x +1) → sym (wk1-wk≡lift-wk1 _ _)})

helper1 : (n : Nat) (x : Fin (1+ n + m)) →
      (lift (liftn ρ n) •ₛ liftSubst (liftSubstn σ n)) x ≡
      liftSubst (liftSubstn (ρ •ₛ σ) n) x
helper1 0      x0     = refl
helper1 0      (x +1) = sym (wk1-wk≡lift-wk1 _ _)
helper1 (1+ n) x0     = refl
helper1 (1+ n) (x +1) = trans (sym (wk1-wk≡lift-wk1 _ _)) (cong wk1 (helper1 n x))

subst-lifts-•ₛ : ∀ n t
              → subst (liftn ρ n •ₛ liftSubstn σ n) t
              ≡ subst (liftSubstn (ρ •ₛ σ) n) t
subst-lifts-•ₛ 0 t = refl
subst-lifts-•ₛ (1+ n) t = substVar-to-subst (helper1 n) t

-- lift σ ₛ• lift ρ = lift (σ ₛ• ρ)

subst-lift-ₛ• : ∀ t
              → subst (liftSubst σ ₛ• lift ρ) t
              ≡ subst (liftSubst (σ ₛ• ρ)) t
subst-lift-ₛ• = substVar-to-subst (λ { x0 → refl ; (x +1) → refl})

helper2 : (n : Nat) → (x : Fin (1+ n + m))
        → liftSubst (liftSubstn σ n) (wkVar (lift (liftn ρ n)) x) ≡
          liftSubst (liftSubstn (λ x₁ → σ (wkVar ρ x₁)) n) x
helper2 0 x0          = refl
helper2 0 (x +1)      = refl
helper2 (1+ n) x0     = refl
helper2 (1+ n) (x +1) = cong wk1 (helper2 n x)

subst-lifts-ₛ• : ∀ n t
              → subst (liftSubstn σ n ₛ• liftn ρ n) t
              ≡ subst (liftSubstn (σ ₛ• ρ) n) t
subst-lifts-ₛ• 0 t = refl
subst-lifts-ₛ• (1+ n) t = substVar-to-subst (helper2 n) t

-- wk ρ ∘ subst σ = subst (ρ •ₛ σ)

mutual
  wk-subst : ∀ t → wk ρ (subst σ t) ≡ subst (ρ •ₛ σ) t
  wk-subst (var x) = refl
  wk-subst (lam t) = cong lam (trans (wk-subst t) (subst-lift-•ₛ t))
  wk-subst (t ∘ u) = cong₂ _∘_ (wk-subst t) (wk-subst u)
  wk-subst zero = refl
  wk-subst (suc t) = cong suc (wk-subst t)
  wk-subst (natrec z s n) = cong₃ natrec (wk-subst z) (trans (wk-subst s) (subst-lifts-•ₛ 2 s)) (wk-subst n)
  wk-subst (prod t u) = cong₂ prod (wk-subst t) (wk-subst u)
  wk-subst (fst t) = cong fst (wk-subst t)
  wk-subst (snd t) = cong snd (wk-subst t)
  wk-subst (prodrec t u) = cong₂ prodrec (wk-subst t) (trans (wk-subst u) (subst-lifts-•ₛ 2 u))
  wk-subst star = refl
  wk-subst undefined = refl

-- subst σ ∘ wk ρ = subst (σ •ₛ ρ)

mutual
  subst-wk : ∀ t → subst σ (wk ρ t) ≡ subst (σ ₛ• ρ) t
  subst-wk (var x) = refl
  subst-wk (lam t) = cong lam (trans (subst-wk t) (subst-lift-ₛ• t))
  subst-wk (t ∘ u) = cong₂ _∘_ (subst-wk t) (subst-wk u)
  subst-wk zero = refl
  subst-wk (suc t) = cong suc (subst-wk t)
  subst-wk (natrec z s n) = cong₃ natrec (subst-wk z) (trans (subst-wk s) (subst-lifts-ₛ• 2 s)) (subst-wk n)
  subst-wk (prod t u) = cong₂ prod (subst-wk t) (subst-wk u)
  subst-wk (fst t) = cong fst (subst-wk t)
  subst-wk (snd t) = cong snd (subst-wk t)
  subst-wk (prodrec t u) = cong₂ prodrec (subst-wk t) (trans (subst-wk u) (subst-lifts-ₛ• 2 u))
  subst-wk star = refl
  subst-wk undefined = refl


-- Composition of liftings is lifting of the composition.

wk-subst-lift : (G : Term (1+ n))
              → wk (lift ρ) (subst (liftSubst σ) G)
              ≡ subst (liftSubst (ρ •ₛ σ)) G
wk-subst-lift G = trans (wk-subst G) (subst-lift-•ₛ G)

-- Renaming with ρ is the same as substituting with ρ turned into a substitution.

wk≡subst : (ρ : Wk m n) (t : Term n) → wk ρ t ≡ subst (toSubst ρ) t
wk≡subst ρ t = trans (cong (wk ρ) (sym (subst-id t))) (wk-subst t)

-- Composition of substitutions.

-- Composition of liftings is lifting of the composition.

substCompLift : ∀ x
              → (liftSubst σ ₛ•ₛ liftSubst σ′) x
              ≡ (liftSubst (σ ₛ•ₛ σ′)) x
substCompLift                    x0    = refl
substCompLift {σ = σ} {σ′ = σ′} (x +1) = trans (subst-wk (σ′ x)) (sym (wk-subst (σ′ x)))

substCompLifts : ∀ n x
              → (liftSubstn σ n ₛ•ₛ liftSubstn σ′ n) x
              ≡ (liftSubstn (σ ₛ•ₛ σ′) n) x
substCompLifts                   0       x     = refl
substCompLifts                   (1+ n)  x0    = refl
substCompLifts {σ = σ} {σ′ = σ′} (1+ n) (x +1) =
  trans (substCompLift {σ = liftSubstn σ n} {σ′ = liftSubstn σ′ n} (x +1))
        (cong wk1 (substCompLifts n x))

-- Soundness of the composition of substitutions.

mutual
  substCompEq : ∀ (t : Term n)
              → subst σ (subst σ′ t) ≡ subst (σ ₛ•ₛ σ′) t
  substCompEq (var x) = refl
  substCompEq (lam t) = cong lam (trans (substCompEq t) (substVar-to-subst substCompLift t))
  substCompEq (t ∘ u) = cong₂ _∘_ (substCompEq t) (substCompEq u)
  substCompEq zero = refl
  substCompEq (suc t) = cong suc (substCompEq t)
  substCompEq (natrec z s n) = cong₃ natrec (substCompEq z) (trans (substCompEq s) (substVar-to-subst (substCompLifts 2) s)) (substCompEq n)
  substCompEq (prod t u) = cong₂ prod (substCompEq t) (substCompEq u)
  substCompEq (fst t) = cong fst (substCompEq t)
  substCompEq (snd t) = cong snd (substCompEq t)
  substCompEq (prodrec t u) = cong₂ prodrec (substCompEq t) (trans (substCompEq u) (substVar-to-subst (substCompLifts 2) u))
  substCompEq star = refl
  substCompEq undefined = refl

-- Weakening single substitutions.

-- Pulling apart a weakening composition in specific context _[a].

wk-comp-subst : ∀ {a : Term m} (ρ : Wk m ℓ) (ρ′ : Wk ℓ n) G
  → wk (lift (ρ • ρ′)) G [ a ] ≡ wk (lift ρ) (wk (lift ρ′) G) [ a ]

wk-comp-subst {a = a} ρ ρ′ G =
  cong (λ x → x [ a ]) (sym (wk-comp (lift ρ) (lift ρ′) G))

-- Pushing a weakening into a single substitution.
-- ρ (t[a]) = ((lift ρ) t)[ρ a]

wk-β : ∀ {a : Term m} t → wk ρ (t [ a ]) ≡ wk (lift ρ) t [ wk ρ a ]
wk-β t = trans (wk-subst t) (sym (trans (subst-wk t)
               (substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) t)))

-- Pushing a weakening into a double substitution
-- ρ (t[a,b]) = ((lift (lift ρ)) t) [ ρ a , ρ b ]

wk-β-doubleSubst : ∀ (ρ : Wk m n) (s : Term (1+ (1+ n))) (t u : Term n)
                 → wk ρ (s [ u , t ])
                 ≡ wk (lift (lift ρ)) s [ wk ρ u , wk ρ t ]
wk-β-doubleSubst ρ s t u =
 begin
    wk ρ (subst (σₜ t u) s)
       ≡⟨ wk-subst s ⟩
     subst (ρ •ₛ (σₜ t u)) s
       ≡⟨ substVar-to-subst (λ { x0 → refl ; (x0 +1) → refl ; (x +1 +1) → refl}) s ⟩
     subst ((σₜ (wk ρ t) (wk ρ u)) ₛ• (lift (lift ρ))) s
       ≡⟨ sym (subst-wk s) ⟩
     wk (lift (lift ρ)) s [ wk ρ u , wk ρ t ] ∎
  where
    σₜ : (x y : Term ℓ) → Subst ℓ (1+ (1+ ℓ))
    σₜ x y = consSubst (consSubst idSubst y) x

-- Composing a singleton substitution and a lifted substitution.
-- sg u ∘ lift σ = cons id u ∘ lift σ = cons σ u

substVarSingletonComp : ∀ {u} (x : Fin (1+ n))
  → (sgSubst u ₛ•ₛ liftSubst σ) x ≡ (consSubst σ u) x
substVarSingletonComp x0 = refl
substVarSingletonComp {σ = σ} (x +1) = trans (subst-wk (σ x)) (subst-id (σ x))

-- The same again, as action on a term t.

substSingletonComp : ∀ {a} t
  → subst (sgSubst a ₛ•ₛ liftSubst σ) t ≡ subst (consSubst σ a) t
substSingletonComp = substVar-to-subst substVarSingletonComp

-- A single substitution after a lifted substitution.
-- ((lift σ) G)[t] = (cons σ t)(G)

singleSubstComp : ∀ t (σ : Subst m n) G
                 → (subst (liftSubst σ) G) [ t ]
                 ≡ subst (consSubst σ t) G
singleSubstComp t σ G = trans (substCompEq G) (substSingletonComp G)

-- A single substitution after a lifted substitution (with weakening).
-- ((lift (ρ ∘ σ)) G)[t] = (cons (ρ ∘ σ) t)(G)

singleSubstWkComp : ∀ t (σ : Subst m n) G
               → wk (lift ρ) (subst (liftSubst σ) G) [ t ]
               ≡ subst (consSubst (ρ •ₛ σ) t) G
singleSubstWkComp t σ G =
  trans (cong (subst (consSubst var t))
              (trans (wk-subst G) (subst-lift-•ₛ G)))
        (trans (substCompEq G) (substSingletonComp G))

-- Pushing a substitution into a single substitution.

singleSubstLift : ∀ G t
                → subst σ (G [ t ])
                ≡ subst (liftSubst σ) G [ subst σ t ]
singleSubstLift G t =
  trans (substCompEq G)
        (trans (trans (substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) G)
                      (sym (substSingletonComp G)))
               (sym (substCompEq G)))

-- Pushing a substiution into a double substitution

doubleSubstLift : (σ : Subst m n) (G : Term (1+ (1+ n))) (t u : Term n)
                → subst σ (G [ t , u ])
                ≡ subst (liftSubst (liftSubst σ)) G [ subst σ t , subst σ u ]
doubleSubstLift {n = n} σ G t u = begin
  subst σ (G [ t , u ])
    ≡⟨⟩
  subst σ (subst (consSubst (consSubst idSubst t) u) G)
    ≡⟨ substCompEq G ⟩
  subst (σ ₛ•ₛ consSubst (consSubst idSubst t) u) G
    ≡⟨ substVar-to-subst eq G ⟩
  subst ((consSubst (consSubst idSubst (subst σ t)) (subst σ u)) ₛ•ₛ (liftSubst (liftSubst σ))) G
    ≡˘⟨ substCompEq G ⟩
  subst (consSubst (consSubst idSubst (subst σ t)) (subst σ u)) (subst (liftSubst (liftSubst σ)) G)
    ≡⟨⟩
  subst (liftSubst (liftSubst σ)) G [ subst σ t , subst σ u ] ∎
  where
  σ₁ =  consSubst (consSubst idSubst t) u
  σ₂ = consSubst (consSubst idSubst (subst σ t)) (subst σ u)
  eq : (x : Fin (1+ (1+ n))) → (σ ₛ•ₛ σ₁) x ≡ (σ₂ ₛ•ₛ (liftSubst (liftSubst σ))) x
  eq x0 = refl
  eq (_+1 x0) = refl
  eq (x +1 +1) = begin
    (σ ₛ•ₛ σ₁) (x +1 +1)                         ≡⟨⟩
    σ x                                          ≡˘⟨ subst-id (σ x) ⟩
    subst idSubst (σ x)                          ≡⟨⟩
    subst (σ₂ ₛ• (step id • step id)) (σ x)      ≡˘⟨ subst-wk (σ x) ⟩
    subst σ₂ (wk ((step id) • (step id)) (σ x))  ≡˘⟨ cong (subst σ₂) (wk-comp (step id) (step id) (σ x)) ⟩
    subst σ₂ (wk1 (wk1 (σ x)))                   ≡⟨⟩
    (σ₂ ₛ•ₛ (liftSubst (liftSubst σ))) (x +1 +1) ∎

-- Reduction properties

-- Closure of substitution reductions

app-subst* : v ⇒* v′ → (v ∘ w) ⇒* (v′ ∘ w)
app-subst* refl = refl
app-subst* (_⇒*_.trans x v⇒*v′) = _⇒*_.trans (app-subst x) (app-subst* v⇒*v′)

fst-subst* : v ⇒* v′ → T.fst v ⇒* T.fst v′
fst-subst* refl = refl
fst-subst* (_⇒*_.trans x v⇒*v′) = _⇒*_.trans (fst-subst x) (fst-subst* v⇒*v′)
