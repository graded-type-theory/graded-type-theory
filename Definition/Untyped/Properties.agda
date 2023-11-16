------------------------------------------------------------------------
-- Properties of the untyped syntax
-- Laws for weakenings and substitutions.
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

module Definition.Untyped.Properties {a} (M : Set a) where

open import Definition.Untyped M

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Relation
open import Tools.PropositionalEquality hiding (subst)
open import Tools.Reasoning.PropositionalEquality

private
  variable
    ℓ m n : Nat
    A t u v : Term _
    ρ ρ′ : Wk m n
    η : Wk n ℓ
    σ σ′ : Subst m n
    p q r : M

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


wkVar-lifts : (∀ x → wkVar ρ x ≡ wkVar ρ′ x)
            → (∀ n x → wkVar (liftn ρ n) x ≡ wkVar (liftn ρ′ n) x)
wkVar-lifts eq 0 x      = eq x
wkVar-lifts eq (1+ n) x = wkVar-lift (wkVar-lifts eq n) x

-- Extensionally equal weakenings, if applied to a term,
-- yield the same weakened term.  Or:
-- If two weakenings are equal under wkVar, then they are equal under wk.

mutual
  wkVar-to-wk : (∀ x → wkVar ρ x ≡ wkVar ρ′ x)
              → ∀ (t : Term n) → wk ρ t ≡ wk ρ′ t
  wkVar-to-wk eq (var x)   = cong var (eq x)
  wkVar-to-wk eq (gen k c) = cong (gen k) (wkVar-to-wkGen eq c)

  wkVar-to-wkGen : (∀ x → wkVar ρ x ≡ wkVar ρ′ x)
                 → ∀ {bs} c → wkGen {bs = bs} ρ c ≡ wkGen {bs = bs} ρ′ c
  wkVar-to-wkGen eq [] = refl
  wkVar-to-wkGen eq (_∷_ {b = b} t ts) =
    cong₂ _∷_ (wkVar-to-wk (wkVar-lifts eq b) t) (wkVar-to-wkGen eq ts)


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
  wk-id (var x)   = refl
  wk-id (gen k ts) = cong (gen k) (wkGen-id ts)

  wkGen-id : ∀ {bs} x → wkGen {m = n} {n} {bs} id x ≡ x
  wkGen-id [] = refl
  wkGen-id (_∷_ {b = b} t ts) =
    cong₂ _∷_ (trans (wkVar-to-wk (wkVar-lifts-id b) t) ( wk-id t)) (wkGen-id ts)

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
  wk-comp ρ ρ′ (gen k ts) = cong (gen k) (wkGen-comp ρ ρ′ ts)

  wkGen-comp : (ρ : Wk m ℓ) (ρ′ : Wk ℓ n) → ∀ {bs} g
             → wkGen ρ (wkGen ρ′ g) ≡ wkGen {bs = bs} (ρ • ρ′) g
  wkGen-comp ρ ρ′ [] = refl
  wkGen-comp ρ ρ′ (_∷_ {b = b} t ts) =
    cong₂ _∷_ (trans (wk-comp (liftn ρ b) (liftn ρ′ b) t)
                     (wkVar-to-wk (wkVar-comps b ρ ρ′) t))
      (wkGen-comp ρ ρ′ ts)


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

-- If σ = σ′ then consSubst σ t = consSubst σ′ t.

consSubst-cong :
  ∀ {t} →
  (∀ x → σ x ≡ σ′ x) →
  ∀ x → consSubst σ t x ≡ consSubst σ′ t x
consSubst-cong eq x0     = refl
consSubst-cong eq (x +1) = eq x

-- If σ = σ′ then wk1Subst σ = wk1Subst σ′.

wk1Subst-cong :
  (∀ x → σ x ≡ σ′ x) →
  ∀ x → wk1Subst σ x ≡ wk1Subst σ′ x
wk1Subst-cong eq x = cong wk1 (eq x)

-- If  σ = σ′  then  t [ σ ] = t [ σ′ ].

mutual
  substVar-to-subst : ((x : Fin n) → σ x ≡ σ′ x)
                    → (t : Term n) → t [ σ ] ≡ t [ σ′ ]
  substVar-to-subst eq (var x)    = eq x
  substVar-to-subst eq (gen k ts) = cong (gen k) (substVar-to-substGen eq ts)

  substVar-to-substGen : ∀ {bs} → ((x : Fin n) → σ x ≡ σ′ x)
                       → ∀ g → substGen {bs = bs} σ g ≡ substGen {bs = bs} σ′ g
  substVar-to-substGen eq [] = refl
  substVar-to-substGen eq (_∷_ {b = b} t ts) =
    cong₂ _∷_ (substVar-to-subst (substVar-lifts eq b) t)
              (substVar-to-substGen eq ts)


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
  subst-id : (t : Term n) → t [ idSubst ] ≡ t
  subst-id (var x) = refl
  subst-id (gen k ts) = cong (gen k) (substGen-id ts)

  substGen-id : ∀ {bs} g → substGen {m = n} {n} {bs} idSubst g ≡ g
  substGen-id [] = refl
  substGen-id (_∷_ {b = b} t ts) =
    cong₂ _∷_ (trans (substVar-to-subst (subst-lifts-id b) t )
                     (subst-id t))
              (substGen-id ts)


-- Correctness of composition of weakening and substitution.

-- Composition of liftings is lifting of the composition.
-- lift ρ •ₛ lift σ = lift (ρ •ₛ σ)

subst-lift-•ₛ : ∀ t
              → t [ lift ρ •ₛ liftSubst σ ]
              ≡ t [ liftSubst (ρ •ₛ σ) ]
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
              → t [ liftn ρ n •ₛ liftSubstn σ n ]
              ≡ t [ liftSubstn (ρ •ₛ σ) n ]
subst-lifts-•ₛ 0 t = refl
subst-lifts-•ₛ (1+ n) t = substVar-to-subst (helper1 n) t

-- lift σ ₛ• lift ρ = lift (σ ₛ• ρ)

subst-lift-ₛ• : ∀ t
              → t [ liftSubst σ ₛ• lift ρ ]
              ≡ t [ liftSubst (σ ₛ• ρ) ]
subst-lift-ₛ• = substVar-to-subst (λ { x0 → refl ; (x +1) → refl})

helper2 : (n : Nat) → (x : Fin (1+ n + m))
        → liftSubst (liftSubstn σ n) (wkVar (lift (liftn ρ n)) x) ≡
          liftSubst (liftSubstn (λ x₁ → σ (wkVar ρ x₁)) n) x
helper2 0 x0          = refl
helper2 0 (x +1)      = refl
helper2 (1+ n) x0     = refl
helper2 (1+ n) (x +1) = cong wk1 (helper2 n x)

subst-lifts-ₛ• : ∀ n t
              → t [ liftSubstn σ n ₛ• liftn ρ n ]
              ≡ t [ liftSubstn (σ ₛ• ρ) n ]
subst-lifts-ₛ• 0 t = refl
subst-lifts-ₛ• (1+ n) t = substVar-to-subst (helper2 n) t

-- wk ρ ∘ _[ σ ] = _[ ρ •ₛ σ ]

mutual
  wk-subst : ∀ t → wk ρ (t [ σ ]) ≡ t [ ρ •ₛ σ ]
  wk-subst (var x) = refl
  wk-subst (gen k ts) = cong (gen k) (wkGen-substGen ts)

  wkGen-substGen : ∀ {bs} t → wkGen ρ (substGen σ t) ≡ substGen {bs = bs} (ρ •ₛ σ) t
  wkGen-substGen [] = refl
  wkGen-substGen (_∷_ {b = b} t ts) =
    cong₂ _∷_ (trans (wk-subst t) ( subst-lifts-•ₛ b t)) (wkGen-substGen ts)


-- _[ σ ] ∘ wk ρ = _[ σ •ₛ ρ ]

mutual
  subst-wk : ∀ t → wk ρ t [ σ ] ≡ t [ σ ₛ• ρ ]
  subst-wk (var x) = refl
  subst-wk (gen k ts) = cong (gen k) (substGen-wkGen ts)

  substGen-wkGen : ∀ {bs} t → substGen σ (wkGen ρ t) ≡ substGen {bs = bs} (σ ₛ• ρ) t
  substGen-wkGen [] = refl
  substGen-wkGen (_∷_ {b = b} t ts) =
    cong₂ _∷_ (trans (subst-wk t) (subst-lifts-ₛ• b t)) (substGen-wkGen ts)

opaque

  -- Applying wk1Subst σ is the same thing as applying σ and then
  -- weakening one step.

  wk1Subst-wk1 : ∀ t → t [ wk1Subst σ ] ≡ wk1 (t [ σ ])
  wk1Subst-wk1 {σ} t =
    t [ wk1Subst σ ]    ≡⟨⟩
    t [ step id •ₛ σ ]  ≡˘⟨ wk-subst t ⟩
    wk1 (t [ σ ])       ∎

opaque

  -- Applying liftSubst σ to wk1 t amounts to the same thing as first
  -- applying σ and then weakening the result one step.

  wk1-liftSubst : ∀ t → wk1 t [ liftSubst σ ] ≡ wk1 (t [ σ ])
  wk1-liftSubst {σ} t =
    wk1 t [ liftSubst σ ]         ≡⟨ subst-wk t ⟩
    t [ liftSubst σ ₛ• step id ]  ≡⟨⟩
    t [ wk1Subst σ ]              ≡⟨ wk1Subst-wk1 t ⟩
    wk1 (t [ σ ])                 ∎

-- Composition of liftings is lifting of the composition.

wk-subst-lift : (G : Term (1+ n))
              → wk (lift ρ) (G [ liftSubst σ ])
              ≡ G [ liftSubst (ρ •ₛ σ) ]
wk-subst-lift G = trans (wk-subst G) (subst-lift-•ₛ G)

-- Renaming with ρ is the same as substituting with ρ turned into a substitution.

wk≡subst : (ρ : Wk m n) (t : Term n) → wk ρ t ≡ t [ toSubst ρ ]
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
              → (t [ σ′ ]) [ σ ] ≡ t [ σ ₛ•ₛ σ′ ]
  substCompEq (var x) = refl
  substCompEq (gen k ts) = cong (gen k) (substGenCompEq ts)

  substGenCompEq : ∀ {bs} t
              → substGen σ (substGen σ′ t) ≡ substGen {bs = bs} (σ ₛ•ₛ σ′) t
  substGenCompEq [] = refl
  substGenCompEq (_∷_ {b = b} t ts) =
    cong₂ _∷_ (trans (substCompEq t) (substVar-to-subst (substCompLifts b) t))
              (substGenCompEq ts)

-- Weakening single substitutions.

-- Pulling apart a weakening composition in specific context _[a].

wk-comp-subst : ∀ {a : Term m} (ρ : Wk m ℓ) (ρ′ : Wk ℓ n) G
  → wk (lift (ρ • ρ′)) G [ a ]₀ ≡ wk (lift ρ) (wk (lift ρ′) G) [ a ]₀

wk-comp-subst {a = a} ρ ρ′ G =
  cong (λ x → x [ a ]₀) (sym (wk-comp (lift ρ) (lift ρ′) G))

-- Pushing a weakening into a single substitution.
-- ρ (t[a]) = ((lift ρ) t)[ρ a]

wk-β : ∀ {a : Term m} t → wk ρ (t [ a ]₀) ≡ wk (lift ρ) t [ wk ρ a ]₀
wk-β t = trans (wk-subst t) (sym (trans (subst-wk t)
               (substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) t)))

-- Pushing a weakening into a single shifting substitution.
-- If  ρ′ = lift ρ  then  ρ′(t[a]↑) = ρ′(t) [ρ′(a)]↑

wk-β↑ : ∀ {a : Term (1+ n)} t {ρ : Wk m n} → wk (lift ρ) (t [ a ]↑) ≡ wk (lift ρ) t [ wk (lift ρ) a ]↑
wk-β↑ t = trans (wk-subst t) (sym (trans (subst-wk t)
                (substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) t)))

-- Pushing a weakening into a double shifting substitution.

wk-β↑² : ∀ {a} t → wk (lift (lift ρ)) (t [ a ]↑²) ≡ wk (lift ρ) t [ wk (lift (lift ρ)) a ]↑²
wk-β↑² t = trans (wk-subst t) (sym (trans (subst-wk t)
                 (substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) t)))


-- Composing a singleton substitution and a lifted substitution.
-- sg u ∘ lift σ = cons id u ∘ lift σ = cons σ u

substVarSingletonComp : ∀ {u} (x : Fin (1+ n))
  → (sgSubst u ₛ•ₛ liftSubst σ) x ≡ (consSubst σ u) x
substVarSingletonComp x0 = refl
substVarSingletonComp {σ = σ} (x +1) = trans (subst-wk (σ x)) (subst-id (σ x))

-- The same again, as action on a term t.

substSingletonComp : ∀ {a} t
  → t [ sgSubst a ₛ•ₛ liftSubst σ ] ≡ t [ consSubst σ a ]
substSingletonComp = substVar-to-subst substVarSingletonComp

-- A single substitution after a lifted substitution.
-- ((lift σ) G)[t] = (cons σ t)(G)

singleSubstComp : ∀ t (σ : Subst m n) G
                 → (G [ liftSubst σ ]) [ t ]₀
                 ≡ G [ consSubst σ t ]
singleSubstComp t σ G = trans (substCompEq G) (substSingletonComp G)

-- A single substitution after a lifted substitution (with weakening).
-- ((lift (ρ ∘ σ)) G)[t]₀ = (cons (ρ ∘ σ) t)(G)

singleSubstWkComp : ∀ t (σ : Subst m n) G
               → wk (lift ρ) (G [ liftSubst σ ]) [ t ]₀
               ≡ G [ consSubst (ρ •ₛ σ) t ]
singleSubstWkComp t σ G =
  trans (cong (_[ sgSubst t ])
              (trans (wk-subst G) (subst-lift-•ₛ G)))
        (trans (substCompEq G) (substSingletonComp G))

-- Pushing a substitution into a single substitution.

singleSubstLift : ∀ G t
                → G [ t ]₀ [ σ ]
                ≡ G [ liftSubst σ ] [ t [ σ ] ]₀
singleSubstLift G t =
  trans (substCompEq G)
        (trans (trans (substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) G)
                      (sym (substSingletonComp G)))
               (sym (substCompEq G)))

-- More specific laws.

idWkLiftSubstLemma : ∀ (σ : Subst m n) G
  → wk (lift (step id)) (G [ liftSubst σ ]) [ var x0 ]₀
  ≡ G [ liftSubst σ ]
idWkLiftSubstLemma σ G =
  trans (singleSubstWkComp (var x0) σ G)
        (substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) G)

substVarComp↑ : ∀ {t} (σ : Subst m n) x
  → (consSubst (wk1Subst idSubst) (t [ liftSubst σ ]) ₛ•ₛ liftSubst σ) x
  ≡ (liftSubst σ ₛ•ₛ consSubst (wk1Subst idSubst) t) x
substVarComp↑ σ x0 = refl
substVarComp↑ σ (x +1) = trans (subst-wk (σ x)) (sym (wk≡subst (step id) (σ x)))

singleSubstLift↑ : ∀ (σ : Subst m n) G t
                 → G [ t ]↑ [ liftSubst σ ]
                 ≡ G [ liftSubst σ ] [ t [ liftSubst σ ] ]↑
singleSubstLift↑ σ G t =
  trans (substCompEq G)
        (sym (trans (substCompEq G) (substVar-to-subst (substVarComp↑ σ) G)))

substConsComp : ∀ {t G}
       → G [ consSubst (λ x → σ (x +1)) (t [ tail σ ]) ]
       ≡ G [ consSubst (λ x → var (x +1)) (wk1 t) ] [ σ ]
substConsComp {t = t} {G = G} =
  trans (substVar-to-subst (λ { x0 → sym (subst-wk t) ; (x +1) → refl }) G)
        (sym (substCompEq G))

wkSingleSubstId : (F : Term (1+ n)) → (wk (lift (step id)) F) [ var x0 ]₀ ≡ F
wkSingleSubstId F =
  trans (subst-wk F)
        (trans (substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) F)
               (subst-id F))

wkSingleSubstWk1 : (F : Term (1+ n))
                 → wk (lift (step (step id))) F [ var (x0 +1) ]₀ ≡ wk1 F
wkSingleSubstWk1 F =
  trans (subst-wk F)
        (trans (substVar-to-subst (λ {x0 → refl; (x +1) → refl}) F)
               (sym (wk≡subst (step id) F)))

cons-wk-subst : ∀ (ρ : Wk m n) (σ : Subst n ℓ) a t
       → t [ sgSubst a ₛ• lift ρ ₛ•ₛ liftSubst σ ]
       ≡ t [ consSubst (ρ •ₛ σ) a ]
cons-wk-subst ρ σ a = substVar-to-subst
  (λ { x0 → refl
     ; (x +1) → trans (subst-wk (σ x)) (sym (wk≡subst ρ (σ x))) })

-- A specific equation on weakenings used for the reduction of natrec.

wk-β-natrec : ∀ (ρ : Wk m n) (G : Term (1+ n))
            → wk (lift (lift ρ)) (G [ suc (var x1) ]↑²)
            ≡ wk (lift ρ) G [ suc (var x1) ]↑²
wk-β-natrec ρ G = wk-β↑² {ρ = ρ} G

-- A specific equation on eakenings used for the reduction of prodrec.

wk-β-prodrec :
  ∀ {s} (ρ : Wk m n) (A : Term (1+ n)) →
  wk (lift (lift ρ)) (A [ prod s p (var x1) (var x0) ]↑²) ≡
  wk (lift ρ) A [ prod s p (var x1) (var x0) ]↑²
wk-β-prodrec {p = p} ρ A = wk-β↑² {ρ = ρ} A

wk-β-doubleSubst : ∀ (ρ : Wk m n) (s : Term (1+ (1+ n))) (t u : Term n)
                 → wk ρ (s [ u , t ])
                 ≡ wk (lift (lift ρ)) s [ wk ρ u , wk ρ t ]
wk-β-doubleSubst ρ s t u =
 begin
    wk ρ (s [ σₜ t u ])
       ≡⟨ wk-subst s ⟩
     s [ ρ •ₛ (σₜ t u) ]
       ≡⟨ substVar-to-subst eq s ⟩
     s [ (σₜ (wk ρ t) (wk ρ u)) ₛ• (lift (lift ρ)) ]
       ≡⟨ sym (subst-wk s) ⟩
     wk (lift (lift ρ)) s [ wk ρ u , wk ρ t ] ∎
  where
    σₜ : (x y : Term ℓ) → Subst ℓ (1+ (1+ ℓ))
    σₜ x y = consSubst (consSubst idSubst y) x
    eq : ∀ x
       → substVar ((ρ •ₛ (σₜ t u))) x
       ≡ substVar (σₜ (wk ρ t) (wk ρ u)) (wkVar (lift (lift ρ)) x)
    eq x0        = refl
    eq (x0 +1)   = refl
    eq (x +1 +1) = refl

natrecSucCaseLemma : (x : Fin (1+ n))
  → (liftSubstn σ 2 ₛ•ₛ consSubst (wk1Subst (wk1Subst idSubst)) (suc (var x1))) x
  ≡ (consSubst (wk1Subst (wk1Subst idSubst)) (suc (var x1)) ₛ•ₛ liftSubst σ) x
natrecSucCaseLemma x0 = refl
natrecSucCaseLemma {σ = σ} (_+1 x) = begin
  wk1 (wk1 (σ x))
    ≡⟨ wk-comp (step id) (step id) (σ x) ⟩
  wk (step id • step id) (σ x)
    ≡⟨ wk≡subst (step id • step id) (σ x) ⟩
  σ x [ wk1Subst (wk1Subst idSubst) ]
    ≡⟨⟩
  σ x [ consSubst (wk1Subst (wk1Subst idSubst)) (suc (var x1)) ₛ• step id ]
    ≡˘⟨ subst-wk (σ x) ⟩
  wk1 (σ x) [ consSubst (wk1Subst (wk1Subst idSubst)) (suc (var x1)) ] ∎

natrecSucCase : ∀ (σ : Subst m n) F
              → F [ suc (var x1) ]↑² [ liftSubstn σ 2 ]
              ≡ F [ liftSubst σ ] [ suc (var x1) ]↑²
natrecSucCase σ F = begin
  F [ suc (var x1) ]↑² [ liftSubstn σ 2 ]
    ≡⟨ substCompEq F ⟩
  F [ liftSubstn σ 2 ₛ•ₛ σₛ ]
    ≡⟨ substVar-to-subst natrecSucCaseLemma F ⟩
  F [ σₛ ₛ•ₛ liftSubst σ ]
    ≡˘⟨ substCompEq F ⟩
  F [ liftSubst σ ] [ suc (var x1) ]↑² ∎
  where
  σₛ : Subst (1+ (1+ ℓ)) (1+ ℓ)
  σₛ = consSubst (wk1Subst (wk1Subst idSubst)) (suc (var x1))

natrecIrrelevantSubstLemma : ∀ p q r F z s m (σ : Subst ℓ n) (x : Fin (1+ n))
  → (sgSubst (natrec p q r
               (F [ liftSubst σ ])
               (z [ σ ])
               (s [ liftSubstn σ 2 ])
               m
             )
     ₛ•ₛ liftSubst (sgSubst m)
     ₛ•ₛ liftSubst (liftSubst σ)
     ₛ•  step id
     ₛ•ₛ consSubst (tail idSubst) (suc (var x0))) x
  ≡ (consSubst σ (suc m)) x
natrecIrrelevantSubstLemma p q r F z s m σ x0 =
  cong suc (trans (subst-wk m) (subst-id m))
natrecIrrelevantSubstLemma p q r F z s m σ (x +1) =
  trans (subst-wk (wk (step id) (σ x)))
           (trans (subst-wk (σ x))
                     (subst-id (σ x)))

natrecIrrelevantSubst : ∀ p q r F z s m (σ : Subst ℓ n)
  → F [ consSubst σ (suc m) ]
  ≡ wk1 (F [ suc (var x0) ]↑)
           [ liftSubstn σ 2 ]
           [ liftSubst (sgSubst m) ]
           [ natrec p q r (F [ liftSubst σ ]) (z [ σ ]) (s [ liftSubstn σ 2 ]) m ]₀
natrecIrrelevantSubst p q r F z s m σ =
  sym (trans (substCompEq (_[ liftSubstn σ 2 ]
        (wk (step id)
         (F [ consSubst (tail idSubst) (suc (var x0)) ]))))
         (trans (substCompEq (wk (step id)
        (F [ consSubst (tail idSubst) (suc (var x0)) ])))
        (trans
           (subst-wk (F [ consSubst (tail idSubst) (suc (var x0)) ]))
           (trans (substCompEq F)
                     (substVar-to-subst (natrecIrrelevantSubstLemma p q r F z s m σ) F)))))

natrecIrrelevantSubstLemma′ : ∀ (p q r : M) F z s n (x : Fin (1+ m))
  → (sgSubst (natrec p q r F z s n)
     ₛ•ₛ liftSubst (sgSubst n)
     ₛ•  step id
     ₛ•ₛ consSubst (tail idSubst) (suc (var x0))) x
  ≡ (consSubst var (suc n)) x
natrecIrrelevantSubstLemma′ p q r F z s n x0 =
  cong suc (trans (subst-wk n) (subst-id n))
natrecIrrelevantSubstLemma′ p q r F z s n (x +1) = refl

natrecIrrelevantSubst′ : ∀ p q r (F : Term (1+ m)) z s n
  → wk1 (F [ suc (var x0) ]↑) [ (liftSubst (sgSubst n)) ] [ natrec p q r F z s n ]₀
  ≡ F [ suc n ]₀
natrecIrrelevantSubst′ p q r F z s n =
  trans (substCompEq (wk (step id)
                         (F [ consSubst (tail idSubst) (suc (var x0)) ])))
        (trans (subst-wk (F [ consSubst (tail idSubst) (suc (var x0)) ]))
               (trans (substCompEq F)
                      (substVar-to-subst (natrecIrrelevantSubstLemma′ p q r F z s n) F)))

cons0wkLift1-id : ∀ (σ : Subst m n) G
    → (wk (lift (step id)) (G [ liftSubst σ ])) [ var x0 ]₀
    ≡ G [ liftSubst σ ]
cons0wkLift1-id σ G =
  trans (subst-wk (G [ liftSubst σ ]))
        (trans (substVar-to-subst (λ { x0 → refl ; (x +1) → refl })
                                  (G [ liftSubst σ ]))
               (subst-id (G [ liftSubst σ ])))

substConsId : ∀ {t} G
        → G [ consSubst σ (t [ σ ]) ]
        ≡ G [ t ]₀ [ σ ]
substConsId G =
  sym (trans (substCompEq G)
             (substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) G))

substConsTailId : ∀ {G t}
                → G [ consSubst (tail σ) (t [ σ ]) ]
                ≡ G [ consSubst (tail idSubst) t ] [ σ ]
substConsTailId {G = G} =
  trans (substVar-to-subst (λ { x0 → refl
                            ; (x +1) → refl }) G)
        (sym (substCompEq G))

substConcatSingleton′ : ∀ {a} t
                      → t [ σ ₛ•ₛ sgSubst a ]
                      ≡ t [ consSubst σ (a [ σ ]) ]
substConcatSingleton′ t = substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) t

wk1-tail : (t : Term n) → wk1 t [ σ ] ≡ t [ tail σ ]
wk1-tail {σ = σ} t = begin
  wk1 t [ σ ]          ≡⟨⟩
  wk (step id) t [ σ ] ≡⟨ subst-wk t ⟩
  t [ σ ₛ• step id ]   ≡⟨⟩
  t [ tail σ ]         ∎

wk1-tailId : (t : Term n) → wk1 t ≡ t [ tail idSubst ]
wk1-tailId t = trans (sym (subst-id (wk1 t))) (subst-wk t)

wk2-tail : (t : Term n) → wk1 (wk1 t) [ σ ] ≡ t [ tail (tail σ) ]
wk2-tail {σ = σ} t = begin
  wk1 (wk1 t) [ σ ]   ≡⟨ wk1-tail (wk1 t) ⟩
  wk1 t [ tail σ ]    ≡⟨ wk1-tail t ⟩
  t [ tail (tail σ) ] ∎

wk2-tail-B′ : ∀ (W : BindingType) (F : Term n) (G : Term (1+ n))
           → ⟦ W ⟧ wk1 (wk1 F) [ σ ] ▹ (wk (lift (step (step id))) G [ liftSubst σ ])
           ≡ ⟦ W ⟧ F [ tail (tail σ) ] ▹ (G [ liftSubst (tail (tail σ)) ])
wk2-tail-B′ {n} {σ = σ} W F G = begin
  ⟦ W ⟧ wk1 (wk1 F) [ σ ] ▹ (wk (lift (step (step id))) G [ liftSubst σ ])
    ≡⟨ cong₂ (⟦ W ⟧_▹_) (wk1-tail (wk1 F)) (subst-wk G) ⟩
  ⟦ W ⟧ wk1 F [ tail σ ] ▹ (G [ liftSubst σ ₛ• lift (step (step id)) ])
    ≡⟨ cong₂ (⟦ W ⟧_▹_) (wk1-tail F) (substVar-to-subst eq G) ⟩
  ⟦ W ⟧ F [ tail (tail σ) ] ▹ (G [ liftSubst (tail (tail σ)) ]) ∎
  where
  eq : (x : Fin (1+ n))
     → (liftSubst σ ₛ• lift (step (step id))) x ≡ liftSubst (tail (tail σ)) x
  eq x0 = refl
  eq (x +1) = refl

wk2-tail-B : ∀ (W : BindingType) (F : Term n) (G : Term (1+ n))
           → ⟦ W ⟧ wk1 (wk1 F) [ σ ] ▹ (wk (lift (step (step id))) G [ liftSubst σ ])
           ≡ ⟦ W ⟧ F ▹ G [ tail (tail σ) ]
wk2-tail-B (BΠ p q)   F G = wk2-tail-B′ (BΠ p q)   F G
wk2-tail-B (BΣ m p q) F G = wk2-tail-B′ (BΣ m p q) F G

wk2-B : ∀ (W : BindingType) (F : Term n) (G : Term (1+ n))
      → ⟦ W ⟧ wk1 (wk1 F) ▹ wk (lift (step (step id))) G
      ≡ wk1 (wk1 (⟦ W ⟧ F ▹ G))
wk2-B (BΠ p q) F G = cong (Π p , q ▷ _ ▹_) (sym (wk-comp _ _ G))
wk2-B (BΣ s p q) F G = cong (Σ⟨ s ⟩ p , q ▷ _ ▹_) (sym (wk-comp _ _ G))

wk1-sgSubst : ∀ (t : Term n) t' → (wk1 t) [ t' ]₀ ≡ t
wk1-sgSubst t t' rewrite wk1-tailId t =
  let substVar-sgSubst-tail : ∀ a n → (sgSubst a ₛ•ₛ tail idSubst) n ≡ idSubst n
      substVar-sgSubst-tail a n = refl
  in  trans (trans
        (substCompEq t)
        (substVar-to-subst (substVar-sgSubst-tail t') t))
      (subst-id t)

-- Applying _[ u ]↑ to a doubly weakened term amounts to the same
-- thing as doing nothing.

wk1-wk1-[]↑ : wk1 (wk1 t) [ u ]↑ ≡ wk1 (wk1 t)
wk1-wk1-[]↑ {t = t} {u = u} =
  wk1 (wk1 t) [ u ]↑                                       ≡⟨⟩
  wk (step id) (wk1 t) [ consSubst (wk1Subst idSubst) u ]  ≡⟨ subst-wk (wk1 t) ⟩
  wk1 t [ consSubst (wk1Subst idSubst) u ₛ• step id ]      ≡⟨ subst-wk t ⟩
  t [ toSubst (step (step id)) ]                           ≡˘⟨ wk≡subst _ _ ⟩
  wk (step (step id)) t                                    ≡˘⟨ wk1-wk _ _ ⟩
  wk1 (wk1 t)                                              ∎

-- Substituting variable one into t using _[_]↑² amounts to the same
-- thing as applying wk1 to t.

[1]↑² : t [ var x1 ]↑² ≡ wk1 t
[1]↑² {t = t} =
  t [ consSubst (λ x → var (x +1 +1)) (var x1) ]  ≡⟨ (flip substVar-to-subst t λ where
                                                        x0     → refl
                                                        (_ +1) → refl) ⟩
  t [ (λ x → var (x +1)) ]                        ≡˘⟨ wk≡subst _ _ ⟩
  wk1 t                                           ∎

-- Substituting something into wk1 t using _[_]↑² amounts to the same
-- thing as applying wk1 once more.

wk1-[]↑² : wk1 t [ u ]↑² ≡ wk1 (wk1 t)
wk1-[]↑² {t = t} {u = u} =
  wk1 t [ u ]↑²                                                 ≡⟨⟩
  wk (step id) t [ consSubst (wk1Subst (wk1Subst idSubst)) u ]  ≡⟨ subst-wk t ⟩
  t [ consSubst (wk1Subst (wk1Subst idSubst)) u ₛ• step id ]    ≡⟨⟩
  t [ toSubst (step (step id)) ]                                ≡˘⟨ wk≡subst _ _ ⟩
  wk (step (step id)) t                                         ≡˘⟨ wk1-wk _ _ ⟩
  wk1 (wk1 t)                                                   ∎

-- Substituting wk1 u into t using _[_]↑² amounts to the same thing as
-- substituting u into t using _[_]↑ and then weakening one step.

[wk1]↑² : (t : Term (1 + n)) → t [ wk1 u ]↑² ≡ wk1 (t [ u ]↑)
[wk1]↑² {u = u} t =
  t [ consSubst (λ x → var ((x +1) +1)) (wk1 u) ]  ≡⟨ (flip substVar-to-subst t λ where
                                                         x0     → refl
                                                         (_ +1) → refl) ⟩
  t [ wk1 ∘→ consSubst (λ x → var (x +1)) u ]      ≡˘⟨ wk-subst t ⟩
  wk1 (t [ consSubst (λ x → var (x +1)) u ])       ∎

subst-β-prodrec :
  ∀ {s} (A : Term (1+ n)) (σ : Subst m n) →
  A [ prod s p (var x1) (var x0) ]↑² [ liftSubstn σ 2 ] ≡
  A [ liftSubst σ ] [ prod s p (var x1) (var x0) ]↑²
subst-β-prodrec {n = n} A σ = begin
   A [ t₁ ]↑² [ liftSubstn σ 2 ]
     ≡⟨ substCompEq A ⟩
   A [ liftSubstn σ 2 ₛ•ₛ consSubst (wk1Subst (wk1Subst idSubst)) t₁ ]
     ≡⟨ substVar-to-subst varEq A ⟩
   A [ consSubst (wk1Subst (wk1Subst idSubst)) t₂ ₛ•ₛ liftSubst σ ]
     ≡˘⟨ substCompEq A ⟩
   A [ liftSubst σ ] [ t₂ ]↑² ∎
   where
   t₁ = prod! (var (x0 +1)) (var x0)
   t₂ = prod! (var (x0 +1)) (var x0)
   varEq :
     (x : Fin (1+ n)) →
     (liftSubstn σ 2 ₛ•ₛ consSubst (wk1Subst (wk1Subst idSubst)) t₁) x ≡
     (consSubst (wk1Subst (wk1Subst idSubst)) t₂ ₛ•ₛ liftSubst σ) x
   varEq x0 = refl
   varEq (x +1) = begin
     wk1 (wk1 (σ x))
       ≡⟨ wk≡subst (step id) (wk1 (σ x)) ⟩
     wk1 (σ x) [ wk1Subst idSubst ]
       ≡⟨ subst-wk (σ x) ⟩
     σ x [ wk1Subst idSubst ₛ• step id ]
       ≡⟨ substVar-to-subst (λ x₁ → refl) (σ x) ⟩
     σ x [ (λ y → var (y +1 +1)) ]
       ≡˘⟨ wk1-tail (σ x) ⟩
     wk1 (σ x) [ consSubst (λ y → var (y +1 +1)) t₂ ] ∎

substComp↑² :
  (A : Term (1+ n)) (t : Term (2 + n)) →
  A [ consSubst (tail (tail σ)) (t [ σ ]) ] ≡ A [ t ]↑² [ σ ]
substComp↑² {n = n} {σ = σ} A t = begin
  A [ consSubst (tail (tail σ)) (t [ σ ]) ]
    ≡⟨ substVar-to-subst varEq A ⟩
  A [ σ ₛ•ₛ consSubst (wk1Subst (wk1Subst idSubst)) t ]
    ≡˘⟨ substCompEq A ⟩
  A [ t ]↑² [ σ ] ∎
  where
  varEq : (x : Fin (1+ n)) →
          consSubst (tail (tail σ)) (t [ σ ]) x ≡
          (σ ₛ•ₛ consSubst (wk1Subst (wk1Subst idSubst)) t) x
  varEq x0 = refl
  varEq (x +1) = refl

substCompProdrec :
  ∀ {s} (A : Term (1+ n)) (t u : Term m) (σ : Subst m n) →
  A [ liftSubst σ ] [ prod s p t u ]₀ ≡
  A [ prod s p (var x1) (var x0) ]↑² [ consSubst (consSubst σ t) u ]
substCompProdrec {n = n} A t u σ = begin
   A [ liftSubst σ ] [ prod! t u ]₀
     ≡⟨ substCompEq A ⟩
   A [ sgSubst (prod! t u) ₛ•ₛ liftSubst σ ]
     ≡⟨ substVar-to-subst varEq A ⟩
   A [ consSubst (consSubst σ t) u ₛ•ₛ consSubst (wk1Subst (wk1Subst idSubst)) px ]
     ≡˘⟨ substCompEq A ⟩
   A [ px ]↑² [ consSubst (consSubst σ t) u ] ∎
   where
   px = prod! (var (x0 +1)) (var x0)
   varEq : (x : Fin (1+ n))
         → (sgSubst (prod! t u) ₛ•ₛ liftSubst σ) x
         ≡ (consSubst (consSubst σ t) u ₛ•ₛ consSubst (wk1Subst (wk1Subst idSubst)) px) x
   varEq x0 = refl
   varEq (x +1) = trans (wk1-tail (σ x)) (subst-id (σ x))

-- A variant of the previous lemma.

[1,0]↑²[,] :
  (t : Term (1+ n)) →
  t [ prodˢ p (var x1) (var x0) ]↑² [ u , v ] ≡
  t [ prodˢ p u v ]₀
[1,0]↑²[,] {p = p} {u = u} {v = v} t =
  t [ prodˢ p (var x1) (var x0) ]↑² [ u , v ]  ≡˘⟨ substCompProdrec t _ _ _ ⟩

  t [ liftSubst idSubst ] [ prodˢ p u v ]₀     ≡⟨ cong _[ _ ] $
                                                  trans (substVar-to-subst subst-lift-id t) $
                                                  subst-id t ⟩
  t [ prodˢ p u v ]₀                           ∎

doubleSubstComp : (A : Term (1+ (1+ n))) (t u : Term m) (σ : Subst m n)
                → A [ liftSubstn σ 2 ] [ t , u ]
                ≡ A [ consSubst (consSubst σ t) u ]
doubleSubstComp {n = n} A t u σ = begin
  A [ liftSubstn σ 2 ] [ t , u ]
    ≡⟨ substCompEq A ⟩
  A [ consSubst (sgSubst t) u ₛ•ₛ liftSubstn σ 2 ]
    ≡⟨ substVar-to-subst varEq A ⟩
  A [ consSubst (consSubst σ t) u ] ∎
  where
  varEq : (x : Fin (1+ (1+ n)))
        → (consSubst (consSubst idSubst t) u ₛ•ₛ liftSubstn σ 2) x
        ≡  consSubst (consSubst σ t) u x
  varEq x0 = refl
  varEq (x0 +1) = refl
  varEq (x +1 +1) = trans (wk1-tail (wk1 (σ x)))
                          (trans (wk1-tail (σ x)) (subst-id (σ x)))

opaque

  -- One can fuse an application of _[_,_] and an application of _[_]
  -- into an application of _[_].

  [,]-[]-fusion :
    ∀ t →
    t [ u , v ] [ σ ] ≡
    t [ consSubst (consSubst σ (u [ σ ])) (v [ σ ]) ]
  [,]-[]-fusion {u} {v} {σ} t =
    t [ u , v ] [ σ ]                                  ≡⟨ substCompEq t ⟩
    t [ σ ₛ•ₛ consSubst (sgSubst u) v ]                ≡⟨ (flip substVar-to-subst t λ where
                                                             x0        → refl
                                                             (x0 +1)   → refl
                                                             (_ +1 +1) → refl) ⟩
    t [ consSubst (consSubst σ (u [ σ ])) (v [ σ ]) ]  ∎

opaque

  -- The function _[_,_] kind of commutes with _[_].

  [,]-[]-commute :
    ∀ t →
    t [ u , v ] [ σ ] ≡
    t [ liftSubstn σ 2 ] [ u [ σ ] , v [ σ ] ]
  [,]-[]-commute {u} {v} {σ} t =
    t [ u , v ] [ σ ]                                  ≡⟨ [,]-[]-fusion t ⟩
    t [ consSubst (consSubst σ (u [ σ ])) (v [ σ ]) ]  ≡˘⟨ doubleSubstComp t _ _ _ ⟩
    t [ liftSubstn σ 2 ] [ u [ σ ] , v [ σ ] ]         ∎

opaque

  -- A lemma related to Id.

  ≡Id-wk1-wk1-0[]₀ :
    Id A t u ≡ Id (wk1 A) (wk1 t) (var x0) [ u ]₀
  ≡Id-wk1-wk1-0[]₀ {A} {t} {u} =
    Id A t u                            ≡˘⟨ cong₂ (λ A t → Id A t _) (wk1-sgSubst _ _) (wk1-sgSubst _ _) ⟩
    Id (wk1 A [ u ]₀) (wk1 t [ u ]₀) u  ≡⟨⟩
    Id (wk1 A) (wk1 t) (var x0) [ u ]₀  ∎

opaque

  -- Another lemma related to Id.

  Id-wk1-wk1-0[⇑]≡ :
    ∀ A t →
    Id (wk1 A) (wk1 t) (var x0) [ liftSubst σ ] ≡
    Id (wk1 (A [ σ ])) (wk1 (t [ σ ])) (var x0)
  Id-wk1-wk1-0[⇑]≡ {σ} A t =
    Id (wk1 A) (wk1 t) (var x0) [ liftSubst σ ]                  ≡⟨⟩
    Id (wk1 A [ liftSubst σ ]) (wk1 t [ liftSubst σ ]) (var x0)  ≡⟨ cong₂ (λ A t → Id A t _) (wk1-liftSubst A) (wk1-liftSubst t) ⟩
    Id (wk1 (A [ σ ])) (wk1 (t [ σ ])) (var x0)                  ∎

opaque

  -- A _[t]₀ after _[u]↑ has the same effect as _[u[t]₀]₀.

  []↑-[]₀ :
    ∀ A →
    A [ u ]↑ [ t ]₀ ≡ A [ u [ t ]₀ ]₀
  []↑-[]₀ {u} {t} A = begin
    (A [ u ]↑) [ t ]₀                                   ≡⟨ substCompEq A ⟩
    A [ sgSubst t ₛ•ₛ consSubst (wk1Subst idSubst) u ]  ≡⟨ substVar-to-subst lemma A ⟩
    A [ u [ t ]₀ ]₀                                     ∎
    where
    lemma : ∀ x → (sgSubst t ₛ•ₛ consSubst (wk1Subst idSubst) u) x ≡ sgSubst (u [ t ]₀) x
    lemma x0 = refl
    lemma (_+1 x) = refl

-- There are no closed neutral terms

noClosedNe : {t : Term 0} → Neutral t → ⊥
noClosedNe (∘ₙ net) = noClosedNe net
noClosedNe (fstₙ net) = noClosedNe net
noClosedNe (sndₙ net) = noClosedNe net
noClosedNe (natrecₙ net) = noClosedNe net
noClosedNe (prodrecₙ net) = noClosedNe net
noClosedNe (emptyrecₙ net) = noClosedNe net
noClosedNe (unitrecₙ net) = noClosedNe net
noClosedNe (Jₙ net) = noClosedNe net
noClosedNe (Kₙ net) = noClosedNe net
noClosedNe ([]-congₙ net) = noClosedNe net

-- Decidability of Strength equality
decStrength : Decidable (_≡_ {A = Strength})
decStrength 𝕤 𝕤 = yes refl
decStrength 𝕤 𝕨 = no λ{()}
decStrength 𝕨 𝕤 = no λ{()}
decStrength 𝕨 𝕨 = yes refl

-- Decidability of equality for BinderMode.
decBinderMode : Decidable (_≡_ {A = BinderMode})
decBinderMode = λ where
  BMΠ      BMΠ      → yes refl
  BMΠ      (BMΣ _)  → no (λ ())
  (BMΣ _)  BMΠ      → no (λ ())
  (BMΣ s₁) (BMΣ s₂) → case decStrength s₁ s₂ of λ where
    (yes refl) → yes refl
    (no s₁≢s₂)    → no λ where
      refl → s₁≢s₂ refl
