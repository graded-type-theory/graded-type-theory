-- Laws for weakenings and substitutions.

{-# OPTIONS --without-K #-}

module Definition.Untyped.Properties where

open import Tools.Nat
open import Tools.Unit
open import Tools.PropositionalEquality as PE hiding (subst)

open import Definition.Untyped


-- Weakening properties

-- Two weakenings ρ and ρ' are extensionally equal if they agree on
-- all arguments when interpreted as functions mapping variables to
-- variables.  Formally, they are considered equal iff
--
--   (∀ x → wkVar ρ x ≡ wkVar ρ' x)
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

wkVar-lift : ∀ {ρ ρ'}
  → (∀ x → wkVar ρ x ≡ wkVar ρ' x)
  → (∀ x → wkVar (lift ρ) x ≡ wkVar (lift ρ') x)

wkVar-lift eq zero    = refl
wkVar-lift eq (suc x) = cong suc (eq x)

wkVar-lifts : ∀ {ρ ρ'}
  → (∀ x → wkVar ρ x ≡ wkVar ρ' x)
  → (∀ n x → wkVar (lifts n ρ) x ≡ wkVar (lifts n ρ') x)
wkVar-lifts eq zero x = eq x
wkVar-lifts eq (suc n) x = wkVar-lift (wkVar-lifts eq n) x

-- Extensionally equal weakenings, if applied to a term,
-- yield the same weakened term.  Or:
-- If two weakenings are equal under wkVar, then they are equal under wk.

mutual
  wkVar-to-wk : ∀ {ρ ρ'}
    → (∀ x → wkVar ρ x ≡ wkVar ρ' x)
    → ∀ t → wk ρ t ≡ wk ρ' t

  wkVar-to-wk eq (var x) = cong var (eq x)
  wkVar-to-wk eq (gen x c) = cong (gen x) (wkVar-to-wk' eq c)

  wkVar-to-wk' : ∀ {ρ ρ'}
    → (∀ x → wkVar ρ x ≡ wkVar ρ' x)
    → ∀ t → wkGen ρ t ≡ wkGen ρ' t
  wkVar-to-wk' eq ε = refl
  wkVar-to-wk' eq (c ∙ ⟦ l , t ⟧) =
    cong₂ _∙_ (wkVar-to-wk' eq c)
              (cong (⟦_,_⟧ l) (wkVar-to-wk (wkVar-lifts eq l) t))

-- lift id  is extensionally equal to  id.

wkVar-lift-id : (x : Nat) → wkVar (lift id) x ≡ wkVar id x
wkVar-lift-id zero    = refl
wkVar-lift-id (suc x) = refl

wkVar-lifts-id : (n x : Nat) → wkVar (lifts n id) x ≡ wkVar id x
wkVar-lifts-id zero x = refl
wkVar-lifts-id (suc n) zero = refl
wkVar-lifts-id (suc n) (suc x) = cong suc (wkVar-lifts-id n x)

-- id is the identity renaming.

wkVar-id : (x : Nat) → wkVar id x ≡ x
wkVar-id x = refl

mutual
  wk-id : (t : Term) → wk id t ≡ t
  wk-id (var x) = refl
  wk-id (gen x c) = cong (gen x) (wk-id' c)

  wk-id' : ∀ c → wkGen id c ≡ c
  wk-id' ε = refl
  wk-id' (c ∙ ⟦ l , t ⟧) =
    cong₂ _∙_ (wk-id' c)
              (cong (⟦_,_⟧ l) (trans (wkVar-to-wk (wkVar-lifts-id l) t) (wk-id t)))

-- lift id  is also the identity renaming.

wk-lift-id : (t : Term) → wk (lift id) t ≡ t
wk-lift-id t = trans (wkVar-to-wk wkVar-lift-id t) (wk-id t)

-- The composition of weakenings is correct...
--
-- ...as action on variables.

wkVar-comp : ∀ ρ ρ' x → wkVar ρ (wkVar ρ' x) ≡ wkVar (ρ • ρ') x
wkVar-comp id       ρ'        x       = refl
wkVar-comp (step ρ) ρ'        x       = cong suc (wkVar-comp ρ ρ' x)
wkVar-comp (lift ρ) id        x       = refl
wkVar-comp (lift ρ) (step ρ') x       = cong suc (wkVar-comp ρ ρ' x)
wkVar-comp (lift ρ) (lift ρ') zero    = refl
wkVar-comp (lift ρ) (lift ρ') (suc x) = cong suc (wkVar-comp ρ ρ' x)

wkVar-comp' : ∀ n ρ ρ' x → wkVar (lifts n ρ • lifts n ρ') x ≡ wkVar (lifts n (ρ • ρ')) x
wkVar-comp' zero ρ ρ' x = refl
wkVar-comp' (suc n) ρ ρ' zero = refl
wkVar-comp' (suc n) ρ ρ' (suc x) = cong suc (wkVar-comp' n ρ ρ' x)

-- ... as action on terms.

mutual
  wk-comp : ∀ ρ ρ' t → wk ρ (wk ρ' t) ≡ wk (ρ • ρ') t
  wk-comp ρ ρ' (var x) = cong var (wkVar-comp ρ ρ' x)
  wk-comp ρ ρ' (gen x c) = cong (gen x) (wk-comp' ρ ρ' c)

  wk-comp' : ∀ ρ ρ' c → wkGen ρ (wkGen ρ' c) ≡ wkGen (ρ • ρ') c
  wk-comp' ρ ρ' ε = refl
  wk-comp' ρ ρ' (c ∙ ⟦ l , t ⟧) =
    cong₂ _∙_ (wk-comp' ρ ρ' c)
              (cong (⟦_,_⟧ l)
                    (trans (wk-comp (lifts l ρ) (lifts l ρ') t)
                           (wkVar-to-wk (wkVar-comp' l ρ ρ') t)))


-- The following lemmata are variations on the equality
--
--   wk1 ∘ ρ = lift ρ ∘ wk1.
--
-- Typing:  Γ∙A ≤ Γ ≤ Δ  <==>  Γ∙A ≤ Δ∙A ≤ Δ.

lift-step-comp : (ρ : Wk) → step id • ρ ≡ lift ρ • step id
lift-step-comp id       = refl
lift-step-comp (step ρ) = cong step (lift-step-comp ρ)
lift-step-comp (lift ρ) = refl

wk1-wk : ∀ ρ t → wk1 (wk ρ t) ≡ wk (step ρ) t
wk1-wk ρ t = wk-comp (step id) ρ t

lift-wk1 : ∀ ρ t → wk (lift ρ) (wk1 t) ≡ wk (step ρ) t
lift-wk1 pr A = trans (wk-comp (lift pr) (step id) A)
                      (sym (cong (λ x → wk x A) (lift-step-comp pr)))

wk1-wk≡lift-wk1 : ∀ ρ t → wk1 (wk ρ t) ≡ wk (lift ρ) (wk1 t)
wk1-wk≡lift-wk1 ρ t = trans (wk1-wk ρ t) (sym (lift-wk1 ρ t))

-- Substitution properties.

-- Two substitutions σ and σ' are equal if they are pointwise equal,
-- i.e., agree on all variables.
--
--   ∀ x →  σ x ≡ σ' x

-- If  σ = σ'  then  lift σ = lift σ'.

substVar-lift : ∀ {σ σ'}
  → (∀ x → σ x ≡ σ' x)
  → ∀ x → liftSubst σ x ≡ liftSubst σ' x

substVar-lift eq zero    = refl
substVar-lift eq (suc x) = cong wk1 (eq x)

substVar-lifts : ∀ {σ σ'}
  → (∀ x → σ x ≡ σ' x)
  → ∀ n x → liftSubsts n σ x ≡ liftSubsts n σ' x

substVar-lifts eq zero x = eq x
substVar-lifts eq (suc n) zero = refl
substVar-lifts eq (suc n) (suc x) = cong wk1 (substVar-lifts eq n x)

-- If  σ = σ'  then  subst σ t = subst σ' t.

mutual
  substVar-to-subst : ∀ {σ σ'}
    → ((x : Nat) → σ x ≡ σ' x)
    → (t : Term) → subst σ t ≡ subst σ' t
  substVar-to-subst eq (var x) = eq x
  substVar-to-subst eq (gen x c) = cong (gen x) (substVar-to-subst' eq c)

  substVar-to-subst' : ∀ {σ σ'}
    → ((x : Nat) → σ x ≡ σ' x)
    → ∀ c → substGen σ c ≡ substGen σ' c
  substVar-to-subst' eq ε = refl
  substVar-to-subst' eq (c ∙ ⟦ l , t ⟧) =
    cong₂ _∙_ (substVar-to-subst' eq c)
              (cong (⟦_,_⟧ l) (substVar-to-subst (substVar-lifts eq l) t))

-- lift id = id  (as substitutions)

subst-lift-id : (x : Nat) → (liftSubst idSubst) x ≡ idSubst x
subst-lift-id zero    = refl
subst-lift-id (suc x) = refl

subst-lifts-id : (n x : Nat) → (liftSubsts n idSubst) x ≡ idSubst x
subst-lifts-id zero x = refl
subst-lifts-id (suc n) zero = refl
subst-lifts-id (suc n) (suc x) = cong wk1 (subst-lifts-id n x)

-- Identity substitution.

mutual
  subst-id : (t : Term) → subst idSubst t ≡ t
  subst-id (var x) = refl
  subst-id (gen x c) = cong (gen x) (subst-id' c)

  subst-id' : ∀ c → substGen idSubst c ≡ c
  subst-id' ε = refl
  subst-id' (c ∙ ⟦ l , t ⟧) =
    cong₂ _∙_ (subst-id' c)
              (cong (⟦_,_⟧ l) (trans (substVar-to-subst (subst-lifts-id l) t)
                                     (subst-id t)))


-- Correctness of composition of weakening and substitution.

-- Composition of liftings is lifting of the composition.
-- lift ρ •ₛ lift σ = lift (ρ •ₛ σ)

subst-lift-•ₛ : ∀ {ρ σ} t
              → subst (lift ρ •ₛ liftSubst σ) t
              ≡ subst (liftSubst (ρ •ₛ σ)) t
subst-lift-•ₛ =
  substVar-to-subst (λ { zero → refl ; (suc x) → sym (wk1-wk≡lift-wk1 _ _)})

helper1 : ∀ {ρ σ} (n x : Nat) →
      (lift (lifts n ρ) •ₛ liftSubst (liftSubsts n σ)) x ≡
      liftSubst (liftSubsts n (ρ •ₛ σ)) x
helper1 zero zero = refl
helper1 zero (suc x) = sym (wk1-wk≡lift-wk1 _ _)
helper1 (suc n) zero = refl
helper1 (suc n) (suc x) = trans (sym (wk1-wk≡lift-wk1 _ _)) (cong wk1 (helper1 n x))

subst-lifts-•ₛ : ∀ {ρ σ} n t
              → subst (lifts n ρ •ₛ liftSubsts n σ) t
              ≡ subst (liftSubsts n (ρ •ₛ σ)) t
subst-lifts-•ₛ zero t = refl
subst-lifts-•ₛ (suc n) t = substVar-to-subst (helper1 n) t

-- lift σ ₛ• lift ρ = lift (σ ₛ• ρ)

subst-lift-ₛ• : ∀ {ρ σ} t
              → subst (liftSubst σ ₛ• lift ρ) t
              ≡ subst (liftSubst (σ ₛ• ρ)) t
subst-lift-ₛ• = substVar-to-subst (λ { zero → refl ; (suc x) → refl})

helper2 : ∀ {ρ σ} (n x : Nat) →
      liftSubst (liftSubsts n σ) (wkVar (lift (lifts n ρ)) x) ≡
      liftSubst (liftSubsts n (λ x₁ → σ (wkVar ρ x₁))) x
helper2 zero zero = refl
helper2 zero (suc x) = refl
helper2 (suc n) zero = refl
helper2 (suc n) (suc x) = cong wk1 (helper2 n x)

subst-lifts-ₛ• : ∀ {ρ σ} n t
              → subst (liftSubsts n σ ₛ• lifts n ρ) t
              ≡ subst (liftSubsts n (σ ₛ• ρ)) t
subst-lifts-ₛ• zero t = refl
subst-lifts-ₛ• (suc n) t = substVar-to-subst (helper2 n) t

-- wk ρ ∘ subst σ = subst (ρ •ₛ σ)

mutual
  wk-subst : ∀ {ρ σ} t → wk ρ (subst σ t) ≡ subst (ρ •ₛ σ) t
  wk-subst (var x) = refl
  wk-subst (gen x c) = cong (gen x) (wk-subst' c)

  wk-subst' : ∀ {ρ σ} t → wkGen ρ (substGen σ t) ≡ substGen (ρ •ₛ σ) t
  wk-subst' ε = refl
  wk-subst' (c ∙ ⟦ l , t ⟧) = cong₂ _∙_ (wk-subst' c) (cong (⟦_,_⟧ l) (trans (wk-subst t) (subst-lifts-•ₛ l t)))

-- subst σ ∘ wk ρ = subst (σ •ₛ ρ)

mutual
  subst-wk : ∀ {ρ σ} t → subst σ (wk ρ t) ≡ subst (σ ₛ• ρ) t
  subst-wk (var x) = refl
  subst-wk (gen x c) = cong (gen x) (subst-wk' c)

  subst-wk' : ∀ {ρ σ} t → substGen σ (wkGen ρ t) ≡ substGen (σ ₛ• ρ) t
  subst-wk' ε = refl
  subst-wk' (c ∙ ⟦ l , t ⟧) = cong₂ _∙_ (subst-wk' c) (cong (⟦_,_⟧ l) (trans (subst-wk t) (subst-lifts-ₛ• l t)))

-- Composition of liftings is lifting of the composition.

wk-subst-lift : ∀ {ρ σ} G
              → wk (lift ρ) (subst (liftSubst σ) G)
              ≡ subst (liftSubst (ρ •ₛ σ)) G
wk-subst-lift G = trans (wk-subst G) (subst-lift-•ₛ G)

-- Renaming with ρ is the same as substituting with ρ turned into a substitution.

wk≡subst : ∀ ρ t → wk ρ t ≡ subst (toSubst ρ) t
wk≡subst ρ t = trans (cong (wk ρ) (sym (subst-id t))) (wk-subst t)


-- Composition of substitutions.

-- Composition of liftings is lifting of the composition.

substCompLift : ∀ {σ σ'} x
              → (liftSubst σ ₛ•ₛ liftSubst σ') x
              ≡ (liftSubst (σ ₛ•ₛ σ')) x
substCompLift          zero    = refl
substCompLift {σ} {σ'} (suc x) = trans (subst-wk (σ' x)) (sym (wk-subst (σ' x)))

substCompLifts : ∀ {σ σ'} n x
              → (liftSubsts n σ ₛ•ₛ liftSubsts n σ') x
              ≡ (liftSubsts n (σ ₛ•ₛ σ')) x
substCompLifts zero x = refl
substCompLifts (suc n) zero = refl
substCompLifts {σ} {σ'} (suc n) (suc x) =
  trans (substCompLift {liftSubsts n σ} {liftSubsts n σ'} (suc x))
        (cong wk1 (substCompLifts n x))

-- Soundness of the composition of substitutions.

mutual
  substCompEq : ∀ {σ σ'} (t : Term)
              → subst σ (subst σ' t) ≡ subst (σ ₛ•ₛ σ') t
  substCompEq (var x) = refl
  substCompEq (gen x c) = cong (gen x) (substCompEq' c)

  substCompEq' : ∀ {σ σ'} t
              → substGen σ (substGen σ' t) ≡ substGen (σ ₛ•ₛ σ') t
  substCompEq' ε = refl
  substCompEq' (c ∙ ⟦ l , t ⟧) =
    cong₂ _∙_ (substCompEq' c)
              (cong (⟦_,_⟧ l) (trans (substCompEq t)
                                     (substVar-to-subst (substCompLifts l) t)))


-- Weakening single substitutions.

-- Pulling apart a weakening composition in specific context _[a].

wk-comp-subst : ∀ {a} ρ ρ' G
  → wk (lift (ρ • ρ')) G [ a ] ≡ wk (lift ρ) (wk (lift ρ') G) [ a ]

wk-comp-subst {a} ρ ρ' G =
  cong (λ x → x [ a ]) (sym (wk-comp (lift ρ) (lift ρ') G))

-- Pushing a weakening into a single substitution.
-- ρ (t[a]) = ((lift ρ) t)[ρ a]

wk-β : ∀ {ρ a} t → wk ρ (t [ a ]) ≡ wk (lift ρ) t [ wk ρ a ]
wk-β t = trans (wk-subst t) (sym (trans (subst-wk t)
               (substVar-to-subst (λ { zero → refl ; (suc x) → refl}) t)))

-- Pushing a weakening into a single shifting substitution.
-- If  ρ' = lift ρ  then  ρ'(t[a]↑) = ρ'(t) [ρ'(a)]↑

wk-β↑ : ∀ {ρ a} t → wk (lift ρ) (t [ a ]↑) ≡ wk (lift ρ) t [ wk (lift ρ) a ]↑
wk-β↑ t = trans (wk-subst t) (sym (trans (subst-wk t)
                (substVar-to-subst (λ { zero → refl ; (suc x) → refl}) t)))

-- A specific equation on weakenings used for the reduction of natrec.

wk-β-natrec : ∀ ρ G
  → Πₑ ℕₑ ▹ (Πₑ wk (lift ρ) G ▹ wk (lift (lift ρ)) (wk1 (G [ sucₑ (var zero) ]↑)))
  ≡ Πₑ ℕₑ ▹ (wk (lift ρ) G ▹▹ wk (lift ρ) G [ sucₑ (var zero) ]↑)
wk-β-natrec ρ G =
  cong₂ Πₑ_▹_ refl (cong₂ Πₑ_▹_ refl
    (trans (wk-comp (lift (lift ρ)) (step id)
                    (subst (consSubst (wk1Subst var) (sucₑ (var zero))) G))
       (trans (wk-subst G) (sym (trans (wk-subst (wk (lift ρ) G))
         (trans (subst-wk G)
                (substVar-to-subst (λ { zero → refl ; (suc x) → refl}) G)))))))

-- Composing a singleton substitution and a lifted substitution.
-- sg u ∘ lift σ = cons id u ∘ lift σ = cons σ u

substVarSingletonComp : ∀ {u σ} (x : Nat)
  → (sgSubst u ₛ•ₛ liftSubst σ) x ≡ (consSubst σ u) x
substVarSingletonComp zero = refl
substVarSingletonComp {σ = σ} (suc x) = trans (subst-wk (σ x)) (subst-id (σ x))

-- The same again, as action on a term t.

substSingletonComp : ∀ {a σ} t
  → subst (sgSubst a ₛ•ₛ liftSubst σ) t ≡ subst (consSubst σ a) t
substSingletonComp = substVar-to-subst substVarSingletonComp

-- A single substitution after a lifted substitution.
-- ((lift σ) G)[t] = (cons σ t)(G)

singleSubstComp : ∀ t σ G
                 → (subst (liftSubst σ) G) [ t ]
                 ≡ subst (consSubst σ t) G
singleSubstComp t σ G = trans (substCompEq G) (substSingletonComp G)

-- A single substitution after a lifted substitution (with weakening).
-- ((lift (ρ ∘ σ)) G)[t] = (cons (ρ ∘ σ) t)(G)

singleSubstWkComp : ∀ {ρ} t σ G
               → wk (lift ρ) (subst (liftSubst σ) G) [ t ]
               ≡ subst (consSubst (ρ •ₛ σ) t) G
singleSubstWkComp t σ G =
  trans (cong (subst (consSubst var t))
              (trans (wk-subst G) (subst-lift-•ₛ G)))
        (trans (substCompEq G) (substSingletonComp G))

-- Pushing a substitution into a single substitution.

singleSubstLift : ∀ {σ} G t
                → subst σ (G [ t ])
                ≡ subst (liftSubst σ) G [ subst σ t ]
singleSubstLift G t =
  trans (substCompEq G)
        (trans (trans (substVar-to-subst (λ { zero → refl ; (suc x) → refl}) G)
                      (sym (substSingletonComp G)))
               (sym (substCompEq G)))

-- More specific laws.

idWkLiftSubstLemma : ∀ σ G
  → wk (lift (step id)) (subst (liftSubst σ) G) [ var 0 ]
  ≡ subst (liftSubst σ) G
idWkLiftSubstLemma σ G =
  trans (singleSubstWkComp (var zero) σ G)
        (substVar-to-subst (λ { zero → refl ; (suc x) → refl}) G)

substVarComp↑ : ∀ {t} σ x
  → (consSubst (wk1Subst idSubst) (subst (liftSubst σ) t) ₛ•ₛ liftSubst σ) x
  ≡ (liftSubst σ ₛ•ₛ consSubst (wk1Subst idSubst) t) x
substVarComp↑ σ zero = refl
substVarComp↑ σ (suc x) = trans (subst-wk (σ x)) (sym (wk≡subst (step id) (σ x)))

singleSubstLift↑ : ∀ σ G t
                 → subst (liftSubst σ) (G [ t ]↑)
                 ≡ subst (liftSubst σ) G [ subst (liftSubst σ) t ]↑
singleSubstLift↑ σ G t =
  trans (substCompEq G)
        (sym (trans (substCompEq G) (substVar-to-subst (substVarComp↑ σ) G)))

substConsComp : ∀ {σ t G}
       → subst (consSubst (λ x → σ (suc x)) (subst (tail σ) t)) G
       ≡ subst σ (subst (consSubst (λ x → var (suc x)) (wk1 t)) G)
substConsComp {t = t} {G = G} =
  trans (substVar-to-subst (λ { zero → sym (subst-wk t) ; (suc x) → refl }) G)
        (sym (substCompEq G))

wkSingleSubstId : ∀ F → (wk (lift (step id)) F) [ var zero ] ≡ F
wkSingleSubstId F =
  trans (subst-wk F)
        (trans (substVar-to-subst (λ { zero → refl ; (suc x) → refl}) F)
               (subst-id F))

cons-wk-subst : ∀ ρ σ a t
       → subst (sgSubst a ₛ• lift ρ ₛ•ₛ liftSubst σ) t
       ≡ subst (consSubst (ρ •ₛ σ) a) t
cons-wk-subst ρ σ a = substVar-to-subst
  (λ { zero → refl
     ; (suc x) → trans (subst-wk (σ x)) (sym (wk≡subst ρ (σ x))) })

natrecSucCaseLemma : ∀ {σ} (x : Nat)
  → (step id •ₛ consSubst (wk1Subst idSubst) (sucₑ (var zero)) ₛ•ₛ liftSubst σ) x
  ≡ (liftSubst (liftSubst σ) ₛ• step id ₛ•ₛ consSubst (wk1Subst idSubst) (sucₑ (var zero))) x
natrecSucCaseLemma zero = refl
natrecSucCaseLemma {σ} (suc x) =
  trans (subst-wk (σ x))
           (sym (trans (wk1-wk (step id) _)
                             (wk≡subst (step (step id)) (σ x))))

natrecSucCase : ∀ σ F
  → Πₑ ℕₑ ▹ (Πₑ subst (liftSubst σ) F
                ▹ subst (liftSubst (liftSubst σ)) (wk1 (F [ sucₑ (var zero) ]↑)))
  ≡ Πₑ ℕₑ ▹ (subst (liftSubst σ) F ▹▹ subst (liftSubst σ) F [ sucₑ (var zero) ]↑)
natrecSucCase σ F =
  cong₂ Πₑ_▹_ refl
    (cong₂ Πₑ_▹_ refl
       (trans (trans (subst-wk (F [ sucₑ (var zero) ]↑))
                           (substCompEq F))
                 (sym (trans (wk-subst (subst (liftSubst σ) F))
                                   (trans (substCompEq F)
                                             (substVar-to-subst natrecSucCaseLemma F))))))

natrecIrrelevantSubstLemma : ∀ F z s m σ (x : Nat)
  → (sgSubst (natrecₑ (subst (liftSubst σ) F) (subst σ z) (subst σ s) m)
     ₛ•ₛ liftSubst (sgSubst m)
     ₛ•ₛ liftSubst (liftSubst σ)
     ₛ•  step id
     ₛ•ₛ consSubst (tail idSubst) (sucₑ (var 0))) x
  ≡ (consSubst σ (sucₑ m)) x
natrecIrrelevantSubstLemma F z s m σ zero =
  cong sucₑ (trans (subst-wk m) (subst-id m))
natrecIrrelevantSubstLemma F z s m σ (suc x) =
  trans (subst-wk (wk (step id) (σ x)))
           (trans (subst-wk (σ x))
                     (subst-id (σ x)))

natrecIrrelevantSubst : ∀ F z s m σ
  → subst (consSubst σ (sucₑ m)) F
  ≡ subst (liftSubst (sgSubst m))
          (subst (liftSubst (liftSubst σ))
                 (wk1 (F [ sucₑ (var zero) ]↑)))
                   [ natrecₑ (subst (liftSubst σ) F) (subst σ z) (subst σ s) m ]
natrecIrrelevantSubst F z s m σ =
  sym (trans (substCompEq (subst (liftSubst (liftSubst σ))
        (wk (step id)
         (subst (consSubst (tail idSubst) (sucₑ (var 0))) F))))
         (trans (substCompEq (wk (step id)
        (subst (consSubst (tail idSubst) (sucₑ (var 0))) F)))
        (trans
           (subst-wk (subst (consSubst (tail idSubst) (sucₑ (var 0))) F))
           (trans (substCompEq F)
                     (substVar-to-subst (natrecIrrelevantSubstLemma F z s m σ) F)))))

natrecIrrelevantSubstLemma' : ∀ F z s n (x : Nat)
  → (sgSubst (natrecₑ F z s n)
     ₛ•ₛ liftSubst (sgSubst n)
     ₛ•  step id
     ₛ•ₛ consSubst (tail idSubst) (sucₑ (var zero))) x
  ≡ (consSubst var (sucₑ n)) x
natrecIrrelevantSubstLemma' F z s n zero =
  cong sucₑ (trans (subst-wk n) (subst-id n))
natrecIrrelevantSubstLemma' F z s n (suc x) = refl

natrecIrrelevantSubst' : ∀ F z s n
  → subst (liftSubst (sgSubst n))
      (wk1 (F [ sucₑ (var zero) ]↑))
      [ natrecₑ F z s n ]
  ≡ F [ sucₑ n ]
natrecIrrelevantSubst' F z s n =
  trans (substCompEq (wk (step id)
                         (subst (consSubst (tail idSubst) (sucₑ (var 0))) F)))
        (trans (subst-wk (subst (consSubst (tail idSubst) (sucₑ (var 0))) F))
               (trans (substCompEq F)
                      (substVar-to-subst (natrecIrrelevantSubstLemma' F z s n) F)))

cons0wkLift1-id : ∀ σ G
    → subst (sgSubst (var zero))
            (wk (lift (step id)) (subst (liftSubst σ) G))
    ≡ subst (liftSubst σ) G
cons0wkLift1-id σ G =
  trans (subst-wk (subst (liftSubst σ) G))
        (trans (substVar-to-subst (λ { zero → refl ; (suc x) → refl })
                                  (subst (liftSubst σ) G))
               (subst-id (subst (liftSubst σ) G)))

substConsId : ∀ {σ t} G
        → subst (consSubst σ (subst σ t)) G
        ≡ subst σ (subst (sgSubst t) G)
substConsId G =
  sym (trans (substCompEq G)
             (substVar-to-subst (λ { zero → refl ; (suc x) → refl}) G))

substConsTailId : ∀ {G t σ}
                → subst (consSubst (tail σ) (subst σ t)) G
                ≡ subst σ (subst (consSubst (tail idSubst) t) G)
substConsTailId {G} {t} {σ} =
  trans (substVar-to-subst (λ { zero → refl
                            ; (suc x) → refl }) G)
        (sym (substCompEq G))

substConcatSingleton' : ∀ {a σ} t
                      → subst (σ ₛ•ₛ sgSubst a) t
                      ≡ subst (consSubst σ (subst σ a)) t
substConcatSingleton' t = substVar-to-subst (λ { zero → refl ; (suc x) → refl}) t

wk1-tailId : ∀ t → wk1 t ≡ subst (tail idSubst) t
wk1-tailId t = trans (sym (subst-id (wk1 t))) (subst-wk t)
