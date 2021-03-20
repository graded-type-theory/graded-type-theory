-- Laws for weakenings and substitutions.

{-# OPTIONS --without-K --safe #-}

module Definition.Untyped.Properties where

open import Definition.Modality
open import Definition.Untyped

open import Tools.Fin
open import Tools.Nat
open import Tools.List
open import Tools.PropositionalEquality hiding (subst)

private
  variable
    M : Set
    ℓ m n : Nat
    ρ ρ′ : Wk m n
    η : Wk n ℓ
    σ σ′ : Subst M m n
    p q r : M
    𝕄 : Modality M

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
              → ∀ (t : Term M n) → wk ρ t ≡ wk ρ′ t
  wkVar-to-wk eq (var x)   = cong var (eq x)
  wkVar-to-wk eq (gen k c) = cong (gen k) (wkVar-to-wkGen eq c)

  wkVar-to-wkGen : (∀ x → wkVar ρ x ≡ wkVar ρ′ x)
                 → ∀ {bs} c → wkGen {bs = bs} ρ c ≡ wkGen {M = M} {bs = bs} ρ′ c
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
  wk-id : (t : Term M n) → wk id t ≡ t
  wk-id (var x)   = refl
  wk-id (gen k ts) = cong (gen k) (wkGen-id ts)

  wkGen-id : ∀ {bs} x → wkGen {M = M} {m = n} {n} {bs} id x ≡ x
  wkGen-id [] = refl
  wkGen-id (_∷_ {b = b} t ts) =
    cong₂ _∷_ (trans (wkVar-to-wk (wkVar-lifts-id b) t) ( wk-id t)) (wkGen-id ts)

-- lift id  is also the identity renaming.

wk-lift-id : (t : Term M (1+ n)) → wk (lift id) t ≡ t
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
  wk-comp : (ρ : Wk m ℓ) (ρ′ : Wk ℓ n) (t : Term M n) → wk ρ (wk ρ′ t) ≡ wk (ρ • ρ′) t
  wk-comp ρ ρ′ (var x) = cong var (wkVar-comp ρ ρ′ x)
  wk-comp {M = M} ρ ρ′ (gen k ts) = cong (gen k) (wkGen-comp {M = M} ρ ρ′ ts)

  wkGen-comp : (ρ : Wk m ℓ) (ρ′ : Wk ℓ n) → ∀ {bs} g
             → wkGen ρ (wkGen ρ′ g) ≡ wkGen {M = M} {bs = bs} (ρ • ρ′) g
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

wk1-wk : (ρ : Wk m n) (t : Term M n) → wk1 (wk ρ t) ≡ wk (step ρ) t
wk1-wk ρ t = wk-comp (step id) ρ t

lift-wk1 : (ρ : Wk m n) (t : Term M n) → wk (lift ρ) (wk1 t) ≡ wk (step ρ) t
lift-wk1 pr A = trans (wk-comp (lift pr) (step id) A)
                      (sym (cong (λ x → wk x A) (lift-step-comp pr)))

wk1-wk≡lift-wk1 : (ρ : Wk m n) (t : Term M n) → wk1 (wk ρ t) ≡ wk (lift ρ) (wk1 t)
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
                    → (t : Term M n) → subst σ t ≡ subst σ′ t
  substVar-to-subst eq (var x)    = eq x
  substVar-to-subst eq (gen k ts) = cong (gen k) (substVar-to-substGen eq ts)

  substVar-to-substGen : ∀ {bs} → ((x : Fin n) → σ x ≡ σ′ x)
                       → ∀ g → substGen {bs = bs} σ g ≡ substGen {bs = bs} σ′ g
  substVar-to-substGen eq [] = refl
  substVar-to-substGen eq (_∷_ {b = b} t ts) =
    cong₂ _∷_ (substVar-to-subst (substVar-lifts eq b) t)
              (substVar-to-substGen eq ts)


-- lift id = id  (as substitutions)

subst-lift-id : (x : Fin (1+ n)) → (liftSubst {M = M} idSubst) x ≡ idSubst x
subst-lift-id x0     = refl
subst-lift-id (x +1) = refl

subst-lifts-id : (n : Nat) → (x : Fin (n + m)) → (liftSubstn {M = M} idSubst n) x ≡ idSubst x
subst-lifts-id 0 x = refl
subst-lifts-id (1+ n) x0 = refl
subst-lifts-id (1+ n) (x +1) = cong wk1 (subst-lifts-id n x)

-- Identity substitution.

mutual
  subst-id : (t : Term M n) → subst idSubst t ≡ t
  subst-id (var x) = refl
  subst-id (gen k ts) = cong (gen k) (substGen-id ts)

  substGen-id : ∀ {bs} g → substGen {M = M} {m = n} {n} {bs} idSubst g ≡ g
  substGen-id [] = refl
  substGen-id (_∷_ {b = b} t ts) =
    cong₂ _∷_ (trans (substVar-to-subst (subst-lifts-id b) t )
                     (subst-id t))
              (substGen-id ts)


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
  wk-subst (gen k ts) = cong (gen k) (wkGen-substGen ts)

  wkGen-substGen : ∀ {bs} t → wkGen ρ (substGen σ t) ≡ substGen {bs = bs} (ρ •ₛ σ) t
  wkGen-substGen [] = refl
  wkGen-substGen (_∷_ {b = b} t ts) =
    cong₂ _∷_ (trans (wk-subst t) ( subst-lifts-•ₛ b t)) (wkGen-substGen ts)


-- subst σ ∘ wk ρ = subst (σ •ₛ ρ)

mutual
  subst-wk : ∀ t → subst σ (wk ρ t) ≡ subst (σ ₛ• ρ) t
  subst-wk (var x) = refl
  subst-wk (gen k ts) = cong (gen k) (substGen-wkGen ts)

  substGen-wkGen : ∀ {bs} t → substGen σ (wkGen ρ t) ≡ substGen {bs = bs} (σ ₛ• ρ) t
  substGen-wkGen [] = refl
  substGen-wkGen (_∷_ {b = b} t ts) =
    cong₂ _∷_ (trans (subst-wk t) (subst-lifts-ₛ• b t)) (substGen-wkGen ts)


-- Composition of liftings is lifting of the composition.

wk-subst-lift : (G : Term M (1+ n))
              → wk (lift ρ) (subst (liftSubst σ) G)
              ≡ subst (liftSubst (ρ •ₛ σ)) G
wk-subst-lift G = trans (wk-subst G) (subst-lift-•ₛ G)

-- Renaming with ρ is the same as substituting with ρ turned into a substitution.

wk≡subst : (ρ : Wk m n) (t : Term M n) → wk ρ t ≡ subst (toSubst ρ) t
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
  substCompEq : ∀ (t : Term M n)
              → subst σ (subst σ′ t) ≡ subst (σ ₛ•ₛ σ′) t
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

wk-comp-subst : ∀ {a : Term M m} (ρ : Wk m ℓ) (ρ′ : Wk ℓ n) G
  → wk (lift (ρ • ρ′)) G [ a ] ≡ wk (lift ρ) (wk (lift ρ′) G) [ a ]

wk-comp-subst {a = a} ρ ρ′ G =
  cong (λ x → x [ a ]) (sym (wk-comp (lift ρ) (lift ρ′) G))

-- Pushing a weakening into a single substitution.
-- ρ (t[a]) = ((lift ρ) t)[ρ a]

wk-β : ∀ {a : Term M m} t → wk ρ (t [ a ]) ≡ wk (lift ρ) t [ wk ρ a ]
wk-β t = trans (wk-subst t) (sym (trans (subst-wk t)
               (substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) t)))

-- Pushing a weakening into a single shifting substitution.
-- If  ρ′ = lift ρ  then  ρ′(t[a]↑) = ρ′(t) [ρ′(a)]↑

wk-β↑ : ∀ {a : Term M (1+ n)} t {ρ : Wk m n} → wk (lift ρ) (t [ a ]↑) ≡ wk (lift ρ) t [ wk (lift ρ) a ]↑
wk-β↑ t = trans (wk-subst t) (sym (trans (subst-wk t)
                (substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) t)))


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

singleSubstComp : ∀ t (σ : Subst M m n) G
                 → (subst (liftSubst σ) G) [ t ]
                 ≡ subst (consSubst σ t) G
singleSubstComp t σ G = trans (substCompEq G) (substSingletonComp G)

-- A single substitution after a lifted substitution (with weakening).
-- ((lift (ρ ∘ σ)) G)[t] = (cons (ρ ∘ σ) t)(G)

singleSubstWkComp : ∀ t (σ : Subst M m n) G
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

-- More specific laws.

idWkLiftSubstLemma : ∀ (σ : Subst M m n) G
  → wk (lift (step id)) (subst (liftSubst σ) G) [ var x0 ]
  ≡ subst (liftSubst σ) G
idWkLiftSubstLemma σ G =
  trans (singleSubstWkComp (var x0) σ G)
        (substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) G)

substVarComp↑ : ∀ {t} (σ : Subst M m n) x
  → (consSubst (wk1Subst idSubst) (subst (liftSubst σ) t) ₛ•ₛ liftSubst σ) x
  ≡ (liftSubst σ ₛ•ₛ consSubst (wk1Subst idSubst) t) x
substVarComp↑ σ x0 = refl
substVarComp↑ σ (x +1) = trans (subst-wk (σ x)) (sym (wk≡subst (step id) (σ x)))

singleSubstLift↑ : ∀ (σ : Subst M m n) G t
                 → subst (liftSubst σ) (G [ t ]↑)
                 ≡ subst (liftSubst σ) G [ subst (liftSubst σ) t ]↑
singleSubstLift↑ σ G t =
  trans (substCompEq G)
        (sym (trans (substCompEq G) (substVar-to-subst (substVarComp↑ σ) G)))

substConsComp : ∀ {t G}
       → subst (consSubst (λ x → σ (x +1)) (subst (tail σ) t)) G
       ≡ subst σ (subst (consSubst (λ x → var (x +1)) (wk1 t)) G)
substConsComp {t = t} {G = G} =
  trans (substVar-to-subst (λ { x0 → sym (subst-wk t) ; (x +1) → refl }) G)
        (sym (substCompEq G))

wkSingleSubstId : (F : Term M (1+ n)) → (wk (lift (step id)) F) [ var x0 ] ≡ F
wkSingleSubstId F =
  trans (subst-wk F)
        (trans (substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) F)
               (subst-id F))

cons-wk-subst : ∀ (ρ : Wk m n) (σ : Subst M n ℓ) a t
       → subst (sgSubst a ₛ• lift ρ ₛ•ₛ liftSubst σ) t
       ≡ subst (consSubst (ρ •ₛ σ) a) t
cons-wk-subst ρ σ a = substVar-to-subst
  (λ { x0 → refl
     ; (x +1) → trans (subst-wk (σ x)) (sym (wk≡subst ρ (σ x))) })

-- A specific equation on weakenings used for the reduction of natrec.

wk-β-natrec : ∀ (ρ : Wk m n) (G : Term M (1+ n))
            → wk (lift (lift ρ)) (wk1 (G [ suc (var x0) ]↑))
            ≡ wk1 (wk (lift ρ) G [ suc (var x0) ]↑)
wk-β-natrec ρ G = let G′ = G [ suc (var x0) ]↑ in
  begin
    wk (lift (lift ρ)) (wk (step id) G′)
      ≡⟨ wk-comp (lift (lift ρ)) (step id) G′ ⟩
    wk (step id • lift ρ) G′
      ≡⟨ sym (wk-comp (step id) (lift ρ) G′) ⟩
    wk1 (wk (lift ρ) G′)
      ≡⟨ cong wk1 (wk≡subst (lift ρ) (subst (consSubst (λ z → var (z +1)) (gen Suckind (var x0 ∷ []))) G)) ⟩
    wk1 (subst (toSubst (lift ρ)) G′)
      ≡⟨ cong wk1 (substVar-to-subst eq G′) ⟩
    wk1 (subst (liftSubst (toSubst ρ)) G′)
      ≡⟨ cong wk1 (singleSubstLift↑ (toSubst ρ) G (suc (var x0))) ⟩
    wk1 ((subst (liftSubst (toSubst ρ)) G) [ subst (liftSubst (toSubst ρ)) (suc (var x0)) ]↑)
      ≡⟨ cong wk1 (cong₂ _[_]↑ (sym (substVar-to-subst eq G)) (sym (substVar-to-subst eq (suc (var x0))))) ⟩
    wk1 ((subst (toSubst (lift ρ)) G) [ (subst (toSubst (lift ρ)) (suc (var x0))) ]↑)
      ≡⟨ cong wk1 (cong₂ _[_]↑ (sym (wk≡subst (lift ρ) G))(sym (wk≡subst (lift ρ) (suc (var x0))))) ⟩
    wk1 ((wk (lift ρ) G) [ (wk (lift ρ) (suc (var x0))) ]↑)
      ≡⟨ refl ⟩
    (wk1 ((wk (lift ρ) G) [ (suc (var x0)) ]↑)) ∎
  where
    eq : ∀ z → var (wkVar (lift ρ) z) ≡
         (liftSubst (λ x → var (wkVar ρ x))) z
    eq x0 = refl
    eq (_+1 z) = refl


-- A specific equation on eakenings used for the reduction of prodrec.

wk-β-prodrec : ∀ (ρ : Wk m n) (A : Term M (1+ n))
             → wk (lift (lift ρ)) (A [⟨ var (x0 +1) , var x0 ⟩])
             ≡ wk (lift ρ) A [⟨ var (x0 +1) , var x0 ⟩]
wk-β-prodrec ρ A =
  begin
       wk (lift (lift ρ)) (subst σₚ′ A)
         ≡⟨ wk-subst A ⟩
       subst (lift (lift ρ) •ₛ σₚ′) A
         ≡⟨ substVar-to-subst eq A ⟩
       subst (σₚ′ ₛ• (lift ρ)) A
         ≡⟨ sym (subst-wk A) ⟩
       subst σₚ′ (wk (lift ρ) A) ∎
     where
        σₚ′ : Subst M (1+ (1+ ℓ)) (1+ ℓ)
        σₚ′ = σₚ (var (x0 +1)) (var x0)
        eq  : ∀ x
            → substVar (lift (lift ρ) •ₛ σₚ′) x
            ≡ substVar σₚ′ (wkVar (lift ρ) x)
        eq x0 = refl
        eq (_+1 x) = refl

wk-β-doubleSubst : ∀ (ρ : Wk m n) (s : Term M (1+ (1+ n))) (t u : Term M n)
                 → wk ρ (s [ t ][ u ])
                 ≡ wk (lift (lift ρ)) s [ wk ρ t ][ wk ρ u ]
wk-β-doubleSubst ρ s t u =
 begin
    wk ρ (subst (σₜ t u) s)
       ≡⟨ wk-subst s ⟩
     subst (ρ •ₛ (σₜ t u)) s
       ≡⟨ substVar-to-subst eq s ⟩
     subst ((σₜ (wk ρ t) (wk ρ u)) ₛ• (lift (lift ρ))) s
       ≡⟨ sym (subst-wk s) ⟩
     wk (lift (lift ρ)) s [ wk ρ t ][ wk ρ u ] ∎
  where
    σₜ : (x y : Term M ℓ) → Subst M ℓ (1+ (1+ ℓ))
    σₜ x y = consSubst (consSubst idSubst y) x
    eq : ∀ x
       → substVar ((ρ •ₛ (σₜ t u))) x
       ≡ substVar (σₜ (wk ρ t) (wk ρ u)) (wkVar (lift (lift ρ)) x)
    eq x0 = refl
    eq (_+1 x0) = refl
    eq (_+1 (_+1 x)) = refl

natrecSucCaseLemma : (x : Fin (1+ n))
  → (step id •ₛ consSubst (wk1Subst idSubst) (suc (var x0)) ₛ•ₛ liftSubst σ) x
  ≡ (liftSubst (liftSubst σ) ₛ• step id ₛ•ₛ consSubst (wk1Subst idSubst) (suc (var x0))) x
natrecSucCaseLemma x0 = refl
natrecSucCaseLemma {σ = σ} (x +1) =
  trans (subst-wk (σ x))
           (sym (trans (wk1-wk (step id) _)
                             (wk≡subst (step (step id)) (σ x))))

natrecSucCase : ∀ (σ : Subst M m n) F
  → Π p , q ▷ ℕ ▹ (Π r , (Modality.𝟘 𝕄) ▷ subst (liftSubst σ) F
                ▹ subst (liftSubst (liftSubst σ)) (wk1 (F [ suc (var x0) ]↑)))
  ≡ Π p , q ▷ ℕ ▹ (𝕄 , r ▷ subst (liftSubst σ) F ▹▹ subst (liftSubst σ) F [ suc (var x0) ]↑)
natrecSucCase {p = p} {q} {r} {𝕄} σ F =
  cong₂ (Π p , q ▷_▹_) refl
    (cong₂ (Π r , (Modality.𝟘 𝕄) ▷_▹_) refl
       (trans (trans (subst-wk (F [ suc (var x0) ]↑))
                           (substCompEq F))
                 (sym (trans (wk-subst (subst (liftSubst σ) F))
                                   (trans (substCompEq F)
                                             (substVar-to-subst natrecSucCaseLemma F))))))

natrecIrrelevantSubstLemma : ∀ p q F z s m (σ : Subst M ℓ n) (x : Fin (1+ n))
  → (sgSubst (natrec p q
               (subst (liftSubst σ) F)
               (subst σ z)
               (subst (liftSubstn σ 2) s)
               m
             )
     ₛ•ₛ liftSubst (sgSubst m)
     ₛ•ₛ liftSubst (liftSubst σ)
     ₛ•  step id
     ₛ•ₛ consSubst (tail idSubst) (suc (var x0))) x
  ≡ (consSubst σ (suc m)) x
natrecIrrelevantSubstLemma p q F z s m σ x0 =
  cong suc (trans (subst-wk m) (subst-id m))
natrecIrrelevantSubstLemma p q F z s m σ (x +1) =
  trans (subst-wk (wk (step id) (σ x)))
           (trans (subst-wk (σ x))
                     (subst-id (σ x)))

natrecIrrelevantSubst : ∀ p q F z s m (σ : Subst M ℓ n)
  → subst (consSubst σ (suc m)) F
  ≡ subst (liftSubst (sgSubst m))
          (subst (liftSubst (liftSubst σ))
                 (wk1 (F [ suc (var x0) ]↑)))
                  [ natrec p q (subst (liftSubst σ) F) (subst σ z) (subst (liftSubstn σ 2) s) m ]
natrecIrrelevantSubst p q F z s m σ =
  sym (trans (substCompEq (subst (liftSubst (liftSubst σ))
        (wk (step id)
         (subst (consSubst (tail idSubst) (suc (var x0))) F))))
         (trans (substCompEq (wk (step id)
        (subst (consSubst (tail idSubst) (suc (var x0))) F)))
        (trans
           (subst-wk (subst (consSubst (tail idSubst) (suc (var x0))) F))
           (trans (substCompEq F)
                     (substVar-to-subst (natrecIrrelevantSubstLemma p q F z s m σ) F)))))

natrecIrrelevantSubstLemma′ : ∀ (p q : M) F z s n (x : Fin (1+ m))
  → (sgSubst (natrec p q F z s n)
     ₛ•ₛ liftSubst (sgSubst n)
     ₛ•  step id
     ₛ•ₛ consSubst (tail idSubst) (suc (var x0))) x
  ≡ (consSubst var (suc n)) x
natrecIrrelevantSubstLemma′ p q F z s n x0 =
  cong suc (trans (subst-wk n) (subst-id n))
natrecIrrelevantSubstLemma′ p q F z s n (x +1) = refl

natrecIrrelevantSubst′ : ∀ p q (F : Term M (1+ m)) z s n
  → subst (liftSubst (sgSubst n))
      (wk1 (F [ suc (var x0) ]↑))
      [ natrec _ _ F z s n ]
  ≡ F [ suc n ]
natrecIrrelevantSubst′ p q F z s n =
  trans (substCompEq (wk (step id)
                         (subst (consSubst (tail idSubst) (suc (var x0))) F)))
        (trans (subst-wk (subst (consSubst (tail idSubst) (suc (var x0))) F))
               (trans (substCompEq F)
                      (substVar-to-subst (natrecIrrelevantSubstLemma′ p q F z s n) F)))

cons0wkLift1-id : ∀ (σ : Subst M m n) G
    → subst (sgSubst (var x0))
            (wk (lift (step id)) (subst (liftSubst σ) G))
    ≡ subst (liftSubst σ) G
cons0wkLift1-id σ G =
  trans (subst-wk (subst (liftSubst σ) G))
        (trans (substVar-to-subst (λ { x0 → refl ; (x +1) → refl })
                                  (subst (liftSubst σ) G))
               (subst-id (subst (liftSubst σ) G)))

substConsId : ∀ {t} G
        → subst (consSubst σ (subst σ t)) G
        ≡ subst σ (subst (sgSubst t) G)
substConsId G =
  sym (trans (substCompEq G)
             (substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) G))

substConsTailId : ∀ {G t}
                → subst (consSubst (tail σ) (subst σ t)) G
                ≡ subst σ (subst (consSubst (tail idSubst) t) G)
substConsTailId {G = G} =
  trans (substVar-to-subst (λ { x0 → refl
                            ; (x +1) → refl }) G)
        (sym (substCompEq G))

substConcatSingleton′ : ∀ {a} t
                      → subst (σ ₛ•ₛ sgSubst a) t
                      ≡ subst (consSubst σ (subst σ a)) t
substConcatSingleton′ t = substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) t

wk1-tailId : (t : Term M n) → wk1 t ≡ subst (tail idSubst) t
wk1-tailId t = trans (sym (subst-id (wk1 t))) (subst-wk t)

wk1-sgSubst : ∀ (t : Term M n) t' → (wk1 t) [ t' ] ≡ t
wk1-sgSubst t t' rewrite wk1-tailId t =
  let substVar-sgSubst-tail : ∀ a n → (sgSubst a ₛ•ₛ tail idSubst) n ≡ idSubst n
      substVar-sgSubst-tail a n = refl
  in  trans (trans
        (substCompEq t)
        (substVar-to-subst (substVar-sgSubst-tail t') t))
      (subst-id t)
