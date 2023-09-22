------------------------------------------------------------------------
-- Laws for substiutions in the target language.
------------------------------------------------------------------------

module Graded.Erasure.Target.Properties.Substitution where

open import Graded.Erasure.Target hiding (refl ; trans)
open import Graded.Erasure.Target.Properties.Weakening

open import Tools.Fin
open import Tools.Nat
open import Tools.PropositionalEquality hiding (subst)
open import Tools.Reasoning.PropositionalEquality

private
  variable
    ℓ m n : Nat
    ρ ρ′ : Wk m n
    σ σ′ : Subst m n
    t : Term n

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

-- If  σ = σ′  then  t [ σ ] = t [ σ′ ].

mutual
  substVar-to-subst : ((x : Fin n) → σ x ≡ σ′ x)
                    → (t : Term n) → t [ σ ] ≡ t [ σ′ ]
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
  substVar-to-subst _  rfl = refl
  substVar-to-subst eq ↯ = refl


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
  subst-id rfl = refl
  subst-id ↯ = refl


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
  wk-subst rfl = refl
  wk-subst ↯ = refl

-- _[ σ ] ∘ wk ρ = _[ σ •ₛ ρ ]

mutual
  subst-wk : ∀ t → wk ρ t [ σ ] ≡ t [ σ ₛ• ρ ]
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
  subst-wk rfl = refl
  subst-wk ↯ = refl


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
              → t [ σ′ ] [ σ ] ≡ t [ σ ₛ•ₛ σ′ ]
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
  substCompEq rfl = refl
  substCompEq ↯ = refl

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

-- Pushing a lifted weakening into a lifted single substitution.

wk-lift-β :
  ∀ u →
  wk (lift ρ) (u [ liftSubst (sgSubst t) ]) ≡
  wk (lift (lift ρ)) u [ liftSubst (sgSubst (wk ρ t)) ]
wk-lift-β {ρ = ρ} {t = t} u =
  wk (lift ρ) (u [ liftSubst (sgSubst t) ])              ≡⟨ wk-subst u ⟩
  u [ lift ρ •ₛ liftSubst (sgSubst t) ]                  ≡˘⟨ substVar-to-subst
                                                                     (λ where
                                                                        x0          → refl
                                                                        (x0 +1)     → wk1-wk≡lift-wk1 _ _
                                                                        ((_ +1) +1) → refl)
                                                                     u ⟩
  u [ liftSubst (sgSubst (wk ρ t)) ₛ• lift (lift ρ) ]    ≡˘⟨ subst-wk u ⟩
  wk (lift (lift ρ)) u [ liftSubst (sgSubst (wk ρ t)) ]  ∎

-- Pushing a weakening into a double substitution
-- ρ (t[a,b]) = ((lift (lift ρ)) t) [ ρ a , ρ b ]

wk-β-doubleSubst : ∀ (ρ : Wk m n) (s : Term (1+ (1+ n))) (t u : Term n)
                 → wk ρ (s [ u , t ])
                 ≡ wk (lift (lift ρ)) s [ wk ρ u , wk ρ t ]
wk-β-doubleSubst ρ s t u =
 begin
    wk ρ (s [ σₜ t u ])
       ≡⟨ wk-subst s ⟩
     s [ ρ •ₛ (σₜ t u) ]
       ≡⟨ substVar-to-subst (λ { x0 → refl ; (x0 +1) → refl ; (x +1 +1) → refl}) s ⟩
     s [ (σₜ (wk ρ t) (wk ρ u)) ₛ• (lift (lift ρ)) ]
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
  → t [ sgSubst a ₛ•ₛ liftSubst σ ] ≡ t [ consSubst σ a ]
substSingletonComp = substVar-to-subst substVarSingletonComp

-- A single substitution after a lifted substitution.
-- ((lift σ) G)[t] = (cons σ t)(G)

singleSubstComp : ∀ t (σ : Subst m n) G
                 → G [ liftSubst σ ] [ t ]₀
                 ≡ G [ consSubst σ t ]
singleSubstComp t σ G = trans (substCompEq G) (substSingletonComp G)

-- A single substitution after a lifted substitution (with weakening).
-- ((lift (ρ ∘ σ)) G)[t] = (cons (ρ ∘ σ) t)(G)

singleSubstWkComp : ∀ t (σ : Subst m n) G
               → wk (lift ρ) (G [ liftSubst σ ]) [ t ]₀
               ≡ G [ consSubst (ρ •ₛ σ) t ]
singleSubstWkComp t σ G =
  trans (cong (_[ t ]₀)
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

-- Pushing a substiution into a double substitution

doubleSubstLift : (σ : Subst m n) (G : Term (1+ (1+ n))) (t u : Term n)
                → G [ t , u ] [ σ ]
                ≡ G [ liftSubstn σ 2 ] [ t [ σ ] , u [ σ ] ]
doubleSubstLift {n = n} σ G t u = begin
  G [ t , u ] [ σ ]
    ≡⟨⟩
  G [ consSubst (sgSubst t) u ] [ σ ]
    ≡⟨ substCompEq G ⟩
  G [ σ ₛ•ₛ consSubst (sgSubst t) u ]
    ≡⟨ substVar-to-subst eq G ⟩
  G [ (consSubst (sgSubst (t [ σ ])) (u [ σ ])) ₛ•ₛ (liftSubst (liftSubst σ)) ]
    ≡˘⟨ substCompEq G ⟩
  G [ liftSubstn σ 2 ] [ consSubst (sgSubst (t [ σ ])) (u [ σ ]) ]
    ≡⟨⟩
  G [ liftSubstn σ 2 ] [ t [ σ ] , u [ σ ] ] ∎
  where
  σ₁ =  consSubst (sgSubst t) u
  σ₂ = consSubst (sgSubst (t [ σ ])) (u [ σ ])
  eq : (x : Fin (1+ (1+ n))) → (σ ₛ•ₛ σ₁) x ≡ (σ₂ ₛ•ₛ (liftSubstn σ 2)) x
  eq x0 = refl
  eq (_+1 x0) = refl
  eq (x +1 +1) = begin
    (σ ₛ•ₛ σ₁) (x +1 +1)                         ≡⟨⟩
    σ x                                          ≡˘⟨ subst-id (σ x) ⟩
    (σ x) [ idSubst ]                            ≡⟨⟩
    (σ x) [ σ₂ ₛ• (step id • step id) ]          ≡˘⟨ subst-wk (σ x) ⟩
    wk ((step id) • (step id)) (σ x) [ σ₂ ]      ≡˘⟨ cong (_[ σ₂ ]) (wk-comp (step id) (step id) (σ x)) ⟩
    wk1 (wk1 (σ x)) [     σ₂ ]                   ≡⟨⟩
    (σ₂ ₛ•ₛ (liftSubst (liftSubst σ))) (x +1 +1) ∎

wk1-tail : (t : Term n) → wk1 t [ σ ] ≡ t [ tail σ ]
wk1-tail {σ = σ} t = begin
  wk1 t [ σ ]           ≡⟨⟩
  wk (step id) t [ σ ]  ≡⟨ subst-wk t ⟩
  t [ σ ₛ• step id ]    ≡⟨⟩
  t [ tail σ ]          ∎

wk1-tailId : (t : Term n) → wk1 t ≡ t [ tail idSubst ]
wk1-tailId t = trans (sym (subst-id (wk1 t))) (subst-wk t)

wk1-sgSubst : ∀ (t : Term n) t' → (wk1 t) [ t' ]₀ ≡ t
wk1-sgSubst t t' rewrite wk1-tailId t =
  let substVar-sgSubst-tail : ∀ a n → (sgSubst a ₛ•ₛ tail idSubst) n ≡ idSubst n
      substVar-sgSubst-tail a n = refl
  in  trans (trans
        (substCompEq t)
        (substVar-to-subst (substVar-sgSubst-tail t') t))
      (subst-id t)

doubleSubstComp : (A : Term (1+ (1+ n))) (t u : Term m) (σ : Subst m n)
                → A [ liftSubstn σ 2 ] [ t , u ]
                ≡ A [ consSubst (consSubst σ t) u ]
doubleSubstComp {n = n} A t u σ = begin
  A [ liftSubstn σ 2 ] [ t , u ]
    ≡⟨ substCompEq A ⟩
  A [ consSubst (consSubst idSubst t) u ₛ•ₛ liftSubstn σ 2 ]
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

-- Lifted substitutions kind of commute with lifted single
-- substitutions.

subst-liftSubst-sgSubst :
  ∀ u →
  u [ liftSubst (sgSubst t) ] [ liftSubst σ ] ≡
  u [ liftSubstn σ 2 ] [ liftSubst (sgSubst (t [ σ ])) ]
subst-liftSubst-sgSubst {t = t} {σ = σ} u =
  u [ liftSubst (sgSubst t) ] [ liftSubst σ ]                      ≡⟨ substCompEq u ⟩
  u [ liftSubst σ ₛ•ₛ liftSubst (sgSubst t) ]                      ≡⟨ substVar-to-subst substCompLift u ⟩
  u [ liftSubst (σ ₛ•ₛ sgSubst t) ]                                ≡˘⟨ substVar-to-subst
                                                                             (substVar-lift λ where
                                                                                x0     → refl
                                                                                (_ +1) → wk1-sgSubst _ _)
                                                                             u ⟩
  u [ liftSubst (sgSubst (t [ σ ]) ₛ•ₛ liftSubst σ) ]              ≡˘⟨ substVar-to-subst substCompLift u ⟩
  u [ liftSubst (sgSubst (t [ σ ])) ₛ•ₛ liftSubst (liftSubst σ) ]  ≡˘⟨ substCompEq u ⟩
  u [ liftSubstn σ 2 ] [ liftSubst (sgSubst (t [ σ ])) ]           ∎
