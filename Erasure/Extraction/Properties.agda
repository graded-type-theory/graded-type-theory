{-# OPTIONS --without-K --safe #-}

module Erasure.Extraction.Properties where

open import Erasure.Extraction
open import Erasure.Target as T hiding (refl; trans)
open import Erasure.Target.Properties.Substitution

open import Definition.Modality.Instances.Erasure
open import Definition.Untyped Erasure as U hiding (Wk; Term; wk; wkVar; _[_]; _[_,_]; liftSubst)

open import Tools.Fin
open import Tools.Nat renaming (_+_ to _+ⁿ_)
open import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private
  variable
    m n : Nat
    σ : U.Subst m n

-- weakenings act the same on variables of both target and source languages
-- wkVar (eraseWk ρ) x ≡ wkVar ρ x

wkVar-erase-comm : (ρ : U.Wk m n) (x : Fin n) → wkVar (eraseWk ρ) x ≡ U.wkVar ρ x
wkVar-erase-comm id x = refl
wkVar-erase-comm (step ρ) x = cong _+1 (wkVar-erase-comm ρ x)
wkVar-erase-comm (lift ρ) x0 = refl
wkVar-erase-comm (lift ρ) (x +1) = cong _+1 (wkVar-erase-comm ρ x)

-- wk commutes with erase (modulo translating weakening to target language)
-- wk (eraseWk ρ) (erase t) ≡ erase (wk ρ t)

wk-erase-comm : (ρ : U.Wk m n) (t : U.Term n)
              → wk (eraseWk ρ) (erase t) ≡ erase (U.wk ρ t)
wk-erase-comm ρ (var x) = cong var (wkVar-erase-comm ρ x)
wk-erase-comm ρ U = refl
wk-erase-comm ρ (Π p , w ▷ F ▹ G) = refl
wk-erase-comm ρ (U.lam p t) =
  cong T.lam (wk-erase-comm (lift ρ) t)
wk-erase-comm ρ (t ∘⟨ 𝟘 ⟩ u) =
  cong (T._∘ undefined) (wk-erase-comm ρ t)
wk-erase-comm ρ (t ∘⟨ ω ⟩ u) =
  cong₂ T._∘_ (wk-erase-comm ρ t) (wk-erase-comm ρ u)
wk-erase-comm ρ (Σ q ▷ F ▹ G) = refl
wk-erase-comm ρ (prod! t u) =
  cong₂ T.prod (wk-erase-comm ρ t) (wk-erase-comm ρ u)
wk-erase-comm ρ (U.fst t) =
  cong T.fst (wk-erase-comm ρ t)
wk-erase-comm ρ (U.snd t) =
  cong T.snd (wk-erase-comm ρ t)
wk-erase-comm ρ (U.prodrec 𝟘 A t u) =
  trans (wk-β-doubleSubst (eraseWk ρ) (erase u) undefined undefined)
        (PE.cong (_[ _ , _ ]) (wk-erase-comm (lift (lift ρ)) u))
wk-erase-comm ρ (U.prodrec ω A t u) =
  cong₂ T.prodrec (wk-erase-comm ρ t) (wk-erase-comm (lift (lift ρ)) u)
wk-erase-comm ρ ℕ = refl
wk-erase-comm ρ U.zero = refl
wk-erase-comm ρ (U.suc t) =
  cong T.suc (wk-erase-comm ρ t)
wk-erase-comm ρ (U.natrec p r A z s n) =
  cong₃ T.natrec (wk-erase-comm ρ z)
                 (wk-erase-comm (lift (lift ρ)) s)
                 (wk-erase-comm ρ n)
wk-erase-comm ρ Unit = refl
wk-erase-comm ρ U.star = refl
wk-erase-comm ρ Empty = refl
wk-erase-comm ρ (Emptyrec p A t) = refl

-- Lifting substitutions commute with erase
-- liftSubst (eraseSubst σ) x ≡ eraseSubst (liftSubst σ) x

liftSubst-erase-comm : (x : Fin (1+ n))
                     → liftSubst (eraseSubst σ) x ≡ eraseSubst (U.liftSubst σ) x
liftSubst-erase-comm x0 = refl
liftSubst-erase-comm {σ = σ} (x +1) with σ x
... | var x₁ = refl
... | U = refl
... | Π p , q ▷ F ▹ G = refl
... | U.lam p t =
  cong T.lam (wk-erase-comm (lift (step id)) t)
... | t ∘⟨ 𝟘 ⟩ u =
  cong (T._∘ undefined) (wk-erase-comm (step id) t)
... | t ∘⟨ ω ⟩ u =
  cong₂ T._∘_ (wk-erase-comm (step id) t) (wk-erase-comm (step id) u)
... | Σ q ▷ F ▹ G = refl
... | prod! t u =
  cong₂ T.prod (wk-erase-comm (step id) t) (wk-erase-comm (step id) u)
... | U.fst t = cong T.fst (wk-erase-comm (step id) t)
... | U.snd t = cong T.snd (wk-erase-comm (step id) t)
... | U.prodrec 𝟘 A t u =
  PE.trans (wk-β-doubleSubst (step id) (erase u) undefined undefined)
           (PE.cong (_[ _ , _ ]) (wk-erase-comm (lift (lift (step id))) u))
... | U.prodrec ω A t u =
  cong₂ Term.prodrec (wk-erase-comm (step id) t)
                     (wk-erase-comm (lift (lift (step id))) u)
... | ℕ = refl
... | U.zero = refl
... | U.suc t = cong T.suc (wk-erase-comm (step id) t)
... | U.natrec p r A z s n =
  cong₃ T.natrec (wk-erase-comm (step id) z)
                 (wk-erase-comm (lift (lift (step id))) s)
                 (wk-erase-comm (step id) n)
... | Unit = refl
... | U.star = refl
... | Empty = refl
... | Emptyrec p A t = refl

-- Multiple lifts commutes with erase
-- liftSubstn (eraseSubst σ) n x ≡ eraseSubst (liftSubstn σ n) x

liftSubsts-erase-comm : (k : Nat) (x : Fin (k +ⁿ n))
                      → T.liftSubstn (eraseSubst σ) k x ≡ eraseSubst (U.liftSubstn σ k) x
liftSubsts-erase-comm 0 x = refl
liftSubsts-erase-comm (1+ k) x0 = refl
liftSubsts-erase-comm {σ = σ} (1+ k) (x +1) = begin
  T.wk1 (T.liftSubstn (eraseSubst σ) k x)
    ≡⟨ cong T.wk1 (liftSubsts-erase-comm k x) ⟩
  T.wk1 (eraseSubst (U.liftSubstn σ k) x)
    ≡⟨⟩
  wk (step id) (eraseSubst (U.liftSubstn σ k) x)
    ≡⟨ wk-erase-comm (U.step U.id) (U.liftSubstn σ k x) ⟩
  erase (U.wk (U.step U.id) (U.liftSubstn σ k x))
    ≡⟨⟩
  eraseSubst (U.liftSubstn σ (1+ k)) (x +1)       ∎


-- Substitution commutes with erase (modulo translating substitution to target language)
-- subst (eraseSubst σ) (erase t) ≡ erase (U.subst σ t)

subst-erase-comm : (σ : U.Subst m n) (t : U.Term n)
                 → T.subst (eraseSubst σ) (erase t) ≡ erase (U.subst σ t)
subst-erase-comm σ (var x) = refl
subst-erase-comm σ U = refl
subst-erase-comm σ (Π p , q ▷ F ▹ G) = refl
subst-erase-comm σ (U.lam p t) =
  cong Term.lam
    (begin
      T.subst (liftSubst (eraseSubst σ)) (erase t)
        ≡⟨ substVar-to-subst (liftSubsts-erase-comm 1) (erase t) ⟩
      T.subst (eraseSubst (U.liftSubst σ)) (erase t)
        ≡⟨ subst-erase-comm (U.liftSubst σ) t ⟩
      erase (U.subst (U.liftSubst σ) t) ∎)
subst-erase-comm σ (t ∘⟨ 𝟘 ⟩ u) =
  cong (T._∘ undefined) (subst-erase-comm σ t)
subst-erase-comm σ (t ∘⟨ ω ⟩ u) =
  cong₂ T._∘_ (subst-erase-comm σ t) (subst-erase-comm σ u)
subst-erase-comm σ (Σ q ▷ F ▹ G) = refl
subst-erase-comm σ (prod! t u) =
  cong₂ T.prod (subst-erase-comm σ t) (subst-erase-comm σ u)
subst-erase-comm σ (U.fst t) = cong T.fst (subst-erase-comm σ t)
subst-erase-comm σ (U.snd t) = cong T.snd (subst-erase-comm σ t)
subst-erase-comm σ (U.prodrec 𝟘 A t u) =
  trans (doubleSubstLift (eraseSubst σ) (erase u) undefined undefined)
        (cong (_[ _ , _ ]) (trans (substVar-to-subst (liftSubsts-erase-comm 2) (erase u))
                                  (subst-erase-comm (U.liftSubstn σ 2) u)))
subst-erase-comm σ (U.prodrec ω A t u) =
  cong₂ Term.prodrec (subst-erase-comm σ t)
        (trans (substVar-to-subst (liftSubsts-erase-comm 2) (erase u))
               (subst-erase-comm (U.liftSubstn σ 2) u))
subst-erase-comm σ ℕ = refl
subst-erase-comm σ U.zero = refl
subst-erase-comm σ (U.suc t) = cong T.suc (subst-erase-comm σ t)
subst-erase-comm σ (U.natrec p r A z s n) = cong₃ T.natrec
  (subst-erase-comm σ z)
  (trans (substVar-to-subst (liftSubsts-erase-comm 2) (erase s))
         (subst-erase-comm (U.liftSubst (U.liftSubst σ)) s))
  (subst-erase-comm σ n)
subst-erase-comm σ Unit = refl
subst-erase-comm σ U.star = refl
subst-erase-comm σ Empty = refl
subst-erase-comm σ (Emptyrec p A t) = refl

subst-undefined : (x : Fin (1+ n)) →
      erase (U.consSubst var Empty x) ≡
      T.consSubst var undefined x
subst-undefined x0 = refl
subst-undefined (x +1) = refl

erase-consSubst-var : (σ : U.Subst m n) (a : U.Term m) (x : Fin (1+ n))
                    → T.consSubst (eraseSubst σ) (erase a) x
                    ≡ eraseSubst (U.consSubst σ a) x
erase-consSubst-var σ a x0 = refl
erase-consSubst-var σ a (x +1) = refl

erase-consSubst : (σ : U.Subst m n) (a : U.Term m) (t : T.Term (1+ n))
                → T.subst (T.consSubst (eraseSubst σ) (erase a)) t
                ≡ T.subst (eraseSubst (U.consSubst σ a)) t
erase-consSubst σ a t = substVar-to-subst (erase-consSubst-var σ a) t
