{-# OPTIONS --without-K --safe #-}

module Erasure.Extraction.Properties where

open import Erasure.Extraction
open import Erasure.Target as T hiding (refl; trans)
open import Erasure.Target.Properties.Substitution

open import Definition.Modality.Erasure
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

wk-erase-comm : (ρ : U.Wk m n) (t : U.Term n) → wk (eraseWk ρ) (erase t) ≡ erase (U.wk ρ t)
wk-erase-comm ρ (var x) = cong var (wkVar-erase-comm ρ x)
wk-erase-comm ρ (gen Ukind []) = refl
wk-erase-comm ρ (gen (Pikind p q) (F ∷ G ∷ [])) = refl
wk-erase-comm ρ (gen (Lamkind p) (t ∷ [])) = cong T.lam (wk-erase-comm (lift ρ) t)
wk-erase-comm ρ (gen (Appkind 𝟘) (t ∷ u ∷ [])) = cong (_∘ undefined) (wk-erase-comm ρ t)
wk-erase-comm ρ (gen (Appkind ω) (t ∷ u ∷ [])) = cong₂ _∘_
  (wk-erase-comm ρ t)
  (wk-erase-comm ρ u)
wk-erase-comm ρ (gen (Sigmakind p) (F ∷ G ∷ [])) = refl
wk-erase-comm ρ (gen Prodkind (t ∷ u ∷ [])) = cong₂ T.prod
  (wk-erase-comm ρ t)
  (wk-erase-comm ρ u)
wk-erase-comm ρ (gen Fstkind (t ∷ [])) = cong T.fst (wk-erase-comm ρ t)
wk-erase-comm ρ (gen Sndkind (t ∷ [])) = cong T.snd (wk-erase-comm ρ t)
wk-erase-comm ρ (gen Natkind []) = refl
wk-erase-comm ρ (gen Zerokind []) = refl
wk-erase-comm ρ (gen Suckind (t ∷ [])) = cong T.suc (wk-erase-comm ρ t)
wk-erase-comm ρ (gen (Natreckind p q) (A ∷ z ∷ s ∷ n ∷ [])) = cong₃ T.natrec
  (wk-erase-comm ρ z)
  (wk-erase-comm (lift (lift ρ)) s)
  (wk-erase-comm ρ n)
wk-erase-comm ρ (gen Unitkind []) = refl
wk-erase-comm ρ (gen Starkind []) = refl
wk-erase-comm ρ (gen Emptykind []) = refl
wk-erase-comm ρ (gen (Emptyreckind p) (A ∷ t ∷ [])) = refl

-- Lifting substitutions commute with erase
-- liftSubst (eraseSubst σ) x ≡ eraseSubst (liftSubst σ) x

liftSubst-erase-comm : (x : Fin (1+ n)) → liftSubst (eraseSubst σ) x ≡ eraseSubst (U.liftSubst σ) x
liftSubst-erase-comm x0 = refl
liftSubst-erase-comm {σ = σ} (x +1) with σ x
... | var x₁ = refl
... | gen Ukind [] = refl
... | gen (Pikind p q) (F ∷ G ∷ []) = refl
... | gen (Lamkind p) (t ∷ []) = cong T.lam (wk-erase-comm (lift (step id)) t)
... | gen (Appkind 𝟘) (t ∷ u ∷ []) = cong (_∘ undefined) (wk-erase-comm (step id) t)
... | gen (Appkind ω) (t ∷ u ∷ []) = cong₂ _∘_
  (wk-erase-comm (step id) t)
  (wk-erase-comm (step id) u)
... | gen (Sigmakind p) (F ∷ G ∷ []) = refl
... | gen Prodkind (t ∷ u ∷ []) = cong₂ T.prod
  (wk-erase-comm (step id) t)
  (wk-erase-comm (step id) u)
... | gen Fstkind (t ∷ []) = cong T.fst (wk-erase-comm (step id) t)
... | gen Sndkind (t ∷ []) = cong T.snd (wk-erase-comm (step id) t)
... | gen Natkind [] = refl
... | gen Zerokind [] = refl
... | gen Suckind (t ∷ []) = cong T.suc (wk-erase-comm (step id) t)
... | gen (Natreckind p q) (A ∷ z ∷ s ∷ n ∷ []) = cong₃ T.natrec
  (wk-erase-comm (step id) z)
  (wk-erase-comm (lift (lift (step id))) s)
  (wk-erase-comm (step id) n)
... | gen Unitkind [] = refl
... | gen Starkind [] = refl
... | gen Emptykind [] = refl
... | gen (Emptyreckind p) (A ∷ t ∷ []) = refl

-- Multiple lifts commutes with erase
-- liftSubstn (eraseSubst σ) n x ≡ eraseSubst (liftSubstn σ n) x

liftSubsts-erase-comm : (k : Nat) (x : Fin (k +ⁿ n)) → T.liftSubstn (eraseSubst σ) k x ≡ eraseSubst (U.liftSubstn σ k) x
liftSubsts-erase-comm 0 x = refl
liftSubsts-erase-comm (1+ k) x0 = refl
liftSubsts-erase-comm {σ = σ} (1+ k) (x +1) = begin
  T.wk1 (T.liftSubstn (eraseSubst σ) k x)         ≡⟨ cong T.wk1 (liftSubsts-erase-comm k x) ⟩
  T.wk1 (eraseSubst (U.liftSubstn σ k) x)         ≡⟨⟩
  wk (step id) (eraseSubst (U.liftSubstn σ k) x)  ≡⟨ wk-erase-comm (U.step U.id) (U.liftSubstn σ k x) ⟩
  erase (U.wk (U.step U.id) (U.liftSubstn σ k x)) ≡⟨⟩
  eraseSubst (U.liftSubstn σ (1+ k)) (x +1)       ∎


-- Substitution commutes with erase (modulo translating substitution to target language)
-- subst (eraseSubst σ) (erase t) ≡ erase (U.subst σ t)

subst-erase-comm : (σ : U.Subst m n) (t : U.Term n) → T.subst (eraseSubst σ) (erase t) ≡ erase (U.subst σ t)
subst-erase-comm σ (var x) = refl
subst-erase-comm σ (gen Ukind []) = refl
subst-erase-comm σ (gen (Pikind p q) (F ∷ G ∷ [])) = refl
subst-erase-comm σ (gen (Lamkind 𝟘) (t ∷ [])) = cong Term.lam
  (begin
    T.subst (liftSubst (eraseSubst σ)) (erase t)
      ≡⟨ substVar-to-subst (liftSubsts-erase-comm 1) (erase t) ⟩
    T.subst (eraseSubst (U.liftSubst σ)) (erase t)
      ≡⟨ subst-erase-comm (U.liftSubst σ) t ⟩
    erase (U.subst (U.liftSubst σ) t) ∎)
subst-erase-comm σ (gen (Lamkind ω) (t ∷ [])) = cong T.lam (trans
  (substVar-to-subst liftSubst-erase-comm (erase t))
  (subst-erase-comm (U.liftSubst σ) t))
subst-erase-comm σ (gen (Appkind 𝟘) (t ∷ u ∷ [])) = cong (_∘ undefined) (subst-erase-comm σ t)
subst-erase-comm σ (gen (Appkind ω) (t ∷ u ∷ [])) = cong₂ _∘_
  (subst-erase-comm σ t)
  (subst-erase-comm σ u)
subst-erase-comm σ (gen (Sigmakind p) (F ∷ G ∷ [])) = refl
subst-erase-comm σ (gen Prodkind (t ∷ u ∷ [])) = cong₂ T.prod
  (subst-erase-comm σ t)
  (subst-erase-comm σ u)
subst-erase-comm σ (gen Fstkind (t ∷ [])) = cong T.fst (subst-erase-comm σ t)
subst-erase-comm σ (gen Sndkind (t ∷ [])) = cong T.snd (subst-erase-comm σ t)
subst-erase-comm σ (gen Natkind []) = refl
subst-erase-comm σ (gen Zerokind []) = refl
subst-erase-comm σ (gen Suckind (t ∷ [])) = cong T.suc (subst-erase-comm σ t)
subst-erase-comm σ (gen (Natreckind p q) (A ∷ z ∷ s ∷ n ∷ [])) = cong₃ T.natrec
  (subst-erase-comm σ z)
  (trans (substVar-to-subst (liftSubsts-erase-comm 2) (erase s))
         (subst-erase-comm (U.liftSubst (U.liftSubst σ)) s))
  (subst-erase-comm σ n)
subst-erase-comm σ (gen Unitkind []) = refl
subst-erase-comm σ (gen Starkind []) = refl
subst-erase-comm σ (gen Emptykind []) = refl
subst-erase-comm σ (gen (Emptyreckind p) (A ∷ t ∷ [])) = refl

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
