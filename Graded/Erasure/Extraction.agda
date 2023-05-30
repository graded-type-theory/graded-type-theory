------------------------------------------------------------------------
-- The extraction function.
------------------------------------------------------------------------

open import Graded.Modality
open import Tools.Nullary
open import Tools.PropositionalEquality

module Graded.Erasure.Extraction {a} {M : Set a} (𝕄 : Modality M)
                                 (open Modality 𝕄)
                                 (is-𝟘? : (p : M) → Dec (p ≡ 𝟘)) where

open import Tools.Function
open import Tools.Nat

open import Definition.Untyped M as U
open import Graded.Erasure.Target as T

private
  variable
    m n : Nat
    Γ : Con U.Term n
    A t t′ u : U.Term n
    v v′ w : T.Term n
    p : M

-- Extraction for prodrec when the match is not erased.

erase-prodrecω : (p : M) (t : T.Term n) (u : T.Term (1+ (1+ n)))
               → T.Term n
erase-prodrecω p t u = case is-𝟘? p of λ where
    (yes p≡𝟘) → T.prodrec (T.prod ↯ t) u
    (no p≢𝟘) → T.prodrec t u

-- The extraction function.

erase : U.Term n → T.Term n
erase (var x) = T.var x
erase U = ↯
erase (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) = ↯
erase (U.lam p t) = T.lam (erase t)
erase (t ∘⟨ p ⟩ u) = case is-𝟘? p of λ where
  (yes p≡𝟘) → erase t T.∘ ↯
  (no p≢𝟘) → erase t T.∘ erase u
erase (U.prod _ p t u) = case is-𝟘? p of λ where
  (yes p≡𝟘) → erase u
  (no p≢𝟘) → T.prod (erase t) (erase u)
erase (U.fst p t) = case is-𝟘? p of λ where
  (yes p≡𝟘) → ↯
  (no p≢𝟘) → T.fst (erase t)
erase (U.snd p t) = case is-𝟘? p of λ where
  (yes p≡𝟘) → erase t
  (no p≢𝟘) → T.snd (erase t)
erase (U.prodrec r p _ _ t u) = case is-𝟘? r of λ where
  (yes r≡𝟘) → T.prodrec (T.prod ↯ ↯) (erase u)
  (no r≢𝟘) → erase-prodrecω p (erase t) (erase u)
erase ℕ = ↯
erase U.zero = T.zero
erase (U.suc t) = T.suc (erase t)
erase (U.natrec p q r A z s n) = T.natrec (erase z) (erase s) (erase n)
erase Unit = ↯
erase U.star = T.star
erase Empty = ↯
erase (Emptyrec p A t) = ↯

-- Extraction of substitutions.

eraseSubst : U.Subst m n → T.Subst m n
eraseSubst σ x = erase (σ x)

-- Extraction of weakenings.

eraseWk : U.Wk m n → T.Wk m n
eraseWk id = id
eraseWk (step ρ) = step (eraseWk ρ)
eraseWk (lift ρ) = lift (eraseWk ρ)
