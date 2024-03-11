------------------------------------------------------------------------
-- The extraction function.
------------------------------------------------------------------------

open import Graded.Modality

module Graded.Erasure.Extraction
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open Modality 𝕄

open import Tools.Function
open import Tools.Nat
open import Tools.Relation

open import Definition.Untyped M as U
open import Graded.Erasure.Target as T
open import Graded.Erasure.Target.Non-terminating

private
  variable
    m n : Nat
    Γ : Con U.Term n
    A t t′ u : U.Term n
    v v′ w : T.Term n
    p : M

-- Extraction for prodrec when the match is not erased.

erase-prodrecω :
  Strictness → M → T.Term n → T.Term (2+ n) → T.Term n
erase-prodrecω s p t u = case is-𝟘? p of λ where
    (yes p≡𝟘) → T.lam (u T.[ T.liftSubst (T.sgSubst (loop s)) ])
                  T.∘⟨ s ⟩ t
    (no p≢𝟘) → T.prodrec t u

-- The extraction function.
--
-- Function and constructor applications are made strict if the first
-- argument is "strict".
--
-- A non-terminating term, loop s, is used instead of ↯ in some
-- places. The idea is that it should be safe to replace this term
-- with, say, a term that throws an exception.

erase : Strictness → U.Term n → T.Term n
erase _ (var x) = T.var x
erase _ U = ↯
erase _ (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) = ↯
erase s (U.lam p t) = T.lam (erase s t)
erase s (t U.∘⟨ p ⟩ u) = case is-𝟘? p of λ where
  (yes p≡𝟘) → erase s t T.∘⟨ s ⟩ ↯
  (no p≢𝟘)  → erase s t T.∘⟨ s ⟩ (erase s u)
erase s (U.prod _ p t u) = case is-𝟘? p of λ where
  (yes p≡𝟘) → erase s u
  (no p≢𝟘) → prod⟨ s ⟩ (erase s t) (erase s u)
erase s (U.fst p t) = case is-𝟘? p of λ where
  (yes p≡𝟘) → loop s
  (no p≢𝟘) → T.fst (erase s t)
erase s (U.snd p t) = case is-𝟘? p of λ where
  (yes p≡𝟘) → erase s t
  (no p≢𝟘) → T.snd (erase s t)
erase s (U.prodrec r p _ _ t u) = case is-𝟘? r of λ where
  (yes r≡𝟘) → erase s u T.[ loop s , loop s ]
  (no r≢𝟘) → erase-prodrecω s p (erase s t) (erase s u)
erase _ ℕ = ↯
erase _ U.zero = T.zero
erase s (U.suc t) = suc⟨ s ⟩ (erase s t)
erase s (U.natrec p q r A t u v) =
  T.natrec (erase s t) (erase s u) (erase s v)
erase _ Unit! = ↯
erase _ U.star! = T.star
erase s (U.unitrec p q A t u) = case is-𝟘? p of λ where
  (yes p≡𝟘) → erase s u
  (no p≢𝟘) → T.unitrec (erase s t) (erase s u)
erase _ Empty = ↯
erase s (emptyrec p A t) = loop s
erase _ (Id _ _ _) = ↯
erase _ U.rfl = ↯
erase s (J _ _ _ _ _ u _ _) = erase s u
erase s (K _ _ _ _ u _) = erase s u
erase _ ([]-cong _ _ _ _ _) = ↯

-- Extraction of substitutions.

eraseSubst : Strictness → U.Subst m n → T.Subst m n
eraseSubst s σ x = erase s (σ x)
