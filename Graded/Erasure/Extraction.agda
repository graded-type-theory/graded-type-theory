------------------------------------------------------------------------
-- The extraction function.
------------------------------------------------------------------------

open import Graded.Modality

module Graded.Erasure.Extraction
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open Modality 𝕄

open import Tools.Bool
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

mutual

  -- The extraction function.
  --
  -- Function and constructor applications are made strict if the
  -- first argument is "strict".
  --
  -- A non-terminating term, loop s, is used instead of ↯ in some
  -- places. The idea is that it should be safe to replace this term
  -- with, say, a term that throws an exception.

  erase : Strictness → U.Term n → T.Term n
  erase = erase′ false

  -- A variant of the extraction function.
  --
  -- If the boolean is true, then erasable arguments are removed
  -- entirely.

  erase′ : Bool → Strictness → U.Term n → T.Term n
  erase′ remove s = erase″
    where
    erase″ : U.Term n → T.Term n
    erase″ (var x)                 = T.var x
    erase″ U                       = ↯
    erase″ (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) = ↯
    erase″ (U.lam p t)             = case remove of λ where
      false → T.lam (erase″ t)
      true  → case is-𝟘? p of λ where
        (no _)  → T.lam (erase″ t)
        (yes _) → erase″ t T.[ ↯ ]₀
    erase″ (t U.∘⟨ p ⟩ u) = case is-𝟘? p of λ where
      (no _)  → erase″ t T.∘⟨ s ⟩ erase″ u
      (yes _) → case remove of λ where
        false → erase″ t T.∘⟨ s ⟩ ↯
        true  → erase″ t
    erase″ (U.prod _ p t u) = case is-𝟘? p of λ where
      (no _)  → prod⟨ s ⟩ (erase″ t) (erase″ u)
      (yes _) → erase″ u
    erase″ (U.fst p t) = case is-𝟘? p of λ where
      (no _)  → T.fst (erase″ t)
      (yes _) → loop s
    erase″ (U.snd p t) = case is-𝟘? p of λ where
      (no _)  → T.snd (erase″ t)
      (yes _) → erase″ t
    erase″ (U.prodrec r p _ _ t u) = case is-𝟘? r of λ where
      (no _)  → erase-prodrecω s p (erase″ t) (erase″ u)
      (yes _) → erase″ u T.[ loop s , loop s ]
    erase″ ℕ                        = ↯
    erase″ U.zero                   = T.zero
    erase″ (U.suc t)                = suc⟨ s ⟩ (erase″ t)
    erase″ (U.natrec p q r A t u v) =
      T.natrec (erase″ t) (erase″ u) (erase″ v)
    erase″ Unit!                 = ↯
    erase″ U.star!               = T.star
    erase″ (U.unitrec p q A t u) = case is-𝟘? p of λ where
      (no _)  → T.unitrec (erase″ t) (erase″ u)
      (yes _) → erase″ u
    erase″ Empty               = ↯
    erase″ (emptyrec p A t)    = loop s
    erase″ (Id _ _ _)          = ↯
    erase″ U.rfl               = ↯
    erase″ (J _ _ _ _ _ u _ _) = erase″ u
    erase″ (K _ _ _ _ u _)     = erase″ u
    erase″ ([]-cong _ _ _ _ _) = ↯

mutual

  -- Extraction of substitutions.

  eraseSubst : Strictness → U.Subst m n → T.Subst m n
  eraseSubst = eraseSubst′ false

  -- A variant of eraseSubst.

  eraseSubst′ : Bool → Strictness → U.Subst m n → T.Subst m n
  eraseSubst′ b s σ x = erase′ b s (σ x)
