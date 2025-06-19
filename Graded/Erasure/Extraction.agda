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
open import Tools.Nat using (Nat; 2+)
open import Tools.Relation

open import Definition.Untyped M as U
open import Graded.Erasure.Target as T
open import Graded.Erasure.Target.Non-terminating

private
  variable
    m n l : Nat
    Γ : Con U.Term n
    A t t′ u : U.Term n
    v v′ w : T.Term n
    p : M

-- If the first argument is strict, then the result is ↯ (which is a
-- value), but if the first argument is non-strict, then the result is
-- loop non-strict (which does not reduce to a value).

loop? : Strictness → T.Term n
loop? non-strict = loop non-strict
loop? strict     = ↯

-- Extraction for prodrec when the match is not erased.

erase-prodrecω :
  Strictness → M → T.Term n → T.Term (2+ n) → T.Term n
erase-prodrecω s p t u = case is-𝟘? p of λ where
    (yes p≡𝟘) → T.lam (u T.[ T.liftSubst (T.sgSubst (loop s)) ])
                  T.∘⟨ s ⟩ t
    (no p≢𝟘) → T.prodrec t u

-- A function application that is used when the grade is 𝟘.
--
-- The argument is removed entirely if the boolean is true.

app-𝟘′ : Bool → Strictness → T.Term n → T.Term n
app-𝟘′ false s t = t T.∘⟨ s ⟩ loop? s
app-𝟘′ true  _ t = t

-- A variant of app-𝟘.

app-𝟘 : Strictness → T.Term n → T.Term n
app-𝟘 s = app-𝟘′ (s == non-strict) s

mutual

  -- The extraction function.
  --
  -- Function and constructor applications are made strict if the
  -- first argument is "strict".
  --
  -- Erasable arguments are removed entirely if the first argument is
  -- "non-strict".
  --
  -- A non-terminating term, loop s, is used in some places. The idea
  -- is that it should be safe to replace this term with, say, a term
  -- that throws an exception. The term loop? s is equal to loop s
  -- when s is non-strict, but if s is strict, then loop? s is ↯,
  -- which is a value.

  erase : Strictness → U.Term n → T.Term n
  erase s = erase′ (s == non-strict) s

  -- A variant of the extraction function.
  --
  -- If the boolean is true, then erasable arguments are removed
  -- entirely.

  erase′ : Bool → Strictness → U.Term n → T.Term n
  erase′ remove s = erase″
    where
    erase″ : U.Term n → T.Term n
    erase″ (var x)                 = T.var x
    erase″ (U _)                   = loop? s
    erase″ Level                   = loop? s
    erase″ zeroᵘ                   = loop? s
    erase″ (sucᵘ _)                = loop? s
    erase″ (_ maxᵘ _)              = loop? s
    erase″ (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) = loop? s
    erase″ (U.lam p t)             = case remove of λ where
      false → T.lam (erase″ t)
      true  → case is-𝟘? p of λ where
        (no _)  → T.lam (erase″ t)
        (yes _) → erase″ t T.[ loop s ]₀
    erase″ (t U.∘⟨ p ⟩ u) = case is-𝟘? p of λ where
      (no _)  → erase″ t T.∘⟨ s ⟩ erase″ u
      (yes _) → app-𝟘′ remove s (erase″ t)
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
      (yes _) → erase″ u T.[ loop s , loop s ]₁₀
    erase″ ℕ                        = loop? s
    erase″ U.zero                   = T.zero
    erase″ (U.suc t)                = suc⟨ s ⟩ (erase″ t)
    erase″ (U.natrec p q r A t u v) =
      T.natrec (erase″ t) (erase″ u) (erase″ v)
    erase″ Unit!                 = loop? s
    erase″ U.star!               = T.star
    erase″ (U.unitrec p _ _ _ t u) = case is-𝟘? p of λ where
      (no _)  → T.unitrec (erase″ t) (erase″ u)
      (yes _) → erase″ u
    erase″ Empty               = loop? s
    erase″ (emptyrec p A t)    = loop s
    erase″ (Id _ _ _)          = loop? s
    erase″ U.rfl               = loop? s
    erase″ (J _ _ _ _ _ u _ _) = erase″ u
    erase″ (K _ _ _ _ u _)     = erase″ u
    erase″ ([]-cong _ _ _ _ _) = loop? s

mutual

  -- Extraction of substitutions.

  eraseSubst : Strictness → U.Subst m n → T.Subst m n
  eraseSubst = eraseSubst′ false

  -- A variant of eraseSubst.

  eraseSubst′ : Bool → Strictness → U.Subst m n → T.Subst m n
  eraseSubst′ b s σ x = erase′ b s (σ x)
