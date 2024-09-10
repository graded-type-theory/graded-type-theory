------------------------------------------------------------------------
-- Proof that consistent negative axioms do not jeopardize canonicity.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Application.NegativeAxioms.Canonicity
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Application.NegativeAxioms.NegativeType R
open import Graded.Erasure.SucRed R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Normal-form M type-variant
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Consequences.Inequality R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Reduction R
open import Definition.Typed.Consequences.Syntactic R

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Fundamental.Reducibility R
open import Definition.LogicalRelation.Substitution.Introductions R

open import Application.NegativeAxioms.NegativeContext R

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
import Tools.PropositionalEquality as PE
open import Tools.Product


-- Preliminaries
---------------------------------------------------------------------------

private
  Ty  = Term
  Cxt = Con Ty
  variable
    m  : Nat
    Γ   : Con Term m
    A B C : Term m
    t u   : Term m

module Main {Γ : Con Term m} (nΓ : NegativeContext Γ)
            (consistent : Consistent Γ) where

  -- Lemma: A neutral has negative type in a consistent negative/erased context.

  neNeg : (d : Γ ⊢ u ∷ A) (n : Neutral u) → NegativeType Γ A
  neNeg (var ⊢Γ h          ) (var x      ) = lookupNegative ⊢Γ nΓ h
  neNeg (d ∘ⱼ ⊢t           ) (∘ₙ n       ) =
    appNeg (neNeg d n) (refl (syntacticTerm d)) ⊢t
  neNeg (fstⱼ ⊢A A⊢B d     ) (fstₙ n     ) =
    fstNeg (neNeg d n) (refl (ΠΣⱼ ⊢A A⊢B (⊢∷ΠΣ→ΠΣ-allowed d)))
  neNeg (sndⱼ ⊢A A⊢B d     ) (sndₙ n     ) =
    sndNeg (neNeg d n) (refl (ΠΣⱼ ⊢A A⊢B (⊢∷ΠΣ→ΠΣ-allowed d)))
      (fstⱼ ⊢A A⊢B d)
  neNeg (natrecⱼ _ _ _ d   ) (natrecₙ n  ) =
    let ⊢ℕ = refl (ℕⱼ (wfTerm d))
    in  ⊥-elim (¬negℕ (neNeg d n) ⊢ℕ)
  neNeg (prodrecⱼ ⊢A A⊢B _ d _ ok) (prodrecₙ n) =
    let ⊢Σ = refl (ΠΣⱼ ⊢A A⊢B ok)
    in  ⊥-elim (¬negΣʷ (neNeg d n) ⊢Σ)
  neNeg (emptyrecⱼ _ d     ) (emptyrecₙ n) =
    ⊥-elim (consistent _ d)
  neNeg (unitrecⱼ _ d _ ok) (unitrecₙ _ n) =
    let ⊢Unit = refl (Unitⱼ (wfTerm d) ok)
    in  ⊥-elim (¬negUnit (neNeg d n) ⊢Unit)
  neNeg (Jⱼ _ ⊢t _ _ ⊢v ⊢w) (Jₙ w-ne) =
    ⊥-elim (¬negId (neNeg ⊢w w-ne) (refl (Idⱼ ⊢t ⊢v)))
  neNeg (Kⱼ ⊢t _ _ ⊢v _) (Kₙ v-ne) =
    ⊥-elim (¬negId (neNeg ⊢v v-ne) (refl (Idⱼ ⊢t ⊢t)))
  neNeg ([]-congⱼ ⊢t ⊢u ⊢v _) ([]-congₙ v-ne) =
    ⊥-elim (¬negId (neNeg ⊢v v-ne) (refl (Idⱼ ⊢t ⊢u)))
  neNeg (conv d c          ) n          = conv (neNeg d n) c

  -- Lemma: A normal form of type ℕ is a numeral in a consistent negative context.

  nfN : (d : Γ ⊢ u ∷ A)
      → (n : Nf u)
      → (c : Γ ⊢ A ≡ ℕ)
      → Numeral u

  -- Case: neutrals. The type cannot be ℕ since it must be negative.
  nfN d (ne n) c =
    ⊥-elim (¬negℕ (neNeg d (nfNeutral n)) c)

  -- Case: numerals.
  nfN (zeroⱼ x) zeroₙ   c = zeroₙ
  nfN (sucⱼ d) (sucₙ n) c = sucₙ (nfN d n c)

  -- Case: conversion.
  nfN (conv d c) n c' = nfN d n (trans c c')

  -- Impossible cases: type is not ℕ.

  -- * Canonical types
  nfN (Uⱼ _)      Uₙ          c = ⊥-elim (U≢ℕ c)
  nfN (ΠΣⱼ _ _ _) (ΠΣₙ _ _)   c = ⊥-elim (U≢ℕ c)
  nfN (ℕⱼ _)      ℕₙ          c = ⊥-elim (U≢ℕ c)
  nfN (Emptyⱼ _)  Emptyₙ      c = ⊥-elim (U≢ℕ c)
  nfN (Unitⱼ _ _) Unitₙ       c = ⊥-elim (U≢ℕ c)
  nfN (Idⱼ _ _ _) (Idₙ _ _ _) c = ⊥-elim (U≢ℕ c)

  -- * Canonical forms
  nfN (lamⱼ _ _ _)      (lamₙ _)    c = ⊥-elim (ℕ≢Π (sym c))
  nfN (prodⱼ _ _ _ _ _) (prodₙ _ _) c = ⊥-elim (ℕ≢Σ (sym c))
  nfN (starⱼ _ _)       starₙ       c = ⊥-elim (ℕ≢Unitⱼ (sym c))
  nfN (rflⱼ _)          rflₙ        c = ⊥-elim (Id≢ℕ c)
  -- q.e.d

   -- Terms of non-negative types reduce to non-neutrals

  ¬NeutralNf : Γ ⊢ t ∷ A → (NegativeType Γ A → ⊥)
             → ∃ λ u → Γ ⊢ t ↘ u ∷ A × (Neutral u → ⊥)
  ¬NeutralNf ⊢t ¬negA =
    let u , whnfU , d = whNormTerm ⊢t
    in  u , (redₜ d , whnfU) , λ x → ¬negA (neNeg (⊢u-redₜ d) x)

  -- Canonicity theorem: Any well-typed term Γ ⊢ t ∷ ℕ
  -- reduces to a numeral under the ⇒ˢ* reduction.

  canonicityRed′ : Γ ⊩ℕ t ∷ℕ → ∃ λ v → Numeral v × Γ ⊢ t ⇒ˢ* v ∷ℕ
  canonicityRed′ (ℕₜ _ d n≡n (sucᵣ x)) =
    let v , numV , d′ = canonicityRed′ x
    in  suc v , sucₙ numV , ⇒ˢ*∷ℕ-trans (whred* (redₜ d)) (sucred* d′)
  canonicityRed′ (ℕₜ _ d n≡n zeroᵣ) =
    zero , zeroₙ , whred* (redₜ d)
  canonicityRed′ (ℕₜ n d n≡n (ne (neNfₜ neK ⊢k k≡k))) =
    let u , d′ , ¬neU =
          ¬NeutralNf (⊢t-redₜ d)
            (flip ¬negℕ $ refl (ℕⱼ $ wfTerm $ ⊢t-redₜ d))
    in  ⊥-elim $ ¬neU $
        PE.subst Neutral (whrDet*Term (redₜ d , ne neK) d′) neK

  canonicityRed : Γ ⊢ t ∷ ℕ → ∃ λ u → Numeral u × Γ ⊢ t ⇒ˢ* u ∷ℕ
  canonicityRed = canonicityRed′ ∘→ ⊩∷ℕ⇔ .proj₁ ∘→ proj₂ ∘→ reducible-⊩∷

  -- Canonicity theorem: Any well-typed term Γ ⊢ t : ℕ is convertible to a numeral.

  canonicityEq : (⊢t : Γ ⊢ t ∷ ℕ) → ∃ λ u → Numeral u × Γ ⊢ t ≡ u ∷ ℕ
  canonicityEq ⊢t =
    let u , numU , d = canonicityRed ⊢t
    in  u , numU , subset*Termˢ d

  -- Q.E.D. 2023-01-24
