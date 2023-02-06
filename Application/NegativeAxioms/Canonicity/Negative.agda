-- Proof that consistent negative axioms do not jeopardize canonicity.
-- https://www.cs.bham.ac.uk/~mhe/papers/negative-axioms.pdf

{-# OPTIONS --without-K --safe #-}

open import Tools.Relation


module Application.NegativeAxioms.Canonicity.Negative
  {a ℓ} (M′ : Setoid a ℓ) where

  -- {Γ : Con _ _ m}
  -- (nΓ : NegativeContext M′ {m = m} Γ)
  -- (consistent : ∀{t} → _⊢_∷_ M′ Γ t Empty → ⊥) where

open Setoid M′ using () renaming (Carrier to M)

open import Application.NegativeAxioms.NegativeType M′
open import Erasure.SucRed M′

open import Definition.Untyped M hiding (_∷_; ℕ≢B)
open import Definition.Typed M′
open import Definition.Typed.Properties M′
open import Definition.Typed.EqRelInstance M′
open import Definition.Typed.Consequences.Consistency M′
open import Definition.Typed.Consequences.Inequality M′
open import Definition.Typed.Consequences.Injectivity M′
open import Definition.Typed.Consequences.Inversion M′
open import Definition.Typed.Consequences.Reduction M′
open import Definition.Typed.Consequences.Syntactic M′

open import Definition.LogicalRelation M′
open import Definition.LogicalRelation.Irrelevance M′
open import Definition.LogicalRelation.Fundamental.Reducibility M′

open import Application.NegativeAxioms.NegativeContext M′
open import Definition.Conversion.FullReduction M′
open import Definition.Conversion.Consequences.Completeness M′

open import Tools.Empty
open import Tools.Nat
import Tools.PropositionalEquality as PE
open import Tools.Product
open import Tools.Sum using (_⊎_; inj₁; inj₂)


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
            (consistent : ∀ {t} → Γ ⊢ t ∷ Empty → ⊥) where

  -- Lemma: A neutral has negative type in a consistent negative/erased context.

  neNeg : (d : Γ ⊢ u ∷ A) (n : Neutral u) → NegativeType Γ A
  neNeg (var ⊢Γ h          ) (var x      ) = lookupNegative ⊢Γ nΓ h
  neNeg (d ∘ⱼ ⊢t           ) (∘ₙ n       ) =
    appNeg (neNeg d n) (refl (syntacticTerm d)) ⊢t
  neNeg (fstⱼ ⊢A A⊢B d     ) (fstₙ n     ) =
    fstNeg (neNeg d n) (refl (Σⱼ ⊢A ▹ A⊢B))
  neNeg (sndⱼ ⊢A A⊢B d     ) (sndₙ n     ) =
    sndNeg (neNeg d n) (refl (Σⱼ ⊢A ▹ A⊢B)) (fstⱼ ⊢A A⊢B d)
  neNeg (natrecⱼ _ _ _ d   ) (natrecₙ n  ) =
    let ⊢ℕ = refl (ℕⱼ (wfTerm d))
    in  ⊥-elim (¬negℕ (neNeg d n) ⊢ℕ)
  neNeg (prodrecⱼ ⊢A A⊢B _ d _) (prodrecₙ n) =
    let ⊢Σ = refl (Σⱼ ⊢A ▹ A⊢B)
    in  ⊥-elim (¬negΣᵣ (neNeg d n) ⊢Σ)
  neNeg (Emptyrecⱼ _ d     ) (Emptyrecₙ n) =
    ⊥-elim (consistent d)
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
  nfN (Πⱼ _ ▹ _)       (Πₙ _ _)   c = ⊥-elim (U≢ℕ c)
  nfN (Σⱼ _ ▹ _)       (Σₙ _ _)   c = ⊥-elim (U≢ℕ c)
  nfN (ℕⱼ _)           ℕₙ         c = ⊥-elim (U≢ℕ c)
  nfN (Emptyⱼ _)       Emptyₙ     c = ⊥-elim (U≢ℕ c)
  nfN (Unitⱼ _)        Unitₙ      c = ⊥-elim (U≢ℕ c)

  -- * Canonical forms
  nfN (lamⱼ _ _)      (lamₙ _)    c = ⊥-elim (ℕ≢Π (sym c))
  nfN (prodⱼ _ _ _ _) (prodₙ _ _) c = ⊥-elim (ℕ≢Σ (sym c))
  nfN (starⱼ _)       starₙ       c = ⊥-elim (ℕ≢Unitⱼ (sym c))
  -- q.e.d

   -- Terms of non-negative types reduce to non-neutrals

  ¬NeutralNf : Γ ⊢ t ∷ A → (NegativeType Γ A → ⊥)
             → ∃ λ u → Γ ⊢ t ⇒* u ∷ A × Whnf u × (Neutral u → ⊥)
  ¬NeutralNf ⊢t ¬negA =
    let u , whnfU , d = whNormTerm ⊢t
    in  u , redₜ d , whnfU , λ x → ¬negA (neNeg (⊢u-redₜ d) x)

  -- Canonicity theorem: Any well-typed term Γ ⊢ t ∷ ℕ
  -- reduces to a numeral under the ⇒ˢ* reduction.

  canonicityRed′ : ∀ {l} → (⊢Γ : ⊢ Γ)
                 → Γ ⊩⟨ l ⟩ t ∷ ℕ / ℕᵣ (idRed:*: (ℕⱼ ⊢Γ))
                 → ∃ λ v → Numeral v × Γ ⊢ t ⇒ˢ* v ∷ℕ
  canonicityRed′ {l = l} ⊢Γ (ℕₜ _ d n≡n (sucᵣ x)) =
    let v , numV , d′ = canonicityRed′ {l = l} ⊢Γ x
    in  suc v , sucₙ numV , ⇒ˢ*∷ℕ-trans (whred* (redₜ d)) (sucred* d′)
  canonicityRed′ ⊢Γ (ℕₜ _ d n≡n zeroᵣ) =
    zero , zeroₙ , whred* (redₜ d)
  canonicityRed′ ⊢Γ (ℕₜ n d n≡n (ne (neNfₜ neK ⊢k k≡k))) =
    let u , d′ , whU , ¬neU = ¬NeutralNf (⊢t-redₜ d) λ negℕ → ¬negℕ negℕ (refl (ℕⱼ ⊢Γ))
    in  ⊥-elim (¬neU (PE.subst Neutral (whrDet*Term (redₜ d , ne neK) (d′ , whU)) neK))

  canonicityRed : Γ ⊢ t ∷ ℕ → ∃ λ u → Numeral u × Γ ⊢ t ⇒ˢ* u ∷ℕ
  canonicityRed ⊢t with reducibleTerm ⊢t
  ... | [ℕ] , [t] =
    let ⊢Γ = wfTerm ⊢t
        [ℕ]′ = ℕᵣ {l = ¹} (idRed:*: (ℕⱼ ⊢Γ))
        [t]′ = irrelevanceTerm [ℕ] [ℕ]′ [t]
    in  canonicityRed′ {l = ¹} ⊢Γ [t]′

  -- Canonicity theorem: Any well-typed term Γ ⊢ t : ℕ is convertible to a numeral.

  canonicityEq : (⊢t : Γ ⊢ t ∷ ℕ) → ∃ λ u → Numeral u × Γ ⊢ t ≡ u ∷ ℕ
  canonicityEq ⊢t =
    let u , numU , d = canonicityRed ⊢t
    in  u , numU , subset*Termˢ d

  -- Q.E.D. 2023-01-24
