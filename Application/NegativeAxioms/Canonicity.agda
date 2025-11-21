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
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Untyped.Normal-form M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Syntactic R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Consequences.Inequality R
open import Definition.Typed.Consequences.Reduction R
import Definition.Typed.Weakening R as W

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Fundamental.Reducibility R
open import Definition.LogicalRelation.Substitution.Introductions R
open import Definition.LogicalRelation.Unary R

open import Application.NegativeAxioms.NegativeContext R

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
import Tools.PropositionalEquality as PE
open import Tools.Product


-- Preliminaries
---------------------------------------------------------------------------

private variable
  m n   : Nat
  Γ     : Cons _ _
  A B C : Term _
  t u   : Term _

module Main {Γ : Cons m n} (nΓ : NegativeContext Γ)
            (consistent : Consistent Γ) where

  -- Lemma: A neutral has a negative type in a consistent, negative
  -- context (given a certain assumption).

  neNeg :
    ⦃ ok : No-equality-reflection or-empty Γ .vars ⦄ →
    Γ ⊢ u ∷ A → Neutral⁺ (Γ .defs) u → NegativeType Γ A
  neNeg (var ⊢Γ x∈) (var _ _) =
    lookupNegative ⊢Γ nΓ x∈
  neNeg (defn ⊢Γ α↦₁ PE.refl) (defn α↦₂) =
    PE.subst (NegativeType _ ∘→ wk _)
      (unique-↦∈ (↦⊘∈⇒↦∈ α↦₂) α↦₁ PE.refl) $
    wkNeg (W.wk₀∷ʷ⊇ ⊢Γ) $
    lookupOpaqueNegative α↦₂ (defn-wf ⊢Γ)
      (negative-definition-context nΓ)
  neNeg (supᵘⱼ _ _) _ =
    level
  neNeg (lowerⱼ x) (lowerₙ y) =
    lowerNeg (neNeg x y) (refl (syntacticTerm x))
  neNeg (d ∘ⱼ ⊢t           ) (∘ₙ n       ) =
    appNeg (neNeg d n) (refl (syntacticTerm d)) ⊢t
  neNeg (fstⱼ A⊢B d) (fstₙ n) =
    fstNeg (neNeg d n) (refl (ΠΣⱼ A⊢B (⊢∷ΠΣ→ΠΣ-allowed d)))
  neNeg (sndⱼ A⊢B d) (sndₙ n) =
    sndNeg (neNeg d n) (refl (ΠΣⱼ A⊢B (⊢∷ΠΣ→ΠΣ-allowed d))) (fstⱼ A⊢B d)
  neNeg (natrecⱼ _ _ d) (natrecₙ n) =
    let ⊢ℕ = refl (⊢ℕ (wfTerm d))
    in  ⊥-elim (¬negℕ (neNeg d n) ⊢ℕ)
  neNeg (prodrecⱼ ⊢A d _ ok) (prodrecₙ n) =
    let ⊢Σ = refl (⊢∙→⊢ (wf ⊢A))
    in  ⊥-elim (¬negΣʷ (neNeg d n) ⊢Σ)
  neNeg (emptyrecⱼ _ d     ) (emptyrecₙ n) =
    ⊥-elim (consistent _ d)
  neNeg (unitrecⱼ _ d _ ok) (unitrecₙ _ n) =
    let ⊢Unit = refl (⊢Unit (wfTerm d) ok)
    in  ⊥-elim (¬negUnit (neNeg d n) ⊢Unit)
  neNeg (Jⱼ ⊢t _ _ ⊢v ⊢w) (Jₙ w-ne) =
    ⊥-elim (¬negId (neNeg ⊢w w-ne) (refl (Idⱼ′ ⊢t ⊢v)))
  neNeg (Kⱼ _ _ ⊢v _) (Kₙ v-ne) =
    ⊥-elim (¬negId (neNeg ⊢v v-ne) (refl (syntacticTerm ⊢v)))
  neNeg ([]-congⱼ _ _ ⊢t ⊢u ⊢v _) ([]-congₙ v-ne) =
    ⊥-elim (¬negId (neNeg ⊢v v-ne) (refl (Idⱼ′ ⊢t ⊢u)))
  neNeg (conv d c) n =
    conv (neNeg d n) c
  neNeg (Uⱼ _)          ()
  neNeg (ΠΣⱼ _ _ _ _)   ()
  neNeg (lamⱼ _ _ _)    ()
  neNeg (prodⱼ _ _ _ _) ()
  neNeg (Emptyⱼ _)      ()
  neNeg (Unitⱼ _ _)     ()
  neNeg (starⱼ _ _)     ()
  neNeg (ℕⱼ _)          ()
  neNeg (zeroⱼ _)       ()
  neNeg (sucⱼ _)        ()
  neNeg (Idⱼ _ _ _)     ()
  neNeg (rflⱼ _)        ()
  neNeg (Levelⱼ _ _)    ()
  neNeg (zeroᵘⱼ _ _)    ()
  neNeg (sucᵘⱼ _)       ()
  neNeg (Liftⱼ _ _ _)   ()
  neNeg (liftⱼ _ _ _)   ()

  -- Lemma: A normal form of type ℕ is a numeral in a consistent
  -- negative context (given a certain assumption).

  nfN : ⦃ ok : No-equality-reflection or-empty Γ .vars ⦄
      → Γ ⊢ u ∷ A
      → Nf (Γ .defs) u
      → Γ ⊢ A ≡ ℕ
      → Numeral u

  -- Case: neutrals. The type cannot be ℕ since it must be negative.
  nfN d (ne n) c =
    ⊥-elim (¬negℕ (neNeg d (nfNeutral n)) c)

  nfN (Levelⱼ _ _)  Levelₙ      c = ⊥-elim (U≢ℕ c)
  nfN (zeroᵘⱼ _ _)  zeroᵘₙ      c = ⊥-elim (Level≢ℕ c)
  nfN (sucᵘⱼ _)     (sucᵘₙ _)   c = ⊥-elim (Level≢ℕ c)
  nfN (Liftⱼ _ _ _) (Liftₙ _ _) c = ⊥-elim (U≢ℕ c)
  nfN (liftⱼ _ _ _) (liftₙ _)   c = ⊥-elim (Lift≢ℕ c)

  -- Case: numerals.
  nfN (zeroⱼ x) zeroₙ   c = zeroₙ
  nfN (sucⱼ d) (sucₙ n) c = sucₙ (nfN d n c)

  -- Case: conversion.
  nfN (conv d c) n c' = nfN d n (trans c c')

  -- Impossible cases: type is not ℕ.

  -- * Canonical types
  nfN (Uⱼ _)        (Uₙ _)      c = ⊥-elim (U≢ℕ c)
  nfN (ΠΣⱼ _ _ _ _) (ΠΣₙ _ _)   c = ⊥-elim (U≢ℕ c)
  nfN (ℕⱼ _)        ℕₙ          c = ⊥-elim (U≢ℕ c)
  nfN (Emptyⱼ _)    Emptyₙ      c = ⊥-elim (U≢ℕ c)
  nfN (Unitⱼ _ _)   Unitₙ       c = ⊥-elim (U≢ℕ c)
  nfN (Idⱼ _ _ _)   (Idₙ _ _ _) c = ⊥-elim (U≢ℕ c)

  -- * Canonical forms
  nfN (lamⱼ _ _ _)    (lamₙ _)    c = ⊥-elim (ℕ≢ΠΣⱼ (sym c))
  nfN (prodⱼ _ _ _ _) (prodₙ _ _) c = ⊥-elim (ℕ≢ΠΣⱼ (sym c))
  nfN (starⱼ _ _)     starₙ       c = ⊥-elim (ℕ≢Unitⱼ (sym c))
  nfN (rflⱼ _)        rflₙ        c = ⊥-elim (Id≢ℕ c)
  -- q.e.d

   -- Terms of non-negative type reduce to non-neutral terms (given a
   -- certain assumption).

  ¬NeutralNf :
    ⦃ ok : No-equality-reflection or-empty Γ .vars ⦄ →
    Γ ⊢ t ∷ A → (NegativeType Γ A → ⊥) →
    ∃ λ u → Γ ⊢ t ↘ u ∷ A × (Neutral⁺ (Γ .defs) u → ⊥)
  ¬NeutralNf ⊢t ¬negA =
    let u , whnfU , d = whNormTerm ⊢t
    in  u , (d , whnfU) ,
        ¬negA ∘→ neNeg (syntacticEqTerm (subset*Term d) .proj₂ .proj₂)

  -- Canonicity theorem: Any well-typed term Γ ⊢ t ∷ ℕ reduces to a
  -- numeral under the ⇒ˢ* reduction (given a certain assumption).

  canonicityRed′ :
    ⦃ ok : No-equality-reflection or-empty Γ .vars ⦄ →
    Γ ⊩ℕ t ∷ℕ → ∃ λ v → Numeral v × Γ ⊢ t ⇒ˢ* v ∷ℕ
  canonicityRed′ (ℕₜ _ d n≡n (sucᵣ x)) =
    let v , numV , d′ = canonicityRed′ x
    in  suc v , sucₙ numV , ⇒ˢ*∷ℕ-trans (whred* d) (sucred* d′)
  canonicityRed′ (ℕₜ _ d n≡n zeroᵣ) =
    zero , zeroₙ , whred* d
  canonicityRed′ (ℕₜ _ d _ (ne (neNfₜ neK _))) =
    let u , d′ , ¬neU =
          ¬NeutralNf (redFirst*Term d)
            (flip ¬negℕ $ refl (⊢ℕ $ wfTerm $ redFirst*Term d))
    in  ⊥-elim $ ¬neU $
        PE.subst (Neutral⁺ _) (whrDet*Term (d , ne! neK) d′) $
        ne→ _ (ne⁻ neK)

  canonicityRed :
    ⦃ ok : No-equality-reflection or-empty Γ .vars ⦄ →
    Γ ⊢ t ∷ ℕ → ∃ λ u → Numeral u × Γ ⊢ t ⇒ˢ* u ∷ℕ
  canonicityRed =
    canonicityRed′ ∘→ ⊩∷ℕ⇔ .proj₁ ∘→ proj₂ ∘→ reducible-⊩∷

  -- Canonicity theorem: Any well-typed term Γ ⊢ t : ℕ is convertible
  -- to a numeral (given a certain assumption).

  canonicityEq :
    ⦃ ok : No-equality-reflection or-empty Γ .vars ⦄ →
    Γ ⊢ t ∷ ℕ → ∃ λ u → Numeral u × Γ ⊢ t ≡ u ∷ ℕ
  canonicityEq ⊢t =
    let u , numU , d = canonicityRed ⊢t
    in  u , numU , subset*Termˢ d

  -- Q.E.D. 2023-01-24
