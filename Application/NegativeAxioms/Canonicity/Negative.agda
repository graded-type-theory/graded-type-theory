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
open import Definition.Typed.Consequences.Consistency M′
open import Definition.Typed.Consequences.Inequality M′
open import Definition.Typed.Consequences.Injectivity M′
open import Definition.Typed.Consequences.Inversion M′
open import Definition.Typed.Consequences.Reduction M′
open import Definition.Typed.Consequences.Syntactic M′

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

  -- Canonicity theorem: Any well-typed term Γ ⊢ t : ℕ is convertible to a numeral.

  thm : (⊢t : Γ ⊢ t ∷ ℕ) → ∃ λ u → Numeral u × Γ ⊢ t ≡ u ∷ ℕ
  thm ⊢t with fullRedTerm (completeEqTerm (refl ⊢t))
  ... | u , nf , eq =
    let _ , _ , ⊢u = syntacticEqTerm eq
    in  u , nfN ⊢u nf (refl (ℕⱼ (wfTerm ⊢t))) , eq

  -- Lemma: Any well-typed term of a non-negative type reduces to a non-neutral

  lem : Γ ⊢ t ∷ A → (NegativeType Γ A → ⊥)
      → ∃ λ u → Γ ⊢ t ⇒* u ∷ A × Whnf u × (Neutral u → ⊥)
  lem ⊢t ¬negA =
    let u , whnfU , d = whNormTerm ⊢t
    in  u , redₜ d , whnfU , λ x → ¬negA (neNeg (⊢u-redₜ d) x)

  -- Canonicity theorem: Any well-typed term Γ ⊢ t : ℕ WH-reduces to zero or suc u for some u

  thm′ : Γ ⊢ t ∷ ℕ → (Γ ⊢ t ⇒* zero ∷ ℕ) ⊎ ∃ λ u → Γ ⊢ t ⇒* suc u ∷ ℕ
  thm′ ⊢t with lem ⊢t (λ x → ¬negℕ x (refl (ℕⱼ (wfTerm ⊢t))))
  -- True cases
  ... | _ , d , zeroₙ , ¬neU = inj₁ d
  ... | _ , d , sucₙ , ¬neU = inj₂ (_ , d)
  -- False cases
  ... | _ , d , Uₙ , ¬neU = ⊥-elim (redU*Term d)
  ... | _ , d , Πₙ , ¬neU =
    let _ , _ , ⊢Π = syntacticRedTerm d
        _ , _ , ℕ≡U = inversion-Π ⊢Π
    in  ⊥-elim (U≢ℕ (sym ℕ≡U))
  ... | _ , d , Σₙ , ¬neU =
    let _ , _ , ⊢Σ = syntacticRedTerm d
        _ , _ , ℕ≡U = inversion-Σ ⊢Σ
    in  ⊥-elim (U≢ℕ (sym ℕ≡U))
  ... | _ , d , ℕₙ , ¬neU =
    let _ , _ , ⊢ℕ = syntacticRedTerm d
        ℕ≡U = inversion-ℕ ⊢ℕ
    in  ⊥-elim (U≢ℕ (sym ℕ≡U))
  ... | _ , d , Unitₙ , ¬neU =
    let _ , _ , ⊢Unit = syntacticRedTerm d
        ℕ≡U = inversion-Unit ⊢Unit
    in  ⊥-elim (U≢ℕ (sym ℕ≡U))
  ... | _ , d , Emptyₙ , ¬neU =
    let _ , _ , ⊢Empty = syntacticRedTerm d
        ℕ≡U = inversion-Empty ⊢Empty
    in  ⊥-elim (U≢ℕ (sym ℕ≡U))
  ... | _ , d , lamₙ , ¬neU =
    let _ , _ , ⊢lam = syntacticRedTerm d
        _ , _ , _ , _ , _ , ℕ≡Π = inversion-lam ⊢lam
    in  ⊥-elim (ℕ≢B BΠ! ℕ≡Π)
  ... | _ , d , starₙ , ¬neU =
    let _ , _ , ⊢star = syntacticRedTerm d
        ℕ≡Unit = inversion-star ⊢star
    in  ⊥-elim (ℕ≢Unitⱼ ℕ≡Unit)
  ... | _ , d , prodₙ , ¬neU =
    let _ , _ , ⊢prod = syntacticRedTerm d
        _ , _ , _ , _ , _ , _ , _ , ℕ≡Σ = inversion-prod ⊢prod
    in  ⊥-elim (ℕ≢B BΣ! ℕ≡Σ)
  ... | _ , d , ne x , ¬neU = ⊥-elim (¬neU x)

  -- Canonicity theorem: Any well-typed term Γ ⊢ t ∷ ℕ, γ ▸ t
  -- reduces to a numeral under the ⇒ˢ* reduction.

  lem′ : Γ ⊢ t ∷ ℕ → Γ ⊢ t ≡ u ∷ ℕ → Numeral u
       → ∃ λ v → Numeral v × Γ ⊢ t ⇒ˢ* v ∷ℕ
  lem′ ⊢t t≡u num with thm′ ⊢t
  lem′ ⊢t t≡u zeroₙ | inj₁ x = zero , zeroₙ , whred* x
  lem′ ⊢t t≡0 zeroₙ | inj₂ (u , t⇒sucu) =
    ⊥-elim (zero≢suc (trans (sym t≡0) (subset*Term t⇒sucu)))
  lem′ ⊢t t≡sucu (sucₙ num) | inj₁ t⇒0 =
    ⊥-elim (zero≢suc (trans (sym (subset*Term t⇒0)) t≡sucu))
  lem′ ⊢t t≡suct′ (sucₙ numT) | inj₂ (u , t⇒sucu) =
    let sucu≡suct′ = trans (sym (subset*Term t⇒sucu)) t≡suct′
        u≡t′ = suc-injectivity sucu≡suct′
        _ , _ , ⊢sucu = syntacticRedTerm t⇒sucu
        ⊢u , _ = inversion-suc ⊢sucu
        v , numV , t⇒v = lem′ ⊢u u≡t′ numT
    in  suc v , sucₙ numV , ⇒ˢ*∷ℕ-trans (whred* t⇒sucu) (sucred* t⇒v)

  thm″ : Γ ⊢ t ∷ ℕ → ∃ λ u → Numeral u × Γ ⊢ t ⇒ˢ* u ∷ℕ
  thm″ ⊢t with thm ⊢t
  ... | u , num , eq = lem′ ⊢t eq num

  -- Q.E.D. 2023-01-24
