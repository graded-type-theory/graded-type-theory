-- Proof that consistent negative axioms do not jeopardize canonicity.
-- https://www.cs.bham.ac.uk/~mhe/papers/negative-axioms.pdf

{-# OPTIONS --without-K --safe #-}

open import Definition.Modality.Instances.Erasure
open import Definition.Modality.Instances.Erasure.Modality (_≤ ω)
open import Application.NegativeAxioms.NegativeErasedContext ErasureModality (λ ())
open import Definition.Typed Erasure′
open import Definition.Untyped Erasure hiding (_∷_; ℕ≢B)

open import Tools.Empty

module Application.NegativeAxioms.Canonicity.NegativeErased {m} {Γ : Con Term m} {γ}
  (nΓγ : NegativeErasedContext Γ γ) (consistent : ∀{t} → Γ ⊢ t ∷ Empty → ⊥) where

open import Definition.Modality.Instances.Erasure.Properties (_≤ ω)
open import Definition.Modality.Context ErasureModality
open import Definition.Modality.Usage ErasureModality
open import Definition.Modality.Usage.Inversion ErasureModality
open import Definition.Modality.FullReduction ErasureModality greatest-elem

open import Application.NegativeAxioms.NegativeType Erasure′
open import Erasure.SucRed Erasure′

open import Definition.Typed.Properties Erasure′
open import Definition.Typed.Usage ErasureModality
open import Definition.Typed.Consequences.Consistency Erasure′
open import Definition.Typed.Consequences.Inequality Erasure′
open import Definition.Typed.Consequences.Injectivity Erasure′
open import Definition.Typed.Consequences.Inversion Erasure′
open import Definition.Typed.Consequences.Reduction Erasure′
open import Definition.Typed.Consequences.Syntactic Erasure′

open import Definition.Conversion.FullReduction Erasure′ hiding (fullRedTerm)

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
    A B C : Term m
    t u   : Term m


-- Main results
---------------------------------------------------------------------------

-- Lemma: A neutral has negative type in a consistent negative/erased context.

neNeg : (d : Γ ⊢ u ∷ A) (n : Neutral u) (f : γ ▸ u) → NegativeType Γ A
neNeg (var ⊢Γ h          ) (var x      ) γ▸u =
  let γ≤γ′ = inv-usage-var γ▸u
      γ⟨x⟩≤𝟙 = PE.subst (λ p → γ ⟨ x ⟩ ≤ p) (update-lookup {γ = 𝟘ᶜ} x)
                        (lookup-monotone x γ≤γ′)
  in  lookupNegative ⊢Γ nΓγ h γ⟨x⟩≤𝟙
neNeg (d ∘ⱼ ⊢t           ) (∘ₙ n       ) γ▸u =
  let invUsageApp δ▸g η▸a γ≤γ′ = inv-usage-app γ▸u
  in  appNeg (neNeg d n (sub δ▸g (≤ᶜ-trans γ≤γ′ (+ᶜ-decreasingˡ _ _))))
             (refl (syntacticTerm d)) ⊢t
neNeg (fstⱼ ⊢A A⊢B d     ) (fstₙ n     ) γ▸u =
  let invUsageProj δ▸t γ≤δ = inv-usage-fst γ▸u
  in  fstNeg (neNeg d n (sub δ▸t γ≤δ))
             (refl (Σⱼ ⊢A ▹ A⊢B))
neNeg (sndⱼ ⊢A A⊢B d     ) (sndₙ n     ) γ▸u =
  let invUsageProj δ▸t γ≤δ = inv-usage-snd γ▸u
  in  sndNeg (neNeg d n (sub δ▸t γ≤δ))
             (refl (Σⱼ ⊢A ▹ A⊢B)) (fstⱼ ⊢A A⊢B d)
neNeg (natrecⱼ _ _ _ d   ) (natrecₙ n  ) γ▸u =
  let invUsageNatrec _ _ δ▸n γ≤γ′ = inv-usage-natrec γ▸u
      ⊢ℕ = refl (ℕⱼ (wfTerm d))
      γ▸n = sub δ▸n (≤ᶜ-trans γ≤γ′ (≤ᶜ-trans (⊛ᶜ-ineq₂ _ _ _) (∧ᶜ-decreasingʳ _ _)))
  in  ⊥-elim (¬negℕ (neNeg d n γ▸n) ⊢ℕ)
neNeg (prodrecⱼ ⊢A A⊢B _ d _) (prodrecₙ n ) γ▸u =
  let invUsageProdrec δ▸t η▸u p≤ω γ≤γ′ = inv-usage-prodrec γ▸u
      γ▸t = sub δ▸t (≤ᶜ-trans γ≤γ′ (≤ᶜ-trans (+ᶜ-decreasingˡ _ _)
                              (≤ᶜ-trans (·ᶜ-monotoneˡ p≤ω) (≤ᶜ-reflexive (·ᶜ-identityˡ _)))))
      ⊢Σ = refl (Σⱼ ⊢A ▹ A⊢B)
  in  ⊥-elim (¬negΣᵣ (neNeg d n γ▸t) ⊢Σ)
neNeg (Emptyrecⱼ _ d     ) (Emptyrecₙ n) γ▸u = ⊥-elim (consistent d)
neNeg (conv d c          ) n             γ▸u = conv (neNeg d n γ▸u) c

-- Lemma: A normal form of type ℕ is a numeral in a consistent negative context.

nfN : (d : Γ ⊢ u ∷ A)
    → (m : γ ▸ u)
    → (n : Nf u)
    → (c : Γ ⊢ A ≡ ℕ)
    → Numeral u

-- Case: neutrals. The type cannot be ℕ since it must be negative.
nfN d γ▸u (ne n) c = ⊥-elim (¬negℕ (neNeg d (nfNeutral n) γ▸u) c)

-- Case: numerals.
nfN (zeroⱼ x) γ▸u zeroₙ   c = zeroₙ
nfN (sucⱼ d) γ▸u (sucₙ n) c =
  let invUsageSuc δ▸n γ≤δ = inv-usage-suc γ▸u
  in  sucₙ (nfN d (sub δ▸n γ≤δ) n c)

-- Case: conversion.
nfN (conv d c) γ▸u n c' = nfN d γ▸u n (trans c c')

-- Impossible cases: type is not ℕ.

-- * Canonical types
nfN (Πⱼ _ ▹ _)       γ▸u (Πₙ _ _)   c = ⊥-elim (U≢ℕ c)
nfN (Σⱼ _ ▹ _)       γ▸u (Σₙ _ _)   c = ⊥-elim (U≢ℕ c)
nfN (ℕⱼ _)           γ▸u ℕₙ         c = ⊥-elim (U≢ℕ c)
nfN (Emptyⱼ _)       γ▸u Emptyₙ     c = ⊥-elim (U≢ℕ c)
nfN (Unitⱼ _)        γ▸u Unitₙ      c = ⊥-elim (U≢ℕ c)

-- * Canonical forms
nfN (lamⱼ _ _)      γ▸u (lamₙ _)    c = ⊥-elim (ℕ≢Π (sym c))
nfN (prodⱼ _ _ _ _) γ▸u (prodₙ _ _) c = ⊥-elim (ℕ≢Σ (sym c))
nfN (starⱼ _)       γ▸u starₙ       c = ⊥-elim (ℕ≢Unitⱼ (sym c))
-- q.e.d

-- Canonicity theorem: Any well-typed term Γ ⊢ t : ℕ is convertible to a numeral.

thm : (⊢t : Γ ⊢ t ∷ ℕ) → (γ▸t : γ ▸ t) → ∃ λ u → Numeral u × Γ ⊢ t ≡ u ∷ ℕ
thm ⊢t γ▸t with fullRedTerm ⊢t γ▸t
... | u , nf , eq , γ▸u =
  u , nfN (proj₂ (proj₂ (syntacticEqTerm eq))) γ▸u nf (refl (ℕⱼ (wfTerm ⊢t))) , eq

-- Any well-typed term Γ ⊢ t : ℕ WH-reduces to zero or suc u for some u

lem : Γ ⊢ t ∷ A → γ ▸ t → (NegativeType Γ A → ⊥)
    → ∃ λ u → Γ ⊢ t ⇒* u ∷ A × Whnf u × (Neutral u → ⊥)
lem ⊢t γ▸t ¬negA =
  let u , whnfU , d = whNormTerm ⊢t
      γ▸u = usagePres*Term γ▸t (redₜ d)
  in  u , redₜ d , whnfU , λ x → ¬negA (neNeg (⊢u-redₜ d) x γ▸u)

-- Canonicity theorem: Any well-typed term Γ ⊢ t : ℕ WH-reduces to zero or suc u for some u

thm′ : Γ ⊢ t ∷ ℕ → γ ▸ t → (Γ ⊢ t ⇒* zero ∷ ℕ) ⊎ ∃ λ u → Γ ⊢ t ⇒* suc u ∷ ℕ
thm′ ⊢t γ▸t with lem ⊢t γ▸t (λ x → ¬negℕ x (refl (ℕⱼ (wfTerm ⊢t))))
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

lem′ : Γ ⊢ t ∷ ℕ → γ ▸ t → Γ ⊢ t ≡ u ∷ ℕ → Numeral u
     → ∃ λ v → Numeral v × Γ ⊢ t ⇒ˢ* v ∷ℕ
lem′ ⊢t γ▸t t≡u num with thm′ ⊢t γ▸t
lem′ ⊢t γ▸t t≡u zeroₙ | inj₁ x = zero , zeroₙ , whred* x
lem′ ⊢t γ▸t t≡0 zeroₙ | inj₂ (u , t⇒sucu) =
  ⊥-elim (zero≢suc (trans (sym t≡0) (subset*Term t⇒sucu)))
lem′ ⊢t γ▸t t≡sucu (sucₙ num) | inj₁ t⇒0 =
  ⊥-elim (zero≢suc (trans (sym (subset*Term t⇒0)) t≡sucu))
lem′ ⊢t γ▸t t≡suct′ (sucₙ numT) | inj₂ (u , t⇒sucu) =
  let sucu≡suct′ = trans (sym (subset*Term t⇒sucu)) t≡suct′
      u≡t′ = suc-injectivity sucu≡suct′
      _ , _ , ⊢sucu = syntacticRedTerm t⇒sucu
      ⊢u , _ = inversion-suc ⊢sucu
      γ▸sucu = usagePres*Term γ▸t t⇒sucu
      invUsageSuc δ▸u γ≤δ = inv-usage-suc γ▸sucu
      γ▸u = sub δ▸u γ≤δ
      v , numV , t⇒v = lem′ ⊢u γ▸u u≡t′ numT
  in  suc v , sucₙ numV , ⇒ˢ*∷ℕ-trans (whred* t⇒sucu) (sucred* t⇒v)

thm″ : Γ ⊢ t ∷ ℕ → γ ▸ t → ∃ λ u → Numeral u × Γ ⊢ t ⇒ˢ* u ∷ℕ
thm″ ⊢t γ▸t with thm ⊢t γ▸t
... | u , num , eq = lem′ ⊢t γ▸t eq num

-- Q.E.D. 2023-01-24
