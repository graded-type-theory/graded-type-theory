-- Proof that consistent negative axioms do not jeopardize canonicity.
-- https://www.cs.bham.ac.uk/~mhe/papers/negative-axioms.pdf

open import Definition.Modality.Instances.Erasure
import Definition.Modality.Instances.Erasure.Modality
open import Definition.Modality.Restrictions Erasure
import Application.NegativeAxioms.NegativeErasedContext
open import Definition.Typed Erasure
open import Definition.Untyped Erasure hiding (_∷_; ℕ≢B)
open import Definition.Typed.EqRelInstance Erasure

open import Tools.Empty

module Application.NegativeAxioms.Canonicity.NegativeErased
  (restrictions : Restrictions)
  (-- In this module prodrec is restricted to the quantity ω.
   open Definition.Modality.Instances.Erasure.Modality
          (prodrec-only-for-ω restrictions))
  (open Application.NegativeAxioms.NegativeErasedContext ErasureModality (λ ()))
  {m} {Γ : Con Term m} {γ}
  (nΓγ : NegativeErasedContext Γ γ)
  (consistent : ∀{t} → Γ ⊢ t ∷ Empty → ⊥)
  where

open import Definition.Modality.Instances.Erasure.Properties
  (prodrec-only-for-ω restrictions)
open import Definition.Modality.Context ErasureModality
open import Definition.Modality.Usage ErasureModality
open import Definition.Modality.Usage.Inversion ErasureModality
open import Definition.Modality.Usage.Properties ErasureModality
open import Definition.Mode ErasureModality

open import Application.NegativeAxioms.NegativeType Erasure
open import Erasure.SucRed Erasure

open import Definition.Typed.Properties Erasure
open import Definition.Typed.Usage ErasureModality
open import Definition.Typed.Consequences.Consistency Erasure
open import Definition.Typed.Consequences.Inequality Erasure
open import Definition.Typed.Consequences.Injectivity Erasure
open import Definition.Typed.Consequences.Inversion Erasure
open import Definition.Typed.Consequences.Reduction Erasure
open import Definition.Typed.Consequences.Syntactic Erasure

open import Definition.Conversion.FullReduction Erasure hiding (fullRedTerm)
open import Definition.LogicalRelation Erasure
open import Definition.LogicalRelation.Irrelevance Erasure
open import Definition.LogicalRelation.Fundamental.Reducibility Erasure

open import Tools.Nat
import Tools.PropositionalEquality as PE
open import Tools.Product


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

-- Lemma: A neutral which is well-typed in a negative/erased context,
-- and which is well-used in the mode 𝟙ᵐ, has a negative type.

neNeg :
  (d : Γ ⊢ u ∷ A) (n : Neutral u) (f : γ ▸[ 𝟙ᵐ ] u) → NegativeType Γ A
neNeg (var ⊢Γ h          ) (var x      ) γ▸u =
  let γ≤γ′ = inv-usage-var γ▸u
      γ⟨x⟩≤𝟙 = PE.subst (λ p → γ ⟨ x ⟩ ≤ p) (update-lookup 𝟘ᶜ x)
                        (lookup-monotone x γ≤γ′)
  in  lookupNegative ⊢Γ nΓγ h γ⟨x⟩≤𝟙
neNeg (d ∘ⱼ ⊢t           ) (∘ₙ n       ) γ▸u =
  let invUsageApp δ▸g η▸a γ≤γ′ = inv-usage-app γ▸u
  in  appNeg (neNeg d n (sub δ▸g (≤ᶜ-trans γ≤γ′ (+ᶜ-decreasingˡ _ _))))
             (refl (syntacticTerm d)) ⊢t
neNeg (fstⱼ ⊢A A⊢B d     ) (fstₙ n     ) γ▸u =
  let invUsageFst _ _ δ▸t γ≤δ _ = inv-usage-fst γ▸u
  in  fstNeg (neNeg d n (sub δ▸t γ≤δ))
             (refl (ΠΣⱼ ⊢A ▹ A⊢B))
neNeg (sndⱼ ⊢A A⊢B d     ) (sndₙ n     ) γ▸u =
  let invUsageSnd δ▸t γ≤δ = inv-usage-snd γ▸u
  in  sndNeg (neNeg d n (sub δ▸t γ≤δ))
             (refl (ΠΣⱼ ⊢A ▹ A⊢B)) (fstⱼ ⊢A A⊢B d)
neNeg (natrecⱼ _ _ _ d   ) (natrecₙ n  ) γ▸u =
  let invUsageNatrec _ _ δ▸n γ≤γ′ = inv-usage-natrec γ▸u
      ⊢ℕ = refl (ℕⱼ (wfTerm d))
      γ▸n = sub δ▸n (≤ᶜ-trans γ≤γ′ (≤ᶜ-trans (⊛ᶜ-ineq₂ _ _ _) (∧ᶜ-decreasingʳ _ _)))
  in  ⊥-elim (¬negℕ (neNeg d n γ▸n) ⊢ℕ)
neNeg (prodrecⱼ ⊢A A⊢B _ d _) (prodrecₙ n ) γ▸u =
  let invUsageProdrec δ▸t η▸u (_ , p≡ω) γ≤γ′ = inv-usage-prodrec γ▸u
      γ▸t = sub δ▸t (≤ᶜ-trans γ≤γ′ (≤ᶜ-trans (+ᶜ-decreasingˡ _ _)
                              (≤ᶜ-trans (·ᶜ-monotoneˡ (≤-reflexive p≡ω))
                                 (≤ᶜ-reflexive (·ᶜ-identityˡ _)))))
      ⊢Σ = refl (ΠΣⱼ ⊢A ▹ A⊢B)
  in  ⊥-elim (¬negΣᵣ (neNeg d n (▸-cong (PE.cong (𝟙ᵐ ᵐ·_) p≡ω) γ▸t)) ⊢Σ)
neNeg (Emptyrecⱼ _ d     ) (Emptyrecₙ n) γ▸u = ⊥-elim (consistent d)
neNeg (conv d c          ) n             γ▸u = conv (neNeg d n γ▸u) c

-- Lemma: A normal form which has the type ℕ in a negative/erased
-- context, and which is well-used in the mode 𝟙ᵐ, is a numeral.

nfN : (d : Γ ⊢ u ∷ A)
    → (m : γ ▸[ 𝟙ᵐ ] u)
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
nfN (ΠΣⱼ _ ▹ _)      γ▸u (ΠΣₙ _ _)  c = ⊥-elim (U≢ℕ c)
nfN (ℕⱼ _)           γ▸u ℕₙ         c = ⊥-elim (U≢ℕ c)
nfN (Emptyⱼ _)       γ▸u Emptyₙ     c = ⊥-elim (U≢ℕ c)
nfN (Unitⱼ _)        γ▸u Unitₙ      c = ⊥-elim (U≢ℕ c)

-- * Canonical forms
nfN (lamⱼ _ _)      γ▸u (lamₙ _)    c = ⊥-elim (ℕ≢Π (sym c))
nfN (prodⱼ _ _ _ _) γ▸u (prodₙ _ _) c = ⊥-elim (ℕ≢Σ (sym c))
nfN (starⱼ _)       γ▸u starₙ       c = ⊥-elim (ℕ≢Unitⱼ (sym c))
-- q.e.d

-- Terms of non-negative types reduce to non-neutrals

¬NeutralNf : Γ ⊢ t ∷ A → γ ▸[ 𝟙ᵐ ] t → (NegativeType Γ A → ⊥)
           → ∃ λ u → Γ ⊢ t ⇒* u ∷ A × Whnf u × (Neutral u → ⊥)
¬NeutralNf ⊢t γ▸t ¬negA =
  let u , whnfU , d = whNormTerm ⊢t
      γ▸u = usagePres*Term γ▸t (redₜ d)
  in  u , redₜ d , whnfU , λ x → ¬negA (neNeg (⊢u-redₜ d) x γ▸u)

-- Canonicity theorem: A term which has the type ℕ in a
-- negative/erased context, and which is well-used in the mode 𝟙ᵐ,
-- ⇒ˢ*-reduces to a numeral.

canonicityRed′ : ∀ {l} → (⊢Γ : ⊢ Γ) → γ ▸[ 𝟙ᵐ ] t
               → Γ ⊩⟨ l ⟩ t ∷ ℕ / ℕᵣ (idRed:*: (ℕⱼ ⊢Γ))
               → ∃ λ v → Numeral v × Γ ⊢ t ⇒ˢ* v ∷ℕ
canonicityRed′ {l = l} ⊢Γ γ▸t (ℕₜ _ d n≡n (sucᵣ x)) =
  let invUsageSuc δ▸n γ≤δ = inv-usage-suc (usagePres*Term γ▸t (redₜ d))
      v , numV , d′ = canonicityRed′ {l = l} ⊢Γ (sub δ▸n γ≤δ) x
  in  suc v , sucₙ numV , ⇒ˢ*∷ℕ-trans (whred* (redₜ d)) (sucred* d′)
canonicityRed′ ⊢Γ γ▸t (ℕₜ _ d n≡n zeroᵣ) =
  zero , zeroₙ , whred* (redₜ d)
canonicityRed′ ⊢Γ γ▸t (ℕₜ n d n≡n (ne (neNfₜ neK ⊢k k≡k))) =
  let u , d′ , whU , ¬neU = ¬NeutralNf (⊢t-redₜ d) γ▸t λ negℕ → ¬negℕ negℕ (refl (ℕⱼ ⊢Γ))
  in  ⊥-elim (¬neU (PE.subst Neutral (whrDet*Term (redₜ d , ne neK) (d′ , whU)) neK))

canonicityRed :
  Γ ⊢ t ∷ ℕ → γ ▸[ 𝟙ᵐ ] t → ∃ λ u → Numeral u × Γ ⊢ t ⇒ˢ* u ∷ℕ
canonicityRed ⊢t γ▸t with reducibleTerm ⊢t
... | [ℕ] , [t] =
  let ⊢Γ = wfTerm ⊢t
      [ℕ]′ = ℕᵣ {l = ¹} (idRed:*: (ℕⱼ ⊢Γ))
      [t]′ = irrelevanceTerm [ℕ] [ℕ]′ [t]
  in  canonicityRed′ {l = ¹} ⊢Γ γ▸t [t]′

-- Canonicity theorem: A term which has the type ℕ in a
-- negative/erased context, and which is well-used in the mode 𝟙ᵐ, is
-- convertible to a numeral.

canonicityEq :
  (⊢t : Γ ⊢ t ∷ ℕ) → (γ▸t : γ ▸[ 𝟙ᵐ ] t) →
  ∃ λ u → Numeral u × Γ ⊢ t ≡ u ∷ ℕ
canonicityEq ⊢t γ▸t =
  let u , numU , d = canonicityRed ⊢t γ▸t
  in  u , numU , subset*Termˢ d

-- Q.E.D.
