------------------------------------------------------------------------
-- Proof that consistent negative or erased axioms do not jeopardize
-- canonicity if erased matches are not allowed.
------------------------------------------------------------------------

open import Tools.Empty
open import Tools.Level

open import Graded.Modality.Instances.Erasure
open import Graded.Modality.Instances.Erasure.Modality
open import Graded.Restrictions
open import Graded.Usage.Restrictions Erasure
open import Graded.Modality.Variant lzero
import Application.NegativeOrErasedAxioms.NegativeOrErasedContext
import Definition.Typed
open import Definition.Typed.Restrictions Erasure
open import Definition.Untyped Erasure hiding (_∷_; ℕ≢B)

module Application.NegativeOrErasedAxioms.Canonicity
  (variant : Modality-variant)
  (TR : Type-restrictions)
  (open Definition.Typed TR)
  (UR : Usage-restrictions)
  -- Erased matches are not allowed.
  (no-erased-matches : No-erased-matches (ErasureModality variant) UR)
  (open Application.NegativeOrErasedAxioms.NegativeOrErasedContext
     (ErasureModality variant) (λ ()) TR)
  {m} {Γ : Con Term m} {γ}
  (nΓγ : NegativeErasedContext Γ γ)
  (consistent : ∀{t} → Γ ⊢ t ∷ Empty → ⊥)
  where

open import Graded.Modality.Instances.Erasure.Properties variant
open import Graded.Context (ErasureModality variant)
open import Graded.Reduction (ErasureModality variant) TR UR
open import Graded.Usage (ErasureModality variant) UR
open import Graded.Usage.Inversion (ErasureModality variant) UR
open import Graded.Usage.Properties (ErasureModality variant) UR
open import Graded.Mode (ErasureModality variant)

open import Application.NegativeOrErasedAxioms.NegativeOrErasedType
  (ErasureModality variant) TR
open import Graded.Erasure.SucRed TR

open import Definition.Untyped.Normal-form Erasure

open import Definition.Typed.EqRelInstance TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Consequences.Inequality TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Consequences.Reduction TR
open import Definition.Typed.Consequences.Syntactic TR

open import Definition.LogicalRelation TR
open import Definition.LogicalRelation.Irrelevance TR
open import Definition.LogicalRelation.Fundamental.Reducibility TR

open import Tools.Function
open import Tools.PropositionalEquality as PE using (_≢_)
open import Tools.Product
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

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
-- and also well-resourced (with respect to the mode 𝟙ᵐ), has a
-- negative type.

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
neNeg (fstⱼ ⊢A A⊢B d) (fstₙ {p = p} n) γ▸u =
  let invUsageFst m 𝟙ᵐ≡mᵐ·p δ▸t γ≤δ ok = inv-usage-fst γ▸u
  in  fstNeg (neNeg d n (sub δ▸t γ≤δ))
             (refl (ΠΣⱼ ⊢A A⊢B (⊢∷ΠΣ→ΠΣ-allowed d)))
             (𝟘≢p m 𝟙ᵐ≡mᵐ·p (ok PE.refl))
  where
  𝟘≢p :
    ∀ m →
    𝟙ᵐ PE.≡ m ᵐ· p →
    p ≤ ω →
    𝟘 ≢ p
  𝟘≢p 𝟘ᵐ ()
  𝟘≢p 𝟙ᵐ _ () PE.refl
neNeg (sndⱼ ⊢A A⊢B d     ) (sndₙ n     ) γ▸u =
  let invUsageSnd δ▸t γ≤δ = inv-usage-snd γ▸u
  in  sndNeg (neNeg d n (sub δ▸t γ≤δ))
             (refl (ΠΣⱼ ⊢A A⊢B (⊢∷ΠΣ→ΠΣ-allowed d)))
             (fstⱼ ⊢A A⊢B d)
neNeg (natrecⱼ {p = p} {r = r} _ _ _ d) (natrecₙ n) γ▸u =
  case inv-usage-natrec γ▸u of λ {
    (invUsageNatrec {δ = δ} {η = η} {θ = θ} {χ = χ}
       _ _ θ▸n _ γ≤χ extra) →
  case
    (case extra of λ where
       invUsageNatrecStar → begin
         γ                            ≤⟨ γ≤χ ⟩
         χ                            ≡⟨⟩
         (δ ∧ᶜ θ) ⊛ᶜ η +ᶜ p ·ᶜ θ ▷ r  ≤⟨ ⊛ᶜ-ineq₂ _ _ _ ⟩
         δ ∧ᶜ θ                       ≤⟨ ∧ᶜ-decreasingʳ _ _ ⟩
         θ                            ∎
       (invUsageNatrecNoStar fix) → begin
         γ                                  ≤⟨ γ≤χ ⟩
         χ                                  ≤⟨ fix ⟩
         δ ∧ᶜ θ ∧ᶜ (η +ᶜ p ·ᶜ θ +ᶜ r ·ᶜ χ)  ≤⟨ ∧ᶜ-decreasingʳ _ _ ⟩
         θ ∧ᶜ (η +ᶜ p ·ᶜ θ +ᶜ r ·ᶜ χ)       ≤⟨ ∧ᶜ-decreasingˡ _ _ ⟩
         θ                                  ∎)
  of λ γ≤θ →
  ⊥-elim (¬negℕ (neNeg d n (sub θ▸n γ≤θ)) (refl (ℕⱼ (wfTerm d)))) }
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
neNeg (prodrecⱼ {r = r} ⊢A A⊢B _ d _ ok₁) (prodrecₙ n) γ▸u =
  let invUsageProdrec {δ = δ} {η = η} δ▸t η▸u _ ok₂ γ≤ =
        inv-usage-prodrec γ▸u
      γ▸t = sub δ▸t
        (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
           γ            ≤⟨ γ≤ ⟩
           r ·ᶜ δ +ᶜ η  ≤⟨ +ᶜ-decreasingˡ _ _ ⟩
           r ·ᶜ δ       ≈⟨ ·ᶜ-congʳ (≢𝟘→≡ω (no-erased-matches (λ ()) ok₂)) ⟩
           ω ·ᶜ δ       ≈⟨ ·ᶜ-identityˡ _ ⟩
           δ            ∎)
      ⊢Σ = refl (ΠΣⱼ ⊢A A⊢B ok₁)
      lemma = let open Tools.Reasoning.PropositionalEquality in
        ⌞ r ⌟  ≡⟨ ≢𝟘→⌞⌟≡𝟙ᵐ (no-erased-matches (λ ()) ok₂) ⟩
        𝟙ᵐ     ∎
  in  ⊥-elim (¬negΣᵣ (neNeg d n (▸-cong lemma γ▸t)) ⊢Σ)
neNeg (emptyrecⱼ _ d     ) (emptyrecₙ n) γ▸u = ⊥-elim (consistent d)
neNeg (conv d c          ) n             γ▸u = conv (neNeg d n γ▸u) c

-- Lemma: A normal form which has the type ℕ in a negative/erased
-- context, and which is well-resourced (with respect to the mode 𝟙ᵐ),
-- is a numeral.

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
nfN (ΠΣⱼ _ _ _) _ (ΠΣₙ _ _) c = ⊥-elim (U≢ℕ c)
nfN (ℕⱼ _)      _ ℕₙ        c = ⊥-elim (U≢ℕ c)
nfN (Emptyⱼ _)  _ Emptyₙ    c = ⊥-elim (U≢ℕ c)
nfN (Unitⱼ _ _) _ Unitₙ     c = ⊥-elim (U≢ℕ c)

-- * Canonical forms
nfN (lamⱼ _ _ _)      _ (lamₙ _)    c = ⊥-elim (ℕ≢Π (sym c))
nfN (prodⱼ _ _ _ _ _) _ (prodₙ _ _) c = ⊥-elim (ℕ≢Σ (sym c))
nfN (starⱼ _ _)       _ starₙ       c = ⊥-elim (ℕ≢Unitⱼ (sym c))
-- q.e.d

-- Terms of non-negative types reduce to non-neutrals

¬NeutralNf : Γ ⊢ t ∷ A → γ ▸[ 𝟙ᵐ ] t → (NegativeType Γ A → ⊥)
           → ∃ λ u → Γ ⊢ t ⇒* u ∷ A × Whnf u × (Neutral u → ⊥)
¬NeutralNf ⊢t γ▸t ¬negA =
  let u , whnfU , d = whNormTerm ⊢t
      γ▸u = usagePres*Term γ▸t (redₜ d)
  in  u , redₜ d , whnfU , λ x → ¬negA (neNeg (⊢u-redₜ d) x γ▸u)

-- Canonicity theorem: A term which has the type ℕ in a
-- negative/erased context, and which is well-resourced (with respect
-- to the mode 𝟙ᵐ), ⇒ˢ*-reduces to a numeral.

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
-- negative/erased context, and which is well-resourced (with respect
-- to the mode 𝟙ᵐ), is convertible to a numeral.

canonicityEq :
  (⊢t : Γ ⊢ t ∷ ℕ) → (γ▸t : γ ▸[ 𝟙ᵐ ] t) →
  ∃ λ u → Numeral u × Γ ⊢ t ≡ u ∷ ℕ
canonicityEq ⊢t γ▸t =
  let u , numU , d = canonicityRed ⊢t γ▸t
  in  u , numU , subset*Termˢ d

-- Q.E.D.
