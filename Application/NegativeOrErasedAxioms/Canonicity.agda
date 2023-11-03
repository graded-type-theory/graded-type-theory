------------------------------------------------------------------------
-- Proof that consistent negative or erased axioms do not jeopardize
-- canonicity if erased matches are not allowed.
------------------------------------------------------------------------

open import Tools.Empty

import Graded.Modality
open import Graded.Restrictions
import Graded.Usage.Restrictions
import Definition.Typed
import Definition.Typed.Restrictions
import Definition.Untyped hiding (_∷_; ℕ≢B)

module Application.NegativeOrErasedAxioms.Canonicity
  {a} {M : Set a}
  (open Graded.Modality M)
  (open Graded.Usage.Restrictions M)
  (open Definition.Typed.Restrictions M)
  (open Definition.Untyped M)
  (𝕄 : Modality)
  (open Modality 𝕄)
  -- The modality has a well-behaved zero.
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄
  (TR : Type-restrictions)
  (open Definition.Typed TR)
  (UR : Usage-restrictions)
  -- Erased matches are not allowed.
  (no-erased-matches : No-erased-matches 𝕄 UR)
  {m} {Γ : Con Term m}
  (consistent : ∀{t} → Γ ⊢ t ∷ Empty → ⊥)
  where

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Reduction 𝕄 TR UR
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Inversion 𝕄 UR
open import Graded.Usage.Properties 𝕄 UR
open import Graded.Modality.Dedicated-nr.Instance
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄

open import Application.NegativeOrErasedAxioms.NegativeOrErasedContext
  𝕄 TR
open import Application.NegativeOrErasedAxioms.NegativeOrErasedType 𝕄 TR
open import Graded.Erasure.SucRed TR

open import Definition.Untyped.Normal-form M

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
open import Tools.Sum using (inj₁; inj₂)

-- Preliminaries
---------------------------------------------------------------------------

private
  Ty  = Term
  Cxt = Con Ty
  variable
    A B C : Term m
    t u   : Term m
    γ     : Conₘ m

-- Main results
---------------------------------------------------------------------------

-- Lemma: A neutral which is well-typed in a negative/erased context,
-- and also well-resourced (with respect to the mode 𝟙ᵐ), has a
-- negative type.

neNeg :
  Γ ⊢ u ∷ A → Neutral u → γ ▸[ 𝟙ᵐ ] u → NegativeErasedContext Γ γ →
  NegativeType Γ A
neNeg {γ = γ} (var ⊢Γ h) (var x) γ▸u nΓγ =
  lookupNegative ⊢Γ nΓγ h
    (                              $⟨ γ▸u ⟩
     γ ▸[ 𝟙ᵐ ] var x               →⟨ inv-usage-var ⟩
     γ ≤ᶜ 𝟘ᶜ , x ≔ 𝟙               →⟨ lookup-monotone _ ⟩
     γ ⟨ x ⟩ ≤ (𝟘ᶜ , x ≔ 𝟙) ⟨ x ⟩  ≡⟨ PE.cong (γ ⟨ x ⟩ ≤_) (update-lookup 𝟘ᶜ x) ⟩→
     γ ⟨ x ⟩ ≤ 𝟙                   →⟨ (λ ≤𝟙 ≡𝟘 → 𝟘≰𝟙 $ begin
                                           𝟘        ≡˘⟨ ≡𝟘 ⟩
                                           γ ⟨ x ⟩  ≤⟨ ≤𝟙 ⟩
                                           𝟙        ∎) ⟩
     γ ⟨ x ⟩ ≢ 𝟘                   □)
  where
  open Tools.Reasoning.PartialOrder ≤-poset
neNeg {γ = γ}
  (_∘ⱼ_ {p = p} {q = q} {F = A} {G = B} {u = u} ⊢t ⊢u) (∘ₙ t-ne) γ▸tu =
  case inv-usage-app γ▸tu of λ {
    (invUsageApp {δ = δ} {η = η} δ▸t _ γ≤δ+pη) →
  NegativeErasedContext Γ γ              →⟨ NegativeErasedContext-upwards-closed γ≤δ+pη ⟩
  NegativeErasedContext Γ (δ +ᶜ p ·ᶜ η)  →⟨ NegativeErasedContext-𝟘 (λ _ → proj₁ ∘→ +ᶜ-positive-⟨⟩ δ) ⟩
  NegativeErasedContext Γ δ              →⟨ neNeg ⊢t t-ne δ▸t ⟩
  NegativeType Γ (Π p , q ▷ A ▹ B)       →⟨ (λ hyp → appNeg hyp (refl (syntacticTerm ⊢t)) ⊢u) ⟩
  NegativeType Γ (B [ u ]₀)              □ }
neNeg (fstⱼ ⊢A A⊢B d) (fstₙ {p = p} n) γ▸u nΓγ =
  let invUsageFst m 𝟙ᵐ≡mᵐ·p δ▸t γ≤δ ok = inv-usage-fst γ▸u
  in  fstNeg (neNeg d n (sub δ▸t γ≤δ) nΓγ)
             (refl (ΠΣⱼ ⊢A A⊢B (⊢∷ΠΣ→ΠΣ-allowed d)))
             (𝟘≢p m 𝟙ᵐ≡mᵐ·p (ok PE.refl))
  where
  𝟘≢p :
    ∀ m →
    𝟙ᵐ PE.≡ m ᵐ· p →
    p ≤ 𝟙 →
    𝟘 ≢ p
  𝟘≢p 𝟘ᵐ ()
  𝟘≢p 𝟙ᵐ _  𝟘≤𝟙 PE.refl = 𝟘≰𝟙 𝟘≤𝟙
neNeg (sndⱼ ⊢A A⊢B d) (sndₙ n) γ▸u nΓγ =
  let invUsageSnd δ▸t γ≤δ = inv-usage-snd γ▸u
  in  sndNeg (neNeg d n (sub δ▸t γ≤δ) nΓγ)
             (refl (ΠΣⱼ ⊢A A⊢B (⊢∷ΠΣ→ΠΣ-allowed d)))
             (fstⱼ ⊢A A⊢B d)
neNeg {γ = γ}
  (natrecⱼ {A = A} {n = n} _ _ _ ⊢n) (natrecₙ n-ne) γ▸natrec =
  case inv-usage-natrec γ▸natrec of λ {
    (invUsageNatrec {δ = δ} {θ = θ} {χ = χ} _ _ θ▸n _ γ≤χ extra) →
  NegativeErasedContext Γ γ            →⟨ NegativeErasedContext-upwards-closed γ≤χ ⟩
  NegativeErasedContext Γ χ            →⟨ (NegativeErasedContext-𝟘 λ x → case extra of λ {
                                             invUsageNatrecNr →
                                               proj₂ ∘→ proj₂ ∘→ nrᶜ-positive-⟨⟩ δ;
                                             (invUsageNatrecNoNr _ _ χ≤θ _) →
                                                $⟨ χ≤θ ⟩
    χ ≤ᶜ θ                                      →⟨ ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 ⟩
    (χ ⟨ x ⟩ PE.≡ 𝟘 → θ ⟨ x ⟩ PE.≡ 𝟘)           □ }) ⟩

  NegativeErasedContext Γ θ            →⟨ neNeg ⊢n n-ne θ▸n ⟩
  NegativeType Γ ℕ                     →⟨ flip ¬negℕ (refl (ℕⱼ (wfTerm ⊢n))) ⟩
  ⊥                                    →⟨ ⊥-elim ⟩
  NegativeType Γ (A [ n ]₀)            □ }
neNeg
  {γ = γ}
  (prodrecⱼ {F = B} {G = C} {p = p} {q′ = q} {A = A} {t = t} {r = r}
     ⊢B ⊢C _ ⊢t _ ok₁)
  (prodrecₙ t-ne)
  γ▸prodrec =
  case inv-usage-prodrec γ▸prodrec of λ {
    (invUsageProdrec {δ = δ} {η = η} δ▸t _ _ ok₂ γ≤rδ+η) →
  case no-erased-matches 𝟙≢𝟘 ok₂ of λ {
    r≢𝟘 →
  NegativeErasedContext Γ γ              →⟨ NegativeErasedContext-upwards-closed γ≤rδ+η ⟩
  NegativeErasedContext Γ (r ·ᶜ δ +ᶜ η)  →⟨ NegativeErasedContext-𝟘 (λ _ → proj₁ ∘→ +ᶜ-positive-⟨⟩ (_ ·ᶜ δ)) ⟩
  NegativeErasedContext Γ (r ·ᶜ δ)       →⟨ (NegativeErasedContext-𝟘 λ _ →
                                               (λ { (inj₁ r≡𝟘)    → ⊥-elim (r≢𝟘 r≡𝟘)
                                                  ; (inj₂ δ⟨x⟩≡𝟘) → δ⟨x⟩≡𝟘
                                                  }) ∘→
                                               ·ᶜ-zero-product-⟨⟩ δ) ⟩
  NegativeErasedContext Γ δ              →⟨ neNeg ⊢t t-ne (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ r≢𝟘) δ▸t) ⟩
  NegativeType Γ (Σᵣ p , q ▷ B ▹ C)      →⟨ flip ¬negΣᵣ (refl (ΠΣⱼ ⊢B ⊢C ok₁)) ⟩
  ⊥                                      →⟨ ⊥-elim ⟩
  NegativeType Γ (A [ t ]₀)              □ }}
neNeg (emptyrecⱼ _ d) (emptyrecₙ _) _ _ =
  ⊥-elim (consistent d)
neNeg (conv d c) n γ▸u nΓγ =
  conv (neNeg d n γ▸u nΓγ) c

-- Lemma: A normal form which has the type ℕ in a negative/erased
-- context, and which is well-resourced (with respect to the mode 𝟙ᵐ),
-- is a numeral.

nfN : (d : Γ ⊢ u ∷ A)
    → (m : γ ▸[ 𝟙ᵐ ] u)
    → NegativeErasedContext Γ γ
    → (n : Nf u)
    → (c : Γ ⊢ A ≡ ℕ)
    → Numeral u

-- Case: neutrals. The type cannot be ℕ since it must be negative.
nfN d γ▸u nΓγ (ne n) c =
  ⊥-elim (¬negℕ (neNeg d (nfNeutral n) γ▸u nΓγ) c)

-- Case: numerals.
nfN (zeroⱼ x) γ▸u _ zeroₙ   c = zeroₙ
nfN (sucⱼ d) γ▸u nΓγ (sucₙ n) c =
  let invUsageSuc δ▸n γ≤δ = inv-usage-suc γ▸u
  in  sucₙ (nfN d (sub δ▸n γ≤δ) nΓγ n c)

-- Case: conversion.
nfN (conv d c) γ▸u nΓγ n c' =
  nfN d γ▸u nΓγ n (trans c c')

-- Impossible cases: type is not ℕ.

-- * Canonical types
nfN (ΠΣⱼ _ _ _) _ _ (ΠΣₙ _ _) c = ⊥-elim (U≢ℕ c)
nfN (ℕⱼ _)      _ _ ℕₙ        c = ⊥-elim (U≢ℕ c)
nfN (Emptyⱼ _)  _ _ Emptyₙ    c = ⊥-elim (U≢ℕ c)
nfN (Unitⱼ _ _) _ _ Unitₙ     c = ⊥-elim (U≢ℕ c)

-- * Canonical forms
nfN (lamⱼ _ _ _)      _ _ (lamₙ _)    c = ⊥-elim (ℕ≢Π (sym c))
nfN (prodⱼ _ _ _ _ _) _ _ (prodₙ _ _) c = ⊥-elim (ℕ≢Σ (sym c))
nfN (starⱼ _ _)       _ _ starₙ       c = ⊥-elim (ℕ≢Unitⱼ (sym c))
-- q.e.d

-- Terms of non-negative types reduce to non-neutrals

¬NeutralNf :
  Γ ⊢ t ∷ A → γ ▸[ 𝟙ᵐ ] t →
  NegativeErasedContext Γ γ → (NegativeType Γ A → ⊥) →
  ∃ λ u → Γ ⊢ t ⇒* u ∷ A × Whnf u × (Neutral u → ⊥)
¬NeutralNf ⊢t γ▸t nΓγ ¬negA =
  let u , whnfU , d = whNormTerm ⊢t
      γ▸u = usagePres*Term γ▸t (redₜ d)
  in  u , redₜ d , whnfU , λ x → ¬negA (neNeg (⊢u-redₜ d) x γ▸u nΓγ)

-- Canonicity theorem: A term which has the type ℕ in a
-- negative/erased context, and which is well-resourced (with respect
-- to the mode 𝟙ᵐ), ⇒ˢ*-reduces to a numeral.

canonicityRed′ :
  ∀ {l} → (⊢Γ : ⊢ Γ) → γ ▸[ 𝟙ᵐ ] t → NegativeErasedContext Γ γ →
  Γ ⊩⟨ l ⟩ t ∷ ℕ / ℕᵣ (idRed:*: (ℕⱼ ⊢Γ)) →
  ∃ λ v → Numeral v × Γ ⊢ t ⇒ˢ* v ∷ℕ
canonicityRed′ {l = l} ⊢Γ γ▸t nΓγ (ℕₜ _ d n≡n (sucᵣ x)) =
  let invUsageSuc δ▸n γ≤δ = inv-usage-suc (usagePres*Term γ▸t (redₜ d))
      v , numV , d′ = canonicityRed′ {l = l} ⊢Γ (sub δ▸n γ≤δ) nΓγ x
  in  suc v , sucₙ numV , ⇒ˢ*∷ℕ-trans (whred* (redₜ d)) (sucred* d′)
canonicityRed′ _ _ _ (ℕₜ _ d _ zeroᵣ) =
  zero , zeroₙ , whred* (redₜ d)
canonicityRed′ ⊢Γ γ▸t nΓγ (ℕₜ n d n≡n (ne (neNfₜ neK ⊢k k≡k))) =
  let u , d′ , whU , ¬neU =
        ¬NeutralNf (⊢t-redₜ d) γ▸t nΓγ
          (λ negℕ → ¬negℕ negℕ (refl (ℕⱼ ⊢Γ)))
  in  ⊥-elim (¬neU (PE.subst Neutral (whrDet*Term (redₜ d , ne neK) (d′ , whU)) neK))

canonicityRed :
  Γ ⊢ t ∷ ℕ → γ ▸[ 𝟙ᵐ ] t → NegativeErasedContext Γ γ →
  ∃ λ u → Numeral u × Γ ⊢ t ⇒ˢ* u ∷ℕ
canonicityRed ⊢t γ▸t nΓγ with reducibleTerm ⊢t
... | [ℕ] , [t] =
  let ⊢Γ = wfTerm ⊢t
      [ℕ]′ = ℕᵣ {l = ¹} (idRed:*: (ℕⱼ ⊢Γ))
      [t]′ = irrelevanceTerm [ℕ] [ℕ]′ [t]
  in  canonicityRed′ {l = ¹} ⊢Γ γ▸t nΓγ [t]′

-- A variant of the previous result for terms that are well-resourced
-- with respect to 𝟘ᶜ.

canonicityRed-𝟘ᶜ :
  Γ ⊢ t ∷ ℕ → 𝟘ᶜ ▸[ 𝟙ᵐ ] t → ∃ λ u → Numeral u × Γ ⊢ t ⇒ˢ* u ∷ℕ
canonicityRed-𝟘ᶜ ⊢t 𝟘▸t = canonicityRed ⊢t 𝟘▸t erasedContext

-- Canonicity theorem: A term which has the type ℕ in a
-- negative/erased context, and which is well-resourced (with respect
-- to the mode 𝟙ᵐ), is convertible to a numeral.

canonicityEq :
  Γ ⊢ t ∷ ℕ → γ ▸[ 𝟙ᵐ ] t → NegativeErasedContext Γ γ →
  ∃ λ u → Numeral u × Γ ⊢ t ≡ u ∷ ℕ
canonicityEq ⊢t γ▸t nΓγ =
  let u , numU , d = canonicityRed ⊢t γ▸t nΓγ
  in  u , numU , subset*Termˢ d

-- A variant of the previous result for terms that are well-resourced
-- with respect to 𝟘ᶜ.

canonicityEq-𝟘ᶜ :
  Γ ⊢ t ∷ ℕ → 𝟘ᶜ ▸[ 𝟙ᵐ ] t → ∃ λ u → Numeral u × Γ ⊢ t ≡ u ∷ ℕ
canonicityEq-𝟘ᶜ ⊢t 𝟘▸t = canonicityEq ⊢t 𝟘▸t erasedContext
