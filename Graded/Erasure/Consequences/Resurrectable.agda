------------------------------------------------------------------------
-- Resurrectable types
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Definition.Typed.Restrictions
import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Erasure.Consequences.Resurrectable
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions M)
  where

open Modality 𝕄
open Type-restrictions TR

open import Definition.Typed TR
open import Definition.Typed.Consequences.Canonicity TR
open import Definition.Typed.Consequences.Consistency TR
open import Definition.Typed.Consequences.DerivedRules TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Consequences.Syntactic TR
open import Definition.Typed.EqRelInstance TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Reasoning.Term TR
open import Definition.Untyped M hiding (_∷_)

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
import Graded.Derived.Erased.Typed TR as ET
open import Graded.Derived.Erased.Untyped 𝕄 as Erased using (Erased)
open import Graded.Derived.Erased.Usage 𝕄 UR
open import Graded.Erasure.Consequences.Identity TR UR
import Graded.Erasure.LogicalRelation TR as L
open import Graded.Erasure.LogicalRelation.Fundamental TR UR
open import Graded.Erasure.LogicalRelation.Fundamental.Assumptions TR UR
import Graded.Erasure.LogicalRelation.Hidden TR as H
import Graded.Erasure.Target.Properties as TP
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄
open import Graded.Reduction TR UR
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Inversion 𝕄 UR
open import Graded.Usage.Properties 𝕄 UR

open import Tools.Bool using (T)
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
open import Tools.Relation
open import Tools.Sum using (inj₁; inj₂)

private variable
  n     : Nat
  Γ     : Con Term _
  q₁ q₂ : M

-- The type A is "resurrectable" with respect to Γ (and some grades)
-- if (roughly speaking) there is a function that
-- * given an erased value x of type A, returns a value y of type A
--   along with an erased proof which shows that y is equal to x,
-- * is well-typed with respect to Γ, and
-- * is well-resourced with respect to 𝟘ᶜ.

Resurrectable : M → M → Con Term n → Term n → Set a
Resurrectable q₁ q₂ Γ A =
  ∃ λ t →
    𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
    Γ ⊢ t ∷
      Π 𝟘 , q₁ ▷ A ▹
      Σᵣ 𝟙 , q₂ ▷ wk1 A ▹ Erased (Id (wk1 (wk1 A)) (var x0) (var x1))

opaque

  -- If Erased and Unit are allowed, then Unit is resurrectable with
  -- respect to any well-formed context and grades that satisfy
  -- certain properties.

  Unit-resurrectable :
    Erased-allowed →
    Unit-allowed →
    Π-allowed 𝟘 q₁ →
    Σᵣ-allowed 𝟙 q₂ →
    ⊢ Γ →
    Resurrectable q₁ q₂ Γ Unit
  Unit-resurrectable {Γ} Erased-ok Unit-ok ok₁ ok₂ ⊢Γ =
      lam 𝟘 (prodᵣ 𝟙 star Erased.[ rfl ])
    , (lamₘ $
       sub (prodᵣₘ starₘ (▸[] rflₘ)) $ begin
         𝟘ᶜ ∙ 𝟙 · 𝟘     ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
         𝟘ᶜ             ≈˘⟨ ·ᶜ-identityˡ _ ⟩
         𝟙 ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
         𝟙 ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎)
    , (lamⱼ′ ok₁ $
       ⊢prod (Erasedⱼ (Idⱼ (var ⊢₂ here) (var ⊢₂ (there here))))
         (starⱼ ⊢₁ Unit-ok)
         ([]ⱼ (rflⱼ′ (Unit-η (var ⊢₁ here)))) ok₂)
    where
    open ET Erased-ok
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

    ⊢₁ : ⊢ Γ ∙ Unit
    ⊢₁ = ⊢Γ ∙ Unitⱼ ⊢Γ Unit-ok

    ⊢₂ : ⊢ Γ ∙ Unit ∙ Unit
    ⊢₂ = ⊢₁ ∙ Unitⱼ ⊢₁ Unit-ok

opaque

  -- If the modality's zero is well-behaved and Erased is allowed,
  -- then ℕ is not resurrectable with respect to the empty context.

  ¬-ℕ-resurrectable-ε :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
    Erased-allowed →
    ¬ Resurrectable q₁ q₂ ε ℕ
  ¬-ℕ-resurrectable-ε ok (_ , ▸t , ⊢t) =
    -- By the fundamental theorem t is related to erase t.
    case Fundamental.fundamentalErased-𝟙ᵐ
           fundamental-assumptions₀ ⊢t ▸t of λ {
      t®erase-t →

    -- Let us first apply t to zero.
    case ®-Σ non-trivial $
         ®-Π₀ t®erase-t .proj₂ .proj₂ zero (zeroⱼ (wfTerm ⊢t)) of λ {
      (_ , _ , t₁ , _ , _ , _ ,
       t∘0⇒t₁,t₂ , erase-t∘↯⇒v₁,v₂ , t₁®v₁ , _) →

    -- The term t₁ is definitionally equal to zero.
    case inv-usage-prodᵣ (usagePres*Term (▸t ∘ₘ zeroₘ) t∘0⇒t₁,t₂) of λ {
      (invUsageProdᵣ ▸t₁ ▸t₂ _) →
    case ε⊢∷Id→ε⊢≡∷ $
         erasedⱼ $
         inversion-prod-Σ
           (syntacticEqTerm (subset*Term t∘0⇒t₁,t₂) .proj₂ .proj₂)
           .proj₂ .proj₁ of λ
      (t₁≡0 : ε ⊢ t₁ ≡ zero ∷ ℕ) →

    -- Either both of t₁ and v₁ reduce to zero, or both reduce to an
    -- application of suc.
    case ®-ℕ t₁®v₁ of λ where
      (sucᵣ {t′ = t₁′} t₁⇒suc-t₁′ _ _) →
        -- The term t₁ is definitionally equal to zero, so it cannot
        -- reduce to an application of suc.
        zero≢suc
          (zero     ≡˘⟨ t₁≡0 ⟩⊢
           t₁       ≡⟨ subset*Term t₁⇒suc-t₁′ ⟩⊢∎
           suc t₁′  ∎)

      (zeroᵣ t₁⇒zero v₁⇒zero) →
        -- Let us now apply t to suc zero.
        case ®-Σ non-trivial $
             ®-Π₀ t®erase-t .proj₂ .proj₂
               (suc zero) (sucⱼ (zeroⱼ (wfTerm ⊢t))) of λ {
          (_ , _ , t₁′ , _ , _ , _ ,
           t∘1⇒t₁′,t₂′ , erase-t∘↯⇒v₁′,v₂′ , t₁′®v₁′ , _) →

        -- The term t₁′ is definitionally equal to suc zero.
        case inv-usage-prodᵣ
               (usagePres*Term (▸t ∘ₘ sucₘ zeroₘ)
                  t∘1⇒t₁′,t₂′) of λ {
          (invUsageProdᵣ ▸t₁′ ▸t₂′ _) →
        case ε⊢∷Id→ε⊢≡∷ $
             erasedⱼ $
             inversion-prod-Σ
               (syntacticEqTerm (subset*Term t∘1⇒t₁′,t₂′)
                  .proj₂ .proj₂)
               .proj₂ .proj₁ of λ
          (t₁′≡1 : ε ⊢ t₁′ ≡ suc zero ∷ ℕ) →

        -- Either both of t₁ and v₁′ reduce to zero, or both
        -- reduce to an application of suc.
        case ®-ℕ t₁′®v₁′ of λ where
          (zeroᵣ t₁′⇒zero _) →
            -- The term t₁′ is definitionally equal to suc zero,
            -- so it cannot reduce to zero.
            zero≢suc
              (zero      ≡˘⟨ subset*Term t₁′⇒zero ⟩⊢
               t₁′       ≡⟨ t₁′≡1 ⟩⊢∎
               suc zero  ∎)

          (sucᵣ _ v₁′⇒suc _) →
            -- The terms v₁ and v₁′ have to be equal, because
            -- reduction is deterministic.
            case
              (case TP.red*Det erase-t∘↯⇒v₁,v₂
                      erase-t∘↯⇒v₁′,v₂′ of λ where
                 (inj₁ v₁,v₂⇒*v₁′,v₂′) → TP.prod-noRed v₁,v₂⇒*v₁′,v₂′
                 (inj₂ v₁′,v₂′⇒*v₁,v₂) →
                   PE.sym $ TP.prod-noRed v₁′,v₂′⇒*v₁,v₂)
            of λ {
              PE.refl →

            -- The term v₁′ cannot reduce to an application of
            -- suc, because it reduces to zero.
            case TP.red*Det v₁⇒zero v₁′⇒suc of λ where
              (inj₁ zero⇒suc) → case TP.zero-noRed zero⇒suc of λ ()
              (inj₂ suc⇒zero) →
                case TP.suc-noRed suc⇒zero of λ () }}}}}}
    where
    open ET ok
    open Fundamental-assumptions fundamental-assumptions₀
    open H is-𝟘? well-formed
    open L is-𝟘? well-formed

opaque

  -- If the modality's zero is well-behaved and []-cong and 𝟘ᵐ are
  -- allowed, then ℕ is not resurrectable with respect to any context
  -- that satisfies Fundamental-assumptions⁻.
  --
  -- Note that if []-cong is allowed, then (at the time of writing)
  -- Fundamental-assumptions⁻ only holds for the empty context.

  ¬-ℕ-resurrectable :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄
    ⦃ ok : T 𝟘ᵐ-allowed ⦄ →
    []-cong-allowed →
    Fundamental-assumptions⁻ Γ →
    ¬ Resurrectable q₁ q₂ Γ ℕ
  ¬-ℕ-resurrectable {Γ} []-cong-ok ok (_ , ▸t , ⊢t) =
    -- By the fundamental theorem t is related to erase t.
    case Fundamental.fundamentalErased-𝟙ᵐ
           (record
              { well-formed       = wfTerm ⊢t
              ; other-assumptions = ok
              })
           ⊢t ▸t of λ {
      t®erase-t →

    -- Let us first apply t to zero.
    case ®-Σ non-trivial $
         ®-Π₀ t®erase-t .proj₂ .proj₂ zero (zeroⱼ (wfTerm ⊢t)) of λ {
      (_ , _ , t₁ , _ , _ , _ ,
       t∘0⇒t₁,t₂ , erase-t∘↯⇒v₁,v₂ , t₁®v₁ , _) →

    -- The term t₁ is definitionally equal to zero.
    case inv-usage-prodᵣ (usagePres*Term (▸t ∘ₘ zeroₘ) t∘0⇒t₁,t₂) of λ {
      (invUsageProdᵣ ▸t₁ ▸t₂ _) →
    case Id→≡″ []-cong-ok ok ℕₘ (▸-𝟘 ▸t₁) zeroₘ (▸-𝟘 ▸t₂) $
         inversion-prod-Σ
           (syntacticEqTerm (subset*Term t∘0⇒t₁,t₂) .proj₂ .proj₂)
           .proj₂ .proj₁ of λ
      (t₁≡0 : Γ ⊢ t₁ ≡ zero ∷ ℕ) →

    -- Either both of t₁ and v₁ reduce to zero, or both reduce to an
    -- application of suc.
    case ®-ℕ t₁®v₁ of λ where
      (sucᵣ {t′ = t₁′} t₁⇒suc-t₁′ _ _) →
        -- The term t₁ is definitionally equal to zero, so it cannot
        -- reduce to an application of suc.
        zero≢suc
          (zero     ≡˘⟨ t₁≡0 ⟩⊢
           t₁       ≡⟨ subset*Term t₁⇒suc-t₁′ ⟩⊢∎
           suc t₁′  ∎)

      (zeroᵣ t₁⇒zero v₁⇒zero) →
        -- Let us now apply t to suc zero.
        case ®-Σ non-trivial $
             ®-Π₀ t®erase-t .proj₂ .proj₂
               (suc zero) (sucⱼ (zeroⱼ (wfTerm ⊢t))) of λ {
          (_ , _ , t₁′ , _ , _ , _ ,
           t∘1⇒t₁′,t₂′ , erase-t∘↯⇒v₁′,v₂′ , t₁′®v₁′ , _) →

        -- The term t₁′ is definitionally equal to suc zero.
        case inv-usage-prodᵣ
               (usagePres*Term (▸t ∘ₘ sucₘ zeroₘ)
                  t∘1⇒t₁′,t₂′) of λ {
          (invUsageProdᵣ ▸t₁′ ▸t₂′ _) →
        case Id→≡″ []-cong-ok ok ℕₘ (▸-𝟘 ▸t₁′) (sucₘ zeroₘ)
               (▸-𝟘 ▸t₂′) $
             inversion-prod-Σ
               (syntacticEqTerm (subset*Term t∘1⇒t₁′,t₂′)
                  .proj₂ .proj₂)
               .proj₂ .proj₁ of λ
          (t₁′≡1 : Γ ⊢ t₁′ ≡ suc zero ∷ ℕ) →

        -- Either both of t₁ and v₁′ reduce to zero, or both
        -- reduce to an application of suc.
        case ®-ℕ t₁′®v₁′ of λ where
          (zeroᵣ t₁′⇒zero _) →
            -- The term t₁′ is definitionally equal to suc zero,
            -- so it cannot reduce to zero.
            zero≢suc
              (zero      ≡˘⟨ subset*Term t₁′⇒zero ⟩⊢
               t₁′       ≡⟨ t₁′≡1 ⟩⊢∎
               suc zero  ∎)

          (sucᵣ _ v₁′⇒suc _) →
            -- The terms v₁ and v₁′ have to be equal, because
            -- reduction is deterministic.
            case
              (case TP.red*Det erase-t∘↯⇒v₁,v₂
                      erase-t∘↯⇒v₁′,v₂′ of λ where
                 (inj₁ v₁,v₂⇒*v₁′,v₂′) → TP.prod-noRed v₁,v₂⇒*v₁′,v₂′
                 (inj₂ v₁′,v₂′⇒*v₁,v₂) →
                   PE.sym $ TP.prod-noRed v₁′,v₂′⇒*v₁,v₂)
            of λ {
              PE.refl →

            -- The term v₁′ cannot reduce to an application of
            -- suc, because it reduces to zero.
            case TP.red*Det v₁⇒zero v₁′⇒suc of λ where
              (inj₁ zero⇒suc) → case TP.zero-noRed zero⇒suc of λ ()
              (inj₂ suc⇒zero) →
                case TP.suc-noRed suc⇒zero of λ () }}}}}}
    where
    open Fundamental-assumptions⁻ ok
    open H is-𝟘? (wfTerm ⊢t)
    open L is-𝟘? (wfTerm ⊢t)
