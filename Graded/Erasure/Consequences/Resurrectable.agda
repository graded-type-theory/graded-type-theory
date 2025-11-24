------------------------------------------------------------------------
-- Resurrectable types
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Erasure.Consequences.Resurrectable
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions TR
open Usage-restrictions UR

open import Definition.Typed TR
open import Definition.Typed.Consequences.Canonicity TR
open import Definition.Typed.Consequences.Consistency TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.EqRelInstance TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Reasoning.Term TR
open import Definition.Typed.Syntactic TR
open import Definition.Untyped M
open import Definition.Untyped.Erased 𝕄 as Erased using (Erased)
open import Definition.Untyped.Unit 𝕄

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Derived.Erased.Usage 𝕄 UR
open import Graded.Derived.Sigma 𝕄 UR
open import Graded.Derived.Unit UR
open import Graded.Erasure.Consequences.Identity TR UR
import Graded.Erasure.LogicalRelation as L
open import Graded.Erasure.LogicalRelation.Assumptions TR
open import Graded.Erasure.LogicalRelation.Fundamental TR UR
open import Graded.Erasure.LogicalRelation.Fundamental.Assumptions TR UR
import Graded.Erasure.LogicalRelation.Hidden as H
import Graded.Erasure.Target as T
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
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private variable
  n       : Nat
  Γ       : Con Term _
  l       : Term _
  q₁ q₂   : M
  s s₁ s₂ : Strength

-- The type A is "resurrectable" with respect to Γ (as well as a
-- strength, some grades and a term that stands for a universe level)
-- if (roughly speaking) there is a function that
-- * given an erased value x of type A, returns a value y of type A
--   along with an erased proof which shows that y is equal to x,
-- * is well-typed with respect to Γ, and
-- * is well-resourced with respect to 𝟘ᶜ.

Resurrectable : Strength → M → M → Con Term n → Term n → Term n → Set a
Resurrectable s q₁ q₂ Γ l A =
  ∃ λ t →
    𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
    Γ ⊢ t ∷
      Π 𝟘 , q₁ ▷ A ▹
      Σ⟨ s ⟩ 𝟙 , q₂ ▷ wk1 A ▹
      Erased s (wk2 l) (Id (wk2 A) (var x0) (var x1))

opaque

  -- If certain assumptions hold, then Empty is resurrectable with
  -- respect to certain things.

  Empty-resurrectable :
    Emptyrec-allowed 𝟙ᵐ 𝟘 →
    Π-allowed 𝟘 q₁ →
    Σ-allowed s 𝟙 q₂ →
    Erased-allowed s →
    (¬ T 𝟘ᵐ-allowed → Id-erased → q₂ ≤ 𝟘) →
    (¬ T 𝟘ᵐ-allowed → ¬ Id-erased → q₂ ≤ 𝟙) →
    ⊢ Γ →
    Resurrectable s q₁ q₂ Γ zeroᵘ Empty
  Empty-resurrectable
    {s} {q₂} {Γ} emptyrec-ok ok₁ ok₂ Erased-ok hyp₁ hyp₂ ⊢Γ =
      (lam 𝟘 $
       emptyrec 𝟘
         (Σ⟨ s ⟩ 𝟙 , q₂ ▷ Empty ▹
          Erased s zeroᵘ (Id Empty (var x0) (var x1)))
         (var x0))
    , (lamₘ $
       sub
         (emptyrecₘ var
            (ΠΣₘ Emptyₘ $ ▸Erased _ zeroᵘₘ $
             Idₘ-generalised Emptyₘ var var
               (λ erased → begin
                  𝟘ᶜ ∧ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝) ∙ (⌜ 𝟘ᵐ? ⌝ · q₂)  ≤⟨ ∧ᶜ-decreasingˡ _ _ ∙
                                                            𝟘ᵐ?-elim (λ m → ⌜ m ⌝ · q₂ ≤ 𝟘)
                                                              (≤-reflexive (·-zeroˡ _))
                                                              (λ not-ok →
                                                                 ≤-trans (≤-reflexive (·-identityˡ _)) $
                                                                 hyp₁ not-ok erased) ⟩
                  𝟘ᶜ                                     ∎)
               (λ not-erased → begin
                  𝟘ᶜ ∧ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝) ∙ (⌜ 𝟘ᵐ? ⌝ · q₂)       ≤⟨ ∧ᶜ-decreasingʳ _ _ ∙
                                                                 𝟘ᵐ?-elim (λ m → ⌜ m ⌝ · q₂ ≤ ⌜ m ⌝)
                                                                   (≤-reflexive (·-zeroˡ _))
                                                                   (λ not-ok →
                                                                      ≤-trans (≤-reflexive (·-identityˡ _)) $
                                                                      hyp₂ not-ok not-erased) ⟩
                  𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ ∙ ⌜ 𝟘ᵐ? ⌝                      ≈˘⟨ +ᶜ-identityˡ _ ∙ +-identityʳ _ ⟩
                  (𝟘ᶜ , x0 ≔ ⌜ 𝟘ᵐ? ⌝) +ᶜ (𝟘ᶜ , x1 ≔ ⌜ 𝟘ᵐ? ⌝)  ∎))
            emptyrec-ok)
         (begin
            𝟘ᶜ ∙ 𝟙 · 𝟘                  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
            𝟘ᶜ                          ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
            𝟘 ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ ⌞ 𝟘 ⌟ ⌝)  ∎))
    , (lamⱼ′ ok₁ $
       emptyrecⱼ
         (ΠΣⱼ
            (Erasedⱼ Erased-ok (⊢zeroᵘ (⊢Γ ∙[ ⊢Empty ] ∙[ ⊢Empty ])) $
             Idⱼ′
               (var₀ (⊢Empty (⊢Γ ∙[ ⊢Empty ])))
               (var₁ (⊢Empty (⊢Γ ∙[ ⊢Empty ]))))
            ok₂)
         (var₀ (⊢Empty ⊢Γ)))
    where
    open ≤ᶜ-reasoning

opaque

  -- If certain assumptions hold, then Unit s₂ is resurrectable with
  -- respect to certain things.

  Unit-resurrectable :
    Π-allowed 𝟘 q₁ →
    Σ-allowed s₁ 𝟙 q₂ →
    Erased-allowed s₁ →
    Unit-allowed s₂ →
    (s₂ PE.≡ 𝕨 → Unitrec-allowed 𝟘ᵐ? 𝟙 Unit-η-grade) →
    ⊢ Γ →
    Resurrectable s₁ q₁ q₂ Γ zeroᵘ (Unit s₂)
  Unit-resurrectable
    {s₁} {s₂} {Γ} ok₁ ok₂ Erased-ok Unit-ok ur-ok ⊢Γ =
      lam 𝟘
        (prod s₁ 𝟙 (star s₂) ([ Unit-η s₂ Unit-η-grade (var x0) ]))
    , (lamₘ $
       prodₘ starₘ (▸[] _ $ ▸Unit-η′ ur-ok (λ _ → _ , var) .proj₂)
         (λ _ → begin
            𝟘ᶜ ∙ 𝟙 · 𝟘     ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
            𝟘ᶜ             ≈˘⟨ ·ᶜ-identityˡ _ ⟩
            𝟙 ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
            𝟙 ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎)
         (λ _ → begin
            𝟘ᶜ ∙ 𝟙 · 𝟘     ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
            𝟘ᶜ             ≈˘⟨ ∧ᶜ-idem _ ⟩
            𝟘ᶜ ∧ᶜ 𝟘ᶜ       ≈˘⟨ ∧ᶜ-congʳ $ ·ᶜ-zeroʳ _ ⟩
            𝟙 ·ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ  ∎))
    , (lamⱼ′ ok₁ $
       prodⱼ
         (Erasedⱼ Erased-ok (⊢zeroᵘ (∙ ⊢Unit₂)) $
          Idⱼ′ (var₀ ⊢Unit₂) (var₁ ⊢Unit₂))
         ⊢star
         (PE.subst (_⊢_∷_ _ _) (PE.sym Erased-[]) $
          []ⱼ Erased-ok (⊢zeroᵘ ⊢Γ∙Unit) (⊢Unit-η (var₀ ⊢Unit₁)))
         ok₂)
    where
    open Erased s₁
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

    ⊢Unit₁ : Γ ⊢ Unit s₂
    ⊢Unit₁ = ⊢Unit ⊢Γ Unit-ok

    ⊢Γ∙Unit : ⊢ Γ ∙ Unit s₂
    ⊢Γ∙Unit = ∙ ⊢Unit₁

    ⊢Unit₂ : Γ ∙ Unit s₂ ⊢ Unit s₂
    ⊢Unit₂ = ⊢Unit ⊢Γ∙Unit Unit-ok

    ⊢star : Γ ∙ Unit s₂ ⊢ star s₂ ∷ Unit s₂
    ⊢star = starⱼ ⊢Γ∙Unit Unit-ok

opaque

  -- If the modality's zero is well-behaved and Erased is allowed,
  -- then ℕ is not resurrectable with respect to the empty context.

  ¬-ℕ-resurrectable-ε :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
    Erased-allowed s →
    ¬ Resurrectable s q₁ q₂ ε l ℕ
  ¬-ℕ-resurrectable-ε ok (_ , ▸t , ⊢t) =
    -- By the fundamental theorem t is related to erase t.
    case Fundamental.fundamentalErased-𝟙ᵐ
           fundamental-assumptions₀ ⊢t ▸t of λ {
      t®erase-t →

    -- Let us first apply t to zero.
    case ®∷Σω⇔ non-trivial .proj₁ $
         ®∷Π₀⇔ .proj₁ t®erase-t .proj₂ .proj₂
           zero (zeroⱼ (wfTerm ⊢t)) of λ {
      (_ , t₁ , _ , _ , _ , t∘0⇒t₁,t₂ , erase-t∘↯⇒v₁,v₂ , t₁®v₁ , _) →

    -- The term t₁ is definitionally equal to zero.
    case ε⊢∷Id→ε⊢≡∷ $
         erasedⱼ $
         PE.subst (_⊢_∷_ _ _)
           (PE.trans (PE.cong _[ _ ]₀ (Erased.Erased-[] _)) $
            Erased.Erased-[] _) $
         inversion-prod-Σ
           (syntacticEqTerm (subset*Term t∘0⇒t₁,t₂) .proj₂ .proj₂)
           .proj₂ .proj₁ of λ
      (t₁≡0 : ε ⊢ t₁ ≡ zero ∷ ℕ) →

    -- Either both of t₁ and v₁ reduce to zero, or both reduce to an
    -- application of suc.
    case ®∷ℕ⇔ .proj₁ t₁®v₁ of λ where
      (sucᵣ {t′ = t₁′} t₁⇒suc-t₁′ _ _ _) →
        -- The term t₁ is definitionally equal to zero, so it cannot
        -- reduce to an application of suc.
        zero≢suc
          (zero     ≡˘⟨ t₁≡0 ⟩⊢
           t₁       ≡⟨ subset*Term t₁⇒suc-t₁′ ⟩⊢∎
           suc t₁′  ∎)

      (zeroᵣ t₁⇒zero v₁⇒zero) →
        -- Let us now apply t to suc zero.
        case ®∷Σω⇔ non-trivial .proj₁ $
             ®∷Π₀⇔ .proj₁ t®erase-t .proj₂ .proj₂
               (suc zero) (sucⱼ (zeroⱼ (wfTerm ⊢t))) of λ {
          (_ , t₁′ , _ , _ , _ ,
           t∘1⇒t₁′,t₂′ , erase-t∘↯⇒v₁′,v₂′ , t₁′®v₁′ , _) →

        -- The term t₁′ is definitionally equal to suc zero.
        case ε⊢∷Id→ε⊢≡∷ $
             erasedⱼ $
             PE.subst (_⊢_∷_ _ _)
               (PE.trans (PE.cong _[ _ ]₀ $ Erased.Erased-[] _) $
                Erased.Erased-[] _) $
             inversion-prod-Σ
               (syntacticEqTerm (subset*Term t∘1⇒t₁′,t₂′)
                  .proj₂ .proj₂)
               .proj₂ .proj₁ of λ
          (t₁′≡1 : ε ⊢ t₁′ ≡ suc zero ∷ ℕ) →

        -- Either both of t₁ and v₁′ reduce to zero, or both
        -- reduce to an application of suc.
        case ®∷ℕ⇔ .proj₁ t₁′®v₁′ of λ where
          (zeroᵣ t₁′⇒zero _) →
            -- The term t₁′ is definitionally equal to suc zero,
            -- so it cannot reduce to zero.
            zero≢suc
              (zero      ≡˘⟨ subset*Term t₁′⇒zero ⟩⊢
               t₁′       ≡⟨ t₁′≡1 ⟩⊢∎
               suc zero  ∎)

          (sucᵣ _ v₁′⇒suc _ _) →
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
                case TP.suc-noRed suc⇒zero of λ () }}}}
    where
    open Fundamental-assumptions fundamental-assumptions₀

    as : Assumptions
    as = record { ⊢Δ = well-formed; inc = inc; str = T.non-strict }

    open H as
    open L as

opaque

  -- If 𝟘ᵐ is allowed, η-equality is not allowed for weak unit types
  -- unless a certain condition is satisfied, and []-cong is allowed
  -- for s (and another assumption holds if s is 𝕨), then ℕ is not
  -- s-resurrectable with respect to zeroᵘ and any context that
  -- satisfies Fundamental-assumptions⁻.
  --
  -- Note that if []-cong is allowed, then (at the time of writing)
  -- Fundamental-assumptions⁻ only holds for the empty context.

  ¬-ℕ-resurrectable :
    ⦃ ok : T 𝟘ᵐ-allowed ⦄ →
    (∀ {p q} →
     Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
     p ≤ 𝟘) →
    (s PE.≡ 𝕨 → Prodrec-allowed 𝟘ᵐ (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    []-cong-allowed s →
    []-cong-allowed-mode s 𝟙ᵐ →
    Fundamental-assumptions⁻ Γ →
    ¬ Resurrectable s q₁ q₂ Γ zeroᵘ ℕ
  ¬-ℕ-resurrectable
    {Γ} ⦃ ok ⦄ Unitʷ-η→ P-ok []-cong-ok []-cong-ok′ as (_ , ▸t , ⊢t) =
    let ⊢0 = ⊢zeroᵘ (wfTerm ⊢t) in

    -- By the fundamental theorem t is related to erase t.
    case Fundamental.fundamentalErased-𝟙ᵐ
           (record
              { well-formed       = wfTerm ⊢t
              ; other-assumptions = as
              })
           ⊢t ▸t of λ {
      t®erase-t →

    -- Let us first apply t to zero.
    case ®∷Σω⇔ non-trivial .proj₁ $
         ®∷Π₀⇔ .proj₁ t®erase-t .proj₂ .proj₂
           zero (zeroⱼ (wfTerm ⊢t)) of λ {
      (_ , t₁ , _ , _ , _ , t∘0⇒t₁,t₂ , erase-t∘↯⇒v₁,v₂ , t₁®v₁ , _) →

    -- The term t₁ is definitionally equal to zero.
    case inv-usage-prod
           (usagePres*Term Unitʷ-η→ (▸t ∘ₘ zeroₘ) t∘0⇒t₁,t₂) of λ {
      (invUsageProd ▸t₁ ▸t₂ _ _) →
    case Id→≡″ []-cong-ok []-cong-ok′ P-ok as zeroᵘₘ ℕₘ (▸-𝟘 ▸t₁) zeroₘ
           (▸-𝟘 ▸t₂) ⊢0 $
         PE.subst (_⊢_∷_ _ _)
           (PE.trans (PE.cong _[ _ ]₀ $ Erased.Erased-[] _) $
            Erased.Erased-[] _) $
         inversion-prod-Σ
           (syntacticEqTerm (subset*Term t∘0⇒t₁,t₂) .proj₂ .proj₂)
           .proj₂ .proj₁ of λ
      (t₁≡0 : Γ ⊢ t₁ ≡ zero ∷ ℕ) →

    -- Either both of t₁ and v₁ reduce to zero, or both reduce to an
    -- application of suc.
    case ®∷ℕ⇔ .proj₁ t₁®v₁ of λ where
      (sucᵣ {t′ = t₁′} t₁⇒suc-t₁′ _ _ _) →
        -- The term t₁ is definitionally equal to zero, so it cannot
        -- reduce to an application of suc.
        zero≢suc
          (zero     ≡˘⟨ t₁≡0 ⟩⊢
           t₁       ≡⟨ subset*Term t₁⇒suc-t₁′ ⟩⊢∎
           suc t₁′  ∎)

      (zeroᵣ t₁⇒zero v₁⇒zero) →
        -- Let us now apply t to suc zero.
        case ®∷Σω⇔ non-trivial .proj₁ $
             ®∷Π₀⇔ .proj₁ t®erase-t .proj₂ .proj₂
               (suc zero) (sucⱼ (zeroⱼ (wfTerm ⊢t))) of λ {
          (_ , t₁′ , _ , _ , _ ,
           t∘1⇒t₁′,t₂′ , erase-t∘↯⇒v₁′,v₂′ , t₁′®v₁′ , _) →

        -- The term t₁′ is definitionally equal to suc zero.
        case inv-usage-prod
               (usagePres*Term Unitʷ-η→ (▸t ∘ₘ sucₘ zeroₘ)
                  t∘1⇒t₁′,t₂′) of λ {
          (invUsageProd ▸t₁′ ▸t₂′ _ _) →
        case Id→≡″ []-cong-ok []-cong-ok′ P-ok as zeroᵘₘ ℕₘ (▸-𝟘 ▸t₁′)
               (sucₘ zeroₘ) (▸-𝟘 ▸t₂′) ⊢0 $
             PE.subst (_⊢_∷_ _ _)
               (PE.trans (PE.cong _[ _ ]₀ $ Erased.Erased-[] _) $
                Erased.Erased-[] _) $
             inversion-prod-Σ
               (syntacticEqTerm (subset*Term t∘1⇒t₁′,t₂′)
                  .proj₂ .proj₂)
               .proj₂ .proj₁ of λ
          (t₁′≡1 : Γ ⊢ t₁′ ≡ suc zero ∷ ℕ) →

        -- Either both of t₁ and v₁′ reduce to zero, or both
        -- reduce to an application of suc.
        case ®∷ℕ⇔ .proj₁ t₁′®v₁′ of λ where
          (zeroᵣ t₁′⇒zero _) →
            -- The term t₁′ is definitionally equal to suc zero,
            -- so it cannot reduce to zero.
            zero≢suc
              (zero      ≡˘⟨ subset*Term t₁′⇒zero ⟩⊢
               t₁′       ≡⟨ t₁′≡1 ⟩⊢∎
               suc zero  ∎)

          (sucᵣ _ v₁′⇒suc _ _) →
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
    open Fundamental-assumptions⁻ as

    as′ : Assumptions
    as′ = record { ⊢Δ = wfTerm ⊢t; inc = inc; str = T.non-strict }

    open H as′
    open L as′

    instance

      _ : Has-well-behaved-zero semiring-with-meet
      _ = 𝟘-well-behaved ok
