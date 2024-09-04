
{-# OPTIONS --hidden-argument-puns #-}

open import Graded.Modality
open import Graded.Usage.Restrictions

open import Definition.Typed.Restrictions

module Heap.Bisimilarity
  {a} {M : Set a} {𝕄 : Modality M}
  (UR : Usage-restrictions 𝕄)
  (TR : Type-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions TR

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum hiding (id)

open import Heap.Options
open import Heap.Untyped 𝕄
open import Heap.Untyped.Properties 𝕄 type-variant
open import Heap.Usage 𝕄 UR
open import Heap.Usage.Assumptions
open import Heap.Usage.Properties UR type-variant
open import Heap.Normalization 𝕄 type-variant
import Heap.Reduction 𝕄 as R
import Heap.Reduction.Properties 𝕄 type-variant as RP


open import Definition.Untyped M
open import Definition.Typed TR
open import Definition.Typed.Properties TR
open import Definition.Typed.RedSteps TR hiding (_⇨*_)
open import Definition.Typed.Consequences.Canonicity TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Consequences.Reduction TR

open import Graded.Context 𝕄
open import Graded.Modality.Properties.Subtraction semiring-with-meet

private variable
  s s′ : State _ _
  H H′ H″ : Heap _
  t t′ u u′ A B : Term _
  E E′ : Env _ _
  S S′ : Stack _
  γ δ η : Conₘ _
  Γ : Con Term _

-- Bisimilarity between the tracking and non-tracking redutions
-- (with or without reduction to numerals).

module _ (ℕ-fullred : Bool) where

  private
    optsₜ optsₙₜ : Options
    optsₜ = tracking-and-ℕ-fullred-if ℕ-fullred
    optsₙₜ = not-tracking-and-ℕ-fullred-if ℕ-fullred
    module Rₜ = R optsₜ
    module Rₙₜ = R optsₙₜ

  open RP optsₙₜ

  -- Most of the bisimilarity properties are proven (only) under
  -- the assumption that the nr-function is factoring

  module _ ⦃ _ : Has-nr M semiring-with-meet ⦄
           ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
           where

    opaque

      bisim₁ₙ : s Rₜ.⇒ₙ ⟨ H , t , E , S ⟩
              → ∃ λ H′ → s Rₙₜ.⇒ₙ ⟨ H′ , t , E , S ⟩ × H ~ʰ H′
      bisim₁ₙ (Rₜ.varₕ d) = _ , Rₙₜ.varₕ′ (↦[]→↦ d) , ~ʰ-sym (update-~ʰ d)
      bisim₁ₙ Rₜ.appₕ     = _ , Rₙₜ.appₕ , ~ʰ-refl
      bisim₁ₙ Rₜ.fstₕ     = _ , Rₙₜ.fstₕ , ~ʰ-refl
      bisim₁ₙ Rₜ.sndₕ     = _ , Rₙₜ.sndₕ , ~ʰ-refl
      bisim₁ₙ Rₜ.prodrecₕ = _ , Rₙₜ.prodrecₕ , ~ʰ-refl
      bisim₁ₙ Rₜ.natrecₕ  = _ , Rₙₜ.natrecₕ , ~ʰ-refl
      bisim₁ₙ Rₜ.unitrecₕ = _ , Rₙₜ.unitrecₕ , ~ʰ-refl
      bisim₁ₙ Rₜ.Jₕ       = _ , Rₙₜ.Jₕ , ~ʰ-refl
      bisim₁ₙ Rₜ.Kₕ       = _ , Rₙₜ.Kₕ , ~ʰ-refl
      bisim₁ₙ Rₜ.[]-congₕ = _ , Rₙₜ.[]-congₕ , ~ʰ-refl

    opaque

      bisim₁ᵥ : s Rₜ.⇒ᵥ ⟨ H , t , E , S ⟩
              → s Rₙₜ.⇒ᵥ ⟨ H , t , E , S ⟩
      bisim₁ᵥ Rₜ.lamₕ   = Rₙₜ.lamₕ
      bisim₁ᵥ Rₜ.prodˢₕ₁ = Rₙₜ.prodˢₕ₁
      bisim₁ᵥ Rₜ.prodˢₕ₂ = Rₙₜ.prodˢₕ₂
      bisim₁ᵥ Rₜ.prodʷₕ = Rₙₜ.prodʷₕ
      bisim₁ᵥ Rₜ.zeroₕ  = Rₙₜ.zeroₕ
      bisim₁ᵥ Rₜ.sucₕ   = Rₙₜ.sucₕ
      bisim₁ᵥ Rₜ.starʷₕ = Rₙₜ.starʷₕ
      bisim₁ᵥ Rₜ.rflₕⱼ  = Rₙₜ.rflₕⱼ
      bisim₁ᵥ Rₜ.rflₕₖ  = Rₙₜ.rflₕₖ
      bisim₁ᵥ Rₜ.rflₕₑ  = Rₙₜ.rflₕₑ

    opaque

      bisim₁ₛ : s Rₜ.⇒ₛ ⟨ H , t , E , S ⟩
              → s Rₙₜ.⇒ₛ ⟨ H , t , E , S ⟩
      bisim₁ₛ (Rₜ.sucₕ x) = Rₙₜ.sucₕ x
      bisim₁ₛ (Rₜ.numₕ x) = Rₙₜ.numₕ x

    opaque

      bisim₁ : s Rₜ.⇒ ⟨ H , t , E , S ⟩
             → ∃ λ H′ → s Rₙₜ.⇒ ⟨ H′ , t , E , S ⟩ × H ~ʰ H′
      bisim₁ (Rₜ.⇒ₙ d) =
        case bisim₁ₙ d of λ
          (_ , d′ , H~H′) →
        _ , Rₙₜ.⇒ₙ d′ , H~H′
      bisim₁ (Rₜ.⇒ᵥ d) =
        _ , Rₙₜ.⇒ᵥ (bisim₁ᵥ d) , ~ʰ-refl
      bisim₁ (Rₜ.⇒ₛ d) =
        _ , Rₙₜ.⇒ₛ (bisim₁ₛ d) , ~ʰ-refl

    opaque

      bisim₁* : s Rₜ.⇒* ⟨ H , t , E , S ⟩
              → ∃ λ H′ → s Rₙₜ.⇒* ⟨ H′ , t , E , S ⟩ × H ~ʰ H′
      bisim₁* Rₜ.id =
        _ , Rₙₜ.id , ~ʰ-refl
      bisim₁* (x Rₜ.⇨ d) =
        case bisim₁ x of λ
          (_ , x′ , H~H′) →
        case bisim₁* d of λ
          (_ , d′ , H~H″) →
        case ~ʰ-⇒* d′ H~H′ of λ
          (_ , d″ , H~H‴) →
        _ , (x′ Rₙₜ.⇨ d″) , ~ʰ-trans H~H″ H~H‴

    opaque

      bisim₂ₙ : Supports-subtraction
              → ⟨ H , t , E , S ⟩ Rₙₜ.⇒ₙ ⟨ H′ , t′ , E′ , S′ ⟩
              → H ~ʰ H″
              → γ ⨾ δ ⨾ η ▸ ⟨ H″ , t , E , S ⟩
              → ∃ λ H‴ → ⟨ H″ , t , E , S ⟩ Rₜ.⇒ₙ ⟨ H‴ , t′ , E′ , S′ ⟩ × H′ ~ʰ H‴
      bisim₂ₙ ok (Rₙₜ.varₕ′ d) H~H′ ▸s =
        case ▸↦→↦[] ok (~ʰ-lookup H~H′ d) ▸s of λ
          (_ , d′) →
        _ , Rₜ.varₕ d′ , ~ʰ-trans H~H′ (update-~ʰ d′)
      bisim₂ₙ ok Rₙₜ.appₕ H~H′ ▸s     = _ , Rₜ.appₕ , H~H′
      bisim₂ₙ ok Rₙₜ.fstₕ H~H′ ▸s     = _ , Rₜ.fstₕ , H~H′
      bisim₂ₙ ok Rₙₜ.sndₕ H~H′ ▸s     = _ , Rₜ.sndₕ , H~H′
      bisim₂ₙ ok Rₙₜ.prodrecₕ H~H′ ▸s = _ , Rₜ.prodrecₕ , H~H′
      bisim₂ₙ ok Rₙₜ.natrecₕ H~H′ ▸s  = _ , Rₜ.natrecₕ , H~H′
      bisim₂ₙ ok Rₙₜ.unitrecₕ H~H′ ▸s = _ , Rₜ.unitrecₕ , H~H′
      bisim₂ₙ ok Rₙₜ.Jₕ H~H′ ▸s       = _ , Rₜ.Jₕ , H~H′
      bisim₂ₙ ok Rₙₜ.Kₕ H~H′ ▸s       = _ , Rₜ.Kₕ , H~H′
      bisim₂ₙ ok Rₙₜ.[]-congₕ H~H′ ▸s = _ , Rₜ.[]-congₕ , H~H′

    opaque

      bisim₂ᵥ : ⟨ H , t , E , S ⟩ Rₙₜ.⇒ᵥ ⟨ H′ , t′ , E′ , S′ ⟩
              → ⟨ H , t , E , S ⟩ Rₜ.⇒ᵥ ⟨ H′ , t′ , E′ , S′ ⟩
      bisim₂ᵥ Rₙₜ.lamₕ    = Rₜ.lamₕ
      bisim₂ᵥ Rₙₜ.prodˢₕ₁ = Rₜ.prodˢₕ₁
      bisim₂ᵥ Rₙₜ.prodˢₕ₂ = Rₜ.prodˢₕ₂
      bisim₂ᵥ Rₙₜ.prodʷₕ  = Rₜ.prodʷₕ
      bisim₂ᵥ Rₙₜ.zeroₕ   = Rₜ.zeroₕ
      bisim₂ᵥ Rₙₜ.sucₕ    = Rₜ.sucₕ
      bisim₂ᵥ Rₙₜ.starʷₕ  = Rₜ.starʷₕ
      bisim₂ᵥ Rₙₜ.rflₕⱼ   = Rₜ.rflₕⱼ
      bisim₂ᵥ Rₙₜ.rflₕₖ   = Rₜ.rflₕₖ
      bisim₂ᵥ Rₙₜ.rflₕₑ   = Rₜ.rflₕₑ

    opaque

      bisim₂ₛ : ⟨ H , t , E , S ⟩ Rₙₜ.⇒ₛ ⟨ H′ , t′ , E′ , S′ ⟩
              → ⟨ H , t , E , S ⟩ Rₜ.⇒ₛ ⟨ H′ , t′ , E′ , S′ ⟩
      bisim₂ₛ (Rₙₜ.sucₕ x) = Rₜ.sucₕ x
      bisim₂ₛ (Rₙₜ.numₕ x) = Rₜ.numₕ x


    opaque

      bisim₂ : Supports-subtraction
             → ⟨ H , t , E , S ⟩ Rₙₜ.⇒ ⟨ H′ , t′ , E′ , S′ ⟩
             → H ~ʰ H″
             → γ ⨾ δ ⨾ η ▸ ⟨ H″ , t , E , S ⟩
             → ∃ λ H‴ → ⟨ H″ , t , E , S ⟩ Rₜ.⇒ ⟨ H‴ , t′ , E′ , S′ ⟩ × H′ ~ʰ H‴
      bisim₂ ok (Rₙₜ.⇒ₙ d) H~H′ ▸s =
        case bisim₂ₙ ok d H~H′ ▸s of λ
          (_ , d′ , H′~H″) →
        _ , Rₜ.⇒ₙ d′ , H′~H″
      bisim₂ ok (Rₙₜ.⇒ᵥ d) H~H′ ▸s =
        case ~ʰ-⇒ᵥ d H~H′ of λ
          (_ , d′ , H′~H″) →
        _ , Rₜ.⇒ᵥ bisim₂ᵥ d′ , H′~H″
      bisim₂ ok (Rₙₜ.⇒ₛ d) H~H′ ▸s =
        case ~ʰ-⇒ₛ d H~H′ of λ
          (_ , d′ , H′~H″) →
        _ , Rₜ.⇒ₛ bisim₂ₛ d′ , H′~H″

  -- The proof that the closure of the non-tracking reduction implies
  -- the closure of the tracking reduction has some extra assumptions

  module _ (UA : UsageAssumptions UR) where

    open UsageAssumptions UA
    open import Heap.Usage.Reduction UA type-variant optsₜ

    bisim₂* : ⟨ H , t , E , S ⟩ Rₙₜ.⇒* ⟨ H′ , t′ , E′ , S′ ⟩
            → H ~ʰ H″
            → γ ⨾ δ ⨾ η ▸ ⟨ H″ , t , E , S ⟩
            → ∃ λ H‴ → ⟨ H″ , t , E , S ⟩ Rₜ.⇒* ⟨ H‴ , t′ , E′ , S′ ⟩ × H′ ~ʰ H‴
    bisim₂* Rₙₜ.id H~H′ ▸s =
      _ , Rₜ.id , H~H′
    bisim₂* (x Rₙₜ.⇨ d) H~H′ ▸s =
      case bisim₂ subtraction-ok x H~H′ ▸s of λ
        (_ , x′ , H~H″) →
      case ▸-⇒ ▸s x′ of λ
        (_ , _ , _ , ▸s′) →
      case bisim₂* d H~H″ ▸s′ of λ
        (_ , d′ , H~H‴) →
      _ , (x′ Rₜ.⇨ d′) , H~H‴

-- Bisimilarity between the call-by-name reduction and the
-- heap reduction without evaluation to numerals.

module _ where

  private
    optsₜ optsₙₜ : Options
    optsₜ = tracking-and-ℕ-fullred-if false
    optsₙₜ = not-tracking-and-ℕ-fullred-if false
    module Rₜ = R optsₜ
    module Rₙₜ = R optsₙₜ

  open RP optsₙₜ
  open import Heap.Typed TR false
  open import Heap.Typed.Properties TR false
  open import Heap.Typed.Reduction TR optsₙₜ

  -- Most of the bisimilarity properties are proven under
  -- the assumption that the nr function is factoring and
  -- either the weak unit type is disallowed or that it
  -- does not have eta equality turned on

  module _ (no-Unitʷ⊎no-η : ¬ Unitʷ-allowed ⊎ ¬ Unitʷ-η)
           ⦃ _ : Has-nr M semiring-with-meet ⦄
           ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
           where

    opaque

      bisim₃ : Γ ⊢ₛ s ∷ A → s Rₙₜ.⇒ s′
             → ε ⊢ norm s ⇒* norm s′ ∷ A
      bisim₃ (_ , _ , ⊢t , ⊢S) (Rₙₜ.⇒ₙ d) =
        subst (ε ⊢ _ ⇒*_∷ _) (⇒ₙ-norm-≡ d) (id (⊢⦅⦆ ⊢S ⊢t))
      bisim₃ ⊢s (Rₙₜ.⇒ᵥ d) =
        redMany (⇒ᵥ→⇒ no-Unitʷ⊎no-η ⊢s d) --(⇒ᵥ→⇒ ⊢s d)

    opaque

      bisim₃* : Γ ⊢ₛ s ∷ A → s Rₙₜ.⇒* s′
              → ε ⊢ norm s ⇒* norm s′ ∷ A
      bisim₃* (_ , ⊢H , ⊢t , ⊢S) Rₙₜ.id = id (⊢⦅⦆ ⊢S ⊢t)
      bisim₃* ⊢s (x Rₙₜ.⇨ d) =
        case ⊢ₛ-⇒ ⊢s x of λ
          (_ , _ , _ , ⊢s′) →
        (bisim₃ ⊢s x) ⇨∷* (bisim₃* ⊢s′ d)

    opaque

      bisim₄ᵥ : ε ⊢ ⦅ S ⦆ (wk E t) [ H ]ₕ ⇒ u ∷ A
              → Val t
              → Γ ⊢ₛ ⟨ H , t , E , S ⟩ ∷ B
              → ∃₃ λ m n (s : State m n) → ⟨ H , t , E , S ⟩ Rₙₜ.⇒ᵥ s × u PE.≡ norm s
      bisim₄ᵥ {S = ε} {E} {H} d v ⊢s =
        ⊥-elim (whnfRedTerm d (Val→Whnf (substVal (toSubstₕ H) (wkVal E v)) .proj₁))
      bisim₄ᵥ {S = e ∙ S} d v ⊢s =
        case ⊢Val-⇒ᵥ ⊢s v of λ
          (_ , _ , _ , d′) →
        _ , _ , _ , d′ , whrDetTerm d (⇒ᵥ→⇒ no-Unitʷ⊎no-η ⊢s d′)

    opaque

      Normal→Val : Γ ⊢ₛ ⟨ H , t , E , S ⟩ ∷ A → Normal t → Val t
      Normal→Val _ (val v) = v
      Normal→Val (_ , ⊢H , ⊢t , _) emptyrecₙ =
        case inversion-emptyrec ⊢t of λ
          (_ , ⊢t , _) →
        ⊥-elim (¬Empty ⊢t)

    opaque

      bisim₄ : ε ⊢ ⦅ S ⦆ (wk E t) [ H ]ₕ ⇒ u ∷ A
             → Γ ⊢ₛ ⟨ H , t , E , S ⟩ ∷ B
             → ∃₃ λ m n (s : State m n) → ⟨ H , t , E , S ⟩ Rₙₜ.⇒* s × u PE.≡ norm s
      bisim₄ {S} {E} {t} {H} d ⊢s =
        case normalize H t E S of λ
          (_ , _ , _ , _ , n , d′) →
        case ⊢ₛ-⇒ₙ* ⊢s d′ of λ
          (_ , _ , _ , ⊢s′) →
        case bisim₄ᵥ (PE.subst (λ x → ε ⊢ x ⇒ _ ∷ _) (⇒ₙ*-norm-≡ d′) d)
               (Normal→Val ⊢s′ n) ⊢s′ of λ
          (_ , _ , s′ , d″ , u≡) →
        _ , _ , s′ , ((⇒ₙ* d′) ⇨* ((Rₙₜ.⇒ᵥ d″) Rₙₜ.⇨ Rₙₜ.id)) , u≡

    opaque

      bisim₄* : ε ⊢ ⦅ S ⦆ (wk E t) [ H ]ₕ ⇒* u ∷ A
             → Γ ⊢ₛ ⟨ H , t , E , S ⟩ ∷ B
             → ∃₃ λ m n (s : State m n) → ⟨ H , t , E , S ⟩ Rₙₜ.⇒* s × u PE.≡ norm s
      bisim₄* (id x) ⊢s =
        _ , _ , _ , Rₙₜ.id , PE.refl
      bisim₄* (x ⇨ d) ⊢s =
        case bisim₄ x ⊢s of λ {
          (_ , _ , _ , x′ , PE.refl) →
        case ⊢ₛ-⇒* ⊢s x′ of λ
          (_ , _ , _ , ⊢s′) →
        case bisim₄* d ⊢s′ of λ
          (_ , _ , _ , d′ , u≡) →
        _ , _ , _ , x′ ⇨* d′ , u≡ }

    opaque

      bisim₅* : Γ ⊢ₛ s ∷ A → s Rₜ.⇒* s′
              → ε ⊢ norm s ⇒* norm s′ ∷ A
      bisim₅* {s′ = ⟨ _ , t , E , S ⟩} ⊢s d =
        case bisim₁* false d of λ
          (_ , d′ , H~H′) →
        PE.subst (λ x → ε ⊢ _ ⇒* ⦅ S ⦆ (wk E t) [ x ] ∷ _)
          (PE.sym (~ʰ-subst H~H′)) (bisim₃* ⊢s d′)

  -- The proof that the closure of the call-by-name reduction
  -- corresponds to the closure of the tracking reduction has
  -- some extra assumptions.

  module _ (UA : UsageAssumptions UR)
           (no-Unitʷ⊎no-η : ¬ Unitʷ-allowed ⊎ ¬ Unitʷ-η) where

    open UsageAssumptions UA

    opaque

      bisim₆* : ε ⊢ ⦅ S ⦆ (wk E t) [ H ]ₕ ⇒* u ∷ A
              → Γ ⊢ₛ ⟨ H , t , E , S ⟩ ∷ B
              → γ ⨾ δ ⨾ η ▸ ⟨ H , t , E , S ⟩
              → ∃₃ λ m n (s : State m n) → ⟨ H , t , E , S ⟩ Rₜ.⇒* s × u PE.≡ norm s
      bisim₆* d ⊢s ▸s =
        case bisim₄* no-Unitʷ⊎no-η d ⊢s of λ
          (_ , _ , ⟨ H , t , E , S ⟩ , d′ , u≡) →
        case bisim₂* false UA d′ ~ʰ-refl ▸s of λ
          (_ , d″ , H~H′) →
        _ , _ , _ , d″
          , PE.trans u≡ (cong (λ x → ⦅ S ⦆ (wk E t) [ x ]) (~ʰ-subst H~H′))

-- Bisimilarity between redutions with and without reuction to numerals
-- (with or without resource tracking).

module _ ⦃ _ : Has-nr M semiring-with-meet ⦄
         ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
         (track-resources : Bool) where

  private
    optsₛ optsₙₛ : Options
    optsₛ = ℕ-Fullred-and-tracking-if track-resources
    optsₙₛ = ¬ℕ-Fullred-and-tracking-if track-resources
    module Rₛ = R optsₛ
    module Rₙₛ = R optsₙₛ

  bisim₇ₙ : s Rₙₛ.⇒ₙ s′ → s Rₛ.⇒ₙ s′
  bisim₇ₙ (Rₙₛ.varₕ d) = Rₛ.varₕ d
  bisim₇ₙ (Rₙₛ.varₕ′ d) = Rₛ.varₕ′ d
  bisim₇ₙ Rₙₛ.appₕ = Rₛ.appₕ
  bisim₇ₙ Rₙₛ.fstₕ = Rₛ.fstₕ
  bisim₇ₙ Rₙₛ.sndₕ = Rₛ.sndₕ
  bisim₇ₙ Rₙₛ.prodrecₕ = Rₛ.prodrecₕ
  bisim₇ₙ Rₙₛ.natrecₕ = Rₛ.natrecₕ
  bisim₇ₙ Rₙₛ.unitrecₕ = Rₛ.unitrecₕ
  bisim₇ₙ Rₙₛ.Jₕ = Rₛ.Jₕ
  bisim₇ₙ Rₙₛ.Kₕ = Rₛ.Kₕ
  bisim₇ₙ Rₙₛ.[]-congₕ = Rₛ.[]-congₕ

  bisim₇ᵥ : s Rₙₛ.⇒ᵥ s′ → s Rₛ.⇒ᵥ s′
  bisim₇ᵥ Rₙₛ.lamₕ = Rₛ.lamₕ
  bisim₇ᵥ Rₙₛ.prodˢₕ₁ = Rₛ.prodˢₕ₁
  bisim₇ᵥ Rₙₛ.prodˢₕ₂ = Rₛ.prodˢₕ₂
  bisim₇ᵥ Rₙₛ.prodʷₕ = Rₛ.prodʷₕ
  bisim₇ᵥ Rₙₛ.zeroₕ = Rₛ.zeroₕ
  bisim₇ᵥ Rₙₛ.sucₕ = Rₛ.sucₕ
  bisim₇ᵥ Rₙₛ.starʷₕ = Rₛ.starʷₕ
  bisim₇ᵥ Rₙₛ.rflₕⱼ = Rₛ.rflₕⱼ
  bisim₇ᵥ Rₙₛ.rflₕₖ = Rₛ.rflₕₖ
  bisim₇ᵥ Rₙₛ.rflₕₑ = Rₛ.rflₕₑ

  bisim₇ : s Rₙₛ.⇒ s′ → s Rₛ.⇒ s′
  bisim₇ (Rₙₛ.⇒ₙ d) = Rₛ.⇒ₙ (bisim₇ₙ d)
  bisim₇ (Rₙₛ.⇒ᵥ d) = Rₛ.⇒ᵥ (bisim₇ᵥ d)

  bisim₇* : s Rₙₛ.⇒* s′ → s Rₛ.⇒* s′
  bisim₇* Rₙₛ.id = Rₛ.id
  bisim₇* (x Rₙₛ.⇨ d) = (bisim₇ x) Rₛ.⇨ (bisim₇* d)
