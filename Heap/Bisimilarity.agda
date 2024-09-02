open import Graded.Modality
open import Graded.Usage.Restrictions
open import Tools.Bool
open import Definition.Typed.Restrictions

module Heap.Bisimilarity
  {a} {M : Set a} {𝕄 : Modality M}
  (UR : Usage-restrictions 𝕄)
  (TR : Type-restrictions 𝕄)
  (erased-heap : Bool)
  where

open Modality 𝕄 hiding (has-nr)
open Type-restrictions TR
open Usage-restrictions UR

open import Tools.Empty
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum hiding (id)

open import Heap.Options
open import Heap.Untyped type-variant UR
open import Heap.Untyped.Properties type-variant UR
open import Heap.Usage type-variant UR erased-heap
open import Heap.Usage.Properties type-variant UR erased-heap
open import Heap.Normalization type-variant UR
import Heap.Reduction type-variant UR as R
import Heap.Reduction.Properties type-variant UR as RP

open import Definition.Untyped M
open import Definition.Untyped.Inversion M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties.Neutral M type-variant

open import Definition.Typed TR
open import Definition.Typed.Properties TR
open import Definition.Typed.RedSteps TR hiding (_⇨*_)
open import Definition.Typed.Consequences.Canonicity TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Consequences.Reduction TR

open import Graded.Context 𝕄 hiding (_⟨_⟩)
open import Graded.Mode 𝕄
open import Graded.Modality.Properties.Subtraction semiring-with-meet
open import Graded.Restrictions 𝕄

private variable
  s s′ : State _ _ _
  H H′ H″ : Heap _ _
  t t′ u u′ v w A B : Term _
  ρ ρ′ : Wk _ _
  S S′ : Stack _
  γ δ η : Conₘ _
  Γ Δ : Con Term _
  m : Mode
  p q : M

-- Assumptions that are used to prove some bisimilarity properties
-- as well as some properties elsewhere that follow from them

record Assumptions : Set a where
  field
    subtraction-ok : Supports-subtraction
    erased-assumption : T (not erased-heap) ⊎ No-erased-matches′ type-variant UR
    Unitʷ-η→ : ∀ {p q} → Unitʷ-η → Unitrec-allowed 𝟙ᵐ p q → p ≤ 𝟘
    instance
      has-well-behaved-zero : Has-well-behaved-zero M semiring-with-meet
      nr-avail : Nr-available

  instance
    has-nr : Has-nr M semiring-with-meet
    has-nr = Modality.has-nr 𝕄 nr-avail

  field instance
    has-factoring-nr : Has-factoring-nr M semiring-with-meet

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

      bisim₁ₙ : s Rₜ.⇒ₙ ⟨ H , t , ρ , S ⟩
              → ∃ λ H′ → s Rₙₜ.⇒ₙ ⟨ H′ , t , ρ , S ⟩ × H ~ʰ H′
      bisim₁ₙ (Rₜ.varₕ d)        = _ , Rₙₜ.varₕ′ (↦[]→↦ d) , ~ʰ-sym (update-~ʰ d)
      bisim₁ₙ Rₜ.appₕ            = _ , Rₙₜ.appₕ , ~ʰ-refl
      bisim₁ₙ Rₜ.fstₕ            = _ , Rₙₜ.fstₕ , ~ʰ-refl
      bisim₁ₙ Rₜ.sndₕ            = _ , Rₙₜ.sndₕ , ~ʰ-refl
      bisim₁ₙ Rₜ.prodrecₕ        = _ , Rₙₜ.prodrecₕ , ~ʰ-refl
      bisim₁ₙ Rₜ.natrecₕ         = _ , Rₙₜ.natrecₕ , ~ʰ-refl
      bisim₁ₙ (Rₜ.unitrecₕ no-η) = _ , Rₙₜ.unitrecₕ no-η , ~ʰ-refl
      bisim₁ₙ Rₜ.emptyrecₕ       = _ , Rₙₜ.emptyrecₕ , ~ʰ-refl
      bisim₁ₙ Rₜ.Jₕ              = _ , Rₙₜ.Jₕ , ~ʰ-refl
      bisim₁ₙ Rₜ.Kₕ              = _ , Rₙₜ.Kₕ , ~ʰ-refl
      bisim₁ₙ Rₜ.[]-congₕ        = _ , Rₙₜ.[]-congₕ , ~ʰ-refl

    opaque

      bisim₁ᵥ : s Rₜ.⇒ᵥ ⟨ H , t , ρ , S ⟩
              → s Rₙₜ.⇒ᵥ ⟨ H , t , ρ , S ⟩
      bisim₁ᵥ Rₜ.lamₕ           = Rₙₜ.lamₕ
      bisim₁ᵥ Rₜ.prodˢₕ₁        = Rₙₜ.prodˢₕ₁
      bisim₁ᵥ Rₜ.prodˢₕ₂        = Rₙₜ.prodˢₕ₂
      bisim₁ᵥ Rₜ.prodʷₕ         = Rₙₜ.prodʷₕ
      bisim₁ᵥ Rₜ.zeroₕ          = Rₙₜ.zeroₕ
      bisim₁ᵥ Rₜ.sucₕ           = Rₙₜ.sucₕ
      bisim₁ᵥ Rₜ.starʷₕ         = Rₙₜ.starʷₕ
      bisim₁ᵥ (Rₜ.unitrec-ηₕ η) = Rₙₜ.unitrec-ηₕ η
      bisim₁ᵥ Rₜ.rflₕⱼ          = Rₙₜ.rflₕⱼ
      bisim₁ᵥ Rₜ.rflₕₖ          = Rₙₜ.rflₕₖ
      bisim₁ᵥ Rₜ.rflₕₑ          = Rₙₜ.rflₕₑ

    opaque

      bisim₁ₛ : s Rₜ.⇒ₛ ⟨ H , t , ρ , S ⟩
              → s Rₙₜ.⇒ₛ ⟨ H , t , ρ , S ⟩
      bisim₁ₛ (Rₜ.sucₕ x) = Rₙₜ.sucₕ x
      bisim₁ₛ (Rₜ.numₕ x) = Rₙₜ.numₕ x

    opaque

      bisim₁ : s Rₜ.⇒ ⟨ H , t , ρ , S ⟩
             → ∃ λ H′ → s Rₙₜ.⇒ ⟨ H′ , t , ρ , S ⟩ × H ~ʰ H′
      bisim₁ (Rₜ.⇒ₙ d) =
        case bisim₁ₙ d of λ
          (_ , d′ , H~H′) →
        _ , Rₙₜ.⇒ₙ d′ , H~H′
      bisim₁ (Rₜ.⇒ᵥ d) =
        _ , Rₙₜ.⇒ᵥ (bisim₁ᵥ d) , ~ʰ-refl
      bisim₁ (Rₜ.⇒ₛ d) =
        _ , Rₙₜ.⇒ₛ (bisim₁ₛ d) , ~ʰ-refl

    opaque

      bisim₁* : s Rₜ.⇒* ⟨ H , t , ρ , S ⟩
              → ∃ λ H′ → s Rₙₜ.⇒* ⟨ H′ , t , ρ , S ⟩ × H ~ʰ H′
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

      bisim₂ᵥ : ⟨ H , t , ρ , S ⟩ Rₙₜ.⇒ᵥ ⟨ H′ , t′ , ρ′ , S′ ⟩
              → ⟨ H , t , ρ , S ⟩ Rₜ.⇒ᵥ ⟨ H′ , t′ , ρ′ , S′ ⟩
      bisim₂ᵥ Rₙₜ.lamₕ            = Rₜ.lamₕ
      bisim₂ᵥ Rₙₜ.prodˢₕ₁         = Rₜ.prodˢₕ₁
      bisim₂ᵥ Rₙₜ.prodˢₕ₂         = Rₜ.prodˢₕ₂
      bisim₂ᵥ Rₙₜ.prodʷₕ          = Rₜ.prodʷₕ
      bisim₂ᵥ Rₙₜ.zeroₕ           = Rₜ.zeroₕ
      bisim₂ᵥ Rₙₜ.sucₕ            = Rₜ.sucₕ
      bisim₂ᵥ Rₙₜ.starʷₕ          = Rₜ.starʷₕ
      bisim₂ᵥ (Rₙₜ.unitrec-ηₕ η)  = Rₜ.unitrec-ηₕ η
      bisim₂ᵥ Rₙₜ.rflₕⱼ           = Rₜ.rflₕⱼ
      bisim₂ᵥ Rₙₜ.rflₕₖ           = Rₜ.rflₕₖ
      bisim₂ᵥ Rₙₜ.rflₕₑ           = Rₜ.rflₕₑ

    opaque

      bisim₂ₛ : ⟨ H , t , ρ , S ⟩ Rₙₜ.⇒ₛ ⟨ H′ , t′ , ρ′ , S′ ⟩
              → ⟨ H , t , ρ , S ⟩ Rₜ.⇒ₛ ⟨ H′ , t′ , ρ′ , S′ ⟩
      bisim₂ₛ (Rₙₜ.sucₕ x) = Rₜ.sucₕ x
      bisim₂ₛ (Rₙₜ.numₕ x) = Rₜ.numₕ x

  -- The proof of the other direction uses some additional assumptions

  module _ (As : Assumptions) where

    open Assumptions As

    open import Heap.Usage.Reduction type-variant UR erased-heap optsₜ Unitʷ-η→

    opaque

      bisim₂ₙ : ⟨ H , t , ρ , S ⟩ Rₙₜ.⇒ₙ ⟨ H′ , t′ , ρ′ , S′ ⟩
              → H ~ʰ H″
              → γ ⨾ δ ⨾ η ▸[ m ] ⟨ H″ , t , ρ , S ⟩
              → ∃ λ H‴ → ⟨ H″ , t , ρ , S ⟩ Rₜ.⇒ₙ ⟨ H‴ , t′ , ρ′ , S′ ⟩ × H′ ~ʰ H‴
      bisim₂ₙ (Rₙₜ.varₕ′ d) H~H′ ▸s =
        case ▸↦→↦[] subtraction-ok (~ʰ-lookup H~H′ d) ▸s .proj₂ of λ
          d′ →
        _ , Rₜ.varₕ d′ , ~ʰ-trans H~H′ (update-~ʰ d′)
      bisim₂ₙ Rₙₜ.appₕ H~H′ _            = _ , Rₜ.appₕ , H~H′
      bisim₂ₙ Rₙₜ.fstₕ H~H′ _            = _ , Rₜ.fstₕ , H~H′
      bisim₂ₙ Rₙₜ.sndₕ H~H′ _            = _ , Rₜ.sndₕ , H~H′
      bisim₂ₙ Rₙₜ.prodrecₕ H~H′ _        = _ , Rₜ.prodrecₕ , H~H′
      bisim₂ₙ Rₙₜ.natrecₕ H~H′ _         = _ , Rₜ.natrecₕ , H~H′
      bisim₂ₙ (Rₙₜ.unitrecₕ no-η) H~H′ _ = _ , Rₜ.unitrecₕ no-η , H~H′
      bisim₂ₙ Rₙₜ.emptyrecₕ H~H′ _       = _ , Rₜ.emptyrecₕ , H~H′
      bisim₂ₙ Rₙₜ.Jₕ H~H′ _              = _ , Rₜ.Jₕ , H~H′
      bisim₂ₙ Rₙₜ.Kₕ H~H′ _              = _ , Rₜ.Kₕ , H~H′
      bisim₂ₙ Rₙₜ.[]-congₕ H~H′ _        = _ , Rₜ.[]-congₕ , H~H′

    opaque

      bisim₂ : ⟨ H , t , ρ , S ⟩ Rₙₜ.⇒ ⟨ H′ , t′ , ρ′ , S′ ⟩
             → H ~ʰ H″
             → γ ⨾ δ ⨾ η ▸[ m ] ⟨ H″ , t , ρ , S ⟩
             → ∃ λ H‴ → ⟨ H″ , t , ρ , S ⟩ Rₜ.⇒ ⟨ H‴ , t′ , ρ′ , S′ ⟩ × H′ ~ʰ H‴
      bisim₂ (Rₙₜ.⇒ₙ d) H~H′ ▸s =
        case bisim₂ₙ d H~H′ ▸s of λ
          (_ , d′ , H′~H″) →
        _ , Rₜ.⇒ₙ d′ , H′~H″
      bisim₂ (Rₙₜ.⇒ᵥ d) H~H′ ▸s =
        case ~ʰ-⇒ᵥ d H~H′ of λ
          (_ , d′ , H′~H″) →
        _ , Rₜ.⇒ᵥ bisim₂ᵥ d′ , H′~H″
      bisim₂ (Rₙₜ.⇒ₛ d) H~H′ ▸s =
        case ~ʰ-⇒ₛ d H~H′ of λ
          d′ →
        case ⇒ₛ-Heap≡ d of λ {
          PE.refl →
        _ , Rₜ.⇒ₛ bisim₂ₛ d′ , H~H′}

    opaque

      bisim₂* : ⟨ H , t , ρ , S ⟩ Rₙₜ.⇒* ⟨ H′ , t′ , ρ′ , S′ ⟩
              → H ~ʰ H″
              → γ ⨾ δ ⨾ η ▸[ m ] ⟨ H″ , t , ρ , S ⟩
              → ∃ λ H‴ → ⟨ H″ , t , ρ , S ⟩ Rₜ.⇒* ⟨ H‴ , t′ , ρ′ , S′ ⟩ × H′ ~ʰ H‴
      bisim₂* Rₙₜ.id H~H′ ▸s =
        _ , Rₜ.id , H~H′
      bisim₂* (x Rₙₜ.⇨ d) H~H′ ▸s =
        case bisim₂ x H~H′ ▸s of λ
          (_ , x′ , H~H″) →
        case ▸-⇒ ▸s x′ of λ
          (_ , _ , _ , _ , ▸s′) →
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
  open import Heap.Typed UR TR false
  open import Heap.Typed.Properties UR TR false
  open import Heap.Typed.Reduction UR TR optsₙₜ

  -- Most of the bisimilarity properties are proven under
  -- the assumption that the nr function is factoring.

  module _ ⦃ _ : Has-nr M semiring-with-meet ⦄
           ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
           where

    opaque

      bisim₃ : Δ ⨾ Γ ⊢ s ∷ A → s Rₙₜ.⇒ s′
             → Δ ⊢ ⦅ s ⦆ ⇒* ⦅ s′ ⦆ ∷ A
      bisim₃ (_ , _ , ⊢t , ⊢S) (Rₙₜ.⇒ₙ d) =
        subst (_ ⊢ _ ⇒*_∷ _) (⇒ₙ-⦅⦆-≡ d) (id (⊢⦅⦆ˢ ⊢S ⊢t))
      bisim₃ ⊢s (Rₙₜ.⇒ᵥ d) =
        redMany (⇒ᵥ→⇒ ⊢s d)

    opaque

      bisim₃* : Δ ⨾ Γ ⊢ s ∷ A → s Rₙₜ.⇒* s′
              → Δ ⊢ ⦅ s ⦆ ⇒* ⦅ s′ ⦆ ∷ A
      bisim₃* (_ , ⊢H , ⊢t , ⊢S) Rₙₜ.id = id (⊢⦅⦆ˢ ⊢S ⊢t)
      bisim₃* ⊢s (x Rₙₜ.⇨ d) =
        case ⊢ₛ-⇒ ⊢s x of λ
          (_ , _ , _ , ⊢s′) →
        (bisim₃ ⊢s x) ⇨∷* (bisim₃* ⊢s′ d)

    opaque

      bisim₄ᵥ : Δ ⊢ ⦅ s ⦆ ⇒ u ∷ A
              → Normal s
              → Δ ⨾ Γ ⊢ s ∷ B
              → ∃₃ λ m n (s′ : State _ m n) → s Rₙₜ.⇒ᵥ s′ × u PE.≡ ⦅ s′ ⦆
      bisim₄ᵥ {Δ} {s = ⟨ H , t , ρ , ε ⟩} d (val x) ⊢s =
        case Value→Whnf (substValue (toSubstₕ H) (wkValue ρ x)) of λ where
          (inj₁ w) → ⊥-elim (whnfRedTerm d w)
          (inj₂ (_ , _ , _ , _ , _ , ≡ur , η)) →
            case subst-unitrec {t = wk ρ t} ≡ur of λ where
              (inj₁ (_ , ≡x)) → case subst Value ≡x (wkValue ρ x) of λ ()
              (inj₂ (_ , _ , _ , ≡ur′ , refl , refl , refl)) →
                case wk-unitrec ≡ur′ of λ {
                  (_ , _ , _ , refl , refl , refl , refl) →
                _ , _ , _ , Rₙₜ.unitrec-ηₕ η , lemma η d}
        where
        lemma : Unitʷ-η → Δ ⊢ unitrec p q A u v ⇒ w ∷ B → w PE.≡ v
        lemma η (conv d x) = lemma η d
        lemma η (unitrec-subst _ _ _ _ no-η) = ⊥-elim (no-η η)
        lemma η (unitrec-β _ _ _ no-η) = ⊥-elim (no-η η)
        lemma η (unitrec-β-η _ _ _ _ _) = refl

      bisim₄ᵥ {s = ⟨ _ , _ , _ , e ∙ S ⟩} d (val v) ⊢s =
        case ⊢Value-⇒ᵥ ⊢s v of λ
          (_ , _ , _ , d′) →
        _ , _ , _ , d′ , whrDetTerm d (⇒ᵥ→⇒ ⊢s d′)
      bisim₄ᵥ d (var d′) (_ , _ , _ , ⊢S) =
        ⊥-elim (neRedTerm d (NeutralAt→Neutral (toSubstₕ-NeutralAt d′ (⊢⦅⦆ˢ-NeutralAt ⊢S var))))

    opaque

      bisim₄ : Δ ⊢ ⦅ s ⦆ ⇒ u ∷ A
             → Δ ⨾ Γ ⊢ s ∷ B
             → ∃₃ λ m n (s′ : State _ m n) → s Rₙₜ.⇒* s′ × u PE.≡ ⦅ s′ ⦆
      bisim₄ {s} d ⊢s =
        case normalizeₛ s of λ
          (_ , _ , n , d′) →
        case ⊢ₛ-⇒ₙ* ⊢s d′ of λ
          ⊢s′ →
        case bisim₄ᵥ (PE.subst (λ x → _ ⊢ x ⇒ _ ∷ _) (⇒ₙ*-⦅⦆-≡ d′) d) n ⊢s′ of λ
          (_ , _ , s′ , d″ , u≡) →
        _ , _ , s′ , (⇒ₙ* d′ ⇨* (Rₙₜ.⇒ᵥ d″) Rₙₜ.⇨ Rₙₜ.id) , u≡

    opaque

      bisim₄* : Δ ⊢ ⦅ s ⦆ ⇒* u ∷ A
              → Δ ⨾ Γ ⊢ s ∷ B
              → ∃₃ λ m n (s′ : State _ m n) → s Rₙₜ.⇒* s′ × u PE.≡ ⦅ s′ ⦆
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

      bisim₅* : Δ ⨾ Γ ⊢ s ∷ A → s Rₜ.⇒* s′
              → Δ ⊢ ⦅ s ⦆ ⇒* ⦅ s′ ⦆ ∷ A
      bisim₅* {s′ = ⟨ _ , t , ρ , S ⟩} ⊢s d =
        case bisim₁* false d of λ
          (_ , d′ , H~H′) →
        PE.subst (λ x → _ ⊢ _ ⇒* ⦅ S ⦆ˢ (wk ρ t) [ x ] ∷ _)
          (PE.sym (~ʰ-subst H~H′)) (bisim₃* ⊢s d′)

  -- The proof that the closure of the call-by-name reduction
  -- corresponds to the closure of the tracking reduction has
  -- some extra assumptions.

  module _ (As : Assumptions) where

    open Assumptions As

    opaque

      bisim₆* : Δ ⊢ ⦅ s ⦆ ⇒* u ∷ A
              → Δ ⨾ Γ ⊢ s ∷ B
              → γ ⨾ δ ⨾ η ▸[ m ] s
              → ∃₃ λ m n (s′ : State _ m n) → s Rₜ.⇒* s′ × u PE.≡ ⦅ s′ ⦆
      bisim₆* d ⊢s ▸s =
        case bisim₄* d ⊢s of λ
          (_ , _ , ⟨ H , t , ρ , S ⟩ , d′ , u≡) →
        case bisim₂* false As d′ ~ʰ-refl ▸s of λ
          (_ , d″ , H~H′) →
        _ , _ , _ , d″
          , PE.trans u≡ (cong (λ x → ⦅ S ⦆ˢ (wk ρ t) [ x ]) (~ʰ-subst H~H′))

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

  opaque

    bisim₇ₙ : s Rₙₛ.⇒ₙ s′ → s Rₛ.⇒ₙ s′
    bisim₇ₙ (Rₙₛ.varₕ d) = Rₛ.varₕ d
    bisim₇ₙ (Rₙₛ.varₕ′ d) = Rₛ.varₕ′ d
    bisim₇ₙ Rₙₛ.appₕ = Rₛ.appₕ
    bisim₇ₙ Rₙₛ.fstₕ = Rₛ.fstₕ
    bisim₇ₙ Rₙₛ.sndₕ = Rₛ.sndₕ
    bisim₇ₙ Rₙₛ.prodrecₕ = Rₛ.prodrecₕ
    bisim₇ₙ Rₙₛ.natrecₕ = Rₛ.natrecₕ
    bisim₇ₙ (Rₙₛ.unitrecₕ no-η) = Rₛ.unitrecₕ no-η
    bisim₇ₙ Rₙₛ.emptyrecₕ = Rₛ.emptyrecₕ
    bisim₇ₙ Rₙₛ.Jₕ = Rₛ.Jₕ
    bisim₇ₙ Rₙₛ.Kₕ = Rₛ.Kₕ
    bisim₇ₙ Rₙₛ.[]-congₕ = Rₛ.[]-congₕ

  opaque

    bisim₇ᵥ : s Rₙₛ.⇒ᵥ s′ → s Rₛ.⇒ᵥ s′
    bisim₇ᵥ Rₙₛ.lamₕ = Rₛ.lamₕ
    bisim₇ᵥ Rₙₛ.prodˢₕ₁ = Rₛ.prodˢₕ₁
    bisim₇ᵥ Rₙₛ.prodˢₕ₂ = Rₛ.prodˢₕ₂
    bisim₇ᵥ Rₙₛ.prodʷₕ = Rₛ.prodʷₕ
    bisim₇ᵥ Rₙₛ.zeroₕ = Rₛ.zeroₕ
    bisim₇ᵥ Rₙₛ.sucₕ = Rₛ.sucₕ
    bisim₇ᵥ Rₙₛ.starʷₕ = Rₛ.starʷₕ
    bisim₇ᵥ (Rₙₛ.unitrec-ηₕ η) = Rₛ.unitrec-ηₕ η
    bisim₇ᵥ Rₙₛ.rflₕⱼ = Rₛ.rflₕⱼ
    bisim₇ᵥ Rₙₛ.rflₕₖ = Rₛ.rflₕₖ
    bisim₇ᵥ Rₙₛ.rflₕₑ = Rₛ.rflₕₑ

  opaque

    bisim₇ : s Rₙₛ.⇒ s′ → s Rₛ.⇒ s′
    bisim₇ (Rₙₛ.⇒ₙ d) = Rₛ.⇒ₙ (bisim₇ₙ d)
    bisim₇ (Rₙₛ.⇒ᵥ d) = Rₛ.⇒ᵥ (bisim₇ᵥ d)

  opaque

    bisim₇* : s Rₙₛ.⇒* s′ → s Rₛ.⇒* s′
    bisim₇* Rₙₛ.id = Rₛ.id
    bisim₇* (x Rₙₛ.⇨ d) = (bisim₇ x) Rₛ.⇨ (bisim₇* d)
