------------------------------------------------------------------------
-- Bisimilarity properties between the different semantics of the
-- abstract machine and the weak head reduction.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions

module Graded.Heap.Bisimilarity
  {a} {M : Set a} {𝕄 : Modality M}
  (UR : Usage-restrictions 𝕄)
  (TR : Type-restrictions 𝕄)
  where

open Modality 𝕄 hiding (has-nr)
open Type-restrictions TR
open Usage-restrictions UR

open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Product
open import Tools.PropositionalEquality as PE
open import Tools.Sum
open import Tools.Unit

open import Graded.Heap.Untyped type-variant UR
open import Graded.Heap.Untyped.Properties type-variant UR
open import Graded.Heap.Usage type-variant UR
open import Graded.Heap.Usage.Properties type-variant UR
open import Graded.Heap.Usage.Reduction type-variant UR
open import Graded.Heap.Normalization type-variant UR
open import Graded.Heap.Reduction type-variant UR
open import Graded.Heap.Reduction.Properties type-variant UR
open import Graded.Heap.Typed UR TR
open import Graded.Heap.Typed.Inversion UR TR
open import Graded.Heap.Typed.Properties UR TR
open import Graded.Heap.Typed.Reduction UR TR

open import Definition.Untyped M
open import Definition.Untyped.Inversion M
open import Definition.Untyped.Neutral M type-variant

open import Definition.Typed TR
open import Definition.Typed.Properties TR hiding (_⇨*_)

open import Graded.Context 𝕄 hiding (_⟨_⟩)
open import Graded.Mode 𝕄
open import Graded.Modality.Properties.Subtraction semiring-with-meet

private variable
  s s′ : State _ _ _
  H H′ H″ : Heap _ _
  t t′ u u′ v w A B : Term _
  ρ ρ′ : Wk _ _
  S S′ : Stack _
  γ δ η : Conₘ _
  Γ Δ : Con Term _
  l : Universe-level
  p q : M

-- Assumptions that are used to prove some bisimilarity properties
-- as well as some properties elsewhere that follow from them

record Assumptions : Set a where
  field
    subtraction-ok : Supports-subtraction
    Unitʷ-η→ : ∀ {p q} → Unitʷ-η → Unitrec-allowed 𝟙ᵐ p q → p ≤ 𝟘
    instance
      has-well-behaved-zero : Has-well-behaved-zero M semiring-with-meet
      nr-avail : Nr-available

  instance
    has-nr : Has-nr M semiring-with-meet
    has-nr = Modality.has-nr 𝕄 nr-avail

  field instance
    has-factoring-nr : Has-factoring-nr M semiring-with-meet

------------------------------------------------------------------------
-- Bisimilarity between the tracking and non-tracking semantics.

-- The first direction is proven only under the assumption
-- that the modality has a factoring nr function.

module _
  ⦃ _ : Has-nr M semiring-with-meet ⦄
  ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
  where

  opaque

    ⇾ₑ→⇢ₑ : s ⇾ₑ ⟨ H , t , ρ , S ⟩
          → ∃ λ H′ → s ⇢ₑ ⟨ H′ , t , ρ , S ⟩ × H ~ʰ H′
    ⇾ₑ→⇢ₑ (var d) = _ , var (↦[]→↦ d) , ~ʰ-sym (update-~ʰ d)
    ⇾ₑ→⇢ₑ (⇒ₑ d) = _ , ⇒ₑ d , ~ʰ-refl

  opaque

    ⇾→⇢ : s ⇾ ⟨ H , t , ρ , S ⟩
        → ∃ λ H′ → s ⇢ ⟨ H′ , t , ρ , S ⟩ × H ~ʰ H′
    ⇾→⇢ (⇾ₑ d) =
      let _ , d′ , H~H′ = ⇾ₑ→⇢ₑ d
      in  _ , ⇢ₑ d′ , H~H′
    ⇾→⇢ (⇒ᵥ d) = _ , ⇒ᵥ d , ~ʰ-refl

  opaque

    ⇾*→⇢* : s ⇾* ⟨ H , t , ρ , S ⟩
          → ∃ λ H′ → s ⇢* ⟨ H′ , t , ρ , S ⟩ × H ~ʰ H′
    ⇾*→⇢* id = _ , id , ~ʰ-refl
    ⇾*→⇢* (_⇨_ {s₂ = record{}} x d) =
      let _ , x′ , H~H′ = ⇾→⇢ x
          _ , d′ , H~H″ = ⇾*→⇢* d
          _ , d″ , H~H‴ = ~ʰ-⇢* d′ H~H′
      in  _ , x′ ⇨ d″ , ~ʰ-trans H~H″ H~H‴

-- The other direction is proven under some additional assumptions

module _ (As : Assumptions) where

  open Assumptions As

  opaque

    ⇢ₑ→⇾ₑ : H ~ʰ H″
          → ▸ ⟨ H″ , t , ρ , S ⟩
          → ⟨ H , t , ρ , S ⟩ ⇢ₑ ⟨ H′ , t′ , ρ′ , S′ ⟩
          → ∃ λ H‴ → ⟨ H″ , t , ρ , S ⟩ ⇾ₑ ⟨ H‴ , t′ , ρ′ , S′ ⟩ × H′ ~ʰ H‴
    ⇢ₑ→⇾ₑ H~H″ ▸s (var d) =
      let H , d′ = ▸↦→↦[] subtraction-ok (~ʰ-lookup H~H″ d) ▸s
      in  _ , var d′ , ~ʰ-trans H~H″ (update-~ʰ d′)
    ⇢ₑ→⇾ₑ H~H″ _ (⇒ₑ d) =
      _ , ⇒ₑ ~ʰ-⇒ₑ d
        , subst (_~ʰ _) (⇒ₑ-Heap≡ d) H~H″

  opaque

    ⇢ₑ*→⇾ₑ* : H ~ʰ H″
            → ▸ ⟨ H″ , t , ρ , S ⟩
            → ⟨ H , t , ρ , S ⟩ ⇢ₑ* ⟨ H′ , t′ , ρ′ , S′ ⟩
            → ∃ λ H‴ → ⟨ H″ , t , ρ , S ⟩ ⇾ₑ* ⟨ H‴ , t′ , ρ′ , S′ ⟩ × H′ ~ʰ H‴
    ⇢ₑ*→⇾ₑ* H~H″ ▸s id = _ , id , H~H″
    ⇢ₑ*→⇾ₑ* H~H″ ▸s (_⇨_ {s′ = record{}} x d) =
      let _ , x′ , H′~H‴ = ⇢ₑ→⇾ₑ H~H″ ▸s x
          ▸s′ = ▸-⇾ₑ Unitʷ-η→ ▸s x′
          _ , d′ , H′~H⁗ = ⇢ₑ*→⇾ₑ* H′~H‴ ▸s′ d
      in  _ , x′ ⇨ d′ , H′~H⁗

  opaque

    ⇢→⇾ : H ~ʰ H″
        → ▸ ⟨ H″ , t , ρ , S ⟩
        → ⟨ H , t , ρ , S ⟩ ⇢ ⟨ H′ , t′ , ρ′ , S′ ⟩
        → ∃ λ H‴ → ⟨ H″ , t , ρ , S ⟩ ⇾ ⟨ H‴ , t′ , ρ′ , S′ ⟩ × H′ ~ʰ H‴
    ⇢→⇾ H~H″ ▸s (⇢ₑ d) =
      let _ , d′ , H~H′ = ⇢ₑ→⇾ₑ H~H″ ▸s d
      in  _ , ⇾ₑ d′ , H~H′
    ⇢→⇾ H~H″ ▸s (⇒ᵥ d) =
      let _ , d′ , H′~H‴ = ~ʰ-⇒ᵥ d H~H″
      in  _ , ⇒ᵥ d′ , H′~H‴

  opaque

    ⇢*→⇾* : H ~ʰ H″
          → ▸ ⟨ H″ , t , ρ , S ⟩
          → ⟨ H , t , ρ , S ⟩ ⇢* ⟨ H′ , t′ , ρ′ , S′ ⟩
          → ∃ λ H‴ → ⟨ H″ , t , ρ , S ⟩ ⇾* ⟨ H‴ , t′ , ρ′ , S′ ⟩ × H′ ~ʰ H‴
    ⇢*→⇾* H~H″ ▸s id = _ , id , H~H″
    ⇢*→⇾* H~H″ ▸s (_⇨_ {s₂ = record{}} x d) =
      let _ , x′ , H′~H‴ = ⇢→⇾ H~H″ ▸s x
          ▸s′ = ▸-⇾ Unitʷ-η→ ▸s x′
          _ , d′ , H′~H⁗ = ⇢*→⇾* H′~H‴ ▸s′ d
      in  _ , x′ ⇨ d′ , H′~H⁗

  opaque

    -- Normalization for the tracking semantics

    ▸normalize :
      ∀ {k m n} (s : State k m n) → No-namesₛ′ s → ▸ s →
      ∃₂ λ n′ (s′ : State _ _ n′) → Normal s′ × s ⇾ₑ* s′
    ▸normalize s@record{} s-nn ▸s =
      let (_ , record{} , n , d) = normalizeₛ s s-nn
          _ , d′ , H~H′ = ⇢ₑ*→⇾ₑ* ~ʰ-refl ▸s d
      in  _ , _ , ~ʰ-Normal H~H′ n , d′

------------------------------------------------------------------------
-- Bisimilarity between the weak head call-by-name reduction and
-- the abstract machine (with tracking).

-- Most properties are proven only under the assumption that the
-- modality has a factoring nr function (and that equality reflection
-- is not allowed or the context is empty).

module _
  ⦃ _ : Has-nr M semiring-with-meet ⦄
  ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
  ⦃ ok : No-equality-reflection or-empty Δ ⦄
  where

  opaque

    ⇾→⊢⇒ : Δ ⊢ₛ s ∷ A → s ⇾ s′ → ε » Δ ⊢ ⦅ s ⦆ ⇒* ⦅ s′ ⦆ ∷ A
    ⇾→⊢⇒ {s} ⊢s (⇾ₑ d) =
      subst (_ ⊢ _ ⇒*_∷ _) (⇾ₑ-⦅⦆-≡ d) (id (⊢⦅⦆ {s = s} ⊢s))
    ⇾→⊢⇒ ⊢s (⇒ᵥ d) =
      redMany (⇒ᵥ→⇒ ⊢s d)

  opaque

    ⇾*→⊢⇒* : Δ ⊢ₛ s ∷ A → s ⇾* s′ → ε » Δ ⊢ ⦅ s ⦆ ⇒* ⦅ s′ ⦆ ∷ A
    ⇾*→⊢⇒* {s} ⊢s id = id (⊢⦅⦆ {s = s} ⊢s)
    ⇾*→⊢⇒* {s = record{}} ⊢s (_⇨_ {s₂ = record{}} x d) =
      ⇾→⊢⇒ ⊢s x ⇨∷* ⇾*→⊢⇒* (⊢ₛ-⇾ ⊢s x) d


  opaque

    ⊢⇒→⇒ᵥ : ε » Δ ⊢ ⦅ s ⦆ ⇒ u ∷ A
          → Normal s
          → Δ ⊢ₛ s ∷ B
          → ∃₃ λ m n (s′ : State _ m n) → s ⇒ᵥ s′ × u PE.≡ ⦅ s′ ⦆
    ⊢⇒→⇒ᵥ {s = ⟨ H , t , ρ , ε ⟩} d (val x) ⊢s =
      case Value→Whnf (substValue (toSubstₕ H) (wkValue ρ x)) of λ where
          (inj₁ w) → ⊥-elim (whnfRedTerm d w)
          (inj₂ (_ , _ , _ , _ , _ , _ , ≡ur , η)) →
            case subst-unitrec {t = wk ρ t} ≡ur of λ where
              (inj₁ (_ , ≡x)) → case subst Value ≡x (wkValue ρ x) of λ ()
              (inj₂ (_ , _ , _ , ≡ur′ , refl , refl , refl)) →
                case wk-unitrec ≡ur′ of λ {
                  (_ , _ , _ , refl , refl , refl , refl) →
                _ , _ , _ , unitrec-ηₕ η , lemma η d}
        where
        lemma :
          Unitʷ-η → ε » Δ ⊢ (unitrec l p q A u v) ⇒ w ∷ B → w PE.≡ v
        lemma η (conv d x) = lemma η d
        lemma η (unitrec-subst _ _ _ _ no-η) = ⊥-elim (no-η η)
        lemma η (unitrec-β _ _ _ no-η) = ⊥-elim (no-η η)
        lemma η (unitrec-β-η _ _ _ _ _) = refl
    ⊢⇒→⇒ᵥ {s = ⟨ H , t , ρ , e ∙ S ⟩} d (val v) ⊢s =
      case ⊢Value-⇒ᵥ ⊢s v of λ
        (_ , _ , _ , d′) →
      _ , _ , _ , d′ , whrDetTerm d (⇒ᵥ→⇒ ⊢s d′)
    ⊢⇒→⇒ᵥ d (var d′) ⊢s =
      let _ , _ , _ , _ , ⊢S = ⊢ₛ-inv ⊢s
      in  ⊥-elim $ neRedTerm {V = Lift _ ⊤} d $ NeutralAt→Neutral $
          toSubstₕ-NeutralAt d′ $ ⊢⦅⦆ˢ-NeutralAt ⊢S (var _)

module _ (As : Assumptions) where

  open Assumptions As

  opaque

    ⊢⇒→⇾* :
      ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
      ε » Δ ⊢ ⦅ s ⦆ ⇒ u ∷ A →
      Δ ⊢ₛ s ∷ B →
      ▸ s →
      ∃₃ λ m n (s′ : State _ m n) → s ⇾* s′ × u PE.≡ ⦅ s′ ⦆
    ⊢⇒→⇾* {s} d ⊢s ▸s =
      let _ , s′ , n , d′ = ▸normalize As s (⊢ₛ→No-namesₛ′ ⊢s) ▸s
          d″ = PE.subst (_ ⊢_⇒ _ ∷ _) (⇾ₑ*-⦅⦆-≡ d′) d
          ⊢s′ = ⊢ₛ-⇾ₑ* ⊢s d′
          _ , _ , s″ , d‴ , u≡ = ⊢⇒→⇒ᵥ d″ n ⊢s′
      in  _ , _ , s″ , ⇾ₑ* d′ ⇨* ⇒ᵥ d‴ ⇨ id , u≡

  opaque

    ⊢⇒*→⇾* :
      ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
      ε » Δ ⊢ ⦅ s ⦆ ⇒* u ∷ A →
      Δ ⊢ₛ s ∷ B →
      ▸ s →
      ∃₃ λ m n (s′ : State _ m n) → s ⇾* s′ × u PE.≡ ⦅ s′ ⦆
    ⊢⇒*→⇾* (id x) ⊢s ▸s =
      _ , _ , _ , id , refl
    ⊢⇒*→⇾* {s} (x ⇨ d) ⊢s ▸s =
      case ⊢⇒→⇾* {s = s} x ⊢s ▸s of λ {
        (_ , _ , _ , x′ , refl) →
      case ⊢ₛ-⇾* ⊢s x′ of λ
        ⊢s′ →
      case ▸-⇾* Unitʷ-η→ ▸s x′ of λ
        ▸s′ →
      case ⊢⇒*→⇾* d ⊢s′ ▸s′ of λ
        (_ , _ , s′ , d′ , u≡) →
      _ , _ , s′ , x′ ⇨* d′ , u≡ }
