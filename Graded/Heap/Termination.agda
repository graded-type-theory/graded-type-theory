------------------------------------------------------------------------
-- Termination properties of the reduction relation
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Graded.Restrictions
open import Definition.Typed.Restrictions
open import Tools.Bool
open import Tools.Sum hiding (sym; id)
import Graded.Heap.Bisimilarity

module Graded.Heap.Termination
  {a} {M : Set a} {𝕄 : Modality M}
  (UR : Usage-restrictions 𝕄)
  (TR : Type-restrictions 𝕄)
  (erased-heap : Bool)
  (open Graded.Heap.Bisimilarity UR TR erased-heap)
  (open Type-restrictions TR)
  (As : Assumptions)
  (erased-assumption :
    T (not erased-heap) ⊎ No-erased-matches′ 𝕄 type-variant UR)
  where

open Usage-restrictions UR
open Assumptions As
open Modality 𝕄

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE hiding (sym)

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Properties.Neutral M type-variant
open import Definition.Typed TR
open import Definition.Typed.Consequences.Canonicity TR
open import Definition.Typed.Consequences.Reduction TR
open import Definition.Typed.Properties TR

open import Graded.Context 𝕄 hiding (_⟨_⟩)
open import Graded.Usage 𝕄 UR
open import Graded.Mode 𝕄

open import Graded.Heap.Normalization type-variant UR
open import Graded.Heap.Untyped type-variant UR
open import Graded.Heap.Untyped.Properties type-variant UR
open import Graded.Heap.Typed UR TR
open import Graded.Heap.Typed.Properties UR TR
open import Graded.Heap.Typed.Reduction UR TR
open import Graded.Heap.Usage type-variant UR erased-heap
open import Graded.Heap.Usage.Properties type-variant UR erased-heap
open import Graded.Heap.Usage.Reduction type-variant UR erased-heap Unitʷ-η→
open import Graded.Heap.Reduction type-variant UR
open import Graded.Heap.Reduction.Properties type-variant UR

private variable
  t u A B : Term _
  γ δ η : Conₘ _
  H : Heap _ _
  ρ : Wk _ _
  S : Stack _
  e : Elim _
  Γ Δ : Con Term _
  s : State _ _ _
  m : Mode
  k : Nat

opaque

  -- Well-typed and well-resourced terms evaluate to values with empty stacks
  -- corresponding to terms in Whnf.

  whBisim : (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent Δ)
          → suc∉ (State.stack s)
          → Δ ⊢ ⦅ s ⦆ ↘ u ∷ A
          → Δ ⨾ Γ ⊢ s ∷ B
          → γ ⨾ δ ⨾ η ▸ s
          → ∃₅ λ m n H t (ρ : Wk m n)
          → s ⇾* ⟨ H , t , ρ , ε ⟩ × wk ρ t [ H ]ₕ ≡ u × Value t
  whBisim {s = s@record{}} consistent suc∉S (d , w) ⊢s ▸s =
    case ⊢⇒*→⇾* As {s = s} d suc∉S ⊢s ▸s of λ {
      (_ , _ , s′ , d₁ , refl) →
    case ⊢ₛ-⇾* ⊢s d₁ of λ
      (_ , _ , _ , ⊢s′) →
    case ▸-⇾* ▸s d₁ of λ
      (_ , _ , _ , ▸s′) →
    case suc∉-⇾* suc∉S d₁ of λ
      suc∉S′ →
    case ▸normalize As s′ ▸s′ of λ
      (_ , s″ , n , dₑ) →
    case ⊢ₛ-⇾ₑ* ⊢s′ dₑ of λ
      ⊢s″ →
    case ▸-⇾ₑ* ▸s′ dₑ of λ
      (_ , _ , _ , ▸s″) →
    case suc∉-⇾ₑ* suc∉S′ dₑ of λ
      suc∉S″ →
    case n of λ where
      (val v) →
        case lemma w v ⊢s″ suc∉S″ (⇾ₑ*-⦅⦆-≡ dₑ) of λ {
          refl →
        _ , _ , _ , _ , _ , d₁ ⇨* ⇾ₑ* dₑ
          , PE.sym (⇾ₑ*-⦅⦆-≡ dₑ) , v }
      (var d′) →
        case erased-assumption of λ where
          (inj₁ ¬eh) → ⊥-elim (¬erased-heap→¬↦● ⦃ neh = ¬eh ⦄ (▸s″ .proj₁) d′)
          (inj₂ nem) →
            case ▸s● subtraction-ok d′ ▸s″ of λ
              (∣S∣≡𝟘 , _) →
            case ▸∣S∣≢𝟘 nem (▸s″ .proj₂ .proj₂ .proj₁) of λ where
              (inj₁ ∣S∣≢𝟘) →
                ⊥-elim (∣S∣≢𝟘 ∣S∣≡𝟘)
              (inj₂ (er∈S , ok)) →
                ⊥-elim (⊢emptyrec₀∉S {ρ = State.env s″} (consistent ok) ⊢s″ er∈S) }
    where
    lemma : ∀ {n} {t : Term n} {H ρ S}
          → Whnf u → Value t → Δ ⨾ Γ ⊢ ⟨ H , t , ρ , S ⟩ ∷ A
          → suc∉ S → u PE.≡ ⦅ ⟨ H , t , ρ , S ⟩ ⦆ → S PE.≡ ε
    lemma {S = ε} w n _ _ u≡ = refl
    lemma {t} {H} {ρ} {S = e ∙ S} w v (_ , _ , _ , ⊢S) suc∉S u≡ =
      case whnf-subst {t = ⦅ e ∙ S ⦆ˢ (wk ρ t)} (subst Whnf u≡ w) of λ
        w′ →
      case subst Neutral (wk≡subst ρ t) (⊢whnf⦅⦆ˢ′ suc∉S ⊢S w′) of λ
        n′ →
      ⊥-elim (Value→¬Neutral v (neutral-subst n′))

opaque

  -- A variant of the above, starting with the initial state

  whBisim-initial : {Δ : Con Term k}
                  → k ≡ 0 ⊎ ((Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent Δ) × T erased-heap)
                  → Δ ⊢ t ↘ u ∷ A → 𝟘ᶜ ▸ t
                  → ∃₅ λ m n H u′ (ρ : Wk m n)
                  → initial t ⇾* ⟨ H , u′ , ρ , ε ⟩ × wk ρ u′ [ H ]ₕ ≡ u × Value u′
  whBisim-initial {k} {Δ} as d ▸t =
    whBisim consistent ε
      (subst (_ ⊢_↘ _ ∷ _)
        (PE.sym (PE.trans (erasedHeap-subst (wk id _)) (wk-id _))) d)
      (⊢initial (redFirst*Term (proj₁ d)))
      (▸initial k≡0⊎erased-heap ▸t)
    where
    consistent : Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent Δ
    consistent ok =
      case as of λ where
        (inj₂ (c , _)) → c ok
        (inj₁ refl) →
          case singleton Δ of λ where
            (ε , refl) → λ _ → ¬Empty
    k≡0⊎erased-heap : k ≡ 0 ⊎ T erased-heap
    k≡0⊎erased-heap =
      case as of λ where
        (inj₁ x) → inj₁ x
        (inj₂ (_ , x)) → inj₂ x

opaque

  -- Well-typed and well-resourced terms evaluate to values with empty stacks
  -- corresponding to terms in Whnf.

  whRed : {Δ : Con Term k}
        → (k ≡ 0 ⊎ (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent Δ) × T erased-heap)
        → Δ ⊢ t ∷ A → 𝟘ᶜ ▸ t
        → ∃₅ λ m n H u (ρ : Wk m n)
          → initial t ⇾* ⟨ H , u , ρ , ε ⟩ × Value u × Whnf ⦅ ⟨ H , u , ρ , ε ⟩ ⦆
  whRed as ⊢t ▸t =
    case whNormTerm ⊢t of λ
      (u , w , d) →
    case whBisim-initial as (redₜ d , w) ▸t of λ {
      (_ , _ , _ , _ , _ , d′ , refl , v) →
    _ , _ , _ , _ , _ , d′ , v , w }
