
open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions
open import Tools.Relation
open import Tools.Bool
import Heap.Bisimilarity

module Heap.Termination
  {a} {M : Set a} {𝕄 : Modality M}
  (UR : Usage-restrictions 𝕄)
  (TR : Type-restrictions 𝕄)
  (erased-heap : Bool)
  (open Heap.Bisimilarity UR TR erased-heap)
  (As : Assumptions)
  where

open Type-restrictions TR
open Assumptions As

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE hiding (sym)
open import Tools.Sum hiding (sym; id)

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Properties.Neutral M type-variant
open import Definition.Typed TR
open import Definition.Typed.Consequences.Canonicity TR
open import Definition.Typed.Consequences.DerivedRules TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Consequences.Syntactic TR
open import Definition.Typed.Consequences.Reduction TR
open import Definition.Typed.Properties TR

open import Graded.Context 𝕄 hiding (_⟨_⟩)
open import Graded.Usage 𝕄 UR
open import Graded.Mode 𝕄

open import Heap.Normalization type-variant UR
open import Heap.Options
open import Heap.Untyped type-variant UR
open import Heap.Untyped.Properties type-variant UR
open import Heap.Typed UR TR false
open import Heap.Typed.Properties UR TR false
import Heap.Typed.Reduction UR TR (tracking-and-ℕ-fullred-if false) as RTₜ
import Heap.Typed.Reduction UR TR (not-tracking-and-ℕ-fullred-if false) as RTₙₜ
open import Heap.Usage type-variant UR erased-heap
open import Heap.Usage.Properties type-variant UR erased-heap
open import Heap.Usage.Reduction type-variant UR erased-heap (tracking-and-ℕ-fullred-if false) Unitʷ-η→
open import Heap.Reduction type-variant UR (tracking-and-ℕ-fullred-if false)
import Heap.Reduction.Properties type-variant UR (tracking-and-ℕ-fullred-if false) as RPₜ
import Heap.Reduction.Properties type-variant UR (not-tracking-and-ℕ-fullred-if false) as RPₙₜ

private variable
  t u A B : Term _
  γ δ η : Conₘ _
  H : Heap _ _
  E : Env _ _
  S : Stack _
  e : Elim _
  Γ Δ : Con Term _
  s : State _ _ _
  m : Mode
  k : Nat

opaque

  -- Well-typed and well-resourced terms evaluate to values with empty stacks
  -- corresponding to terms in Whnf.

  whBisim : Consistent Δ
          → Δ ⊢ ⦅ s ⦆ ↘ u ∷ A
          → Δ ⨾ Γ ⊢ s ∷ B
          → γ ⨾ δ ⨾ η ▸[ m ] s
          → ∃₂ λ m n → ∃₃ λ H t (E : Env m n)
          → s ⇒* ⟨ H , t , E , ε ⟩ × wk E t [ H ]ₕ ≡ u × Value t
  whBisim {s = ⟨ H , t , E , S ⟩} consistent (d , w) ⊢s ▸s =
    case bisim₆* As consistent d ⊢s ▸s of λ {
      (_ , _ , ⟨ H , t′ , E , S ⟩ , d₁ , refl) →
    case normalize H t′ E S of λ
      (_ , t″ , E′ , S′ , n , dₙ) →
    case RPₙₜ.⇒ₙ*-⦅⦆-≡ dₙ of λ {
      t′≡t″ →
    case ▸-⇒* ▸s d₁ of λ
      (_ , _ , _ , _ , ▸s′) →
    case RTₜ.⊢ₛ-⇒* ⊢s d₁ of λ
      (_ , _ , _ , ⊢s′) →
    case bisim₂* false As (RPₙₜ.⇒ₙ* dₙ) ~ʰ-refl ▸s′ of λ
      (H′ , dₜ , H~H′) →
    case RTₙₜ.⊢ₛ-⇒* ⊢s′ (RPₙₜ.⇒ₙ* dₙ) of λ
      (_ , _ , _ , ⊢s″@(B , _ , ⊢t″ , ⊢S′)) →
    case n of λ where
      (val v) →
        case lemma {H = H} {S = S′} w v ⊢s″ (RPₙₜ.⇒ₙ*-⦅⦆-≡ dₙ) of λ {
          refl →
        _ , _ , _ , t″ , E′ , d₁ RPₜ.⇨* dₜ
          , PE.sym (PE.trans t′≡t″ (cong (wk E′ t″ [_]) (~ʰ-subst H~H′))) , v}
      (var ¬d) →
        case ▸-⇒* ▸s′ dₜ of λ
          (_ , _ , _ , _ , ▸s″) →
        case ▸s→y↦ subtraction-ok erased-assumption ▸s″ of λ
          (_ , _ , _ , d) →
        ⊥-elim (¬d (~ʰ-lookup (~ʰ-sym H~H′) (↦[]→↦ d)))
      emptyrecₙ →
        case inversion-emptyrec ⊢t″ of λ
          (_ , ⊢∷Empty , _) →
        ⊥-elim (consistent _ ⊢∷Empty)
      (unitrec-ηₙ {u = u} η) →
        case inversion-unitrec ⊢t″ of λ
          (⊢A , ⊢t , ⊢u , B≡) →
        case ⊢⦅⦆ˢ-subst {u = wk E′ u} ⊢S′ (conv (unitrec-β-η-⇒ ⊢A ⊢t ⊢u η) (sym B≡)) of λ
          d′ →
        ⊥-elim (whnfRedTerm d′ (subst Whnf t′≡t″ w)) }}
    where
    lemma : ∀ {n} {t : Term n} {H E S}
          → Whnf u → Value t → Δ ⨾ Γ ⊢ ⟨ H , t , E , S ⟩ ∷ A
          → u PE.≡ ⦅ ⟨ H , t , E , S ⟩ ⦆ → S PE.≡ ε
    lemma {S = ε} w n _ u≡ = refl
    lemma {t} {H} {E} {S = e ∙ S} w v (_ , _ , _ , ⊢S) u≡ =
      case Value→Whnf v of λ
        (_ , ¬n) →
      ⊥-elim (¬whnf-subst {σ = toSubstₕ H}
        (⊢whnf⦅⦆ˢ {t = wk E t} ⊢S
          λ n → ¬n (neutral-subst (subst Neutral (wk≡subst E t) n)))
        (subst Whnf u≡ w))

opaque

  -- A variant of the above, starting with the initial state

  whBisim-initial : {Δ : Con Term k}
                  → k ≡ 0 ⊎ (Consistent Δ × T erased-heap)
                  → Δ ⊢ t ↘ u ∷ A → 𝟘ᶜ ▸ t
                  → ∃₂ λ m n → ∃₃ λ H u′ (E : Env m n)
                  → initial t ⇒* ⟨ H , u′ , E , ε ⟩ × wk E u′ [ H ]ₕ ≡ u × Value u′
  whBisim-initial {k} {Δ} as d ▸t =
    whBisim consistent
      (subst (_ ⊢_↘ _ ∷ _)
        (PE.sym (PE.trans (erasedHeap-subst (wk id _)) (wk-id _))) d)
      (⊢initial (redFirst*Term (proj₁ d)))
      (▸initial k≡0⊎erased-heap ▸t)
    where
    consistent : Consistent Δ
    consistent =
      case as of λ where
        (inj₂ (c , _)) → c
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
        → (k ≡ 0 ⊎ Consistent Δ × T erased-heap)
        → Δ ⊢ t ∷ A → 𝟘ᶜ ▸ t
        → ∃₂ λ m n → ∃₃ λ H u′ (E : Env m n)
          → initial t ⇒* ⟨ H , u′ , E , ε ⟩ × Value u′ × Whnf ⦅ ⟨ H , u′ , E , ε ⟩ ⦆
  whRed as ⊢t ▸t =
    case whNormTerm ⊢t of λ
      (u , w , d) →
    case whBisim-initial as (redₜ d , w) ▸t of λ {
      (_ , _ , _ , _ , _ , d′ , refl , v) →
    _ , _ , _ , _ , _ , d′ , v , w }
