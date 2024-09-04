
open import Graded.Modality
open import Graded.Usage.Restrictions
open import Heap.Usage.Assumptions
open import Definition.Typed.Restrictions
open import Tools.Relation
open import Tools.Sum hiding (id)

module Heap.Termination
  {a} {M : Set a} {𝕄 : Modality M}
  {UR : Usage-restrictions 𝕄}
  (UA : UsageAssumptions UR)
  (TR : Type-restrictions 𝕄)
  (open Type-restrictions TR)
  (no-Unitʷ⊎no-η : ¬ Unitʷ-allowed ⊎ ¬ Unitʷ-η)
  where

open UsageAssumptions UA

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality as PE

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Properties.Neutral M type-variant
open import Definition.Typed TR
open import Definition.Typed.Consequences.Canonicity TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Consequences.Syntactic TR
open import Definition.Typed.Consequences.Reduction TR
open import Definition.Typed.Properties TR

open import Graded.Context 𝕄 hiding (_⟨_⟩)
open import Graded.Usage 𝕄 UR

open import Heap.Bisimilarity UR TR
open import Heap.Normalization 𝕄 type-variant
open import Heap.Options
open import Heap.Untyped 𝕄
open import Heap.Untyped.Properties 𝕄 type-variant
open import Heap.Typed TR false
open import Heap.Typed.Properties TR false
import Heap.Typed.Reduction TR (tracking-and-ℕ-fullred-if false) as RTₜ
import Heap.Typed.Reduction TR (not-tracking-and-ℕ-fullred-if false) as RTₙₜ
open import Heap.Usage 𝕄 UR
open import Heap.Usage.Properties UR type-variant
open import Heap.Usage.Reduction UA type-variant (tracking-and-ℕ-fullred-if false)
open import Heap.Reduction 𝕄 (tracking-and-ℕ-fullred-if false)
import Heap.Reduction.Properties 𝕄 type-variant (tracking-and-ℕ-fullred-if false) as RPₜ
import Heap.Reduction.Properties 𝕄 type-variant (not-tracking-and-ℕ-fullred-if false) as RPₙₜ

private variable
  t u A B : Term _
  γ δ η : Conₘ _
  H : Heap _
  E : Env _ _
  S : Stack _
  e : Elim _
  Γ : Con Term _
  s : State _ _

opaque

  -- Well-typed and well-resourced terms evaluate to values with empty stacks
  -- corresponding to terms in Whnf.

  whBisim : ε ⊢ norm s ↘ u ∷ A
          → Γ ⊢ₛ s ∷ B
          → γ ⨾ δ ⨾ η ▸ s
          → ∃₂ λ m n → ∃₃ λ H t (E : Env m n)
          → s ⇒* ⟨ H , t , E , ε ⟩ × wk E t [ H ]ₕ ≡ u × Val t
  whBisim {s = ⟨ H , t , E , S ⟩} (d , w) ⊢s ▸s =
    case bisim₆* UA no-Unitʷ⊎no-η {S = S} {E = E} {t} d ⊢s ▸s of λ
      (_ , _ , ⟨ H , t′ , E , S ⟩ , d₁ , u≡) →
    case normalize H t′ E S of λ
      (_ , t″ , E′ , S′ , n , dₙ) →
    case ▸-⇒* ▸s d₁ of λ
      (_ , _ , _ , ▸s′) →
    case RTₜ.⊢ₛ-⇒* ⊢s d₁ of λ
      (_ , _ , _ , ⊢s′) →
    case bisim₂* false UA (RPₙₜ.⇒ₙ* dₙ) ~ʰ-refl ▸s′ of λ
      (H′ , dₜ , H~H′) →
    case RTₙₜ.⊢ₛ-⇒* ⊢s′ (RPₙₜ.⇒ₙ* dₙ) of λ
      (_ , _ , _ , ⊢s″) →
    case lemma {H = H} {S = S′} w n ⊢s″
           (PE.trans u≡ (RPₙₜ.⇒ₙ*-norm-≡ dₙ)) of λ {
      PE.refl →
    case n of λ {
      emptyrecₙ →
    case inversion-emptyrec
           (subst (ε ⊢_∷ _) (PE.trans u≡ (RPₙₜ.⇒ₙ*-norm-≡ dₙ))
           (syntacticRedTerm d .proj₂ .proj₂)) of λ
      (_ , ⊢∷Empty , _) →
    ⊥-elim (¬Empty ⊢∷Empty) ;
      (val v) →
    _ , _ , _ , t″ , E′ , (d₁ RPₜ.⇨* dₜ)
      , PE.sym (PE.trans u≡ (PE.trans
          (RPₙₜ.⇒ₙ*-norm-≡ dₙ) (cong (wk E′ t″ [_]) (~ʰ-subst H~H′))))
      , v }}
    where
    lemma : ∀ {n} {t : Term n} {H E S}
          → Whnf u → Normal t → Γ ⊢ₛ ⟨ H , t , E , S ⟩ ∷ A
          → u PE.≡ norm ⟨ H , t , E , S ⟩ → S PE.≡ ε
    lemma {S = ε} w n _ u≡ = refl
    lemma {t} {H} {E} {S = e ∙ S} w (val v) (_ , _ , _ , ⊢S) u≡ =
      case Val→Whnf v of λ
        (_ , ¬n) →
      ⊥-elim (¬whnf-subst {σ = toSubstₕ H}
        (⊢whnf⦅⦆ {t = wk E t} ⊢S
          λ n → ¬n (neutral-subst (subst Neutral (wk≡subst E t) n)))
        (subst Whnf u≡ w))
    lemma {S = e ∙ S} w emptyrecₙ (_ , ⊢H , ⊢t , ⊢S) u≡ =
      case inversion-emptyrec ⊢t of λ
        (_ , ⊢∷Empty , _) →
      ⊥-elim (¬Empty ⊢∷Empty)

opaque

  -- A variant of the above, starting with the initial state

  whBisim-initial : ε ⊢ t ↘ u ∷ A → ε ▸ t
                  → ∃₂ λ m n → ∃₃ λ H u′ (E : Env m n)
                  → initial t ⇒* ⟨ H , u′ , E , ε ⟩ × wk E u′ [ H ]ₕ ≡ u × Val u′
  whBisim-initial d ▸t =
    whBisim
      (subst (ε ⊢_↘ _ ∷ _)
        (PE.sym (PE.trans (subst-id (wk id _)) (wk-id _))) d)
      (⊢initial (redFirst*Term (proj₁ d)))
      (▸initial ▸t)

opaque

  -- Well-typed and well-resourced terms evaluate to values with empty stacks
  -- corresponding to terms in Whnf.

  whRed : ε ⊢ t ∷ A → ε ▸ t
        → ∃₂ λ m n → ∃₃ λ H u′ (E : Env m n)
          → initial t ⇒* ⟨ H , u′ , E , ε ⟩ × Val u′ × Whnf (norm ⟨ H , u′ , E , ε ⟩)
  whRed ⊢t ▸t =
    case whNormTerm ⊢t of λ
      (u , w , d) →
    case whBisim-initial (redₜ d , w) ▸t of λ {
      (_ , _ , _ , _ , _ , d′ , refl , v) →
    _ , _ , _ , _ , _ , d′ , v , w }
