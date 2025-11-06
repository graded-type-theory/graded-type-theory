------------------------------------------------------------------------
-- Properties of the heap reduction relation.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Variant
open import Tools.Relation
open import Graded.Usage.Restrictions.Natrec

module Graded.Heap.Reduction.Properties
  {a} {M : Set a} {𝕄 : Modality M}
  (type-variant : Type-variant)
  (UR : Usage-restrictions 𝕄)
  (open Usage-restrictions UR)
  (factoring-nr :
    ⦃ has-nr : Nr-available ⦄ →
    Is-factoring-nr M (Natrec-mode-Has-nr 𝕄 has-nr))
  where

open Type-variant type-variant
open Modality 𝕄

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+; 2+; Nat-set)
open import Tools.PropositionalEquality
open import Tools.Product
open import Tools.Sum

open import Definition.Untyped M

open import Graded.Heap.Untyped type-variant UR factoring-nr
open import Graded.Heap.Untyped.Properties type-variant UR factoring-nr
open import Graded.Heap.Reduction type-variant UR factoring-nr
open import Graded.Heap.Reduction.Inversion type-variant UR factoring-nr
open import Graded.Modality.Properties.Subtraction semiring-with-meet

private variable
  m n m′ n′ m″ n″ k : Nat
  t t′ u A : Term _
  H H′ H″ H‴ : Heap _ _
  ρ ρ′ ρ″ : Wk _ _
  e : Elim _
  S S′ S″ : Stack _
  p p′ q r r′ : M
  s s′ s″ : State _ _ _
  c : Entryₘ _ _
  x x′ : Fin _

opaque
  infixr 28 _⇨*_
  -- Concatenation of reduction

  _⇨*_ : s ⇾* s′ → s′ ⇾* s″ → s ⇾* s″
  id ⇨* d′ = d′
  (x ⇨ d) ⇨* d′ = x ⇨ (d ⇨* d′)

opaque

  -- Concatenation of reduction

  ↠*-concat : s ↠* s′ → s′ ↠* s″ → s ↠* s″
  ↠*-concat id d′ = d′
  ↠*-concat (x ⇨ d) d′ = x ⇨ (↠*-concat d d′)

opaque
  infix 30 ⇾ₑ*_

  -- Lifting normalising reduction to main reduction

  ⇾ₑ*_ : s ⇾ₑ* s′ → s ⇾* s′
  ⇾ₑ* id = id
  ⇾ₑ* (x ⇨ d) = (⇾ₑ x) ⇨ (⇾ₑ* d)

------------------------------------------------------------------------
-- The heap semantics are deterministic

opaque

  -- The reduction relation for eliminators is deterministic

  ⇒ₑ-det : s ⇒ₑ s′ → s ⇒ₑ s″ → s′ ≡ s″
  ⇒ₑ-det d lowerₕ = ⇒ₑ-inv-lower d
  ⇒ₑ-det d appₕ = ⇒ₑ-inv-∘ d
  ⇒ₑ-det d fstₕ = ⇒ₑ-inv-fst d
  ⇒ₑ-det d sndₕ = ⇒ₑ-inv-snd d
  ⇒ₑ-det d prodrecₕ = ⇒ₑ-inv-prodrec d
  ⇒ₑ-det d natrecₕ = ⇒ₑ-inv-natrec d
  ⇒ₑ-det d (unitrecₕ x) = ⇒ₑ-inv-unitrec d .proj₁
  ⇒ₑ-det d emptyrecₕ = ⇒ₑ-inv-emptyrec d
  ⇒ₑ-det d Jₕ = ⇒ₑ-inv-J d
  ⇒ₑ-det d Kₕ = ⇒ₑ-inv-K d
  ⇒ₑ-det d []-congₕ = ⇒ₑ-inv-[]-cong d

opaque

  -- The normalising reduction relation is deterministic

  ⇾ₑ-det :
    {s′ : State k m n} {s″ : State k m n′} →
    s ⇾ₑ s′ → s ⇾ₑ s″ →
    Σ (n ≡ n′) λ n≡n′ → subst (State k m) n≡n′ s′ ≡ s″
  ⇾ₑ-det {s′ = record{}} d (var ∣S∣≡ x′) =
    case ⇾ₑ-inv-var d of λ {
      (_ , ∣S∣≡′ , refl , x) →
    case ∣∣-functional ∣S∣≡ ∣S∣≡′ of λ {
      refl →
    case lookup-det x x′ of λ {
      (refl , refl , refl , refl) →
    refl , refl }}}
  ⇾ₑ-det (⇒ₑ d) (⇒ₑ d′) =
    refl , ⇒ₑ-det d d′
  ⇾ₑ-det (var _ _) (⇒ₑ ())

opaque

  -- The non-tracking reduction relation is deterministic

  ⇢ₑ-det :
    {s′ : State k m n} {s″ : State k m n′} →
    s ⇢ₑ s′ → s ⇢ₑ s″ →
    Σ (n ≡ n′) λ n≡n′ → subst (State k m) n≡n′ s′ ≡ s″
  ⇢ₑ-det {s′ = record{}} d (var x′) =
    case ⇢ₑ-inv-var d of λ {
      (refl , refl , x) →
    case lookup-det′ x x′ of λ {
      (refl , refl , refl) →
    refl , refl }}
  ⇢ₑ-det (⇒ₑ d) (⇒ₑ d′) = refl , ⇒ₑ-det d d′
  ⇢ₑ-det (var _) (⇒ₑ ())

opaque

  -- The reduction relation for values is deterministic

  ⇒ᵥ-det : {s′ : State k m n} {s″ : State k m′ n′}
         → (d : s ⇒ᵥ s′) (d′ : s ⇒ᵥ s″)
         → Σ (m ≡ m′) λ m≡m′ → Σ (n ≡ n′) λ n≡n′ →
            subst₂ (State k) m≡m′ n≡n′ s′ ≡ s″
  ⇒ᵥ-det d liftₕ = ⇒ᵥ-inv-lift-lowerₑ d
  ⇒ᵥ-det d (lamₕ ∣S∣≡) =
    let _ , ∣S∣≡′ , rest = ⇒ᵥ-inv-lam-∘ₑ d
    in  case ∣∣-functional ∣S∣≡ ∣S∣≡′ of λ where
          refl → rest
  ⇒ᵥ-det d prodˢₕ₁ = ⇒ᵥ-inv-prodˢ-fstₑ d
  ⇒ᵥ-det d prodˢₕ₂ = ⇒ᵥ-inv-prodˢ-sndₑ d
  ⇒ᵥ-det d (prodʷₕ ∣S∣≡) =
    let _ , ∣S∣≡′ , rest = ⇒ᵥ-inv-prodʷ-prodrecₑ d
    in  case ∣∣-functional ∣S∣≡ ∣S∣≡′ of λ where
          refl → rest
  ⇒ᵥ-det d zeroₕ = ⇒ᵥ-inv-zero-natrecₑ d
  ⇒ᵥ-det d (sucₕ ∣S∣≡ ∣nr∣≡) =
    let _ , _ , ∣S∣≡′ , ∣nr∣≡′ , rest = ⇒ᵥ-inv-suc-natrecₑ d
    in  case ∣∣-functional ∣S∣≡ ∣S∣≡′ of λ {
          refl →
        case ∣natrec∣ᵉ-functional ∣nr∣≡ ∣nr∣≡′ of λ {
          refl →
        rest }}
  ⇒ᵥ-det d starʷₕ = ⇒ᵥ-inv-starʷ-unitrecₑ d
  ⇒ᵥ-det d (unitrec-ηₕ x) = ⇒ᵥ-inv-unitrec-η d .proj₂
  ⇒ᵥ-det d rflₕⱼ = ⇒ᵥ-inv-rfl-Jₑ d
  ⇒ᵥ-det d rflₕₖ = ⇒ᵥ-inv-rfl-Kₑ d
  ⇒ᵥ-det d rflₕₑ = ⇒ᵥ-inv-rfl-[]-congₑ d

opaque

  -- The reduction relation for reducing to numerals is deterministic

  ⇒ₙ-det : {s′ : State k m n} {s″ : State k m n}
         → (d : s ⇒ₙ s′) (d′ : s ⇒ₙ s″)
         → s′ ≡ s″
  ⇒ₙ-det d (sucₕ x) = ⇒ₙ-inv-suc x d .proj₂ .proj₂
  ⇒ₙ-det d (numₕ x) =
    case ⇒ₙ-inv-num x d of λ {
      (S , refl , refl) → refl }

opaque

  -- A state cannot reduce in both ⇒ᵥ and ⇒ₙ

  not-⇒ᵥ-and-⇒ₑ : s ⇒ᵥ s′ → s ⇒ₑ s″ → ⊥
  not-⇒ᵥ-and-⇒ₑ liftₕ d = ⇒ₑ-inv-lift d
  not-⇒ᵥ-and-⇒ₑ (lamₕ _) d = ⇒ₑ-inv-lam d
  not-⇒ᵥ-and-⇒ₑ prodˢₕ₁ d = ⇒ₑ-inv-prod d
  not-⇒ᵥ-and-⇒ₑ prodˢₕ₂ d = ⇒ₑ-inv-prod d
  not-⇒ᵥ-and-⇒ₑ (prodʷₕ _) d = ⇒ₑ-inv-prod d
  not-⇒ᵥ-and-⇒ₑ zeroₕ d = ⇒ₑ-inv-zero d
  not-⇒ᵥ-and-⇒ₑ (sucₕ _ _) d = ⇒ₑ-inv-suc d
  not-⇒ᵥ-and-⇒ₑ starʷₕ d = ⇒ₑ-inv-star d
  not-⇒ᵥ-and-⇒ₑ (unitrec-ηₕ η) d = ⇒ₑ-inv-unitrec-η η d
  not-⇒ᵥ-and-⇒ₑ rflₕⱼ d = ⇒ₑ-inv-rfl d
  not-⇒ᵥ-and-⇒ₑ rflₕₖ d = ⇒ₑ-inv-rfl d
  not-⇒ᵥ-and-⇒ₑ rflₕₑ d = ⇒ₑ-inv-rfl d

opaque

  not-⇒ᵥ-and-⇾ₑ : s ⇒ᵥ s′ → s ⇾ₑ s″ → ⊥
  not-⇒ᵥ-and-⇾ₑ d  (⇒ₑ d′) = not-⇒ᵥ-and-⇒ₑ d d′
  not-⇒ᵥ-and-⇾ₑ () (var _ _)

opaque

  not-⇒ᵥ-and-⇢ₑ : s ⇒ᵥ s′ → s ⇢ₑ s″ → ⊥
  not-⇒ᵥ-and-⇢ₑ d (var x) = ⇒ᵥ-inv-var d
  not-⇒ᵥ-and-⇢ₑ d (⇒ₑ d′) = not-⇒ᵥ-and-⇒ₑ d d′

opaque

  -- A state cannot reduce in both ⇒ₙ and ⇒ᵥ

  not-⇒ₙ-and-⇒ᵥ : s ⇒ₙ s′ → s ⇒ᵥ s″ → ⊥
  not-⇒ₙ-and-⇒ᵥ (sucₕ {ℓ = 0} x) d =
    case ⇒ᵥ-inv-suc d of λ {
      (_ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , () , _)}
  not-⇒ₙ-and-⇒ᵥ (sucₕ {ℓ = 1+ ℓ} x) d =
    case ⇒ᵥ-inv-suc d of λ {
      (_ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , () , _)}
  not-⇒ₙ-and-⇒ᵥ (numₕ zeroₙ) d =
    case ⇒ᵥ-inv-zero d of λ {
      (_ , _ , _ , _ , _ , _ , _ , _ , _ , () , _)}
  not-⇒ₙ-and-⇒ᵥ (numₕ (sucₙ x)) d =
    case ⇒ᵥ-inv-suc d of λ {
      (_ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , () , _)}

opaque

  -- A state cannot reduce in both ⇒ₙ and ⇾ₑ

  not-⇒ₙ-and-⇒ₑ : s ⇒ₙ s′ → s ⇒ₑ s″ → ⊥
  not-⇒ₙ-and-⇒ₑ (sucₕ x) d = ⇒ₑ-inv-suc d
  not-⇒ₙ-and-⇒ₑ (numₕ zeroₙ) d = ⇒ₑ-inv-zero d
  not-⇒ₙ-and-⇒ₑ (numₕ (sucₙ x)) d = ⇒ₑ-inv-suc d

opaque

  -- A state cannot reduce in both ⇒ₙ and ⇾ₑ

  not-⇒ₙ-and-⇾ₑ : s ⇒ₙ s′ → s ⇾ₑ s″ → ⊥
  not-⇒ₙ-and-⇾ₑ d (var _ _) = ⇒ₙ-inv-var d
  not-⇒ₙ-and-⇾ₑ d (⇒ₑ d′) = not-⇒ₙ-and-⇒ₑ d d′

opaque

  -- The small-step heap semantics is deterministic

  ⇾-det : {s′ : State k m n} {s″ : State k m′ n′}
        → (d : s ⇾ s′) (d′ : s ⇾ s″)
        → Σ (m ≡ m′) λ m≡m′ →
          Σ (n ≡ n′) λ n≡n′ →
            subst₂ (State k) m≡m′ n≡n′ s′ ≡ s″
  ⇾-det (⇾ₑ d) (⇾ₑ d′) =
    case ⇾ₑ-det d d′ of λ where
      (refl , s~s′) → refl , refl , s~s′
  ⇾-det (⇒ᵥ d) (⇒ᵥ d′) = ⇒ᵥ-det d d′
  ⇾-det (⇾ₑ d) (⇒ᵥ d′) =
    ⊥-elim (not-⇒ᵥ-and-⇾ₑ d′ d)
  ⇾-det (⇒ᵥ d) (⇾ₑ d′) =
    ⊥-elim (not-⇒ᵥ-and-⇾ₑ d d′)

opaque

  -- The non-trackigng small-step heap semantics is deterministic.

  ⇢-det : {s′ : State k m n} {s″ : State k m′ n′}
        → (d : s ⇢ s′) (d′ : s ⇢ s″)
        → Σ (m ≡ m′) λ m≡m′ →
          Σ (n ≡ n′) λ n≡n′ →
            subst₂ (State k) m≡m′ n≡n′ s′ ≡ s″
  ⇢-det (⇢ₑ d) (⇢ₑ d′) =
    case ⇢ₑ-det d d′ of λ where
      (refl , refl) → refl , refl , refl
  ⇢-det (⇒ᵥ d) (⇒ᵥ d′) = ⇒ᵥ-det d d′
  ⇢-det (⇢ₑ d) (⇒ᵥ d′) = ⊥-elim (not-⇒ᵥ-and-⇢ₑ d′ d)
  ⇢-det (⇒ᵥ d) (⇢ₑ d′) = ⊥-elim (not-⇒ᵥ-and-⇢ₑ d d′)

opaque

  -- The fully evaluating small-step heap semantics is deterministic.

  ↠-det : {s′ : State k m n} {s″ : State k m′ n′}
        → (d : s ↠ s′) (d′ : s ↠ s″)
        → Σ (m ≡ m′) λ m≡m′ →
          Σ (n ≡ n′) λ n≡n′ →
            subst₂ (State k) m≡m′ n≡n′ s′ ≡ s″
  ↠-det (⇾ₑ d) (⇾ₑ d′) =
    case ⇾ₑ-det d d′ of λ where
      (refl , s~s′) → refl , refl , s~s′
  ↠-det (⇒ᵥ d) (⇒ᵥ d′) = ⇒ᵥ-det d d′
  ↠-det (⇒ₙ d) (⇒ₙ d′) = refl , refl , ⇒ₙ-det d d′
  ↠-det (⇾ₑ d) (⇒ᵥ d′) =
    ⊥-elim (not-⇒ᵥ-and-⇾ₑ d′ d)
  ↠-det (⇾ₑ d) (⇒ₙ d′) =
    ⊥-elim (not-⇒ₙ-and-⇾ₑ d′ d)
  ↠-det (⇒ᵥ d) (⇾ₑ d′) =
    ⊥-elim (not-⇒ᵥ-and-⇾ₑ d d′)
  ↠-det (⇒ᵥ d) (⇒ₙ d′) =
    ⊥-elim (not-⇒ₙ-and-⇒ᵥ d′ d)
  ↠-det (⇒ₙ d) (⇾ₑ d′) =
    ⊥-elim (not-⇒ₙ-and-⇾ₑ d d′)
  ↠-det (⇒ₙ d) (⇒ᵥ d′) =
    ⊥-elim (not-⇒ₙ-and-⇒ᵥ d d′)

opaque

  -- The reflexive, transitive closure of the fully evaluating
  -- heap semantics is deterministic.

  ↠*-det : {s′ : State k m n} {s″ : State k m′ n′}
         → (d : s ↠* s′) (d′ : s ↠* s″)
         → (∀ {m n} (s‴ : State k m n) → ¬ s′ ↠ s‴)
         → (∀ {m n} (s‴ : State k m n) → ¬ s″ ↠ s‴)
         → Σ (m ≡ m′) λ m≡m′ →
           Σ (n ≡ n′) λ n≡n′ →
             subst₂ (State k) m≡m′ n≡n′ s′ ≡ s″
  ↠*-det id id ¬d ¬d′ = refl , refl , refl
  ↠*-det id (x ⇨ d′) ¬d ¬d′ = ⊥-elim (¬d _ x)
  ↠*-det (x ⇨ d) id ¬d ¬d′ = ⊥-elim (¬d′ _ x)
  ↠*-det (x ⇨ d) (x′ ⇨ d′) ¬d ¬d′ =
    case ↠-det x x′ of λ where
      (refl , refl , refl) →
        ↠*-det d d′ ¬d ¬d′

opaque

  -- The normalising reduction preserves equality in a certain way

  ⇒ₑ-⦅⦆-≡ : s ⇒ₑ s′ → ⦅ s ⦆ ≡ ⦅ s′ ⦆
  ⇒ₑ-⦅⦆-≡ lowerₕ = refl
  ⇒ₑ-⦅⦆-≡ appₕ = refl
  ⇒ₑ-⦅⦆-≡ fstₕ = refl
  ⇒ₑ-⦅⦆-≡ sndₕ = refl
  ⇒ₑ-⦅⦆-≡ prodrecₕ = refl
  ⇒ₑ-⦅⦆-≡ natrecₕ = refl
  ⇒ₑ-⦅⦆-≡ (unitrecₕ _) = refl
  ⇒ₑ-⦅⦆-≡ emptyrecₕ = refl
  ⇒ₑ-⦅⦆-≡ Jₕ = refl
  ⇒ₑ-⦅⦆-≡ Kₕ = refl
  ⇒ₑ-⦅⦆-≡ []-congₕ = refl

opaque

  -- The normalising reduction preserves equality in a certain way

  ⇾ₑ-⦅⦆-≡ : s ⇾ₑ s′ → ⦅ s ⦆ ≡ ⦅ s′ ⦆
  ⇾ₑ-⦅⦆-≡ {s = ⟨ _ , _ , _ , S ⟩} (var _ d) =
    trans (⦅⦆ˢ-cong S (heapSubstVar d))
      (cong (λ x → ⦅ S ⦆ˢ _ [ x ]) (heapUpdateSubst d))
  ⇾ₑ-⦅⦆-≡ (⇒ₑ d) = ⇒ₑ-⦅⦆-≡ d

opaque

  -- The normalising reduction preserves equality in a certain way

  ⇾ₑ*-⦅⦆-≡ : s ⇾ₑ* s′ → ⦅ s ⦆ ≡ ⦅ s′ ⦆
  ⇾ₑ*-⦅⦆-≡ id = refl
  ⇾ₑ*-⦅⦆-≡ (x ⇨ d) = trans (⇾ₑ-⦅⦆-≡ x) (⇾ₑ*-⦅⦆-≡ d)

opaque

  -- The normalising reduction preserves equality in a certain way

  ⇢ₑ-⦅⦆-≡ : s ⇢ₑ s′ → ⦅ s ⦆ ≡ ⦅ s′ ⦆
  ⇢ₑ-⦅⦆-≡ {s = ⟨ _ , _ , _ , S ⟩} (var d) = ⦅⦆ˢ-cong S (heapSubstVar′ d)
  ⇢ₑ-⦅⦆-≡ (⇒ₑ d) = ⇒ₑ-⦅⦆-≡ d

opaque

  -- The reduction evaluating numerals preserves equality in a certain
  -- way

  ⇒ₙ-⦅⦆-≡ : s ⇒ₙ s′ → ⦅ s ⦆ ≡ ⦅ s′ ⦆
  ⇒ₙ-⦅⦆-≡ (sucₕ x) = refl
  ⇒ₙ-⦅⦆-≡ (numₕ x) = refl

opaque

  -- Lifting a normalising reduction to a larger heap

  wk1-⇒ₑ : ⟨ H , t , ρ , S ⟩ ⇒ₑ ⟨ H′ , t′ , ρ′ , S′ ⟩
          → ⟨ H ∙ c , t , step ρ , wk1ˢ S ⟩ ⇒ₑ ⟨ H′ ∙ c , t′ , step ρ′ , wk1ˢ S′ ⟩
  wk1-⇒ₑ lowerₕ = lowerₕ
  wk1-⇒ₑ appₕ = appₕ
  wk1-⇒ₑ fstₕ = fstₕ
  wk1-⇒ₑ sndₕ = sndₕ
  wk1-⇒ₑ prodrecₕ = prodrecₕ
  wk1-⇒ₑ natrecₕ = natrecₕ
  wk1-⇒ₑ (unitrecₕ x) = unitrecₕ x
  wk1-⇒ₑ emptyrecₕ = emptyrecₕ
  wk1-⇒ₑ Jₕ = Jₕ
  wk1-⇒ₑ Kₕ = Kₕ
  wk1-⇒ₑ []-congₕ = []-congₕ

opaque

  -- Lifting a normalising reduction to a larger heap

  wk1-⇾ₑ : ⟨ H , t , ρ , S ⟩ ⇾ₑ ⟨ H′ , t′ , ρ′ , S′ ⟩
         → ⟨ H ∙ c , t , step ρ , wk1ˢ S ⟩ ⇾ₑ ⟨ H′ ∙ c , t′ , step ρ′ , wk1ˢ S′ ⟩
  wk1-⇾ₑ {S} (var ∣S∣≡ d) =
    var (wk-∣∣ ∣S∣≡) (there d)
  wk1-⇾ₑ (⇒ₑ d) = ⇒ₑ (wk1-⇒ₑ d)

opaque

  -- Lifting a normalising reduction to a larger heap

  wk1-⇢ₑ : ⟨ H , t , ρ , S ⟩ ⇢ₑ ⟨ H′ , t′ , ρ′ , S′ ⟩
         → ⟨ H ∙ c , t , step ρ , wk1ˢ S ⟩ ⇢ₑ ⟨ H′ ∙ c , t′ , step ρ′ , wk1ˢ S′ ⟩
  wk1-⇢ₑ (var d) = var (there d)
  wk1-⇢ₑ (⇒ₑ d) = ⇒ₑ (wk1-⇒ₑ d)

opaque

  -- Lifting a normalising reduction to a larger heap

  wk1-⇢ₑ* : ⟨ H , t , ρ , S ⟩ ⇢ₑ* ⟨ H′ , t′ , ρ′ , S′ ⟩
          → ⟨ H ∙ c , t , step ρ , wk1ˢ S ⟩ ⇢ₑ* ⟨ H′ ∙ c , t′ , step ρ′ , wk1ˢ S′ ⟩
  wk1-⇢ₑ* id = id
  wk1-⇢ₑ* (_⇨_ {s′ = record{}} x d) = wk1-⇢ₑ x ⇨ wk1-⇢ₑ* d

opaque

  -- Lifting a normalising reduction to a larger heap

  wk1●-⇒ₑ : ⟨ H , t , ρ , S ⟩ ⇒ₑ ⟨ H′ , t′ , ρ′ , S′ ⟩
           → ⟨ H ∙● , t , step ρ , wk1ˢ S ⟩ ⇒ₑ ⟨ H′ ∙● , t′ , step ρ′ , wk1ˢ S′ ⟩
  wk1●-⇒ₑ lowerₕ = lowerₕ
  wk1●-⇒ₑ appₕ = appₕ
  wk1●-⇒ₑ fstₕ = fstₕ
  wk1●-⇒ₑ sndₕ = sndₕ
  wk1●-⇒ₑ prodrecₕ = prodrecₕ
  wk1●-⇒ₑ natrecₕ = natrecₕ
  wk1●-⇒ₑ (unitrecₕ x) = unitrecₕ x
  wk1●-⇒ₑ emptyrecₕ = emptyrecₕ
  wk1●-⇒ₑ Jₕ = Jₕ
  wk1●-⇒ₑ Kₕ = Kₕ
  wk1●-⇒ₑ []-congₕ = []-congₕ

opaque

  -- Lifting a normalising reduction to a larger heap

  wk1●-⇾ₑ : ⟨ H , t , ρ , S ⟩ ⇾ₑ ⟨ H′ , t′ , ρ′ , S′ ⟩
          → ⟨ H ∙● , t , step ρ , wk1ˢ S ⟩ ⇾ₑ ⟨ H′ ∙● , t′ , step ρ′ , wk1ˢ S′ ⟩
  wk1●-⇾ₑ {S} (var ∣S∣≡ d) =
    var (wk-∣∣ ∣S∣≡) (there● d)
  wk1●-⇾ₑ (⇒ₑ d) = ⇒ₑ wk1●-⇒ₑ d

opaque

  -- Lifting a normalising reduction to a larger heap

  wk1●-⇢ₑ : ⟨ H , t , ρ , S ⟩ ⇢ₑ ⟨ H′ , t′ , ρ′ , S′ ⟩
           → ⟨ H ∙● , t , step ρ , wk1ˢ S ⟩ ⇢ₑ ⟨ H′ ∙● , t′ , step ρ′ , wk1ˢ S′ ⟩
  wk1●-⇢ₑ (var d) = var (there● d)
  wk1●-⇢ₑ (⇒ₑ d) = ⇒ₑ (wk1●-⇒ₑ d)

opaque

  -- Lifting a normalising reduction to a larger heap

  wk1●-⇢ₑ* : (d : ⟨ H , t , ρ , S ⟩ ⇢ₑ* ⟨ H′ , t′ , ρ′ , S′ ⟩)
          → ⟨ H ∙● , t , step ρ , wk1ˢ S ⟩ ⇢ₑ* ⟨ H′ ∙● , t′ , step ρ′ , wk1ˢ S′ ⟩
  wk1●-⇢ₑ* id = id
  wk1●-⇢ₑ* (_⇨_ {s′ = record{}} x d) = wk1●-⇢ₑ x ⇨ wk1●-⇢ₑ* d

opaque

  -- Replacing a variable and environment in a state

  var-env-⇢ₑ : ⟨ H , var x , ρ , S ⟩ ⇢ₑ s
            → wkVar ρ x ≡ wkVar ρ′ x′
            → ⟨ H , var x′ , ρ′ , S ⟩ ⇢ₑ s
  var-env-⇢ₑ (var d) eq = var (subst (_ ⊢_↦ _) eq d)
  var-env-⇢ₑ (⇒ₑ ())

opaque

  -- Replacing a variable and environment in a state

  var-env-⇢ₑ* : {ρ : Wk m n} {ρ″ : Wk m n′}
              → ⟨ H , var x , ρ , S ⟩ ⇢ₑ* ⟨ H′ , t , ρ″ , S′ ⟩
             → wkVar ρ x ≡ wkVar ρ′ x′
             → Normal ⟨ H′ , t , ρ″ , S′ ⟩
             → ⟨ H , var x′ , ρ′ , S ⟩ ⇢ₑ* ⟨ H′ , t , ρ″ , S′ ⟩
             ⊎ Σ (n′ ≡ n) λ n′≡n → ⟨ H , var x , ρ , S ⟩ ≡ subst (State _ _) n′≡n ⟨ H′ , t , ρ″ , S′ ⟩
  var-env-⇢ₑ* id eq (var x) = inj₂ (refl , refl)
  var-env-⇢ₑ* id _ (val ())
  var-env-⇢ₑ* (x ⇨ d) eq n = inj₁ (var-env-⇢ₑ x eq ⇨ d)

opaque

  -- Extending the stack of a reduction

  ++-⇒ₑ : ∀ S₀ → ⟨ H , t , ρ , S ⟩ ⇒ₑ ⟨ H′ , t′ , ρ′ , S′ ⟩
         → ⟨ H , t , ρ , S ++ S₀ ⟩ ⇒ₑ ⟨ H′ , t′ , ρ′ , S′ ++ S₀ ⟩
  ++-⇒ₑ S₀ appₕ = appₕ
  ++-⇒ₑ S₀ fstₕ = fstₕ
  ++-⇒ₑ S₀ sndₕ = sndₕ
  ++-⇒ₑ S₀ prodrecₕ = prodrecₕ
  ++-⇒ₑ S₀ natrecₕ = natrecₕ
  ++-⇒ₑ S₀ (unitrecₕ x) = unitrecₕ x
  ++-⇒ₑ S₀ emptyrecₕ = emptyrecₕ
  ++-⇒ₑ S₀ Jₕ = Jₕ
  ++-⇒ₑ S₀ Kₕ = Kₕ
  ++-⇒ₑ S₀ []-congₕ = []-congₕ
  ++-⇒ₑ S₀ lowerₕ = lowerₕ

opaque

  -- Extending the stack of a reduction

  ++-⇢ₑ : ∀ S₀ → ⟨ H , t , ρ , S ⟩ ⇢ₑ ⟨ H′ , t′ , ρ′ , S′ ⟩
        → ⟨ H , t , ρ , S ++ S₀ ⟩ ⇢ₑ ⟨ H′ , t′ , ρ′ , S′ ++ S₀ ⟩
  ++-⇢ₑ S₀ (var d) = var d
  ++-⇢ₑ S₀ (⇒ₑ d) = ⇒ₑ (++-⇒ₑ S₀ d)

opaque

  -- Extending the stack of a reduction

  ++-⇢ₑ* : ∀ S₀ → (d : ⟨ H , t , ρ , S ⟩ ⇢ₑ* ⟨ H′ , t′ , ρ′ , S′ ⟩)
         → ⟨ H , t , ρ , S ++ S₀ ⟩ ⇢ₑ* ⟨ H′ , t′ , ρ′ , S′ ++ S₀ ⟩
  ++-⇢ₑ* S₀ id = id
  ++-⇢ₑ* S₀ (_⇨_ {s′ = record{}} x d) = ++-⇢ₑ S₀ x ⇨ ++-⇢ₑ* S₀ d

opaque

  -- Extending the stack of a reduction with sucₛ

  ++sucₛ-⇾ₑ : (d : ⟨ H , t , ρ , S ⟩ ⇾ₑ ⟨ H′ , t′ , ρ′ , S′ ⟩)
            → ⟨ H , t , ρ , S ++ sucₛ k ⟩ ⇾ₑ ⟨ H′ , t′ , ρ′ , S′ ++ sucₛ k ⟩
  ++sucₛ-⇾ₑ {S} (var ∣S∣≡ d) =
    var (∣S++sucₛ∣≡∣S∣ ∣S∣≡) d
  ++sucₛ-⇾ₑ (⇒ₑ x) = ⇒ₑ (++-⇒ₑ _ x)

opaque

  -- Extending the stack of a reduction with sucₛ

  ++sucₛ-⇒ᵥ : (d : ⟨ H , t , ρ , S ⟩ ⇒ᵥ ⟨ H′ , t′ , ρ′ , S′ ⟩)
            → ⟨ H , t , ρ , S ++ sucₛ k ⟩ ⇒ᵥ ⟨ H′ , t′ , ρ′ , S′ ++ sucₛ k ⟩
  ++sucₛ-⇒ᵥ liftₕ = liftₕ
  ++sucₛ-⇒ᵥ {k} (lamₕ {S} {H} {p} {t} {ρ} {u} {ρ′} ∣S∣≡) =
    subst
      (λ x →
         ⟨ H , lam p t , ρ , (∘ₑ p u ρ′ ∙ S) ++ sucₛ k ⟩ ⇒ᵥ
         ⟨ H ∙ (_ · p , u , ρ′) , t , lift ρ , x ⟩)
         (wk-++sucₛ (step id) S) (lamₕ (∣S++sucₛ∣≡∣S∣ ∣S∣≡))
  ++sucₛ-⇒ᵥ prodˢₕ₁ = prodˢₕ₁
  ++sucₛ-⇒ᵥ prodˢₕ₂ = prodˢₕ₂
  ++sucₛ-⇒ᵥ {k} (prodʷₕ {S} {H} {p} {t₁} {t₂} {ρ} {r} {q} {A} {u} {ρ′} ∣S∣≡) =
    subst
      (λ x →
         ⟨ H , prodʷ p t₁ t₂ , ρ , (prodrecₑ r p q A u ρ′ ∙ S) ++ sucₛ k ⟩ ⇒ᵥ
         ⟨ H ∙ (_ · r · p , t₁ , ρ) ∙ (_ · r , t₂ , step ρ) , u , liftn ρ′ 2 , x ⟩)
      (wk-++sucₛ (step (step id)) S) (prodʷₕ (∣S++sucₛ∣≡∣S∣ ∣S∣≡ ))
  ++sucₛ-⇒ᵥ zeroₕ = zeroₕ
  ++sucₛ-⇒ᵥ {k} (sucₕ {S} {r} {H} {t} {ρ} {A} {z} {s} {ρ′} ∣S∣≡ ∣nr∣≡) =
    subst
      (λ x →
        ⟨ H , suc t , ρ , natrecₑ _ _ r A z s ρ′ ∙ S ++ sucₛ k ⟩ ⇒ᵥ
        ⟨ H ∙ (_ · _ , t , ρ) ∙ (_ · r , _ , lift ρ′) , s , liftn ρ′ 2 , x ⟩)
      (wk-++sucₛ (step (step id)) S) (sucₕ (∣S++sucₛ∣≡∣S∣ ∣S∣≡) ∣nr∣≡)
  ++sucₛ-⇒ᵥ starʷₕ = starʷₕ
  ++sucₛ-⇒ᵥ (unitrec-ηₕ η) = unitrec-ηₕ η
  ++sucₛ-⇒ᵥ rflₕⱼ = rflₕⱼ
  ++sucₛ-⇒ᵥ rflₕₖ = rflₕₖ
  ++sucₛ-⇒ᵥ rflₕₑ = rflₕₑ

opaque

  -- Extending the stack of a reduction with sucₛ

  ++sucₛ-⇒ₙ : (d : ⟨ H , t , ρ , S ⟩ ⇒ₙ ⟨ H′ , t′ , ρ′ , S′ ⟩)
            → ⟨ H , t , ρ , S ++ sucₛ k ⟩ ⇒ₙ ⟨ H′ , t′ , ρ′ , S′ ++ sucₛ k ⟩
  ++sucₛ-⇒ₙ {k} (sucₕ {t} {H} {ρ} {ℓ} x) =
    subst (λ x → ⟨ H , suc t , ρ , x ⟩ ⇒ₙ ⟨ H , t , ρ , sucₑ ∙ x ⟩)
      (sym (sucₛ++sucₛ ℓ k)) (sucₕ x)
  ++sucₛ-⇒ₙ (numₕ x) = numₕ x

opaque

  ++sucₛ-↠ : ⟨ H , t , ρ , S ⟩ ↠ ⟨ H′ , t′ , ρ′ , S′ ⟩
           → ⟨ H , t , ρ , S ++ sucₛ k ⟩ ↠ ⟨ H′ , t′ , ρ′ , S′ ++ sucₛ k ⟩
  ++sucₛ-↠ (⇾ₑ x) = ⇾ₑ ++sucₛ-⇾ₑ x
  ++sucₛ-↠ (⇒ᵥ x) = ⇒ᵥ ++sucₛ-⇒ᵥ x
  ++sucₛ-↠ (⇒ₙ x) = ⇒ₙ ++sucₛ-⇒ₙ x

opaque

  ++sucₛ-↠* : ⟨ H , t , ρ , S ⟩ ↠* ⟨ H′ , t′ , ρ′ , S′ ⟩
            → ⟨ H , t , ρ , S ++ sucₛ k ⟩ ↠* ⟨ H′ , t′ , ρ′ , S′ ++ sucₛ k ⟩
  ++sucₛ-↠* id = id
  ++sucₛ-↠* (_⇨_ {s₂ = record{}} x d) =
    ++sucₛ-↠ x ⇨ ++sucₛ-↠* d

opaque

  -- The relation _⇒ₑ_ preserves the heap

  ⇒ₑ-Heap≡ : ⟨ H , t , ρ , S ⟩ ⇒ₑ ⟨ H′ , t′ , ρ′ , S′ ⟩ → H ≡ H′
  ⇒ₑ-Heap≡ lowerₕ = refl
  ⇒ₑ-Heap≡ appₕ = refl
  ⇒ₑ-Heap≡ fstₕ = refl
  ⇒ₑ-Heap≡ sndₕ = refl
  ⇒ₑ-Heap≡ prodrecₕ = refl
  ⇒ₑ-Heap≡ natrecₕ = refl
  ⇒ₑ-Heap≡ (unitrecₕ x) = refl
  ⇒ₑ-Heap≡ emptyrecₕ = refl
  ⇒ₑ-Heap≡ Jₕ = refl
  ⇒ₑ-Heap≡ Kₕ = refl
  ⇒ₑ-Heap≡ []-congₕ = refl

opaque

  -- The relation _⇢ₑ_ preserves the heap

  ⇢ₑ-Heap≡ : ⟨ H , t , ρ , S ⟩ ⇢ₑ ⟨ H′ , t′ , ρ′ , S′ ⟩ → H ≡ H′
  ⇢ₑ-Heap≡ (var d) = refl
  ⇢ₑ-Heap≡ (⇒ₑ d) = ⇒ₑ-Heap≡ d

opaque

  -- The relation _⇒ₙ_ preserves the heap

  ⇒ₙ-Heap≡ : ⟨ H , t , ρ , S ⟩ ⇒ₙ ⟨ H′ , t′ , ρ′ , S′ ⟩ → H ≡ H′
  ⇒ₙ-Heap≡ (sucₕ x) = refl
  ⇒ₙ-Heap≡ (numₕ x) = refl

opaque

  -- The reduction for eliminators behaves the same on equal heaps

  ~ʰ-⇒ₑ :
    ⟨ H , t , ρ , S ⟩ ⇒ₑ ⟨ H′ , t′ , ρ′ , S′ ⟩ → H ~ʰ H″ →
    ∃ λ H‴ → ⟨ H″ , t , ρ , S ⟩ ⇒ₑ ⟨ H‴ , t′ , ρ′ , S′ ⟩ × H′ ~ʰ H‴
  ~ʰ-⇒ₑ lowerₕ H~H″ =
    _ , lowerₕ , H~H″
  ~ʰ-⇒ₑ appₕ H~H″ =
    _ , appₕ , H~H″
  ~ʰ-⇒ₑ fstₕ H~H″ =
    _ , fstₕ , H~H″
  ~ʰ-⇒ₑ sndₕ H~H″ =
    _ , sndₕ , H~H″
  ~ʰ-⇒ₑ prodrecₕ H~H″ =
    _ , prodrecₕ , H~H″
  ~ʰ-⇒ₑ natrecₕ H~H″ =
    _ , natrecₕ , H~H″
  ~ʰ-⇒ₑ (unitrecₕ x) H~H″ =
    _ , unitrecₕ x , H~H″
  ~ʰ-⇒ₑ emptyrecₕ H~H″ =
    _ , emptyrecₕ , H~H″
  ~ʰ-⇒ₑ Jₕ H~H″ =
    _ , Jₕ , H~H″
  ~ʰ-⇒ₑ Kₕ H~H″ =
    _ , Kₕ , H~H″
  ~ʰ-⇒ₑ []-congₕ H~H″ =
    _ , []-congₕ , H~H″

opaque

  -- The non resource tracking reduction for eliminators behaves the
  -- same on equal heaps

  ~ʰ-⇢ₑ :
    ⟨ H , t , ρ , S ⟩ ⇢ₑ ⟨ H′ , t′ , ρ′ , S′ ⟩ → H ~ʰ H″ →
    ∃ λ H‴ → ⟨ H″ , t , ρ , S ⟩ ⇢ₑ ⟨ H‴ , t′ , ρ′ , S′ ⟩ × H′ ~ʰ H‴
  ~ʰ-⇢ₑ (var d) H~H″ =
    _ ,  var (~ʰ-lookup H~H″ d) , H~H″
  ~ʰ-⇢ₑ (⇒ₑ d) H~H″ =
    let _ , d′ , H~H′ = ~ʰ-⇒ₑ d H~H″
    in  _ , ⇒ₑ d′ , H~H′

opaque

  -- The reduction for values behaves the same on equal heaps

  ~ʰ-⇒ᵥ :
    ⟨ H , t , ρ , S ⟩ ⇒ᵥ ⟨ H′ , t′ , ρ′ , S′ ⟩ → H ~ʰ H″ →
    ∃ λ H‴ → ⟨ H″ , t , ρ , S ⟩ ⇒ᵥ ⟨ H‴ , t′ , ρ′ , S′ ⟩ × H′ ~ʰ H‴
  ~ʰ-⇒ᵥ liftₕ H~H″ = _ , liftₕ , H~H″
  ~ʰ-⇒ᵥ (lamₕ ∣S∣≡) H~H″ = _ , lamₕ ∣S∣≡ , H~H″ ∙ _
  ~ʰ-⇒ᵥ prodˢₕ₁ H~H″ = _ , prodˢₕ₁ , H~H″
  ~ʰ-⇒ᵥ prodˢₕ₂ H~H″ = _ , prodˢₕ₂ , H~H″
  ~ʰ-⇒ᵥ (prodʷₕ ∣S∣≡) H~H″ = _ , prodʷₕ ∣S∣≡ , H~H″ ∙ _ ∙ _
  ~ʰ-⇒ᵥ zeroₕ H~H″ = _ , zeroₕ , H~H″
  ~ʰ-⇒ᵥ (sucₕ ∣S∣≡ ∣nr∣≡) H~H″ = _ , sucₕ ∣S∣≡ ∣nr∣≡ , H~H″ ∙ _ ∙ _
  ~ʰ-⇒ᵥ starʷₕ H~H″ = _ , starʷₕ , H~H″
  ~ʰ-⇒ᵥ (unitrec-ηₕ x) H~H″ = _ , unitrec-ηₕ x , H~H″
  ~ʰ-⇒ᵥ rflₕⱼ H~H″ = _ , rflₕⱼ , H~H″
  ~ʰ-⇒ᵥ rflₕₖ H~H″ = _ , rflₕₖ , H~H″
  ~ʰ-⇒ᵥ rflₕₑ H~H″ = _ , rflₕₑ , H~H″

opaque

  -- The non resource tracking reduction behaves the same on equal heaps

  ~ʰ-⇢ :
    ⟨ H , t , ρ , S ⟩ ⇢ ⟨ H′ , t′ , ρ′ , S′ ⟩ → H ~ʰ H″ →
    ∃ λ H‴ → ⟨ H″ , t , ρ , S ⟩ ⇢ ⟨ H‴ , t′ , ρ′ , S′ ⟩ × H′ ~ʰ H‴
  ~ʰ-⇢ (⇢ₑ d) H~H″ =
    let _ , d′ , H~H′ = ~ʰ-⇢ₑ d H~H″
    in  _ , ⇢ₑ d′ , H~H′
  ~ʰ-⇢ (⇒ᵥ d) H~H″ =
    let _ , d′ , H~H′ = ~ʰ-⇒ᵥ d H~H″
    in  _ , ⇒ᵥ d′ , H~H′

opaque

  -- The non resource tracking reduction behaves the same on equal heaps

  ~ʰ-⇢* :
    ⟨ H , t , ρ , S ⟩ ⇢* ⟨ H′ , t′ , ρ′ , S′ ⟩ → H ~ʰ H″ →
    ∃ λ H‴ → ⟨ H″ , t , ρ , S ⟩ ⇢* ⟨ H‴ , t′ , ρ′ , S′ ⟩ × H′ ~ʰ H‴
  ~ʰ-⇢* id H~H″ =
    _ , id , H~H″
  ~ʰ-⇢* (_⇨_ {s₂ = record{}} x d) H~H″ =
    let _ , x′ , H~H′ = ~ʰ-⇢ x H~H″
        _ , d′ , H~H‴ = ~ʰ-⇢* d H~H′
    in  _ , x′ ⇨ d′ , H~H‴

opaque

  -- _⇾_ is a subset of _↠_, if s ⇾ s′ then s ↠ s′.

  ⇾→↠ : s ⇾ s′ → s ↠ s′
  ⇾→↠ (⇾ₑ d) = ⇾ₑ d
  ⇾→↠ (⇒ᵥ d) = ⇒ᵥ d

opaque

  -- _⇾*_ is a subset of _↠*_, if s ⇾* s′ then s ↠* s′.

  ⇾*→↠* : s ⇾* s′ → s ↠* s′
  ⇾*→↠* id = id
  ⇾*→↠* (x ⇨ d) = ⇾→↠ x ⇨ ⇾*→↠* d

opaque

  -- If subtraction of the grade correspoding to a heap entry cannot
  -- by subtracted by the current stack multiplicity then states with
  -- a variable in head position "pointing" to that entry do not reduce.

  var-noRed :
    H ⟨ wkVar ρ x ⟩ʰ ≡ p → ∣ S ∣≡ q →
    (∀ {r} → p - q ≡ r → ⊥) →
    ⟨ H , var x , ρ , S ⟩ ⇾ ⟨ H′ , t , ρ′ , S′ ⟩ → ⊥
  var-noRed H⟨⟩≡ ∣S∣≡ p-q≢r (⇾ₑ d) =
    let q′ , ∣S∣≡′ , _ , d′ = ⇾ₑ-inv-var d
    in  -≢-no-lookup
          (subst₂ (λ p q → ∀ {r} → p - q ≡ r → ⊥)
            (sym H⟨⟩≡) (∣∣-functional ∣S∣≡ ∣S∣≡′) p-q≢r) d′
  var-noRed _ _ _ (⇒ᵥ d) = ⊥-elim (⇒ᵥ-inv-var d)

opaque

  -- States with a matching head and stack reduce

  Matching→⇒ᵥ :
    Matching t S →
    ∣ S ∣≡ p →
    ∃₃ λ m n (s : State _ m n) → ⟨ H , t , ρ , S ⟩ ⇒ᵥ s
  Matching→⇒ᵥ lowerₑ _ = _ , _ , _ , liftₕ
  Matching→⇒ᵥ ∘ₑ (_ ∙ ok) = _ , _ , _ , lamₕ ok
  Matching→⇒ᵥ fstₑ _ = _ , _ , _ , prodˢₕ₁
  Matching→⇒ᵥ sndₑ _ = _ , _ , _ , prodˢₕ₂
  Matching→⇒ᵥ prodrecₑ (_ ∙ ok) = _ , _ , _ , prodʷₕ ok
  Matching→⇒ᵥ natrecₑ₀ _ = _ , _ , _ , zeroₕ
  Matching→⇒ᵥ natrecₑ₊ (natrecₑ ok ∙ ok′) = _ , _ , _ , sucₕ ok′ ok
  Matching→⇒ᵥ unitrecₑ _ = _ , _ , _ , starʷₕ
  Matching→⇒ᵥ (unitrec-η η) _ = _ , _ , _ , unitrec-ηₕ η
  Matching→⇒ᵥ Jₑ _ = _ , _ , _ , rflₕⱼ
  Matching→⇒ᵥ Kₑ _ = _ , _ , _ , rflₕₖ
  Matching→⇒ᵥ []-congₑ _ = _ , _ , _ , rflₕₑ

opaque

  -- States reducing with the reduction for values have a matching
  -- head and stack

  ⇒ᵥ→Matching :
    ⟨ H , t , ρ , S ⟩ ⇒ᵥ s →
    Matching t S
  ⇒ᵥ→Matching liftₕ = lowerₑ
  ⇒ᵥ→Matching (lamₕ _) = ∘ₑ
  ⇒ᵥ→Matching prodˢₕ₁ = fstₑ
  ⇒ᵥ→Matching prodˢₕ₂ = sndₑ
  ⇒ᵥ→Matching (prodʷₕ _) = prodrecₑ
  ⇒ᵥ→Matching zeroₕ = natrecₑ₀
  ⇒ᵥ→Matching (sucₕ _ _) = natrecₑ₊
  ⇒ᵥ→Matching starʷₕ = unitrecₑ
  ⇒ᵥ→Matching (unitrec-ηₕ η) = unitrec-η η
  ⇒ᵥ→Matching rflₕⱼ = Jₑ
  ⇒ᵥ→Matching rflₕₖ = Kₑ
  ⇒ᵥ→Matching rflₕₑ = []-congₑ

opaque

  -- A variant of the previous property

  ¬Matching→¬⇒̬ :
    ¬ Matching t S
    → ⟨ H , t , ρ , S ⟩ ⇒ᵥ s → ⊥
  ¬Matching→¬⇒̬ ¬m d = ¬m (⇒ᵥ→Matching d)

opaque

  -- A kind of inversion lemma for Final
  -- There are three different reasons a state can be Final:
  -- 1. It has a variable in head position but lookup does not succeed
  --    (for the number of copies matching the current stack
  --    multiplicity).
  -- 1b. It has a level of the form t ⊔ u in head position.
  -- 2. It has a value in head position, the stack is not empty and it
  --    is not the case that the head matches the stack and that the
  --    stack multiplicity does not exist.
  -- 3. It has a value in head position and the stack is empty.

  Final-reasons :
      ∀ t → Final ⟨ H , t , ρ , S ⟩ →
      ((∃ λ x → t ≡ var x ×
         (∀ {p n H′} {c : Entry _ n} → ∣ S ∣≡ p → H ⊢ wkVar ρ x ↦[ p ] c ⨾ H′ → ⊥)) ⊎
      (∃₂ λ u v → t ≡ u supᵘ v)) ⊎
      (∃₂ λ e S′ → S ≡ e ∙ S′ × Value t × ¬ (Matching t S × ∃ ∣ S ∣≡_)) ⊎
      Value t × S ≡ ε

  Final-reasons = λ where
      (var x) ¬d → inj₁ (inj₁ (_ , refl , λ x y → ¬d (⇾ₑ (var x y))))
      Level ¬d → inj₂ (lemma Levelᵥ ¬d)
      zeroᵘ ¬d → inj₂ (lemma zeroᵘᵥ ¬d)
      (sucᵘ t) ¬d → inj₂ (lemma sucᵘᵥ ¬d)
      (t supᵘ u) ¬d → inj₁ (inj₂ (_ , _ , refl))
      (Lift t A) ¬d → inj₂ (lemma Liftᵥ ¬d)
      (lift t) ¬d → inj₂ (lemma liftᵥ ¬d)
      (lower t) ¬d → ⊥-elim (¬d (⇾ₑ′ lowerₕ))
      (U x) ¬d → inj₂ (lemma Uᵥ ¬d)
      (ΠΣ⟨ b ⟩ p , q ▷ t ▹ t₁) ¬d → inj₂ (lemma ΠΣᵥ ¬d)
      (lam p t) ¬d → inj₂ (lemma lamᵥ ¬d)
      (t ∘⟨ p ⟩ t₁) ¬d → ⊥-elim (¬d (⇾ₑ′ appₕ))
      (prod x p t t₁) ¬d → inj₂ (lemma prodᵥ ¬d)
      (fst p t) ¬d → ⊥-elim (¬d (⇾ₑ′ fstₕ))
      (snd p t) ¬d → ⊥-elim (¬d (⇾ₑ′ sndₕ))
      (prodrec r p q t t₁ t₂) ¬d → ⊥-elim (¬d (⇾ₑ′ prodrecₕ))
      ℕ ¬d → inj₂ (lemma ℕᵥ ¬d)
      zero ¬d → inj₂ (lemma zeroᵥ ¬d)
      (suc t) ¬d → inj₂ (lemma sucᵥ ¬d)
      (natrec p q r t t₁ t₂ t₃) ¬d → ⊥-elim (¬d (⇾ₑ′ natrecₕ))
      (Unit x) ¬d → inj₂ (lemma Unitᵥ ¬d)
      (star x) ¬d → inj₂ (lemma starᵥ ¬d)
      (unitrec p q t t₁ t₂) ¬d →
        case Unitʷ-η? of λ where
          (yes η) → inj₂ (lemma (unitrec-ηᵥ η) ¬d)
          (no no-η) → ⊥-elim (¬d (⇾ₑ′ (unitrecₕ no-η)))
      Empty ¬d → inj₂ (lemma Emptyᵥ ¬d)
      (emptyrec p t t₁) ¬d → ⊥-elim (¬d (⇾ₑ′ emptyrecₕ))
      (Id t t₁ t₂) ¬d → inj₂ (lemma Idᵥ ¬d)
      rfl ¬d → inj₂ (lemma rflᵥ ¬d)
      (J p q t t₁ t₂ t₃ t₄ t₅) ¬d → ⊥-elim (¬d (⇾ₑ′ Jₕ))
      (K p t t₁ t₂ t₃ t₄) ¬d → ⊥-elim (¬d (⇾ₑ′ Kₕ))
      ([]-cong _ _ _ _ _ _) ¬d → ⊥-elim (¬d (⇾ₑ′ []-congₕ))
        where
        lemma′ :
          Value t → Final ⟨ H , t , ρ , e ∙ S ⟩ →
          ¬ (Matching t (e ∙ S) × ∃ ∣ e ∙ S ∣≡_)
        lemma′ liftᵥ ¬d (lowerₑ , _ , _) =
          ¬d (⇒ᵥ liftₕ)
        lemma′ lamᵥ ¬d (∘ₑ , _ , _ ∙ ∣S∣≡) =
          ¬d (⇒ᵥ lamₕ ∣S∣≡)
        lemma′ zeroᵥ ¬d (natrecₑ₀ , _ , _) =
          ¬d (⇒ᵥ zeroₕ)
        lemma′ sucᵥ ¬d (natrecₑ₊ , _ , natrecₑ ∣nr∣≡ ∙ ∣S∣≡) =
          ¬d (⇒ᵥ sucₕ ∣S∣≡ ∣nr∣≡)
        lemma′ starᵥ ¬d (unitrecₑ , _ , _) =
          ¬d (⇒ᵥ starʷₕ)
        lemma′ prodᵥ ¬d (prodrecₑ , _ , _ ∙ ∣S∣≡) =
          ¬d (⇒ᵥ prodʷₕ ∣S∣≡)
        lemma′ prodᵥ ¬d (fstₑ , _ , _) =
          ¬d (⇒ᵥ prodˢₕ₁)
        lemma′ prodᵥ ¬d (sndₑ , _ , _) =
          ¬d (⇒ᵥ prodˢₕ₂)
        lemma′ rflᵥ ¬d (Jₑ , _ , _) =
          ¬d (⇒ᵥ rflₕⱼ)
        lemma′ rflᵥ ¬d (Kₑ , _ , _) =
          ¬d (⇒ᵥ rflₕₖ)
        lemma′ rflᵥ ¬d ([]-congₑ , _ , _) =
          ¬d (⇒ᵥ rflₕₑ)
        lemma′ Levelᵥ ¬d (() , _ , _)
        lemma′ zeroᵘᵥ ¬d (() , _ , _)
        lemma′ sucᵘᵥ ¬d (() , _ , _)
        lemma′ Liftᵥ ¬d (() , _ , _)
        lemma′ Uᵥ ¬d (() , _ , _)
        lemma′ ΠΣᵥ ¬d (() , _ , _)
        lemma′ ℕᵥ ¬d (() , _ , _)
        lemma′ Unitᵥ ¬d (() , _ , _)
        lemma′ Emptyᵥ ¬d (() , _ , _)
        lemma′ Idᵥ ¬d (() , _ , _)
        lemma′ (unitrec-ηᵥ x) ¬d _ =
          ¬d (⇒ᵥ unitrec-ηₕ x)
        lemma : ∀ {S : Stack m} → Value t → Final ⟨ H , t , ρ , S ⟩ →
                (∃₂ λ e S′ → S ≡ e ∙ S′ × Value t × ¬ (Matching t S × ∃ ∣ S ∣≡_)) ⊎
                Value t × S ≡ ε
        lemma {S = ε} v _ = inj₂ (v , refl)
        lemma {S = e ∙ S} v ¬d = inj₁ (_ , _ , refl , v , lemma′ v ¬d)

  opaque

    -- A variant of the above property.

    ⇘-reasons :
      s ⇘ ⟨ H , t , ρ , S ⟩ →
      ((∃ λ x → t ≡ var x ×
         (∀ {p n H′} {c : Entry _ n} → ∣ S ∣≡ p → H ⊢ wkVar ρ x ↦[ p ] c ⨾ H′ → ⊥)) ⊎
      (∃₂ λ u v → t ≡ u supᵘ v)) ⊎
      (∃₂ λ e S′ → S ≡ e ∙ S′ × Value t × ¬ (Matching t S × (∃ ∣ S ∣≡_))) ⊎
      Value t × S ≡ ε
    ⇘-reasons (d , ¬d) = Final-reasons _ ¬d

opaque

  -- A kind of inversion lemma for Final when having natrec tokens on
  -- the stack implies that the usage rule for natrec with an nr function
  -- is used.
  --
  -- In this case there are three different reasons a state can be Final:
  -- 1. It has a variable in head position but lookup does not succeed
  --    (for the number of copies matching the current stack
  --    multiplicity).
  -- 1b. It has a level of the form t ⊔ u in head position.
  -- 2. It has a value in head position, the stack is not empty and the
  --    head does not match the stack.
  -- 3. It has a value in head position and the stack is empty.

  nr∉-Final-reasons :
      ∀ t → (∀ {p r} → natrec p , r ∈ S → Nr-available) →
      Final ⟨ H , t , ρ , S ⟩ →
      ((∃ λ x → t ≡ var x ×
         (∀ {p n H′} {c : Entry _ n} → ∣ S ∣≡ p → H ⊢ wkVar ρ x ↦[ p ] c ⨾ H′ → ⊥)) ⊎
      (∃₂ λ u v → t ≡ u supᵘ v)) ⊎
      (∃₂ λ e S′ → S ≡ e ∙ S′ × Value t × ¬ Matching t S) ⊎
      Value t × S ≡ ε
  nr∉-Final-reasons t has-nr ¬d =
    case Final-reasons t ¬d of λ where
      (inj₁ x) → inj₁ x
      (inj₂ (inj₁ (e , S′ , S≡ , v , prop))) →
        inj₂ (inj₁ (e , S′ , S≡ , v , λ m → prop (m , ∣∣≡ has-nr)))
      (inj₂ (inj₂ x)) → inj₂ (inj₂ x)

opaque

  -- A variant of the above where the stack is assumed to not contain
  -- any natrecₑ tokens.
  --
  -- In this case there are three different reasons a state can be Final:
  -- 1. It has a variable in head position but lookup does not succeed
  --    (for the number of copies matching the current stack
  --    multiplicity).
  -- 1b. It has a level of the form t ⊔ u in head position.
  -- 2. It has a value in head position, the stack is not empty and the
  --    head does not match the stack.
  -- 3. It has a value in head position and the stack is empty.

  nr∉-Final-reasons′ :
      ∀ t → (∀ {p r} → natrec p , r ∈ S → ⊥) →
      Final ⟨ H , t , ρ , S ⟩ →
      ((∃ λ x → t ≡ var x ×
         (∀ {p n H′} {c : Entry _ n} → ∣ S ∣≡ p → H ⊢ wkVar ρ x ↦[ p ] c ⨾ H′ → ⊥)) ⊎
      (∃₂ λ u v → t ≡ u supᵘ v)) ⊎
      (∃₂ λ e S′ → S ≡ e ∙ S′ × Value t × ¬ Matching t S) ⊎
      Value t × S ≡ ε
  nr∉-Final-reasons′ t nr∉ ¬d =
    nr∉-Final-reasons t (⊥-elim ∘→ nr∉) ¬d

opaque

  -- Values do not reduce with the reduction for elims.

  Value-¬⇒ₑ : Value t → ⟨ H , t , ρ , S ⟩ ⇒ₑ s → ⊥
  Value-¬⇒ₑ () lowerₕ
  Value-¬⇒ₑ () appₕ
  Value-¬⇒ₑ () fstₕ
  Value-¬⇒ₑ () sndₕ
  Value-¬⇒ₑ () prodrecₕ
  Value-¬⇒ₑ () natrecₕ
  Value-¬⇒ₑ (unitrec-ηᵥ η) (unitrecₕ no-η) = no-η η
  Value-¬⇒ₑ () emptyrecₕ
  Value-¬⇒ₑ () Jₕ
  Value-¬⇒ₑ () Kₕ
  Value-¬⇒ₑ () []-congₕ

opaque

  -- Values that reduce do so with the reduction for values

  Value-⇾→⇒ᵥ : Value t → ⟨ H , t , ρ , S ⟩ ⇾ s′ → ⟨ H , t , ρ , S ⟩ ⇒ᵥ s′
  Value-⇾→⇒ᵥ v (⇾ₑ′ d) = ⊥-elim (Value-¬⇒ₑ v d)
  Value-⇾→⇒ᵥ () (⇾ₑ (var _ _))
  Value-⇾→⇒ᵥ _ (⇒ᵥ d) = d

opaque

  -- Normal form states that reduce do so with the reduction for values

  Normal-⇾→⇒ᵥ : Normal s → s ⇾ s′ → s ⇒ᵥ s′
  Normal-⇾→⇒ᵥ (val v) d = Value-⇾→⇒ᵥ v d
  Normal-⇾→⇒ᵥ (var x) (⇾ₑ d) =
    let _ , _ , _ , d′ = ⇾ₑ-inv-var d
    in  ⊥-elim (¬↦∧↦● (↦[]→↦ d′) x)
  Normal-⇾→⇒ᵥ (var _) (⇒ᵥ ())
  Normal-⇾→⇒ᵥ sup (⇾ₑ′ ())
  Normal-⇾→⇒ᵥ sup (⇒ᵥ ())
