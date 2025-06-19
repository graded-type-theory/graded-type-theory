------------------------------------------------------------------------
-- Properties of the heap reduction relation.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Variant

module Graded.Heap.Reduction.Properties
  {a} {M : Set a} {𝕄 : Modality M}
  (type-variant : Type-variant)
  (UR : Usage-restrictions 𝕄)
  (open Modality 𝕄)
  ⦃ _ : Has-nr M semiring-with-meet ⦄
  ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
  where

open Type-variant type-variant

open import Tools.Bool
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+; 2+; Nat-set)
open import Tools.PropositionalEquality
open import Tools.Product as Σ
open import Tools.Relation
open import Tools.Sum

open import Definition.Untyped M
open import Definition.Untyped.Names-below M

open import Graded.Modality.Nr-instances

open import Graded.Heap.Untyped type-variant UR
open import Graded.Heap.Untyped.Properties type-variant UR
open import Graded.Heap.Reduction type-variant UR
open import Graded.Heap.Reduction.Inversion type-variant UR

private variable
  m n m′ n′ m″ n″ k : Nat
  t t′ u A : Term _
  H H′ H″ H‴ H₁ H₂ : Heap _ _
  ρ ρ′ ρ″ : Wk _ _
  e : Elim _
  S S′ : Stack _
  p p′ q r r′ : M
  s s′ s″ s₁ s₂ : State _ _ _
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

  ⇒ₑ-det : s ⇒ₑ s′ → s ⇒ₑ s″ → s′ ≡ s″
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
  ⇾ₑ-det {s′ = record{}} d (var x′) =
    case ⇾ₑ-inv-var d of λ {
      (refl , x) →
    case lookup-det x x′ of λ {
      (refl , refl , refl , refl) →
    refl , refl }}
  ⇾ₑ-det (⇒ₑ d)  (⇒ₑ d′) = refl , ⇒ₑ-det d d′
  ⇾ₑ-det (var _) (⇒ₑ ())

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
  ⇢ₑ-det (⇒ₑ d)  (⇒ₑ d′) = refl , ⇒ₑ-det d d′
  ⇢ₑ-det (var _) (⇒ₑ ())
opaque

  -- The reduction relation for values is deterministic

  ⇒ᵥ-det : {s′ : State k m n} {s″ : State k m′ n′}
         → (d : s ⇒ᵥ s′) (d′ : s ⇒ᵥ s″)
         → Σ (m ≡ m′) λ m≡m′ → Σ (n ≡ n′) λ n≡n′ →
            subst₂ (State k) m≡m′ n≡n′ s′ ≡ s″
  ⇒ᵥ-det d lamₕ = ⇒ᵥ-inv-lam-∘ₑ d
  ⇒ᵥ-det d prodˢₕ₁ = ⇒ᵥ-inv-prodˢ-fstₑ d
  ⇒ᵥ-det d prodˢₕ₂ = ⇒ᵥ-inv-prodˢ-sndₑ d
  ⇒ᵥ-det d prodʷₕ = ⇒ᵥ-inv-prodʷ-prodrecₑ d
  ⇒ᵥ-det d zeroₕ = ⇒ᵥ-inv-zero-natrecₑ d
  ⇒ᵥ-det d sucₕ = ⇒ᵥ-inv-suc-natrecₑ d
  ⇒ᵥ-det d starʷₕ = ⇒ᵥ-inv-starʷ-unitrecₑ d .proj₂
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
  not-⇒ᵥ-and-⇒ₑ lamₕ d = ⇒ₑ-inv-lam d
  not-⇒ᵥ-and-⇒ₑ prodˢₕ₁ d = ⇒ₑ-inv-prod d
  not-⇒ᵥ-and-⇒ₑ prodˢₕ₂ d = ⇒ₑ-inv-prod d
  not-⇒ᵥ-and-⇒ₑ prodʷₕ d = ⇒ₑ-inv-prod d
  not-⇒ᵥ-and-⇒ₑ zeroₕ d = ⇒ₑ-inv-zero d
  not-⇒ᵥ-and-⇒ₑ sucₕ d = ⇒ₑ-inv-suc d
  not-⇒ᵥ-and-⇒ₑ starʷₕ d = ⇒ₑ-inv-star d
  not-⇒ᵥ-and-⇒ₑ (unitrec-ηₕ η) d = ⇒ₑ-inv-unitrec-η η d
  not-⇒ᵥ-and-⇒ₑ rflₕⱼ d = ⇒ₑ-inv-rfl d
  not-⇒ᵥ-and-⇒ₑ rflₕₖ d = ⇒ₑ-inv-rfl d
  not-⇒ᵥ-and-⇒ₑ rflₕₑ d = ⇒ₑ-inv-rfl d


opaque

  not-⇒ᵥ-and-⇾ₑ : s ⇒ᵥ s′ → s ⇾ₑ s″ → ⊥
  not-⇒ᵥ-and-⇾ₑ d  (⇒ₑ d′) = not-⇒ᵥ-and-⇒ₑ d d′
  not-⇒ᵥ-and-⇾ₑ () (var _)

opaque

  not-⇒ᵥ-and-⇢ₑ : s ⇒ᵥ s′ → s ⇢ₑ s″ → ⊥
  not-⇒ᵥ-and-⇢ₑ d (var x) = ⇒ᵥ-inv-var d
  not-⇒ᵥ-and-⇢ₑ d (⇒ₑ d′) = not-⇒ᵥ-and-⇒ₑ d d′

opaque

  -- A state cannot reduce in both ⇒ₙ and ⇒ᵥ

  not-⇒ₙ-and-⇒ᵥ : s ⇒ₙ s′ → s ⇒ᵥ s″ → ⊥
  not-⇒ₙ-and-⇒ᵥ (sucₕ {ℓ = 0} x) d =
    case ⇒ᵥ-inv-suc d of λ {
      (_ , _ , _ , _ , _ , _ , _ , _ , _ , () , _)}
  not-⇒ₙ-and-⇒ᵥ (sucₕ {ℓ = 1+ ℓ} x) d =
    case ⇒ᵥ-inv-suc d of λ {
      (_ , _ , _ , _ , _ , _ , _ , _ , _ , () , _)}
  not-⇒ₙ-and-⇒ᵥ (numₕ zeroₙ) d =
    case ⇒ᵥ-inv-zero d of λ {
      (_ , _ , _ , _ , _ , _ , _ , _ , _ , () , _)}
  not-⇒ₙ-and-⇒ᵥ (numₕ (sucₙ x)) d =
    case ⇒ᵥ-inv-suc d of λ {
      (_ , _ , _ , _ , _ , _ , _ , _ , _ , () , _)}

opaque

  -- A state cannot reduce in both ⇒ₙ and ⇾ₑ

  not-⇒ₙ-and-⇒ₑ : s ⇒ₙ s′ → s ⇒ₑ s″ → ⊥
  not-⇒ₙ-and-⇒ₑ (sucₕ x) d = ⇒ₑ-inv-suc d
  not-⇒ₙ-and-⇒ₑ (numₕ zeroₙ) d = ⇒ₑ-inv-zero d
  not-⇒ₙ-and-⇒ₑ (numₕ (sucₙ x)) d = ⇒ₑ-inv-suc d

opaque

  -- A state cannot reduce in both ⇒ₙ and ⇾ₑ

  not-⇒ₙ-and-⇾ₑ : s ⇒ₙ s′ → s ⇾ₑ s″ → ⊥
  not-⇒ₙ-and-⇾ₑ d (var _) = ⇒ₙ-inv-var d
  not-⇒ₙ-and-⇾ₑ d (⇒ₑ d′) = not-⇒ₙ-and-⇒ₑ d d′

opaque

  -- The small-step heap semantics is deterministic.

  ⇾-det : {s′ : State k m n} {s″ : State k m′ n′}
        → (d : s ⇾ s′) (d′ : s ⇾ s″)
        → Σ (m ≡ m′) λ m≡m′ →
          Σ (n ≡ n′) λ n≡n′ →
            subst₂ (State k) m≡m′ n≡n′ s′ ≡ s″
  ⇾-det (⇾ₑ d) (⇾ₑ d′) =
    case ⇾ₑ-det d d′ of λ where
      (refl , refl) → refl , refl , refl
  ⇾-det (⇒ᵥ d) (⇒ᵥ d′) = ⇒ᵥ-det d d′
  ⇾-det (⇾ₑ d) (⇒ᵥ d′) =
    ⊥-elim (not-⇒ᵥ-and-⇾ₑ d′ d)
  ⇾-det (⇒ᵥ d) (⇾ₑ d′) =
    ⊥-elim (not-⇒ᵥ-and-⇾ₑ d d′)

opaque

  -- The small-step heap semantics is deterministic.

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

  -- The small-step heap semantics is deterministic.

  ↠-det : {s′ : State k m n} {s″ : State k m′ n′}
        → (d : s ↠ s′) (d′ : s ↠ s″)
        → Σ (m ≡ m′) λ m≡m′ →
          Σ (n ≡ n′) λ n≡n′ →
            subst₂ (State k) m≡m′ n≡n′ s′ ≡ s″
  ↠-det (⇾ₑ d) (⇾ₑ d′) =
    case ⇾ₑ-det d d′ of λ where
      (refl , refl) → refl , refl , refl
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

  -- The normalising reduction preserves equality
  -- in a certain way

  ⇒ₑ-⦅⦆-≡ : s ⇒ₑ s′ → ⦅ s ⦆ ≡ ⦅ s′ ⦆
  ⇒ₑ-⦅⦆-≡ appₕ = refl
  ⇒ₑ-⦅⦆-≡ fstₕ = refl
  ⇒ₑ-⦅⦆-≡ sndₕ = refl
  ⇒ₑ-⦅⦆-≡ prodrecₕ = refl
  ⇒ₑ-⦅⦆-≡ natrecₕ = refl
  ⇒ₑ-⦅⦆-≡ (unitrecₕ x) = refl
  ⇒ₑ-⦅⦆-≡ emptyrecₕ = refl
  ⇒ₑ-⦅⦆-≡ Jₕ = refl
  ⇒ₑ-⦅⦆-≡ Kₕ = refl
  ⇒ₑ-⦅⦆-≡ []-congₕ = refl

opaque

  -- The normalising reduction preserves equality
  -- in a certain way

  ⇾ₑ-⦅⦆-≡ : s ⇾ₑ s′ → ⦅ s ⦆ ≡ ⦅ s′ ⦆
  ⇾ₑ-⦅⦆-≡ {s = ⟨ _ , _ , _ , S ⟩} (var d) =
    trans (⦅⦆ˢ-cong S (heapSubstVar d))
      (cong (λ x → ⦅ S ⦆ˢ _ [ x ]) (heapUpdateSubst d))
  ⇾ₑ-⦅⦆-≡ (⇒ₑ d) = ⇒ₑ-⦅⦆-≡ d

opaque

  -- The normalising reduction preserves equality
  -- in a certain way

  ⇾ₑ*-⦅⦆-≡ : s ⇾ₑ* s′ → ⦅ s ⦆ ≡ ⦅ s′ ⦆
  ⇾ₑ*-⦅⦆-≡ id = refl
  ⇾ₑ*-⦅⦆-≡ (x ⇨ d) = trans (⇾ₑ-⦅⦆-≡ x) (⇾ₑ*-⦅⦆-≡ d)

opaque

  -- The normalising reduction preserves equality
  -- in a certain way

  ⇢ₑ-⦅⦆-≡ : s ⇢ₑ s′ → ⦅ s ⦆ ≡ ⦅ s′ ⦆
  ⇢ₑ-⦅⦆-≡ {s = ⟨ _ , _ , _ , S ⟩} (var d) = ⦅⦆ˢ-cong S (heapSubstVar′ d)
  ⇢ₑ-⦅⦆-≡ (⇒ₑ d) = ⇒ₑ-⦅⦆-≡ d

-- opaque

--   ⇒ₙ*-⦅⦆-≡ : s ⇒ₙ* s′ → ⦅ s ⦆ ≡ ⦅ s′ ⦆
--   ⇒ₙ*-⦅⦆-≡ id = refl
--   ⇒ₙ*-⦅⦆-≡ (x ⇨ d) = trans (⇒ₙ-⦅⦆-≡ x) (⇒ₙ*-⦅⦆-≡ d)


opaque

  -- The reduction evaluating numerals preserves equality
  -- in a certain way

  ⇒ₙ-⦅⦆-≡ : s ⇒ₙ s′ → ⦅ s ⦆ ≡ ⦅ s′ ⦆
  ⇒ₙ-⦅⦆-≡ (sucₕ x) = refl
  ⇒ₙ-⦅⦆-≡ (numₕ x) = refl

opaque

  -- Lifting a normalising reduction to a larger heap

  wk1-⇒ₑ : ⟨ H , t , ρ , S ⟩ ⇒ₑ ⟨ H′ , t′ , ρ′ , S′ ⟩
          → ⟨ H ∙ c , t , step ρ , wk1ˢ S ⟩ ⇒ₑ ⟨ H′ ∙ c , t′ , step ρ′ , wk1ˢ S′ ⟩
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

-- opaque

--   -- Lifting a normalising reduction to a larger heap

--   wk1-⇾ₑ : ⟨ H , t , ρ , S ⟩ ⇾ₑ ⟨ H′ , t′ , ρ′ , S′ ⟩
--          → ⟨ H ∙ c , t , step ρ , wk1ˢ S ⟩ ⇾ₑ ⟨ H′ ∙ c , t′ , step ρ′ , wk1ˢ S′ ⟩
--   wk1-⇾ₑ {S} (var d) =
--     var (subst (_ ⊢ _ ↦[_] _ ⨾ _) (wk-∣S∣ (step id) S) (there d))
--   wk1-⇾ₑ (⇒ₑ d) = ⇒ₑ (wk1-⇒ₑ d)

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

-- opaque

--   -- Lifting a normalising reduction to a larger heap

--   wk1●-⇾ₑ : ⟨ H , t , ρ , S ⟩ ⇾ₑ ⟨ H′ , t′ , ρ′ , S′ ⟩
--           → ⟨ H ∙● , t , step ρ , wk1ˢ S ⟩ ⇾ₑ ⟨ H′ ∙● , t′ , step ρ′ , wk1ˢ S′ ⟩
--   wk1●-⇾ₑ {S} (var d) =
--     var (subst (_ ⊢ _ ↦[_] _ ⨾ _) (wk-∣S∣ (step id) S) (there● d))
--   wk1●-⇾ₑ (⇒ₑ d) = ⇒ₑ wk1●-⇒ₑ d

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
  ++sucₛ-⇾ₑ {S} (var x) =
    var (subst (_ ⊢ _ ↦[_] _ ⨾ _) (sym (∣S++sucₛ∣≡∣S∣ S)) x)
  ++sucₛ-⇾ₑ (⇒ₑ x) = ⇒ₑ (++-⇒ₑ _ x)

opaque

  -- Extending the stack of a reduction with sucₛ

  ++sucₛ-⇒ᵥ : (d : ⟨ H , t , ρ , S ⟩ ⇒ᵥ ⟨ H′ , t′ , ρ′ , S′ ⟩)
            → ⟨ H , t , ρ , S ++ sucₛ k ⟩ ⇒ᵥ ⟨ H′ , t′ , ρ′ , S′ ++ sucₛ k ⟩
  ++sucₛ-⇒ᵥ {k} (lamₕ {H} {p} {t} {ρ} {u} {ρ′} {S}) =
    subst₂
      (λ x y →
         ⟨ H , lam p t , ρ , (∘ₑ p u ρ′ ∙ S) ++ sucₛ k ⟩ ⇒ᵥ
         ⟨ H ∙ (x · p , u , ρ′) , t , lift ρ , y ⟩)
      (∣S++sucₛ∣≡∣S∣ S) (wk-++sucₛ (step id) S) lamₕ
  ++sucₛ-⇒ᵥ prodˢₕ₁ = prodˢₕ₁
  ++sucₛ-⇒ᵥ prodˢₕ₂ = prodˢₕ₂
  ++sucₛ-⇒ᵥ {k} (prodʷₕ {H} {p} {t₁} {t₂} {ρ} {r} {q} {A} {u} {ρ′} {S}) =
    subst₂
      (λ x y →
         ⟨ H , prodʷ p t₁ t₂ , ρ , (prodrecₑ r p q A u ρ′ ∙ S) ++ sucₛ k ⟩ ⇒ᵥ
         ⟨ H ∙ (x · r · p , t₁ , ρ) ∙ (x · r , t₂ , step ρ) , u , liftn ρ′ 2 , y ⟩)
      (∣S++sucₛ∣≡∣S∣ S) (wk-++sucₛ (step (step id)) S) prodʷₕ
  ++sucₛ-⇒ᵥ zeroₕ = zeroₕ
  ++sucₛ-⇒ᵥ {k} (sucₕ {H} {t} {ρ} {p} {q} {r} {A} {z} {s} {ρ′} {S}) =
    subst₂
      (λ x y →
        ⟨ H , suc t , ρ , natrecₑ p q r A z s ρ′ ∙ S ++ sucₛ k ⟩ ⇒ᵥ
        ⟨ H ∙ (x · nr₂ p r , t , ρ) ∙ (x · r , _ , lift ρ′) , s , liftn ρ′ 2 , y ⟩)
      (∣S++sucₛ∣≡∣S∣ S) (wk-++sucₛ (step (step id)) S) sucₕ
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

  -- Evaluation in _⇒ᵥ_ behaves the same under equal heaps

  ~ʰ-⇒ᵥ : ⟨ H , t , ρ , S ⟩ ⇒ᵥ ⟨ H′ , t′ , ρ′ , S′ ⟩ → H ~ʰ H″
        → ∃ λ H‴ → ⟨ H″ , t , ρ , S ⟩ ⇒ᵥ ⟨ H‴ , t′ , ρ′ , S′ ⟩ × H′ ~ʰ H‴
  ~ʰ-⇒ᵥ lamₕ H~H″           = _ , lamₕ , H~H″ ∙ _
  ~ʰ-⇒ᵥ prodˢₕ₁ H~H″         = _ , prodˢₕ₁ , H~H″
  ~ʰ-⇒ᵥ prodˢₕ₂ H~H″         = _ , prodˢₕ₂ , H~H″
  ~ʰ-⇒ᵥ prodʷₕ H~H″         = _ , prodʷₕ , H~H″ ∙ _ ∙ _
  ~ʰ-⇒ᵥ zeroₕ H~H″          = _ , zeroₕ , H~H″
  ~ʰ-⇒ᵥ sucₕ H~H″           = _ , sucₕ , H~H″ ∙ _ ∙ _
  ~ʰ-⇒ᵥ starʷₕ H~H″         = _ , starʷₕ , H~H″
  ~ʰ-⇒ᵥ (unitrec-ηₕ η) H~H″ = _ , unitrec-ηₕ η , H~H″
  ~ʰ-⇒ᵥ rflₕⱼ H~H″          = _ , rflₕⱼ , H~H″
  ~ʰ-⇒ᵥ rflₕₖ H~H″          = _ , rflₕₖ , H~H″
  ~ʰ-⇒ᵥ rflₕₑ H~H″          = _ , rflₕₑ , H~H″

opaque

  -- Evaluation in _⇒ₑ_ behaves the same under a different heap
  -- Note that the heaps do not need to be equal

  ~ʰ-⇒ₑ : ⟨ H , t , ρ , S ⟩ ⇒ₑ ⟨ H′ , t′ , ρ′ , S′ ⟩
         → ⟨ H″ , t , ρ , S ⟩ ⇒ₑ ⟨ H″ , t′ , ρ′ , S′ ⟩
  ~ʰ-⇒ₑ appₕ            = appₕ
  ~ʰ-⇒ₑ fstₕ            = fstₕ
  ~ʰ-⇒ₑ sndₕ            = sndₕ
  ~ʰ-⇒ₑ prodrecₕ        = prodrecₕ
  ~ʰ-⇒ₑ natrecₕ         = natrecₕ
  ~ʰ-⇒ₑ (unitrecₕ no-η) = unitrecₕ no-η
  ~ʰ-⇒ₑ emptyrecₕ       = emptyrecₕ
  ~ʰ-⇒ₑ Jₕ              = Jₕ
  ~ʰ-⇒ₑ Kₕ              = Kₕ
  ~ʰ-⇒ₑ []-congₕ        = []-congₕ

opaque

  -- Evaluation in _⇢ₑ_ behaves the same under equal heaps when
  -- resource tracking is turned off.

  ~ʰ-⇢ₑ : ⟨ H , t , ρ , S ⟩ ⇢ₑ ⟨ H′ , t′ , ρ′ , S′ ⟩ → H ~ʰ H″
        → ⟨ H″ , t , ρ , S ⟩ ⇢ₑ ⟨ H″ , t′ , ρ′ , S′ ⟩
  ~ʰ-⇢ₑ (var d) H~H″ =
    var (~ʰ-lookup H~H″ d)
  ~ʰ-⇢ₑ (⇒ₑ d) H~H″ = ⇒ₑ (~ʰ-⇒ₑ d)


opaque

  -- Evaluation in _⇢ₙ_ behaves the same under different heaps.
  -- Note that the heaps do not need to be equal

  ~ʰ-⇒ₙ : ⟨ H , t , ρ , S ⟩ ⇒ₙ ⟨ H′ , t′ , ρ′ , S′ ⟩
        → ⟨ H″ , t , ρ , S ⟩ ⇒ₙ ⟨ H″ , t′ , ρ′ , S′ ⟩
  ~ʰ-⇒ₙ (sucₕ x) = sucₕ x
  ~ʰ-⇒ₙ (numₕ x) = numₕ x

opaque

  -- The non resource tracking reduction behaves the same on equal heaps

  ~ʰ-⇢ : ⟨ H , t , ρ , S ⟩ ⇢ ⟨ H′ , t′ , ρ′ , S′ ⟩ → H ~ʰ H″
       → ∃ λ H‴ → ⟨ H″ , t , ρ , S ⟩ ⇢ ⟨ H‴ , t′ , ρ′ , S′ ⟩ × H′ ~ʰ H‴
  ~ʰ-⇢ (⇢ₑ d) H~H″ =
    let d′ = ~ʰ-⇢ₑ d H~H″
    in  _ , ⇢ₑ d′ , subst (_~ʰ _) (⇢ₑ-Heap≡ d) H~H″
  ~ʰ-⇢ (⇒ᵥ d) H~H″ =
    let _ , d′ , H′~H‴ = ~ʰ-⇒ᵥ d H~H″
    in  _ , ⇒ᵥ d′ , H′~H‴

opaque

  -- The non resource tracking reduction behaves the same on equal heaps

  ~ʰ-⇢* :  ⟨ H , t , ρ , S ⟩ ⇢* ⟨ H′ , t′ , ρ′ , S′ ⟩ → H ~ʰ H″
        → ∃ λ H‴ → ⟨ H″ , t , ρ , S ⟩ ⇢* ⟨ H‴ , t′ , ρ′ , S′ ⟩ × H′ ~ʰ H‴
  ~ʰ-⇢* id H~H′ =
    _ , id , H~H′
  ~ʰ-⇢* (_⇨_ {s₂ = record{}} x d) H~H′ =
    case ~ʰ-⇢ x H~H′ of λ
      (_ , x′ , H~H″) →
    case ~ʰ-⇢* d H~H″ of λ
      (_ , d′ , H~H‴) →
    _ , (x′ ⇨ d′) , H~H‴

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

  Matching→⇒ᵥ :
    Matching t S →
    ∃₃ λ m n (s : State _ m n) → ⟨ H , t , ρ , S ⟩ ⇒ᵥ s
  Matching→⇒ᵥ ∘ₑ = _ , _ , _ , lamₕ
  Matching→⇒ᵥ fstₑ = _ , _ , _ , prodˢₕ₁
  Matching→⇒ᵥ sndₑ = _ , _ , _ , prodˢₕ₂
  Matching→⇒ᵥ prodrecₑ = _ , _ , _ , prodʷₕ
  Matching→⇒ᵥ natrecₑ₀ = _ , _ , _ , zeroₕ
  Matching→⇒ᵥ natrecₑ₊ = _ , _ , _ , sucₕ
  Matching→⇒ᵥ unitrecₑ = _ , _ , _ , starʷₕ
  Matching→⇒ᵥ (unitrec-η η) = _ , _ , _ , unitrec-ηₕ η
  Matching→⇒ᵥ Jₑ = _ , _ , _ , rflₕⱼ
  Matching→⇒ᵥ Kₑ = _ , _ , _ , rflₕₖ
  Matching→⇒ᵥ []-congₑ = _ , _ , _ , rflₕₑ

opaque

  ⇒ᵥ→Matching :
    ⟨ H , t , ρ , S ⟩ ⇒ᵥ s →
    Matching t S
  ⇒ᵥ→Matching lamₕ = ∘ₑ
  ⇒ᵥ→Matching prodˢₕ₁ = fstₑ
  ⇒ᵥ→Matching prodˢₕ₂ = sndₑ
  ⇒ᵥ→Matching prodʷₕ = prodrecₑ
  ⇒ᵥ→Matching zeroₕ = natrecₑ₀
  ⇒ᵥ→Matching sucₕ = natrecₑ₊
  ⇒ᵥ→Matching starʷₕ = unitrecₑ
  ⇒ᵥ→Matching (unitrec-ηₕ η) = unitrec-η η
  ⇒ᵥ→Matching rflₕⱼ = Jₑ
  ⇒ᵥ→Matching rflₕₖ = Kₑ
  ⇒ᵥ→Matching rflₕₑ = []-congₑ

opaque

  -- A kind of inversion lemma for Final.
  -- There are four different reasons why a state can be Final:
  -- 1. It has a variable in head position but lookup does not succeed.
  -- 2. It has a value in head position, the stack is not empty and the
  --    top of the stack does not match the head.
  -- 3. It has a value in head position and the stack is empty.
  -- 4. It has a name in head position.

  Final-reasons :
    ∀ t → Final ⟨ H , t , ρ , S ⟩ →
    (∃ λ x → t ≡ var x ×
       (∀ {n H′} {c : Entry _ n} → H ⊢ wkVar ρ x ↦[ ∣ S ∣ ] c ⨾ H′ → ⊥)) ⊎
    (∃₂ λ e S′ → S ≡ e ∙ S′ × Value t × (Matching t S → ⊥)) ⊎
    Value t × S ≡ ε ⊎
    (∃ λ α → t ≡ defn α)
  Final-reasons = λ where
    (defn _) _ → inj₂ (inj₂ (inj₂ (_ , refl)))
    (var x) ¬d → inj₁ (_ , refl , λ d → ¬d (⇾ₑ (var d)))
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
    (Unit x x₁) ¬d → inj₂ (lemma Unitᵥ ¬d)
    (star x x₁) ¬d → inj₂ (lemma starᵥ ¬d)
    (unitrec x p q t t₁ t₂) ¬d →
      case Unitʷ-η? of λ where
        (yes η) → inj₂ (lemma (unitrec-ηᵥ η) ¬d)
        (no no-η) → ⊥-elim (¬d (⇾ₑ′ (unitrecₕ no-η)))
    Empty ¬d → inj₂ (lemma Emptyᵥ ¬d)
    (emptyrec p t t₁) ¬d → ⊥-elim (¬d (⇾ₑ′ emptyrecₕ))
    (Id t t₁ t₂) ¬d → inj₂ (lemma Idᵥ ¬d)
    rfl ¬d → inj₂ (lemma rflᵥ ¬d)
    (J p q t t₁ t₂ t₃ t₄ t₅) ¬d → ⊥-elim (¬d (⇾ₑ′ Jₕ))
    (K p t t₁ t₂ t₃ t₄) ¬d → ⊥-elim (¬d (⇾ₑ′ Kₕ))
    ([]-cong x t t₁ t₂ t₃) ¬d → ⊥-elim (¬d (⇾ₑ′ []-congₕ))
      where
      lemma′ : Value t → Final ⟨ H , t , ρ , e ∙ S ⟩ → Matching t (e ∙ S) → ⊥
      lemma′ lamᵥ ¬d ∘ₑ = ¬d (⇒ᵥ lamₕ)
      lemma′ zeroᵥ ¬d natrecₑ₀ = ¬d (⇒ᵥ zeroₕ)
      lemma′ sucᵥ ¬d natrecₑ₊ = ¬d (⇒ᵥ sucₕ)
      lemma′ starᵥ ¬d unitrecₑ = ¬d (⇒ᵥ starʷₕ)
      lemma′ prodᵥ ¬d fstₑ = ¬d (⇒ᵥ prodˢₕ₁)
      lemma′ prodᵥ ¬d sndₑ = ¬d (⇒ᵥ prodˢₕ₂)
      lemma′ prodᵥ ¬d prodrecₑ = ¬d (⇒ᵥ prodʷₕ)
      lemma′ rflᵥ ¬d Jₑ = ¬d (⇒ᵥ rflₕⱼ)
      lemma′ rflᵥ ¬d Kₑ = ¬d (⇒ᵥ rflₕₖ)
      lemma′ rflᵥ ¬d []-congₑ = ¬d (⇒ᵥ rflₕₑ)
      lemma′ Uᵥ ¬d ()
      lemma′ ΠΣᵥ ¬d ()
      lemma′ ℕᵥ ¬d ()
      lemma′ Unitᵥ ¬d ()
      lemma′ Emptyᵥ ¬d ()
      lemma′ Idᵥ ¬d ()
      lemma′ (unitrec-ηᵥ x) ¬d t = ¬d (⇒ᵥ (unitrec-ηₕ x))
      lemma : ∀ {S : Stack m} → Value t → Final ⟨ H , t , ρ , S ⟩ →
              (∃₂ λ e S′ → S ≡ e ∙ S′ × Value t × (Matching t S → ⊥)) ⊎
              Value t × S ≡ ε ⊎
              (∃ λ α → t ≡ defn α)
      lemma {S = ε}     v _  = inj₂ (inj₁ (v , refl))
      lemma {S = e ∙ S} v ¬d = inj₁ (_ , _ , refl , v , lemma′ v ¬d)

opaque

  -- A variant of the above property.

  ⇘-reasons :
    s ⇘ ⟨ H , t , ρ , S ⟩ →
    (∃ λ x → t ≡ var x ×
       (∀ {n H′} {c : Entry _ n} → H ⊢ wkVar ρ x ↦[ ∣ S ∣ ] c ⨾ H′ → ⊥)) ⊎
    (∃₂ λ e S′ → S ≡ e ∙ S′ × Value t × (Matching t S → ⊥)) ⊎
    Value t × S ≡ ε ⊎
    (∃ λ α → t ≡ defn α)
  ⇘-reasons (d , ¬d) = Final-reasons _ ¬d

opaque

  Value-¬⇒ₑ : Value t → ⟨ H , t , ρ , S ⟩ ⇒ₑ s → ⊥
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

  Value-⇾→⇒ᵥ : Value t → ⟨ H , t , ρ , S ⟩ ⇾ s′ → ⟨ H , t , ρ , S ⟩ ⇒ᵥ s′
  Value-⇾→⇒ᵥ v (⇾ₑ′ d) = ⊥-elim (Value-¬⇒ₑ v d)
  Value-⇾→⇒ᵥ () (⇾ₑ (var _))
  Value-⇾→⇒ᵥ _ (⇒ᵥ d) = d

opaque

  Normal-⇾→⇒ᵥ : Normal s → s ⇾ s′ → s ⇒ᵥ s′
  Normal-⇾→⇒ᵥ (val v) d = Value-⇾→⇒ᵥ v d
  Normal-⇾→⇒ᵥ (var x) (⇾ₑ d) =
    ⊥-elim (¬↦∧↦● (↦[]→↦ (⇾ₑ-inv-var d .proj₂)) x)
  Normal-⇾→⇒ᵥ (var _) (⇒ᵥ ())

------------------------------------------------------------------------
-- Some properties related to the No-names variants

opaque

  -- No-namesₛ implies No-namesₛ′.

  →No-namesₛ′ : No-namesₛ s → No-namesₛ′ s
  →No-namesₛ′ {s = ⟨ _ , _ , _ , _ ⟩} = proj₁

opaque

  -- If there are no names in a given heap, then there are no names in
  -- terms obtained from the heap via the _⊢_↦_ form of lookup.

  No-names-⊢↦ : H ⊢ x ↦ (t , ρ) → No-namesʰ H → No-names t
  No-names-⊢↦ here        (_ ∙ t-nn) = t-nn
  No-names-⊢↦ (there x↦)  (H-nn ∙ _) = No-names-⊢↦ x↦ H-nn
  No-names-⊢↦ (there● x↦) (H-nn ∙●)  = No-names-⊢↦ x↦ H-nn

opaque

  -- If there are no names in a given heap, then there are no names in
  -- terms or heaps obtained from the heap via the _⊢_↦[_]_⨾_ form of
  -- lookup.

  No-names-⊢↦[]⨾ :
    H₁ ⊢ x ↦[ p ] t , ρ ⨾ H₂ → No-namesʰ H₁ →
    No-names t × No-namesʰ H₂
  No-names-⊢↦[]⨾ (here _) (H-nn ∙ t-nn) =
    t-nn , H-nn ∙ t-nn
  No-names-⊢↦[]⨾ (there x↦)  (H-nn ∙ t-nn) =
    Σ.map idᶠ (_∙ t-nn) (No-names-⊢↦[]⨾ x↦ H-nn)
  No-names-⊢↦[]⨾ (there● x↦) (H-nn ∙●) =
    Σ.map idᶠ _∙● (No-names-⊢↦[]⨾ x↦ H-nn)

-- No-namesₛ is preserved by various forms of reduction.

opaque

  No-namesₛ-⇒ₑ : s₁ ⇒ₑ s₂ → No-namesₛ s₁ → No-namesₛ s₂
  No-namesₛ-⇒ₑ appₕ ((H-nn , app nn₁ nn₂) , S-nn) =
    (H-nn , nn₁) , ∘ₑ nn₂ ∙ S-nn
  No-namesₛ-⇒ₑ fstₕ ((H-nn , fst nn) , S-nn) =
    (H-nn , nn) , fstₑ ∙ S-nn
  No-namesₛ-⇒ₑ sndₕ ((H-nn , snd nn) , S-nn) =
    (H-nn , nn) , sndₑ ∙ S-nn
  No-namesₛ-⇒ₑ prodrecₕ ((H-nn , prodrec nn₁ nn₂ nn₃) , S-nn) =
    (H-nn , nn₂) , prodrecₑ nn₁ nn₃ ∙ S-nn
  No-namesₛ-⇒ₑ natrecₕ ((H-nn , natrec nn₁ nn₂ nn₃ nn₄) , S-nn) =
    (H-nn , nn₄) , natrecₑ nn₁ nn₂ nn₃ ∙ S-nn
  No-namesₛ-⇒ₑ (unitrecₕ _) ((H-nn , unitrec nn₁ nn₂ nn₃) , S-nn) =
    (H-nn , nn₂) , unitrecₑ nn₁ nn₃ ∙ S-nn
  No-namesₛ-⇒ₑ emptyrecₕ ((H-nn , emptyrec nn₁ nn₂) , S-nn) =
    (H-nn , nn₂) , emptyrecₑ nn₁ ∙ S-nn
  No-namesₛ-⇒ₑ Jₕ ((H-nn , J nn₁ nn₂ nn₃ nn₄ nn₅ nn₆) , S-nn) =
    (H-nn , nn₆) , Jₑ nn₁ nn₂ nn₃ nn₄ nn₅ ∙ S-nn
  No-namesₛ-⇒ₑ Kₕ ((H-nn , K nn₁ nn₂ nn₃ nn₄ nn₅) , S-nn) =
    (H-nn , nn₅) , Kₑ nn₁ nn₂ nn₃ nn₄ ∙ S-nn
  No-namesₛ-⇒ₑ []-congₕ ((H-nn , []-cong nn₁ nn₂ nn₃ nn₄) , S-nn) =
    (H-nn , nn₄) , []-congₑ nn₁ nn₂ nn₃ ∙ S-nn

opaque

  No-namesₛ-⇾ₑ : s₁ ⇾ₑ s₂ → No-namesₛ s₁ → No-namesₛ s₂
  No-namesₛ-⇾ₑ (var x↦) ((H-nn , var) , S-nn) =
    let t-nn , H′-nn = No-names-⊢↦[]⨾ x↦ H-nn in
    (H′-nn , t-nn) , S-nn
  No-namesₛ-⇾ₑ (⇒ₑ s₁⇒ₑs₂) nn =
    No-namesₛ-⇒ₑ s₁⇒ₑs₂ nn

opaque

  No-namesₛ-⇾ₑ* : s₁ ⇾ₑ* s₂ → No-namesₛ s₁ → No-namesₛ s₂
  No-namesₛ-⇾ₑ* id                 = idᶠ
  No-namesₛ-⇾ₑ* (s₁⇾ₑs₂ ⇨ s₂⇾ₑ*s₃) =
    No-namesₛ-⇾ₑ* s₂⇾ₑ*s₃ ∘→ No-namesₛ-⇾ₑ s₁⇾ₑs₂

opaque

  No-namesₛ-⇢ₑ : s₁ ⇢ₑ s₂ → No-namesₛ s₁ → No-namesₛ s₂
  No-namesₛ-⇢ₑ (var x↦) ((H-nn , var) , S-nn) =
    (H-nn , No-names-⊢↦ x↦ H-nn) , S-nn
  No-namesₛ-⇢ₑ (⇒ₑ s₁⇒ₑs₂) nn =
    No-namesₛ-⇒ₑ s₁⇒ₑs₂ nn

opaque

  No-namesₛ-⇢ₑ* : s₁ ⇢ₑ* s₂ → No-namesₛ s₁ → No-namesₛ s₂
  No-namesₛ-⇢ₑ* id                 = idᶠ
  No-namesₛ-⇢ₑ* (s₁⇢ₑs₂ ⇨ s₂⇢ₑ*s₃) =
    No-namesₛ-⇢ₑ* s₂⇢ₑ*s₃ ∘→ No-namesₛ-⇢ₑ s₁⇢ₑs₂

opaque

  No-namesₛ-⇒ᵥ : s₁ ⇒ᵥ s₂ → No-namesₛ s₁ → No-namesₛ s₂
  No-namesₛ-⇒ᵥ lamₕ ((H-nn , lam nn₁) , ∘ₑ nn₂ ∙ S-nn) =
    (H-nn ∙ nn₂ , nn₁) , No-namesˢ-wk S-nn
  No-namesₛ-⇒ᵥ prodˢₕ₁ ((H-nn , prod nn _) , _ ∙ S-nn) =
    (H-nn , nn) , S-nn
  No-namesₛ-⇒ᵥ prodˢₕ₂ ((H-nn , prod _ nn) , _ ∙ S-nn) =
    (H-nn , nn) , S-nn
  No-namesₛ-⇒ᵥ prodʷₕ ((H-nn , prod nn₁ nn₂) , prodrecₑ _ nn₃ ∙ S-nn) =
    (H-nn ∙ nn₁ ∙ nn₂ , nn₃) , No-namesˢ-wk S-nn
  No-namesₛ-⇒ᵥ zeroₕ ((H-nn , _) , natrecₑ _ nn _ ∙ S-nn) =
    (H-nn , nn) , S-nn
  No-namesₛ-⇒ᵥ sucₕ ((H-nn , suc nn₁) , natrecₑ nn₂ nn₃ nn₄ ∙ S-nn) =
    (H-nn ∙ nn₁ ∙
       natrec (Names<-wk nn₂) (Names<-wk nn₃) (Names<-wk nn₄) var ,
     nn₄) ,
    No-namesˢ-wk S-nn
  No-namesₛ-⇒ᵥ starʷₕ ((H-nn , _) , unitrecₑ _ nn ∙ S-nn) =
    (H-nn , nn) , S-nn
  No-namesₛ-⇒ᵥ (unitrec-ηₕ _) ((H-nn , unitrec _ _ nn) , S-nn) =
    (H-nn , nn) , S-nn
  No-namesₛ-⇒ᵥ rflₕⱼ ((H-nn , _) , Jₑ _ _ _ nn _ ∙ S-nn) =
    (H-nn , nn) , S-nn
  No-namesₛ-⇒ᵥ rflₕₖ ((H-nn , _) , Kₑ _ _ _ nn ∙ S-nn) =
    (H-nn , nn) , S-nn
  No-namesₛ-⇒ᵥ rflₕₑ ((H-nn , _) , _ ∙ S-nn) =
    (H-nn , rfl) , S-nn

opaque

  No-namesₛ-⇒ₙ : s₁ ⇒ₙ s₂ → No-namesₛ s₁ → No-namesₛ s₂
  No-namesₛ-⇒ₙ (sucₕ _) ((H-nn , suc t-nn) , S-nn) =
    (H-nn , t-nn) , sucₑ ∙ S-nn
  No-namesₛ-⇒ₙ (numₕ _) ((H-nn , t-nn) , _ ∙ S-nn) =
    (H-nn , suc t-nn) , S-nn

opaque

  No-namesₛ-⇾ : s₁ ⇾ s₂ → No-namesₛ s₁ → No-namesₛ s₂
  No-namesₛ-⇾ (⇾ₑ s₁⇾ₑs₂) = No-namesₛ-⇾ₑ s₁⇾ₑs₂
  No-namesₛ-⇾ (⇒ᵥ s₁⇒ᵥs₂) = No-namesₛ-⇒ᵥ s₁⇒ᵥs₂

opaque

  No-namesₛ-↠ : s₁ ↠ s₂ → No-namesₛ s₁ → No-namesₛ s₂
  No-namesₛ-↠ (⇾ₑ s₁⇾ₑs₂) = No-namesₛ-⇾ₑ s₁⇾ₑs₂
  No-namesₛ-↠ (⇒ᵥ s₁⇒ᵥs₂) = No-namesₛ-⇒ᵥ s₁⇒ᵥs₂
  No-namesₛ-↠ (⇒ₙ s₁⇒ₙs₂) = No-namesₛ-⇒ₙ s₁⇒ₙs₂

opaque

  No-namesₛ-⇢ : s₁ ⇢ s₂ → No-namesₛ s₁ → No-namesₛ s₂
  No-namesₛ-⇢ (⇢ₑ s₁⇢ₑs₂) = No-namesₛ-⇢ₑ s₁⇢ₑs₂
  No-namesₛ-⇢ (⇒ᵥ s₁⇒ᵥs₂) = No-namesₛ-⇒ᵥ s₁⇒ᵥs₂

opaque

  No-namesₛ-⇾* : s₁ ⇾* s₂ → No-namesₛ s₁ → No-namesₛ s₂
  No-namesₛ-⇾* id               = idᶠ
  No-namesₛ-⇾* (s₁⇾s₂ ⇨ s₂⇾*s₃) =
    No-namesₛ-⇾* s₂⇾*s₃ ∘→ No-namesₛ-⇾ s₁⇾s₂

opaque

  No-namesₛ-↠* : s₁ ↠* s₂ → No-namesₛ s₁ → No-namesₛ s₂
  No-namesₛ-↠* id               = idᶠ
  No-namesₛ-↠* (s₁↠s₂ ⇨ s₂↠*s₃) =
    No-namesₛ-↠* s₂↠*s₃ ∘→ No-namesₛ-↠ s₁↠s₂

opaque

  No-namesₛ-⇢* : s₁ ⇢* s₂ → No-namesₛ s₁ → No-namesₛ s₂
  No-namesₛ-⇢* id               = idᶠ
  No-namesₛ-⇢* (s₁⇢s₂ ⇨ s₂⇢*s₃) =
    No-namesₛ-⇢* s₂⇢*s₃ ∘→ No-namesₛ-⇢ s₁⇢s₂

opaque

  No-namesₛ-⇘ : s₁ ⇘ s₂ → No-namesₛ s₁ → No-namesₛ s₂
  No-namesₛ-⇘ (s₁⇾*s₂ , _) = No-namesₛ-⇾* s₁⇾*s₂
