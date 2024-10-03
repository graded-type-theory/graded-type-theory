------------------------------------------------------------------------
-- Properties of the heap reduction relation.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Graded.Heap.Options
open import Definition.Typed.Variant

module Graded.Heap.Reduction.Properties
  {a} {M : Set a} {𝕄 : Modality M}
  (type-variant : Type-variant)
  (UR : Usage-restrictions 𝕄)
  (opts : Options)
  (open Modality 𝕄)
  ⦃ _ : Has-nr M semiring-with-meet ⦄
  ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
  where

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+; 2+; Nat-set)
open import Tools.PropositionalEquality
open import Tools.Product
open import Tools.Sum hiding (id; sym)

open import Definition.Untyped M
open import Graded.Modality.Nr-instances

open import Graded.Heap.Untyped type-variant UR
open import Graded.Heap.Untyped.Properties type-variant UR
open import Graded.Heap.Reduction type-variant UR opts
open import Graded.Heap.Reduction.Inversion type-variant UR opts

open Options opts

private variable
  m n m′ n′ m″ n″ k : Nat
  t t′ u A : Term _
  H H′ H″ H‴ : Heap _ _
  ρ ρ′ ρ″ : Wk _ _
  S S′ : Stack _
  p p′ q r r′ : M
  s s′ s″ : State _ _ _
  c : Entryₘ _ _
  x x′ : Fin _

opaque
  infixr 28 _⇨*_
  -- Concatenation of reduction

  _⇨*_ : s ⇒* s′ → s′ ⇒* s″ → s ⇒* s″
  id ⇨* d′ = d′
  (x ⇨ d) ⇨* d′ = x ⇨ (d ⇨* d′)

opaque
  infix 30 ⇒ₙ*_

  -- Lifting normalising reduction to main reduction

  ⇒ₙ*_ : s ⇒ₙ* s′ → s ⇒* s′
  ⇒ₙ* id = id
  ⇒ₙ* (x ⇨ d) = (⇒ₙ x) ⇨ (⇒ₙ* d)

------------------------------------------------------------------------
-- The heap semantics are deterministic

opaque

  -- The normalising reduction relation is deterministic

  ⇒ₙ-det : {s′ : State k m n} {s″ : State k m n′}
         → (d : s ⇒ₙ s′) (d′ : s ⇒ₙ s″)
         → Σ (n ≡ n′) λ n≡n′ →
            subst (State k m) n≡n′ s′ ≡ s″
  ⇒ₙ-det {s′ = record{}} d (varₕ x′) =
    case ⇒ₙ-inv-var d of λ {
      (refl , x) →
    case lookup-det x x′ of λ {
      (refl , refl , refl , refl) →
    refl , refl }}
  ⇒ₙ-det {s′ = record{}} d (varₕ′ x′) =
    case ⇒ₙ-inv-var′ d of λ {
      (refl , refl , x) →
    case lookup-det′ x x′ of λ {
      (refl , refl , refl) →
    refl , refl }}
  ⇒ₙ-det d appₕ = ⇒ₙ-inv-∘ d
  ⇒ₙ-det d fstₕ = ⇒ₙ-inv-fst d
  ⇒ₙ-det d sndₕ = ⇒ₙ-inv-snd d
  ⇒ₙ-det d prodrecₕ = ⇒ₙ-inv-prodrec d
  ⇒ₙ-det d natrecₕ = ⇒ₙ-inv-natrec d
  ⇒ₙ-det d (unitrecₕ x) = ⇒ₙ-inv-unitrec d
  ⇒ₙ-det d emptyrecₕ = ⇒ₙ-inv-emptyrec d
  ⇒ₙ-det d Jₕ = ⇒ₙ-inv-J d
  ⇒ₙ-det d Kₕ = ⇒ₙ-inv-K d
  ⇒ₙ-det d []-congₕ = ⇒ₙ-inv-[]-cong d

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

  ⇒ₛ-det : {s′ : State k m n} {s″ : State k m n}
         → (d : s ⇒ₛ s′) (d′ : s ⇒ₛ s″)
         → s′ ≡ s″
  ⇒ₛ-det d (sucₕ x) = ⇒ₛ-inv-suc x d .proj₂ .proj₂
  ⇒ₛ-det d (numₕ x) =
    case ⇒ₛ-inv-num x d of λ {
      (S , refl , refl) → refl }

opaque

  -- A state cannot reduce in both ⇒ᵥ and ⇒ₙ

  not-⇒ᵥ-and-⇒ₙ : s ⇒ᵥ s′ → s ⇒ₙ s″ → ⊥
  not-⇒ᵥ-and-⇒ₙ lamₕ d = ⇒ₙ-inv-lam d
  not-⇒ᵥ-and-⇒ₙ prodˢₕ₁ d = ⇒ₙ-inv-prod d
  not-⇒ᵥ-and-⇒ₙ prodˢₕ₂ d = ⇒ₙ-inv-prod d
  not-⇒ᵥ-and-⇒ₙ prodʷₕ d = ⇒ₙ-inv-prod d
  not-⇒ᵥ-and-⇒ₙ zeroₕ d = ⇒ₙ-inv-zero d
  not-⇒ᵥ-and-⇒ₙ sucₕ d = ⇒ₙ-inv-suc d
  not-⇒ᵥ-and-⇒ₙ starʷₕ d = ⇒ₙ-inv-star d
  not-⇒ᵥ-and-⇒ₙ (unitrec-ηₕ η) d = ⇒ₙ-inv-unitrec-η η d
  not-⇒ᵥ-and-⇒ₙ rflₕⱼ d = ⇒ₙ-inv-rfl d
  not-⇒ᵥ-and-⇒ₙ rflₕₖ d = ⇒ₙ-inv-rfl d
  not-⇒ᵥ-and-⇒ₙ rflₕₑ d = ⇒ₙ-inv-rfl d

opaque

  -- A state cannot reduce in both ⇒ₛ and ⇒ᵥ

  not-⇒ₛ-and-⇒ᵥ : s ⇒ₛ s′ → s ⇒ᵥ s″ → ⊥
  not-⇒ₛ-and-⇒ᵥ (sucₕ {k = 0} x) d =
    case ⇒ᵥ-inv-suc d of λ {
      (_ , _ , _ , _ , _ , _ , _ , _ , _ , () , _)}
  not-⇒ₛ-and-⇒ᵥ (sucₕ {k = 1+ k} x) d =
    case ⇒ᵥ-inv-suc d of λ {
      (_ , _ , _ , _ , _ , _ , _ , _ , _ , () , _)}
  not-⇒ₛ-and-⇒ᵥ (numₕ zeroₙ) d =
    case ⇒ᵥ-inv-zero d of λ {
      (_ , _ , _ , _ , _ , _ , _ , _ , _ , () , _)}
  not-⇒ₛ-and-⇒ᵥ (numₕ (sucₙ x)) d =
    case ⇒ᵥ-inv-suc d of λ {
      (_ , _ , _ , _ , _ , _ , _ , _ , _ , () , _)}

opaque

  -- A state cannot reduce in both ⇒ₛ and ⇒ₙ

  not-⇒ₛ-and-⇒ₙ : s ⇒ₛ s′ → s ⇒ₙ s″ → ⊥
  not-⇒ₛ-and-⇒ₙ (sucₕ x) d = ⇒ₙ-inv-suc d
  not-⇒ₛ-and-⇒ₙ (numₕ zeroₙ) d = ⇒ₙ-inv-zero d
  not-⇒ₛ-and-⇒ₙ (numₕ (sucₙ x)) d = ⇒ₙ-inv-suc d

opaque

  -- The small-step heap semantics is deterministic.

  ⇒-det : {s′ : State k m n} {s″ : State k m′ n′}
        → (d : s ⇒ s′) (d′ : s ⇒ s″)
        → Σ (m ≡ m′) λ m≡m′ →
          Σ (n ≡ n′) λ n≡n′ →
            subst₂ (State k) m≡m′ n≡n′ s′ ≡ s″
  ⇒-det (⇒ᵥ d) (⇒ᵥ d′) =
    ⇒ᵥ-det d d′
  ⇒-det (⇒ₙ d) (⇒ₙ d′) =
    case ⇒ₙ-det d d′ of λ {
      (refl , refl) →
    refl , refl , refl }
  ⇒-det (⇒ₛ d) (⇒ₛ d′) =
    refl , refl , ⇒ₛ-det d d′
  ⇒-det (⇒ₙ d) (⇒ᵥ d′) = ⊥-elim (not-⇒ᵥ-and-⇒ₙ d′ d)
  ⇒-det (⇒ₙ d) (⇒ₛ d′) = ⊥-elim (not-⇒ₛ-and-⇒ₙ d′ d)
  ⇒-det (⇒ᵥ d) (⇒ₙ d′) = ⊥-elim (not-⇒ᵥ-and-⇒ₙ d d′)
  ⇒-det (⇒ᵥ d) (⇒ₛ d′) = ⊥-elim (not-⇒ₛ-and-⇒ᵥ d′ d)
  ⇒-det (⇒ₛ d) (⇒ₙ d′) = ⊥-elim (not-⇒ₛ-and-⇒ₙ d d′)
  ⇒-det (⇒ₛ d) (⇒ᵥ d′) = ⊥-elim (not-⇒ₛ-and-⇒ᵥ d d′)

opaque

  -- The normalising reduction preserves equality
  -- in a certain way

  ⇒ₙ-⦅⦆-≡ : s ⇒ₙ s′ → ⦅ s ⦆ ≡ ⦅ s′ ⦆
  ⇒ₙ-⦅⦆-≡ {s = ⟨ _ , _ , _ , S ⟩} (varₕ d) =
    trans (⦅⦆ˢ-cong S (heapSubstVar d))
      (cong (λ x → ⦅ S ⦆ˢ _ [ x ]) (heapUpdateSubst d))
  ⇒ₙ-⦅⦆-≡ {s = ⟨ _ , _ , _ , S ⟩} (varₕ′ d) =
    ⦅⦆ˢ-cong S (heapSubstVar′ d)
  ⇒ₙ-⦅⦆-≡ appₕ = refl
  ⇒ₙ-⦅⦆-≡ fstₕ = refl
  ⇒ₙ-⦅⦆-≡ sndₕ = refl
  ⇒ₙ-⦅⦆-≡ prodrecₕ = refl
  ⇒ₙ-⦅⦆-≡ natrecₕ = refl
  ⇒ₙ-⦅⦆-≡ (unitrecₕ _) = refl
  ⇒ₙ-⦅⦆-≡ emptyrecₕ = refl
  ⇒ₙ-⦅⦆-≡ Jₕ = refl
  ⇒ₙ-⦅⦆-≡ Kₕ = refl
  ⇒ₙ-⦅⦆-≡ []-congₕ = refl

opaque

  ⇒ₙ*-⦅⦆-≡ : s ⇒ₙ* s′ → ⦅ s ⦆ ≡ ⦅ s′ ⦆
  ⇒ₙ*-⦅⦆-≡ id = refl
  ⇒ₙ*-⦅⦆-≡ (x ⇨ d) = trans (⇒ₙ-⦅⦆-≡ x) (⇒ₙ*-⦅⦆-≡ d)


opaque

  -- The reduction evaluating numerals preserves equality
  -- in a certain way

  ⇒ₛ-⦅⦆-≡ : s ⇒ₛ s′ → ⦅ s ⦆ ≡ ⦅ s′ ⦆
  ⇒ₛ-⦅⦆-≡ (sucₕ x) = refl
  ⇒ₛ-⦅⦆-≡ (numₕ x) = refl

opaque

  -- Lifting a normalising reduction to a larger heap

  wk1-⇒ₙ : ⟨ H , t , ρ , S ⟩ ⇒ₙ ⟨ H′ , t′ , ρ′ , S′ ⟩
        → ⟨ H ∙ c , t , step ρ , wk1ˢ S ⟩ ⇒ₙ ⟨ H′ ∙ c , t′ , step ρ′ , wk1ˢ S′ ⟩
  wk1-⇒ₙ (varₕ {S} d) =
    varₕ (subst (_ ⊢ _ ↦[_] _ ⨾ _) (wk-∣S∣ (step id) S) (there d))
  wk1-⇒ₙ (varₕ′ d) =
    varₕ′ (there d)
  wk1-⇒ₙ appₕ = appₕ
  wk1-⇒ₙ fstₕ = fstₕ
  wk1-⇒ₙ sndₕ = sndₕ
  wk1-⇒ₙ prodrecₕ = prodrecₕ
  wk1-⇒ₙ natrecₕ = natrecₕ
  wk1-⇒ₙ (unitrecₕ no-η) = unitrecₕ no-η
  wk1-⇒ₙ emptyrecₕ = emptyrecₕ
  wk1-⇒ₙ Jₕ = Jₕ
  wk1-⇒ₙ Kₕ = Kₕ
  wk1-⇒ₙ []-congₕ = []-congₕ

opaque

  -- Lifting a normalising reduction to a larger heap

  wk1-⇒ₙ* : (d : ⟨ H , t , ρ , S ⟩ ⇒ₙ* ⟨ H′ , t′ , ρ′ , S′ ⟩)
          → ⟨ H ∙ c , t , step ρ , wk1ˢ S ⟩ ⇒ₙ* ⟨ H′ ∙ c , t′ , step ρ′ , wk1ˢ S′ ⟩
  wk1-⇒ₙ* id = id
  wk1-⇒ₙ* (_⇨_ {s′ = record{}} x d) = wk1-⇒ₙ x ⇨ wk1-⇒ₙ* d

opaque

  -- Lifting a normalising reduction to a larger heap

  wk1●-⇒ₙ : ⟨ H , t , ρ , S ⟩ ⇒ₙ ⟨ H′ , t′ , ρ′ , S′ ⟩
          → ⟨ H ∙● , t , step ρ , wk1ˢ S ⟩ ⇒ₙ ⟨ H′ ∙● , t′ , step ρ′ , wk1ˢ S′ ⟩
  wk1●-⇒ₙ (varₕ {S} d) = varₕ (subst (_ ⊢ _ ↦[_] _ ⨾ _) (wk-∣S∣ (step id) S) (there● d))
  wk1●-⇒ₙ (varₕ′ d) = varₕ′ (there● d)
  wk1●-⇒ₙ appₕ = appₕ
  wk1●-⇒ₙ fstₕ = fstₕ
  wk1●-⇒ₙ sndₕ = sndₕ
  wk1●-⇒ₙ prodrecₕ = prodrecₕ
  wk1●-⇒ₙ natrecₕ = natrecₕ
  wk1●-⇒ₙ (unitrecₕ no-η) = unitrecₕ no-η
  wk1●-⇒ₙ emptyrecₕ = emptyrecₕ
  wk1●-⇒ₙ Jₕ = Jₕ
  wk1●-⇒ₙ Kₕ = Kₕ
  wk1●-⇒ₙ []-congₕ = []-congₕ

opaque

  -- Lifting a normalising reduction to a larger heap

  wk1●-⇒ₙ* : (d : ⟨ H , t , ρ , S ⟩ ⇒ₙ* ⟨ H′ , t′ , ρ′ , S′ ⟩)
          → ⟨ H ∙● , t , step ρ , wk1ˢ S ⟩ ⇒ₙ* ⟨ H′ ∙● , t′ , step ρ′ , wk1ˢ S′ ⟩
  wk1●-⇒ₙ* id = id
  wk1●-⇒ₙ* (_⇨_ {s′ = record{}} x d) = wk1●-⇒ₙ x ⇨ wk1●-⇒ₙ* d

opaque

  -- Replacing a variable and environment in a state

  var-env-⇒ₙ : ⟨ H , var x , ρ , S ⟩ ⇒ₙ s
            → wkVar ρ x ≡ wkVar ρ′ x′
            → ⟨ H , var x′ , ρ′ , S ⟩ ⇒ₙ s
  var-env-⇒ₙ (varₕ d) eq =
    varₕ (subst (_ ⊢_↦[ _ ] _ ⨾ _) eq d)
  var-env-⇒ₙ (varₕ′ d) eq =
    varₕ′ (subst (_ ⊢_↦ _) eq d)

opaque

  -- Replacing a variable and environment in a state

  var-env-⇒ₙ* : {ρ : Wk m n} {ρ″ : Wk m n′}
              → ⟨ H , var x , ρ , S ⟩ ⇒ₙ* ⟨ H′ , t , ρ″ , S′ ⟩
             → wkVar ρ x ≡ wkVar ρ′ x′
             → Normal ⟨ H′ , t , ρ″ , S′ ⟩
             → ⟨ H , var x′ , ρ′ , S ⟩ ⇒ₙ* ⟨ H′ , t , ρ″ , S′ ⟩
             ⊎ Σ (n′ ≡ n) λ n′≡n → ⟨ H , var x , ρ , S ⟩ ≡ subst (State _ _) n′≡n ⟨ H′ , t , ρ″ , S′ ⟩
  var-env-⇒ₙ* id eq (var x) = inj₂ (refl , refl)
  var-env-⇒ₙ* (x ⇨ d) eq n = inj₁ (var-env-⇒ₙ x eq ⇨ d)

opaque

  -- Extending the stack of a reduction

  ++-⇒ₙ : ⦃ ¬Track-resources ⦄
        → ∀ S₀ → ⟨ H , t , ρ , S ⟩ ⇒ₙ ⟨ H′ , t′ , ρ′ , S′ ⟩
        → ⟨ H , t , ρ , S ++ S₀ ⟩ ⇒ₙ ⟨ H′ , t′ , ρ′ , S′ ++ S₀ ⟩
  ++-⇒ₙ S₀ (varₕ x) = ⊥-elim not-tracking-and-no-tracking
  ++-⇒ₙ S₀ (varₕ′ ⦃ (nt) ⦄ x) = varₕ′ ⦃ tr = nt ⦄ x
  ++-⇒ₙ S₀ appₕ = appₕ
  ++-⇒ₙ S₀ fstₕ = fstₕ
  ++-⇒ₙ S₀ sndₕ = sndₕ
  ++-⇒ₙ S₀ prodrecₕ = prodrecₕ
  ++-⇒ₙ S₀ natrecₕ = natrecₕ
  ++-⇒ₙ S₀ (unitrecₕ no-η) = unitrecₕ no-η
  ++-⇒ₙ S₀ emptyrecₕ = emptyrecₕ
  ++-⇒ₙ S₀ Jₕ = Jₕ
  ++-⇒ₙ S₀ Kₕ = Kₕ
  ++-⇒ₙ S₀ []-congₕ = []-congₕ

opaque

  -- Extending the stack of a reduction

  ++-⇒ₙ* : ⦃ ¬Track-resources ⦄
         → ∀ S₀ → (d : ⟨ H , t , ρ , S ⟩ ⇒ₙ* ⟨ H′ , t′ , ρ′ , S′ ⟩)
         → ⟨ H , t , ρ , S ++ S₀ ⟩ ⇒ₙ* ⟨ H′ , t′ , ρ′ , S′ ++ S₀ ⟩
  ++-⇒ₙ* S₀ id = id
  ++-⇒ₙ* S₀ (_⇨_ {s′ = record{}} x d) = ++-⇒ₙ S₀ x ⇨ ++-⇒ₙ* S₀ d

opaque

  -- Extending the stack of a reduction with sucₛ

  ++sucₛ-⇒ₙ : (d : ⟨ H , t , ρ , S ⟩ ⇒ₙ ⟨ H′ , t′ , ρ′ , S′ ⟩)
            → ⟨ H , t , ρ , S ++ sucₛ k ⟩ ⇒ₙ ⟨ H′ , t′ , ρ′ , S′ ++ sucₛ k ⟩
  ++sucₛ-⇒ₙ {S} (varₕ x) =
    varₕ (subst (_ ⊢ _ ↦[_] _ ⨾ _) (sym (∣S++sucₛ∣≡∣S∣ S)) x)
  ++sucₛ-⇒ₙ (varₕ′ x) = varₕ′ x
  ++sucₛ-⇒ₙ appₕ = appₕ
  ++sucₛ-⇒ₙ fstₕ = fstₕ
  ++sucₛ-⇒ₙ sndₕ = sndₕ
  ++sucₛ-⇒ₙ prodrecₕ = prodrecₕ
  ++sucₛ-⇒ₙ natrecₕ = natrecₕ
  ++sucₛ-⇒ₙ (unitrecₕ no-η) = unitrecₕ no-η
  ++sucₛ-⇒ₙ emptyrecₕ = emptyrecₕ
  ++sucₛ-⇒ₙ Jₕ = Jₕ
  ++sucₛ-⇒ₙ Kₕ = Kₕ
  ++sucₛ-⇒ₙ []-congₕ = []-congₕ

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

  ++sucₛ-⇒ₛ : (d : ⟨ H , t , ρ , S ⟩ ⇒ₛ ⟨ H′ , t′ , ρ′ , S′ ⟩)
            → ⟨ H , t , ρ , S ++ sucₛ k ⟩ ⇒ₛ ⟨ H′ , t′ , ρ′ , S′ ++ sucₛ k ⟩
  ++sucₛ-⇒ₛ {k = k′} (sucₕ {t} {H} {ρ} {k} x) =
    subst (λ x → ⟨ H , suc t , ρ , x ⟩ ⇒ₛ ⟨ H , t , ρ , sucₑ ∙ x ⟩)
      (sym (sucₛ++sucₛ k k′)) (sucₕ x)
  ++sucₛ-⇒ₛ (numₕ x) = numₕ x

opaque

  -- Extending the stack of a reduction with sucₛ

  ++sucₛ-⇒ : (d : ⟨ H , t , ρ , S ⟩ ⇒ ⟨ H′ , t′ , ρ′ , S′ ⟩)
           → ⟨ H , t , ρ , S ++ sucₛ k ⟩ ⇒ ⟨ H′ , t′ , ρ′ , S′ ++ sucₛ k ⟩
  ++sucₛ-⇒ (⇒ₙ d) = ⇒ₙ (++sucₛ-⇒ₙ d)
  ++sucₛ-⇒ (⇒ᵥ d) = ⇒ᵥ (++sucₛ-⇒ᵥ d)
  ++sucₛ-⇒ (⇒ₛ d) = ⇒ₛ (++sucₛ-⇒ₛ d)

opaque

  -- Extending the stack of a reduction with sucₛ

  ++sucₛ-⇒* : (d : ⟨ H , t , ρ , S ⟩ ⇒* ⟨ H′ , t′ , ρ′ , S′ ⟩)
            → ⟨ H , t , ρ , S ++ sucₛ k ⟩ ⇒* ⟨ H′ , t′ , ρ′ , S′ ++ sucₛ k ⟩
  ++sucₛ-⇒* id = id
  ++sucₛ-⇒* (_⇨_ {s′ = record{}} x d) = ++sucₛ-⇒ x ⇨ ++sucₛ-⇒* d

opaque

  -- The relation _⇒ₙ_ preserves the heap when resource tracking is
  -- turned off.

  ⇒ₙ-Heap≡ : ⦃ ¬Track-resources ⦄
           → ⟨ H , t , ρ , S ⟩ ⇒ₙ ⟨ H′ , t′ , ρ′ , S′ ⟩ → H ≡ H′
  ⇒ₙ-Heap≡ (varₕ x) = ⊥-elim not-tracking-and-no-tracking
  ⇒ₙ-Heap≡ (varₕ′ x) = refl
  ⇒ₙ-Heap≡ appₕ = refl
  ⇒ₙ-Heap≡ fstₕ = refl
  ⇒ₙ-Heap≡ sndₕ = refl
  ⇒ₙ-Heap≡ prodrecₕ = refl
  ⇒ₙ-Heap≡ natrecₕ = refl
  ⇒ₙ-Heap≡ (unitrecₕ x) = refl
  ⇒ₙ-Heap≡ emptyrecₕ = refl
  ⇒ₙ-Heap≡ Jₕ = refl
  ⇒ₙ-Heap≡ Kₕ = refl
  ⇒ₙ-Heap≡ []-congₕ = refl

opaque

  -- The relation _⇒ₛ_ preserves the heap

  ⇒ₛ-Heap≡ : ⟨ H , t , ρ , S ⟩ ⇒ₛ ⟨ H′ , t′ , ρ′ , S′ ⟩ → H ≡ H′
  ⇒ₛ-Heap≡ (sucₕ x) = refl
  ⇒ₛ-Heap≡ (numₕ x) = refl

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

  -- Evaluation in _⇒ₙ_ behaves the same under equal heaps when
  -- resource tracking is turned off.

  ~ʰ-⇒ₙ : ⦃ ¬Track-resources ⦄
        → ⟨ H , t , ρ , S ⟩ ⇒ₙ ⟨ H′ , t′ , ρ′ , S′ ⟩ → H ~ʰ H″
        → ⟨ H″ , t , ρ , S ⟩ ⇒ₙ ⟨ H″ , t′ , ρ′ , S′ ⟩
  ~ʰ-⇒ₙ (varₕ d) H~H″              = ⊥-elim not-tracking-and-no-tracking
  ~ʰ-⇒ₙ (varₕ′ ⦃ tr = tr ⦄ d) H~H″ = varₕ′ ⦃ tr = tr ⦄ (~ʰ-lookup H~H″ d)
  ~ʰ-⇒ₙ appₕ H~H″                  = appₕ
  ~ʰ-⇒ₙ fstₕ H~H″                  = fstₕ
  ~ʰ-⇒ₙ sndₕ H~H″                  = sndₕ
  ~ʰ-⇒ₙ prodrecₕ H~H″              = prodrecₕ
  ~ʰ-⇒ₙ natrecₕ H~H″               = natrecₕ
  ~ʰ-⇒ₙ (unitrecₕ no-η) H~H″       = unitrecₕ no-η
  ~ʰ-⇒ₙ emptyrecₕ H~H″                    = emptyrecₕ
  ~ʰ-⇒ₙ Jₕ H~H″                    = Jₕ
  ~ʰ-⇒ₙ Kₕ H~H″                    = Kₕ
  ~ʰ-⇒ₙ []-congₕ H~H″              = []-congₕ

opaque

  -- Evaluation in _⇒ᵥ_ behaves the same under equal heaps

  ~ʰ-⇒ₛ : ⟨ H , t , ρ , S ⟩ ⇒ₛ ⟨ H′ , t′ , ρ′ , S′ ⟩ → H ~ʰ H″
        → ⟨ H″ , t , ρ , S ⟩ ⇒ₛ ⟨ H″ , t′ , ρ′ , S′ ⟩
  ~ʰ-⇒ₛ (sucₕ x) H~H″ = sucₕ x
  ~ʰ-⇒ₛ (numₕ x) H~H″ = numₕ x

opaque

  -- The non resource tracking reduction behaves the same on equal heaps

  ~ʰ-⇒ : ⦃ ¬Track-resources ⦄
       → ⟨ H , t , ρ , S ⟩ ⇒ ⟨ H′ , t′ , ρ′ , S′ ⟩ → H ~ʰ H″
       → ∃ λ H‴ → ⟨ H″ , t , ρ , S ⟩ ⇒ ⟨ H‴ , t′ , ρ′ , S′ ⟩ × H′ ~ʰ H‴
  ~ʰ-⇒ (⇒ₙ d) H~H″ =
    _ , ⇒ₙ (~ʰ-⇒ₙ d H~H″) , subst (_~ʰ _) (⇒ₙ-Heap≡ d) H~H″
  ~ʰ-⇒ (⇒ᵥ d) H~H″ =
    case ~ʰ-⇒ᵥ d H~H″ of λ
      (_ , d′ , H′~H‴) →
    _ , ⇒ᵥ d′ , H′~H‴
  ~ʰ-⇒ (⇒ₛ d) H~H″ =
    _ , ⇒ₛ ~ʰ-⇒ₛ d H~H″ , subst (_~ʰ _) (⇒ₛ-Heap≡ d) H~H″

opaque

  -- The non resource tracking reduction behaves the same on equal heaps

  ~ʰ-⇒* :  ⦃ ¬tr : ¬Track-resources ⦄
        → ⟨ H , t , ρ , S ⟩ ⇒* ⟨ H′ , t′ , ρ′ , S′ ⟩ → H ~ʰ H″
        → ∃ λ H‴ → ⟨ H″ , t , ρ , S ⟩ ⇒* ⟨ H‴ , t′ , ρ′ , S′ ⟩ × H′ ~ʰ H‴
  ~ʰ-⇒* id H~H′ =
    _ , id , H~H′
  ~ʰ-⇒* (_⇨_ {s′ = record{}} x d) H~H′ =
    case ~ʰ-⇒ x H~H′ of λ
      (_ , x′ , H~H″) →
    case ~ʰ-⇒* d H~H″ of λ
      (_ , d′ , H~H‴) →
    _ , (x′ ⇨ d′) , H~H‴
