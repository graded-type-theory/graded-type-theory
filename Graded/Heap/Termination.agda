------------------------------------------------------------------------
-- Termination properties of the reduction relation
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions
open import Tools.Sum
open import Graded.Heap.Assumptions

module Graded.Heap.Termination
  {a} {M : Set a} {𝕄 : Modality M}
  (UR : Usage-restrictions 𝕄)
  (TR : Type-restrictions 𝕄)
  (As : Assumptions UR TR)
  where

open Assumptions As
open Modality 𝕄
open Type-restrictions TR
open Usage-restrictions UR

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE hiding (sym)

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Typed TR
open import Definition.Typed.Consequences.Canonicity TR
open import Definition.Typed.Consequences.Reduction TR
open import Definition.Typed.Properties TR hiding (_⇨*_)

open import Graded.Context 𝕄 hiding (_⟨_⟩)
open import Graded.Usage 𝕄 UR
open import Graded.Mode 𝕄
open import Graded.Restrictions 𝕄

open import Graded.Heap.Bisimilarity UR TR
open import Graded.Heap.Untyped type-variant UR factoring-nr
open import Graded.Heap.Untyped.Properties type-variant UR factoring-nr
open import Graded.Heap.Typed UR TR factoring-nr
open import Graded.Heap.Typed.Properties UR TR factoring-nr
open import Graded.Heap.Typed.Reduction UR TR factoring-nr
open import Graded.Heap.Usage type-variant UR factoring-nr
open import Graded.Heap.Usage.Properties type-variant UR factoring-nr
open import Graded.Heap.Usage.Reduction type-variant UR factoring-nr Unitʷ-η→ ¬Nr-not-available
open import Graded.Heap.Reduction type-variant UR factoring-nr
open import Graded.Heap.Reduction.Properties type-variant UR factoring-nr

private variable
  t t′ u A B : Term _
  γ δ η : Conₘ _
  H H′ : Heap _ _
  ρ ρ′ : Wk _ _
  S S′ : Stack _
  e : Elim _
  Γ Δ : Con Term _
  s s′ : State _ _ _
  m : Mode
  k : Nat

opaque

  ⊢▸Final-reasons :
    {Δ : Con Term k}
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent Δ) →
    (k ≢ 0 → No-erased-matches′ type-variant UR) →
    Δ ⊢ₛ ⟨ H , t , ρ , S ⟩ ∷ A →
    ▸ ⟨ H , t , ρ , S ⟩ →
    Final ⟨ H , t , ρ , S ⟩ →
    Value t × S ≡ ε
  ⊢▸Final-reasons consistent nem ⊢s ▸s f =
    case ▸Final-reasons′ subtraction-ok nem ▸s f of λ where
      (inj₁ (_ , _  , _ , er∈S , ok)) →
        ⊥-elim (⊢emptyrec₀∉S (consistent ok) ⊢s er∈S)
      (inj₂ (inj₁ (_ , _ , refl , v , ¬m))) →
        ⊥-elim (¬m (⊢Matching ⊢s v))
      (inj₂ (inj₂ x)) → x

opaque

  ⊢▸-⇘-reasons :
    {Δ : Con Term k}
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent Δ) →
    (k ≢ 0 → No-erased-matches′ type-variant UR) →
    Δ ⊢ₛ s ∷ A →
    ▸ s →
    s ⇘ s′ →
    Value (State.head s′) × State.stack s′ ≡ ε
  ⊢▸-⇘-reasons {s′ = record{}} consistent nem ⊢s ▸s (d , f) =
    let ⊢s′ = ⊢ₛ-⇾* ⊢s d
        ▸s′ = ▸-⇾* ▸s d
    in  ⊢▸Final-reasons consistent nem ⊢s′ ▸s′ f

opaque

  ↘→⇘ :
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    Δ ⊢ₛ s ∷ B →
    ▸ s →
    Δ ⊢ ⦅ s ⦆ ↘ u ∷ A →
    ∃₃ λ m n (s′ : State _ m n) → s ⇘ s′ × u ≡ ⦅ s′ ⦆
  ↘→⇘ ⊢s ▸s (d , w) =
    let _ , _ , s′ , d₁ , u≡ = ⊢⇒*→⇾* As d ⊢s ▸s
        ▸s′ = ▸-⇾* ▸s d₁
        _ , s″ , n , d₂ = ▸normalize As s′ ▸s′
        d′ = d₁ ⇨* ⇾ₑ* d₂
        ⊢s″ = ⊢ₛ-⇾* ⊢s d′
        u≡′ = PE.trans u≡ (⇾ₑ*-⦅⦆-≡ d₂)
        w′ = subst Whnf u≡′ w
    in  _ , _ , s″
          , (d′ , λ d″ → whnfRedTerm (⇒ᵥ→⇒ ⊢s″ (Normal-⇾→⇒ᵥ n d″)) w′)
          , u≡′

opaque

  whBisim :
    {Δ : Con Term k} →
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent Δ) →
    (k ≢ 0 → No-erased-matches′ type-variant UR) →
    Δ ⊢ₛ s ∷ B →
    ▸ s →
    Δ ⊢ ⦅ s ⦆ ↘ u ∷ A →
    ∃₅ λ m n H t (ρ : Wk m n) → s ⇘ ⟨ H , t , ρ , ε ⟩ × wk ρ t [ H ]ₕ ≡ u × Value t
  whBisim {s = ⟨ H , t , ρ , S ⟩} consistent nem ⊢s ▸s d
    with ↘→⇘ {s = ⟨ H , t , ρ , S ⟩} ⊢s ▸s d
  … |  _ , _ , ⟨ H′ , t′ , ρ′ , S′ ⟩ , d′ , u≡ =
    let v , S≡ε = ⊢▸-⇘-reasons consistent nem ⊢s ▸s d′
    in  _ , _ , H′ , t′ , ρ′ , lemma S≡ε d′ u≡ v
    where
    lemma :
      S′ ≡ ε → ⟨ H , t , ρ , S ⟩ ⇘ ⟨ H′ , t′ , ρ′ , S′ ⟩ →
      u ≡ ⦅ ⟨ H′ , t′ , ρ′ , S′ ⟩ ⦆ → Value t′ →
      ⟨ H , t , ρ , S ⟩ ⇘ ⟨ H′ , t′ , ρ′ , ε ⟩ × wk ρ′ t′ [ H′ ]ₕ ≡ u × Value t′
    lemma refl d u≡ v = d , PE.sym u≡ , v

opaque

  whBisim-initial :
    {Δ : Con Term k} →
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent Δ) →
    (k ≢ 0 → No-erased-matches′ type-variant UR) →
    𝟘ᶜ ▸ t →
    Δ ⊢ t ↘ u ∷ A →
    ∃₅ λ m n H u′ (ρ : Wk m n) → initial t ⇘ ⟨ H , u′ , ρ , ε ⟩ × wk ρ u′ [ H ]ₕ ≡ u × Value u′
  whBisim-initial consistent nem ▸t d =
    whBisim consistent nem (⊢initial (redFirst*Term (d .proj₁)))
      (▸initial ▸t) (PE.subst (_ ⊢_↘ _ ∷ _) (PE.sym ⦅initial⦆≡) d)

opaque

  ⊢▸-⇘ :
    {Δ : Con Term k} →
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent Δ) →
    (k ≢ 0 → No-erased-matches′ type-variant UR) →
    Δ ⊢ₛ s ∷ B →
    ▸ s →
    ∃₅ λ m n H t (ρ : Wk m n) → s ⇘ ⟨ H , t , ρ , ε ⟩ × Value t
  ⊢▸-⇘ {s = ⟨ H , t , ρ , S ⟩} consistent nem ⊢s ▸s =
    let u , w , d = whNormTerm (⊢⦅⦆ {s = ⟨ H , t , ρ , S ⟩} ⊢s)
        _ , _ , H′ , t′ , ρ′ , d′ , _ , v =
          whBisim {s = ⟨ H , t , ρ , S ⟩} consistent nem ⊢s ▸s (d , w)
    in  _ , _ , H′ , t′ , ρ′ , d′ , v

opaque

  initial-⇘ :
    {Δ : Con Term k} →
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent Δ) →
    (k ≢ 0 → No-erased-matches′ type-variant UR) →
    Δ ⊢ t ∷ A → 𝟘ᶜ ▸ t →
    ∃₅ λ m n H u (ρ : Wk m n)→ initial t ⇘ ⟨ H , u , ρ , ε ⟩ × Value u
  initial-⇘ consistent nem ⊢t ▸t =
    ⊢▸-⇘ consistent nem (⊢initial ⊢t) (▸initial ▸t)

opaque

  initial-⇘-closed :
    ε ⊢ t ∷ A → ε ▸ t →
    ∃₅ λ m n H u (ρ : Wk m n)→ initial t ⇘ ⟨ H , u , ρ , ε ⟩ × Value u
  initial-⇘-closed ⊢t ▸t =
    initial-⇘ ⦃ ok = ε ⦄
      (λ _ _ → ¬Empty) (λ 0≢0 → ⊥-elim (0≢0 refl)) ⊢t ▸t
