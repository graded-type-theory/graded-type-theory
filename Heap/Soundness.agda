------------------------------------------------------------------------
-- Bisimilarity properties between the heap semantics with different
-- options and the call by name weak-head reduction.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions
open import Tools.Bool
import Heap.Bisimilarity

module Heap.Soundness
  {a} {M : Set a} {𝕄 : Modality M}
  {UR : Usage-restrictions 𝕄}
  (TR : Type-restrictions 𝕄)
  (erased-heap : Bool)
  (open Heap.Bisimilarity UR TR erased-heap)
  (As : Assumptions)
  where

open Type-restrictions TR
open Modality 𝕄
open Assumptions As

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
import Tools.Reasoning.PartialOrder as RPo
open import Tools.Sum hiding (id; sym)

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Inversion M
open import Definition.Untyped.Properties M
open import Definition.Typed TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Consequences.Canonicity TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.EqRelInstance TR
open import Definition.LogicalRelation TR
open import Definition.LogicalRelation.Fundamental.Reducibility TR
open import Definition.LogicalRelation.Substitution.Introductions.Nat TR

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Mode 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Inversion 𝕄 UR

open import Heap.Options
open import Heap.Untyped type-variant UR
open import Heap.Untyped.Properties type-variant UR
open import Heap.Usage type-variant UR erased-heap
open import Heap.Usage.Properties type-variant UR erased-heap
import Heap.Usage.Reduction type-variant UR erased-heap (tracking-and-ℕ-fullred-if false) Unitʷ-η→ as URᶠ
import Heap.Usage.Reduction type-variant UR erased-heap (tracking-and-ℕ-fullred-if true) Unitʷ-η→ as URᵗ
open import Heap.Termination UR TR erased-heap As
open import Heap.Typed UR TR false
import Heap.Typed UR TR true as HTₜ
open import Heap.Typed.Reduction UR TR (tracking-and-ℕ-fullred-if false) hiding (⇒*→≡)
open import Heap.Typed.Reduction UR TR (tracking-and-ℕ-fullred-if true) using (⇒*→≡)
open import Heap.Typed.Properties UR TR
open import Heap.Normalization type-variant UR
open import Heap.Reduction type-variant UR (tracking-and-ℕ-fullred-if true)
open import Heap.Reduction.Properties type-variant UR (tracking-and-ℕ-fullred-if true)
  using (_⇨*_; ++sucₛ-⇒*)
open import Heap.Reduction.Properties type-variant UR (not-tracking-and-ℕ-fullred-if false)
  using (⇒ₙ*_)

private variable
  k : Nat
  n t A : Term _
  s : State _ _ _
  γ δ η : Conₘ _
  Γ Δ : Con Term _
  H : Heap _ _
  E : Env _ _
  S : Stack _
  m : Mode

opaque

  -- All well-typed and well-resourced states of type ℕ reduce to numerals

  redNumeral : Consistent Δ → Δ ⊩ℕ n ∷ℕ → n PE.≡ ⦅ s ⦆ → Δ ⨾ Γ ⊢ s ∷ ℕ → γ ⨾ δ ⨾ η ▸[ m ] s
             → ∃₄ λ m n H (E : Env m n) → ∃ λ t → s ⇒* ⟨ H , t , E , ε ⟩ × Numeral t
  redNumeral consistent (ℕₜ _ d n≡n (sucᵣ x)) PE.refl ⊢s ▸s =
    case whBisim consistent (redₜ d , sucₙ) ⊢s ▸s of λ
      (_ , _ , H , t , E , d′ , ≡u , v) →
    case subst-suc {t = wk E t} ≡u of λ {
      (inj₁ (x , ≡x)) →
    case wk-var ≡x of λ {
      (_ , PE.refl , _) →
    case v of λ ()};
      (inj₂ (n′ , ≡suc , ≡n)) →
    case wk-suc ≡suc of λ {
      (n″ , PE.refl , ≡n′) →
    case isNumeral? n″ of λ {
      (yes num) →
    _ , _ , _ , _ , _ , bisim₇* true d′ , sucₙ num ;
      (no ¬num) →
    case ⊢ₛ-⇒* ⊢s d′ of λ
      (_ , _ , _ , _ , ⊢H , ⊢t , ⊢S) →
    case inversion-suc ⊢t of λ
      (⊢n″ , ≡ℕ) →
    case URᶠ.▸-⇒* ▸s d′ of λ
      (_ , _ , _ , _ , ▸H , ▸t , ▸ε , m≤ , γ≤) →
    case inv-usage-suc ▸t of λ
      (invUsageSuc ▸n″ δ≤)  →
    case redNumeral {s = ⟨ H , n″ , E , ε ⟩} consistent x
          (PE.sym (PE.trans (PE.cong (_[ H ]ₕ) ≡n′) ≡n))
          (_ , ⊢H , ⊢n″ , ε)
          (▸H , ▸n″ , ▸ε , m≤ , ≤ᶜ-trans γ≤ (+ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E δ≤)))) of λ
      (_ , _ , H′ , E′ , t′ , d₀ , n) →
    _ , _ , _ , _ , _
      , (bisim₇* true d′ ⇨* ((⇒ₛ (sucₕ ¬num)) ⇨
          (++sucₛ-⇒* {k = 1} d₀ ⇨* ((⇒ₛ (numₕ n)) ⇨ id))))
      , sucₙ n }}}

  redNumeral consistent (ℕₜ _ d n≡n zeroᵣ) PE.refl ⊢s ▸s =
    case whBisim consistent (redₜ d , zeroₙ) ⊢s ▸s of λ
      (_ , _ , H , t , E , d′ , ≡u , v) →
    case subst-zero {t = wk E t} ≡u of λ {
      (inj₁ (x , ≡x)) →
    case wk-var ≡x of λ {
      (_ , PE.refl , w) →
    case v of λ ()} ;
      (inj₂ ≡zero) →
    case wk-zero ≡zero of λ {
      PE.refl →
    _ , _ , _ , _ , _ , bisim₇* true d′ , zeroₙ }}

  redNumeral consistent (ℕₜ _ d n≡n (ne (neNfₜ neK ⊢k k≡k))) PE.refl ⊢s ▸s =
    case whBisim consistent (redₜ d , ne neK) ⊢s ▸s of λ {
      (_ , _ , H , t , E , d′ , PE.refl , v) →
    case Value→Whnf (substValue (toSubstₕ H) (wkValue E v)) of λ
      (_ , ¬neK) →
    ⊥-elim (¬neK neK) }

opaque

  -- All well-typed and erased terms of type ℕ reduce to some
  -- numeral and the resulting heap has all grades less than or equal to 𝟘.

  -- Note that some assumptions to this theorem are given as a module parameter.

  soundness : {Δ : Con Term k}
            → (k PE.≡ 0 ⊎ Consistent Δ × T erased-heap)
            → Δ ⊢ t ∷ ℕ → 𝟘ᶜ ▸ t
            → ∃₂ λ m n → ∃₃ λ H k (E : Env m n) →
              initial t ⇒* ⟨ H , sucᵏ k , E , ε ⟩ ×
              (Δ ⊢ t ≡ sucᵏ k ∷ ℕ) ×
              H ≤ʰ 𝟘
  soundness {k} {t} {Δ} as ⊢t ▸t =
    case ▸initial k≡0⊎erased-heap ▸t of λ
      ▸s →
    case ⊩∷ℕ⇔ .proj₁ (reducible-⊩∷ ⊢t) of λ
      [t] →
    case redNumeral consistent [t] (PE.sym (PE.trans (erasedHeap-subst (wk id t)) (wk-id t)))
           (⊢initial false ⊢t) ▸s of λ
      (_ , _ , H , E , t , d , num) →
    case URᵗ.▸-⇒* ▸s d of λ {
      (γ , δ , _ , _ , ▸H , ▸n , ε , _ , γ≤) →
    case Numeral→sucᵏ num of λ
      (k , ≡sucᵏ) →
    case PE.subst (λ x → _ ⇒* ⟨ _ , x , _ , _ ⟩) ≡sucᵏ d of λ
      d′ →
    let open RPo ≤ᶜ-poset in
    _ , _ , _ , _ , _
      , d′
      , PE.subst₂ (_ ⊢_≡_∷ ℕ)
          (PE.trans (erasedHeap-subst (wk id _)) (wk-id _))
          (PE.trans (PE.cong (_[ H ]ₕ) (wk-sucᵏ k)) (subst-sucᵏ k))
          (⇒*→≡ (⊢initial true ⊢t) d′)
      , 𝟘▸H→H≤𝟘 (subₕ ▸H (begin
          γ                  ≤⟨ γ≤ ⟩
          𝟙 ·ᶜ wkᶜ E δ +ᶜ 𝟘ᶜ ≈⟨ +ᶜ-identityʳ _ ⟩
          𝟙 ·ᶜ wkᶜ E δ       ≈⟨ ·ᶜ-identityˡ _ ⟩
          wkᶜ E δ            ≤⟨ wk-≤ᶜ E (inv-usage-numeral ▸n num) ⟩
          wkᶜ E 𝟘ᶜ           ≡⟨ wk-𝟘ᶜ E ⟩
          𝟘ᶜ                 ∎ ))}
    where
    consistent : Consistent Δ
    consistent =
      case as of λ where
        (inj₂ (c , _)) → c
        (inj₁ PE.refl) →
          case PE.singleton Δ of λ where
            (ε , PE.refl) → λ _ → ¬Empty
    k≡0⊎erased-heap : k PE.≡ 0 ⊎ T erased-heap
    k≡0⊎erased-heap =
      case as of λ where
        (inj₁ x) → inj₁ x
        (inj₂ (_ , x)) → inj₂ x
