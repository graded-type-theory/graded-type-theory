------------------------------------------------------------------------
-- Properties of the usage relation for Heaps, Stacks and States.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Variant
open import Graded.Usage.Restrictions.Natrec

module Graded.Heap.Usage.Properties
  {a} {M : Set a} {𝕄 : Modality M}
  (type-variant : Type-variant)
  (UR : Usage-restrictions 𝕄)
  (open Usage-restrictions UR)
  (factoring-nr :
    ⦃ has-nr : Nr-available ⦄ →
    Is-factoring-nr M (Natrec-mode-Has-nr 𝕄 has-nr))
  where

open Modality 𝕄

open import Definition.Untyped M
open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄
open import Graded.Restrictions 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Restrictions.Instance UR
open import Graded.Usage.Inversion 𝕄 UR
open import Graded.Usage.Properties 𝕄 UR

open import Graded.Heap.Untyped type-variant UR factoring-nr
open import Graded.Heap.Usage type-variant UR factoring-nr
open import Graded.Heap.Usage.Inversion type-variant UR factoring-nr

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum
import Tools.Reasoning.PartialOrder as RPo
import Tools.Reasoning.PropositionalEquality as RPe


private variable
  k n : Nat
  γ δ η : Conₘ _
  p q r : M
  m : Mode
  H H′ : Heap _ _
  x : Fin _
  y : Ptr _
  A z s t : Term _
  ρ ρ′ : Wk _ _
  S : Stack _
  e : Elim _
  c : Entryₘ _ _
  c′ : Entry _ _

opaque

  -- Usage for erased heaps

  ▸erasedHeap : 𝟘ᶜ ▸ʰ erasedHeap n
  ▸erasedHeap {(0)} = ε
  ▸erasedHeap {(1+ n)} = ▸erasedHeap ∙●

opaque

  -- Well-usage for the initial state

  ▸initial : 𝟘ᶜ {n} ▸ t → ▸ initial t
  ▸initial ▸t =
    ▸ₛ ▸erasedHeap (▸-cong (sym ⌞𝟙⌟) ▸t) ε
      (≤ᶜ-reflexive (≈ᶜ-sym (≈ᶜ-trans (+ᶜ-identityʳ _) (·ᶜ-zeroʳ _))))

opaque

  -- Usage of closures where the mode is 𝟘ᵐ

  ▸ᶜ⁰ : ∀ {ok}
      → γ ▸[ 𝟘ᵐ[ ok ] ] t
      → γ ⨾ 𝟘 ▸ᶜ (𝟘 , t , ρ)
  ▸ᶜ⁰ {γ} {t} {ρ} ▸t =
    ▸ᶜ (▸-cong (sym ⌞𝟘⌟) ▸t) ≤-refl

opaque

  -- Usage of closures where the mode is 𝟘ᵐ?

  ▸ᶜ⁰? : γ ▸[ 𝟘ᵐ? ] t
       → γ ⨾ 𝟘 ▸ᶜ (𝟘 , t , ρ)
  ▸ᶜ⁰? {γ} {t} {ρ} =
    𝟘ᵐ?-elim (λ m → γ ▸[ m ] t → γ ⨾ 𝟘 ▸ᶜ (𝟘 , t , ρ))
      ▸ᶜ⁰ (λ not-ok ▸t → ▸ᶜ (▸-cong (sym (only-𝟙ᵐ-without-𝟘ᵐ not-ok)) ▸t) ≤-refl)

opaque

  -- Subsumption for closures

  subᶜ : γ ⨾ p ▸ᶜ c → p ≤ q → γ ⨾ q ▸ᶜ c
  subᶜ (▸ᶜ ▸t p′≤p) p≤q = ▸ᶜ ▸t (≤-trans p′≤p p≤q)

opaque

  -- A lemma for well-resourced closures

  ▸ᶜᵖ : γ ▸[ ⌞ p ⌟ ] t → γ ⨾ p ▸ᶜ (p , t , ρ)
  ▸ᶜᵖ ▸t = ▸ᶜ ▸t ≤-refl

opaque

  -- A lemma for well-resourced closures

  ▸ᶜᵖʳ : γ ▸[ ⌞ p ⌟ ] t → ∃ λ δ → δ ⨾ p · r ▸ᶜ (p · r , t , ρ) × r ·ᶜ γ ≈ᶜ r ·ᶜ δ
  ▸ᶜᵖʳ {r} ▸t =
    case is-𝟘? r of λ where
      (yes refl) →
        case ▸-𝟘ᵐ? ▸t of λ
          (_ , ▸t′) →
            _ , subst (λ x → _ ⨾ x ▸ᶜ (x , _)) (sym (·-zeroʳ _)) (▸ᶜ⁰? ▸t′)
              , ≈ᶜ-trans (·ᶜ-zeroˡ _) (≈ᶜ-sym (·ᶜ-zeroˡ _))
      (no r≢𝟘) →
        _ , ▸ᶜᵖ (▸-cong (sym (≢𝟘→⌞·⌟≡ʳ r≢𝟘)) ▸t) , ≈ᶜ-refl

opaque

  -- Subsumption for heaps

  subₕ : ⦃ Has-well-behaved-zero M semiring-with-meet ⦄
       → γ ▸ʰ H → γ ≤ᶜ δ → δ ▸ʰ H
  subₕ {δ = ε} ε ε = ε
  subₕ {δ = δ ∙ p} (▸H ∙ ▸c) (γ≤δ ∙ p″≤p) =
    subₕ ▸H (+ᶜ-monotone γ≤δ (·ᶜ-monotoneˡ p″≤p)) ∙ subᶜ ▸c p″≤p
  subₕ {δ = δ ∙ p} (▸H ∙●) (γ≤δ ∙ 𝟘≤p) =
    subst (λ p → (δ ∙ p) ▸ʰ _) (sym (𝟘≮ 𝟘≤p)) (subₕ ▸H γ≤δ ∙●)

opaque

  -- An inversion lemma for ▸ʰ with a dummy entry.

  inv-▸ʰ● : γ ∙ p ▸ʰ H ∙● → p ≡ 𝟘 × γ ▸ʰ H
  inv-▸ʰ● (▸H ∙●) = refl , ▸H

opaque

  -- A well-resourced heap under the zero-context has all grades bounded by 𝟘.

  𝟘▸H→H≤𝟘 : 𝟘ᶜ ▸ʰ H → H ≤ʰ 𝟘
  𝟘▸H→H≤𝟘 {H = ε} ε = ε
  𝟘▸H→H≤𝟘 {H = H ∙ c} (_∙_ {ρ} {δ} ▸H (▸ᶜ _ p≤𝟘)) =
    𝟘▸H→H≤𝟘 (subst (_▸ʰ _) (≈ᶜ→≡ lemma) ▸H) ∙ p≤𝟘
    where
    open import Tools.Reasoning.Equivalence Conₘ-setoid
    lemma : 𝟘ᶜ +ᶜ 𝟘 ·ᶜ wkConₘ ρ δ ≈ᶜ 𝟘ᶜ
    lemma = begin
      𝟘ᶜ +ᶜ 𝟘 ·ᶜ wkConₘ ρ δ  ≈⟨ +ᶜ-identityˡ _ ⟩
      𝟘 ·ᶜ wkConₘ ρ δ        ≈⟨ ·ᶜ-zeroˡ _ ⟩
      𝟘ᶜ                     ∎
  𝟘▸H→H≤𝟘 {H = H ∙●} ▸H = 𝟘▸H→H≤𝟘 (inv-▸ʰ● ▸H .proj₂) ∙●

opaque

  -- In a well-resorced heap, a pointer lookup yields a well-resourced
  -- term and a well-resourced heap.

  ▸-heapLookup : ⦃ Has-well-behaved-zero M semiring-with-meet ⦄
               → H ⊢ y ↦[ q ] t , ρ ⨾ H′
               → γ ▸ʰ H
               → γ ⟨ y ⟩ - q ≤ r
               → ∃ λ δ → δ ▸[ ⌞ q ⌟ ] t × (γ , y ≔ r) +ᶜ q ·ᶜ wkConₘ ρ δ ▸ʰ H′
  ▸-heapLookup {q} {r} (here {r = r′} p′-q≡r′) (_∙_ {p} ▸H (▸ᶜ {q = p′} ▸t p′≤p)) p-q≤r =
    case is-𝟘? p′ of λ where
      (yes refl) →
        case p′≡𝟘→ refl of λ {
          (refl , refl , refl , refl) →
        _ , ▸t , subₕ ▸H lemma₀ ∙ ▸ᶜ ▸t r′≤r+q·𝟘 }
      (no p′≢𝟘) →
        case ▸-𝟘ᵐ? ▸t of λ
          (η , ▸⁰t) →
        case ▸-cong (sym ⌞𝟘⌟≡𝟘ᵐ?) ▸⁰t of λ
          ▸⁰t′ →
        case is-𝟘? q of λ where
          (yes refl) →
            case is-𝟘? r′ of λ where
              (yes refl) →
                _ , ▸⁰t′ , subₕ ▸H (lemma₁ (r′≡𝟘→ refl) refl) ∙ ▸ᶜ ▸⁰t′ r′≤r+q·𝟘
              (no r′≢𝟘) →
                _ , ▸⁰t′ , subₕ ▸H (lemma₂ refl) ∙ ▸ᶜ (▸-cong (trans (≢𝟘→⌞⌟≡𝟙ᵐ p′≢𝟘) (sym (≢𝟘→⌞⌟≡𝟙ᵐ r′≢𝟘))) ▸t) r′≤r+q·𝟘
          (no q≢𝟘) →
            case ▸-cong (trans (≢𝟘→⌞⌟≡𝟙ᵐ p′≢𝟘) (sym (≢𝟘→⌞⌟≡𝟙ᵐ q≢𝟘))) ▸t of λ
              ▸t′ →
            case is-𝟘? r′ of λ where
              (yes refl) →
                _ , ▸t′ , subₕ ▸H (lemma₃ (r′≡𝟘→ refl)) ∙ ▸ᶜ ▸⁰t′ r′≤r+q·𝟘
              (no r′≢𝟘) →
                _ , ▸t′ , subₕ ▸H lemma₀ ∙ ▸ᶜ (▸-cong (trans (≢𝟘→⌞⌟≡𝟙ᵐ p′≢𝟘) (sym (≢𝟘→⌞⌟≡𝟙ᵐ r′≢𝟘))) ▸t) r′≤r+q·𝟘
    where
    r′≤r : r′ ≤ r
    r′≤r = p′-q≡r′ .proj₂ r (≤-trans p′≤p p-q≤r)
    p′≡𝟘→ : p′ ≡ 𝟘 → p ≡ 𝟘 × q ≡ 𝟘 × r ≡ 𝟘 × r′ ≡ 𝟘
    p′≡𝟘→ refl =
      case 𝟘≮ p′≤p of λ {
        refl →
      case 𝟘-p≤q p-q≤r of λ {
        (refl , refl) →
      refl , refl , refl , 𝟘-p≡q p′-q≡r′ .proj₁ }}
    r′≡𝟘→ : r′ ≡ 𝟘 → r ≡ 𝟘
    r′≡𝟘→ refl = 𝟘≮ r′≤r
    r≡r+q·𝟘 : r ≡ r + q · 𝟘
    r≡r+q·𝟘 = begin
      r          ≡˘⟨ +-identityʳ r ⟩
      r + 𝟘      ≡˘⟨ +-congˡ (·-zeroʳ q) ⟩
      r + q · 𝟘 ∎
      where
      open RPe
    r′≤r+q·𝟘 : r′ ≤ r + q · 𝟘
    r′≤r+q·𝟘 = begin
      r′        ≤⟨ -≡≤-monotoneˡ p′≤p p′-q≡r′ p-q≤r ⟩
      r         ≈⟨ r≡r+q·𝟘 ⟩
      r + q · 𝟘 ∎
      where
      open RPo ≤-poset
    lemma₀′ : ∀ {n} {γ δ : Conₘ n} → γ +ᶜ p ·ᶜ δ ≤ᶜ (γ +ᶜ q ·ᶜ δ) +ᶜ r ·ᶜ δ
    lemma₀′ {γ} {δ} = begin
      γ +ᶜ p ·ᶜ δ                       ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneˡ p-q≤r) ⟩
      γ +ᶜ (r + q) ·ᶜ δ                 ≈⟨ +ᶜ-congˡ (·ᶜ-distribʳ-+ᶜ r q δ) ⟩
      γ +ᶜ (r ·ᶜ δ +ᶜ q ·ᶜ δ)           ≈⟨ +ᶜ-congˡ (+ᶜ-comm (r ·ᶜ δ) (q ·ᶜ δ)) ⟩
      γ +ᶜ (q ·ᶜ δ +ᶜ r ·ᶜ δ)           ≈˘⟨ +ᶜ-assoc γ (q ·ᶜ δ) (r ·ᶜ δ) ⟩
      (γ +ᶜ q ·ᶜ δ) +ᶜ r ·ᶜ δ           ∎
      where
      open RPo ≤ᶜ-poset
    lemma₀ : ∀ {n} {γ δ : Conₘ n} → γ +ᶜ p ·ᶜ δ ≤ᶜ (γ +ᶜ q ·ᶜ δ) +ᶜ (r + q · 𝟘) ·ᶜ δ
    lemma₀ {γ} {δ} = begin
      γ +ᶜ p ·ᶜ δ                       ≤⟨ lemma₀′ ⟩
      (γ +ᶜ q ·ᶜ δ) +ᶜ r ·ᶜ δ           ≈⟨ +ᶜ-congˡ (·ᶜ-congʳ r≡r+q·𝟘) ⟩
      (γ +ᶜ q ·ᶜ δ) +ᶜ (r + q · 𝟘) ·ᶜ δ ∎
      where
      open RPo ≤ᶜ-poset
    lemma₁ : ∀ {n} {γ δ η : Conₘ n} → r ≡ 𝟘 → q ≡ 𝟘
           → γ +ᶜ p ·ᶜ δ ≤ᶜ (γ +ᶜ q ·ᶜ η) +ᶜ (r + q · 𝟘) ·ᶜ η
    lemma₁ {γ} {δ} {η} refl refl = begin
      γ +ᶜ p ·ᶜ δ                        ≤⟨ lemma₀′ ⟩
      (γ +ᶜ 𝟘 ·ᶜ δ) +ᶜ 𝟘 ·ᶜ δ            ≈⟨ +ᶜ-cong (+ᶜ-congˡ (·ᶜ-zeroˡ δ)) (·ᶜ-zeroˡ δ) ⟩
      (γ +ᶜ 𝟘ᶜ) +ᶜ 𝟘ᶜ                    ≈˘⟨ +ᶜ-cong (+ᶜ-congˡ (·ᶜ-zeroˡ η)) (·ᶜ-zeroˡ η) ⟩
      (γ +ᶜ 𝟘 ·ᶜ η) +ᶜ 𝟘 ·ᶜ η            ≈⟨ +ᶜ-congˡ (·ᶜ-congʳ r≡r+q·𝟘) ⟩
      (γ +ᶜ 𝟘 ·ᶜ η) +ᶜ (𝟘 + 𝟘 · 𝟘) ·ᶜ η ∎
      where
      open RPo ≤ᶜ-poset
    lemma₂ : ∀ {n} {γ δ η : Conₘ n} → q ≡ 𝟘
           → γ +ᶜ p ·ᶜ δ ≤ᶜ (γ +ᶜ q ·ᶜ η) +ᶜ (r + q · 𝟘) ·ᶜ δ
    lemma₂ {γ} {δ} {η} refl = begin
      γ +ᶜ p ·ᶜ δ ≤⟨ lemma₀ ⟩
      (γ +ᶜ 𝟘 ·ᶜ δ) +ᶜ (r + 𝟘 · 𝟘) ·ᶜ δ ≈⟨ +ᶜ-congʳ (+ᶜ-congˡ (·ᶜ-zeroˡ δ)) ⟩
      (γ +ᶜ 𝟘ᶜ) +ᶜ (r + 𝟘 · 𝟘) ·ᶜ δ     ≈˘⟨ +ᶜ-congʳ (+ᶜ-congˡ (·ᶜ-zeroˡ η)) ⟩
      (γ +ᶜ 𝟘 ·ᶜ η) +ᶜ (r + 𝟘 · 𝟘) ·ᶜ δ ∎
      where
      open RPo ≤ᶜ-poset
    lemma₃ : ∀ {n} {γ δ η : Conₘ n} → r ≡ 𝟘
           → γ +ᶜ p ·ᶜ δ ≤ᶜ (γ +ᶜ q ·ᶜ δ) +ᶜ (r + q · 𝟘) ·ᶜ η
    lemma₃ {γ} {δ} {η} refl = begin
      γ +ᶜ p ·ᶜ δ                        ≤⟨ lemma₀′ ⟩
      (γ +ᶜ q ·ᶜ δ) +ᶜ 𝟘 ·ᶜ δ            ≈⟨ +ᶜ-congˡ (·ᶜ-zeroˡ δ) ⟩
      (γ +ᶜ q ·ᶜ δ) +ᶜ 𝟘ᶜ                ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroˡ η) ⟩
      (γ +ᶜ q ·ᶜ δ) +ᶜ 𝟘 ·ᶜ η            ≈⟨ +ᶜ-congˡ (·ᶜ-congʳ r≡r+q·𝟘) ⟩
      (γ +ᶜ q ·ᶜ δ) +ᶜ (𝟘 + q · 𝟘) ·ᶜ η ∎
      where
      open RPo ≤ᶜ-poset

  ▸-heapLookup {H = H ∙ (p′ , u , ρ)} {y +1} {q} {γ = γ ∙ p} {r}
    (there {c = _ , ρ′} d) (_∙_ {δ} ▸H (▸ᶜ ▸u p′≤p)) γ⟨y⟩-q≤r =
    case p+q-r≤p-r+q γ⟨y⟩-q≤r ((p ·ᶜ wkConₘ ρ δ) ⟨ y ⟩) of λ
      γ⟨y⟩+pδ⟨y⟩-q≤pδ⟨y⟩+r →
    case subst (_- q ≤ ((p ·ᶜ wkConₘ ρ δ) ⟨ y ⟩ + r))
           (sym (lookup-distrib-+ᶜ γ (p ·ᶜ wkConₘ ρ δ) y))
           γ⟨y⟩+pδ⟨y⟩-q≤pδ⟨y⟩+r of λ
      γ+pδ⟨y⟩-q≤pδ⟨y⟩+r →
    case ▸-heapLookup d ▸H γ+pδ⟨y⟩-q≤pδ⟨y⟩+r of λ
      (δ′ , ▸t , ▸H′) →
    _ , ▸t , subₕ ▸H′ lemma₁ ∙ ▸ᶜ ▸u lemma₂
    where
    lemma₁ : ∀ {δ δ′}
           →  (γ +ᶜ p ·ᶜ δ , y ≔ (p ·ᶜ δ) ⟨ y ⟩ + r) +ᶜ q ·ᶜ δ′
           ≤ᶜ ((γ , y ≔ r) +ᶜ q ·ᶜ δ′) +ᶜ (p + q · 𝟘) ·ᶜ δ
    lemma₁ {δ} {δ′} = begin
      (γ +ᶜ p ·ᶜ δ , y ≔ (p ·ᶜ δ) ⟨ y ⟩ + r) +ᶜ q ·ᶜ δ′
        ≈⟨ +ᶜ-congʳ (update-congʳ (+-comm _ r)) ⟩
      (γ +ᶜ p ·ᶜ δ , y ≔ r + (p ·ᶜ δ) ⟨ y ⟩) +ᶜ q ·ᶜ δ′
        ≡⟨ cong (_+ᶜ _) (update-distrib-+ᶜ γ (p ·ᶜ δ) r _ y) ⟩
      ((γ , y ≔ r) +ᶜ (p ·ᶜ δ , y ≔ (p ·ᶜ δ) ⟨ y ⟩)) +ᶜ q ·ᶜ δ′
        ≡⟨ cong (λ x → (_ +ᶜ x) +ᶜ _) (update-self (p ·ᶜ δ) y) ⟩
      ((γ , y ≔ r) +ᶜ p ·ᶜ δ) +ᶜ q ·ᶜ δ′
        ≈⟨ +ᶜ-assoc (γ , y ≔ r) (p ·ᶜ δ) (q ·ᶜ δ′) ⟩
      (γ , y ≔ r) +ᶜ p ·ᶜ δ +ᶜ q ·ᶜ δ′
        ≈⟨ +ᶜ-congˡ (+ᶜ-comm (p ·ᶜ δ) (q ·ᶜ δ′)) ⟩
      (γ , y ≔ r) +ᶜ q ·ᶜ δ′ +ᶜ p ·ᶜ δ
        ≈˘⟨ +ᶜ-assoc (γ , y ≔ r) (q ·ᶜ δ′) (p ·ᶜ δ) ⟩
      ((γ , y ≔ r) +ᶜ q ·ᶜ δ′) +ᶜ p ·ᶜ δ
        ≈˘⟨ +ᶜ-congˡ (·ᶜ-congʳ (+-identityʳ p)) ⟩
      ((γ , y ≔ r) +ᶜ q ·ᶜ δ′) +ᶜ (p + 𝟘) ·ᶜ δ
        ≈˘⟨ +ᶜ-congˡ (·ᶜ-congʳ (+-congˡ (·-zeroʳ q))) ⟩
      ((γ , y ≔ r) +ᶜ q ·ᶜ δ′) +ᶜ (p + q · 𝟘) ·ᶜ δ ∎
      where
      open RPo ≤ᶜ-poset
    lemma₂ : p′ ≤ p + q · 𝟘
    lemma₂ = begin
      p′         ≤⟨ p′≤p ⟩
      p          ≈˘⟨ +-identityʳ p ⟩
      p + 𝟘      ≈˘⟨ +-congˡ (·-zeroʳ q) ⟩
      p + q · 𝟘  ∎
      where
      open RPo ≤-poset
  ▸-heapLookup {H = H ∙●} {y +1} {q} {H′} {γ = γ ∙ p} {r}
      (there● {c = _ , ρ′} d) (▸H ∙●) γ⟨y⟩-q≤r =
    case ▸-heapLookup d ▸H γ⟨y⟩-q≤r of λ
      (δ , ▸t , ▸H′) →
    δ , ▸t
      , subst (_▸ʰ H′) ((cong ((γ , y ≔ r) +ᶜ q ·ᶜ wkConₘ ρ′ δ ∙_)
          (sym (trans (+-identityˡ _) (·-zeroʳ _))))) (▸H′ ∙●)

opaque

  -- For well-resourced natrec terms, there is a valid
  -- choice for the multiplicity.

  ▸natrec→Ok-nr :
    ¬ Nr-not-available →
    γ ▸[ m ] natrec p q r A z s t →
    ∃ λ q′ → Ok-natrec-multiplicity p r q′
  ▸natrec→Ok-nr {p} {r} not-ok ▸nr =
    case inv-usage-natrec ▸nr of λ where
      (invUsageNatrec _ _ _ _ _ invUsageNatrecNr) →
        nr₂ p r , Ok-natrec-multiplicity.has-nr refl
      (invUsageNatrec _ _ _ _ _ (invUsageNatrecNoNr ⦃ (x) ⦄ _ _ _ _)) →
        ⊥-elim (not-ok x)
      (invUsageNatrec _ _ _ _ _ (invUsageNatrecNoNrGLB x-glb _)) →
        _ , no-nr x-glb

opaque

  -- An invariant of InvUsageNatrecₑ

  InvUsageNatrecₑ-≤ : InvUsageNatrecₑ p r q γ δ ρ η → q ≤ p + r · q × η ≤ᶜ wkConₘ ρ δ +ᶜ r ·ᶜ η
  InvUsageNatrecₑ-≤ {p} {r} {q} {γ} {δ} {ρ} = λ where
    (invUsageNatrecNr refl) → nr₂≤  , (begin
      wkConₘ ρ (nrᶜ p r γ δ 𝟘ᶜ)                      ≤⟨ wk-≤ᶜ ρ nrᶜ-suc ⟩
      wkConₘ ρ (δ +ᶜ p ·ᶜ 𝟘ᶜ +ᶜ r ·ᶜ nrᶜ p r γ δ 𝟘ᶜ) ≈⟨ wk-≈ᶜ ρ (+ᶜ-congˡ (+ᶜ-congʳ (·ᶜ-zeroʳ _))) ⟩
      wkConₘ ρ (δ +ᶜ 𝟘ᶜ +ᶜ r ·ᶜ nrᶜ p r γ δ 𝟘ᶜ)      ≈⟨ wk-≈ᶜ ρ (+ᶜ-congˡ (+ᶜ-identityˡ _)) ⟩
      wkConₘ ρ (δ +ᶜ r ·ᶜ nrᶜ p r γ δ 𝟘ᶜ)            ≈⟨ wk-+ᶜ ρ ⟩
      wkConₘ ρ δ +ᶜ wkConₘ ρ (r ·ᶜ nrᶜ p r γ δ 𝟘ᶜ)   ≈⟨ +ᶜ-congˡ (wk-·ᶜ ρ) ⟩
      wkConₘ ρ δ +ᶜ r ·ᶜ wkConₘ ρ (nrᶜ p r γ δ 𝟘ᶜ)   ∎)
    (invUsageNatrecNoNr {χ} x-glb χ-glb) → nrᵢ-GLB-≤ x-glb , (begin
      wkConₘ ρ χ                      ≤⟨ wk-≤ᶜ ρ (nrᵢᶜ-GLBᶜ-≤ᶜ χ-glb) ⟩
      wkConₘ ρ (δ +ᶜ r ·ᶜ χ)          ≈⟨ wk-+ᶜ ρ ⟩
      wkConₘ ρ δ +ᶜ wkConₘ ρ (r ·ᶜ χ) ≈⟨ +ᶜ-congˡ (wk-·ᶜ ρ) ⟩
      wkConₘ ρ δ +ᶜ r ·ᶜ wkConₘ ρ χ   ∎)
      where
      open ≤ᶜ-reasoning

-- Some properties proven under some assumptions about erased matches

module _ (nem : No-erased-matches′ type-variant UR) where

  opaque

    -- The multiplicity of a well-resourced eliminator is not zero

    ▸∣e∣≢𝟘 : ⦃ Has-well-behaved-zero M semiring-with-meet ⦄
           → γ ▸ᵉ[ 𝟙ᵐ ] e → ∣ e ∣ᵉ ≢ 𝟘 ⊎
             ∃₃ λ n (A : Term n) ρ → e ≡ emptyrecₑ 𝟘 A ρ × Emptyrec-allowed 𝟙ᵐ 𝟘
    ▸∣e∣≢𝟘 (∘ₑ x) = inj₁ non-trivial
    ▸∣e∣≢𝟘 (fstₑ x) = inj₁ non-trivial
    ▸∣e∣≢𝟘 sndₑ = inj₁ non-trivial
    ▸∣e∣≢𝟘 (prodrecₑ x ok) = inj₁ (nem non-trivial .proj₁ ok)
    ▸∣e∣≢𝟘 (natrecₑ _ _ _ ≡nr₂) =
      inj₁ (λ ≡𝟘 → nr₂≢𝟘 (trans (sym ≡nr₂) ≡𝟘))
    ▸∣e∣≢𝟘 (natrec-no-nrₑ _ _ _ q-glb _) =
      inj₁ λ ≡𝟘 → 𝟘≰𝟙 (≤-trans (≤-reflexive (sym ≡𝟘)) (q-glb .proj₁ 0))
    ▸∣e∣≢𝟘 (unitrecₑ x ok no-η) = inj₁ (no-η ∘→ nem non-trivial .proj₂ .proj₁ ok)
    ▸∣e∣≢𝟘 (emptyrecₑ {p} ok) =
      case is-𝟘? p of λ where
        (yes refl) → inj₂ (_ , _ , _ , refl , ok)
        (no p≢𝟘) → inj₁ p≢𝟘
    ▸∣e∣≢𝟘 (Jₑ x) rewrite nem non-trivial .proj₂ .proj₂ .proj₂ .proj₁ = inj₁ ω≢𝟘
    ▸∣e∣≢𝟘 (Kₑ x) rewrite nem non-trivial .proj₂ .proj₂ .proj₂ .proj₂ = inj₁ ω≢𝟘
    ▸∣e∣≢𝟘 ([]-congₑ ok) = inj₁ λ _ → nem non-trivial .proj₂ .proj₂ .proj₁ ok

  opaque

    -- The multiplicity of a well-resourced stack is either not zero
    -- or contains a non-erased application of emptyrec

    ▸∣S∣≢𝟘 : ⦃ Has-well-behaved-zero M semiring-with-meet ⦄
           → γ ▸ˢ S → ∣ S ∣ ≢ 𝟘 ⊎ (emptyrec₀∈ S × Emptyrec-allowed 𝟙ᵐ 𝟘)
    ▸∣S∣≢𝟘 ε = inj₁ non-trivial
    ▸∣S∣≢𝟘 (▸e ∙ ▸S) =
      case ▸∣S∣≢𝟘 ▸S of λ where
        (inj₂ (x , ok)) → inj₂ (there x , ok)
        (inj₁ ∣S∣≢𝟘) →
          case ▸∣e∣≢𝟘 (subst (_ ▸ᵉ[_] _) (≢𝟘→⌞⌟≡𝟙ᵐ ∣S∣≢𝟘) ▸e) of λ where
            (inj₂ (_ , _ , _ , refl , ok)) → inj₂ (here , ok)
            (inj₁ ∣e∣≢𝟘) → inj₁ λ ∣eS∣≡𝟘 →
              case zero-product ∣eS∣≡𝟘 of λ where
                (inj₁ ∣S∣≡𝟘) → ∣S∣≢𝟘 ∣S∣≡𝟘
                (inj₂ ∣e∣≡𝟘) → ∣e∣≢𝟘 ∣e∣≡𝟘

-- Some properties proven under the assumption that the modality
-- supports subtraction.

module _ ⦃ _ : Has-well-behaved-zero M semiring-with-meet ⦄
         (subtraction-ok : Supports-subtraction) where

  -- Under some assumptions, lookup always succeeds for well-resourced heaps

  opaque

    ↦→↦[] : {H : Heap k _}
        → H ⊢ y ↦ c′ → γ ▸ʰ H → γ ⟨ y ⟩ ≤ p + q
        → ∃ λ H′ → H ⊢ y ↦[ q ] c′ ⨾ H′
    ↦→↦[] here (_∙_ ▸H (▸ᶜ _ mq≤p′)) p′≤p+q′ =
      _ , here (subtraction-ok (≤-trans mq≤p′ p′≤p+q′) .proj₂)
    ↦→↦[] {y = y +1} {γ = γ ∙ r} {p} {q} (there d) (_∙_ {ρ} {δ} ▸H _) γ⟨y⟩≤p+q =
      case ↦→↦[] d ▸H lemma of λ
        (_ , d′) →
      _ , there d′
      where
      open RPo ≤-poset
      lemma : (γ +ᶜ r ·ᶜ wkConₘ ρ δ) ⟨ y ⟩ ≤ (p + (r ·ᶜ wkConₘ ρ δ) ⟨ y ⟩) + q
      lemma = begin
        (γ +ᶜ r ·ᶜ wkConₘ ρ δ) ⟨ y ⟩      ≡⟨ lookup-distrib-+ᶜ γ _ y ⟩
        γ ⟨ y ⟩ + (r ·ᶜ wkConₘ ρ δ) ⟨ y ⟩  ≤⟨ +-monotoneˡ γ⟨y⟩≤p+q ⟩
        (p + q) + (r ·ᶜ wkConₘ ρ δ) ⟨ y ⟩ ≈⟨ +-assoc p q _ ⟩
        p + q + (r ·ᶜ wkConₘ ρ δ) ⟨ y ⟩   ≈⟨ +-congˡ (+-comm q _) ⟩
        p + (r ·ᶜ wkConₘ ρ δ) ⟨ y ⟩ + q   ≈˘⟨ +-assoc p _ q ⟩
        (p + (r ·ᶜ wkConₘ ρ δ) ⟨ y ⟩) + q ∎
    ↦→↦[] (there● d) (▸H ∙●) γ⟨y⟩≤p+q =
      case ↦→↦[] d ▸H γ⟨y⟩≤p+q of λ
        (_ , d′) →
      _ , there● d′

  opaque

    -- A variant of the above property with usage of states

    ▸↦→↦[] : {H : Heap k _}
          → H ⊢ wkVar ρ x ↦ c′
          → ▸ ⟨ H , var x , ρ , S ⟩
          → ∃ λ H′ → H ⊢ wkVar ρ x ↦[ ∣ S ∣ ] c′ ⨾ H′
    ▸↦→↦[] {ρ} {x} {S} d ▸s =
      let _ , _ , ▸H , _ , γ⟨x⟩≤ = ▸ₛ-var-inv′ ▸s
      in  ↦→↦[] d ▸H (≤-trans γ⟨x⟩≤ (≤-reflexive (+-comm _ _)))

  opaque

    -- If a pointer points to a dummy entry in a well-resource heap then
    -- the corresponding entry in the usage context is 𝟘.

    ▸H● : H ⊢ y ↦● → γ ▸ʰ H → γ ⟨ y ⟩ ≡ 𝟘
    ▸H● here (▸H ∙●) = refl
    ▸H● {γ = γ ∙ p} (there d) (▸H ∙ x) =
      +ᶜ-positive-⟨⟩ γ (▸H● d ▸H) .proj₁
    ▸H● (there● d) (▸H ∙●) = ▸H● d ▸H

  opaque

    -- In a well-resourced state with a variable in head position with a
    -- corresponding dummy entry in the heap, the stack multiplicity and usage
    -- context of the stack are both 𝟘.

    ▸s● : H ⊢ wkVar ρ x ↦● → ▸ ⟨ H , var x , ρ , S ⟩ → ∣ S ∣ ≡ 𝟘
    ▸s● d ▸s =
      let _ , _ , ▸H , ▸S , γ⟨x⟩≤ = ▸ₛ-var-inv′ ▸s
      in  +-positiveˡ (𝟘≮ (≤-trans (≤-reflexive (sym (▸H● d ▸H))) γ⟨x⟩≤))
