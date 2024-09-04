------------------------------------------------------------------------
-- Properties of the usage relation for Heaps, Stacks and States.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Variant
open import Tools.Bool

module Heap.Usage.Properties
  {a} {M : Set a} {𝕄 : Modality M}
  (type-variant : Type-variant)
  (UR : Usage-restrictions 𝕄)
  (erased-heap : Bool)
  (open Modality 𝕄)
  ⦃ _ : Has-nr M semiring-with-meet ⦄
  ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
  where

open import Definition.Untyped M
open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄
open import Graded.Restrictions 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Inversion 𝕄 UR
open import Graded.Usage.Properties 𝕄 UR
open import Graded.Usage.Weakening 𝕄 UR

open import Heap.Untyped type-variant UR
open import Heap.Untyped.Properties type-variant UR
open import Heap.Usage type-variant UR erased-heap

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum hiding (sym)
import Tools.Reasoning.PartialOrder as RPo


private variable
  k n : Nat
  γ δ η : Conₘ _
  p q r : M
  m : Mode
  H H′ : Heap _ _
  x : Fin _
  y : Ptr _
  t : Term _
  E E′ : Env _ _
  S : Stack _
  e : Elim _
  c : Closureₘ _ _
  c′ : Closure _ _

opaque

  -- Usage for erased heaps

  ▸erasedHeap : ⦃ T erased-heap ⦄ →
              ∀ {n} → 𝟘ᶜ ▸ʰ erasedHeap n
  ▸erasedHeap {(0)} = ε
  ▸erasedHeap {(1+ n)} = ▸erasedHeap ∙●

opaque

  -- Well-usage for the initial state

  ▸initial : n ≡ 0 ⊎ T erased-heap → 𝟘ᶜ {n} ▸ t → 𝟘ᶜ ⨾ 𝟘ᶜ ⨾ 𝟘ᶜ ▸[ 𝟙ᵐ ] initial t
  ▸initial P ▸t =
    lemma P , ▸t , ε , 𝟙ᵐ≤ᵐ
            , ≤ᶜ-reflexive (≈ᶜ-sym (≈ᶜ-trans (+ᶜ-identityʳ _) (·ᶜ-zeroʳ _)))
      where
      lemma : n ≡ 0 ⊎ T erased-heap → 𝟘ᶜ ▸ʰ erasedHeap n
      lemma (inj₁ refl) = ε
      lemma (inj₂ x) = ▸erasedHeap ⦃ x ⦄

opaque

  -- Usage of closures where the mode is 𝟙ᵐ

  ▸ᶜ¹ : γ ▸ t
      → q ≤ p
      → γ ⨾ p ▸ᶜ (q , t , E)
  ▸ᶜ¹ {γ = γ} {t} {q} {p} {E = E} ▸t q≤p =
    let 𝟙q≡q = ·-identityˡ q
    in  subst (λ x → γ ⨾ p ▸ᶜ (x , t , E)) 𝟙q≡q
         (▸ᶜ ▸t (≤-trans (≤-reflexive 𝟙q≡q) q≤p))

opaque

  -- Usage of closures where the mode is 𝟘ᵐ

  ▸ᶜ⁰ : ∀ {ok}
      → γ ▸[ 𝟘ᵐ[ ok ] ] t
      → γ ⨾ 𝟘 ▸ᶜ (𝟘 , t , E)
  ▸ᶜ⁰ {γ} {t} {E} ▸t =
    subst (λ x → γ ⨾ 𝟘 ▸ᶜ (x , t , E))
      (·-zeroˡ 𝟘)
      (▸ᶜ ▸t (≤-reflexive (·-zeroˡ _)))

opaque

  -- Usage of closures where the mode is 𝟘ᵐ?

  ▸ᶜ⁰? : γ ▸[ 𝟘ᵐ? ] t
       → γ ⨾ 𝟘 ▸ᶜ (𝟘 , t , E)
  ▸ᶜ⁰? {γ} {t} {E} =
    𝟘ᵐ?-elim (λ m → γ ▸[ m ] t → γ ⨾ 𝟘 ▸ᶜ (𝟘 , t , E))
      ▸ᶜ⁰ (λ _ ▸t → ▸ᶜ¹ ▸t ≤-refl)

opaque

  -- Subsumption for closures

  subᶜ : γ ⨾ p ▸ᶜ c → p ≤ q → γ ⨾ q ▸ᶜ c
  subᶜ (▸ᶜ ▸t p′≤p) p≤q = ▸ᶜ ▸t (≤-trans p′≤p p≤q)

opaque

  -- A lemma for well-resourced closures

  ▸ᶜᵐ : γ ▸[ m ] t → m ≤ᵐ p → γ ⨾ p ▸ᶜ (p , t , E)
  ▸ᶜᵐ ▸t 𝟘ᵐ≤ᵐ𝟘 = ▸ᶜ⁰ ▸t
  ▸ᶜᵐ ▸t 𝟙ᵐ≤ᵐ = ▸ᶜ¹ ▸t ≤-refl

opaque

  -- A lemma for well-resourced closures

  ▸ᶜᵐᵖ : γ ▸[ m ᵐ· p ] t → m ≤ᵐ q → γ ⨾ (q · p) ▸ᶜ (q · p , t , E)
  ▸ᶜᵐᵖ {p} ▸t 𝟘ᵐ≤ᵐ𝟘 rewrite ·-zeroˡ p = ▸ᶜ⁰ ▸t
  ▸ᶜᵐᵖ {p} ▸t 𝟙ᵐ≤ᵐ =
    case is-𝟘? p of λ where
      (yes refl) → subst (λ x → _ ⨾ x ▸ᶜ (x , _)) (sym (·-zeroʳ _)) (▸ᶜ⁰? (▸-cong ⌞𝟘⌟≡𝟘ᵐ? ▸t))
      (no p≢𝟘) → ▸ᶜ¹ (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) ▸t) ≤-refl

opaque

  𝟘ᵐ?≤ᵐ𝟘 : 𝟘ᵐ? ≤ᵐ 𝟘
  𝟘ᵐ?≤ᵐ𝟘 =
    𝟘ᵐ?-elim (_≤ᵐ 𝟘) 𝟘ᵐ≤ᵐ𝟘 λ _ → 𝟙ᵐ≤ᵐ

opaque

  -- The relation ≤ᵐ repects multiplication in a certain sense.

  ≤ᵐ-· : m ≤ᵐ p → m ᵐ· q ≤ᵐ p · q
  ≤ᵐ-· {q = q} 𝟘ᵐ≤ᵐ𝟘 =
    subst (_ ≤ᵐ_) (sym (·-zeroˡ _)) 𝟘ᵐ≤ᵐ𝟘
  ≤ᵐ-· {q = q} 𝟙ᵐ≤ᵐ =
    case is-𝟘? q of λ where
      (yes refl) → subst₂ _≤ᵐ_ (sym ⌞𝟘⌟≡𝟘ᵐ?) (sym (·-zeroʳ _)) 𝟘ᵐ?≤ᵐ𝟘
      (no q≢𝟘) → subst (_≤ᵐ _) (sym (≢𝟘→⌞⌟≡𝟙ᵐ q≢𝟘)) 𝟙ᵐ≤ᵐ

opaque

  -- Multiplying a grade with a "smaller" mode is the same as doing nothing

  ≤ᵐ-·⌜⌝ : m ≤ᵐ p → p · ⌜ m ⌝ ≡ p
  ≤ᵐ-·⌜⌝ 𝟘ᵐ≤ᵐ𝟘 = ·-zeroʳ _
  ≤ᵐ-·⌜⌝ 𝟙ᵐ≤ᵐ = ·-identityʳ _

opaque

  -- Multiplying a grade with a "smaller" mode is the same as doing nothing

  ≤ᵐ-⌜⌝· : m ≤ᵐ p → ⌜ m ⌝ · p ≡ p
  ≤ᵐ-⌜⌝· 𝟘ᵐ≤ᵐ𝟘 = ·-zeroˡ _
  ≤ᵐ-⌜⌝· 𝟙ᵐ≤ᵐ = ·-identityˡ _

opaque

  𝟘ᵐ≤ᵐp→p≡𝟘 : ∀ {ok} → 𝟘ᵐ[ ok ] ≤ᵐ p → p ≡ 𝟘
  𝟘ᵐ≤ᵐp→p≡𝟘 𝟘ᵐ≤ᵐ𝟘 = refl

opaque

  ≤ᵐ𝟘 : m ≤ᵐ 𝟘
  ≤ᵐ𝟘 {m = 𝟘ᵐ} = 𝟘ᵐ≤ᵐ𝟘
  ≤ᵐ𝟘 {m = 𝟙ᵐ} = 𝟙ᵐ≤ᵐ

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

  -- If erased matches are turned on then a well-resourced heap does
  -- not contain any erased entries.

  no-erased-heap : {H : Heap k n} → T (not erased-heap) → γ ▸ʰ H → k ≡ 0
  no-erased-heap _ ε = refl
  no-erased-heap ¬eh (▸H ∙ x) = no-erased-heap ¬eh ▸H
  no-erased-heap ¬eh (_∙● ⦃ (eh) ⦄ _) = ⊥-elim (not-T-and-¬T erased-heap eh ¬eh)

-- opaque

--   -- A well-resourced heap either has no erased entries or erased matches
--   -- are turned off.

--   no-erased-heap⊎no-erased-matches : {H : Heap k n} → γ ▸ʰ H → k ≡ 0 ⊎ T (not erased-matches)
--   no-erased-heap⊎no-erased-matches ▸H = lemma erased-matches refl ▸H
--     where
--     lemma : {H : Heap k n} → (b : Bool) → b ≡ erased-matches
--           → γ ▸ʰ H → k ≡ 0 ⊎ T (not erased-matches)
--     lemma false refl ▸H = inj₂ _
--     lemma true refl ε = inj₁ refl
--     lemma true refl (▸H ∙ x) = lemma true refl ▸H

opaque

  -- An inversion lemma for ▸ʰ

  inv-▸ʰ● : γ ∙ p ▸ʰ H ∙● → p ≡ 𝟘 × γ ▸ʰ H
  inv-▸ʰ● (▸H ∙●) = refl , ▸H

opaque

  -- A well-resourced heap under the zero-context has all grades bounded by 𝟘.

  𝟘▸H→H≤𝟘 : 𝟘ᶜ ▸ʰ H → H ≤ʰ 𝟘
  𝟘▸H→H≤𝟘 {H = ε} ε = ε
  𝟘▸H→H≤𝟘 {H = H ∙ c} (_∙_ {E = E} {δ} ▸H (▸ᶜ _ p≤𝟘)) =
    𝟘▸H→H≤𝟘 (subst (_▸ʰ _) (≈ᶜ→≡ lemma) ▸H) ∙ p≤𝟘
    where
    open import Tools.Reasoning.Equivalence Conₘ-setoid
    lemma : 𝟘ᶜ +ᶜ 𝟘 ·ᶜ wkᶜ E δ ≈ᶜ 𝟘ᶜ
    lemma = begin
      𝟘ᶜ +ᶜ 𝟘 ·ᶜ wkᶜ E δ  ≈⟨ +ᶜ-identityˡ _ ⟩
      𝟘 ·ᶜ wkᶜ E δ        ≈⟨ ·ᶜ-zeroˡ _ ⟩
      𝟘ᶜ                  ∎
  𝟘▸H→H≤𝟘 {H = H ∙●} ▸H = 𝟘▸H→H≤𝟘 (inv-▸ʰ● ▸H .proj₂) ∙●

opaque

  -- In a well-resorced heap, a pointer lookup yields a well-resourced
  -- term and a well-resourced heap.

  ▸-heapLookup : ⦃ Has-well-behaved-zero M semiring-with-meet ⦄
               → H ⊢ y ↦[ q ] t , E ⨾ H′
               → γ ▸ʰ H
               → γ ⟨ y ⟩ - q ≤ r
               → ∃₂ λ m δ → δ ▸[ m ] t × (γ , y ≔ r) +ᶜ q ·ᶜ wkᶜ E δ ▸ʰ H′ × m ≤ᵐ q
  ▸-heapLookup {q} {r} (here {r = r′} mp′-q≡r′)
      (_∙_ {p} ▸H (▸ᶜ {m} {q = p′} ▸t mp′≤p)) p-q≤r =
        case singleton m of λ where
          (𝟙ᵐ , refl) → _ , _ , ▸t , subₕ ▸H lemma₁ ∙ ▸ᶜ¹ ▸t lemma₂ , 𝟙ᵐ≤ᵐ
          (𝟘ᵐ , refl) →
            case 𝟘≮ (subst (_≤ _) (·-zeroˡ _) mp′≤p) of λ {
              refl →
            case 𝟘-p≤q p-q≤r of λ {
              (refl , refl) →
            case 𝟘-p≡q (subst (_- 𝟘 ≡ _) (·-zeroˡ _) mp′-q≡r′) of λ {
              (refl , _) →
            _ , _ , ▸t , subₕ ▸H lemma₁
              ∙ subst (λ x → _ ⨾ 𝟘 + 𝟘 · 𝟘 ▸ᶜ (x , _)) (·-zeroˡ _)
                  (▸ᶜ ▸t (≤-reflexive (sym (+-identityˡ _))))
              , 𝟘ᵐ≤ᵐ𝟘 }}}
    where
    lemma₁ : ∀ {n} {γ δ : Conₘ n} → γ +ᶜ p ·ᶜ δ ≤ᶜ (γ +ᶜ q ·ᶜ δ) +ᶜ (r + q · 𝟘) ·ᶜ δ
    lemma₁ {γ} {δ} = begin
      γ +ᶜ p ·ᶜ δ                       ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneˡ p-q≤r) ⟩
      γ +ᶜ (r + q) ·ᶜ δ                 ≈⟨ +ᶜ-congˡ (·ᶜ-distribʳ-+ᶜ r q δ) ⟩
      γ +ᶜ (r ·ᶜ δ +ᶜ q ·ᶜ δ)           ≈⟨ +ᶜ-congˡ (+ᶜ-comm (r ·ᶜ δ) (q ·ᶜ δ)) ⟩
      γ +ᶜ (q ·ᶜ δ +ᶜ r ·ᶜ δ)           ≈˘⟨ +ᶜ-assoc γ (q ·ᶜ δ) (r ·ᶜ δ) ⟩
      (γ +ᶜ q ·ᶜ δ) +ᶜ r ·ᶜ δ           ≈˘⟨ +ᶜ-congˡ (·ᶜ-congʳ (+-identityʳ r)) ⟩
      (γ +ᶜ q ·ᶜ δ) +ᶜ (r + 𝟘) ·ᶜ δ     ≈˘⟨ +ᶜ-congˡ (·ᶜ-congʳ (+-congˡ (·-zeroʳ q))) ⟩
      (γ +ᶜ q ·ᶜ δ) +ᶜ (r + q · 𝟘) ·ᶜ δ ∎
      where
      open RPo ≤ᶜ-poset
    lemma₂ : r′ ≤ r + q · 𝟘
    lemma₂ = begin
      r′ ≤⟨ -≡≤-monotoneˡ mp′≤p mp′-q≡r′ p-q≤r ⟩
      r ≈˘⟨ +-identityʳ r ⟩
      r + 𝟘 ≈˘⟨ +-congˡ (·-zeroʳ q) ⟩
      r + q · 𝟘 ∎
      where
      open RPo ≤-poset
  ▸-heapLookup {H = H ∙ (p′ , u , E)} {y +1} {q} {γ = γ ∙ p} {r}
      (there {c = _ , E′} d) (_∙_ {δ} ▸H (▸ᶜ ▸u p′≤p)) γ⟨y⟩-q≤r  =
    case p+q-r≤p-r+q γ⟨y⟩-q≤r ((p ·ᶜ wkᶜ E δ) ⟨ y ⟩) of λ
      γ⟨y⟩+pδ⟨y⟩-q≤pδ⟨y⟩+r →
    case subst (_- q ≤ ((p ·ᶜ wkᶜ E δ) ⟨ y ⟩ + r))
           (sym (lookup-distrib-+ᶜ γ (p ·ᶜ wkᶜ E δ) y))
           γ⟨y⟩+pδ⟨y⟩-q≤pδ⟨y⟩+r of λ
      γ+pδ⟨y⟩-q≤pδ⟨y⟩+r →
    case ▸-heapLookup d ▸H γ+pδ⟨y⟩-q≤pδ⟨y⟩+r of λ
      (_ , δ′ , ▸t , ▸H′ , m≤ᵐS) →
    _ , _ , ▸t
      , subₕ ▸H′ lemma₁ ∙ ▸ᶜ ▸u lemma₂
      , m≤ᵐS
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
      (there● {c = _ , E′} d) (▸H ∙●) γ⟨y⟩-q≤r =
    case ▸-heapLookup d ▸H γ⟨y⟩-q≤r of λ
      (_ , δ , ▸t , ▸H′ , m≤ᵐS) →
    _ , δ , ▸t
      , subst (_▸ʰ H′) ((cong ((γ , y ≔ r) +ᶜ q ·ᶜ wkᶜ E′ δ ∙_)
          (sym (trans (+-identityˡ _) (·-zeroʳ _))))) (▸H′ ∙●)
      , m≤ᵐS

-- Some properties proven under some assumptions about erased matches

module _ (nem : No-erased-matches′ type-variant UR) where

  opaque

    -- The multiplicity of a well-resourced eliminator is not zero

    ▸∣e∣≢𝟘 : ⦃ Has-well-behaved-zero M semiring-with-meet ⦄
           → γ ▸ᵉ[ 𝟙ᵐ ] e → ∣ e ∣ᵉ ≢ 𝟘
    ▸∣e∣≢𝟘 (∘ₑ x) = non-trivial
    ▸∣e∣≢𝟘 (fstₑ x) = non-trivial
    ▸∣e∣≢𝟘 sndₑ = non-trivial
    ▸∣e∣≢𝟘 (prodrecₑ x ok) = nem non-trivial .proj₁ ok
    ▸∣e∣≢𝟘 (natrecₑ x x₁ x₂) = nr₂≢𝟘
    ▸∣e∣≢𝟘 (unitrecₑ x ok no-η) = no-η ∘→ nem non-trivial .proj₂ .proj₁ ok
    ▸∣e∣≢𝟘 (Jₑ x) rewrite nem non-trivial .proj₂ .proj₂ .proj₂ .proj₁ = ω≢𝟘
    ▸∣e∣≢𝟘 (Kₑ x) rewrite nem non-trivial .proj₂ .proj₂ .proj₂ .proj₂ = ω≢𝟘
    ▸∣e∣≢𝟘 ([]-congₑ ok) = λ _ → nem non-trivial .proj₂ .proj₂ .proj₁ ok
    ▸∣e∣≢𝟘 sucₑ = non-trivial

  opaque

    -- The multiplicity of a well-resourced stack is not zero

    ▸∣S∣≢𝟘 : ⦃ Has-well-behaved-zero M semiring-with-meet ⦄
           → γ ▸ˢ S → ∣ S ∣ ≢ 𝟘
    ▸∣S∣≢𝟘 ε = non-trivial
    ▸∣S∣≢𝟘 (_∙_ {m} (▸e , m≤) ▸S) ∣eS∣≡𝟘 =
      case zero-product ∣eS∣≡𝟘 of λ where
        (inj₁ ∣S∣≡𝟘) → ▸∣S∣≢𝟘 ▸S ∣S∣≡𝟘
        (inj₂ ∣e∣≡𝟘) →
          case singleton m of λ where
            (𝟘ᵐ , refl) → ▸∣S∣≢𝟘 ▸S (𝟘ᵐ≤ᵐp→p≡𝟘 m≤)
            (𝟙ᵐ , refl) → ▸∣e∣≢𝟘 ▸e ∣e∣≡𝟘

-- Some properties proven under the assumption that the modality
-- supports subtraction.

module _ ⦃ _ : Has-well-behaved-zero M semiring-with-meet ⦄
         (subtraction-ok : Supports-subtraction) where

  opaque

    -- In a well-resorced heap, lookup of q copies succeeds for pointers whose
    -- associated grade is at most p + q for some p.

    ▸H→y↦ : {H : Heap k _}
          → γ ▸ʰ H → γ ⟨ y ⟩ ≤ p + q → q ≢ 𝟘 ⊎ k ≡ 0
          → ∃₃ λ n (c : Closure _ n) H′ → H ⊢ y ↦[ q ] c ⨾ H′
    ▸H→y↦ {y = y0} {p} {q} (_∙_ {p = p′} ▸H (▸ᶜ {q = q′} _ mq′≤p′)) p′≤p+q _ =
      _ , _ , _
        , here (subtraction-ok (≤-trans mq′≤p′ p′≤p+q) .proj₂)
    ▸H→y↦ {y = y0} {(p)} {(q)} (▸H ∙●) 𝟘≤p+q (inj₁ q≢𝟘) =
      ⊥-elim (q≢𝟘 (+-positiveʳ (𝟘≮ 𝟘≤p+q)))
    ▸H→y↦ {γ = γ ∙ r} {y = y +1} {p} {q} (_∙_ {E} {δ} ▸H _) γ⟨y⟩≤p+q q≢𝟘 =
      case ▸H→y↦ {y = y} ▸H lemma q≢𝟘 of λ
        (_ , _ , _ , d) →
      _ , _ , _ , there d
      where
      open RPo ≤-poset
      lemma : (γ +ᶜ r ·ᶜ wkᶜ E δ) ⟨ y ⟩ ≤ (p + (r ·ᶜ wkᶜ E δ) ⟨ y ⟩) + q
      lemma = begin
        (γ +ᶜ r ·ᶜ wkᶜ E δ) ⟨ y ⟩      ≡⟨ lookup-distrib-+ᶜ γ _ y ⟩
        γ ⟨ y ⟩ + (r ·ᶜ wkᶜ E δ) ⟨ y ⟩  ≤⟨ +-monotoneˡ γ⟨y⟩≤p+q ⟩
        (p + q) + (r ·ᶜ wkᶜ E δ) ⟨ y ⟩ ≈⟨ +-assoc p q _ ⟩
        p + q + (r ·ᶜ wkᶜ E δ) ⟨ y ⟩   ≈⟨ +-congˡ (+-comm q _) ⟩
        p + (r ·ᶜ wkᶜ E δ) ⟨ y ⟩ + q   ≈˘⟨ +-assoc p _ q ⟩
        (p + (r ·ᶜ wkᶜ E δ) ⟨ y ⟩) + q ∎
    ▸H→y↦ {γ = γ ∙ r} {y = y +1} {p} {q} (▸H ∙●) γ⟨y⟩≤p+q (inj₁ q≢𝟘) =
      case ▸H→y↦ {y = y} ▸H γ⟨y⟩≤p+q (inj₁ q≢𝟘) of λ
        (_ , _ , _ , d) →
      _ , _ , _ , there● d

  opaque

    -- A variant of the above property with usage of states

    ▸s→y↦ : {H : Heap k _}
          → T (not erased-heap) ⊎ No-erased-matches′ type-variant UR
          → γ ⨾ δ ⨾ η ▸[ m ] ⟨ H , var x , E , S ⟩
          → ∃₃ λ n (c : Closure _ n) H′ → H ⊢ wkVar E x ↦[ ∣ S ∣ ] c ⨾ H′
    ▸s→y↦ {γ} {δ} {η} {m} {x} {E} {S} prop (▸H , ▸t , ▸S , m≤ , γ≤) =
      case prop of λ where
        (inj₁ ¬eh) → ▸H→y↦ ▸H lemma (inj₂ (no-erased-heap ¬eh ▸H))
        (inj₂ nem) → ▸H→y↦ ▸H lemma (inj₁ (▸∣S∣≢𝟘 nem ▸S))
      where
      open RPo ≤-poset
      lemma′ : (∣ S ∣ ·ᶜ wkᶜ E δ) ⟨ wkVar E x ⟩ ≤ ∣ S ∣
      lemma′ = begin
        (∣ S ∣ ·ᶜ wkᶜ E δ) ⟨ wkVar E x ⟩ ≈⟨ lookup-distrib-·ᶜ (wkᶜ E δ) ∣ S ∣ (wkVar E x) ⟩
        ∣ S ∣ · wkᶜ E δ ⟨ wkVar E x ⟩    ≡⟨ cong (∣ S ∣ ·_) (wk-⟨⟩ E) ⟩
        ∣ S ∣ · δ ⟨ x ⟩                  ≤⟨ ·-monotoneʳ (lookup-monotone x (inv-usage-var ▸t)) ⟩
        ∣ S ∣ · (𝟘ᶜ , x ≔ ⌜ m ⌝) ⟨ x ⟩   ≡⟨ cong (∣ S ∣ ·_) (update-lookup 𝟘ᶜ x) ⟩
        ∣ S ∣ · ⌜ m ⌝                   ≈⟨ ≤ᵐ-·⌜⌝ m≤ ⟩
        ∣ S ∣                           ∎
      lemma : γ ⟨ wkVar E x ⟩ ≤ η ⟨ wkVar E x ⟩ + ∣ S ∣
      lemma = begin
        γ ⟨ wkVar E x ⟩                                   ≤⟨ lookup-monotone (wkVar E x) γ≤ ⟩
        (∣ S ∣ ·ᶜ wkᶜ E δ +ᶜ η) ⟨ wkVar E x ⟩             ≡⟨ lookup-distrib-+ᶜ (∣ S ∣ ·ᶜ wkᶜ E δ) η (wkVar E x) ⟩
        (∣ S ∣ ·ᶜ wkᶜ E δ) ⟨ wkVar E x ⟩ + η ⟨ wkVar E x ⟩ ≤⟨ +-monotoneˡ lemma′ ⟩
        ∣ S ∣ + η ⟨ wkVar E x ⟩                           ≈⟨ +-comm _ _ ⟩
        η ⟨ wkVar E x ⟩ + ∣ S ∣                           ∎

  opaque

    -- In a well-resourced state, lookup with update succeeds and has the same
    -- result as lookup without update

    ▸↦→↦[] : {H : Heap k _}
           → T (not erased-heap) ⊎ No-erased-matches′ type-variant UR
           → H ⊢ wkVar E x ↦ c′ → γ ⨾ δ ⨾ η ▸[ m ] ⟨ H , var x , E , S ⟩
           → ∃ λ H′ → H ⊢ wkVar E x ↦[ ∣ S ∣ ] c′ ⨾ H′
    ▸↦→↦[] prop d ▸s =
      case ▸s→y↦ prop ▸s of λ
        (_ , _ , _ , d′) →
      case lookup-det′ d (↦[]→↦ d′) of λ {
        (refl , refl , refl) →
      _ , d′ }
