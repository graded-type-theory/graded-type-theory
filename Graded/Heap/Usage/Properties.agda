------------------------------------------------------------------------
-- Properties of the usage relation for Heaps, Stacks and States.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Variant
open import Tools.Bool

module Graded.Heap.Usage.Properties
  {a} {M : Set a} {𝕄 : Modality M}
  (type-variant : Type-variant)
  (UR : Usage-restrictions 𝕄)
  (erased-heap : Bool)
  (open Modality 𝕄)
  ⦃ _ : Has-nr M semiring-with-meet ⦄
  ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
  where

open Usage-restrictions UR

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

open import Graded.Heap.Untyped type-variant UR
open import Graded.Heap.Usage type-variant UR erased-heap

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
  ρ ρ′ : Wk _ _
  S : Stack _
  e : Elim _
  c : Entryₘ _ _
  c′ : Entry _ _

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

  -- If heaps are not allowed to be erased then lookup to ● will always fail

  ¬erased-heap→¬↦● : ⦃ neh : T (not erased-heap) ⦄ → γ ▸ʰ H → H ⊢ y ↦● → ⊥
  ¬erased-heap→¬↦● (▸H ∙●) here = not-T-and-¬T′ erased-heap
  ¬erased-heap→¬↦● (▸H ∙ _) (there d) = ¬erased-heap→¬↦● ▸H d
  ¬erased-heap→¬↦● (▸H ∙●) (there● d) = ¬erased-heap→¬↦● ▸H d

opaque

  -- Usage of closures where the mode is 𝟙ᵐ

  ▸ᶜ¹ : γ ▸ t
      → q ≤ p
      → γ ⨾ p ▸ᶜ (q , t , ρ)
  ▸ᶜ¹ {γ} {t} {q} {p} {ρ} ▸t q≤p =
    let 𝟙q≡q = ·-identityˡ q
    in  subst (λ x → γ ⨾ p ▸ᶜ (x , t , ρ)) 𝟙q≡q
         (▸ᶜ ▸t (≤-trans (≤-reflexive 𝟙q≡q) q≤p))

opaque

  -- Usage of closures where the mode is 𝟘ᵐ

  ▸ᶜ⁰ : ∀ {ok}
      → γ ▸[ 𝟘ᵐ[ ok ] ] t
      → γ ⨾ 𝟘 ▸ᶜ (𝟘 , t , ρ)
  ▸ᶜ⁰ {γ} {t} {ρ} ▸t =
    subst (λ x → γ ⨾ 𝟘 ▸ᶜ (x , t , ρ))
      (·-zeroˡ 𝟘)
      (▸ᶜ ▸t (≤-reflexive (·-zeroˡ _)))

opaque

  -- Usage of closures where the mode is 𝟘ᵐ?

  ▸ᶜ⁰? : γ ▸[ 𝟘ᵐ? ] t
       → γ ⨾ 𝟘 ▸ᶜ (𝟘 , t , ρ)
  ▸ᶜ⁰? {γ} {t} {ρ} =
    𝟘ᵐ?-elim (λ m → γ ▸[ m ] t → γ ⨾ 𝟘 ▸ᶜ (𝟘 , t , ρ))
      ▸ᶜ⁰ (λ _ ▸t → ▸ᶜ¹ ▸t ≤-refl)

opaque

  -- Subsumption for closures

  subᶜ : γ ⨾ p ▸ᶜ c → p ≤ q → γ ⨾ q ▸ᶜ c
  subᶜ (▸ᶜ ▸t p′≤p) p≤q = ▸ᶜ ▸t (≤-trans p′≤p p≤q)

opaque

  -- A lemma for well-resourced closures

  ▸ᶜᵐ : γ ▸[ m ] t → m ≤ᵐ p → γ ⨾ p ▸ᶜ (p , t , ρ)
  ▸ᶜᵐ ▸t 𝟘ᵐ≤ᵐ𝟘 = ▸ᶜ⁰ ▸t
  ▸ᶜᵐ ▸t 𝟙ᵐ≤ᵐ = ▸ᶜ¹ ▸t ≤-refl

opaque

  -- A lemma for well-resourced closures

  ▸ᶜᵐᵖ : γ ▸[ m ᵐ· p ] t → m ≤ᵐ q → γ ⨾ (q · p) ▸ᶜ (q · p , t , ρ)
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

opaque

  -- An inversion lemma for ▸ʰ

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
    lemma : 𝟘ᶜ +ᶜ 𝟘 ·ᶜ wkᶜ ρ δ ≈ᶜ 𝟘ᶜ
    lemma = begin
      𝟘ᶜ +ᶜ 𝟘 ·ᶜ wkᶜ ρ δ  ≈⟨ +ᶜ-identityˡ _ ⟩
      𝟘 ·ᶜ wkᶜ ρ δ        ≈⟨ ·ᶜ-zeroˡ _ ⟩
      𝟘ᶜ                  ∎
  𝟘▸H→H≤𝟘 {H = H ∙●} ▸H = 𝟘▸H→H≤𝟘 (inv-▸ʰ● ▸H .proj₂) ∙●

opaque

  -- An inversion lemma for usage of states with variables in head position

  ▸var : γ ⨾ δ ⨾ η ▸[ m ] ⟨ H , var x , ρ , S ⟩
       → γ ≤ᶜ (𝟘ᶜ , wkVar ρ x ≔ ∣ S ∣) +ᶜ η
  ▸var {γ} {δ} {η} {m} {x} {ρ} {S} (▸H , ▸x , ▸S , m≤ , γ≤) = begin
    γ                                             ≤⟨ γ≤ ⟩
    ∣ S ∣ ·ᶜ wkᶜ ρ δ +ᶜ η                          ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (inv-usage-var ▸x))) ⟩
    ∣ S ∣ ·ᶜ wkᶜ ρ (𝟘ᶜ , x ≔ ⌜ m ⌝) +ᶜ η           ≡⟨ cong (λ y → ∣ S ∣ ·ᶜ y +ᶜ η) (wk-,≔ ρ) ⟩
    ∣ S ∣ ·ᶜ (wkᶜ ρ 𝟘ᶜ , wkVar ρ x ≔ ⌜ m ⌝) +ᶜ η   ≡⟨ cong (λ y → ∣ S ∣ ·ᶜ (y , wkVar ρ x ≔ ⌜ m ⌝) +ᶜ η) (wk-𝟘ᶜ ρ) ⟩
    ∣ S ∣ ·ᶜ (𝟘ᶜ , wkVar ρ x ≔ ⌜ m ⌝) +ᶜ η         ≡˘⟨ cong (_+ᶜ η) (update-distrib-·ᶜ _ _ _ _) ⟩
    (∣ S ∣ ·ᶜ 𝟘ᶜ , wkVar ρ x ≔ ∣ S ∣ · ⌜ m ⌝) +ᶜ η ≈⟨ +ᶜ-congʳ (update-congˡ (·ᶜ-zeroʳ _)) ⟩
    (𝟘ᶜ , wkVar ρ x ≔ ∣ S ∣ · ⌜ m ⌝) +ᶜ η          ≡⟨ cong (λ y → (𝟘ᶜ , wkVar ρ x ≔ y) +ᶜ η) (≤ᵐ-·⌜⌝ m≤) ⟩
    (𝟘ᶜ , wkVar ρ x ≔ ∣ S ∣) +ᶜ η                  ∎
    where
    open RPo ≤ᶜ-poset

opaque

  -- A consequence of the above lemma

  ▸var′ : γ ⨾ δ ⨾ η ▸[ m ] ⟨ H , var x , ρ , S ⟩
        → γ ⟨ wkVar ρ x ⟩ ≤ ∣ S ∣ + η ⟨ wkVar ρ x ⟩
  ▸var′ {γ} {δ} {η} {x} {ρ} {S} ▸s = begin
    γ ⟨ wkVar ρ x ⟩                                         ≤⟨ lookup-monotone (wkVar ρ x) (▸var ▸s) ⟩
    ((𝟘ᶜ , wkVar ρ x ≔ ∣ S ∣) +ᶜ η) ⟨ wkVar ρ x ⟩           ≡⟨ lookup-distrib-+ᶜ (𝟘ᶜ , wkVar ρ x ≔ ∣ S ∣) η (wkVar ρ x) ⟩
    (𝟘ᶜ , wkVar ρ x ≔ ∣ S ∣) ⟨ wkVar ρ x ⟩ + η ⟨ wkVar ρ x ⟩ ≡⟨ +-congʳ (update-lookup 𝟘ᶜ (wkVar ρ x)) ⟩
    ∣ S ∣ + η ⟨ wkVar ρ x ⟩                                 ∎
    where
    open RPo ≤-poset

opaque

  -- In a well-resorced heap, a pointer lookup yields a well-resourced
  -- term and a well-resourced heap.

  ▸-heapLookup : ⦃ Has-well-behaved-zero M semiring-with-meet ⦄
               → H ⊢ y ↦[ q ] t , ρ ⨾ H′
               → γ ▸ʰ H
               → γ ⟨ y ⟩ - q ≤ r
               → ∃₂ λ m δ → δ ▸[ m ] t × (γ , y ≔ r) +ᶜ q ·ᶜ wkᶜ ρ δ ▸ʰ H′ × m ≤ᵐ q
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
  ▸-heapLookup {H = H ∙ (p′ , u , ρ)} {y +1} {q} {γ = γ ∙ p} {r}
      (there {c = _ , ρ′} d) (_∙_ {δ} ▸H (▸ᶜ ▸u p′≤p)) γ⟨y⟩-q≤r  =
    case p+q-r≤p-r+q γ⟨y⟩-q≤r ((p ·ᶜ wkᶜ ρ δ) ⟨ y ⟩) of λ
      γ⟨y⟩+pδ⟨y⟩-q≤pδ⟨y⟩+r →
    case subst (_- q ≤ ((p ·ᶜ wkᶜ ρ δ) ⟨ y ⟩ + r))
           (sym (lookup-distrib-+ᶜ γ (p ·ᶜ wkᶜ ρ δ) y))
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
      (there● {c = _ , ρ′} d) (▸H ∙●) γ⟨y⟩-q≤r =
    case ▸-heapLookup d ▸H γ⟨y⟩-q≤r of λ
      (_ , δ , ▸t , ▸H′ , m≤ᵐS) →
    _ , δ , ▸t
      , subst (_▸ʰ H′) ((cong ((γ , y ≔ r) +ᶜ q ·ᶜ wkᶜ ρ′ δ ∙_)
          (sym (trans (+-identityˡ _) (·-zeroʳ _))))) (▸H′ ∙●)
      , m≤ᵐS

-- Some properties proven under some assumptions about erased matches

module _ (nem : No-erased-matches′ type-variant UR) where

  opaque

    -- The multiplicity of a well-resourced eliminator is not zero

    ▸∣e∣≢𝟘 : ⦃ Has-well-behaved-zero M semiring-with-meet ⦄
           → γ ▸ᵉ[ 𝟙ᵐ ] e → ∣ e ∣ᵉ ≢ 𝟘 ⊎ ∃₃ λ n (A : Term n) ρ → e ≡ emptyrecₑ 𝟘 A ρ × Emptyrec-allowed 𝟙ᵐ 𝟘
    ▸∣e∣≢𝟘 (∘ₑ x) = inj₁ non-trivial
    ▸∣e∣≢𝟘 (fstₑ x) = inj₁ non-trivial
    ▸∣e∣≢𝟘 sndₑ = inj₁ non-trivial
    ▸∣e∣≢𝟘 (prodrecₑ x ok) = inj₁ (nem non-trivial .proj₁ ok)
    ▸∣e∣≢𝟘 (natrecₑ x x₁ x₂) = inj₁ nr₂≢𝟘
    ▸∣e∣≢𝟘 (unitrecₑ x ok no-η) = inj₁ (no-η ∘→ nem non-trivial .proj₂ .proj₁ ok)
    ▸∣e∣≢𝟘 (emptyrecₑ {p} ok) =
      case is-𝟘? p of λ where
        (yes refl) → inj₂ (_ , _ , _ , refl , ok)
        (no p≢𝟘) → inj₁ p≢𝟘
    ▸∣e∣≢𝟘 (Jₑ x) rewrite nem non-trivial .proj₂ .proj₂ .proj₂ .proj₁ = inj₁ ω≢𝟘
    ▸∣e∣≢𝟘 (Kₑ x) rewrite nem non-trivial .proj₂ .proj₂ .proj₂ .proj₂ = inj₁ ω≢𝟘
    ▸∣e∣≢𝟘 ([]-congₑ ok) = inj₁ λ _ → nem non-trivial .proj₂ .proj₂ .proj₁ ok
    ▸∣e∣≢𝟘 sucₑ = inj₁ non-trivial

  opaque

    -- The multiplicity of a well-resourced stack is either not zero
    -- or contains a non-erased application of emptyrec

    ▸∣S∣≢𝟘 : ⦃ Has-well-behaved-zero M semiring-with-meet ⦄
           → γ ▸ˢ S → ∣ S ∣ ≢ 𝟘 ⊎ (emptyrec₀∈ S × Emptyrec-allowed 𝟙ᵐ 𝟘)
    ▸∣S∣≢𝟘 ε = inj₁ non-trivial
    ▸∣S∣≢𝟘 (_∙_ {m} (▸e , m≤) ▸S) =
      case ▸∣S∣≢𝟘 ▸S of λ where
        (inj₂ (x , ok)) → inj₂ (there x , ok)
        (inj₁ ∣S∣≢𝟘) →
          case singleton m of λ where
            (𝟘ᵐ , refl) → ⊥-elim (∣S∣≢𝟘 (𝟘ᵐ≤ᵐp→p≡𝟘 m≤))
            (𝟙ᵐ , refl) →
              case ▸∣e∣≢𝟘 ▸e of λ where
                (inj₂ (_ , _ , _ , refl , ok)) → inj₂ (here , ok)
                (inj₁ ∣e∣≢𝟘) → inj₁ (λ ∣eS∣≡𝟘 →
                  case zero-product ∣eS∣≡𝟘 of λ where
                    (inj₁ ∣S∣≡𝟘) → ∣S∣≢𝟘 ∣S∣≡𝟘
                    (inj₂ ∣e∣≡𝟘) → ∣e∣≢𝟘 ∣e∣≡𝟘)


-- Some properties proven under the assumption that the modality
-- supports subtraction.

module _ ⦃ _ : Has-well-behaved-zero M semiring-with-meet ⦄
         (subtraction-ok : Supports-subtraction) where

  -- Under some assumptions, lookup always succeeds for welll-resourced heaps

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
      lemma : (γ +ᶜ r ·ᶜ wkᶜ ρ δ) ⟨ y ⟩ ≤ (p + (r ·ᶜ wkᶜ ρ δ) ⟨ y ⟩) + q
      lemma = begin
        (γ +ᶜ r ·ᶜ wkᶜ ρ δ) ⟨ y ⟩      ≡⟨ lookup-distrib-+ᶜ γ _ y ⟩
        γ ⟨ y ⟩ + (r ·ᶜ wkᶜ ρ δ) ⟨ y ⟩  ≤⟨ +-monotoneˡ γ⟨y⟩≤p+q ⟩
        (p + q) + (r ·ᶜ wkᶜ ρ δ) ⟨ y ⟩ ≈⟨ +-assoc p q _ ⟩
        p + q + (r ·ᶜ wkᶜ ρ δ) ⟨ y ⟩   ≈⟨ +-congˡ (+-comm q _) ⟩
        p + (r ·ᶜ wkᶜ ρ δ) ⟨ y ⟩ + q   ≈˘⟨ +-assoc p _ q ⟩
        (p + (r ·ᶜ wkᶜ ρ δ) ⟨ y ⟩) + q ∎
    ↦→↦[] (there● d) (▸H ∙●) γ⟨y⟩≤p+q =
      case ↦→↦[] d ▸H γ⟨y⟩≤p+q of λ
        (_ , d′) →
      _ , there● d′

  opaque

    -- A variant of the above property with usage of states

    ▸↦→↦[] : {H : Heap k _}
          → H ⊢ wkVar ρ x ↦ c′
          → γ ⨾ δ ⨾ η ▸[ m ] ⟨ H , var x , ρ , S ⟩
          → ∃ λ H′ → H ⊢ wkVar ρ x ↦[ ∣ S ∣ ] c′ ⨾ H′
    ▸↦→↦[] {ρ} {x} {γ} {η} {S} d ▸s@(▸H , _) =
      ↦→↦[] d ▸H (begin
      -- (begin
        γ ⟨ wkVar ρ x ⟩         ≤⟨ ▸var′ ▸s ⟩
        ∣ S ∣ + η ⟨ wkVar ρ x ⟩ ≡⟨ +-comm _ _ ⟩
        η ⟨ wkVar ρ x ⟩ + ∣ S ∣ ∎)
      where
      open RPo ≤-poset

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

    ▸s● : H ⊢ wkVar ρ x ↦● → γ ⨾ δ ⨾ η ▸[ m ] ⟨ H , var x , ρ , S ⟩
        → ∣ S ∣ ≡ 𝟘 × η ⟨ wkVar ρ x ⟩ ≡ 𝟘
    ▸s● d ▸s@(▸H , ▸t , ▸S , m≤ , γ≤) =
      +-positive (𝟘≮ (≤-trans (≤-reflexive (sym (▸H● d ▸H))) (▸var′ ▸s)))
