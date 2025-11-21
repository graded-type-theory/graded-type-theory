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
open import Graded.Heap.Untyped.Properties type-variant UR factoring-nr
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
  c : Cont _
  e : Entryₘ _ _
  e′ : Entry _ _

opaque

  -- Usage for erased heaps

  ▸erasedHeap : 𝟘ᶜ ▸ʰ erasedHeap n
  ▸erasedHeap {(0)} = ε
  ▸erasedHeap {(1+ n)} = ▸erasedHeap ∙●

opaque

  -- Well-usage for the initial state

  ▸initial : 𝟘ᶜ {n} ▸ t → ▸ initial t
  ▸initial ▸t =
    ▸ₛ ε ▸erasedHeap (▸-cong (sym ⌞𝟙⌟) ▸t) ε
      (≤ᶜ-reflexive (≈ᶜ-sym (≈ᶜ-trans (+ᶜ-identityʳ _) (·ᶜ-zeroʳ _))))

opaque

  -- A well-resourced heap under the zero-context has all grades bounded by 𝟘.

  𝟘▸H→H≤𝟘 : 𝟘ᶜ ▸ʰ H → H ≤ʰ 𝟘
  𝟘▸H→H≤𝟘 {H = ε} ▸H = ε
  𝟘▸H→H≤𝟘 {H = H ∙ (p , t , ρ)} ▸H =
    let open ≤ᶜ-reasoning
        δ , η , ▸t , ▸H′ , p≤𝟘 , η≤ = ▸ʰ∙-inv ▸H
        H′≤ = 𝟘▸H→H≤𝟘 $ sub ▸H′ $ begin
          η                     ≤⟨ η≤ ⟩
          𝟘ᶜ +ᶜ p ·ᶜ wkConₘ ρ δ ≈⟨ +ᶜ-identityˡ _ ⟩
          p ·ᶜ wkConₘ ρ δ       ≤⟨ ·ᶜ-monotoneˡ p≤𝟘 ⟩
          𝟘 ·ᶜ wkConₘ ρ δ       ≈⟨ ·ᶜ-zeroˡ _ ⟩
          𝟘ᶜ ∎
    in  H′≤ ∙ p≤𝟘
  𝟘▸H→H≤𝟘 {H = H ∙●} ▸H =
    let δ , _ , ▸H′ , δ≤𝟘 = ▸ʰ●-inv ▸H
    in  𝟘▸H→H≤𝟘 (sub ▸H′ δ≤𝟘) ∙●

opaque

  -- In a well-resorced heap, a pointer lookup yields a well-resourced
  -- term and a well-resourced heap.

  ▸-heapLookup : H ⊢ y ↦[ q ] t , ρ ⨾ H′
               → γ ▸ʰ H
               → γ ⟨ y ⟩ - q ≤ r
               → ∃ λ δ → δ ▸[ ⌞ q ⌟ ] t × (γ , y ≔ r) +ᶜ q ·ᶜ wkConₘ ρ δ ▸ʰ H′
  ▸-heapLookup {γ = ε} ()
  ▸-heapLookup
    {q} {γ = γ ∙ p} {r}
    (here {p = p′} {r = r′} {e = t , ρ} p′-q≡r′) ▸H p-q≤r =
    let _ , _ , ▸t , ▸H′ , p′≤p , η≤ = ▸ʰ∙-inv ▸H
    in  lemma ▸t ▸H′ p′≤p η≤
    where
    lemma :
      δ ▸[ ⌞ p′ ⌟ ] t → η ▸ʰ H → p′ ≤ p → η ≤ᶜ γ +ᶜ p′ ·ᶜ wkConₘ ρ δ →
      ∃ λ δ′ → δ′ ▸[ ⌞ q ⌟ ] t × ((γ ∙ r) +ᶜ q ·ᶜ wkConₘ (step ρ) δ′) ▸ʰ H ∙ (r′ , t , ρ)
    lemma {δ} {η} ▸t ▸H p′≤p η≤ =
      case is-𝟘? p′ of λ where
        (yes refl) →
          _ , ▸-cong (mode-eq refl .proj₁) ▸t
            , sub (sub ▸H η≤′ ∙ ▸-cong (mode-eq refl .proj₂) ▸t) (≤ᶜ-refl ∙ r′≤r+q·𝟘)
        (no p′≢𝟘) →
          case ▸-𝟘ᵐ? ▸t of λ
            (δ′ , ▸⁰t) →
          case ▸-cong (sym ⌞𝟘⌟≡𝟘ᵐ?) ▸⁰t of λ
            ▸⁰t′ →
          case is-𝟘? q of λ where
            (yes refl) →
              case is-𝟘? r′ of λ where
                (yes refl) →
                  _ , ▸⁰t′
                    , sub (sub ▸H (η≤″ refl) ∙ ▸⁰t′)
                       (lemma′ ∙ r′≤r+q·𝟘)
                (no r′≢𝟘) →
                  _ , ▸⁰t′
                    , sub (sub ▸H η≤′ ∙ ▸-cong (trans (≢𝟘→⌞⌟≡𝟙ᵐ p′≢𝟘) (sym (≢𝟘→⌞⌟≡𝟙ᵐ r′≢𝟘))) ▸t)
                       (lemma′ ∙ r′≤r+q·𝟘)
            (no q≢𝟘) →
              case ▸-cong (trans (≢𝟘→⌞⌟≡𝟙ᵐ p′≢𝟘) (sym (≢𝟘→⌞⌟≡𝟙ᵐ q≢𝟘))) ▸t of λ
                ▸t′ →
              case is-𝟘? r′ of λ where
                (yes refl) →
                  _ , ▸t′ , sub (sub ▸H (η≤″ refl) ∙ ▸⁰t′) (≤ᶜ-refl ∙ r′≤r+q·𝟘)
                (no r′≢𝟘) →
                  _ , ▸t′
                    , sub (sub ▸H η≤′
                          ∙ ▸-cong (trans (≢𝟘→⌞⌟≡𝟙ᵐ q≢𝟘) (sym (≢𝟘→⌞⌟≡𝟙ᵐ r′≢𝟘))) ▸t′)
                        (≤ᶜ-refl ∙ r′≤r+q·𝟘)
      where
      r′≤r : r′ ≤ r
      r′≤r = p′-q≡r′ .proj₂ r (≤-trans p′≤p p-q≤r)
      mode-eq′ : ⦃ Has-well-behaved-zero M semiring-with-meet ⦄ → p′ ≡ 𝟘 → ⌞ p′ ⌟ ≡ ⌞ q ⌟ × ⌞ p′ ⌟ ≡ ⌞ r′ ⌟
      mode-eq′ refl =
        case 𝟘≮ p′≤p of λ {
          refl →
        case 𝟘-p≤q p-q≤r of λ {
          (refl , refl) →
        case 𝟘-p≡q p′-q≡r′ .proj₁ of λ {
          refl →
        refl , refl }}}
      mode-eq : p′ ≡ 𝟘 → ⌞ p′ ⌟ ≡ ⌞ q ⌟ × ⌞ p′ ⌟ ≡ ⌞ r′ ⌟
      mode-eq p′≡𝟘 = 𝟘ᵐ-allowed-elim
        (λ x → mode-eq′ ⦃ 𝟘-well-behaved x ⦄ p′≡𝟘)
        (λ x → Mode-propositional-without-𝟘ᵐ x , Mode-propositional-without-𝟘ᵐ x)
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
      η≤′ : η ≤ᶜ (γ +ᶜ q ·ᶜ wkConₘ ρ δ) +ᶜ r′ ·ᶜ wkConₘ ρ δ
      η≤′ = begin
        η                                          ≤⟨ η≤ ⟩
        γ +ᶜ p′ ·ᶜ wkConₘ ρ δ                      ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneˡ (p′-q≡r′ .proj₁)) ⟩
        γ +ᶜ (r′ + q) ·ᶜ wkConₘ ρ δ                ≈⟨ +ᶜ-congˡ (·ᶜ-congʳ (+-comm _ _)) ⟩
        γ +ᶜ (q + r′) ·ᶜ wkConₘ ρ δ                ≈⟨ +ᶜ-congˡ (·ᶜ-distribʳ-+ᶜ _ _ _) ⟩
        γ +ᶜ q ·ᶜ wkConₘ ρ δ +ᶜ r′ ·ᶜ wkConₘ ρ δ   ≈˘⟨ +ᶜ-assoc _ _ _ ⟩
        (γ +ᶜ q ·ᶜ wkConₘ ρ δ) +ᶜ r′ ·ᶜ wkConₘ ρ δ ∎
        where
        open ≤ᶜ-reasoning
      η≤″ : ∀ {δ′} → r′ ≡ 𝟘 → η ≤ᶜ (γ +ᶜ q ·ᶜ wkConₘ ρ δ) +ᶜ r′ ·ᶜ δ′
      η≤″ {δ′} refl = begin
        η                                         ≤⟨ η≤′ ⟩
        (γ +ᶜ q ·ᶜ wkConₘ ρ δ) +ᶜ 𝟘 ·ᶜ wkConₘ ρ δ ≈⟨ +ᶜ-congˡ (·ᶜ-zeroˡ _) ⟩
        (γ +ᶜ q ·ᶜ wkConₘ ρ δ) +ᶜ 𝟘ᶜ              ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroˡ _) ⟩
        (γ +ᶜ q ·ᶜ wkConₘ ρ δ) +ᶜ 𝟘 ·ᶜ δ′         ∎
        where
        open ≤ᶜ-reasoning
      lemma′ : ∀ {δ′} → γ +ᶜ 𝟘 ·ᶜ wkConₘ ρ δ ≤ᶜ γ +ᶜ 𝟘 ·ᶜ δ′
      lemma′ {δ′} = begin
        γ +ᶜ 𝟘 ·ᶜ wkConₘ ρ δ ≈⟨ +ᶜ-congˡ (·ᶜ-zeroˡ _) ⟩
        γ +ᶜ 𝟘ᶜ              ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroˡ _) ⟩
        γ +ᶜ 𝟘 ·ᶜ δ′         ∎
        where
        open ≤ᶜ-reasoning
  ▸-heapLookup
    {q} {γ = γ ∙ p} {r}
    (there {y} {e = (t , ρ′)} {e′ = (p′ , u , ρ)} d) ▸H γ⟨y⟩-q≤r =
    let δ , η , ▸u , ▸H′ , p′≤p , η≤ = ▸ʰ∙-inv ▸H
        γ⟨y⟩+pδ⟨y⟩-q≤pδ⟨y⟩+r = p+q-r≤p-r+q γ⟨y⟩-q≤r ((p′ ·ᶜ wkConₘ ρ δ) ⟨ y ⟩)
        η⟨y⟩-q≤ = let open RPo ≤-poset in begin
          η ⟨ y ⟩                              ≤⟨ lookup-monotone y η≤ ⟩
          (γ +ᶜ p′ ·ᶜ wkConₘ ρ δ) ⟨ y ⟩        ≈⟨ lookup-distrib-+ᶜ γ _ y ⟩
          γ ⟨ y ⟩ + (p′ ·ᶜ wkConₘ ρ δ) ⟨ y ⟩    ≤⟨ γ⟨y⟩+pδ⟨y⟩-q≤pδ⟨y⟩+r ⟩
          ((p′ ·ᶜ wkConₘ ρ δ) ⟨ y ⟩ + r) + q   ∎
        δ′ , ▸t , ▸H″ = ▸-heapLookup d ▸H′ η⟨y⟩-q≤
        η,y≔≤ = let open ≤ᶜ-reasoning in begin
          (η , y ≔ (p′ ·ᶜ wkConₘ ρ δ) ⟨ y ⟩ + r) +ᶜ q ·ᶜ wkConₘ ρ′ δ′
            ≤⟨ +ᶜ-monotoneˡ (update-monotoneˡ y η≤) ⟩
          (γ +ᶜ p′ ·ᶜ wkConₘ ρ δ , y ≔ (p′ ·ᶜ wkConₘ ρ δ) ⟨ y ⟩ + r) +ᶜ q ·ᶜ wkConₘ ρ′ δ′
            ≈⟨ +ᶜ-congʳ (update-congʳ (+-comm _ r)) ⟩
          (γ +ᶜ p′ ·ᶜ wkConₘ ρ δ , y ≔ r + (p′ ·ᶜ wkConₘ ρ δ) ⟨ y ⟩) +ᶜ q ·ᶜ wkConₘ ρ′ δ′
            ≡⟨ cong (_+ᶜ q ·ᶜ wkConₘ ρ′ δ′) (update-distrib-+ᶜ γ (p′ ·ᶜ wkConₘ ρ δ) r _ y) ⟩
          ((γ , y ≔ r) +ᶜ (p′ ·ᶜ wkConₘ ρ δ , y ≔ (p′ ·ᶜ wkConₘ ρ δ) ⟨ y ⟩)) +ᶜ q ·ᶜ wkConₘ ρ′ δ′
            ≡⟨ cong (λ x → (_ +ᶜ x) +ᶜ q ·ᶜ wkConₘ ρ′ δ′) (update-self (p′ ·ᶜ wkConₘ ρ δ) y) ⟩
          ((γ , y ≔ r) +ᶜ p′ ·ᶜ wkConₘ ρ δ) +ᶜ q ·ᶜ wkConₘ ρ′ δ′
            ≈⟨ +ᶜ-assoc (γ , y ≔ r) (p′ ·ᶜ wkConₘ ρ δ) (q ·ᶜ wkConₘ ρ′ δ′) ⟩
          (γ , y ≔ r) +ᶜ p′ ·ᶜ wkConₘ ρ δ +ᶜ q ·ᶜ wkConₘ ρ′ δ′
            ≈⟨ +ᶜ-congˡ (+ᶜ-comm (p′ ·ᶜ wkConₘ ρ δ) (q ·ᶜ wkConₘ ρ′ δ′)) ⟩
          (γ , y ≔ r) +ᶜ q ·ᶜ wkConₘ ρ′ δ′ +ᶜ p′ ·ᶜ wkConₘ ρ δ
            ≈˘⟨ +ᶜ-assoc (γ , y ≔ r) (q ·ᶜ wkConₘ ρ′ δ′) (p′ ·ᶜ wkConₘ ρ δ) ⟩
          ((γ , y ≔ r) +ᶜ q ·ᶜ wkConₘ ρ′ δ′) +ᶜ p′ ·ᶜ wkConₘ ρ δ ∎
    in  _ , ▸t
          , sub (sub ▸H″ η,y≔≤ ∙ ▸u)
              (≤ᶜ-refl ∙ ≤-trans p′≤p (≤-reflexive
                (sym (trans (+-congˡ (·-zeroʳ _)) (+-identityʳ _)))))
  ▸-heapLookup {q} {γ = γ ∙ p} {r} (there● {y} {e = _ , ρ} d) ▸H γ⟨y⟩-q≤r =
    let δ , 𝟘≤p , ▸H′ , δ≤γ = ▸ʰ●-inv ▸H
        η , ▸t , ▸H″ = ▸-heapLookup d ▸H′
          (≤-trans (lookup-monotone y δ≤γ) γ⟨y⟩-q≤r)
        open ≤ᶜ-reasoning
    in  _ , ▸t , sub (▸H″ ∙●) (begin
        (δ , y ≔ r) +ᶜ q ·ᶜ wkConₘ ρ η ∙ 𝟘         ≤⟨ +ᶜ-monotoneˡ (update-monotoneˡ y δ≤γ) ∙ 𝟘≤p ⟩
        (γ , y ≔ r) +ᶜ q ·ᶜ wkConₘ ρ η ∙ p         ≈˘⟨ ≈ᶜ-refl ∙ +-identityʳ _ ⟩
        (γ , y ≔ r) +ᶜ q ·ᶜ wkConₘ ρ η ∙ p + 𝟘     ≈˘⟨ ≈ᶜ-refl ∙ +-congˡ (·-zeroʳ _) ⟩
        (γ , y ≔ r) +ᶜ q ·ᶜ wkConₘ ρ η ∙ p + q · 𝟘 ∎)

opaque

  -- An invariant of InvUsageNatrecₑ

  InvUsageNatrecₑ-≤ : InvUsageNatrecₑ p r γ δ ρ η → η ≤ᶜ wkConₘ ρ δ +ᶜ r ·ᶜ η
  InvUsageNatrecₑ-≤ {p} {r} {γ} {δ} {ρ} = λ where
    invUsageNatrecNr → begin
      wkConₘ ρ (nrᶜ p r γ δ 𝟘ᶜ)                      ≤⟨ wk-≤ᶜ ρ nrᶜ-suc ⟩
      wkConₘ ρ (δ +ᶜ p ·ᶜ 𝟘ᶜ +ᶜ r ·ᶜ nrᶜ p r γ δ 𝟘ᶜ) ≈⟨ wk-≈ᶜ ρ (+ᶜ-congˡ (+ᶜ-congʳ (·ᶜ-zeroʳ _))) ⟩
      wkConₘ ρ (δ +ᶜ 𝟘ᶜ +ᶜ r ·ᶜ nrᶜ p r γ δ 𝟘ᶜ)      ≈⟨ wk-≈ᶜ ρ (+ᶜ-congˡ (+ᶜ-identityˡ _)) ⟩
      wkConₘ ρ (δ +ᶜ r ·ᶜ nrᶜ p r γ δ 𝟘ᶜ)            ≈⟨ wk-+ᶜ ρ ⟩
      wkConₘ ρ δ +ᶜ wkConₘ ρ (r ·ᶜ nrᶜ p r γ δ 𝟘ᶜ)   ≈⟨ +ᶜ-congˡ (wk-·ᶜ ρ) ⟩
      wkConₘ ρ δ +ᶜ r ·ᶜ wkConₘ ρ (nrᶜ p r γ δ 𝟘ᶜ)   ∎
    (invUsageNatrecNoNr {χ} χ-glb) → begin
      wkConₘ ρ χ                      ≤⟨ wk-≤ᶜ ρ (nrᵢᶜ-GLBᶜ-≤ᶜ χ-glb) ⟩
      wkConₘ ρ (δ +ᶜ r ·ᶜ χ)          ≈⟨ wk-+ᶜ ρ ⟩
      wkConₘ ρ δ +ᶜ wkConₘ ρ (r ·ᶜ χ) ≈⟨ +ᶜ-congˡ (wk-·ᶜ ρ) ⟩
      wkConₘ ρ δ +ᶜ r ·ᶜ wkConₘ ρ χ   ∎
      where
      open ≤ᶜ-reasoning

-- Some properties proven under some assumptions about erased matches

module _ (nem : No-erased-matches′ type-variant UR) where

  opaque

    -- The multiplicity of a well-resourced continuation is not zero
    -- unless it is an erased emptyrec

    ▸∣∣ᶜ≢𝟘 :
      ⦃ Has-well-behaved-zero M semiring-with-meet ⦄ →
      γ ▸ᶜ[ 𝟙ᵐ ] c →
      ¬ ∣ c ∣ᶜ≡ 𝟘 ⊎
      ∃₃ λ n (A : Term n) ρ → c ≡ emptyrecₑ 𝟘 A ρ × Emptyrec-allowed 𝟙ᵐ 𝟘
    ▸∣∣ᶜ≢𝟘 (∘ₑ _) = inj₁ λ ∣e∣≡𝟘 → non-trivial (∣∣ᶜ-functional ∘ₑ ∣e∣≡𝟘)
    ▸∣∣ᶜ≢𝟘 = λ where
        lowerₑ → inj₁ (lemma non-trivial lowerₑ)
        (∘ₑ _) → inj₁ (lemma non-trivial ∘ₑ)
        (fstₑ _) → inj₁ (lemma non-trivial fstₑ)
        sndₑ → inj₁ (lemma non-trivial sndₑ)
        (prodrecₑ _ ok) →
          inj₁ (lemma (nem non-trivial .proj₁ ok) prodrecₑ)
        (natrecₑ _ _ _) →
          inj₁ (lemma nr₂≢𝟘 (natrecₑ has-nrₑ))
        (natrec-no-nrₑ _ _ _ _) →
          inj₁ λ { (natrecₑ x) → lemma-nr x refl}
        (unitrecₑ _ ok no-η) →
          inj₁ (lemma (no-η ∘→ nem non-trivial .proj₂ .proj₁ ok) unitrecₑ)
        (emptyrecₑ {p} ok) →
          case is-𝟘? p of λ where
            (yes refl) → inj₂ (_ , _ , _ , refl , ok)
            (no p≢𝟘) → inj₁ (lemma p≢𝟘 emptyrecₑ)
        (Jₑ _) →
          inj₁ (lemma ω≢𝟘
            (Jₑ (subst (∣J_, _ , _ ∣≡ _)
                  (sym (nem non-trivial .proj₂ .proj₂ .proj₂ .proj₁))
                  J-none)))
        (Kₑ _) →
          inj₁ (lemma ω≢𝟘
            (Kₑ (subst (∣K_, _ ∣≡ _)
                  (sym (nem non-trivial .proj₂ .proj₂ .proj₂ .proj₂))
                  K-none)))
        ([]-congₑ ok) →
          inj₁ λ _ → nem non-trivial .proj₂ .proj₂ .proj₁ ok
      where
      lemma :  p ≢ r → ∣ c ∣ᶜ≡ p → ∣ c ∣ᶜ≡ r → ⊥
      lemma p≢r ≡p ≡r = p≢r (∣∣ᶜ-functional ≡p ≡r)
      lemma-nr : ∣natrec p , r ∣≡ q → q ≢ 𝟘
      lemma-nr has-nrₑ nr₂≡𝟘 = nr₂≢𝟘 nr₂≡𝟘
      lemma-nr (no-nrₑ x) refl = 𝟘≰𝟙 (x .proj₁ 0)

  opaque

    -- The multiplicity of a well-resourced stack is either not zero
    -- or contains an erased application of emptyrec

    ▸∣∣≢𝟘 : ⦃ Has-well-behaved-zero M semiring-with-meet ⦄
           → γ ▸ˢ S → ¬ ∣ S ∣≡ 𝟘 ⊎ (emptyrec 𝟘 ∈ S × Emptyrec-allowed 𝟙ᵐ 𝟘)
    ▸∣∣≢𝟘 ε = inj₁ λ ≡𝟘 → non-trivial (∣∣-functional ε ≡𝟘)
    ▸∣∣≢𝟘 (▸ˢ∙ ∣S∣≡ ▸c ▸S) =
      case ▸∣∣≢𝟘 ▸S of λ where
        (inj₂ (x , ok)) → inj₂ (there x , ok)
        (inj₁ ∣S∣≢𝟘) →
          case ▸∣∣ᶜ≢𝟘 (subst (_ ▸ᶜ[_] _)
                        (≢𝟘→⌞⌟≡𝟙ᵐ (λ {refl → ∣S∣≢𝟘 ∣S∣≡})) ▸c) of λ where
            (inj₂ (_ , _ , _ , refl , ok)) → inj₂ (here , ok)
            (inj₁ ∣c∣≢𝟘) → inj₁ λ ∣cS∣≡ →
              let q , r , ∣c∣≡q , ∣S∣≡r , 𝟘≡rq = ∣∣∙-inv ∣cS∣≡
              in  case zero-product (sym 𝟘≡rq) of λ where
                    (inj₁ r≡𝟘) → ∣S∣≢𝟘 (subst (∣ _ ∣≡_) r≡𝟘 ∣S∣≡r)
                    (inj₂ q≡𝟘) → ∣c∣≢𝟘 (subst (∣ _ ∣ᶜ≡_) q≡𝟘 ∣c∣≡q)

-- Some properties proven under the assumption that the modality
-- supports subtraction.

module _ (subtraction-ok : Supports-subtraction) where

  -- Under some assumptions, lookup always succeeds for well-resourced heaps

  opaque

    ↦→↦[] : {H : Heap k _}
        → H ⊢ y ↦ e′ → γ ▸ʰ H → γ ⟨ y ⟩ ≤ p + q
        → ∃ λ H′ → H ⊢ y ↦[ q ] e′ ⨾ H′
    ↦→↦[] {γ = ε} ()
    ↦→↦[] {γ = _ ∙ _} here ▸H p′≤p+q =
      let _ , _ , _ , _ , p≤ , _ = ▸ʰ∙-inv ▸H
      in  _ , here (subtraction-ok (≤-trans p≤ p′≤p+q) .proj₂)
    ↦→↦[] {γ = γ ∙ r} {p} {q} (there {y} {e′ = r′ , _ , ρ} d) ▸H γ⟨y⟩≤p+q =
      let δ , η , _ , ▸H′ , r′≤r , η≤ = ▸ʰ∙-inv ▸H
          open RPo ≤-poset
          _ , d′ = ↦→↦[] d ▸H′ (begin
           η ⟨ y ⟩                           ≤⟨ lookup-monotone y η≤ ⟩
           (γ +ᶜ r′ ·ᶜ wkConₘ ρ δ) ⟨ y ⟩     ≤⟨ lookup-monotone y (+ᶜ-monotoneʳ {η = γ}
                                                (·ᶜ-monotoneˡ r′≤r)) ⟩
           (γ +ᶜ r ·ᶜ wkConₘ ρ δ) ⟨ y ⟩      ≡⟨ lookup-distrib-+ᶜ γ _ y ⟩
           γ ⟨ y ⟩ + (r ·ᶜ wkConₘ ρ δ) ⟨ y ⟩  ≤⟨ +-monotoneˡ γ⟨y⟩≤p+q ⟩
           (p + q) + (r ·ᶜ wkConₘ ρ δ) ⟨ y ⟩ ≈⟨ +-assoc p q _ ⟩
           p + q + (r ·ᶜ wkConₘ ρ δ) ⟨ y ⟩   ≈⟨ +-congˡ (+-comm q _) ⟩
           p + (r ·ᶜ wkConₘ ρ δ) ⟨ y ⟩ + q   ≈˘⟨ +-assoc p _ q ⟩
           (p + (r ·ᶜ wkConₘ ρ δ) ⟨ y ⟩) + q ∎)
      in  _ , there d′
    ↦→↦[] {γ = _ ∙ _} (there● d) ▸H γ⟨y⟩≤p+q =
      let _ , _ , ▸H′ , δ≤γ = ▸ʰ●-inv ▸H
          _ , d′ = ↦→↦[] d ▸H′ (≤-trans (lookup-monotone _ δ≤γ) γ⟨y⟩≤p+q)
      in  _ , there● d′

  opaque

    -- A variant of the above property with usage of states

    ▸↦→↦[] : {H : Heap k _}
          → ∣ S ∣≡ p
          → H ⊢ wkVar ρ x ↦ e′
          → ▸ ⟨ H , var x , ρ , S ⟩
          → ∃ λ H′ → H ⊢ wkVar ρ x ↦[ p ] e′ ⨾ H′
    ▸↦→↦[] {p} {ρ} {x} ∣S∣≡p d ▸s =
      let q , γ , δ , ∣S∣≡q , ▸H , _ , γ⟨x⟩≤ = ▸ₛ-var-inv′ ▸s
          open RPo ≤-poset
      in  ↦→↦[] d ▸H $ begin
        γ ⟨ wkVar ρ x ⟩     ≤⟨ γ⟨x⟩≤ ⟩
        q + δ ⟨ wkVar ρ x ⟩ ≈⟨ +-comm _ _ ⟩
        δ ⟨ wkVar ρ x ⟩ + q ≈⟨ +-congˡ (∣∣-functional ∣S∣≡q ∣S∣≡p) ⟩
        δ ⟨ wkVar ρ x ⟩ + p ∎

  opaque

    -- A variant of the above property for closed states

    ▸↦[]-closed :
      {H : Heap 0 _} →
      ∣ S ∣≡ p → ▸ ⟨ H , var x , ρ , S ⟩ →
      ∃₃ λ n H′ (c′ : Entry _ n) → H ⊢ wkVar ρ x ↦[ p ] c′ ⨾ H′
    ▸↦[]-closed {x} {ρ} ∣S∣≡ ▸s =
      let _ , _ , d′ = ¬erased-heap→↦ refl (wkVar ρ x)
          _ , d = ▸↦→↦[] ∣S∣≡ d′ ▸s
      in  _ , _ , _ , d

  opaque

    -- If a pointer points to a dummy entry in a well-resource heap then
    -- the corresponding entry in the usage context is 𝟘.

    ▸H● : ⦃ _ : Has-well-behaved-zero M semiring-with-meet ⦄ →
          H ⊢ y ↦● → γ ▸ʰ H → γ ⟨ y ⟩ ≡ 𝟘
    ▸H● {γ = ε} ()
    ▸H● {γ = _ ∙ _} here ▸H =
      let _ , 𝟘≤p , _ , _ = ▸ʰ●-inv ▸H
      in  𝟘≮ 𝟘≤p
    ▸H● {γ = γ ∙ _} (there d) ▸H =
      let _ , _ , _ , ▸H′ , _ , η≤ = ▸ʰ∙-inv ▸H
      in  +-positiveˡ
            (𝟘≮ (≤-trans (≤-reflexive (sym (▸H● d ▸H′)))
                   (≤-trans (lookup-monotone _ η≤)
                     (≤-reflexive (lookup-distrib-+ᶜ γ _ _)))))
    ▸H● {γ = _ ∙ _} (there● d) ▸H =
      let _ , _ , ▸H′ , δ≤γ = ▸ʰ●-inv ▸H
      in  𝟘≮ (≤-trans (≤-reflexive (sym (▸H● d ▸H′)))
                (lookup-monotone _ δ≤γ))

  opaque

    -- In a well-resourced state with a variable in head position with a
    -- corresponding dummy entry in the heap, the stack multiplicity and usage
    -- context of the stack are both 𝟘.

    ▸s● : ⦃ _ : Has-well-behaved-zero M semiring-with-meet ⦄ →
          H ⊢ wkVar ρ x ↦● → ▸ ⟨ H , var x , ρ , S ⟩ → ∣ S ∣≡ 𝟘
    ▸s● d ▸s =
      let _ , _ , _ , ∣S∣≡ , ▸H , ▸S , γ⟨x⟩≤ = ▸ₛ-var-inv′ ▸s
      in  subst (∣ _ ∣≡_)
            (+-positiveˡ (𝟘≮ (≤-trans (≤-reflexive (sym (▸H● d ▸H))) γ⟨x⟩≤)))
            ∣S∣≡
