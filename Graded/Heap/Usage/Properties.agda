------------------------------------------------------------------------
-- Properties of the usage relation for Heaps, Stacks and States.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions
open import Definition.Typed.Variant
open import Graded.Usage.Restrictions.Natrec

module Graded.Heap.Usage.Properties
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (type-variant : Type-variant)
  (UR : Usage-restrictions 𝕄 𝐌)
  (open Usage-restrictions UR)
  (factoring-nr :
    ⦃ has-nr : Nr-available ⦄ →
    Is-factoring-nr M (Natrec-mode-Has-nr 𝕄 has-nr))
  (∣ε∣ : M)
  where

open Modality 𝕄
open IsMode 𝐌

open import Definition.Untyped M
open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄
open import Graded.Restrictions 𝕄 𝐌
open import Graded.Usage UR
open import Graded.Usage.Restrictions.Instance UR
open import Graded.Usage.Inversion UR
open import Graded.Usage.Properties UR

open import Graded.Heap.Untyped type-variant UR factoring-nr ∣ε∣
open import Graded.Heap.Untyped.Properties type-variant UR factoring-nr ∣ε∣
open import Graded.Heap.Usage type-variant UR factoring-nr ∣ε∣
open import Graded.Heap.Usage.Inversion type-variant UR factoring-nr ∣ε∣

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

  ▸initial : 𝟘ᶜ {n} ▸[ ⌞ ∣ε∣ ⌟ ] t → ▸ initial t
  ▸initial ▸t =
    ▸ₛ ε ▸erasedHeap ▸t ε
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
      let ▸t′ = let open ≤ᵐ-reasoning in ▸-≤ᵐ ▸t $ begin
            ⌞ p′ ⌟    ≤⟨ ⌞⌟-monotone p′≤p ⟩
            ⌞ p ⌟     ≤⟨ ⌞⌟-monotone p-q≤r ⟩
            ⌞ r + q ⌟ ≤⟨ ⌞+⌟-decreasingʳ ⟩
            ⌞ q ⌟     ∎
          ▸t″ = let open ≤ᵐ-reasoning in ▸-≤ᵐ ▸t $ begin
            ⌞ p′ ⌟     ≤⟨ ⌞⌟-monotone (p′-q≡r′ .proj₁) ⟩
            ⌞ r′ + q ⌟ ≤⟨ ⌞+⌟-decreasingˡ ⟩
            ⌞ r′ ⌟     ∎
          open ≤ᶜ-reasoning
          ▸H′ = sub ▸H $ begin
            η                                                         ≤⟨ η≤ ⟩
            γ +ᶜ p′ ·ᶜ wkConₘ ρ δ                                      ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneˡ (p′-q≡r′ .proj₁)) ⟩
            γ +ᶜ (r′ + q) ·ᶜ wkConₘ ρ δ                                ≈⟨ +ᶜ-congˡ (·ᶜ-congʳ (+-comm _ _)) ⟩
            γ +ᶜ (q + r′) ·ᶜ wkConₘ ρ δ                                ≈⟨ +ᶜ-congˡ (·ᶜ-distribʳ-+ᶜ _ _ _) ⟩
            γ +ᶜ q ·ᶜ wkConₘ ρ δ +ᶜ r′ ·ᶜ wkConₘ ρ δ                   ≈˘⟨ +ᶜ-assoc _ _ _ ⟩
            (γ +ᶜ q ·ᶜ wkConₘ ρ δ) +ᶜ r′ ·ᶜ wkConₘ ρ δ                 ≈˘⟨ +ᶜ-congˡ (·ᶜ-congʳ ·⌜⌞⌟⌝) ⟩
            (γ +ᶜ q ·ᶜ wkConₘ ρ δ) +ᶜ (r′ · ⌜ ⌞ r′ ⌟ ⌝) ·ᶜ wkConₘ ρ δ  ≈⟨ +ᶜ-congˡ (·ᶜ-assoc _ _ _) ⟩
            (γ +ᶜ q ·ᶜ wkConₘ ρ δ) +ᶜ r′ ·ᶜ ⌜ ⌞ r′ ⌟ ⌝ ·ᶜ wkConₘ ρ δ   ≈˘⟨ +ᶜ-congˡ (·ᶜ-congˡ (wk-·ᶜ ρ)) ⟩
            (γ +ᶜ q ·ᶜ wkConₘ ρ δ) +ᶜ r′ ·ᶜ wkConₘ ρ (⌜ ⌞ r′ ⌟ ⌝ ·ᶜ δ) ∎
      in  _ , ▸t′ , sub (▸H′ ∙ ▸t″) (begin
            γ +ᶜ q ·ᶜ wkConₘ ρ δ ∙ r′                        ≤⟨ ≤ᶜ-refl ∙ p′-q≡r′ .proj₂ r (≤-trans p′≤p p-q≤r) ⟩
            γ +ᶜ q ·ᶜ wkConₘ ρ δ ∙ r                         ≈˘⟨ +ᶜ-congˡ (·ᶜ-congʳ ·⌜⌞⌟⌝) ∙ +-identityʳ _ ⟩
            γ +ᶜ (q · ⌜ ⌞ q ⌟ ⌝) ·ᶜ wkConₘ ρ δ ∙ r + 𝟘       ≈⟨ +ᶜ-congˡ (·ᶜ-assoc _ _ _) ∙ refl ⟩
            γ +ᶜ q ·ᶜ ⌜ ⌞ q ⌟ ⌝ ·ᶜ wkConₘ ρ δ ∙ r + 𝟘        ≈˘⟨ +ᶜ-congˡ (·ᶜ-congˡ (wk-·ᶜ ρ)) ∙ +-congˡ (·-zeroʳ _) ⟩
            γ +ᶜ q ·ᶜ wkConₘ ρ (⌜ ⌞ q ⌟ ⌝ ·ᶜ δ) ∙ r + q · 𝟘  ≡⟨⟩
            (γ ∙ r) +ᶜ q ·ᶜ wkConₘ (step ρ) (⌜ ⌞ q ⌟ ⌝ ·ᶜ δ) ∎)

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
