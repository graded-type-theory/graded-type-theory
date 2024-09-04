------------------------------------------------------------------------
-- Properties of the usage relation for Heaps, Stacks and States.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Variant

module Heap.Usage.Properties
  {a} {M : Set a} {𝕄 : Modality M}
  (UR : Usage-restrictions 𝕄)
  (type-variant : Type-variant)
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
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Inversion 𝕄 UR

open import Heap.Untyped 𝕄 hiding (wkᶜ)
open import Heap.Untyped.Properties 𝕄 type-variant
open import Heap.Usage 𝕄 UR

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Sum hiding (sym)
import Tools.Reasoning.PartialOrder as RPo


private variable
  γ δ η : Conₘ _
  p q r : M
  m : Mode
  H H′ : Heap _
  x : Fin _
  y : Ptr _
  t : Term _
  E : Env _ _
  S : Stack _
  e : Elim _
  c : Closureₘ _ _
  c′ : Closure _ _

opaque

  -- Well-usage for the initial state

  ▸initial : γ ▸ t → 𝟘ᶜ ⨾ γ ⨾ 𝟘ᶜ ▸ initial t
  ▸initial {γ = ε} ▸t = ε , ▸t , ε , ε

opaque

  -- Subsumption for closures

  subᶜ : γ ⨾ p ▸ᶜ[ m ] c → p ≤ q → γ ⨾ q ▸ᶜ[ m ] c
  subᶜ (▸ᶜ ▸t p′≤p) p≤q = ▸ᶜ ▸t (≤-trans p′≤p p≤q)

opaque

  -- Subsumption for heaps

  subₕ : γ ▸ʰ H → γ ≤ᶜ δ → δ ▸ʰ H
  subₕ {δ = ε} ε ε = ε
  subₕ {δ = δ ∙ p} (▸H ∙ ▸c) (γ≤δ ∙ p″≤p) =
    subₕ ▸H (+ᶜ-monotone γ≤δ (·ᶜ-monotoneˡ p″≤p)) ∙ subᶜ ▸c p″≤p

opaque

  -- A well-resourced heap under the zero-context has all grades bounded by 𝟘.

  𝟘▸H→H≤𝟘 : 𝟘ᶜ ▸ʰ H → H ≤ʰ 𝟘
  𝟘▸H→H≤𝟘 ε = ε
  𝟘▸H→H≤𝟘 (_∙_ {E = E} {δ} ▸H (▸ᶜ _ p≤𝟘)) =
    𝟘▸H→H≤𝟘 (subst (_▸ʰ _) (≈ᶜ→≡ lemma) ▸H) ∙ p≤𝟘
    where
    open import Tools.Reasoning.Equivalence Conₘ-setoid
    lemma : 𝟘ᶜ +ᶜ 𝟘 ·ᶜ wkᶜ E δ ≈ᶜ 𝟘ᶜ
    lemma = begin
      𝟘ᶜ +ᶜ 𝟘 ·ᶜ wkᶜ E δ  ≈⟨ +ᶜ-identityˡ _ ⟩
      𝟘 ·ᶜ wkᶜ E δ        ≈⟨ ·ᶜ-zeroˡ _ ⟩
      𝟘ᶜ                     ∎

opaque

  -- The multiplicity of a well-resourced eliminator is not zero

  ▸∣e∣≢𝟘 : ⦃ Has-well-behaved-zero M semiring-with-meet ⦄
         → γ ▸ᵉ[ q ] e → ∣ e ∣ᵉ ≢ 𝟘
  ▸∣e∣≢𝟘 (∘ₑ x) = non-trivial
  ▸∣e∣≢𝟘 (fstₑ x) = non-trivial
  ▸∣e∣≢𝟘 sndₑ = non-trivial
  ▸∣e∣≢𝟘 (prodrecₑ x r≢𝟘) = r≢𝟘
  ▸∣e∣≢𝟘 (natrecₑ x x₁ x₂) = nr₂≢𝟘
  ▸∣e∣≢𝟘 (unitrecₑ x 𝟘≤𝟙) refl = 𝟘≰𝟙 𝟘≤𝟙
  ▸∣e∣≢𝟘 (Jₑ x) = ω≢𝟘
  ▸∣e∣≢𝟘 (Kₑ x) = ω≢𝟘
  ▸∣e∣≢𝟘 sucₑ = non-trivial

opaque

  -- The multiplicity of a well-resourced stack is not zero

  ▸∣S∣≢𝟘 : ⦃ Has-well-behaved-zero M semiring-with-meet ⦄
         → γ ▸ˢ S → ∣ S ∣ ≢ 𝟘
  ▸∣S∣≢𝟘 ε = non-trivial
  ▸∣S∣≢𝟘 (▸e ∙ ▸S) ∣eS∣≡𝟘 =
    case zero-product ∣eS∣≡𝟘 of λ where
      (inj₁ ∣S∣≡𝟘) → ▸∣S∣≢𝟘 ▸S ∣S∣≡𝟘
      (inj₂ ∣e∣≡𝟘) → ▸∣e∣≢𝟘 ▸e ∣e∣≡𝟘

opaque

  -- In a well-resorced heap, a pointer lookup yields a well-resourced
  -- term and a well-resourced heap.

  ▸-heapLookup : ⦃ Has-well-behaved-zero M semiring-with-meet ⦄
               → H ⊢ y ↦[ q ] t , E ⨾ H′
               → γ ▸ʰ H
               → γ ⟨ y ⟩ - q ≤ r
               → q ≢ 𝟘
               → ∃ λ δ → δ ▸ t × (γ , y ≔ r) +ᶜ q ·ᶜ wkᶜ E δ ▸ʰ H′
  ▸-heapLookup {q} {r} (here {r = r′} mp′-q≡r′)
      (_∙_ {p} {m} ▸H (▸ᶜ {q = p′} ▸t mp′≤p)) p-q≤r q≢𝟘 =
    case mp-q≡r→m≡𝟙 m q≢𝟘 mp′-q≡r′ of λ {
      refl →
    _ , ▸t
      , subₕ ▸H lemma₁ ∙ ▸ᶜ¹ ▸t lemma₂ }
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
    mp-q≡r→m≡𝟙 : ∀ {q p r} m → q ≢ 𝟘 → ⌜ m ⌝ · p - q ≡ r → m ≡ 𝟙ᵐ
    mp-q≡r→m≡𝟙 𝟘ᵐ q≢𝟘 x =
      ⊥-elim (𝟘-q≢p q≢𝟘 (subst (λ x → x - _ ≡ _) (·-zeroˡ _) x))
    mp-q≡r→m≡𝟙 𝟙ᵐ _ _ = refl
  ▸-heapLookup {H = H ∙ (p′ , u , E)} {y +1} {q} {γ = γ ∙ p} {r}
      (there {c = _ , E′} d) (_∙_ {δ} ▸H (▸ᶜ ▸u p′≤p)) γ⟨y⟩-q≤r q≢𝟘 =
    case p+q-r≤p-r+q γ⟨y⟩-q≤r ((p ·ᶜ wkᶜ E δ) ⟨ y ⟩) of λ
      γ⟨y⟩+pδ⟨y⟩-q≤pδ⟨y⟩+r →
    case subst (_- q ≤ ((p ·ᶜ wkᶜ E δ) ⟨ y ⟩ + r))
           (sym (lookup-distrib-+ᶜ γ (p ·ᶜ wkᶜ E δ) y))
           γ⟨y⟩+pδ⟨y⟩-q≤pδ⟨y⟩+r of λ
      γ+pδ⟨y⟩-q≤pδ⟨y⟩+r →
    case ▸-heapLookup d ▸H γ+pδ⟨y⟩-q≤pδ⟨y⟩+r q≢𝟘 of λ
      (δ′ , ▸t , ▸H′) →
    _ , ▸t
      , subₕ ▸H′ lemma₁
      ∙ ▸ᶜ ▸u lemma₂
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

-- Some properties proven under the assumption that the modality
-- supports subtraction.

module _ (subtraction-ok : Supports-subtraction) where

  opaque

    -- In a well-resorced heap, lookup of q copies succeeds for pointers whose
    -- associated grade is at most p + q for some p.

    ▸H→y↦ : γ ▸ʰ H → γ ⟨ y ⟩ ≤ p + q
          → ∃₃ λ n (c : Closure _ n) H′ → H ⊢ y ↦[ q ] c ⨾ H′
    ▸H→y↦ {y = y0} {p} {q} (_∙_ {p = p′} ▸H (▸ᶜ {q = q′} _ mq′≤p′)) p′≤p+q =
      _ , _ , _
        , here (subtraction-ok (≤-trans mq′≤p′ p′≤p+q) .proj₂)
    ▸H→y↦ {γ = γ ∙ r} {y = _+1 y} {p} {q} (_∙_ {E} {δ} ▸H _) γ⟨y⟩≤p+q =
      case ▸H→y↦ {y = y} ▸H lemma of λ
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

  opaque

    -- A variant of the above property with usage of states

    ▸s→y↦ : γ ⨾ δ ⨾ η ▸ ⟨ H , var x , E , S ⟩
          → ∃₃ λ n (c : Closure _ n) H′ → H ⊢ wkVar E x ↦[ ∣ S ∣ ] c ⨾ H′
    ▸s→y↦ {γ} {δ} {η} {x} {E} {S} (▸H , ▸t , ▸S , γ≤) =
      ▸H→y↦ ▸H lemma
      where
      open RPo ≤-poset
      lemma′ : (∣ S ∣ ·ᶜ wkᶜ E δ) ⟨ wkVar E x ⟩ ≤ ∣ S ∣
      lemma′ = begin
        (∣ S ∣ ·ᶜ wkᶜ E δ) ⟨ wkVar E x ⟩ ≈⟨ lookup-distrib-·ᶜ (wkᶜ E δ) ∣ S ∣ (wkVar E x) ⟩
        ∣ S ∣ · wkᶜ E δ ⟨ wkVar E x ⟩    ≡⟨ cong (∣ S ∣ ·_) (wk-⟨⟩ E) ⟩
        ∣ S ∣ · δ ⟨ x ⟩                     ≤⟨ ·-monotoneʳ (lookup-monotone x (inv-usage-var ▸t)) ⟩
        ∣ S ∣ · (𝟘ᶜ , x ≔ 𝟙) ⟨ x ⟩          ≡⟨ cong (∣ S ∣ ·_) (update-lookup 𝟘ᶜ x) ⟩
        ∣ S ∣ · 𝟙                          ≈⟨ ·-identityʳ _ ⟩
        ∣ S ∣                              ∎
      lemma : γ ⟨ wkVar E x ⟩ ≤ η ⟨ wkVar E x ⟩ + ∣ S ∣
      lemma = begin
        γ ⟨ wkVar E x ⟩                                      ≤⟨ lookup-monotone (wkVar E x) γ≤ ⟩
        (∣ S ∣ ·ᶜ wkᶜ E δ +ᶜ η) ⟨ wkVar E x ⟩             ≡⟨ lookup-distrib-+ᶜ (∣ S ∣ ·ᶜ wkᶜ E δ) η (wkVar E x) ⟩
        (∣ S ∣ ·ᶜ wkᶜ E δ) ⟨ wkVar E x ⟩ + η ⟨ wkVar E x ⟩ ≤⟨ +-monotoneˡ lemma′ ⟩
        ∣ S ∣ + η ⟨ wkVar E x ⟩                              ≈⟨ +-comm _ _ ⟩
        η ⟨ wkVar E x ⟩ + ∣ S ∣                              ∎

  opaque

    -- In a well-resourced state, lookup with update succeeds and has the same
    -- result as lookup without update

    ▸↦→↦[] : H ⊢ wkVar E x ↦ c′ → γ ⨾ δ ⨾ η ▸ ⟨ H , var x , E , S ⟩
           → ∃ λ H′ → H ⊢ wkVar E x ↦[ ∣ S ∣ ] c′ ⨾ H′
    ▸↦→↦[] d ▸s =
      case ▸s→y↦ ▸s of λ
        (_ , _ , _ , d′) →
      case lookup-det′ d (↦[]→↦ d′) of λ {
        (refl , refl , refl) →
      _ , d′ }
