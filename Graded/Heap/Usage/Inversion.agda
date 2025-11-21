------------------------------------------------------------------------
-- Inversion lemmata for Heap usage
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions
open import Definition.Typed.Variant
open import Graded.Usage.Restrictions.Natrec

module Graded.Heap.Usage.Inversion
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (type-variant : Type-variant)
  (UR : Usage-restrictions 𝕄 𝐌)
  (open Usage-restrictions UR)
  (factoring-nr :
    ⦃ has-nr : Nr-available ⦄ →
    Is-factoring-nr M (Natrec-mode-Has-nr 𝕄 has-nr))
  where

open import Definition.Untyped M

open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄
open import Graded.Usage UR
open import Graded.Usage.Inversion UR
open import Graded.Usage.Properties UR
open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Usage.Restrictions.Instance UR

open import Graded.Heap.Untyped type-variant UR factoring-nr
open import Graded.Heap.Untyped.Properties type-variant UR factoring-nr
open import Graded.Heap.Usage type-variant UR factoring-nr

open import Tools.Empty
open import Tools.Fin
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
import Tools.Reasoning.PartialOrder as RPo

open Modality 𝕄
open IsMode 𝐌
open Type-variant type-variant

private variable
  H : Heap _ _
  A B s t u v z : Term _
  ρ : Wk _ _
  c : Cont _
  S : Stack _
  γ η χ : Conₘ _
  p q q′ r : M
  m : Mode
  x : Fin _
  str : Strength
  l : Universe-level

opaque

  -- Inversion of heaps with a "normal" entry on top

  ▸ʰ∙-inv :
    γ ∙ q ▸ʰ H ∙ (p , t , ρ) →
    ∃₂ λ δ η → δ ▸[ ⌞ p ⌟ ] t × η ▸ʰ H × p ≤ q × η ≤ᶜ γ +ᶜ p ·ᶜ wkConₘ ρ δ
  ▸ʰ∙-inv (▸H ∙ ▸t) = _ , _ , ▸t , ▸H , ≤-refl , ≤ᶜ-refl
  ▸ʰ∙-inv (sub {γ = _ ∙ _} ▸H (≤γ ∙ ≤q)) =
    let _ , _ , ▸t , ▸H , p≤ , η≤ = ▸ʰ∙-inv ▸H
    in  _ , _ , ▸t , ▸H
          , ≤-trans p≤ ≤q
          , ≤ᶜ-trans η≤ (+ᶜ-monotoneˡ ≤γ)

opaque

  -- An inversion lemma for ▸ʰ with a dummy entry.

  ▸ʰ●-inv : γ ∙ p ▸ʰ H ∙● → ∃ λ δ → 𝟘 ≤ p × δ ▸ʰ H × δ ≤ᶜ γ
  ▸ʰ●-inv (▸H ∙●) = _ , ≤-refl , ▸H , ≤ᶜ-refl
  ▸ʰ●-inv (sub ▸H (≤γ ∙ ≤p)) =
    let _ , 𝟘≤ , ▸H , δ≤ = ▸ʰ●-inv ▸H
    in  _ , ≤-trans 𝟘≤ ≤p , ▸H
          , ≤ᶜ-trans δ≤ ≤γ

opaque

  -- Inversion of non-empty stacks

  ▸ˢ-∙-inv :
    η ▸ˢ c ∙ S →
    ∃₃ λ p δ γ → ∣ S ∣≡ p × δ ▸ᶜ[ ⌞ p ⌟ ] c × γ ▸ˢ S × η ≈ᶜ γ +ᶜ p ·ᶜ δ
  ▸ˢ-∙-inv (▸ˢ∙ ∣S∣≡ ▸e ▸S) = _ , _ , _ , ∣S∣≡ , ▸e , ▸S , ≈ᶜ-refl

opaque

  -- Inversion of empty stacks

  ▸ˢ-ε-inv : η ▸ˢ ε → η ≈ᶜ 𝟘ᶜ
  ▸ˢ-ε-inv ε = ≈ᶜ-refl

opaque

  -- Inversion of state usage.

  ▸ₛ-inv :
    ▸ ⟨ H , t , ρ , S ⟩ →
    ∃₄ λ p γ δ η →
    ∣ S ∣≡ p ×
    γ ▸ʰ H × δ ▸[ ⌞ p ⌟ ] t ×
    η ▸ˢ S × γ ≤ᶜ p ·ᶜ wkConₘ ρ δ +ᶜ η
  ▸ₛ-inv (▸ₛ ∣S∣≡ ▸H ▸t ▸S γ≤) =
    _ , _ , _ , _ , ∣S∣≡ , ▸H , ▸t , ▸S , γ≤

opaque

  -- Inversion of states with non-empty stacks.

  ▸ₛ-∙-inv :
    ▸ ⟨ H , t , ρ , c ∙ S ⟩ →
    ∃₆ λ p q γ δ η θ →
    ∣ S ∣≡ p × ∣ c ∣ᶜ[ ⌞ p ⌟ ]≡ q ×
    γ ▸ʰ H × δ ▸[ ⌞ p · q ⌟ ] t ×
    η ▸ˢ S × θ ▸ᶜ[ ⌞ p ⌟ ] c ×
    γ ≤ᶜ (p · q) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ p ·ᶜ θ
  ▸ₛ-∙-inv {ρ} ▸s =
    let p , γ , δ , η , ∣cS∣≡ , ▸H , ▸t , ▸cS , γ≤ = ▸ₛ-inv ▸s
        q , δ′ , η′ , ∣S∣≡ , ▸c , ▸S , η≈ = ▸ˢ-∙-inv ▸cS
        r , q′ , ∣c∣≡ , ∣S∣≡′ , p≡ = ∣∣∙-inv ∣cS∣≡
        q′≡q = ∣∣-functional ∣S∣≡′ ∣S∣≡
    in  _ , _ , _ , _ , _ , _ , ∣S∣≡
          , subst (λ q → ∣ _ ∣ᶜ[ ⌞ q ⌟ ]≡ r) q′≡q ∣c∣≡
          , ▸H , ▸-cong (⌞⌟-cong (trans p≡ (·-congʳ q′≡q))) ▸t , ▸S , ▸c
          , (begin
            γ                                           ≤⟨ γ≤ ⟩
            p ·ᶜ wkConₘ ρ δ +ᶜ η                        ≈⟨ +ᶜ-cong (·ᶜ-congʳ p≡) η≈ ⟩
            (q′ · r) ·ᶜ wkConₘ ρ δ +ᶜ (η′ +ᶜ q ·ᶜ δ′)   ≈⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-congʳ q′≡q)) ⟩
            (q · r) ·ᶜ wkConₘ ρ δ +ᶜ η′ +ᶜ q ·ᶜ δ′ ∎)
    where
    open ≤ᶜ-reasoning

opaque

  -- Inversion of states with a variable in head position

  ▸ₛ-var-inv :
    ▸ ⟨ H , var x , ρ , S ⟩ →
    ∃₃ λ p γ η → ∣ S ∣≡ p × γ ▸ʰ H × η ▸ˢ S ×
    γ ≤ᶜ (𝟘ᶜ , wkVar ρ x ≔ p) +ᶜ η
  ▸ₛ-var-inv {x} {ρ} {S} ▸s =
    let p , γ , δ , η , ∣S∣≡ , ▸H , ▸x , ▸S , γ≤ = ▸ₛ-inv ▸s
    in  p , γ , η , ∣S∣≡ , ▸H , ▸S , (begin
    γ                                                ≤⟨ γ≤ ⟩
    p ·ᶜ wkConₘ ρ δ +ᶜ η                             ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (inv-usage-var ▸x))) ⟩
    p ·ᶜ wkConₘ ρ (𝟘ᶜ , x ≔ ⌜ ⌞ p ⌟ ⌝) +ᶜ η          ≡⟨ cong (λ y → p ·ᶜ y +ᶜ η) (wk-,≔ ρ) ⟩
    p ·ᶜ (wkConₘ ρ 𝟘ᶜ , wkVar ρ x ≔ ⌜ ⌞ p ⌟ ⌝) +ᶜ η  ≡⟨ cong (λ y → p ·ᶜ (y , wkVar ρ x ≔ ⌜ ⌞ p ⌟ ⌝) +ᶜ η) (wk-𝟘ᶜ ρ) ⟩
    p ·ᶜ (𝟘ᶜ , wkVar ρ x ≔ ⌜ ⌞ p ⌟ ⌝) +ᶜ η           ≡˘⟨ cong (_+ᶜ η) (update-distrib-·ᶜ _ _ _ _) ⟩
    (p ·ᶜ 𝟘ᶜ , wkVar ρ x ≔ p · ⌜ ⌞ p ⌟ ⌝) +ᶜ η       ≈⟨ +ᶜ-congʳ (update-congˡ (·ᶜ-zeroʳ _)) ⟩
    (𝟘ᶜ , wkVar ρ x ≔ p · ⌜ ⌞ p ⌟ ⌝) +ᶜ η            ≡⟨ cong (λ y → (𝟘ᶜ , wkVar ρ x ≔ y) +ᶜ η) ·⌜⌞⌟⌝ ⟩
    (𝟘ᶜ , wkVar ρ x ≔ p) +ᶜ η                        ∎)
    where
    open ≤ᶜ-reasoning

opaque

  -- A variant of the above

  ▸ₛ-var-inv′ :
    ▸ ⟨ H , var x , ρ , S ⟩ →
    ∃₃ λ p γ η → ∣ S ∣≡ p × γ ▸ʰ H × η ▸ˢ S ×
    γ ⟨ wkVar ρ x ⟩ ≤ p + η ⟨ wkVar ρ x ⟩
  ▸ₛ-var-inv′ {x} {ρ} {S} ▸s =
    let p , γ , η , ∣S∣≡ , ▸H , ▸S , γ≤ = ▸ₛ-var-inv ▸s
    in  p , γ , η , ∣S∣≡ , ▸H , ▸S , (begin
    γ ⟨ wkVar ρ x ⟩                                     ≤⟨ lookup-monotone (wkVar ρ x) γ≤ ⟩
    ((𝟘ᶜ , wkVar ρ x ≔ p) +ᶜ η) ⟨ wkVar ρ x ⟩           ≡⟨ lookup-distrib-+ᶜ (𝟘ᶜ , wkVar ρ x ≔ p) η (wkVar ρ x) ⟩
    (𝟘ᶜ , wkVar ρ x ≔ p) ⟨ wkVar ρ x ⟩ + η ⟨ wkVar ρ x ⟩ ≡⟨ +-congʳ (update-lookup 𝟘ᶜ (wkVar ρ x)) ⟩
    p + η ⟨ wkVar ρ x ⟩                                 ∎)
    where
    open RPo ≤-poset

opaque

  -- Inversion of application

  ▸-inv-∘ₑ :
    γ ▸ᶜ[ m ] ∘ₑ p u ρ →
    ∃ λ δ → δ ▸[ m ᵐ· p ] u × γ ≈ᶜ p ·ᶜ wkConₘ ρ δ
  ▸-inv-∘ₑ (∘ₑ ▸u) = _ , ▸u , ≈ᶜ-refl

opaque

  -- Inversion of fst

  ▸-inv-fstₑ :
    γ ▸ᶜ[ m ] fstₑ p → (⌜ m ⌝ ≢ 𝟘 → p ≤ 𝟙) × γ ≈ᶜ 𝟘ᶜ
  ▸-inv-fstₑ (fstₑ x) = x , ≈ᶜ-refl

opaque

  -- Inversion of snd

  ▸-inv-sndₑ :
    γ ▸ᶜ[ m ] sndₑ p → γ ≈ᶜ 𝟘ᶜ
  ▸-inv-sndₑ sndₑ = ≈ᶜ-refl

opaque

  -- Inversion of prodrec

  ▸-inv-prodrecₑ :
    γ ▸ᶜ[ m ] prodrecₑ r p q A u ρ →
    ∃ λ δ → δ ∙ ⌜ m ⌝ · r · p ∙ ⌜ m ⌝ · r ▸[ m ] u ×
    Prodrec-allowed m r p q × γ ≈ᶜ wkConₘ ρ δ
  ▸-inv-prodrecₑ (prodrecₑ ▸u ok) =
    _ , ▸u , ok , ≈ᶜ-refl

-- "Extra data" for inversion of natrec

data InvUsageNatrecₑ {m n} (p r : M) (δ η : Conₘ n) (ρ : Wk m n) : Conₘ m → Set a where
  invUsageNatrecNr :
    ⦃ has-nr : Nr-available ⦄ →
    InvUsageNatrecₑ p r δ η ρ (wkConₘ ρ (nrᶜ p r δ η 𝟘ᶜ))
  invUsageNatrecNoNr :
    ⦃ no-nr : Nr-not-available-GLB ⦄ →
    Greatest-lower-boundᶜ χ (nrᵢᶜ r δ η) →
    InvUsageNatrecₑ p r δ η ρ (wkConₘ ρ χ)

opaque

  -- Inversion of natrec

  ▸-inv-natrecₑ :
    γ ▸ᶜ[ m ] natrecₑ p q r A z s ρ →
    ∃₃ λ δ η θ → δ ▸[ m ] z × η ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s ×
    θ ∙ ⌜ 𝟘ᵐ ⌝ · q ▸[ 𝟘ᵐ ] A × InvUsageNatrecₑ p r δ η ρ γ
  ▸-inv-natrecₑ (natrecₑ ▸z ▸s ▸A) =
    _ , _ , _ , ▸z , ▸s , ▸A , invUsageNatrecNr
  ▸-inv-natrecₑ (natrec-no-nrₑ ▸z ▸s ▸A χ-glb) =
    _ , _ , _ , ▸z , ▸s , ▸A , invUsageNatrecNoNr χ-glb

opaque

  -- Inversion of unitrec

  ▸-inv-unitrecₑ :
    γ ▸ᶜ[ m ] unitrecₑ l p q A u ρ →
    ∃ λ δ → δ ▸[ m ] u × Unitrec-allowed m p q ×
    ¬ Unitʷ-η × γ ≈ᶜ wkConₘ ρ δ
  ▸-inv-unitrecₑ (unitrecₑ ▸u ok no-η) =
    _ , ▸u , ok , no-η , ≈ᶜ-refl

opaque

  -- Inversion of emptyrec

  ▸-inv-emptyrecₑ :
    γ ▸ᶜ[ m ] emptyrecₑ p A ρ →
    Emptyrec-allowed m p × γ ≈ᶜ 𝟘ᶜ
  ▸-inv-emptyrecₑ (emptyrecₑ ok) =
    ok , ≈ᶜ-refl

opaque

  -- Inversion of J

  ▸-inv-Jₑ :
    γ ▸ᶜ[ m ] Jₑ p q A t B u v ρ →
    ∃ λ δ → δ ▸[ m ] u × γ ≈ᶜ wkConₘ ρ δ
  ▸-inv-Jₑ (Jₑ ▸u) = _ , ▸u , ≈ᶜ-refl

opaque

  -- Inversion of K

  ▸-inv-Kₑ :
    γ ▸ᶜ[ m ] Kₑ p A t B u ρ →
    ∃ λ δ → δ ▸[ m ] u × γ ≈ᶜ wkConₘ ρ δ
  ▸-inv-Kₑ (Kₑ ▸u) =
    _ , ▸u , ≈ᶜ-refl

opaque

  -- Inversion of []-cong

  ▸-inv-[]-congₑ :
    γ ▸ᶜ[ m ] []-congₑ str A t u ρ →
    []-cong-allowed-mode str m × γ ≈ᶜ 𝟘ᶜ
  ▸-inv-[]-congₑ ([]-congₑ ok) =
    ok , ≈ᶜ-refl

opaque

  -- Inversion of suc

  ▸-inv-sucₑ : γ ▸ᶜ[ m ] sucₑ → ⊥
  ▸-inv-sucₑ ()
