------------------------------------------------------------------------
-- Inversion lemmata for Heap usage
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Variant
open import Graded.Usage.Restrictions.Natrec

module Graded.Heap.Usage.Inversion
  {a} {M : Set a} {𝕄 : Modality M}
  (type-variant : Type-variant)
  (UR : Usage-restrictions 𝕄)
  (open Usage-restrictions UR)
  (factoring-nr :
    ⦃ has-nr : Nr-available ⦄ →
    Is-factoring-nr M (Natrec-mode-Has-nr 𝕄 has-nr))
  where

open import Definition.Untyped M

open import Graded.Mode 𝕄
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Inversion 𝕄 UR
open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Usage.Restrictions.Instance UR

open import Graded.Heap.Untyped type-variant UR factoring-nr
open import Graded.Heap.Usage type-variant UR factoring-nr

open import Tools.Empty
open import Tools.Fin
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
import Tools.Reasoning.PartialOrder as RPo

open Modality 𝕄
open Type-variant type-variant

private variable
  H : Heap _ _
  A B s t u v z : Term _
  ρ : Wk _ _
  e : Elim _
  S : Stack _
  γ η χ : Conₘ _
  p q q′ r : M
  m : Mode
  x : Fin _
  str : Strength
  l : Universe-level

opaque

  -- Inversion of non-empty stacks

  ▸ˢ-∙-inv :
    η ▸ˢ e ∙ S →
    ∃₂ λ δ γ → δ ▸ᵉ[ ⌞ ∣ S ∣ ⌟ ] e × γ ▸ˢ S × η ≈ᶜ γ +ᶜ ∣ S ∣ ·ᶜ δ
  ▸ˢ-∙-inv (▸e ∙ ▸S) = _ , _ , ▸e , ▸S , ≈ᶜ-refl

opaque

  -- Inversion of empty stacks

  ▸ˢ-ε-inv : η ▸ˢ ε → η ≈ᶜ 𝟘ᶜ
  ▸ˢ-ε-inv ε = ≈ᶜ-refl

opaque

  -- Inversion of state usage.

  ▸ₛ-inv :
    ▸ ⟨ H , t , ρ , S ⟩ →
    ∃₃ λ γ δ η →
    γ ▸ʰ H × δ ▸[ ⌞ ∣ S ∣ ⌟ ] t ×
    η ▸ˢ S × γ ≤ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η
  ▸ₛ-inv (▸ₛ ▸H ▸t ▸S γ≤) =
    _ , _ , _ , ▸H , ▸t , ▸S , γ≤

opaque

  -- Inversion of states with non-empty stacks.

  ▸ₛ-∙-inv :
    ▸ ⟨ H , t , ρ , e ∙ S ⟩ →
    ∃₄ λ γ δ η θ →
    γ ▸ʰ H × δ ▸[ ⌞ ∣ e ∙ S ∣ ⌟ ] t ×
    η ▸ˢ S × θ ▸ᵉ[ ⌞ ∣ S ∣ ⌟ ] e ×
    γ ≤ᶜ ∣ e ∙ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ θ
  ▸ₛ-∙-inv ▸s =
    let _ , _ , _ , ▸H , ▸t , ▸eS , γ≤ = ▸ₛ-inv ▸s
        _ , _ , ▸e , ▸S , η≈ = ▸ˢ-∙-inv ▸eS
    in  _ , _ , _ , _ , ▸H , ▸t , ▸S , ▸e
          , ≤ᶜ-trans γ≤ (≤ᶜ-reflexive (+ᶜ-congˡ η≈))

opaque

  -- Inversion of states with a variable in head position

  ▸ₛ-var-inv :
    ▸ ⟨ H , var x , ρ , S ⟩ →
    ∃₂ λ γ η → γ ▸ʰ H × η ▸ˢ S ×
    γ ≤ᶜ (𝟘ᶜ , wkVar ρ x ≔ ∣ S ∣) +ᶜ η
  ▸ₛ-var-inv {x} {ρ} {S} ▸s =
    let γ , δ , η , ▸H , ▸x , ▸S , γ≤ = ▸ₛ-inv ▸s
    in  γ , η , ▸H , ▸S , (begin
    γ                                                        ≤⟨ γ≤ ⟩
    ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                                 ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (inv-usage-var ▸x))) ⟩
    ∣ S ∣ ·ᶜ wkConₘ ρ (𝟘ᶜ , x ≔ ⌜ ⌞ ∣ S ∣ ⌟ ⌝) +ᶜ η          ≡⟨ cong (λ y → ∣ S ∣ ·ᶜ y +ᶜ η) (wk-,≔ ρ) ⟩
    ∣ S ∣ ·ᶜ (wkConₘ ρ 𝟘ᶜ , wkVar ρ x ≔ ⌜ ⌞ ∣ S ∣ ⌟ ⌝) +ᶜ η  ≡⟨ cong (λ y → ∣ S ∣ ·ᶜ (y , wkVar ρ x ≔ ⌜ ⌞ ∣ S ∣ ⌟ ⌝) +ᶜ η) (wk-𝟘ᶜ ρ) ⟩
    ∣ S ∣ ·ᶜ (𝟘ᶜ , wkVar ρ x ≔ ⌜ ⌞ ∣ S ∣ ⌟ ⌝) +ᶜ η           ≡˘⟨ cong (_+ᶜ η) (update-distrib-·ᶜ _ _ _ _) ⟩
    (∣ S ∣ ·ᶜ 𝟘ᶜ , wkVar ρ x ≔ ∣ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝) +ᶜ η   ≈⟨ +ᶜ-congʳ (update-congˡ (·ᶜ-zeroʳ _)) ⟩
    (𝟘ᶜ , wkVar ρ x ≔ ∣ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝) +ᶜ η            ≡⟨ cong (λ y → (𝟘ᶜ , wkVar ρ x ≔ y) +ᶜ η) ·⌜⌞⌟⌝ ⟩
    (𝟘ᶜ , wkVar ρ x ≔ ∣ S ∣) +ᶜ η                            ∎)
    where
    open ≤ᶜ-reasoning

opaque

  -- A variant of the above

  ▸ₛ-var-inv′ :
    ▸ ⟨ H , var x , ρ , S ⟩ →
    ∃₂ λ γ η → γ ▸ʰ H × η ▸ˢ S ×
    γ ⟨ wkVar ρ x ⟩ ≤ ∣ S ∣ + η ⟨ wkVar ρ x ⟩
  ▸ₛ-var-inv′ {x} {ρ} {S} ▸s =
    let γ , η , ▸H , ▸S , γ≤ = ▸ₛ-var-inv ▸s
    in  γ , η , ▸H , ▸S , (begin
    γ ⟨ wkVar ρ x ⟩                                         ≤⟨ lookup-monotone (wkVar ρ x) γ≤ ⟩
    ((𝟘ᶜ , wkVar ρ x ≔ ∣ S ∣) +ᶜ η) ⟨ wkVar ρ x ⟩           ≡⟨ lookup-distrib-+ᶜ (𝟘ᶜ , wkVar ρ x ≔ ∣ S ∣) η (wkVar ρ x) ⟩
    (𝟘ᶜ , wkVar ρ x ≔ ∣ S ∣) ⟨ wkVar ρ x ⟩ + η ⟨ wkVar ρ x ⟩ ≡⟨ +-congʳ (update-lookup 𝟘ᶜ (wkVar ρ x)) ⟩
    ∣ S ∣ + η ⟨ wkVar ρ x ⟩                                 ∎)
    where
    open RPo ≤-poset

opaque

  -- Inversion of application

  ▸-inv-∘ₑ :
    γ ▸ᵉ[ m ] ∘ₑ p u ρ →
    ∃ λ δ → δ ▸[ m ᵐ· p ] u × γ ≈ᶜ p ·ᶜ wkConₘ ρ δ
  ▸-inv-∘ₑ (∘ₑ ▸u) = _ , ▸u , ≈ᶜ-refl

opaque

  -- Inversion of fst

  ▸-inv-fstₑ :
    γ ▸ᵉ[ m ] fstₑ p → (m ≡ 𝟙ᵐ → p ≤ 𝟙) × γ ≈ᶜ 𝟘ᶜ
  ▸-inv-fstₑ (fstₑ x) = x , ≈ᶜ-refl

opaque

  -- Inversion of snd

  ▸-inv-sndₑ :
    γ ▸ᵉ[ m ] sndₑ p → γ ≈ᶜ 𝟘ᶜ
  ▸-inv-sndₑ sndₑ = ≈ᶜ-refl

opaque

  -- Inversion of prodrec

  ▸-inv-prodrecₑ :
    γ ▸ᵉ[ m ] prodrecₑ r p q A u ρ →
    ∃ λ δ → δ ∙ ⌜ m ⌝ · r · p ∙ ⌜ m ⌝ · r ▸[ m ] u ×
    Prodrec-allowed m r p q × γ ≈ᶜ wkConₘ ρ δ
  ▸-inv-prodrecₑ (prodrecₑ ▸u ok) =
    _ , ▸u , ok , ≈ᶜ-refl

-- "Extra data" for inversion of natrec

data InvUsageNatrecₑ {m n} (p r q : M) (δ η : Conₘ n) (ρ : Wk m n) : Conₘ m → Set a where
  invUsageNatrecNr :
    ⦃ has-nr : Nr-available ⦄ →
    q ≡ nr₂ p r →
    InvUsageNatrecₑ p r q δ η ρ (wkConₘ ρ (nrᶜ p r δ η 𝟘ᶜ))
  invUsageNatrecNoNr :
    ⦃ no-nr : Nr-not-available-GLB ⦄ →
    Greatest-lower-bound q (nrᵢ r 𝟙 p) →
    Greatest-lower-boundᶜ χ (nrᵢᶜ r δ η) →
    InvUsageNatrecₑ p r q δ η ρ (wkConₘ ρ χ)

opaque

  -- Inversion of natrec

  ▸-inv-natrecₑ :
    γ ▸ᵉ[ m ] natrecₑ p q r q′ A z s ρ →
    ∃₃ λ δ η θ → δ ▸[ m ] z × η ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s ×
    θ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A × InvUsageNatrecₑ p r q′ δ η ρ γ
  ▸-inv-natrecₑ (natrecₑ ▸z ▸s ▸A ≡nr₂) =
    _ , _ , _ , ▸z , ▸s , ▸A , invUsageNatrecNr ≡nr₂
  ▸-inv-natrecₑ (natrec-no-nrₑ ▸z ▸s ▸A x-glb χ-glb) =
    _ , _ , _ , ▸z , ▸s , ▸A , invUsageNatrecNoNr x-glb χ-glb

opaque

  -- Inversion of unitrec

  ▸-inv-unitrecₑ :
    γ ▸ᵉ[ m ] unitrecₑ l p q A u ρ →
    ∃ λ δ → δ ▸[ m ] u × Unitrec-allowed m p q ×
    ¬ Unitʷ-η × γ ≈ᶜ wkConₘ ρ δ
  ▸-inv-unitrecₑ (unitrecₑ ▸u ok no-η) =
    _ , ▸u , ok , no-η , ≈ᶜ-refl

opaque

  -- Inversion of emptyrec

  ▸-inv-emptyrecₑ :
    γ ▸ᵉ[ m ] emptyrecₑ p A ρ →
    Emptyrec-allowed m p × γ ≈ᶜ 𝟘ᶜ
  ▸-inv-emptyrecₑ (emptyrecₑ ok) =
    ok , ≈ᶜ-refl

opaque

  -- Inversion of J

  ▸-inv-Jₑ :
    γ ▸ᵉ[ m ] Jₑ p q A t B u v ρ →
    ∃ λ δ → δ ▸[ m ] u × γ ≈ᶜ wkConₘ ρ δ
  ▸-inv-Jₑ (Jₑ ▸u) = _ , ▸u , ≈ᶜ-refl

opaque

  -- Inversion of K

  ▸-inv-Kₑ :
    γ ▸ᵉ[ m ] Kₑ p A t B u ρ →
    ∃ λ δ → δ ▸[ m ] u × γ ≈ᶜ wkConₘ ρ δ
  ▸-inv-Kₑ (Kₑ ▸u) =
    _ , ▸u , ≈ᶜ-refl

opaque

  -- Inversion of []-cong

  ▸-inv-[]-congₑ :
    γ ▸ᵉ[ m ] []-congₑ str A t u ρ →
    []-cong-allowed-mode str m × γ ≈ᶜ 𝟘ᶜ
  ▸-inv-[]-congₑ ([]-congₑ ok) =
    ok , ≈ᶜ-refl

opaque

  -- Inversion of suc

  ▸-inv-sucₑ : γ ▸ᵉ[ m ] sucₑ → ⊥
  ▸-inv-sucₑ ()
