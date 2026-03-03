------------------------------------------------------------------------
-- Weakening of grade contexts.
------------------------------------------------------------------------

import Graded.Modality

module Graded.Context.Weakening
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  where

open Modality 𝕄

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄

open import Definition.Untyped.NotParametrised

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; Sequence)
open import Tools.Product
open import Tools.PropositionalEquality as PE
open import Tools.Sum
import Tools.Reasoning.PartialOrder

private variable
  m n ℓ : Nat
  p r : M
  γ δ η θ : Conₘ _
  x : Fin _
  ρ : Wk _ _

------------------------------------------------------------------------
-- The function wkConₘ

-- Weakenings of modality contexts

wkConₘ : Wk m n → Conₘ n → Conₘ m
wkConₘ id γ = γ
wkConₘ (step ρ) γ = (wkConₘ ρ γ) ∙ 𝟘
wkConₘ (lift ρ) (γ ∙ p) = wkConₘ ρ γ ∙ p

-- Weakening the zero context is the zero context
-- wkConₘ ρ 𝟘ᶜ ≡ 𝟘ᶜ

wk-𝟘ᶜ : (ρ : Wk m n) → wkConₘ ρ 𝟘ᶜ ≡ 𝟘ᶜ
wk-𝟘ᶜ id = PE.refl
wk-𝟘ᶜ (step ρ) = cong (λ γ → γ ∙ 𝟘) (wk-𝟘ᶜ ρ)
wk-𝟘ᶜ (lift ρ) = cong (λ γ → γ ∙ 𝟘) (wk-𝟘ᶜ ρ)

-- Weakening of modality contexts distribute over addition
-- wkConₘ ρ (γ +ᶜ δ) ≈ᶜ wkConₘ ρ γ +ᶜ wkConₘ ρ δ

wk-+ᶜ : (ρ : Wk m n) → wkConₘ ρ (γ +ᶜ δ) ≈ᶜ wkConₘ ρ γ +ᶜ wkConₘ ρ δ
wk-+ᶜ id = ≈ᶜ-refl
wk-+ᶜ (step ρ) = wk-+ᶜ ρ ∙ PE.sym (+-identityˡ 𝟘)
wk-+ᶜ {γ = γ ∙ p} {δ ∙ q} (lift ρ) = wk-+ᶜ ρ ∙ refl

-- Weakening of modality contexts distribute over multiplication
-- wkConₘ ρ (p ·ᶜ γ) ≈ᶜ p ·ᶜ wkConₘ ρ γ

wk-·ᶜ : (ρ : Wk m n) → wkConₘ ρ (p ·ᶜ γ) ≈ᶜ p ·ᶜ wkConₘ ρ γ
wk-·ᶜ id = ≈ᶜ-refl
wk-·ᶜ (step ρ) = wk-·ᶜ ρ ∙ PE.sym (·-zeroʳ _)
wk-·ᶜ {γ = γ ∙ p} (lift ρ) = wk-·ᶜ ρ ∙ refl

-- Weakening of modality contexts distribute over meet
-- wkConₘ ρ (γ ∧ᶜ δ) ≈ᶜ wkConₘ ρ γ ∧ᶜ wkConₘ ρ δ

wk-∧ᶜ : (ρ : Wk m n) → wkConₘ ρ (γ ∧ᶜ δ) ≈ᶜ wkConₘ ρ γ ∧ᶜ wkConₘ ρ δ
wk-∧ᶜ id = ≈ᶜ-refl
wk-∧ᶜ (step ρ) = wk-∧ᶜ ρ ∙ PE.sym (∧-idem 𝟘)
wk-∧ᶜ {γ = γ ∙ p} {δ ∙ q} (lift ρ) = wk-∧ᶜ ρ ∙ refl

-- Weakening of modality contexts distribute over the reccurence operator
-- wkConₘ ρ (γ ⊛ᵣ δ) ≈ᶜ (wkConₘ ρ γ) ⊛ᵣ (wkConₘ ρ δ)

wk-⊛ᶜ :
  ⦃ has-star : Has-star 𝕄 ⦄ →
  (ρ : Wk m n) → wkConₘ ρ (γ ⊛ᶜ δ ▷ r) ≈ᶜ (wkConₘ ρ γ) ⊛ᶜ (wkConₘ ρ δ) ▷ r
wk-⊛ᶜ id = ≈ᶜ-refl
wk-⊛ᶜ (step ρ) = wk-⊛ᶜ ρ ∙ PE.sym (⊛-idem-𝟘 _)
wk-⊛ᶜ {γ = γ ∙ p} {δ ∙ q} (lift ρ) = wk-⊛ᶜ ρ ∙ refl

-- The function wkConₘ ρ commutes with nrᶜ p r.

wk-nrᶜ :
  ⦃ has-nr : Has-nr 𝕄 ⦄ →
  (ρ : Wk m n) →
  wkConₘ ρ (nrᶜ p r γ δ η) ≈ᶜ
  nrᶜ p r (wkConₘ ρ γ) (wkConₘ ρ δ) (wkConₘ ρ η)
wk-nrᶜ id =
  ≈ᶜ-refl
wk-nrᶜ (step ρ) =
  wk-nrᶜ ρ ∙ PE.sym nr-𝟘
wk-nrᶜ {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} (lift ρ) =
  wk-nrᶜ ρ ∙ refl

-- Congruence of modality context weakening

wk-≈ᶜ : (ρ : Wk m n) → γ ≈ᶜ δ → wkConₘ ρ γ ≈ᶜ wkConₘ ρ δ
wk-≈ᶜ id γ≈δ = γ≈δ
wk-≈ᶜ (step ρ) γ≈δ = wk-≈ᶜ ρ γ≈δ ∙ refl
wk-≈ᶜ (lift ρ) (γ≈δ ∙ p≈q) = wk-≈ᶜ ρ γ≈δ ∙ p≈q

opaque

  -- The function wkConₘ ρ commutes with nrᵢᶜ r.

  wk-nrᵢᶜ :
    ∀ i
    (ρ : Wk m n) →
    wkConₘ ρ (nrᵢᶜ r γ δ i) ≈ᶜ nrᵢᶜ r (wkConₘ ρ γ) (wkConₘ ρ δ) i
  wk-nrᵢᶜ _ id = ≈ᶜ-refl
  wk-nrᵢᶜ i (step ρ) =
    wk-nrᵢᶜ i ρ ∙ PE.sym (nrᵢ-𝟘 i)
  wk-nrᵢᶜ {γ = _ ∙ _} {δ = _ ∙ _} i (lift ρ) =
    wk-nrᵢᶜ i ρ ∙ refl

-- Weakening of modality contexts is monotone
-- If γ ≤ᶜ δ then wkConₘ ρ γ ≤ᶜ wkConₘ ρ δ

wk-≤ᶜ : (ρ : Wk m n) → γ ≤ᶜ δ → wkConₘ ρ γ ≤ᶜ wkConₘ ρ δ
wk-≤ᶜ id γ≤δ = γ≤δ
wk-≤ᶜ (step ρ) γ≤δ = (wk-≤ᶜ ρ γ≤δ) ∙ ≤-refl
wk-≤ᶜ {γ = γ ∙ p} {δ ∙ q} (lift ρ) (γ≤δ ∙ p≤q) = wk-≤ᶜ ρ γ≤δ ∙ p≤q

-- Weakening of context lookups

wk-⟨⟩ : (ρ : Wk m n) → wkConₘ ρ γ ⟨ wkVar ρ x ⟩ ≡ γ ⟨ x ⟩
wk-⟨⟩ id = refl
wk-⟨⟩ (step ρ) = wk-⟨⟩ ρ
wk-⟨⟩ {γ = γ ∙ p} {x = x0} (lift ρ) = refl
wk-⟨⟩ {γ = γ ∙ p} {x = x +1} (lift ρ) = wk-⟨⟩ ρ

-- Weakening of context updates

wk-,≔ : (ρ : Wk m n) → wkConₘ ρ (γ , x ≔ p) ≡ wkConₘ ρ γ , wkVar ρ x ≔ p
wk-,≔ id = refl
wk-,≔ (step ρ) = cong (_∙ 𝟘) (wk-,≔ ρ)
wk-,≔ {γ = γ ∙ p} {x = x0} (lift ρ) = refl
wk-,≔ {γ = γ ∙ p} {x = x +1} (lift ρ) = cong (_∙ p) (wk-,≔ ρ)

-- Composition of context Weakenings

wk-•ᶜ : (ρ : Wk m n) (ρ′ : Wk n ℓ)
      → wkConₘ (ρ • ρ′) γ ≡ wkConₘ ρ (wkConₘ ρ′ γ)
wk-•ᶜ id ρ′ = refl
wk-•ᶜ (step ρ) ρ′ = cong (_∙ 𝟘) (wk-•ᶜ ρ ρ′)
wk-•ᶜ (lift ρ) id = refl
wk-•ᶜ (lift ρ) (step ρ′) = cong (_∙ 𝟘) (wk-•ᶜ ρ ρ′)
wk-•ᶜ {γ = γ ∙ p} (lift ρ) (lift ρ′) = cong (_∙ p) (wk-•ᶜ ρ ρ′)

opaque

  -- Weakening of greatest lower bounds

  wk-GLBᶜ : ∀ {δ : Sequence (Conₘ n)}
          → (ρ : Wk m n)
          → Greatest-lower-boundᶜ γ (λ i → δ i)
          → Greatest-lower-boundᶜ (wkConₘ ρ γ) (λ i → wkConₘ ρ (δ i))
  wk-GLBᶜ id γ≤ = γ≤
  wk-GLBᶜ (step ρ) γ≤ =
    let γ≤′ , γ-glb = wk-GLBᶜ ρ γ≤
    in  (λ i → γ≤′ i ∙ ≤-refl) ,
        λ { (η ∙ q) η≤ → γ-glb η (λ i → tailₘ-monotone (η≤ i)) ∙ headₘ-monotone (η≤ 0) }
  wk-GLBᶜ {γ = γ ∙ p} {δ} (lift ρ) γ≤ =
    let γₜ-glb , γₕ-glb = GLBᶜ-pointwise γ≤
        γ≤′ , γ-glb = wk-GLBᶜ ρ γₜ-glb
    in  (λ i → begin
          wkConₘ ρ γ ∙ p ≤⟨ wk-≤ᶜ ρ (γₜ-glb .proj₁ i) ∙ γₕ-glb .proj₁ i ⟩
          wkConₘ (lift ρ) (tailₘ (δ i) ∙ headₘ (δ i)) ≡⟨ cong (wkConₘ (lift ρ)) (headₘ-tailₘ-correct (δ i)) ⟩
          wkConₘ (lift ρ) (δ i) ∎)
      , λ η η≤ →
          let η≤′ : ∀ i → η ≤ᶜ wkConₘ ρ (tailₘ (δ i)) ∙ headₘ (δ i)
              η≤′ i = begin
                η                                           ≤⟨ η≤ i ⟩
                wkConₘ (lift ρ) (δ i)                       ≡˘⟨ cong (wkConₘ (lift ρ)) (headₘ-tailₘ-correct (δ i)) ⟩
                wkConₘ (lift ρ) (tailₘ (δ i) ∙ headₘ (δ i)) ≡⟨⟩
                wkConₘ ρ (tailₘ (δ i)) ∙ headₘ (δ i)        ∎
          in begin
            η                 ≡˘⟨ headₘ-tailₘ-correct η ⟩
            tailₘ η ∙ headₘ η ≤⟨ γ-glb (tailₘ η) (tailₘ-monotone ∘→ η≤′) ∙
                                γₕ-glb .proj₂ (headₘ η) (headₘ-monotone ∘→ η≤′) ⟩
            wkConₘ ρ γ ∙ p ∎
    where
    open ≤ᶜ-reasoning

opaque

  -- The result of weakening ε is 𝟘ᶜ.

  wkConₘ-ε : wkConₘ ρ ε ≡ 𝟘ᶜ
  wkConₘ-ε {ρ} = wk-𝟘ᶜ ρ

------------------------------------------------------------------------
-- The function wkConₘ⁻¹

-- A left inverse of wkConₘ ρ.

wkConₘ⁻¹ : Wk m n → Conₘ m → Conₘ n
wkConₘ⁻¹ id       γ       = γ
wkConₘ⁻¹ (step ρ) (γ ∙ _) = wkConₘ⁻¹ ρ γ
wkConₘ⁻¹ (lift ρ) (γ ∙ p) = wkConₘ⁻¹ ρ γ ∙ p

-- The function wkConₘ⁻¹ ρ is a left inverse of wkConₘ ρ.

wkConₘ⁻¹-wkConₘ : (ρ : Wk m n) → wkConₘ⁻¹ ρ (wkConₘ ρ γ) ≡ γ
wkConₘ⁻¹-wkConₘ             id       = refl
wkConₘ⁻¹-wkConₘ             (step ρ) = wkConₘ⁻¹-wkConₘ ρ
wkConₘ⁻¹-wkConₘ {γ = _ ∙ _} (lift ρ) = cong (_∙ _) (wkConₘ⁻¹-wkConₘ ρ)

-- Congruence of the function wkConₘ⁻¹ ρ.

wkConₘ⁻¹-≈ᶜ : (ρ : Wk m n) → γ ≈ᶜ δ → wkConₘ⁻¹ ρ γ ≈ᶜ wkConₘ⁻¹ ρ δ
wkConₘ⁻¹-≈ᶜ id γ≈δ = γ≈δ
wkConₘ⁻¹-≈ᶜ (step ρ) (γ≈δ ∙ _) = wkConₘ⁻¹-≈ᶜ ρ γ≈δ
wkConₘ⁻¹-≈ᶜ (lift ρ) (γ≈δ ∙ p≈q) = wkConₘ⁻¹-≈ᶜ ρ γ≈δ ∙ p≈q

-- The function wkConₘ⁻¹ ρ is monotone.

wkConₘ⁻¹-monotone : (ρ : Wk m n) → γ ≤ᶜ δ → wkConₘ⁻¹ ρ γ ≤ᶜ wkConₘ⁻¹ ρ δ
wkConₘ⁻¹-monotone id leq =
  leq
wkConₘ⁻¹-monotone {γ = _ ∙ _} {δ = _ ∙ _} (step ρ) (leq ∙ _) =
  wkConₘ⁻¹-monotone ρ leq
wkConₘ⁻¹-monotone {γ = _ ∙ _} {δ = _ ∙ _} (lift ρ) (leq₁ ∙ leq₂) =
  wkConₘ⁻¹-monotone ρ leq₁ ∙ leq₂

-- The function wkConₘ⁻¹ ρ maps 𝟘ᶜ to 𝟘ᶜ.

wkConₘ⁻¹-𝟘ᶜ : (ρ : Wk m n) → wkConₘ⁻¹ ρ 𝟘ᶜ ≈ᶜ 𝟘ᶜ
wkConₘ⁻¹-𝟘ᶜ id       = ≈ᶜ-refl
wkConₘ⁻¹-𝟘ᶜ (step ρ) = wkConₘ⁻¹-𝟘ᶜ ρ
wkConₘ⁻¹-𝟘ᶜ (lift ρ) = wkConₘ⁻¹-𝟘ᶜ ρ ∙ refl

-- The function wkConₘ⁻¹ ρ commutes with _+ᶜ_.

wkConₘ⁻¹-+ᶜ :
  (ρ : Wk m n) → wkConₘ⁻¹ ρ (γ +ᶜ δ) ≈ᶜ wkConₘ⁻¹ ρ γ +ᶜ wkConₘ⁻¹ ρ δ
wkConₘ⁻¹-+ᶜ                         id       = ≈ᶜ-refl
wkConₘ⁻¹-+ᶜ {γ = _ ∙ _} {δ = _ ∙ _} (step ρ) = wkConₘ⁻¹-+ᶜ ρ
wkConₘ⁻¹-+ᶜ {γ = _ ∙ _} {δ = _ ∙ _} (lift ρ) = wkConₘ⁻¹-+ᶜ ρ ∙ refl

-- The function wkConₘ⁻¹ ρ commutes with _∧ᶜ_.

wkConₘ⁻¹-∧ᶜ :
  (ρ : Wk m n) → wkConₘ⁻¹ ρ (γ ∧ᶜ δ) ≈ᶜ wkConₘ⁻¹ ρ γ ∧ᶜ wkConₘ⁻¹ ρ δ
wkConₘ⁻¹-∧ᶜ                         id       = ≈ᶜ-refl
wkConₘ⁻¹-∧ᶜ {γ = _ ∙ _} {δ = _ ∙ _} (step ρ) = wkConₘ⁻¹-∧ᶜ ρ
wkConₘ⁻¹-∧ᶜ {γ = _ ∙ _} {δ = _ ∙ _} (lift ρ) = wkConₘ⁻¹-∧ᶜ ρ ∙ refl

-- The function wkConₘ⁻¹ ρ commutes with p ·ᶜ_.

wkConₘ⁻¹-·ᶜ :
  (ρ : Wk m n) → wkConₘ⁻¹ ρ (p ·ᶜ γ) ≈ᶜ p ·ᶜ wkConₘ⁻¹ ρ γ
wkConₘ⁻¹-·ᶜ             id       = ≈ᶜ-refl
wkConₘ⁻¹-·ᶜ {γ = _ ∙ _} (step ρ) = wkConₘ⁻¹-·ᶜ ρ
wkConₘ⁻¹-·ᶜ {γ = _ ∙ _} (lift ρ) = wkConₘ⁻¹-·ᶜ ρ ∙ refl

-- The function wkConₘ⁻¹ ρ commutes with _⊛ᶜ_▷ r.

wkConₘ⁻¹-⊛ᶜ :
  ⦃ has-star : Has-star 𝕄 ⦄
  (ρ : Wk m n) →
  wkConₘ⁻¹ ρ (γ ⊛ᶜ δ ▷ r) ≈ᶜ wkConₘ⁻¹ ρ γ ⊛ᶜ wkConₘ⁻¹ ρ δ ▷ r
wkConₘ⁻¹-⊛ᶜ                         id       = ≈ᶜ-refl
wkConₘ⁻¹-⊛ᶜ {γ = _ ∙ _} {δ = _ ∙ _} (step ρ) = wkConₘ⁻¹-⊛ᶜ ρ
wkConₘ⁻¹-⊛ᶜ {γ = _ ∙ _} {δ = _ ∙ _} (lift ρ) = wkConₘ⁻¹-⊛ᶜ ρ ∙ refl

-- The function wkConₘ⁻¹ ρ commutes with nrᶜ p r.

wkConₘ⁻¹-nrᶜ :
  ⦃ has-nr : Has-nr 𝕄 ⦄
  (ρ : Wk m n) →
  wkConₘ⁻¹ ρ (nrᶜ p r γ δ η) ≈ᶜ
  nrᶜ p r (wkConₘ⁻¹ ρ γ) (wkConₘ⁻¹ ρ δ) (wkConₘ⁻¹ ρ η)
wkConₘ⁻¹-nrᶜ id =
  ≈ᶜ-refl
wkConₘ⁻¹-nrᶜ {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} (step ρ) =
  wkConₘ⁻¹-nrᶜ ρ
wkConₘ⁻¹-nrᶜ {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} (lift ρ) =
  wkConₘ⁻¹-nrᶜ ρ ∙ refl

-- The function wkConₘ⁻¹ ρ commutes with nrᵢᶜ r.

wkConₘ⁻¹-nrᵢᶜ :
  ∀ i (ρ : Wk m n) →
  wkConₘ⁻¹ ρ (nrᵢᶜ r γ δ i) ≈ᶜ nrᵢᶜ r (wkConₘ⁻¹ ρ γ) (wkConₘ⁻¹ ρ δ) i
wkConₘ⁻¹-nrᵢᶜ _ id =
  ≈ᶜ-refl
wkConₘ⁻¹-nrᵢᶜ {γ = _ ∙ _} {δ = _ ∙ _} i (step ρ) =
  wkConₘ⁻¹-nrᵢᶜ i ρ
wkConₘ⁻¹-nrᵢᶜ {γ = _ ∙ _} {δ = _ ∙ _} i (lift ρ) =
  wkConₘ⁻¹-nrᵢᶜ i ρ ∙ refl

-- The function wkConₘ⁻¹ ρ "commutes" in a certain sense with _,_≔_.

wkConₘ⁻¹-,≔ :
  (ρ : Wk m n) → wkConₘ⁻¹ ρ (γ , wkVar ρ x ≔ p) ≈ᶜ wkConₘ⁻¹ ρ γ , x ≔ p
wkConₘ⁻¹-,≔                        id       = ≈ᶜ-refl
wkConₘ⁻¹-,≔ {γ = _ ∙ _}            (step ρ) = wkConₘ⁻¹-,≔ ρ
wkConₘ⁻¹-,≔ {γ = _ ∙ _} {x = x0}   (lift ρ) = ≈ᶜ-refl
wkConₘ⁻¹-,≔ {γ = _ ∙ _} {x = _ +1} (lift ρ) = wkConₘ⁻¹-,≔ ρ ∙ refl

opaque

  -- Inversion of weakening of greatest lower bounds

  wkConₘ⁻¹-GLBᶜ : ∀ {δ : Sequence (Conₘ m)}
                → (ρ : Wk m n)
                → Greatest-lower-boundᶜ γ (λ i → δ i)
                → Greatest-lower-boundᶜ (wkConₘ⁻¹ ρ γ) (λ i → wkConₘ⁻¹ ρ (δ i))
  wkConₘ⁻¹-GLBᶜ id γ≤ = γ≤
  wkConₘ⁻¹-GLBᶜ {γ = γ ∙ p} {δ} (step ρ) γ≤ =
    let γₜ-glb , γₕ-glb = GLBᶜ-pointwise γ≤
        γ≤′ , γ-glb = wkConₘ⁻¹-GLBᶜ ρ γₜ-glb
    in  (λ i → begin
           wkConₘ⁻¹ ρ γ                                  ≤⟨ γ≤′ i ⟩
           wkConₘ⁻¹ ρ (tailₘ (δ i))                      ≡⟨⟩
           wkConₘ⁻¹ (step ρ) (tailₘ (δ i) ∙ headₘ (δ i)) ≡⟨ cong (wkConₘ⁻¹ (step ρ)) (headₘ-tailₘ-correct (δ i)) ⟩
           wkConₘ⁻¹ (step ρ) (δ i)                       ∎) ,
        λ η η≤ → γ-glb η λ i → begin
            η                                             ≤⟨ η≤ i ⟩
            wkConₘ⁻¹ (step ρ) (δ i)                       ≡˘⟨ cong (wkConₘ⁻¹ (step ρ)) (headₘ-tailₘ-correct (δ i)) ⟩
            wkConₘ⁻¹ (step ρ) (tailₘ (δ i) ∙ headₘ (δ i)) ≡⟨⟩
            wkConₘ⁻¹ ρ (tailₘ (δ i))                      ∎
    where
    open ≤ᶜ-reasoning
  wkConₘ⁻¹-GLBᶜ {γ = γ ∙ p} {δ} (lift ρ) γ≤ =
   let γₜ-glb , γₕ-glb = GLBᶜ-pointwise γ≤
       γ≤′ , γ-glb = wkConₘ⁻¹-GLBᶜ ρ γₜ-glb
   in  (λ i → begin
          wkConₘ⁻¹ ρ γ ∙ p                              ≤⟨ γ≤′ i ∙ γₕ-glb .proj₁ i ⟩
          wkConₘ⁻¹ ρ (tailₘ (δ i)) ∙ headₘ (δ i)        ≡⟨⟩
          wkConₘ⁻¹ (lift ρ) (tailₘ (δ i) ∙ headₘ (δ i)) ≡⟨ cong (wkConₘ⁻¹ (lift ρ)) (headₘ-tailₘ-correct (δ i)) ⟩
          wkConₘ⁻¹ (lift ρ) (δ i)                       ∎) ,
       λ η η≤ →
         let η≤′ : ∀ i → η ≤ᶜ wkConₘ⁻¹ ρ (tailₘ (δ i)) ∙ headₘ (δ i)
             η≤′ i = begin
               η                                             ≤⟨ η≤ i ⟩
               wkConₘ⁻¹ (lift ρ) (δ i)                       ≡˘⟨ cong (wkConₘ⁻¹ (lift ρ)) (headₘ-tailₘ-correct (δ i)) ⟩
               wkConₘ⁻¹ (lift ρ) (tailₘ (δ i) ∙ headₘ (δ i)) ≡⟨⟩
               wkConₘ⁻¹ ρ (tailₘ (δ i)) ∙ headₘ (δ i)        ∎
         in  begin
           η                 ≡˘⟨ headₘ-tailₘ-correct η ⟩
           tailₘ η ∙ headₘ η ≤⟨ γ-glb (tailₘ η) (tailₘ-monotone ∘→ η≤′) ∙
                               γₕ-glb .proj₂ (headₘ η) (headₘ-monotone ∘→ η≤′) ⟩
           wkConₘ⁻¹ ρ γ ∙ p  ∎
   where
   open ≤ᶜ-reasoning

opaque

  -- The inverse weakening step corresponds to the tail of the context

  wkConₘ⁻¹-step : ∀ γ → wkConₘ⁻¹ (step ρ) γ ≈ᶜ wkConₘ⁻¹ ρ (tailₘ γ)
  wkConₘ⁻¹-step (γ ∙ p) = ≈ᶜ-refl

------------------------------------------------------------------------
-- Inversion properties for wkConₘ

-- An inversion lemma for wkConₘ and 𝟘ᶜ.

wkConₘ-𝟘 : wkConₘ ρ γ ≤ᶜ 𝟘ᶜ → γ ≤ᶜ 𝟘ᶜ
wkConₘ-𝟘 {ρ = ρ} {γ = γ} =
  wkConₘ ρ γ ≤ᶜ 𝟘ᶜ                          →⟨ wkConₘ⁻¹-monotone ρ ⟩
  wkConₘ⁻¹ ρ (wkConₘ ρ γ) ≤ᶜ wkConₘ⁻¹ ρ 𝟘ᶜ  →⟨ subst₂ _≤ᶜ_ (wkConₘ⁻¹-wkConₘ ρ) (≈ᶜ→≡ (wkConₘ⁻¹-𝟘ᶜ ρ)) ⟩
  γ ≤ᶜ 𝟘ᶜ                                   □

-- An inversion lemma for wkConₘ, wkVar and _,_≔_.

wkConₘ-,-wkVar-≔ :
  (x : Fin n) →
  wkConₘ ρ γ ≤ᶜ δ , wkVar ρ x ≔ p →
  ∃₂ λ δ′ p′ → γ ≤ᶜ δ′ , x ≔ p′ × wkConₘ ρ δ′ ≤ᶜ δ × p′ ≤ p
wkConₘ-,-wkVar-≔ {ρ = id} _ leq =
  _ , _ , leq , ≤ᶜ-refl , ≤-refl
wkConₘ-,-wkVar-≔ {ρ = step _} {δ = _ ∙ _} _ (leq₁ ∙ leq₂) =
  case wkConₘ-,-wkVar-≔ _ leq₁ of λ {
    (_ , _ , leq₁ , leq₃ , leq₄) →
  _ , _ , leq₁ , leq₃ ∙ leq₂ , leq₄ }
wkConₘ-,-wkVar-≔ {ρ = lift _} {γ = _ ∙ _} {δ = _ ∙ _} x0 (leq₁ ∙ leq₂) =
  _ ∙ _ , _ , ≤ᶜ-refl , leq₁ ∙ ≤-refl , leq₂
wkConₘ-,-wkVar-≔
  {ρ = lift ρ} {γ = _ ∙ _} {δ = _ ∙ _} (x +1) (leq₁ ∙ leq₂) =
  case wkConₘ-,-wkVar-≔ x leq₁ of λ {
    (_ , _ , leq₁ , leq₃ , leq₄) →
  _ ∙ _ , _ , leq₁ ∙ leq₂ , leq₃ ∙ ≤-refl , leq₄ }

-- The lemmas in the following anonymous module are defined under the
-- assumption that the zero is well-behaved.

module _
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero 𝕄 ⦄
  where

  -- An inversion lemma for wkConₘ and _+ᶜ_.

  wkConₘ-+ᶜ :
    ∀ ρ → wkConₘ ρ γ ≤ᶜ δ +ᶜ η →
    ∃₂ λ δ′ η′ → γ ≤ᶜ δ′ +ᶜ η′ × wkConₘ ρ δ′ ≤ᶜ δ × wkConₘ ρ η′ ≤ᶜ η
  wkConₘ-+ᶜ id leq =
    _ , _ , leq , ≤ᶜ-refl , ≤ᶜ-refl
  wkConₘ-+ᶜ {δ = _ ∙ _} {η = _ ∙ _} (step _) (leq₁ ∙ leq₂) =
    case wkConₘ-+ᶜ _ leq₁ of λ {
      (_ , _ , leq₁ , leq₃ , leq₄) →
    _ , _ , leq₁ ,
    leq₃ ∙ ≤-reflexive (PE.sym (+-positiveˡ (𝟘≮ leq₂))) ,
    leq₄ ∙ ≤-reflexive (PE.sym (+-positiveʳ (𝟘≮ leq₂))) }
  wkConₘ-+ᶜ
    {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} (lift ρ) (leq₁ ∙ leq₂) =
    case wkConₘ-+ᶜ ρ leq₁ of λ {
      (_ , _ , leq₁ , leq₃ , leq₄) →
    _ , _ , leq₁ ∙ leq₂ , leq₃ ∙ ≤-refl , leq₄ ∙ ≤-refl }

  -- An inversion lemma for wkConₘ and _∧ᶜ_.

  wkConₘ-∧ᶜ :
    ∀ ρ → wkConₘ ρ γ ≤ᶜ δ ∧ᶜ η →
    ∃₂ λ δ′ η′ → γ ≤ᶜ δ′ ∧ᶜ η′ × wkConₘ ρ δ′ ≤ᶜ δ × wkConₘ ρ η′ ≤ᶜ η
  wkConₘ-∧ᶜ id leq =
    _ , _ , leq , ≤ᶜ-refl , ≤ᶜ-refl
  wkConₘ-∧ᶜ {δ = _ ∙ _} {η = _ ∙ _} (step _) (leq₁ ∙ leq₂) =
    case wkConₘ-∧ᶜ _ leq₁ of λ {
      (_ , _ , leq₁ , leq₃ , leq₄) →
    _ , _ , leq₁ ,
    leq₃ ∙ ≤-reflexive (PE.sym (∧-positiveˡ (𝟘≮ leq₂))) ,
    leq₄ ∙ ≤-reflexive (PE.sym (∧-positiveʳ (𝟘≮ leq₂))) }
  wkConₘ-∧ᶜ
    {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} (lift ρ) (leq₁ ∙ leq₂) =
    case wkConₘ-∧ᶜ ρ leq₁ of λ {
      (_ , _ , leq₁ , leq₃ , leq₄) →
    _ , _ , leq₁ ∙ leq₂ , leq₃ ∙ ≤-refl , leq₄ ∙ ≤-refl }

  -- An inversion lemma for wkConₘ and _·ᶜ_.

  wkConₘ-·ᶜ :
    ∀ ρ → wkConₘ ρ γ ≤ᶜ p ·ᶜ δ →
    p ≡ 𝟘 × γ ≤ᶜ 𝟘ᶜ ⊎
    ∃ λ δ′ → γ ≤ᶜ p ·ᶜ δ′ × wkConₘ ρ δ′ ≤ᶜ δ
  wkConₘ-·ᶜ id leq =
    inj₂ (_ , leq , ≤ᶜ-refl)
  wkConₘ-·ᶜ {γ = γ} {δ = _ ∙ q} (step ρ) (leq₁ ∙ leq₂) =
    case wkConₘ-·ᶜ ρ leq₁ of λ where
      (inj₁ (refl , leq₁))      → inj₁ (refl , leq₁)
      (inj₂ (δ′ , leq₁ , leq₃)) →
        case zero-product (𝟘≮ leq₂) of λ where
          (inj₂ refl) → inj₂ (_ , leq₁ , leq₃ ∙ ≤-refl)
          (inj₁ refl) → inj₁
            ( refl
            , (begin
                 γ        ≤⟨ leq₁ ⟩
                 𝟘 ·ᶜ δ′  ≈⟨ ·ᶜ-zeroˡ _ ⟩
                 𝟘ᶜ       ∎)
            )
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset
  wkConₘ-·ᶜ {γ = γ ∙ q} {δ = _ ∙ r} (lift ρ) (leq₁ ∙ leq₂) =
    case wkConₘ-·ᶜ ρ leq₁ of λ where
      (inj₂ (_ , leq₁ , leq₃)) →
        inj₂ (_ , leq₁ ∙ leq₂ , leq₃ ∙ ≤-refl)
      (inj₁ (refl , leq₁)) → inj₁
        ( refl
        , (begin
             γ ∙ q       ≤⟨ leq₁ ∙ leq₂ ⟩
             𝟘ᶜ ∙ 𝟘 · r  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
             𝟘ᶜ          ∎)
        )
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

  -- An inversion lemma for wkConₘ and _⊛ᶜ_▷_.

  wkConₘ-⊛ᶜ :
    ⦃ has-star : Has-star 𝕄 ⦄ →
    ∀ ρ → wkConₘ ρ γ ≤ᶜ δ ⊛ᶜ η ▷ r →
    ∃₂ λ δ′ η′ → γ ≤ᶜ δ′ ⊛ᶜ η′ ▷ r × wkConₘ ρ δ′ ≤ᶜ δ × wkConₘ ρ η′ ≤ᶜ η
  wkConₘ-⊛ᶜ id leq =
    _ , _ , leq , ≤ᶜ-refl , ≤ᶜ-refl
  wkConₘ-⊛ᶜ {δ = _ ∙ _} {η = _ ∙ _} (step _) (leq₁ ∙ leq₂) =
    case wkConₘ-⊛ᶜ _ leq₁ of λ {
      (_ , _ , leq₁ , leq₃ , leq₄) →
    _ , _ , leq₁ ,
    leq₃ ∙ ≤-reflexive (PE.sym (⊛≡𝟘ˡ (𝟘≮ leq₂))) ,
    leq₄ ∙ ≤-reflexive (PE.sym (⊛≡𝟘ʳ (𝟘≮ leq₂))) }
  wkConₘ-⊛ᶜ
    {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} (lift ρ) (leq₁ ∙ leq₂) =
    case wkConₘ-⊛ᶜ ρ leq₁ of λ {
      (_ , _ , leq₁ , leq₃ , leq₄) →
    _ , _ , leq₁ ∙ leq₂ , leq₃ ∙ ≤-refl , leq₄ ∙ ≤-refl }

  -- An inversion lemma for wkConₘ and nrᶜ.

  wkConₘ-nrᶜ :
    ⦃ has-nr : Has-nr 𝕄 ⦄ →
    ∀ ρ → wkConₘ ρ γ ≤ᶜ nrᶜ p r δ η θ →
    ∃₃ λ δ′ η′ θ′ →
      γ ≤ᶜ nrᶜ p r δ′ η′ θ′ ×
      wkConₘ ρ δ′ ≤ᶜ δ × wkConₘ ρ η′ ≤ᶜ η × wkConₘ ρ θ′ ≤ᶜ θ
  wkConₘ-nrᶜ id leq =
    _ , _ , _ , leq , ≤ᶜ-refl , ≤ᶜ-refl , ≤ᶜ-refl
  wkConₘ-nrᶜ {δ = _ ∙ _} {η = η ∙ _} {θ = _ ∙ _}
    (step ρ) (leq₁ ∙ leq₂) =
    case wkConₘ-nrᶜ ρ leq₁ of λ where
      (_ , _ , _ , leq₁ , leq₃ , leq₄ , leq₅) →
        _ , _ , _ , leq₁ ,
        leq₃
          ∙
        ≤-reflexive (PE.sym $ nr-positive (𝟘≮ leq₂) .proj₁) ,
        leq₄
          ∙
        ≤-reflexive (PE.sym $ nr-positive (𝟘≮ leq₂) .proj₂ .proj₁) ,
        leq₅
          ∙
        ≤-reflexive (PE.sym $ nr-positive (𝟘≮ leq₂) .proj₂ .proj₂)
  wkConₘ-nrᶜ
    {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} {θ = _ ∙ _}
    (lift ρ) (leq₁ ∙ leq₂) =
    case wkConₘ-nrᶜ ρ leq₁ of λ where
      (_ , _ , _ , leq₁ , leq₃ , leq₄ , leq₅) →
        _ , _ , _ ,
        leq₁ ∙ leq₂ ,
        leq₃ ∙ ≤-refl ,
        leq₄ ∙ ≤-refl ,
        leq₅ ∙ ≤-refl
