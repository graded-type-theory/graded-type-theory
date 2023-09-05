------------------------------------------------------------------------
-- The usage relation for substitutions can be decided
-- (given certain assumptions)
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Tools.Nullary
open import Tools.PropositionalEquality
open import Tools.Relation

module Graded.Substitution.Decidable
  {a} {M : Set a}
  (𝕄 : Modality M)
  (R : Usage-restrictions M)
  (open Usage-restrictions R)
  -- Equality is assumed to be decidable for M.
  (_≟_ : Decidable (_≡_ {A = M}))
  -- The Prodrec-allowed relation is assumed to be decidable.
  (Prodrec? : ∀ r p q → Dec (Prodrec-allowed r p q))
  where

open Modality 𝕄

open import Definition.Untyped M

open import Graded.Context 𝕄
open import Graded.Substitution 𝕄 R
open import Graded.Substitution.Properties 𝕄 R
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Dedicated-nr 𝕄
open import Graded.Modality.Dedicated-nr.Instance
open import Graded.Modality.Properties 𝕄
open import Graded.Usage 𝕄 R
open import Graded.Usage.Decidable 𝕄 R _≟_ Prodrec?
open import Graded.Usage.Properties 𝕄 R
open import Graded.Mode 𝕄

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
open import Tools.Sum

private
  variable
    m n : Nat
    mos : Mode-vector n

-- If there is a dedicated nr function, then a given substitution is
-- either well-resourced with respect to a given mode vector and the
-- substitution matrix computed by ∥_∥, or it is not well-resourced
-- with respect to any substitution matrix (and the given mode).

∥∥▶?_ :
  ⦃ has-nr : Dedicated-nr ⦄ →
  (σ : Subst m n) →
  (∥ σ ∥ mos ▶[ mos ] σ) ⊎ (∀ Ψ → ¬ Ψ ▶[ mos ] σ)
∥∥▶?_ {n = 0}                _ = inj₁ (λ ())
∥∥▶?_ {n = 1+ _} {mos = mos} σ =
  case ⌈⌉▸[ headᵐ mos ]? (head σ) of λ where
    (inj₂ ¬▸head-σ) → inj₂ λ where
      _ ▶σ → ¬▸head-σ _ (▶σ x0)
    (inj₁ ▸head-σ) → case ∥∥▶? tail σ of λ where
      (inj₂ ¬▶tail-σ) → inj₂ λ where
        (Ψ ⊙ _) ▶σ → ¬▶tail-σ Ψ (wf-tailSubstₘ ▶σ)
      (inj₁ ▶tail-σ) → inj₁ λ where
        x0 → sub ▸head-σ (begin
          ⌜ headᵐ mos ⌝ ·ᶜ ⌈ head σ ⌉ (headᵐ mos) +ᶜ
          𝟘ᶜ <* ∥ tail σ ∥ (tailᵐ mos)                   ≈⟨ +ᶜ-congˡ (<*-zeroˡ (∥ tail σ ∥ _)) ⟩

          ⌜ headᵐ mos ⌝ ·ᶜ ⌈ head σ ⌉ (headᵐ mos) +ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityʳ _ ⟩

          ⌜ headᵐ mos ⌝ ·ᶜ ⌈ head σ ⌉ (headᵐ mos)        ≈⟨ ·-⌈⌉ (head σ) ⟩

          ⌈ head σ ⌉ (headᵐ mos)                         ∎)
        (x +1) → sub (▶tail-σ x) (begin
          𝟘 ·ᶜ ⌈ head σ ⌉ (headᵐ mos) +ᶜ
          (𝟘ᶜ , x ≔ ⌜ tailᵐ mos x ⌝) <* ∥ tail σ ∥ (tailᵐ mos)         ≈⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩

          𝟘ᶜ +ᶜ (𝟘ᶜ , x ≔ ⌜ tailᵐ mos x ⌝) <* ∥ tail σ ∥ (tailᵐ mos)  ≈⟨ +ᶜ-identityˡ _ ⟩

          (𝟘ᶜ , x ≔ ⌜ tailᵐ mos x ⌝) <* ∥ tail σ ∥ (tailᵐ mos)        ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

_eᵢ≤ᶜ?_eᵢ_ :
  (Ψ Ψ′ : Substₘ m n) (mos : Mode-vector n) →
  Dec (∀ x → (𝟘ᶜ , x ≔ ⌜ mos x ⌝) <* Ψ ≤ᶜ (𝟘ᶜ , x ≔ ⌜ mos x ⌝) <* Ψ′)
[] eᵢ≤ᶜ? [] eᵢ _ = yes λ ()
(Ψ ⊙ γ) eᵢ≤ᶜ? Ψ′ ⊙ δ eᵢ mos
  with Ψ eᵢ≤ᶜ? Ψ′ eᵢ tailᵐ mos
     | ≤ᶜ-decidable (≡-decidable→≤-decidable _≟_)
         (⌜ headᵐ mos ⌝ ·ᶜ γ) (⌜ headᵐ mos ⌝ ·ᶜ δ)
... | _ | no γ≰δ = no λ P → γ≰δ (begin
  ⌜ headᵐ mos ⌝ ·ᶜ γ              ≈˘⟨ +ᶜ-identityʳ _ ⟩
  ⌜ headᵐ mos ⌝ ·ᶜ γ +ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-congˡ (<*-zeroˡ Ψ) ⟩
  ⌜ headᵐ mos ⌝ ·ᶜ γ +ᶜ 𝟘ᶜ <* Ψ   ≤⟨ P x0 ⟩
  ⌜ headᵐ mos ⌝ ·ᶜ δ +ᶜ 𝟘ᶜ <* Ψ′  ≈⟨ +ᶜ-congˡ (<*-zeroˡ Ψ′) ⟩
  ⌜ headᵐ mos ⌝ ·ᶜ δ +ᶜ 𝟘ᶜ        ≈⟨ +ᶜ-identityʳ _ ⟩
  ⌜ headᵐ mos ⌝ ·ᶜ δ              ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
... | no Ψ≰Ψ′ | _ = no λ P → Ψ≰Ψ′ λ x → begin
  (𝟘ᶜ , x ≔ ⌜ tailᵐ mos x ⌝) <* Ψ             ≈˘⟨ +ᶜ-identityˡ _ ⟩
  𝟘ᶜ +ᶜ (𝟘ᶜ , x ≔ ⌜ tailᵐ mos x ⌝) <* Ψ       ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
  (𝟘ᶜ , x +1 ≔ ⌜ tailᵐ mos x ⌝) <* (Ψ ⊙ γ)    ≤⟨ P (x +1) ⟩
  𝟘 ·ᶜ δ +ᶜ (𝟘ᶜ , x ≔ ⌜ tailᵐ mos x ⌝) <* Ψ′  ≈⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
  𝟘ᶜ +ᶜ (𝟘ᶜ , x ≔ ⌜ tailᵐ mos x ⌝) <* Ψ′      ≈⟨ +ᶜ-identityˡ _ ⟩
  (𝟘ᶜ , x ≔ ⌜ tailᵐ mos x ⌝) <* Ψ′            ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
... | yes Ψ≤Ψ′ | yes γ≤δ = yes λ where
    x0 → begin
      ⌜ headᵐ mos ⌝ ·ᶜ γ +ᶜ 𝟘ᶜ <* Ψ   ≈⟨ +ᶜ-congˡ (<*-zeroˡ Ψ) ⟩
      ⌜ headᵐ mos ⌝ ·ᶜ γ +ᶜ 𝟘ᶜ        ≈⟨ +ᶜ-identityʳ _ ⟩
      ⌜ headᵐ mos ⌝ ·ᶜ γ              ≤⟨ γ≤δ ⟩
      ⌜ headᵐ mos ⌝ ·ᶜ δ              ≈˘⟨ +ᶜ-identityʳ _ ⟩
      ⌜ headᵐ mos ⌝ ·ᶜ δ +ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-congˡ (<*-zeroˡ Ψ′) ⟩
      ⌜ headᵐ mos ⌝ ·ᶜ δ +ᶜ 𝟘ᶜ <* Ψ′  ∎
    (x +1) → begin
      𝟘 ·ᶜ γ +ᶜ (𝟘ᶜ , x ≔ ⌜ tailᵐ mos x ⌝) <* Ψ   ≈⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
      𝟘ᶜ +ᶜ (𝟘ᶜ , x ≔ ⌜ tailᵐ mos x ⌝) <* Ψ       ≈⟨ +ᶜ-identityˡ _ ⟩
      (𝟘ᶜ , x ≔ ⌜ tailᵐ mos x ⌝) <* Ψ             ≤⟨ Ψ≤Ψ′ x ⟩
      (𝟘ᶜ , x ≔ ⌜ tailᵐ mos x ⌝) <* Ψ′            ≈˘⟨ +ᶜ-identityˡ _ ⟩
      𝟘ᶜ +ᶜ (𝟘ᶜ , x ≔ ⌜ tailᵐ mos x ⌝) <* Ψ′      ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
      𝟘 ·ᶜ δ +ᶜ (𝟘ᶜ , x ≔ ⌜ tailᵐ mos x ⌝) <* Ψ′  ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

_▶?_ :
  ⦃ has-nr : Dedicated-nr ⦄ →
  (Ψ : Substₘ m n) (σ : Subst m n) → Dec (Ψ ▶[ mos ] σ)
_▶?_ {mos = mos} Ψ σ = case ∥∥▶? σ of λ where
    (inj₂ ¬▶σ) → no (¬▶σ Ψ)
    (inj₁ ▶σ)  → case Ψ eᵢ≤ᶜ? ∥ σ ∥ mos eᵢ mos of λ where
      (yes Ψ≤∥σ∥) → yes (λ x → sub (▶σ x) (Ψ≤∥σ∥ x))
      (no Ψ≰∥σ∥)  → no λ Ψ▶σ → Ψ≰∥σ∥ λ x → begin
        (𝟘ᶜ , x ≔ ⌜ mos x ⌝) <* Ψ          ≤⟨ substₘ-calc-upper-bound σ _ (Ψ▶σ x) ⟩
        (𝟘ᶜ , x ≔ 𝟙) <* ∥ σ ∥ mos          ≈⟨ ∥∥-*>-𝟘ᶜ,≔𝟙 σ ⟩
        (𝟘ᶜ , x ≔ ⌜ mos x ⌝) <* ∥ σ ∥ mos  ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
