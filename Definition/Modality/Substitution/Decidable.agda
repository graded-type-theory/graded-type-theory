------------------------------------------------------------------------
-- The usage relation can be decided (given certain assumptions)
------------------------------------------------------------------------

open import Definition.Modality
open import Tools.Nullary
open import Tools.PropositionalEquality
open import Tools.Relation

module Definition.Modality.Substitution.Decidable
  {a} {M : Set a} (𝕄 : Modality M)
  (open Modality 𝕄)
  -- Equality is assumed to be decidable for M.
  (_≟_ : Decidable (_≡_ {A = M}))
  -- The Prodrec relation is assumed to be decidable.
  (Prodrec? : ∀ r p q → Dec (Prodrec r p q))
  -- The Binder relation is assumed to be decidable.
  (Binder? : ∀ b p q → Dec (Binder b p q))
  where

open import Definition.Untyped M

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Substitution 𝕄
open import Definition.Modality.Substitution.Properties 𝕄
open import Definition.Modality.Context.Properties 𝕄
open import Definition.Modality.Properties 𝕄
open import Definition.Modality.Usage 𝕄
open import Definition.Modality.Usage.Decidable 𝕄 _≟_ Prodrec? Binder?
open import Definition.Modality.Usage.Properties 𝕄
open import Definition.Mode 𝕄

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
open import Tools.Sum

private
  variable
    m n : Nat
    mos : Mode-vector n

-- A given substitution is either well-resourced with respect to a
-- given mode vector and the substitution matrix computed by ∥_∥, or
-- it is not well-resourced with respect to any substitution matrix
-- (and the given mode).

∥∥▶?_ :
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
          ∥ tail σ ∥ (tailᵐ mos) *> 𝟘ᶜ                   ≈⟨ +ᶜ-congˡ (*>-zeroʳ (∥ tail σ ∥ _)) ⟩

          ⌜ headᵐ mos ⌝ ·ᶜ ⌈ head σ ⌉ (headᵐ mos) +ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityʳ _ ⟩

          ⌜ headᵐ mos ⌝ ·ᶜ ⌈ head σ ⌉ (headᵐ mos)        ≈⟨ ·-⌈⌉ (head σ) ⟩

          ⌈ head σ ⌉ (headᵐ mos)                         ∎)
        (x +1) → sub (▶tail-σ x) (begin
          𝟘 ·ᶜ ⌈ head σ ⌉ (headᵐ mos) +ᶜ
          ∥ tail σ ∥ (tailᵐ mos) *> (𝟘ᶜ , x ≔ ⌜ tailᵐ mos x ⌝)        ≈⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩

          𝟘ᶜ +ᶜ ∥ tail σ ∥ (tailᵐ mos) *> (𝟘ᶜ , x ≔ ⌜ tailᵐ mos x ⌝)  ≈⟨ +ᶜ-identityˡ _ ⟩

          ∥ tail σ ∥ (tailᵐ mos) *> (𝟘ᶜ , x ≔ ⌜ tailᵐ mos x ⌝)        ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

_eᵢ≤ᶜ?_eᵢ_ :
  (Ψ Ψ′ : Substₘ m n) (mos : Mode-vector n) →
  Dec (∀ x → Ψ *> (𝟘ᶜ , x ≔ ⌜ mos x ⌝) ≤ᶜ Ψ′ *> (𝟘ᶜ , x ≔ ⌜ mos x ⌝))
[] eᵢ≤ᶜ? [] eᵢ _ = yes λ ()
(Ψ ⊙ γ) eᵢ≤ᶜ? Ψ′ ⊙ δ eᵢ mos
  with Ψ eᵢ≤ᶜ? Ψ′ eᵢ tailᵐ mos
     | ≤ᶜ-decidable (≈-decidable→≤-decidable _≟_)
         (⌜ headᵐ mos ⌝ ·ᶜ γ) (⌜ headᵐ mos ⌝ ·ᶜ δ)
... | _ | no γ≰δ = no λ P → γ≰δ (begin
  ⌜ headᵐ mos ⌝ ·ᶜ γ              ≈˘⟨ +ᶜ-identityʳ _ ⟩
  ⌜ headᵐ mos ⌝ ·ᶜ γ +ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-congˡ (*>-zeroʳ Ψ) ⟩
  ⌜ headᵐ mos ⌝ ·ᶜ γ +ᶜ Ψ *> 𝟘ᶜ   ≤⟨ P x0 ⟩
  ⌜ headᵐ mos ⌝ ·ᶜ δ +ᶜ Ψ′ *> 𝟘ᶜ  ≈⟨ +ᶜ-congˡ (*>-zeroʳ Ψ′) ⟩
  ⌜ headᵐ mos ⌝ ·ᶜ δ +ᶜ 𝟘ᶜ        ≈⟨ +ᶜ-identityʳ _ ⟩
  ⌜ headᵐ mos ⌝ ·ᶜ δ              ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
... | no Ψ≰Ψ′ | _ = no λ P → Ψ≰Ψ′ λ x → begin
  Ψ *> (𝟘ᶜ , x ≔ ⌜ tailᵐ mos x ⌝)             ≈˘⟨ +ᶜ-identityˡ _ ⟩
  𝟘ᶜ +ᶜ Ψ *> (𝟘ᶜ , x ≔ ⌜ tailᵐ mos x ⌝)       ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
  (Ψ ⊙ γ) *> (𝟘ᶜ , x +1 ≔ ⌜ tailᵐ mos x ⌝)    ≤⟨ P (x +1) ⟩
  𝟘 ·ᶜ δ +ᶜ Ψ′ *> (𝟘ᶜ , x ≔ ⌜ tailᵐ mos x ⌝)  ≈⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
  𝟘ᶜ +ᶜ Ψ′ *> (𝟘ᶜ , x ≔ ⌜ tailᵐ mos x ⌝)      ≈⟨ +ᶜ-identityˡ _ ⟩
  Ψ′ *> (𝟘ᶜ , x ≔ ⌜ tailᵐ mos x ⌝)            ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
... | yes Ψ≤Ψ′ | yes γ≤δ = yes λ where
    x0 → begin
      ⌜ headᵐ mos ⌝ ·ᶜ γ +ᶜ Ψ *> 𝟘ᶜ   ≈⟨ +ᶜ-congˡ (*>-zeroʳ Ψ) ⟩
      ⌜ headᵐ mos ⌝ ·ᶜ γ +ᶜ 𝟘ᶜ        ≈⟨ +ᶜ-identityʳ _ ⟩
      ⌜ headᵐ mos ⌝ ·ᶜ γ              ≤⟨ γ≤δ ⟩
      ⌜ headᵐ mos ⌝ ·ᶜ δ              ≈˘⟨ +ᶜ-identityʳ _ ⟩
      ⌜ headᵐ mos ⌝ ·ᶜ δ +ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-congˡ (*>-zeroʳ Ψ′) ⟩
      ⌜ headᵐ mos ⌝ ·ᶜ δ +ᶜ Ψ′ *> 𝟘ᶜ  ∎
    (x +1) → begin
      𝟘 ·ᶜ γ +ᶜ Ψ *> (𝟘ᶜ , x ≔ ⌜ tailᵐ mos x ⌝)   ≈⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
      𝟘ᶜ +ᶜ Ψ *> (𝟘ᶜ , x ≔ ⌜ tailᵐ mos x ⌝)       ≈⟨ +ᶜ-identityˡ _ ⟩
      Ψ *> (𝟘ᶜ , x ≔ ⌜ tailᵐ mos x ⌝)             ≤⟨ Ψ≤Ψ′ x ⟩
      Ψ′ *> (𝟘ᶜ , x ≔ ⌜ tailᵐ mos x ⌝)            ≈˘⟨ +ᶜ-identityˡ _ ⟩
      𝟘ᶜ +ᶜ Ψ′ *> (𝟘ᶜ , x ≔ ⌜ tailᵐ mos x ⌝)      ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
      𝟘 ·ᶜ δ +ᶜ Ψ′ *> (𝟘ᶜ , x ≔ ⌜ tailᵐ mos x ⌝)  ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

_▶?_ : (Ψ : Substₘ m n) (σ : Subst m n) → Dec (Ψ ▶[ mos ] σ)
_▶?_ {mos = mos} Ψ σ = case ∥∥▶? σ of λ where
    (inj₂ ¬▶σ) → no (¬▶σ Ψ)
    (inj₁ ▶σ)  → case Ψ eᵢ≤ᶜ? ∥ σ ∥ mos eᵢ mos of λ where
      (yes Ψ≤∥σ∥) → yes (λ x → sub (▶σ x) (Ψ≤∥σ∥ x))
      (no Ψ≰∥σ∥)  → no λ Ψ▶σ → Ψ≰∥σ∥ λ x → begin
        Ψ *> (𝟘ᶜ , x ≔ ⌜ mos x ⌝)          ≤⟨ substₘ-calc-upper-bound σ _ (Ψ▶σ x) ⟩
        ∥ σ ∥ mos *> (𝟘ᶜ , x ≔ 𝟙)          ≈⟨ ∥∥-*>-𝟘ᶜ,≔𝟙 σ ⟩
        ∥ σ ∥ mos *> (𝟘ᶜ , x ≔ ⌜ mos x ⌝)  ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
