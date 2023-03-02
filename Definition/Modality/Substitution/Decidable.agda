{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- The usage relation can be decided (given certain assumptions)
------------------------------------------------------------------------

open import Definition.Modality
open import Tools.Nullary
open import Tools.Relation

module Definition.Modality.Substitution.Decidable
  {a ℓ} {M′ : Setoid a ℓ} (𝕄 : Modality M′)
  (open Setoid M′ renaming (Carrier to M)) (open Modality 𝕄)
  -- Equality is assumed to be decidable for M.
  (_≟_ : Decidable (_≈_))
  -- The Prodrec relation is assumed to be decidable.
  (Prodrec? : ∀ p → Dec (Prodrec p))
  where

open import Definition.Untyped M

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Substitution 𝕄
open import Definition.Modality.Substitution.Properties 𝕄
open import Definition.Modality.Context.Properties 𝕄
open import Definition.Modality.Usage 𝕄
open import Definition.Modality.Usage.Decidable 𝕄 _≟_ Prodrec?

open import Tools.Fin
open import Tools.Nat hiding (_≟_)
import Tools.PropositionalEquality as PE

private
  variable
    m n : Nat

∥∥▶?_ : (σ : Subst m n) → Dec (∥ σ ∥ ▶ σ)
∥∥▶?_ {n = 0}    σ = yes λ ()
∥∥▶?_ {n = 1+ n} σ with ∥∥▶? (tail σ)
... | no ¬σ′ = no λ ▶σ →
  ¬σ′ (λ x → sub (▶σ (x +1))
                 (≤ᶜ-reflexive (≈ᶜ-sym (≈ᶜ-trans (+ᶜ-congʳ (·ᶜ-zeroˡ ⌈ σ x0 ⌉))
                                                 (+ᶜ-identityˡ _)))))
... | yes ▶σ′ with ⌈⌉▸? (σ x0)
... | no ¬t = no λ ▶σ →
  ¬t (sub (▶σ x0)
          (≤ᶜ-reflexive (≈ᶜ-sym (≈ᶜ-trans (+ᶜ-cong (·ᶜ-identityˡ ⌈ σ x0 ⌉) (*>-zeroʳ ∥ tail σ ∥))
                                          (+ᶜ-identityʳ ⌈ σ x0 ⌉)))))
... | yes ▸t =
  yes λ { x0    → sub ▸t (≤ᶜ-reflexive (≈ᶜ-trans (+ᶜ-cong (·ᶜ-identityˡ ⌈ σ x0 ⌉) (*>-zeroʳ ∥ tail σ ∥))
                                                 (+ᶜ-identityʳ ⌈ σ x0 ⌉)))
        ;(x +1) → sub (▶σ′ x) (≤ᶜ-reflexive (≈ᶜ-trans (+ᶜ-congʳ (·ᶜ-zeroˡ ⌈ σ x0 ⌉))
                                                      (+ᶜ-identityˡ _)))}

_eᵢ≤ᶜ?_eᵢ : (Ψ Ψ′ : Substₘ m n) → Dec (∀ x → Ψ *> (𝟘ᶜ , x ≔ 𝟙) ≤ᶜ Ψ′ *> (𝟘ᶜ , x ≔ 𝟙))
[] eᵢ≤ᶜ? [] eᵢ = yes λ ()
(Ψ ⊙ γ) eᵢ≤ᶜ? Ψ′ ⊙ δ eᵢ with Ψ eᵢ≤ᶜ? Ψ′ eᵢ | γ ≤ᶜ? δ
... | _ | no γ≰δ = no λ P →
  γ≰δ (≤ᶜ-trans (≤ᶜ-reflexive (≈ᶜ-sym (≈ᶜ-trans (+ᶜ-cong (·ᶜ-identityˡ γ) (*>-zeroʳ Ψ))
                                                         (+ᶜ-identityʳ γ))))
      (≤ᶜ-trans (P x0)
      (≤ᶜ-reflexive (≈ᶜ-trans (+ᶜ-cong (·ᶜ-identityˡ δ) (*>-zeroʳ Ψ′))
                              (+ᶜ-identityʳ δ)))))
... | no Ψ≰Ψ′ | _ = no λ P →
  Ψ≰Ψ′ (λ x → ≤ᶜ-trans (≤ᶜ-reflexive (≈ᶜ-sym (≈ᶜ-trans (+ᶜ-congʳ (·ᶜ-zeroˡ γ))
                                                       (+ᶜ-identityˡ _))))
             (≤ᶜ-trans (P (x +1))
             (≤ᶜ-reflexive (≈ᶜ-trans (+ᶜ-congʳ (·ᶜ-zeroˡ δ)) (
                                     +ᶜ-identityˡ _)))))
... | yes Ψ≤Ψ′ | yes γ≤δ =
  yes λ {x0     → ≤ᶜ-trans (≤ᶜ-reflexive (≈ᶜ-trans (+ᶜ-cong (·ᶜ-identityˡ γ) (*>-zeroʳ Ψ))
                                                   (+ᶜ-identityʳ γ)))
                  (≤ᶜ-trans γ≤δ
                  (≤ᶜ-reflexive (≈ᶜ-sym (≈ᶜ-trans (+ᶜ-cong (·ᶜ-identityˡ δ) (*>-zeroʳ Ψ′))
                                                  (+ᶜ-identityʳ δ)))))
        ;(x +1) → ≤ᶜ-trans (≤ᶜ-reflexive (≈ᶜ-trans (+ᶜ-congʳ (·ᶜ-zeroˡ γ)) (+ᶜ-identityˡ _)))
                  (≤ᶜ-trans (Ψ≤Ψ′ x)
                  (≤ᶜ-reflexive (≈ᶜ-sym (≈ᶜ-trans (+ᶜ-congʳ (·ᶜ-zeroˡ δ))
                                                  (+ᶜ-identityˡ _)))))}

_▶?_ : (Ψ : Substₘ m n) (σ : Subst m n) → Dec (Ψ ▶ σ)
Ψ ▶? σ with ∥∥▶? σ
... | no ¬σ = no (λ Ψ▶σ → ¬σ (subst-calc-correct′ {Ψ = Ψ} Ψ▶σ))
... | yes ▶σ with Ψ eᵢ≤ᶜ? ∥ σ ∥ eᵢ
... | no Ψ≰∥σ∥ = no (λ Ψ▶σ → Ψ≰∥σ∥ (λ x → substₘ-calc-upper-bound σ x (Ψ▶σ x)))
... | yes Ψ≤∥σ∥ = yes (λ x → sub (▶σ x) (Ψ≤∥σ∥ x))
