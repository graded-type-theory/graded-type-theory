------------------------------------------------------------------------
-- Properties of context updates.
------------------------------------------------------------------------

import Graded.Modality

module Graded.Context.Properties.Update
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  where

open import Graded.Context 𝕄
open import Graded.Context.Properties.Equivalence 𝕄
open import Graded.Context.Properties.Lookup 𝕄
open import Graded.Context.Properties.Natrec 𝕄
open import Graded.Context.Properties.PartialOrder 𝕄
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄

open import Tools.Fin
open import Tools.Nat using (Nat; 1+)
open import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

open Modality 𝕄

private
  variable
    n i : Nat
    p q r : M
    γ δ : Conₘ n
    x : Fin n

-- Updating a context with its own content has no effect
-- (γ , x ≔ (γ ⟨ x ⟩)) ≡ γ

update-self : (γ : Conₘ n) (x : Fin n) → (γ , x ≔ (γ ⟨ x ⟩)) ≡ γ
update-self ε       ()
update-self (γ ∙ p) x0     = PE.refl
update-self (γ ∙ p) (x +1) = cong (_∙ _) (update-self γ x)

-- Updating a value in 𝟘ᶜ with 𝟘 has no effect.

𝟘ᶜ,≔𝟘 : 𝟘ᶜ , x ≔ 𝟘 ≡ 𝟘ᶜ
𝟘ᶜ,≔𝟘 {x = x} = begin
  𝟘ᶜ , x ≔ 𝟘         ≡˘⟨ cong (λ p → 𝟘ᶜ , _ ≔ p) (𝟘ᶜ-lookup x) ⟩
  𝟘ᶜ , x ≔ 𝟘ᶜ ⟨ x ⟩  ≡⟨ update-self _ _ ⟩
  𝟘ᶜ                 ∎
  where
  open Tools.Reasoning.PropositionalEquality

-- Updating a value in 𝟙ᶜ with 𝟙 has no effect.

𝟙ᶜ,≔𝟙 : 𝟙ᶜ , x ≔ 𝟙 ≡ 𝟙ᶜ
𝟙ᶜ,≔𝟙 {x = x} = begin
  𝟙ᶜ , x ≔ 𝟙         ≡˘⟨ cong (λ p → 𝟙ᶜ , _ ≔ p) (𝟙ᶜ-lookup x) ⟩
  𝟙ᶜ , x ≔ 𝟙ᶜ ⟨ x ⟩  ≡⟨ update-self _ _ ⟩
  𝟙ᶜ                 ∎
  where
  open Tools.Reasoning.PropositionalEquality

-- If a given position is updated twice, then the first update has no
-- effect.

update-twice : (γ , x ≔ p) , x ≔ q ≡ γ , x ≔ q
update-twice {γ = ε}     {x = ()}
update-twice {γ = _ ∙ _} {x = x0}   = PE.refl
update-twice {γ = _ ∙ _} {x = x +1} = cong (_∙ _) update-twice

-- Context update is a monotone function with regards to the context
-- If γ ≤ᶜ δ then (γ , x ≔ p) ≤ᶜ (δ , x ≔ p)

update-monotoneˡ : (x : Fin n) → γ ≤ᶜ δ → (γ , x ≔ p) ≤ᶜ (δ , x ≔ p)
update-monotoneˡ {γ = ε}             ()
update-monotoneˡ {γ = γ ∙ p} {δ ∙ q} x0 (γ≤δ ∙ _)        = γ≤δ ∙ ≤-refl
update-monotoneˡ {γ = γ ∙ p} {δ ∙ q} (_+1 x) (γ≤δ ∙ p≤q) = (update-monotoneˡ x γ≤δ) ∙ p≤q

-- Context update is monotone with regards to the inserted element
-- If p ≤ q then( γ , x ≔ p) ≤ᶜ (γ , x ≔ q)

update-monotoneʳ : (x : Fin n) → p ≤ q → (γ , x ≔ p) ≤ᶜ (γ , x ≔ q)
update-monotoneʳ {γ = ε}     ()
update-monotoneʳ {γ = γ ∙ p} x0 p≤q     = ≤ᶜ-refl ∙ p≤q
update-monotoneʳ {γ = γ ∙ p} (x +1) p≤q = (update-monotoneʳ x p≤q) ∙ ≤-refl

-- Context update is monotone.

update-monotone :
  (x : Fin n) → γ ≤ᶜ δ → p ≤ q → (γ , x ≔ p) ≤ᶜ (δ , x ≔ q)
update-monotone {γ = γ} {δ = δ} {p = p} {q = q} x γ≤δ p≤q = begin
  γ , x ≔ p  ≤⟨ update-monotoneˡ _ γ≤δ ⟩
  δ , x ≔ p  ≤⟨ update-monotoneʳ _ p≤q ⟩
  δ , x ≔ q  ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- The update operation preserves equivalence in its first argument.

update-congˡ : γ ≈ᶜ δ → (γ , x ≔ p) ≈ᶜ (δ , x ≔ p)
update-congˡ γ≈ᶜδ =
  ≤ᶜ-antisym (update-monotoneˡ _ (≤ᶜ-reflexive γ≈ᶜδ))
    (update-monotoneˡ _ (≤ᶜ-reflexive (≈ᶜ-sym γ≈ᶜδ)))

-- The update operation preserves equivalence in its third argument.

update-congʳ : p ≡ q → (γ , x ≔ p) ≈ᶜ (γ , x ≔ q)
update-congʳ p≡q =
  ≤ᶜ-antisym (update-monotoneʳ _ (≤-reflexive p≡q))
    (update-monotoneʳ _ (≤-reflexive (sym p≡q)))

-- The update operation preserves equivalence in its first and third
-- arguments.

update-cong : γ ≈ᶜ δ → p ≡ q → (γ , x ≔ p) ≈ᶜ (δ , x ≔ q)
update-cong γ≈ᶜδ p≡q =
  ≈ᶜ-trans (update-congˡ γ≈ᶜδ) (update-congʳ p≡q)

-- Context update distributes over addition
-- (γ +ᶜ δ) , x ≔ (p + q) ≡ (γ , x ≔ p) +ᶜ (δ , x ≔ q)

update-distrib-+ᶜ : (γ δ : Conₘ n) (p q : M) (x : Fin n)
                  → (γ +ᶜ δ) , x ≔ (p + q) ≡ (γ , x ≔ p) +ᶜ (δ , x ≔ q)
update-distrib-+ᶜ ε        _        _ _ ()
update-distrib-+ᶜ (γ ∙ p′) (δ ∙ q′) p q x0     = PE.refl
update-distrib-+ᶜ (γ ∙ p′) (δ ∙ q′) p q (x +1) = cong (_∙ _) (update-distrib-+ᶜ γ δ p q x)

-- Context update distributes over multiplication
-- (p ·ᶜ γ) , x ≔ (p · q) ≡ p ·ᶜ (γ , x ≔ q)

update-distrib-·ᶜ : (γ : Conₘ n) (p q : M) (x : Fin n)
                  → (p ·ᶜ γ) , x ≔ (p · q) ≡ p ·ᶜ (γ , x ≔ q)
update-distrib-·ᶜ ε       _ _ ()
update-distrib-·ᶜ (γ ∙ r) p q x0     = PE.refl
update-distrib-·ᶜ (γ ∙ r) p q (x +1) = cong (_∙ _) (update-distrib-·ᶜ γ p q x)

-- Context update distributes over meet
-- (γ ∧ᶜ δ) , x ≔ (p ∧ q) ≡ (γ , x ≔ p) ∧ᶜ (δ , x ≔ q)

update-distrib-∧ᶜ : (γ δ : Conₘ n) (p q : M) (x : Fin n)
                  → (γ ∧ᶜ δ) , x ≔ (p ∧ q) ≡ (γ , x ≔ p) ∧ᶜ (δ , x ≔ q)
update-distrib-∧ᶜ ε        _        _ _ ()
update-distrib-∧ᶜ (γ ∙ p′) (δ ∙ q′) p q x0 = PE.refl
update-distrib-∧ᶜ (γ ∙ p′) (δ ∙ q′) p q (x +1) = cong (_∙ _) (update-distrib-∧ᶜ γ δ p q x)

-- Context update distributes over ⊛ᶜ
-- γ ⊛ᶜ δ ▷ r , x ≔ p ⊛ q ▷ r ≡ (γ , x ≔ p) ⊛ᶜ (δ , x ≔ q) ▷ r

update-distrib-⊛ᶜ :
  ⦃ has-star : Has-star semiring-with-meet ⦄ →
  (γ δ : Conₘ n) (r p q : M) (x : Fin n) →
  γ ⊛ᶜ δ ▷ r , x ≔ (p ⊛ q ▷ r) ≡ (γ , x ≔ p) ⊛ᶜ (δ , x ≔ q) ▷ r
update-distrib-⊛ᶜ ε       _       _ _ _ ()
update-distrib-⊛ᶜ (γ ∙ _) (δ ∙ _) r p q x0 = PE.refl
update-distrib-⊛ᶜ (γ ∙ _) (δ ∙ _) r p q (x +1) =
  cong (_∙ _) (update-distrib-⊛ᶜ γ δ r p q x)

opaque

  -- Context update distributes over nrᵢᶜ

  update-distrib-nrᵢᶜ :
    ∀ x → nrᵢᶜ r γ δ i , x ≔ nrᵢ r p q i ≈ᶜ nrᵢᶜ r (γ , x ≔ p) (δ , x ≔ q) i
  update-distrib-nrᵢᶜ {γ = ε} {(ε)} ()
  update-distrib-nrᵢᶜ {γ = _ ∙ _} {_ ∙ _} x0 = ≈ᶜ-refl
  update-distrib-nrᵢᶜ {γ = _ ∙ _} {(_ ∙ _)} (x +1) =
    update-distrib-nrᵢᶜ x ∙ refl

-- Updating the head of a context leaves the tail untouched
-- γ , x0 ≔ p ≡ tailₘ γ ∙ p

update-head : (γ : Conₘ (1+ n)) (p : M) → γ , x0 ≔ p ≡ tailₘ γ ∙ p
update-head (γ ∙ q) p = PE.refl

-- Updating the tail of a context leaves the head untouched
-- γ , (x +1) ≔ p ≡ (tailₘ γ , x ≔ p) ∙ headₘ γ

update-step : (γ : Conₘ (1+ n)) (p : M) (x : Fin n)
            → γ , (x +1) ≔ p ≡ (tailₘ γ , x ≔ p) ∙ headₘ γ
update-step (γ ∙ q) p x = PE.refl

opaque

  -- Looking up x0 is the same as headₘ.

  headₘ-⟨⟩ : (γ : Conₘ (1+ n)) → γ ⟨ x0 ⟩ ≡ headₘ γ
  headₘ-⟨⟩ (γ ∙ p) = refl

opaque

  -- Looking up x +1 in γ is the same as looking up
  -- x in tailₘ γ.

  tailₘ-⟨⟩ : (γ : Conₘ (1+ n)) → γ ⟨ x +1 ⟩ ≡ tailₘ γ ⟨ x ⟩
  tailₘ-⟨⟩ (γ ∙ p) = refl
