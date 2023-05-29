------------------------------------------------------------------------
-- Properties of the erasure modality.
------------------------------------------------------------------------

open import Definition.Modality.Instances.Erasure
open import Definition.Mode.Restrictions

module Definition.Modality.Instances.Erasure.Properties
  (mrs : Mode-restrictions)
  where

open Mode-restrictions mrs

open import Definition.Modality.Instances.Erasure.Modality mrs

open import Definition.Modality.Context ErasureModality
open import Definition.Modality.Context.Properties ErasureModality public

open import Definition.Modality.FullReduction.Assumptions

open import Definition.Modality.Properties ErasureModality public

open import Definition.Modality.Usage ErasureModality
open import Definition.Modality.Usage.Inversion ErasureModality
open import Definition.Mode ErasureModality

open import Definition.Typed.Restrictions Erasure

open import Definition.Untyped Erasure

open import Tools.Bool
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat hiding (_+_)
open import Tools.Nullary
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≡_; _≢_)
import Tools.Reasoning.PartialOrder
open import Tools.Unit

private
  module EM = Modality ErasureModality

private
  variable
    m n : Nat
    σ σ′ : Subst m n
    γ δ : Conₘ n
    t u a : Term n
    x : Fin n
    p : Erasure
    mo : Mode
    rs : Type-restrictions

-- Addition on the left is a decreasing function
-- γ + δ ≤ᶜ γ

+-decreasingˡ : (p q : Erasure) → (p + q) ≤ p
+-decreasingˡ 𝟘 𝟘 = PE.refl
+-decreasingˡ 𝟘 ω = PE.refl
+-decreasingˡ ω 𝟘 = PE.refl
+-decreasingˡ ω ω = PE.refl

-- Addition on the right is a decreasing function
-- γ + δ ≤ᶜ δ

+-decreasingʳ : (p q : Erasure) → (p + q) ≤ q
+-decreasingʳ 𝟘 𝟘 = PE.refl
+-decreasingʳ 𝟘 ω = PE.refl
+-decreasingʳ ω 𝟘 = PE.refl
+-decreasingʳ ω ω = PE.refl

-- Addition on the left is a decreasing function
-- γ +ᶜ δ ≤ᶜ γ

+ᶜ-decreasingˡ : (γ δ : Conₘ n) → γ +ᶜ δ ≤ᶜ γ
+ᶜ-decreasingˡ ε ε = ≤ᶜ-refl
+ᶜ-decreasingˡ (γ ∙ p) (δ ∙ q) = (+ᶜ-decreasingˡ γ δ) ∙ (+-decreasingˡ p q)

-- Addition on the right is a decreasing function
-- γ +ᶜ δ ≤ᶜ δ

+ᶜ-decreasingʳ : (γ δ : Conₘ n) → γ +ᶜ δ ≤ᶜ δ
+ᶜ-decreasingʳ ε ε = ≤ᶜ-refl
+ᶜ-decreasingʳ (γ ∙ p) (δ ∙ q) = (+ᶜ-decreasingʳ γ δ) ∙ (+-decreasingʳ p q)

-- Addition is idempotent
-- γ +ᶜ γ ≡ γ

+ᶜ-idem : (γ : Conₘ n) → γ +ᶜ γ PE.≡ γ
+ᶜ-idem ε = PE.refl
+ᶜ-idem (γ ∙ p) = PE.cong₂ _∙_ (+ᶜ-idem γ) (+-Idempotent p)

-- ⊛ᵣ is a decreasing function on its first argument
-- p ⊛ q ▷ r ≤ p

⊛-decreasingˡ : (p q r : Erasure) → p ⊛ q ▷ r ≤ p
⊛-decreasingˡ 𝟘 𝟘 r = PE.refl
⊛-decreasingˡ 𝟘 ω r = PE.refl
⊛-decreasingˡ ω 𝟘 r = PE.refl
⊛-decreasingˡ ω ω r = PE.refl

-- ⊛ᵣ is a decreasing function on its second argument
-- p ⊛ q ▷ r ≤ q

⊛-decreasingʳ : (p q r : Erasure) → p ⊛ q ▷ r ≤ q
⊛-decreasingʳ 𝟘 𝟘 r = PE.refl
⊛-decreasingʳ 𝟘 ω 𝟘 = PE.refl
⊛-decreasingʳ 𝟘 ω ω = PE.refl
⊛-decreasingʳ ω 𝟘 r = PE.refl
⊛-decreasingʳ ω ω r = PE.refl


-- ⊛ᶜ is a decreasing function on its first argument
-- γ ⊛ᶜ δ ▷ r ≤ᶜ γ

⊛ᶜ-decreasingˡ : (γ δ : Conₘ n) (r : Erasure) → γ ⊛ᶜ δ ▷ r ≤ᶜ γ
⊛ᶜ-decreasingˡ ε ε r = ≤ᶜ-refl
⊛ᶜ-decreasingˡ (γ ∙ 𝟘) (δ ∙ 𝟘) r = (⊛ᶜ-decreasingˡ γ δ r) ∙ PE.refl
⊛ᶜ-decreasingˡ (γ ∙ 𝟘) (δ ∙ ω) r = (⊛ᶜ-decreasingˡ γ δ r) ∙ PE.refl
⊛ᶜ-decreasingˡ (γ ∙ ω) (δ ∙ 𝟘) r = (⊛ᶜ-decreasingˡ γ δ r) ∙ PE.refl
⊛ᶜ-decreasingˡ (γ ∙ ω) (δ ∙ ω) r = (⊛ᶜ-decreasingˡ γ δ r) ∙ PE.refl

-- ⊛ᶜ is a decreasing function on its second argument
-- γ ⊛ᶜ δ ▷ r ≤ᶜ δ

⊛ᶜ-decreasingʳ : (γ δ : Conₘ n) (r : Erasure)  → γ ⊛ᶜ δ ▷ r ≤ᶜ δ
⊛ᶜ-decreasingʳ ε ε r = ≤ᶜ-refl
⊛ᶜ-decreasingʳ (γ ∙ 𝟘) (δ ∙ 𝟘) r = ⊛ᶜ-decreasingʳ γ δ r ∙ PE.refl
⊛ᶜ-decreasingʳ (γ ∙ 𝟘) (δ ∙ ω) r = ⊛ᶜ-decreasingʳ γ δ r ∙ PE.refl
⊛ᶜ-decreasingʳ (γ ∙ ω) (δ ∙ 𝟘) r = ⊛ᶜ-decreasingʳ γ δ r ∙ PE.refl
⊛ᶜ-decreasingʳ (γ ∙ ω) (δ ∙ ω) r = ⊛ᶜ-decreasingʳ γ δ r ∙ PE.refl

-- 𝟘 is the greatest element of the erasure modality
-- p ≤ 𝟘

greatest-elem : (p : Erasure) → p ≤ 𝟘
greatest-elem 𝟘 = PE.refl
greatest-elem ω = PE.refl

-- ω is the least element of the erasure modality
-- ω ≤ p

least-elem : (p : Erasure) → ω ≤ p
least-elem p = PE.refl

-- 𝟘 is the greatest element of the erasure modality
-- If 𝟘 ≤ p then p ≡ 𝟘

greatest-elem′ : (p : Erasure) → 𝟘 ≤ p → p PE.≡ 𝟘
greatest-elem′ p 𝟘≤p = ≤-antisym (greatest-elem p) 𝟘≤p

-- ω is the least element of the erasure modality
-- If p ≤ ω then p ≡ ω

least-elem′ : (p : Erasure) → p ≤ ω → p PE.≡ ω
least-elem′ p p≤ω = ≤-antisym p≤ω (least-elem p)

-- 𝟘ᶜ is the greatest erasure modality context
-- γ ≤ 𝟘ᶜ

greatest-elemᶜ : (γ : Conₘ n) → γ ≤ᶜ 𝟘ᶜ
greatest-elemᶜ ε = ε
greatest-elemᶜ (γ ∙ p) = (greatest-elemᶜ γ) ∙ (greatest-elem p)

-- 𝟙ᶜ is the least erasure modality context
-- 𝟙ᶜ ≤ γ

least-elemᶜ : (γ : Conₘ n) → 𝟙ᶜ ≤ᶜ γ
least-elemᶜ ε = ε
least-elemᶜ (γ ∙ p) = (least-elemᶜ γ) ∙ (least-elem p)

-- The functions _∧ᶜ_ and _+ᶜ_ are pointwise equivalent.

∧ᶜ≈ᶜ+ᶜ : γ ∧ᶜ δ ≈ᶜ γ +ᶜ δ
∧ᶜ≈ᶜ+ᶜ {γ = ε}     {δ = ε}     = ≈ᶜ-refl
∧ᶜ≈ᶜ+ᶜ {γ = _ ∙ _} {δ = _ ∙ _} = ∧ᶜ≈ᶜ+ᶜ ∙ PE.refl

-- The mode corresponding to ω is 𝟙ᵐ.

⌞ω⌟≡𝟙ᵐ : ⌞ ω ⌟ ≡ 𝟙ᵐ
⌞ω⌟≡𝟙ᵐ = 𝟙ᵐ′≡𝟙ᵐ

-- If p is not equal to 𝟘, then p is equal to ω.

≢𝟘→≡ω : p ≢ 𝟘 → p ≡ ω
≢𝟘→≡ω {p = 𝟘} 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 PE.refl)
≢𝟘→≡ω {p = ω} _   = PE.refl

-- An instance of Type-restrictions is suitable for the full reduction
-- theorem if Σₚ-restriction 𝟘 p implies that 𝟘ᵐ is allowed.

Suitable-for-full-reduction :
  Type-restrictions → Set
Suitable-for-full-reduction rs =
  ∀ p → Σₚ-restriction 𝟘 p → T 𝟘ᵐ-allowed
  where
  open Type-restrictions rs

-- Given an instance of Type-restrictions one can create a "suitable"
-- instance.

suitable-for-full-reduction :
  Type-restrictions → ∃ Suitable-for-full-reduction
suitable-for-full-reduction rs =
    record rs
      { ΠΣ-restriction = λ b p q →
          ΠΣ-restriction b p q × T 𝟘ᵐ-allowed
      }
  , (λ _ → proj₂)
  where
  open Type-restrictions rs

-- The full reduction assumptions hold for ErasureModality and any
-- "suitable" Type-restrictions.

full-reduction-assumptions :
  Suitable-for-full-reduction rs →
  Full-reduction-assumptions ErasureModality rs
full-reduction-assumptions {rs = rs} 𝟘→𝟘ᵐ = record
  { ≤𝟘           = λ _ → greatest-elem _
  ; ·-increasing = λ where
      {p = p} {r = 𝟘} _ → begin
        𝟘      ≡˘⟨ EM.·-zeroʳ _ ⟩
        p · 𝟘  ∎
      {p = p} {r = ω} _ → begin
        ω      ≤⟨ least-elem p ⟩
        p · ω  ∎
  ; ⌞⌟≡𝟙ᵐ→≤𝟙 = λ where
      {p = ω} _ _ → begin
        ω  ≡⟨⟩
        ω  ∎
      {p = 𝟘} ok →
        ⌞ 𝟘 ⌟ ≡ 𝟙ᵐ      →⟨ (λ hyp ok → ⌞⌟≡𝟙ᵐ→≉𝟘 ok hyp PE.refl) ⟩
        ¬ T 𝟘ᵐ-allowed  →⟨ _$ 𝟘→𝟘ᵐ _ ok ⟩
        ⊥               →⟨ ⊥-elim ⟩
        𝟘 ≤ ω           □
  }
  where
  open Tools.Reasoning.PartialOrder ≤-poset
