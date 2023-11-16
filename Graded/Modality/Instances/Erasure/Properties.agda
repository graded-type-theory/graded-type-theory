------------------------------------------------------------------------
-- Properties of the erasure modality.
------------------------------------------------------------------------

open import Tools.Level

open import Graded.Modality.Instances.Erasure
open import Graded.Modality.Variant lzero

module Graded.Modality.Instances.Erasure.Properties
  (variant : Modality-variant)
  where

open Modality-variant variant

open import Graded.Modality.Instances.Erasure.Modality

open import Graded.Context (ErasureModality variant)
open import Graded.Context.Properties (ErasureModality variant) public

open import Graded.FullReduction.Assumptions

open import Graded.Modality.Properties (ErasureModality variant) as P
  public

open import Graded.Usage (ErasureModality variant)
open import Graded.Usage.Restrictions Erasure
open import Graded.Usage.Inversion (ErasureModality variant)
open import Graded.Mode (ErasureModality variant)

open import Definition.Typed.Restrictions (ErasureModality variant)

open import Definition.Untyped Erasure hiding (Identity)

open import Tools.Algebra Erasure
open import Tools.Bool hiding (_∧_)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product as Σ
open import Tools.PropositionalEquality as PE using (_≡_; _≢_)
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Sum
open import Tools.Unit

private
  module EM = Modality (ErasureModality variant)

private
  variable
    m n : Nat
    σ σ′ : Subst m n
    γ δ : Conₘ n
    t u a : Term n
    x : Fin n
    p r s z : Erasure
    mo : Mode
    rs : Type-restrictions
    us : Usage-restrictions

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

-- The nr function returns the sum of its last three arguments.

nr≡ : ∀ {n} → nr p r z s n ≡ z + s + n
nr≡ {p = 𝟘} {z = z} {s = s} {n = n} =
  z + n + (s + 𝟘)  ≡⟨ PE.cong (λ s → z + _ + s) (EM.+-identityʳ _) ⟩
  z + n + s        ≡⟨ EM.+-assoc z _ _ ⟩
  z + (n + s)      ≡⟨ PE.cong (z +_) (EM.+-comm n _) ⟩
  z + (s + n)      ≡˘⟨ EM.+-assoc z _ _ ⟩
  z + s + n        ∎
  where
  open Tools.Reasoning.PropositionalEquality
nr≡ {p = ω} {z = z} {s = s} {n = n} =
  z + n + (s + n)    ≡⟨ EM.+-assoc z _ _ ⟩
  z + (n + (s + n))  ≡˘⟨ PE.cong (z +_) (EM.+-assoc n _ _) ⟩
  z + ((n + s) + n)  ≡⟨ PE.cong ((z +_) ∘→ (_+ _)) (EM.+-comm n _) ⟩
  z + ((s + n) + n)  ≡⟨ PE.cong (z +_) (EM.+-assoc s _ _) ⟩
  z + (s + (n + n))  ≡⟨ PE.cong ((z +_) ∘→ (s +_)) (EM.∧-idem _) ⟩
  z + (s + n)        ≡˘⟨ EM.+-assoc z _ _ ⟩
  z + s + n          ∎
  where
  open Tools.Reasoning.PropositionalEquality

-- Division is correctly defined.

/≡/ : ∀ p q → p P./ q ≡ (p / q)
/≡/ = λ where
  𝟘 𝟘 → PE.refl , λ _ → λ _ → PE.refl
  ω 𝟘 → PE.refl , λ _ → idᶠ
  𝟘 ω → PE.refl , λ _ → idᶠ
  ω ω → PE.refl , λ _ → idᶠ

-- An instance of Type-restrictions is suitable for the full reduction
-- theorem if Σˢ-allowed 𝟘 p implies that 𝟘ᵐ is allowed.

Suitable-for-full-reduction :
  Type-restrictions → Set
Suitable-for-full-reduction rs =
  ∀ p → Σˢ-allowed 𝟘 p → T 𝟘ᵐ-allowed
  where
  open Type-restrictions rs

-- Given an instance of Type-restrictions one can create a "suitable"
-- instance.

suitable-for-full-reduction :
  Type-restrictions → ∃ Suitable-for-full-reduction
suitable-for-full-reduction rs =
    record rs
      { ΠΣ-allowed = λ b p q →
          ΠΣ-allowed b p q × (b ≡ BMΣ 𝕤 × p ≡ 𝟘 → T 𝟘ᵐ-allowed)
      ; []-cong-allowed = λ s →
          []-cong-allowed s × T 𝟘ᵐ-allowed
      ; []-cong→Erased = λ (ok₁ , ok₂) →
            []-cong→Erased ok₁ .proj₁ , []-cong→Erased ok₁ .proj₂
          , (λ _ → ok₂)
      ; []-cong→¬Trivial =
          𝟘ᵐ.non-trivial ∘→ proj₂
      }
  , (λ _ → (_$ (PE.refl , PE.refl)) ∘→ proj₂)
  where
  open Type-restrictions rs

-- The full reduction assumptions hold for ErasureModality variant and
-- any "suitable" Type-restrictions.

full-reduction-assumptions :
  Suitable-for-full-reduction rs →
  Full-reduction-assumptions rs us
full-reduction-assumptions {rs = rs} 𝟘→𝟘ᵐ = record
  { sink⊎𝟙≤𝟘 = λ _ → inj₂ PE.refl
  ; ≡𝟙⊎𝟙≤𝟘   = λ where
      {p = ω} _  → inj₁ PE.refl
      {p = 𝟘} ok → inj₂ (PE.refl , 𝟘→𝟘ᵐ _ ok , PE.refl)
  }


-- Type and usage restrictions that satisfy the full reduction
-- assumptions are "suitable".

full-reduction-assumptions-suitable :
  Full-reduction-assumptions rs us → Suitable-for-full-reduction rs
full-reduction-assumptions-suitable as =
    λ p Σ-ok → case ≡𝟙⊎𝟙≤𝟘 Σ-ok of λ where
      (inj₁ ())
      (inj₂ (_ , 𝟘ᵐ-ok , _)) → 𝟘ᵐ-ok
  where
  open Full-reduction-assumptions as

-- If _∧_ is defined in the given way and 𝟘 is the additive unit, then
-- there is only one lawful way to define addition (up to pointwise
-- equality).

+-unique :
  (_+_ : Op₂ Erasure) →
  Identity 𝟘 _+_ →
  _+_ DistributesOverˡ _∧_ →
  ∀ p q → (p + q) ≡ p ∧ q
+-unique _+_ (identityˡ , identityʳ) +-distrib-∧ˡ = λ where
  𝟘 q →
    let open Tools.Reasoning.PropositionalEquality in
      𝟘 + q  ≡⟨ identityˡ _ ⟩
      q      ≡⟨⟩
      𝟘 ∧ q  ∎
  p 𝟘 →
    let open Tools.Reasoning.PropositionalEquality in
      p + 𝟘  ≡⟨ identityʳ _ ⟩
      p      ≡⟨ EM.∧-comm 𝟘 _ ⟩
      p ∧ 𝟘  ∎
  ω ω →
    let open Tools.Reasoning.PartialOrder ≤-poset in
    ≤-antisym
      (begin
         ω + ω  ≤⟨ +-distrib-∧ˡ ω ω 𝟘 ⟩
         ω + 𝟘  ≡⟨ identityʳ _ ⟩
         ω      ∎)
      (begin
         ω      ≤⟨ least-elem (ω + ω) ⟩
         ω + ω  ∎)

-- If _∧_ is defined in the given way, 𝟘 is the multiplicative zero,
-- and ω is the multiplicative unit, then there is only one lawful way
-- to define multiplication (up to pointwise equality).

·-unique :
  (_·′_ : Op₂ Erasure) →
  Zero 𝟘 _·′_ →
  LeftIdentity ω _·′_ →
  ∀ p q → (p ·′ q) ≡ p · q
·-unique _·′_ (zeroˡ , zeroʳ) identityˡ = λ where
    𝟘 q →
      𝟘 ·′ q  ≡⟨ zeroˡ _ ⟩
      𝟘       ≡⟨⟩
      𝟘 · q   ∎
    p 𝟘 →
      p ·′ 𝟘  ≡⟨ zeroʳ _ ⟩
      𝟘       ≡˘⟨ EM.·-zeroʳ _ ⟩
      p · 𝟘   ∎
    ω ω →
      ω ·′ ω  ≡⟨ identityˡ _ ⟩
      ω       ≡⟨⟩
      ω · ω   ∎
  where
  open Tools.Reasoning.PropositionalEquality

-- With the given definitions of _∧_, _+_ and _·_ there is only one
-- lawful way to define the star operator (up to pointwise equality).

⊛-unique :
  (_⊛_▷_ : Op₃ Erasure) →
  (∀ p q r → (p ⊛ q ▷ r) ≤ q + r · (p ⊛ q ▷ r)) →
  (∀ p q r → (p ⊛ q ▷ r) ≤ p) →
  (∀ r → _·_ SubDistributesOverʳ (_⊛_▷ r) by _≤_) →
  ∀ p q r → (p ⊛ q ▷ r) ≡ p ∧ q
⊛-unique _⊛_▷_ ⊛-ineq₁ ⊛-ineq₂ ·-sub-distribʳ-⊛ = λ where
    ω q r → ≤-antisym
      (begin
         ω ⊛ q ▷ r  ≤⟨ ⊛-ineq₂ ω q r ⟩
         ω          ∎)
      (begin
         ω          ≤⟨ least-elem (ω ⊛ q ▷ r) ⟩
         ω ⊛ q ▷ r  ∎)
    p ω r → ≤-antisym
      (begin
         p ⊛ ω ▷ r  ≤⟨ ⊛-ineq₁ p ω r ⟩
         ω          ≡⟨ EM.∧-comm ω _ ⟩
         p ∧ ω      ∎)
      (begin
         p ∧ ω      ≡⟨ EM.∧-comm p _ ⟩
         ω          ≤⟨ least-elem (p ⊛ ω ▷ r) ⟩
         p ⊛ ω ▷ r  ∎)
    𝟘 𝟘 r → ≤-antisym
      (begin
         𝟘 ⊛ 𝟘 ▷ r  ≤⟨ greatest-elem _ ⟩
         𝟘          ∎)
      (begin
         𝟘                ≡˘⟨ EM.·-zeroʳ _ ⟩
         (ω ⊛ 𝟘 ▷ r) · 𝟘  ≤⟨ ·-sub-distribʳ-⊛ r 𝟘 ω 𝟘 ⟩
         𝟘 ⊛ 𝟘 ▷ r        ∎)
  where
  open Tools.Reasoning.PartialOrder ≤-poset
