------------------------------------------------------------------------
-- Properties of the erasure modality.
------------------------------------------------------------------------

open import Tools.Level

open import Graded.Modality.Instances.Erasure

module Graded.Modality.Instances.Erasure.Properties where


open import Graded.Modality.Instances.Erasure.Modality

open import Graded.Context ErasureModality
open import Graded.Context.Properties ErasureModality as C
  public
  hiding (+ᶜ-decreasingˡ; +ᶜ-decreasingʳ)
open import Graded.Mode.Instances.Zero-one.Variant ErasureModality

open import Graded.Modality.Properties ErasureModality as P
  public

open import Definition.Untyped Erasure

open import Tools.Algebra Erasure
open import Tools.Bool hiding (_∧_)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+; Sequence)
open import Tools.Product as Σ
open import Tools.PropositionalEquality as PE using (_≡_; _≢_)
open import Tools.Relation
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Sum

private
  module EM = Modality ErasureModality

private
  variable
    m n : Nat
    σ σ′ : Subst m n
    γ δ η χ : Conₘ n
    t u a : Term n
    x : Fin n
    p q r s z z′ s′ : Erasure

-- Addition on the left is a decreasing function
-- γ +ᶜ δ ≤ᶜ γ

+ᶜ-decreasingˡ : (γ δ : Conₘ n) → γ +ᶜ δ ≤ᶜ γ
+ᶜ-decreasingˡ _ _ = C.+ᶜ-decreasingˡ PE.refl

-- Addition on the right is a decreasing function
-- γ +ᶜ δ ≤ᶜ δ

+ᶜ-decreasingʳ : (γ δ : Conₘ n) → γ +ᶜ δ ≤ᶜ δ
+ᶜ-decreasingʳ _ _ = C.+ᶜ-decreasingʳ PE.refl

-- Addition is idempotent
-- γ +ᶜ γ ≡ γ

+ᶜ-idem : (γ : Conₘ n) → γ +ᶜ γ PE.≡ γ
+ᶜ-idem ε = PE.refl
+ᶜ-idem (γ ∙ p) = PE.cong₂ _∙_ (+ᶜ-idem γ) (+-Idempotent p)

opaque

  ·-comm : Commutative _·_
  ·-comm 𝟘 𝟘 = PE.refl
  ·-comm 𝟘 ω = PE.refl
  ·-comm ω 𝟘 = PE.refl
  ·-comm ω ω = PE.refl

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

opaque

  ⊛ᶜ≈+ᶜ : (γ δ : Conₘ n) → γ ⊛ᶜ δ ▷ r ≈ᶜ γ +ᶜ δ
  ⊛ᶜ≈+ᶜ ε ε = ε
  ⊛ᶜ≈+ᶜ (γ ∙ p) (δ ∙ q) = ⊛ᶜ≈+ᶜ γ δ ∙ PE.refl

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

opaque

  -- Multiplication from the right is increasing.

  ·-increasingʳ : p ≤ p · q
  ·-increasingʳ {p = 𝟘} = PE.refl
  ·-increasingʳ {p = ω} = PE.refl

opaque

  -- Multiplication from the left is increasing.

  ·-increasingˡ : p ≤ q · p
  ·-increasingˡ {q = 𝟘} = greatest-elem _
  ·-increasingˡ {q = ω} = ≤-refl

opaque

  -- Multiplication from the left is increasing.

  ·ᶜ-increasingˡ : γ ≤ᶜ p ·ᶜ γ
  ·ᶜ-increasingˡ {γ = ε}     = ε
  ·ᶜ-increasingˡ {γ = _ ∙ _} = ·ᶜ-increasingˡ ∙ ·-increasingˡ

-- The functions _∧ᶜ_ and _+ᶜ_ are pointwise equivalent.

∧ᶜ≈ᶜ+ᶜ : γ ∧ᶜ δ ≈ᶜ γ +ᶜ δ
∧ᶜ≈ᶜ+ᶜ {γ = ε}     {δ = ε}     = ≈ᶜ-refl
∧ᶜ≈ᶜ+ᶜ {γ = _ ∙ _} {δ = _ ∙ _} = ∧ᶜ≈ᶜ+ᶜ ∙ PE.refl

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

opaque

  -- The nr function returns the sum of its last three arguments.

  nrᶜ≈ᶜ : nrᶜ p r γ δ η ≈ᶜ γ +ᶜ δ +ᶜ η
  nrᶜ≈ᶜ         {γ = ε}     {δ = ε}     {η = ε}     = ε
  nrᶜ≈ᶜ {p} {r} {γ = _ ∙ z} {δ = _ ∙ s} {η = _ ∙ n} =
    nrᶜ≈ᶜ ∙
    (nr p r z s n  ≡⟨ nr≡ {r = r} {z = z} ⟩
     z + s + n     ≡⟨ EM.+-assoc z _ _ ⟩
     z + (s + n)   ∎)
    where
    open Tools.Reasoning.PropositionalEquality

-- Division is correctly defined.

/≡/ : ∀ p q → p P./ q ≡ (p / q)
/≡/ = λ where
  𝟘 𝟘 → PE.refl , λ _ → λ _ → PE.refl
  ω 𝟘 → PE.refl , λ _ → idᶠ
  𝟘 ω → PE.refl , λ _ → idᶠ
  ω ω → PE.refl , λ _ → idᶠ

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

opaque

  -- There is only one lawful way to define the nr function for
  -- ErasureModality.

  nr-unique :
    (has-nr : Has-nr ErasureModality) →
    ∀ p r z s n → Has-nr.nr has-nr p r z s n ≡ nr p r z s n
  nr-unique has-nr = λ where
      p r ω s n → nr′ω≡nrω λ ()
      p r z ω n → nr′ω≡nrω λ ()
      p r z s ω → nr′ω≡nrω λ ()
      p r 𝟘 𝟘 𝟘 → nr′𝟘≡nr𝟘 (PE.refl , PE.refl , PE.refl)
    where
    open Has-nr has-nr renaming (nr to nr′; nr-positive to nr′-positive)
    open Has-nr erasure-has-nr using (nr-positive)
    open Tools.Reasoning.PropositionalEquality
    nr′ω≡nrω : ∀ {p r z s n} → ¬ (z ≡ 𝟘 × s ≡ 𝟘 × n ≡ 𝟘)
         → nr′ p r z s n ≡ nr p r z s n
    nr′ω≡nrω {p} {r} {z} {s} {n} ≢𝟘 = begin
      nr′ p r z s n ≡⟨ ≢𝟘→≡ω (≢𝟘 ∘→ nr′-positive) ⟩
      ω             ≡˘⟨ ≢𝟘→≡ω (≢𝟘 ∘→ nr-positive {r = r}) ⟩
      nr p r z s n  ∎
    nr′𝟘≡nr𝟘 : ∀ {p r z s n} → (z ≡ 𝟘 × s ≡ 𝟘 × n ≡ 𝟘)
         → nr′ p r z s n ≡ nr p r z s n
    nr′𝟘≡nr𝟘 {p} {r} {z} {s} {n} (PE.refl , PE.refl , PE.refl) = begin
      nr′ p r z s n ≡⟨ nr-𝟘 ⦃ has-nr ⦄ ⟩
      𝟘             ≡˘⟨ nr-𝟘 {r = r} ⟩
      nr p r z s n  ∎

opaque

  -- There is only one lawful way to define the nr function for
  -- ErasureModality.

  nrᶜ-unique :
    {has-nr : Has-nr ErasureModality} →
    nrᶜ ⦃ has-nr = has-nr ⦄ p r γ δ η ≈ᶜ nrᶜ p r γ δ η
  nrᶜ-unique {γ = ε}     {δ = ε}     {η = ε}              = ε
  nrᶜ-unique {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} {has-nr} =
    nrᶜ-unique ∙ nr-unique has-nr _ _ _ _ _

opaque

  -- The nr function satisfies Linearity-like-nr-for-𝟙.

  nr-linearity-like-for-𝟙 :
    Has-nr.Linearity-like-nr-for-𝟙 erasure-has-nr
  nr-linearity-like-for-𝟙 {p = 𝟘} {z} {s} {n} =
    (z + n) + (s + 𝟘)  ≡⟨ PE.cong₂ _+_ (EM.+-comm z _) (EM.+-identityʳ _) ⟩
    (n + z) + s        ≡⟨ EM.+-assoc n _ _ ⟩
    n + (z + s)        ≡˘⟨ PE.cong (n +_) (EM.+-comm s _) ⟩
    n + (s + z)        ∎
    where
    open Tools.Reasoning.PropositionalEquality
  nr-linearity-like-for-𝟙 {p = ω} {z} {s} {n} =
    (z + n) + (s + n)  ≡⟨ PE.cong₂ _+_ (EM.+-comm z _) (EM.+-comm s _) ⟩
    (n + z) + (n + s)  ≡˘⟨ EM.+-assoc (n + _) _ _ ⟩
    ((n + z) + n) + s  ≡⟨ PE.cong (_+ _) $ EM.+-assoc n _ _ ⟩
    (n + (z + n)) + s  ≡⟨ PE.cong (_+ _) $ PE.cong (n +_) $ EM.+-comm z _ ⟩
    (n + (n + z)) + s  ≡˘⟨ PE.cong (_+ _) $ EM.+-assoc n _ _ ⟩
    ((n + n) + z) + s  ≡⟨ EM.+-assoc (n + _) _ _ ⟩
    (n + n) + (z + s)  ≡⟨ PE.cong₂ _+_ (+-Idempotent n) (EM.+-comm z _) ⟩
    n + (s + z)        ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque

  -- The nr function satisfies Linearity-like-nr-for-𝟘.

  nr-linearity-like-for-𝟘 :
    Has-nr.Linearity-like-nr-for-𝟘 erasure-has-nr
  nr-linearity-like-for-𝟘 {p} {z} {s} {n} =
    nr p 𝟘 z s n       ≡⟨⟩
    nr p ω z s n       ≡⟨ nr-linearity-like-for-𝟙 {z = z} ⟩
    n + (s + z)        ≡⟨ PE.cong (n +_) $ EM.+-comm s _ ⟩
    n + (z + s)        ≡˘⟨ PE.cong₂ _+_ (+-Idempotent n) (EM.+-comm s _) ⟩
    (n + n) + (s + z)  ≡⟨ EM.+-assoc n _ _ ⟩
    n + (n + (s + z))  ≡˘⟨ PE.cong (n +_) $ EM.+-assoc n _ _ ⟩
    n + ((n + s) + z)  ≡⟨ PE.cong (n +_) $ PE.cong (_+ _) $ EM.+-comm n _ ⟩
    n + ((s + n) + z)  ≡⟨ PE.cong (n +_) $ EM.+-assoc s _ _ ⟩
    n + (s + (n + z))  ≡˘⟨ EM.+-assoc n _ _ ⟩
    (n + s) + (n + z)  ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque

  -- Subtraction of ω by anything is ω

  ω-p≡ω : ∀ p → ω - p ≡ ω
  ω-p≡ω p = ∞-p≡∞ PE.refl p

opaque

  -- Subtraction is supported with
  --  ω - p ≡ ω for any p
  --  p - 𝟘 ≡ p for any p

  supports-subtraction : Supports-subtraction
  supports-subtraction =
    Addition≡Meet.supports-subtraction (λ _ _ → PE.refl)

-- An alternative definition of the subtraction relation with
--   ω - p ≡ ω for all p
--   p - 𝟘 ≡ p for all p
-- and not defined otherwise

data _-_≡′_ : (p q r : Erasure) → Set where
  ω-p≡′ω : ω - p ≡′ ω
  p-𝟘≡′p : p - 𝟘 ≡′ p

opaque

  -- The two subtraction relations are equivalent.

  -≡↔-≡′ : ∀ p q r → (p - q ≡ r) ⇔ (p - q ≡′ r)
  -≡↔-≡′ p q r = left p q r , right
    where
    left : ∀ p q r → p - q ≡ r → p - q ≡′ r
    left ω q r p-q≡r =
      case -≡-functional {q = q} p-q≡r (ω-p≡ω q) of λ {
        PE.refl →
      ω-p≡′ω }
    left p 𝟘 r p-q≡r =
      case -≡-functional p-q≡r p-𝟘≡p of λ {
        PE.refl →
      p-𝟘≡′p }
    left 𝟘 q r p-q≡r =
      case 𝟘-p≡q p-q≡r of λ {
        (PE.refl , PE.refl) →
      p-𝟘≡′p}
    right : p - q ≡′ r → p - q ≡ r
    right ω-p≡′ω = ω-p≡ω q
    right p-𝟘≡′p = p-𝟘≡p

opaque

  -- z ∧ s is the greatest lower bound of the sequence nrᵢ r z s.

  Erasure-nrᵢ-glb-∧ :
    ∀ r z s →
    Modality.Greatest-lower-bound
        ErasureModality (z ∧ s)
         (Modality.nrᵢ ErasureModality r z s)
  Erasure-nrᵢ-glb-∧ r 𝟘 𝟘 =
    ≤-reflexive ∘→ PE.sym ∘→ nrᵢ-𝟘
      , λ { 𝟘 q≤ → ≤-refl ; ω q≤ → least-elem 𝟘}
  Erasure-nrᵢ-glb-∧ _ ω _ =
    (λ _ → PE.refl) , λ { 𝟘 𝟘≤ → 𝟘≤ 0 ; ω _ → ≤-refl}
  Erasure-nrᵢ-glb-∧ _ _ ω =
    lemma , λ { 𝟘 𝟘≤ → case 𝟘≤ 1 of λ () ; ω _ → ≤-refl}
    where
    lemma : ∀ i → z ∧ ω ≤ EM.nrᵢ r z ω i
    lemma i = ≤-trans (≤-reflexive (EM.+-comm _ ω)) PE.refl

opaque

  -- The sequence nrᵢ r z s has a greatest lowest bound.

  Erasure-nrᵢ-glb :
    ∀ r z s → ∃ λ x →
      Modality.Greatest-lower-bound
        ErasureModality x
         (Modality.nrᵢ ErasureModality r z s)
  Erasure-nrᵢ-glb r z s = z ∧ s , Erasure-nrᵢ-glb-∧ r z s

opaque

  -- A variant of Erasure-nrᵢ-glb-∧ for grade contexts.

  Erasure-nrᵢᶜ-glb-∧ᶜ : Greatest-lower-boundᶜ (γ ∧ᶜ δ) (nrᵢᶜ r γ δ)
  Erasure-nrᵢᶜ-glb-∧ᶜ {γ = ε}     {δ = ε}     = ε-GLB
  Erasure-nrᵢᶜ-glb-∧ᶜ {γ = _ ∙ _} {δ = _ ∙ _} =
    GLBᶜ-pointwise′ Erasure-nrᵢᶜ-glb-∧ᶜ (Erasure-nrᵢ-glb-∧ _ _ _)

opaque instance

  -- The modality has well-behaved GLBs.

  Erasure-supports-factoring-nr-rule :
    Has-well-behaved-GLBs ErasureModality
  Erasure-supports-factoring-nr-rule = record
    { +-GLBˡ = +-GLBˡ′
    ; ·-GLBˡ = ·-GLBˡ′
    ; ·-GLBʳ = comm∧·-GLBˡ⇒·-GLBʳ ·-comm ·-GLBˡ′
    ; +nrᵢ-GLB = λ {_} {r} {_} {s} {_} {_} {s′} x x₁ →
        nrᵢ+-GLB {r = r} {s = s} {s′ = s′} x x₁
    }
    where
    open Modality ErasureModality
      hiding (_+_; _·_; _≤_; 𝟘; ω)

    +-GLBˡ′ : {p q : Erasure} {pᵢ : Sequence Erasure} →
            Greatest-lower-bound p pᵢ →
            Greatest-lower-bound (q + p) (λ i → q + pᵢ i)
    +-GLBˡ′ {q = 𝟘} p-glb = p-glb
    +-GLBˡ′ {q = ω} p-glb = GLB-const′

    ·-GLBˡ′ : {p q : Erasure} {pᵢ : Sequence Erasure} →
            Greatest-lower-bound p pᵢ →
            Greatest-lower-bound (q · p) (λ i → q · pᵢ i)
    ·-GLBˡ′ {q = 𝟘} p-glb = GLB-const′
    ·-GLBˡ′ {q = ω} p-glb = p-glb

    nrᵢ+-ω-GLB : ∀ {r z s} i →
      nrᵢ r z s i ≡ ω →
      Greatest-lower-bound ω (nrᵢ r z s)
    nrᵢ+-ω-GLB {r} {z} {s} i nrᵢ≡ω =
        (λ i → least-elem (nrᵢ r z s i))
      , λ q q≤ → ≤-trans (q≤ i) (≤-reflexive nrᵢ≡ω)

    nrᵢ+-GLB :
      Greatest-lower-bound p (nrᵢ r z s) →
      Greatest-lower-bound q (nrᵢ r z′ s′) →
      ∃ λ x → Greatest-lower-bound x (nrᵢ r (z + z′) (s + s′)) × p + q ≤ x
    nrᵢ+-GLB {z = 𝟘} {s = 𝟘} {z′ = 𝟘} {s′ = 𝟘} p-glb q-glb =
      let p≡𝟘 = GLB-unique p-glb (GLB-const nrᵢ-𝟘)
          q≡𝟘 = GLB-unique q-glb (GLB-const nrᵢ-𝟘)
      in  𝟘 , GLB-const nrᵢ-𝟘 , ≤-reflexive (+-cong p≡𝟘 q≡𝟘)
    nrᵢ+-GLB {r} {z = 𝟘} {s = 𝟘} {z′ = 𝟘} {s′ = ω} p-glb q-glb =
      ω , nrᵢ+-ω-GLB {r = r} {s = ω} 1 PE.refl
        , ≤-trans (+-monotoneʳ (q-glb .proj₁ 1))
            (≤-reflexive (+-comm _ ω))
    nrᵢ+-GLB {r} {z = 𝟘} {s = ω} {z′ = 𝟘} {s′} p-glb q-glb =
      ω , nrᵢ+-ω-GLB {r = r} {s = ω} 1 PE.refl
        , +-monotoneˡ (p-glb .proj₁ 1)
    nrᵢ+-GLB {r} {z = 𝟘} {s} {z′ = ω} {s′} p-glb q-glb =
      ω , nrᵢ+-ω-GLB {r = r} {s = s + s′} 0 PE.refl
        , ≤-trans (+-monotoneʳ (q-glb .proj₁ 0))
            (≤-reflexive (+-comm _ ω))
    nrᵢ+-GLB {r} {z = ω} {s} {s′} p-glb q-glb =
      ω , nrᵢ+-ω-GLB {r = r} {s = s + s′} 0 PE.refl
        , +-monotoneˡ (p-glb .proj₁ 0)

opaque

  -- The context in the conclusions of the usage rules for natrec with
  -- the natrec-star operator and with greatest lower bounds are the same

  ▸⊛≈GLB :
    let open Modality ErasureModality in
    Greatest-lower-bound q (nrᵢ r 𝟙 p) →
    Greatest-lower-boundᶜ χ (nrᵢᶜ r γ δ) →
    ((γ ∧ᶜ η) ⊛ᶜ p ·ᶜ η +ᶜ δ ▷ r) ≈ᶜ (q ·ᶜ η +ᶜ χ)
  ▸⊛≈GLB {q} {r} {p} {χ} {γ} {δ} {η} q-GLB χ-GLB = begin
    (γ ∧ᶜ η) ⊛ᶜ p ·ᶜ η +ᶜ δ ▷ r ≈⟨ ⊛ᶜ≈+ᶜ _ _ ⟩
    (γ ∧ᶜ η) +ᶜ p ·ᶜ η +ᶜ δ     ≈⟨ +ᶜ-congʳ ∧ᶜ≈ᶜ+ᶜ ⟩
    (γ +ᶜ η) +ᶜ p ·ᶜ η +ᶜ δ     ≈˘⟨ +ᶜ-assoc _ _ _ ⟩
    ((γ +ᶜ η) +ᶜ p ·ᶜ η) +ᶜ δ   ≈⟨ +ᶜ-congʳ (+ᶜ-assoc _ _ _) ⟩
    (γ +ᶜ η +ᶜ p ·ᶜ η) +ᶜ δ     ≈⟨ +ᶜ-assoc _ _ _ ⟩
    γ +ᶜ (η +ᶜ p ·ᶜ η) +ᶜ δ     ≈⟨ +ᶜ-comm _ _ ⟩
    ((η +ᶜ p ·ᶜ η) +ᶜ δ) +ᶜ γ   ≈⟨ +ᶜ-assoc _ _ _ ⟩
    (η +ᶜ p ·ᶜ η) +ᶜ (δ +ᶜ γ)   ≈⟨ +ᶜ-cong (lemma p) (+ᶜ-comm _ _) ⟩
    η +ᶜ (γ +ᶜ δ)               ≈˘⟨ +ᶜ-congʳ (·ᶜ-identityˡ _) ⟩
    ω ·ᶜ η +ᶜ (γ +ᶜ δ)          ≈˘⟨ +ᶜ-cong (·ᶜ-congʳ q≡ω) χ≈ ⟩
    q ·ᶜ η +ᶜ χ                 ∎
    where
    open ≈ᶜ-reasoning
    q≡ω : q ≡ ω
    q≡ω = GLB-unique q-GLB (Erasure-nrᵢ-glb-∧ _ _ _)
    χ≈ : χ ≈ᶜ γ +ᶜ δ
    χ≈ = GLBᶜ-unique χ-GLB (lemma _ _)
      where
      lemma : (γ δ : Conₘ n) → Greatest-lower-boundᶜ (γ +ᶜ δ) (nrᵢᶜ r γ δ)
      lemma ε ε = ε-GLB
      lemma (γ ∙ p) (δ ∙ q) =
        GLBᶜ-pointwise′ (lemma γ δ) (Erasure-nrᵢ-glb-∧ r p q)
    lemma : ∀ p → η +ᶜ p ·ᶜ η ≈ᶜ η
    lemma 𝟘 = begin
      η +ᶜ 𝟘 ·ᶜ η ≈⟨ +ᶜ-congˡ (·ᶜ-zeroˡ _) ⟩
      η +ᶜ 𝟘ᶜ     ≈⟨ +ᶜ-identityʳ _ ⟩
      η           ∎
    lemma ω = begin
      η +ᶜ ω ·ᶜ η ≈⟨ +ᶜ-congˡ (·ᶜ-identityˡ _) ⟩
      η +ᶜ η      ≡⟨ +ᶜ-idem _ ⟩
      η           ∎

------------------------------------------------------------------------
-- Properties relating to the mode structure Zero-one

module _ {𝟘ᵐ-allowed : Bool} where

  private
    variant : Mode-variant
    variant = record
      { 𝟘ᵐ-allowed = 𝟘ᵐ-allowed
      ; 𝟘-well-behaved = λ _ → erasure-has-well-behaved-zero
      }

  open import Graded.FullReduction.Assumptions variant
  open import Graded.Mode.Instances.Zero-one variant
  open import Graded.Usage.Restrictions ErasureModality Zero-one-isMode
  open import Definition.Typed.Restrictions ErasureModality

  private variable
    TR : Type-restrictions
    UR : Usage-restrictions

  opaque

    -- For the erasure modality, if 𝟘ᵐ is allowed, then ⌜ ⌞ p ⌟ ⌝ is
    -- equal to p.

    ⌜⌞⌟⌝ : T 𝟘ᵐ-allowed → ⌜ ⌞ p ⌟ ⌝ PE.≡ p
    ⌜⌞⌟⌝ {p}     ok with ⌞ p ⌟ | ⌞⌟-view-total p
    ⌜⌞⌟⌝         ok | _   | 𝟘ᵐ-not-allowed not-ok _ = ⊥-elim (not-ok ok)
    ⌜⌞⌟⌝ {p = 𝟘} _  | _   | 𝟙ᵐ 𝟘≢𝟘 _                = ⊥-elim (𝟘≢𝟘 PE.refl)
    ⌜⌞⌟⌝ {p = ω} _  | .𝟙ᵐ | 𝟙ᵐ _ PE.refl            = PE.refl
    ⌜⌞⌟⌝         _  | .𝟘ᵐ | 𝟘ᵐ PE.refl PE.refl      = PE.refl

  opaque

    -- The mode corresponding to ω is 𝟙ᵐ.

    ⌞ω⌟≡𝟙ᵐ : ⌞ ω ⌟ ≡ 𝟙ᵐ
    ⌞ω⌟≡𝟙ᵐ = ≢𝟘→⌞⌟≡𝟙ᵐ (λ ())

  -- Instances of Type-restrictions and Usage-restrictions are suitable for
  -- the full reduction theorem if Σˢ-allowed 𝟘 p implies that 𝟘ᵐ is allowed.

  Suitable-for-full-reduction :
    Type-restrictions → Usage-restrictions → Set
  Suitable-for-full-reduction TR UR =
    ∀ p → Σˢ-allowed 𝟘 p → T 𝟘ᵐ-allowed
    where
    open Type-restrictions TR
    open Usage-restrictions UR

  -- Given an instance of Type-restrictions one can create a "suitable"
  -- instance for any Usage-restrictions.

  suitable-for-full-reduction :
    Type-restrictions → ∃ λ TR → Suitable-for-full-reduction TR UR
  suitable-for-full-reduction {UR} TR =
      record TR
        { ΠΣ-allowed = λ b p q →
            ΠΣ-allowed b p q × (b ≡ BMΣ 𝕤 × p ≡ 𝟘 → T 𝟘ᵐ-allowed)
        ; []-cong-allowed = λ s →
            []-cong-allowed s × T 𝟘ᵐ-allowed
        ; []-cong→Erased = λ (ok₁ , ok₂) →
              []-cong→Erased ok₁ .proj₁ , []-cong→Erased ok₁ .proj₂
            , (λ _ → ok₂)
        ; []-cong→¬Trivial = λ _ → non-trivial ⦃ erasure-has-well-behaved-zero ⦄
        }
    , (λ _ → (_$ (PE.refl , PE.refl)) ∘→ proj₂)
    where
    open Type-restrictions TR
    open Usage-restrictions UR

  -- The full reduction assumptions hold for ErasureModality and
  -- any "suitable" Type-restrictions and Usage-restrictions.

  full-reduction-assumptions :
    Suitable-for-full-reduction TR UR →
    Full-reduction-assumptions TR UR
  full-reduction-assumptions 𝟘→𝟘ᵐ = record
    { sink⊎𝟙≤𝟘 = λ _ _ → inj₂ PE.refl
    ; ≡𝟙⊎𝟙≤𝟘   = λ where
        {p = ω} _  → inj₁ PE.refl
        {p = 𝟘} ok → inj₂ (PE.refl , 𝟘→𝟘ᵐ _ ok , PE.refl)
    }

  -- Type and usage restrictions that satisfy the full reduction
  -- assumptions are "suitable".

  full-reduction-assumptions-suitable :
    Full-reduction-assumptions TR UR → Suitable-for-full-reduction TR UR
  full-reduction-assumptions-suitable as =
      λ p Σ-ok → case ≡𝟙⊎𝟙≤𝟘 Σ-ok of λ where
        (inj₁ ())
        (inj₂ (_ , 𝟘ᵐ-ok , _)) → 𝟘ᵐ-ok
    where
    open Full-reduction-assumptions _ _ as
