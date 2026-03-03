------------------------------------------------------------------------
-- Properties of nr and nrᵢ
------------------------------------------------------------------------

open import Graded.Modality

module Graded.Modality.Properties.Natrec
  {a} {M : Set a} (𝕄 : Modality M)
  where

open Modality 𝕄

open import Graded.Modality.Properties.Addition 𝕄
open import Graded.Modality.Properties.Greatest-lower-bound 𝕄
open import Graded.Modality.Properties.Has-well-behaved-zero 𝕄
open import Graded.Modality.Properties.Meet 𝕄
open import Graded.Modality.Properties.Multiplication 𝕄
open import Graded.Modality.Properties.PartialOrder 𝕄

open import Tools.Empty
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Sum
import Tools.Reasoning.PartialOrder ≤-poset as RPo
import Tools.Reasoning.PropositionalEquality as RPe

private variable
  p p′ q q′ r r′ z z′ s s′ n n′ q₁ q₂ : M

------------------------------------------------------------------------
-- Properties of nr functions

module _ ⦃ has-nr : Has-nr _ 𝕄 ⦄ where

  open Has-nr has-nr

  opaque

    nr-𝟘 : nr p r 𝟘 𝟘 𝟘 ≡ 𝟘
    nr-𝟘 {p} {r} = ≤-antisym (nr-zero ≤-refl) (begin
      𝟘                               ≡˘⟨ ·-zeroʳ _ ⟩
      nr p r 𝟘 𝟘 𝟘 · 𝟘               ≤⟨ nr-· ⟩
      nr p r (𝟘 · 𝟘) (𝟘 · 𝟘) (𝟘 · 𝟘) ≡⟨ cong (λ x → nr p r x x x) (·-zeroˡ _) ⟩
      nr p r 𝟘 𝟘 𝟘                    ∎)
      where
      open RPo

------------------------------------------------------------------------
-- Properties of factoring nr functions

module _
  ⦃ has-nr : Has-nr _ 𝕄 ⦄
  ⦃ is-factoring-nr : Is-factoring-nr _ has-nr ⦄ where

  open Is-factoring-nr is-factoring-nr
  open Has-nr has-nr

  opaque

    -- The function nr₂ can be expressed using the function nr

    nr₂≡ : nr₂ p r ≡ nr p r 𝟘 𝟘 𝟙
    nr₂≡ {p} {r} = begin
      nr₂ p r                     ≡˘⟨ +-identityʳ _ ⟩
      nr₂ p r + 𝟘                 ≡˘⟨ +-cong (·-identityʳ _) nr-𝟘 ⟩
      nr₂ p r · 𝟙 + nr p r 𝟘 𝟘 𝟘 ≡˘⟨ nr-factoring ⟩
      nr p r 𝟘 𝟘 𝟙               ∎
      where
      open RPe

  opaque

    -- An inequality for nr₂

    nr₂≤ : nr₂ p r ≤ p + r · nr₂ p r
    nr₂≤ {p} {r} = begin
      nr₂ p r                              ≡⟨ nr₂≡ ⟩
      nr p r 𝟘 𝟘 𝟙                         ≤⟨ nr-suc ⟩
      𝟘 + p · 𝟙 + r · nr p r 𝟘 𝟘 𝟙         ≡⟨ +-identityˡ _ ⟩
      p · 𝟙 + r · nr p r 𝟘 𝟘 𝟙             ≡⟨ +-cong (·-identityʳ _) (·-congˡ nr-factoring) ⟩
      p + r · (nr₂ p r · 𝟙 + nr p r 𝟘 𝟘 𝟘) ≡⟨ +-congˡ (·-congˡ (+-cong (·-identityʳ _) nr-𝟘)) ⟩
      p + r · (nr₂ p r + 𝟘)                ≡⟨ +-congˡ (·-congˡ (+-identityʳ _)) ⟩
      p + r · nr₂ p r                      ∎
      where
      open RPo

------------------------------------------------------------------------
-- "Optimal" nr functions

-- A type used to express that there isn't a greatest factoring nr function.

record No-greatest-factoring-nr : Set a where
  no-eta-equality

  field
    -- There are two nr functions
    has-nr₁ : Has-nr M 𝕄
    has-nr₂ : Has-nr M 𝕄
    -- Both nr functions are factoring
    factoring₁ : Is-factoring-nr M has-nr₁
    factoring₂ : Is-factoring-nr M has-nr₂

  open Has-nr has-nr₁ renaming (nr to nr₁)
  open Has-nr has-nr₂ renaming (nr to nr₂)

  field
    -- There is some input to the nr functions...
    p₀ r₀ z₀ s₀ n₀ : M

    -- ...such that their outputs are not equal...
    nr₁≢nr₂ : nr₁ p₀ r₀ z₀ s₀ n₀ ≢ nr₂ p₀ r₀ z₀ s₀ n₀

    -- ...and there is no other possible output that is greater than both
    -- i.e. no other nr function could be greater than both of them.
    nr≰ : ∀ q → nr₁ p₀ r₀ z₀ s₀ n₀ ≤ q → nr₂ p₀ r₀ z₀ s₀ n₀ ≤ q → ⊥

------------------------------------------------------------------------
-- Sequences used to define one of the usage rules for natrec.

opaque

  -- The sequence nrᵢ r 𝟘 𝟘 is constantly 𝟘.

  nrᵢ-𝟘 : ∀ i → nrᵢ r 𝟘 𝟘 i ≡ 𝟘
  nrᵢ-𝟘 0 = refl
  nrᵢ-𝟘 {r} (1+ i) rewrite nrᵢ-𝟘 {r} i =
    trans (+-identityˡ _) (·-zeroʳ r)

opaque

  -- A monotonicity property for nrᵢ

  nrᵢ-monotone : ∀ i → p ≤ p′ → q ≤ q′ → nrᵢ r p q i ≤ nrᵢ r p′ q′ i
  nrᵢ-monotone 0 p≤ q≤ = p≤
  nrᵢ-monotone (1+ i) p≤ q≤ =
    +-monotone q≤ (·-monotoneʳ (nrᵢ-monotone i p≤ q≤))

opaque

  -- The greatest lower bound of the sequence nrᵢ 𝟘 p q is p ∧ q.

  nrᵢ-𝟘-GLB : Greatest-lower-bound (p ∧ q) (λ i → nrᵢ 𝟘 p q i)
  nrᵢ-𝟘-GLB {p} {q} =
    (λ { 0 → ∧-decreasingˡ p q
       ; (1+ i) → ≤-trans (∧-decreasingʳ p q)
                   (≤-reflexive (sym (lemma i)))}) ,
    λ r r≤ →
      ∧-greatest-lower-bound (r≤ 0)
        (≤-trans (r≤ 1) (≤-reflexive (lemma 0)))
    where
    lemma : ∀ i → nrᵢ 𝟘 p q (1+ i) ≡ q
    lemma i = trans (+-congˡ (·-zeroˡ _)) (+-identityʳ q)

opaque

  -- The greatest lower bound of the sequence nrᵢ r 𝟘 𝟘 is 𝟘.

  GLB-nrᵢ-𝟘 : Greatest-lower-bound 𝟘 (nrᵢ r 𝟘 𝟘)
  GLB-nrᵢ-𝟘 = GLB-const nrᵢ-𝟘

opaque

  -- A property of greatest lower bounds of nrᵢ sequences

  nrᵢ-GLB-≤₀ :
    Greatest-lower-bound p (nrᵢ r z s) → p ≤ z
  nrᵢ-GLB-≤₀ p-glb = p-glb .proj₁ 0

opaque

  -- A property of greatest lower bounds of nrᵢ sequences

  nrᵢ-GLB-≤ :
    ⦃ ok : Has-well-behaved-GLBs _ 𝕄 ⦄ →
    Greatest-lower-bound p (nrᵢ r z s) → p ≤ s + r · p
  nrᵢ-GLB-≤ ⦃ ok ⦄ p-glb =
    +-GLBˡ (·-GLBˡ p-glb) .proj₂ _ (λ i → p-glb .proj₁ (1+ i))
    where
    open Has-well-behaved-GLBs ok

opaque

  -- The greatest lower bound of nrᵢ r p q is the greatest solution to
  -- the "characteristic inequalities" x ≤ p and x ≤ q + r · x.

  ≤-nrᵢ-GLB :
    ∀ {x y} → x ≤ p → x ≤ q + r · x →
    Greatest-lower-bound y (nrᵢ r p q) →
    x ≤ y
  ≤-nrᵢ-GLB {p} {q} {r} {x} le₁ le₂ glb =
    glb .proj₂ _ lemma
    where
    open RPo
    lemma : ∀ i → x ≤ nrᵢ r p q i
    lemma 0 = le₁
    lemma (1+ i) = begin
      x                   ≤⟨ le₂ ⟩
      q + r · x           ≤⟨ +-monotoneʳ (·-monotoneʳ (lemma i)) ⟩
      q + r · nrᵢ r p q i ≡⟨⟩
      nrᵢ r p q (1+ i)    ∎

opaque

  -- nrᵢ distributes over addition in a certain sense.

  nrᵢ-+ : ∀ i → nrᵢ r (p + p′) (q + q′) i ≡ nrᵢ r p q i + nrᵢ r p′ q′ i
  nrᵢ-+ 0 = refl
  nrᵢ-+ {r} {p} {p′} {q} {q′} (1+ i) = begin
    (q + q′) + r · nrᵢ r (p + p′) (q + q′) i         ≡⟨ +-congˡ (·-congˡ (nrᵢ-+ i)) ⟩
    (q + q′) + r · (nrᵢ r p q i + nrᵢ r p′ q′ i)     ≡⟨ +-congˡ (·-distribˡ-+ _ _ _) ⟩
    (q + q′) + r · nrᵢ r p q i + r · nrᵢ r p′ q′ i   ≡⟨ +-sub-interchangeable-+ _ _ _ _ ⟩
    (q + r · nrᵢ r p q i) + (q′ + r · nrᵢ r p′ q′ i) ∎
    where
    open RPe

opaque

  -- Multiplication right-distributes over nrᵢ.

  ·-distribʳ-nrᵢ : ∀ i → nrᵢ r p q i · p′ ≡ nrᵢ r (p · p′) (q · p′) i
  ·-distribʳ-nrᵢ 0 = refl
  ·-distribʳ-nrᵢ {r} {p} {q} {p′} (1+ i) = begin
    (q + r · nrᵢ r p q i) · p′             ≡⟨ ·-distribʳ-+ _ _ _ ⟩
    q · p′ + (r · nrᵢ r p q i) · p′        ≡⟨ +-congˡ (·-assoc _ _ _) ⟩
    q · p′ + r · nrᵢ r p q i · p′          ≡⟨ +-congˡ (·-congˡ (·-distribʳ-nrᵢ i)) ⟩
    q · p′ + r · nrᵢ r (p · p′) (q · p′) i ∎
    where
    open RPe

opaque

  -- The sequence nrᵢ 𝟙 z 𝟘 is constantly equal to z

  nrᵢ-const₁ : ∀ i → nrᵢ 𝟙 z 𝟘 i ≡ z
  nrᵢ-const₁ 0 = refl
  nrᵢ-const₁ {z} (1+ i) = begin
    𝟘 + 𝟙 · nrᵢ 𝟙 z 𝟘 i ≡⟨ +-identityˡ _ ⟩
    𝟙 · nrᵢ 𝟙 z 𝟘 i     ≡⟨ ·-identityˡ _ ⟩
    nrᵢ 𝟙 z 𝟘 i         ≡⟨ nrᵢ-const₁ i ⟩
    z                    ∎
    where
    open RPe

opaque

  -- The greatest lower bound of the sequence nrᵢ 𝟙 z 𝟘 is z

  nrᵢ-const-GLB₁ : Greatest-lower-bound z (nrᵢ 𝟙 z 𝟘)
  nrᵢ-const-GLB₁ = GLB-const (λ i → trans (nrᵢ-const₁ i) (sym (nrᵢ-const₁ 0)))

opaque

  -- The sequence nrᵢ 𝟘 p p is constantly equal to p

  nrᵢ-const₂ : ∀ i → nrᵢ 𝟘 p p i ≡ p
  nrᵢ-const₂ 0 = refl
  nrᵢ-const₂ {p} (1+ i) = begin
    p + 𝟘 · nrᵢ 𝟘 p p i ≡⟨ +-congˡ (·-zeroˡ _) ⟩
    p + 𝟘               ≡⟨ +-identityʳ _ ⟩
    p                   ∎
    where
    open RPe

opaque

  -- The greatest lower bound of the sequence nrᵢ 𝟘 p p is p

  nrᵢ-const-GLB₂ : Greatest-lower-bound p (nrᵢ 𝟘 p p)
  nrᵢ-const-GLB₂ = GLB-const (λ i → trans (nrᵢ-const₂ i) (sym (nrᵢ-const₂ 0)))

opaque

  -- The greatest lower bound of nrᵢ r 𝟙 p is not 𝟘.
  -- That is, the natural number argument is never erased for the
  -- usage rule using greatest lower bounds.

  nrᵢ-natrec-not-erased :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero M 𝕄 ⦄ →
    Greatest-lower-bound q (nrᵢ r 𝟙 p) → q ≢ 𝟘
  nrᵢ-natrec-not-erased (q≤ , _) refl = 𝟘≰𝟙 (q≤ 0)

------------------------------------------------------------------------
-- Relating nr functions and greatest lower bounds of nrᵢ sequences

opaque

  -- If the modality has an nr function it computes a lower
  -- bound for nrᵢ sequences.

  nr→nrᵢ-LB :
    (has-nr : Has-nr _ 𝕄) →
    let open Has-nr has-nr in
    ∀ i → nr p r z s 𝟘 ≤ nrᵢ r z s i
  nr→nrᵢ-LB has-nr = lemma
    where
    open Has-nr has-nr
    open RPo
    lemma : ∀ i → nr p r z s 𝟘 ≤ nrᵢ r z s i
    lemma 0 = nr-zero ≤-refl
    lemma {p} {r} {z} {s} (1+ i) = begin
      nr p r z s 𝟘 ≤⟨ nr-suc ⟩
      s + p · 𝟘 + r · nr p r z s 𝟘 ≡⟨ +-congˡ (+-congʳ (·-zeroʳ _)) ⟩
      s + 𝟘 + r · nr p r z s 𝟘     ≡⟨ +-congˡ (+-identityˡ _) ⟩
      s + r · nr p r z s 𝟘         ≤⟨ +-monotoneʳ (·-monotoneʳ (lemma i)) ⟩
      s + r · nrᵢ r z s i          ≡⟨⟩
      nrᵢ r z s (1+ i)             ∎

opaque

  -- A bound for factoring nr functions
  --
  -- Certain factoring nr functions are bounded by the grade used in the
  -- usage rule for natrec using greatest lower bounds.
  --
  -- The assumption that nr₂ p r ≤ 𝟙 can, in some sense, be interpreted
  -- as the natural number being used (at least) 𝟙 time(s) by matching.

  factoring-nr-≤ :
    (has-nr : Has-nr _ 𝕄)
    (is-factoring-nr : Is-factoring-nr _ has-nr) →
    Greatest-lower-bound q₁ (nrᵢ r 𝟙 p) →
    Greatest-lower-bound q₂ (nrᵢ r z s) →
    let open Has-nr has-nr
        open Is-factoring-nr is-factoring-nr in
    nr₂ p r ≤ 𝟙 →
    nr p r z s n ≤ q₁ · n + q₂
  factoring-nr-≤ {q₁} {r} {p} {q₂} {z} {s} {n}
    has-nr is-factoring-nr q₁-glb q₂-glb nr₂≤𝟙 =
    begin
      nr p r z s n               ≈⟨ nr-factoring ⟩
      nr₂ p r · n + nr p r z s 𝟘 ≤⟨ +-monotone (·-monotoneˡ (q₁-glb .proj₂ _ lemma))
                                      (q₂-glb .proj₂ _ (nr→nrᵢ-LB has-nr)) ⟩
      q₁ · n + q₂                ∎
    where
    open Has-nr has-nr
    open Is-factoring-nr is-factoring-nr
    open RPo
    lemma : ∀ i → nr₂ p r ≤ nrᵢ r 𝟙 p i
    lemma 0 = nr₂≤𝟙
    lemma (1+ i) = begin
      nr₂ p r             ≤⟨ nr₂≤ ⦃ has-nr = has-nr ⦄ ⦃ is-factoring-nr = is-factoring-nr ⦄ ⟩
      p + r · nr₂ p r     ≤⟨ +-monotoneʳ (·-monotoneʳ (lemma i)) ⟩
      p + r · nrᵢ r 𝟙 p i ≡⟨⟩
      nrᵢ r 𝟙 p (1+ i)    ∎

-- When all nrᵢ sequences has greater lower bounds an nr function can
-- be defined.

module _
  ⦃ ok : Has-well-behaved-GLBs _ 𝕄 ⦄
  (has-glb : ∀ r z s → ∃ λ p → Greatest-lower-bound p (nrᵢ r z s))
  where

  private

    -- The nr function

    nr₃ : M → M → M → M
    nr₃ r z s = has-glb r z s .proj₁

    nr₂ : M → M → M
    nr₂ p r = nr₃ r 𝟙 p

    nr : M → M → M → M → M → M
    nr p r z s n = nr₂ p r · n + nr₃ r z s

    opaque

      -- nr₂ p r is not equal to 𝟘 if the modality has a
      -- well-behaved zero.

      nr₂≢𝟘 : ⦃ 𝟘-well-behaved : Has-well-behaved-zero M 𝕄 ⦄ →
              nr₂ p r ≢ 𝟘
      nr₂≢𝟘 {p} {r} nr₂≡𝟘 =
        𝟘≰𝟙 (≤-trans (≤-reflexive (sym nr₂≡𝟘))
          (has-glb r 𝟙 p .proj₂ .proj₁ 0))

  opaque

    -- If a greatest lower bound exists for all nrᵢ sequences,
    -- the modality supports GLB for natrec and has a well-behaved zero
    -- a factoring nr function can be defined for the modality.

    nrᵢ-GLB→nr : Has-nr M 𝕄
    nrᵢ-GLB→nr = record
      { nr = nr
      ; nr-monotone = λ z≤z′ s≤s′ n≤n′ →
          +-monotone (·-monotoneʳ n≤n′) (nr₃-monotone z≤z′ s≤s′)
      ; nr-· = nr-·
      ; nr-+ = nr-+
      ; nr-positive = nr-positive
      ; nr-zero = nr-zero
      ; nr-suc = nr-suc
      }
      where
      open Has-well-behaved-GLBs ok
      open RPo
      nr₃-monotone : z ≤ z′ → s ≤ s′ → nr₃ r z s ≤ nr₃ r z′ s′
      nr₃-monotone {z} {z′} {s} {s′} {r} z≤z′ s≤s′ =
        has-glb r z′ s′ .proj₂ .proj₂ _ (λ i →
          ≤-trans (has-glb r z s .proj₂ .proj₁ i)
            (nrᵢ-monotone i z≤z′ s≤s′))
      nr₃-· : nr₃ r z s · q ≡ nr₃ r (z · q) (s · q)
      nr₃-· {r} {z} {s} {q} =
        let p , nr-GLB = has-glb r z s
            p′ , nrq-GLB′ = has-glb r (z · q) (s · q)
            nrq-GLB = ·-GLBʳ {q = q} nr-GLB
        in  GLB-unique (GLB-congˡ ·-distribʳ-nrᵢ nrq-GLB) nrq-GLB′
      nr-· : nr p r z s n · q ≤ nr p r (z · q) (s · q) (n · q)
      nr-· {p} {r} {z} {s} {n} {q} = begin
        nr p r z s n · q                          ≡⟨⟩
        (nr₂ p r · n + nr₃ r z s) · q             ≡⟨ ·-distribʳ-+ _ _ _ ⟩
        (nr₂ p r · n) · q + nr₃ r z s · q         ≡⟨ +-cong (·-assoc _ _ _) nr₃-· ⟩
        nr₂ p r · (n · q) + nr₃ r (z · q) (s · q) ≡⟨⟩
        nr p r (z · q) (s · q) (n · q)            ∎
      nr₃-+ : nr₃ r z s + nr₃ r z′ s′ ≤ nr₃ r (z + z′) (s + s′)
      nr₃-+ {r} {z} {s} {z′} {s′} =
        let p , nr-GLB = has-glb r z s
            p′ , nr′-GLB = has-glb r z′ s′
            q , nr+-GLB = has-glb r (z + z′) (s + s′)
            q′ , nr+-GLB′ , p+p′≤q′ = +nrᵢ-GLB nr-GLB nr′-GLB
        in  ≤-trans p+p′≤q′ (≤-reflexive (GLB-unique nr+-GLB′ nr+-GLB))
      nr-+ : nr p r z s n + nr p r z′ s′ n′ ≤ nr p r (z + z′) (s + s′) (n + n′)
      nr-+ {p} {r} {z} {s} {n} {z′} {s′} {n′} = begin
        nr p r z s n + nr p r z′ s′ n′ ≡⟨⟩
        (nr₂ p r · n + nr₃ r z s) + nr₂ p r · n′ + nr₃ r z′ s′ ≡⟨ +-sub-interchangeable-+ _ _ _ _ ⟩
        (nr₂ p r · n + nr₂ p r · n′) + nr₃ r z s + nr₃ r z′ s′ ≡˘⟨ +-congʳ (·-distribˡ-+ _ _ _) ⟩
        nr₂ p r · (n + n′) + nr₃ r z s + nr₃ r z′ s′           ≤⟨ +-monotoneʳ nr₃-+ ⟩
        nr₂ p r · (n + n′) + nr₃ r (z + z′) (s + s′)           ≡⟨⟩
        nr p r (z + z′) (s + s′) (n + n′)                      ∎
      nr₃-positive :
        ⦃ 𝟘-well-behaved : Has-well-behaved-zero M 𝕄 ⦄ →
        nr₃ r z s ≡ 𝟘 → z ≡ 𝟘 × s ≡ 𝟘
      nr₃-positive {r} {z} {s} nr₃≡𝟘 =
        let q , q≤ , _ = has-glb r z s
            z≡𝟘 = 𝟘≮ (≤-trans (≤-reflexive (sym nr₃≡𝟘)) (q≤ 0))
            s≡𝟘 = 𝟘≮ $ begin
                   𝟘           ≡˘⟨ nr₃≡𝟘 ⟩
                   q           ≤⟨ q≤ 1 ⟩
                   nrᵢ r z s 1 ≡⟨⟩
                   s + r · z   ≡⟨ +-congˡ (·-congˡ z≡𝟘) ⟩
                   s + r · 𝟘   ≡⟨ +-congˡ (·-zeroʳ _) ⟩
                   s + 𝟘       ≡⟨ +-identityʳ _ ⟩
                   s ∎
        in  z≡𝟘 , s≡𝟘
      nr-positive :
        ⦃ 𝟘-well-behaved : Has-well-behaved-zero M 𝕄 ⦄ →
        nr p r z s n ≡ 𝟘 → z ≡ 𝟘 × s ≡ 𝟘 × n ≡ 𝟘
      nr-positive nr≡𝟘 =
        let nr₂·n≡𝟘 , nr₃≡𝟘 = +-positive nr≡𝟘
            z≡𝟘 , s≡𝟘 = nr₃-positive nr₃≡𝟘
            n≡𝟘 = case zero-product nr₂·n≡𝟘 of λ where
                    (inj₁ nr₂≡𝟘) → ⊥-elim (nr₂≢𝟘 nr₂≡𝟘)
                    (inj₂ n≡𝟘) → n≡𝟘
        in  z≡𝟘 , s≡𝟘 , n≡𝟘
      nr-zero : n ≤ 𝟘 → nr p r z s n ≤ z
      nr-zero {n} {p} {r} {z} {s} n≤𝟘 = begin
        nr p r z s n            ≡⟨⟩
        nr₂ p r · n + nr₃ r z s ≤⟨ +-monotoneˡ (·-monotoneʳ n≤𝟘) ⟩
        nr₂ p r · 𝟘 + nr₃ r z s ≡⟨ +-congʳ (·-zeroʳ _) ⟩
        𝟘 + nr₃ r z s           ≡⟨ +-identityˡ _ ⟩
        nr₃ r z s               ≤⟨ has-glb r z s .proj₂ .proj₁ 0 ⟩
        z                       ∎
      nr-suc : nr p r z s n ≤ s + p · n + r · nr p r z s n
      nr-suc {p} {r} {z} {s} {n} =
        let q , q-glb = has-glb r z s
            q′ , q′-glb = has-glb r 𝟙 p
        in  begin
          nr p r z s n                         ≡⟨⟩
          q′ · n + q                           ≤⟨ +-monotone (·-monotoneˡ (nrᵢ-GLB-≤ q′-glb)) (nrᵢ-GLB-≤ q-glb) ⟩
          (p + r · q′) · n + (s + r · q)       ≡⟨ +-congʳ (·-distribʳ-+ _ _ _) ⟩
          (p · n + (r · q′) · n) + (s + r · q) ≡⟨ +-sub-interchangeable-+ _ _ _ _ ⟩
          (p · n + s) + (r · q′) · n + r · q   ≡⟨ +-cong (+-comm _ _) (+-congʳ (·-assoc _ _ _)) ⟩
          (s + p · n) + r · q′ · n + r · q     ≡˘⟨ +-congˡ (·-distribˡ-+ _ _ _) ⟩
          (s + p · n) + r · (q′ · n + q)       ≡⟨ +-assoc _ _ _ ⟩
          s + p · n + r · (q′ · n + q)         ≡⟨⟩
          s + p · n + r · nr p r z s n         ∎

  opaque
    unfolding nrᵢ-GLB→nr

    -- If the modality additionally has a well-behaved zero, then the
    -- nr function given by nrᵢ-GLB→nr is factoring

    nrᵢ-GLB→nr-factoring :
      ⦃ 𝟘-well-behaved : Has-well-behaved-zero M 𝕄 ⦄ →
      Is-factoring-nr M nrᵢ-GLB→nr
    nrᵢ-GLB→nr-factoring = record
      { nr₂ = nr₂
      ; nr₂≢𝟘 = nr₂≢𝟘
      ; nr-factoring = nr-factoring
      }
      where
      open RPe
      nr-factoring : nr p r z s n ≡ nr₂ p r · n + nr p r z s 𝟘
      nr-factoring {p} {r} {z} {s} {n} = begin
        nr p r z s n                            ≡⟨⟩
        nr₂ p r · n + nr₃ r z s                 ≡˘⟨ +-congˡ (+-identityˡ _) ⟩
        nr₂ p r · n + (𝟘 + nr₃ r z s)           ≡˘⟨ +-congˡ (+-congʳ (·-zeroʳ _)) ⟩
        nr₂ p r · n + (nr₂ p r · 𝟘 + nr₃ r z s) ≡⟨⟩
        nr₂ p r · n + nr p r z s 𝟘              ∎

  opaque
    unfolding nrᵢ-GLB→nr

    -- The nr function given by nrᵢ-GLB→nr is the
    -- greatest factoring nr function given a certain assumption.
    --
    -- The assumption that nr₂ p r ≤ 𝟙 can, in some sense, be
    -- interpreted as the natural number being used (at least) 𝟙 times
    -- by matching.
    --
    -- Note that without this assumption there might not be a greatest
    -- factoring nr function.
    -- See Graded.Modality.Instances.Nat-plus-infinity.no-greatest-nrₑ

    nrᵢ-GLB→nr-factoring-greatest :
      (has-nr : Has-nr _ 𝕄)
      (is-factoring-nr : Is-factoring-nr _ has-nr) →
      ∀ p r z s n →
      Is-factoring-nr.nr₂ is-factoring-nr p r ≤ 𝟙 →
      Has-nr.nr has-nr p r z s n ≤ Has-nr.nr nrᵢ-GLB→nr p r z s n
    nrᵢ-GLB→nr-factoring-greatest has-nr is-factoring-nr p r z s n nr₂≤𝟙 =
      begin
        nr″ p r z s n ≤⟨ factoring-nr-≤ has-nr is-factoring-nr
                           (has-glb r 𝟙 p .proj₂) (has-glb r z s .proj₂)
                           nr₂≤𝟙 ⟩
        has-glb r 𝟙 p .proj₁ · n + has-glb r z s .proj₁ ≡⟨⟩
        nr′ p r z s n ∎
      where
      open Has-nr nrᵢ-GLB→nr renaming (nr to nr′)
      open Has-nr has-nr renaming (nr to nr″)
      open RPo
