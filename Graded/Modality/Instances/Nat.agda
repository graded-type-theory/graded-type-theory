------------------------------------------------------------------------
-- A modality for the natural numbers.
--
-- Unlike ℕ⊎∞, it is not possible to define an nr function for this
-- modality. The usage rule for natrec using greatest lower bounds
-- is still supported.
------------------------------------------------------------------------

open import Tools.Bool hiding (_∧_; ∧-decreasingˡ; ∧-decreasingʳ)

module Graded.Modality.Instances.Nat where

open import Tools.Empty
open import Tools.Function
open import Tools.Level using (lzero)
import Tools.Nat as N
open import Tools.Nat using (Nat; 1+; 2+; _⊔_; _∸_; Sequence)
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum
import Tools.Reasoning.PartialOrder as RPo

open import Graded.Modality Nat

import Graded.Modality.Properties.Addition
import Graded.Modality.Properties.Greatest-lower-bound
import Graded.Modality.Properties.Has-well-behaved-zero
import Graded.Modality.Properties.Natrec
import Graded.Modality.Properties.PartialOrder
import Graded.Modality.Properties.Subtraction
import Graded.Mode.Instances.Zero-one.Variant
import Graded.Mode.Instances.Zero-one

open import Definition.Untyped Nat
import Definition.Typed.Restrictions
import Graded.FullReduction.Assumptions
import Graded.Usage.Restrictions

private variable
  p q r z z₁ z₂ s s₁ s₂ : Nat
  pᵢ : Sequence Nat

------------------------------------------------------------------------
-- The modality

opaque

  -- A modality structure for Nat.

  Nat-modality : Modality
  Nat-modality = record
    { _+_ = _+_
    ; _·_ = _*_
    ; _∧_ = _⊔_
    ; 𝟘 = 0
    ; 𝟙 = 1
    ; ω = 1
    ; +-·-Semiring = +-*-isSemiring
    ; ∧-Semilattice = ⊔-isSemilattice
    ; ·-distrib-∧ = *-distribˡ-⊔ , *-distribʳ-⊔
    ; +-distrib-∧ = +-distribˡ-⊔ , +-distribʳ-⊔
    ; ω≤𝟙 = refl
    ; ω·+≤ω·ʳ = λ {p} {q} →
      sym (m≥n⇒m⊔n≡m (≤-trans (m≤n+m (q + 0) p)
        (≤-reflexive (sym (+-assoc p q 0)))))
    ; is-𝟘? = _≟ 0
    }
    where
    open N

open Modality Nat-modality

opaque
  unfolding Nat-modality

  instance
    -- The modality has a well-behaved zero.

    Nat-has-well-behaved-zero :
      Has-well-behaved-zero Nat-modality
    Nat-has-well-behaved-zero = record
      { non-trivial = λ ()
      ; zero-product = m*n≡0⇒m≡0∨n≡0 _
      ; +-positiveˡ = λ { {(0)} _ → refl ; {1+ p} () }
      ; ∧-positiveˡ = λ { {(0)} x → refl
                       ; {1+ p} {(0)} ()
                       ; {1+ p} {1+ q} () }
      }
      where
      open N

opaque
  unfolding Nat-modality

  -- The order for the modality is the reverse order for Nat

  ≤⇔≥ : p ≤ q ⇔ q N.≤ p
  ≤⇔≥ = N.m⊔n≡m⇒n≤m ∘→ sym , sym ∘→ N.m≥n⇒m⊔n≡m

opaque

  -- Zero is the greatest element

  ≤0 : ∀ p → p ≤ 0
  ≤0 p = ≤⇔≥ .proj₂ N.z≤n

opaque

  -- There is no least element

  no-least : ¬ (∃ λ p → ∀ q → p ≤ q)
  no-least (p , p≤) =
    case ≤-antisym (p≤ (1+ p)) (≤⇔≥ .proj₂ (N.n≤1+n _)) of λ ()
    where
    open Graded.Modality.Properties.PartialOrder Nat-modality

opaque

  -- 1+ p is less than p

  1+-decreasing : ∀ p → 1+ p ≤ p
  1+-decreasing p = ≤⇔≥ .proj₂ (N.m≤n+m p 1)

------------------------------------------------------------------------
-- Nr functions for Nat

opaque
  unfolding Nat-modality

  -- The modality does not have an nr function

  ¬Nat-Has-nr : ¬ Has-nr Nat-modality
  ¬Nat-Has-nr has-nr = lemma _ (nr-suc {0} {1} {0} {1} {0})
    where
    open Has-nr has-nr
    lemma : ∀ n → n ≢ n ⊔ 1+ (n + 0)
    lemma Nat.zero ()
    lemma (1+ n) eq = lemma n (N.1+-injective eq)

------------------------------------------------------------------------
-- Instances of Full-reduction-assumptions

module _ {𝟘ᵐ-allowed : Bool} where

  open Graded.Mode.Instances.Zero-one.Variant Nat-modality

  private opaque
    unfolding Nat-modality

    variant : Mode-variant
    variant = record
      { 𝟘ᵐ-allowed = 𝟘ᵐ-allowed
      ; 𝟘-well-behaved = λ _ → Nat-has-well-behaved-zero
      }

  open Graded.Mode.Instances.Zero-one   variant
  open Definition.Typed.Restrictions    Nat-modality
  open Graded.Usage.Restrictions        Nat-modality Zero-one-isMode
  open Graded.FullReduction.Assumptions variant

  private variable
    TR : Type-restrictions
    UR : Usage-restrictions

  -- Instances of Type-restrictions Nat-modality and are
  -- suitable for the full reduction theorem if
  -- * whenever Σˢ-allowed m n holds, then m is ⌞ 1 ⌟, or
  --   m is ⌞ 0 ⌟, and 𝟘ᵐ is allowed.

  Suitable-for-full-reduction :
    Type-restrictions → Set
  Suitable-for-full-reduction TRs =
    ∀ p q → Σˢ-allowed p q → p ≡ 1 ⊎ p ≡ 0 × T 𝟘ᵐ-allowed
    where
    open Type-restrictions TRs

  opaque
    unfolding Nat-modality Nat-modality

    -- Given an instance of Type-restrictions ℕ⊎∞-modality one
    -- can create a "suitable" instance.

    suitable-for-full-reduction :
      Type-restrictions →
      ∃ Suitable-for-full-reduction
    suitable-for-full-reduction TR =
      record TR
        { ΠΣ-allowed = λ b p q →
            ΠΣ-allowed b p q × (b ≡ BMΣ 𝕤 → p ≡ 1 ⊎ p ≡ 0 × T 𝟘ᵐ-allowed)
        ; []-cong-allowed = λ s →
            []-cong-allowed s × T 𝟘ᵐ-allowed
        ; []-cong→Erased = λ (hyp₁ , hyp₂) →
            let ok₁ , ok₂ = []-cong→Erased hyp₁
            in  ok₁ , ok₂ , λ { refl → inj₂ (refl , hyp₂) }
        ; []-cong→¬Trivial = λ _ ()
        }
      , λ _ _ (_ , hyp) → hyp refl
      where
      open Type-restrictions TR

  opaque
    unfolding Nat-modality Nat-modality variant

    -- The full reduction assumptions hold for Nat-modality and
    -- any "suitable" instance of Type-restrictions.

    full-reduction-assumptions :
      Suitable-for-full-reduction TR →
      Full-reduction-assumptions TR UR
    full-reduction-assumptions hyp = record
      { sink⊎𝟙≤𝟘 = λ _ _ → inj₂ refl
      ; ≡𝟙⊎𝟙≤𝟘 = λ {p} {q} ok →
          case hyp p q ok of λ where
            (inj₁ p≡1) → inj₁ p≡1
            (inj₂ (p≡0 , ok)) → inj₂ (p≡0 , ok , refl)
      }

  opaque
    unfolding Nat-modality Nat-modality variant

    -- Type and usage restrictions that satisfy the full reduction
    -- assumptions are "suitable".

    full-reduction-assumptions-suitable :
      Full-reduction-assumptions TR UR →
      Suitable-for-full-reduction TR
    full-reduction-assumptions-suitable as p q ok =
      case ≡𝟙⊎𝟙≤𝟘 ok of λ where
        (inj₁ p≡1) → inj₁ p≡1
        (inj₂ (p≡0 , ok , _)) → inj₂ (p≡0 , ok)
      where
      open Full-reduction-assumptions _ _ as

------------------------------------------------------------------------
-- Subtraction

open Graded.Modality.Properties.Addition Nat-modality
open Graded.Modality.Properties.Greatest-lower-bound Nat-modality
open Graded.Modality.Properties.Has-well-behaved-zero Nat-modality
open Graded.Modality.Properties.Natrec Nat-modality
open Graded.Modality.Properties.PartialOrder Nat-modality
open Graded.Modality.Properties.Subtraction Nat-modality

opaque

  unfolding Nat-modality

  -- An inversion lemma for Subtraction

  p-q≤r-inv : p - q ≤ r → p ≤ q × (p ∸ q) ≤ r
  p-q≤r-inv {p} {(0)} {r} p-q≤r =
    sym (N.⊔-identityʳ p) , trans p-q≤r (∧-congˡ (N.+-identityʳ r))
  p-q≤r-inv {(0)} {1+ q} {r} p-q≤r =
    case trans p-q≤r (N.+-suc r q) of λ ()
  p-q≤r-inv {1+ p} {1+ q} {r} p-q≤r =
    let p≤q , p∸q≤r = p-q≤r-inv {p} {q} (N.1+-injective
                        (trans p-q≤r (∧-congˡ (N.+-suc r q))))
    in  (+-monotoneʳ p≤q) , p∸q≤r

opaque
  unfolding Nat-modality

  -- If p ≤ q then p - q ≡ p ∸ q

  p-q≡p∸q : p ≤ q → p - q ≡ (p ∸ q)
  p-q≡p∸q {q} p≤q =
    let p∸q+q≡p = N.m∸n+n≡m (≤⇔≥ .proj₁ p≤q)
    in  ≤⇔≥ .proj₂ (N.≤-reflexive p∸q+q≡p)
         , λ r′ p-q≤r′ → p-q≤r-inv {q = q} p-q≤r′ .proj₂

opaque

  -- The modality supports subtraction with
  --   p - q ≡ p ∸ q whenever p ≤ q
  -- and not defined otherwise

  supports-subtraction : Supports-subtraction
  supports-subtraction {p} {q} {r} p-q≤r =
    let p≤q , _ = p-q≤r-inv {q = q} p-q≤r
        p∸q+q≡p = N.m∸n+n≡m (≤⇔≥ .proj₁ p≤q)
    in  p ∸ q , p-q≡p∸q p≤q


-- An alternative definition of the subtraction relation with
--   p - q ≡ p ∸ q whenever p ≤ q
-- and not defined otherwise

data _-_≡′_ : (p q r : Nat) → Set where
  m-n≡′m∸n : p ≤ q → p - q ≡′ (p ∸ q)

opaque

  -- The two subtraction relations are equivalent.

  -≡↔-≡′ : (p - q ≡ r) ⇔ (p - q ≡′ r)
  -≡↔-≡′ = left , right
    where
    left : p - q ≡ r → p - q ≡′ r
    left p-q≡r@(p-q≤r , _) =
      let p≤q , _ = p-q≤r-inv p-q≤r
      in  case -≡-functional p-q≡r (p-q≡p∸q p≤q) of λ {
            refl →
          m-n≡′m∸n p≤q }
    right : p - q ≡′ r → p - q ≡ r
    right (m-n≡′m∸n p≤q) = p-q≡p∸q p≤q

------------------------------------------------------------------------
-- Greatest-lower-bounds

opaque
  unfolding Nat-modality

  -- An inversion lemma for greatest lower bounds of nrᵢ sequences

  nrᵢ-GLB-inv :
    ∀ r z s → Greatest-lower-bound p (nrᵢ r z s) →
    r ≡ 0 ⊎ (r ≡ 1 × s ≡ 0) ⊎ (z ≡ 0 × s ≡ 0)
  nrᵢ-GLB-inv 0 _ s p-glb = inj₁ refl
  nrᵢ-GLB-inv (1+ 0) _ 0 p-glb = inj₂ (inj₁ (refl , refl))
  nrᵢ-GLB-inv (2+ r) 0 0 p-glb = inj₂ (inj₂ (refl , refl))
  nrᵢ-GLB-inv {p} (2+ r) (1+ z) 0 p-glb =
    case ≤-antisym
           (≤-trans (p-glb .proj₁ (1+ p)) (≤⇔≥ .proj₂ (lemma₃ (1+ p))))
           (1+-decreasing p) of λ ()
    where
    lemma₁ : ∀ p q → p ≢ 0 → 1+ p N.≤ (2+ q) · p
    lemma₁ 0 q p≢0 = ⊥-elim (p≢0 refl)
    lemma₁ (1+ p) q p≢0 = let open N.≤-Reasoning in begin
      2+ p                       ≤⟨ N.s≤s (N.s≤s (N.m≤m+n p (p + q · 1+ p))) ⟩
      1+ (1+ p + (p + q · 1+ p)) ≡˘⟨ cong 1+ (N.+-suc p (p + q · 1+ p)) ⟩
      1+ (p + 1+ (p + q · 1+ p)) ≡⟨⟩
      2+ q · 1+ p ∎
    lemma₂ : ∀ i → nrᵢ (2+ r) (1+ z) 0 i ≢ 0
    lemma₂ 0 ()
    lemma₂ (1+ i) nrᵢ≡0 =
      case N.m*n≡0⇒m≡0∨n≡0 (2+ r) {nrᵢ (2+ r) (1+ z) 0 i} nrᵢ≡0 of λ where
        (inj₁ ())
        (inj₂ x) → lemma₂ i x
    lemma₃ : ∀ i → i N.≤ nrᵢ (2+ r) (1+ z) 0 i
    lemma₃ 0 = N.z≤n
    lemma₃ (1+ i) = let open N.≤-Reasoning in begin
      1+ i                           ≤⟨ N.s≤s (lemma₃ i) ⟩
      1+ (nrᵢ (2+ r) (1+ z) 0 i)     ≤⟨ lemma₁ _ r (lemma₂ i) ⟩
      (2+ r) · nrᵢ (2+ r) (1+ z) 0 i ≡⟨⟩
      nrᵢ (2+ r) (1+ z) 0 (1+ i)     ∎
  nrᵢ-GLB-inv {p} (1+ r) z (1+ s) p-glb =
    case ≤-antisym
           (≤-trans (p-glb .proj₁ (1+ p)) (≤⇔≥ .proj₂ (lemma (1+ p))))
           (1+-decreasing p) of λ ()
    where
    lemma : ∀ i → i N.≤ nrᵢ (1+ r) z (1+ s) i
    lemma 0 = N.z≤n
    lemma (1+ i) = let open N.≤-Reasoning in begin
      1+ i                                    ≤⟨ N.s≤s (lemma i) ⟩
      1+ (nrᵢ (1+ r) z (1+ s) i)              ≤⟨ N.m≤n+m _ _ ⟩
      s + 1+ (nrᵢ (1+ r) z (1+ s) i)          ≡⟨ N.+-suc _ _ ⟩
      (1+ s) + nrᵢ (1+ r) z (1+ s) i          ≡˘⟨ +-congˡ {x = 1+ s} (·-identityˡ _) ⟩
      (1+ s) + 1 · (nrᵢ (1+ r) z (1+ s) i)    ≤⟨ N.+-mono-≤ {x = 1+ s} N.≤-refl
                                                 (N.*-mono-≤ (N.s≤s (N.z≤n {n = r})) N.≤-refl) ⟩
      (1+ s) + (1+ r) · nrᵢ (1+ r) z (1+ s) i ≡⟨⟩
      nrᵢ (1+ r) z (1+ s) (1+ i)              ∎

opaque
  unfolding Nat-modality

  -- The existence of a greatest lower bound to the sequence nrᵢ r z s
  -- is decidable.

  nrᵢ-GLB-dec : ∀ r z s → Dec (∃ λ p → Greatest-lower-bound p (nrᵢ r z s))
  nrᵢ-GLB-dec 0 z s = yes (_ , nrᵢ-𝟘-GLB)
  nrᵢ-GLB-dec r 0 0 = yes (_ , GLB-nrᵢ-𝟘)
  nrᵢ-GLB-dec (1+ 0) (1+ z) 0 = yes (_ , nrᵢ-const-GLB₁)
  nrᵢ-GLB-dec (2+ r) (1+ z) 0 =
    no (λ (_ , p-glb) →
      case nrᵢ-GLB-inv _ _ _ p-glb of λ where
        (inj₁ ())
        (inj₂ (inj₁ ()))
        (inj₂ (inj₂ ())))
  nrᵢ-GLB-dec (1+ r) z (1+ s) =
    no (λ (_ , p-glb) →
      case nrᵢ-GLB-inv _ _ _ p-glb of λ where
        (inj₁ ())
        (inj₂ (inj₁ ()))
        (inj₂ (inj₂ ())))

opaque

  -- There are values for r, z and s such that nrᵢ r z s does not have a
  -- greatest lower bound.

  ¬nrᵢ-GLB : ∃₃ λ r z s → ¬ (∃ λ p → Greatest-lower-bound p (nrᵢ r z s))
  ¬nrᵢ-GLB = 1 , 1 , 1 , λ (_ , glb) →
    case nrᵢ-GLB-inv 1 1 1 glb of λ
      { (inj₁ ()) ; (inj₂ (inj₁ ())) ; (inj₂ (inj₂ ()))}

opaque
  unfolding Nat-modality

  -- The modality has well-behaved greatest lower bounds.

  Nat-has-well-behaved-GLBs :
    Has-well-behaved-GLBs Nat-modality
  Nat-has-well-behaved-GLBs = record
    { +-GLBˡ = +-GLBˡ
    ; ·-GLBˡ = λ {_} {_} {q} → ·-GLBˡ {q = q}
    ; ·-GLBʳ = comm∧·-GLBˡ⇒·-GLBʳ N.*-comm (λ {_} {_} {q} → ·-GLBˡ {q = q})
    ; +nrᵢ-GLB = +nrᵢ-GLB
    }
    where
    +-GLBˡ :
      Greatest-lower-bound p pᵢ →
      Greatest-lower-bound (q + p) (λ i → q + pᵢ i)
    +-GLBˡ {p} {pᵢ} {q} (p≤pᵢ , p-glb) =
      let pᵢ≤p , p-lub = N.+-LUB {k = q} pᵢ (≤⇔≥ .proj₁ ∘→ p≤pᵢ)
                           λ r pᵢ≤r → ≤⇔≥ .proj₁ (p-glb r (≤⇔≥ .proj₂ ∘→ pᵢ≤r))
      in  ≤⇔≥ .proj₂ ∘→ pᵢ≤p , λ r r≤pᵢ → ≤⇔≥ .proj₂ (p-lub r (≤⇔≥ .proj₁ ∘→ r≤pᵢ))
    ·-GLBˡ :
      Greatest-lower-bound p pᵢ →
      Greatest-lower-bound (q · p) (λ i → q · pᵢ i)
    ·-GLBˡ {p} {pᵢ} {q} (p≤pᵢ , p-glb) =
      let pᵢ≤p , p-lub = N.*-LUB {k = q} pᵢ (≤⇔≥ .proj₁ ∘→ p≤pᵢ)
                           λ r pᵢ≤r → ≤⇔≥ .proj₁ (p-glb r (≤⇔≥ .proj₂ ∘→ pᵢ≤r))
      in  ≤⇔≥ .proj₂ ∘→ pᵢ≤p , λ r r≤pᵢ → ≤⇔≥ .proj₂ (p-lub r (≤⇔≥ .proj₁ ∘→ r≤pᵢ))
    open RPo ≤-poset
    +-nrᵢ-GLB′ :
      Greatest-lower-bound p (nrᵢ 0 z₁ s₁) →
      Greatest-lower-bound q (nrᵢ 0 z₂ s₂) →
      ∃ λ r → Greatest-lower-bound r (nrᵢ 0 (z₁ + z₂) (s₁ + s₂)) × p + q ≤ r
    +-nrᵢ-GLB′ {z₁} {s₁} {z₂} {s₂} p-GLB q-GLB =
      case GLB-unique p-GLB nrᵢ-𝟘-GLB of λ {
        refl →
      case GLB-unique q-GLB nrᵢ-𝟘-GLB of λ {
        refl →
      _ , nrᵢ-𝟘-GLB , +-sub-interchangeable-∧ z₁ s₁ z₂ s₂ }}
    +nrᵢ-GLB :
      Greatest-lower-bound p (nrᵢ r z₁ s₁) →
      Greatest-lower-bound q (nrᵢ r z₂ s₂) →
      ∃ λ r′ → Greatest-lower-bound r′ (nrᵢ r (z₁ + z₂) (s₁ + s₂)) × p + q ≤ r′
    +nrᵢ-GLB {p} {r} {z₁} {s₁} {q} {z₂} {s₂}
             p-GLB@(p≤ , p-glb) q-GLB@(q≤ , q-glb) =
      case nrᵢ-GLB-inv r z₁ s₁ p-GLB of λ where
        (inj₁ refl) → +-nrᵢ-GLB′ p-GLB q-GLB
        (inj₂ (inj₁ (refl , refl))) →
          case nrᵢ-GLB-inv r z₂ s₂ q-GLB of λ where
            (inj₁ ())
            (inj₂ (inj₁ (refl , refl))) →
              _ , nrᵢ-const-GLB₁ , +-monotone (p≤ 0) (q≤ 0)
            (inj₂ (inj₂ (refl , refl))) →
              _ , nrᵢ-const-GLB₁ , +-monotone (p≤ 0) (q≤ 0)
        (inj₂ (inj₂ (refl , refl))) →
          case nrᵢ-GLB-inv r z₂ s₂ q-GLB of λ where
            (inj₁ refl) → +-nrᵢ-GLB′ p-GLB q-GLB
            (inj₂ (inj₁ (refl , refl))) →
              _ , nrᵢ-const-GLB₁ , +-monotone (p≤ 0) (q≤ 0)
            (inj₂ (inj₂ (refl , refl))) →
              _ , GLB-const nrᵢ-𝟘
                , +-monotone (p≤ 0) (q≤ 0)
