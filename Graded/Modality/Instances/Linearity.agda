------------------------------------------------------------------------
-- A modality for linear types.
------------------------------------------------------------------------

open import Tools.Bool using (T; false)
open import Tools.Level
open import Tools.Sum

open import Graded.Modality.Instances.Zero-one-many false as 𝟘𝟙ω

module Graded.Modality.Instances.Linearity where

open 𝟘𝟙ω renaming (Zero-one-many to Linearity) public

open import Graded.Modality Linearity
import Graded.Mode.Instances.Zero-one.Variant
import Graded.Mode.Instances.Zero-one
import Graded.Modality.Properties
import Graded.FullReduction.Assumptions
import Graded.Usage.Restrictions

open import Definition.Untyped using (BMΣ; 𝕤; 𝕨)
import Definition.Typed.Restrictions
import Graded.Usage.Restrictions

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Nat using (Sequence)
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation

-- A "linear types" modality.

linearityModality : Modality
linearityModality = zero-one-many-modality

private variable
  pᵢ : Sequence Linearity

-- The nr function zero-one-many-has-nr.nr is
-- incomparable to (neither bounded from below nor from above by) the
-- nr function zero-one-many-greatest-star-nr.nr

incomparable :
 let nr₁ = zero-one-many-has-nr .Has-nr.nr
     nr₂ = zero-one-many-greatest-star-nr .Has-nr.nr
  in
  (∃₅ λ p r z s n → ¬ nr₁ p r z s n ≤ nr₂ p r z s n) ×
  (∃₅ λ p r z s n → ¬ nr₂ p r z s n ≤ nr₁ p r z s n)
incomparable =
    (𝟘 , 𝟙 , 𝟘 , 𝟘 , 𝟙 , (λ ()))
  , (𝟘 , 𝟙 , 𝟙 , 𝟘 , 𝟙 , (λ ()))

instance

  -- The "linear types" modality has a well-behaved zero.

  linearity-has-well-behaved-zero :
    Has-well-behaved-zero linearityModality
  linearity-has-well-behaved-zero = zero-one-many-has-well-behaved-zero

instance

  -- The "linear types" modality has grade ω.

  linearity-has-omega :
    Has-omega linearityModality
  linearity-has-omega = zero-one-many-has-omega

open Graded.Modality.Properties linearityModality
open Graded.Mode.Instances.Zero-one.Variant linearityModality

opaque

  -- If 𝟙 is the greatest lower bounds of a sequence then the sequence is
  -- constantly 𝟙

  𝟙-GLB-inv :
    Modality.Greatest-lower-bound zero-one-many-modality 𝟙 pᵢ →
    ∀ i → pᵢ i ≡ 𝟙
  𝟙-GLB-inv 𝟙-glb i = lemma _ (𝟙-glb .proj₁ i)
    where
    lemma : ∀ p → 𝟙 ≤ p → p ≡ 𝟙
    lemma 𝟘 ()
    lemma 𝟙 _ = refl
    lemma ω ()

opaque

  -- If the greatest lower bound of nrᵢ r z s is 𝟘 then z = s 𝟘.

  nrᵢ-GLB-𝟘-inv :
   let 𝕄 = zero-one-many-modality in
    ∀ r z s →
    Modality.Greatest-lower-bound 𝕄 𝟘 (Modality.nrᵢ 𝕄 r z s) →
    z ≡ 𝟘 × s ≡ 𝟘
  nrᵢ-GLB-𝟘-inv r 𝟘 𝟘 (𝟘≤ , _) = refl , refl
  nrᵢ-GLB-𝟘-inv 𝟘 𝟘 𝟙 (𝟘≤ , _) = case 𝟘≤ 1 of λ ()
  nrᵢ-GLB-𝟘-inv 𝟙 𝟘 𝟙 (𝟘≤ , _) = case 𝟘≤ 1 of λ ()
  nrᵢ-GLB-𝟘-inv ω 𝟘 𝟙 (𝟘≤ , _) = case 𝟘≤ 1 of λ ()
  nrᵢ-GLB-𝟘-inv r 𝟘 ω (𝟘≤ , _) = case 𝟘≤ 1 of λ ()
  nrᵢ-GLB-𝟘-inv r 𝟙 s (𝟘≤ , _) = case 𝟘≤ 0 of λ ()
  nrᵢ-GLB-𝟘-inv r ω s (𝟘≤ , _) = case 𝟘≤ 0 of λ ()

opaque

  -- If the greatest lower bound of nrᵢ r z s is 𝟙 then either
  -- r=𝟙, z=𝟙, s≡𝟘
  -- r≡𝟘, z≡𝟙, s≡𝟙

  nrᵢ-GLB-𝟙-inv :
   let 𝕄 = zero-one-many-modality in
    ∀ r z s →
    Modality.Greatest-lower-bound 𝕄 𝟙 (Modality.nrᵢ 𝕄 r z s) →
    r ≡ 𝟙 × z ≡ 𝟙 × s ≡ 𝟘 ⊎ r ≡ 𝟘 × z ≡ 𝟙 × s ≡ 𝟙
  nrᵢ-GLB-𝟙-inv 𝟘 𝟘 𝟘 (𝟙≤ , glb) = case glb 𝟘 (λ i → ≤-reflexive (sym (nrᵢ-𝟘 i))) of λ ()
  nrᵢ-GLB-𝟙-inv 𝟙 𝟘 𝟘 (𝟙≤ , glb) = case glb 𝟘 (λ i → ≤-reflexive (sym (nrᵢ-𝟘 i))) of λ ()
  nrᵢ-GLB-𝟙-inv ω 𝟘 𝟘 (𝟙≤ , glb) = case glb 𝟘 (λ i → ≤-reflexive (sym (nrᵢ-𝟘 i))) of λ ()
  nrᵢ-GLB-𝟙-inv 𝟘 𝟘 𝟙 (𝟙≤ , _) = case 𝟙≤ 0 of λ ()
  nrᵢ-GLB-𝟙-inv 𝟙 𝟘 𝟙 (𝟙≤ , _) = case 𝟙≤ 2 of λ ()
  nrᵢ-GLB-𝟙-inv ω 𝟘 𝟙 (𝟙≤ , _) = case 𝟙≤ 2 of λ ()
  nrᵢ-GLB-𝟙-inv r 𝟘 ω (𝟙≤ , _) = case 𝟙≤ 1 of λ ()
  nrᵢ-GLB-𝟙-inv 𝟘 𝟙 𝟘 (𝟙≤ , _) = case 𝟙≤ 1 of λ ()
  nrᵢ-GLB-𝟙-inv 𝟙 𝟙 𝟘 (𝟙≤ , _) = inj₁ (refl , refl , refl)
  nrᵢ-GLB-𝟙-inv ω 𝟙 𝟘 (𝟙≤ , _) = case 𝟙≤ 1 of λ ()
  nrᵢ-GLB-𝟙-inv 𝟘 𝟙 𝟙 (𝟙≤ , _) = inj₂ (refl , refl , refl)
  nrᵢ-GLB-𝟙-inv 𝟙 𝟙 𝟙 (𝟙≤ , _) = case 𝟙≤ 1 of λ ()
  nrᵢ-GLB-𝟙-inv ω 𝟙 𝟙 (𝟙≤ , _) = case 𝟙≤ 1 of λ ()
  nrᵢ-GLB-𝟙-inv r 𝟙 ω (𝟙≤ , _) = case 𝟙≤ 1 of λ ()
  nrᵢ-GLB-𝟙-inv r ω s (𝟙≤ , _) = case 𝟙≤ 0 of λ ()

opaque

  -- The greatest lower bound of nrᵢ r 𝟙 p is 𝟙 only if
  -- p ≡ 𝟘 and r ≡ 𝟙 or p ≡ 𝟙 and r ≡ 𝟘

  nrᵢ-r𝟙p-GLB-𝟙-inv :
    let 𝕄 = zero-one-many-modality in
      ∀ p r →
    Modality.Greatest-lower-bound 𝕄 𝟙 (Modality.nrᵢ 𝕄 r 𝟙 p) →
    p ≡ 𝟘 × r ≡ 𝟙 ⊎ p ≡ 𝟙 × r ≡ 𝟘
  nrᵢ-r𝟙p-GLB-𝟙-inv p r glb =
    case nrᵢ-GLB-𝟙-inv r 𝟙 p glb of λ where
      (inj₁ (r≡𝟙 , _ , p≡𝟘)) → inj₁ (p≡𝟘 , r≡𝟙)
      (inj₂ (r≡𝟘 , _ , p≡𝟙)) → inj₂ (p≡𝟙 , r≡𝟘)

------------------------------------------------------------------------
-- Properties relating to the Zero-one mode structure

module Zero-one {𝟘ᵐ-allowed : Bool} where

  private
    variant : Mode-variant
    variant = record
      { 𝟘ᵐ-allowed = 𝟘ᵐ-allowed
      ; 𝟘-well-behaved = λ _ → linearity-has-well-behaved-zero
      }

  open Graded.Mode.Instances.Zero-one   variant
  open Definition.Typed.Restrictions    linearityModality
  open Graded.Usage.Restrictions        linearityModality Zero-one-isMode
  open Graded.FullReduction.Assumptions variant

  private variable
    rs : Type-restrictions
    us : Usage-restrictions

  -- Instances of Type-restrictions and Usage-restrictions are suitable
  -- for the full reduction theorem if
  -- * whenever Unitˢ-allowed holds, then Starˢ-sink holds,
  -- * Unitʷ-allowed and Unitʷ-η do not both hold,
  -- * Σˢ-allowed 𝟘 p does not hold, and
  -- * Σˢ-allowed ω p does not hold.

  Suitable-for-full-reduction :
    Type-restrictions → Usage-restrictions → Set
  Suitable-for-full-reduction rs us =
    (Unitˢ-allowed → Starˢ-sink) ×
    (Unitʷ-allowed → ¬ Unitʷ-η) ×
    (∀ p → ¬ Σˢ-allowed 𝟘 p) ×
    (∀ p → ¬ Σˢ-allowed ω p)
    where
    open Type-restrictions rs
    open Usage-restrictions us

  -- Given an instance of Type-restrictions one can create a "suitable"
  -- instance.

  suitable-for-full-reduction :
    Type-restrictions → ∃ λ rs → Suitable-for-full-reduction rs us
  suitable-for-full-reduction {us} rs =
      record rs
        { Unit-allowed = λ where
            𝕨 → Unitʷ-allowed × ¬ Unitʷ-η
            𝕤 → Unitˢ-allowed × Starˢ-sink
        ; ΠΣ-allowed = λ b p q →
            ΠΣ-allowed b p q × (b ≡ BMΣ 𝕤 → p ≡ 𝟙)
        ; []-cong-allowed = λ where
            𝕨 → []-congʷ-allowed × ¬ Unitʷ-η
            𝕤 → ⊥
        ; []-cong→Erased = λ where
            {s = 𝕨} (ok , no-η) →
                ([]-cong→Erased ok .proj₁ , no-η)
              , []-cong→Erased ok .proj₂
              , λ ()
            {s = 𝕤} ()
        ; []-cong→¬Trivial = λ { {s = 𝕨} _ (); {s = 𝕤} () }
        }
    , proj₂
    , proj₂
    , (λ _ → ((λ ()) ∘→ (_$ refl)) ∘→ proj₂)
    , (λ _ → ((λ ()) ∘→ (_$ refl)) ∘→ proj₂)
    where
    open Type-restrictions rs
    open Usage-restrictions us

  -- The full reduction assumptions hold for linearityModality and any
  -- "suitable" Type-restrictions and Usage-restrictions.

  full-reduction-assumptions :
    Suitable-for-full-reduction rs us →
    Full-reduction-assumptions rs us
  full-reduction-assumptions (sink , no-η , ¬𝟘 , ¬ω) = record
    { sink⊎𝟙≤𝟘 = λ where
        {s = 𝕤} ok _         → inj₁ (refl , sink ok)
        {s = 𝕨} _  (inj₁ ())
        {s = 𝕨} ok (inj₂ η)  → ⊥-elim (no-η ok η)
    ; ≡𝟙⊎𝟙≤𝟘   = λ where
        {p = 𝟘} ok → ⊥-elim (¬𝟘 _ ok)
        {p = ω} ok → ⊥-elim (¬ω _ ok)
        {p = 𝟙} _  → inj₁ refl
    }

  -- Type and usage restrictions that satisfy the full reduction
  -- assumptions are "suitable".

  full-reduction-assumptions-suitable :
    Full-reduction-assumptions rs us → Suitable-for-full-reduction rs us
  full-reduction-assumptions-suitable {us = us} as =
      (λ ok → case sink⊎𝟙≤𝟘 ok (inj₁ refl) of λ where
         (inj₁ (_ , sink)) → sink
         (inj₂ ()))
    , (λ ok η → case sink⊎𝟙≤𝟘 ok (inj₂ η) of λ where
         (inj₁ (() , _))
         (inj₂ ()))
    , (λ p Σ-ok → case ≡𝟙⊎𝟙≤𝟘 Σ-ok of λ where
        (inj₁ ())
        (inj₂ (_ , _ , ())))
    , (λ p Σ-ok → case ≡𝟙⊎𝟙≤𝟘 Σ-ok of λ where
        (inj₁ ())
        (inj₂ (() , _)))
    where
    open Full-reduction-assumptions _ _ as
    open Usage-restrictions us

open Zero-one public
