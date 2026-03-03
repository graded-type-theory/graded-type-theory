------------------------------------------------------------------------
-- Modes
------------------------------------------------------------------------

import Graded.Modality

module Graded.Mode
  {a b} {M : Set a}
  (Mode : Set b)
  (open Graded.Modality M)
  (𝕄 : Modality)
  where

open Modality 𝕄

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄

open import Tools.Algebra Mode
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Level
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PropositionalEquality
import Tools.Reasoning.PartialOrder
open import Tools.Relation
open import Tools.Sum

private variable
  n : Nat
  m m′ m₁ m₂ m₃ m₄ : Mode
  p q r z s : M
  γ δ η : Conₘ _
  A : Set _

------------------------------------------------------------------------
-- Mode vectors

-- Mode vectors of the given length.

Mode-vector : Nat → Set b
Mode-vector n = Fin n → Mode

private variable
  ms : Mode-vector _

-- An empty mode vector.

nilᵐ : Mode-vector 0
nilᵐ ()

-- Adds an element to the mode vector.

consᵐ : Mode → Mode-vector n → Mode-vector (1+ n)
consᵐ m ρ x0     = m
consᵐ m ρ (x +1) = ρ x

-- The head of the mode vector.

headᵐ : Mode-vector (1+ n) → Mode
headᵐ ρ = ρ x0

-- The tail of the mode vector.

tailᵐ : Mode-vector (1+ n) → Mode-vector n
tailᵐ ρ x = ρ (x +1)

-- A constant vector.

replicateᵐ : Mode → Mode-vector n
replicateᵐ m _ = m

------------------------------------------------------------------------
-- The algebraic structure of modes

record IsMode : Set (a ⊔ b) where

  no-eta-equality

  infixr 45 _·ᵐ_

  field
    -- A mode structure consists of a binary operation (multiplication)
    -- and two special elements as well as translation functions between
    -- grades and modes with certain properties.

    _·ᵐ_ : Op₂ Mode
    𝟘ᵐ 𝟙ᵐ : Mode

    ⌞_⌟ : M → Mode
    ⌜_⌝ : Mode → M

    -- _·ᵐ_ forms an idempotent, commutative monoid with 𝟙ᵐ as the unit

    ·ᵐ-IdempotentCommutativeMonoid :
      IsIdempotentCommutativeMonoid _·ᵐ_ 𝟙ᵐ

    -- 𝟘ᵐ is the zero for _·ᵐ_
    ·ᵐ-zero : Zero 𝟘ᵐ _·ᵐ_

    -- The function ⌞_⌟ is a left inverse of ⌜_⌝.
    ⌞⌜⌝⌟ : ∀ m → ⌞ ⌜ m ⌝ ⌟ ≡ m

    -- ⌜_⌝ commutes with _·_/_·ᵐ_.
    ⌜·ᵐ⌝ : ∀ m₁ → ⌜ m₁ ·ᵐ m₂ ⌝ ≡ ⌜ m₁ ⌝ · ⌜ m₂ ⌝

    -- ⌞_⌟ commutes with _·ᵐ_/_·_.
    ⌞⌟·ᵐ : ⌞ p ⌟ ·ᵐ ⌞ q ⌟ ≡ ⌞ p · q ⌟

    -- A form of commutativity.
    ⌜⌝-·-comm : ∀ m → ⌜ m ⌝ · p ≡ p · ⌜ m ⌝

    -- The value p · ⌜ ⌞ p ⌟ ⌝ is equal to p.
    ·⌜⌞⌟⌝ : p · ⌜ ⌞ p ⌟ ⌝ ≡ p

    -- If p ≤ q and q ≤ ⌜ m ⌝ · q then p ≤ ⌜ m ⌝ · p.
    ≤⌜⌝· : p ≤ q → q ≤ ⌜ m ⌝ · q → p ≤ ⌜ m ⌝ · p

    -- It is decidable whether a mode is equal to 𝟘ᵐ.
    is-𝟘ᵐ? : (m : Mode) → Dec (m ≡ 𝟘ᵐ)

  -- The property of being a trivial mode structure

  Trivialᵐ : Set b
  Trivialᵐ = 𝟙ᵐ ≡ 𝟘ᵐ

  field

    -- If the mode structure is not trivial then ⌜ 𝟘ᵐ ⌝ ≡ 𝟘.
    ⌜𝟘ᵐ⌝ : ¬ Trivialᵐ → ⌜ 𝟘ᵐ ⌝ ≡ 𝟘

  -- The multiplication induces an order relation for modes

  infix 10 _≤ᵐ_

  _≤ᵐ_ : Rel Mode b
  m ≤ᵐ m′ = m′ ≡ m′ ·ᵐ m

  -- Scaling a mode by a grade

  infixr 45 _ᵐ·_

  _ᵐ·_ : Mode → M → Mode
  m ᵐ· p = m ·ᵐ ⌞ p ⌟

  field

    -- Addition and meet are decreasing in a certain sense.
    -- See ⌞⌟·ᵐ⌞+⌟ˡ and ⌞⌟·ᵐ⌞∧⌟ˡ for alternative characterizations of
    -- this property.

    ⌞+⌟-decreasingˡ : ⌞ p + q ⌟ ≤ᵐ ⌞ p ⌟
    ⌞∧⌟-decreasingˡ : ⌞ p ∧ q ⌟ ≤ᵐ ⌞ p ⌟

  ----------------------------------------------------------------------
  -- Exporting some algebraic properties

  open IsIdempotentCommutativeMonoid ·ᵐ-IdempotentCommutativeMonoid
    public
    using ()
    renaming (
              assoc to ·ᵐ-assoc;
              comm to ·ᵐ-comm;
              ∙-cong to ·ᵐ-cong;
              ∙-congˡ to ·ᵐ-congˡ;
              ∙-congʳ to ·ᵐ-congʳ;
              identity to ·ᵐ-identity;
              identityˡ to ·ᵐ-identityˡ;
              identityʳ to ·ᵐ-identityʳ;
              idem to ·ᵐ-idem
              )
  opaque

    ·ᵐ-zeroˡ : LeftZero 𝟘ᵐ _·ᵐ_
    ·ᵐ-zeroˡ = ·ᵐ-zero .proj₁

  opaque

    ·ᵐ-zeroʳ : RightZero 𝟘ᵐ _·ᵐ_
    ·ᵐ-zeroʳ = ·ᵐ-zero .proj₂

  ----------------------------------------------------------------------
  -- Congruence properties

  opaque

    -- The function ⌜_⌝ preserves "equality".

    ⌜⌝-cong : m₁ ≡ m₂ → ⌜ m₁ ⌝ ≡ ⌜ m₂ ⌝
    ⌜⌝-cong refl = refl

  opaque

    -- The function ⌞_⌟ preserves "equality".

    ⌞⌟-cong : p ≡ q → ⌞ p ⌟ ≡ ⌞ q ⌟
    ⌞⌟-cong refl = refl

  opaque

    -- The function ⌜ ⌞_⌟ ⌝ preserves "equality".

    ⌜⌞⌟⌝-cong : p ≡ q → ⌜ ⌞ p ⌟ ⌝ ≡ ⌜ ⌞ q ⌟ ⌝
    ⌜⌞⌟⌝-cong refl = refl

  opaque

    -- The function m ᵐ·_ preserves "equality".

    ᵐ·-congˡ : p ≡ q → m ᵐ· p ≡ m ᵐ· q
    ᵐ·-congˡ = ·ᵐ-congˡ ∘→ ⌞⌟-cong

  opaque

    -- The function _ᵐ· p preserves "equality".

    ᵐ·-congʳ : m₁ ≡ m₂ → m₁ ᵐ· p ≡ m₂ ᵐ· p
    ᵐ·-congʳ = ·ᵐ-congʳ

  ----------------------------------------------------------------------
  -- Properties of 𝟘ᵐ and 𝟙ᵐ.

  opaque

    -- If the mode structure is trivial, then every value is equal
    -- to 𝟘.

    ≡𝟘ᵐ : Trivialᵐ → m ≡ 𝟘ᵐ
    ≡𝟘ᵐ {m} 𝟙≡𝟘 = begin
      m        ≡˘⟨ ·ᵐ-identityˡ _ ⟩
      𝟙ᵐ ·ᵐ m  ≡⟨ ·ᵐ-congʳ 𝟙≡𝟘 ⟩
      𝟘ᵐ ·ᵐ m  ≡⟨ ·ᵐ-zeroˡ _ ⟩
      𝟘ᵐ       ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- If the mode structure is trivial, then _≡_ is trivial.

    ≡-trivialᵐ : Trivialᵐ → m₁ ≡ m₂
    ≡-trivialᵐ {m₁} {m₂} 𝟙≡𝟘 = begin
      m₁   ≡⟨ ≡𝟘ᵐ 𝟙≡𝟘 ⟩
      𝟘ᵐ   ≡˘⟨ ≡𝟘ᵐ 𝟙≡𝟘 ⟩
      m₂   ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- It is decidable if the mode structure is trivial

    trivialᵐ? : Dec Trivialᵐ
    trivialᵐ? = is-𝟘ᵐ? 𝟙ᵐ

  opaque

    -- ⌞ 𝟙 ⌟ is equal to 𝟙ᵐ.

    ⌞𝟙⌟ : ⌞ 𝟙 ⌟ ≡ 𝟙ᵐ
    ⌞𝟙⌟ = begin
      ⌞ 𝟙 ⌟               ≡˘⟨ ·ᵐ-identityʳ _ ⟩
      ⌞ 𝟙 ⌟ ·ᵐ 𝟙ᵐ         ≡˘⟨ ·ᵐ-congˡ (⌞⌜⌝⌟ _) ⟩
      ⌞ 𝟙 ⌟ ·ᵐ ⌞ ⌜ 𝟙ᵐ ⌝ ⌟ ≡⟨ ⌞⌟·ᵐ ⟩
      ⌞ 𝟙 · ⌜ 𝟙ᵐ ⌝ ⌟      ≡⟨ ⌞⌟-cong (·-identityˡ _) ⟩
      ⌞ ⌜ 𝟙ᵐ ⌝ ⌟          ≡⟨ ⌞⌜⌝⌟ _ ⟩
      𝟙ᵐ                  ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- ⌜ 𝟙ᵐ ⌝ is equal to 𝟙.

    ⌜𝟙ᵐ⌝ : ⌜ 𝟙ᵐ ⌝ ≡ 𝟙
    ⌜𝟙ᵐ⌝ = begin
      ⌜ 𝟙ᵐ ⌝                   ≡˘⟨ ·-identityˡ _ ⟩
      𝟙 · ⌜ 𝟙ᵐ ⌝               ≡˘⟨ ·-congʳ ·⌜⌞⌟⌝ ⟩
      (𝟙 · ⌜ ⌞ 𝟙 ⌟ ⌝) · ⌜ 𝟙ᵐ ⌝ ≡⟨ ·-assoc _ _ _ ⟩
      𝟙 · ⌜ ⌞ 𝟙 ⌟ ⌝ · ⌜ 𝟙ᵐ ⌝   ≡˘⟨ ·-congˡ (⌜·ᵐ⌝ _) ⟩
      𝟙 · ⌜ ⌞ 𝟙 ⌟ ·ᵐ 𝟙ᵐ ⌝      ≡⟨ ·-congˡ (⌜⌝-cong (·ᵐ-identityʳ _)) ⟩
      𝟙 · ⌜ ⌞ 𝟙 ⌟ ⌝            ≡⟨ ·⌜⌞⌟⌝ ⟩
      𝟙                        ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- If the mode structure is trivial, then ⌜ m ⌝ ≡ 𝟙.

    ⌜⌝-trivialᵐ : Trivialᵐ → ⌜ m ⌝ ≡ 𝟙
    ⌜⌝-trivialᵐ {m} trivial = begin
      ⌜ m ⌝  ≡⟨ ⌜⌝-cong (≡-trivialᵐ trivial) ⟩
      ⌜ 𝟙ᵐ ⌝ ≡⟨ ⌜𝟙ᵐ⌝ ⟩
      𝟙      ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- The structure is either trivial or ⌜_⌝ maps 𝟘ᵐ to 𝟘.

    trivial⊎⌜𝟘ᵐ⌝≡𝟘 : Trivialᵐ ⊎ ⌜ 𝟘ᵐ ⌝ ≡ 𝟘
    trivial⊎⌜𝟘ᵐ⌝≡𝟘 =
      case trivialᵐ? of λ where
        (yes trivial) → inj₁ trivial
        (no ¬trivial) → inj₂ (⌜𝟘ᵐ⌝ ¬trivial)

  opaque

    -- If two modes are equal under the assumption that ⌜ 𝟘ᵐ ⌝ ≡ 𝟘
    -- then they are always equal.

    ⌜𝟘ᵐ⌝≡𝟘→ : (⌜ 𝟘ᵐ ⌝ ≡ 𝟘 → m₁ ≡ m₂) → m₁ ≡ m₂
    ⌜𝟘ᵐ⌝≡𝟘→ p = case trivial⊎⌜𝟘ᵐ⌝≡𝟘 of λ where
      (inj₁ trivial) → ≡-trivialᵐ trivial
      (inj₂ ⌜𝟘ᵐ⌝≡𝟘) → p ⌜𝟘ᵐ⌝≡𝟘

  opaque

    -- If the mode structure is trivial then ⌜ 𝟘ᵐ ⌝ ≡ 𝟙.

    ⌜𝟘ᵐ⌝′ : Trivialᵐ → ⌜ 𝟘ᵐ ⌝ ≡ 𝟙
    ⌜𝟘ᵐ⌝′ 𝟙ᵐ≡𝟘ᵐ = begin
      ⌜ 𝟘ᵐ ⌝ ≡˘⟨ ⌜⌝-cong 𝟙ᵐ≡𝟘ᵐ ⟩
      ⌜ 𝟙ᵐ ⌝ ≡⟨ ⌜𝟙ᵐ⌝ ⟩
      𝟙 ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- ⌞ 𝟘 ⌟ is equal to 𝟘ᵐ.

    ⌞𝟘⌟ : ⌞ 𝟘 ⌟ ≡ 𝟘ᵐ
    ⌞𝟘⌟ = ⌜𝟘ᵐ⌝≡𝟘→ (λ ⌜𝟘ᵐ⌝≡𝟘 → begin
      ⌞ 𝟘 ⌟      ≡˘⟨ ⌞⌟-cong ⌜𝟘ᵐ⌝≡𝟘 ⟩
      ⌞ ⌜ 𝟘ᵐ ⌝ ⌟ ≡⟨ ⌞⌜⌝⌟ 𝟘ᵐ ⟩
      𝟘ᵐ         ∎)
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- If ⌜ m ⌝ ≡ 𝟘 then m ≡ 𝟘ᵐ.

    ⌜⌝≡𝟘→ : ⌜ m ⌝ ≡ 𝟘 → m ≡ 𝟘ᵐ
    ⌜⌝≡𝟘→ {m} ⌜m⌝≡𝟘 = begin
      m         ≡˘⟨ ⌞⌜⌝⌟ _ ⟩
      ⌞ ⌜ m ⌝ ⌟ ≡⟨ ⌞⌟-cong ⌜m⌝≡𝟘 ⟩
      ⌞ 𝟘 ⌟     ≡⟨ ⌞𝟘⌟ ⟩
      𝟘ᵐ        ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- If ⌜ 𝟘ᵐ ⌝ ≢ 𝟘 then the mode structure is trivial

    ⌜𝟘ᵐ⌝≢𝟘→ : ⌜ 𝟘ᵐ ⌝ ≢ 𝟘 → Trivialᵐ
    ⌜𝟘ᵐ⌝≢𝟘→ ⌜𝟘ᵐ⌝≢𝟘 = case trivial⊎⌜𝟘ᵐ⌝≡𝟘 of λ where
      (inj₁ trivial) → trivial
      (inj₂ ⌜𝟘ᵐ⌝≡𝟘) → ⊥-elim (⌜𝟘ᵐ⌝≢𝟘 ⌜𝟘ᵐ⌝≡𝟘)

  opaque

    -- If the modality is trivial then the mode structure is trivial

    Trivial→Trivialᵐ : Trivial → Trivialᵐ
    Trivial→Trivialᵐ 𝟙≡𝟘 = begin
      𝟙ᵐ    ≡˘⟨ ⌞𝟙⌟ ⟩
      ⌞ 𝟙 ⌟ ≡⟨ ⌞⌟-cong 𝟙≡𝟘 ⟩
      ⌞ 𝟘 ⌟ ≡⟨ ⌞𝟘⌟ ⟩
      𝟘ᵐ    ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- A form of eliminator for the cases of a mode mapping to 𝟘 or not.

    ⌜⌝≡𝟘-elim :
      ∀ {ℓ} (P : Mode → Set ℓ) →
      ∀ m →
      (Trivial → P m′) →
      (¬ Trivialᵐ → m ≡ 𝟘ᵐ → P 𝟘ᵐ) →
      (⌜ m ⌝ ≢ 𝟘 → P m) →
      P m
    ⌜⌝≡𝟘-elim P m ok₁ ok₂ ok₃ =
      case is-𝟘? ⌜ m ⌝ of λ where
        (yes m≡𝟘) →
          case trivialᵐ? of λ where
            (yes 𝟙ᵐ≡𝟘ᵐ) →
              subst P (≡-trivialᵐ 𝟙ᵐ≡𝟘ᵐ)
                (ok₁ (trans (sym (⌜⌝-trivialᵐ 𝟙ᵐ≡𝟘ᵐ)) m≡𝟘))
            (no 𝟙ᵐ≢𝟘ᵐ) →
              subst P (sym (⌜⌝≡𝟘→ m≡𝟘)) (ok₂ 𝟙ᵐ≢𝟘ᵐ (⌜⌝≡𝟘→ m≡𝟘))
        (no m≢𝟘) →
          ok₃ m≢𝟘

  ----------------------------------------------------------------------
  -- Properties of the order relation

  opaque

    -- The order relation is reflexive

    ≤ᵐ-refl : Reflexive _≤ᵐ_
    ≤ᵐ-refl = sym (·ᵐ-idem _)

  opaque

    -- The order relation is antisymmetric

    ≤ᵐ-antisym : Antisymmetric _≡_ _≤ᵐ_
    ≤ᵐ-antisym {i = m₁} {j = m₂} m₁≤m₂ m₂≤m₁ = begin
      m₁       ≡⟨ m₂≤m₁ ⟩
      m₁ ·ᵐ m₂ ≡⟨ ·ᵐ-comm _ _ ⟩
      m₂ ·ᵐ m₁ ≡˘⟨ m₁≤m₂ ⟩
      m₂       ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- The order relation is transitive

    ≤ᵐ-trans : Transitive _≤ᵐ_
    ≤ᵐ-trans {i = m₁} {j = m₂} {k = m₃} m₁≤m₂ m₂≤m₃ = begin
      m₃               ≡⟨ m₂≤m₃ ⟩
      m₃ ·ᵐ m₂         ≡⟨ ·ᵐ-congˡ m₁≤m₂ ⟩
      m₃ ·ᵐ m₂ ·ᵐ m₁   ≡˘⟨ ·ᵐ-assoc _ _ _ ⟩
      (m₃ ·ᵐ m₂) ·ᵐ m₁ ≡˘⟨ ·ᵐ-congʳ m₂≤m₃ ⟩
      m₃ ·ᵐ m₁         ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- The relation _≤ᵐ_ is a non-strict ordering relation.

    ≤ᵐ-reflexive : m₁ ≡ m₂ → m₁ ≤ᵐ m₂
    ≤ᵐ-reflexive refl = ≤ᵐ-refl

  opaque

    -- _≤ᵐ_ is a preorder relation

    ≤ᵐ-preorder : IsPreorder _≡_ _≤ᵐ_
    ≤ᵐ-preorder = record
      { isEquivalence = isEquivalence
      ; reflexive     = ≤ᵐ-reflexive
      ; trans         = ≤ᵐ-trans
      }

  opaque

    -- _≤ᵐ_ is a partial ordering relation

    ≤ᵐ-partial : IsPartialOrder _≡_ _≤ᵐ_
    ≤ᵐ-partial = record
      { isPreorder = ≤ᵐ-preorder
      ; antisym    = ≤ᵐ-antisym
      }

  -- (Mode, _≤ᵐ_) is a poset

  ≤ᵐ-poset : Poset b b b
  ≤ᵐ-poset = record
    { Carrier        = Mode
    ; _≈_            = _≡_
    ; _≤_            = _≤ᵐ_
    ; isPartialOrder = ≤ᵐ-partial
    }


  -- Reasoning combinators for _≤ᵐ_
  module ≤ᵐ-reasoning = Tools.Reasoning.PartialOrder ≤ᵐ-poset

  opaque

    -- 𝟙ᵐ is the least mode

    𝟙ᵐ≤ : 𝟙ᵐ ≤ᵐ m
    𝟙ᵐ≤ = sym (·ᵐ-identityʳ _)


  opaque

    -- 𝟘ᵐ is the greatest mode

    ≤𝟘ᵐ : m ≤ᵐ 𝟘ᵐ
    ≤𝟘ᵐ = sym (·ᵐ-zeroˡ _)

  opaque

    -- Addition is decreasing in a certain sense

    ⌞+⌟-decreasingʳ : ⌞ p + q ⌟ ≤ᵐ ⌞ q ⌟
    ⌞+⌟-decreasingʳ {p} {q} = begin
      ⌞ p + q ⌟ ≡⟨ ⌞⌟-cong (+-comm _ _) ⟩
      ⌞ q + p ⌟ ≤⟨ ⌞+⌟-decreasingˡ ⟩
      ⌞ q ⌟     ∎
      where
      open ≤ᵐ-reasoning

  opaque

    -- Meet is decreasing in a certain sense

    ⌞∧⌟-decreasingʳ : ⌞ p ∧ q ⌟ ≤ᵐ ⌞ q ⌟
    ⌞∧⌟-decreasingʳ {p} {q} = begin
      ⌞ p ∧ q ⌟ ≡⟨ ⌞⌟-cong (∧-comm _ _) ⟩
      ⌞ q ∧ p ⌟ ≤⟨ ⌞∧⌟-decreasingˡ ⟩
      ⌞ q ⌟     ∎
      where
      open ≤ᵐ-reasoning


  ----------------------------------------------------------------------
  -- Properties of _·ᵐ_ and _ᵐ·_

  opaque

    -- A form of associativity.

    ·ᵐ-ᵐ·-assoc : ∀ m₁ → (m₁ ·ᵐ m₂) ᵐ· p ≡ m₁ ·ᵐ (m₂ ᵐ· p)
    ·ᵐ-ᵐ·-assoc m₁ = ·ᵐ-assoc m₁ _ _

  opaque

    -- A form of associativity.

    ᵐ·-·-assoc : ∀ m → (m ᵐ· p) ᵐ· q ≡ m ᵐ· (p · q)
    ᵐ·-·-assoc {p} {q} m = begin
      (m ᵐ· p) ᵐ· q         ≡⟨⟩
      (m ·ᵐ ⌞ p ⌟) ·ᵐ ⌞ q ⌟ ≡⟨ ·ᵐ-assoc _ _ _ ⟩
      m ·ᵐ ⌞ p ⌟ ·ᵐ ⌞ q ⌟   ≡⟨ ·ᵐ-congˡ ⌞⌟·ᵐ ⟩
      m ·ᵐ ⌞ p · q ⌟        ≡⟨⟩
      m ᵐ· (p · q)          ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- A form of associativity.

    ·ᵐ-·-assoc : ∀ m₁ → ⌜ m₁ ·ᵐ m₂ ⌝ · p ≡ ⌜ m₁ ⌝ · ⌜ m₂ ⌝ · p
    ·ᵐ-·-assoc {m₂ = m₂} {p = p} m₁ = begin
      ⌜ m₁ ·ᵐ m₂ ⌝ · p       ≡⟨ ·-congʳ (⌜·ᵐ⌝ m₁) ⟩
      (⌜ m₁ ⌝ · ⌜ m₂ ⌝) · p  ≡⟨ ·-assoc _ _ _ ⟩
      ⌜ m₁ ⌝ · ⌜ m₂ ⌝ · p    ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- A form of associativity.

    ·ᵐ-·ᶜ-assoc : ∀ m₁ → ⌜ m₁ ·ᵐ m₂ ⌝ ·ᶜ γ ≈ᶜ ⌜ m₁ ⌝ ·ᶜ ⌜ m₂ ⌝ ·ᶜ γ
    ·ᵐ-·ᶜ-assoc {γ = ε}     m₁ = ε
    ·ᵐ-·ᶜ-assoc {γ = _ ∙ _} m₁ = ·ᵐ-·ᶜ-assoc m₁ ∙ ·ᵐ-·-assoc m₁

  opaque

    -- Multiplication is idempotent for ⌜ m ⌝.

    ·-idem-⌜⌝ : ∀ m → ⌜ m ⌝ · ⌜ m ⌝ ≡ ⌜ m ⌝
    ·-idem-⌜⌝ m = begin
      ⌜ m ⌝ · ⌜ m ⌝ ≡˘⟨ ⌜·ᵐ⌝ _ ⟩
      ⌜ m ·ᵐ m ⌝    ≡⟨ ⌜⌝-cong (·ᵐ-idem _) ⟩
      ⌜ m ⌝         ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- A variant of the above

    ·-idem-⌜⌝′ : ⌜ m ⌝ · ⌜ m ⌝ · p ≡ ⌜ m ⌝ · p
    ·-idem-⌜⌝′ {m} {p} = begin
      ⌜ m ⌝ · ⌜ m ⌝ · p   ≡˘⟨ ·-assoc _ _ _ ⟩
      (⌜ m ⌝ · ⌜ m ⌝) · p ≡⟨ ·-congʳ (·-idem-⌜⌝ _) ⟩
      ⌜ m ⌝ · p           ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- A form of idempotence for _ᵐ·_.

    ⌞⌟·ᵐ-idem : ⌞ p ⌟ ᵐ· p ≡ ⌞ p ⌟
    ⌞⌟·ᵐ-idem = ·ᵐ-idem _

  opaque

    -- The function _ᵐ· p is idempotent.

    ᵐ·-idem : ∀ m → (m ᵐ· p) ᵐ· p ≡ m ᵐ· p
    ᵐ·-idem {p} m = begin
      (m ᵐ· p) ᵐ· p         ≡⟨⟩
      (m ·ᵐ ⌞ p ⌟) ·ᵐ ⌞ p ⌟ ≡⟨ ·ᵐ-assoc _ _ _ ⟩
      m ·ᵐ ⌞ p ⌟ ·ᵐ ⌞ p ⌟   ≡⟨ ·ᵐ-congˡ (·ᵐ-idem _) ⟩
      m ·ᵐ ⌞ p ⌟            ≡⟨⟩
      m ᵐ· p                ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- 𝟘 is a right zero for _ᵐ·_.

    ᵐ·-zeroʳ : ∀ m → m ᵐ· 𝟘 ≡ 𝟘ᵐ
    ᵐ·-zeroʳ m = begin
      m ᵐ· 𝟘     ≡⟨⟩
      m ·ᵐ ⌞ 𝟘 ⌟ ≡⟨ ·ᵐ-congˡ ⌞𝟘⌟ ⟩
      m ·ᵐ 𝟘ᵐ    ≡⟨ ·ᵐ-zeroʳ _ ⟩
      𝟘ᵐ         ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- 𝟘ᵐ is a left zero for _ᵐ·_.

    ᵐ·-zeroˡ : 𝟘ᵐ ᵐ· p ≡ 𝟘ᵐ
    ᵐ·-zeroˡ = ·ᵐ-zeroˡ _

  opaque

    -- 𝟙ᵐ is a kind of left identity for _ᵐ·_.

    ᵐ·-identityˡ : 𝟙ᵐ ᵐ· p ≡ ⌞ p ⌟
    ᵐ·-identityˡ = ·ᵐ-identityˡ _

  opaque

    -- 𝟙 is a right identity for _ᵐ·_.

    ᵐ·-identityʳ : m ᵐ· 𝟙 ≡ m
    ᵐ·-identityʳ {m} = begin
      m ᵐ· 𝟙     ≡⟨⟩
      m ·ᵐ ⌞ 𝟙 ⌟ ≡⟨ ·ᵐ-congˡ ⌞𝟙⌟ ⟩
      m ·ᵐ 𝟙ᵐ    ≡⟨ ·ᵐ-identityʳ _ ⟩
      m          ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- Multiplication of modes is increasing

    ·ᵐ-increasingˡ : m₁ ≤ᵐ m₂ ·ᵐ m₁
    ·ᵐ-increasingˡ {m₁} {m₂} = begin
      m₂ ·ᵐ m₁         ≡˘⟨ ·ᵐ-congˡ (·ᵐ-idem _) ⟩
      m₂ ·ᵐ m₁ ·ᵐ m₁   ≡˘⟨ ·ᵐ-assoc _ _ _ ⟩
      (m₂ ·ᵐ m₁) ·ᵐ m₁ ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- Multiplication of modes is increasing

    ·ᵐ-increasingʳ : m₁ ≤ᵐ m₁ ·ᵐ m₂
    ·ᵐ-increasingʳ {m₁} {m₂} = begin
      m₁       ≤⟨ ·ᵐ-increasingˡ ⟩
      m₂ ·ᵐ m₁ ≡⟨ ·ᵐ-comm _ _ ⟩
      m₁ ·ᵐ m₂ ∎
      where
      open ≤ᵐ-reasoning

  opaque

    -- Scaling by a grade is increasing

    ᵐ·-increasing : m ≤ᵐ m ᵐ· p
    ᵐ·-increasing = ·ᵐ-increasingʳ

  opaque

    -- _·ᵐ m is monotone with respect to _≤ᵐ_.

    ·ᵐ-monotoneˡ : m₁ ≤ᵐ m₂ → m₁ ·ᵐ m ≤ᵐ m₂ ·ᵐ m
    ·ᵐ-monotoneˡ {m₁} {m₂} {m} m₁≤m₂ = begin
        m₂ ·ᵐ m                ≡⟨ ·ᵐ-cong m₁≤m₂ (sym (·ᵐ-idem _)) ⟩
        (m₂ ·ᵐ m₁) ·ᵐ m ·ᵐ m   ≡˘⟨ ·ᵐ-assoc _ _ _ ⟩
        ((m₂ ·ᵐ m₁) ·ᵐ m) ·ᵐ m ≡⟨ ·ᵐ-congʳ (·ᵐ-assoc _ _ _) ⟩
        (m₂ ·ᵐ m₁ ·ᵐ m) ·ᵐ m   ≡⟨ ·ᵐ-congʳ (·ᵐ-congˡ (·ᵐ-comm _ _)) ⟩
        (m₂ ·ᵐ m ·ᵐ m₁) ·ᵐ m   ≡˘⟨ ·ᵐ-congʳ (·ᵐ-assoc _ _ _) ⟩
        ((m₂ ·ᵐ m) ·ᵐ m₁) ·ᵐ m ≡⟨ ·ᵐ-assoc _ _ _ ⟩
        (m₂ ·ᵐ m) ·ᵐ m₁ ·ᵐ m   ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- m ·ᵐ_ is monotone with respect to _≤ᵐ_.

    ·ᵐ-monotoneʳ : m₁ ≤ᵐ m₂ → m ·ᵐ m₁ ≤ᵐ m ·ᵐ m₂
    ·ᵐ-monotoneʳ {m₁} {m₂} {m} m₁≤m₂ = begin
        m ·ᵐ m₁ ≡⟨ ·ᵐ-comm _ _ ⟩
        m₁ ·ᵐ m ≤⟨ ·ᵐ-monotoneˡ m₁≤m₂ ⟩
        m₂ ·ᵐ m ≡⟨ ·ᵐ-comm _ _ ⟩
        m ·ᵐ m₂ ∎
      where
      open ≤ᵐ-reasoning

  opaque

    -- _·ᵐ_ is monotone with respect to _≤ᵐ_.

    ·ᵐ-monotone : m₁ ≤ᵐ m₂ → m₃ ≤ᵐ m₄ → m₁ ·ᵐ m₃ ≤ᵐ m₂ ·ᵐ m₄
    ·ᵐ-monotone le₁ le₂ = ≤ᵐ-trans (·ᵐ-monotoneʳ le₂) (·ᵐ-monotoneˡ le₁)

  opaque

    -- _ᵐ· p is monotone with respect to _≤ᵐ_.

    ᵐ·-monotoneˡ : m₁ ≤ᵐ m₂ → m₁ ᵐ· p ≤ᵐ m₂ ᵐ· p
    ᵐ·-monotoneˡ = ·ᵐ-monotoneˡ

  opaque

    -- ⌞ p · q ⌟ is greater than ⌞ p ⌟

    ⌞·⌟-increasingˡ : ⌞ p ⌟ ≤ᵐ ⌞ p · q ⌟
    ⌞·⌟-increasingˡ {p} {q} = begin
      ⌞ p ⌟          ≤⟨ ·ᵐ-increasingʳ ⟩
      ⌞ p ⌟ ·ᵐ ⌞ q ⌟ ≡⟨ ⌞⌟·ᵐ ⟩
      ⌞ p · q ⌟      ∎
      where
      open ≤ᵐ-reasoning

  opaque

    -- ⌞ p · q ⌟ is greater than ⌞ p ⌟

    ⌞·⌟-increasingʳ : ⌞ q ⌟ ≤ᵐ ⌞ p · q ⌟
    ⌞·⌟-increasingʳ {q} {p} = begin
      ⌞ q ⌟          ≤⟨ ·ᵐ-increasingˡ ⟩
      ⌞ p ⌟ ·ᵐ ⌞ q ⌟ ≡⟨ ⌞⌟·ᵐ ⟩
      ⌞ p · q ⌟      ∎
      where
      open ≤ᵐ-reasoning

  opaque

    -- A lemma relating ⌞_⌟, _·_, ⌜_⌝ and _ᵐ·_.

    ⌞⌜⌝·⌟ : ∀ m → ⌞ ⌜ m ⌝ · p ⌟ ≡ m ᵐ· p
    ⌞⌜⌝·⌟ {p} m = begin
      ⌞ ⌜ m ⌝ · p ⌟      ≡˘⟨ ⌞⌟·ᵐ ⟩
      ⌞ ⌜ m ⌝ ⌟ ·ᵐ ⌞ p ⌟ ≡⟨ ·ᵐ-congʳ (⌞⌜⌝⌟ m) ⟩
      m ·ᵐ ⌞ p ⌟         ≡⟨⟩
      m ᵐ· p             ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- ⌞_⌟ commutes with _· q/_ᵐ· q.

    ⌞⌟ᵐ· : ⌞ p ⌟ ᵐ· q ≡ ⌞ p · q ⌟
    ⌞⌟ᵐ· = ⌞⌟·ᵐ

  opaque

    -- ⌜_⌝ commutes, in a certain sense, with _·_/_ᵐ·_.

    ⌜ᵐ·⌝ : ∀ m → ⌜ m ᵐ· p ⌝ ≡ ⌜ m ⌝ · ⌜ ⌞ p ⌟ ⌝
    ⌜ᵐ·⌝ = ⌜·ᵐ⌝

  opaque

    ⌜⌞⌟⌝· : ⌜ ⌞ p ⌟ ⌝ · p ≡ p
    ⌜⌞⌟⌝· {p} = begin
      ⌜ ⌞ p ⌟ ⌝ · p ≡⟨ ⌜⌝-·-comm _ ⟩
      p · ⌜ ⌞ p ⌟ ⌝ ≡⟨ ·⌜⌞⌟⌝ ⟩
      p             ∎
      where
      open Tools.Reasoning.PropositionalEquality


  opaque

    -- If m₁ ·ᵐ m₂ ≡ 𝟙ᵐ then m₁ ≡ 𝟙ᵐ

    ·ᵐ-𝟙ˡ : m₁ ·ᵐ m₂ ≡ 𝟙ᵐ → m₁ ≡ 𝟙ᵐ
    ·ᵐ-𝟙ˡ {m₁} {m₂} m₁m₂≡𝟙ᵐ = flip ≤ᵐ-antisym 𝟙ᵐ≤ $ begin
      m₁       ≤⟨ ·ᵐ-increasingʳ ⟩
      m₁ ·ᵐ m₂ ≡⟨ m₁m₂≡𝟙ᵐ ⟩
      𝟙ᵐ       ∎
      where
      open ≤ᵐ-reasoning

  opaque

    -- If m₁ ·ᵐ m₂ ≡ 𝟙ᵐ then m₂ ≡ 𝟙ᵐ

    ·ᵐ-𝟙ʳ : m₁ ·ᵐ m₂ ≡ 𝟙ᵐ → m₂ ≡ 𝟙ᵐ
    ·ᵐ-𝟙ʳ m₁m₂≡𝟙ᵐ = ·ᵐ-𝟙ˡ (trans (·ᵐ-comm _ _) m₁m₂≡𝟙ᵐ)

  opaque

    -- If m ≤ᵐ 𝟙ᵐ then m ≡ 𝟙ᵐ.

    ≤ᵐ-𝟙ᵐ→ : m ≤ᵐ 𝟙ᵐ → m ≡ 𝟙ᵐ
    ≤ᵐ-𝟙ᵐ→ = ·ᵐ-𝟙ʳ ∘→ sym

  opaque

    -- If m₁ ·ᵐ m₂ ≢ 𝟘ᵐ then m₁ ≢ 𝟘ᵐ

    ·ᵐ-𝟘ˡ : m₁ ·ᵐ m₂ ≢ 𝟘ᵐ → m₁ ≢ 𝟘ᵐ
    ·ᵐ-𝟘ˡ m₁m₂≢𝟘 refl = m₁m₂≢𝟘 (·ᵐ-zeroˡ _)

  opaque

    -- If m₁ ·ᵐ m₂ ≢ 𝟘ᵐ then m₂ ≢ 𝟘ᵐ

    ·ᵐ-𝟘ʳ : m₁ ·ᵐ m₂ ≢ 𝟘ᵐ → m₂ ≢ 𝟘ᵐ
    ·ᵐ-𝟘ʳ m₁m₂≢𝟘 refl = m₁m₂≢𝟘 (·ᵐ-zeroʳ _)

  opaque

    -- If ⌜ m₁ ·ᵐ m₂ ⌝ ≢ 𝟘 then ⌜ m₁ ⌝ ≢ 𝟘

    ⌜⌝-·ᵐ-𝟘ˡ : ⌜ m₁ ·ᵐ m₂ ⌝ ≢ 𝟘 → ⌜ m₁ ⌝ ≢ 𝟘
    ⌜⌝-·ᵐ-𝟘ˡ {m₁} {m₂} ≢𝟘 m₁≡𝟘 = ≢𝟘 $ begin
      ⌜ m₁ ·ᵐ m₂ ⌝    ≡⟨ ⌜·ᵐ⌝ _ ⟩
      ⌜ m₁ ⌝ · ⌜ m₂ ⌝ ≡⟨ ·-congʳ m₁≡𝟘 ⟩
      𝟘 · ⌜ m₂ ⌝      ≡⟨ ·-zeroˡ _ ⟩
      𝟘               ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- If ⌜ m₁ ·ᵐ m₂ ⌝ ≢ 𝟘 then ⌜ m₂ ⌝ ≢ 𝟘

    ⌜⌝-·ᵐ-𝟘ʳ : ⌜ m₁ ·ᵐ m₂ ⌝ ≢ 𝟘 → ⌜ m₂ ⌝ ≢ 𝟘
    ⌜⌝-·ᵐ-𝟘ʳ {m₁} {m₂} ≢𝟘 m₂≡𝟘 =
      ⌜⌝-·ᵐ-𝟘ˡ (subst (λ m → ⌜ m ⌝ ≢ 𝟘) (·ᵐ-comm _ _) ≢𝟘) m₂≡𝟘

  opaque

    -- A lemma relating _ᵐ·_ and _·ᵐ_.

    ᵐ·-·ᵐ-comm : ∀ m₁ → (m₁ ᵐ· p) ·ᵐ m₂ ≡ (m₁ ·ᵐ m₂) ᵐ· p
    ᵐ·-·ᵐ-comm {p} {m₂} m₁ = begin
      (m₁ ᵐ· p) ·ᵐ m₂     ≡⟨⟩
      (m₁ ·ᵐ ⌞ p ⌟) ·ᵐ m₂ ≡⟨ ·ᵐ-assoc _ _ _ ⟩
      m₁ ·ᵐ ⌞ p ⌟ ·ᵐ m₂   ≡⟨ ·ᵐ-congˡ (·ᵐ-comm _ _) ⟩
      m₁ ·ᵐ m₂ ·ᵐ ⌞ p ⌟   ≡˘⟨ ·ᵐ-assoc _ _ _ ⟩
      (m₁ ·ᵐ m₂) ·ᵐ ⌞ p ⌟ ≡⟨⟩
      (m₁ ·ᵐ m₂) ᵐ· p     ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- Another lemma relating _ᵐ·_ and _·ᵐ_.

    ᵐ·-·ᵐ : ∀ m → (m ᵐ· p) ·ᵐ m ≡ m ᵐ· p
    ᵐ·-·ᵐ {p} m = begin
      (m ᵐ· p) ·ᵐ m ≡⟨ ᵐ·-·ᵐ-comm m ⟩
      (m ·ᵐ m) ᵐ· p ≡⟨ ᵐ·-congʳ (·ᵐ-idem _) ⟩
      m ᵐ· p        ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- A lemma relating _ᵐ·_, _·ᵐ_ and ⌞_⌟.

    ᵐ·-·ᵐ-⌞⌟ : ∀ m → (m ᵐ· p) ·ᵐ ⌞ p ⌟ ≡ m ᵐ· p
    ᵐ·-·ᵐ-⌞⌟ m = ᵐ·-idem m

  opaque

    -- The value p · ⌜ m ᵐ· p ⌝ is equivalent to p · ⌜ m ⌝.

    ·⌜ᵐ·⌝ : ∀ m → p · ⌜ m ᵐ· p ⌝ ≡ p · ⌜ m ⌝
    ·⌜ᵐ·⌝ {p} m = begin
      p · ⌜ m ᵐ· p ⌝          ≡⟨ ·-congˡ (⌜ᵐ·⌝ _) ⟩
      p · ⌜ m ⌝ · ⌜ ⌞ p ⌟ ⌝   ≡⟨ ·-congˡ (⌜⌝-·-comm _) ⟩
      p · ⌜ ⌞ p ⌟ ⌝ · ⌜ m ⌝   ≡˘⟨ ·-assoc _ _ _ ⟩
      (p · ⌜ ⌞ p ⌟ ⌝) · ⌜ m ⌝ ≡⟨ ·-congʳ ·⌜⌞⌟⌝ ⟩
      p · ⌜ m ⌝               ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- Multiplicating into an addition is absorbing in a certain sense

    ⌞⌟·ᵐ⌞+⌟ˡ : ⌞ p ⌟ ·ᵐ ⌞ p + q ⌟ ≡ ⌞ p ⌟
    ⌞⌟·ᵐ⌞+⌟ˡ = sym ⌞+⌟-decreasingˡ

  opaque

    -- Multiplicating into an addition is absorbing in a certain sense

    ⌞⌟·ᵐ⌞+⌟ʳ : ⌞ q ⌟ ·ᵐ ⌞ p + q ⌟ ≡ ⌞ q ⌟
    ⌞⌟·ᵐ⌞+⌟ʳ = sym ⌞+⌟-decreasingʳ

  opaque

    -- Multiplicating into a meet is absorbing in a certain sense

    ⌞⌟·ᵐ⌞∧⌟ˡ : ⌞ p ⌟ ·ᵐ ⌞ p ∧ q ⌟ ≡ ⌞ p ⌟
    ⌞⌟·ᵐ⌞∧⌟ˡ = sym ⌞∧⌟-decreasingˡ

  opaque

    -- Multiplicating into a meet is absorbing in a certain sense

    ⌞⌟·ᵐ⌞∧⌟ʳ : ⌞ q ⌟ ·ᵐ ⌞ p ∧ q ⌟ ≡ ⌞ q ⌟
    ⌞⌟·ᵐ⌞∧⌟ʳ = sym ⌞∧⌟-decreasingʳ

  opaque

    -- The function ⌞_⌟ respects the grade order

    ⌞⌟-monotone : p ≤ q → ⌞ p ⌟ ≤ᵐ ⌞ q ⌟
    ⌞⌟-monotone {p} {q} p≤q = begin
      ⌞ q ⌟              ≡˘⟨ ⌞⌟·ᵐ⌞∧⌟ʳ ⟩
      ⌞ q ⌟ ·ᵐ ⌞ p ∧ q ⌟ ≡˘⟨ ·ᵐ-congˡ (⌞⌟-cong p≤q) ⟩
      ⌞ q ⌟ ·ᵐ ⌞ p ⌟     ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- The function ⌜_⌝ is injective

    ⌜⌝-injective : ⌜ m₁ ⌝ ≡ ⌜ m₂ ⌝ → m₁ ≡ m₂
    ⌜⌝-injective {m₁} {m₂} ⌜m₁⌝≡⌜m₂⌝ = begin
      m₁         ≡˘⟨ ⌞⌜⌝⌟ _ ⟩
      ⌞ ⌜ m₁ ⌝ ⌟ ≡⟨ ⌞⌟-cong ⌜m₁⌝≡⌜m₂⌝ ⟩
      ⌞ ⌜ m₂ ⌝ ⌟ ≡⟨ ⌞⌜⌝⌟ _ ⟩
      m₂         ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- Grades smaller than or equal to 𝟙 are right identities for _ᵐ·_

    ᵐ·-identityʳ-≤𝟙 : p ≤ 𝟙 → m ᵐ· p ≡ m
    ᵐ·-identityʳ-≤𝟙 {p} {m} p≤𝟙 = begin
      m ᵐ· p                                 ≡˘⟨ ᵐ·-congʳ (⌞⌜⌝⌟ _) ⟩
      ⌞ ⌜ m ⌝ ⌟ ᵐ· p                         ≡˘⟨ ᵐ·-congʳ (·ᵐ-idem _) ⟩
      (⌞ ⌜ m ⌝ ⌟ ·ᵐ ⌞ ⌜ m ⌝ ⌟) ᵐ· p          ≡⟨ ·ᵐ-ᵐ·-assoc _ ⟩
      ⌞ ⌜ m ⌝ ⌟ ·ᵐ ⌞ ⌜ m ⌝ ⌟ ·ᵐ ⌞ p ⌟        ≡⟨ ·ᵐ-congˡ ⌞⌟·ᵐ ⟩
      ⌞ ⌜ m ⌝ ⌟ ·ᵐ ⌞ ⌜ m ⌝ · p ⌟             ≡⟨ ·ᵐ-congˡ (⌞⌟-cong (·-congˡ p≤𝟙)) ⟩
      ⌞ ⌜ m ⌝ ⌟ ·ᵐ ⌞ ⌜ m ⌝ · (p ∧ 𝟙) ⌟       ≡⟨ ·ᵐ-congˡ (⌞⌟-cong (·-distribˡ-∧ _ _ _)) ⟩
      ⌞ ⌜ m ⌝ ⌟ ·ᵐ ⌞ ⌜ m ⌝ · p ∧ ⌜ m ⌝ · 𝟙 ⌟ ≡⟨ ·ᵐ-congˡ (⌞⌟-cong (∧-congˡ (·-identityʳ _))) ⟩
      ⌞ ⌜ m ⌝ ⌟ ·ᵐ ⌞ ⌜ m ⌝ · p ∧ ⌜ m ⌝ ⌟     ≡⟨ ⌞⌟·ᵐ⌞∧⌟ʳ ⟩
      ⌞ ⌜ m ⌝ ⌟                              ≡⟨ ⌞⌜⌝⌟ _ ⟩
      m                                      ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- The quantity ω is a right identity for _ᵐ·_.

    ᵐ·-identityʳ-ω : m ᵐ· ω ≡ m
    ᵐ·-identityʳ-ω = ᵐ·-identityʳ-≤𝟙 ω≤𝟙

  opaque

    -- Multiplication from the left with values of the form ⌜ m ⌝
    -- distributes over nrᵢ r.

    ⌜⌝-·-nrᵢ : ∀ i → ⌜ m ⌝ · nrᵢ r p q i ≡ nrᵢ r (⌜ m ⌝ · p) (⌜ m ⌝ · q) i
    ⌜⌝-·-nrᵢ 0 = refl
    ⌜⌝-·-nrᵢ {m} {r} {p} {q} (1+ i) = begin
      ⌜ m ⌝ · nrᵢ r p q (1+ i)                        ≡⟨⟩
      ⌜ m ⌝ · (q + r · nrᵢ r p q i)                   ≡⟨ ·-distribˡ-+ _ _ _ ⟩
      ⌜ m ⌝ · q + ⌜ m ⌝ · r · nrᵢ r p q i             ≡˘⟨ +-congˡ (·-assoc _ _ _) ⟩
      ⌜ m ⌝ · q + (⌜ m ⌝ · r) · nrᵢ r p q i           ≡⟨ +-congˡ (·-congʳ (⌜⌝-·-comm _)) ⟩
      ⌜ m ⌝ · q + (r · ⌜ m ⌝) · nrᵢ r p q i           ≡⟨ +-congˡ (·-assoc _ _ _) ⟩
      ⌜ m ⌝ · q + r · ⌜ m ⌝ · nrᵢ r p q i             ≡⟨ +-congˡ (·-congˡ (⌜⌝-·-nrᵢ i)) ⟩
      ⌜ m ⌝ · q + r · nrᵢ r (⌜ m ⌝ · p) (⌜ m ⌝ · q) i ≡⟨⟩
      nrᵢ r (⌜ m ⌝ · p) (⌜ m ⌝ · q) (1+ i)            ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- Multiplication from the left with values of the form ⌜ m ⌝
    -- distributes over nrᵢᶜ r.

    ⌜⌝-·ᶜ-nrᵢᶜ : ∀ i → ⌜ m ⌝ ·ᶜ nrᵢᶜ r γ δ i ≈ᶜ nrᵢᶜ r (⌜ m ⌝ ·ᶜ γ) (⌜ m ⌝ ·ᶜ δ) i
    ⌜⌝-·ᶜ-nrᵢᶜ {γ = ε} {(ε)} i = ε
    ⌜⌝-·ᶜ-nrᵢᶜ {γ = _ ∙ _} {_ ∙ _} i =
      ⌜⌝-·ᶜ-nrᵢᶜ i ∙ ⌜⌝-·-nrᵢ i

  opaque

    -- If γ ≤ᶜ δ and δ ≤ᶜ ⌜ m ⌝ ·ᶜ δ then γ ≤ᶜ ⌜ m ⌝ ·ᶜ γ.

    ≤ᶜ⌜⌝·ᶜ : γ ≤ᶜ δ → δ ≤ᶜ ⌜ m ⌝ ·ᶜ δ → γ ≤ᶜ ⌜ m ⌝ ·ᶜ γ
    ≤ᶜ⌜⌝·ᶜ {γ = ε} {δ = ε} _ _ = ε
    ≤ᶜ⌜⌝·ᶜ {γ = _ ∙ _} {δ = _ ∙ _} (γ≤ ∙ p≤) (δ≤ ∙ q≤) =
      ≤ᶜ⌜⌝·ᶜ γ≤ δ≤ ∙ ≤⌜⌝· p≤ q≤

  ----------------------------------------------------------------------
  -- Definitions and properties related to mode vectors

  -- Converts usage contexts to mode vectors.

  ⌞_⌟ᶜ : Conₘ n → Mode-vector n
  ⌞ γ ⌟ᶜ x = ⌞ γ ⟨ x ⟩ ⌟

  -- Converts mode vectors to usage contexts.

  ⌜_⌝ᶜ : Mode-vector n → Conₘ n
  ⌜_⌝ᶜ {n = 0}    _ = ε
  ⌜_⌝ᶜ {n = 1+ _} ρ = ⌜ tailᵐ ρ ⌝ᶜ ∙ ⌜ headᵐ ρ ⌝

  opaque

    -- The function ⌞_⌟ᶜ preserves "equality".

    ⌞⌟ᶜ-cong : γ ≈ᶜ δ → ∀ x → ⌞ γ ⌟ᶜ x ≡ ⌞ δ ⌟ᶜ x
    ⌞⌟ᶜ-cong ε            = λ ()
    ⌞⌟ᶜ-cong (γ≈ᶜδ ∙ p≡q) = λ where
      x0     → ⌞⌟-cong p≡q
      (x +1) → ⌞⌟ᶜ-cong γ≈ᶜδ x

  opaque

    -- The result of looking up the x-th entry in ⌜ ms ⌝ᶜ is ⌜ ms x ⌝.

    ⌜⌝ᶜ⟨⟩ : (x : Fin n) → ⌜ ms ⌝ᶜ ⟨ x ⟩ ≡ ⌜ ms x ⌝
    ⌜⌝ᶜ⟨⟩ x0     = refl
    ⌜⌝ᶜ⟨⟩ (x +1) = ⌜⌝ᶜ⟨⟩ x

  opaque

    ·ᶜ-idem-⌜⌝ : ⌜ m ⌝ ·ᶜ ⌜ m ⌝ ·ᶜ γ ≈ᶜ ⌜ m ⌝ ·ᶜ γ
    ·ᶜ-idem-⌜⌝ {m} {γ} = begin
      ⌜ m ⌝ ·ᶜ ⌜ m ⌝ ·ᶜ γ   ≈˘⟨ ·ᶜ-assoc _ _ _ ⟩
      (⌜ m ⌝ · ⌜ m ⌝) ·ᶜ γ  ≈⟨ ·ᶜ-congʳ (·-idem-⌜⌝ _) ⟩
      ⌜ m ⌝ ·ᶜ γ            ∎
      where
      open ≈ᶜ-reasoning

  opaque

    ⌜⌝·ᶜ-comm : ∀ m p (γ : Conₘ n) → ⌜ m ⌝ ·ᶜ p ·ᶜ γ ≈ᶜ p ·ᶜ ⌜ m ⌝ ·ᶜ γ
    ⌜⌝·ᶜ-comm m p γ = begin
      ⌜ m ⌝ ·ᶜ p ·ᶜ γ  ≈˘⟨ ·ᶜ-assoc _ _ _ ⟩
      (⌜ m ⌝ · p) ·ᶜ γ ≈⟨ ·ᶜ-congʳ (⌜⌝-·-comm m) ⟩
      (p · ⌜ m ⌝) ·ᶜ γ ≈⟨ ·ᶜ-assoc _ _ _ ⟩
      p ·ᶜ ⌜ m ⌝ ·ᶜ γ  ∎
      where
      open ≈ᶜ-reasoning

------------------------------------------------------------------------
-- The property of being a mode structure supporting nr functions

record Mode-supports-nr
  ⦃ has-nr : Has-nr 𝕄 ⦄
  (𝐌 : IsMode) : Set (a ⊔ b) where
  no-eta-equality

  open IsMode 𝐌

  field

    -- Multiplication by a mode distributes over nr

    ⌜⌝-·-nr :
      ⌜ m ⌝ · nr p r z s q ≡
      nr p r (⌜ m ⌝ · z) (⌜ m ⌝ · s) (⌜ m ⌝ · q)

    -- The nr function is decreasing in one of its arguments as a mode

    ⌞nr⌟-decreasing₁ :
      ⌞ nr p r z s q ⌟ ≤ᵐ ⌞ z ⌟

    -- The nr function is decreasing in one of its arguments as a mode

    ⌞nr⌟-decreasing₃ :
      ⌞ nr p r z s q ⌟ ≤ᵐ ⌞ q ⌟

  ≡nr-𝟘-𝟘-⌜⌝ : ∀ m → ⌜ m ⌝ · nr p r 𝟘 𝟘 𝟙 ≡ nr p r 𝟘 𝟘 ⌜ m ⌝
  ≡nr-𝟘-𝟘-⌜⌝ {p} {r} m = begin
    ⌜ m ⌝ · nr p r 𝟘 𝟘 𝟙                       ≡⟨ ⌜⌝-·-nr ⟩
    nr p r (⌜ m ⌝ · 𝟘) (⌜ m ⌝ · 𝟘) (⌜ m ⌝ · 𝟙) ≡⟨ cong₃ (nr p r) (·-zeroʳ _) (·-zeroʳ _) (·-identityʳ _) ⟩
    nr p r 𝟘 𝟘 ⌜ m ⌝                           ∎
    where
    open Tools.Reasoning.PropositionalEquality
