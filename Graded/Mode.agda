------------------------------------------------------------------------
-- Modes
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

import Graded.Modality

module Graded.Mode
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  where

open Modality 𝕄

open import Graded.Context 𝕄
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄
open import Tools.Algebra
open import Tools.Bool as B using (Bool; true; false; T)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
open import Tools.PropositionalEquality as PE
open import Tools.Unit
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

private variable
  A          : Set _
  n          : Nat
  p q r s z  : M
  γ δ η      : Conₘ n
  b          : Bool
  ok ok₁ ok₂ : T b

------------------------------------------------------------------------
-- The mode type

-- Modes.

data Mode : Set where
  𝟘ᵐ : ⦃ ok : T 𝟘ᵐ-allowed ⦄ → Mode
  𝟙ᵐ : Mode

pattern 𝟘ᵐ[_] ok = 𝟘ᵐ ⦃ ok = ok ⦄

private variable
  m m₁ m₁′ m₂ m₂′ m₃ : Mode

------------------------------------------------------------------------
-- Some eliminators or similar principles

private

  -- A lemma used in the implementation of 𝟘ᵐ-allowed-elim.

  𝟘ᵐ-allowed-elim-helper :
    ∀ {p} {P : Set p} (b : Bool) →
    (T b → P) →
    ((not-ok : ¬ T b) → P) →
    P
  𝟘ᵐ-allowed-elim-helper true  t f = t _
  𝟘ᵐ-allowed-elim-helper false t f = f (λ ())

-- One can prove that a predicate holds for 𝟘ᵐ-allowed by proving that
-- it holds given that T 𝟘ᵐ-allowed is inhabited, and that it holds
-- given that T 𝟘ᵐ-allowed is not inhabited.

𝟘ᵐ-allowed-elim :
  ∀ {p} {P : Set p} →
  (T 𝟘ᵐ-allowed → P) →
  ((not-ok : ¬ T 𝟘ᵐ-allowed) → P) →
  P
𝟘ᵐ-allowed-elim = 𝟘ᵐ-allowed-elim-helper 𝟘ᵐ-allowed

-- An eliminator for modes.

Mode-elim :
  ∀ {p} (P : Mode → Set p) →
  (⦃ ok : T 𝟘ᵐ-allowed ⦄ → P 𝟘ᵐ[ ok ]) →
  P 𝟙ᵐ →
  ∀ m → P m
Mode-elim _ z o = λ where
  𝟘ᵐ[ ok ] → z ⦃ ok = ok ⦄
  𝟙ᵐ       → o

------------------------------------------------------------------------
-- Properties related to 𝟘ᵐ-allowed

-- Any two applications of 𝟘ᵐ[_] are equal.

𝟘ᵐ-cong : 𝟘ᵐ[ ok₁ ] ≡ 𝟘ᵐ[ ok₂ ]
𝟘ᵐ-cong = PE.cong 𝟘ᵐ[_] B.T-propositional

-- If 𝟘ᵐ is not allowed, then every mode is equal to 𝟙ᵐ.

only-𝟙ᵐ-without-𝟘ᵐ : ¬ T 𝟘ᵐ-allowed → m ≡ 𝟙ᵐ
only-𝟙ᵐ-without-𝟘ᵐ {m = 𝟘ᵐ[ ok ]} not-ok = ⊥-elim (not-ok ok)
only-𝟙ᵐ-without-𝟘ᵐ {m = 𝟙ᵐ}       _      = PE.refl

-- If 𝟘ᵐ is not allowed, then all modes are equal.

Mode-propositional-without-𝟘ᵐ : ¬ T 𝟘ᵐ-allowed → m₁ ≡ m₂
Mode-propositional-without-𝟘ᵐ {m₁ = m₁} {m₂ = m₂} not-ok =
  m₁  ≡⟨ only-𝟙ᵐ-without-𝟘ᵐ not-ok ⟩
  𝟙ᵐ  ≡˘⟨ only-𝟙ᵐ-without-𝟘ᵐ not-ok ⟩
  m₂  ∎
  where
  open Tools.Reasoning.PropositionalEquality

-- If the modality is trivial, then all modes are equal.

Mode-propositional-if-trivial : Trivial → m₁ ≡ m₂
Mode-propositional-if-trivial 𝟙≡𝟘 =
  Mode-propositional-without-𝟘ᵐ (flip 𝟘ᵐ.non-trivial 𝟙≡𝟘)

------------------------------------------------------------------------
-- 𝟘ᵐ? and 𝟙ᵐ′

-- A mode that is 𝟘ᵐ[ something ] if 𝟘ᵐ-allowed is true, and otherwise
-- 𝟙ᵐ.

𝟘ᵐ? : Mode
𝟘ᵐ? = 𝟘ᵐ-allowed-elim 𝟘ᵐ[_] (λ _ → 𝟙ᵐ)

-- One can prove that a predicate holds for 𝟘ᵐ? by proving that it
-- holds for 𝟘ᵐ[ ok ] (for any ok) and that it holds for 𝟙ᵐ (under the
-- assumption that T 𝟘ᵐ-allowed is not inhabited).

𝟘ᵐ?-elim :
  ∀ {p} (P : Mode → Set p) →
  (⦃ ok : T 𝟘ᵐ-allowed ⦄ → P 𝟘ᵐ) →
  (¬ T 𝟘ᵐ-allowed → P 𝟙ᵐ) →
  P 𝟘ᵐ?
𝟘ᵐ?-elim P = lemma _ refl
  where
  lemma :
    ∀ b (eq : b ≡ 𝟘ᵐ-allowed)
    (z : ⦃ ok : T b ⦄ → P 𝟘ᵐ[ subst T eq ok ])
    (o : ¬ T b → P 𝟙ᵐ) →
    P (𝟘ᵐ-allowed-elim-helper b (λ ok → 𝟘ᵐ[ subst T eq ok ]) (λ _ → 𝟙ᵐ))
  lemma true  _ z _ = z ⦃ ok = _ ⦄
  lemma false _ _ o = o (λ ())

-- 𝟘ᵐ? is equal to 𝟘ᵐ[ ok ].

𝟘ᵐ?≡𝟘ᵐ : 𝟘ᵐ? ≡ 𝟘ᵐ[ ok ]
𝟘ᵐ?≡𝟘ᵐ {ok = ok} = 𝟘ᵐ?-elim
  (λ m → m ≡ 𝟘ᵐ[ ok ])
  𝟘ᵐ-cong
  (λ not-ok → ⊥-elim (not-ok ok))

-- A variant of 𝟙ᵐ.

𝟙ᵐ′ : Mode
𝟙ᵐ′ = 𝟘ᵐ-allowed-elim (λ _ → 𝟙ᵐ) (λ _ → 𝟙ᵐ)

-- 𝟙ᵐ′ is equal to 𝟙ᵐ.

𝟙ᵐ′≡𝟙ᵐ : 𝟙ᵐ′ ≡ 𝟙ᵐ
𝟙ᵐ′≡𝟙ᵐ with 𝟘ᵐ-allowed
… | true  = refl
… | false = refl

-- 𝟙ᵐ′ is not equal to 𝟘ᵐ[ ok ].

𝟙ᵐ′≢𝟘ᵐ : 𝟙ᵐ′ ≢ 𝟘ᵐ[ ok ]
𝟙ᵐ′≢𝟘ᵐ 𝟙ᵐ′≡𝟘ᵐ =
  case
    𝟙ᵐ       ≡˘⟨ 𝟙ᵐ′≡𝟙ᵐ ⟩
    𝟙ᵐ′      ≡⟨ 𝟙ᵐ′≡𝟘ᵐ ⟩
    𝟘ᵐ[ _ ]  ∎
  of λ ()
  where
  open Tools.Reasoning.PropositionalEquality

------------------------------------------------------------------------
-- Some basic definitions

-- The join of two modes.

infixr 40 _∨ᵐ_

_∨ᵐ_ : Mode → Mode → Mode
𝟘ᵐ ∨ᵐ m = m
𝟙ᵐ ∨ᵐ m = 𝟙ᵐ

-- Multiplication of modes.

infixr 45 _·ᵐ_

_·ᵐ_ : Mode → Mode → Mode
𝟘ᵐ ·ᵐ _ = 𝟘ᵐ
𝟙ᵐ ·ᵐ m = m

-- Modes can be translated to quantities.

⌜_⌝ : Mode → M
⌜ 𝟘ᵐ ⌝ = 𝟘
⌜ 𝟙ᵐ ⌝ = 𝟙

private

  -- A function used in the implementation of ⌞_⌟.

  ⌞_⌟′ : M → T 𝟘ᵐ-allowed → Mode
  ⌞ p ⌟′ ok = case 𝟘ᵐ.is-𝟘? ok p of λ where
    (yes _) → 𝟘ᵐ[ ok ]
    (no _)  → 𝟙ᵐ

-- Quantities can be translated to modes (in a potentially lossy way).

⌞_⌟ : M → Mode
⌞ p ⌟ = 𝟘ᵐ-allowed-elim ⌞ p ⌟′ (λ _ → 𝟙ᵐ)

-- Modes can be scaled by quantities.
--
-- This definition is based on the typing rule for application in
-- Robert Atkey's "Syntax and Semantics of Quantitative Type Theory".

infixr 45 _ᵐ·_

_ᵐ·_ : Mode → M → Mode
𝟘ᵐ ᵐ· _ = 𝟘ᵐ
𝟙ᵐ ᵐ· p = ⌞ p ⌟

-- Equality of modes is decidable.

infix 4 _≟_

_≟_ : (m₁ m₂ : Mode) → Dec (m₁ ≡ m₂)
𝟙ᵐ ≟ 𝟙ᵐ = yes refl
𝟘ᵐ ≟ 𝟘ᵐ = yes 𝟘ᵐ-cong
𝟙ᵐ ≟ 𝟘ᵐ = no (λ ())
𝟘ᵐ ≟ 𝟙ᵐ = no (λ ())

------------------------------------------------------------------------
-- Mode vectors

-- Mode vectors of the given length.

Mode-vector : Nat → Set
Mode-vector n = Fin n → Mode

private variable
  ms : Mode-vector n

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

-- Converts usage contexts to mode vectors.

⌞_⌟ᶜ : Conₘ n → Mode-vector n
⌞ γ ⌟ᶜ x = ⌞ γ ⟨ x ⟩ ⌟

-- Converts mode vectors to usage contexts.

⌜_⌝ᶜ : Mode-vector n → Conₘ n
⌜_⌝ᶜ {n = 0}    _ = ε
⌜_⌝ᶜ {n = 1+ _} ρ = ⌜ tailᵐ ρ ⌝ᶜ ∙ ⌜ headᵐ ρ ⌝

------------------------------------------------------------------------
-- Properties related to _∨ᵐ_ and _·ᵐ_

-- The multiplication operation is idempotent.

·ᵐ-idem : m ·ᵐ m ≡ m
·ᵐ-idem {m = 𝟘ᵐ} = PE.refl
·ᵐ-idem {m = 𝟙ᵐ} = PE.refl

-- If m₁ ·ᵐ m₂ ≡ 𝟙ᵐ then m₁ ≡ 𝟙ᵐ

·ᵐ-𝟙ˡ : m₁ ·ᵐ m₂ ≡ 𝟙ᵐ → m₁ ≡ 𝟙ᵐ
·ᵐ-𝟙ˡ {m₁ = 𝟙ᵐ} eq = PE.refl

-- If m₁ ·ᵐ m₂ ≡ 𝟙ᵐ then m₂ ≡ 𝟙ᵐ

·ᵐ-𝟙ʳ : m₁ ·ᵐ m₂ ≡ 𝟙ᵐ → m₂ ≡ 𝟙ᵐ
·ᵐ-𝟙ʳ {m₁ = 𝟙ᵐ} eq = eq


-- The operations _∨ᵐ_ and _·ᵐ_, along with the values 𝟘ᵐ? and 𝟙ᵐ,
-- form a commutative semiring.

∨ᵐ-·ᵐ-is-commutative-semiring :
  IsCommutativeSemiring Mode _∨ᵐ_ _·ᵐ_ 𝟘ᵐ? 𝟙ᵐ
∨ᵐ-·ᵐ-is-commutative-semiring = record
  { isSemiring = record
    { isSemiringWithoutAnnihilatingZero = record
      { +-isCommutativeMonoid = record
        { isMonoid = record
          { isSemigroup = record
            { isMagma = record
              { isEquivalence = PE.isEquivalence
              ; ∙-cong        = cong₂ _∨ᵐ_
              }
            ; assoc = λ where
                𝟘ᵐ _ _ → PE.refl
                𝟙ᵐ _ _ → PE.refl
            }
          ; identity =
                (λ where
                   𝟘ᵐ[ ok ] →
                     𝟘ᵐ? ∨ᵐ 𝟘ᵐ  ≡⟨ PE.cong (_∨ᵐ _) (𝟘ᵐ?≡𝟘ᵐ {ok = ok}) ⟩
                     𝟘ᵐ ∨ᵐ 𝟘ᵐ   ≡⟨⟩
                     𝟘ᵐ         ∎
                   𝟙ᵐ → 𝟘ᵐ?-elim
                     (λ m → m ∨ᵐ 𝟙ᵐ ≡ 𝟙ᵐ)
                     PE.refl
                     (λ _ → PE.refl))
              , (λ where
                   𝟘ᵐ → 𝟘ᵐ?≡𝟘ᵐ
                   𝟙ᵐ → PE.refl)
          }
        ; comm = λ where
            𝟘ᵐ 𝟘ᵐ → 𝟘ᵐ-cong
            𝟘ᵐ 𝟙ᵐ → PE.refl
            𝟙ᵐ 𝟘ᵐ → PE.refl
            𝟙ᵐ 𝟙ᵐ → PE.refl
        }
        ; *-cong = cong₂ _·ᵐ_
        ; *-assoc = λ where
            𝟘ᵐ _ _ → PE.refl
            𝟙ᵐ _ _ → PE.refl
        ; *-identity =
              (λ _ → PE.refl)
            , (λ where
                 𝟘ᵐ → PE.refl
                 𝟙ᵐ → PE.refl)
      ; distrib =
            (λ where
               𝟘ᵐ _ _ → PE.refl
               𝟙ᵐ _ _ → PE.refl)
          , (λ where
               𝟘ᵐ 𝟘ᵐ _  → PE.refl
               𝟘ᵐ 𝟙ᵐ 𝟘ᵐ → 𝟘ᵐ-cong
               𝟘ᵐ 𝟙ᵐ 𝟙ᵐ → PE.refl
               𝟙ᵐ 𝟘ᵐ _  → PE.refl
               𝟙ᵐ 𝟙ᵐ _  → PE.refl)
      }
    ; zero =
          (λ where
             𝟘ᵐ →
               𝟘ᵐ? ·ᵐ 𝟘ᵐ  ≡⟨ PE.cong (_·ᵐ _) 𝟘ᵐ?≡𝟘ᵐ ⟩
               𝟘ᵐ ·ᵐ 𝟘ᵐ   ≡⟨⟩
               𝟘ᵐ         ≡˘⟨ 𝟘ᵐ?≡𝟘ᵐ ⟩
               𝟘ᵐ?        ∎
             𝟙ᵐ → 𝟘ᵐ?-elim
               (λ m → m ·ᵐ 𝟙ᵐ ≡ m)
               PE.refl
               (λ _ → PE.refl))
        , (λ where
             𝟘ᵐ → PE.sym 𝟘ᵐ?≡𝟘ᵐ
             𝟙ᵐ → PE.refl)
    }
  ; *-comm = λ where
      𝟘ᵐ 𝟘ᵐ → 𝟘ᵐ-cong
      𝟘ᵐ 𝟙ᵐ → PE.refl
      𝟙ᵐ 𝟘ᵐ → PE.refl
      𝟙ᵐ 𝟙ᵐ → PE.refl
  }
  where
  open Tools.Reasoning.PropositionalEquality

open IsCommutativeSemiring Mode ∨ᵐ-·ᵐ-is-commutative-semiring
  public
  using
    ()
  renaming
    ( *-assoc       to ·ᵐ-assoc
    ; *-identity    to ·ᵐ-identity
    ; *-identityʳ   to ·ᵐ-identityʳ
    ; *-identityˡ   to ·ᵐ-identityˡ
    ; *-comm        to ·ᵐ-comm
    ; +-assoc       to ∨ᵐ-assoc
    ; +-comm        to ∨ᵐ-comm
    ; +-identity    to ∨ᵐ-identity
    ; +-identityʳ   to ∨ᵐ-identityʳ
    ; +-identityˡ   to ∨ᵐ-identityˡ
    ; distrib       to ·ᵐ-distrib-∨ᵐ
    ; distribʳ      to ·ᵐ-distribʳ-∨ᵐ
    ; distribˡ      to ·ᵐ-distribˡ-∨ᵐ
    ; zero          to ·ᵐ-zero
    ; zeroʳ         to ·ᵐ-zeroʳ
    ; zeroˡ         to ·ᵐ-zeroˡ
    )

-- 𝟘ᵐ is a right zero for _·ᵐ_.

·ᵐ-zeroʳ-𝟘ᵐ : m ·ᵐ 𝟘ᵐ[ ok ] ≡ 𝟘ᵐ[ ok ]
·ᵐ-zeroʳ-𝟘ᵐ {m = 𝟘ᵐ} = 𝟘ᵐ-cong
·ᵐ-zeroʳ-𝟘ᵐ {m = 𝟙ᵐ} = refl

------------------------------------------------------------------------
-- Properties related to ⌜_⌝ and ⌜_⌝ᶜ

-- ⌜_⌝ commutes with _·_/_·ᵐ_.

⌜·ᵐ⌝ : ∀ m₁ → ⌜ m₁ ·ᵐ m₂ ⌝ ≡ ⌜ m₁ ⌝ · ⌜ m₂ ⌝
⌜·ᵐ⌝ {m₂ = m₂} 𝟘ᵐ = begin
  𝟘           ≡˘⟨ ·-zeroˡ _ ⟩
  𝟘 · ⌜ m₂ ⌝  ∎
  where
  open Tools.Reasoning.PropositionalEquality
⌜·ᵐ⌝ {m₂ = m₂} 𝟙ᵐ = begin
  ⌜ m₂ ⌝      ≡˘⟨ ·-identityˡ _ ⟩
  𝟙 · ⌜ m₂ ⌝  ∎
  where
  open Tools.Reasoning.PropositionalEquality

-- A form of commutativity.

⌜⌝-·-comm : ∀ m → ⌜ m ⌝ · p ≡ p · ⌜ m ⌝
⌜⌝-·-comm {p = p} 𝟘ᵐ = begin
  𝟘 · p  ≡⟨ ·-zeroˡ _ ⟩
  𝟘      ≡˘⟨ ·-zeroʳ _ ⟩
  p · 𝟘  ∎
  where
  open Tools.Reasoning.PropositionalEquality
⌜⌝-·-comm {p = p} 𝟙ᵐ = begin
  𝟙 · p  ≡⟨ ·-identityˡ _ ⟩
  p      ≡˘⟨ ·-identityʳ _ ⟩
  p · 𝟙  ∎
  where
  open Tools.Reasoning.PropositionalEquality

-- A form of associativity.

·ᵐ-·-assoc : ∀ m₁ → ⌜ m₁ ·ᵐ m₂ ⌝ · p ≡ ⌜ m₁ ⌝ · ⌜ m₂ ⌝ · p
·ᵐ-·-assoc {m₂ = m₂} {p = p} m₁ = begin
  ⌜ m₁ ·ᵐ m₂ ⌝ · p       ≡⟨ ·-congʳ (⌜·ᵐ⌝ m₁) ⟩
  (⌜ m₁ ⌝ · ⌜ m₂ ⌝) · p  ≡⟨ ·-assoc _ _ _ ⟩
  ⌜ m₁ ⌝ · ⌜ m₂ ⌝ · p    ∎
  where
  open Tools.Reasoning.PropositionalEquality

-- A form of associativity.

·ᵐ-·ᶜ-assoc : ∀ m₁ → ⌜ m₁ ·ᵐ m₂ ⌝ ·ᶜ γ ≈ᶜ ⌜ m₁ ⌝ ·ᶜ ⌜ m₂ ⌝ ·ᶜ γ
·ᵐ-·ᶜ-assoc {γ = ε}     m₁ = ε
·ᵐ-·ᶜ-assoc {γ = _ ∙ _} m₁ = ·ᵐ-·ᶜ-assoc m₁ ∙ ·ᵐ-·-assoc m₁

-- ⌜ m ⌝ ·_ distributes over _⊛_▷ r from the left.

⌜⌝-·-distribˡ-⊛ :
  ⦃ has-star : Has-star semiring-with-meet ⦄ →
  ∀ m → ⌜ m ⌝ · p ⊛ q ▷ r ≡ (⌜ m ⌝ · p) ⊛ ⌜ m ⌝ · q ▷ r
⌜⌝-·-distribˡ-⊛ {p = p} {q = q} {r = r} 𝟙ᵐ = begin
  𝟙 · p ⊛ q ▷ r        ≡⟨ ·-identityˡ _ ⟩
  p ⊛ q ▷ r            ≡˘⟨ ⊛ᵣ-cong (·-identityˡ _) (·-identityˡ _) ⟩
  (𝟙 · p) ⊛ 𝟙 · q ▷ r  ∎
  where
  open Tools.Reasoning.PropositionalEquality
⌜⌝-·-distribˡ-⊛ {p = p} {q = q} {r = r} 𝟘ᵐ =
  let open Tools.Reasoning.PropositionalEquality in begin
  𝟘 · p ⊛ q ▷ r        ≡⟨ ·-zeroˡ _ ⟩
  𝟘                    ≡˘⟨ ⊛-idem-𝟘 _ ⟩
  𝟘 ⊛ 𝟘 ▷ r            ≡˘⟨ ⊛ᵣ-cong (·-zeroˡ _) (·-zeroˡ _) ⟩
  (𝟘 · p) ⊛ 𝟘 · q ▷ r  ∎

-- ⌜ m ⌝ ·ᶜ_ distributes over _⊛ᶜ_▷ r from the left.

⌜⌝-·ᶜ-distribˡ-⊛ᶜ :
  ⦃ has-star : Has-star semiring-with-meet ⦄ →
  ∀ m → ⌜ m ⌝ ·ᶜ γ ⊛ᶜ δ ▷ r ≈ᶜ (⌜ m ⌝ ·ᶜ γ) ⊛ᶜ ⌜ m ⌝ ·ᶜ δ ▷ r
⌜⌝-·ᶜ-distribˡ-⊛ᶜ {γ = ε}     {δ = ε}     _ = ε
⌜⌝-·ᶜ-distribˡ-⊛ᶜ {γ = _ ∙ _} {δ = _ ∙ _} m =
  ⌜⌝-·ᶜ-distribˡ-⊛ᶜ m ∙ ⌜⌝-·-distribˡ-⊛ m

-- Multiplication from the left with values of the form ⌜ m ⌝
-- distributes over nr p r.

⌜⌝-·-distribˡ-nr :
  ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
  ∀ {n} m →
  ⌜ m ⌝ · nr p r z s n ≡ nr p r (⌜ m ⌝ · z) (⌜ m ⌝ · s) (⌜ m ⌝ · n)
⌜⌝-·-distribˡ-nr {p = p} {r = r} {z = z} {s = s} {n = n} 𝟙ᵐ =
  𝟙 · nr p r z s n                ≡⟨ ·-identityˡ _ ⟩
  nr p r z s n                    ≡˘⟨ cong₂ (nr _ _ _) (·-identityˡ _) (·-identityˡ _) ⟩
  nr p r z (𝟙 · s) (𝟙 · n)        ≡˘⟨ cong (λ z → nr _ _ z _ _) (·-identityˡ _) ⟩
  nr p r (𝟙 · z) (𝟙 · s) (𝟙 · n)  ∎
  where
  open Tools.Reasoning.PropositionalEquality
⌜⌝-·-distribˡ-nr {p = p} {r = r} {z = z} {s = s} {n = n} 𝟘ᵐ =
  𝟘 · nr p r z s n                ≡⟨ ·-zeroˡ _ ⟩
  𝟘                               ≡˘⟨ nr-𝟘 ⟩
  nr p r 𝟘 𝟘 𝟘                    ≡˘⟨ cong₂ (nr _ _ _) (·-zeroˡ _) (·-zeroˡ _) ⟩
  nr p r 𝟘 (𝟘 · s) (𝟘 · n)        ≡˘⟨ cong (λ z → nr _ _ z (_ · _) (_ · _)) (·-zeroˡ _) ⟩
  nr p r (𝟘 · z) (𝟘 · s) (𝟘 · n)  ∎
  where
  open Tools.Reasoning.PropositionalEquality

-- Multiplication from the left with values of the form ⌜ m ⌝
-- distributes over nrᶜ p r.

⌜⌝ᶜ-·ᶜ-distribˡ-nrᶜ :
  ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
  ∀ m →
  ⌜ m ⌝ ·ᶜ nrᶜ p r γ δ η ≈ᶜ
  nrᶜ p r (⌜ m ⌝ ·ᶜ γ) (⌜ m ⌝ ·ᶜ δ) (⌜ m ⌝ ·ᶜ η)
⌜⌝ᶜ-·ᶜ-distribˡ-nrᶜ {γ = ε}     {δ = ε}     {η = ε}     _ = ε
⌜⌝ᶜ-·ᶜ-distribˡ-nrᶜ {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} m =
  ⌜⌝ᶜ-·ᶜ-distribˡ-nrᶜ m ∙ ⌜⌝-·-distribˡ-nr m

-- The result of looking up the x-th entry in ⌜ ms ⌝ᶜ is ⌜ ms x ⌝.

⌜⌝ᶜ⟨⟩ : (x : Fin n) → ⌜ ms ⌝ᶜ ⟨ x ⟩ ≡ ⌜ ms x ⌝
⌜⌝ᶜ⟨⟩ x0     = PE.refl
⌜⌝ᶜ⟨⟩ (x +1) = ⌜⌝ᶜ⟨⟩ x

-- If 𝟘ᵐ is allowed, then ⌜ 𝟘ᵐ? ⌝ is equal to 𝟘.

⌜𝟘ᵐ?⌝≡𝟘 : T 𝟘ᵐ-allowed → ⌜ 𝟘ᵐ? ⌝ ≡ 𝟘
⌜𝟘ᵐ?⌝≡𝟘 ok =
  ⌜ 𝟘ᵐ? ⌝       ≡⟨ cong ⌜_⌝ (𝟘ᵐ?≡𝟘ᵐ {ok = ok}) ⟩
  ⌜ 𝟘ᵐ[ ok ] ⌝  ≡⟨⟩
  𝟘             ∎
  where
  open Tools.Reasoning.PropositionalEquality

-- Multiplication is idempotent for ⌜ m ⌝.

·-idem-⌜⌝ : ∀ m → ⌜ m ⌝ · ⌜ m ⌝ ≡ ⌜ m ⌝
·-idem-⌜⌝ 𝟘ᵐ = ·-zeroʳ _
·-idem-⌜⌝ 𝟙ᵐ = ·-identityʳ _

------------------------------------------------------------------------
-- Properties related to ⌞_⌟ and ⌞_⌟ᶜ

-- The function ⌞_⌟ preserves "equality".

⌞⌟-cong : p ≡ q → ⌞ p ⌟ ≡ ⌞ q ⌟
⌞⌟-cong refl = refl

-- The function ⌞_⌟ᶜ preserves "equality".

⌞⌟ᶜ-cong : γ ≈ᶜ δ → ∀ x → ⌞ γ ⌟ᶜ x ≡ ⌞ δ ⌟ᶜ x
⌞⌟ᶜ-cong (γ≈ᶜδ ∙ p≡q) = λ where
  x0     → ⌞⌟-cong p≡q
  (x +1) → ⌞⌟ᶜ-cong γ≈ᶜδ x

-- A view for ⌞_⌟.

data ⌞⌟-view (p : M) (m : Mode) : Set a where
  𝟘ᵐ-not-allowed : ¬ T 𝟘ᵐ-allowed                → m ≡ 𝟙ᵐ → ⌞⌟-view p m
  𝟙ᵐ             : ⦃ ok : T 𝟘ᵐ-allowed ⦄ → p ≢ 𝟘 → m ≡ 𝟙ᵐ → ⌞⌟-view p m
  𝟘ᵐ             : ⦃ ok : T 𝟘ᵐ-allowed ⦄ → p ≡ 𝟘 → m ≡ 𝟘ᵐ → ⌞⌟-view p m

opaque

  -- The view is total.

  ⌞⌟-view-total : ∀ p → ⌞⌟-view p ⌞ p ⌟
  ⌞⌟-view-total p = lemma _ refl
    where
    lemma :
      ∀ b (eq : b ≡ 𝟘ᵐ-allowed) →
      ⌞⌟-view p
        (𝟘ᵐ-allowed-elim-helper b
           (λ ok → ⌞ p ⌟′ (subst T eq ok))
           (λ _ → 𝟙ᵐ))
    lemma false refl = 𝟘ᵐ-not-allowed idᶠ refl
    lemma true  refl with 𝟘ᵐ.is-𝟘? tt p
    … | no p≢𝟘  = 𝟙ᵐ ⦃ ok = _ ⦄ p≢𝟘 refl
    … | yes p≡𝟘 = 𝟘ᵐ ⦃ ok = _ ⦄ p≡𝟘 refl

opaque

  -- The value of ⌞ p ⌟ is 𝟙ᵐ if and only if
  -- * 𝟘ᵐ is not allowed, or
  -- * 𝟘ᵐ is allowed and p is not equal to 𝟘.

  ⌞⌟≡𝟙ᵐ⇔≢𝟘 : ⌞ p ⌟ ≡ 𝟙ᵐ ⇔ (¬ T 𝟘ᵐ-allowed ⊎ T 𝟘ᵐ-allowed × p ≢ 𝟘)
  ⌞⌟≡𝟙ᵐ⇔≢𝟘 = case ⌞⌟-view-total _ of λ where
    (𝟘ᵐ-not-allowed not-ok ≡𝟙ᵐ) → (λ _ → inj₁ not-ok) , (λ _ → ≡𝟙ᵐ)
    (𝟙ᵐ ⦃ ok ⦄ ≢𝟘 ≡𝟙ᵐ)          → (λ _ → inj₂ (ok , ≢𝟘)) , (λ _ → ≡𝟙ᵐ)
    (𝟘ᵐ ⦃ ok ⦄ ≡𝟘 ≡𝟘ᵐ)          →
        (λ ≡𝟙ᵐ → inj₂ (ok , (case trans (PE.sym ≡𝟘ᵐ) ≡𝟙ᵐ of λ ())))
      , (λ where
           (inj₁ not-ok)   → ⊥-elim $ not-ok ok
           (inj₂ (_ , ≢𝟘)) → ⊥-elim $ ≢𝟘 ≡𝟘)

opaque

  -- The value of ⌞ p ⌟ is 𝟘ᵐ[ ok ] if and only if p is 𝟘.

  ⌞⌟≡𝟘ᵐ⇔≡𝟘 : ⌞ p ⌟ ≡ 𝟘ᵐ[ ok ] ⇔ p ≡ 𝟘
  ⌞⌟≡𝟘ᵐ⇔≡𝟘 {ok} = case ⌞⌟-view-total _ of λ where
    (𝟘ᵐ-not-allowed not-ok ≡𝟙ᵐ) → ⊥-elim $ not-ok ok
    (𝟘ᵐ ≡𝟘 ≡𝟘ᵐ)                 → (λ _ → ≡𝟘) , (λ _ → trans ≡𝟘ᵐ 𝟘ᵐ-cong)
    (𝟙ᵐ ≢𝟘 ≡𝟙ᵐ)                 →
        (λ ≡𝟘ᵐ → case trans (PE.sym ≡𝟘ᵐ) ≡𝟙ᵐ of λ ())
      , (λ ≡𝟘 → ⊥-elim $ ≢𝟘 ≡𝟘)

opaque

  -- The value of ⌞ p ⌟ is 𝟘ᵐ? if and only if
  -- * 𝟘ᵐ is not allowed or
  -- * 𝟘ᵐ is allowed and p is equal to 𝟘.

  ⌞⌟≡𝟘ᵐ?⇔≡𝟘 : ⌞ p ⌟ ≡ 𝟘ᵐ? ⇔ (¬ T 𝟘ᵐ-allowed ⊎ T 𝟘ᵐ-allowed × p ≡ 𝟘)
  ⌞⌟≡𝟘ᵐ?⇔≡𝟘 {p} = lemma _ refl
    where
    lemma :
      ∀ b (eq : b ≡ 𝟘ᵐ-allowed) →
      𝟘ᵐ-allowed-elim-helper b
        (λ ok → ⌞ p ⌟′ (subst T eq ok))
        (λ _ → 𝟙ᵐ) ≡
      𝟘ᵐ?
        ⇔
      (¬ T 𝟘ᵐ-allowed ⊎ T 𝟘ᵐ-allowed × p ≡ 𝟘)
    lemma false refl =
      𝟘ᵐ?-elim
        (λ m →
           𝟙ᵐ ≡ m ⇔ (¬ T 𝟘ᵐ-allowed ⊎ T 𝟘ᵐ-allowed × p ≡ 𝟘))
        (λ ⦃ ok = ok ⦄ → ⊥-elim ok)
        (λ _ → (λ _ → inj₁ idᶠ) , (λ _ → refl))
    lemma true refl with 𝟘ᵐ.is-𝟘? tt p
    … | no p≢𝟘 =
        (λ ())
      , (λ where
           (inj₁ ¬⊤)        → ⊥-elim $ ¬⊤ _
           (inj₂ (_ , p≡𝟘)) → ⊥-elim $ p≢𝟘 p≡𝟘)
    … | yes p≡𝟘 =
        (λ _ → inj₂ (_ , p≡𝟘))
      , (λ _ → refl)

-- If p is equal to 𝟘, then ⌞ p ⌟ is equal to 𝟘ᵐ[ ok ].

≡𝟘→⌞⌟≡𝟘ᵐ : p ≡ 𝟘 → ⌞ p ⌟ ≡ 𝟘ᵐ[ ok ]
≡𝟘→⌞⌟≡𝟘ᵐ = ⌞⌟≡𝟘ᵐ⇔≡𝟘 .proj₂

-- ⌞ 𝟘 ⌟ is equal to 𝟘ᵐ[ ok ].

⌞𝟘⌟ : ⌞ 𝟘 ⌟ ≡ 𝟘ᵐ[ ok ]
⌞𝟘⌟ = ≡𝟘→⌞⌟≡𝟘ᵐ refl

-- ⌞ 𝟘 ⌟ is equal to 𝟘ᵐ?.

⌞𝟘⌟≡𝟘ᵐ? : ⌞ 𝟘 ⌟ ≡ 𝟘ᵐ?
⌞𝟘⌟≡𝟘ᵐ? = 𝟘ᵐ?-elim
  (⌞ 𝟘 ⌟ ≡_)
  ⌞𝟘⌟
  only-𝟙ᵐ-without-𝟘ᵐ

-- If p is equal to 𝟘, then ⌞ p ⌟ is equal to 𝟘ᵐ?.

≡𝟘→⌞⌟≡𝟘ᵐ? : p ≡ 𝟘 → ⌞ p ⌟ ≡ 𝟘ᵐ?
≡𝟘→⌞⌟≡𝟘ᵐ? refl = ⌞𝟘⌟≡𝟘ᵐ?

-- If ⌞ p ⌟ is equal to 𝟘ᵐ[ ok ], then p is equal to 𝟘.

⌞⌟≡𝟘ᵐ→≡𝟘 : ⌞ p ⌟ ≡ 𝟘ᵐ[ ok ] → p ≡ 𝟘
⌞⌟≡𝟘ᵐ→≡𝟘 = ⌞⌟≡𝟘ᵐ⇔≡𝟘 .proj₁

opaque

  -- If "𝟘ᵐ is allowed" implies that p is not equal to 𝟘, then ⌞ p ⌟
  -- is equal to 𝟙ᵐ.

  ≢𝟘→⌞⌟≡𝟙ᵐ′ : (T 𝟘ᵐ-allowed → p ≢ 𝟘) → ⌞ p ⌟ ≡ 𝟙ᵐ
  ≢𝟘→⌞⌟≡𝟙ᵐ′ p≢𝟘 =
    𝟘ᵐ-allowed-elim
      (λ ok → ⌞⌟≡𝟙ᵐ⇔≢𝟘 .proj₂ (inj₂ (ok , p≢𝟘 ok)))
      (λ not-ok → ⌞⌟≡𝟙ᵐ⇔≢𝟘 .proj₂ (inj₁ not-ok))

-- A variant of ≢𝟘→⌞⌟≡𝟙ᵐ′.

≢𝟘→⌞⌟≡𝟙ᵐ : p ≢ 𝟘 → ⌞ p ⌟ ≡ 𝟙ᵐ
≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘 = ≢𝟘→⌞⌟≡𝟙ᵐ′ (λ _ → p≢𝟘)

-- If 𝟘ᵐ is allowed and ⌞ p ⌟ is equal to 𝟙ᵐ, then p is not equal to
-- 𝟘.

⌞⌟≡𝟙ᵐ→≢𝟘 : T 𝟘ᵐ-allowed → ⌞ p ⌟ ≡ 𝟙ᵐ → p ≢ 𝟘
⌞⌟≡𝟙ᵐ→≢𝟘 ok ≡𝟙ᵐ = case ⌞⌟≡𝟙ᵐ⇔≢𝟘 .proj₁ ≡𝟙ᵐ of λ where
  (inj₁ not-ok)    → ⊥-elim $ not-ok ok
  (inj₂ (_ , p≢𝟘)) → p≢𝟘

-- ⌞ 𝟙 ⌟ is equal to 𝟙ᵐ.

⌞𝟙⌟ : ⌞ 𝟙 ⌟ ≡ 𝟙ᵐ
⌞𝟙⌟ = ≢𝟘→⌞⌟≡𝟙ᵐ′ 𝟘ᵐ.non-trivial

-- The function taking p to ⌜ ⌞ p ⌟ ⌝ preserves equivalence.

⌜⌞⌟⌝-cong : p ≡ q → ⌜ ⌞ p ⌟ ⌝ ≡ ⌜ ⌞ q ⌟ ⌝
⌜⌞⌟⌝-cong p≡q = cong ⌜_⌝ (⌞⌟-cong p≡q)

-- If 𝟙 ≤ 𝟘, then the function taking p to ⌜ ⌞ p ⌟ ⌝ is monotone.

⌜⌞⌟⌝-monotone : 𝟙 ≤ 𝟘 → p ≤ q → ⌜ ⌞ p ⌟ ⌝ ≤ ⌜ ⌞ q ⌟ ⌝
⌜⌞⌟⌝-monotone {p = p} {q = q} 𝟙≤𝟘 p≤q = lemma _ _ refl refl
  where
  lemma : ∀ m₁ m₂ → ⌞ p ⌟ ≡ m₁ → ⌞ q ⌟ ≡ m₂ → ⌜ m₁ ⌝ ≤ ⌜ m₂ ⌝
  lemma 𝟘ᵐ       𝟘ᵐ _      _      = ≤-refl
  lemma 𝟙ᵐ       𝟙ᵐ _      _      = ≤-refl
  lemma 𝟙ᵐ       𝟘ᵐ _      _      = 𝟙≤𝟘
  lemma 𝟘ᵐ[ ok ] 𝟙ᵐ ⌞p⌟≡𝟘ᵐ ⌞q⌟≡𝟙ᵐ =
    ⊥-elim (⌞⌟≡𝟙ᵐ→≢𝟘 ok ⌞q⌟≡𝟙ᵐ (𝟘ᵐ.𝟘≮ ok (begin
      𝟘  ≈˘⟨ ⌞⌟≡𝟘ᵐ→≡𝟘 ⌞p⌟≡𝟘ᵐ ⟩
      p  ≤⟨ p≤q ⟩
      q  ∎)))
    where
    open Tools.Reasoning.PartialOrder ≤-poset

-- The value p · ⌜ ⌞ p ⌟ ⌝ is equal to p.

·⌜⌞⌟⌝ : p · ⌜ ⌞ p ⌟ ⌝ ≡ p
·⌜⌞⌟⌝ {p = p} = lemma _ refl
  where
  open Tools.Reasoning.PropositionalEquality

  lemma : ∀ m → ⌞ p ⌟ ≡ m → p · ⌜ m ⌝ ≡ p
  lemma 𝟙ᵐ _ =
    p · 𝟙  ≡⟨ ·-identityʳ _ ⟩
    p      ∎
  lemma 𝟘ᵐ ⌞p⌟≡𝟘ᵐ =
    p · 𝟘  ≡⟨ ·-zeroʳ _ ⟩
    𝟘      ≡˘⟨ ⌞⌟≡𝟘ᵐ→≡𝟘 ⌞p⌟≡𝟘ᵐ ⟩
    p      ∎

-- The function ⌞_⌟ is a left inverse of ⌜_⌝.

⌞⌜⌝⌟ : ∀ m → ⌞ ⌜ m ⌝ ⌟ ≡ m
⌞⌜⌝⌟ 𝟘ᵐ = ⌞𝟘⌟
⌞⌜⌝⌟ 𝟙ᵐ = ⌞𝟙⌟

-- A lemma relating _·ᵐ_, ⌞_⌟ and _ᵐ·_.

·ᵐ⌞⌟ : m ·ᵐ ⌞ p ⌟ ≡ m ᵐ· p
·ᵐ⌞⌟ {m = 𝟘ᵐ} = PE.refl
·ᵐ⌞⌟ {m = 𝟙ᵐ} = PE.refl

-- A lemma relating ⌞_⌟, _·_, ⌜_⌝ and _ᵐ·_.

⌞⌜⌝·⌟ : ∀ m → ⌞ ⌜ m ⌝ · p ⌟ ≡ m ᵐ· p
⌞⌜⌝·⌟ {p = p} 𝟘ᵐ =
  ⌞ 𝟘 · p ⌟  ≡⟨ ⌞⌟-cong (·-zeroˡ _) ⟩
  ⌞ 𝟘 ⌟      ≡⟨ ⌞𝟘⌟ ⟩
  𝟘ᵐ         ∎
  where
  open Tools.Reasoning.PropositionalEquality
⌞⌜⌝·⌟ {p = p} 𝟙ᵐ =
  ⌞ 𝟙 · p ⌟  ≡⟨ ⌞⌟-cong (·-identityˡ _) ⟩
  ⌞ p ⌟      ≡⟨⟩
  𝟙ᵐ ᵐ· p    ∎
  where
  open Tools.Reasoning.PropositionalEquality

-- The property "if ⌞ p ⌟ is 𝟙ᵐ then A" is logically equivalent
-- to "A or 𝟘ᵐ is allowed and p is 𝟘".

⌞⌟≡𝟙→⇔⊎𝟘ᵐ×≡𝟘 :
  (⌞ p ⌟ ≡ 𝟙ᵐ → A) ⇔
  (A ⊎ T 𝟘ᵐ-allowed × p ≡ 𝟘)
⌞⌟≡𝟙→⇔⊎𝟘ᵐ×≡𝟘 {p = p} {A = A} =
    lemma _ refl
  , λ where
      (inj₁ p≡𝟙)         → λ _ → p≡𝟙
      (inj₂ (ok , refl)) →
        ⌞ 𝟘 ⌟ ≡ 𝟙ᵐ     →⟨ trans (PE.sym ⌞𝟘⌟) ⟩
        𝟘ᵐ[ ok ] ≡ 𝟙ᵐ  →⟨ (λ ()) ⟩
        A              □
  where
  lemma :
    ∀ m → ⌞ p ⌟ ≡ m → (m ≡ 𝟙ᵐ → A) →
    A ⊎ T 𝟘ᵐ-allowed × p ≡ 𝟘
  lemma = λ where
    𝟙ᵐ _ →
      (𝟙ᵐ ≡ 𝟙ᵐ → A)             →⟨ inj₁ ∘→ (_$ refl) ⟩
      A ⊎ T 𝟘ᵐ-allowed × p ≡ 𝟘  □
    𝟘ᵐ[ ok ] → flip λ _ →
      ⌞ p ⌟ ≡ 𝟘ᵐ                →⟨ inj₂ ∘→ (ok ,_) ∘→ ⌞⌟≡𝟘ᵐ→≡𝟘 ⟩
      A ⊎ T 𝟘ᵐ-allowed × p ≡ 𝟘  □

------------------------------------------------------------------------
-- Properties related to _ᵐ·_

-- The function m ᵐ·_ preserves "equality".

ᵐ·-cong : ∀ m → p ≡ q → m ᵐ· p ≡ m ᵐ· q
ᵐ·-cong 𝟘ᵐ = λ _ → PE.refl
ᵐ·-cong 𝟙ᵐ = ⌞⌟-cong

-- 𝟘 is a kind of right zero for _ᵐ·_.

ᵐ·-zeroʳ : ∀ m → m ᵐ· 𝟘 ≡ 𝟘ᵐ?
ᵐ·-zeroʳ 𝟘ᵐ = PE.sym 𝟘ᵐ?≡𝟘ᵐ
ᵐ·-zeroʳ 𝟙ᵐ = ⌞𝟘⌟≡𝟘ᵐ?

-- 𝟘ᵐ? is a left zero for _ᵐ·_.

ᵐ·-zeroˡ : 𝟘ᵐ? ᵐ· p ≡ 𝟘ᵐ?
ᵐ·-zeroˡ {p = p} = 𝟘ᵐ?-elim
  (λ m → m ᵐ· p ≡ m)
  PE.refl
  only-𝟙ᵐ-without-𝟘ᵐ

-- ⌞_⌟ commutes with _·ᵐ_/_·_.

⌞⌟·ᵐ : ⌞ p ⌟ ·ᵐ ⌞ q ⌟ ≡ ⌞ p · q ⌟
⌞⌟·ᵐ {p = p} {q = q} = lemma _ _ _ refl refl refl
  where
  open Tools.Reasoning.PropositionalEquality

  lemma :
    ∀ m₁ m₂ m₃ → ⌞ p ⌟ ≡ m₁ → ⌞ q ⌟ ≡ m₂ → ⌞ p · q ⌟ ≡ m₃ →
    m₁ ·ᵐ m₂ ≡ m₃
  lemma 𝟘ᵐ _ _ ⌞p⌟≡𝟘ᵐ _ refl =
    𝟘ᵐ         ≡˘⟨ ⌞𝟘⌟ ⟩
    ⌞ 𝟘 ⌟      ≡˘⟨ cong ⌞_⌟ (·-zeroˡ _) ⟩
    ⌞ 𝟘 · q ⌟  ≡˘⟨ cong (λ p → ⌞ p · _ ⌟) (⌞⌟≡𝟘ᵐ→≡𝟘 ⌞p⌟≡𝟘ᵐ) ⟩
    ⌞ p · q ⌟  ∎
  lemma 𝟙ᵐ 𝟘ᵐ 𝟘ᵐ _ _ _ =
    𝟘ᵐ-cong
  lemma _ 𝟘ᵐ 𝟙ᵐ _ ⌞q⌟≡𝟘ᵐ ⌞pq⌟≡𝟙ᵐ =
    case
      𝟘ᵐ         ≡˘⟨ ⌞𝟘⌟ ⟩
      ⌞ 𝟘 ⌟      ≡˘⟨ cong ⌞_⌟ (·-zeroʳ _) ⟩
      ⌞ p · 𝟘 ⌟  ≡˘⟨ cong (λ q → ⌞ _ · q ⌟) (⌞⌟≡𝟘ᵐ→≡𝟘 ⌞q⌟≡𝟘ᵐ) ⟩
      ⌞ p · q ⌟  ≡⟨ ⌞pq⌟≡𝟙ᵐ ⟩
      𝟙ᵐ         ∎
    of λ ()
  lemma 𝟙ᵐ 𝟙ᵐ 𝟘ᵐ[ ok ] ⌞p⌟≡𝟙ᵐ ⌞q⌟≡𝟙ᵐ ⌞pq⌟≡𝟘ᵐ =
    case 𝟘ᵐ.zero-product ok (⌞⌟≡𝟘ᵐ→≡𝟘 ⌞pq⌟≡𝟘ᵐ) of λ where
      (inj₁ refl) →
        case
          𝟘ᵐ[ ok ]  ≡˘⟨ ⌞𝟘⌟ ⟩
          ⌞ 𝟘 ⌟     ≡⟨ ⌞p⌟≡𝟙ᵐ ⟩
          𝟙ᵐ        ∎
        of λ ()
      (inj₂ refl) →
        case
          𝟘ᵐ[ ok ]  ≡˘⟨ ⌞𝟘⌟ ⟩
          ⌞ 𝟘 ⌟     ≡⟨ ⌞q⌟≡𝟙ᵐ ⟩
          𝟙ᵐ        ∎
        of λ ()
  lemma 𝟙ᵐ 𝟙ᵐ 𝟙ᵐ _ _ _ = refl

-- ⌞_⌟ commutes with _· q/_ᵐ· q.

⌞⌟ᵐ· : ⌞ p ⌟ ᵐ· q ≡ ⌞ p · q ⌟
⌞⌟ᵐ· {p = p} {q = q} =
  ⌞ p ⌟ ᵐ· q      ≡˘⟨ ·ᵐ⌞⌟ ⟩
  ⌞ p ⌟ ·ᵐ ⌞ q ⌟  ≡⟨ ⌞⌟·ᵐ ⟩
  ⌞ p · q ⌟       ∎
  where
  open Tools.Reasoning.PropositionalEquality

-- A form of associativity.

ᵐ·-·-assoc : ∀ m → (m ᵐ· p) ᵐ· q ≡ m ᵐ· (p · q)
ᵐ·-·-assoc 𝟘ᵐ = PE.refl
ᵐ·-·-assoc 𝟙ᵐ = ⌞⌟ᵐ·

-- A form of associativity.

·ᵐ-ᵐ·-assoc : ∀ m₁ → (m₁ ·ᵐ m₂) ᵐ· p ≡ m₁ ·ᵐ (m₂ ᵐ· p)
·ᵐ-ᵐ·-assoc 𝟘ᵐ = PE.refl
·ᵐ-ᵐ·-assoc 𝟙ᵐ = PE.refl

-- A form of idempotence for _ᵐ·_.

⌞⌟·ᵐ-idem : ⌞ p ⌟ ᵐ· p ≡ ⌞ p ⌟
⌞⌟·ᵐ-idem {p = p} = lemma _ refl
  where
  lemma : ∀ m → ⌞ p ⌟ ≡ m → m ᵐ· p ≡ m
  lemma 𝟘ᵐ _      = refl
  lemma 𝟙ᵐ ⌞p⌟≡𝟙ᵐ = ⌞p⌟≡𝟙ᵐ

-- The function _ᵐ· p is idempotent.

ᵐ·-idem : ∀ m → (m ᵐ· p) ᵐ· p ≡ m ᵐ· p
ᵐ·-idem 𝟘ᵐ = PE.refl
ᵐ·-idem 𝟙ᵐ = ⌞⌟·ᵐ-idem

opaque

  -- A lemma relating _ᵐ·_ and _·ᵐ_.

  ᵐ·-·ᵐ-comm : ∀ m₁ → (m₁ ᵐ· p) ·ᵐ m₂ ≡ (m₁ ·ᵐ m₂) ᵐ· p
  ᵐ·-·ᵐ-comm               𝟘ᵐ = refl
  ᵐ·-·ᵐ-comm {p} {m₂ = 𝟙ᵐ} 𝟙ᵐ =
    ⌞ p ⌟ ·ᵐ 𝟙ᵐ  ≡⟨ ·ᵐ-identityʳ _ ⟩
    ⌞ p ⌟        ∎
    where
    open Tools.Reasoning.PropositionalEquality
  ᵐ·-·ᵐ-comm {p} {m₂ = 𝟘ᵐ} 𝟙ᵐ =
    ⌞ p ⌟ ·ᵐ 𝟘ᵐ  ≡⟨ ·ᵐ-comm ⌞ _ ⌟ _ ⟩
    𝟘ᵐ ·ᵐ ⌞ p ⌟  ≡⟨⟩
    𝟘ᵐ           ∎
    where
    open Tools.Reasoning.PropositionalEquality

-- Another lemma relating _ᵐ·_ and _·ᵐ_.

ᵐ·-·ᵐ : ∀ m → (m ᵐ· p) ·ᵐ m ≡ m ᵐ· p
ᵐ·-·ᵐ {p} m =
  (m ᵐ· p) ·ᵐ m  ≡⟨ ᵐ·-·ᵐ-comm m ⟩
  (m ·ᵐ m) ᵐ· p  ≡⟨ cong (_ᵐ· _) $ ·ᵐ-idem {m = m} ⟩
  m ᵐ· p         ∎
  where
  open Tools.Reasoning.PropositionalEquality

-- A lemma relating _ᵐ·_, _·ᵐ_ and ⌞_⌟.

ᵐ·-·ᵐ-⌞⌟ : ∀ m → (m ᵐ· p) ·ᵐ ⌞ p ⌟ ≡ m ᵐ· p
ᵐ·-·ᵐ-⌞⌟         𝟘ᵐ = PE.refl
ᵐ·-·ᵐ-⌞⌟ {p = p} 𝟙ᵐ =
  ⌞ p ⌟ ·ᵐ ⌞ p ⌟  ≡⟨ ·ᵐ-idem ⟩
  ⌞ p ⌟           ∎
  where
  open Tools.Reasoning.PropositionalEquality

-- If 𝟙 ≤ 𝟘, then the function taking p to ⌜ m ᵐ· p ⌝ is monotone for
-- every m.

⌜ᵐ·⌝-monotoneʳ : 𝟙 ≤ 𝟘 → ∀ m → p ≤ q → ⌜ m ᵐ· p ⌝ ≤ ⌜ m ᵐ· q ⌝
⌜ᵐ·⌝-monotoneʳ _   𝟘ᵐ = λ _ → ≤-refl
⌜ᵐ·⌝-monotoneʳ 𝟙≤𝟘 𝟙ᵐ = ⌜⌞⌟⌝-monotone 𝟙≤𝟘

-- The value p · ⌜ m ᵐ· p ⌝ is equivalent to ⌜ m ⌝ · p.

·⌜ᵐ·⌝ : ∀ m → p · ⌜ m ᵐ· p ⌝ ≡ p · ⌜ m ⌝
·⌜ᵐ·⌝         𝟘ᵐ = refl
·⌜ᵐ·⌝ {p = p} 𝟙ᵐ = begin
  p · ⌜ ⌞ p ⌟ ⌝  ≡⟨ ·⌜⌞⌟⌝ ⟩
  p              ≡˘⟨ ·-identityʳ _ ⟩
  p · 𝟙          ∎
  where
  open Tools.Reasoning.PropositionalEquality

opaque

  -- If "𝟘ᵐ is allowed" implies that p is non-zero, then m ᵐ· p is
  -- equal to m.

  ≢𝟘→ᵐ·≡′ : (T 𝟘ᵐ-allowed → p ≢ 𝟘) → m ᵐ· p ≡ m
  ≢𝟘→ᵐ·≡′ {m = 𝟘ᵐ} _ = PE.refl
  ≢𝟘→ᵐ·≡′ {m = 𝟙ᵐ}   = ≢𝟘→⌞⌟≡𝟙ᵐ′

-- A variant of ≢𝟘→ᵐ·≡′.

≢𝟘→ᵐ·≡ : p ≢ 𝟘 → m ᵐ· p ≡ m
≢𝟘→ᵐ·≡ p≢𝟘 = ≢𝟘→ᵐ·≡′ (λ _ → p≢𝟘)

-- 𝟙 is a right identity for _ᵐ·_.

ᵐ·-identityʳ : m ᵐ· 𝟙 ≡ m
ᵐ·-identityʳ = ≢𝟘→ᵐ·≡′ 𝟘ᵐ.non-trivial
