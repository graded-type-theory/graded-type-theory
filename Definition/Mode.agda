------------------------------------------------------------------------
-- Modes
------------------------------------------------------------------------

open import Definition.Modality

module Definition.Mode
  {a} {M : Set a} (𝕄 : Modality M) where

open Modality 𝕄

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Properties 𝕄
open import Tools.Algebra
open import Tools.Bool as B using (Bool; true; false; T)
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Nullary
open import Tools.Product
open import Tools.PropositionalEquality as PE
open import Tools.Unit
import Tools.Reasoning.Equivalence
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Sum

private variable
  n          : Nat
  p q r      : M
  γ δ        : Conₘ n
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
-- Basic definitions

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
  ⌞ p ⌟′ ok = case is-𝟘? ok p of λ where
    (yes _) → 𝟘ᵐ[ ok ]
    (no _)  → 𝟙ᵐ

-- Quantities can be translated to modes (in a potentially lossy way).

⌞_⌟ : M → Mode
⌞ p ⌟ = 𝟘ᵐ-allowed-elim ⌞ p ⌟′ (λ _ → 𝟙ᵐ)

-- Modes can be scaled by quantities.
--
-- This definition is based on the typing rule for application in Bob
-- Atkey's "Syntax and Semantics of Quantitative Type Theory".

infixr 45 _ᵐ·_

_ᵐ·_ : Mode → M → Mode
𝟘ᵐ ᵐ· _ = 𝟘ᵐ
𝟙ᵐ ᵐ· p = ⌞ p ⌟

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
-- Properties related to 𝟘ᵐ-allowed

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

------------------------------------------------------------------------
-- Properties related to 𝟘ᵐ?

-- Any two applications of 𝟘ᵐ[_] are equal.

𝟘ᵐ-cong : 𝟘ᵐ[ ok₁ ] ≡ 𝟘ᵐ[ ok₂ ]
𝟘ᵐ-cong = PE.cong 𝟘ᵐ[_] B.T-propositional

-- 𝟘ᵐ? is equal to 𝟘ᵐ[ ok ].

𝟘ᵐ?≡𝟘ᵐ : 𝟘ᵐ? ≡ 𝟘ᵐ[ ok ]
𝟘ᵐ?≡𝟘ᵐ {ok = ok} = 𝟘ᵐ?-elim
  (λ m → m ≡ 𝟘ᵐ[ ok ])
  𝟘ᵐ-cong
  (λ not-ok → ⊥-elim (not-ok ok))

------------------------------------------------------------------------
-- Properties related to _∨ᵐ_ and _·ᵐ_

-- The multiplication operation is idempotent.

·ᵐ-idem : m ·ᵐ m ≡ m
·ᵐ-idem {m = 𝟘ᵐ} = PE.refl
·ᵐ-idem {m = 𝟙ᵐ} = PE.refl

-- The operations _∨ᵐ_ and _·ᵐ_, along with the values 𝟘ᵐ and 𝟙ᵐ, form
-- a commutative semiring.

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
      ; *-isMonoid = record
        { isSemigroup = record
          { isMagma = record
            { isEquivalence = PE.isEquivalence
            ; ∙-cong        = cong₂ _·ᵐ_
            }
          ; assoc = λ where
              𝟘ᵐ _ _ → PE.refl
              𝟙ᵐ _ _ → PE.refl
          }
        ; identity =
              (λ _ → PE.refl)
            , (λ where
                 𝟘ᵐ → PE.refl
                 𝟙ᵐ → PE.refl)
        }
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

------------------------------------------------------------------------
-- Properties related to ⌜_⌝ and ⌜_⌝ᶜ

-- ⌜_⌝ commutes with _·_/_·ᵐ_.

⌜·ᵐ⌝ : ∀ m₁ → ⌜ m₁ ·ᵐ m₂ ⌝ ≈ ⌜ m₁ ⌝ · ⌜ m₂ ⌝
⌜·ᵐ⌝ {m₂ = m₂} 𝟘ᵐ = begin
  𝟘           ≈˘⟨ ·-zeroˡ _ ⟩
  𝟘 · ⌜ m₂ ⌝  ∎
  where
  open Tools.Reasoning.Equivalence (setoid M)
⌜·ᵐ⌝ {m₂ = m₂} 𝟙ᵐ = begin
  ⌜ m₂ ⌝      ≈˘⟨ ·-identityˡ _ ⟩
  𝟙 · ⌜ m₂ ⌝  ∎
  where
  open Tools.Reasoning.Equivalence (setoid M)

-- A form of commutativity.

⌜⌝-·-comm : ∀ m → ⌜ m ⌝ · p ≈ p · ⌜ m ⌝
⌜⌝-·-comm {p = p} 𝟘ᵐ = begin
  𝟘 · p  ≈⟨ ·-zeroˡ _ ⟩
  𝟘      ≈˘⟨ ·-zeroʳ _ ⟩
  p · 𝟘  ∎
  where
  open Tools.Reasoning.Equivalence (setoid M)
⌜⌝-·-comm {p = p} 𝟙ᵐ = begin
  𝟙 · p  ≈⟨ ·-identityˡ _ ⟩
  p      ≈˘⟨ ·-identityʳ _ ⟩
  p · 𝟙  ∎
  where
  open Tools.Reasoning.Equivalence (setoid M)

-- A form of associativity.

·ᵐ-·-assoc : ∀ m₁ → ⌜ m₁ ·ᵐ m₂ ⌝ · p ≈ ⌜ m₁ ⌝ · ⌜ m₂ ⌝ · p
·ᵐ-·-assoc {m₂ = m₂} {p = p} m₁ = begin
  ⌜ m₁ ·ᵐ m₂ ⌝ · p       ≈⟨ ·-congʳ (⌜·ᵐ⌝ m₁) ⟩
  (⌜ m₁ ⌝ · ⌜ m₂ ⌝) · p  ≈⟨ ·-assoc _ _ _ ⟩
  ⌜ m₁ ⌝ · ⌜ m₂ ⌝ · p    ∎
  where
  open Tools.Reasoning.Equivalence (setoid M)

-- A form of associativity.

·ᵐ-·ᶜ-assoc : ∀ m₁ → ⌜ m₁ ·ᵐ m₂ ⌝ ·ᶜ γ ≈ᶜ ⌜ m₁ ⌝ ·ᶜ ⌜ m₂ ⌝ ·ᶜ γ
·ᵐ-·ᶜ-assoc {γ = ε}     m₁ = ε
·ᵐ-·ᶜ-assoc {γ = _ ∙ _} m₁ = ·ᵐ-·ᶜ-assoc m₁ ∙ ·ᵐ-·-assoc m₁

-- ⌜ m ⌝ ·_ distributes over _⊛_▷ r from the left.

⌜⌝-·-distribˡ-⊛ :
  ∀ m → ⌜ m ⌝ · p ⊛ q ▷ r ≈ (⌜ m ⌝ · p) ⊛ ⌜ m ⌝ · q ▷ r
⌜⌝-·-distribˡ-⊛ {p = p} {q = q} {r = r} 𝟙ᵐ = begin
  𝟙 · p ⊛ q ▷ r        ≈⟨ ·-identityˡ _ ⟩
  p ⊛ q ▷ r            ≈˘⟨ ⊛ᵣ-cong (·-identityˡ _) (·-identityˡ _) ⟩
  (𝟙 · p) ⊛ 𝟙 · q ▷ r  ∎
  where
  open Tools.Reasoning.Equivalence (setoid M)
⌜⌝-·-distribˡ-⊛ {p = p} {q = q} {r = r} 𝟘ᵐ =
  let open Tools.Reasoning.Equivalence (setoid M) in begin
  𝟘 · p ⊛ q ▷ r        ≈⟨ ·-zeroˡ _ ⟩
  𝟘                    ≈˘⟨ ⊛-idem-𝟘 _ ⟩
  𝟘 ⊛ 𝟘 ▷ r            ≈˘⟨ ⊛ᵣ-cong (·-zeroˡ _) (·-zeroˡ _) ⟩
  (𝟘 · p) ⊛ 𝟘 · q ▷ r  ∎

-- ⌜ m ⌝ ·ᶜ_ distributes over _⊛ᶜ_▷ r from the left.

⌜⌝-·ᶜ-distribˡ-⊛ᶜ :
  ∀ m → ⌜ m ⌝ ·ᶜ γ ⊛ᶜ δ ▷ r ≈ᶜ (⌜ m ⌝ ·ᶜ γ) ⊛ᶜ ⌜ m ⌝ ·ᶜ δ ▷ r
⌜⌝-·ᶜ-distribˡ-⊛ᶜ {γ = ε}     {δ = ε}     _ = ε
⌜⌝-·ᶜ-distribˡ-⊛ᶜ {γ = _ ∙ _} {δ = _ ∙ _} m =
  ⌜⌝-·ᶜ-distribˡ-⊛ᶜ m ∙ ⌜⌝-·-distribˡ-⊛ m

-- The result of looking up the x-th entry in ⌜ ms ⌝ᶜ is ⌜ ms x ⌝.

⌜⌝ᶜ⟨⟩ : (x : Fin n) → ⌜ ms ⌝ᶜ ⟨ x ⟩ ≡ ⌜ ms x ⌝
⌜⌝ᶜ⟨⟩ x0     = PE.refl
⌜⌝ᶜ⟨⟩ (x +1) = ⌜⌝ᶜ⟨⟩ x

-- If 𝟘ᵐ is allowed, then ⌜ 𝟘ᵐ? ⌝ is equal to 𝟘.

⌜𝟘ᵐ?⌝≈𝟘 : T 𝟘ᵐ-allowed → ⌜ 𝟘ᵐ? ⌝ ≡ 𝟘
⌜𝟘ᵐ?⌝≈𝟘 ok =
  ⌜ 𝟘ᵐ? ⌝       ≡⟨ cong ⌜_⌝ (𝟘ᵐ?≡𝟘ᵐ {ok = ok}) ⟩
  ⌜ 𝟘ᵐ[ ok ] ⌝  ≡⟨⟩
  𝟘             ∎
  where
  open Tools.Reasoning.PropositionalEquality

------------------------------------------------------------------------
-- Properties related to ⌞_⌟ and ⌞_⌟ᶜ

-- The function ⌞_⌟ preserves "equality".

⌞⌟-cong : p ≈ q → ⌞ p ⌟ ≡ ⌞ q ⌟
⌞⌟-cong refl = refl

-- The function ⌞_⌟ᶜ preserves "equality".

⌞⌟ᶜ-cong : γ ≈ᶜ δ → ∀ x → ⌞ γ ⌟ᶜ x ≡ ⌞ δ ⌟ᶜ x
⌞⌟ᶜ-cong (γ≈δ ∙ p≈q) = λ where
  x0     → ⌞⌟-cong p≈q
  (x +1) → ⌞⌟ᶜ-cong γ≈δ x

-- ⌞ 𝟘 ⌟ is equal to 𝟘ᵐ[ ok ].

⌞𝟘⌟ : ⌞ 𝟘 ⌟ ≡ 𝟘ᵐ[ ok ]
⌞𝟘⌟ = lemma _ refl
  where
  lemma :
    ∀ b (eq : b ≡ 𝟘ᵐ-allowed) {ok : T b} →
    𝟘ᵐ-allowed-elim-helper b
      (λ ok → ⌞ 𝟘 ⌟′ (subst T eq ok))
      (λ _ → 𝟙ᵐ) ≡
    𝟘ᵐ[ subst T eq ok ]
  lemma true refl with is-𝟘? tt 𝟘
  … | yes _  = refl
  … | no 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 refl)

-- If p is equal to 𝟘, then ⌞ p ⌟ is equal to 𝟘ᵐ[ ok ].

≈𝟘→⌞⌟≡𝟘ᵐ : p ≈ 𝟘 → ⌞ p ⌟ ≡ 𝟘ᵐ[ ok ]
≈𝟘→⌞⌟≡𝟘ᵐ refl = ⌞𝟘⌟

-- ⌞ 𝟘 ⌟ is equal to 𝟘ᵐ?.

⌞𝟘⌟≡𝟘ᵐ? : ⌞ 𝟘 ⌟ ≡ 𝟘ᵐ?
⌞𝟘⌟≡𝟘ᵐ? = 𝟘ᵐ?-elim
  (⌞ 𝟘 ⌟ ≡_)
  ⌞𝟘⌟
  only-𝟙ᵐ-without-𝟘ᵐ

-- If p is equal to 𝟘, then ⌞ p ⌟ is equal to 𝟘ᵐ?.

≈𝟘→⌞⌟≡𝟘ᵐ? : p ≈ 𝟘 → ⌞ p ⌟ ≡ 𝟘ᵐ?
≈𝟘→⌞⌟≡𝟘ᵐ? refl = ⌞𝟘⌟≡𝟘ᵐ?

-- If ⌞ p ⌟ is equal to 𝟘ᵐ[ ok ], then p is equal to 𝟘.

⌞⌟≡𝟘ᵐ→≈𝟘 : ⌞ p ⌟ ≡ 𝟘ᵐ[ ok ] → p ≈ 𝟘
⌞⌟≡𝟘ᵐ→≈𝟘 {p = p} = lemma _ refl
  where
  lemma :
    ∀ b (eq : b ≡ 𝟘ᵐ-allowed) →
    𝟘ᵐ-allowed-elim-helper b
      (λ ok → ⌞ p ⌟′ (subst T eq ok))
      (λ _ → 𝟙ᵐ) ≡
    𝟘ᵐ[ ok ] →
    p ≡ 𝟘
  lemma true refl with is-𝟘? tt p
  … | yes p≡𝟘 = λ _ → p≡𝟘
  … | no _    = λ ()

-- If p is not equal to 𝟘, then ⌞ p ⌟ is equal to 𝟙ᵐ.

≉𝟘→⌞⌟≡𝟙ᵐ : p ≉ 𝟘 → ⌞ p ⌟ ≡ 𝟙ᵐ
≉𝟘→⌞⌟≡𝟙ᵐ {p = p} p≉𝟘 = lemma _ refl
  where
  lemma :
    ∀ b (eq : b ≡ 𝟘ᵐ-allowed) →
    𝟘ᵐ-allowed-elim-helper b
      (λ ok → ⌞ p ⌟′ (subst T eq ok))
      (λ _ → 𝟙ᵐ) ≡
    𝟙ᵐ
  lemma false refl = refl
  lemma true  refl with is-𝟘? tt p
  … | no _    = refl
  … | yes p≈𝟘 = ⊥-elim (p≉𝟘 p≈𝟘)

-- If 𝟘ᵐ is allowed and ⌞ p ⌟ is equal to 𝟙ᵐ, then p is not equal to
-- 𝟘.

⌞⌟≡𝟙ᵐ→≉𝟘 : T 𝟘ᵐ-allowed → ⌞ p ⌟ ≡ 𝟙ᵐ → p ≉ 𝟘
⌞⌟≡𝟙ᵐ→≉𝟘 {p = p} ok = lemma _ refl
  where
  lemma :
    ∀ b (eq : b ≡ 𝟘ᵐ-allowed) →
    𝟘ᵐ-allowed-elim-helper b
      (λ ok → ⌞ p ⌟′ (subst T eq ok))
      (λ _ → 𝟙ᵐ) ≡
    𝟙ᵐ →
    p ≢ 𝟘
  lemma false refl = ⊥-elim ok
  lemma true  refl with is-𝟘? tt p
  … | yes _  = λ ()
  … | no p≢𝟘 = λ _ → p≢𝟘

-- ⌞ 𝟙 ⌟ is equal to 𝟙ᵐ.

⌞𝟙⌟ : ⌞ 𝟙 ⌟ ≡ 𝟙ᵐ
⌞𝟙⌟ = 𝟘ᵐ-allowed-elim
  (λ ok → ≉𝟘→⌞⌟≡𝟙ᵐ (𝟘ᵐ→𝟙≉𝟘 ok))
  only-𝟙ᵐ-without-𝟘ᵐ

-- The function taking p to ⌜ ⌞ p ⌟ ⌝ preserves equivalence.

⌜⌞⌟⌝-cong : p ≈ q → ⌜ ⌞ p ⌟ ⌝ ≈ ⌜ ⌞ q ⌟ ⌝
⌜⌞⌟⌝-cong p≈q = ≈-reflexive (cong ⌜_⌝ (⌞⌟-cong p≈q))

-- If 𝟙 ≤ 𝟘, then the function taking p to ⌜ ⌞ p ⌟ ⌝ is monotone.

⌜⌞⌟⌝-monotone : 𝟙 ≤ 𝟘 → p ≤ q → ⌜ ⌞ p ⌟ ⌝ ≤ ⌜ ⌞ q ⌟ ⌝
⌜⌞⌟⌝-monotone {p = p} {q = q} 𝟙≤𝟘 p≤q = lemma _ _ refl refl
  where
  lemma : ∀ m₁ m₂ → ⌞ p ⌟ ≡ m₁ → ⌞ q ⌟ ≡ m₂ → ⌜ m₁ ⌝ ≤ ⌜ m₂ ⌝
  lemma 𝟘ᵐ       𝟘ᵐ _      _      = ≤-refl
  lemma 𝟙ᵐ       𝟙ᵐ _      _      = ≤-refl
  lemma 𝟙ᵐ       𝟘ᵐ _      _      = 𝟙≤𝟘
  lemma 𝟘ᵐ[ ok ] 𝟙ᵐ ⌞p⌟≡𝟘ᵐ ⌞q⌟≡𝟙ᵐ =
    ⊥-elim (⌞⌟≡𝟙ᵐ→≉𝟘 ok ⌞q⌟≡𝟙ᵐ (𝟘≮ ok (begin
      𝟘  ≈˘⟨ ⌞⌟≡𝟘ᵐ→≈𝟘 ⌞p⌟≡𝟘ᵐ ⟩
      p  ≤⟨ p≤q ⟩
      q  ∎)))
    where
    open Tools.Reasoning.PartialOrder ≤-poset

-- The value p · ⌜ ⌞ p ⌟ ⌝ is equal to p.

·⌜⌞⌟⌝ : p · ⌜ ⌞ p ⌟ ⌝ ≈ p
·⌜⌞⌟⌝ {p = p} = lemma _ refl
  where
  open Tools.Reasoning.PropositionalEquality

  lemma : ∀ m → ⌞ p ⌟ ≡ m → p · ⌜ m ⌝ ≡ p
  lemma 𝟙ᵐ _ =
    p · 𝟙  ≡⟨ ·-identityʳ _ ⟩
    p      ∎
  lemma 𝟘ᵐ ⌞p⌟≡𝟘ᵐ =
    p · 𝟘  ≡⟨ ·-zeroʳ _ ⟩
    𝟘      ≡˘⟨ ⌞⌟≡𝟘ᵐ→≈𝟘 ⌞p⌟≡𝟘ᵐ ⟩
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

-- If 1 ≈ 𝟘, then ⌞ p ⌟ is equal to 𝟘ᵐ?.

⌞⌟≡𝟘ᵐ : 𝟙 ≈ 𝟘 → ⌞ p ⌟ ≡ 𝟘ᵐ?
⌞⌟≡𝟘ᵐ {p = p} 𝟙≈𝟘 =
  ⌞ p ⌟  ≡⟨ ⌞⌟-cong (≈-trivial 𝟙≈𝟘) ⟩
  ⌞ 𝟘 ⌟  ≡⟨ ⌞𝟘⌟≡𝟘ᵐ? ⟩
  𝟘ᵐ?    ∎
  where
  open Tools.Reasoning.PropositionalEquality

------------------------------------------------------------------------
-- Properties related to _ᵐ·_

-- The function m ᵐ·_ preserves "equality".

ᵐ·-cong : ∀ m → p ≈ q → m ᵐ· p ≡ m ᵐ· q
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
    ⌞ 𝟘 · q ⌟  ≡˘⟨ cong (λ p → ⌞ p · _ ⌟) (⌞⌟≡𝟘ᵐ→≈𝟘 ⌞p⌟≡𝟘ᵐ) ⟩
    ⌞ p · q ⌟  ∎
  lemma 𝟙ᵐ 𝟘ᵐ 𝟘ᵐ _ _ _ =
    𝟘ᵐ-cong
  lemma _ 𝟘ᵐ 𝟙ᵐ _ ⌞q⌟≡𝟘ᵐ ⌞pq⌟≡𝟙ᵐ =
    case
      𝟘ᵐ         ≡˘⟨ ⌞𝟘⌟ ⟩
      ⌞ 𝟘 ⌟      ≡˘⟨ cong ⌞_⌟ (·-zeroʳ _) ⟩
      ⌞ p · 𝟘 ⌟  ≡˘⟨ cong (λ q → ⌞ _ · q ⌟) (⌞⌟≡𝟘ᵐ→≈𝟘 ⌞q⌟≡𝟘ᵐ) ⟩
      ⌞ p · q ⌟  ≡⟨ ⌞pq⌟≡𝟙ᵐ ⟩
      𝟙ᵐ         ∎
    of λ ()
  lemma 𝟙ᵐ 𝟙ᵐ 𝟘ᵐ[ ok ] ⌞p⌟≡𝟙ᵐ ⌞q⌟≡𝟙ᵐ ⌞pq⌟≡𝟘ᵐ =
    case zero-product ok (⌞⌟≡𝟘ᵐ→≈𝟘 ⌞pq⌟≡𝟘ᵐ) of λ where
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

-- A lemma relating _ᵐ·_ and _·ᵐ_.

ᵐ·-·ᵐ : ∀ m → (m ᵐ· p) ·ᵐ m ≡ m ᵐ· p
ᵐ·-·ᵐ         𝟘ᵐ = PE.refl
ᵐ·-·ᵐ {p = p} 𝟙ᵐ =
  ⌞ p ⌟ ·ᵐ 𝟙ᵐ  ≡⟨ ·ᵐ-identityʳ _ ⟩
  ⌞ p ⌟        ∎
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

·⌜ᵐ·⌝ : ∀ m → p · ⌜ m ᵐ· p ⌝ ≈ p · ⌜ m ⌝
·⌜ᵐ·⌝         𝟘ᵐ = ≈-refl
·⌜ᵐ·⌝ {p = p} 𝟙ᵐ = begin
  p · ⌜ ⌞ p ⌟ ⌝  ≈⟨ ·⌜⌞⌟⌝ ⟩
  p              ≈˘⟨ ·-identityʳ _ ⟩
  p · 𝟙          ∎
  where
  open Tools.Reasoning.Equivalence (setoid M)

-- If p is non-zero, then m ᵐ· p is equal to m.

≉𝟘→ᵐ·≡ : p ≉ 𝟘 → m ᵐ· p ≡ m
≉𝟘→ᵐ·≡ {m = 𝟘ᵐ} _ = PE.refl
≉𝟘→ᵐ·≡ {m = 𝟙ᵐ}   = ≉𝟘→⌞⌟≡𝟙ᵐ

-- If 1 ≈ 𝟘, then m ᵐ· p is equal to m.

ᵐ·-identityʳ : 𝟙 ≈ 𝟘 → m ᵐ· p ≡ m
ᵐ·-identityʳ {m = 𝟘ᵐ}         _   = PE.refl
ᵐ·-identityʳ {m = 𝟙ᵐ} {p = p} 𝟙≈𝟘 =
  ⌞ p ⌟  ≡⟨ ⌞⌟≡𝟘ᵐ 𝟙≈𝟘 ⟩
  𝟘ᵐ?    ≡⟨ only-𝟙ᵐ-without-𝟘ᵐ (λ ok → 𝟘ᵐ→𝟙≉𝟘 ok 𝟙≈𝟘) ⟩
  𝟙ᵐ     ∎
  where
  open Tools.Reasoning.PropositionalEquality
