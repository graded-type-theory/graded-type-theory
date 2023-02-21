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
import Tools.Reasoning.Equivalence
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

private variable
  n          : Nat
  p q r      : M
  γ δ        : Conₘ n
  b          : Bool
  ok ok₁ ok₂ : T b

------------------------------------------------------------------------
-- Definitions

-- Modes.

data Mode : Set where
  𝟘ᵐ : ⦃ ok : T 𝟘ᵐ-allowed ⦄ → Mode
  𝟙ᵐ : Mode

pattern 𝟘ᵐ[_] ok = 𝟘ᵐ ⦃ ok = ok ⦄

private variable
  m m₁ m₁′ m₂ m₂′ m₃ : Mode

private

  -- A function used in the implementation of 𝟘ᵐ?.

  𝟘ᵐ′ : ∀ b → b ≡ 𝟘ᵐ-allowed → Mode
  𝟘ᵐ′ true  eq = 𝟘ᵐ[ subst T eq _ ]
  𝟘ᵐ′ false _  = 𝟙ᵐ

-- A mode that is 𝟘ᵐ[ something ] if 𝟘ᵐ-allowed is true, and otherwise
-- 𝟙ᵐ.

𝟘ᵐ? : Mode
𝟘ᵐ? = 𝟘ᵐ′ 𝟘ᵐ-allowed PE.refl

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

-- Quantities can be translated to modes (in a potentially lossy way).

⌞_⌟ : M → Mode
⌞ p ⌟ = case is-𝟘? p of λ where
  (yes _) → 𝟘ᵐ?
  (no _)  → 𝟙ᵐ

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
-- Some eliminators or similar principles

-- One can prove that a predicate holds for 𝟘ᵐ-allowed by proving that
-- it holds given that T 𝟘ᵐ-allowed is inhabited, and that it holds
-- given that T 𝟘ᵐ-allowed is not inhabited.

𝟘ᵐ-allowed-elim :
  ∀ {p} {P : Set p} →
  (T 𝟘ᵐ-allowed → P) →
  ((not-ok : ¬ T 𝟘ᵐ-allowed) → P) →
  P
𝟘ᵐ-allowed-elim t f with 𝟘ᵐ-allowed
… | true  = t _
… | false = f (λ ())

-- An eliminator for modes.

Mode-elim :
  ∀ {p} (P : Mode → Set p) →
  (⦃ ok : T 𝟘ᵐ-allowed ⦄ → P 𝟘ᵐ[ ok ]) →
  P 𝟙ᵐ →
  ∀ m → P m
Mode-elim _ z o = λ where
  𝟘ᵐ[ ok ] → z ⦃ ok = ok ⦄
  𝟙ᵐ       → o

-- One can prove that a predicate holds for 𝟘ᵐ? by proving that it
-- holds for 𝟘ᵐ[ ok ] (for any ok) and that it holds for 𝟙ᵐ (under the
-- assumption that T 𝟘ᵐ-allowed is not inhabited).

𝟘ᵐ?-elim :
  ∀ {p} (P : Mode → Set p) →
  (⦃ ok : T 𝟘ᵐ-allowed ⦄ → P 𝟘ᵐ) →
  (¬ T 𝟘ᵐ-allowed → P 𝟙ᵐ) →
  P 𝟘ᵐ?
𝟘ᵐ?-elim P z o = lemma _ _
  where
  lemma : ∀ b (eq : b ≡ 𝟘ᵐ-allowed) → P (𝟘ᵐ′ b eq)
  lemma false eq = o (PE.subst T (PE.sym eq))
  lemma true  eq = z ⦃ ok = PE.subst T eq _ ⦄

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

-- If 𝟘ᵐ is not allowed, then 𝟘ᵐ? is equal to 𝟙ᵐ.

𝟘ᵐ?≡𝟙ᵐ : ¬ T 𝟘ᵐ-allowed → 𝟘ᵐ? ≡ 𝟙ᵐ
𝟘ᵐ?≡𝟙ᵐ not-ok = 𝟘ᵐ?-elim
  (_≡ 𝟙ᵐ)
  (λ ⦃ ok = ok ⦄ → ⊥-elim (not-ok ok))
  (λ _ → PE.refl)

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

------------------------------------------------------------------------
-- Properties related to ⌞_⌟ and ⌞_⌟ᶜ

-- The function ⌞_⌟ preserves "equality".

⌞⌟-cong : p ≈ q → ⌞ p ⌟ ≡ ⌞ q ⌟
⌞⌟-cong {p = p} {q = q} p≈q with is-𝟘? p | is-𝟘? q
… | yes _   | yes _  = PE.refl
… | no _    | no _   = PE.refl
… | yes p≈𝟘 | no q≉𝟘 = ⊥-elim (q≉𝟘 (begin
  q  ≈˘⟨ p≈q ⟩
  p  ≈⟨ p≈𝟘 ⟩
  𝟘  ∎))
  where
  open Tools.Reasoning.Equivalence (setoid M)
… | no p≉𝟘 | yes q≈𝟘 = ⊥-elim (p≉𝟘 (begin
  p  ≈⟨ p≈q ⟩
  q  ≈⟨ q≈𝟘 ⟩
  𝟘  ∎))
  where
  open Tools.Reasoning.Equivalence (setoid M)

-- The function ⌞_⌟ᶜ preserves "equality".

⌞⌟ᶜ-cong : γ ≈ᶜ δ → ∀ x → ⌞ γ ⌟ᶜ x ≡ ⌞ δ ⌟ᶜ x
⌞⌟ᶜ-cong (γ≈δ ∙ p≈q) = λ where
  x0     → ⌞⌟-cong p≈q
  (x +1) → ⌞⌟ᶜ-cong γ≈δ x

-- If p is equivalent to 𝟘, then ⌞ p ⌟ is equal to 𝟘ᵐ?.

≈𝟘→⌞⌟≡𝟘ᵐ? : p ≈ 𝟘 → ⌞ p ⌟ ≡ 𝟘ᵐ?
≈𝟘→⌞⌟≡𝟘ᵐ? {p = p} p≈𝟘 with is-𝟘? p
… | yes _  = PE.refl
… | no p≉𝟘 = ⊥-elim (p≉𝟘 p≈𝟘)

-- If p is equivalent to 𝟘, then ⌞ p ⌟ is equal to 𝟘ᵐ[ ok ].

≈𝟘→⌞⌟≡𝟘ᵐ : p ≈ 𝟘 → ⌞ p ⌟ ≡ 𝟘ᵐ[ ok ]
≈𝟘→⌞⌟≡𝟘ᵐ {p = p} {ok = ok} p≈𝟘 =
  ⌞ p ⌟     ≡⟨ ≈𝟘→⌞⌟≡𝟘ᵐ? p≈𝟘 ⟩
  𝟘ᵐ?       ≡⟨ 𝟘ᵐ?≡𝟘ᵐ ⟩
  𝟘ᵐ[ ok ]  ∎
  where
  open Tools.Reasoning.PropositionalEquality

-- If p is not equivalent to 𝟘, then ⌞ p ⌟ is equal to 𝟙ᵐ.

≉𝟘→⌞⌟≡𝟙ᵐ : p ≉ 𝟘 → ⌞ p ⌟ ≡ 𝟙ᵐ
≉𝟘→⌞⌟≡𝟙ᵐ {p = p} p≉𝟘 with is-𝟘? p
… | no _    = PE.refl
… | yes p≈𝟘 = ⊥-elim (p≉𝟘 p≈𝟘)

-- If ⌞ p ⌟ is equal to 𝟘ᵐ[ ok ], then p is equivalent to 𝟘.

⌞⌟≡𝟘ᵐ→≈𝟘 : ⌞ p ⌟ ≡ 𝟘ᵐ[ ok ] → p ≈ 𝟘
⌞⌟≡𝟘ᵐ→≈𝟘 {p = p} _  with is-𝟘? p
⌞⌟≡𝟘ᵐ→≈𝟘         _  | yes p≈𝟘 = p≈𝟘
⌞⌟≡𝟘ᵐ→≈𝟘         () | no _

-- If 𝟘ᵐ is allowed and ⌞ p ⌟ is equal to 𝟙ᵐ, then p is not equivalent
-- to 𝟘.

⌞⌟≡𝟙ᵐ→≉𝟘 : T 𝟘ᵐ-allowed → ⌞ p ⌟ ≡ 𝟙ᵐ → p ≉ 𝟘
⌞⌟≡𝟙ᵐ→≉𝟘 {p = p} ok _      with is-𝟘? p
⌞⌟≡𝟙ᵐ→≉𝟘         ok _      | no p≉𝟘 = p≉𝟘
⌞⌟≡𝟙ᵐ→≉𝟘         ok 𝟘ᵐ?≡𝟙ᵐ | yes _  =
  case 𝟘ᵐ[ ok ]  ≡˘⟨ 𝟘ᵐ?≡𝟘ᵐ ⟩
       𝟘ᵐ?       ≡⟨ 𝟘ᵐ?≡𝟙ᵐ ⟩
       𝟙ᵐ        ∎
  of λ ()
  where
  open Tools.Reasoning.PropositionalEquality

-- The value of ⌞ 𝟘 ⌟ is 𝟘ᵐ?.

⌞𝟘⌟≡𝟘ᵐ? : ⌞ 𝟘 ⌟ ≡ 𝟘ᵐ?
⌞𝟘⌟≡𝟘ᵐ? = ≈𝟘→⌞⌟≡𝟘ᵐ? ≈-refl

-- ⌞ 𝟘 ⌟ is equal to 𝟘ᵐ[ ok ].

⌞𝟘⌟ : ⌞ 𝟘 ⌟ ≡ 𝟘ᵐ[ ok ]
⌞𝟘⌟ {ok = ok} = begin
  ⌞ 𝟘 ⌟     ≡⟨ ⌞𝟘⌟≡𝟘ᵐ? ⟩
  𝟘ᵐ?       ≡⟨ 𝟘ᵐ?≡𝟘ᵐ ⟩
  𝟘ᵐ[ ok ]  ∎
  where
  open Tools.Reasoning.PropositionalEquality

-- If 𝟙 ≉ 𝟘, then the value of ⌞ 𝟙 ⌟ is 𝟙ᵐ.

⌞𝟙⌟ : 𝟙 ≉ 𝟘 → ⌞ 𝟙 ⌟ ≡ 𝟙ᵐ
⌞𝟙⌟ = ≉𝟘→⌞⌟≡𝟙ᵐ

-- The function taking p to ⌜ ⌞ p ⌟ ⌝ preserves equivalence.

⌜⌞⌟⌝-cong : p ≈ q → ⌜ ⌞ p ⌟ ⌝ ≈ ⌜ ⌞ q ⌟ ⌝
⌜⌞⌟⌝-cong p≈q = ≈-reflexive (cong ⌜_⌝ (⌞⌟-cong p≈q))

-- If 𝟙 ≤ 𝟘, then the function taking p to ⌜ ⌞ p ⌟ ⌝ is monotone.

⌜⌞⌟⌝-monotone : 𝟙 ≤ 𝟘 → p ≤ q → ⌜ ⌞ p ⌟ ⌝ ≤ ⌜ ⌞ q ⌟ ⌝
⌜⌞⌟⌝-monotone {p = p} {q = q} 𝟙≤𝟘 p≤q with is-𝟘? p | is-𝟘? q
… | yes _ | yes _ = ≤-refl
… | no _  | no _  = ≤-refl
… | no _  | yes _ = 𝟘ᵐ?-elim
  (λ m → 𝟙 ≈ 𝟙 ∧ ⌜ m ⌝)
  𝟙≤𝟘
  (λ _ → ≤-refl)
… | yes p≈𝟘 | no q≉𝟘 = ⊥-elim (q≉𝟘 (𝟘≮ (begin
  𝟘  ≈˘⟨ p≈𝟘 ⟩
  p  ≤⟨ p≤q ⟩
  q  ∎)))
  where
  open Tools.Reasoning.PartialOrder ≤-poset

-- The value p · ⌜ ⌞ p ⌟ ⌝ is equivalent to p.

·⌜⌞⌟⌝ : p · ⌜ ⌞ p ⌟ ⌝ ≈ p
·⌜⌞⌟⌝ {p = p} with is-𝟘? p
… | no _ = begin
  p · 𝟙  ≈⟨ ·-identityʳ _ ⟩
  p      ∎
  where
  open Tools.Reasoning.Equivalence (setoid M)
… | yes p≈𝟘 = 𝟘ᵐ?-elim
  (λ m → p · ⌜ m ⌝ ≈ p)
  (begin
     p · 𝟘  ≈⟨ ·-zeroʳ _ ⟩
     𝟘      ≈˘⟨ p≈𝟘 ⟩
     p      ∎)
  (λ _ → ·-identityʳ _)
  where
  open Tools.Reasoning.Equivalence (setoid M)

-- The function ⌞_⌟ is a left inverse of ⌜_⌝ if 𝟙 ≉ 𝟘.

⌞⌜⌝⌟ : 𝟙 ≉ 𝟘 → ∀ m → ⌞ ⌜ m ⌝ ⌟ ≡ m
⌞⌜⌝⌟ _   𝟘ᵐ = ⌞𝟘⌟
⌞⌜⌝⌟ 𝟙≉𝟘 𝟙ᵐ = ⌞𝟙⌟ 𝟙≉𝟘

-- The function ⌜_⌝ is a left inverse of ⌞_⌟ (up to _≈_) for arguments
-- in the image of ⌜_⌝.

⌜⌞⌜⌝⌟⌝ : ∀ m → ⌜ ⌞ ⌜ m ⌝ ⌟ ⌝ ≈ ⌜ m ⌝
⌜⌞⌜⌝⌟⌝ 𝟘ᵐ[ ok ] = begin
  ⌜ ⌞ 𝟘 ⌟ ⌝  ≡⟨ cong ⌜_⌝ (⌞𝟘⌟ {ok = ok}) ⟩
  ⌜ 𝟘ᵐ ⌝     ≡⟨⟩
  𝟘          ∎
  where
  open Tools.Reasoning.Equivalence (setoid M)
⌜⌞⌜⌝⌟⌝ 𝟙ᵐ with is-𝟘? 𝟙
… | no _    = ≈-refl
… | yes 𝟙≈𝟘 = 𝟘ᵐ?-elim
  (λ m → ⌜ m ⌝ ≈ 𝟙)
  (≈-sym 𝟙≈𝟘)
  (λ _ → ≈-refl)

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
⌞⌟≡𝟘ᵐ {p = p} 𝟙≈𝟘 with is-𝟘? p
… | yes _  = PE.refl
… | no p≉𝟘 = ⊥-elim (p≉𝟘 (begin
  p      ≈˘⟨ ·-identityʳ _ ⟩
  p · 𝟙  ≈⟨ ·-congˡ 𝟙≈𝟘 ⟩
  p · 𝟘  ≈⟨ ·-zeroʳ _ ⟩
  𝟘      ∎))
  where
  open Tools.Reasoning.Equivalence (setoid M)

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

-- A form of associativity.

·ᵐ-ᵐ·-assoc : ∀ m₁ → (m₁ ·ᵐ m₂) ᵐ· p ≡ m₁ ·ᵐ (m₂ ᵐ· p)
·ᵐ-ᵐ·-assoc 𝟘ᵐ = PE.refl
·ᵐ-ᵐ·-assoc 𝟙ᵐ = PE.refl

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

-- If 1 ≈ 𝟘, then m ᵐ· p is equal to m.

ᵐ·-identityʳ : 𝟙 ≈ 𝟘 → m ᵐ· p ≡ m
ᵐ·-identityʳ {m = 𝟘ᵐ}         _   = PE.refl
ᵐ·-identityʳ {m = 𝟙ᵐ} {p = p} 𝟙≈𝟘 =
  ⌞ p ⌟  ≡⟨ ⌞⌟≡𝟘ᵐ 𝟙≈𝟘 ⟩
  𝟘ᵐ?    ≡⟨ 𝟘ᵐ?≡𝟙ᵐ (λ ok → 𝟘ᵐ→𝟙≉𝟘 ok 𝟙≈𝟘) ⟩
  𝟙ᵐ     ∎
  where
  open Tools.Reasoning.PropositionalEquality
