------------------------------------------------------------------------
-- The mode instances Zero-one, either the single mode instance or the
-- two mode instance.
------------------------------------------------------------------------

open import Tools.Bool as B using (Bool; true; false; T)
import Graded.Modality
open import Graded.Mode.Instances.Zero-one.Variant

module Graded.Mode.Instances.Zero-one
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (open Modality 𝕄)
  (mode-variant : Mode-variant 𝕄)
  where

open Mode-variant mode-variant

open import Graded.Context 𝕄
open import Graded.Mode
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄
open import Tools.Algebra
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
open import Tools.PropositionalEquality as PE
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
-- An instance for Has-well-behaved-zero

private opaque instance

  𝟘ᵐ-allowed→𝟘-well-behaved :
    ⦃ ok : T 𝟘ᵐ-allowed ⦄ → Has-well-behaved-zero semiring-with-meet
  𝟘ᵐ-allowed→𝟘-well-behaved ⦃ ok ⦄ = 𝟘-well-behaved ok

------------------------------------------------------------------------
-- If 𝟘ᵐ is allowed then properties which are proven under the
-- assumption that 𝟘 is well behaved hold

module 𝟘ᵐ (ok : T 𝟘ᵐ-allowed) where
  open import Graded.Modality.Properties.Has-well-behaved-zero
    semiring-with-meet
    ⦃ 𝟘-well-behaved = 𝟘-well-behaved ok ⦄ public

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

opaque

  private

    -- A lemma used in the implementation of 𝟘ᵐ-allowed-elim.

    𝟘ᵐ-allowed-elim-helper :
      ∀ {p} {P : Set p} (b : Bool) →
      (T b → P) →
      ((not-ok : ¬ T b) → P) →
      P
    𝟘ᵐ-allowed-elim-helper true  t f = t _
    𝟘ᵐ-allowed-elim-helper false t f = f (λ ())

  -- One can prove that a predicate holds for 𝟘ᵐ-allowed by proving
  -- that it holds given that T 𝟘ᵐ-allowed is inhabited, and that it
  -- holds given that T 𝟘ᵐ-allowed is not inhabited.

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
  Mode-propositional-without-𝟘ᵐ
    λ ok → non-trivial ⦃ 𝟘-well-behaved ok ⦄ 𝟙≡𝟘

------------------------------------------------------------------------
-- 𝟘ᵐ?

opaque
  unfolding 𝟘ᵐ-allowed-elim

  -- A mode that is 𝟘ᵐ[ something ] if 𝟘ᵐ-allowed is true, and otherwise
  -- 𝟙ᵐ.

  𝟘ᵐ? : Mode
  𝟘ᵐ? = 𝟘ᵐ-allowed-elim 𝟘ᵐ[_] (λ _ → 𝟙ᵐ)

opaque
  unfolding 𝟘ᵐ?

  -- One can prove that a predicate holds for 𝟘ᵐ? by proving that it
  -- holds for 𝟘ᵐ[ ok ] (for any ok) and that it holds for 𝟙ᵐ (under
  -- the assumption that T 𝟘ᵐ-allowed is not inhabited).

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

opaque

  -- 𝟘ᵐ? is equal to 𝟙ᵐ if and only if 𝟘ᵐ is not allowed.

  𝟘ᵐ?≡𝟙ᵐ⇔ : 𝟘ᵐ? ≡ 𝟙ᵐ ⇔ (¬ T 𝟘ᵐ-allowed)
  𝟘ᵐ?≡𝟙ᵐ⇔ =
      (λ 𝟘ᵐ?≡𝟙ᵐ ok →
         case
           𝟘ᵐ[ ok ]  ≡˘⟨ 𝟘ᵐ?≡𝟘ᵐ ⟩
           𝟘ᵐ?       ≡⟨ 𝟘ᵐ?≡𝟙ᵐ ⟩
           𝟙ᵐ        ∎
         of λ ())
    , Mode-propositional-without-𝟘ᵐ
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

opaque
  unfolding 𝟘ᵐ-allowed-elim

  private

    -- A function used in the implementation of ⌞_⌟.

    ⌞_⌟′ : M → T 𝟘ᵐ-allowed → Mode
    ⌞ p ⌟′ ok = case is-𝟘? p of λ where
      (yes _) → 𝟘ᵐ[ ok ]
      (no _)  → 𝟙ᵐ

  -- Quantities can be translated to modes (in a potentially lossy way).

  ⌞_⌟ : M → Mode
  ⌞ p ⌟ = 𝟘ᵐ-allowed-elim ⌞ p ⌟′ (λ _ → 𝟙ᵐ)

-- Equality of modes is decidable.

infix 4 _≟_

_≟_ : (m₁ m₂ : Mode) → Dec (m₁ ≡ m₂)
𝟙ᵐ ≟ 𝟙ᵐ = yes refl
𝟘ᵐ ≟ 𝟘ᵐ = yes 𝟘ᵐ-cong
𝟙ᵐ ≟ 𝟘ᵐ = no (λ ())
𝟘ᵐ ≟ 𝟙ᵐ = no (λ ())

------------------------------------------------------------------------
-- Properties related to _∨ᵐ_ and _·ᵐ_

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

opaque

  -- 𝟘ᵐ is a right zero for _·ᵐ_.

  ·ᵐ-zeroʳ-𝟘ᵐ : m ·ᵐ 𝟘ᵐ[ ok ] ≡ 𝟘ᵐ[ ok ]
  ·ᵐ-zeroʳ-𝟘ᵐ {m = 𝟘ᵐ} = 𝟘ᵐ-cong
  ·ᵐ-zeroʳ-𝟘ᵐ {m = 𝟙ᵐ} = refl

------------------------------------------------------------------------
-- Properties related to ⌜_⌝ and ⌜_⌝ᶜ

opaque

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

opaque

  -- ⌜ m ⌝ ·ᶜ_ distributes over _⊛ᶜ_▷ r from the left.

  ⌜⌝-·ᶜ-distribˡ-⊛ᶜ :
    ⦃ has-star : Has-star semiring-with-meet ⦄ →
    ∀ m → ⌜ m ⌝ ·ᶜ γ ⊛ᶜ δ ▷ r ≈ᶜ (⌜ m ⌝ ·ᶜ γ) ⊛ᶜ ⌜ m ⌝ ·ᶜ δ ▷ r
  ⌜⌝-·ᶜ-distribˡ-⊛ᶜ {γ = ε}     {δ = ε}     _ = ε
  ⌜⌝-·ᶜ-distribˡ-⊛ᶜ {γ = _ ∙ _} {δ = _ ∙ _} m =
    ⌜⌝-·ᶜ-distribˡ-⊛ᶜ m ∙ ⌜⌝-·-distribˡ-⊛ m

opaque

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
    nr p r 𝟘 (𝟘 · s) (𝟘 · n)        ≡˘⟨ cong (λ z → nr _ _ z (𝟘 · _) (𝟘 · _)) (·-zeroˡ _) ⟩
    nr p r (𝟘 · z) (𝟘 · s) (𝟘 · n)  ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque

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

opaque

  -- A variant of ⌜⌝-·-distribˡ-nr.

  ≡nr-𝟘-𝟘-⌜⌝ :
    ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
    ∀ m → ⌜ m ⌝ · nr p r 𝟘 𝟘 𝟙 ≡ nr p r 𝟘 𝟘 ⌜ m ⌝
  ≡nr-𝟘-𝟘-⌜⌝ {p} {r} m =
    ⌜ m ⌝ · nr p r 𝟘 𝟘 𝟙                        ≡⟨ ⌜⌝-·-distribˡ-nr m ⟩
    nr p r (⌜ m ⌝ · 𝟘) (⌜ m ⌝ · 𝟘) (⌜ m ⌝ · 𝟙)  ≡⟨ cong₃ (nr _ _) (·-zeroʳ _) (·-zeroʳ _) (·-identityʳ _) ⟩
    nr p r 𝟘 𝟘 ⌜ m ⌝                            ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque

  -- If 𝟘ᵐ is allowed, then ⌜ 𝟘ᵐ? ⌝ is equal to 𝟘.

  ⌜𝟘ᵐ?⌝≡𝟘 : T 𝟘ᵐ-allowed → ⌜ 𝟘ᵐ? ⌝ ≡ 𝟘
  ⌜𝟘ᵐ?⌝≡𝟘 ok =
    ⌜ 𝟘ᵐ? ⌝       ≡⟨ cong ⌜_⌝ (𝟘ᵐ?≡𝟘ᵐ {ok = ok}) ⟩
    ⌜ 𝟘ᵐ[ ok ] ⌝  ≡⟨⟩
    𝟘             ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque

  -- If 𝟘ᵐ is not allowed, then ⌜ 𝟘ᵐ? ⌝ is equal to 𝟙.

  ⌜𝟘ᵐ?⌝≡𝟙 : ¬ T 𝟘ᵐ-allowed → ⌜ 𝟘ᵐ? ⌝ ≡ 𝟙
  ⌜𝟘ᵐ?⌝≡𝟙 =
    cong ⌜_⌝ {x = 𝟘ᵐ?} {y = 𝟙ᵐ} ∘→
    Mode-propositional-without-𝟘ᵐ

opaque

  -- If ⌜ m ⌝ ≢ 𝟘 then m ≡ 𝟙ᵐ.

  ⌜⌝≢𝟘→≡𝟙ᵐ : ⌜ m ⌝ ≢ 𝟘 → m ≡ 𝟙ᵐ
  ⌜⌝≢𝟘→≡𝟙ᵐ {(𝟘ᵐ)} 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 refl)
  ⌜⌝≢𝟘→≡𝟙ᵐ {(𝟙ᵐ)} _ = refl

------------------------------------------------------------------------
-- Properties related to ⌞_⌟ and ⌞_⌟ᶜ

-- A view for ⌞_⌟.

data ⌞⌟-view (p : M) (m : Mode) : Set a where
  𝟘ᵐ-not-allowed : ¬ T 𝟘ᵐ-allowed                → m ≡ 𝟙ᵐ → ⌞⌟-view p m
  𝟙ᵐ             : ⦃ ok : T 𝟘ᵐ-allowed ⦄ → p ≢ 𝟘 → m ≡ 𝟙ᵐ → ⌞⌟-view p m
  𝟘ᵐ             : ⦃ ok : T 𝟘ᵐ-allowed ⦄ → p ≡ 𝟘 → m ≡ 𝟘ᵐ → ⌞⌟-view p m

opaque
  unfolding ⌞_⌟

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
    lemma false ≡𝟘ᵐ-allowed =
      𝟘ᵐ-not-allowed (subst T (PE.sym ≡𝟘ᵐ-allowed)) refl
    lemma true  ≡𝟘ᵐ-allowed with is-𝟘? p
    … | no p≢𝟘  = 𝟙ᵐ ⦃ ok = subst T ≡𝟘ᵐ-allowed _ ⦄ p≢𝟘 refl
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
  unfolding ⌞_⌟ 𝟘ᵐ?

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
    lemma false ≡𝟘ᵐ-allowed =
      𝟘ᵐ?-elim
        (λ m →
           𝟙ᵐ ≡ m ⇔ (¬ T 𝟘ᵐ-allowed ⊎ T 𝟘ᵐ-allowed × p ≡ 𝟘))
        (λ ⦃ ok = ok ⦄ → ⊥-elim (subst T (PE.sym ≡𝟘ᵐ-allowed) ok))
        (λ _ →
           (λ _ → inj₁ (subst T (PE.sym ≡𝟘ᵐ-allowed))) , (λ _ → refl))
    lemma true ≡𝟘ᵐ-allowed with is-𝟘? p
    … | no p≢𝟘 =
        𝟘ᵐ?-elim
          (λ m →
             𝟙ᵐ ≡ m → (¬ T 𝟘ᵐ-allowed ⊎ T 𝟘ᵐ-allowed × p ≡ 𝟘))
          (λ ())
          (λ not-ok _ → inj₁ not-ok)
      , (λ where
           (inj₁ ¬⊤)        → ⊥-elim $ ¬⊤ (subst T ≡𝟘ᵐ-allowed _)
           (inj₂ (_ , p≡𝟘)) → ⊥-elim $ p≢𝟘 p≡𝟘)
    … | yes p≡𝟘 =
      let ok = subst T ≡𝟘ᵐ-allowed _ in
        (λ _ → inj₂ (ok , p≡𝟘))
      , (λ _ →
           𝟘ᵐ?-elim (λ m → 𝟘ᵐ[ _ ] ≡ m) 𝟘ᵐ-cong
             (λ not-ok → ⊥-elim (not-ok ok)))

opaque

  -- If p is equal to 𝟘, then ⌞ p ⌟ is equal to 𝟘ᵐ[ ok ].

  ≡𝟘→⌞⌟≡𝟘ᵐ : p ≡ 𝟘 → ⌞ p ⌟ ≡ 𝟘ᵐ[ ok ]
  ≡𝟘→⌞⌟≡𝟘ᵐ = ⌞⌟≡𝟘ᵐ⇔≡𝟘 .proj₂

opaque

  -- ⌞ 𝟘 ⌟ is equal to 𝟘ᵐ[ ok ].

  ⌞𝟘⌟′ : ⌞ 𝟘 ⌟ ≡ 𝟘ᵐ[ ok ]
  ⌞𝟘⌟′ = ≡𝟘→⌞⌟≡𝟘ᵐ refl

opaque

  -- ⌞ 𝟘 ⌟ is equal to 𝟘ᵐ?.

  ⌞𝟘⌟≡𝟘ᵐ? : ⌞ 𝟘 ⌟ ≡ 𝟘ᵐ?
  ⌞𝟘⌟≡𝟘ᵐ? = 𝟘ᵐ?-elim
    (⌞ 𝟘 ⌟ ≡_)
    ⌞𝟘⌟′
    only-𝟙ᵐ-without-𝟘ᵐ

opaque

  -- If p is equal to 𝟘, then ⌞ p ⌟ is equal to 𝟘ᵐ?.

  ≡𝟘→⌞⌟≡𝟘ᵐ? : p ≡ 𝟘 → ⌞ p ⌟ ≡ 𝟘ᵐ?
  ≡𝟘→⌞⌟≡𝟘ᵐ? refl = ⌞𝟘⌟≡𝟘ᵐ?

opaque

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

opaque

  -- A variant of ≢𝟘→⌞⌟≡𝟙ᵐ′.

  ≢𝟘→⌞⌟≡𝟙ᵐ : p ≢ 𝟘 → ⌞ p ⌟ ≡ 𝟙ᵐ
  ≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘 = ≢𝟘→⌞⌟≡𝟙ᵐ′ (λ _ → p≢𝟘)

opaque

  -- If 𝟘ᵐ is allowed and ⌞ p ⌟ is equal to 𝟙ᵐ, then p is not equal to
  -- 𝟘.

  ⌞⌟≡𝟙ᵐ→≢𝟘 : T 𝟘ᵐ-allowed → ⌞ p ⌟ ≡ 𝟙ᵐ → p ≢ 𝟘
  ⌞⌟≡𝟙ᵐ→≢𝟘 ok ≡𝟙ᵐ = case ⌞⌟≡𝟙ᵐ⇔≢𝟘 .proj₁ ≡𝟙ᵐ of λ where
    (inj₁ not-ok)    → ⊥-elim $ not-ok ok
    (inj₂ (_ , p≢𝟘)) → p≢𝟘

private opaque

  -- ⌞ 𝟙 ⌟ is equal to 𝟙ᵐ.

  ⌞𝟙⌟ : ⌞ 𝟙 ⌟ ≡ 𝟙ᵐ
  ⌞𝟙⌟ = ≢𝟘→⌞⌟≡𝟙ᵐ′ λ ok → non-trivial ⦃ 𝟘-well-behaved ok ⦄

opaque

  -- If 𝟙 ≤ 𝟘, then the function taking p to ⌜ ⌞ p ⌟ ⌝ is monotone.

  ⌜⌞⌟⌝-monotone : 𝟙 ≤ 𝟘 → p ≤ q → ⌜ ⌞ p ⌟ ⌝ ≤ ⌜ ⌞ q ⌟ ⌝
  ⌜⌞⌟⌝-monotone {p = p} {q = q} 𝟙≤𝟘 p≤q = lemma _ _ refl refl
    where
    lemma : ∀ m₁ m₂ → ⌞ p ⌟ ≡ m₁ → ⌞ q ⌟ ≡ m₂ → ⌜ m₁ ⌝ ≤ ⌜ m₂ ⌝
    lemma 𝟘ᵐ       𝟘ᵐ _      _      = ≤-refl
    lemma 𝟙ᵐ       𝟙ᵐ _      _      = ≤-refl
    lemma 𝟙ᵐ       𝟘ᵐ _      _      = 𝟙≤𝟘
    lemma 𝟘ᵐ[ ok ] 𝟙ᵐ ⌞p⌟≡𝟘ᵐ ⌞q⌟≡𝟙ᵐ =
      ⊥-elim (⌞⌟≡𝟙ᵐ→≢𝟘 ok ⌞q⌟≡𝟙ᵐ (𝟘≮ (begin
        𝟘  ≈˘⟨ ⌞⌟≡𝟘ᵐ→≡𝟘 ⌞p⌟≡𝟘ᵐ ⟩
        p  ≤⟨ p≤q ⟩
        q  ∎)))
      where
      open Tools.Reasoning.PartialOrder ≤-poset

opaque

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
          ⌞ 𝟘 ⌟ ≡ 𝟙ᵐ     →⟨ trans (PE.sym ⌞𝟘⌟′) ⟩
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
-- The structure of modes

Zero-one-isMode : IsMode Mode 𝕄
Zero-one-isMode = record
  { _·ᵐ_ = _·ᵐ_
  ; 𝟘ᵐ = 𝟘ᵐ?
  ; 𝟙ᵐ = 𝟙ᵐ
  ; ⌞_⌟ = ⌞_⌟
  ; ⌜_⌝ = ⌜_⌝
  ; ·ᵐ-IdempotentCommutativeMonoid = record
    { isCommutativeMonoid =
        IsCommutativeSemiring.*-isCommutativeMonoid Mode ∨ᵐ-·ᵐ-is-commutative-semiring
    ; idem = λ _ → ·ᵐ-idem
    }
  ; ·ᵐ-zero =
      IsCommutativeSemiring.zero Mode ∨ᵐ-·ᵐ-is-commutative-semiring
  ; ⌞⌜⌝⌟ = ⌞⌜⌝⌟
  ; ⌜·ᵐ⌝ = ⌜·ᵐ⌝
  ; ⌞⌟·ᵐ = ⌞⌟·ᵐ
  ; ⌜⌝-·-comm = ⌜⌝-·-comm
  ; ·⌜⌞⌟⌝ = ·⌜⌞⌟⌝
  ; ≤⌜⌝· = λ {_ _ m} → ≤⌜⌝· {m = m}
  ; is-𝟘ᵐ? = _≟ 𝟘ᵐ?
  ; ⌜𝟘ᵐ⌝ = ⌜𝟘ᵐ⌝
  ; ⌞+⌟-decreasingˡ = ⌞+⌟-decreasingˡ
  ; ⌞∧⌟-decreasingˡ = ⌞∧⌟-decreasingˡ
  }
  where

  ·ᵐ-idem : m ·ᵐ m ≡ m
  ·ᵐ-idem {m = 𝟘ᵐ} = PE.refl
  ·ᵐ-idem {m = 𝟙ᵐ} = PE.refl

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

  ⌞⌜⌝⌟ : ∀ m → ⌞ ⌜ m ⌝ ⌟ ≡ m
  ⌞⌜⌝⌟ 𝟘ᵐ = ⌞𝟘⌟′
  ⌞⌜⌝⌟ 𝟙ᵐ = ⌞𝟙⌟

  ⌜𝟘ᵐ⌝ : 𝟙ᵐ ≢ 𝟘ᵐ? → ⌜ 𝟘ᵐ? ⌝ ≡ 𝟘
  ⌜𝟘ᵐ⌝ 𝟙ᵐ≢𝟘ᵐ? = ⌜𝟘ᵐ?⌝≡𝟘 (lemma _ 𝟙ᵐ≢𝟘ᵐ?)
    where
    lemma : (m : Mode) → 𝟙ᵐ ≢ m → T 𝟘ᵐ-allowed
    lemma 𝟘ᵐ[ ok ] 𝟙ᵐ≢ = ok
    lemma 𝟙ᵐ 𝟙ᵐ≢ = ⊥-elim (𝟙ᵐ≢ refl)

  ⌞⌟·ᵐ : ⌞ p ⌟ ·ᵐ ⌞ q ⌟ ≡ ⌞ p · q ⌟
  ⌞⌟·ᵐ {p = p} {q = q} = lemma _ _ _ refl refl refl
    where
    open Tools.Reasoning.PropositionalEquality

    lemma :
      ∀ m₁ m₂ m₃ → ⌞ p ⌟ ≡ m₁ → ⌞ q ⌟ ≡ m₂ → ⌞ p · q ⌟ ≡ m₃ →
      m₁ ·ᵐ m₂ ≡ m₃
    lemma 𝟘ᵐ _ _ ⌞p⌟≡𝟘ᵐ _ refl =
      𝟘ᵐ         ≡˘⟨ ⌞𝟘⌟′ ⟩
      ⌞ 𝟘 ⌟      ≡˘⟨ cong ⌞_⌟ (·-zeroˡ _) ⟩
      ⌞ 𝟘 · q ⌟  ≡˘⟨ cong (λ p → ⌞ p · _ ⌟) (⌞⌟≡𝟘ᵐ→≡𝟘 ⌞p⌟≡𝟘ᵐ) ⟩
      ⌞ p · q ⌟  ∎
    lemma 𝟙ᵐ 𝟘ᵐ 𝟘ᵐ _ _ _ =
      𝟘ᵐ-cong
    lemma _ 𝟘ᵐ 𝟙ᵐ _ ⌞q⌟≡𝟘ᵐ ⌞pq⌟≡𝟙ᵐ =
      case
        𝟘ᵐ         ≡˘⟨ ⌞𝟘⌟′ ⟩
        ⌞ 𝟘 ⌟      ≡˘⟨ cong ⌞_⌟ (·-zeroʳ _) ⟩
        ⌞ p · 𝟘 ⌟  ≡˘⟨ cong (λ q → ⌞ _ · q ⌟) (⌞⌟≡𝟘ᵐ→≡𝟘 ⌞q⌟≡𝟘ᵐ) ⟩
        ⌞ p · q ⌟  ≡⟨ ⌞pq⌟≡𝟙ᵐ ⟩
        𝟙ᵐ         ∎
      of λ ()
    lemma 𝟙ᵐ 𝟙ᵐ 𝟘ᵐ[ ok ] ⌞p⌟≡𝟙ᵐ ⌞q⌟≡𝟙ᵐ ⌞pq⌟≡𝟘ᵐ =
      case zero-product (⌞⌟≡𝟘ᵐ→≡𝟘 ⌞pq⌟≡𝟘ᵐ) of λ where
        (inj₁ refl) →
          case
            𝟘ᵐ[ ok ]  ≡˘⟨ ⌞𝟘⌟′ ⟩
            ⌞ 𝟘 ⌟     ≡⟨ ⌞p⌟≡𝟙ᵐ ⟩
            𝟙ᵐ        ∎
          of λ ()
        (inj₂ refl) →
          case
            𝟘ᵐ[ ok ]  ≡˘⟨ ⌞𝟘⌟′ ⟩
            ⌞ 𝟘 ⌟     ≡⟨ ⌞q⌟≡𝟙ᵐ ⟩
            𝟙ᵐ        ∎
          of λ ()
    lemma 𝟙ᵐ 𝟙ᵐ 𝟙ᵐ _ _ _ = refl

  ≤⌜⌝· : p ≤ q → q ≤ ⌜ m ⌝ · q → p ≤ ⌜ m ⌝ · p
  ≤⌜⌝· {p} {q} {m = 𝟘ᵐ} p≤q q≤mq = begin
    p     ≤⟨ p≤q ⟩
    q     ≤⟨ q≤mq ⟩
    𝟘 · q ≡⟨ ·-zeroˡ _ ⟩
    𝟘     ≡˘⟨ ·-zeroˡ _ ⟩
    𝟘 · p ∎
    where
    open ≤-reasoning
  ≤⌜⌝· {m = 𝟙ᵐ} p≤q q≤mq =
    ≤-reflexive (sym (·-identityˡ _))

  ⌞+⌟-decreasingˡ : ⌞ p ⌟ ≡ ⌞ p ⌟ ·ᵐ ⌞ p + q ⌟
  ⌞+⌟-decreasingˡ = lemma _ _ refl refl
    where

    lemma :
      ∀ m₁ m₂ → ⌞ p ⌟ ≡ m₁ → ⌞ p + q ⌟ ≡ m₂ →
      m₁ ≡ m₁ ·ᵐ m₂
    lemma 𝟘ᵐ _ _ _ = refl
    lemma 𝟙ᵐ 𝟙ᵐ _ _ = refl
    lemma 𝟙ᵐ 𝟘ᵐ[ ok ] eq₁ eq₂ =
      ⊥-elim $ ⌞⌟≡𝟙ᵐ→≢𝟘 ok eq₁ $ +-positiveˡ $ ⌞⌟≡𝟘ᵐ→≡𝟘 eq₂

  ⌞∧⌟-decreasingˡ : ⌞ p ⌟ ≡ ⌞ p ⌟ ·ᵐ ⌞ p ∧ q ⌟
  ⌞∧⌟-decreasingˡ = lemma _ _ refl refl
    where

    lemma :
      ∀ m₁ m₂ → ⌞ p ⌟ ≡ m₁ → ⌞ p ∧ q ⌟ ≡ m₂ →
      m₁ ≡ m₁ ·ᵐ m₂
    lemma 𝟘ᵐ _ _ _ = refl
    lemma 𝟙ᵐ 𝟙ᵐ _ _ = refl
    lemma 𝟙ᵐ 𝟘ᵐ[ ok ] eq₁ eq₂ =
      ⊥-elim $ ⌞⌟≡𝟙ᵐ→≢𝟘 ok eq₁ $ ∧-positiveˡ $ ⌞⌟≡𝟘ᵐ→≡𝟘 eq₂

open IsMode Zero-one-isMode public
  hiding (𝟘ᵐ; 𝟙ᵐ; ⌞_⌟; ⌜_⌝; _·ᵐ_)

opaque

  -- If 𝟘ᵐ is allowed then then the mode structure is not trivial.

  𝟘ᵐ-allowed→¬Trivialᵐ : T 𝟘ᵐ-allowed → ¬ IsMode.Trivialᵐ Zero-one-isMode
  𝟘ᵐ-allowed→¬Trivialᵐ ok 𝟙ᵐ≡𝟘ᵐ =
    case PE.trans 𝟙ᵐ≡𝟘ᵐ (𝟘ᵐ?≡𝟘ᵐ {ok = ok}) of λ ()

opaque

  -- A variant of the above

  𝟘ᵐ-allowed→¬Trivialᵐ′ :
    ⦃ ok : T 𝟘ᵐ-allowed ⦄ → ¬ IsMode.Trivialᵐ Zero-one-isMode
  𝟘ᵐ-allowed→¬Trivialᵐ′ ⦃ ok ⦄ = 𝟘ᵐ-allowed→¬Trivialᵐ ok

opaque

  -- If 𝟘ᵐ is not allowed then then the mode structure is trivial.

  ¬𝟘ᵐ-allowed→Trivialᵐ : ¬ T 𝟘ᵐ-allowed → IsMode.Trivialᵐ Zero-one-isMode
  ¬𝟘ᵐ-allowed→Trivialᵐ = Mode-propositional-without-𝟘ᵐ

opaque

  -- If the mode structure is trivial then 𝟘ᵐ is not allowed

  Trivialᵐ→¬𝟘ᵐ-allowed : IsMode.Trivialᵐ Zero-one-isMode → ¬ T 𝟘ᵐ-allowed
  Trivialᵐ→¬𝟘ᵐ-allowed = 𝟘ᵐ?≡𝟙ᵐ⇔ .proj₁ ∘→ sym

opaque

  -- If the mode structure is not trivial then 𝟘ᵐ is allowed

  ¬Trivialᵐ→𝟘ᵐ-allowed : ¬ IsMode.Trivialᵐ Zero-one-isMode → T 𝟘ᵐ-allowed
  ¬Trivialᵐ→𝟘ᵐ-allowed 𝟙ᵐ≢𝟘ᵐ =
    𝟘ᵐ-allowed-elim idᶠ (⊥-elim ∘→ 𝟙ᵐ≢𝟘ᵐ ∘→ ¬𝟘ᵐ-allowed→Trivialᵐ)

-- The Zero-one mode structure supports nr functions.

Zero-one-supports-nr :
  ⦃ has-nr : Has-nr semiring-with-meet ⦄ → Mode-supports-nr _ _ Zero-one-isMode
Zero-one-supports-nr = record
  { ⌜⌝-·-nr = λ {m} → ⌜⌝-·-distribˡ-nr m
  ; ⌞nr⌟-decreasing₁ = ⌞nr⌟-decreasing₁
  ; ⌞nr⌟-decreasing₃ = ⌞nr⌟-decreasing₃
  }
  where
  open ≤ᵐ-reasoning
  ⌞nr⌟-decreasing₁ : ⌞ nr p r z s q ⌟ ≤ᵐ ⌞ z ⌟
  ⌞nr⌟-decreasing₁ {p} {r} {z} {s} {q} =
    case is-𝟘? (nr p r z s q) of λ where
      (yes nr≡𝟘) →
        𝟘ᵐ-allowed-elim
          (λ ok → begin
            ⌞ nr p r z s q ⌟ ≡⟨ ⌞⌟-cong nr≡𝟘 ⟩
            ⌞ 𝟘 ⌟ ≡˘⟨ ⌞⌟-cong (nr-positive ⦃ 𝟘-well-behaved = 𝟘-well-behaved ok ⦄ nr≡𝟘 .proj₁) ⟩
            ⌞ z ⌟ ∎)
          (≡-trivialᵐ ∘→ ¬𝟘ᵐ-allowed→Trivialᵐ)
      (no nr≢𝟘) → begin
        ⌞ nr p r z s q ⌟ ≡⟨ ≢𝟘→⌞⌟≡𝟙ᵐ nr≢𝟘 ⟩
        𝟙ᵐ               ≤⟨ 𝟙ᵐ≤ ⟩
        ⌞ z ⌟            ∎
  ⌞nr⌟-decreasing₃ : ⌞ nr p r z s q ⌟ ≤ᵐ ⌞ q ⌟
  ⌞nr⌟-decreasing₃ {p} {r} {z} {s} {q} =
    case is-𝟘? (nr p r z s q) of λ where
      (yes nr≡𝟘) →
        𝟘ᵐ-allowed-elim
          (λ ok → begin
            ⌞ nr p r z s q ⌟ ≡⟨ ⌞⌟-cong nr≡𝟘 ⟩
            ⌞ 𝟘 ⌟ ≡˘⟨ ⌞⌟-cong (nr-positive ⦃ 𝟘-well-behaved = 𝟘-well-behaved ok ⦄ nr≡𝟘 .proj₂ .proj₂) ⟩
            ⌞ q ⌟ ∎)
          (≡-trivialᵐ ∘→ ¬𝟘ᵐ-allowed→Trivialᵐ)
      (no nr≢𝟘) → begin
        ⌞ nr p r z s q ⌟ ≡⟨ ≢𝟘→⌞⌟≡𝟙ᵐ nr≢𝟘 ⟩
        𝟙ᵐ               ≤⟨ 𝟙ᵐ≤ ⟩
        ⌞ q ⌟            ∎

------------------------------------------------------------------------
-- Properties related to _ᵐ·_

opaque

  -- If 𝟙 ≤ 𝟘, then the function taking p to ⌜ m ᵐ· p ⌝ is monotone for
  -- every m.

  ⌜ᵐ·⌝-monotoneʳ : 𝟙 ≤ 𝟘 → ∀ m → p ≤ q → ⌜ m ᵐ· p ⌝ ≤ ⌜ m ᵐ· q ⌝
  ⌜ᵐ·⌝-monotoneʳ _   𝟘ᵐ = λ _ → ≤-refl
  ⌜ᵐ·⌝-monotoneʳ 𝟙≤𝟘 𝟙ᵐ = ⌜⌞⌟⌝-monotone 𝟙≤𝟘

opaque

  -- If "𝟘ᵐ is allowed" implies that p is non-zero, then m ᵐ· p is
  -- equal to m.

  ≢𝟘→ᵐ·≡′ : (T 𝟘ᵐ-allowed → p ≢ 𝟘) → m ᵐ· p ≡ m
  ≢𝟘→ᵐ·≡′ {m = 𝟘ᵐ} _ = PE.refl
  ≢𝟘→ᵐ·≡′ {m = 𝟙ᵐ}   = ≢𝟘→⌞⌟≡𝟙ᵐ′

opaque

  -- A variant of ≢𝟘→ᵐ·≡′.

  ≢𝟘→ᵐ·≡ : p ≢ 𝟘 → m ᵐ· p ≡ m
  ≢𝟘→ᵐ·≡ p≢𝟘 = ≢𝟘→ᵐ·≡′ (λ _ → p≢𝟘)

opaque

  -- If p is non-zero then ⌞ p · q ⌟ is equal to ⌞ q ⌟

  ≢𝟘→⌞·⌟≡ˡ : p ≢ 𝟘 → ⌞ p · q ⌟ ≡ ⌞ q ⌟
  ≢𝟘→⌞·⌟≡ˡ p≢𝟘 = trans (PE.sym ⌞⌟·ᵐ) (cong (_·ᵐ _) (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘))

opaque

  -- If q is non-zero then ⌞ p · q ⌟ is equal to ⌞ p ⌟

  ≢𝟘→⌞·⌟≡ʳ : q ≢ 𝟘 → ⌞ p · q ⌟ ≡ ⌞ p ⌟
  ≢𝟘→⌞·⌟≡ʳ q≢𝟘 =
    trans (PE.sym ⌞⌟·ᵐ)
      (trans (cong (_ ·ᵐ_) (≢𝟘→⌞⌟≡𝟙ᵐ q≢𝟘)) (·ᵐ-identityʳ _))

opaque

  -- It is decidable if there is a mode m′ such that m′ ᵐ· p ≡ m.

  ᵐ·-split-dec : ∀ m → Dec (∃ λ m′ → m′ ᵐ· p ≡ m)
  ᵐ·-split-dec {p} = λ where
      𝟘ᵐ → yes (𝟘ᵐ , (begin
        𝟘ᵐ ᵐ· p  ≡˘⟨ ᵐ·-congʳ 𝟘ᵐ?≡𝟘ᵐ ⟩
        𝟘ᵐ? ᵐ· p ≡⟨ ᵐ·-zeroˡ ⟩
        𝟘ᵐ?      ≡⟨ 𝟘ᵐ?≡𝟘ᵐ ⟩
        𝟘ᵐ       ∎))
      𝟙ᵐ → case is-𝟘? p of λ where
        (yes refl) →
          𝟘ᵐ-allowed-elim
            (λ ok → no (λ (m , ≡𝟙ᵐ) → 𝟘ᵐ-allowed→¬Trivialᵐ ok $ begin
              𝟙ᵐ     ≡˘⟨ ≡𝟙ᵐ ⟩
              m ᵐ· 𝟘 ≡⟨ ᵐ·-zeroʳ _ ⟩
              𝟘ᵐ?    ∎))
            (λ not-ok → yes (𝟙ᵐ , Mode-propositional-without-𝟘ᵐ not-ok))
        (no p≢𝟘) → yes (𝟙ᵐ , (begin
          𝟙ᵐ ᵐ· p ≡⟨ ᵐ·-identityˡ ⟩
          ⌞ p ⌟   ≡⟨ ≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘 ⟩
          𝟙ᵐ      ∎))
    where
    open Tools.Reasoning.PropositionalEquality
