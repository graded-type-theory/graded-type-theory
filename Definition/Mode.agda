------------------------------------------------------------------------
-- Modes
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Tools.Relation
open import Definition.Modality

module Definition.Mode
  {a ℓ} {M′ : Setoid a ℓ} (𝕄 : Modality M′)
  where

open Modality 𝕄
open Setoid M′ renaming (Carrier to M)

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Properties 𝕄
open import Tools.Algebra
import Tools.Bool as B
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
open import Tools.PropositionalEquality as PE
import Tools.Reasoning.Equivalence
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

private variable
  n     : Nat
  p q r : M
  γ δ   : Conₘ n

------------------------------------------------------------------------
-- Definitions

-- Modes.

Mode : Set
Mode = B.Bool

-- The two modes.

pattern 𝟘ᵐ = B.false
pattern 𝟙ᵐ = B.true

private variable
  m m₁ m₁′ m₂ m₂′ m₃ : Mode

-- The join of two modes.

infixr 40 _∨ᵐ_

_∨ᵐ_ : Mode → Mode → Mode
_∨ᵐ_ = B._∨_

-- Multiplication of modes.

infixr 45 _·ᵐ_

_·ᵐ_ : Mode → Mode → Mode
_·ᵐ_ = B._∧_

-- Modes can be translated to quantities.

⌜_⌝ : Mode → M
⌜ 𝟘ᵐ ⌝ = 𝟘
⌜ 𝟙ᵐ ⌝ = 𝟙

-- Quantities can be translated to modes (in a potentially lossy way).

⌞_⌟ : M → Mode
⌞ p ⌟ = case is-𝟘? p of λ where
  (yes _) → 𝟘ᵐ
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
-- Properties related to _∨ᵐ_ and _·ᵐ_

-- The multiplication operation is idempotent.

·ᵐ-idem : m ·ᵐ m ≡ m
·ᵐ-idem {m = 𝟘ᵐ} = PE.refl
·ᵐ-idem {m = 𝟙ᵐ} = PE.refl

-- The operations _∨ᵐ_ and _·ᵐ_, along with the values 𝟘ᵐ and 𝟙ᵐ, form
-- a commutative semiring.

∨ᵐ-·ᵐ-is-commutative-semiring :
  IsCommutativeSemiring (PE.setoid Mode) _∨ᵐ_ _·ᵐ_ 𝟘ᵐ 𝟙ᵐ
∨ᵐ-·ᵐ-is-commutative-semiring = B.∨-∧-isCommutativeSemiring

open IsCommutativeSemiring
       (PE.setoid Mode)
       ∨ᵐ-·ᵐ-is-commutative-semiring
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
  open Tools.Reasoning.Equivalence M′
⌜·ᵐ⌝ {m₂ = m₂} 𝟙ᵐ = begin
  ⌜ m₂ ⌝      ≈˘⟨ ·-identityˡ _ ⟩
  𝟙 · ⌜ m₂ ⌝  ∎
  where
  open Tools.Reasoning.Equivalence M′

-- A form of commutativity.

⌜⌝-·-comm : ∀ m → ⌜ m ⌝ · p ≈ p · ⌜ m ⌝
⌜⌝-·-comm {p = p} 𝟘ᵐ = begin
  𝟘 · p  ≈⟨ ·-zeroˡ _ ⟩
  𝟘      ≈˘⟨ ·-zeroʳ _ ⟩
  p · 𝟘  ∎
  where
  open Tools.Reasoning.Equivalence M′
⌜⌝-·-comm {p = p} 𝟙ᵐ = begin
  𝟙 · p  ≈⟨ ·-identityˡ _ ⟩
  p      ≈˘⟨ ·-identityʳ _ ⟩
  p · 𝟙  ∎
  where
  open Tools.Reasoning.Equivalence M′

-- A form of associativity.

·ᵐ-·-assoc : ∀ m₁ → ⌜ m₁ ·ᵐ m₂ ⌝ · p ≈ ⌜ m₁ ⌝ · ⌜ m₂ ⌝ · p
·ᵐ-·-assoc {m₂ = m₂} {p = p} m₁ = begin
  ⌜ m₁ ·ᵐ m₂ ⌝ · p       ≈⟨ ·-congʳ (⌜·ᵐ⌝ m₁) ⟩
  (⌜ m₁ ⌝ · ⌜ m₂ ⌝) · p  ≈⟨ ·-assoc _ _ _ ⟩
  ⌜ m₁ ⌝ · ⌜ m₂ ⌝ · p    ∎
  where
  open Tools.Reasoning.Equivalence M′

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
  open Tools.Reasoning.Equivalence M′
⌜⌝-·-distribˡ-⊛ {p = p} {q = q} {r = r} 𝟘ᵐ =
  let open Tools.Reasoning.Equivalence M′ in begin
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
  open Tools.Reasoning.Equivalence M′
… | no p≉𝟘 | yes q≈𝟘 = ⊥-elim (p≉𝟘 (begin
  p  ≈⟨ p≈q ⟩
  q  ≈⟨ q≈𝟘 ⟩
  𝟘  ∎))
  where
  open Tools.Reasoning.Equivalence M′

-- The function ⌞_⌟ᶜ preserves "equality".

⌞⌟ᶜ-cong : γ ≈ᶜ δ → ∀ x → ⌞ γ ⌟ᶜ x ≡ ⌞ δ ⌟ᶜ x
⌞⌟ᶜ-cong (γ≈δ ∙ p≈q) = λ where
  x0     → ⌞⌟-cong p≈q
  (x +1) → ⌞⌟ᶜ-cong γ≈δ x

-- If p is equivalent to 𝟘, then ⌞ p ⌟ is equal to 𝟘ᵐ.

≈𝟘→⌞⌟≡𝟘ᵐ : p ≈ 𝟘 → ⌞ p ⌟ ≡ 𝟘ᵐ
≈𝟘→⌞⌟≡𝟘ᵐ {p = p} p≈𝟘 with is-𝟘? p
… | yes _  = PE.refl
… | no p≉𝟘 = ⊥-elim (p≉𝟘 p≈𝟘)

-- If p is not equivalent to 𝟘, then ⌞ p ⌟ is equal to 𝟙ᵐ.

≉𝟘→⌞⌟≡𝟙ᵐ : p ≉ 𝟘 → ⌞ p ⌟ ≡ 𝟙ᵐ
≉𝟘→⌞⌟≡𝟙ᵐ {p = p} p≉𝟘 with is-𝟘? p
… | no _    = PE.refl
… | yes p≈𝟘 = ⊥-elim (p≉𝟘 p≈𝟘)

-- If ⌞ p ⌟ is equal to 𝟘ᵐ, then p is equivalent to 𝟘.

⌞⌟≡𝟘ᵐ→≈𝟘 : ⌞ p ⌟ ≡ 𝟘ᵐ → p ≈ 𝟘
⌞⌟≡𝟘ᵐ→≈𝟘 {p = p} _  with is-𝟘? p
⌞⌟≡𝟘ᵐ→≈𝟘         _  | yes p≈𝟘 = p≈𝟘
⌞⌟≡𝟘ᵐ→≈𝟘         () | no _

-- If ⌞ p ⌟ is equal to 𝟙ᵐ, then p is not equivalent to 𝟘.

⌞⌟≡𝟙ᵐ→≉𝟘 : ⌞ p ⌟ ≡ 𝟙ᵐ → p ≉ 𝟘
⌞⌟≡𝟙ᵐ→≉𝟘 {p = p} _  with is-𝟘? p
⌞⌟≡𝟙ᵐ→≉𝟘         _  | no p≉𝟘 = p≉𝟘
⌞⌟≡𝟙ᵐ→≉𝟘         () | yes _

-- The value of ⌞ 𝟘 ⌟ is 𝟘ᵐ.

⌞𝟘⌟ : ⌞ 𝟘 ⌟ ≡ 𝟘ᵐ
⌞𝟘⌟ = ≈𝟘→⌞⌟≡𝟘ᵐ ≈-refl

-- If 𝟙 ≉ 𝟘, then the value of ⌞ 𝟙 ⌟ is 𝟙ᵐ.

⌞𝟙⌟ : 𝟙 ≉ 𝟘 → ⌞ 𝟙 ⌟ ≡ 𝟙ᵐ
⌞𝟙⌟ = ≉𝟘→⌞⌟≡𝟙ᵐ

-- The function taking p to ⌜ ⌞ p ⌟ ⌝ preserves equivalence.

⌜⌞⌟⌝-cong : p ≈ q → ⌜ ⌞ p ⌟ ⌝ ≈ ⌜ ⌞ q ⌟ ⌝
⌜⌞⌟⌝-cong p≈q = ≈-reflexive (cong ⌜_⌝ (⌞⌟-cong p≈q))

-- If 𝟙 ≤ 𝟘, then the function taking p to ⌜ ⌞ p ⌟ ⌝ is monotone.

⌜⌞⌟⌝-monotone : 𝟙 ≤ 𝟘 → p ≤ q → ⌜ ⌞ p ⌟ ⌝ ≤ ⌜ ⌞ q ⌟ ⌝
⌜⌞⌟⌝-monotone {p = p} {q = q} 𝟙≤𝟘 p≤q with is-𝟘? p | is-𝟘? q
… | yes _   | yes _  = ≤-refl
… | no _    | no _   = ≤-refl
… | no _    | yes _  = 𝟙≤𝟘
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
  open Tools.Reasoning.Equivalence M′
… | yes p≈𝟘 = begin
  p · 𝟘  ≈⟨ ·-zeroʳ _ ⟩
  𝟘      ≈˘⟨ p≈𝟘 ⟩
  p      ∎
  where
  open Tools.Reasoning.Equivalence M′

-- The function ⌞_⌟ is a left inverse of ⌜_⌝ if 𝟙 ≉ 𝟘.

⌞⌜⌝⌟ : 𝟙 ≉ 𝟘 → ∀ m → ⌞ ⌜ m ⌝ ⌟ ≡ m
⌞⌜⌝⌟ _   𝟘ᵐ = ⌞𝟘⌟
⌞⌜⌝⌟ 𝟙≉𝟘 𝟙ᵐ = ⌞𝟙⌟ 𝟙≉𝟘

-- The function ⌜_⌝ is a left inverse of ⌞_⌟ (up to _≈_) for arguments
-- in the image of ⌜_⌝.

⌜⌞⌜⌝⌟⌝ : ∀ m → ⌜ ⌞ ⌜ m ⌝ ⌟ ⌝ ≈ ⌜ m ⌝
⌜⌞⌜⌝⌟⌝ 𝟘ᵐ = begin
  ⌜ ⌞ 𝟘 ⌟ ⌝  ≡⟨ cong ⌜_⌝ ⌞𝟘⌟ ⟩
  ⌜ 𝟘ᵐ ⌝     ≡⟨⟩
  𝟘          ∎
  where
  open Tools.Reasoning.Equivalence M′
⌜⌞⌜⌝⌟⌝ 𝟙ᵐ with is-𝟘? 𝟙
… | no _    = ≈-refl
… | yes 𝟙≈𝟘 = ≈-sym 𝟙≈𝟘

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

-- If 1 ≈ 𝟘, then ⌞ p ⌟ is equal to 𝟘ᵐ.

⌞⌟≡𝟘ᵐ : 𝟙 ≈ 𝟘 → ⌞ p ⌟ ≡ 𝟘ᵐ
⌞⌟≡𝟘ᵐ {p = p} 𝟙≈𝟘 with is-𝟘? p
… | yes _  = PE.refl
… | no p≉𝟘 = ⊥-elim (p≉𝟘 (begin
  p      ≈˘⟨ ·-identityʳ _ ⟩
  p · 𝟙  ≈⟨ ·-congˡ 𝟙≈𝟘 ⟩
  p · 𝟘  ≈⟨ ·-zeroʳ _ ⟩
  𝟘      ∎))
  where
  open Tools.Reasoning.Equivalence M′

------------------------------------------------------------------------
-- Properties related to _ᵐ·_

-- The function m ᵐ·_ preserves "equality".

ᵐ·-cong : ∀ m → p ≈ q → m ᵐ· p ≡ m ᵐ· q
ᵐ·-cong 𝟘ᵐ = λ _ → PE.refl
ᵐ·-cong 𝟙ᵐ = ⌞⌟-cong

-- 𝟘 is a kind of right zero for _ᵐ·_.

ᵐ·-zeroʳ : ∀ m → m ᵐ· 𝟘 ≡ 𝟘ᵐ
ᵐ·-zeroʳ 𝟘ᵐ = PE.refl
ᵐ·-zeroʳ 𝟙ᵐ = ⌞𝟘⌟

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
  open Tools.Reasoning.Equivalence M′
