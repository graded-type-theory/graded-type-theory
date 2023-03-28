------------------------------------------------------------------------
-- A function that translates modes, and some related properties
------------------------------------------------------------------------

open import Definition.Modality

module Definition.Mode.QuantityTranslation
  {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
  (𝕄₁ : Modality M₁) (𝕄₂ : Modality M₂)
  (tr : M₁ → M₂)
  where

open import Definition.Modality.Morphism as M
  using (Is-morphism; Is-order-embedding)
  hiding (module Is-morphism; module Is-order-embedding)
open import Definition.Modality.Properties 𝕄₂
open import Definition.Mode

private
  module Mo₁ = Definition.Mode 𝕄₁
  module Mo₂ = Definition.Mode 𝕄₂
  module M₁  = Modality 𝕄₁
  module M₂  = Modality 𝕄₂

open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

private variable
  p    : M₁
  m m′ : Mode _

------------------------------------------------------------------------
-- Definitions that require tr to be a morphism

module Is-morphism (mor : Is-morphism 𝕄₁ 𝕄₂ tr) where

  open M.Is-morphism mor

  open Modality 𝕄₂ using (_≤_)

  -- Translation of modes.

  tr-Mode : Mo₁.Mode → Mo₂.Mode
  tr-Mode 𝟘ᵐ[ ok ] = 𝟘ᵐ[ 𝟘ᵐ-in-second-if-in-first ok ]
  tr-Mode 𝟙ᵐ       = 𝟙ᵐ

  -- Translation commutes with ⌜_⌝ up to _≤_.

  tr-⌜⌝ : ∀ m → tr Mo₁.⌜ m ⌝ ≤ Mo₂.⌜ tr-Mode m ⌝
  tr-⌜⌝ 𝟘ᵐ[ ok ] = ≤-reflexive (tr-𝟘-≡ ok)
  tr-⌜⌝ 𝟙ᵐ       = tr-𝟙

  -- A variant of the previous property with _≡_ instead of _≤_.

  tr-⌜⌝-· : ∀ m → Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p ≡ tr (Mo₁.⌜ m ⌝ M₁.· p)
  tr-⌜⌝-· {p = p} = λ where
      𝟘ᵐ[ ok ] → begin
        M₂.𝟘 M₂.· tr p    ≡⟨ M₂.·-zeroˡ _ ⟩
        M₂.𝟘              ≡˘⟨ tr-𝟘-≡ ok ⟩
        tr M₁.𝟘           ≡˘⟨ cong tr (M₁.·-zeroˡ _) ⟩
        tr (M₁.𝟘 M₁.· p)  ∎
      𝟙ᵐ → begin
        M₂.𝟙 M₂.· tr p    ≡⟨ M₂.·-identityˡ _ ⟩
        tr p              ≡˘⟨ cong tr (M₁.·-identityˡ _) ⟩
        tr (M₁.𝟙 M₁.· p)  ∎
    where
    open Tools.Reasoning.PropositionalEquality

  -- Translation commutes with _ᵐ·_.

  tr-Mode-ᵐ· : ∀ m → tr-Mode (m Mo₁.ᵐ· p) ≡ (tr-Mode m Mo₂.ᵐ· tr p)
  tr-Mode-ᵐ·         𝟘ᵐ = refl
  tr-Mode-ᵐ· {p = p} 𝟙ᵐ = lemma _ _ refl refl
    where
    open Tools.Reasoning.PropositionalEquality

    lemma :
      ∀ m₁ m₂ → Mo₁.⌞ p ⌟ ≡ m₁ → Mo₂.⌞ tr p ⌟ ≡ m₂ → tr-Mode m₁ ≡ m₂
    lemma 𝟘ᵐ       𝟘ᵐ _  _     = Mo₂.𝟘ᵐ-cong
    lemma 𝟙ᵐ       𝟙ᵐ _  _     = refl
    lemma 𝟘ᵐ[ ok ] 𝟙ᵐ p≡ tr-p≡ =
      ⊥-elim (Mo₂.⌞⌟≡𝟙ᵐ→≉𝟘 (𝟘ᵐ-in-second-if-in-first ok) tr-p≡ (
        tr p     ≡⟨ cong tr (Mo₁.⌞⌟≡𝟘ᵐ→≈𝟘 p≡) ⟩
        tr M₁.𝟘  ≡⟨ tr-𝟘-≡ ok ⟩
        M₂.𝟘     ∎))
    lemma 𝟙ᵐ 𝟘ᵐ[ ok ] p≡ tr-p≡ = Mo₁.𝟘ᵐ-allowed-elim
      (λ ok →
         ⊥-elim $
         Mo₁.⌞⌟≡𝟙ᵐ→≉𝟘 ok p≡ $
         tr-≡-𝟘-⇔ ok .proj₁ $
         Mo₂.⌞⌟≡𝟘ᵐ→≈𝟘 tr-p≡)
      (λ not-ok →
         case
           Mo₂.𝟙ᵐ        ≡˘⟨ Mo₂.≉𝟘→⌞⌟≡𝟙ᵐ (tr-<-𝟘 not-ok ok .proj₂) ⟩
           Mo₂.⌞ tr p ⌟  ≡⟨ tr-p≡ ⟩
           Mo₂.𝟘ᵐ        ∎
         of λ ())

------------------------------------------------------------------------
-- Definitions that require tr to be an order embedding

module Is-order-embedding (emb : Is-order-embedding 𝕄₁ 𝕄₂ tr) where

  open M.Is-order-embedding emb

  open Is-morphism tr-morphism public

  -- If the translation of p is bounded by Mo₂.⌜ tr-Mode m ⌝, then p
  -- is bounded by Mo₁.⌜ m ⌝.

  tr-≤-⌜tr-Mode⌝ : ∀ m → tr p M₂.≤ Mo₂.⌜ tr-Mode m ⌝ → p M₁.≤ Mo₁.⌜ m ⌝
  tr-≤-⌜tr-Mode⌝         𝟙ᵐ              = tr-≤-𝟙
  tr-≤-⌜tr-Mode⌝ {p = p} 𝟘ᵐ[ ok ] tr-p≤𝟘 = tr-order-reflecting (begin
    tr p     ≤⟨ tr-p≤𝟘 ⟩
    M₂.𝟘     ≡˘⟨ tr-𝟘-≡ ok ⟩
    tr M₁.𝟘  ∎)
    where
    open Tools.Reasoning.PartialOrder ≤-poset

  -- If the translation of m′ is m ᵐ· tr p, then there is some m″ such
  -- that the translation of m″ is m and m′ is equal to m″ ᵐ· p.

  tr-Mode-≡-ᵐ· :
    m Mo₂.ᵐ· tr p ≡ tr-Mode m′ →
    ∃ λ m″ → tr-Mode m″ ≡ m × m″ Mo₁.ᵐ· p ≡ m′
  tr-Mode-≡-ᵐ· {m = 𝟘ᵐ} {m′ = 𝟘ᵐ} _ =
    𝟘ᵐ , Mo₂.𝟘ᵐ-cong , refl
  tr-Mode-≡-ᵐ· {m = 𝟙ᵐ} {p = p} {m′ = 𝟘ᵐ[ ok ]} ⌞tr-p⌟≡𝟘 =
      𝟙ᵐ
    , refl
    , (Mo₁.⌞ p ⌟  ≡⟨ Mo₁.≈𝟘→⌞⌟≡𝟘ᵐ (tr-≡-𝟘-⇔ ok .proj₁ (Mo₂.⌞⌟≡𝟘ᵐ→≈𝟘 ⌞tr-p⌟≡𝟘)) ⟩
       𝟘ᵐ         ∎)
    where
    open Tools.Reasoning.PropositionalEquality
  tr-Mode-≡-ᵐ· {m = 𝟙ᵐ} {p = p} {m′ = 𝟙ᵐ} ⌞tr-p⌟≡𝟙 =
      𝟙ᵐ
    , refl
    , Mo₁.𝟘ᵐ-allowed-elim
        (λ ok →
           Mo₁.⌞ p ⌟  ≡⟨ Mo₁.≉𝟘→⌞⌟≡𝟙ᵐ
                           (Mo₂.⌞⌟≡𝟙ᵐ→≉𝟘 (𝟘ᵐ-in-second-if-in-first ok) ⌞tr-p⌟≡𝟙 ∘→
                            tr-≡-𝟘-⇔ ok .proj₂) ⟩
           𝟙ᵐ         ∎)
        Mo₁.Mode-propositional-without-𝟘ᵐ
    where
    open Tools.Reasoning.PropositionalEquality
