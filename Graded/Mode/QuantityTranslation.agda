------------------------------------------------------------------------
-- A function that translates modes, and some related properties
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Modality.Morphism as M
  using (Is-morphism; Is-order-embedding; Is-Σ-morphism)
  hiding (module Is-morphism; module Is-order-embedding)

module Graded.Mode.QuantityTranslation
  {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
  (𝕄₁ : Modality M₁) (𝕄₂ : Modality M₂)
  (tr tr-Σ : M₁ → M₂)
  where

open import Graded.Modality.Properties 𝕄₂
open import Graded.Mode
open import Definition.Untyped
open import Definition.Untyped.QuantityTranslation tr tr-Σ

private
  module Mo₁ = Graded.Mode 𝕄₁
  module Mo₂ = Graded.Mode 𝕄₂
  module M₁  = Modality 𝕄₁
  module M₂  = Modality 𝕄₂

open import Tools.Empty
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

private variable
  p    : M₁
  m m′ : Mode _

------------------------------------------------------------------------
-- Definitions that are made under the assumptions that tr is a
-- morphism and that tr-Σ is a Σ-morphism with respect to tr

module Is-morphism
  (m   : Is-morphism 𝕄₁ 𝕄₂ tr)
  (m-Σ : Is-Σ-morphism 𝕄₁ 𝕄₂ tr tr-Σ)
  where

  open M.Is-morphism m

  open Modality 𝕄₂ using (_≤_)

  -- Translation of modes.

  tr-Mode : Mo₁.Mode → Mo₂.Mode
  tr-Mode 𝟘ᵐ[ ok ] = 𝟘ᵐ[ 𝟘ᵐ-in-second-if-in-first ok ]
  tr-Mode 𝟙ᵐ       = 𝟙ᵐ

  -- Translation commutes with ⌜_⌝ up to _≤_.

  tr-⌜⌝ : ∀ m → tr Mo₁.⌜ m ⌝ ≤ Mo₂.⌜ tr-Mode m ⌝
  tr-⌜⌝ 𝟘ᵐ[ ok ] = ≤-reflexive (tr-𝟘-≡-𝟘ᵐ ok)
  tr-⌜⌝ 𝟙ᵐ       = tr-𝟙

  -- A variant of the previous property with _≡_ instead of _≤_.

  tr-⌜⌝-· : ∀ m → Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p ≡ tr (Mo₁.⌜ m ⌝ M₁.· p)
  tr-⌜⌝-· {p = p} = λ where
      𝟘ᵐ[ ok ] → begin
        M₂.𝟘 M₂.· tr p    ≡⟨ M₂.·-zeroˡ _ ⟩
        M₂.𝟘              ≡˘⟨ tr-𝟘-≡-𝟘ᵐ ok ⟩
        tr M₁.𝟘           ≡˘⟨ cong tr (M₁.·-zeroˡ _) ⟩
        tr (M₁.𝟘 M₁.· p)  ∎
      𝟙ᵐ → begin
        M₂.𝟙 M₂.· tr p    ≡⟨ M₂.·-identityˡ _ ⟩
        tr p              ≡˘⟨ cong tr (M₁.·-identityˡ _) ⟩
        tr (M₁.𝟙 M₁.· p)  ∎
    where
    open Tools.Reasoning.PropositionalEquality

  -- The translation of Mo₁.⌜ Mo₁.𝟘ᵐ? ⌝ is bounded by Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝.

  tr-⌜𝟘ᵐ?⌝ : tr Mo₁.⌜ Mo₁.𝟘ᵐ? ⌝ ≤ Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝
  tr-⌜𝟘ᵐ?⌝ = Mo₁.𝟘ᵐ?-elim
    (λ m → tr Mo₁.⌜ m ⌝ ≤ Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝)
    (λ ⦃ ok = ok ⦄ → begin
       tr M₁.𝟘                                    ≤⟨ tr-𝟘-≤ ⟩
       M₂.𝟘                                       ≡⟨⟩
       Mo₂.⌜ 𝟘ᵐ[ 𝟘ᵐ-in-second-if-in-first ok ] ⌝  ≡˘⟨ cong Mo₂.⌜_⌝ $ Mo₂.𝟘ᵐ?≡𝟘ᵐ {ok = 𝟘ᵐ-in-second-if-in-first ok} ⟩
       Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝                            ∎)
    (λ not-ok →
       Mo₂.𝟘ᵐ?-elim
         (λ m → tr M₁.𝟙 ≤ Mo₂.⌜ m ⌝)
         (λ ⦃ ok = ok ⦄ →
            tr-<-𝟘 not-ok ok .proj₁)
         (λ _ → tr-𝟙))
    where
    open Tools.Reasoning.PartialOrder ≤-poset

  -- Translation commutes with _ᵐ·_ in a certain way.

  tr-Mode-ᵐ· :
    ∀ m b → tr-Mode (m Mo₁.ᵐ· p) ≡ (tr-Mode m Mo₂.ᵐ· tr-BinderMode b p)
  tr-Mode-ᵐ·         𝟘ᵐ = λ _ → refl
  tr-Mode-ᵐ· {p = p} 𝟙ᵐ = λ where
      BMΠ     → lemma (M.Is-morphism→Is-Σ-morphism m) _ _ refl refl
      (BMΣ _) → lemma m-Σ                             _ _ refl refl
    where
    module _
      {tr′ : M₁ → M₂}
      (m′ : Is-Σ-morphism 𝕄₁ 𝕄₂ tr tr′)
      where

      open Is-Σ-morphism m′
      open Tools.Reasoning.PropositionalEquality

      lemma :
        ∀ m₁ m₂ → Mo₁.⌞ p ⌟ ≡ m₁ → Mo₂.⌞ tr′ p ⌟ ≡ m₂ → tr-Mode m₁ ≡ m₂
      lemma 𝟘ᵐ       𝟘ᵐ _  _     = Mo₂.𝟘ᵐ-cong
      lemma 𝟙ᵐ       𝟙ᵐ _  _     = refl
      lemma 𝟘ᵐ[ ok ] 𝟙ᵐ p≡ tr-p≡ =
        ⊥-elim (Mo₂.⌞⌟≡𝟙ᵐ→≢𝟘 (𝟘ᵐ-in-second-if-in-first ok) tr-p≡ (
          tr′ p     ≡⟨ cong tr′ (Mo₁.⌞⌟≡𝟘ᵐ→≡𝟘 p≡) ⟩
          tr′ M₁.𝟘  ≡⟨ tr-Σ-𝟘-≡-𝟘ᵐ ok ⟩
          M₂.𝟘      ∎))
      lemma 𝟙ᵐ 𝟘ᵐ[ ok ] p≡ tr-p≡ = Mo₁.𝟘ᵐ-allowed-elim
        (λ ok →
           ⊥-elim $
           Mo₁.⌞⌟≡𝟙ᵐ→≢𝟘 ok p≡ $
           proj₂ $
           tr-Σ-≡-𝟘-→ (𝟘ᵐ-in-second-if-in-first ok) $
           Mo₂.⌞⌟≡𝟘ᵐ→≡𝟘 tr-p≡)
        (λ not-ok →
           case
             Mo₂.𝟙ᵐ         ≡˘⟨ Mo₂.≢𝟘→⌞⌟≡𝟙ᵐ (tr-Σ-≢-𝟘 not-ok ok) ⟩
             Mo₂.⌞ tr′ p ⌟  ≡⟨ tr-p≡ ⟩
             Mo₂.𝟘ᵐ         ∎
           of λ ())

  -- Translation is injective

  tr-Mode-injective : ∀ {m m′} → tr-Mode m ≡ tr-Mode m′ → m ≡ m′
  tr-Mode-injective {m = 𝟘ᵐ} {𝟘ᵐ} eq = 𝟘ᵐ-cong 𝕄₁
  tr-Mode-injective {m = 𝟙ᵐ} {𝟙ᵐ} eq = refl

------------------------------------------------------------------------
-- Definitions that are made under the assumptions that tr is an order
-- embedding and that tr-Σ is a Σ-morphism with respect to tr

module Is-order-embedding
  (tr-emb : Is-order-embedding 𝕄₁ 𝕄₂ tr)
  (tr-Σ-m : Is-Σ-morphism 𝕄₁ 𝕄₂ tr tr-Σ)
  where

  open M.Is-order-embedding tr-emb
  open M.Is-Σ-morphism tr-Σ-m

  open Is-morphism tr-morphism tr-Σ-m public

  -- If the translation of p is bounded by Mo₂.⌜ tr-Mode m ⌝, then p
  -- is bounded by Mo₁.⌜ m ⌝.

  tr-≤-⌜tr-Mode⌝ : ∀ m → tr p M₂.≤ Mo₂.⌜ tr-Mode m ⌝ → p M₁.≤ Mo₁.⌜ m ⌝
  tr-≤-⌜tr-Mode⌝         𝟙ᵐ              = tr-≤-𝟙
  tr-≤-⌜tr-Mode⌝ {p = p} 𝟘ᵐ[ ok ] tr-p≤𝟘 = tr-order-reflecting (begin
    tr p     ≤⟨ tr-p≤𝟘 ⟩
    M₂.𝟘     ≡˘⟨ tr-𝟘-≡-𝟘ᵐ ok ⟩
    tr M₁.𝟘  ∎)
    where
    open Tools.Reasoning.PartialOrder ≤-poset

  -- If the translation of m′ is m ᵐ· tr-Σ p, then there is some m″
  -- such that the translation of m″ is m and m′ is equal to m″ ᵐ· p.

  tr-Mode-≡-ᵐ· :
    m Mo₂.ᵐ· tr-Σ p ≡ tr-Mode m′ →
    ∃ λ m″ → tr-Mode m″ ≡ m × m″ Mo₁.ᵐ· p ≡ m′
  tr-Mode-≡-ᵐ· {m = 𝟘ᵐ} {m′ = 𝟘ᵐ} _ =
    𝟘ᵐ , Mo₂.𝟘ᵐ-cong , refl
  tr-Mode-≡-ᵐ· {m = 𝟙ᵐ} {p = p} {m′ = 𝟘ᵐ[ ok ]} ⌞tr-p⌟≡𝟘 =
      𝟙ᵐ
    , refl
    , (Mo₁.⌞ p ⌟  ≡⟨ Mo₁.≡𝟘→⌞⌟≡𝟘ᵐ
                       (tr-Σ-≡-𝟘-→ (𝟘ᵐ-in-second-if-in-first ok)
                          (Mo₂.⌞⌟≡𝟘ᵐ→≡𝟘 ⌞tr-p⌟≡𝟘) .proj₂) ⟩
       𝟘ᵐ         ∎)
    where
    open Tools.Reasoning.PropositionalEquality
  tr-Mode-≡-ᵐ· {m = 𝟙ᵐ} {p = p} {m′ = 𝟙ᵐ} ⌞tr-p⌟≡𝟙 =
      𝟙ᵐ
    , refl
    , Mo₁.𝟘ᵐ-allowed-elim
        (λ ok →
           Mo₁.⌞ p ⌟  ≡⟨ Mo₁.≢𝟘→⌞⌟≡𝟙ᵐ
                           (λ { refl →
                                Mo₂.⌞⌟≡𝟙ᵐ→≢𝟘 (𝟘ᵐ-in-second-if-in-first ok) ⌞tr-p⌟≡𝟙
                                  (tr-Σ-𝟘-≡-𝟘ᵐ ok) }) ⟩
           𝟙ᵐ         ∎)
        Mo₁.Mode-propositional-without-𝟘ᵐ
    where
    open Tools.Reasoning.PropositionalEquality
