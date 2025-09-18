------------------------------------------------------------------------
-- Some properties related to usage and the strong variant of Erased
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Derived.Erased.Usage.Eta
  {a} {M : Set a}
  (𝕄 : Modality M)
  (R : Usage-restrictions 𝕄)
  where

open Modality 𝕄

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Usage 𝕄 R
open import Graded.Usage.Inversion 𝕄 R
open import Graded.Usage.Properties 𝕄 R
open import Graded.Mode 𝕄

open import Definition.Untyped M
open import Definition.Untyped.Erased.Eta 𝕄

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation

private variable
  t : Term _
  γ   : Conₘ _
  m   : Mode
  ok  : T _

private

  -- A lemma used below.

  ᵐ·𝟘≡𝟘ᵐ : ∀ m ok → m ᵐ· 𝟘 PE.≡ 𝟘ᵐ[ ok ]
  ᵐ·𝟘≡𝟘ᵐ m _ =
    m ᵐ· 𝟘   ≡⟨ ᵐ·-zeroʳ m ⟩
    𝟘ᵐ?      ≡⟨ 𝟘ᵐ?≡𝟘ᵐ ⟩
    𝟘ᵐ[ _ ]  ∎
    where
    open Tools.Reasoning.PropositionalEquality

------------------------------------------------------------------------
-- Usage rules

opaque
  unfolding erased

  -- A usage rule for erased.

  ▸erased′ :
    (¬ T 𝟘ᵐ-allowed → 𝟘 ≤ 𝟙) →
    γ ▸[ 𝟘ᵐ? ] t → ⌜ 𝟘ᵐ? ⌝ ·ᶜ γ ▸[ 𝟘ᵐ? ] erased t
  ▸erased′ {γ} {t} hyp = 𝟘ᵐ?-elim
    (λ m → γ ▸[ m ] t → ⌜ m ⌝ ·ᶜ γ ▸[ m ] erased t)
    (λ ▸t → fstₘ
       𝟘ᵐ
       (▸-cong (PE.sym lemma) $
        sub (▸-𝟘 ▸t) $ begin
          𝟘 ·ᶜ γ  ≈⟨ ·ᶜ-zeroˡ _ ⟩
          𝟘ᶜ      ∎)
       lemma
       (λ ()))
    (λ not-ok ▸t → fstₘ
       𝟙ᵐ
       (▸-cong (Mode-propositional-without-𝟘ᵐ not-ok) $
        sub ▸t $ begin
          𝟙 ·ᶜ γ  ≈⟨ ·ᶜ-identityˡ _ ⟩
          γ       ∎)
       (Mode-propositional-without-𝟘ᵐ not-ok)
       (λ _ → hyp not-ok))
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

    lemma : ∀ {ok} → 𝟘ᵐ[ ok ] ᵐ· 𝟘 PE.≡ 𝟘ᵐ[ ok ]
    lemma {ok} = ᵐ·𝟘≡𝟘ᵐ 𝟘ᵐ[ ok ] _

-- Another usage rule for erased.

▸erased : γ ▸[ 𝟘ᵐ[ ok ] ] t → 𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] erased t
▸erased {γ} {ok} ▸t = sub
  (▸-cong 𝟘ᵐ?≡𝟘ᵐ $
   ▸erased′ (⊥-elim ∘→ (_$ ok)) $
   ▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸t)
  (begin
     𝟘ᶜ            ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
     𝟘 ·ᶜ γ        ≈˘⟨ ·ᶜ-congʳ $ PE.cong ⌜_⌝ $ 𝟘ᵐ?≡𝟘ᵐ {ok = ok} ⟩
     ⌜ 𝟘ᵐ? ⌝ ·ᶜ γ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

------------------------------------------------------------------------
-- Inversion lemmas for usage

opaque
  unfolding erased

  -- An inversion lemma for erased.

  inv-usage-erased :
    γ ▸[ m ] erased t → 𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] t × γ ≤ᶜ 𝟘ᶜ × m PE.≡ 𝟘ᵐ[ ok ]
  inv-usage-erased {γ = γ} {ok = ok} ▸[] =
    case inv-usage-fst ▸[] of λ where
      (invUsageFst {δ = δ} m PE.refl ▸t γ≤ _) →
          ▸-𝟘 ▸t
        , (begin
             γ   ≤⟨ γ≤ ⟩
             δ   ≤⟨ ▸-𝟘ᵐ (▸-cong (ᵐ·𝟘≡𝟘ᵐ m ok) ▸t) ⟩
             𝟘ᶜ  ∎)
        , ᵐ·𝟘≡𝟘ᵐ m _
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset
