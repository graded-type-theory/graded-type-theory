------------------------------------------------------------------------
-- Some examples related to a "linear or affine types" modality
-- without a dedicated nr function
------------------------------------------------------------------------

open import Tools.Bool using (T; T-not⇔¬-T)
open import Tools.Level

open import Definition.Typed.Restrictions

open import Graded.Modality.Instances.Linear-or-affine
open import Graded.Modality.Variant lzero
open import Graded.Usage.Restrictions

module Graded.Modality.Instances.Linear-or-affine.Bad.No-dedicated-nr
  -- The modality variant.
  (variant : Modality-variant)
  (TR : Type-restrictions (linear-or-affine variant))
  (open Type-restrictions TR)
  (UR : Usage-restrictions (linear-or-affine variant))
  (open Usage-restrictions UR)
  -- It is assumed that "Π 𝟙 , 𝟘" is allowed.
  (Π-𝟙-𝟘 : Π-allowed 𝟙 𝟘)
  -- There is no dedicated nr function.
  ⦃ no-nr : Nr-not-available ⦄
  where

open Modality-variant variant

open import Tools.Empty
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
open import Tools.Relation

open import Graded.Modality Linear-or-affine

private

  -- The modality that is used in this file.

  linear-or-affine′ : Modality
  linear-or-affine′ = linear-or-affine variant

  module M = Modality linear-or-affine′

open import Graded.Context linear-or-affine′
open import Graded.Context.Properties linear-or-affine′
open import Graded.Modality.Instances.Examples TR Π-𝟙-𝟘
open import Graded.Modality.Properties linear-or-affine′
open import Graded.Mode linear-or-affine′
open import Graded.Usage linear-or-affine′ UR
open import Graded.Usage.Inversion linear-or-affine′ UR

-- The term double is well-resourced (even though it can be given a
-- linear type) if and only if 𝟘ᵐ is not allowed.

▸double : (¬ T 𝟘ᵐ-allowed) ⇔ ε ▸[ 𝟙ᵐ ] double
▸double =
    (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
     λ not-ok →
       lamₘ $
       natrec-no-nrₘ var (sucₘ var) var
         (sub ℕₘ $ begin
            𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ M.·-zeroʳ ⌜ 𝟘ᵐ? ⌝ ⟩
            𝟘ᶜ                ∎)
         ≤ᶜ-refl
         (⊥-elim ∘→ not-ok)
         ≤ᶜ-refl
         ≤ᶜ-refl)
  , (let open Tools.Reasoning.PartialOrder ≤-poset in
     λ ▸λ+ ok →
       case inv-usage-lam ▸λ+ of λ {
         (invUsageLam ▸+ _) →
       case inv-usage-natrec-no-nr ▸+ of λ {
         (_ , _ ∙ p , _ ∙ q , _ , _ ∙ r , _ , _ , _ , _
            , _ ∙ 𝟙≤r , _ , r≤₁ , _ , _ ∙ r≤₂) →
       case r≤₁ ok of λ {
         (_ ∙ r≤₁) →
       case lemma p $ begin
         𝟙                  ≤⟨ 𝟙≤r ⟩
         r                  ≤⟨ r≤₂ ⟩
         p + 𝟘 · q + 𝟙 · r  ≡⟨ cong (p +_) $
                               trans (cong₂ _+_ (M.·-zeroˡ q) (M.·-identityˡ _)) $
                               trans (M.+-identityˡ _) $
                               𝟙-maximal 𝟙≤r ⟩
         p + 𝟙              ∎
       of λ {
         p≡𝟘 →
       case begin
         𝟙  ≤⟨ 𝟙≤r ⟩
         r  ≤⟨ r≤₁ ⟩
         p  ≡⟨ p≡𝟘 ⟩
         𝟘  ∎
       of λ () }}}})
  where
  lemma : ∀ p → 𝟙 ≤ p + 𝟙 → p ≡ 𝟘
  lemma 𝟘  refl = refl
  lemma 𝟙  ()
  lemma ≤𝟙 ()
  lemma ≤ω ()

-- The term plus is not well-resourced.

¬▸plus : ¬ ε ▸[ 𝟙ᵐ ] plus
¬▸plus ▸λλ+ =
  case inv-usage-lam ▸λλ+ of λ {
    (invUsageLam ▸λ+ _) →
  case inv-usage-lam ▸λ+ of λ {
    (invUsageLam {δ = _ ∙ ≤ω} _  (_ ∙ ()));
    (invUsageLam {δ = _ ∙ 𝟘}  _  (_ ∙ ()));
    (invUsageLam {δ = _ ∙ ≤𝟙} _  (_ ∙ ()));
    (invUsageLam {δ = _ ∙ 𝟙}  ▸+ _) →
  case inv-usage-natrec-no-nr ▸+ of λ {
    (_ ∙ p ∙ _ , _ , _ , _ , _ ∙ q ∙ _ , ▸x0 , _ , _ , _
               , _ ∙ 𝟙≤q ∙ _ , _ ∙ q≤p ∙ _ , _) →
  case inv-usage-var ▸x0 of λ {
    (_ ∙ p≤𝟘 ∙ _) →
  case begin
    𝟙  ≤⟨ 𝟙≤q ⟩
    q  ≤⟨ q≤p ⟩
    p  ≤⟨ p≤𝟘 ⟩
    𝟘  ∎
  of λ () }}}}
  where
  open Tools.Reasoning.PartialOrder ≤-poset
