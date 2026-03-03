------------------------------------------------------------------------
-- Properties related to the usage relation and reduction for the
-- "Zero-one" mode structure.
------------------------------------------------------------------------

open import Graded.Modality
import Graded.Mode.Instances.Zero-one
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions
open import Graded.Mode.Instances.Zero-one.Variant

module Graded.Reduction.Zero-one
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  (mode-variant : Mode-variant 𝕄)
  (open Graded.Mode.Instances.Zero-one mode-variant)
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄 Zero-one-isMode)
  where

open Mode-variant mode-variant
open Type-restrictions TR
open Usage-restrictions UR

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Reduction TR UR
open import Graded.Usage UR
open import Graded.Usage.Inversion UR
open import Graded.Usage.Properties.Zero-one mode-variant UR
open import Definition.Typed TR
open import Definition.Typed.Eta-long-normal-form TR
open import Definition.Typed.Properties TR
open import Definition.Untyped M
open import Definition.Untyped.Normal-form M type-variant
open import Definition.Untyped.Whnf M type-variant

open import Tools.Bool using (T)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≢_)
import Tools.Reasoning.PartialOrder
open import Tools.Relation
open import Tools.Sum as ⊎ using (_⊎_; inj₁; inj₂)

private variable
  Γ : Cons _ _
  γ : Conₘ _
  t u A B : Term _
  m : Mode
  p q r : M

------------------------------------------------------------------------
-- Subject reduction properties for modality usage

module _
  (Unitʷ-η→ :
     ∀ {p q} →
     Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
     p ≤ 𝟘)
  where

  private opaque
    Unitʷ-η→′ :
      ∀ {m p q} →
        Unitʷ-η → Unitʷ-allowed → Unitrec-allowed m p q → ⌜ m ⌝ PE.≢ 𝟘 →
        p ≤ 𝟘
    Unitʷ-η→′ ok₁ ok₂ ok₃ m≢𝟘 =
      Unitʷ-η→ ok₁ ok₂ (lemma _ m≢𝟘 ok₃)
      where
      lemma :
        ∀ m → ⌜ m ⌝ ≢ 𝟘 → Unitrec-allowed m p q → Unitrec-allowed 𝟙ᵐ p q
      lemma 𝟘ᵐ m≢𝟘 _ = ⊥-elim (m≢𝟘 PE.refl)
      lemma 𝟙ᵐ _ ok  = ok

  opaque

    -- Term reduction preserves usage (for well-resourced definition
    -- contexts).

    usagePresTerm₀₁ :
      ▸[ m ] Γ .defs → γ ▸[ m ] t → Γ ⊢ t ⇒ u ∷ A → γ ▸[ m ] u
    usagePresTerm₀₁ =
      usagePresTerm Unitʷ-η→′

  opaque

    -- Type reduction preserves usage (for well-resourced definition
    -- contexts).

    usagePres₀₁ : ▸[ m ] Γ .defs → γ ▸[ m ] A → Γ ⊢ A ⇒ B → γ ▸[ m ] B
    usagePres₀₁ = usagePres Unitʷ-η→′

  opaque

    -- Multi-step term reduction preserves usage (for well-resourced
    -- definition contexts).

    usagePres*Term₀₁ :
      ▸[ m ] Γ .defs → γ ▸[ m ] t → Γ ⊢ t ⇒* u ∷ A → γ ▸[ m ] u
    usagePres*Term₀₁ = usagePres*Term Unitʷ-η→′

  opaque

    -- Multi-step type reduction preserves usage (for well-resourced
    -- definition contexts).

    usagePres*₀₁ :
      ▸[ m ] Γ .defs → γ ▸[ m ] A → Γ ⊢ A ⇒* B → γ ▸[ m ] B
    usagePres*₀₁ = usagePres* Unitʷ-η→′

------------------------------------------------------------------------
-- Some results related to η-long normal forms

-- If "Σˢ p , q" is allowed, then variable 0 is well-typed and
-- well-resourced (with respect to the usage context ε ∙ 𝟙), and is
-- definitionally equal to the η-long normal form
-- prodˢ p (fst p (var x0)) (snd p (var x0)). However, this η-long
-- normal form is well-resourced with respect to the usage context
-- ε ∙ 𝟙 if and only if either p is 𝟙, or p is 𝟘, 𝟘ᵐ is allowed, and
-- 𝟙 ≤ 𝟘.

η-long-nf-for-0⇔≡𝟙⊎≡𝟘 :
  Σˢ-allowed p q →
  let Γ = ε ∙ (Σˢ p , q ▷ ℕ ▹ ℕ)
      γ = ε ∙ 𝟙
      A = Σˢ p , q ▷ ℕ ▹ ℕ
      t = var x0
      u = prodˢ p (fst p (var x0)) (snd p (var x0))
  in
  ε » Γ ⊢ t ∷ A ×
  γ ▸[ 𝟙ᵐ ] t ×
  ε » Γ ⊢nf u ∷ A ×
  ε » Γ ⊢ t ≡ u ∷ A ×
  (γ ▸[ 𝟙ᵐ ] u ⇔ (p PE.≡ 𝟙 ⊎ p PE.≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘))
η-long-nf-for-0⇔≡𝟙⊎≡𝟘 {p = p} ok =
    ⊢0
  , var
  , prodₙ (⊢ℕ ε∙Σℕℕ∙ℕ)
      (neₙ ℕₙ (fstₙ Σℕℕ∙ℕ⊢ℕ (varₙ (∙ ⊢Σℕℕ) here)))
      (neₙ ℕₙ (sndₙ Σℕℕ∙ℕ⊢ℕ (varₙ (∙ ⊢Σℕℕ) here)))
      ok
  , sym′ (Σ-η-prod-fst-snd ⊢0)
  , (ε ∙ 𝟙 ▸[ 𝟙ᵐ ] u′                              ⇔⟨ lemma₁ ⟩
     (𝟙 ≤ p × (⌞ p ⌟ PE.≡ 𝟙ᵐ → p ≤ 𝟙))             ⇔⟨ id⇔ ×-cong-⇔ ⌞⌟≡𝟙→⇔⊎𝟘ᵐ×≡𝟘 ⟩
     (𝟙 ≤ p × (p ≤ 𝟙 ⊎ T 𝟘ᵐ-allowed × p PE.≡ 𝟘))   ⇔⟨ lemma₂ ⟩
     (p PE.≡ 𝟙 ⊎ p PE.≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘)  □⇔)
  where
  u′      = prodˢ p (fst p (var x0)) (snd p (var x0))
  ⊢Σℕℕ    = ΠΣⱼ (⊢ℕ (∙ ⊢ℕ (ε ε))) ok
  ε∙Σℕℕ∙ℕ = ∙ ⊢ℕ (∙ ⊢Σℕℕ)
  Σℕℕ∙ℕ⊢ℕ = ⊢ℕ ε∙Σℕℕ∙ℕ
  ⊢0      = var₀ ⊢Σℕℕ

  lemma₁ : ε ∙ 𝟙 ▸[ 𝟙ᵐ ] u′ ⇔ (𝟙 ≤ p × (⌞ p ⌟ PE.≡ 𝟙ᵐ → p ≤ 𝟙))
  lemma₁ =
      (λ ▸1,2 →
         let open Tools.Reasoning.PartialOrder ≤-poset in
         case inv-usage-prodˢ ▸1,2 of λ {
           (invUsageProdˢ {δ = _ ∙ q₁} {η = _ ∙ q₂} ▸1 _ (_ ∙ 𝟙≤pq₁∧q₂)) →
         case inv-usage-fst₀₁ ▸1 of λ {
           (_ ∙ q₃ , _ , _ , ▸0 , _ ∙ q₁≤q₃ , ⌞p⌟≡𝟙ᵐ→p≤𝟙) →
         case inv-usage-var ▸0 of λ {
           (_ ∙ q₃≤⌜⌞p⌟⌝) →
           (begin
              𝟙              ≤⟨ 𝟙≤pq₁∧q₂ ⟩
              p · q₁ ∧ q₂    ≤⟨ ∧-decreasingˡ _ _ ⟩
              p · q₁         ≤⟨ ·-monotoneʳ q₁≤q₃ ⟩
              p · q₃         ≤⟨ ·-monotoneʳ q₃≤⌜⌞p⌟⌝ ⟩
              p · ⌜ ⌞ p ⌟ ⌝  ≡⟨ ·⌜⌞⌟⌝ ⟩
              p              ∎)
         , ⌞p⌟≡𝟙ᵐ→p≤𝟙 }}})
    , (λ (𝟙≤p , ⌞p⌟≡𝟙→≤𝟙) →
         sub
           (prodˢₘ (fstₘ₀₁ 𝟙ᵐ var PE.refl ⌞p⌟≡𝟙→≤𝟙) (sndₘ var))
           (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
              ε ∙ 𝟙                  ≤⟨ ε ∙ ∧-greatest-lower-bound 𝟙≤p ≤-refl ⟩
              ε ∙ p ∧ 𝟙              ≈˘⟨ ε ∙ ∧-congʳ ·⌜⌞⌟⌝ ⟩
              ε ∙ p · ⌜ ⌞ p ⌟ ⌝ ∧ 𝟙  ∎))

  lemma₂ :
    (𝟙 ≤ p × (p ≤ 𝟙 ⊎ T 𝟘ᵐ-allowed × p PE.≡ 𝟘)) ⇔
    (p PE.≡ 𝟙 ⊎ p PE.≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘)
  lemma₂ =
      (λ where
         (𝟙≤p , inj₁ p≤𝟙) →
           inj₁ (≤-antisym p≤𝟙 𝟙≤p)
         (𝟙≤𝟘 , inj₂ (ok , PE.refl)) →
           inj₂ (PE.refl , ok , 𝟙≤𝟘))
    , (λ where
         (inj₁ PE.refl) →
           ≤-refl , inj₁ ≤-refl
         (inj₂ (PE.refl , ok , 𝟙≤𝟘)) →
           𝟙≤𝟘 , inj₂ (ok , PE.refl))

-- If "Π 𝟙 , r" and "Σˢ p , q" are allowed, then the identity function
-- lam 𝟙 (var x0) has type
-- Π 𝟙 , r ▷ Σˢ p , q ▷ ℕ ▹ ℕ ▹ Σˢ p , q ▷ ℕ ▹ ℕ, is well-resourced in
-- the empty context, and is definitionally equal to the η-long normal
-- form lam 𝟙 (prodˢ p (fst p (var x0)) (snd p (var x0))), however,
-- this η-long normal form is well-resourced in the empty context if
-- and only if either p is 𝟙, or p is 𝟘, 𝟘ᵐ is allowed, and 𝟙 ≤ 𝟘.

η-long-nf-for-id⇔≡𝟙⊎≡𝟘 :
  Π-allowed 𝟙 r →
  Σˢ-allowed p q →
  let A = Π 𝟙 , r ▷ Σˢ p , q ▷ ℕ ▹ ℕ ▹ Σˢ p , q ▷ ℕ ▹ ℕ
      t = lam 𝟙 (var x0)
      u = lam 𝟙 (prodˢ p (fst p (var x0)) (snd p (var x0)))
  in
  ε » ε ⊢ t ∷ A ×
  ε ▸[ 𝟙ᵐ ] t ×
  ε » ε ⊢nf u ∷ A ×
  ε » ε ⊢ t ≡ u ∷ A ×
  (ε ▸[ 𝟙ᵐ ] u ⇔ (p PE.≡ 𝟙 ⊎ p PE.≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘))
η-long-nf-for-id⇔≡𝟙⊎≡𝟘 {r = r} {p = p} {q = q} ok₁ ok₂ =
  case η-long-nf-for-0⇔≡𝟙⊎≡𝟘 ok₂ of λ {
    (⊢t , ▸t , ⊢u , t≡u , ▸u⇔) →
    lamⱼ′ ok₁ ⊢t
  , lamₘ (sub ▸t
            (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
               𝟘ᶜ ∙ 𝟙 · 𝟙  ≈⟨ ≈ᶜ-refl ∙ ·-identityˡ _ ⟩
               𝟘ᶜ ∙ 𝟙      ∎))
  , lamₙ ⊢u ok₁
  , lam-cong t≡u ok₁
  , (ε ▸[ 𝟙ᵐ ] lam 𝟙 u′                            ⇔⟨ (λ ▸λ* → case inv-usage-lam ▸λ* of λ where
                                                         (invUsageLam {δ = ε} ▸* _) → ▸*)
                                                    , lamₘ
                                                    ⟩
     ε ∙ 𝟙 · 𝟙 ▸[ 𝟙ᵐ ] u′                          ≡⟨ PE.cong (λ p → _ ∙ p ▸[ _ ] _) (·-identityˡ _) ⟩⇔
     ε ∙ 𝟙 ▸[ 𝟙ᵐ ] u′                              ⇔⟨ ▸u⇔ ⟩
     (p PE.≡ 𝟙 ⊎ p PE.≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘)  □⇔) }
  where
  u′ = prodˢ p (fst p (var x0)) (snd p (var x0))

-- The type Well-resourced-normal-form-without-η-long-normal-form is
-- inhabited if equality reflection is not allowed and there are
-- quantities p, q and r such that
-- * p is distinct from 𝟙,
-- * "p is 𝟘 and 𝟘ᵐ is allowed and 𝟙 ≤ 𝟘" does not hold,
-- * Σˢ-allowed p q holds, and
-- * Π-allowed 𝟙 r holds.

well-resourced-normal-form-without-η-long-normal-form-Σˢ :
  ⦃ not-ok : No-equality-reflection ⦄ →
  ¬ Level-allowed →
  p ≢ 𝟙 →
  ¬ (p PE.≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘) →
  Σˢ-allowed p q →
  Π-allowed 𝟙 r →
  Well-resourced-normal-form-without-η-long-normal-form
well-resourced-normal-form-without-η-long-normal-form-Σˢ
  {p = p} not-ok p≢𝟙 ¬[p≡𝟘×𝟘ᵐ×𝟙≤𝟘] ok₁ ok₂ =
  case η-long-nf-for-id⇔≡𝟙⊎≡𝟘 ok₂ ok₁ of λ {
    (⊢t , ▸t , ⊢u , t≡u , ▸u→ , _) →
    _ , _
  , ⊢t
  , lamₙ (ne (var _))
  , ▸t
  , λ (v , ⊢v , t≡v , ▸v) →                                        $⟨ ▸v ⟩
      ε ▸[ 𝟙ᵐ ] v                                                  →⟨ PE.subst (_▸[_]_ _ _) $
                                                                      normal-terms-unique not-ok ⊢v ⊢u (trans (sym′ t≡v) t≡u) ⟩
      ε ▸[ 𝟙ᵐ ] lam 𝟙 (prodˢ p (fst p (var x0)) (snd p (var x0)))  →⟨ ▸u→ ⟩
      p PE.≡ 𝟙 ⊎ p PE.≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘                   →⟨ (λ { (inj₁ p≡𝟙) → p≢𝟙 p≡𝟙; (inj₂ hyp) → ¬[p≡𝟘×𝟘ᵐ×𝟙≤𝟘] hyp }) ⟩
      ⊥                                                            □ }
