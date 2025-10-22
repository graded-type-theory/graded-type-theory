------------------------------------------------------------------------
-- A well-resourced term has a well-resourced η-long normal form
-- (given certain assumptions)
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions

module Graded.FullReduction
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions TR
open Usage-restrictions UR

open import Tools.Bool
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

open import Definition.Untyped M as U
open import Definition.Typed TR
open import Definition.Typed.Eta-long-normal-form TR
open import Definition.Typed.Inversion TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Syntactic TR

open import Definition.Conversion TR
open import Definition.Conversion.Consequences.Completeness TR
import Definition.Conversion.FullReduction TR as FR

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.FullReduction.Assumptions TR UR
open import Graded.Modality.Properties 𝕄
open import Graded.Reduction TR UR
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Inversion 𝕄 UR
open import Graded.Usage.Properties 𝕄 UR
open import Graded.Usage.Weakening 𝕄 UR

open import Graded.Mode 𝕄

private
  variable
    n : Nat
    Γ : Con Term n
    A A′ t t′ : Term n
    p : M
    γ : Conₘ n
    m : Mode
    q r : M
    s : Strength
    l : Universe-level

------------------------------------------------------------------------
-- Some lemmas

-- The lemmas below are proved under the assumption that
-- Full-reduction-assumptions holds.

module _ (as : Full-reduction-assumptions) where

  open Full-reduction-assumptions as
  open Full-reduction-assumptions′
         (Full-reduction-assumptions⇔Full-reduction-assumptions′
            .proj₁ as)

  private

    -- A lemma used below.

    Unitʷ-η→ :
      Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
      p ≤ 𝟘
    Unitʷ-η→ η ok _ =
      case sink⊎𝟙≤𝟘 ok (inj₂ η) of λ where
        (inj₁ (() , _))
        (inj₂ 𝟙≤𝟘)      → ≤𝟘⇔𝟙≤𝟘 .proj₂ 𝟙≤𝟘

    -- A lemma used in the η-unit case of fullRedTermConv↓.
    --
    -- Note that the Unit-allowed and Unit-with-η assumptions are only
    -- used when the mode is 𝟙ᵐ. Currently the typing relation does
    -- not track modes, but if it did, then it might suffice to
    -- require that these assumptions hold when the mode is 𝟙ᵐ.

    Unit-lemma :
      Unit-allowed s → Unit-with-η s → γ ▸[ m ] t → γ ▸[ m ] star s
    Unit-lemma {s} {γ} {m} ok η ▸t =
      case lemma of λ
        (δ , prop , γ≤) →
      case PE.singleton s of λ where
        (𝕤 , PE.refl) → sub (starˢₘ (prop ∘→ inj₂)) γ≤
        (𝕨 , PE.refl) → sub starₘ $ begin
          γ            ≤⟨ γ≤ ⟩
          ⌜ m ⌝ ·ᶜ δ   ≈˘⟨ ·ᶜ-congˡ (prop (inj₁ PE.refl)) ⟩
          ⌜ m ⌝ ·ᶜ 𝟘ᶜ  ≈⟨ ·ᶜ-zeroʳ _ ⟩
          𝟘ᶜ           ∎
      where
      open ≤ᶜ-reasoning

      lemma :
        ∃ λ δ → (s PE.≡ 𝕨 ⊎ ¬ Starˢ-sink → 𝟘ᶜ ≈ᶜ δ) × γ ≤ᶜ ⌜ m ⌝ ·ᶜ δ
      lemma =
        case PE.singleton m of λ where
          (𝟘ᵐ , PE.refl) →
              𝟘ᶜ , (λ _ → ≈ᶜ-refl)
            , (begin
                 γ        ≤⟨ ▸-𝟘ᵐ ▸t ⟩
                 𝟘ᶜ       ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
                 𝟘 ·ᶜ 𝟘ᶜ  ∎)
          (𝟙ᵐ , PE.refl) → case sink⊎≤𝟘 ok η of λ where
            (inj₁ (PE.refl , sink)) →
                γ
              , (λ where
                   (inj₁ ())
                   (inj₂ ¬sink) →
                     ⊥-elim (not-sink-and-no-sink sink ¬sink))
              , (begin
                   γ       ≈˘⟨ ·ᶜ-identityˡ _ ⟩
                   𝟙 ·ᶜ γ  ∎)
            (inj₂ ≤𝟘) →
                𝟘ᶜ
              , (λ _ → ≈ᶜ-refl)
              , (begin
                   γ        ≤⟨ ≤ᶜ𝟘ᶜ ≤𝟘 ⟩
                   𝟘ᶜ       ≈˘⟨ ·ᶜ-identityˡ _ ⟩
                   𝟙 ·ᶜ 𝟘ᶜ  ∎)

    -- A lemma used in the Σ-η case of fullRedTermConv↓.
    --
    -- Note that the Σˢ-allowed assumption is only used when the mode
    -- is 𝟙ᵐ. Currently the typing relation does not track modes, but
    -- if it did, then it might suffice to require that the Σˢ-allowed
    -- assumptions hold when the mode is 𝟙ᵐ.

    Σ-η-lemma :
      ∀ m →
      Σˢ-allowed p q →
      γ ▸[ m ] t →
      ∃ λ δ → δ ▸[ m ᵐ· p ] fst p t × γ ≤ᶜ p ·ᶜ δ
    Σ-η-lemma {p = p} {γ = γ} = λ where
      𝟘ᵐ[ ok ] _ ▸t →
          𝟘ᶜ
        , fstₘ 𝟘ᵐ[ ok ] (▸-𝟘 ▸t) PE.refl (λ ())
        , (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
             γ        ≤⟨ ▸-𝟘ᵐ ▸t ⟩
             𝟘ᶜ       ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
             p ·ᶜ 𝟘ᶜ  ∎)
      𝟙ᵐ ok ▸t →
          ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ
        , fstₘ 𝟙ᵐ
            (▸-cong
               (let open Tools.Reasoning.PropositionalEquality in
                  ⌞ p ⌟ ·ᵐ 𝟙ᵐ  ≡⟨ ·ᵐ-identityʳ _ ⟩
                  ⌞ p ⌟        ∎)
               (▸-· ▸t))
            PE.refl
            (⌞⌟≡𝟙ᵐ→≤𝟙 ok)
        , (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
             γ                     ≤⟨ ·ᶜ-increasing (·-increasing ok) ⟩
             p ·ᶜ γ                ≈˘⟨ ·ᶜ-congʳ ·⌜⌞⌟⌝ ⟩
             (p · ⌜ ⌞ p ⌟ ⌝) ·ᶜ γ  ≈⟨ ·ᶜ-assoc _ _ _ ⟩
             p ·ᶜ ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ   ∎)

  mutual

    -- Some lemmas used to prove the main theorems below.

    fullRedNe :
      ⦃ not-ok : No-equality-reflection ⦄ →
      (⊢t : Γ ⊢ t ~ t′ ↑ A) → γ ▸[ m ] t →
      γ ▸[ m ] FR.fullRedNe ⊢t .proj₁
    fullRedNe {Γ = Γ} = λ where
      (var-refl _ _) ▸x →
        ▸x
      (lower-cong t~) ▸lower-t →
        lowerₘ (fullRedNe~↓ t~ (inv-usage-lower ▸lower-t))
      (app-cong t~ u↑) ▸tu →
        case inv-usage-app ▸tu of λ {
          (invUsageApp ▸t ▸u γ≤) →
        sub (fullRedNe~↓ t~ ▸t ∘ₘ fullRedTermConv↑ u↑ ▸u) γ≤ }
      (fst-cong t~) ▸fst-t →
        case inv-usage-fst ▸fst-t of λ {
          (invUsageFst m′ PE.refl ▸t γ≤ ok) →
        sub (fstₘ m′ (fullRedNe~↓ t~ ▸t) PE.refl ok) γ≤ }
      (snd-cong t~) ▸snd-t →
        case inv-usage-snd ▸snd-t of λ {
          (invUsageSnd ▸t γ≤) →
        sub (sndₘ (fullRedNe~↓ t~ ▸t)) γ≤ }
      (natrec-cong A↑ t↑ u↑ v~) ▸natrec →
        case inv-usage-natrec ▸natrec of λ {
          (invUsageNatrec ▸t ▸u ▸v ▸A γ≤ extra) →
        case extra of λ where
          invUsageNatrecNr →
            sub (natrecₘ (fullRedTermConv↑ t↑ ▸t) (fullRedTermConv↑ u↑ ▸u)
                   (fullRedNe~↓ v~ ▸v) (fullRedConv↑ A↑ ▸A))
              γ≤
          (invUsageNatrecNoNr χ≤δ χ≤η χ≤θ fix) →
            sub (natrec-no-nrₘ (fullRedTermConv↑ t↑ ▸t)
                   (fullRedTermConv↑ u↑ ▸u) (fullRedNe~↓ v~ ▸v)
                   (fullRedConv↑ A↑ ▸A) χ≤δ χ≤η χ≤θ fix)
              γ≤
          (invUsageNatrecNoNrGLB x-glb χ-glb) →
            sub (natrec-no-nr-glbₘ (fullRedTermConv↑ t↑ ▸t)
                  (fullRedTermConv↑ u↑ ▸u) (fullRedNe~↓ v~ ▸v)
                  (fullRedConv↑ A↑ ▸A) x-glb χ-glb) γ≤}
      (prodrec-cong C↑ u~ v↑) ▸prodrec →
        case inv-usage-prodrec ▸prodrec of λ {
          (invUsageProdrec ▸u ▸v ▸C ok₁ γ≤) →
        sub (prodrecₘ (fullRedNe~↓ u~ ▸u) (fullRedTermConv↑ v↑ ▸v)
               (fullRedConv↑ C↑ ▸C) ok₁)
          γ≤ }
      (emptyrec-cong A↑ t~) ▸emptyrec →
        case inv-usage-emptyrec ▸emptyrec of λ {
          (invUsageEmptyrec ▸t ▸A ok γ≤) →
        sub (emptyrecₘ (fullRedNe~↓ t~ ▸t) (fullRedConv↑ A↑ ▸A) ok) γ≤ }
      (unitrec-cong A↑ t~ u↑ _) ▸unitrec →
        case inv-usage-unitrec ▸unitrec of λ {
          (invUsageUnitrec ▸A ▸t ▸u ok γ≤) →
        sub (unitrecₘ (fullRedConv↑ A↑ ▸A) (fullRedNe~∷ t~ ▸t) (fullRedTermConv↑ u↑ ▸u)
              ok)
            γ≤ }
      (J-cong A↑ t↑ B↑ u↑ v↑ w~ _) ▸J →
        case inv-usage-J ▸J of λ where
          (invUsageJ ok₁ ok₂ ▸A ▸t ▸B ▸u ▸v ▸w γ≤) →
            sub (Jₘ ok₁ ok₂ (fullRedConv↑ A↑ ▸A)
                   (fullRedTermConv↑ t↑ ▸t) (fullRedConv↑ B↑ ▸B)
                   (fullRedTermConv↑ u↑ ▸u) (fullRedTermConv↑ v↑ ▸v)
                   (fullRedNe~↓ w~ ▸w))
              γ≤
          (invUsageJ₀₁ ok p≡𝟘 q≡𝟘 ▸A ▸t ▸B ▸u ▸v ▸w γ≤) →
            sub (J₀ₘ₁ ok p≡𝟘 q≡𝟘 (fullRedConv↑ A↑ ▸A)
                   (fullRedTermConv↑ t↑ ▸t) (fullRedConv↑ B↑ ▸B)
                   (fullRedTermConv↑ u↑ ▸u) (fullRedTermConv↑ v↑ ▸v)
                   (fullRedNe~↓ w~ ▸w))
              γ≤
          (invUsageJ₀₂ ok ▸A ▸t ▸B ▸u ▸v ▸w γ≤) →
            sub (J₀ₘ₂ ok (fullRedConv↑ A↑ ▸A) (fullRedTermConv↑ t↑ ▸t)
                   (fullRedConv↑ B↑ ▸B) (fullRedTermConv↑ u↑ ▸u)
                   (fullRedTermConv↑ v↑ ▸v) (fullRedNe~↓ w~ ▸w))
              γ≤
      (K-cong A↑ t↑ B↑ u↑ v~ _ _) ▸K →
        case inv-usage-K ▸K of λ where
          (invUsageK ok₁ ok₂ ▸A ▸t ▸B ▸u ▸v γ≤) →
            sub (Kₘ ok₁ ok₂ (fullRedConv↑ A↑ ▸A)
                   (fullRedTermConv↑ t↑ ▸t) (fullRedConv↑ B↑ ▸B)
                   (fullRedTermConv↑ u↑ ▸u) (fullRedNe~↓ v~ ▸v))
              γ≤
          (invUsageK₀₁ ok p≡𝟘 ▸A ▸t ▸B ▸u ▸v γ≤) →
            sub (K₀ₘ₁ ok p≡𝟘 (fullRedConv↑ A↑ ▸A)
                   (fullRedTermConv↑ t↑ ▸t) (fullRedConv↑ B↑ ▸B)
                   (fullRedTermConv↑ u↑ ▸u) (fullRedNe~↓ v~ ▸v))
              γ≤
          (invUsageK₀₂ ok ▸A ▸t ▸B ▸u ▸v γ≤) →
            sub (K₀ₘ₂ ok (fullRedConv↑ A↑ ▸A) (fullRedTermConv↑ t↑ ▸t)
                   (fullRedConv↑ B↑ ▸B) (fullRedTermConv↑ u↑ ▸u)
                   (fullRedNe~↓ v~ ▸v))
              γ≤
      ([]-cong-cong l↑ A↑ t↑ u↑ v~ _ _) ▸[]-cong →
        let invUsage-[]-cong ▸l ▸A ▸t ▸u ▸v ok γ≤ =
              inv-usage-[]-cong ▸[]-cong
        in
        sub
          ([]-congₘ (fullRedTermConv↑ l↑ ▸l) (fullRedTermConv↑ A↑ ▸A)
             (fullRedTermConv↑ t↑ ▸t) (fullRedTermConv↑ u↑ ▸u)
             (fullRedNe~↓ v~ ▸v) ok)
          γ≤

    fullRedNe~↓ :
      ⦃ not-ok : No-equality-reflection ⦄ →
      (⊢t : Γ ⊢ t ~ t′ ↓ A) → γ ▸[ m ] t →
      γ ▸[ m ] FR.fullRedNe~↓ ⊢t .proj₁
    fullRedNe~↓ ([~] _ _ k~l) γ▸t =
      fullRedNe k~l γ▸t

    fullRedNe~∷ :
      ⦃ not-ok : No-equality-reflection ⦄ →
      (⊢t : Γ ⊢ t ~ t′ ∷ A) → γ ▸[ m ] t →
      γ ▸[ m ] FR.fullRedNe~∷ ⊢t .proj₁
    fullRedNe~∷ (↑ A≡B k~↑l) γ▸t = fullRedNe k~↑l γ▸t

    fullRedConv↑ :
      ⦃ not-ok : No-equality-reflection ⦄ →
      (⊢A : Γ ⊢ A [conv↑] A′) → γ ▸[ m ] A →
      γ ▸[ m ] FR.fullRedConv↑ ⊢A .proj₁
    fullRedConv↑ ([↑] _ _ (D , _) _ A′<>B′) γ▸A =
      fullRedConv↓ A′<>B′ (usagePres* Unitʷ-η→ γ▸A D)

    fullRedConv↓ :
      ⦃ not-ok : No-equality-reflection ⦄ →
      (⊢A : Γ ⊢ A [conv↓] A′) → γ ▸[ m ] A →
      γ ▸[ m ] FR.fullRedConv↓ ⊢A .proj₁
    fullRedConv↓ = λ where
      (Level-refl _)        ▸Level → ▸Level
      (Lift-cong x x₁) ▸Lift →
        case inv-usage-Lift ▸Lift of λ ((δ , ▸l) , ▸F) →
          Liftₘ (fullRedTermConv↑ x ▸l) (fullRedConv↑ x₁ ▸F)
      (U-cong     l↑)       ▸U    →
        case inv-usage-U ▸U of λ (γ≤ , _ , ▸l) →
          sub (Uₘ (fullRedTermConv↑ l↑ ▸l)) γ≤
      (ℕ-refl     _)        ▸ℕ    → ▸ℕ
      (Empty-refl _)        ▸⊥    → ▸⊥
      (Unit-refl  _ _)      ▸⊤    → ▸⊤
      (ne A~)               ▸A    → fullRedNe~↓ A~ ▸A
      (ΠΣ-cong A↑ B↑ ok) ▸ΠΣAB →
        case inv-usage-ΠΣ ▸ΠΣAB of λ {
          (invUsageΠΣ ▸A ▸B γ≤) →
        sub (ΠΣₘ (fullRedConv↑ A↑ ▸A) (fullRedConv↑ B↑ ▸B)) γ≤ }
      (Id-cong A↑ t↑ u↑) ▸Id →
        case inv-usage-Id ▸Id of λ where
          (invUsageId ok ▸A ▸t ▸u γ≤) →
            sub (Idₘ ok (fullRedConv↑ A↑ ▸A) (fullRedTermConv↑ t↑ ▸t)
                   (fullRedTermConv↑ u↑ ▸u))
              γ≤
          (invUsageId₀ ok ▸A ▸t ▸u γ≤) →
            sub (Id₀ₘ ok (fullRedConv↑ A↑ ▸A) (fullRedTermConv↑ t↑ ▸t)
                   (fullRedTermConv↑ u↑ ▸u))
              γ≤

    fullRedTermConv↑ :
      ⦃ not-ok : No-equality-reflection ⦄ →
      (⊢t : Γ ⊢ t [conv↑] t′ ∷ A) → γ ▸[ m ] t →
      γ ▸[ m ] FR.fullRedTermConv↑ ⊢t .proj₁
    fullRedTermConv↑ ([↑]ₜ _ _ _ _ (d , _) _ t<>u) γ▸t =
      fullRedTermConv↓ t<>u (usagePres*Term Unitʷ-η→ γ▸t d)

    fullRedTermConv↑ᵛ :
      ⦃ not-ok : No-equality-reflection ⦄ →
      ∀ {tᵛ} (⊢t : Γ ⊢ t ↑ᵛ tᵛ) → γ ▸[ m ] t →
      γ ▸[ m ] FR.fullRedTermConv↑ᵛ ⊢t .proj₁
    fullRedTermConv↑ᵛ ([↑]ᵛ (d , _) t↓v) ▸t =
      fullRedTermConv↓ᵛ t↓v (usagePres*Term Unitʷ-η→ ▸t d)

    fullRedTermConv~ᵛ :
      ⦃ not-ok : No-equality-reflection ⦄ →
      ∀ {tᵛ} (⊢t : Γ ⊢ t ~ᵛ tᵛ) → γ ▸[ m ] t →
      γ ▸[ m ] FR.fullRedTermConv~ᵛ ⊢t .proj₁
    fullRedTermConv~ᵛ (supᵘˡₙ x ⊢t x₁) ▸t =
      case inv-usage-supᵘ ▸t of λ (δ , η , γ≤ , ▸u , ▸v) →
        sub (supᵘₘ (fullRedTermConv~ᵛ ⊢t ▸u) (fullRedTermConv↑ᵛ x₁ ▸v)) γ≤
    fullRedTermConv~ᵛ (supᵘʳₙ x x₁ ⊢t) ▸t =
      case inv-usage-supᵘ ▸t of λ (δ , η , γ≤ , ▸u , ▸v) →
        sub (supᵘₘ
          (sucᵘₘ (fullRedTermConv↑ᵛ x₁ (inv-usage-sucᵘ ▸u)))
          (fullRedTermConv~ᵛ ⊢t ▸v))
          γ≤
    fullRedTermConv~ᵛ (neₙ [t] x) ▸t = fullRedNe~↓ [t] ▸t

    fullRedTermConv↓ᵛ :
      ⦃ not-ok : No-equality-reflection ⦄ →
      ∀ {tᵛ} (⊢t : Γ ⊢ t ↓ᵛ tᵛ) → γ ▸[ m ] t →
      γ ▸[ m ] FR.fullRedTermConv↓ᵛ ⊢t .proj₁
    fullRedTermConv↓ᵛ (zeroᵘₙ x) ▸t = ▸t
    fullRedTermConv↓ᵛ (sucᵘₙ PE.refl x₁) ▸t = sucᵘₘ (fullRedTermConv↑ᵛ x₁ (inv-usage-sucᵘ ▸t))
    fullRedTermConv↓ᵛ (neₙ x) ▸t = fullRedTermConv~ᵛ x ▸t

    fullRedTermConv↓Level :
      ⦃ not-ok : No-equality-reflection ⦄ →
      (⊢t : Γ ⊢ t [conv↓] t′ ∷Level) → γ ▸[ m ] t →
      γ ▸[ m ] FR.fullRedTermConv↓Level ⊢t .proj₁
    fullRedTermConv↓Level ([↓]ˡ tᵛ uᵛ t↓ u↓ t≡u) ▸t =
      fullRedTermConv↓ᵛ t↓ ▸t

    fullRedTermConv↓ :
      ⦃ not-ok : No-equality-reflection ⦄ →
      (⊢t : Γ ⊢ t [conv↓] t′ ∷ A) → γ ▸[ m ] t →
      γ ▸[ m ] FR.fullRedTermConv↓ ⊢t .proj₁
    fullRedTermConv↓ {Γ = Γ} {t = t} {γ = γ} {m = m} = λ where
      (Level-ins x)       y      → fullRedTermConv↓Level x y
      (Lift-η x x₁ x₂ x₃ x₄) ▸t  → liftₘ (fullRedTermConv↑ x₄ (lowerₘ ▸t))
      (ℕ-ins t~)          ▸t     → fullRedNe~↓ t~ ▸t
      (Empty-ins t~)      ▸t     → fullRedNe~↓ t~ ▸t
      (Unitʷ-ins _ t~)    ▸t     → fullRedNe~∷ t~ ▸t
      (Σʷ-ins _ _ t~)     ▸t     → fullRedNe~↓ t~ ▸t
      (ne-ins _ _ _ t~↓B) ▸t     → fullRedNe~↓ t~↓B ▸t
      (univ _ _ A↓)       ▸A     → fullRedConv↓ A↓ ▸A
      (zero-refl _)       ▸zero  → ▸zero
      (starʷ-refl _ _ _)  ▸star  → ▸star
      (suc-cong t↑)       ▸suc-t →
        case inv-usage-suc ▸suc-t of λ {
          (invUsageSuc ▸t γ≤) →
        sub (sucₘ (fullRedTermConv↑ t↑ ▸t)) γ≤ }
      (prod-cong _ t↑ u↑ _) ▸t,u →
        case inv-usage-prodʷ ▸t,u of λ {
          (invUsageProdʷ ▸t ▸u γ≤) →
        sub (prodʷₘ (fullRedTermConv↑ t↑ ▸t) (fullRedTermConv↑ u↑ ▸u))
          γ≤ }
      (η-eq {p = p} _ _ _ _ t0≡u0) ▸t →
        let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
        lamₘ $
        sub (fullRedTermConv↑ t0≡u0 (wkUsage (step id) ▸t ∘ₘ var)) $
        begin
          γ ∙ ⌜ m ⌝ · p                      ≈⟨ ≈ᶜ-refl ∙ ⌜⌝-·-comm m ⟩
          γ ∙ p · ⌜ m ⌝                      ≈˘⟨ +ᶜ-identityʳ _ ∙ ·⌜ᵐ·⌝ m ⟩
          γ +ᶜ 𝟘ᶜ ∙ p · ⌜ m ᵐ· p ⌝           ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _) ∙ +-identityˡ _ ⟩
          γ +ᶜ p ·ᶜ 𝟘ᶜ ∙ 𝟘 + p · ⌜ m ᵐ· p ⌝  ∎
      (Σ-η {p = p} ⊢t _ _ _ fst-t↑ snd-t↑) ▸t →
        case inversion-ΠΣ (syntacticTerm ⊢t) of λ {
          (_ , _ , ok) →
        case Σ-η-lemma m ok ▸t of λ {
          (δ , ▸fst-t , γ≤) →
        let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
        sub (prodˢₘ (fullRedTermConv↑ fst-t↑ ▸fst-t)
               (fullRedTermConv↑ snd-t↑ (sndₘ ▸t))) $
        begin
          γ            ≤⟨ ∧ᶜ-greatest-lower-bound γ≤ ≤ᶜ-refl ⟩
          p ·ᶜ δ ∧ᶜ γ  ∎ }}
      (η-unit ⊢t _ _ _ _ η) ▸t →
        Unit-lemma (⊢∷Unit→Unit-allowed ⊢t) η ▸t
      (Id-ins _ v~) ▸v   → fullRedNe~↓ v~ ▸v
      (rfl-refl _)  ▸rfl → sub rflₘ (inv-usage-rfl ▸rfl)

------------------------------------------------------------------------
-- The main theorems

-- If a type is well-formed and well-resourced, then it is
-- definitionally equal to a well-resourced type in η-long normal
-- form (given certain assumptions).

fullRed :
  ⦃ not-ok : No-equality-reflection ⦄ →
  Full-reduction-assumptions →
  Γ ⊢ A → γ ▸[ m ] A →
  ∃ λ B → Γ ⊢nf B × Γ ⊢ A ≡ B × γ ▸[ m ] B
fullRed as ⊢A ▸A =
  let B , ⊢B , A≡B = FR.fullRedConv↑ A≡A in
  B , ⊢B , A≡B , fullRedConv↑ as A≡A ▸A
  where
  A≡A = completeEq (refl ⊢A)

-- Full-reduction-term holds if, for every well-typed and
-- well-resourced term t, t is definitionally equal (with respect to a
-- certain context and type) to a term that is well-resourced (with
-- respect to a certain usage context and mode) and in η-long normal
-- form (with respect to a certain context and type).

Full-reduction-term : Set a
Full-reduction-term =
  ∀ {n} {Γ : Con Term n} {t A γ m} →
  Γ ⊢ t ∷ A → γ ▸[ m ] t →
  ∃ λ u → Γ ⊢nf u ∷ A × Γ ⊢ t ≡ u ∷ A × γ ▸[ m ] u

-- If a term is well-formed and well-resourced, then it is
-- definitionally equal to a well-resourced term in η-long normal
-- form (given certain assumptions).

fullRedTerm :
  ⦃ not-ok : No-equality-reflection ⦄ →
  Full-reduction-assumptions →
  Full-reduction-term
fullRedTerm as ⊢t ▸t =
  let u , ⊢u , t≡u = FR.fullRedTermConv↑ t≡t in
  u , ⊢u , t≡u , fullRedTermConv↑ as t≡t ▸t
  where
  t≡t = completeEqTerm (refl ⊢t)
