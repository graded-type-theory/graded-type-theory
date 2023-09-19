------------------------------------------------------------------------
-- A well-resourced term has a well-resourced η-long normal form
-- (given certain assumptions)
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions

module Graded.FullReduction
  {a} {M : Set a}
  (𝕄 : Modality M)
  (TR : Type-restrictions M)
  (UR : Usage-restrictions M)
  where

open Modality 𝕄
open Type-restrictions TR

open import Tools.Bool
open import Tools.Fin
open import Tools.Function
open import Tools.Level
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Sum using (_⊎_; inj₁; inj₂)
open import Tools.Unit

open import Definition.Untyped M as U hiding (_∷_)
open import Definition.Typed TR
open import Definition.Typed.Eta-long-normal-form TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Weakening TR
open import Definition.Typed.Consequences.DerivedRules TR
open import Definition.Typed.Consequences.InverseUniv TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Consequences.NeTypeEq TR
open import Definition.Typed.Consequences.Substitution TR
open import Definition.Typed.Consequences.Stability TR
open import Definition.Typed.Consequences.Syntactic TR

open import Definition.Conversion TR
open import Definition.Conversion.Consequences.Completeness TR
import Definition.Conversion.FullReduction TR as FR
open import Definition.Conversion.Soundness TR
open import Definition.Conversion.Whnf TR

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.FullReduction.Assumptions 𝕄 TR
open import Graded.Modality.Properties 𝕄
open import Graded.Reduction 𝕄 TR UR
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

------------------------------------------------------------------------
-- Some lemmas

-- The lemmas below are proved under the assumption that
-- Full-reduction-assumptions holds.

module _ (as : Full-reduction-assumptions) where

  open Full-reduction-assumptions′
         (Full-reduction-assumptions⇔Full-reduction-assumptions′
            .proj₁ as)

  private

    -- A lemma used in the Unit-ins and η-unit cases of
    -- fullRedTermConv↓.
    --
    -- Note that the Unit-allowed assumption is only used when the
    -- mode is 𝟙ᵐ. Currently the typing relation does not track modes,
    -- but if it did, then it might suffice to require that the
    -- Unit-allowed assumption holds when the mode is 𝟙ᵐ.

    ▸→≤ᶜ𝟘ᶜ :
      ∀ {t : Term n} m →
      Unit-allowed →
      γ ▸[ m ] t → γ ≤ᶜ 𝟘ᶜ
    ▸→≤ᶜ𝟘ᶜ 𝟘ᵐ _  γ▸t = ▸-𝟘ᵐ γ▸t
    ▸→≤ᶜ𝟘ᶜ 𝟙ᵐ ok _   = ≤ᶜ𝟘ᶜ (≤𝟘 ok)

    -- A lemma used in the Σ-η case of fullRedTermConv↓.
    --
    -- Note that the Σₚ-allowed assumption is only used when the mode
    -- is 𝟙ᵐ. Currently the typing relation does not track modes, but
    -- if it did, then it might suffice to require that the Σₚ-allowed
    -- assumptions hold when the mode is 𝟙ᵐ.

    Σ-η-lemma :
      ∀ m →
      Σₚ-allowed p q →
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
      (⊢t : Γ ⊢ t ~ t′ ↑ A) → γ ▸[ m ] t →
      γ ▸[ m ] FR.fullRedNe ⊢t .proj₁
    fullRedNe {Γ = Γ} = λ where
      (var-refl _ _) ▸x →
        ▸x
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
              γ≤ }
      (prodrec-cong C↑ u~ v↑) ▸prodrec →
        case inv-usage-prodrec ▸prodrec of λ {
          (invUsageProdrec ▸u ▸v ▸C ok₁ γ≤) →
        sub (prodrecₘ (fullRedNe~↓ u~ ▸u) (fullRedTermConv↑ v↑ ▸v)
               (fullRedConv↑ C↑ ▸C) ok₁)
          γ≤ }
      (emptyrec-cong A↑ t~) ▸emptyrec →
        case inv-usage-emptyrec ▸emptyrec of λ {
          (invUsageemptyrec ▸t ▸A γ≤) →
        sub (emptyrecₘ (fullRedNe~↓ t~ ▸t) (fullRedConv↑ A↑ ▸A)) γ≤ }

    fullRedNe~↓ :
      (⊢t : Γ ⊢ t ~ t′ ↓ A) → γ ▸[ m ] t →
      γ ▸[ m ] FR.fullRedNe~↓ ⊢t .proj₁
    fullRedNe~↓ ([~] _ _ _ k~l) γ▸t =
      fullRedNe k~l γ▸t

    fullRedConv↑ :
      (⊢A : Γ ⊢ A [conv↑] A′) → γ ▸[ m ] A →
      γ ▸[ m ] FR.fullRedConv↑ ⊢A .proj₁
    fullRedConv↑ ([↑] _ _ D _ _ _ A′<>B′) γ▸A =
      fullRedConv↓ A′<>B′ (usagePres* γ▸A D)

    fullRedConv↓ :
      (⊢A : Γ ⊢ A [conv↓] A′) → γ ▸[ m ] A →
      γ ▸[ m ] FR.fullRedConv↓ ⊢A .proj₁
    fullRedConv↓ = λ where
      (U-refl     _)        ▸U    → ▸U
      (ℕ-refl     _)        ▸ℕ    → ▸ℕ
      (Empty-refl _)        ▸⊥    → ▸⊥
      (Unit-refl  _ _)      ▸⊤    → ▸⊤
      (ne A~)               ▸A    → fullRedNe~↓ A~ ▸A
      (ΠΣ-cong ⊢A A↑ B↑ ok) ▸ΠΣAB →
        case inv-usage-ΠΣ ▸ΠΣAB of λ {
          (invUsageΠΣ ▸A ▸B γ≤) →
        sub (ΠΣₘ (fullRedConv↑ A↑ ▸A) (fullRedConv↑ B↑ ▸B)) γ≤ }

    fullRedTermConv↑ :
      (⊢t : Γ ⊢ t [conv↑] t′ ∷ A) → γ ▸[ m ] t →
      γ ▸[ m ] FR.fullRedTermConv↑ ⊢t .proj₁
    fullRedTermConv↑ ([↑]ₜ _ _ _ _ d _ _ _ _ t<>u) γ▸t =
      fullRedTermConv↓ t<>u (usagePres*Term γ▸t d)

    fullRedTermConv↓ :
      (⊢t : Γ ⊢ t [conv↓] t′ ∷ A) → γ ▸[ m ] t →
      γ ▸[ m ] FR.fullRedTermConv↓ ⊢t .proj₁
    fullRedTermConv↓ {Γ = Γ} {t = t} {γ = γ} {m = m} = λ where
      (ℕ-ins t~)     ▸t → fullRedNe~↓ t~ ▸t
      (Empty-ins t~) ▸t → fullRedNe~↓ t~ ▸t
      (Unit-ins t~)  ▸t →
        case syntacticEqTerm (soundness~↓ t~) of λ {
          (_ , ⊢t , _) →
        sub starₘ (▸→≤ᶜ𝟘ᶜ _ (⊢∷Unit→Unit-allowed ⊢t) ▸t) }
      (Σᵣ-ins _ _ t~)     ▸t     → fullRedNe~↓ t~ ▸t
      (ne-ins _ _ _ t~↓B) ▸t     → fullRedNe~↓ t~↓B ▸t
      (univ _ _ A↓)       ▸A     → fullRedConv↓ A↓ ▸A
      (zero-refl _)       ▸zero  → ▸zero
      (suc-cong t↑)       ▸suc-t →
        case inv-usage-suc ▸suc-t of λ {
          (invUsageSuc ▸t γ≤) →
        sub (sucₘ (fullRedTermConv↑ t↑ ▸t)) γ≤ }
      (prod-cong _ _ t↑ u↑ _) ▸t,u →
        case inv-usage-prodᵣ ▸t,u of λ {
          (invUsageProdᵣ ▸t ▸u γ≤) →
        sub (prodᵣₘ (fullRedTermConv↑ t↑ ▸t) (fullRedTermConv↑ u↑ ▸u))
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
        sub (prodₚₘ (fullRedTermConv↑ fst-t↑ ▸fst-t)
               (fullRedTermConv↑ snd-t↑ (sndₘ ▸t))) $
        begin
          γ            ≤⟨ ∧ᶜ-greatest-lower-bound γ≤ ≤ᶜ-refl ⟩
          p ·ᶜ δ ∧ᶜ γ  ∎ }}
      (η-unit ⊢t _ _ _) ▸t →
        sub starₘ (▸→≤ᶜ𝟘ᶜ _ (⊢∷Unit→Unit-allowed ⊢t) ▸t)

------------------------------------------------------------------------
-- The main theorems

-- If a type is well-formed and well-resourced, then it is
-- definitionally equal to a well-resourced type in η-long normal
-- form (given certain assumptions).

fullRed :
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
  Full-reduction-assumptions →
  Full-reduction-term
fullRedTerm as ⊢t ▸t =
  let u , ⊢u , t≡u = FR.fullRedTermConv↑ t≡t in
  u , ⊢u , t≡u , fullRedTermConv↑ as t≡t ▸t
  where
  t≡t = completeEqTerm (refl ⊢t)

-- Full-reduction-term is logically equivalent to
-- Full-reduction-assumptions.

Full-reduction-term⇔Full-reduction-assumptions :
  Full-reduction-term ⇔ Full-reduction-assumptions
Full-reduction-term⇔Full-reduction-assumptions =
    (λ red → λ where
       .𝟙≤𝟘 →
         Unit-allowed                                           →⟨ η-long-nf-for-0⇔𝟙≤𝟘 ⟩

         (let Γ = ε ∙ Unit
              γ = ε ∙ 𝟙
              A = Unit
              t = var x0
              u = star
          in
          Γ ⊢ t ∷ A ×
          γ ▸[ 𝟙ᵐ ] t ×
          Γ ⊢nf u ∷ A ×
          Γ ⊢ t ≡ u ∷ A ×
          (γ ▸[ 𝟙ᵐ ] u ⇔ 𝟙 ≤ 𝟘))                                →⟨ (λ (⊢t , ▸t , ⊢u , t≡u , ▸u⇔) →
                                                                     ⊢u , t≡u , ▸u⇔ , red ⊢t ▸t) ⟩
         (let Γ = ε ∙ Unit
              γ = ε ∙ 𝟙
              A = Unit
              t = var x0
              u = star
          in
          Γ ⊢nf u ∷ A ×
          Γ ⊢ t ≡ u ∷ A ×
          (γ ▸[ 𝟙ᵐ ] u ⇔ 𝟙 ≤ 𝟘) ×
          ∃ λ v → Γ ⊢nf v ∷ A × Γ ⊢ t ≡ v ∷ A × γ ▸[ 𝟙ᵐ ] v)    →⟨ (λ (⊢u , t≡u , ▸u⇔ , v , ⊢v , t≡v , ▸v) →
                                                                      v ,
                                                                      PE.subst (λ u → _ ▸[ _ ] u ⇔ _)
                                                                        (normal-terms-unique ⊢u ⊢v (trans (sym t≡u) t≡v))
                                                                        ▸u⇔ ,
                                                                      ▸v) ⟩
         (∃ λ v → (ε ∙ 𝟙 ▸[ 𝟙ᵐ ] v ⇔ 𝟙 ≤ 𝟘) × ε ∙ 𝟙 ▸[ 𝟙ᵐ ] v)  →⟨ (λ (_ , ▸v⇔ , ▸v) → ▸v⇔ .proj₁ ▸v) ⟩

         𝟙 ≤ 𝟘                                                  □

       .≡𝟙⊎𝟙≤𝟘 {p = p} {q = q} →
         Σₚ-allowed p q                                                   →⟨ η-long-nf-for-0⇔≡𝟙⊎≡𝟘 ⟩

         (let Γ = ε ∙ (Σₚ p , q ▷ ℕ ▹ ℕ)
              γ = ε ∙ 𝟙
              A = Σₚ p , q ▷ ℕ ▹ ℕ
              t = var x0
              u = prodₚ p (fst p (var x0)) (snd p (var x0))
          in
          Γ ⊢ t ∷ A ×
          γ ▸[ 𝟙ᵐ ] t ×
          Γ ⊢nf u ∷ A ×
          Γ ⊢ t ≡ u ∷ A ×
          (γ ▸[ 𝟙ᵐ ] u ⇔ (p PE.≡ 𝟙 ⊎ p PE.≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘)))   →⟨ (λ (⊢t , ▸t , ⊢u , t≡u , ▸u⇔) →
                                                                               ⊢u , t≡u , ▸u⇔ , red ⊢t ▸t) ⟩
         (let Γ = ε ∙ (Σₚ p , q ▷ ℕ ▹ ℕ)
              γ = ε ∙ 𝟙
              A = Σₚ p , q ▷ ℕ ▹ ℕ
              t = var x0
              u = prodₚ p (fst p (var x0)) (snd p (var x0))
          in
          Γ ⊢nf u ∷ A ×
          Γ ⊢ t ≡ u ∷ A ×
          (γ ▸[ 𝟙ᵐ ] u ⇔ (p PE.≡ 𝟙 ⊎ p PE.≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘)) ×
          ∃ λ v → Γ ⊢nf v ∷ A × Γ ⊢ t ≡ v ∷ A × γ ▸[ 𝟙ᵐ ] v)              →⟨ (λ (⊢u , t≡u , ▸u⇔ , v , ⊢v , t≡v , ▸v) →
                                                                                v ,
                                                                                PE.subst (λ u → _ ▸[ _ ] u ⇔ _)
                                                                                  (normal-terms-unique ⊢u ⊢v (trans (sym t≡u) t≡v))
                                                                                  ▸u⇔ ,
                                                                                ▸v) ⟩
         (∃ λ v →
          (ε ∙ 𝟙 ▸[ 𝟙ᵐ ] v ⇔
           (p PE.≡ 𝟙 ⊎ p PE.≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘)) ×
          ε ∙ 𝟙 ▸[ 𝟙ᵐ ] v)                                                →⟨ (λ (_ , ▸v⇔ , ▸v) → ▸v⇔ .proj₁ ▸v) ⟩

         p PE.≡ 𝟙 ⊎ p PE.≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘                       □)
  , fullRedTerm
  where
  open Full-reduction-assumptions
  open Tools.Reasoning.PartialOrder ≤-poset

------------------------------------------------------------------------
-- Full-reduction-term-ε

-- A variant of Full-reduction-term that is restricted to empty
-- contexts.

Full-reduction-term-ε : Set a
Full-reduction-term-ε =
  ∀ {t A m} →
  ε ⊢ t ∷ A → ε ▸[ m ] t →
  ∃ λ u → ε ⊢nf u ∷ A × ε ⊢ t ≡ u ∷ A × ε ▸[ m ] u

-- If Π-allowed 𝟙 r holds for any r, then Full-reduction-term-ε
-- implies Full-reduction-assumptions.

Full-reduction-term-ε→Full-reduction-assumptions :
  Π-allowed 𝟙 r →
  Full-reduction-term-ε →
  Full-reduction-assumptions
Full-reduction-term-ε→Full-reduction-assumptions
  {r = r} ok red = λ where
    .𝟙≤𝟘 →
      Unit-allowed                                         →⟨ η-long-nf-for-id⇔𝟙≤𝟘 ok ⟩

      (let A = Π 𝟙 , r ▷ Unit ▹ Unit
           t = lam 𝟙 (var x0)
           u = lam 𝟙 star
       in
       ε ⊢ t ∷ A ×
       ε ▸[ 𝟙ᵐ ] t ×
       ε ⊢nf u ∷ A ×
       ε ⊢ t ≡ u ∷ A ×
       (ε ▸[ 𝟙ᵐ ] u ⇔ 𝟙 ≤ 𝟘))                              →⟨ (λ (⊢t , ▸t , ⊢u , t≡u , ▸u⇔) →
                                                                ⊢u , t≡u , ▸u⇔ , red ⊢t ▸t) ⟩
      (let A = Π 𝟙 , r ▷ Unit ▹ Unit
           t = lam 𝟙 (var x0)
           u = lam 𝟙 star
       in
       ε ⊢nf u ∷ A ×
       ε ⊢ t ≡ u ∷ A ×
       (ε ▸[ 𝟙ᵐ ] u ⇔ 𝟙 ≤ 𝟘) ×
       ∃ λ v → ε ⊢nf v ∷ A × ε ⊢ t ≡ v ∷ A × ε ▸[ 𝟙ᵐ ] v)  →⟨ (λ (⊢u , t≡u , ▸u⇔ , v , ⊢v , t≡v , ▸v) →
                                                                 v ,
                                                                 PE.subst (λ u → _ ▸[ _ ] u ⇔ _)
                                                                   (normal-terms-unique ⊢u ⊢v (trans (sym t≡u) t≡v))
                                                                   ▸u⇔ ,
                                                                 ▸v) ⟩
      (∃ λ v → (ε ▸[ 𝟙ᵐ ] v ⇔ 𝟙 ≤ 𝟘) × ε ▸[ 𝟙ᵐ ] v)        →⟨ (λ (_ , ▸v⇔ , ▸v) → ▸v⇔ .proj₁ ▸v) ⟩

      𝟙 ≤ 𝟘                                                □

    .≡𝟙⊎𝟙≤𝟘 {p = p} {q = q} →
      Σₚ-allowed p q                                                  →⟨ η-long-nf-for-id⇔≡𝟙⊎≡𝟘 ok ⟩

      (let A = Π 𝟙 , r ▷ Σₚ p , q ▷ ℕ ▹ ℕ ▹ Σₚ p , q ▷ ℕ ▹ ℕ
           t = lam 𝟙 (var x0)
           u = lam 𝟙 (prodₚ p (fst p (var x0)) (snd p (var x0)))
       in
       ε ⊢ t ∷ A ×
       ε ▸[ 𝟙ᵐ ] t ×
       ε ⊢nf u ∷ A ×
       ε ⊢ t ≡ u ∷ A ×
       (ε ▸[ 𝟙ᵐ ] u ⇔ (p PE.≡ 𝟙 ⊎ p PE.≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘)))  →⟨ (λ (⊢t , ▸t , ⊢u , t≡u , ▸u⇔) →
                                                                           ⊢u , t≡u , ▸u⇔ , red ⊢t ▸t) ⟩
      (let A = Π 𝟙 , r ▷ Σₚ p , q ▷ ℕ ▹ ℕ ▹ Σₚ p , q ▷ ℕ ▹ ℕ
           t = lam 𝟙 (var x0)
           u = lam 𝟙 (prodₚ p (fst p (var x0)) (snd p (var x0)))
       in
       ε ⊢nf u ∷ A ×
       ε ⊢ t ≡ u ∷ A ×
       (ε ▸[ 𝟙ᵐ ] u ⇔ (p PE.≡ 𝟙 ⊎ p PE.≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘)) ×
       ∃ λ v → ε ⊢nf v ∷ A × ε ⊢ t ≡ v ∷ A × ε ▸[ 𝟙ᵐ ] v)             →⟨ (λ (⊢u , t≡u , ▸u⇔ , v , ⊢v , t≡v , ▸v) →
                                                                            v ,
                                                                            PE.subst (λ u → _ ▸[ _ ] u ⇔ _)
                                                                              (normal-terms-unique ⊢u ⊢v (trans (sym t≡u) t≡v))
                                                                              ▸u⇔ ,
                                                                            ▸v) ⟩
      (∃ λ v →
       (ε ▸[ 𝟙ᵐ ] v ⇔ (p PE.≡ 𝟙 ⊎ p PE.≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘)) ×
       ε ▸[ 𝟙ᵐ ] v)                                                   →⟨ (λ (_ , ▸v⇔ , ▸v) → ▸v⇔ .proj₁ ▸v) ⟩

      p PE.≡ 𝟙 ⊎ p PE.≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘                      □
  where
  open Full-reduction-assumptions
  open Tools.Reasoning.PartialOrder ≤-poset

-- If Π-allowed 𝟙 r holds for any r, then Full-reduction-term is
-- logically equivalent to Full-reduction-term-ε.

Full-reduction-term⇔Full-reduction-term-ε :
  Π-allowed 𝟙 r →
  Full-reduction-term ⇔ Full-reduction-term-ε
Full-reduction-term⇔Full-reduction-term-ε ok =
    (λ red → red)
  , (Full-reduction-term-ε       →⟨ Full-reduction-term-ε→Full-reduction-assumptions ok ⟩
     Full-reduction-assumptions  →⟨ fullRedTerm ⟩
     Full-reduction-term         □)
