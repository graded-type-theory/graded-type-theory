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
open import Tools.Nullary
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Sum using (_⊎_; inj₂)
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
open import Definition.Typed.Consequences.Syntactic TR

open import Definition.Conversion TR
open import Definition.Conversion.Consequences.Completeness TR
open import Definition.Conversion.Soundness TR
open import Definition.Conversion.Stability TR
open import Definition.Conversion.Whnf TR

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.FullReduction.Assumptions 𝕄 TR
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
    q : M

-- The lemmas below are proved under the assumption that
-- Full-reduction-assumptions holds.

module _ (as : Full-reduction-assumptions) where

  open Full-reduction-assumptions as

  private

    -- A lemma used in the Unit-ins and η-unit cases of
    -- fullRedTermConv↓.
    --
    -- Note that the Unit-restriction assumption is only used when the
    -- mode is 𝟙ᵐ. Currently the typing relation does not track modes,
    -- but if it did, then it might suffice to require that the
    -- Unit-restriction assumption holds when the mode is 𝟙ᵐ.

    ▸→≤ᶜ𝟘ᶜ :
      ∀ {t : Term n} m →
      Unit-restriction →
      γ ▸[ m ] t → γ ≤ᶜ 𝟘ᶜ
    ▸→≤ᶜ𝟘ᶜ 𝟘ᵐ _  γ▸t = ▸-𝟘ᵐ γ▸t
    ▸→≤ᶜ𝟘ᶜ 𝟙ᵐ ok _   = ≤ᶜ𝟘ᶜ (≤𝟘 ok)

    -- A lemma used in the Σ-η case of fullRedTermConv↓.
    --
    -- Note that the Σₚ-restriction assumption is only used when the
    -- mode is 𝟙ᵐ. Currently the typing relation does not track modes,
    -- but if it did, then it might suffice to require that the
    -- Σₚ-restriction assumptions hold when the mode is 𝟙ᵐ.

    Σ-η-lemma :
      ∀ m →
      Σₚ-restriction p q →
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
      Γ ⊢ t ~ t′ ↑ A → γ ▸[ m ] t →
      ∃ λ u → Γ ⊢ne u ∷ A × Γ ⊢ t ≡ u ∷ A × γ ▸[ m ] u
    fullRedNe {Γ = Γ} = λ where
      (var-refl {x = x} ⊢x _) ▸x →
        case inversion-var ⊢x of λ {
          (_ , x∈ , A≡B) →
          var x
        , convₙ (varₙ (wfEq A≡B) x∈) (sym A≡B)
        , refl ⊢x
        , ▸x }
      (app-cong {G = B} {t = u} t~ u↑) ▸tu →
        case inv-usage-app ▸tu of λ {
          (invUsageApp ▸t ▸u γ≤) →
        case fullRedNe~↓ t~ ▸t of λ {
          (t′ , t′-ne , t≡t′ , ▸t′) →
        case fullRedTermConv↑ u↑ ▸u of λ {
          (u′ , u′-nf , u≡u′ , ▸u′) →
        case inversion-ΠΣ (syntacticEqTerm t≡t′ .proj₁) of λ {
          (_ , ⊢B , _) →
          t′ ∘ u′
        , (                          $⟨ ∘ₙ t′-ne u′-nf ⟩
           Γ ⊢ne t′ ∘ u′ ∷ B [ u′ ]  →⟨ flip convₙ $
                                        substTypeEq (refl ⊢B) (sym u≡u′) ⟩
           Γ ⊢ne t′ ∘ u′ ∷ B [ u ]   □)
        , app-cong t≡t′ u≡u′
        , sub (▸t′ ∘ₘ ▸u′) γ≤ }}}}
      (fst-cong {p = p} t~) ▸fst-t →
        case inv-usage-fst ▸fst-t of λ {
          (invUsageFst m′ PE.refl ▸t γ≤ ok) →
        case fullRedNe~↓ t~ ▸t of λ {
          (t′ , t′-ne , t≡t′ , ▸t′) →
        case inversion-ΠΣ (syntacticEqTerm t≡t′ .proj₁) of λ {
          (⊢A , ⊢B , _) →
          fst p t′
        , fstₙ ⊢A ⊢B t′-ne
        , fst-cong ⊢A ⊢B t≡t′
        , sub (fstₘ m′ ▸t′ PE.refl ok) γ≤ }}}
      (snd-cong {k = t} {p = p} {G = B} t~) ▸snd-t →
        case inv-usage-snd ▸snd-t of λ {
          (invUsageSnd ▸t γ≤) →
        case fullRedNe~↓ t~ ▸t of λ {
          (t′ , t′-ne , t≡t′ , ▸t′) →
        case inversion-ΠΣ (syntacticEqTerm t≡t′ .proj₁) of λ {
          (⊢A , ⊢B , _) →
          snd p t′
        , (                                 $⟨ sndₙ ⊢A ⊢B t′-ne ⟩
           Γ ⊢ne snd p t′ ∷ B [ fst p t′ ]  →⟨ flip _⊢ne_∷_.convₙ $
                                               substTypeEq (refl ⊢B) (fst-cong ⊢A ⊢B (sym t≡t′)) ⟩
           Γ ⊢ne snd p t′ ∷ B [ fst p t ]   □)
        , snd-cong ⊢A ⊢B t≡t′
        , sub (sndₘ ▸t′) γ≤ }}}
      (natrec-cong {F = A} {k = v} {p = p} {q = q} {r = r} A↑ t↑ u↑ v~)
        ▸natrec →
        case inv-usage-natrec ▸natrec of λ {
          (invUsageNatrec ▸t ▸u ▸v ▸A γ≤) →
        case fullRedConv↑ A↑ ▸A of λ {
          (A′ , A′-nf , A≡A′ , ▸A′) →
        case fullRedTermConv↑ t↑ ▸t of λ {
          (t′ , t′-nf , t≡t′ , ▸t′) →
        case fullRedTermConv↑ u↑ ▸u of λ {
          (u′ , u′-nf , u≡u′ , ▸u′) →
        case fullRedNe~↓ v~ ▸v of λ {
          (v′ , v′-ne , v≡v′ , ▸v′) →
        case syntacticEq A≡A′ of λ {
          (⊢A , ⊢A′) →
        case wfEqTerm v≡v′ of λ {
          ⊢Γ →
        case ⊢Γ ∙ ℕⱼ ⊢Γ of λ {
          ⊢Γℕ →
          natrec p q r A′ t′ u′ v′
        , (                                                $⟨ u′-nf ⟩
           Γ ∙ ℕ ∙ A ⊢nf u′ ∷ wk1 (A [ suc (var x0) ]↑)    →⟨ ⊢nf∷-stable (reflConEq ⊢Γℕ ∙ A≡A′) ⟩
           Γ ∙ ℕ ∙ A′ ⊢nf u′ ∷ wk1 (A [ suc (var x0) ]↑)   →⟨ flip _⊢nf_∷_.convₙ $
                                                              wkEq (step id) (⊢Γℕ ∙ ⊢A′) $
                                                              subst↑TypeEq A≡A′ (refl (sucⱼ (var ⊢Γℕ here))) ⟩
           Γ ∙ ℕ ∙ A′ ⊢nf u′ ∷ wk1 (A′ [ suc (var x0) ]↑)  →⟨ (λ hyp → natrecₙ
                                                                 A′-nf
                                                                 (convₙ t′-nf (substTypeEq A≡A′ (refl (zeroⱼ ⊢Γ))))
                                                                 hyp
                                                                 v′-ne) ⟩
           Γ ⊢ne natrec p q r A′ t′ u′ v′ ∷ A′ [ v′ ]      →⟨ flip _⊢ne_∷_.convₙ $ _⊢_≡_.sym $
                                                              substTypeEq A≡A′ v≡v′ ⟩
           Γ ⊢ne natrec p q r A′ t′ u′ v′ ∷ A [ v ]        □)
        , natrec-cong ⊢A A≡A′ t≡t′ u≡u′ v≡v′
        , sub (natrecₘ ▸t′ ▸u′ ▸v′ ▸A′) γ≤ }}}}}}}}
      (prodrec-cong
         {p = p} {F = A} {G = B} {C = C} {g = u} {r = r} {q′ = q}
         C↑ u~ v↑)
        ▸prodrec →
        case inv-usage-prodrec ▸prodrec of λ {
          (invUsageProdrec ▸u ▸v ▸C ok₁ γ≤) →
        case fullRedConv↑ C↑ ▸C of λ {
          (C′ , C′-nf , C≡C′ , ▸C′) →
        case fullRedNe~↓ u~ ▸u of λ {
          (u′ , u′-ne , u≡u′ , ▸u′) →
        case fullRedTermConv↑ v↑ ▸v of λ {
          (v′ , v′-nf , v≡v′ , ▸v′) →
        case inversion-ΠΣ (syntacticEqTerm u≡u′ .proj₁) of λ {
          (⊢A , ⊢B , ok₂) →
          prodrec r p q C′ u′ v′
        , (                                                       $⟨ v′-nf ⟩
           Γ ∙ A ∙ B ⊢nf v′ ∷ C [ prodᵣ p (var x1) (var x0) ]↑²   →⟨ flip _⊢nf_∷_.convₙ $
                                                                     subst↑²TypeEq C≡C′ ok₂ ⟩
           Γ ∙ A ∙ B ⊢nf v′ ∷ C′ [ prodᵣ p (var x1) (var x0) ]↑²  →⟨ flip (prodrecₙ ⊢A ⊢B C′-nf u′-ne) ok₂ ⟩
           Γ ⊢ne prodrec r p q C′ u′ v′ ∷ C′ [ u′ ]               →⟨ flip _⊢ne_∷_.convₙ $ _⊢_≡_.sym $
                                                                     substTypeEq C≡C′ u≡u′ ⟩
           Γ ⊢ne prodrec r p q C′ u′ v′ ∷ C [ u ]                 □)
        , prodrec-cong ⊢A ⊢B C≡C′ u≡u′ v≡v′ ok₂
        , sub (prodrecₘ ▸u′ ▸v′ ▸C′ ok₁) γ≤ }}}}}
      (Emptyrec-cong {F = A} {p = p} A↑ t~) ▸Emptyrec →
        case inv-usage-Emptyrec ▸Emptyrec of λ {
          (invUsageEmptyrec ▸t ▸A γ≤) →
        case fullRedConv↑ A↑ ▸A of λ {
          (A′ , A′-nf , A≡A′ , ▸A′) →
        case fullRedNe~↓ t~ ▸t of λ {
          (t′ , t′-ne , t≡t′ , ▸t′) →
          Emptyrec p A′ t′
        , (                             $⟨ Emptyrecₙ A′-nf t′-ne ⟩
           Γ ⊢ne Emptyrec p A′ t′ ∷ A′  →⟨ flip _⊢ne_∷_.convₙ (sym A≡A′) ⟩
           Γ ⊢ne Emptyrec p A′ t′ ∷ A   □)
        , Emptyrec-cong A≡A′ t≡t′
        , sub (Emptyrecₘ ▸t′ ▸A′) γ≤ }}}

    fullRedNe~↓ :
      Γ ⊢ t ~ t′ ↓ A → γ ▸[ m ] t →
      ∃ λ u → Γ ⊢ne u ∷ A × Γ ⊢ t ≡ u ∷ A × γ ▸[ m ] u
    fullRedNe~↓ ([~] A D whnfB k~l) γ▸t =
      let u , A-ne , t≡u , γ▸u = fullRedNe k~l γ▸t
      in  u , convₙ A-ne A≡ , conv t≡u A≡ , γ▸u
      where
      A≡ = subset* D

    fullRedConv↑ :
      Γ ⊢ A [conv↑] A′ → γ ▸[ m ] A →
      ∃ λ B → Γ ⊢nf B × Γ ⊢ A ≡ B × γ ▸[ m ] B
    fullRedConv↑ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) γ▸A =
      let γ▸A′ = usagePres* γ▸A D
          B″ , nf , B′≡B″ , γ▸B″ = fullRedConv↓ A′<>B′ γ▸A′
      in  B″ , nf , trans (subset* D) B′≡B″ , γ▸B″

    fullRedConv↓ :
      Γ ⊢ A [conv↓] A′ → γ ▸[ m ] A →
      ∃ λ B → Γ ⊢nf B × Γ ⊢ A ≡ B × γ ▸[ m ] B
    fullRedConv↓ = λ where
      (U-refl     ⊢Γ)    ▸U → U     , Uₙ     ⊢Γ , refl (Uⱼ     ⊢Γ) , ▸U
      (ℕ-refl     ⊢Γ)    ▸ℕ → ℕ     , ℕₙ     ⊢Γ , refl (ℕⱼ     ⊢Γ) , ▸ℕ
      (Empty-refl ⊢Γ)    ▸⊥ → Empty , Emptyₙ ⊢Γ , refl (Emptyⱼ ⊢Γ) , ▸⊥
      (Unit-refl  ⊢Γ ok) ▸⊤ →
        Unit , Unitₙ ⊢Γ ok , refl (Unitⱼ ⊢Γ ok) , ▸⊤
      (ne A~)           ▸A →
        case fullRedNe~↓ A~ ▸A of λ {
          (B , B-ne , A≡B , ▸B) →
        B , univₙ (neₙ Uₙ B-ne) , univ A≡B , ▸B }
      (ΠΣ-cong ⊢A A↑ B↑ ok) ▸ΠΣAB →
        case inv-usage-ΠΣ ▸ΠΣAB of λ {
          (invUsageΠΣ ▸A ▸B γ≤) →
        case fullRedConv↑ A↑ ▸A of λ {
          (A′ , A′-nf , A≡A′ , ▸A′) →
        case fullRedConv↑ B↑ ▸B of λ {
          (B′ , B′-nf , B≡B′ , ▸B′) →
        ΠΣ⟨ _ ⟩ _ , _ ▷ A′ ▹ B′ ,
        ΠΣₙ A′-nf (⊢nf-stable (reflConEq (wfEq A≡A′) ∙ A≡A′) B′-nf) ok ,
        ΠΣ-cong ⊢A A≡A′ B≡B′ ok ,
        sub (ΠΣₘ ▸A′ ▸B′) γ≤ }}}

    fullRedTermConv↑ :
      Γ ⊢ t [conv↑] t′ ∷ A → γ ▸[ m ] t →
      ∃ λ u → Γ ⊢nf u ∷ A × Γ ⊢ t ≡ u ∷ A × γ ▸[ m ] u
    fullRedTermConv↑
      ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) γ▸t =
      case fullRedTermConv↓ t<>u (usagePres*Term γ▸t d) of λ {
        (u″ , nf , u′≡u″ , γ▸u″) →
      u″ ,
      convₙ nf B≡A ,
      conv (trans (subset*Term d) u′≡u″) B≡A ,
      γ▸u″ }
      where
      B≡A = sym (subset* D)

    fullRedTermConv↓ :
      Γ ⊢ t [conv↓] t′ ∷ A → γ ▸[ m ] t →
      ∃ λ u → Γ ⊢nf u ∷ A × Γ ⊢ t ≡ u ∷ A × γ ▸[ m ] u
    fullRedTermConv↓ {Γ = Γ} {t = t} {γ = γ} {m = m} = λ where
      (ℕ-ins t~) ▸t →
        case fullRedNe~↓ t~ ▸t of λ {
          (u , u-nf , t≡u , ▸u) →
        u , neₙ ℕₙ u-nf , t≡u , ▸u }
      (Empty-ins t~) ▸t →
        case fullRedNe~↓ t~ ▸t of λ {
          (u , u-nf , t≡u , ▸u) →
        u , neₙ Emptyₙ u-nf , t≡u , ▸u }
      (Unit-ins t~) ▸t →
        case syntacticEqTerm (soundness~↓ t~) of λ {
          (Γ⊢ , ⊢t , _) →
        case wf Γ⊢ of λ {
          ⊢Γ →
        case ⊢∷Unit→Unit-restriction ⊢t of λ {
          ok →
          star
        , starₙ ⊢Γ ok
        , η-unit ⊢t (starⱼ ⊢Γ ok)
        , sub starₘ (▸→≤ᶜ𝟘ᶜ _ ok ▸t) }}}
      (Σᵣ-ins ⊢t∷ΣAB _ t~) ▸t →
        case fullRedNe~↓ t~ ▸t of λ {
          (v , v-ne , t≡v , ▸v) →
        case syntacticEqTerm t≡v of λ {
          (_ , ⊢t∷ΣCD , _) →
        case ne~↓ t~ of λ {
          (_ , t-ne , _) →
        case neTypeEq t-ne ⊢t∷ΣCD ⊢t∷ΣAB of λ {
          ΣCD≡ΣAB →
        case inversion-ΠΣ (syntacticTerm ⊢t∷ΣAB) of λ {
          (⊢A , ⊢B) →
          v
        , neₙ Σᵣₙ (convₙ v-ne ΣCD≡ΣAB)
        , conv t≡v ΣCD≡ΣAB
        , ▸v }}}}}
      (ne-ins ⊢t∷A _ A-ne t~↓B) ▸t →
        case fullRedNe~↓ t~↓B ▸t of λ {
          (u , u-ne , t≡u∷B , ▸u) →
        case syntacticEqTerm t≡u∷B of λ {
          (_ , ⊢t∷B , _) →
        case ne~↓ t~↓B of λ {
          (_ , t-ne , _) →
        case neTypeEq t-ne ⊢t∷B ⊢t∷A of λ {
          B≡A →
          u
        , neₙ (neₙ A-ne) (convₙ u-ne B≡A)
        , conv t≡u∷B B≡A
        , ▸u }}}}
      (univ {A = A} ⊢A _ A↓) ▸A →
        case fullRedConv↓ A↓ ▸A of λ {
          (B , B-nf , A≡B , ▸B) →
          B
        , (               $⟨ A≡B ⟩
           (Γ ⊢ A ≡ B)    →⟨ inverseUnivEq ⊢A ⟩
           Γ ⊢ A ≡ B ∷ U  →⟨ (λ hyp → syntacticEqTerm hyp .proj₂ .proj₂) ⟩
           Γ ⊢ B ∷ U      →⟨ ⊢nf∷U→⊢nf∷U B-nf ⟩
           Γ ⊢nf B ∷ U    □)
        , inverseUnivEq ⊢A A≡B
        , ▸B }
      (zero-refl ⊢Γ) ▸zero →
        zero , zeroₙ ⊢Γ , refl (zeroⱼ ⊢Γ) , ▸zero
      (suc-cong t↑) ▸suc-t →
        case inv-usage-suc ▸suc-t of λ {
          (invUsageSuc ▸t γ≤) →
        case fullRedTermConv↑ t↑ ▸t of λ {
          (u , u-nf , t≡u , ▸u) →
        suc u , sucₙ u-nf , suc-cong t≡u , sub (sucₘ ▸u) γ≤ }}
      (prod-cong {p = p} {q = q} {F = A} {G = B} {t = t} ⊢A ⊢B t↑ u↑ ok)
        ▸t,u →
        case inv-usage-prodᵣ ▸t,u of λ {
          (invUsageProdᵣ ▸t ▸u γ≤) →
        case fullRedTermConv↑ t↑ ▸t of λ {
          (t′ , t′-nf , t≡t′ , ▸t′) →
        case fullRedTermConv↑ u↑ ▸u of λ {
          (u′ , u′-nf , u≡u′ , ▸u′) →
          prod! t′ u′
        , (                                      $⟨ u′-nf ⟩
           Γ ⊢nf u′ ∷ B [ t ]                    →⟨ flip _⊢nf_∷_.convₙ $
                                                    substTypeEq (refl ⊢B) t≡t′ ⟩
           Γ ⊢nf u′ ∷ B [ t′ ]                   →⟨ flip (_⊢nf_∷_.prodₙ ⊢A ⊢B t′-nf) ok ⟩
           Γ ⊢nf prod! t′ u′ ∷ Σᵣ p , q ▷ A ▹ B  □)
        , prod-cong ⊢A ⊢B t≡t′ u≡u′ ok
        , sub (prodᵣₘ ▸t′ ▸u′) γ≤ }}}
      (η-eq {p = p} {q = q} {f = t} {F = A} {G = B} ⊢t _ _ _ t0≡u0) ▸t →
        case fullRedTermConv↑ t0≡u0 (wkUsage (step id) ▸t ∘ₘ var) of λ {
          (u , u-nf , t0≡u , ▸u) →
        case ⊢∷ΠΣ→ΠΣ-restriction ⊢t of λ {
          ok →
          lam p u
        , lamₙ (inversion-ΠΣ (syntacticTerm ⊢t) .proj₁) u-nf ok
        , (                                                       $⟨ sym (Π-η ⊢t) ⟩
           Γ ⊢ t ≡ lam p (wk1 t ∘⟨ p ⟩ var x0) ∷ Π p , q ▷ A ▹ B  →⟨ flip _⊢_≡_∷_.trans (lam-cong t0≡u ok) ⟩
           Γ ⊢ t ≡ lam p u ∷ Π p , q ▷ A ▹ B                      □)
        , (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
           lamₘ $ sub ▸u $ begin
             γ ∙ ⌜ m ⌝ · p                      ≈⟨ ≈ᶜ-refl ∙ ⌜⌝-·-comm m ⟩
             γ ∙ p · ⌜ m ⌝                      ≈˘⟨ +ᶜ-identityʳ _ ∙ ·⌜ᵐ·⌝ m ⟩
             γ +ᶜ 𝟘ᶜ ∙ p · ⌜ m ᵐ· p ⌝           ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _) ∙ +-identityˡ _ ⟩
             γ +ᶜ p ·ᶜ 𝟘ᶜ ∙ 𝟘 + p · ⌜ m ᵐ· p ⌝  ∎) }}
      (Σ-η {p = p} {q = q} {F = A} {G = B} ⊢t _ _ _ fst-t↑ snd-t↑) ▸t →
        case inversion-ΠΣ (syntacticTerm ⊢t) of λ {
          (⊢A , ⊢B , ok) →
        case Σ-η-lemma m ok ▸t of λ {
          (δ , ▸fst-t , γ≤) →
        case fullRedTermConv↑ fst-t↑ ▸fst-t of λ {
          (u₁ , u₁-nf , fst-t≡u₁ , ▸u₁) →
        case fullRedTermConv↑ snd-t↑ (sndₘ ▸t) of λ {
          (u₂ , u₂-nf , snd-t≡u₂ , ▸u₂) →
          prodₚ p u₁ u₂
        , (                                        $⟨ u₂-nf ⟩
           Γ ⊢nf u₂ ∷ B [ fst p t ]                →⟨ flip _⊢nf_∷_.convₙ $
                                                      substTypeEq (refl ⊢B) fst-t≡u₁ ⟩
           Γ ⊢nf u₂ ∷ B [ u₁ ]                     →⟨ flip (prodₙ ⊢A ⊢B u₁-nf) ok ⟩
           Γ ⊢nf prodₚ p u₁ u₂ ∷ Σₚ p , q ▷ A ▹ B  □)
        , (                                                        $⟨ sym (Σ-η-prod-fst-snd ⊢t) ⟩
           Γ ⊢ t ≡ prodₚ p (fst p t) (snd p t) ∷ Σₚ p , q ▷ A ▹ B  →⟨ flip _⊢_≡_∷_.trans $
                                                                      prod-cong ⊢A ⊢B fst-t≡u₁ snd-t≡u₂ ok ⟩
           Γ ⊢ t ≡ prodₚ p u₁ u₂ ∷ Σₚ p , q ▷ A ▹ B                □)
        , (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
           sub (prodₚₘ ▸u₁ ▸u₂) $ begin
             γ            ≤⟨ ∧ᶜ-greatest-lower-bound γ≤ ≤ᶜ-refl ⟩
             p ·ᶜ δ ∧ᶜ γ  ∎) }}}}
      (η-unit ⊢t _ _ _) ▸t →
        case wfTerm ⊢t of λ {
          ⊢Γ →
        case ⊢∷Unit→Unit-restriction ⊢t of λ {
          ok →
          star
        , starₙ ⊢Γ ok
        , η-unit ⊢t (starⱼ ⊢Γ ok)
        , sub starₘ (▸→≤ᶜ𝟘ᶜ _ ok ▸t) }}

-- If a type is well-formed and well-resourced, then it is
-- definitionally equal to a well-resourced type in η-long normal
-- form (given certain assumptions).

fullRed :
  Full-reduction-assumptions →
  Γ ⊢ A → γ ▸[ m ] A →
  ∃ λ B → Γ ⊢nf B × Γ ⊢ A ≡ B × γ ▸[ m ] B
fullRed as ⊢A = fullRedConv↑ as (completeEq (refl ⊢A))

-- If a term is well-formed and well-resourced, then it is
-- definitionally equal to a well-resourced term in η-long normal
-- form (given certain assumptions).

fullRedTerm :
  Full-reduction-assumptions →
  Γ ⊢ t ∷ A → γ ▸[ m ] t →
  ∃ λ u → Γ ⊢nf u ∷ A × Γ ⊢ t ≡ u ∷ A × γ ▸[ m ] u
fullRedTerm as ⊢t = fullRedTermConv↑ as (completeEqTerm (refl ⊢t))
