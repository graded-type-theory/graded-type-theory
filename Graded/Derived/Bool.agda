------------------------------------------------------------------------
-- Some properties related to usage and Bool
------------------------------------------------------------------------

open import Definition.Untyped.NotParametrised using (Strength)
import Graded.Modality
import Graded.Modality.Dedicated-nr
open import Graded.Usage.Restrictions

module Graded.Derived.Bool
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (open Graded.Modality.Dedicated-nr 𝕄)
  (R : Usage-restrictions 𝕄)
  -- One can define the booleans using either weak or strong Σ and
  -- unit types.
  {s : Strength}
  -- It is assumed that there is a dedicated nr function.
  ⦃ has-nr : Dedicated-nr ⦄
  where

open Modality 𝕄
open Usage-restrictions R

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Derived.Nat 𝕄 R
open import Graded.Derived.Sigma 𝕄 R
open import Graded.Derived.Unit R
open import Graded.Modality.Dedicated-nr.Instance
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄
open import Graded.Substitution.Properties 𝕄 R
open import Graded.Usage 𝕄 R
open import Graded.Usage.Properties 𝕄 R
open import Graded.Usage.Weakening 𝕄 R

open import Definition.Untyped M
open import Definition.Untyped.Bool 𝕄 s
open import Definition.Untyped.Unit 𝕄

open import Tools.Bool using (T)
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+; 2+)
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation

private variable
  k n           : Nat
  A t u v       : Term _
  γ γ₁ γ₂ γ₃ γ₄ : Conₘ _
  p p′ q r      : M
  m             : Mode

private opaque

  -- Some lemmas used below.

  ≡nr-⌜⌝-𝟘-𝟘 : ∀ m → ⌜ m ⌝ · nr p q 𝟙 𝟘 𝟘 PE.≡ nr p q ⌜ m ⌝ 𝟘 𝟘
  ≡nr-⌜⌝-𝟘-𝟘 {p} {q} = λ where
      𝟘ᵐ →
        𝟘 · nr p q 𝟙 𝟘 𝟘  ≡⟨ ·-zeroˡ _ ⟩
        𝟘                 ≡˘⟨ nr-𝟘 ⟩
        nr p q 𝟘 𝟘 𝟘      ∎
      𝟙ᵐ →
        𝟙 · nr p q 𝟙 𝟘 𝟘  ≡⟨ ·-identityˡ _ ⟩
        nr p q 𝟙 𝟘 𝟘      ∎
    where
    open Tools.Reasoning.PropositionalEquality

  ≡nr-𝟘-𝟘-⌜⌝ : ∀ m → ⌜ m ⌝ · nr p q 𝟘 𝟘 𝟙 PE.≡ nr p q 𝟘 𝟘 ⌜ m ⌝
  ≡nr-𝟘-𝟘-⌜⌝ {p} {q} = λ where
      𝟘ᵐ →
        𝟘 · nr p q 𝟘 𝟘 𝟙  ≡⟨ ·-zeroˡ _ ⟩
        𝟘                 ≡˘⟨ nr-𝟘 ⟩
        nr p q 𝟘 𝟘 𝟘      ∎
      𝟙ᵐ →
        𝟙 · nr p q 𝟘 𝟘 𝟙  ≡⟨ ·-identityˡ _ ⟩
        nr p q 𝟘 𝟘 𝟙      ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding OK OKᵍ

  -- A usage lemma for OK.

  ▸OK :
    γ ▸[ m ] t →
    nrᶜ OKᵍ 𝟘 𝟘ᶜ 𝟘ᶜ γ ▸[ m ] OK t
  ▸OK {m} ▸t =
    ▸natcase Unitₘ
      (sub
         (▸natcase Unitₘ
            (sub Emptyₘ $ begin
               𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
               𝟘ᶜ              ∎)
            var
            (sub Uₘ $ begin
               𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
               𝟘ᶜ                ∎))
         (begin
            𝟘ᶜ ∙ ⌜ m ⌝ · nr 𝟘 𝟘 𝟘 𝟘 𝟙   ≈⟨ ≈ᶜ-refl ∙ ≡nr-𝟘-𝟘-⌜⌝ m ⟩
            𝟘ᶜ ∙ nr 𝟘 𝟘 𝟘 𝟘 ⌜ m ⌝       ≈˘⟨ nrᶜ-𝟘ᶜ ∙ PE.refl ⟩
            nrᶜ 𝟘 𝟘 𝟘ᶜ 𝟘ᶜ (𝟘ᶜ ∙ ⌜ m ⌝)  ∎))
      ▸t
      (sub Uₘ $ begin
         𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
         𝟘ᶜ                ∎)
    where
    open ≤ᶜ-reasoning

opaque
  unfolding Bool Boolᵍ

  -- A usage lemma for Bool.

  ▸Bool : 𝟘ᶜ ▸[ m ] Bool {n = n}
  ▸Bool {m} = sub
    (ΠΣₘ ℕₘ $
     sub (▸OK var) $ begin
       𝟘ᶜ ∙ ⌜ m ⌝ · nr OKᵍ 𝟘 𝟘 𝟘 𝟙   ≈⟨ ≈ᶜ-refl ∙ ≡nr-𝟘-𝟘-⌜⌝ m ⟩
       𝟘ᶜ ∙ nr OKᵍ 𝟘 𝟘 𝟘 ⌜ m ⌝       ≈˘⟨ nrᶜ-𝟘ᶜ ∙ PE.refl ⟩
       nrᶜ OKᵍ 𝟘 𝟘ᶜ 𝟘ᶜ (𝟘ᶜ ∙ ⌜ m ⌝)  ∎)
    (begin
       𝟘ᶜ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
       𝟘ᶜ +ᶜ 𝟘ᶜ  ∎)
    where
    open ≤ᶜ-reasoning

opaque
  unfolding true

  -- A usage lemma for true.

  ▸true : 𝟘ᶜ ▸[ m ] true {n = n}
  ▸true {m} =
    prodₘ (sucₘ zeroₘ) starₘ
      (λ _ → begin
         𝟘ᶜ             ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
         𝟙 ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
         𝟙 ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎)
      (λ _ → begin
         𝟘ᶜ             ≈˘⟨ ∧ᶜ-idem _ ⟩
         𝟘ᶜ ∧ᶜ 𝟘ᶜ       ≈˘⟨ ∧ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
         𝟙 ·ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ  ∎)
    where
    open ≤ᶜ-reasoning

opaque
  unfolding false

  -- A usage lemma for false.

  ▸false : 𝟘ᶜ ▸[ m ] false {n = n}
  ▸false {m} =
    prodₘ zeroₘ starₘ
      (λ _ → begin
         𝟘ᶜ             ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
         𝟙 ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
         𝟙 ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎)
      (λ _ → begin
         𝟘ᶜ             ≈˘⟨ ∧ᶜ-idem _ ⟩
         𝟘ᶜ ∧ᶜ 𝟘ᶜ       ≈˘⟨ ∧ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
         𝟙 ·ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ  ∎)
    where
    open ≤ᶜ-reasoning

opaque
  unfolding Target

  -- A usage lemma for Target.

  ▸Target :
    (s PE.≡ 𝕨 → ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ₄ ≤ᶜ γ₂ +ᶜ γ₃) →
    (s PE.≡ 𝕤 → ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ₄ ≤ᶜ γ₂ ∧ᶜ γ₃) →
    γ₁ ∙ p ▸[ m ] A →
    γ₂ ▸[ ⌞ p ⌟ ] t →
    γ₃ ▸[ ⌞ p ⌟ ] u →
    wkConₘ (stepn id k) γ₁ +ᶜ p ·ᶜ γ₄ ▸[ m ] Target k A t u
  ▸Target {p} {γ₄} {γ₂} {γ₃} ≤+ ≤∧ ▸A ▸t ▸u =
    ▸[][]↑ ▸A $
    prodₘ (▸-cong (PE.sym ᵐ·-identityʳ) ▸t) ▸u
      (λ s≡𝕨 → begin
         ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ₄  ≤⟨ ≤+ s≡𝕨 ⟩
         γ₂ +ᶜ γ₃         ≈˘⟨ +ᶜ-congʳ (·ᶜ-identityˡ _) ⟩
         𝟙 ·ᶜ γ₂ +ᶜ γ₃    ∎)
      (λ s≡𝕤 → begin
         ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ₄  ≤⟨ ≤∧ s≡𝕤 ⟩
         γ₂ ∧ᶜ γ₃         ≈˘⟨ ∧ᶜ-congʳ (·ᶜ-identityˡ _) ⟩
         𝟙 ·ᶜ γ₂ ∧ᶜ γ₃    ∎)
    where
    open ≤ᶜ-reasoning

opaque
  unfolding boolrec boolrecᵍ-Π boolrecᵍ-nc₁ boolrecᵍ-nc₂ boolrecᵍ-pr

  -- A usage lemma for boolrec.

  ▸boolrec :
    (s PE.≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → 𝟙 ≤ 𝟘) →
    (s PE.≡ 𝕤 → r ≤ ⌜ m ⌝ · boolrecᵍ-pr · (𝟙 + 𝟙)) →
    (s PE.≡ 𝕨 → r ≤ boolrecᵍ-pr) →
    (s PE.≡ 𝕨 → Prodrec-allowed m boolrecᵍ-pr 𝟙 p) →
    (s PE.≡ 𝕨 → Unitrec-allowed m boolrecᵍ-Π p) →
    Emptyrec-allowed m boolrecᵍ-er →
    γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · p ▸[ 𝟘ᵐ? ] A →
    γ₂ ▸[ m ] t →
    γ₃ ▸[ m ] u →
    γ₄ ▸[ m ] v →
    nrᶜ boolrecᵍ-nc₂ 𝟘 γ₃ (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ 𝟘ᶜ 𝟘ᶜ) 𝟘ᶜ +ᶜ r ·ᶜ γ₄
      ▸[ m ] boolrec p A t u v
  ▸boolrec
    {r} {m} {p} {γ₁} {A} {γ₂} {γ₃} {γ₄}
    𝟙≤𝟘 hyp₁ hyp₂ ok₁ ok₂ ok₃ ▸A ▸t ▸u ▸v = sub
    (▸prodrec⟨⟩ (λ _ _ → ≤-refl) hyp₁ hyp₂ ok₁ (λ _ → γ₁ , ▸A)
       (▸-cong
          (PE.sym $ ≢𝟘→ᵐ·≡′ λ ok →
           boolrecᵍ-pr≢𝟘 ⦃ 𝟘-well-behaved = 𝟘-well-behaved ok ⦄)
          ▸v)
       (sub
          (▸natcase (unitrec-lemma zeroₘ ▸u)
             (sub
                (▸natcase (unitrec-lemma (sucₘ zeroₘ) ▸t)
                   (lamₘ $
                    sub
                      (emptyrecₘ (▸strict-const Emptyₘ var var)
                         (Target-lemma (sucₘ (sucₘ var))) ok₃)
                      (begin
                         𝟘ᶜ ∙ ⌜ m ⌝ · boolrecᵍ-nc₁ ∙ ⌜ m ⌝ · boolrecᵍ-Π   ≡⟨⟩

                         𝟘ᶜ ∙ ⌜ m ⌝ · nr 𝟘 𝟙 𝟘 𝟘 boolrecᵍ-er ∙
                         ⌜ m ⌝ · nr 𝟘 𝟙 boolrecᵍ-er 𝟘 𝟘                   ≈⟨ ≈ᶜ-refl ∙ ⌜⌝·nr≡₂ m ∙ ⌜⌝·nr≡₁ m ⟩


                         𝟘ᶜ ∙
                         boolrecᵍ-er · nr 𝟘 𝟙 𝟘 𝟘 ⌜ m ᵐ· boolrecᵍ-er ⌝ ∙
                         boolrecᵍ-er · nr 𝟘 𝟙 ⌜ m ᵐ· boolrecᵍ-er ⌝ 𝟘 𝟘    ≈˘⟨ ≈ᶜ-trans (·ᶜ-congˡ nrᶜ-𝟘ᶜ) (·ᶜ-zeroʳ _) ∙ PE.refl ∙ PE.refl ⟩

                         boolrecᵍ-er ·ᶜ
                         nrᶜ 𝟘 𝟙 (𝟘ᶜ ∙ ⌜ m ᵐ· boolrecᵍ-er ⌝) 𝟘ᶜ
                           (𝟘ᶜ ∙ ⌜ m ᵐ· boolrecᵍ-er ⌝ ∙ 𝟘)                ∎))
                   var (Π-lemma (sucₘ var) (sucₘ var)))
                (begin
                   wkConₘ (stepn id 2) (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ 𝟘ᶜ 𝟘ᶜ) ∙
                   ⌜ m ⌝ · boolrecᵍ-nc₂                                 ≡⟨⟩

                   wkConₘ (stepn id 2) (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ 𝟘ᶜ 𝟘ᶜ) ∙
                   ⌜ m ⌝ · nr boolrecᵍ-nc₁ 𝟘 𝟘 𝟘 𝟙                      ≈⟨ wk-nrᶜ (stepn id 2) ∙ ≡nr-𝟘-𝟘-⌜⌝ m ⟩

                   nrᶜ boolrecᵍ-nc₁ 𝟘 (wkConₘ (stepn id 2) γ₂)
                     (wkConₘ (stepn id 2) 𝟘ᶜ)
                     (wkConₘ (stepn id 2) 𝟘ᶜ) ∙
                   nr boolrecᵍ-nc₁ 𝟘 𝟘 𝟘 ⌜ m ⌝                          ≡⟨⟩

                   nrᶜ boolrecᵍ-nc₁ 𝟘 (wkConₘ (stepn id 3) γ₂) 𝟘ᶜ
                     (𝟘ᶜ ∙ ⌜ m ⌝)                                       ∎))
             var (Π-lemma var var) ∘ₘ
           var)
          (begin
             nrᶜ boolrecᵍ-nc₂ 𝟘 γ₃ (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ 𝟘ᶜ 𝟘ᶜ) 𝟘ᶜ ∙
             ⌜ m ⌝ · boolrecᵍ-pr · 𝟙 ∙ ⌜ m ⌝ · boolrecᵍ-pr               ≈⟨ ≈ᶜ-refl ∙ PE.cong (_·_ _) (·-identityʳ _) ∙ PE.refl ⟩

             nrᶜ boolrecᵍ-nc₂ 𝟘 γ₃ (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ 𝟘ᶜ 𝟘ᶜ) 𝟘ᶜ ∙
             ⌜ m ⌝ · (nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 𝟙 ∧ boolrecᵍ-Π) ∙
             ⌜ m ⌝ · (nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 𝟙 ∧ boolrecᵍ-Π)              ≤⟨ ≤ᶜ-refl ∙ ·-monotoneʳ (∧-decreasingˡ _ _) ∙
                                                                         ·-monotoneʳ (∧-decreasingʳ _ _) ⟩
             nrᶜ boolrecᵍ-nc₂ 𝟘 γ₃ (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ 𝟘ᶜ 𝟘ᶜ) 𝟘ᶜ ∙
             ⌜ m ⌝ · nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 𝟙 ∙ ⌜ m ⌝ · boolrecᵍ-Π        ≈⟨ ≈ᶜ-refl ∙ ⌜⌝-·-comm m ⟩

             nrᶜ boolrecᵍ-nc₂ 𝟘 γ₃ (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ 𝟘ᶜ 𝟘ᶜ) 𝟘ᶜ ∙
             ⌜ m ⌝ · nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 𝟙 ∙ boolrecᵍ-Π · ⌜ m ⌝        ≈⟨ ≈ᶜ-refl ∙ ≡nr-𝟘-𝟘-⌜⌝ m ∙ PE.sym (+-identityˡ _) ⟩

             nrᶜ boolrecᵍ-nc₂ 𝟘 γ₃ (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ 𝟘ᶜ 𝟘ᶜ) 𝟘ᶜ ∙
             nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 ⌜ m ⌝ ∙ 𝟘 + boolrecᵍ-Π · ⌜ m ⌝        ≈˘⟨ +ᶜ-identityʳ _ ∙ PE.cong (flip _+_ _) nr-𝟘 ⟩

             (nrᶜ boolrecᵍ-nc₂ 𝟘 γ₃ (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ 𝟘ᶜ 𝟘ᶜ) 𝟘ᶜ ∙
              nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 ⌜ m ⌝ ∙ nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 𝟘) +ᶜ
             (𝟘ᶜ ∙ boolrecᵍ-Π · ⌜ m ⌝)                                   ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _ ∙ ·⌜ᵐ·⌝ m) ⟩

             nrᶜ boolrecᵍ-nc₂ 𝟘 (wkConₘ (stepn id 2) γ₃)
               (wkConₘ (stepn id 2) (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ 𝟘ᶜ 𝟘ᶜ))
               (𝟘ᶜ ∙ ⌜ m ⌝ ∙ 𝟘) +ᶜ
             boolrecᵍ-Π ·ᶜ (𝟘ᶜ ∙ ⌜ m ᵐ· boolrecᵍ-Π ⌝)                    ∎)))
    (begin
       nrᶜ boolrecᵍ-nc₂ 𝟘 γ₃ (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ 𝟘ᶜ 𝟘ᶜ) 𝟘ᶜ +ᶜ r ·ᶜ γ₄  ≈⟨ +ᶜ-comm _ _ ⟩
       r ·ᶜ γ₄ +ᶜ nrᶜ boolrecᵍ-nc₂ 𝟘 γ₃ (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ 𝟘ᶜ 𝟘ᶜ) 𝟘ᶜ  ∎)
    where
    ≤𝟘∧ :
      s PE.≡ 𝕤 →
      ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝ ≤ 𝟘 ∧ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝
    ≤𝟘∧ s≡𝕤 = ∧-greatest-lower-bound ≤𝟘 ≤-refl
      where
      open Tools.Reasoning.PartialOrder ≤-poset

      ≤𝟘 : ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝ ≤ 𝟘
      ≤𝟘 = 𝟘ᵐ?-elim (λ m → ⌜ ⌞ ⌜ m ⌝ · p ⌟ ⌝ ≤ 𝟘)
        (λ ⦃ ok ⦄ →
           begin
             ⌜ ⌞ 𝟘 · p ⌟ ⌝  ≡⟨ PE.cong (λ p → ⌜ ⌞ p ⌟ ⌝) $ ·-zeroˡ _ ⟩
             ⌜ ⌞ 𝟘 ⌟ ⌝      ≡⟨ PE.cong ⌜_⌝ (⌞𝟘⌟ {ok = ok}) ⟩
             ⌜ 𝟘ᵐ[ ok ] ⌝   ≡⟨⟩
             𝟘              ∎)
        (λ not-ok → begin
           ⌜ ⌞ 𝟙 · p ⌟ ⌝  ≡⟨ PE.cong ⌜_⌝ $ only-𝟙ᵐ-without-𝟘ᵐ {m = ⌞ _ ⌟} not-ok ⟩
           ⌜ 𝟙ᵐ ⌝         ≡⟨⟩
           𝟙              ≤⟨ 𝟙≤𝟘 s≡𝕤 not-ok ⟩
           𝟘              ∎)

    opaque
      unfolding boolrecᵍ-er

      ⌜⌝·nr≡₁ :
        ∀ m →
        ⌜ m ⌝ · nr p′ q boolrecᵍ-er 𝟘 𝟘 PE.≡
        boolrecᵍ-er · nr p′ q ⌜ m ᵐ· boolrecᵍ-er ⌝ 𝟘 𝟘
      ⌜⌝·nr≡₁ {p′} {q} m =
        case PE.singleton s of λ where
          (𝕨 , PE.refl) →
            ⌜ m ⌝ · nr p′ q 𝟙 𝟘 𝟘       ≡⟨ ≡nr-⌜⌝-𝟘-𝟘 m ⟩
            nr p′ q ⌜ m ⌝ 𝟘 𝟘           ≡˘⟨ PE.cong (λ p → nr _ _ p _ _) $ PE.cong ⌜_⌝ $ ᵐ·-identityʳ {m = m} ⟩
            nr p′ q ⌜ m ᵐ· 𝟙 ⌝ 𝟘 𝟘      ≡˘⟨ ·-identityˡ _ ⟩
            𝟙 · nr p′ q ⌜ m ᵐ· 𝟙 ⌝ 𝟘 𝟘  ∎
          (𝕤 , PE.refl) →
            ⌜ m ⌝ · nr p′ q 𝟘 𝟘 𝟘       ≡⟨ PE.cong (_·_ _) nr-𝟘 ⟩
            ⌜ m ⌝ · 𝟘                   ≡⟨ ·-zeroʳ _ ⟩
            𝟘                           ≡˘⟨ ·-zeroˡ _ ⟩
            𝟘 · nr p′ q ⌜ m ᵐ· 𝟘 ⌝ 𝟘 𝟘  ∎
        where
        open Tools.Reasoning.PropositionalEquality

      ⌜⌝·nr≡₂ :
        ∀ m →
        ⌜ m ⌝ · nr p′ q 𝟘 𝟘 boolrecᵍ-er PE.≡
        boolrecᵍ-er · nr p′ q 𝟘 𝟘 ⌜ m ᵐ· boolrecᵍ-er ⌝
      ⌜⌝·nr≡₂ {p′} {q} m =
        case PE.singleton s of λ where
          (𝕨 , PE.refl) →
            ⌜ m ⌝ · nr p′ q 𝟘 𝟘 𝟙       ≡⟨ ≡nr-𝟘-𝟘-⌜⌝ m ⟩
            nr p′ q 𝟘 𝟘 ⌜ m ⌝           ≡˘⟨ PE.cong (nr _ _ _ _) $ PE.cong ⌜_⌝ $ ᵐ·-identityʳ {m = m} ⟩
            nr p′ q 𝟘 𝟘 ⌜ m ᵐ· 𝟙 ⌝      ≡˘⟨ ·-identityˡ _ ⟩
            𝟙 · nr p′ q 𝟘 𝟘 ⌜ m ᵐ· 𝟙 ⌝  ∎
          (𝕤 , PE.refl) →
            ⌜ m ⌝ · nr p′ q 𝟘 𝟘 𝟘       ≡⟨ PE.cong (_·_ _) nr-𝟘 ⟩
            ⌜ m ⌝ · 𝟘                   ≡⟨ ·-zeroʳ _ ⟩
            𝟘                           ≡˘⟨ ·-zeroˡ _ ⟩
            𝟘 · nr p′ q 𝟘 𝟘 ⌜ m ᵐ· 𝟘 ⌝  ∎
        where
        open Tools.Reasoning.PropositionalEquality

    open ≤ᶜ-reasoning

    Target-lemma :
      let q = ⌜ 𝟘ᵐ? ⌝ · p in
      𝟘ᶜ ∙ ⌜ ⌞ q ⌟ ⌝ ∙ 𝟘 ▸[ ⌞ q ⌟ ] t →
      wkConₘ (stepn id k) γ₁ +ᶜ q ·ᶜ 𝟘ᶜ ∙ 𝟘 + q · 𝟙 ∙ 𝟘 + q · 𝟙 ▸[ 𝟘ᵐ? ]
        Target (2+ k) A t (var x0)
    Target-lemma ▸t =
      ▸Target
        (λ _ → begin
           ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝ ·ᶜ (𝟘ᶜ ∙ 𝟙 ∙ 𝟙)                           ≈⟨ ·ᶜ-zeroʳ _ ∙ ·-identityʳ _ ∙ ·-identityʳ _ ⟩
           𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝                ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityˡ _ ⟩
           𝟘ᶜ +ᶜ 𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝ + 𝟘 ∙ 𝟘 + ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝  ∎)
        (λ s≡𝕤 → begin
           ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝ ·ᶜ (𝟘ᶜ ∙ 𝟙 ∙ 𝟙)                           ≈⟨ ·ᶜ-zeroʳ _ ∙ ·-identityʳ _ ∙ ·-identityʳ _ ⟩
           𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝                ≤⟨ ≤ᶜ-refl ∙ ≤𝟘∧ s≡𝕤 ∙ ≤𝟘∧ s≡𝕤 ⟩
           𝟘ᶜ ∙ 𝟘 ∧ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝ ∙ 𝟘 ∧ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝        ≈˘⟨ ∧ᶜ-idem _ ∙ ∧-comm _ _ ∙ PE.refl ⟩
           𝟘ᶜ ∧ᶜ 𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝ ∧ 𝟘 ∙ 𝟘 ∧ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝  ∎)
        ▸A ▸t var

    opaque
      unfolding Boolᵍ boolrecᵍ-nc₃

      Π-lemma :
        𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ᵐ· boolrecᵍ-Π ⌝ ▸[ 𝟘ᵐ? ᵐ· boolrecᵍ-Π ] t →
        𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝ ∙ 𝟘 ▸[ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ] u →
        wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · (boolrecᵍ-nc₃ + p) ▸[ 𝟘ᵐ? ]
          Π boolrecᵍ-Π , p ▷ OK t ▹ Target (2+ k) A u (var x0)
      Π-lemma {k} ▸t ▸u = sub
        (ΠΣₘ (▸OK ▸t) $
         sub (Target-lemma ▸u) $ begin
           wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · p ∙ ⌜ 𝟘ᵐ? ⌝ · p            ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityˡ _ ∙ +-identityˡ _ ⟩

           (wkConₘ (stepn id k) γ₁ ∙ 𝟘 ∙ 𝟘) +ᶜ
           (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · p ∙ ⌜ 𝟘ᵐ? ⌝ · p)                              ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _ ∙ ·-identityʳ _ ∙ ·-identityʳ _) ⟩

           wkConₘ (stepn id (2+ k)) γ₁ +ᶜ (⌜ 𝟘ᵐ? ⌝ · p) ·ᶜ (𝟘ᶜ ∙ 𝟙 ∙ 𝟙)  ∎)
        (begin
           wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · (boolrecᵍ-nc₃ + p)  ≡⟨⟩

           wkConₘ (stepn id k) γ₁ ∙
           ⌜ 𝟘ᵐ? ⌝ · (⌜ ⌞ boolrecᵍ-Π ⌟ ⌝ · Boolᵍ + p)             ≈⟨ ≈ᶜ-refl ∙
                                                                     PE.trans (·-distribˡ-+ _ _ _)
                                                                       (PE.cong (flip _+_ _) (PE.sym $ ·-assoc _ _ _)) ⟩
           wkConₘ (stepn id k) γ₁ ∙
           (⌜ 𝟘ᵐ? ⌝ · ⌜ ⌞ boolrecᵍ-Π ⌟ ⌝) · Boolᵍ + ⌜ 𝟘ᵐ? ⌝ · p   ≈˘⟨ ≈ᶜ-refl ∙ PE.cong (flip _+_ _) (PE.cong (flip _·_ _) (⌜ᵐ·⌝ 𝟘ᵐ?)) ⟩

           wkConₘ (stepn id k) γ₁ ∙
           ⌜ 𝟘ᵐ? ᵐ· boolrecᵍ-Π ⌝ · Boolᵍ + ⌜ 𝟘ᵐ? ⌝ · p            ≈⟨ ≈ᶜ-sym (+ᶜ-identityˡ _) ∙ PE.cong (flip _+_ _) (≡nr-𝟘-𝟘-⌜⌝ (𝟘ᵐ? ᵐ· _)) ⟩

           (𝟘ᶜ +ᶜ wkConₘ (stepn id k) γ₁) ∙
           nr OKᵍ 𝟘 𝟘 𝟘 ⌜ 𝟘ᵐ? ᵐ· boolrecᵍ-Π ⌝ + ⌜ 𝟘ᵐ? ⌝ · p       ≡⟨⟩

           (𝟘ᶜ ∙ nr OKᵍ 𝟘 𝟘 𝟘 ⌜ 𝟘ᵐ? ᵐ· boolrecᵍ-Π ⌝) +ᶜ
           (wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · p)                 ≈˘⟨ +ᶜ-congʳ $ nrᶜ-𝟘ᶜ ∙ PE.refl ⟩

           nrᶜ OKᵍ 𝟘 𝟘ᶜ 𝟘ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ᵐ· boolrecᵍ-Π ⌝) +ᶜ
           (wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · p)                 ∎)

    unitrec-lemma :
      𝟘ᶜ ▸[ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ] t →
      γ ▸[ m ] u →
      wkConₘ (stepn id k) γ ▸[ m ]
        lam boolrecᵍ-Π
          (unitrec⟨ s ⟩ 0 boolrecᵍ-Π p (Target (2+ k) A t (var x0))
             (var x0) (wk[ 1+ k ]′ u))
    unitrec-lemma {k} {γ} ▸t ▸u =
      lamₘ $
      ▸unitrec⟨⟩ ok₂
        (λ { PE.refl →
             wkConₘ (stepn id (1+ k)) γ₁ ,
             sub
               (▸Target
                  (λ _ → begin
                     ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝ ·ᶜ (𝟘ᶜ ∙ 𝟙)   ≈⟨ ·ᶜ-zeroʳ _ ∙ ·-identityʳ _ ⟩
                     𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝          ≈˘⟨ +ᶜ-identityˡ _ ⟩
                     𝟘ᶜ +ᶜ (𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝)  ∎)
                  (λ ()) ▸A ▸t var)
               (begin
                  wkConₘ (stepn id (1+ k)) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · p          ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityˡ _ ⟩

                  wkConₘ (stepn id (2+ k)) γ₁ +ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · p)  ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _ ∙ ·-identityʳ _) ⟩

                  wkConₘ (stepn id (2+ k)) γ₁ +ᶜ
                  (⌜ 𝟘ᵐ? ⌝ · p) ·ᶜ (𝟘ᶜ ∙ 𝟙)                          ∎) })
        (λ { PE.refl →
             𝟘ᶜ ∙ ⌜ m ᵐ· boolrecᵍ-Π ⌝ ,
             var ,
             (begin
                wkConₘ (stepn id k) γ ∙ ⌜ m ⌝ · boolrecᵍ-Π               ≈˘⟨ +ᶜ-identityˡ _ ∙ +-identityʳ _ ⟩

                (𝟘ᶜ ∙ ⌜ m ⌝ · boolrecᵍ-Π) +ᶜ wkConₘ (stepn id (1+ k)) γ  ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _ ∙ PE.trans (·⌜ᵐ·⌝ m) (PE.sym $ ⌜⌝-·-comm m)) ⟩

                boolrecᵍ-Π ·ᶜ (𝟘ᶜ ∙ ⌜ m ᵐ· boolrecᵍ-Π ⌝) +ᶜ
                wkConₘ (stepn id (1+ k)) γ                               ∎) })
        (λ { PE.refl → begin
             wkConₘ (stepn id k) γ ∙ ⌜ m ⌝ · boolrecᵍ-Π  ≈⟨ ≈ᶜ-refl ∙ PE.cong (_·_ _) (boolrecᵍ-Π≡𝟘 PE.refl) ⟩
             wkConₘ (stepn id k) γ ∙ ⌜ m ⌝ · 𝟘           ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
             wkConₘ (stepn id k) γ ∙ 𝟘                   ∎ })
        (wkUsage (stepn id (1+ k)) ▸u)

opaque
  unfolding boolrecᵍ-er

  -- A variant of ▸boolrec that can be used if the dedicated nr
  -- function satisfies Linearity-like-nr-for-𝟘 and
  -- Linearity-like-nr-for-𝟙.
  --
  -- Note that the resulting usage vector might not be what one would
  -- have hoped for (maybe something like γ₂ ∧ᶜ γ₃ +ᶜ γ₄).

  ▸boolrec′ :
    Linearity-like-nr-for-𝟘 →
    Linearity-like-nr-for-𝟙 →
    (s PE.≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → 𝟙 ≤ 𝟘) →
    (s PE.≡ 𝕤 → r ≤ ⌜ m ⌝ · (𝟘 ∧ (𝟙 + 𝟙))) →
    (s PE.≡ 𝕨 → r ≤ 𝟙) →
    (s PE.≡ 𝕨 → Prodrec-allowed m 𝟙 𝟙 p) →
    (s PE.≡ 𝕨 → Unitrec-allowed m 𝟙 p) →
    Emptyrec-allowed m boolrecᵍ-er →
    γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · p ▸[ 𝟘ᵐ? ] A →
    γ₂ ▸[ m ] t →
    γ₃ ▸[ m ] u →
    γ₄ ▸[ m ] v →
    (𝟘ᶜ ∧ᶜ γ₂ ∧ᶜ γ₃) +ᶜ r ·ᶜ γ₄ ▸[ m ] boolrec p A t u v
  ▸boolrec′
    {r} {m} {γ₂} {γ₃}
    lin₀ lin₁ 𝟙≤𝟘 hyp₁ hyp₂ ok₁ ok₂ ok₃ ▸A ▸t ▸u ▸v = sub
    (▸boolrec 𝟙≤𝟘
       (λ { PE.refl →
            let open Tools.Reasoning.PartialOrder ≤-poset in begin
            r                              ≤⟨ hyp₁ PE.refl ⟩
            ⌜ m ⌝ · (𝟘 ∧ (𝟙 + 𝟙))          ≡˘⟨ PE.cong (_·_ _) $
                                               PE.trans (·-distribʳ-∧ _ _ _) $
                                               PE.cong₂ _∧_ (·-zeroˡ _) (·-identityˡ _) ⟩
            ⌜ m ⌝ · (𝟘 ∧ 𝟙) · (𝟙 + 𝟙)      ≡˘⟨ PE.cong (_·_ _) $ PE.cong (_· _) $ boolrecᵍ-pr≡ lin₀ lin₁ ⟩
            ⌜ m ⌝ · boolrecᵍ-pr · (𝟙 + 𝟙)  ∎ })
       (λ s≡𝕨 →
          let open Tools.Reasoning.PartialOrder ≤-poset in begin
          r            ≤⟨ hyp₂ s≡𝕨 ⟩
          𝟙            ≡⟨ lemma s≡𝕨 ⟩
          boolrecᵍ-pr  ∎)
       (λ s≡𝕨 →
          PE.subst₃ (Prodrec-allowed _) (lemma s≡𝕨) PE.refl PE.refl $
          ok₁ s≡𝕨)
       (λ { PE.refl →
            PE.subst₂ (Unitrec-allowed _)
              (PE.sym $ boolrecᵍ-Π≡ lin₁) PE.refl $
            ok₂ PE.refl })
       ok₃ ▸A ▸t ▸u ▸v)
    (let open ≤ᶜ-reasoning in
     +ᶜ-monotoneˡ $ begin
       𝟘ᶜ ∧ᶜ γ₂ ∧ᶜ γ₃                                                ≈˘⟨ ∧ᶜ-assoc _ _ _ ⟩

       (𝟘ᶜ ∧ᶜ γ₂) ∧ᶜ γ₃                                              ≈˘⟨ ∧ᶜ-congʳ $
                                                                         ∧ᶜ-cong (≈ᶜ-trans (+ᶜ-congʳ $ ·ᶜ-zeroʳ _) $ +ᶜ-identityˡ _)
                                                                           (+ᶜ-identityˡ _) ⟩

       (((𝟙 ∧ boolrecᵍ-nc₁) ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ) ∧ᶜ (𝟘ᶜ +ᶜ γ₂)) ∧ᶜ γ₃        ≈˘⟨ ∧ᶜ-congʳ $ nrᶜ-linearity-like-for-𝟘 lin₀ ⟩

       nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ 𝟘ᶜ 𝟘ᶜ ∧ᶜ γ₃                             ≈˘⟨ ∧ᶜ-cong (≈ᶜ-trans (+ᶜ-congʳ $ ·ᶜ-zeroʳ _) $ +ᶜ-identityˡ _)
                                                                           (+ᶜ-identityˡ _) ⟩
       ((𝟙 ∧ boolrecᵍ-nc₂) ·ᶜ 𝟘ᶜ +ᶜ nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ 𝟘ᶜ 𝟘ᶜ) ∧ᶜ
         (𝟘ᶜ +ᶜ γ₃)                                                  ≈˘⟨ nrᶜ-linearity-like-for-𝟘 lin₀ ⟩

       nrᶜ boolrecᵍ-nc₂ 𝟘 γ₃ (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ 𝟘ᶜ 𝟘ᶜ) 𝟘ᶜ        ∎)
    where
    lemma : s PE.≡ 𝕨 → 𝟙 PE.≡ boolrecᵍ-pr
    lemma PE.refl =
      𝟙            ≡˘⟨ ∧-idem _ ⟩
      𝟙 ∧ 𝟙        ≡˘⟨ boolrecᵍ-pr≡ lin₀ lin₁ ⟩
      boolrecᵍ-pr  ∎
      where
      open Tools.Reasoning.PropositionalEquality
