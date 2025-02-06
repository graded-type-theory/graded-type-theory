------------------------------------------------------------------------
-- Some properties related to usage and Bool
------------------------------------------------------------------------

import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Derived.Bool
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (R : Usage-restrictions 𝕄)
  (open Usage-restrictions R)
  -- It is assumed that the modality has an nr function.
  ⦃ has-nr : Nr-available ⦄
  where

open Modality 𝕄

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Derived.Empty R
open import Graded.Derived.Nat 𝕄 R
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄
open import Graded.Substitution.Properties 𝕄 R
open import Graded.Usage 𝕄 R
open import Graded.Usage.Properties 𝕄 R
open import Graded.Usage.Restrictions.Instance R
open import Graded.Usage.Weakening 𝕄 R

open import Definition.Untyped M
open import Definition.Untyped.Bool 𝕄

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+; 2+)
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder

private variable
  k n             : Nat
  A t u v         : Term _
  γ γ₁ γ₂ γ₃ γ₄ δ : Conₘ _
  p               : M
  m               : Mode

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
    sub (prodʷₘ (sucₘ zeroₘ) starₘ) $ begin
      𝟘ᶜ             ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
      ω ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
      ω ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎
    where
    open ≤ᶜ-reasoning

opaque
  unfolding false

  -- A usage lemma for false.

  ▸false : 𝟘ᶜ ▸[ m ] false {n = n}
  ▸false {m} =
    sub (prodʷₘ zeroₘ starₘ) $ begin
      𝟘ᶜ             ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
      ω ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
      ω ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎
    where
    open ≤ᶜ-reasoning

opaque
  unfolding Target

  -- A usage lemma for Target.

  ▸Target :
    γ₁ ∙ p ▸[ m ] A →
    γ₂ ▸[ ⌞ p ⌟ ] t →
    γ₃ ▸[ ⌞ p ⌟ ] u →
    (⌜ ⌞ p ⌟ ⌝ ·ᶜ γ₄ ≤ᶜ ω ·ᶜ γ₂ +ᶜ γ₃) →
    wkConₘ (stepn id k) γ₁ +ᶜ p ·ᶜ γ₄ ▸[ m ] Target k A t u
  ▸Target ▸A ▸t ▸u ≤+ =
    ▸[][]↑ ▸A $ sub (prodʷₘ (▸-cong (PE.sym ᵐ·-identityʳ-ω) ▸t) ▸u) ≤+

opaque
  unfolding boolrec boolrecᵍ-nc₂ boolrecᵍ-pr

  -- A usage lemma for boolrec.

  ▸boolrec :
    Prodrec-allowed m boolrecᵍ-pr ω p →
    Unitrec-allowed m boolrecᵍ-Π p →
    Emptyrec-allowed m 𝟘 →
    Starˢ-sink →
    γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · p ▸[ 𝟘ᵐ? ] A →
    γ₂ ▸[ m ] t →
    γ₃ ▸[ m ] u →
    γ₄ ▸[ m ] v →
    nrᶜ boolrecᵍ-nc₂ 𝟘 γ₃ (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ (⌜ m ⌝ ·ᶜ δ) 𝟘ᶜ) 𝟘ᶜ +ᶜ
      boolrecᵍ-pr ·ᶜ γ₄ ▸[ m ]
      boolrec p A t u v
  ▸boolrec
    {m} {p} {γ₁} {A} {γ₂} {γ₃} {γ₄} {δ}
    ok₁ ok₂ ok₃ ok₄ ▸A ▸t ▸u ▸v = sub
    (prodrecₘ
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
                      (▸emptyrec-sink var
                         (Target-lemma (sucₘ (sucₘ var))) ok₃ ok₄)
                      (begin
                         wkConₘ (stepn id 3) (⌜ m ⌝ ·ᶜ δ) ∙
                         ⌜ m ⌝ · boolrecᵍ-nc₁ ∙ ⌜ m ⌝ · boolrecᵍ-Π  ≈⟨ wk-·ᶜ (stepn id 3) ∙ PE.refl ∙ PE.refl ⟩

                         ⌜ m ⌝ ·ᶜ
                         (wkConₘ (stepn id 3) δ ∙
                          boolrecᵍ-nc₁ ∙ boolrecᵍ-Π)                ∎))
                   var (Π-lemma (sucₘ var) (sucₘ var)))
                (begin
                   wkConₘ (stepn id 2)
                     (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ (⌜ m ⌝ ·ᶜ δ) 𝟘ᶜ) ∙
                   ⌜ m ⌝ · boolrecᵍ-nc₂                               ≡⟨⟩

                   wkConₘ (stepn id 2)
                     (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ (⌜ m ⌝ ·ᶜ δ) 𝟘ᶜ) ∙
                   ⌜ m ⌝ · nr boolrecᵍ-nc₁ 𝟘 𝟘 𝟘 𝟙                    ≈⟨ wk-nrᶜ (stepn id 2) ∙ ≡nr-𝟘-𝟘-⌜⌝ m ⟩

                   nrᶜ boolrecᵍ-nc₁ 𝟘 (wkConₘ (stepn id 2) γ₂)
                     (wkConₘ (stepn id 2) (⌜ m ⌝ ·ᶜ δ))
                     (wkConₘ (stepn id 2) 𝟘ᶜ) ∙
                   nr boolrecᵍ-nc₁ 𝟘 𝟘 𝟘 ⌜ m ⌝                        ≡⟨⟩

                   nrᶜ boolrecᵍ-nc₁ 𝟘 (wkConₘ (stepn id 3) γ₂)
                     (wkConₘ (stepn id 3) (⌜ m ⌝ ·ᶜ δ)) (𝟘ᶜ ∙ ⌜ m ⌝)  ∎))
             var (Π-lemma var var) ∘ₘ
           var)
          (begin
             nrᶜ boolrecᵍ-nc₂ 𝟘 γ₃
               (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ (⌜ m ⌝ ·ᶜ δ) 𝟘ᶜ) 𝟘ᶜ ∙
             ⌜ m ⌝ · boolrecᵍ-pr · ω ∙ ⌜ m ⌝ · boolrecᵍ-pr               ≤⟨ ≤ᶜ-refl ∙ ·-monotoneʳ ·ω-decreasing ∙ ≤-refl ⟩

             nrᶜ boolrecᵍ-nc₂ 𝟘 γ₃
               (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ (⌜ m ⌝ ·ᶜ δ) 𝟘ᶜ) 𝟘ᶜ ∙
             ⌜ m ⌝ · boolrecᵍ-pr ∙ ⌜ m ⌝ · boolrecᵍ-pr                   ≡⟨⟩

             nrᶜ boolrecᵍ-nc₂ 𝟘 γ₃
               (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ (⌜ m ⌝ ·ᶜ δ) 𝟘ᶜ) 𝟘ᶜ ∙
             ⌜ m ⌝ · (nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 𝟙 ∧ boolrecᵍ-Π) ∙
             ⌜ m ⌝ · (nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 𝟙 ∧ boolrecᵍ-Π)              ≤⟨ ≤ᶜ-refl ∙ ·-monotoneʳ (∧-decreasingˡ _ _) ∙
                                                                            ·-monotoneʳ (∧-decreasingʳ _ _) ⟩
             nrᶜ boolrecᵍ-nc₂ 𝟘 γ₃
               (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ (⌜ m ⌝ ·ᶜ δ) 𝟘ᶜ) 𝟘ᶜ ∙
             ⌜ m ⌝ · nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 𝟙 ∙ ⌜ m ⌝ · boolrecᵍ-Π        ≈⟨ ≈ᶜ-refl ∙ ⌜⌝-·-comm m ⟩

             nrᶜ boolrecᵍ-nc₂ 𝟘 γ₃
               (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ (⌜ m ⌝ ·ᶜ δ) 𝟘ᶜ) 𝟘ᶜ ∙
             ⌜ m ⌝ · nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 𝟙 ∙ boolrecᵍ-Π · ⌜ m ⌝        ≈⟨ ≈ᶜ-refl ∙ ≡nr-𝟘-𝟘-⌜⌝ m ∙ PE.sym (+-identityˡ _) ⟩

             nrᶜ boolrecᵍ-nc₂ 𝟘 γ₃
               (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ (⌜ m ⌝ ·ᶜ δ) 𝟘ᶜ) 𝟘ᶜ ∙
             nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 ⌜ m ⌝ ∙ 𝟘 + boolrecᵍ-Π · ⌜ m ⌝        ≈˘⟨ +ᶜ-identityʳ _ ∙ PE.cong (flip _+_ _) nr-𝟘 ⟩

             (nrᶜ boolrecᵍ-nc₂ 𝟘 γ₃
                (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ (⌜ m ⌝ ·ᶜ δ) 𝟘ᶜ) 𝟘ᶜ ∙
              nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 ⌜ m ⌝ ∙ nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 𝟘) +ᶜ
             (𝟘ᶜ ∙ boolrecᵍ-Π · ⌜ m ⌝)                                   ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _ ∙ ·⌜ᵐ·⌝ m) ⟩

             nrᶜ boolrecᵍ-nc₂ 𝟘 (wkConₘ (stepn id 2) γ₃)
               (wkConₘ (stepn id 2)
                  (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ (⌜ m ⌝ ·ᶜ δ) 𝟘ᶜ))
               (𝟘ᶜ ∙ ⌜ m ⌝ ∙ 𝟘) +ᶜ
             boolrecᵍ-Π ·ᶜ (𝟘ᶜ ∙ ⌜ m ᵐ· boolrecᵍ-Π ⌝)                    ∎))
       ▸A ok₁)
    (begin
       nrᶜ boolrecᵍ-nc₂ 𝟘 γ₃
         (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ (⌜ m ⌝ ·ᶜ δ) 𝟘ᶜ) 𝟘ᶜ +ᶜ
       boolrecᵍ-pr ·ᶜ γ₄                                                 ≈⟨ +ᶜ-comm _ _ ⟩

       boolrecᵍ-pr ·ᶜ γ₄ +ᶜ
       nrᶜ boolrecᵍ-nc₂ 𝟘 γ₃ (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ (⌜ m ⌝ ·ᶜ δ) 𝟘ᶜ) 𝟘ᶜ  ∎)
    where
    open ≤ᶜ-reasoning

    Target-lemma :
      let q = ⌜ 𝟘ᵐ? ⌝ · p in
      𝟘ᶜ ∙ ⌜ ⌞ q ⌟ ⌝ ∙ 𝟘 ▸[ ⌞ q ⌟ ] t →
      wkConₘ (stepn id k) γ₁ +ᶜ q ·ᶜ 𝟘ᶜ ∙ 𝟘 + q · ω ∙ 𝟘 + q · 𝟙 ▸[ 𝟘ᵐ? ]
        Target (2+ k) A t (var x0)
    Target-lemma ▸t =
      let q = ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝ in
      ▸Target ▸A ▸t var $ begin
        q ·ᶜ (𝟘ᶜ ∙ ω ∙ 𝟙)              ≈⟨ ·ᶜ-zeroʳ _ ∙ PE.refl ∙ ·-identityʳ _ ⟩
        𝟘ᶜ ∙ q · ω ∙ q                 ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityˡ _ ⟩
        (𝟘ᶜ ∙ q · ω ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ q)   ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _ ∙ PE.sym (⌜⌝-·-comm ⌞ _ ⌟) ∙ ·-zeroʳ _) ⟩
        ω ·ᶜ (𝟘ᶜ ∙ q ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ q)  ∎

    opaque
      unfolding Boolᵍ boolrecᵍ-nc₃

      Π-lemma :
        𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ᵐ· boolrecᵍ-Π ⌝ ▸[ 𝟘ᵐ? ᵐ· boolrecᵍ-Π ] t →
        𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝ ∙ 𝟘 ▸[ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ] u →
        wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · boolrecᵍ-nc₃ p ▸[ 𝟘ᵐ? ]
          Π boolrecᵍ-Π , p ▷ OK t ▹ Target (2+ k) A u (var x0)
      Π-lemma {k} ▸t ▸u = sub
        (ΠΣₘ (▸OK ▸t) $
         sub (Target-lemma ▸u) $ begin
           wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · p · ω ∙ ⌜ 𝟘ᵐ? ⌝ · p        ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityˡ _ ∙ +-identityˡ _ ⟩

           (wkConₘ (stepn id k) γ₁ ∙ 𝟘 ∙ 𝟘) +ᶜ
           (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · p · ω ∙ ⌜ 𝟘ᵐ? ⌝ · p)                          ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _ ∙ ·-assoc _ _ _ ∙ ·-identityʳ _) ⟩

           wkConₘ (stepn id (2+ k)) γ₁ +ᶜ (⌜ 𝟘ᵐ? ⌝ · p) ·ᶜ (𝟘ᶜ ∙ ω ∙ 𝟙)  ∎)
        (begin
           wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · boolrecᵍ-nc₃ p         ≡⟨⟩

           wkConₘ (stepn id k) γ₁ ∙
           ⌜ 𝟘ᵐ? ⌝ · (⌜ ⌞ boolrecᵍ-Π ⌟ ⌝ · Boolᵍ + p · ω)            ≈⟨ ≈ᶜ-refl ∙
                                                                        PE.trans (·-distribˡ-+ _ _ _)
                                                                          (PE.cong (flip _+_ _) (PE.sym $ ·-assoc _ _ _)) ⟩
           wkConₘ (stepn id k) γ₁ ∙
           (⌜ 𝟘ᵐ? ⌝ · ⌜ ⌞ boolrecᵍ-Π ⌟ ⌝) · Boolᵍ + ⌜ 𝟘ᵐ? ⌝ · p · ω  ≈˘⟨ ≈ᶜ-refl ∙ PE.cong (flip _+_ _) (PE.cong (flip _·_ _) (⌜ᵐ·⌝ 𝟘ᵐ?)) ⟩

           wkConₘ (stepn id k) γ₁ ∙
           ⌜ 𝟘ᵐ? ᵐ· boolrecᵍ-Π ⌝ · Boolᵍ + ⌜ 𝟘ᵐ? ⌝ · p · ω           ≈⟨ ≈ᶜ-sym (+ᶜ-identityˡ _) ∙ PE.cong (flip _+_ _) (≡nr-𝟘-𝟘-⌜⌝ (𝟘ᵐ? ᵐ· _)) ⟩

           (𝟘ᶜ +ᶜ wkConₘ (stepn id k) γ₁) ∙
           nr OKᵍ 𝟘 𝟘 𝟘 ⌜ 𝟘ᵐ? ᵐ· boolrecᵍ-Π ⌝ + ⌜ 𝟘ᵐ? ⌝ · p · ω      ≡⟨⟩

           (𝟘ᶜ ∙ nr OKᵍ 𝟘 𝟘 𝟘 ⌜ 𝟘ᵐ? ᵐ· boolrecᵍ-Π ⌝) +ᶜ
           (wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · p · ω)                ≈˘⟨ +ᶜ-congʳ $ nrᶜ-𝟘ᶜ ∙ PE.refl ⟩

           nrᶜ OKᵍ 𝟘 𝟘ᶜ 𝟘ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ᵐ· boolrecᵍ-Π ⌝) +ᶜ
           (wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · p · ω)                ∎)

    unitrec-lemma :
      𝟘ᶜ ▸[ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ] t →
      γ ▸[ m ] u →
      wkConₘ (stepn id k) γ ▸[ m ]
        lam boolrecᵍ-Π
          (unitrec 0 boolrecᵍ-Π p (Target (2+ k) A t (var x0)) (var x0)
             (wk[ 1+ k ]′ u))
    unitrec-lemma {k} {γ} ▸t ▸u =
      lamₘ $
      sub
        (unitrecₘ var (wkUsage (stepn id (1+ k)) ▸u)
           (sub
              (▸Target ▸A ▸t var $ begin
                 ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝ ·ᶜ (𝟘ᶜ ∙ 𝟙)        ≈⟨ ·ᶜ-zeroʳ _ ∙ ·-identityʳ _ ⟩
                 𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝               ≈˘⟨ +ᶜ-identityˡ _ ⟩
                 𝟘ᶜ +ᶜ (𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝)       ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
                 ω ·ᶜ 𝟘ᶜ +ᶜ (𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝)  ∎)
              (begin
                 wkConₘ (stepn id (1+ k)) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · p          ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityˡ _ ⟩

                 wkConₘ (stepn id (2+ k)) γ₁ +ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · p)  ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _ ∙ ·-identityʳ _) ⟩

                 wkConₘ (stepn id (2+ k)) γ₁ +ᶜ
                 (⌜ 𝟘ᵐ? ⌝ · p) ·ᶜ (𝟘ᶜ ∙ 𝟙)                          ∎))
           ok₂)
        (begin
           wkConₘ (stepn id k) γ ∙ ⌜ m ⌝ · boolrecᵍ-Π               ≈˘⟨ +ᶜ-identityˡ _ ∙ +-identityʳ _ ⟩

           (𝟘ᶜ ∙ ⌜ m ⌝ · boolrecᵍ-Π) +ᶜ wkConₘ (stepn id (1+ k)) γ  ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _ ∙ PE.trans (·⌜ᵐ·⌝ m) (PE.sym $ ⌜⌝-·-comm m)) ⟩

           boolrecᵍ-Π ·ᶜ (𝟘ᶜ ∙ ⌜ m ᵐ· boolrecᵍ-Π ⌝) +ᶜ
           wkConₘ (stepn id (1+ k)) γ                               ∎)

opaque

  -- A variant of ▸boolrec that can be used if the nr
  -- function satisfies Linearity-like-nr-for-𝟘 and
  -- Linearity-like-nr-for-𝟙.

  ▸boolrec′ :
    Linearity-like-nr-for-𝟘 →
    Linearity-like-nr-for-𝟙 →
    Prodrec-allowed m 𝟙 ω p →
    Unitrec-allowed m 𝟙 p →
    Emptyrec-allowed m 𝟘 →
    Starˢ-sink →
    γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · p ▸[ 𝟘ᵐ? ] A →
    γ₂ ▸[ m ] t →
    γ₃ ▸[ m ] u →
    γ₄ ▸[ m ] v →
    γ₂ ∧ᶜ γ₃ +ᶜ γ₄ ▸[ m ] boolrec p A t u v
  ▸boolrec′
    {m} {γ₂} {γ₃} {γ₄} lin₀ lin₁ ok₁ ok₂ ok₃ ok₄ ▸A ▸t ▸u ▸v = sub
    (▸boolrec
       (PE.subst₃ (Prodrec-allowed _)
          (PE.sym $ boolrecᵍ-pr≡ lin₀ lin₁) PE.refl PE.refl ok₁)
       (PE.subst₂ (Unitrec-allowed _)
          (PE.sym $ boolrecᵍ-Π≡ lin₁) PE.refl ok₂)
       ok₃ ok₄ ▸A ▸t ▸u ▸v)
    (begin
       γ₂ ∧ᶜ γ₃ +ᶜ γ₄                                                   ≈˘⟨ +ᶜ-congʳ $ ∧ᶜ-congʳ (∧ᶜ-idem _) ⟩

       (γ₂ ∧ᶜ γ₂) ∧ᶜ γ₃ +ᶜ γ₄                                           ≤⟨ +ᶜ-monotoneˡ $ ∧ᶜ-monotoneˡ $ ∧ᶜ-monotoneˡ $ ≤ᶜ⌜⌝·ᶜ ▸t ⟩

       (⌜ m ⌝ ·ᶜ γ₂ ∧ᶜ γ₂) ∧ᶜ γ₃ +ᶜ γ₄                                  ≈˘⟨ +ᶜ-congʳ $ ∧ᶜ-congʳ $
                                                                            ∧ᶜ-cong (≈ᶜ-trans (+ᶜ-congʳ $ ·ᶜ-zeroʳ _) $ +ᶜ-identityˡ _)
                                                                              (+ᶜ-identityˡ _) ⟩

       (((𝟙 ∧ boolrecᵍ-nc₁) ·ᶜ 𝟘ᶜ +ᶜ ⌜ m ⌝ ·ᶜ γ₂) ∧ᶜ (𝟘ᶜ +ᶜ γ₂)) ∧ᶜ γ₃
         +ᶜ
       γ₄                                                               ≈˘⟨ +ᶜ-congʳ $ ∧ᶜ-congʳ $ nrᶜ-linearity-like-for-𝟘 lin₀ ⟩

       nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ (⌜ m ⌝ ·ᶜ γ₂) 𝟘ᶜ ∧ᶜ γ₃ +ᶜ γ₄               ≈˘⟨ +ᶜ-cong
                                                                              (∧ᶜ-cong (≈ᶜ-trans (+ᶜ-congʳ $ ·ᶜ-zeroʳ _) $ +ᶜ-identityˡ _)
                                                                                 (+ᶜ-identityˡ _))
                                                                              (·ᶜ-identityˡ _) ⟩
       ((𝟙 ∧ boolrecᵍ-nc₂) ·ᶜ 𝟘ᶜ +ᶜ
        nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ (⌜ m ⌝ ·ᶜ γ₂) 𝟘ᶜ) ∧ᶜ
       (𝟘ᶜ +ᶜ γ₃) +ᶜ
       𝟙 ·ᶜ γ₄                                                          ≈˘⟨ +ᶜ-cong (nrᶜ-linearity-like-for-𝟘 lin₀)
                                                                              (·ᶜ-congʳ $ boolrecᵍ-pr≡ lin₀ lin₁) ⟩
       nrᶜ boolrecᵍ-nc₂ 𝟘 γ₃
         (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ (⌜ m ⌝ ·ᶜ γ₂) 𝟘ᶜ) 𝟘ᶜ +ᶜ
       boolrecᵍ-pr ·ᶜ γ₄                                                ∎)
    where
    open ≤ᶜ-reasoning
