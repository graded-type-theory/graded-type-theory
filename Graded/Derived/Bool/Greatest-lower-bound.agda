------------------------------------------------------------------------
-- Some properties related to usage and Bool for the theory using
-- greatest lower bounds in the usage rule for natrec.
------------------------------------------------------------------------

import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Derived.Bool.Greatest-lower-bound
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (R : Usage-restrictions 𝕄)
  (open Usage-restrictions R)
  ⦃ no-nr : Nr-not-available-GLB ⦄
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
open import Definition.Untyped.Bool.Greatest-lower-bound 𝕄

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
  unfolding OK

  -- A usage lemma for OK.

  ▸OK :
    γ ▸[ m ] t →
    (𝟙 ∧ 𝟘) ·ᶜ γ ▸[ m ] OK t
  ▸OK {γ} {m} ▸t = sub-≈ᶜ
    (▸natcase′ Unitₘ
      (sub-≈ᶜ
         (▸natcase′ Unitₘ
            (sub-≈ᶜ Emptyₘ $ begin
               𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
               𝟘ᶜ              ∎)
            var
            (sub-≈ᶜ Uₘ $ begin
               𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
               𝟘ᶜ                ∎))
          (begin
            𝟘ᶜ ∙ ⌜ m ⌝ · (𝟙 ∧ 𝟘)                                ≈˘⟨ +ᶜ-identityʳ _ ⟩
            𝟘ᶜ +ᶜ 𝟘ᶜ ∙ ⌜ m ⌝ · (𝟙 ∧ 𝟘) + 𝟘                      ≈˘⟨ +ᶜ-cong (·ᶜ-zeroʳ _) (∧ᶜ-idem _) ∙
                                                                    +-cong (PE.sym (⌜⌝-·-comm m)) (∧-idem _) ⟩
            (𝟙 ∧ 𝟘) ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∙ (𝟙 ∧ 𝟘) · ⌜ m ⌝ + 𝟘 ∧ 𝟘 ∎))
      ▸t
      (sub-≈ᶜ Uₘ $ begin
         𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
         𝟘ᶜ                ∎))
    (begin
      (𝟙 ∧ 𝟘) ·ᶜ γ                 ≈˘⟨ ·ᶜ-congʳ (∧-congʳ (∧-idem _)) ⟩
      ((𝟙 ∧ 𝟙) ∧ 𝟘) ·ᶜ γ           ≈˘⟨ +ᶜ-identityʳ _ ⟩
      ((𝟙 ∧ 𝟙) ∧ 𝟘) ·ᶜ γ +ᶜ 𝟘ᶜ     ≈⟨ +ᶜ-cong (·ᶜ-congʳ (∧-assoc _ _ _)) (≈ᶜ-sym (∧ᶜ-idem _)) ⟩
      (𝟙 ∧ 𝟙 ∧ 𝟘) ·ᶜ γ +ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∎)
    where
    open ≈ᶜ-reasoning

opaque
  unfolding Bool

  -- A usage lemma for Bool.

  ▸Bool : 𝟘ᶜ ▸[ m ] Bool {n = n}
  ▸Bool {m} = sub-≈ᶜ
    (ΠΣₘ ℕₘ $
     sub-≈ᶜ (▸OK var) $ begin
       𝟘ᶜ ∙ ⌜ m ⌝ · (𝟙 ∧ 𝟘)    ≈˘⟨ ·ᶜ-zeroʳ _ ∙ PE.sym (⌜⌝-·-comm m) ⟩
       (𝟙 ∧ 𝟘) ·ᶜ (𝟘ᶜ ∙ ⌜ m ⌝) ∎)
    (begin
       𝟘ᶜ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
       𝟘ᶜ +ᶜ 𝟘ᶜ  ∎)
    where
    open ≈ᶜ-reasoning

opaque
  unfolding true

  -- A usage lemma for true.

  ▸true : 𝟘ᶜ ▸[ m ] true {n = n}
  ▸true {m} =
    sub-≈ᶜ (prodʷₘ (sucₘ zeroₘ) starₘ) $ begin
      𝟘ᶜ                  ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
      𝟙 ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
      𝟙 ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎
    where
    open ≈ᶜ-reasoning

opaque
  unfolding false

  -- A usage lemma for false.

  ▸false : 𝟘ᶜ ▸[ m ] false {n = n}
  ▸false {m} =
    sub-≈ᶜ (prodʷₘ zeroₘ starₘ) $ begin
      𝟘ᶜ                  ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
      𝟙 ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
      𝟙 ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎
    where
    open ≈ᶜ-reasoning

opaque
  unfolding Target

  -- A usage lemma for Target.

  ▸Target :
    γ₁ ∙ p ▸[ m ] A →
    γ₂ ▸[ ⌞ p ⌟ ] t →
    γ₃ ▸[ ⌞ p ⌟ ] u →
    wkConₘ (stepn id k) γ₁ +ᶜ p ·ᶜ (𝟙 ·ᶜ γ₂ +ᶜ γ₃) ▸[ m ] Target k A t u
  ▸Target ▸A ▸t ▸u =
    ▸[][]↑ ▸A $ ▸-·′ (prodʷₘ (▸-cong (PE.sym ᵐ·-identityʳ) ▸t) ▸u)

opaque
  unfolding Target

  -- A usage lemma for Target.

  ▸Target′ :
    γ₁ ∙ p ▸[ m ] A →
    γ₂ ▸[ ⌞ p ⌟ ] t →
    γ₃ ▸[ ⌞ p ⌟ ] u →
    (⌜ ⌞ p ⌟ ⌝ ·ᶜ γ₄ ≤ᶜ 𝟙 ·ᶜ γ₂ +ᶜ γ₃) →
    wkConₘ (stepn id k) γ₁ +ᶜ p ·ᶜ γ₄ ▸[ m ] Target k A t u
  ▸Target′ ▸A ▸t ▸u ≤+ =
    ▸[][]↑ ▸A $ sub (prodʷₘ (▸-cong (PE.sym ᵐ·-identityʳ) ▸t) ▸u) ≤+

opaque
  unfolding boolrec

  -- A usage lemma for boolrec.

  ▸boolrec :
    Prodrec-allowed m 𝟙 𝟙 p →
    Unitrec-allowed m 𝟙 p →
    Emptyrec-allowed m 𝟘 →
    Starˢ-sink →
    γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · p ▸[ 𝟘ᵐ? ] A →
    γ₂ ▸[ m ] t →
    γ₃ ▸[ m ] u →
    γ₄ ▸[ m ] v →
    γ₄ +ᶜ γ₂ ∧ᶜ γ₃ ▸[ m ] boolrec p A t u v
  ▸boolrec
    {m} {p} {γ₁} {A} {γ₂} {γ₃} {γ₄}
    ok₁ ok₂ ok₃ ok₄ ▸A ▸t ▸u ▸v = sub
      (prodrecₘ
        (▸-cong (PE.sym ᵐ·-identityʳ) ▸v)
        (sub
          (▸natcase′
            (unitrec-lemma zeroₘ ▸u)
            (sub
              (▸natcase′
                (unitrec-lemma (sucₘ zeroₘ) ▸t)
                (lamₘ $ sub
                  (▸emptyrec-sink var (Target-lemma (sucₘ (sucₘ var))) ok₃ ok₄)
                  (begin
                    γ₂ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ ⌜ m ⌝ · 𝟙 ∙ ⌜ m ⌝ · 𝟙                                  ≈˘⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ PE.refl ∙ PE.refl ⟩
                    γ₂ ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟙 ∙ ⌜ m ⌝ · 𝟙          ≤⟨ ≤ᶜ⌜⌝·ᶜ ▸t ∙ ≤-refl ∙ ≤-refl ∙ ≤-refl ∙ ≤-refl ∙ ≤-refl ⟩
                    ⌜ m ⌝ ·ᶜ γ₂ ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟙 ∙ ⌜ m ⌝ · 𝟙 ≡⟨⟩
                    ⌜ m ⌝ ·ᶜ (γ₂ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟙 ∙ 𝟙)                                       ∎))
                var (Π-lemma (sucₘ var) (sucₘ var)))
              (begin
                γ₂ ∙ 𝟘 ∙ 𝟘 ∙ ⌜ m ⌝ · 𝟙                                          ≈⟨ ≈ᶜ-refl ∙ ·-identityʳ _ ⟩
                γ₂ ∙ 𝟘 ∙ 𝟘 ∙ ⌜ m ⌝                                              ≈˘⟨ +ᶜ-identityˡ _ ∙ +-identityʳ _ ⟩
                (𝟘ᶜ ∙ ⌜ m ⌝) +ᶜ (γ₂ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘)                                ≈˘⟨ +ᶜ-congʳ (·ᶜ-identityˡ _) ⟩
                𝟙 ·ᶜ (𝟘ᶜ ∙ ⌜ m ⌝) +ᶜ (γ₂ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘)                           ≈˘⟨ +ᶜ-cong (·ᶜ-congʳ (∧-idem _)) (∧ᶜ-idem _) ⟩
                (𝟙 ∧ 𝟙) ·ᶜ (𝟘ᶜ ∙ ⌜ m ⌝) +ᶜ (γ₂ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘) ∧ᶜ (γ₂ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘) ∎))
            var (Π-lemma var var)
           ∘ₘ var)
          (begin
            γ₂ ∧ᶜ γ₃ ∙ ⌜ m ⌝ · 𝟙 · 𝟙 ∙ ⌜ m ⌝ · 𝟙                                                     ≈⟨ ∧ᶜ-comm _ _ ∙ ·-congˡ (·-identityʳ _) ∙ PE.refl ⟩
            γ₃ ∧ᶜ γ₂ ∙ ⌜ m ⌝ · 𝟙 ∙ ⌜ m ⌝ · 𝟙                                                         ≈⟨ ≈ᶜ-refl ∙ ·-identityʳ _ ∙ ·-identityʳ _ ⟩
            γ₃ ∧ᶜ γ₂ ∙ ⌜ m ⌝ ∙ ⌜ m ⌝                                                                 ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityˡ _ ⟩
            (γ₃ ∧ᶜ γ₂ ∙ ⌜ m ⌝ ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ ⌜ m ⌝)                                                   ≈˘⟨ +ᶜ-congʳ (+ᶜ-identityˡ _ ∙ +-identityʳ _ ∙ +-identityʳ _) ⟩
            ((𝟘ᶜ ∙ ⌜ m ⌝ ∙ 𝟘) +ᶜ (γ₃ ∧ᶜ γ₂ ∙ 𝟘 ∙ 𝟘)) +ᶜ (𝟘ᶜ ∙ ⌜ m ⌝)                                 ≈˘⟨ +ᶜ-cong (+ᶜ-congʳ (·ᶜ-identityˡ _)) (≈ᶜ-refl ∙ PE.cong ⌜_⌝ (ᵐ·-identityʳ {m = m})) ⟩
            (𝟙 ·ᶜ (𝟘ᶜ ∙ ⌜ m ⌝ ∙ 𝟘) +ᶜ (γ₃ ∧ᶜ γ₂ ∙ 𝟘 ∙ 𝟘)) +ᶜ (𝟘ᶜ ∙ ⌜ m ᵐ· 𝟙 ⌝)                       ≈˘⟨ +ᶜ-cong (+ᶜ-cong (·ᶜ-congʳ (∧-idem _)) (≈ᶜ-refl ∙ ∧-idem _ ∙ ∧-idem _)) (·ᶜ-identityˡ _) ⟩
            ((𝟙 ∧ 𝟙) ·ᶜ (𝟘ᶜ ∙ ⌜ m ⌝ ∙ 𝟘) +ᶜ (γ₃ ∙ 𝟘 ∙ 𝟘) ∧ᶜ (γ₂ ∙ 𝟘 ∙ 𝟘)) +ᶜ 𝟙 ·ᶜ (𝟘ᶜ ∙ ⌜ m ᵐ· 𝟙 ⌝) ∎))
        ▸A ok₁)
      (begin
        γ₄ +ᶜ γ₂ ∧ᶜ γ₃      ≈˘⟨ +ᶜ-congʳ (·ᶜ-identityˡ _) ⟩
        𝟙 ·ᶜ γ₄ +ᶜ γ₂ ∧ᶜ γ₃ ∎)
      where
      open ≤ᶜ-reasoning

      Target-lemma :
        let q = ⌜ 𝟘ᵐ? ⌝ · p in
        𝟘ᶜ ∙ ⌜ ⌞ q ⌟ ⌝ ∙ 𝟘 ▸[ ⌞ q ⌟ ] t →
        wkConₘ (stepn id k) γ₁ +ᶜ q ·ᶜ 𝟘ᶜ ∙ 𝟘 + q · 𝟙 ∙ 𝟘 + q · 𝟙 ▸[ 𝟘ᵐ? ]
          Target (2+ k) A t (var x0)
      Target-lemma ▸t =
        let q = ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝ in
        ▸Target′ ▸A ▸t var $ begin
          q ·ᶜ (𝟘ᶜ ∙ 𝟙 ∙ 𝟙)              ≈⟨ ·ᶜ-zeroʳ _ ∙ PE.refl ∙ ·-identityʳ _ ⟩
          𝟘ᶜ ∙ q · 𝟙 ∙ q                 ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityˡ _ ⟩
          (𝟘ᶜ ∙ q · 𝟙 ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ q)   ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _ ∙ PE.sym (⌜⌝-·-comm ⌞ _ ⌟) ∙ ·-zeroʳ _) ⟩
          𝟙 ·ᶜ (𝟘ᶜ ∙ q ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ q)  ∎

      Π-lemma :
        𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ᵐ· 𝟙 ⌝ ▸[ 𝟘ᵐ? ᵐ· 𝟙 ] t →
        𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝ ∙ 𝟘 ▸[ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ] u →
        wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · ((𝟙 + p) ∧ p) ▸[ 𝟘ᵐ? ]
          Π 𝟙 , p ▷ OK t ▹ Target (2+ k) A u (var x0)
      Π-lemma  {k} ▸t ▸u = sub
        (ΠΣₘ (▸OK ▸t) $
         sub (Target-lemma ▸u) $ begin
           wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · p ∙ ⌜ 𝟘ᵐ? ⌝ · p                   ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityˡ _ ∙ +-identityˡ _ ⟩
           (wkConₘ (stepn id k) γ₁ ∙ 𝟘 ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · p ∙ ⌜ 𝟘ᵐ? ⌝ · p) ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _ ∙ ·-identityʳ _ ∙ ·-identityʳ _) ⟩
           (wkConₘ (stepn id k) γ₁ ∙ 𝟘 ∙ 𝟘) +ᶜ (⌜ 𝟘ᵐ? ⌝ · p) ·ᶜ (𝟘ᶜ ∙ 𝟙 ∙ 𝟙)    ∎)
        (begin
          wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · ((𝟙 + p) ∧ p)                         ≈˘⟨ ≈ᶜ-refl ∙ ·-congˡ (∧-congˡ (+-identityˡ _)) ⟩
          wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · ((𝟙 + p) ∧ (𝟘 + p))                   ≈˘⟨ ≈ᶜ-refl ∙ ·-congˡ (+-distribʳ-∧ _ _ _) ⟩
          wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · ((𝟙 ∧ 𝟘) + p)                         ≈⟨ ≈ᶜ-refl ∙ ·-distribˡ-+ _ _ _ ⟩
          wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · (𝟙 ∧ 𝟘) + ⌜ 𝟘ᵐ? ⌝ · p                 ≈˘⟨ +ᶜ-identityˡ _ ∙ +-congʳ (PE.sym (⌜⌝-·-comm 𝟘ᵐ?)) ⟩
          (𝟘ᶜ ∙ (𝟙 ∧ 𝟘) · ⌜ 𝟘ᵐ? ⌝) +ᶜ (wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · p)       ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _ ∙ ·-congˡ (PE.cong ⌜_⌝ (ᵐ·-identityʳ {m = 𝟘ᵐ?}))) ⟩
          (𝟙 ∧ 𝟘) ·ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ᵐ· 𝟙 ⌝) +ᶜ (wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · p) ∎)

      unitrec-lemma :
        𝟘ᶜ ▸[ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ] t →
        γ ▸[ m ] u →
        wkConₘ (stepn id k) γ ▸[ m ] lam 𝟙 (unitrec 0 𝟙 p (Target (2+ k) A t (var x0)) (var x0) (wk[ 1+ k ]′ u))
      unitrec-lemma {k} {γ} ▸t ▸u =
        lamₘ $
        sub
          (unitrecₘ var (wkUsage (stepn id (1+ k)) ▸u)
            (sub (▸Target ▸A ▸t var) $ begin
              wkConₘ (stepn id (1+ k)) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · p                                                     ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityˡ _ ⟩
              (wkConₘ (stepn id (1+ k)) γ₁ ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · p)                                       ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _ ∙ ·⌜⌞⌟⌝) ⟩
              (wkConₘ (stepn id (1+ k)) γ₁ ∙ 𝟘) +ᶜ (⌜ 𝟘ᵐ? ⌝ · p) ·ᶜ (𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝)              ≈˘⟨  +ᶜ-congˡ (·ᶜ-congˡ (+ᶜ-identityˡ _)) ⟩
              (wkConₘ (stepn id (1+ k)) γ₁ ∙ 𝟘) +ᶜ (⌜ 𝟘ᵐ? ⌝ · p) ·ᶜ (𝟘ᶜ +ᶜ (𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝))      ≈˘⟨ +ᶜ-congˡ (·ᶜ-congˡ (+ᶜ-congʳ (·ᶜ-identityˡ _))) ⟩
              (wkConₘ (stepn id (1+ k)) γ₁ ∙ 𝟘) +ᶜ (⌜ 𝟘ᵐ? ⌝ · p) ·ᶜ (𝟙 ·ᶜ 𝟘ᶜ +ᶜ (𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝)) ∎)
            ok₂)
          (begin
            wkConₘ (stepn id k) γ ∙ (⌜ m ⌝ · 𝟙)                    ≈⟨ ≈ᶜ-refl ∙ ·-identityʳ _ ⟩
            wkConₘ (stepn id k) γ ∙ ⌜ m ⌝                          ≈˘⟨ ≈ᶜ-refl ∙ PE.cong ⌜_⌝ (ᵐ·-identityʳ {m = m})  ⟩
            wkConₘ (stepn id k) γ ∙ ⌜ m ᵐ· 𝟙 ⌝                     ≈˘⟨ +ᶜ-identityˡ _ ∙ +-identityʳ _ ⟩
            (𝟘ᶜ ∙ ⌜ m ᵐ· 𝟙 ⌝) +ᶜ (wkConₘ (stepn id k) γ ∙ 𝟘)       ≈˘⟨ +ᶜ-congʳ (·ᶜ-identityˡ _) ⟩
            𝟙 ·ᶜ (𝟘ᶜ ∙ ⌜ m ᵐ· 𝟙 ⌝) +ᶜ (wkConₘ (stepn id k) γ ∙ 𝟘)  ∎)
