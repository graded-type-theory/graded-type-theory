------------------------------------------------------------------------
-- Some properties related to usage and Bool for the theory using
-- greatest lower bounds in the usage rule for natrec.
------------------------------------------------------------------------

import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions

module Graded.Derived.Bool.Greatest-lower-bound
  {a b} {M : Set a} {Mode : Set b}
  (open Graded.Modality M)
  {𝕄 : Modality}
  {𝐌 : IsMode Mode 𝕄}
  (R : Usage-restrictions 𝕄 𝐌)
  (open Usage-restrictions R)
  ⦃ no-nr : Nr-not-available-GLB ⦄
  where

open Modality 𝕄
open IsMode 𝐌

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Derived.Empty R
open import Graded.Derived.Nat R
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄
open import Graded.Substitution.Properties R
open import Graded.Usage R
open import Graded.Usage.Inversion R
open import Graded.Usage.Properties R
open import Graded.Usage.Restrictions.Instance R
open import Graded.Usage.Weakening R

open import Definition.Untyped M
open import Definition.Untyped.Bool.Greatest-lower-bound 𝕄

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+; 2+)
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder

private variable
  k n             : Nat
  A t u v         : Term _
  γ γ₁ γ₂ γ₃ γ₄ δ : Conₘ _
  p               : M
  m               : Mode

------------------------------------------------------------------------
-- Usage lemmas

opaque
  unfolding OK

  -- A usage lemma for OK.

  ▸OK :
    γ ▸[ m ] t →
    (𝟙 ∧ 𝟘) ·ᶜ γ ▸[ m ] OK t
  ▸OK {γ} {m} ▸t = sub-≈ᶜ
    (▸natcase-glb Unitₘ
      (sub-≈ᶜ
         (▸natcase-glb Unitₘ
            (sub-≈ᶜ Emptyₘ $ begin
               𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
               𝟘ᶜ              ∎)
            var
            (sub-≈ᶜ (Uₘ zeroᵘₘ) $ begin
               𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
               𝟘ᶜ                ∎))
          (begin
            𝟘ᶜ ∙ ⌜ m ⌝ · (𝟙 ∧ 𝟘)                                ≈˘⟨ +ᶜ-identityʳ _ ⟩
            𝟘ᶜ +ᶜ 𝟘ᶜ ∙ ⌜ m ⌝ · (𝟙 ∧ 𝟘) + 𝟘                      ≈˘⟨ +ᶜ-cong (·ᶜ-zeroʳ _) (∧ᶜ-idem _) ∙
                                                                    +-cong (PE.sym (⌜⌝-·-comm m)) (∧-idem _) ⟩
            (𝟙 ∧ 𝟘) ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∙ (𝟙 ∧ 𝟘) · ⌜ m ⌝ + 𝟘 ∧ 𝟘 ∎))
      ▸t
      (sub-≈ᶜ (Uₘ zeroᵘₘ) $ begin
         𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
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
       𝟘ᶜ             ≈˘⟨ +ᶜ-identityʳ _ ⟩
       𝟘ᶜ +ᶜ 𝟘ᶜ       ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
       𝟙 ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎)
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
    γ₁ ∙ ⌜ 𝟘ᵐ ⌝ · p ▸[ 𝟘ᵐ ] A →
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
          (▸natcase-glb
            (unitrec-lemma zeroₘ ▸u)
            (sub
              (▸natcase-glb
                (unitrec-lemma (sucₘ zeroₘ) ▸t)
                (lamₘ $ sub
                  (▸emptyrec-sink var (Target-lemma (sucₘ (sucₘ var))) ok₃ ok₄)
                  (begin
                    γ₂ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ ⌜ m ⌝ · 𝟙 ∙ ⌜ m ⌝ · 𝟙                                  ≈˘⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ PE.refl ∙ PE.refl ⟩
                    γ₂ ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟙 ∙ ⌜ m ⌝ · 𝟙          ≤⟨ ▸ᵐ ▸t ∙ ≤-refl ∙ ≤-refl ∙ ≤-refl ∙ ≤-refl ∙ ≤-refl ⟩
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
        let q = ⌜ 𝟘ᵐ ⌝ · p in
        𝟘ᶜ ∙ ⌜ ⌞ q ⌟ ⌝ ∙ 𝟘 ▸[ ⌞ q ⌟ ] t →
        wkConₘ (stepn id k) γ₁ +ᶜ q ·ᶜ 𝟘ᶜ ∙ 𝟘 + q · 𝟙 ∙ 𝟘 + q · 𝟙 ▸[ 𝟘ᵐ ]
          Target (2+ k) A t (var x0)
      Target-lemma ▸t =
        let q = ⌜ ⌞ ⌜ 𝟘ᵐ ⌝ · p ⌟ ⌝ in
        ▸Target′ ▸A ▸t var $ begin
          q ·ᶜ (𝟘ᶜ ∙ 𝟙 ∙ 𝟙)              ≈⟨ ·ᶜ-zeroʳ _ ∙ PE.refl ∙ ·-identityʳ _ ⟩
          𝟘ᶜ ∙ q · 𝟙 ∙ q                 ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityˡ _ ⟩
          (𝟘ᶜ ∙ q · 𝟙 ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ q)   ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _ ∙ PE.sym (⌜⌝-·-comm ⌞ _ ⌟) ∙ ·-zeroʳ _) ⟩
          𝟙 ·ᶜ (𝟘ᶜ ∙ q ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ q)  ∎

      Π-lemma :
        𝟘ᶜ ∙ ⌜ 𝟘ᵐ ᵐ· 𝟙 ⌝ ▸[ 𝟘ᵐ ᵐ· 𝟙 ] t →
        𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ ⌝ · p ⌟ ⌝ ∙ 𝟘 ▸[ ⌞ ⌜ 𝟘ᵐ ⌝ · p ⌟ ] u →
        wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ ⌝ · ((𝟙 + p) ∧ p) ▸[ 𝟘ᵐ ]
          Π 𝟙 , p ▷ OK t ▹ Target (2+ k) A u (var x0)
      Π-lemma  {k} ▸t ▸u = sub
        (ΠΣₘ (▸OK ▸t) $
         sub (Target-lemma ▸u) $ begin
           wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ ⌝ · p ∙ ⌜ 𝟘ᵐ ⌝ · p                   ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityˡ _ ∙ +-identityˡ _ ⟩
           (wkConₘ (stepn id k) γ₁ ∙ 𝟘 ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · p ∙ ⌜ 𝟘ᵐ ⌝ · p) ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _ ∙ ·-identityʳ _ ∙ ·-identityʳ _) ⟩
           (wkConₘ (stepn id k) γ₁ ∙ 𝟘 ∙ 𝟘) +ᶜ (⌜ 𝟘ᵐ ⌝ · p) ·ᶜ (𝟘ᶜ ∙ 𝟙 ∙ 𝟙)   ∎)
        (begin
          wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ ⌝ · ((𝟙 + p) ∧ p)                             ≈˘⟨ ≈ᶜ-refl ∙ ·-congˡ (∧-congˡ (+-identityˡ _)) ⟩
          wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ ⌝ · ((𝟙 + p) ∧ (𝟘 + p))                       ≈˘⟨ ≈ᶜ-refl ∙ ·-congˡ (+-distribʳ-∧ _ _ _) ⟩
          wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ ⌝ · ((𝟙 ∧ 𝟘) + p)                             ≈⟨ ≈ᶜ-refl ∙ ·-distribˡ-+ _ _ _ ⟩
          wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ ⌝ · (𝟙 ∧ 𝟘) + ⌜ 𝟘ᵐ ⌝ · p                      ≈˘⟨ +ᶜ-identityˡ _ ∙ +-congʳ (PE.sym (⌜⌝-·-comm 𝟘ᵐ)) ⟩
          (𝟘ᶜ ∙ (𝟙 ∧ 𝟘) · ⌜ 𝟘ᵐ ⌝) +ᶜ (wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ ⌝ · p)            ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _ ∙ ·-congˡ (PE.cong ⌜_⌝ (ᵐ·-identityʳ {m = 𝟘ᵐ}))) ⟩
          (𝟙 ∧ 𝟘) ·ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ ᵐ· 𝟙 ⌝) +ᶜ (wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ ⌝ · p)      ≈˘⟨ +ᶜ-congʳ (·ᶜ-identityˡ _) ⟩
          𝟙 ·ᶜ (𝟙 ∧ 𝟘) ·ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ ᵐ· 𝟙 ⌝) +ᶜ (wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ ⌝ · p) ∎)

      unitrec-lemma :
        𝟘ᶜ ▸[ ⌞ ⌜ 𝟘ᵐ ⌝ · p ⌟ ] t →
        γ ▸[ m ] u →
        wkConₘ (stepn id k) γ ▸[ m ] lam 𝟙 (unitrec 𝟙 p (Target (2+ k) A t (var x0)) (var x0) (wk[ 1+ k ]′ u))
      unitrec-lemma {k} {γ} ▸t ▸u =
        lamₘ $
        sub
          (unitrecₘ var (wkUsage (stepn id (1+ k)) ▸u)
            (sub (▸Target ▸A ▸t var) $ begin
              wkConₘ (stepn id (1+ k)) γ₁ ∙ ⌜ 𝟘ᵐ ⌝ · p                                                    ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityˡ _ ⟩
              (wkConₘ (stepn id (1+ k)) γ₁ ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · p)                                      ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _ ∙ ·⌜⌞⌟⌝) ⟩
              (wkConₘ (stepn id (1+ k)) γ₁ ∙ 𝟘) +ᶜ (⌜ 𝟘ᵐ ⌝ · p) ·ᶜ (𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ ⌝ · p ⌟ ⌝)              ≈˘⟨  +ᶜ-congˡ (·ᶜ-congˡ (+ᶜ-identityˡ _)) ⟩
              (wkConₘ (stepn id (1+ k)) γ₁ ∙ 𝟘) +ᶜ (⌜ 𝟘ᵐ ⌝ · p) ·ᶜ (𝟘ᶜ +ᶜ (𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ ⌝ · p ⌟ ⌝))      ≈˘⟨ +ᶜ-congˡ (·ᶜ-congˡ (+ᶜ-congʳ (·ᶜ-identityˡ _))) ⟩
              (wkConₘ (stepn id (1+ k)) γ₁ ∙ 𝟘) +ᶜ (⌜ 𝟘ᵐ ⌝ · p) ·ᶜ (𝟙 ·ᶜ 𝟘ᶜ +ᶜ (𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ ⌝ · p ⌟ ⌝)) ∎)
            ok₂)
          (begin
            wkConₘ (stepn id k) γ ∙ (⌜ m ⌝ · 𝟙)                    ≈⟨ ≈ᶜ-refl ∙ ·-identityʳ _ ⟩
            wkConₘ (stepn id k) γ ∙ ⌜ m ⌝                          ≈˘⟨ ≈ᶜ-refl ∙ PE.cong ⌜_⌝ (ᵐ·-identityʳ {m = m})  ⟩
            wkConₘ (stepn id k) γ ∙ ⌜ m ᵐ· 𝟙 ⌝                     ≈˘⟨ +ᶜ-identityˡ _ ∙ +-identityʳ _ ⟩
            (𝟘ᶜ ∙ ⌜ m ᵐ· 𝟙 ⌝) +ᶜ (wkConₘ (stepn id k) γ ∙ 𝟘)       ≈˘⟨ +ᶜ-congʳ (·ᶜ-identityˡ _) ⟩
            𝟙 ·ᶜ (𝟘ᶜ ∙ ⌜ m ᵐ· 𝟙 ⌝) +ᶜ (wkConₘ (stepn id k) γ ∙ 𝟘)  ∎)

------------------------------------------------------------------------
-- Usage inversion lemmas

opaque
  unfolding OK

  -- A usage inversion lemma for OK.

  inv-usage-OK :
    γ ▸[ m ] OK t →
    ∃ λ δ → δ ▸[ m ] t × γ ≤ᶜ (𝟙 ∧ 𝟘) ·ᶜ δ
  inv-usage-OK {γ} ▸OK =
    let δ , η , θ , φ , ▸⊤ , ▸nc , ▸t , ▸U , γ≤ = inv-usage-natcase-glb ▸OK
        open ≤ᶜ-reasoning
    in  case inv-usage-natcase-glb ▸nc of λ {
         (δ′ ∙ _ , η′ ∙ _ , θ′ ∙ _ , φ′ ∙ _ , ▸⊤′ , ▸⊥ , ▸x0 , ▸U′ , η≤) →
        _ , ▸t , (begin
          γ                                                        ≤⟨ γ≤ ⟩
          (𝟙 ∧ 𝟙 ∧ 𝟘) ·ᶜ θ +ᶜ δ ∧ᶜ η                               ≤⟨ +ᶜ-monotoneʳ (∧ᶜ-monotoneʳ (tailₘ-monotone η≤)) ⟩
          (𝟙 ∧ 𝟙 ∧ 𝟘) ·ᶜ θ +ᶜ δ ∧ᶜ ((𝟙 ∧ 𝟘) ·ᶜ θ′ +ᶜ (δ′ ∧ᶜ η′))   ≤⟨ +ᶜ-monotoneʳ (∧ᶜ-monotone (inv-usage-Unit ▸⊤)
                                                                       (+ᶜ-monotone (·ᶜ-monotoneʳ (tailₘ-monotone (inv-usage-var ▸x0)))
                                                                         (∧ᶜ-monotone (tailₘ-monotone (inv-usage-Unit ▸⊤′))
                                                                           (tailₘ-monotone (tailₘ-monotone (inv-usage-Empty ▸⊥)))))) ⟩
          (𝟙 ∧ 𝟙 ∧ 𝟘) ·ᶜ θ +ᶜ 𝟘ᶜ ∧ᶜ ((𝟙 ∧ 𝟘) ·ᶜ 𝟘ᶜ +ᶜ (𝟘ᶜ ∧ᶜ 𝟘ᶜ)) ≈⟨ +ᶜ-cong (·ᶜ-congʳ (PE.sym (∧-assoc _ _ _))) (∧ᶜ-congˡ (+ᶜ-cong (·ᶜ-zeroʳ _) (∧ᶜ-idem _))) ⟩
          ((𝟙 ∧ 𝟙) ∧ 𝟘) ·ᶜ θ +ᶜ 𝟘ᶜ ∧ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ)                  ≈⟨ +ᶜ-cong (·ᶜ-congʳ (∧-congʳ (∧-idem _))) (∧ᶜ-congˡ (+ᶜ-identityʳ _)) ⟩
          (𝟙 ∧ 𝟘) ·ᶜ θ +ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ                                ≈⟨ +ᶜ-congˡ (∧ᶜ-idem _) ⟩
          (𝟙 ∧ 𝟘) ·ᶜ θ +ᶜ 𝟘ᶜ                                      ≈⟨ +ᶜ-identityʳ _ ⟩
          (𝟙 ∧ 𝟘) ·ᶜ θ                                            ∎)}

opaque
  unfolding Bool

  -- A usage inversion lemma for Bool.

  inv-usage-Bool : γ ▸[ m ] Bool → γ ≤ᶜ 𝟘ᶜ
  inv-usage-Bool {γ} ▸Bool =
    let invUsageΠΣ {δ} {η} ▸ℕ ▸OK γ≤ = inv-usage-ΠΣ ▸Bool
        θ , ▸x0 , η≤ = inv-usage-OK ▸OK
        open ≤ᶜ-reasoning
    in  begin
      γ                          ≤⟨ γ≤ ⟩
      𝟙 ·ᶜ δ +ᶜ η                ≈⟨ +ᶜ-congʳ (·ᶜ-identityˡ _) ⟩
      δ +ᶜ η                     ≤⟨ +ᶜ-monotone (inv-usage-ℕ ▸ℕ) (tailₘ-monotone η≤) ⟩
      𝟘ᶜ +ᶜ tailₘ ((𝟙 ∧ 𝟘) ·ᶜ θ) ≈⟨ +ᶜ-identityˡ _ ⟩
      tailₘ ((𝟙 ∧ 𝟘) ·ᶜ θ)       ≤⟨ tailₘ-monotone (·ᶜ-monotoneʳ (inv-usage-var ▸x0)) ⟩
      tailₘ ((𝟙 ∧ 𝟘) ·ᶜ 𝟘ᶜ)      ≈⟨ tailₘ-cong (·ᶜ-zeroʳ _) ⟩
      𝟘ᶜ                         ∎

opaque
  unfolding true

  -- A usage inversion lemma for true.

  inv-usage-true : γ ▸[ m ] true → γ ≤ᶜ 𝟘ᶜ
  inv-usage-true {γ} ▸true =
    let invUsageProdʷ {δ} {η} ▸1 ▸* γ≤ = inv-usage-prodʷ ▸true
        invUsageSuc {δ = δ′} ▸0 δ≤ = inv-usage-suc ▸1
        open ≤ᶜ-reasoning
    in  begin
      γ             ≤⟨ γ≤ ⟩
      𝟙 ·ᶜ δ +ᶜ η   ≤⟨ +ᶜ-monotone (·ᶜ-monotoneʳ δ≤) (inv-usage-starʷ ▸*) ⟩
      𝟙 ·ᶜ δ′ +ᶜ 𝟘ᶜ ≈⟨ +ᶜ-identityʳ _ ⟩
      𝟙 ·ᶜ δ′       ≤⟨ ·ᶜ-monotoneʳ (inv-usage-zero ▸0) ⟩
      𝟙 ·ᶜ 𝟘ᶜ       ≈⟨ ·ᶜ-identityˡ _ ⟩
      𝟘ᶜ            ∎


opaque
  unfolding false

  -- A usage inversion lemma for false.

  inv-usage-false : γ ▸[ m ] false → γ ≤ᶜ 𝟘ᶜ
  inv-usage-false {γ} ▸false =
    let invUsageProdʷ {δ} {η} ▸0 ▸* γ≤ = inv-usage-prodʷ ▸false
        open ≤ᶜ-reasoning
    in  begin
      γ             ≤⟨ γ≤ ⟩
      𝟙 ·ᶜ δ +ᶜ η   ≤⟨ +ᶜ-monotone (·ᶜ-monotoneʳ (inv-usage-zero ▸0)) (inv-usage-starʷ ▸*) ⟩
      𝟙 ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ ≈⟨ +ᶜ-identityʳ _ ⟩
      𝟙 ·ᶜ 𝟘ᶜ       ≈⟨ ·ᶜ-identityˡ _ ⟩
      𝟘ᶜ            ∎

opaque
  unfolding boolrec

  -- A usage inversion lemma for boolrec.

  inv-usage-boolrec :
    γ ▸[ m ] boolrec p A t u v →
    ∃₄ λ δ η θ φ →
    δ ▸[ m ] t × η ▸[ m ] u × θ ▸[ m ] v × φ ∙ ⌜ 𝟘ᵐ ⌝ · p ▸[ 𝟘ᵐ ] A ×
    Prodrec-allowed m 𝟙 𝟙 p × Unitrec-allowed m 𝟙 p × Emptyrec-allowed m 𝟘 × γ ≤ᶜ θ +ᶜ δ ∧ᶜ η
  inv-usage-boolrec {γ} ▸br =
    let invUsageProdrec {δ = δ₁} {η = δ₂} ▸v ▸nc∘ ▸A ok γ≤ = inv-usage-prodrec ▸br
        open ≤ᶜ-reasoning
    in  case inv-usage-app ▸nc∘ of λ {
          (invUsageApp  {δ = η₁ ∙ _ ∙ _} {η = η₂ ∙ _ ∙ _} ▸nc ▸x0 (δ₂≤ ∙ _ ∙ _)) →
        case inv-usage-natcase-glb ▸nc of λ {
          (θ₁ ∙ _ ∙ _ , θ₂ ∙ _ ∙ _ , θ₃ ∙ _ ∙ _ , θ₄ ∙ _ ∙ _ , ▸λur , ▸nc′ , ▸x1 , ▸Π , (η₁≤ ∙ _ ∙ _)) →
        case inv-usage-lam ▸λur of λ {
          (invUsageLam {δ = θ₁′ ∙ _ ∙ _} ▸ur (θ₁≤ ∙ _ ∙ _)) →
        case inv-usage-unitrec ▸ur of λ {
          (invUsageUnitrec {δ = φ₁ ∙ _ ∙ _ ∙ _} {η = φ₂ ∙ _ ∙ _ ∙ _} ▸x0′ ▸u ▸T ok′ (θ₁′≤ ∙ _ ∙ _ ∙ _)) →
        case inv-usage-natcase-glb ▸nc′ of λ {
          (χ₁ ∙ _ ∙ _ ∙ _ , χ₂ ∙ _ ∙ _ ∙ _ , χ₃ ∙ _ ∙ _ ∙ _ , χ₄ ∙ _ ∙ _ ∙ _ , ▸λur′ , ▸λer , ▸x0″ , ▸Π′ , (θ₂≤ ∙ _ ∙ _ ∙ _)) →
        case inv-usage-lam ▸λur′ of λ {
          (invUsageLam {δ = χ₁′ ∙ _ ∙ _ ∙ _} ▸ur′ (χ₁≤ ∙ _ ∙ _ ∙ _)) →
        case inv-usage-lam ▸λer of λ {
          (invUsageLam {δ = χ₂′ ∙ _ ∙ _ ∙ _ ∙ _} ▸er (χ₂≤ ∙ _ ∙ _ ∙ _ ∙ _)) →
        case inv-usage-unitrec ▸ur′ of λ {
          (invUsageUnitrec {δ = ζ₁ ∙ _ ∙ _ ∙ _ ∙ _} {η = ζ₂ ∙ _ ∙ _ ∙ _ ∙ _} ▸x0‴ ▸t ▸T′ _ (χ₁′≤ ∙ _ ∙ _ ∙ _ ∙ _)) →
        case inv-usage-emptyrec-sink ▸er of λ {
          (ξ₁ , ξ₂ , qe , wer , ok″) →
        _ , _ , _ , _ , wkUsage⁻¹ ▸t , wkUsage⁻¹ ▸u , ▸-cong ᵐ·-identityʳ ▸v , ▸A , ok , ok′ , ok″ , (begin
          γ                                                      ≤⟨ γ≤ ⟩
          𝟙 ·ᶜ δ₁ +ᶜ δ₂                                          ≈⟨ +ᶜ-congʳ (·ᶜ-identityˡ _) ⟩
          δ₁ +ᶜ δ₂                                               ≤⟨ +ᶜ-monotoneʳ δ₂≤ ⟩
          δ₁ +ᶜ η₁ +ᶜ 𝟙 ·ᶜ η₂                                    ≈⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-identityˡ _)) ⟩
          δ₁ +ᶜ η₁ +ᶜ η₂                                         ≤⟨ +ᶜ-monotoneʳ (+ᶜ-monotone η₁≤ (tailₘ-monotone (tailₘ-monotone (inv-usage-var ▸x0)))) ⟩
          δ₁ +ᶜ ((𝟙 ∧ 𝟙) ·ᶜ θ₃ +ᶜ θ₁ ∧ᶜ θ₂) +ᶜ 𝟘ᶜ                ≈⟨ +ᶜ-congˡ (+ᶜ-identityʳ _) ⟩
          δ₁ +ᶜ ((𝟙 ∧ 𝟙) ·ᶜ θ₃ +ᶜ θ₁ ∧ᶜ θ₂)                      ≈⟨ +ᶜ-congˡ (+ᶜ-congʳ (·ᶜ-congʳ (∧-idem _))) ⟩
          δ₁ +ᶜ (𝟙 ·ᶜ θ₃ +ᶜ θ₁ ∧ᶜ θ₂)                            ≈⟨ +ᶜ-congˡ (+ᶜ-congʳ (·ᶜ-identityˡ _)) ⟩
          δ₁ +ᶜ (θ₃ +ᶜ θ₁ ∧ᶜ θ₂)                                 ≤⟨ +ᶜ-monotoneʳ (+ᶜ-monotone (tailₘ-monotone (tailₘ-monotone (inv-usage-var ▸x1)))
                                                                    (∧ᶜ-monotone θ₁≤ θ₂≤)) ⟩
          δ₁ +ᶜ (𝟘ᶜ +ᶜ θ₁′ ∧ᶜ ((𝟙 ∧ 𝟙) ·ᶜ χ₃ +ᶜ χ₁ ∧ᶜ χ₂))       ≈⟨ +ᶜ-congˡ (+ᶜ-identityˡ _) ⟩
          δ₁ +ᶜ (θ₁′ ∧ᶜ ((𝟙 ∧ 𝟙) ·ᶜ χ₃ +ᶜ χ₁ ∧ᶜ χ₂))             ≤⟨ +ᶜ-monotoneʳ (∧ᶜ-monotoneˡ θ₁′≤) ⟩
          δ₁ +ᶜ ((𝟙 ·ᶜ φ₁ +ᶜ φ₂) ∧ᶜ ((𝟙 ∧ 𝟙) ·ᶜ χ₃ +ᶜ χ₁ ∧ᶜ χ₂)) ≈⟨ +ᶜ-congˡ (∧ᶜ-cong (+ᶜ-congʳ (·ᶜ-identityˡ _)) (+ᶜ-congʳ (·ᶜ-congʳ (∧-idem _)))) ⟩
          δ₁ +ᶜ ((φ₁ +ᶜ φ₂) ∧ᶜ (𝟙 ·ᶜ χ₃ +ᶜ χ₁ ∧ᶜ χ₂))            ≈⟨ +ᶜ-congˡ (∧ᶜ-congˡ (+ᶜ-congʳ (·ᶜ-identityˡ _))) ⟩
          δ₁ +ᶜ ((φ₁ +ᶜ φ₂) ∧ᶜ (χ₃ +ᶜ χ₁ ∧ᶜ χ₂))                 ≤⟨ +ᶜ-monotoneʳ (∧ᶜ-monotone (+ᶜ-monotoneˡ
                                                                      (tailₘ-monotone (tailₘ-monotone (tailₘ-monotone (inv-usage-var ▸x0′)))))
                                                                      (+ᶜ-monotone (tailₘ-monotone (tailₘ-monotone (tailₘ-monotone (inv-usage-var ▸x0″))))
                                                                        (∧ᶜ-monotone χ₁≤ χ₂≤))) ⟩
          δ₁ +ᶜ ((𝟘ᶜ +ᶜ φ₂) ∧ᶜ (𝟘ᶜ +ᶜ χ₁′ ∧ᶜ χ₂′))               ≈⟨ +ᶜ-congˡ (∧ᶜ-cong (+ᶜ-identityˡ _) (+ᶜ-identityˡ _)) ⟩
          δ₁ +ᶜ (φ₂ ∧ᶜ (χ₁′ ∧ᶜ χ₂′))                             ≤⟨ +ᶜ-monotoneʳ (∧ᶜ-monotoneʳ (∧ᶜ-decreasingˡ _ _)) ⟩
          δ₁ +ᶜ (φ₂ ∧ᶜ χ₁′)                                      ≤⟨ +ᶜ-monotoneʳ (∧ᶜ-monotoneʳ χ₁′≤) ⟩
          δ₁ +ᶜ (φ₂ ∧ᶜ (𝟙 ·ᶜ ζ₁ +ᶜ ζ₂))                          ≈⟨ +ᶜ-congˡ (∧ᶜ-congˡ (+ᶜ-congʳ (·ᶜ-identityˡ _))) ⟩
          δ₁ +ᶜ (φ₂ ∧ᶜ (ζ₁ +ᶜ ζ₂))                               ≤⟨ +ᶜ-monotoneʳ (∧ᶜ-monotoneʳ (+ᶜ-monotoneˡ (tailₘ-monotone
                                                                    (tailₘ-monotone (tailₘ-monotone (tailₘ-monotone (inv-usage-var ▸x0‴))))))) ⟩
          δ₁ +ᶜ (φ₂ ∧ᶜ (𝟘ᶜ +ᶜ ζ₂))                               ≈⟨ +ᶜ-congˡ (∧ᶜ-congˡ (+ᶜ-identityˡ _)) ⟩
          δ₁ +ᶜ (φ₂ ∧ᶜ ζ₂)                                       ≈⟨ +ᶜ-congˡ (∧ᶜ-comm _ _) ⟩
          δ₁ +ᶜ ζ₂ ∧ᶜ φ₂                                         ∎ ) }}}}}}}}}
