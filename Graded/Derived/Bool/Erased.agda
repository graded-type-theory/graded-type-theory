------------------------------------------------------------------------
-- Some properties related to usage and Bool
------------------------------------------------------------------------

import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Derived.Bool.Erased
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (R : Usage-restrictions 𝕄)
  (open Usage-restrictions R)
  -- It is assumed that the modality has an nr function.
  ⦃ has-nr : Nr-available ⦄
  where

open Modality 𝕄

open import Definition.Untyped M
open import Definition.Untyped.Bool.Nr 𝕄
  using (OK; OKᵍ; boolrecᵍ-nc₁; boolrecᵍ-nc₂)
open import Definition.Untyped.Bool.Erased 𝕄
open import Definition.Untyped.Erased 𝕄 𝕨 as E

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
import Graded.Derived.Bool.Nr R as B
open import Graded.Derived.Empty R
open import Graded.Derived.Erased.Usage 𝕄 R 𝕨
open import Graded.Derived.Nat 𝕄 R
open import Graded.Usage.Restrictions.Instance R
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄
open import Graded.Substitution.Properties 𝕄 R
open import Graded.Usage 𝕄 R
open import Graded.Usage.Properties 𝕄 R
open import Graded.Usage.Weakening 𝕄 R

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+; 2+; 3+)
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality

private variable
  k n             : Nat
  A t u v         : Term _
  γ γ₁ γ₂ γ₃ γ₄ δ : Conₘ _
  p r             : M
  m               : Mode

private opaque

  -- A lemma used below.

  ≡nr-𝟘-𝟘-⌜𝟘ᵐ?⌝ :
    ∀ m → ⌜ m ⌝ · nr p r 𝟘 𝟘 ⌜ 𝟘ᵐ? ⌝ PE.≡ nr p r 𝟘 𝟘 ⌜ 𝟘ᵐ? ⌝
  ≡nr-𝟘-𝟘-⌜𝟘ᵐ?⌝ {p} {r} m =
    ⌜ m ⌝ · nr p r 𝟘 𝟘 ⌜ 𝟘ᵐ? ⌝                        ≡⟨ ⌜⌝-·-distribˡ-nr m ⟩
    nr p r (⌜ m ⌝ · 𝟘) (⌜ m ⌝ · 𝟘) (⌜ m ⌝ · ⌜ 𝟘ᵐ? ⌝)  ≡⟨ PE.cong₃ (nr _ _) (·-zeroʳ _) (·-zeroʳ _) (PE.sym $ ⌜·ᵐ⌝ m) ⟩
    nr p r 𝟘 𝟘 (⌜ m ·ᵐ 𝟘ᵐ? ⌝)                         ≡⟨ PE.cong (nr _ _ _ _) $ PE.cong ⌜_⌝ $ ·ᵐ-zeroʳ m ⟩
    nr p r 𝟘 𝟘 ⌜ 𝟘ᵐ? ⌝                                ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding Bool Boolᵍ

  -- A usage lemma for Bool.

  ▸Bool : 𝟘ᶜ ▸[ m ] Bool {n = n}
  ▸Bool {m} = sub
    (ΠΣₘ ℕₘ $
     sub (▸Erased (B.▸OK var)) $ begin
       𝟘ᶜ ∙ ⌜ m ⌝ · Boolᵍ              ≈⟨ ≈ᶜ-refl ∙ ≡nr-𝟘-𝟘-⌜𝟘ᵐ?⌝ m ⟩
       𝟘ᶜ ∙ Boolᵍ                      ≈˘⟨ nrᶜ-𝟘ᶜ ∙ PE.refl ⟩
       nrᶜ OKᵍ 𝟘 𝟘ᶜ 𝟘ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝)  ∎)
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
    sub (prodʷₘ (sucₘ zeroₘ) (▸[] starₘ)) $ begin
      𝟘ᶜ             ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
      𝟙 ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
      𝟙 ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎
    where
    open ≤ᶜ-reasoning

opaque
  unfolding false

  -- A usage lemma for false.

  ▸false : 𝟘ᶜ ▸[ m ] false {n = n}
  ▸false {m} =
    sub (prodʷₘ zeroₘ (▸[] starₘ)) $ begin
      𝟘ᶜ             ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
      𝟙 ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
      𝟙 ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎
    where
    open ≤ᶜ-reasoning

opaque
  unfolding Target

  -- A usage lemma for Target.

  ▸Target :
    γ₁ ∙ p ▸[ m ] A →
    γ₂ ▸[ ⌞ p ⌟ ] t →
    γ₃ ▸[ ⌞ p ⌟ ] u →
    (⌜ ⌞ p ⌟ ⌝ ·ᶜ γ₄ ≤ᶜ γ₂ +ᶜ γ₃) →
    wkConₘ (stepn id k) γ₁ +ᶜ p ·ᶜ γ₄ ▸[ m ] Target k A t u
  ▸Target {p} {γ₂} {γ₃} {γ₄} ▸A ▸t ▸u ≤+ =
    ▸[][]↑ ▸A $
    sub (prodʷₘ (▸-cong (PE.sym ᵐ·-identityʳ) ▸t) ▸u) $ (begin
      ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ₄  ≤⟨ ≤+ ⟩
      γ₂ +ᶜ γ₃         ≈˘⟨ +ᶜ-congʳ (·ᶜ-identityˡ _) ⟩
      𝟙 ·ᶜ γ₂ +ᶜ γ₃    ∎)
    where
    open ≤ᶜ-reasoning

opaque
  unfolding boolrec boolrecᵍ-nc₂ boolrecᵍ-pr is-𝕨

  -- A usage lemma for boolrec.

  ▸boolrec :
    Prodrec-allowed m boolrecᵍ-pr 𝟙 p →
    Prodrec-allowed m 𝟙 𝟘 p →
    Unitrec-allowed m 𝟙 p →
    Unitrec-allowed m 𝟘 𝟘 →
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
    ok₁ ok₂ ok₃ ok₄ ok₅ ok₆ ▸A ▸t ▸u ▸v = sub
    (prodrecₘ
       (▸-cong
          (PE.sym $ ≢𝟘→ᵐ·≡′ λ ok →
           boolrecᵍ-pr≢𝟘 ⦃ 𝟘-well-behaved = 𝟘-well-behaved ok ⦄)
          ▸v)
       (sub
          (▸natcase (lam-lemma zeroₘ ▸u)
             (sub
                (▸natcase (lam-lemma (sucₘ zeroₘ) ▸t)
                   (lamₘ $
                    sub
                      (▸erasedrec (λ ()) (λ _ → ok₂) (λ _ → ok₃)
                         (λ _ →
                            wkConₘ (stepn id 3) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · p ∙ 𝟘 ,
                            sub
                              (▸Target ▸A (sucₘ (sucₘ var)) var $
                               begin
                                 ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝ ·ᶜ (𝟘ᶜ ∙ 𝟙 ∙ 𝟘 ∙ 𝟙)  ≈⟨ ·ᶜ-zeroʳ _ ∙ ·-identityʳ _ ∙ ·-zeroʳ _ ∙ ·-identityʳ _ ⟩

                                 𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝ ∙ 𝟘 ∙
                                 ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝                      ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityˡ _ ⟩

                                 (𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝ ∙ 𝟘 ∙ 𝟘) +ᶜ
                                 (𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝)               ∎)
                              (begin
                                 wkConₘ (stepn id 3) γ₁ ∙
                                 ⌜ 𝟘ᵐ? ⌝ · p ∙ 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ · p         ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityˡ _ ∙ +-identityˡ _ ∙ +-identityˡ _ ⟩

                                 wkConₘ (stepn id 6) γ₁ +ᶜ
                                 (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · p ∙ 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ · p)  ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _ ∙ ·-identityʳ _ ∙ ·-zeroʳ _ ∙ ·-identityʳ _) ⟩

                                 wkConₘ (stepn id 6) γ₁ +ᶜ
                                 (⌜ 𝟘ᵐ? ⌝ · p) ·ᶜ (𝟘ᶜ ∙ 𝟙 ∙ 𝟘 ∙ 𝟙)     ∎))
                         (sub
                            (▸emptyrec-sink var
                               (▸Target ▸A (sucₘ (sucₘ var))
                                  (▸[] var) $
                                begin
                                  ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝ ·ᶜ
                                  (𝟘ᶜ ∙ 𝟙 ∙ 𝟘 ∙ 𝟘)                       ≈⟨ ·ᶜ-zeroʳ _ ∙ ·-identityʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩

                                  𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝ ∙ 𝟘 ∙ 𝟘       ≈˘⟨ +ᶜ-identityʳ _ ⟩


                                  (𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝ ∙ 𝟘 ∙ 𝟘) +ᶜ
                                  𝟘ᶜ                                     ∎)
                               ok₅ ok₆)
                            (begin
                               ⌜ m ⌝ ·ᶜ
                               (wkConₘ (stepn id 3) δ ∙ boolrecᵍ-nc₁ ∙
                                𝟘) ∙
                               𝟘                                        ≈˘⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩

                               ⌜ m ⌝ ·ᶜ
                               (wkConₘ (stepn id 3) δ ∙ boolrecᵍ-nc₁ ∙
                                𝟘 ∙ 𝟘)                                  ∎))
                         var)
                      (begin
                         wkConₘ (stepn id 3) (⌜ m ⌝ ·ᶜ δ) ∙
                         ⌜ m ⌝ · boolrecᵍ-nc₁ ∙ ⌜ m ⌝ · 𝟙               ≈⟨ wk-·ᶜ (stepn id 3) ∙ PE.refl ∙ PE.refl ⟩

                         ⌜ m ⌝ ·ᶜ
                         (wkConₘ (stepn id 3) δ ∙ boolrecᵍ-nc₁ ∙ 𝟙)     ≈˘⟨ +ᶜ-identityʳ _ ∙
                                                                            PE.trans (PE.cong (flip _+_ _) (·-zeroʳ _))
                                                                              (PE.trans (+-identityˡ _) (PE.sym (·-identityʳ _))) ⟩
                         ⌜ m ⌝ ·ᶜ
                         (wkConₘ (stepn id 3) δ ∙ boolrecᵍ-nc₁ ∙ 𝟘) +ᶜ
                         (𝟘ᶜ ∙ ⌜ m ⌝)                                   ≈˘⟨ +ᶜ-congˡ (≈ᶜ-refl ∙ PE.cong ⌜_⌝ (ᵐ·-identityʳ {m = m})) ⟩

                         ⌜ m ⌝ ·ᶜ
                         (wkConₘ (stepn id 3) δ ∙ boolrecᵍ-nc₁ ∙ 𝟘) +ᶜ
                         (𝟘ᶜ ∙ ⌜ m ᵐ· 𝟙 ⌝)                              ≡⟨⟩

                         ⌜ m ⌝ ·ᶜ
                         (wkConₘ (stepn id 3) δ ∙ boolrecᵍ-nc₁ ∙ 𝟘) +ᶜ
                         (𝟘ᶜ ∙ ⌜ m ᵐ· is-𝕨 ⌝)                           ∎))
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
             ⌜ m ⌝ · boolrecᵍ-pr · 𝟙 ∙ ⌜ m ⌝ · boolrecᵍ-pr               ≈⟨ ≈ᶜ-refl ∙ PE.cong (_·_ _) (·-identityʳ _) ∙ PE.refl ⟩

             nrᶜ boolrecᵍ-nc₂ 𝟘 γ₃
               (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ (⌜ m ⌝ ·ᶜ δ) 𝟘ᶜ) 𝟘ᶜ ∙
             ⌜ m ⌝ · (nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 𝟙 ∧ 𝟙) ∙
             ⌜ m ⌝ · (nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 𝟙 ∧ 𝟙)                       ≤⟨ ≤ᶜ-refl ∙ ·-monotoneʳ (∧-decreasingˡ _ _) ∙
                                                                            ·-monotoneʳ (∧-decreasingʳ _ _) ⟩
             nrᶜ boolrecᵍ-nc₂ 𝟘 γ₃
               (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ (⌜ m ⌝ ·ᶜ δ) 𝟘ᶜ) 𝟘ᶜ ∙
             ⌜ m ⌝ · nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 𝟙 ∙ ⌜ m ⌝ · 𝟙                 ≈⟨ ≈ᶜ-refl ∙ ⌜⌝-·-comm m ⟩

             nrᶜ boolrecᵍ-nc₂ 𝟘 γ₃
               (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ (⌜ m ⌝ ·ᶜ δ) 𝟘ᶜ) 𝟘ᶜ ∙
             ⌜ m ⌝ · nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 𝟙 ∙ 𝟙 · ⌜ m ⌝                 ≈⟨ ≈ᶜ-refl ∙ ≡nr-𝟘-𝟘-⌜⌝ m ∙ PE.sym (+-identityˡ _) ⟩

             nrᶜ boolrecᵍ-nc₂ 𝟘 γ₃
               (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ (⌜ m ⌝ ·ᶜ δ) 𝟘ᶜ) 𝟘ᶜ ∙
             nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 ⌜ m ⌝ ∙ 𝟘 + 𝟙 · ⌜ m ⌝                 ≈˘⟨ +ᶜ-identityʳ _ ∙ PE.cong (flip _+_ _) nr-𝟘 ⟩

             (nrᶜ boolrecᵍ-nc₂ 𝟘 γ₃
                (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ (⌜ m ⌝ ·ᶜ δ) 𝟘ᶜ) 𝟘ᶜ ∙
              nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 ⌜ m ⌝ ∙ nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 𝟘) +ᶜ
             (𝟘ᶜ ∙ 𝟙 · ⌜ m ⌝)                                            ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _ ∙ ·⌜ᵐ·⌝ m) ⟩

             nrᶜ boolrecᵍ-nc₂ 𝟘 (wkConₘ (stepn id 2) γ₃)
               (wkConₘ (stepn id 2)
                  (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ (⌜ m ⌝ ·ᶜ δ) 𝟘ᶜ))
               (𝟘ᶜ ∙ ⌜ m ⌝ ∙ 𝟘) +ᶜ
             𝟙 ·ᶜ (𝟘ᶜ ∙ ⌜ m ᵐ· 𝟙 ⌝)                                      ∎))
       ▸A ok₁)
    (begin
       nrᶜ boolrecᵍ-nc₂ 𝟘 γ₃
         (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ (⌜ m ⌝ ·ᶜ δ) 𝟘ᶜ) 𝟘ᶜ +ᶜ
       boolrecᵍ-pr ·ᶜ γ₄                                                 ≈⟨ +ᶜ-comm _ _ ⟩

       boolrecᵍ-pr ·ᶜ γ₄ +ᶜ
       nrᶜ boolrecᵍ-nc₂ 𝟘 γ₃ (nrᶜ boolrecᵍ-nc₁ 𝟘 γ₂ (⌜ m ⌝ ·ᶜ δ) 𝟘ᶜ) 𝟘ᶜ  ∎)
    where
    open ≤ᶜ-reasoning

    opaque
      unfolding Boolᵍ

      Π-lemma :
        𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ ▸[ 𝟘ᵐ? ] t →
        𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝ ∙ 𝟘 ▸[ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ] u →
        wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · (Boolᵍ + p) ▸[ 𝟘ᵐ? ]
          Π 𝟙 , p ▷ Erased (OK t) ▹ Target (2+ k) A u (var x0)
      Π-lemma {k} ▸t ▸u = sub
        (ΠΣₘ (▸Erased (B.▸OK ▸t)) $
         sub
           (▸Target ▸A ▸u var $ begin
              ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝ ·ᶜ (𝟘ᶜ ∙ 𝟙 ∙ 𝟙)             ≈⟨ ·ᶜ-zeroʳ _ ∙ ·-identityʳ _ ∙ ·-identityʳ _ ⟩

              𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝  ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityˡ _ ⟩

              𝟘ᶜ +ᶜ 𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝ + 𝟘 ∙ 𝟘 +
              ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝                             ∎)
           (begin
              wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · p ∙ ⌜ 𝟘ᵐ? ⌝ · p  ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityˡ _ ∙ +-identityˡ _ ⟩

              (wkConₘ (stepn id k) γ₁ ∙ 𝟘 ∙ 𝟘) +ᶜ
              (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · p ∙ ⌜ 𝟘ᵐ? ⌝ · p)                    ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _ ∙ ·-identityʳ _ ∙ ·-identityʳ _) ⟩

              wkConₘ (stepn id (2+ k)) γ₁ +ᶜ
              (⌜ 𝟘ᵐ? ⌝ · p) ·ᶜ (𝟘ᶜ ∙ 𝟙 ∙ 𝟙)                       ∎))
        (begin
           wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · (Boolᵍ + p)          ≈⟨ ≈ᶜ-refl ∙ ·-distribˡ-+ _ _ _ ⟩

           wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · Boolᵍ + ⌜ 𝟘ᵐ? ⌝ · p  ≈⟨ ≈ᶜ-sym (+ᶜ-identityˡ _) ∙ PE.cong (flip _+_ _) (≡nr-𝟘-𝟘-⌜𝟘ᵐ?⌝ 𝟘ᵐ?) ⟩

           (𝟘ᶜ +ᶜ wkConₘ (stepn id k) γ₁) ∙ Boolᵍ + ⌜ 𝟘ᵐ? ⌝ · p    ≡⟨⟩

           (𝟘ᶜ ∙ nr OKᵍ 𝟘 𝟘 𝟘 ⌜ 𝟘ᵐ? ⌝) +ᶜ
           (wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · p)                  ≈˘⟨ +ᶜ-congʳ $ nrᶜ-𝟘ᶜ ∙ PE.refl ⟩

           nrᶜ OKᵍ 𝟘 𝟘ᶜ 𝟘ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝) +ᶜ
           (wkConₘ (stepn id k) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · p)                  ∎)

    lam-lemma :
      𝟘ᶜ ▸[ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ] t →
      γ ▸[ m ] u →
      wkConₘ (stepn id k) γ ▸[ m ]
        lam 𝟙
          (erasedrec p (Target (2+ k) A t (var x0))
             (unitrec 0 𝟘 𝟘
                (Target (3+ k) A (wk1 t) E.[ var x0 ]) (var x0)
                (wk[ 2+ k ]′ u))
             (var x0))
    lam-lemma {k} {γ} ▸t ▸u =
      lamₘ $
      sub
        (▸erasedrec (λ ()) (λ _ → ok₂) (λ _ → ok₃)
           (λ _ →
              wkConₘ (stepn id (1+ k)) γ₁ ,
              sub
                (▸Target ▸A ▸t var $ begin
                   ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝ ·ᶜ (𝟘ᶜ ∙ 𝟙)   ≈⟨ ·ᶜ-zeroʳ _ ∙ ·-identityʳ _ ⟩
                   𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝          ≈˘⟨ +ᶜ-identityˡ _ ⟩
                   𝟘ᶜ +ᶜ (𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝)  ∎)
                (begin
                   wkConₘ (stepn id (1+ k)) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · p          ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityˡ _ ⟩

                   wkConₘ (stepn id (2+ k)) γ₁ +ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · p)  ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _ ∙ ·-identityʳ _) ⟩

                   wkConₘ (stepn id (2+ k)) γ₁ +ᶜ
                   (⌜ 𝟘ᵐ? ⌝ · p) ·ᶜ (𝟘ᶜ ∙ 𝟙)                          ∎))
           (sub
              (unitrecₘ var (wkUsage (stepn id (2+ k)) ▸u)
                 (sub
                    (▸Target ▸A (wkUsage (step id) ▸t) (▸[] var) $
                     begin
                       ⌜ ⌞ ⌜ 𝟘ᵐ? ⌝ · p ⌟ ⌝ ·ᶜ 𝟘ᶜ  ≈⟨ ·ᶜ-zeroʳ _ ⟩
                       𝟘ᶜ                         ≈˘⟨ +ᶜ-identityˡ _ ⟩
                       𝟘ᶜ +ᶜ 𝟘ᶜ                   ∎)
                    (begin
                       wkConₘ (stepn id (2+ k)) γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩

                       wkConₘ (stepn id (3+ k)) γ₁                ≈˘⟨ +ᶜ-identityʳ _ ⟩

                       wkConₘ (stepn id (3+ k)) γ₁ +ᶜ 𝟘ᶜ          ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _) ⟩

                       wkConₘ (stepn id (3+ k)) γ₁ +ᶜ
                       (⌜ 𝟘ᵐ? ⌝ · p) ·ᶜ 𝟘ᶜ                        ∎))
                 ok₄)
              (begin
                 wkConₘ (stepn id (2+ k)) γ                            ≈˘⟨ +ᶜ-identityˡ _ ⟩
                 𝟘ᶜ +ᶜ wkConₘ (stepn id (2+ k)) γ                      ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
                 𝟘 ·ᶜ (𝟘ᶜ ∙ ⌜ m ᵐ· 𝟘 ⌝) +ᶜ wkConₘ (stepn id (2+ k)) γ  ∎))
           var)
        (begin
           wkConₘ (stepn id k) γ ∙ ⌜ m ⌝ · 𝟙                   ≈⟨ ≈ᶜ-sym (+ᶜ-identityʳ _) ∙ PE.trans (·-identityʳ _) (PE.sym (+-identityˡ _)) ⟩
           wkConₘ (stepn id (1+ k)) γ +ᶜ (𝟘ᶜ ∙ ⌜ m ⌝)          ≈˘⟨ +ᶜ-congˡ (≈ᶜ-refl ∙ PE.cong ⌜_⌝ (ᵐ·-identityʳ {m = m})) ⟩
           wkConₘ (stepn id (1+ k)) γ +ᶜ (𝟘ᶜ ∙ ⌜ m ᵐ· 𝟙 ⌝)     ≡⟨⟩
           wkConₘ (stepn id (1+ k)) γ +ᶜ (𝟘ᶜ ∙ ⌜ m ᵐ· is-𝕨 ⌝)  ∎)

opaque

  -- A variant of ▸boolrec that can be used if the nr
  -- function satisfies Linearity-like-nr-for-𝟘 and
  -- Linearity-like-nr-for-𝟙.
  --
  -- Note that one of the assumptions is that one kind of erased match
  -- is allowed for unitrec.

  ▸boolrec′ :
    Linearity-like-nr-for-𝟘 →
    Linearity-like-nr-for-𝟙 →
    Prodrec-allowed m 𝟙 𝟙 p →
    Prodrec-allowed m 𝟙 𝟘 p →
    Unitrec-allowed m 𝟙 p →
    Unitrec-allowed m 𝟘 𝟘 →
    Emptyrec-allowed m 𝟘 →
    Starˢ-sink →
    γ₁ ∙ ⌜ 𝟘ᵐ? ⌝ · p ▸[ 𝟘ᵐ? ] A →
    γ₂ ▸[ m ] t →
    γ₃ ▸[ m ] u →
    γ₄ ▸[ m ] v →
    γ₂ ∧ᶜ γ₃ +ᶜ γ₄ ▸[ m ] boolrec p A t u v
  ▸boolrec′
    {m} {γ₂} {γ₃} {γ₄}
    lin₀ lin₁ ok₁ ok₂ ok₃ ok₄ ok₅ ok₆ ▸A ▸t ▸u ▸v = sub
    (▸boolrec
       (PE.subst₃ (Prodrec-allowed m)
          (PE.sym $ boolrecᵍ-pr≡ lin₀ lin₁) PE.refl PE.refl ok₁)
       ok₂ ok₃ ok₄ ok₅ ok₆ ▸A ▸t ▸u ▸v)
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
