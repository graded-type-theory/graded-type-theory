------------------------------------------------------------------------
-- Properties of the usage relation.
------------------------------------------------------------------------

import Graded.Modality
import Graded.Mode
open import Graded.Usage.Restrictions

module Graded.Usage.Properties
  {a b} {M : Set a} {Mode : Set b}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (open Graded.Mode Mode 𝕄)
  {𝐌 : IsMode}
  (R : Usage-restrictions 𝕄 𝐌)
  where

open Modality 𝕄
open IsMode 𝐌
open Usage-restrictions R

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Usage R
open import Graded.Usage.Inversion R
open import Graded.Usage.Erased-matches
open import Graded.Usage.Restrictions.Natrec 𝕄
import Graded.Usage.Restrictions.Instance
open import Graded.Usage.Weakening R
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄

import Definition.Typed
open import Definition.Typed.Restrictions 𝕄
open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Tools.Bool using (Bool; T)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat as N using (Nat; 1+; _<′_)
open import Tools.Product
open import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum
import Tools.Reasoning.Equivalence
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

private
  module CR {n} = Tools.Reasoning.PartialOrder (≤ᶜ-poset {n = n})

private
  variable
    α n l : Nat
    ∇ : DCon (Term 0) n
    ξ : DExt _ _ _
    Γ : Con Term n
    A B F t u v w : Term n
    G : Term (1+ n)
    γ γ₁ γ₂ γ₃ γ₄ γ₅ γ₆ δ η θ χ : Conₘ n
    p q r s z : M
    m m₁ m₂ m₃ m′ : Mode
    -- b : Bool
    ok : T _
    x : Fin n
    sem : Some-erased-matches
    nm : Natrec-mode

------------------------------------------------------------------------
-- Lemmas related to _◂_∈_

-- Variables only have one annotation in a context

unique-var-usage : x ◂ p ∈ γ → x ◂ q ∈ γ → p PE.≡ q
unique-var-usage here here = PE.refl
unique-var-usage (there x) (there y) = unique-var-usage x y

-- Variable lookup and the usage relation for variables match

var-usage-lookup : x ◂ p ∈ γ → γ ⟨ x ⟩ ≡ p
var-usage-lookup here = PE.refl
var-usage-lookup (there x) = var-usage-lookup x

-- An alternative characterisation of _◂_∈_.

◂∈⇔ : x ◂ p ∈ γ ⇔ γ ⟨ x ⟩ ≡ p
◂∈⇔ = to , from
  where
  to : x ◂ p ∈ γ → γ ⟨ x ⟩ ≡ p
  to here      = refl
  to (there q) = to q

  from : γ ⟨ x ⟩ ≡ p → x ◂ p ∈ γ
  from {γ = ε}     {x = ()}
  from {γ = _ ∙ _} {x = x0}   refl = here
  from {γ = _ ∙ _} {x = _ +1} eq   = there (from eq)

opaque

  -- An inversion lemma for _◂_∈_.

  x0◂∈ : x0 ◂ p ∈ γ ∙ q → p ≡ q
  x0◂∈ here = refl

opaque

  -- An inversion lemma for _◂_∈_.

  +1◂∈ : (x +1) ◂ p ∈ γ ∙ q → x ◂ p ∈ γ
  +1◂∈ (there x∈) = x∈

------------------------------------------------------------------------
-- Replacing one usage mode with another

-- γ ▸[_] t respects _≡_.

▸-cong : m₁ ≡ m₂ → γ ▸[ m₁ ] t → γ ▸[ m₂ ] t
▸-cong = subst (_ ▸[_] _)

-- If the mode structure is trivial, then one can convert usage modes freely.

▸-trivialᵐ : Trivialᵐ → γ ▸[ m ] t → γ ▸[ m′ ] t
▸-trivialᵐ ok =
  ▸-cong (≡-trivialᵐ ok)

-- If the modality is trivial, then one can convert usage modes
-- freely.

▸-trivial : Trivial → γ ▸[ m ] t → γ ▸[ m′ ] t
▸-trivial 𝟙≡𝟘 = ▸-trivialᵐ (Trivial→Trivialᵐ 𝟙≡𝟘)

------------------------------------------------------------------------
-- -- The lemma ▸-· and some related results


opaque mutual

  ▸-𝟘 : γ ▸[ m ] t → ⌜ 𝟘ᵐ ⌝ ·ᶜ γ ▸[ 𝟘ᵐ ] t
  ▸-𝟘 ▸t = ▸-cong (·ᵐ-zeroˡ _) (▸-· {m′ = 𝟘ᵐ} ▸t)

  -- The relation _▸[_]_ respects multiplication (in a certain sense).

  ▸-· : γ ▸[ m ] t → ⌜ m′ ⌝ ·ᶜ γ ▸[ m′ ·ᵐ m ] t
  ▸-· {m} {m′} = λ where
      (sub ▸t γ≤δ) →
        sub (▸-· ▸t) (·ᶜ-monotoneʳ γ≤δ)
      (var {x}) →
        sub var $ begin
          ⌜ m′ ⌝ ·ᶜ (𝟘ᶜ , x ≔ ⌜ m ⌝)        ≡˘⟨ update-distrib-·ᶜ _ _ _ x ⟩
          ⌜ m′ ⌝ ·ᶜ 𝟘ᶜ , x ≔ ⌜ m′ ⌝ · ⌜ m ⌝ ≈⟨ update-cong (·ᶜ-zeroʳ _) (sym (⌜·ᵐ⌝ m′)) ⟩
          𝟘ᶜ , x ≔ ⌜ m′ ·ᵐ m ⌝              ∎
      defn → sub-≈ᶜ defn (·ᶜ-zeroʳ _)
      Uₘ →
        sub-≈ᶜ Uₘ (·ᶜ-zeroʳ _)
      Emptyₘ →
        sub-≈ᶜ Emptyₘ (·ᶜ-zeroʳ _)
      (emptyrecₘ {γ} {p} ▸t ▸A ok) →
        sub-≈ᶜ (emptyrecₘ (▸-ᵐ· ▸t) ▸A (Emptyrec-allowed-·ᵐ ok)) (⌜⌝·ᶜ-comm _ _ _)
      Unitₘ →
        sub-≈ᶜ Unitₘ (·ᶜ-zeroʳ _)
      (starˢₘ {γ} ok) →
        sub (starˢₘ ok) $ begin
          ⌜ m′ ⌝ ·ᶜ ⌜ m ⌝ ·ᶜ γ ≈˘⟨ ·ᶜ-assoc _ _ _ ⟩
          (⌜ m′ ⌝ · ⌜ m ⌝) ·ᶜ γ ≈˘⟨ ·ᶜ-congʳ (⌜·ᵐ⌝ m′) ⟩
          ⌜ m′ ·ᵐ m ⌝ ·ᶜ γ      ∎
      starʷₘ →
        sub-≈ᶜ starʷₘ (·ᶜ-zeroʳ _)
      (unitrecₘ {γ} {p} {δ} ▸t ▸u ▸A ok) →
        sub (unitrecₘ (▸-ᵐ· ▸t) (▸-· ▸u) ▸A (Unitrec-allowed-·ᵐ ok)) $ begin
         ⌜ m′ ⌝ ·ᶜ (p ·ᶜ γ +ᶜ δ)         ≈⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
         ⌜ m′ ⌝ ·ᶜ p ·ᶜ γ +ᶜ ⌜ m′ ⌝ ·ᶜ δ ≈⟨ +ᶜ-congʳ (⌜⌝·ᶜ-comm _ _ _) ⟩
         p ·ᶜ ⌜ m′ ⌝ ·ᶜ γ +ᶜ ⌜ m′ ⌝ ·ᶜ δ ∎
      (ΠΣₘ ▸A ▸B) →
        sub-≈ᶜ (ΠΣₘ (▸-· ▸A) (▸-·-∙ ▸B))
          (·ᶜ-distribˡ-+ᶜ _ _ _)
      (lamₘ {γ} {p} ▸t) →
        lamₘ (▸-·-∙ ▸t)
      (_∘ₘ_ {γ} {δ} {p} ▸t ▸u) →
        sub (▸-· ▸t ∘ₘ ▸-ᵐ· ▸u) $ begin
          ⌜ m′ ⌝ ·ᶜ (γ +ᶜ p ·ᶜ δ)         ≈⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
          ⌜ m′ ⌝ ·ᶜ γ +ᶜ ⌜ m′ ⌝ ·ᶜ p ·ᶜ δ ≈⟨ +ᶜ-congˡ (⌜⌝·ᶜ-comm _ _ _) ⟩
          ⌜ m′ ⌝ ·ᶜ γ +ᶜ p ·ᶜ ⌜ m′ ⌝ ·ᶜ δ ∎
      (prodˢₘ {γ} {p} {δ} ▸t ▸u) →
        sub (prodˢₘ (▸-ᵐ· ▸t) (▸-· ▸u)) $ begin
        ⌜ m′ ⌝ ·ᶜ (p ·ᶜ γ ∧ᶜ δ)         ≈⟨ ·ᶜ-distribˡ-∧ᶜ _ _ _ ⟩
        ⌜ m′ ⌝ ·ᶜ p ·ᶜ γ ∧ᶜ ⌜ m′ ⌝ ·ᶜ δ ≈⟨ ∧ᶜ-congʳ (⌜⌝·ᶜ-comm _ _ _) ⟩
        p ·ᶜ ⌜ m′ ⌝ ·ᶜ γ ∧ᶜ ⌜ m′ ⌝ ·ᶜ δ ∎
      (fstₘ m″ ▸t refl ok) →
        fstₘ _ (▸-cong (sym (·ᵐ-ᵐ·-assoc m′)) (▸-· ▸t))
          (·ᵐ-ᵐ·-assoc m′) (ok ∘→ ⌜⌝-·ᵐ-𝟘ʳ)
      (sndₘ ▸t) →
        sndₘ (▸-· ▸t)
      (prodʷₘ {γ} {p} {δ} ▸t ▸u) →
        sub (prodʷₘ (▸-ᵐ· ▸t) (▸-· ▸u)) $ begin
        ⌜ m′ ⌝ ·ᶜ (p ·ᶜ γ +ᶜ δ)         ≈⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
        ⌜ m′ ⌝ ·ᶜ p ·ᶜ γ +ᶜ ⌜ m′ ⌝ ·ᶜ δ ≈⟨ +ᶜ-congʳ (⌜⌝·ᶜ-comm _ _ _) ⟩
        p ·ᶜ ⌜ m′ ⌝ ·ᶜ γ +ᶜ ⌜ m′ ⌝ ·ᶜ δ ∎
      (prodrecₘ {γ} {r} {δ} {p} ▸t ▸u ▸A ok) →
        sub (prodrecₘ (▸-ᵐ· ▸t) (▸-·-∙₂ ▸u) ▸A (Prodrec-allowed-·ᵐ ok)) $ begin
          ⌜ m′ ⌝ ·ᶜ (r ·ᶜ γ +ᶜ δ)         ≈⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
          ⌜ m′ ⌝ ·ᶜ r ·ᶜ γ +ᶜ ⌜ m′ ⌝ ·ᶜ δ ≈⟨ +ᶜ-congʳ (⌜⌝·ᶜ-comm _ _ _) ⟩
          r ·ᶜ ⌜ m′ ⌝ ·ᶜ γ +ᶜ ⌜ m′ ⌝ ·ᶜ δ ∎
      ℕₘ →
        sub-≈ᶜ ℕₘ (·ᶜ-zeroʳ _)
      zeroₘ →
        sub-≈ᶜ zeroₘ (·ᶜ-zeroʳ _)
      (sucₘ ▸t) →
        sucₘ (▸-· ▸t)
      (natrecₘ ▸z ▸s ▸n ▸A) →
        sub-≈ᶜ (natrecₘ (▸-· ▸z) (▸-·-∙₂ ▸s) (▸-· ▸n) ▸A) ⌜⌝-·ᶜ-nrᶜ
      (natrec-no-nrₘ {γ} {δ} {p} {r} {η} {χ} ▸z ▸s ▸n ▸A le₁ le₂ le₃ le₄) →
        natrec-no-nrₘ (▸-· ▸z) (▸-·-∙₂ ▸s) (▸-· ▸n) ▸A
          (·ᶜ-monotoneʳ le₁) (·ᶜ-monotoneʳ ∘→ le₂)
          (·ᶜ-monotoneʳ ∘→ le₃) $ begin
            ⌜ m′ ⌝ ·ᶜ χ                                         ≤⟨ ·ᶜ-monotoneʳ le₄ ⟩
            ⌜ m′ ⌝ ·ᶜ (δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ)                   ≈⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
            ⌜ m′ ⌝ ·ᶜ δ +ᶜ ⌜ m′ ⌝ ·ᶜ (p ·ᶜ η +ᶜ r ·ᶜ χ)         ≈⟨ +ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
            ⌜ m′ ⌝ ·ᶜ δ +ᶜ ⌜ m′ ⌝ ·ᶜ p ·ᶜ η +ᶜ ⌜ m′ ⌝ ·ᶜ r ·ᶜ χ ≈⟨ +ᶜ-congˡ (+ᶜ-cong (⌜⌝·ᶜ-comm _ _ _) (⌜⌝·ᶜ-comm _ _ _)) ⟩
            ⌜ m′ ⌝ ·ᶜ δ +ᶜ p ·ᶜ ⌜ m′ ⌝ ·ᶜ η +ᶜ r ·ᶜ ⌜ m′ ⌝ ·ᶜ χ ∎
      (natrec-no-nr-glbₘ {η} {χ} {x} ▸z ▸s ▸n ▸A x-GLB χ-GLB) →
        sub (natrec-no-nr-glbₘ (▸-· ▸z) (▸-·-∙₂ ▸s) (▸-· ▸n) ▸A x-GLB
              (GLBᶜ-congˡ ⌜⌝-·ᶜ-nrᵢᶜ (·ᶜ-GLBᶜˡ χ-GLB))) $ begin
            ⌜ m′ ⌝ ·ᶜ (x ·ᶜ η +ᶜ χ)         ≈⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
            ⌜ m′ ⌝ ·ᶜ x ·ᶜ η +ᶜ ⌜ m′ ⌝ ·ᶜ χ ≈⟨ +ᶜ-congʳ (⌜⌝·ᶜ-comm _ _ _) ⟩
            x ·ᶜ ⌜ m′ ⌝ ·ᶜ η +ᶜ ⌜ m′ ⌝ ·ᶜ χ ∎
      (Idₘ {γ} {δ} {η} ok ▸A ▸t ▸u) →
        sub (Idₘ ok (▸-· ▸A) (▸-· ▸t) (▸-· ▸u)) $ begin
          ⌜ m′ ⌝ ·ᶜ (γ +ᶜ δ +ᶜ η)                   ≈⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
          ⌜ m′ ⌝ ·ᶜ γ +ᶜ ⌜ m′ ⌝ ·ᶜ (δ +ᶜ η)         ≈⟨ +ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
          ⌜ m′ ⌝ ·ᶜ γ +ᶜ ⌜ m′ ⌝ ·ᶜ δ +ᶜ ⌜ m′ ⌝ ·ᶜ η ∎
      (Id₀ₘ ok ▸A ▸t ▸u) →
        sub-≈ᶜ (Id₀ₘ ok ▸A ▸t ▸u) (·ᶜ-zeroʳ _)
      rflₘ →
        sub-≈ᶜ rflₘ (·ᶜ-zeroʳ _)
      (Jₘ {p} {q} {γ₂} {γ₃} {γ₄} {γ₅} {γ₆} x x₁ ▸A ▸t ▸B ▸u ▸v ▸w) →
        case J-view p q (m′ ·ᵐ m) of λ where
          (is-all x₂) →
            let ▸B′ = sub-≈ᶜ (▸-𝟘 ▸B) (≈ᶜ-refl ∙ lemma″ ∙ lemma″)
            in  sub (J₀ₘ₂ x₂ ▸A (▸-𝟘 ▸t) ▸B′ (▸-· ▸u) (▸-𝟘 ▸v) (▸-𝟘 ▸w)) $ begin
              ⌜ m′ ⌝ ·ᶜ ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆) ≤⟨ ·ᶜ-monotoneʳ ω·ᶜ+ᶜ≤ω·ᶜʳ ⟩
              ⌜ m′ ⌝ ·ᶜ ω ·ᶜ (γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)       ≤⟨ ·ᶜ-monotoneʳ ω·ᶜ+ᶜ≤ω·ᶜʳ ⟩
              ⌜ m′ ⌝ ·ᶜ ω ·ᶜ (γ₄ +ᶜ γ₅ +ᶜ γ₆)             ≤⟨ ·ᶜ-monotoneʳ ω·ᶜ+ᶜ≤ω·ᶜˡ  ⟩
              ⌜ m′ ⌝ ·ᶜ ω ·ᶜ γ₄                           ≤⟨ ·ᶜ-monotoneʳ ω·ᶜ-decreasing ⟩
              ⌜ m′ ⌝ ·ᶜ γ₄                                ∎
          (is-some-yes x₂ (refl , refl)) →
            let ▸B′ = sub-≈ᶜ (▸-· ▸B) (≈ᶜ-refl ∙ lemma′ ∙ lemma′)
            in  sub (J₀ₘ₁ x₂ refl refl ▸A (▸-𝟘 ▸t) ▸B′ (▸-· ▸u) (▸-𝟘 ▸v) (▸-𝟘 ▸w)) $ begin
              ⌜ m′ ⌝ ·ᶜ ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆) ≤⟨ ·ᶜ-monotoneʳ ω·ᶜ+ᶜ≤ω·ᶜʳ ⟩
              ⌜ m′ ⌝ ·ᶜ ω ·ᶜ (γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)       ≈˘⟨ ·ᶜ-congˡ (·ᶜ-congˡ (+ᶜ-assoc _ _ _)) ⟩
              ⌜ m′ ⌝ ·ᶜ ω ·ᶜ ((γ₃ +ᶜ γ₄) +ᶜ γ₅ +ᶜ γ₆)     ≤⟨ ·ᶜ-monotoneʳ ω·ᶜ+ᶜ≤ω·ᶜˡ ⟩
              ⌜ m′ ⌝ ·ᶜ ω ·ᶜ (γ₃ +ᶜ γ₄)                  ≈⟨ ⌜⌝·ᶜ-comm _ _ _ ⟩
              ω ·ᶜ ⌜ m′ ⌝ ·ᶜ (γ₃ +ᶜ γ₄)                  ≈⟨ ·ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
              ω ·ᶜ (⌜ m′ ⌝ ·ᶜ γ₃ +ᶜ ⌜ m′ ⌝ ·ᶜ γ₄)        ∎
          (is-other x₂ x₃) →
            sub (Jₘ x₂ x₃ ▸A (▸-· ▸t) (▸-·-∙₂ ▸B) (▸-· ▸u) (▸-· ▸v) (▸-· ▸w)) $ begin
              ⌜ m′ ⌝ ·ᶜ ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)                                         ≈⟨ ⌜⌝·ᶜ-comm _ _ _ ⟩
              ω ·ᶜ (⌜ m′ ⌝ ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆))                                       ≈⟨ ·ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
              ω ·ᶜ (⌜ m′ ⌝ ·ᶜ γ₂ +ᶜ ⌜ m′ ⌝ ·ᶜ (γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆))                             ≈⟨ ·ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _)) ⟩
              ω ·ᶜ (⌜ m′ ⌝ ·ᶜ γ₂ +ᶜ ⌜ m′ ⌝ ·ᶜ γ₃ +ᶜ ⌜ m′ ⌝ ·ᶜ (γ₄ +ᶜ γ₅ +ᶜ γ₆))                   ≈⟨ ·ᶜ-congˡ (+ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _))) ⟩
              ω ·ᶜ (⌜ m′ ⌝ ·ᶜ γ₂ +ᶜ ⌜ m′ ⌝ ·ᶜ γ₃ +ᶜ ⌜ m′ ⌝ ·ᶜ γ₄ +ᶜ ⌜ m′ ⌝ ·ᶜ (γ₅ +ᶜ γ₆))         ≈⟨ ·ᶜ-congˡ (+ᶜ-congˡ (+ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _)))) ⟩
              ω ·ᶜ (⌜ m′ ⌝ ·ᶜ γ₂ +ᶜ ⌜ m′ ⌝ ·ᶜ γ₃ +ᶜ ⌜ m′ ⌝ ·ᶜ γ₄ +ᶜ ⌜ m′ ⌝ ·ᶜ γ₅ +ᶜ ⌜ m′ ⌝ ·ᶜ γ₆) ∎
      (J₀ₘ₁ {γ₃} {γ₄} x refl refl ▸A ▸t ▸B ▸u ▸v ▸w) →
        case erased-matches-for-J-some·ᵐ {m′ = m′} x of λ where
          (inj₁ ≡all) →
            let ▸B′ = ▸-𝟘 ▸B
            in  sub (J₀ₘ₂ ≡all ▸A ▸t ▸B′ (▸-· ▸u) ▸v ▸w) $ begin
              ⌜ m′ ⌝ ·ᶜ ω ·ᶜ (γ₃ +ᶜ γ₄) ≤⟨ ·ᶜ-monotoneʳ ω·ᶜ+ᶜ≤ω·ᶜʳ ⟩
              ⌜ m′ ⌝ ·ᶜ ω ·ᶜ γ₄         ≤⟨ ·ᶜ-monotoneʳ ω·ᶜ-decreasing ⟩
              ⌜ m′ ⌝ ·ᶜ γ₄              ∎
          (inj₂ ≡some) →
            let ▸B′ = sub-≈ᶜ (▸-· ▸B) (≈ᶜ-refl ∙ sym (·-zeroʳ _) ∙ sym (·-zeroʳ _))
            in  sub (J₀ₘ₁ ≡some refl refl ▸A ▸t ▸B′ (▸-· ▸u) ▸v ▸w) $ begin
              ⌜ m′ ⌝ ·ᶜ ω ·ᶜ (γ₃ +ᶜ γ₄)           ≈⟨ ⌜⌝·ᶜ-comm _ _ _ ⟩
              ω ·ᶜ ⌜ m′ ⌝ ·ᶜ (γ₃ +ᶜ γ₄)           ≈⟨ ·ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
              ω ·ᶜ (⌜ m′ ⌝ ·ᶜ γ₃ +ᶜ ⌜ m′ ⌝ ·ᶜ γ₄) ∎
      (J₀ₘ₂ x ▸A ▸t ▸B ▸u ▸v ▸w) →
        J₀ₘ₂ (erased-matches-for-J-all·ᵐ x) ▸A ▸t ▸B (▸-· ▸u) ▸v ▸w
      (Kₘ {p} {γ₂} {γ₃} {γ₄} {γ₅} x x₁ ▸A ▸t ▸B ▸u ▸v) →
        case K-view p (m′ ·ᵐ m) of λ where
          (is-all x₂) →
            let ▸B′ = sub-≈ᶜ (▸-𝟘 ▸B) (≈ᶜ-refl ∙ lemma″)
            in  sub (K₀ₘ₂ x₂ ▸A (▸-𝟘 ▸t) ▸B′ (▸-· ▸u) (▸-𝟘 ▸v)) $ begin
              ⌜ m′ ⌝ ·ᶜ ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅) ≤⟨ ·ᶜ-monotoneʳ ω·ᶜ+ᶜ≤ω·ᶜʳ ⟩
              ⌜ m′ ⌝ ·ᶜ ω ·ᶜ (γ₃ +ᶜ γ₄ +ᶜ γ₅)       ≤⟨ ·ᶜ-monotoneʳ ω·ᶜ+ᶜ≤ω·ᶜʳ ⟩
              ⌜ m′ ⌝ ·ᶜ ω ·ᶜ (γ₄ +ᶜ γ₅)             ≤⟨ ·ᶜ-monotoneʳ ω·ᶜ+ᶜ≤ω·ᶜˡ ⟩
              ⌜ m′ ⌝ ·ᶜ ω ·ᶜ γ₄                     ≤⟨ ·ᶜ-monotoneʳ ω·ᶜ-decreasing ⟩
              ⌜ m′ ⌝ ·ᶜ γ₄                          ∎
          (is-some-yes x₂ refl) →
            let ▸B′ = sub-≈ᶜ (▸-· ▸B) (≈ᶜ-refl ∙ lemma′)
            in  sub (K₀ₘ₁ x₂ refl ▸A (▸-𝟘 ▸t) ▸B′ (▸-· ▸u) (▸-𝟘 ▸v)) $ begin
             ⌜ m′ ⌝ ·ᶜ ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅) ≤⟨ ·ᶜ-monotoneʳ ω·ᶜ+ᶜ≤ω·ᶜʳ ⟩
             ⌜ m′ ⌝ ·ᶜ ω ·ᶜ (γ₃ +ᶜ γ₄ +ᶜ γ₅)       ≈˘⟨ ·ᶜ-congˡ (·ᶜ-congˡ (+ᶜ-assoc _ _ _)) ⟩
             ⌜ m′ ⌝ ·ᶜ ω ·ᶜ ((γ₃ +ᶜ γ₄) +ᶜ γ₅)     ≤⟨ ·ᶜ-monotoneʳ ω·ᶜ+ᶜ≤ω·ᶜˡ ⟩
             ⌜ m′ ⌝ ·ᶜ ω ·ᶜ (γ₃ +ᶜ γ₄)             ≈⟨ ⌜⌝·ᶜ-comm _ _ _ ⟩
             ω ·ᶜ ⌜ m′ ⌝ ·ᶜ (γ₃ +ᶜ γ₄)             ≈⟨ ·ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
             ω ·ᶜ (⌜ m′ ⌝ ·ᶜ γ₃ +ᶜ ⌜ m′ ⌝ ·ᶜ γ₄) ∎
          (is-other x₂ x₃) →
            sub (Kₘ x₂ x₃ ▸A (▸-· ▸t) (▸-·-∙ ▸B) (▸-· ▸u) (▸-· ▸v)) $ begin
            ⌜ m′ ⌝ ·ᶜ ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅)                               ≈⟨ ⌜⌝·ᶜ-comm _ _ _ ⟩
            ω ·ᶜ ⌜ m′ ⌝ ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅)                               ≈⟨ ·ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
            ω ·ᶜ (⌜ m′ ⌝ ·ᶜ γ₂ +ᶜ ⌜ m′ ⌝ ·ᶜ (γ₃ +ᶜ γ₄ +ᶜ γ₅))                   ≈⟨ ·ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _)) ⟩
            ω ·ᶜ (⌜ m′ ⌝ ·ᶜ γ₂ +ᶜ ⌜ m′ ⌝ ·ᶜ γ₃ +ᶜ ⌜ m′ ⌝ ·ᶜ (γ₄ +ᶜ γ₅))         ≈⟨ ·ᶜ-congˡ (+ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _))) ⟩
            ω ·ᶜ (⌜ m′ ⌝ ·ᶜ γ₂ +ᶜ ⌜ m′ ⌝ ·ᶜ γ₃ +ᶜ ⌜ m′ ⌝ ·ᶜ γ₄ +ᶜ ⌜ m′ ⌝ ·ᶜ γ₅) ∎
      (K₀ₘ₁ {γ₃} {γ₄} x refl ▸A ▸t ▸B ▸u ▸v) →
        case erased-matches-for-K-some·ᵐ {m′ = m′} x of λ where
          (inj₁ ≡all) →
            let ▸B′ = ▸-𝟘 ▸B
            in  sub (K₀ₘ₂ ≡all ▸A ▸t ▸B′ (▸-· ▸u) ▸v) $ begin
              ⌜ m′ ⌝ ·ᶜ ω ·ᶜ (γ₃ +ᶜ γ₄) ≤⟨ ·ᶜ-monotoneʳ ω·ᶜ+ᶜ≤ω·ᶜʳ ⟩
              ⌜ m′ ⌝ ·ᶜ ω ·ᶜ γ₄         ≤⟨ ·ᶜ-monotoneʳ ω·ᶜ-decreasing ⟩
              ⌜ m′ ⌝ ·ᶜ γ₄              ∎
          (inj₂ ≡some) →
            let ▸B′ = sub-≈ᶜ (▸-· ▸B) (≈ᶜ-refl ∙ sym (·-zeroʳ _))
            in  sub (K₀ₘ₁ ≡some refl ▸A ▸t ▸B′ (▸-· ▸u) ▸v) $ begin
              ⌜ m′ ⌝ ·ᶜ ω ·ᶜ (γ₃ +ᶜ γ₄)           ≈⟨ ⌜⌝·ᶜ-comm _ _ _ ⟩
              ω ·ᶜ ⌜ m′ ⌝ ·ᶜ (γ₃ +ᶜ γ₄)           ≈⟨ ·ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
              ω ·ᶜ (⌜ m′ ⌝ ·ᶜ γ₃ +ᶜ ⌜ m′ ⌝ ·ᶜ γ₄) ∎
      (K₀ₘ₂ x ▸A ▸t ▸B ▸u ▸v) →
        K₀ₘ₂ (erased-matches-for-K-all·ᵐ x)
          ▸A ▸t ▸B (▸-· ▸u) ▸v
      ([]-congₘ ▸A ▸t ▸u ▸v ok) →
        sub-≈ᶜ ([]-congₘ ▸A ▸t ▸u ▸v ([]-cong-allowed-mode-·ᵐ ok)) (·ᶜ-zeroʳ _)
    where
    ▸-ᵐ· : γ ▸[ m ᵐ· p ] t → ⌜ m′ ⌝ ·ᶜ γ ▸[ (m′ ·ᵐ m) ᵐ· p ] t
    ▸-ᵐ· ▸t = ▸-cong (sym (·ᵐ-ᵐ·-assoc m′)) (▸-· ▸t)
    lemma : ⌜ m′ ·ᵐ m ⌝ · p ≡ ⌜ m′ ⌝ · ⌜ m ⌝ · p
    lemma {p} = let open Tools.Reasoning.PropositionalEquality in begin
      ⌜ m′ ·ᵐ m ⌝ · p      ≡⟨ ·-congʳ (⌜·ᵐ⌝ m′) ⟩
      (⌜ m′ ⌝ · ⌜ m ⌝) · p ≡⟨ ·-assoc _ _ _ ⟩
      ⌜ m′ ⌝ · ⌜ m ⌝ · p   ∎
    ▸-·-∙ : γ ∙ ⌜ m ⌝ · p ▸[ m ] t → ⌜ m′ ⌝ ·ᶜ γ ∙ ⌜ m′ ·ᵐ m ⌝ · p ▸[ m′ ·ᵐ m ] t
    ▸-·-∙ ▸t = sub-≈ᶜ (▸-· ▸t) (≈ᶜ-refl ∙ lemma)
    ▸-·-∙₂ :
      γ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] t →
      ⌜ m′ ⌝ ·ᶜ γ ∙ ⌜ m′ ·ᵐ m ⌝ · p ∙ ⌜ m′ ·ᵐ m ⌝ · r ▸[ m′ ·ᵐ m ] t
    ▸-·-∙₂ ▸t =
      sub-≈ᶜ (▸-·-∙ ▸t) (≈ᶜ-refl ∙ lemma ∙ refl)
    lemma′ : 𝟘 ≡ ⌜ m′ ⌝ · ⌜ m ⌝ · 𝟘
    lemma′ = let open Tools.Reasoning.PropositionalEquality in begin
      𝟘                  ≡˘⟨ ·-zeroʳ _ ⟩
      ⌜ m′ ⌝ · 𝟘         ≡˘⟨ ·-congˡ (·-zeroʳ _) ⟩
      ⌜ m′ ⌝ · ⌜ m ⌝ · 𝟘 ∎
    lemma″ : ⌜ 𝟘ᵐ ⌝ · p ≡ ⌜ 𝟘ᵐ ⌝ · ⌜ m ⌝ · p
    lemma″ {p} = let open Tools.Reasoning.PropositionalEquality in begin
      ⌜ 𝟘ᵐ ⌝ · p           ≡˘⟨ ·-congʳ (⌜⌝-cong (·ᵐ-zeroˡ _)) ⟩
      ⌜ 𝟘ᵐ ·ᵐ m ⌝ · p      ≡⟨ ·-congʳ (⌜·ᵐ⌝ 𝟘ᵐ) ⟩
      (⌜ 𝟘ᵐ ⌝ · ⌜ m ⌝) · p ≡⟨ ·-assoc _ _ _ ⟩
      ⌜ 𝟘ᵐ ⌝ · ⌜ m ⌝ · p   ∎
    open ≤ᶜ-reasoning
    open Graded.Usage.Restrictions.Instance R

opaque

  -- A variant of ▸-·.

  ▸-ᵐ· : γ ▸[ m ] t → ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ ▸[ m ᵐ· p ] t
  ▸-ᵐ· {m} {p} =
    ▸-cong
      (⌞ p ⌟ ·ᵐ m  ≡⟨ ·ᵐ-comm ⌞ _ ⌟ _ ⟩
       m ·ᵐ ⌞ p ⌟  ≡⟨⟩
       m ᵐ· p      ∎) ∘→
    ▸-·
    where
    open Tools.Reasoning.PropositionalEquality

opaque

  -- If a term is well-resourced with respect to any context and mode,
  -- then it is well-resourced with respect to the zero usage context
  -- and the mode 𝟘ᵐ (if the mode structire is not trivial).

  ▸-𝟘′ : ¬ Trivialᵐ → γ ▸[ m ] t → 𝟘ᶜ ▸[ 𝟘ᵐ ] t
  ▸-𝟘′ {γ} not-trivial ▸t = sub-≈ᶜ (▸-𝟘 ▸t) $ begin
    𝟘ᶜ          ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
    𝟘 ·ᶜ γ      ≈˘⟨ ·ᶜ-congʳ (⌜𝟘ᵐ⌝ not-trivial) ⟩
    ⌜ 𝟘ᵐ ⌝ ·ᶜ γ ∎
    where
    open ≈ᶜ-reasoning

opaque

  -- The relation _▸[_]_ respects mode ordering (in a certain sense)

  ▸-≤ᵐ : γ ▸[ m ] t → m ≤ᵐ m′ → ⌜ m′ ⌝ ·ᶜ γ ▸[ m′ ] t
  ▸-≤ᵐ ▸t m≤m′ = ▸-cong (sym m≤m′) (▸-· ▸t)

opaque

  -- A variant of ▸-ᵐ·.

  ▸-ᵐ·-DCon : ▸[ m ] ∇ → ▸[ m ᵐ· p ] ∇
  ▸-ᵐ·-DCon ▸∇ = ▸-ᵐ· ∘→ ▸∇

opaque

  -- The relation _▸[_]_ respects multiplication (in a certain sense).

  ▸-·′ : γ ▸[ m ] t → ⌜ m ⌝ ·ᶜ γ ▸[ m ] t
  ▸-·′ ▸t = ▸-cong (·ᵐ-idem _) (▸-· ▸t)

opaque

  -- If a term does not use any resources, then it is well-resourced
  -- with respect to any mode.

  𝟘ᶜ▸[𝟙ᵐ]→ : 𝟘ᶜ ▸[ 𝟙ᵐ ] t → 𝟘ᶜ ▸[ m ] t
  𝟘ᶜ▸[𝟙ᵐ]→ ▸t =
    sub-≈ᶜ (▸-cong (·ᵐ-identityʳ _) (▸-· ▸t))
      (≈ᶜ-sym (·ᶜ-zeroʳ _))

opaque

  -- If t is well-resourced with respect to m and γ, then t is
  -- well-resourced with respect to m ᵐ· p and some δ for which
  -- p ·ᶜ γ ≈ᶜ p ·ᶜ δ.

  ▸→▸[ᵐ·] :
    γ ▸[ m ] t →
    ∃ λ δ → δ ▸[ m ᵐ· p ] t × p ·ᶜ γ ≈ᶜ p ·ᶜ δ
  ▸→▸[ᵐ·] {γ} {p} ▸t = _ , ▸-ᵐ· ▸t , (begin
    p ·ᶜ γ               ≈˘⟨ ·ᶜ-congʳ ·⌜⌞⌟⌝ ⟩
    (p · ⌜ ⌞ p ⌟ ⌝) ·ᶜ γ ≈⟨ ·ᶜ-assoc _ _ _ ⟩
    p ·ᶜ ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ  ∎)
    where
    open ≈ᶜ-reasoning


opaque

  -- If a term is well-resourced with respect to ε and any mode, then
  -- it is well-resourced with respect to ε and the mode 𝟘ᵐ.

  ε-▸-𝟘ᵐ : ε ▸[ m ] t → ε ▸[ 𝟘ᵐ ] t
  ε-▸-𝟘ᵐ ▸t = ▸-𝟘 ▸t

opaque

  -- A variant of ε-▸-𝟘ᵐ.

  ▸-𝟘ᵐ-DCon : ▸[ m ] ∇ → ▸[ 𝟘ᵐ ] ∇
  ▸-𝟘ᵐ-DCon ▸∇ = ε-▸-𝟘ᵐ ∘→ ▸∇

------------------------------------------------------------------------
-- The lemmas ▸ᵐ and ▸-𝟘ᵐ

opaque mutual

  ▸ᵐ-ᵐ· : γ ▸[ m ᵐ· p ] t → p ·ᶜ γ ≤ᶜ ⌜ m ⌝ ·ᶜ p ·ᶜ γ
  ▸ᵐ-ᵐ· {γ} {m} {p} ▸t = begin
    p ·ᶜ γ                ≤⟨ ·ᶜ-monotoneʳ (▸ᵐ ▸t) ⟩
    p ·ᶜ ⌜ m ᵐ· p ⌝ ·ᶜ γ  ≈˘⟨ ·ᶜ-assoc _ _ _ ⟩
    (p · ⌜ m ᵐ· p ⌝) ·ᶜ γ ≈⟨ ·ᶜ-congʳ (·⌜ᵐ·⌝ _) ⟩
    (p · ⌜ m ⌝) ·ᶜ γ      ≈˘⟨ ·ᶜ-congʳ (⌜⌝-·-comm _) ⟩
    (⌜ m ⌝ · p) ·ᶜ γ      ≈⟨ ·ᶜ-assoc _ _ _ ⟩
    ⌜ m ⌝ ·ᶜ p ·ᶜ γ       ∎
    where
    open ≤ᶜ-reasoning

  ▸ᵐ : γ ▸[ m ] t → γ ≤ᶜ ⌜ m ⌝ ·ᶜ γ
  ▸ᵐ {m} = λ where
      (sub ▸t γ≤) →
        ≤ᶜ⌜⌝·ᶜ γ≤ (▸ᵐ ▸t)
      (var {x}) → begin
        𝟘ᶜ , x ≔ ⌜ m ⌝                  ≈˘⟨ update-cong (·ᶜ-zeroʳ _) (·-idem-⌜⌝ _) ⟩
        ⌜ m ⌝ ·ᶜ 𝟘ᶜ , x ≔ ⌜ m ⌝ · ⌜ m ⌝ ≡⟨ update-distrib-·ᶜ _ _ _ x ⟩
        ⌜ m ⌝ ·ᶜ (𝟘ᶜ , x ≔ ⌜ m ⌝)       ∎
      defn →
        𝟘ᶜ≤ᶜm𝟘ᶜ
      Uₘ →
        𝟘ᶜ≤ᶜm𝟘ᶜ
      Emptyₘ →
        𝟘ᶜ≤ᶜm𝟘ᶜ
      (emptyrecₘ ▸t _ _) →
        ▸ᵐ-ᵐ· ▸t
      Unitₘ →
        𝟘ᶜ≤ᶜm𝟘ᶜ
      (starˢₘ x) →
        ≤ᶜ-reflexive (≈ᶜ-sym ·ᶜ-idem-⌜⌝)
      starʷₘ →
        𝟘ᶜ≤ᶜm𝟘ᶜ
      (unitrecₘ ▸t ▸u _ _) →
        lemma (▸ᵐ-ᵐ· ▸t) (▸ᵐ ▸u)
      (ΠΣₘ ▸A ▸B) →
        lemma (▸ᵐ ▸A) (tailₘ-monotone (▸ᵐ ▸B))
      (lamₘ ▸t) →
        tailₘ-monotone (▸ᵐ ▸t)
      (▸t ∘ₘ ▸u) →
        lemma (▸ᵐ ▸t) (▸ᵐ-ᵐ· ▸u)
      (prodˢₘ {γ} {p} {δ} ▸t ▸u) → begin
        p ·ᶜ γ ∧ᶜ δ                   ≤⟨ ∧ᶜ-monotone (▸ᵐ-ᵐ· ▸t) (▸ᵐ ▸u) ⟩
        ⌜ m ⌝ ·ᶜ p ·ᶜ γ ∧ᶜ ⌜ m ⌝ ·ᶜ δ ≈˘⟨ ·ᶜ-distribˡ-∧ᶜ _ _ _ ⟩
        ⌜ m ⌝ ·ᶜ (p ·ᶜ γ ∧ᶜ δ)        ∎
      (fstₘ _ ▸t refl _) →
        ▸ᵐ ▸t
      (sndₘ ▸t) →
        ▸ᵐ ▸t
      (prodʷₘ ▸t ▸u) →
        lemma (▸ᵐ-ᵐ· ▸t) (▸ᵐ ▸u)
      (prodrecₘ ▸t ▸u _ _) →
        lemma (▸ᵐ-ᵐ· ▸t) (tailₘ-monotone (tailₘ-monotone (▸ᵐ ▸u)))
      ℕₘ →
        𝟘ᶜ≤ᶜm𝟘ᶜ
      zeroₘ →
        𝟘ᶜ≤ᶜm𝟘ᶜ
      (sucₘ ▸t) →
        ▸ᵐ ▸t
      (natrecₘ {γ} {δ} {p} {r} {η} ▸z ▸s ▸n _) → begin
        nrᶜ p r γ δ η                                  ≤⟨ nrᶜ-monotone (▸ᵐ ▸z)
                                                          (tailₘ-monotone (tailₘ-monotone (▸ᵐ ▸s)))
                                                          (▸ᵐ ▸n) ⟩
        nrᶜ p r (⌜ m ⌝ ·ᶜ γ) (⌜ m ⌝ ·ᶜ δ) (⌜ m ⌝ ·ᶜ η) ≈˘⟨ ⌜⌝-·ᶜ-nrᶜ ⟩
        ⌜ m ⌝ ·ᶜ nrᶜ p r γ δ η ∎
      (natrec-no-nrₘ ▸z _ _ _ γ≤ _ _ _) →
        ≤ᶜ⌜⌝·ᶜ γ≤ (▸ᵐ ▸z)
      (natrec-no-nr-glbₘ {η} {χ} {x} ▸z ▸s ▸n _ x-GLB χ-GLB) →
        let mχ-GLB = GLBᶜ-congˡ ⌜⌝-·ᶜ-nrᵢᶜ (·ᶜ-GLBᶜˡ χ-GLB)
        in  begin
          x ·ᶜ η +ᶜ χ                   ≤⟨ +ᶜ-monotone (·ᶜ-monotoneʳ (▸ᵐ ▸n))
                                            (GLBᶜ-monotone (λ _ → nrᵢᶜ-monotone (▸ᵐ ▸z) (tailₘ-monotone (tailₘ-monotone (▸ᵐ ▸s))))
                                              χ-GLB mχ-GLB) ⟩
          x ·ᶜ ⌜ m ⌝ ·ᶜ η +ᶜ ⌜ m ⌝ ·ᶜ χ ≈˘⟨ +ᶜ-congʳ (⌜⌝·ᶜ-comm _ _ _) ⟩
          ⌜ m ⌝ ·ᶜ x ·ᶜ η +ᶜ ⌜ m ⌝ ·ᶜ χ ≈˘⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
          ⌜ m ⌝ ·ᶜ (x ·ᶜ η +ᶜ χ)        ∎
      (Idₘ _ ▸A ▸t ▸u) →
        lemma (▸ᵐ ▸A) (lemma (▸ᵐ ▸t) (▸ᵐ ▸u))
      (Id₀ₘ _ _ _ _) →
        𝟘ᶜ≤ᶜm𝟘ᶜ
      rflₘ →
        𝟘ᶜ≤ᶜm𝟘ᶜ
      (Jₘ {γ₂} {γ₃} {γ₄} {γ₅} {γ₆} _ _ _ ▸t ▸B ▸u ▸v ▸w) → begin
        ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)                                              ≤⟨ ·ᶜ-monotoneʳ (+ᶜ-monotone (▸ᵐ ▸t)
                                                                                          (+ᶜ-monotone (tailₘ-monotone (tailₘ-monotone (▸ᵐ ▸B)))
                                                                                          (+ᶜ-monotone (▸ᵐ ▸u) (+ᶜ-monotone (▸ᵐ ▸v) (▸ᵐ ▸w))))) ⟩
        ω ·ᶜ (⌜ m ⌝ ·ᶜ γ₂ +ᶜ ⌜ m ⌝ ·ᶜ γ₃ +ᶜ ⌜ m ⌝ ·ᶜ γ₄ +ᶜ ⌜ m ⌝ ·ᶜ γ₅ +ᶜ ⌜ m ⌝ ·ᶜ γ₆) ≈˘⟨ ·ᶜ-congˡ (+ᶜ-congˡ (+ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _)))) ⟩
        ω ·ᶜ (⌜ m ⌝ ·ᶜ γ₂ +ᶜ ⌜ m ⌝ ·ᶜ γ₃ +ᶜ ⌜ m ⌝ ·ᶜ γ₄ +ᶜ ⌜ m ⌝ ·ᶜ (γ₅ +ᶜ γ₆))        ≈˘⟨ ·ᶜ-congˡ (+ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _))) ⟩
        ω ·ᶜ (⌜ m ⌝ ·ᶜ γ₂ +ᶜ ⌜ m ⌝ ·ᶜ γ₃ +ᶜ ⌜ m ⌝ ·ᶜ (γ₄ +ᶜ γ₅ +ᶜ γ₆))                 ≈˘⟨ ·ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _)) ⟩
        ω ·ᶜ (⌜ m ⌝ ·ᶜ γ₂ +ᶜ ⌜ m ⌝ ·ᶜ (γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆))                          ≈˘⟨ ·ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
        ω ·ᶜ ⌜ m ⌝ ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)                                     ≈˘⟨ ⌜⌝·ᶜ-comm _ _ _ ⟩
        ⌜ m ⌝ ·ᶜ ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆) ∎
      (J₀ₘ₁ {γ₃} {γ₄} _ _ _ _ _ ▸B ▸u _ _) → begin
        ω ·ᶜ (γ₃ +ᶜ γ₄)                   ≤⟨ ·ᶜ-monotoneʳ (+ᶜ-monotone (tailₘ-monotone (tailₘ-monotone (▸ᵐ ▸B))) (▸ᵐ ▸u)) ⟩
        ω ·ᶜ (⌜ m ⌝ ·ᶜ γ₃ +ᶜ ⌜ m ⌝ ·ᶜ γ₄) ≈˘⟨ ·ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
        ω ·ᶜ ⌜ m ⌝ ·ᶜ (γ₃ +ᶜ γ₄)          ≈˘⟨ ⌜⌝·ᶜ-comm _ _ _ ⟩
        ⌜ m ⌝ ·ᶜ ω ·ᶜ (γ₃ +ᶜ γ₄)          ∎
      (J₀ₘ₂ _ _ _ _ ▸u _ _) →
        ▸ᵐ ▸u
      (Kₘ {γ₂} {γ₃} {γ₄} {γ₅} _ _ _ ▸t ▸B ▸u ▸v) → begin
        ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅)                                     ≤⟨ ·ᶜ-monotoneʳ (+ᶜ-monotone (▸ᵐ ▸t)
                                                                           (+ᶜ-monotone (tailₘ-monotone (▸ᵐ ▸B))
                                                                           (+ᶜ-monotone (▸ᵐ ▸u) (▸ᵐ ▸v)))) ⟩
        ω ·ᶜ (⌜ m ⌝ ·ᶜ γ₂ +ᶜ ⌜ m ⌝ ·ᶜ γ₃ +ᶜ ⌜ m ⌝ ·ᶜ γ₄ +ᶜ ⌜ m ⌝ ·ᶜ γ₅) ≈˘⟨ ·ᶜ-congˡ (+ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _))) ⟩
        ω ·ᶜ (⌜ m ⌝ ·ᶜ γ₂ +ᶜ ⌜ m ⌝ ·ᶜ γ₃ +ᶜ ⌜ m ⌝ ·ᶜ (γ₄ +ᶜ γ₅))        ≈˘⟨ ·ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _)) ⟩
        ω ·ᶜ (⌜ m ⌝ ·ᶜ γ₂ +ᶜ ⌜ m ⌝ ·ᶜ (γ₃ +ᶜ γ₄ +ᶜ γ₅))                 ≈˘⟨ ·ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
        ω ·ᶜ ⌜ m ⌝ ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅)                            ≈˘⟨ ⌜⌝·ᶜ-comm _ _ _ ⟩
        ⌜ m ⌝ ·ᶜ ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅) ∎
      (K₀ₘ₁ {γ₃} {γ₄} _ _ _ _ ▸B ▸u _) → begin
        ω ·ᶜ (γ₃ +ᶜ γ₄)                   ≤⟨ ·ᶜ-monotoneʳ (+ᶜ-monotone (tailₘ-monotone (▸ᵐ ▸B)) (▸ᵐ ▸u)) ⟩
        ω ·ᶜ (⌜ m ⌝ ·ᶜ γ₃ +ᶜ ⌜ m ⌝ ·ᶜ γ₄) ≈˘⟨ ·ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
        ω ·ᶜ ⌜ m ⌝ ·ᶜ (γ₃ +ᶜ γ₄)          ≈˘⟨ ⌜⌝·ᶜ-comm _ _ _ ⟩
        ⌜ m ⌝ ·ᶜ ω ·ᶜ (γ₃ +ᶜ γ₄)          ∎
      (K₀ₘ₂ _ _ _ _ ▸u _) →
        ▸ᵐ ▸u
      ([]-congₘ _ _ _ _ _) →
        𝟘ᶜ≤ᶜm𝟘ᶜ
    where
    open ≤ᶜ-reasoning
    open Graded.Usage.Restrictions.Instance R
    𝟘ᶜ≤ᶜm𝟘ᶜ : 𝟘ᶜ {n} ≤ᶜ ⌜ m ⌝ ·ᶜ 𝟘ᶜ
    𝟘ᶜ≤ᶜm𝟘ᶜ = ≤ᶜ-reflexive (≈ᶜ-sym (·ᶜ-zeroʳ _))
    lemma :
      γ ≤ᶜ ⌜ m ⌝ ·ᶜ γ → δ ≤ᶜ ⌜ m ⌝ ·ᶜ δ →
      γ +ᶜ δ ≤ᶜ ⌜ m ⌝ ·ᶜ (γ +ᶜ δ)
    lemma {γ} {δ} γ≤ δ≤ = begin
      γ +ᶜ δ                   ≤⟨ +ᶜ-monotone γ≤ δ≤ ⟩
      ⌜ m ⌝ ·ᶜ γ +ᶜ ⌜ m ⌝ ·ᶜ δ ≈˘⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
      ⌜ m ⌝ ·ᶜ (γ +ᶜ δ)        ∎

opaque

  -- If the mode structure is not trivial and γ ▸[ 𝟘ᵐ ] t, then γ ≤ᶜ 𝟘ᶜ.

  ▸-𝟘ᵐ : ¬ Trivialᵐ → γ ▸[ 𝟘ᵐ ] t → γ ≤ᶜ 𝟘ᶜ
  ▸-𝟘ᵐ {γ} 𝟙ᵐ≢𝟘ᵐ ▸t = begin
    γ           ≤⟨ ▸ᵐ ▸t ⟩
    ⌜ 𝟘ᵐ ⌝ ·ᶜ γ ≈⟨ ·ᶜ-congʳ (⌜𝟘ᵐ⌝ 𝟙ᵐ≢𝟘ᵐ) ⟩
    𝟘 ·ᶜ γ      ≈⟨ ·ᶜ-zeroˡ _ ⟩
    𝟘ᶜ          ∎
    where
    open ≤ᶜ-reasoning

------------------------------------------------------------------------
-- Inversion lemmas

opaque

  -- A kind of inversion lemma for _▸[_]_ related to addition.

  ▸-⌞+⌟ˡ :
    ⌜ ⌞ p + q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p + q ⌟ ] t →
    ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⌟ ] t
  ▸-⌞+⌟ˡ {p} {q} {γ} ▸t =
    sub-≈ᶜ (▸-cong ⌞⌟·ᵐ⌞+⌟ˡ (▸-· {m′ = ⌞ p ⌟} ▸t)) $ begin
      ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ                   ≈˘⟨ ·ᶜ-congʳ (⌜⌝-cong ⌞⌟·ᵐ⌞+⌟ˡ) ⟩
      (⌜ ⌞ p ⌟ ·ᵐ ⌞ p + q ⌟ ⌝) ·ᶜ γ    ≈⟨ ·ᶜ-congʳ (⌜·ᵐ⌝ _) ⟩
      (⌜ ⌞ p ⌟ ⌝ · ⌜ ⌞ p + q ⌟ ⌝) ·ᶜ γ ≈⟨ ·ᶜ-assoc _ _ _ ⟩
      ⌜ ⌞ p ⌟ ⌝ ·ᶜ ⌜ ⌞ p + q ⌟ ⌝ ·ᶜ γ  ∎
    where
    open ≈ᶜ-reasoning

opaque

  -- A kind of inversion lemma for _▸[_]_ related to addition.

  ▸-⌞+⌟ʳ :
    ⌜ ⌞ p + q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p + q ⌟ ] t →
    ⌜ ⌞ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ q ⌟ ] t
  ▸-⌞+⌟ʳ ▸t =
    ▸-⌞+⌟ˡ (subst (λ m → ⌜ m ⌝ ·ᶜ _ ▸[ m ] _) (⌞⌟-cong (+-comm _ _)) ▸t)

opaque

  -- A kind of inversion lemma for _▸[_]_ related to the meet operation.

  ▸-⌞∧⌟ˡ :
    ⌜ ⌞ p ∧ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ∧ q ⌟ ] t →
    ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⌟ ] t
  ▸-⌞∧⌟ˡ {p} {q} {γ} ▸t =
    sub-≈ᶜ (▸-cong ⌞⌟·ᵐ⌞∧⌟ˡ (▸-· {m′ = ⌞ p ⌟} ▸t)) $ begin
      ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ                   ≈˘⟨ ·ᶜ-congʳ (⌜⌝-cong ⌞⌟·ᵐ⌞∧⌟ˡ) ⟩
      (⌜ ⌞ p ⌟ ·ᵐ ⌞ p ∧ q ⌟ ⌝) ·ᶜ γ    ≈⟨ ·ᶜ-congʳ (⌜·ᵐ⌝ _) ⟩
      (⌜ ⌞ p ⌟ ⌝ · ⌜ ⌞ p ∧ q ⌟ ⌝) ·ᶜ γ ≈⟨ ·ᶜ-assoc _ _ _ ⟩
      ⌜ ⌞ p ⌟ ⌝ ·ᶜ ⌜ ⌞ p ∧ q ⌟ ⌝ ·ᶜ γ  ∎
    where
    open ≈ᶜ-reasoning

opaque

  -- A kind of inversion lemma for _▸[_]_ related to the meet operation.

  ▸-⌞∧⌟ʳ :
    ⌜ ⌞ p ∧ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ∧ q ⌟ ] t →
    ⌜ ⌞ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ q ⌟ ] t
  ▸-⌞∧⌟ʳ ▸t =
    ▸-⌞∧⌟ˡ (subst (λ m → ⌜ m ⌝ ·ᶜ _ ▸[ m ] _) (⌞⌟-cong (∧-comm _ _)) ▸t)

opaque

  -- A form of monotonicity for _▸[_]_.

  ▸-≤ : p ≤ q → ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⌟ ] t → ⌜ ⌞ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ q ⌟ ] t
  ▸-≤ {p} {q} {γ} {t} p≤q ▸t =
    ▸-⌞∧⌟ʳ (subst (λ p → ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⌟ ] t) p≤q ▸t)

opaque

  -- A form of monotonicity for _▸[_]_.

  ▸-≤′ : p ≤ q → γ ▸[ ⌞ p ⌟ ] t → ⌜ ⌞ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ q ⌟ ] t
  ▸-≤′ p≤q ▸t = ▸-≤ᵐ ▸t (⌞⌟-monotone p≤q)

opaque

  -- A kind of inversion lemma for _▸[_]_ related to the star operation.

  ▸-⌞⊛⌟ˡ :
    ⦃ has-star : Has-star semiring-with-meet ⦄ →
    ⌜ ⌞ p ⊛ q ▷ r ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⊛ q ▷ r ⌟ ] t →
    ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⌟ ] t
  ▸-⌞⊛⌟ˡ {p} {q} {r} = ▸-≤ (⊛-ineq₂ p q r)

opaque

  -- A kind of inversion lemma for _▸[_]_ related to the star operation.

  ▸-⌞⊛⌟ʳ :
    ⦃ has-star : Has-star semiring-with-meet ⦄ →
    ⌜ ⌞ p ⊛ q ▷ r ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⊛ q ▷ r ⌟ ] t →
    ⌜ ⌞ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ q ⌟ ] t
  ▸-⌞⊛⌟ʳ {p} {q} {r} = ▸-⌞+⌟ˡ ∘→ ▸-≤ (⊛-ineq₁ p q r)

opaque

  -- A kind of inversion lemma for _▸[_]_ related to the nr function.

  ▸-⌞nr⌟₁ :
    ∀ {n} ⦃ ok : Nr-available ⦄ →
    let open Graded.Usage.Restrictions.Instance R in
    ⌜ ⌞ nr p r z s n ⌟ ⌝ ·ᶜ γ ▸[ ⌞ nr p r z s n ⌟ ] t →
    ⌜ ⌞ z ⌟ ⌝ ·ᶜ γ ▸[ ⌞ z ⌟ ] t
  ▸-⌞nr⌟₁ {p} {r} {z} {s} {γ} {n} ▸t =
    sub-≈ᶜ (▸-cong ⌞⌟·ᵐ⌞nr⌟₁ (▸-· {m′ = ⌞ z ⌟} ▸t)) $ begin
      ⌜ ⌞ z ⌟ ⌝ ·ᶜ γ                          ≈˘⟨ ·ᶜ-congʳ (⌜⌝-cong ⌞⌟·ᵐ⌞nr⌟₁) ⟩
      ⌜ ⌞ z ⌟ ·ᵐ ⌞ nr p r z s n ⌟ ⌝ ·ᶜ γ      ≈⟨ ·ᶜ-congʳ (⌜·ᵐ⌝ _) ⟩
      (⌜ ⌞ z ⌟ ⌝ · ⌜ ⌞ nr p r z s n ⌟ ⌝) ·ᶜ γ ≈⟨ ·ᶜ-assoc _ _ _ ⟩
      ⌜ ⌞ z ⌟ ⌝ ·ᶜ ⌜ ⌞ nr p r z s n ⌟ ⌝ ·ᶜ γ  ∎
    where
    open Graded.Usage.Restrictions.Instance R
    open ≈ᶜ-reasoning

opaque

  -- A kind of inversion lemma for _▸[_]_ related to the nr function.

  ▸-⌞nr⌟₂ :
    ∀ {n} ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
    ⌜ ⌞ nr p r z s n ⌟ ⌝ ·ᶜ γ ▸[ ⌞ nr p r z s n ⌟ ] t →
    ⌜ ⌞ s ⌟ ⌝ ·ᶜ γ ▸[ ⌞ s ⌟ ] t
  ▸-⌞nr⌟₂ ▸t = ▸-⌞+⌟ˡ (▸-≤ nr-suc ▸t)

opaque

  -- A kind of inversion lemma for _▸[_]_ related to the nr function.

  ▸-⌞nr⌟₃ :
    ∀ {n} ⦃ ok : Nr-available ⦄ →
    let open Graded.Usage.Restrictions.Instance R in
    ⌜ ⌞ nr p r z s n ⌟ ⌝ ·ᶜ γ ▸[ ⌞ nr p r z s n ⌟ ] t →
    ⌜ ⌞ n ⌟ ⌝ ·ᶜ γ ▸[ ⌞ n ⌟ ] t
  ▸-⌞nr⌟₃ {p} {r} {z} {s} {γ} {n} ▸t =
    sub-≈ᶜ (▸-cong ⌞⌟·ᵐ⌞nr⌟₃ (▸-· {m′ = ⌞ n ⌟} ▸t)) $ begin
      ⌜ ⌞ n ⌟ ⌝ ·ᶜ γ                          ≈˘⟨ ·ᶜ-congʳ (⌜⌝-cong ⌞⌟·ᵐ⌞nr⌟₃) ⟩
      ⌜ ⌞ n ⌟ ·ᵐ ⌞ nr p r z s n ⌟ ⌝ ·ᶜ γ      ≈⟨ ·ᶜ-congʳ (⌜·ᵐ⌝ _) ⟩
      (⌜ ⌞ n ⌟ ⌝ · ⌜ ⌞ nr p r z s n ⌟ ⌝) ·ᶜ γ ≈⟨ ·ᶜ-assoc _ _ _ ⟩
      ⌜ ⌞ n ⌟ ⌝ ·ᶜ ⌜ ⌞ nr p r z s n ⌟ ⌝ ·ᶜ γ  ∎
    where
    open Graded.Usage.Restrictions.Instance R
    open ≈ᶜ-reasoning

------------------------------------------------------------------------
-- The lemma Conₘ-interchange

private opaque

  -- Some lemmas used below.

  Conₘ-interchange₀₁ :
    ∀ δ₃ δ₄ → ω ·ᶜ (γ₃ +ᶜ γ₄) , x ≔ (ω ·ᶜ (δ₃ +ᶜ δ₄)) ⟨ x ⟩ ≡
    ω ·ᶜ ((γ₃ , x ≔ δ₃ ⟨ x ⟩) +ᶜ (γ₄ , x ≔ δ₄ ⟨ x ⟩))
  Conₘ-interchange₀₁ {γ₃} {γ₄} {x} δ₃ δ₄ =
    ω ·ᶜ (γ₃ +ᶜ γ₄) , x ≔ (ω ·ᶜ (δ₃ +ᶜ δ₄)) ⟨ x ⟩      ≡⟨ cong (_ , _ ≔_) $ lookup-distrib-·ᶜ (δ₃ +ᶜ _) _ _ ⟩
    ω ·ᶜ (γ₃ +ᶜ γ₄) , x ≔ ω · (δ₃ +ᶜ δ₄) ⟨ x ⟩         ≡⟨ update-distrib-·ᶜ _ _ _ _ ⟩
    ω ·ᶜ (γ₃ +ᶜ γ₄ , x ≔ (δ₃ +ᶜ δ₄) ⟨ x ⟩)             ≡⟨ cong (_ ·ᶜ_) $
                                                          trans (cong (_ , _ ≔_) $ lookup-distrib-+ᶜ δ₃ _ _) $
                                                          update-distrib-+ᶜ _ _ _ _ _ ⟩
    ω ·ᶜ ((γ₃ , x ≔ δ₃ ⟨ x ⟩) +ᶜ (γ₄ , x ≔ δ₄ ⟨ x ⟩))  ∎
    where
    open Tools.Reasoning.PropositionalEquality

  Conₘ-interchange-J :
    ∀ δ₂ δ₃ δ₄ δ₅ δ₆ →
    ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆) ,
    x ≔ (ω ·ᶜ (δ₂ +ᶜ δ₃ +ᶜ δ₄ +ᶜ δ₅ +ᶜ δ₆)) ⟨ x ⟩ ≡
    ω ·ᶜ
     ((γ₂ , x ≔ δ₂ ⟨ x ⟩) +ᶜ (γ₃ , x ≔ δ₃ ⟨ x ⟩) +ᶜ
      (γ₄ , x ≔ δ₄ ⟨ x ⟩) +ᶜ (γ₅ , x ≔ δ₅ ⟨ x ⟩) +ᶜ
      (γ₆ , x ≔ δ₆ ⟨ x ⟩))
  Conₘ-interchange-J {γ₂} {γ₃} {γ₄} {γ₅} {γ₆} {x} δ₂ δ₃ δ₄ δ₅ δ₆ =
    ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆) ,
    x ≔ (ω ·ᶜ (δ₂ +ᶜ δ₃ +ᶜ δ₄ +ᶜ δ₅ +ᶜ δ₆)) ⟨ x ⟩   ≡⟨ cong (_ , _ ≔_) $ lookup-distrib-·ᶜ (δ₂ +ᶜ _) _ _ ⟩

    ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆) ,
    x ≔ ω · (δ₂ +ᶜ δ₃ +ᶜ δ₄ +ᶜ δ₅ +ᶜ δ₆) ⟨ x ⟩      ≡⟨ update-distrib-·ᶜ _ _ _ _ ⟩

    ω ·ᶜ
    (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆ ,
     x ≔ (δ₂ +ᶜ δ₃ +ᶜ δ₄ +ᶜ δ₅ +ᶜ δ₆) ⟨ x ⟩)        ≡⟨ cong (ω ·ᶜ_) $
                                                       trans (cong (_ , _ ≔_) $ lookup-distrib-+ᶜ δ₂ _ _) $
                                                       trans (update-distrib-+ᶜ _ _ _ _ _) $
                                                       cong (_ +ᶜ_) $
                                                       trans (cong (_ , _ ≔_) $ lookup-distrib-+ᶜ δ₃ _ _) $
                                                       trans (update-distrib-+ᶜ _ _ _ _ _) $
                                                       cong (_ +ᶜ_) $
                                                       trans (cong (_ , _ ≔_) $ lookup-distrib-+ᶜ δ₄ _ _) $
                                                       trans (update-distrib-+ᶜ _ _ _ _ _) $
                                                       cong (_ +ᶜ_) $
                                                       trans (cong (_ , _ ≔_) $ lookup-distrib-+ᶜ δ₅ _ _) $
                                                       update-distrib-+ᶜ _ _ _ _ _ ⟩

    ω ·ᶜ
    ((γ₂ , x ≔ δ₂ ⟨ x ⟩) +ᶜ (γ₃ , x ≔ δ₃ ⟨ x ⟩) +ᶜ
     (γ₄ , x ≔ δ₄ ⟨ x ⟩) +ᶜ (γ₅ , x ≔ δ₅ ⟨ x ⟩) +ᶜ
     (γ₆ , x ≔ δ₆ ⟨ x ⟩))                           ∎
    where
    open Tools.Reasoning.PropositionalEquality

  Conₘ-interchange-K :
    ∀ δ₂ δ₃ δ₄ δ₅ →
    ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅) ,
    x ≔ (ω ·ᶜ (δ₂ +ᶜ δ₃ +ᶜ δ₄ +ᶜ δ₅)) ⟨ x ⟩ ≡
    ω ·ᶜ
     ((γ₂ , x ≔ δ₂ ⟨ x ⟩) +ᶜ (γ₃ , x ≔ δ₃ ⟨ x ⟩) +ᶜ
      (γ₄ , x ≔ δ₄ ⟨ x ⟩) +ᶜ (γ₅ , x ≔ δ₅ ⟨ x ⟩))
  Conₘ-interchange-K {γ₂} {γ₃} {γ₄} {γ₅} {x} δ₂ δ₃ δ₄ δ₅ =
    ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅) ,
    x ≔ (ω ·ᶜ (δ₂ +ᶜ δ₃ +ᶜ δ₄ +ᶜ δ₅)) ⟨ x ⟩                    ≡⟨ cong (_ , _ ≔_) $ lookup-distrib-·ᶜ (δ₂ +ᶜ _) _ _ ⟩

    ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅) ,
    x ≔ ω · (δ₂ +ᶜ δ₃ +ᶜ δ₄ +ᶜ δ₅) ⟨ x ⟩                       ≡⟨ update-distrib-·ᶜ _ _ _ _ ⟩

    ω ·ᶜ
    (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ , x ≔ (δ₂ +ᶜ δ₃ +ᶜ δ₄ +ᶜ δ₅) ⟨ x ⟩)  ≡⟨ cong (ω ·ᶜ_) $
                                                                  trans (cong (_ , _ ≔_) $ lookup-distrib-+ᶜ δ₂ _ _) $
                                                                  trans (update-distrib-+ᶜ _ _ _ _ _) $
                                                                  cong (_ +ᶜ_) $
                                                                  trans (cong (_ , _ ≔_) $ lookup-distrib-+ᶜ δ₃ _ _) $
                                                                  trans (update-distrib-+ᶜ _ _ _ _ _) $
                                                                  cong (_ +ᶜ_) $
                                                                  trans (cong (_ , _ ≔_) $ lookup-distrib-+ᶜ δ₄ _ _) $
                                                                  update-distrib-+ᶜ _ _ _ _ _ ⟩
    ω ·ᶜ
    ((γ₂ , x ≔ δ₂ ⟨ x ⟩) +ᶜ (γ₃ , x ≔ δ₃ ⟨ x ⟩) +ᶜ
     (γ₄ , x ≔ δ₄ ⟨ x ⟩) +ᶜ (γ₅ , x ≔ δ₅ ⟨ x ⟩))               ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque

  -- The contents of two valid modality contexts can be freely
  -- interchanged.

  Conₘ-interchange :
    γ ▸[ m ] t → δ ▸[ m ] t → (x : Fin n) → (γ , x ≔ δ ⟨ x ⟩) ▸[ m ] t
  Conₘ-interchange (sub γ▸t γ≤γ′) δ▸t x = sub
    (Conₘ-interchange γ▸t δ▸t x)
    (update-monotoneˡ x γ≤γ′)

  Conₘ-interchange {m} {δ} (var {x = y}) ▸var x = sub
    var
    (begin
       𝟘ᶜ , y ≔ ⌜ m ⌝ , x ≔ δ ⟨ x ⟩                 ≤⟨ update-monotoneʳ _ $ lookup-monotone _ $ inv-usage-var ▸var ⟩
       𝟘ᶜ , y ≔ ⌜ m ⌝ , x ≔ (𝟘ᶜ , y ≔ ⌜ m ⌝) ⟨ x ⟩  ≡⟨ update-self _ _ ⟩
       𝟘ᶜ , y ≔ ⌜ m ⌝                               ∎)
    where
    open CR

  Conₘ-interchange {δ} defn ▸defn x = sub
    defn
    (begin
       𝟘ᶜ , x ≔ δ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ $ inv-usage-defn ▸defn ⟩
       𝟘ᶜ , x ≔ 𝟘ᶜ ⟨ x ⟩  ≡⟨ update-self _ _ ⟩
       𝟘ᶜ                 ∎)
    where
    open CR

  Conₘ-interchange {δ} Uₘ ▸U x = sub
    Uₘ
    (begin
       𝟘ᶜ , x ≔ δ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ $ inv-usage-U ▸U ⟩
       𝟘ᶜ , x ≔ 𝟘ᶜ ⟨ x ⟩  ≡⟨ update-self _ _ ⟩
       𝟘ᶜ                 ∎)
    where
    open CR

  Conₘ-interchange {δ = η} (ΠΣₘ {γ} {δ} ▸t ▸u) ▸ΠΣ x =
    case inv-usage-ΠΣ ▸ΠΣ of λ
      (invUsageΠΣ {δ = γ′} {η = δ′} ▸t′ ▸u′ η≤γ′+δ′) → sub
    (ΠΣₘ (Conₘ-interchange ▸t ▸t′ x) (Conₘ-interchange ▸u ▸u′ (x +1)))
    (begin
       γ +ᶜ δ , x ≔ η ⟨ x ⟩                      ≤⟨ update-monotoneʳ _ $ lookup-monotone _ η≤γ′+δ′ ⟩
       γ +ᶜ δ , x ≔ (γ′ +ᶜ δ′) ⟨ x ⟩             ≡⟨ cong (_ , x ≔_) (lookup-distrib-+ᶜ γ′ _ _) ⟩
       γ +ᶜ δ , x ≔ γ′ ⟨ x ⟩ + δ′ ⟨ x ⟩          ≡⟨ update-distrib-+ᶜ γ _ _ _ x ⟩
       (γ , x ≔ γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)  ∎)
    where
    open CR

  Conₘ-interchange {δ} (lamₘ {γ} ▸t) ▸lam x =
    case inv-usage-lam ▸lam of λ
      (invUsageLam {δ = γ′} ▸t′ δ≤γ′) → sub
    (lamₘ (Conₘ-interchange ▸t ▸t′ (x +1)))
    (begin
       γ , x ≔ δ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ δ≤γ′ ⟩
       γ , x ≔ γ′ ⟨ x ⟩  ∎)
    where
    open CR

  Conₘ-interchange {δ = η} (_∘ₘ_ {γ} {δ} {p} ▸t ▸u) ▸∘ x =
    case inv-usage-app ▸∘ of λ
      (invUsageApp {δ = γ′} {η = δ′} ▸t′ ▸u′ η≤γ′+pδ′) → sub
    (Conₘ-interchange ▸t ▸t′ x ∘ₘ Conₘ-interchange ▸u ▸u′ x)
    (begin
       γ +ᶜ p ·ᶜ δ , x ≔ η ⟨ x ⟩                             ≤⟨ update-monotoneʳ _ $ lookup-monotone _ η≤γ′+pδ′ ⟩
       (γ +ᶜ p ·ᶜ δ) , x ≔ (γ′ +ᶜ p ·ᶜ δ′) ⟨ x ⟩             ≡⟨ cong (_ , _ ≔_) $ lookup-distrib-+ᶜ γ′ _ _ ⟩
       (γ +ᶜ p ·ᶜ δ) , x ≔ γ′ ⟨ x ⟩ + (p ·ᶜ δ′) ⟨ x ⟩        ≡⟨ update-distrib-+ᶜ _ _ _ _ _ ⟩
       (γ , x ≔ γ′ ⟨ x ⟩) +ᶜ (p ·ᶜ δ , x ≔ (p ·ᶜ δ′) ⟨ x ⟩)  ≡⟨ cong (_ +ᶜ_) $ cong (_ , _ ≔_) $ lookup-distrib-·ᶜ δ′ _ _ ⟩
       (γ , x ≔ γ′ ⟨ x ⟩) +ᶜ (p ·ᶜ δ , x ≔ p · δ′ ⟨ x ⟩)     ≡⟨ cong (_ +ᶜ_) $ update-distrib-·ᶜ _ _ _ _ ⟩
       (γ , x ≔ γ′ ⟨ x ⟩) +ᶜ p ·ᶜ (δ , x ≔ δ′ ⟨ x ⟩)         ∎)
    where
    open CR

  Conₘ-interchange {δ = η} (prodʷₘ {γ} {p} {δ} ▸t ▸u) ▸prod x =
    case inv-usage-prodʷ ▸prod of λ
      (invUsageProdʷ {δ = γ′} {η = δ′} ▸t′ ▸u′ η≤pγ′+δ′) → sub
    (prodʷₘ (Conₘ-interchange ▸t ▸t′ x) (Conₘ-interchange ▸u ▸u′ x))
    (begin
       p ·ᶜ γ +ᶜ δ , x ≔ η ⟨ x ⟩                          ≤⟨ update-monotoneʳ _ $ lookup-monotone _ η≤pγ′+δ′ ⟩
       p ·ᶜ γ +ᶜ δ , x ≔ (p ·ᶜ γ′ +ᶜ δ′) ⟨ x ⟩            ≡⟨ cong (_ , _ ≔_) $ lookup-distrib-+ᶜ (_ ·ᶜ γ′) _ _ ⟩
       p ·ᶜ γ +ᶜ δ , x ≔ (p ·ᶜ γ′) ⟨ x ⟩ + δ′ ⟨ x ⟩       ≡⟨ cong (_,_≔_ _ _) $ cong (_+ _) $ lookup-distrib-·ᶜ γ′ _ _ ⟩
       p ·ᶜ γ +ᶜ δ , x ≔ p · γ′ ⟨ x ⟩ + δ′ ⟨ x ⟩          ≡⟨ update-distrib-+ᶜ _ _ _ _ _ ⟩
       (p ·ᶜ γ , x ≔ p · γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)  ≡⟨ cong (_+ᶜ _) $ update-distrib-·ᶜ _ _ _ _ ⟩
       p ·ᶜ (γ , x ≔ γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)      ∎)
    where
    open CR

  Conₘ-interchange {δ = η} (prodˢₘ {γ} {p} {δ} ▸t ▸u) ▸prod x =
    case inv-usage-prodˢ ▸prod of λ
      (invUsageProdˢ {δ = γ′} {η = δ′} ▸t′ ▸u′ η≤pγ′∧δ′) → sub
    (prodˢₘ (Conₘ-interchange ▸t ▸t′ x) (Conₘ-interchange ▸u ▸u′ x))
    (begin
       p ·ᶜ γ ∧ᶜ δ , x ≔ η ⟨ x ⟩                          ≤⟨ update-monotoneʳ _ $ lookup-monotone _ η≤pγ′∧δ′ ⟩
       p ·ᶜ γ ∧ᶜ δ , x ≔ (p ·ᶜ γ′ ∧ᶜ δ′) ⟨ x ⟩            ≡⟨ cong (_ , _ ≔_) $ lookup-distrib-∧ᶜ (_ ·ᶜ γ′) _ _ ⟩
       p ·ᶜ γ ∧ᶜ δ , x ≔ (p ·ᶜ γ′) ⟨ x ⟩ ∧ δ′ ⟨ x ⟩       ≡⟨ cong (_,_≔_ _ _) $ cong (_∧ _) $ lookup-distrib-·ᶜ γ′ _ _ ⟩
       p ·ᶜ γ ∧ᶜ δ , x ≔ p · γ′ ⟨ x ⟩ ∧ δ′ ⟨ x ⟩          ≡⟨ update-distrib-∧ᶜ _ _ _ _ _ ⟩
       (p ·ᶜ γ , x ≔ p · γ′ ⟨ x ⟩) ∧ᶜ (δ , x ≔ δ′ ⟨ x ⟩)  ≡⟨ cong (_∧ᶜ _) $ update-distrib-·ᶜ _ _ _ _ ⟩
       p ·ᶜ (γ , x ≔ γ′ ⟨ x ⟩) ∧ᶜ (δ , x ≔ δ′ ⟨ x ⟩)      ∎)
    where
    open CR

  Conₘ-interchange {δ} (fstₘ {γ} m ▸t PE.refl ok) ▸fst x =
    case inv-usage-fst ▸fst of λ
      (invUsageFst {δ = γ′} _ _ ▸t′ δ≤γ′ _) → sub
    (fstₘ m (Conₘ-interchange ▸t ▸t′ x) PE.refl ok)
    (begin
       γ , x ≔ δ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ δ≤γ′ ⟩
       γ , x ≔ γ′ ⟨ x ⟩  ∎)
    where
    open CR

  Conₘ-interchange {δ} (sndₘ {γ} ▸t) ▸snd x =
    case inv-usage-snd ▸snd of λ
      (invUsageSnd {δ = γ′} ▸t′ δ≤γ′) → sub
    (sndₘ (Conₘ-interchange ▸t ▸t′ x))
    (begin
       γ , x ≔ δ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ δ≤γ′ ⟩
       γ , x ≔ γ′ ⟨ x ⟩  ∎)
    where
    open CR

  Conₘ-interchange {δ = η} (prodrecₘ {γ} {r} {δ} ▸t ▸u ▸A ok) ▸pr x =
    case inv-usage-prodrec ▸pr of λ
      (invUsageProdrec
         {δ = γ′} {η = δ′} ▸t′ ▸u′ _ _ η≤rγ+δ′) → sub
    (prodrecₘ (Conₘ-interchange ▸t ▸t′ x)
       (Conₘ-interchange ▸u ▸u′ (x +2)) ▸A ok)
    (begin
       r ·ᶜ γ +ᶜ δ , x ≔ η ⟨ x ⟩                          ≤⟨ update-monotoneʳ _ $ lookup-monotone _ η≤rγ+δ′ ⟩
       r ·ᶜ γ +ᶜ δ , x ≔ (r ·ᶜ γ′ +ᶜ δ′) ⟨ x ⟩            ≡⟨ cong (_,_≔_ _ _) $ lookup-distrib-+ᶜ (_ ·ᶜ γ′) _ _ ⟩
       r ·ᶜ γ +ᶜ δ , x ≔ (r ·ᶜ γ′) ⟨ x ⟩ + δ′ ⟨ x ⟩       ≡⟨ cong (_,_≔_ _ _) $ cong (_+ _) $ lookup-distrib-·ᶜ γ′ _ _ ⟩
       r ·ᶜ γ +ᶜ δ , x ≔ r · γ′ ⟨ x ⟩ + δ′ ⟨ x ⟩          ≡⟨ update-distrib-+ᶜ _ _ _ _ _ ⟩
       (r ·ᶜ γ , x ≔ r · γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)  ≡⟨ cong (_+ᶜ _) $ update-distrib-·ᶜ _ _ _ _ ⟩
       r ·ᶜ (γ , x ≔ γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)      ∎)
    where
    open CR

  Conₘ-interchange {δ} Emptyₘ ▸Empty x = sub
    Emptyₘ
    (begin
       𝟘ᶜ , x ≔ δ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ $ inv-usage-Empty ▸Empty ⟩
       𝟘ᶜ , x ≔ 𝟘ᶜ ⟨ x ⟩  ≡⟨ update-self _ _ ⟩
       𝟘ᶜ                 ∎)
    where
    open CR

  Conₘ-interchange {δ} (emptyrecₘ {γ} {p} ▸t ▸A ok) ▸er x =
    case inv-usage-emptyrec ▸er of λ
      (invUsageEmptyrec {δ = γ′} ▸t′ _ _ δ≤pγ′) → sub
    (emptyrecₘ (Conₘ-interchange ▸t ▸t′ x) ▸A ok)
    (begin
       p ·ᶜ γ , x ≔ δ ⟨ x ⟩          ≤⟨ update-monotoneʳ _ $ lookup-monotone _ δ≤pγ′ ⟩
       p ·ᶜ γ , x ≔ (p ·ᶜ γ′) ⟨ x ⟩  ≡⟨ cong (_ , _ ≔_) $ lookup-distrib-·ᶜ γ′ _ _ ⟩
       p ·ᶜ γ , x ≔ p · (γ′ ⟨ x ⟩)   ≡⟨ update-distrib-·ᶜ _ _ _ _ ⟩
       p ·ᶜ (γ , x ≔ γ′ ⟨ x ⟩)       ∎)
    where
    open CR

  Conₘ-interchange {δ} Unitₘ ▸Unit x = sub
    Unitₘ
    (begin
       𝟘ᶜ , x ≔ δ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ $ inv-usage-Unit ▸Unit ⟩
       𝟘ᶜ , x ≔ 𝟘ᶜ ⟨ x ⟩  ≡⟨ update-self _ _ ⟩
       𝟘ᶜ                 ∎)
    where
    open CR

  Conₘ-interchange {δ} starʷₘ ▸star x = sub
    starʷₘ
    (begin
       𝟘ᶜ , x ≔ δ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ $ inv-usage-starʷ ▸star ⟩
       𝟘ᶜ , x ≔ 𝟘ᶜ ⟨ x ⟩  ≡⟨ update-self _ _ ⟩
       𝟘ᶜ                 ∎)
    where
    open CR

  Conₘ-interchange {δ} (starˢₘ {γ} {m} ok) ▸star x =
    case inv-usage-starˢ ▸star of λ
      (invUsageStarˢ {δ = γ′} δ≤⌜m⌝γ′ 𝟘≈γ′) → sub
    (let open Tools.Reasoning.Equivalence Conₘ-setoid in
     starˢₘ λ not-sink → begin
       𝟘ᶜ                 ≡˘⟨ update-self _ _ ⟩
       𝟘ᶜ , x ≔ 𝟘ᶜ ⟨ x ⟩  ≈⟨ update-cong (ok not-sink) (lookup-cong $ 𝟘≈γ′ not-sink) ⟩
       γ , x ≔ γ′ ⟨ x ⟩   ∎)
    (let open CR in begin
       ⌜ m ⌝ ·ᶜ γ , x ≔ δ ⟨ x ⟩              ≤⟨ update-monotoneʳ _ $ lookup-monotone _ δ≤⌜m⌝γ′ ⟩
       ⌜ m ⌝ ·ᶜ γ , x ≔ (⌜ m ⌝ ·ᶜ γ′) ⟨ x ⟩  ≡⟨ cong (_ , _ ≔_) $ lookup-distrib-·ᶜ γ′ _ _ ⟩
       ⌜ m ⌝ ·ᶜ γ , x ≔ ⌜ m ⌝ · γ′ ⟨ x ⟩     ≡⟨ update-distrib-·ᶜ _ _ _ _ ⟩
       ⌜ m ⌝ ·ᶜ (γ , x ≔ γ′ ⟨ x ⟩)           ∎)

  Conₘ-interchange {δ = η} (unitrecₘ {γ} {p} {δ} ▸t ▸u ▸A ok) ▸ur x =
    case inv-usage-unitrec ▸ur of λ
      (invUsageUnitrec {δ = γ′} {η = δ′} ▸t′ ▸u′ _ _ η≤pγ′+δ′) → sub
    (unitrecₘ (Conₘ-interchange ▸t ▸t′ x) (Conₘ-interchange ▸u ▸u′ x) ▸A
       ok)
    (begin
       p ·ᶜ γ +ᶜ δ , x ≔ η ⟨ x ⟩                          ≤⟨ update-monotoneʳ _ $ lookup-monotone _ η≤pγ′+δ′ ⟩
       p ·ᶜ γ +ᶜ δ , x ≔ (p ·ᶜ γ′ +ᶜ δ′) ⟨ x ⟩            ≡⟨ cong (_ , _ ≔_) $ lookup-distrib-+ᶜ (_ ·ᶜ γ′) _ _ ⟩
       p ·ᶜ γ +ᶜ δ , x ≔ (p ·ᶜ γ′) ⟨ x ⟩ + δ′ ⟨ x ⟩       ≡⟨ cong (_,_≔_ _ _) $ cong (_+ _) $ lookup-distrib-·ᶜ γ′ _ _ ⟩
       p ·ᶜ γ +ᶜ δ , x ≔ p · γ′ ⟨ x ⟩ + δ′ ⟨ x ⟩          ≡⟨ update-distrib-+ᶜ _ _ _ _ _ ⟩
       (p ·ᶜ γ , x ≔ p · γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)  ≡⟨ cong (_+ᶜ _) $ update-distrib-·ᶜ _ _ _ _ ⟩
       p ·ᶜ (γ , x ≔ γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)      ∎)
    where
    open CR

  Conₘ-interchange {δ} ℕₘ ▸ℕ x = sub
    ℕₘ
    (begin
       𝟘ᶜ , x ≔ δ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ $ inv-usage-ℕ ▸ℕ ⟩
       𝟘ᶜ , x ≔ 𝟘ᶜ ⟨ x ⟩  ≡⟨ update-self _ _ ⟩
       𝟘ᶜ                 ∎)
    where
    open CR

  Conₘ-interchange {δ} zeroₘ ▸zero x = sub
    zeroₘ
    (begin
       𝟘ᶜ , x ≔ δ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ $ inv-usage-zero ▸zero ⟩
       𝟘ᶜ , x ≔ 𝟘ᶜ ⟨ x ⟩  ≡⟨ update-self _ _ ⟩
       𝟘ᶜ                 ∎)
    where
    open CR

  Conₘ-interchange {δ} (sucₘ {γ} ▸t) ▸suc x =
    case inv-usage-suc ▸suc of λ
      (invUsageSuc {δ = γ′} ▸t′ δ≤γ′) → sub
    (sucₘ (Conₘ-interchange ▸t ▸t′ x))
    (begin
       γ , x ≔ δ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ δ≤γ′ ⟩
       γ , x ≔ γ′ ⟨ x ⟩  ∎)
    where
    open CR

  Conₘ-interchange
    {δ = θ}
    (natrecₘ {γ} {δ} {p} {r} {η} ⦃ has-nr = nr₁ ⦄ ▸z ▸s ▸n ▸A) ▸nr x =
    let γ′ , δ′ , η′ , _ , ▸z′ , ▸s′ , ▸n′ , _ , θ≤ = inv-usage-natrec-has-nr ▸nr
    in  sub (natrecₘ (Conₘ-interchange ▸z ▸z′ x)
              (Conₘ-interchange ▸s ▸s′ (x +2))
              (Conₘ-interchange ▸n ▸n′ x) ▸A)
            (begin
               nrᶜ p r γ δ η , x ≔ θ ⟨ x ⟩                                  ≤⟨ update-monotoneʳ _ $ lookup-monotone _ θ≤ ⟩

               nrᶜ p r γ δ η , x ≔ nrᶜ p r γ′ δ′ η′ ⟨ x ⟩                   ≡⟨ cong (_ , _ ≔_) $ nrᶜ-⟨⟩ γ′ ⟩

               nrᶜ p r γ δ η , x ≔ nr p r (γ′ ⟨ x ⟩) (δ′ ⟨ x ⟩) (η′ ⟨ x ⟩)  ≡˘⟨ ≈ᶜ→≡ nrᶜ-,≔ ⟩

               nrᶜ p r (γ , x ≔ γ′ ⟨ x ⟩) (δ , x ≔ δ′ ⟨ x ⟩)
                (η , x ≔ η′ ⟨ x ⟩)                                         ∎)
    where
    open CR
    open import Graded.Usage.Restrictions.Instance R

  Conₘ-interchange
    {δ = θ}
    (natrec-no-nrₘ {γ} {δ} {p} {r} {η} {χ}
       ▸z ▸s ▸n ▸A χ≤γ χ≤δ χ≤η fix)
    ▸nr x =
    let γ′ , δ′ , η′ , _ , χ′ , ▸z′ , ▸s′ , ▸n′ , _
           , θ≤χ′ , χ′≤γ′ , χ′≤δ′ , χ′≤η′ , fix′ = inv-usage-natrec-no-nr ▸nr
    in  sub (natrec-no-nrₘ (Conₘ-interchange ▸z ▸z′ x)
               (Conₘ-interchange ▸s ▸s′ (x +2))
               (Conₘ-interchange ▸n ▸n′ x) ▸A
               (begin
                  χ , x ≔ χ′ ⟨ x ⟩  ≤⟨ update-monotone _ χ≤γ $ lookup-monotone _ χ′≤γ′ ⟩
                  γ , x ≔ γ′ ⟨ x ⟩  ∎)
               (λ ok → begin
                  χ , x ≔ χ′ ⟨ x ⟩  ≤⟨ update-monotone _ (χ≤δ ok) (lookup-monotone _ (χ′≤δ′ ok)) ⟩
                  δ , x ≔ δ′ ⟨ x ⟩  ∎)
               (λ ok → begin
                  χ , x ≔ χ′ ⟨ x ⟩  ≤⟨ update-monotone _ (χ≤η ok) (lookup-monotone _ (χ′≤η′ ok)) ⟩
                  η , x ≔ η′ ⟨ x ⟩  ∎)
               (begin
                  χ , x ≔ χ′ ⟨ x ⟩                                    ≤⟨ update-monotone _ fix (lookup-monotone _ fix′) ⟩

                  δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ ,
                  x ≔ (δ′ +ᶜ p ·ᶜ η′ +ᶜ r ·ᶜ χ′) ⟨ x ⟩                ≈⟨ update-congʳ $
                                                                         trans (lookup-distrib-+ᶜ δ′ _ _) $
                                                                         cong (δ′ ⟨ x ⟩ +_) $
                                                                         trans (lookup-distrib-+ᶜ (_ ·ᶜ η′) _ _) $
                                                                         cong₂ _+_
                                                                           (lookup-distrib-·ᶜ η′ _ _)
                                                                           (lookup-distrib-·ᶜ χ′ _ _) ⟩
                  δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ ,
                  x ≔ δ′ ⟨ x ⟩ + p · η′ ⟨ x ⟩ + r · χ′ ⟨ x ⟩          ≡⟨ trans (update-distrib-+ᶜ _ _ _ _ _) $
                                                                         cong (_ +ᶜ_) $
                                                                         trans (update-distrib-+ᶜ _ _ _ _ _) $
                                                                         cong₂ _+ᶜ_
                                                                           (update-distrib-·ᶜ _ _ _ _)
                                                                           (update-distrib-·ᶜ _ _ _ _) ⟩
                  (δ , x ≔ δ′ ⟨ x ⟩) +ᶜ
                  p ·ᶜ (η , x ≔ η′ ⟨ x ⟩) +ᶜ r ·ᶜ (χ , x ≔ χ′ ⟨ x ⟩)  ∎))
            (begin
              χ , x ≔ θ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ θ≤χ′ ⟩
              χ , x ≔ χ′ ⟨ x ⟩  ∎)
    where
    open CR

  Conₘ-interchange {δ = θ}
    (natrec-no-nr-glbₘ {η} {χ} {x = y} ▸z ▸s ▸n ▸A x-glb χ-glb) ▸nr x =
    let γ′ , δ′ , θ′ , _ , y′ , χ′
          , ▸z′ , ▸s′ , ▸n′ , ▸A′
          , θ≤ , x-glb′ , χ-glb′ = inv-usage-natrec-no-nr-glb ▸nr
    in  sub (natrec-no-nr-glbₘ (Conₘ-interchange ▸z ▸z′ x)
          (Conₘ-interchange ▸s ▸s′ (x +2))
          (Conₘ-interchange ▸n ▸n′ x) ▸A
          x-glb′
          (GLBᶜ-congˡ
            (λ i → ≈ᶜ-trans (update-congʳ (lookup-distrib-nrᵢᶜ _ γ′ δ′ x))
                    (update-distrib-nrᵢᶜ x))
            (Conₘ-interchange-GLBᶜ χ-glb χ-glb′ x))) $ begin
           y ·ᶜ η +ᶜ χ , x ≔ θ ⟨ x ⟩ ≤⟨ update-monotoneʳ x (lookup-monotone x θ≤) ⟩
           y ·ᶜ η +ᶜ χ , x ≔ (y′ ·ᶜ θ′ +ᶜ χ′) ⟨ x ⟩              ≈⟨ update-congˡ (+ᶜ-congʳ (·ᶜ-congʳ (GLB-unique x-glb x-glb′))) ⟩
           y′ ·ᶜ η +ᶜ χ , x ≔ (y′ ·ᶜ θ′ +ᶜ χ′) ⟨ x ⟩             ≈⟨ update-congʳ (lookup-distrib-+ᶜ (y′ ·ᶜ θ′) χ′ x) ⟩
           y′ ·ᶜ η +ᶜ χ , x ≔ ((y′ ·ᶜ θ′) ⟨ x ⟩ + χ′ ⟨ x ⟩)       ≡⟨ update-distrib-+ᶜ _ _ _ _ x ⟩
           (y′ ·ᶜ η , x ≔ (y′ ·ᶜ θ′) ⟨ x ⟩) +ᶜ (χ , x ≔ χ′ ⟨ x ⟩) ≈⟨ +ᶜ-congʳ (update-congʳ (lookup-distrib-·ᶜ θ′ _ x)) ⟩
           (y′ ·ᶜ η , x ≔ y′ · θ′ ⟨ x ⟩) +ᶜ (χ , x ≔ χ′ ⟨ x ⟩)    ≡⟨ cong (_+ᶜ _) (update-distrib-·ᶜ _ _ _ x) ⟩
           y′ ·ᶜ (η , x ≔ θ′ ⟨ x ⟩) +ᶜ (χ , x ≔ χ′ ⟨ x ⟩)         ∎
    where
    open CR

  Conₘ-interchange {δ = θ} (Idₘ {γ} {δ} {η} not-erased ▸A ▸t ▸u) ▸Id x =
    case inv-usage-Id ▸Id of λ where
      (invUsageId₀ erased _ _ _ _) →
        ⊥-elim $ not-erased erased
      (invUsageId {δ = γ′} {η = δ′} {θ = η′} _ ▸A′ ▸t′ ▸u′ θ≤γ′+δ′+η′) →
        sub
          (Idₘ not-erased (Conₘ-interchange ▸A ▸A′ x)
             (Conₘ-interchange ▸t ▸t′ x) (Conₘ-interchange ▸u ▸u′ x))
          (begin
             γ +ᶜ δ +ᶜ η , x ≔ θ ⟨ x ⟩                         ≤⟨ update-monotoneʳ _ $ lookup-monotone _ θ≤γ′+δ′+η′ ⟩

             γ +ᶜ δ +ᶜ η , x ≔ (γ′ +ᶜ δ′ +ᶜ η′) ⟨ x ⟩          ≡⟨ cong (_ , _ ≔_) $
                                                                  PE.trans (lookup-distrib-+ᶜ γ′ _ _) $
                                                                  PE.cong (_+_ _) $ lookup-distrib-+ᶜ δ′ _ _ ⟩

             γ +ᶜ δ +ᶜ η , x ≔ γ′ ⟨ x ⟩ + δ′ ⟨ x ⟩ + η′ ⟨ x ⟩  ≡⟨ PE.trans (update-distrib-+ᶜ _ _ _ _ _) $
                                                                  PE.cong (_+ᶜ_ _) $ update-distrib-+ᶜ _ _ _ _ _ ⟩
             (γ , x ≔ γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩) +ᶜ
             (η , x ≔ η′ ⟨ x ⟩)                                ∎)
    where
    open CR

  Conₘ-interchange {δ} (Id₀ₘ erased ▸A ▸t ▸u) ▸Id x =
    case inv-usage-Id ▸Id of λ where
      (invUsageId not-erased _ _ _ _) →
        ⊥-elim $ not-erased erased
      (invUsageId₀ _ _ ▸t′ ▸u′ γ≤𝟘) → sub
        (Id₀ₘ erased ▸A (Conₘ-interchange ▸t ▸t′ x)
           (Conₘ-interchange ▸u ▸u′ x))
        (begin
           𝟘ᶜ , x ≔ δ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ γ≤𝟘 ⟩
           𝟘ᶜ , x ≔ 𝟘ᶜ ⟨ x ⟩  ≡⟨ update-self _ _ ⟩
           𝟘ᶜ                 ∎)
    where
    open CR

  Conₘ-interchange {δ} rflₘ ▸rfl x = sub
    rflₘ
    (begin
       𝟘ᶜ , x ≔ δ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ $ inv-usage-rfl ▸rfl ⟩
       𝟘ᶜ , x ≔ 𝟘ᶜ ⟨ x ⟩  ≡⟨ update-self _ _ ⟩
       𝟘ᶜ                 ∎)
    where
    open CR

  Conₘ-interchange
    {δ = η}
    (Jₘ {γ₂} {γ₃} {γ₄} {γ₅} {γ₆} ≤some ok ▸A ▸t ▸F ▸u ▸v ▸w) ▸J x =
    case inv-usage-J ▸J of λ where
      (invUsageJ₀₁ ≡some p≡𝟘 q≡𝟘 _ _ _ _ _ _ _) →
        ⊥-elim $ ok ≡some (p≡𝟘 , q≡𝟘)
      (invUsageJ₀₂ ≡all _ _ _ _ _ _ _) →
        case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ()
      (invUsageJ {γ₂ = δ₂} {γ₃ = δ₃} {γ₄ = δ₄} {γ₅ = δ₅} {γ₆ = δ₆}
         _ _ _ ▸t′ ▸F′ ▸u′ ▸v′ ▸w′ η≤ω·) → sub
        (Jₘ ≤some ok ▸A (Conₘ-interchange ▸t ▸t′ x)
           (Conₘ-interchange ▸F ▸F′ (x +2)) (Conₘ-interchange ▸u ▸u′ x)
           (Conₘ-interchange ▸v ▸v′ x) (Conₘ-interchange ▸w ▸w′ x))
        (begin
           ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆) , x ≔ η ⟨ x ⟩  ≤⟨ update-monotoneʳ _ $ lookup-monotone _ η≤ω· ⟩

           ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆) ,
           x ≔ (ω ·ᶜ (δ₂ +ᶜ δ₃ +ᶜ δ₄ +ᶜ δ₅ +ᶜ δ₆)) ⟨ x ⟩    ≡⟨ Conₘ-interchange-J δ₂ δ₃ δ₄ δ₅ δ₆ ⟩

           ω ·ᶜ
           ((γ₂ , x ≔ δ₂ ⟨ x ⟩) +ᶜ (γ₃ , x ≔ δ₃ ⟨ x ⟩) +ᶜ
            (γ₄ , x ≔ δ₄ ⟨ x ⟩) +ᶜ (γ₅ , x ≔ δ₅ ⟨ x ⟩) +ᶜ
            (γ₆ , x ≔ δ₆ ⟨ x ⟩))                            ∎)
    where
    open CR

  Conₘ-interchange
    {δ = η} (J₀ₘ₁ {γ₃} {γ₄} ≡some p≡𝟘 q≡𝟘 ▸A ▸t ▸F ▸u ▸v ▸w) ▸J x =
    case inv-usage-J ▸J of λ where
      (invUsageJ _ ok _ _ _ _ _ _ _) →
        ⊥-elim $ ok ≡some (p≡𝟘 , q≡𝟘)
      (invUsageJ₀₂ ≡all _ _ _ _ _ _ _) →
        case trans (PE.sym ≡some) ≡all of λ ()
      (invUsageJ₀₁ {γ₃ = δ₃} {γ₄ = δ₄}
         _ _ _ _ ▸t′ ▸F′ ▸u′ ▸v′ ▸w′ η≤ω·) → sub
        (J₀ₘ₁ ≡some p≡𝟘 q≡𝟘 ▸A (Conₘ-interchange ▸t ▸t′ x)
           (Conₘ-interchange ▸F ▸F′ (x +2)) (Conₘ-interchange ▸u ▸u′ x)
           (Conₘ-interchange ▸v ▸v′ x) (Conₘ-interchange ▸w ▸w′ x))
        (begin
           ω ·ᶜ (γ₃ +ᶜ γ₄) , x ≔ η ⟨ x ⟩                      ≤⟨ update-monotoneʳ _ $ lookup-monotone _ η≤ω· ⟩
           ω ·ᶜ (γ₃ +ᶜ γ₄) , x ≔ (ω ·ᶜ (δ₃ +ᶜ δ₄)) ⟨ x ⟩      ≡⟨ Conₘ-interchange₀₁ δ₃ δ₄ ⟩
           ω ·ᶜ ((γ₃ , x ≔ δ₃ ⟨ x ⟩) +ᶜ (γ₄ , x ≔ δ₄ ⟨ x ⟩))  ∎)
    where
    open CR

  Conₘ-interchange {δ} (J₀ₘ₂ {γ₄} ≡all ▸A ▸t ▸F ▸u ▸v ▸w) ▸J x =
    case inv-usage-J ▸J of λ where
      (invUsageJ ≤some _ _ _ _ _ _ _ _) →
        case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ()
      (invUsageJ₀₁ ≡some _ _ _ _ _ _ _ _ _) →
        case trans (PE.sym ≡all) ≡some of λ ()
      (invUsageJ₀₂ {γ₄ = γ₄′} _ _ _ _ ▸u′ _ _ δ≤γ₄′) → sub
        (J₀ₘ₂ ≡all ▸A ▸t ▸F (Conₘ-interchange ▸u ▸u′ x) ▸v ▸w)
        (begin
           γ₄ , x ≔ δ ⟨ x ⟩    ≤⟨ update-monotoneʳ _ $ lookup-monotone _ δ≤γ₄′ ⟩
           γ₄ , x ≔ γ₄′ ⟨ x ⟩  ∎)
    where
    open CR

  Conₘ-interchange
    {δ = η} (Kₘ {γ₂} {γ₃} {γ₄} {γ₅} ≤some ok ▸A ▸t ▸F ▸u ▸v) ▸K x =
    case inv-usage-K ▸K of λ where
      (invUsageK₀₁ ≡some p≡𝟘 _ _ _ _ _ _) →
        ⊥-elim $ ok ≡some p≡𝟘
      (invUsageK₀₂ ≡all _ _ _ _ _ _) →
        case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ()
      (invUsageK {γ₂ = δ₂} {γ₃ = δ₃} {γ₄ = δ₄} {γ₅ = δ₅}
         _ _ _ ▸t′ ▸F′ ▸u′ ▸v′ η≤ω·) → sub
        (Kₘ ≤some ok ▸A (Conₘ-interchange ▸t ▸t′ x)
           (Conₘ-interchange ▸F ▸F′ (x +1)) (Conₘ-interchange ▸u ▸u′ x)
           (Conₘ-interchange ▸v ▸v′ x))
        (begin
           ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅) , x ≔ η ⟨ x ⟩       ≤⟨ update-monotoneʳ _ $ lookup-monotone _ η≤ω· ⟩

           ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅) ,
           x ≔ (ω ·ᶜ (δ₂ +ᶜ δ₃ +ᶜ δ₄ +ᶜ δ₅)) ⟨ x ⟩         ≡⟨ Conₘ-interchange-K δ₂ δ₃ δ₄ δ₅ ⟩

           ω ·ᶜ
           ((γ₂ , x ≔ δ₂ ⟨ x ⟩) +ᶜ (γ₃ , x ≔ δ₃ ⟨ x ⟩) +ᶜ
            (γ₄ , x ≔ δ₄ ⟨ x ⟩) +ᶜ (γ₅ , x ≔ δ₅ ⟨ x ⟩))    ∎)
    where
    open CR

  Conₘ-interchange
    {δ = η} (K₀ₘ₁ {γ₃} {γ₄} ≡some p≡𝟘 ▸A ▸t ▸F ▸u ▸v) ▸K x =
    case inv-usage-K ▸K of λ where
      (invUsageK _ ok _ _ _ _ _ _) →
        ⊥-elim $ ok ≡some p≡𝟘
      (invUsageK₀₂ ≡all _ _ _ _ _ _) →
        case trans (PE.sym ≡some) ≡all of λ ()
      (invUsageK₀₁ {γ₃ = δ₃} {γ₄ = δ₄} _ _ _ ▸t′ ▸F′ ▸u′ ▸v′ η≤ω·) → sub
        (K₀ₘ₁ ≡some p≡𝟘 ▸A (Conₘ-interchange ▸t ▸t′ x)
           (Conₘ-interchange ▸F ▸F′ (x +1)) (Conₘ-interchange ▸u ▸u′ x)
           (Conₘ-interchange ▸v ▸v′ x))
        (begin
           ω ·ᶜ (γ₃ +ᶜ γ₄) , x ≔ η ⟨ x ⟩                      ≤⟨ update-monotoneʳ _ $ lookup-monotone _ η≤ω· ⟩
           ω ·ᶜ (γ₃ +ᶜ γ₄) , x ≔ (ω ·ᶜ (δ₃ +ᶜ δ₄)) ⟨ x ⟩      ≡⟨ Conₘ-interchange₀₁ δ₃ δ₄ ⟩
           ω ·ᶜ ((γ₃ , x ≔ δ₃ ⟨ x ⟩) +ᶜ (γ₄ , x ≔ δ₄ ⟨ x ⟩))  ∎)
    where
    open CR

  Conₘ-interchange {δ} (K₀ₘ₂ {γ₄} ≡all ▸A ▸t ▸F ▸u ▸v) ▸K x =
    case inv-usage-K ▸K of λ where
      (invUsageK ≤some _ _ _ _ _ _ _) →
        case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ()
      (invUsageK₀₁ ≡some _ _ _ _ _ _ _) →
        case trans (PE.sym ≡all) ≡some of λ ()
      (invUsageK₀₂ {γ₄ = γ₄′} _ _ _ _ ▸u′ _ δ≤γ₄′) → sub
        (K₀ₘ₂ ≡all ▸A ▸t ▸F (Conₘ-interchange ▸u ▸u′ x) ▸v)
        (begin
           γ₄ , x ≔ δ ⟨ x ⟩    ≤⟨ update-monotoneʳ _ $ lookup-monotone _ δ≤γ₄′ ⟩
           γ₄ , x ≔ γ₄′ ⟨ x ⟩  ∎)
    where
    open CR

  Conₘ-interchange {δ} ([]-congₘ ▸A ▸t ▸u ▸v ok) ▸bc x =
    case inv-usage-[]-cong ▸bc of λ
      (invUsage-[]-cong _ _ _ _ _ δ≤𝟘) → sub
    ([]-congₘ ▸A ▸t ▸u ▸v ok)
    (begin
       𝟘ᶜ , x ≔ δ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ δ≤𝟘 ⟩
       𝟘ᶜ , x ≔ 𝟘ᶜ ⟨ x ⟩  ≡⟨ update-self _ _ ⟩
       𝟘ᶜ                 ∎)
    where
    open CR

-- Some variants of Conₘ-interchange

Conₘ-interchange₁ :
  γ ▸[ m ] t → δ ▸[ m ] t →
  tailₘ γ ∙ δ ⟨ x0 ⟩ ▸[ m ] t
Conₘ-interchange₁ {γ = γ} {m} {t} {δ} γ▸t δ▸t =
  subst (_▸[ m ] t) (update-head γ (δ ⟨ x0 ⟩))
        (Conₘ-interchange γ▸t δ▸t x0)


Conₘ-interchange₂ :
  γ ▸[ m ] t → δ ▸[ m ] t →
  tailₘ (tailₘ γ) ∙ δ ⟨ x1 ⟩ ∙ δ ⟨ x0 ⟩ ▸[ m ] t
Conₘ-interchange₂ {γ = γ} {m} {t} {δ} γ▸t δ▸t =
  subst (_▸[ m ] t) eq
        (Conₘ-interchange (Conₘ-interchange γ▸t δ▸t x1) δ▸t x0)
  where
  open Tools.Reasoning.PropositionalEquality
  δ₁ = δ ⟨ x1 ⟩
  δ₀ = δ ⟨ x0 ⟩
  eq = begin
    γ , x1 ≔ δ₁ , x0 ≔ δ₀ ≡⟨ update-head _ _ ⟩
    tailₘ (γ , x1 ≔ δ₁) ∙ δ₀ ≡⟨ cong (λ x → tailₘ x ∙ δ₀) (update-step γ δ₁ x0) ⟩
    (tailₘ γ , x0 ≔ δ₁) ∙ δ₀ ≡⟨ cong (_∙ _) (update-head (tailₘ γ) δ₁) ⟩
    tailₘ (tailₘ γ) ∙ δ₁ ∙ δ₀ ∎

------------------------------------------------------------------------
-- Variants of some usage rules

module _ where

  open import Graded.Usage.Restrictions.Instance R

  -- A variant of natrecₘ, natrec-no-nrₘ and natrec-no-nr-glbₘ.

  natrec-nr-or-no-nrₘ :
    γ ▸[ m ] t →
    δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] u →
    η ▸[ m ] v →
    θ ∙ ⌜ 𝟘ᵐ ⌝ · q ▸[ 𝟘ᵐ ] A →
    (⦃ has-nr : Nr-available ⦄ →
     χ ≤ᶜ nrᶜ p r γ δ η) →
    (⦃ no-nr : Nr-not-available ⦄ →
     χ ≤ᶜ γ ×
     (¬ Trivialᵐ →
      χ ≤ᶜ δ) ×
     ((Trivialᵐ → Has-well-behaved-zero semiring-with-meet) →
       χ ≤ᶜ η) ×
     χ ≤ᶜ δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ) →
    (⦃ no-nr : Nr-not-available-GLB ⦄ →
      ∃₂ λ x θ →
      Greatest-lower-bound x (nrᵢ r 𝟙 p) ×
      Greatest-lower-boundᶜ θ (nrᵢᶜ r γ δ) ×
      χ ≤ᶜ x ·ᶜ η +ᶜ θ) →
    χ ▸[ m ] natrec p q r A t u v
  natrec-nr-or-no-nrₘ ▸t ▸u ▸v ▸A hyp₁ hyp₂ hyp₃ =
    case natrec-mode? natrec-mode of λ where
      does-have-nr →
        sub (natrecₘ ▸t ▸u ▸v ▸A) hyp₁
      does-not-have-nr →
        let χ≤γ , χ≤δ , χ≤η , fix = hyp₂
        in  natrec-no-nrₘ ▸t ▸u ▸v ▸A χ≤γ χ≤δ χ≤η fix
      does-not-have-nr-glb →
        let _ , _ , x-glb , θ-glb , χ≤ = hyp₃
        in  sub (natrec-no-nr-glbₘ ▸t ▸u ▸v ▸A x-glb θ-glb) χ≤

opaque

  -- A variant of Idₘ and Id₀ₘ.

  Idₘ-generalised :
    γ₁ ▸[ m ] A →
    γ₂ ▸[ m ] t →
    γ₃ ▸[ m ] u →
    (Id-erased → δ ≤ᶜ 𝟘ᶜ) →
    (¬ Id-erased → δ ≤ᶜ γ₁ +ᶜ γ₂ +ᶜ γ₃) →
    δ ▸[ m ] Id A t u
  Idₘ-generalised ▸A ▸t ▸u δ≤𝟘ᶜ δ≤γ₁+γ₂+γ₃ =
    case Id-erased? of λ where
      (no not-erased) →
        sub (Idₘ not-erased ▸A ▸t ▸u) (δ≤γ₁+γ₂+γ₃ not-erased)
      (yes erased) →
        sub (Id₀ₘ erased (▸-𝟘 ▸A) (▸-𝟘 ▸t) (▸-𝟘 ▸u)) (δ≤𝟘ᶜ erased)

opaque

  -- A generalisation of the usage rule Jₘ:
  -- erased-matches-for-J m ≡ none and
  -- erased-matches-for-J m ≡ some → ¬ (p ≡ 𝟘 × q ≡ 𝟘) have been
  -- removed.

  Jₘ-generalised :
    γ₁ ▸[ 𝟘ᵐ ] A →
    γ₂ ▸[ m ] t →
    γ₃ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · q ▸[ m ] B →
    γ₄ ▸[ m ] u →
    γ₅ ▸[ m ] v →
    γ₆ ▸[ m ] w →
    ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆) ▸[ m ] J p q A t B u v w
  Jₘ-generalised
    {γ₂} {m} {γ₃} {p} {q} {B} {γ₄} {γ₅} {γ₆} ▸A ▸t ▸B ▸u ▸v ▸w
    with J-view p q m
  … | is-other ≤some ≢𝟘 =
    Jₘ ≤some ≢𝟘 ▸A ▸t ▸B ▸u ▸v ▸w
  … | is-some-yes ≡some (refl , refl) = sub
    (J₀ₘ₁ ≡some refl refl ▸A (▸-𝟘 ▸t)
       (sub ▸B $ begin
          γ₃ ∙ 𝟘 ∙ 𝟘                  ≈˘⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩
          γ₃ ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘  ∎)
       ▸u (▸-𝟘 ▸v) (▸-𝟘 ▸w))
    (begin
       ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)  ≤⟨ ≤ᶜ-trans ω·ᶜ+ᶜ≤ω·ᶜʳ $
                                             ≤ᶜ-trans (≤ᶜ-reflexive $ ≈ᶜ-sym $ ·ᶜ-congˡ $ +ᶜ-assoc _ _ _)
                                             ω·ᶜ+ᶜ≤ω·ᶜˡ ⟩
       ω ·ᶜ (γ₃ +ᶜ γ₄)                    ∎)
    where
    open CR
  Jₘ-generalised
    {γ₂} {m} {γ₃} {p} {q} {B} {γ₄} {γ₅} {γ₆} ▸A ▸t ▸B ▸u ▸v ▸w
    | is-all ≡all = sub
    (J₀ₘ₂ ≡all ▸A (▸-𝟘 ▸t)
      (sub (▸-𝟘 ▸B) (begin
        ⌜ 𝟘ᵐ ⌝ ·ᶜ γ₃ ∙ ⌜ 𝟘ᵐ ⌝ · p ∙ ⌜ 𝟘ᵐ ⌝ · q                 ≈⟨ ≈ᶜ-refl ∙ lemma ∙ lemma ⟩
        ⌜ 𝟘ᵐ ⌝ ·ᶜ γ₃ ∙ ⌜ 𝟘ᵐ ⌝ · ⌜ m ⌝ · p ∙ ⌜ 𝟘ᵐ ⌝ · ⌜ m ⌝ · q ∎))
       ▸u (▸-𝟘 ▸v) (▸-𝟘 ▸w))
    (begin
       ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)  ≤⟨ ≤ᶜ-trans ω·ᶜ+ᶜ≤ω·ᶜʳ $
                                             ≤ᶜ-trans ω·ᶜ+ᶜ≤ω·ᶜʳ
                                             ω·ᶜ+ᶜ≤ω·ᶜˡ ⟩
       ω ·ᶜ γ₄                            ≤⟨ ω·ᶜ-decreasing ⟩
       γ₄                                 ∎)
    where
    lemma : ∀ {p} → ⌜ 𝟘ᵐ ⌝ · p ≡ ⌜ 𝟘ᵐ ⌝ · ⌜ m ⌝ · p
    lemma {p} = begin
      ⌜ 𝟘ᵐ ⌝ · p           ≡˘⟨ ·-congʳ (⌜⌝-cong (·ᵐ-zeroˡ _)) ⟩
      ⌜ 𝟘ᵐ ·ᵐ m ⌝ · p      ≡⟨ ·-congʳ (⌜·ᵐ⌝ 𝟘ᵐ) ⟩
      (⌜ 𝟘ᵐ ⌝ · ⌜ m ⌝) · p ≡⟨ ·-assoc _ _ _ ⟩
      ⌜ 𝟘ᵐ ⌝ · ⌜ m ⌝ · p   ∎
      where
      open Tools.Reasoning.PropositionalEquality
    open ≤ᶜ-reasoning

opaque

  -- A generalisation of the usage rule J₀ₘ₁:
  -- erased-matches-for-J m ≡ some has been replaced by
  -- erased-matches-for-J m ≡ not-none sem.

  J₀ₘ₁-generalised :
    erased-matches-for-J m ≡ not-none sem →
    p ≡ 𝟘 →
    q ≡ 𝟘 →
    γ₁ ▸[ 𝟘ᵐ ] A →
    γ₂ ▸[ 𝟘ᵐ ] t →
    γ₃ ∙ 𝟘 ∙ 𝟘 ▸[ m ] B →
    γ₄ ▸[ m ] u →
    γ₅ ▸[ 𝟘ᵐ ] v →
    γ₆ ▸[ 𝟘ᵐ ] w →
    ω ·ᶜ (γ₃ +ᶜ γ₄) ▸[ m ] J p q A t B u v w
  J₀ₘ₁-generalised {m} {γ₃} {B} {γ₄} hyp refl refl ▸A ▸t ▸B ▸u ▸v ▸w
    with erased-matches-for-J m in ok
  … | none = case hyp of λ ()
  … | some = J₀ₘ₁ ok refl refl ▸A ▸t ▸B ▸u ▸v ▸w
  … | all  = sub
    (J₀ₘ₂ ok ▸A (▸-𝟘 ▸t)
       (▸-𝟘 ▸B) ▸u (▸-𝟘 ▸v) (▸-𝟘 ▸w))
    (begin
       ω ·ᶜ (γ₃ +ᶜ γ₄)  ≤⟨ ω·ᶜ+ᶜ≤ω·ᶜʳ ⟩
       ω ·ᶜ γ₄          ≤⟨ ω·ᶜ-decreasing ⟩
       γ₄               ∎)
    where
    open CR

opaque

  -- A generalisation of the usage rule Kₘ:
  -- erased-matches-for-K m ≤ᵉᵐ some and
  -- erased-matches-for-K m ≡ some → p ≢ 𝟘 have been removed.

  Kₘ-generalised :
    γ₁ ▸[ 𝟘ᵐ ] A →
    γ₂ ▸[ m ] t →
    γ₃ ∙ ⌜ m ⌝ · p ▸[ m ] B →
    γ₄ ▸[ m ] u →
    γ₅ ▸[ m ] v →
    ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅) ▸[ m ] K p A t B u v
  Kₘ-generalised {γ₂} {m} {γ₃} {p} {B} {γ₄} {γ₅} ▸A ▸t ▸B ▸u ▸v
    with K-view p m
  … | is-other ≤some ≢𝟘 =
    Kₘ ≤some ≢𝟘 ▸A ▸t ▸B ▸u ▸v
  … | is-some-yes ≡some refl = sub
    (K₀ₘ₁ ≡some refl ▸A (▸-𝟘 ▸t)
       (sub ▸B $ begin
          γ₃ ∙ 𝟘          ≈˘⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
          γ₃ ∙ ⌜ m ⌝ · 𝟘  ∎)
       ▸u (▸-𝟘 ▸v))
    (begin
       ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅)  ≤⟨ ≤ᶜ-trans ω·ᶜ+ᶜ≤ω·ᶜʳ $
                                       ≤ᶜ-trans (≤ᶜ-reflexive $ ≈ᶜ-sym $ ·ᶜ-congˡ $ +ᶜ-assoc _ _ _)
                                       ω·ᶜ+ᶜ≤ω·ᶜˡ ⟩
       ω ·ᶜ (γ₃ +ᶜ γ₄)              ∎)
    where
    open CR
  … | is-all ≡all = sub
    (K₀ₘ₂ ≡all ▸A (▸-𝟘 ▸t)
       (sub (▸-𝟘 ▸B) (begin
         ⌜ 𝟘ᵐ ⌝ ·ᶜ γ₃ ∙ ⌜ 𝟘ᵐ ⌝ · p          ≈⟨ ≈ᶜ-refl ∙ lemma ⟩
         ⌜ 𝟘ᵐ ⌝ ·ᶜ γ₃ ∙ ⌜ 𝟘ᵐ ⌝ · ⌜ m ⌝ · p  ∎))
       ▸u (▸-𝟘 ▸v))
    (begin
       ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅)  ≤⟨ ≤ᶜ-trans ω·ᶜ+ᶜ≤ω·ᶜʳ $
                                       ≤ᶜ-trans ω·ᶜ+ᶜ≤ω·ᶜʳ
                                       ω·ᶜ+ᶜ≤ω·ᶜˡ ⟩
       ω ·ᶜ γ₄                      ≤⟨ ω·ᶜ-decreasing ⟩
       γ₄                           ∎)
    where
    lemma : ∀ {p} → ⌜ 𝟘ᵐ ⌝ · p ≡ ⌜ 𝟘ᵐ ⌝ · ⌜ m ⌝ · p
    lemma {p} = begin
      ⌜ 𝟘ᵐ ⌝ · p           ≡˘⟨ ·-congʳ (⌜⌝-cong (·ᵐ-zeroˡ _)) ⟩
      ⌜ 𝟘ᵐ ·ᵐ m ⌝ · p      ≡⟨ ·-congʳ (⌜·ᵐ⌝ 𝟘ᵐ) ⟩
      (⌜ 𝟘ᵐ ⌝ · ⌜ m ⌝) · p ≡⟨ ·-assoc _ _ _ ⟩
      ⌜ 𝟘ᵐ ⌝ · ⌜ m ⌝ · p   ∎
      where
      open Tools.Reasoning.PropositionalEquality
    open CR

opaque

  -- A generalisation of the usage rule K₀ₘ₁:
  -- erased-matches-for-K m ≡ some has been replaced by
  -- erased-matches-for-K m ≡ not-none sem.

  K₀ₘ₁-generalised :
    erased-matches-for-K m ≡ not-none sem →
    p ≡ 𝟘 →
    γ₁ ▸[ 𝟘ᵐ ] A →
    γ₂ ▸[ 𝟘ᵐ ] t →
    γ₃ ∙ 𝟘 ▸[ m ] B →
    γ₄ ▸[ m ] u →
    γ₅ ▸[ 𝟘ᵐ ] v →
    ω ·ᶜ (γ₃ +ᶜ γ₄) ▸[ m ] K p A t B u v
  K₀ₘ₁-generalised {m} {γ₃} {B} {γ₄} hyp refl ▸A ▸t ▸B ▸u ▸v
    with erased-matches-for-K m in ok
  … | none = case hyp of λ ()
  … | some = K₀ₘ₁ ok refl ▸A ▸t ▸B ▸u ▸v
  … | all  = sub
    (K₀ₘ₂ ok ▸A (▸-𝟘 ▸t)
       (▸-𝟘 ▸B)
       ▸u (▸-𝟘 ▸v))
    (begin
       ω ·ᶜ (γ₃ +ᶜ γ₄)  ≤⟨ ω·ᶜ+ᶜ≤ω·ᶜʳ ⟩
       ω ·ᶜ γ₄          ≤⟨ ω·ᶜ-decreasing ⟩
       γ₄               ∎)
    where
    open CR

------------------------------------------------------------------------
-- Lemmas related to ⌈_⌉

opaque

  -- If nr functions are used then the usage inference function for
  -- natrec uses an nr function.

  ⌈⌉-natrec-nr :
    ⦃ has-nr : Natrec-mode-has-nr nm ⦄ →
    ⦃ ok : Natrec-mode-supports-usage-inference nm ⦄ →
    ⌈⌉-natrec p r γ δ η ≈ᶜ nrᶜ ⦃ Natrec-mode-Has-nr has-nr ⦄ p r γ δ η
  ⌈⌉-natrec-nr ⦃ has-nr ⦄ ⦃ ok = Nr ⦃ has-nr = has-nr′ ⦄ ⦄ =
    case Nr-available-propositional has-nr has-nr′ of λ where
      refl → ≈ᶜ-refl
  ⌈⌉-natrec-nr ⦃ has-nr ⦄ ⦃ ok = No-nr-glb ⦃ no-nr ⦄ _ ⦄ =
    ⊥-elim (¬[Nr∧No-nr-glb] has-nr no-nr)

opaque

  -- If neither nr functions nor greatest lower bounds are used for
  -- natrec then usage inference is not supported.

  ⌈⌉-natrec-no-nr :
    ⦃ no-nr : Natrec-mode-no-nr nm ⦄ →
    ⦃ ok : Natrec-mode-supports-usage-inference nm ⦄ →
    ⊥
  ⌈⌉-natrec-no-nr ⦃ no-nr ⦄ ⦃ ok = Nr ⦃ has-nr ⦄ ⦄ =
    ¬[Nr∧No-nr] has-nr no-nr
  ⌈⌉-natrec-no-nr ⦃ no-nr ⦄ ⦃ ok = No-nr-glb ⦃ no-nr = no-nr′ ⦄ _ ⦄ =
    ¬[No-nr∧No-nr-glb] no-nr no-nr′

opaque


  -- If greatest lower bounds are used for natrec then the usage
  -- inference function for natrec uses greatest lower bounds.

  ⌈⌉-natrec-no-nr-glb :
    ⦃ no-nr : Natrec-mode-no-nr-glb nm ⦄ →
    ⦃ ok : Natrec-mode-supports-usage-inference nm ⦄ →
    Σ ((r z s : M) → ∃ λ p → Greatest-lower-bound p (nrᵢ r z s)) λ has-GLB →
    ∀ {n p r} {γ δ η : Conₘ n} →
      ⌈⌉-natrec p r γ δ η ≈ᶜ (has-GLB r 𝟙 p .proj₁ ·ᶜ η +ᶜ nrᵢᶜ-has-GLBᶜ has-GLB r γ δ .proj₁)
  ⌈⌉-natrec-no-nr-glb ⦃ no-nr ⦄ ⦃ ok = Nr ⦃ has-nr ⦄ ⦄ =
    ⊥-elim (¬[Nr∧No-nr-glb] has-nr no-nr)
  ⌈⌉-natrec-no-nr-glb ⦃ ok = No-nr-glb has-GLB ⦄ =
    has-GLB , ≈ᶜ-refl

opaque

  -- The context ⌈ t ⌉ m does not change (up to _≈ᶜ_) if it is
  -- multiplied by ⌜ m ⌝.

  ·-⌈⌉ :
    ⦃ ok : Natrec-mode-supports-usage-inference natrec-mode ⦄ →
    (t : Term n) → ⌜ m ⌝ ·ᶜ ⌈ t ⌉ m ≈ᶜ ⌈ t ⌉ m
  ·-⌈⌉ {m} ⦃ ok ⦄ = λ where
      (var x) → begin
        ⌜ m ⌝ ·ᶜ (𝟘ᶜ , x ≔ ⌜ m ⌝)       ≡˘⟨ update-distrib-·ᶜ _ _ _ _ ⟩
        ⌜ m ⌝ ·ᶜ 𝟘ᶜ , x ≔ ⌜ m ⌝ · ⌜ m ⌝ ≈⟨ update-cong (·ᶜ-zeroʳ _) (·-idem-⌜⌝ _) ⟩
        𝟘ᶜ , x ≔ ⌜ m ⌝                  ∎
      (defn α) →
        ·ᶜ-zeroʳ _
      (U _) →
        ·ᶜ-zeroʳ _
      Empty →
        ·ᶜ-zeroʳ _
      (emptyrec _ _ t) →
        ·-⌈⌉-ᵐ· t
      Unit! →
        ·ᶜ-zeroʳ _
      star! →
        ·ᶜ-zeroʳ _
      (unitrec _ p _ _ t u) → begin
        ⌜ m ⌝ ·ᶜ (p ·ᶜ ⌈ t ⌉ (m ·ᵐ ⌞ p ⌟) +ᶜ ⌈ u ⌉ m)        ≈⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
        ⌜ m ⌝ ·ᶜ p ·ᶜ ⌈ t ⌉ (m ·ᵐ ⌞ p ⌟) +ᶜ ⌜ m ⌝ ·ᶜ ⌈ u ⌉ m ≈⟨ +ᶜ-cong (·-⌈⌉-ᵐ· t) (·-⌈⌉ u) ⟩
        p ·ᶜ ⌈ t ⌉ (m ·ᵐ ⌞ p ⌟) +ᶜ ⌈ u ⌉ m                   ∎
      (ΠΣ⟨ _ ⟩ _ , _ ▷ A ▹ B) → begin
        ⌜ m ⌝ ·ᶜ (⌈ A ⌉ m +ᶜ tailₘ (⌈ B ⌉ m))        ≈⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
        ⌜ m ⌝ ·ᶜ ⌈ A ⌉ m +ᶜ ⌜ m ⌝ ·ᶜ tailₘ (⌈ B ⌉ m) ≈˘⟨ +ᶜ-congˡ (tailₘ-distrib-·ᶜ _ (⌈ B ⌉ m)) ⟩
        ⌜ m ⌝ ·ᶜ ⌈ A ⌉ m +ᶜ tailₘ (⌜ m ⌝ ·ᶜ ⌈ B ⌉ m) ≈⟨ +ᶜ-cong (·-⌈⌉ A) (tailₘ-cong (·-⌈⌉ B)) ⟩
        ⌈ A ⌉ m +ᶜ tailₘ (⌈ B ⌉ m) ∎
      (lam _ t) → begin
        ⌜ m ⌝ ·ᶜ tailₘ (⌈ t ⌉ m) ≈˘⟨ tailₘ-distrib-·ᶜ _ (⌈ t ⌉ m) ⟩
        tailₘ (⌜ m ⌝ ·ᶜ ⌈ t ⌉ m) ≈⟨ tailₘ-cong (·-⌈⌉ t) ⟩
        tailₘ (⌈ t ⌉ m)          ∎
      (t ∘⟨ p ⟩ u) → begin
        ⌜ m ⌝ ·ᶜ (⌈ t ⌉ m +ᶜ p ·ᶜ ⌈ u ⌉ (m ·ᵐ ⌞ p ⌟))        ≈⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
        ⌜ m ⌝ ·ᶜ ⌈ t ⌉ m +ᶜ ⌜ m ⌝ ·ᶜ p ·ᶜ ⌈ u ⌉ (m ·ᵐ ⌞ p ⌟) ≈⟨ +ᶜ-cong (·-⌈⌉ t) (·-⌈⌉-ᵐ· u) ⟩
        ⌈ t ⌉ m +ᶜ p ·ᶜ ⌈ u ⌉ (m ·ᵐ ⌞ p ⌟) ∎
      (prodˢ p t u) → begin
        ⌜ m ⌝ ·ᶜ (p ·ᶜ ⌈ t ⌉ (m ·ᵐ ⌞ p ⌟) ∧ᶜ ⌈ u ⌉ m)        ≈⟨ ·ᶜ-distribˡ-∧ᶜ _ _ _ ⟩
        ⌜ m ⌝ ·ᶜ p ·ᶜ ⌈ t ⌉ (m ·ᵐ ⌞ p ⌟) ∧ᶜ ⌜ m ⌝ ·ᶜ ⌈ u ⌉ m ≈⟨ ∧ᶜ-cong (·-⌈⌉-ᵐ· t) (·-⌈⌉ u) ⟩
        p ·ᶜ ⌈ t ⌉ (m ·ᵐ ⌞ p ⌟) ∧ᶜ ⌈ u ⌉ m ∎
      (prodʷ p t u) → begin
        ⌜ m ⌝ ·ᶜ (p ·ᶜ ⌈ t ⌉ (m ·ᵐ ⌞ p ⌟) +ᶜ ⌈ u ⌉ m)        ≈⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
        ⌜ m ⌝ ·ᶜ p ·ᶜ ⌈ t ⌉ (m ·ᵐ ⌞ p ⌟) +ᶜ ⌜ m ⌝ ·ᶜ ⌈ u ⌉ m ≈⟨ +ᶜ-cong (·-⌈⌉-ᵐ· t) (·-⌈⌉ u) ⟩
        p ·ᶜ ⌈ t ⌉ (m ·ᵐ ⌞ p ⌟) +ᶜ ⌈ u ⌉ m ∎
      (fst _ t) →
        ·-⌈⌉ t
      (snd _ t) →
        ·-⌈⌉ t
      (prodrec r _ _ _ t u) → begin
        ⌜ m ⌝ ·ᶜ (r ·ᶜ ⌈ t ⌉ (m ·ᵐ ⌞ r ⌟) +ᶜ tailₘ (tailₘ (⌈ u ⌉ m)))        ≈⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
        ⌜ m ⌝ ·ᶜ r ·ᶜ ⌈ t ⌉ (m ·ᵐ ⌞ r ⌟) +ᶜ ⌜ m ⌝ ·ᶜ tailₘ (tailₘ (⌈ u ⌉ m)) ≈˘⟨ +ᶜ-congˡ (tailₘ-distrib-·ᶜ _ (tailₘ (⌈ u ⌉ m))) ⟩
        ⌜ m ⌝ ·ᶜ r ·ᶜ ⌈ t ⌉ (m ·ᵐ ⌞ r ⌟) +ᶜ tailₘ (⌜ m ⌝ ·ᶜ tailₘ (⌈ u ⌉ m)) ≈˘⟨ +ᶜ-congˡ (tailₘ-cong (tailₘ-distrib-·ᶜ _ (⌈ u ⌉ m))) ⟩
        ⌜ m ⌝ ·ᶜ r ·ᶜ ⌈ t ⌉ (m ·ᵐ ⌞ r ⌟) +ᶜ tailₘ (tailₘ (⌜ m ⌝ ·ᶜ ⌈ u ⌉ m)) ≈⟨ +ᶜ-cong (·-⌈⌉-ᵐ· t) (tailₘ-cong (tailₘ-cong (·-⌈⌉ u))) ⟩
        r ·ᶜ ⌈ t ⌉ (m ·ᵐ ⌞ r ⌟) +ᶜ tailₘ (tailₘ (⌈ u ⌉ m))                   ∎
      ℕ →
        ·ᶜ-zeroʳ _
      zero →
        ·ᶜ-zeroʳ _
      (suc t) →
        ·-⌈⌉ t
      (natrec _ _ _ _ z s n) →
        ·-⌈⌉-natrec z s n (natrec-mode? natrec-mode)
      (Id _ _ _) →
        ·-⌈⌉-Id
      rfl →
        ·ᶜ-zeroʳ _
      (J _ _ A _ _ _ _ _) → ·-⌈⌉-J {A = A}
      (K _ A _ _ _ _) → ·-⌈⌉-K {A = A}
      ([]-cong _ _ _ _ _) →
        ·ᶜ-zeroʳ _
    where
    open ≈ᶜ-reasoning
    open Graded.Usage.Restrictions.Instance R

    ·-⌈⌉-natrec :
      ∀ {k} (z : Term k) s n →
      Natrec-mode? natrec-mode →
      ⌜ m ⌝ ·ᶜ ⌈⌉-natrec ⦃ ok = ok ⦄ p r (⌈ z ⌉ m) (tailₘ (tailₘ (⌈ s ⌉ m))) (⌈ n ⌉ m) ≈ᶜ
      ⌈⌉-natrec ⦃ ok = ok ⦄ p r (⌈ z ⌉ m) (tailₘ (tailₘ (⌈ s ⌉ m))) (⌈ n ⌉ m)
    ·-⌈⌉-natrec {p} {r} z s n does-have-nr = begin
      ⌜ m ⌝ ·ᶜ ⌈⌉-natrec p r (⌈ z ⌉ m) (tailₘ (tailₘ (⌈ s ⌉ m))) (⌈ n ⌉ m)             ≈⟨ ·ᶜ-congˡ ⌈⌉-natrec-nr ⟩
      ⌜ m ⌝ ·ᶜ nrᶜ p r (⌈ z ⌉ m) (tailₘ (tailₘ (⌈ s ⌉ m))) (⌈ n ⌉ m)                   ≈⟨ ⌜⌝-·ᶜ-nrᶜ ⟩
      nrᶜ p r (⌜ m ⌝ ·ᶜ ⌈ z ⌉ m) (⌜ m ⌝ ·ᶜ tailₘ (tailₘ (⌈ s ⌉ m))) (⌜ m ⌝ ·ᶜ ⌈ n ⌉ m) ≈˘⟨ nrᶜ-cong ≈ᶜ-refl (tailₘ-distrib-·ᶜ _ (tailₘ (⌈ s ⌉ m))) ≈ᶜ-refl ⟩
      nrᶜ p r (⌜ m ⌝ ·ᶜ ⌈ z ⌉ m) (tailₘ (⌜ m ⌝ ·ᶜ tailₘ (⌈ s ⌉ m))) (⌜ m ⌝ ·ᶜ ⌈ n ⌉ m) ≈˘⟨ nrᶜ-cong ≈ᶜ-refl (tailₘ-cong (tailₘ-distrib-·ᶜ _ (⌈ s ⌉ m))) ≈ᶜ-refl ⟩
      nrᶜ p r (⌜ m ⌝ ·ᶜ ⌈ z ⌉ m) (tailₘ (tailₘ (⌜ m ⌝ ·ᶜ ⌈ s ⌉ m))) (⌜ m ⌝ ·ᶜ ⌈ n ⌉ m) ≈⟨ nrᶜ-cong (·-⌈⌉ z) (tailₘ-cong (tailₘ-cong (·-⌈⌉ s))) (·-⌈⌉ n) ⟩
      nrᶜ p r (⌈ z ⌉ m) (tailₘ (tailₘ (⌈ s ⌉ m))) (⌈ n ⌉ m)                            ≈˘⟨ ⌈⌉-natrec-nr ⟩
      ⌈⌉-natrec p r (⌈ z ⌉ m) (tailₘ (tailₘ (⌈ s ⌉ m))) (⌈ n ⌉ m) ∎
    ·-⌈⌉-natrec {p} {r} z s n does-not-have-nr = ⊥-elim ⌈⌉-natrec-no-nr
    ·-⌈⌉-natrec {p} {r} z s n does-not-have-nr-glb =
      let has-GLB , ⌈⌉-natrec≈ᶜ = ⌈⌉-natrec-no-nr-glb
          x , _ = has-GLB r 𝟙 p
          χ , χ-GLB = nrᵢᶜ-has-GLBᶜ has-GLB r (⌈ z ⌉ m) (tailₘ (tailₘ (⌈ s ⌉ m)))
          mnrᵢ≈ = λ i → begin
            ⌜ m ⌝ ·ᶜ nrᵢᶜ r (⌈ z ⌉ m) (tailₘ (tailₘ (⌈ s ⌉ m))) i          ≈⟨ ⌜⌝-·ᶜ-nrᵢᶜ i ⟩
            nrᵢᶜ r (⌜ m ⌝ ·ᶜ ⌈ z ⌉ m) (⌜ m ⌝ ·ᶜ tailₘ (tailₘ (⌈ s ⌉ m))) i ≈˘⟨ nrᵢᶜ-cong ≈ᶜ-refl (tailₘ-distrib-·ᶜ _ (tailₘ (⌈ s ⌉ m))) ⟩
            nrᵢᶜ r (⌜ m ⌝ ·ᶜ ⌈ z ⌉ m) (tailₘ (⌜ m ⌝ ·ᶜ tailₘ (⌈ s ⌉ m))) i ≈˘⟨ nrᵢᶜ-cong ≈ᶜ-refl (tailₘ-cong (tailₘ-distrib-·ᶜ _ (⌈ s ⌉ m))) ⟩
            nrᵢᶜ r (⌜ m ⌝ ·ᶜ ⌈ z ⌉ m) (tailₘ (tailₘ (⌜ m ⌝ ·ᶜ ⌈ s ⌉ m))) i ≈⟨ nrᵢᶜ-cong (·-⌈⌉ z) (tailₘ-cong (tailₘ-cong (·-⌈⌉ s))) ⟩
            nrᵢᶜ r (⌈ z ⌉ m) (tailₘ (tailₘ (⌈ s ⌉ m))) i ∎
          mχ-GLB = GLBᶜ-congˡ mnrᵢ≈ (·ᶜ-GLBᶜˡ χ-GLB)
      in  begin
        ⌜ m ⌝ ·ᶜ ⌈⌉-natrec p r (⌈ z ⌉ m) (tailₘ (tailₘ (⌈ s ⌉ m))) (⌈ n ⌉ m) ≈⟨ ·ᶜ-congˡ ⌈⌉-natrec≈ᶜ ⟩
        ⌜ m ⌝ ·ᶜ (x ·ᶜ ⌈ n ⌉ m +ᶜ χ)                                         ≈⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
        ⌜ m ⌝ ·ᶜ x ·ᶜ ⌈ n ⌉ m +ᶜ ⌜ m ⌝ ·ᶜ χ                                  ≈⟨ +ᶜ-congʳ (⌜⌝·ᶜ-comm _ _ _) ⟩
        x ·ᶜ ⌜ m ⌝ ·ᶜ ⌈ n ⌉ m +ᶜ ⌜ m ⌝ ·ᶜ χ                                  ≈⟨ +ᶜ-cong (·ᶜ-congˡ (·-⌈⌉ n)) (GLBᶜ-unique mχ-GLB χ-GLB) ⟩
        x ·ᶜ ⌈ n ⌉ m +ᶜ χ                                                    ≈˘⟨ ⌈⌉-natrec≈ᶜ ⟩
        ⌈⌉-natrec p r (⌈ z ⌉ m) (tailₘ (tailₘ (⌈ s ⌉ m))) (⌈ n ⌉ m)          ∎

    ·-⌈⌉-Id : (⌜ m ⌝ ·ᶜ ⌈ Id A t u ⌉ m) ≈ᶜ ⌈ Id A t u ⌉ m
    ·-⌈⌉-Id {A} {t} {u} with Id-erased?
    … | yes _ = ·ᶜ-zeroʳ _
    … | no _ = begin
      ⌜ m ⌝ ·ᶜ (⌈ A ⌉ m +ᶜ ⌈ t ⌉ m +ᶜ ⌈ u ⌉ m)                 ≈⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
      ⌜ m ⌝ ·ᶜ ⌈ A ⌉ m +ᶜ ⌜ m ⌝ ·ᶜ (⌈ t ⌉ m +ᶜ ⌈ u ⌉ m)        ≈⟨ +ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
      ⌜ m ⌝ ·ᶜ ⌈ A ⌉ m +ᶜ ⌜ m ⌝ ·ᶜ ⌈ t ⌉ m +ᶜ ⌜ m ⌝ ·ᶜ ⌈ u ⌉ m ≈⟨ +ᶜ-cong (·-⌈⌉ A) (+ᶜ-cong (·-⌈⌉ t) (·-⌈⌉ u)) ⟩
      ⌈ A ⌉ m +ᶜ ⌈ t ⌉ m +ᶜ ⌈ u ⌉ m                            ∎

    ·-⌈⌉-J : ⌜ m ⌝ ·ᶜ ⌈ J p q A t B u v w ⌉ m ≈ᶜ ⌈ J p q A t B u v w ⌉ m
    ·-⌈⌉-J {p} {q} {t} {B} {u} {v} {w} with J-view p q m
    … | is-all _ = ·-⌈⌉ u
    … | is-some-yes _ _ = begin
      ⌜ m ⌝ ·ᶜ ω ·ᶜ (tailₘ (tailₘ (⌈ B ⌉ m)) +ᶜ ⌈ u ⌉ m)          ≈⟨ ⌜⌝·ᶜ-comm _ _ _ ⟩
      ω ·ᶜ ⌜ m ⌝ ·ᶜ (tailₘ (tailₘ (⌈ B ⌉ m)) +ᶜ ⌈ u ⌉ m)          ≈⟨ ·ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
      ω ·ᶜ (⌜ m ⌝ ·ᶜ tailₘ (tailₘ (⌈ B ⌉ m)) +ᶜ ⌜ m ⌝ ·ᶜ ⌈ u ⌉ m) ≈˘⟨ ·ᶜ-congˡ (+ᶜ-congʳ (tailₘ-distrib-·ᶜ _ (tailₘ (⌈ B ⌉ m)))) ⟩
      ω ·ᶜ (tailₘ (⌜ m ⌝ ·ᶜ tailₘ (⌈ B ⌉ m)) +ᶜ ⌜ m ⌝ ·ᶜ ⌈ u ⌉ m) ≈˘⟨ ·ᶜ-congˡ (+ᶜ-congʳ (tailₘ-cong (tailₘ-distrib-·ᶜ _ (⌈ B ⌉ m)))) ⟩
      ω ·ᶜ (tailₘ (tailₘ (⌜ m ⌝ ·ᶜ ⌈ B ⌉ m)) +ᶜ ⌜ m ⌝ ·ᶜ ⌈ u ⌉ m) ≈⟨ ·ᶜ-congˡ (+ᶜ-cong (tailₘ-cong (tailₘ-cong (·-⌈⌉ B))) (·-⌈⌉ u)) ⟩
      ω ·ᶜ (tailₘ (tailₘ (⌈ B ⌉ m)) +ᶜ ⌈ u ⌉ m)                   ∎
    … | is-other _ _ = begin
      ⌜ m ⌝ ·ᶜ ω ·ᶜ (⌈ t ⌉ m +ᶜ tailₘ (tailₘ (⌈ B ⌉ m)) +ᶜ ⌈ u ⌉ m +ᶜ ⌈ v ⌉ m +ᶜ ⌈ w ⌉ m)
        ≈⟨ ⌜⌝·ᶜ-comm _ _ _ ⟩
      ω ·ᶜ ⌜ m ⌝ ·ᶜ (⌈ t ⌉ m +ᶜ tailₘ (tailₘ (⌈ B ⌉ m)) +ᶜ ⌈ u ⌉ m +ᶜ ⌈ v ⌉ m +ᶜ ⌈ w ⌉ m)
        ≈⟨ ·ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
      ω ·ᶜ (⌜ m ⌝ ·ᶜ ⌈ t ⌉ m +ᶜ ⌜ m ⌝ ·ᶜ (tailₘ (tailₘ (⌈ B ⌉ m)) +ᶜ ⌈ u ⌉ m +ᶜ ⌈ v ⌉ m +ᶜ ⌈ w ⌉ m))
        ≈⟨ ·ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _)) ⟩
      ω ·ᶜ (⌜ m ⌝ ·ᶜ ⌈ t ⌉ m +ᶜ ⌜ m ⌝ ·ᶜ tailₘ (tailₘ (⌈ B ⌉ m)) +ᶜ ⌜ m ⌝ ·ᶜ (⌈ u ⌉ m +ᶜ ⌈ v ⌉ m +ᶜ ⌈ w ⌉ m))
        ≈⟨ ·ᶜ-congˡ (+ᶜ-congˡ (+ᶜ-cong (≈ᶜ-sym (tailₘ-distrib-·ᶜ _ (tailₘ (⌈ B ⌉ m)))) (·ᶜ-distribˡ-+ᶜ _ _ _))) ⟩
      ω ·ᶜ (⌜ m ⌝ ·ᶜ ⌈ t ⌉ m +ᶜ tailₘ (⌜ m ⌝ ·ᶜ tailₘ (⌈ B ⌉ m)) +ᶜ ⌜ m ⌝ ·ᶜ ⌈ u ⌉ m +ᶜ ⌜ m ⌝ ·ᶜ (⌈ v ⌉ m +ᶜ ⌈ w ⌉ m))
        ≈⟨ ·ᶜ-congˡ (+ᶜ-congˡ (+ᶜ-cong (tailₘ-cong (≈ᶜ-sym (tailₘ-distrib-·ᶜ _ (⌈ B ⌉ m)))) (+ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _)))) ⟩
      ω ·ᶜ (⌜ m ⌝ ·ᶜ ⌈ t ⌉ m +ᶜ tailₘ (tailₘ (⌜ m ⌝ ·ᶜ ⌈ B ⌉ m)) +ᶜ ⌜ m ⌝ ·ᶜ ⌈ u ⌉ m +ᶜ ⌜ m ⌝ ·ᶜ ⌈ v ⌉ m +ᶜ ⌜ m ⌝ ·ᶜ ⌈ w ⌉ m)
        ≈⟨ ·ᶜ-congˡ (+ᶜ-cong (·-⌈⌉ t) (+ᶜ-cong (tailₘ-cong (tailₘ-cong (·-⌈⌉ B))) (+ᶜ-cong (·-⌈⌉ u) (+ᶜ-cong (·-⌈⌉ v) (·-⌈⌉ w))))) ⟩
      ω ·ᶜ (⌈ t ⌉ m +ᶜ tailₘ (tailₘ (⌈ B ⌉ m)) +ᶜ ⌈ u ⌉ m +ᶜ ⌈ v ⌉ m +ᶜ ⌈ w ⌉ m) ∎

    ·-⌈⌉-K : ⌜ m ⌝ ·ᶜ ⌈ K p A t B u v ⌉ m ≈ᶜ ⌈ K p A t B u v ⌉ m
    ·-⌈⌉-K {p} {t} {B} {u} {v} with K-view p m
    … | is-all _ = ·-⌈⌉ u
    … | is-some-yes _ _ = begin
      ⌜ m ⌝ ·ᶜ ω ·ᶜ (tailₘ (⌈ B ⌉ m) +ᶜ ⌈ u ⌉ m)          ≈⟨ ⌜⌝·ᶜ-comm _ _ _ ⟩
      ω ·ᶜ ⌜ m ⌝ ·ᶜ (tailₘ (⌈ B ⌉ m) +ᶜ ⌈ u ⌉ m)          ≈⟨ ·ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
      ω ·ᶜ (⌜ m ⌝ ·ᶜ tailₘ (⌈ B ⌉ m) +ᶜ ⌜ m ⌝ ·ᶜ ⌈ u ⌉ m) ≈˘⟨ ·ᶜ-congˡ (+ᶜ-congʳ (tailₘ-distrib-·ᶜ _ (⌈ B ⌉ m))) ⟩
      ω ·ᶜ (tailₘ (⌜ m ⌝ ·ᶜ ⌈ B ⌉ m) +ᶜ ⌜ m ⌝ ·ᶜ ⌈ u ⌉ m) ≈⟨ ·ᶜ-congˡ (+ᶜ-cong (tailₘ-cong (·-⌈⌉ B)) (·-⌈⌉ u)) ⟩
      ω ·ᶜ (tailₘ (⌈ B ⌉ m) +ᶜ ⌈ u ⌉ m)                   ∎
    … | is-other _ _ = begin
      ⌜ m ⌝ ·ᶜ ω ·ᶜ (⌈ t ⌉ m +ᶜ tailₘ (⌈ B ⌉ m) +ᶜ ⌈ u ⌉ m +ᶜ ⌈ v ⌉ m)
        ≈⟨ ⌜⌝·ᶜ-comm _ _ _ ⟩
      ω ·ᶜ ⌜ m ⌝ ·ᶜ (⌈ t ⌉ m +ᶜ tailₘ (⌈ B ⌉ m) +ᶜ ⌈ u ⌉ m +ᶜ ⌈ v ⌉ m)
        ≈⟨ ·ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
      ω ·ᶜ (⌜ m ⌝ ·ᶜ ⌈ t ⌉ m +ᶜ ⌜ m ⌝ ·ᶜ (tailₘ (⌈ B ⌉ m) +ᶜ ⌈ u ⌉ m +ᶜ ⌈ v ⌉ m))
        ≈⟨ ·ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _)) ⟩
      ω ·ᶜ (⌜ m ⌝ ·ᶜ ⌈ t ⌉ m +ᶜ ⌜ m ⌝ ·ᶜ tailₘ (⌈ B ⌉ m) +ᶜ ⌜ m ⌝ ·ᶜ (⌈ u ⌉ m +ᶜ ⌈ v ⌉ m))
        ≈⟨ ·ᶜ-congˡ (+ᶜ-congˡ (+ᶜ-cong (≈ᶜ-sym (tailₘ-distrib-·ᶜ _ (⌈ B ⌉ m))) (·ᶜ-distribˡ-+ᶜ _ _ _))) ⟩
      ω ·ᶜ (⌜ m ⌝ ·ᶜ ⌈ t ⌉ m +ᶜ tailₘ (⌜ m ⌝ ·ᶜ ⌈ B ⌉ m) +ᶜ ⌜ m ⌝ ·ᶜ ⌈ u ⌉ m +ᶜ ⌜ m ⌝ ·ᶜ ⌈ v ⌉ m)
        ≈⟨ ·ᶜ-congˡ (+ᶜ-cong (·-⌈⌉ t) (+ᶜ-cong (tailₘ-cong (·-⌈⌉ B)) (+ᶜ-cong (·-⌈⌉ u) (·-⌈⌉ v)))) ⟩
      ω ·ᶜ (⌈ t ⌉ m +ᶜ tailₘ (⌈ B ⌉ m) +ᶜ ⌈ u ⌉ m +ᶜ ⌈ v ⌉ m) ∎

    ·-⌈⌉-ᵐ· : (t : Term n) → ⌜ m ⌝ ·ᶜ p ·ᶜ ⌈ t ⌉ (m ᵐ· p) ≈ᶜ p ·ᶜ ⌈ t ⌉ (m ᵐ· p)
    ·-⌈⌉-ᵐ· {p} t = begin
      ⌜ m ⌝ ·ᶜ p ·ᶜ ⌈ t ⌉ (m ᵐ· p)               ≈⟨ ⌜⌝·ᶜ-comm _ _ _ ⟩
      p ·ᶜ ⌜ m ⌝ ·ᶜ ⌈ t ⌉ (m ᵐ· p)               ≈˘⟨ ·ᶜ-congʳ ·⌜⌞⌟⌝ ⟩
      (p · ⌜ ⌞ p ⌟ ⌝) ·ᶜ ⌜ m ⌝ ·ᶜ ⌈ t ⌉ (m ᵐ· p) ≈⟨ ·ᶜ-assoc _ _ _ ⟩
      p ·ᶜ ⌜ ⌞ p ⌟ ⌝ ·ᶜ ⌜ m ⌝ ·ᶜ ⌈ t ⌉ (m ᵐ· p)  ≈˘⟨ ·ᶜ-congˡ (·ᶜ-assoc _ _ _) ⟩
      p ·ᶜ (⌜ ⌞ p ⌟ ⌝ · ⌜ m ⌝) ·ᶜ ⌈ t ⌉ (m ᵐ· p) ≈˘⟨ ·ᶜ-congˡ (·ᶜ-congʳ (⌜·ᵐ⌝ _)) ⟩
      p ·ᶜ (⌜ ⌞ p ⌟ ·ᵐ m ⌝) ·ᶜ ⌈ t ⌉ (m ᵐ· p)    ≈⟨ ·ᶜ-congˡ (·ᶜ-congʳ (⌜⌝-cong (·ᵐ-comm _ _))) ⟩
      p ·ᶜ (⌜ m ·ᵐ ⌞ p ⌟ ⌝) ·ᶜ ⌈ t ⌉ (m ᵐ· p)    ≡⟨⟩
      p ·ᶜ (⌜ m ᵐ· p ⌝) ·ᶜ ⌈ t ⌉ (m ᵐ· p)        ≈⟨ ·ᶜ-congˡ (·-⌈⌉ t) ⟩
      p ·ᶜ ⌈ t ⌉ (m ᵐ· p)                        ∎

opaque

  -- If the mode structure is not trivial then
  -- the context ⌈ t ⌉ 𝟘ᵐ is equivalent to 𝟘ᶜ.

  ⌈⌉-𝟘ᵐ :
    ⦃ ok : Natrec-mode-supports-usage-inference natrec-mode ⦄ →
    ¬ Trivialᵐ →
    (t : Term n) → ⌈ t ⌉ 𝟘ᵐ ≈ᶜ 𝟘ᶜ
  ⌈⌉-𝟘ᵐ not-trivial t = begin
    ⌈ t ⌉ 𝟘ᵐ           ≈˘⟨ ·-⌈⌉ t ⟩
    ⌜ 𝟘ᵐ ⌝ ·ᶜ ⌈ t ⌉ 𝟘ᵐ ≈⟨ ·ᶜ-congʳ (⌜𝟘ᵐ⌝ not-trivial) ⟩
    𝟘 ·ᶜ ⌈ t ⌉ 𝟘ᵐ      ≈⟨ ·ᶜ-zeroˡ _ ⟩
    𝟘ᶜ                 ∎
    where
    open ≈ᶜ-reasoning

-- For dedicated nr functions the function ⌈_⌉ provides upper bounds
-- for valid modality contexts if strong unit types are not allowed to
-- be used as sinks, or if 𝟘 is a greatest grade.

usage-upper-bound :
  ⦃ ok : Natrec-mode-supports-usage-inference natrec-mode ⦄ →
  ¬ Starˢ-sink ⊎ (∀ {p} → p ≤ 𝟘) →
  γ ▸[ m ] t → γ ≤ᶜ ⌈ t ⌉ m
usage-upper-bound ⦃ ok ⦄ ok′ = usage-upper-bound′
  where
  usage-upper-bound′ : γ ▸[ m ] t → γ ≤ᶜ ⌈ t ⌉ m
  usage-upper-bound′ Uₘ     = ≤ᶜ-refl
  usage-upper-bound′ ℕₘ     = ≤ᶜ-refl
  usage-upper-bound′ Emptyₘ = ≤ᶜ-refl
  usage-upper-bound′ Unitₘ  = ≤ᶜ-refl

  usage-upper-bound′ (ΠΣₘ {G = G} ▸F ▸G) =
    +ᶜ-monotone (usage-upper-bound′ ▸F)
                (subst (_ ≈ᶜ_) (tailₘ-distrib-∧ᶜ (_ ∙ _) (⌈ G ⌉ _))
                       (tailₘ-cong (usage-upper-bound′ ▸G)))

  usage-upper-bound′ var = ≤ᶜ-refl

  usage-upper-bound′ defn = ≤ᶜ-refl

  usage-upper-bound′ (lamₘ {t = t} ▸t) =
    subst (_ ≈ᶜ_) (tailₘ-distrib-∧ᶜ (_ ∙ _) (⌈ t ⌉ _))
      (tailₘ-cong (usage-upper-bound′ ▸t))

  usage-upper-bound′ (▸t ∘ₘ ▸u) =
    +ᶜ-monotone (usage-upper-bound′ ▸t)
      (·ᶜ-monotoneʳ (usage-upper-bound′ ▸u))

  usage-upper-bound′ (prodʷₘ t u) =
    +ᶜ-monotone (·ᶜ-monotoneʳ (usage-upper-bound′ t))
      (usage-upper-bound′ u)
  usage-upper-bound′ (prodˢₘ t u) =
    ∧ᶜ-monotone (·ᶜ-monotoneʳ (usage-upper-bound′ t))
      (usage-upper-bound′ u)
  usage-upper-bound′ (fstₘ _ t PE.refl _) = usage-upper-bound′ t
  usage-upper-bound′ (sndₘ t) = usage-upper-bound′ t
  usage-upper-bound′ (prodrecₘ t u A _) =
    +ᶜ-monotone (·ᶜ-monotoneʳ (usage-upper-bound′ t))
                (tailₘ-monotone (tailₘ-monotone (usage-upper-bound′ u)))

  usage-upper-bound′ zeroₘ    = ≤ᶜ-refl
  usage-upper-bound′ (sucₘ t) = usage-upper-bound′ t

  usage-upper-bound′ {m}
    (natrecₘ {γ} {z} {δ} {p} {r} {η} {q} {A} {s} {n} ⦃ has-nr ⦄ γ▸z δ▸s η▸n θ▸A) =
    let open ≤ᶜ-reasoning
        open Graded.Usage.Restrictions.Instance R
        γ≤γ′ = usage-upper-bound′ γ▸z
        δ≤δ′ = tailₘ-monotone $ tailₘ-monotone $ usage-upper-bound′ δ▸s
        η≤η′ = usage-upper-bound′ η▸n
    in  begin
      nrᶜ p r γ δ η                                                ≤⟨ nrᶜ-monotone γ≤γ′ δ≤δ′ η≤η′ ⟩
      nrᶜ p r (⌈ z ⌉ m) (tailₘ (tailₘ (⌈ s ⌉ m))) (⌈ n ⌉ m)       ≈˘⟨ ⌈⌉-natrec-nr ⟩
      ⌈⌉-natrec p r (⌈ z ⌉ m) (tailₘ (tailₘ (⌈ s ⌉ m))) (⌈ n ⌉ m) ∎

  usage-upper-bound′ (natrec-no-nrₘ ⦃ no-nr ⦄ _ _ _ _ _ _ _ _) =
    ⊥-elim ⌈⌉-natrec-no-nr

  usage-upper-bound′ {m} (natrec-no-nr-glbₘ {γ} {z} {δ} {p} {r} {η} {q} {A} {χ} {n} {s} {x} ⦃ no-nr ⦄ ▸z ▸s ▸n ▸A x-GLB χ-GLB) =
    let open ≤ᶜ-reasoning
        has-GLB , ⌈⌉-natrec≈ᶜ = ⌈⌉-natrec-no-nr-glb
        x′ , x′-GLB = has-GLB r 𝟙 p
        χ′ , χ′-GLB = nrᵢᶜ-has-GLBᶜ has-GLB r (⌈ z ⌉ m) (tailₘ (tailₘ (⌈ s ⌉ m)))
        γ≤γ′ = usage-upper-bound′ ▸z
        δ≤δ′ = tailₘ-monotone $ tailₘ-monotone $ usage-upper-bound′ ▸s
        η≤η′ = usage-upper-bound′ ▸n
    in  begin
      x ·ᶜ η +ᶜ χ                                                 ≤⟨ +ᶜ-monotone (·ᶜ-monotoneʳ η≤η′)
                                                                     (GLBᶜ-monotone (λ _ → nrᵢᶜ-monotone γ≤γ′ δ≤δ′) χ-GLB χ′-GLB) ⟩
      x ·ᶜ ⌈ n ⌉ m +ᶜ χ′                                          ≈⟨ +ᶜ-congʳ (·ᶜ-congʳ (GLB-unique x-GLB x′-GLB)) ⟩
      x′ ·ᶜ ⌈ n ⌉ m +ᶜ χ′                                         ≈˘⟨ ⌈⌉-natrec≈ᶜ ⟩
      ⌈⌉-natrec p r (⌈ z ⌉ m) (tailₘ (tailₘ (⌈ s ⌉ m))) (⌈ n ⌉ m) ∎

  usage-upper-bound′ (emptyrecₘ e A _) =
    ·ᶜ-monotoneʳ (usage-upper-bound′ e)

  usage-upper-bound′ starʷₘ = ≤ᶜ-refl
  usage-upper-bound′ {m} (starˢₘ {γ} {l} hyp) =
    case ok′ of λ where
      (inj₁ no-sink) → begin
        ⌜ m ⌝ ·ᶜ γ   ≈˘⟨ ·ᶜ-congˡ (hyp no-sink) ⟩
        ⌜ m ⌝ ·ᶜ 𝟘ᶜ  ≈⟨ ·ᶜ-zeroʳ _ ⟩
        𝟘ᶜ           ∎
      (inj₂ ≤𝟘) → begin
        ⌜ m ⌝ ·ᶜ γ   ≤⟨ ·ᶜ-monotoneʳ (≤ᶜ𝟘ᶜ ≤𝟘) ⟩
        ⌜ m ⌝ ·ᶜ 𝟘ᶜ  ≈⟨ ·ᶜ-zeroʳ _ ⟩
        𝟘ᶜ           ∎
    where
    open ≤ᶜ-reasoning

  usage-upper-bound′ (unitrecₘ t u A ok) =
    +ᶜ-monotone (·ᶜ-monotoneʳ (usage-upper-bound′ t))
      (usage-upper-bound′ u)

  usage-upper-bound′ {m} (Idₘ {γ} {A} {δ} {t} {η} {u} not-ok ▸A ▸t ▸u)
    with Id-erased?
  … | yes ok = ⊥-elim (not-ok ok)
  … | no _   = begin
    γ +ᶜ δ +ᶜ η                    ≤⟨ +ᶜ-monotone (usage-upper-bound′ ▸A) $
                                      +ᶜ-monotone (usage-upper-bound′ ▸t) (usage-upper-bound′ ▸u) ⟩
    ⌈ A ⌉ m +ᶜ ⌈ t ⌉ m +ᶜ ⌈ u ⌉ m  ∎
    where
    open ≤ᶜ-reasoning

  usage-upper-bound′ (Id₀ₘ ok _ _ _) with Id-erased?
  … | no not-ok = ⊥-elim (not-ok ok)
  … | yes _     = ≤ᶜ-refl

  usage-upper-bound′ rflₘ =
    ≤ᶜ-refl

  usage-upper-bound′
    {m}
    (Jₘ {p} {q} {γ₂} {t} {γ₃} {B} {γ₄} {u} {γ₅} {v} {γ₆} {w}
       ≤some ok _ ▸t ▸B ▸u ▸v ▸w)
    with J-view p q m
  … | is-all ≡all               = case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ()
  … | is-some-yes ≡some p≡𝟘×q≡𝟘 = ⊥-elim $ ok ≡some p≡𝟘×q≡𝟘
  … | is-other _ _              = begin
    ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)                           ≤⟨ ·ᶜ-monotoneʳ $
                                                                   +ᶜ-monotone (usage-upper-bound′ ▸t) $
                                                                   +ᶜ-monotone (tailₘ-monotone (tailₘ-monotone (usage-upper-bound′ ▸B))) $
                                                                   +ᶜ-monotone (usage-upper-bound′ ▸u) $
                                                                   +ᶜ-monotone (usage-upper-bound′ ▸v) $
                                                                   usage-upper-bound′ ▸w ⟩
    ω ·ᶜ
    (⌈ t ⌉ m +ᶜ
     tailₘ (tailₘ (⌈ B ⌉ m)) +ᶜ ⌈ u ⌉ m +ᶜ ⌈ v ⌉ m +ᶜ ⌈ w ⌉ m)  ∎
    where
    open ≤ᶜ-reasoning

  usage-upper-bound′
    {m} (J₀ₘ₁ {p} {q} {γ₃} {B} {γ₄} {u} ≡some p≡𝟘 q≡𝟘 _ ▸t ▸B ▸u ▸v ▸w)
    with J-view p q m
  … | is-all ≡all     = case trans (PE.sym ≡some) ≡all of λ ()
  … | is-other _ 𝟘≢𝟘  = ⊥-elim $ 𝟘≢𝟘 ≡some (p≡𝟘 , q≡𝟘)
  … | is-some-yes _ _ = begin
    ω ·ᶜ (γ₃ +ᶜ γ₄)                            ≤⟨ ·ᶜ-monotoneʳ $
                                                  +ᶜ-monotone (tailₘ-monotone (tailₘ-monotone (usage-upper-bound′ ▸B))) $
                                                  usage-upper-bound′ ▸u ⟩
    ω ·ᶜ (tailₘ (tailₘ (⌈ B ⌉ m)) +ᶜ ⌈ u ⌉ m)  ∎
    where
    open ≤ᶜ-reasoning

  usage-upper-bound′ {m} (J₀ₘ₂ {p} {q} ≡all _ _ _ ▸u _ _)
    with J-view p q m
  … | is-other ≤some _    = case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ()
  … | is-some-yes ≡some _ = case trans (PE.sym ≡some) ≡all of λ ()
  … | is-all _            = usage-upper-bound′ ▸u

  usage-upper-bound′
    {m}
    (Kₘ {p} {γ₂} {t} {γ₃} {B} {γ₄} {u} {γ₅} {v} ≤some ok _ ▸t ▸B ▸u ▸v)
    with K-view p m
  … | is-all ≡all           = case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ()
  … | is-some-yes ≡some p≡𝟘 = ⊥-elim $ ok ≡some p≡𝟘
  … | is-other _ _          = begin
    ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅)                              ≤⟨ ·ᶜ-monotoneʳ $
                                                                +ᶜ-monotone (usage-upper-bound′ ▸t) $
                                                                +ᶜ-monotone (tailₘ-monotone (usage-upper-bound′ ▸B)) $
                                                                +ᶜ-monotone (usage-upper-bound′ ▸u) $
                                                                usage-upper-bound′ ▸v ⟩
    ω ·ᶜ (⌈ t ⌉ m +ᶜ tailₘ (⌈ B ⌉ m) +ᶜ ⌈ u ⌉ m +ᶜ ⌈ v ⌉ m)  ∎
    where
    open ≤ᶜ-reasoning

  usage-upper-bound′
    {m} (K₀ₘ₁ {p} {γ₃} {B} {γ₄} {u} ≡some p≡𝟘 _ ▸t ▸B ▸u ▸v)
    with K-view p m
  … | is-all ≡all     = case trans (PE.sym ≡some) ≡all of λ ()
  … | is-other _ 𝟘≢𝟘  = ⊥-elim $ 𝟘≢𝟘 ≡some p≡𝟘
  … | is-some-yes _ _ = begin
    ω ·ᶜ (γ₃ +ᶜ γ₄)                    ≤⟨ ·ᶜ-monotoneʳ $
                                          +ᶜ-monotone (tailₘ-monotone (usage-upper-bound′ ▸B)) $
                                          usage-upper-bound′ ▸u ⟩
    ω ·ᶜ (tailₘ (⌈ B ⌉ m) +ᶜ ⌈ u ⌉ m)  ∎
    where
    open ≤ᶜ-reasoning

  usage-upper-bound′ {m} (K₀ₘ₂ {p} ≡all _ _ _ ▸u _) with K-view p m
  … | is-other ≤some _    = case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ()
  … | is-some-yes ≡some _ = case trans (PE.sym ≡some) ≡all of λ ()
  … | is-all _            = usage-upper-bound′ ▸u

  usage-upper-bound′ ([]-congₘ _ _ _ _ _) =
    ≤ᶜ-refl

  usage-upper-bound′ (sub t x) = ≤ᶜ-trans x (usage-upper-bound′ t)

opaque

  -- A valid modality context can be computed from a well-resourced term
  -- (if there is a dedicated nr functions).

  usage-inf :
    ⦃ ok : Natrec-mode-supports-usage-inference natrec-mode ⦄ →
    γ ▸[ m ] t → ⌈ t ⌉ m ▸[ m ] t
  usage-inf Uₘ = Uₘ
  usage-inf ℕₘ = ℕₘ
  usage-inf Emptyₘ = Emptyₘ
  usage-inf Unitₘ = Unitₘ
  usage-inf (ΠΣₘ {G = G} γ▸F δ▸G) =
    ΠΣₘ (usage-inf γ▸F) (Conₘ-interchange₁ (usage-inf δ▸G) δ▸G)
  usage-inf var = var
  usage-inf defn = defn
  usage-inf (lamₘ {p = p} {t = t} γ▸t) =
    lamₘ (Conₘ-interchange₁ (usage-inf γ▸t) γ▸t)
  usage-inf (γ▸t ∘ₘ γ▸t₁) = usage-inf γ▸t ∘ₘ usage-inf γ▸t₁
  usage-inf (prodʷₘ γ▸t γ▸t₁) = prodʷₘ (usage-inf γ▸t) (usage-inf γ▸t₁)
  usage-inf (prodˢₘ γ▸t γ▸t₁) = prodˢₘ (usage-inf γ▸t) (usage-inf γ▸t₁)
  usage-inf (fstₘ m γ▸t PE.refl ok) =
    fstₘ m (usage-inf γ▸t) PE.refl ok
  usage-inf (sndₘ γ▸t) = sndₘ (usage-inf γ▸t)
  usage-inf {m = m} (prodrecₘ {r = r} {δ = δ} {p = p} {u = u} γ▸t δ▸u η▸A ok) =
    prodrecₘ (usage-inf γ▸t)
             (Conₘ-interchange₂ (usage-inf δ▸u) δ▸u)
             η▸A
             ok
  usage-inf zeroₘ = zeroₘ
  usage-inf (sucₘ γ▸t) = sucₘ (usage-inf γ▸t)
  usage-inf ⦃ ok ⦄
    (natrecₘ {γ} {z} {δ} {p} {r} {η} {q} {A} {s} {n} ⦃ has-nr ⦄ γ▸z δ▸s η▸n θ▸A) =
      sub-≈ᶜ
        (natrecₘ (usage-inf γ▸z)
          (Conₘ-interchange₂ (usage-inf δ▸s) δ▸s)
          (usage-inf η▸n) θ▸A)
        ⌈⌉-natrec-nr
  usage-inf ⦃ ok ⦄ (natrec-no-nrₘ ⦃ no-nr ⦄ _ _ _ _ _ _ _ _) =
    ⊥-elim ⌈⌉-natrec-no-nr
  usage-inf {m} ⦃ ok ⦄ (natrec-no-nr-glbₘ {γ} {z} {δ} {p} {r} {η} {q} {A} {χ} {n} {s} {x} ⦃ no-nr ⦄ γ▸z δ▸s η▸n θ▸A x-GLB χ-GLB) =
    let open ≈ᶜ-reasoning
        has-GLB , ⌈⌉-natrec≈ᶜ = ⌈⌉-natrec-no-nr-glb
        x′ , x′-GLB = has-GLB r 𝟙 p
        χ′ , χ′-GLB = nrᵢᶜ-has-GLBᶜ has-GLB r (⌈ z ⌉ m) (tailₘ (tailₘ (⌈ s ⌉ m)))
    in  sub-≈ᶜ (natrec-no-nr-glbₘ (usage-inf γ▸z)
          (Conₘ-interchange₂ (usage-inf δ▸s) δ▸s)
          (usage-inf η▸n) θ▸A x′-GLB χ′-GLB)
        ⌈⌉-natrec≈ᶜ
  usage-inf (emptyrecₘ γ▸t δ▸A ok) = emptyrecₘ (usage-inf γ▸t) δ▸A ok
  usage-inf starʷₘ = starʷₘ
  usage-inf (starˢₘ prop) = starₘ
  usage-inf (unitrecₘ γ▸t δ▸u η▸A ok) =
    unitrecₘ (usage-inf γ▸t) (usage-inf δ▸u) η▸A ok
  usage-inf (Idₘ not-ok ▸A ▸t ▸u) with Id-erased?
  … | yes ok = ⊥-elim (not-ok ok)
  … | no _   = Idₘ not-ok (usage-inf ▸A) (usage-inf ▸t) (usage-inf ▸u)
  usage-inf (Id₀ₘ ok ▸A ▸t ▸u) with Id-erased?
  … | no not-ok = ⊥-elim (not-ok ok)
  … | yes _     = Id₀ₘ ok ▸A ▸t ▸u
  usage-inf rflₘ =
    rflₘ
  usage-inf {m} (Jₘ {p} {q} ≤some ok ▸A ▸t ▸B ▸u ▸v ▸w) with J-view p q m
  … | is-all ≡all               = case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ()
  … | is-some-yes ≡some p≡𝟘×q≡𝟘 = ⊥-elim $ ok ≡some p≡𝟘×q≡𝟘
  … | is-other _ _              =
    Jₘ ≤some ok ▸A (usage-inf ▸t) (Conₘ-interchange₂ (usage-inf ▸B) ▸B)
      (usage-inf ▸u) (usage-inf ▸v) (usage-inf ▸w)
  usage-inf {m} (J₀ₘ₁ {p} {q} ≡some p≡𝟘 q≡𝟘 ▸A ▸t ▸B ▸u ▸v ▸w)
    with J-view p q m
  … | is-all ≡all     = case trans (PE.sym ≡some) ≡all of λ ()
  … | is-other _ 𝟘≢𝟘  = ⊥-elim $ 𝟘≢𝟘 ≡some (p≡𝟘 , q≡𝟘)
  … | is-some-yes _ _ =
    J₀ₘ₁ ≡some p≡𝟘 q≡𝟘 ▸A (usage-inf ▸t)
      (Conₘ-interchange₂ (usage-inf ▸B) ▸B) (usage-inf ▸u) (usage-inf ▸v)
      (usage-inf ▸w)
  usage-inf {m} (J₀ₘ₂ {p} {q} ≡all ▸A ▸t ▸B ▸u ▸v ▸w) with J-view p q m
  … | is-other ≤some _    = case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ()
  … | is-some-yes ≡some _ = case trans (PE.sym ≡some) ≡all of λ ()
  … | is-all _            = J₀ₘ₂ ≡all ▸A ▸t ▸B (usage-inf ▸u) ▸v ▸w
  usage-inf {m} (Kₘ {p} ≤some ok ▸A ▸t ▸B ▸u ▸v) with K-view p m
  … | is-all ≡all           = case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ()
  … | is-some-yes ≡some p≡𝟘 = ⊥-elim $ ok ≡some p≡𝟘
  … | is-other _ _          =
    Kₘ ≤some ok ▸A (usage-inf ▸t) (Conₘ-interchange₁ (usage-inf ▸B) ▸B)
      (usage-inf ▸u) (usage-inf ▸v)
  usage-inf {m} (K₀ₘ₁ {p} ≡some p≡𝟘 ▸A ▸t ▸B ▸u ▸v) with K-view p m
  … | is-all ≡all     = case trans (PE.sym ≡some) ≡all of λ ()
  … | is-other _ 𝟘≢𝟘  = ⊥-elim $ 𝟘≢𝟘 ≡some p≡𝟘
  … | is-some-yes _ _ =
    K₀ₘ₁ ≡some p≡𝟘 ▸A (usage-inf ▸t) (Conₘ-interchange₁ (usage-inf ▸B) ▸B)
      (usage-inf ▸u) (usage-inf ▸v)
  usage-inf {m} (K₀ₘ₂ {p} ≡all ▸A ▸t ▸B ▸u ▸v) with K-view p m
  … | is-other ≤some _    = case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ()
  … | is-some-yes ≡some _ = case trans (PE.sym ≡some) ≡all of λ ()
  … | is-all _            = K₀ₘ₂ ≡all ▸A ▸t ▸B (usage-inf ▸u) ▸v
  usage-inf ([]-congₘ ▸A ▸t ▸u ▸v ok) =
    []-congₘ ▸A ▸t ▸u ▸v ok
  usage-inf (sub γ▸t x) = usage-inf γ▸t


-- Inlining

opaque
 unfolding inline _ᵈ•_
 mutual

  -- If glassify (∇ ᵈ• ξ) is well-resourced, then inline-< ∇ l≤α α<n
  -- is well-resourced.

  ▸inline-< :
    {ξ : DExt (Term 0) n l} {l≤α : l N.≤ α} {α<n : α <′ n} →
    ▸[ m ] glassify (∇ ᵈ• ξ) → ε ▸[ m ] inline-< ξ l≤α α<n
  ▸inline-< {ξ = idᵉ} {l≤α = n≤α} {α<n} =
    ⊥-elim $ N.n≮n _ $ N.≤-trans (N.<′⇒< α<n) n≤α
  ▸inline-< {ξ = step _ _ _ _} {α<n = N.≤′-reflexive _} ▸ξ =
    ▸inline (▸ξ ∘→ there) (▸ξ here)
  ▸inline-< {ξ = step ξ _ _ _} {α<n = N.≤′-step _} ▸ξ =
    ▸inline-< {ξ = ξ} (▸ξ ∘→ there)

  -- If glassify (∇ ᵈ• ξ) is well-resourced, then inline-Nat ξ α is
  -- well-resourced.

  ▸inline-Nat :
    {ξ : DExt (Term 0) n l} →
    ▸[ m ] glassify (∇ ᵈ• ξ) → ε ▸[ m ] inline-Nat ξ α
  ▸inline-Nat {n} {l} {α} {ξ} ▸ξ with l N.≤? α
  … | no _  = defn
  … | yes _ with α N.<′? n
  …   | no _  = defn
  …   | yes _ = ▸inline-< {ξ = ξ} ▸ξ

  -- If glassify (∇ ᵈ• ξ) and t are well-resourced, then inline ξ t is
  -- well-resourced.

  ▸inline : ▸[ m ] glassify (∇ ᵈ• ξ) → γ ▸[ m ] t → γ ▸[ m ] inline ξ t
  ▸inline ▸ξ (sub ▸t γ≤δ) =
    sub (▸inline ▸ξ ▸t) γ≤δ
  ▸inline _ var =
    var
  ▸inline {ξ} ▸ξ defn =
    PE.subst (_▸[ _ ] _) wkConₘ-ε $
    wkUsage _ (▸inline-Nat {ξ = ξ} ▸ξ)
  ▸inline _ Uₘ =
    Uₘ
  ▸inline _ Emptyₘ =
    Emptyₘ
  ▸inline ▸ξ (emptyrecₘ ▸A ▸t ok) =
    emptyrecₘ (▸inline (▸-ᵐ·-DCon ▸ξ) ▸A) (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸t)
      ok
  ▸inline _ Unitₘ =
    Unitₘ
  ▸inline _ starʷₘ =
    starʷₘ
  ▸inline _ (starˢₘ ok) =
    starˢₘ ok
  ▸inline ▸ξ (unitrecₘ ▸t ▸u ▸A ok) =
    unitrecₘ (▸inline (▸-ᵐ·-DCon ▸ξ) ▸t) (▸inline ▸ξ ▸u)
      (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸A) ok
  ▸inline ▸ξ (ΠΣₘ ▸A ▸B) =
    ΠΣₘ (▸inline ▸ξ ▸A) (▸inline ▸ξ ▸B)
  ▸inline ▸ξ (lamₘ ▸t) =
    lamₘ (▸inline ▸ξ ▸t)
  ▸inline ▸ξ (▸t ∘ₘ ▸u) =
    ▸inline ▸ξ ▸t ∘ₘ ▸inline (▸-ᵐ·-DCon ▸ξ) ▸u
  ▸inline ▸ξ (prodˢₘ ▸t ▸u) =
    prodˢₘ (▸inline (▸-ᵐ·-DCon ▸ξ) ▸t) (▸inline ▸ξ ▸u)
  ▸inline ▸ξ (fstₘ m ▸t refl ok) =
    fstₘ m (▸inline ▸ξ ▸t) refl ok
  ▸inline ▸ξ (sndₘ ▸t) =
    sndₘ (▸inline ▸ξ ▸t)
  ▸inline ▸ξ (prodʷₘ ▸t ▸u) =
    prodʷₘ (▸inline (▸-ᵐ·-DCon ▸ξ) ▸t) (▸inline ▸ξ ▸u)
  ▸inline ▸ξ (prodrecₘ ▸t ▸u ▸A ok) =
    prodrecₘ (▸inline (▸-ᵐ·-DCon ▸ξ) ▸t) (▸inline ▸ξ ▸u)
      (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸A) ok
  ▸inline _ ℕₘ =
    ℕₘ
  ▸inline _ zeroₘ =
    zeroₘ
  ▸inline ▸ξ (sucₘ ▸t) =
    sucₘ (▸inline ▸ξ ▸t)
  ▸inline ▸ξ (natrecₘ ▸t ▸u ▸v ▸A) =
    natrecₘ (▸inline ▸ξ ▸t) (▸inline ▸ξ ▸u) (▸inline ▸ξ ▸v)
      (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸A)
  ▸inline ▸ξ (natrec-no-nrₘ ▸t ▸u ▸v ▸A ok₁ ok₂ ok₃ ok₄) =
    natrec-no-nrₘ (▸inline ▸ξ ▸t) (▸inline ▸ξ ▸u) (▸inline ▸ξ ▸v)
      (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸A) ok₁ ok₂ ok₃ ok₄
  ▸inline ▸ξ (natrec-no-nr-glbₘ ▸t ▸u ▸v ▸A ok₁ ok₂) =
    natrec-no-nr-glbₘ (▸inline ▸ξ ▸t) (▸inline ▸ξ ▸u) (▸inline ▸ξ ▸v)
      (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸A) ok₁ ok₂
  ▸inline ▸ξ (Idₘ not-erased ▸A ▸t ▸u) =
    Idₘ not-erased (▸inline ▸ξ ▸A) (▸inline ▸ξ ▸t) (▸inline ▸ξ ▸u)
  ▸inline ▸ξ (Id₀ₘ erased ▸A ▸t ▸u) =
    Id₀ₘ erased (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸A)
      (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸t) (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸u)
  ▸inline _ rflₘ =
    rflₘ
  ▸inline ▸ξ (Jₘ ok₁ ok₂ ▸A ▸t ▸B ▸u ▸v ▸w) =
    Jₘ ok₁ ok₂ (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸A) (▸inline ▸ξ ▸t)
      (▸inline ▸ξ ▸B) (▸inline ▸ξ ▸u) (▸inline ▸ξ ▸v) (▸inline ▸ξ ▸w)
  ▸inline ▸ξ (J₀ₘ₁ ok₁ ok₂ ok₃ ▸A ▸t ▸B ▸u ▸v ▸w) =
    J₀ₘ₁ ok₁ ok₂ ok₃ (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸A)
      (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸t) (▸inline ▸ξ ▸B) (▸inline ▸ξ ▸u)
      (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸v) (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸w)
  ▸inline ▸ξ (J₀ₘ₂ ok ▸A ▸t ▸B ▸u ▸v ▸w) =
    J₀ₘ₂ ok (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸A) (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸t)
      (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸B) (▸inline ▸ξ ▸u)
      (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸v) (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸w)
  ▸inline ▸ξ (Kₘ ok₁ ok₂ ▸A ▸t ▸B ▸u ▸v) =
    Kₘ ok₁ ok₂ (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸A) (▸inline ▸ξ ▸t)
      (▸inline ▸ξ ▸B) (▸inline ▸ξ ▸u) (▸inline ▸ξ ▸v)
  ▸inline ▸ξ (K₀ₘ₁ ok₁ ok₂ ▸A ▸t ▸B ▸u ▸v) =
    K₀ₘ₁ ok₁ ok₂ (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸A)
      (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸t) (▸inline ▸ξ ▸B) (▸inline ▸ξ ▸u)
      (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸v)
  ▸inline ▸ξ (K₀ₘ₂ ok ▸A ▸t ▸B ▸u ▸v) =
    K₀ₘ₂ ok (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸A) (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸t)
      (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸B) (▸inline ▸ξ ▸u)
      (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸v)
  ▸inline ▸ξ ([]-congₘ ▸A ▸t ▸u ▸v ok) =
    []-congₘ (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸A) (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸t)
      (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸u) (▸inline (▸-𝟘ᵐ-DCon ▸ξ) ▸v) ok

opaque
  unfolding inlineᵈ

  -- A variant of ▸inline.

  ▸inlineᵈ : ▸[ m ] glassify ∇ → γ ▸[ m ] t → γ ▸[ m ] inlineᵈ ∇ t
  ▸inlineᵈ =
    ▸inline ∘→
    PE.subst (▸[_]_ _) (PE.cong glassify $ PE.sym εᵈ•as-DExt)

------------------------------------------------------------------------
-- A negative result

module _ (TR : Type-restrictions) where

  open Definition.Typed TR

  -- It is always the case that ∇ » Γ ⊢ t ∷ A implies ∇ » Γ ⊢ A (see
  -- Definition.Typed.Well-formed.wf-⊢∷), but if ε » Γ ⊢ t ∷ A and
  -- γ ▸[ 𝟙ᵐ ] t always imply γ ▸[ 𝟙ᵐ ] A, then the modality is
  -- trivial.

  ▸-term→▸-type :
    (∀ {n} {Γ : Con Term n} {t A : Term n} {γ : Conₘ n} →
       ε » Γ ⊢ t ∷ A → γ ▸[ 𝟙ᵐ ] t → γ ▸[ 𝟙ᵐ ] A) →
    Trivial
  ▸-term→▸-type hyp =
    case inv-usage-var (hyp ⊢t ▸t) of λ {
      (ε ∙ 𝟘≤𝟙 ∙ 𝟙≤𝟘) →
    PE.trans (PE.sym ⌜𝟙ᵐ⌝) (≤-antisym 𝟙≤𝟘 𝟘≤𝟙) }
    where
    Γ′ = ε ∙ U 0 ∙ var x0
    t′ = var x0
    A′ = var x1
    γ′ = ε ∙ 𝟘 ∙ ⌜ 𝟙ᵐ ⌝

    ⊢U : ε »⊢ ε ∙ U 0
    ⊢U = ∙ Uⱼ (ε ε)

    ⊢Γ : ε »⊢ Γ′
    ⊢Γ = ∙ univ (var ⊢U here)

    ⊢t : ε » Γ′ ⊢ t′ ∷ A′
    ⊢t = var ⊢Γ here

    ▸t : γ′ ▸[ 𝟙ᵐ ] t′
    ▸t = var
