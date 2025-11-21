------------------------------------------------------------------------
-- Some lemmas related to Graded.Modality.Instances.Erasure.Combined
------------------------------------------------------------------------

open import Tools.Bool
open import Tools.Level using (lzero)

open import Definition.Typed.Restrictions

open import Graded.Modality.Variant lzero
open import Graded.Modality.Instances.Erasure.Modality
open import Graded.Usage.Restrictions

module Graded.Modality.Instances.Erasure.Combined.Properties
  (TR : Type-restrictions (ErasureModality (𝟘ᵐ-allowed-if true)))
  (UR : Usage-restrictions (ErasureModality (𝟘ᵐ-allowed-if true)))
  where

open Usage-restrictions UR

private

  -- The modality variant used in this module.

  variant : Modality-variant
  variant = 𝟘ᵐ-allowed-if true

  -- The modality used in this module.

  𝕄 : Modality
  𝕄 = ErasureModality variant

open import Graded.Context 𝕄
open import Graded.Modality.Instances.Erasure
open import Graded.Modality.Instances.Erasure.Combined TR UR
open import Graded.Modality.Instances.Erasure.Properties variant
open import Graded.Mode 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Erased-matches

open import Definition.Untyped Erasure

open import Tools.Empty
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder ≤-poset as POR
open import Tools.Relation

private variable
  Γ   : Cons _ _
  A t : Term _
  γ δ : Conₘ _
  p   : Erasure

opaque mutual

  -- Subsumption for _▸_⊢[_]_.

  sub-⊢ : γ ▸ Γ ⊢[ p ] A → δ ≤ᶜ γ → δ ▸ Γ ⊢[ p ] A
  sub-⊢ (Level ok ⊢Γ) _ =
    Level ok ⊢Γ
  sub-⊢ (univ ⊢A) δ≤γ =
    univ (sub-⊢∷ ⊢A δ≤γ)
  sub-⊢ (Lift ⊢l ⊢A) δ≤γ =
    Lift ⊢l (sub-⊢ ⊢A δ≤γ)
  sub-⊢ (ΠΣ ok ⊢A ⊢B) δ≤γ =
    ΠΣ ok (sub-⊢ ⊢A δ≤γ) (sub-⊢ ⊢B (δ≤γ ∙ ≤-refl))
  sub-⊢ {γ} {δ} (Id {δ = η} hyp₁ hyp₂ ⊢A ⊢t ⊢u) δ≤γ =
    case Id-erased? of λ where
      (yes erased) →
        let η≡𝟘 , r′≡𝟘 = hyp₁ erased in
        Id (λ _ → PE.refl , PE.refl) (⊥-elim ∘→ (_$ erased))
          (PE.subst (_ ▸ _ ⊢[_] _) r′≡𝟘 $
           sub-⊢ ⊢A $ begin
             𝟘ᶜ  ≡˘⟨ η≡𝟘 ⟩
             η   ∎)
          (PE.subst (_ ▸ _ ⊢ _ ∷[_] _) r′≡𝟘 $
           sub-⊢∷ ⊢t $ begin
             𝟘ᶜ  ≡˘⟨ η≡𝟘 ⟩
             η   ∎)
          (PE.subst (_ ▸ _ ⊢ _ ∷[_] _) r′≡𝟘 $
           sub-⊢∷ ⊢u $ begin
             𝟘ᶜ  ≡˘⟨ η≡𝟘 ⟩
             η   ∎)
      (no not-erased) →
        let η≡γ , r′≡p = hyp₂ not-erased in
        Id (⊥-elim ∘→ not-erased) (λ _ → PE.refl , PE.refl)
          (PE.subst (_ ▸ _ ⊢[_] _) r′≡p $
           sub-⊢ ⊢A $ begin
             δ  ≤⟨ δ≤γ ⟩
             γ  ≡˘⟨ η≡γ ⟩
             η  ∎)
          (PE.subst (_ ▸ _ ⊢ _ ∷[_] _) r′≡p $
           sub-⊢∷ ⊢t $ begin
             δ  ≤⟨ δ≤γ ⟩
             γ  ≡˘⟨ η≡γ ⟩
             η  ∎)
          (PE.subst (_ ▸ _ ⊢ _ ∷[_] _) r′≡p $
           sub-⊢∷ ⊢u $ begin
             δ  ≤⟨ δ≤γ ⟩
             γ  ≡˘⟨ η≡γ ⟩
             η  ∎)
    where
    open ≤ᶜ-reasoning

  -- Subsumption for _▸_⊢_∷[_]_.

  sub-⊢∷ : γ ▸ Γ ⊢ t ∷[ p ] A → δ ≤ᶜ γ → δ ▸ Γ ⊢ t ∷[ p ] A
  sub-⊢∷ (conv ⊢t A≡B) δ≤γ =
    conv (sub-⊢∷ ⊢t δ≤γ) A≡B
  sub-⊢∷ {γ} {p} {δ} (var {x} γ⟨x⟩≤p ⊢Γ x∈) δ≤γ =
    var
      (begin
         δ ⟨ x ⟩  ≤⟨ lookup-monotone _ δ≤γ ⟩
         γ ⟨ x ⟩  ≤⟨ γ⟨x⟩≤p ⟩
         p        ∎)
      ⊢Γ x∈
    where
    open POR
  sub-⊢∷ (defn ⊢Γ α∈ eq) _ =
    defn ⊢Γ α∈ eq
  sub-⊢∷ (Level ok ⊢Γ) _ =
    Level ok ⊢Γ
  sub-⊢∷ (zeroᵘ ok ⊢Γ) _ =
    zeroᵘ ok ⊢Γ
  sub-⊢∷ (sucᵘ ⊢l) δ≤γ =
    sucᵘ (sub-⊢∷ ⊢l δ≤γ)
  sub-⊢∷ (⊢supᵘ ⊢l₁ ⊢l₂) δ≤γ =
    ⊢supᵘ (sub-⊢∷ ⊢l₁ δ≤γ) (sub-⊢∷ ⊢l₂ δ≤γ)
  sub-⊢∷ (U ⊢Γ) _ =
    U ⊢Γ
  sub-⊢∷ (Lift ⊢l ⊢A) δ≤γ =
    Lift ⊢l (sub-⊢∷ ⊢A δ≤γ)
  sub-⊢∷ (lift ⊢l ⊢t) δ≤γ =
    lift ⊢l (sub-⊢∷ ⊢t δ≤γ)
  sub-⊢∷ (lower ⊢t) δ≤γ =
    lower (sub-⊢∷ ⊢t δ≤γ)
  sub-⊢∷ (Empty ⊢Γ) _ =
    Empty ⊢Γ
  sub-⊢∷ (emptyrec ok ⊢A ⊢t) δ≤γ =
    emptyrec ok ⊢A (sub-⊢∷ ⊢t δ≤γ)
  sub-⊢∷ (Unit ok ⊢Γ) _ =
    Unit ok ⊢Γ
  sub-⊢∷ (star ok ⊢Γ) _ =
    star ok ⊢Γ
  sub-⊢∷ (unitrec ok ⊢A ⊢t ⊢u) δ≤γ =
    unitrec ok ⊢A (sub-⊢∷ ⊢t δ≤γ) (sub-⊢∷ ⊢u δ≤γ)
  sub-⊢∷ (ΠΣ ok ⊢A ⊢B) δ≤γ =
    ΠΣ ok (sub-⊢∷ ⊢A δ≤γ) (sub-⊢∷ ⊢B (δ≤γ ∙ ≤-refl))
  sub-⊢∷ (lam ok ⊢t) δ≤γ =
    lam ok (sub-⊢∷ ⊢t (δ≤γ ∙ ≤-refl))
  sub-⊢∷ (app ⊢t ⊢u) δ≤γ =
    app (sub-⊢∷ ⊢t δ≤γ) (sub-⊢∷ ⊢u δ≤γ)
  sub-⊢∷ (prod ok ⊢B ⊢t ⊢u) δ≤γ =
    prod ok ⊢B (sub-⊢∷ ⊢t δ≤γ) (sub-⊢∷ ⊢u δ≤γ)
  sub-⊢∷ (fst q≤p ⊢t) δ≤γ =
    fst q≤p (sub-⊢∷ ⊢t δ≤γ)
  sub-⊢∷ (snd ⊢t) δ≤γ =
    snd (sub-⊢∷ ⊢t δ≤γ)
  sub-⊢∷ (prodrec ok ⊢C ⊢t ⊢u) δ≤γ =
    prodrec ok ⊢C (sub-⊢∷ ⊢t δ≤γ) (sub-⊢∷ ⊢u (δ≤γ ∙ ≤-refl ∙ ≤-refl))
  sub-⊢∷ (ℕ ⊢Γ) _ =
    ℕ ⊢Γ
  sub-⊢∷ (zero ⊢Γ) _ =
    zero ⊢Γ
  sub-⊢∷ (suc ⊢t) δ≤γ =
    suc (sub-⊢∷ ⊢t δ≤γ)
  sub-⊢∷ (natrec ⊢A ⊢t ⊢u ⊢v) δ≤γ =
    natrec ⊢A (sub-⊢∷ ⊢t δ≤γ) (sub-⊢∷ ⊢u (δ≤γ ∙ ≤-refl ∙ ≤-refl))
      (sub-⊢∷ ⊢v δ≤γ)
  sub-⊢∷ {γ} {δ} (Id {δ = η} hyp₁ hyp₂ ⊢A ⊢t ⊢u) δ≤γ =
    case Id-erased? of λ where
      (yes erased) →
        let η≡𝟘 , r′≡𝟘 = hyp₁ erased in
        Id (λ _ → PE.refl , PE.refl) (⊥-elim ∘→ (_$ erased))
          (PE.subst (_ ▸ _ ⊢ _ ∷[_] _) r′≡𝟘 $
           sub-⊢∷ ⊢A $ begin
             𝟘ᶜ  ≡˘⟨ η≡𝟘 ⟩
             η   ∎)
          (PE.subst (_ ▸ _ ⊢ _ ∷[_] _) r′≡𝟘 $
           sub-⊢∷ ⊢t $ begin
             𝟘ᶜ  ≡˘⟨ η≡𝟘 ⟩
             η   ∎)
          (PE.subst (_ ▸ _ ⊢ _ ∷[_] _) r′≡𝟘 $
           sub-⊢∷ ⊢u $ begin
             𝟘ᶜ  ≡˘⟨ η≡𝟘 ⟩
             η   ∎)
      (no not-erased) →
        let η≡γ , r′≡p = hyp₂ not-erased in
        Id (⊥-elim ∘→ not-erased) (λ _ → PE.refl , PE.refl)
          (PE.subst (_ ▸ _ ⊢ _ ∷[_] _) r′≡p $
           sub-⊢∷ ⊢A $ begin
             δ  ≤⟨ δ≤γ ⟩
             γ  ≡˘⟨ η≡γ ⟩
             η  ∎)
          (PE.subst (_ ▸ _ ⊢ _ ∷[_] _) r′≡p $
           sub-⊢∷ ⊢t $ begin
             δ  ≤⟨ δ≤γ ⟩
             γ  ≡˘⟨ η≡γ ⟩
             η  ∎)
          (PE.subst (_ ▸ _ ⊢ _ ∷[_] _) r′≡p $
           sub-⊢∷ ⊢u $ begin
             δ  ≤⟨ δ≤γ ⟩
             γ  ≡˘⟨ η≡γ ⟩
             η  ∎)
    where
    open ≤ᶜ-reasoning
  sub-⊢∷ (rfl ⊢Γ) _ =
    rfl ⊢Γ
  sub-⊢∷ {p = r} (J {p} {q} hyp₁ hyp₂ hyp₃ ⊢A ⊢t ⊢B ⊢u ⊢v ⊢w) δ≤γ =
    case J-view p q ⌞ r ⌟ of λ where
      (is-all ≡all) →
        case hyp₃ ≡all of λ {
          (PE.refl , PE.refl , PE.refl , PE.refl) →
        J (λ ≤some → case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ())
          (λ ≡some _ _ → case PE.trans (PE.sym ≡some) ≡all of λ ())
          (λ _ → PE.refl , PE.refl , PE.refl , PE.refl)
          ⊢A ⊢t ⊢B (sub-⊢∷ ⊢u δ≤γ) ⊢v ⊢w }
      (is-some-yes ≡some (PE.refl , PE.refl)) →
        case hyp₂ ≡some PE.refl PE.refl of λ {
          (PE.refl , PE.refl , PE.refl , PE.refl) →
        J (λ _ ¬[p≡𝟘×q≡𝟘] →
             ⊥-elim (¬[p≡𝟘×q≡𝟘] ≡some (PE.refl , PE.refl)))
          (λ _ _ _ → PE.refl , PE.refl , PE.refl , PE.refl)
          (λ ≡all → case PE.trans (PE.sym ≡some) ≡all of λ ())
          ⊢A ⊢t (sub-⊢ ⊢B (δ≤γ ∙ ≤-refl ∙ ≤-refl)) (sub-⊢∷ ⊢u δ≤γ) ⊢v
          ⊢w }
      (is-other ≤some ¬[p≡𝟘×q≡𝟘]) →
        case hyp₁ ≤some ¬[p≡𝟘×q≡𝟘] of λ {
          (PE.refl , PE.refl , PE.refl , PE.refl) →
        J (λ _ _ → PE.refl , PE.refl , PE.refl , PE.refl)
          (λ ≡some p≡𝟘 q≡𝟘 → ⊥-elim (¬[p≡𝟘×q≡𝟘] ≡some (p≡𝟘 , q≡𝟘)))
          (λ ≡all → case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ())
          ⊢A (sub-⊢∷ ⊢t δ≤γ) (sub-⊢ ⊢B (δ≤γ ∙ ≤-refl ∙ ≤-refl))
          (sub-⊢∷ ⊢u δ≤γ) (sub-⊢∷ ⊢v δ≤γ) (sub-⊢∷ ⊢w δ≤γ) }
  sub-⊢∷ {p = r} (K {p} hyp₁ hyp₂ hyp₃ ok ⊢A ⊢t ⊢B ⊢u ⊢v) δ≤γ =
    case K-view p ⌞ r ⌟ of λ where
      (is-all ≡all) →
        case hyp₃ ≡all of λ {
          (PE.refl , PE.refl , PE.refl , PE.refl) →
        K (λ ≤some → case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ())
          (λ ≡some _ → case PE.trans (PE.sym ≡some) ≡all of λ ())
          (λ _ → PE.refl , PE.refl , PE.refl , PE.refl)
          ok ⊢A ⊢t ⊢B (sub-⊢∷ ⊢u δ≤γ) ⊢v }
      (is-some-yes ≡some PE.refl) →
        case hyp₂ ≡some PE.refl of λ {
          (PE.refl , PE.refl , PE.refl , PE.refl) →
        K (λ _ p≢𝟘 → ⊥-elim (p≢𝟘 ≡some PE.refl))
          (λ _ _ → PE.refl , PE.refl , PE.refl , PE.refl)
          (λ ≡all → case PE.trans (PE.sym ≡some) ≡all of λ ())
          ok ⊢A ⊢t (sub-⊢ ⊢B (δ≤γ ∙ ≤-refl)) (sub-⊢∷ ⊢u δ≤γ) ⊢v }
      (is-other ≤some p≢𝟘) →
        case hyp₁ ≤some p≢𝟘 of λ {
          (PE.refl , PE.refl , PE.refl , PE.refl) →
        K (λ _ _ → PE.refl , PE.refl , PE.refl , PE.refl)
          (λ ≡some p≡𝟘 → ⊥-elim (p≢𝟘 ≡some p≡𝟘))
          (λ ≡all → case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ())
          ok ⊢A (sub-⊢∷ ⊢t δ≤γ) (sub-⊢ ⊢B (δ≤γ ∙ ≤-refl))
          (sub-⊢∷ ⊢u δ≤γ) (sub-⊢∷ ⊢v δ≤γ) }
  sub-⊢∷ ([]-cong ok₁ ok₂ ⊢l ⊢A ⊢t ⊢u ⊢v) _ =
    []-cong ok₁ ok₂ ⊢l ⊢A ⊢t ⊢u ⊢v
