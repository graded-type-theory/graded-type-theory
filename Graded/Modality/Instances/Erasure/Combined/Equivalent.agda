------------------------------------------------------------------------
-- The type system in Graded.Modality.Instances.Erasure.Combined is
-- logically equivalent to the usual type and usage systems for the
-- erasure modality with modes, given certain assumptions
------------------------------------------------------------------------

{-# OPTIONS --backtracking-instance-search #-}

open import Tools.Bool using (true; T)
open import Tools.Level using (lzero)

open import Definition.Typed.Restrictions

open import Graded.Modality.Instances.Erasure.Modality
open import Graded.Usage.Restrictions
open import Graded.Mode.Instances.Zero-one.Variant ErasureModality
open import Graded.Mode.Instances.Zero-one 𝟘ᵐ-Allowed

module Graded.Modality.Instances.Erasure.Combined.Equivalent
  (TR : Type-restrictions ErasureModality)
  (UR : Usage-restrictions ErasureModality Zero-one-isMode)
  where

open Usage-restrictions UR
open Mode-variant 𝟘ᵐ-Allowed

private

  -- The modality used in this module.

  𝕄 : Modality
  𝕄 = ErasureModality

  module M = Modality 𝕄

open import Graded.Context 𝕄
open import Graded.Modality.Instances.Erasure
open import Graded.Modality.Instances.Erasure.Combined TR UR as C
open import Graded.Modality.Instances.Erasure.Combined.Properties TR UR
open import Graded.Modality.Instances.Erasure.Properties
open import Graded.Usage UR
open import Graded.Usage.Erased-matches
open import Graded.Usage.Inversion UR
open import Graded.Usage.Properties UR
open import Graded.Usage.Properties.Zero-one 𝟘ᵐ-Allowed UR
open import Graded.Usage.Restrictions.Natrec 𝕄

open import Definition.Typed TR as T
open import Definition.Typed.Inversion TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Size TR
open import Definition.Typed.Substitution TR as S
open import Definition.Typed.Well-formed TR
open import Definition.Untyped Erasure
open import Definition.Untyped.Allowed-literal TR

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder ≤-poset as POR
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Size
open import Tools.Size.Instances

private variable
  ∇               : DCon _ _
  Γ Η             : Cons _ _
  Δ               : Con _ _
  𝓙               : Judgement _
  A A₁ A₂ t t₁ t₂ : Term _
  l l₁ l₂         : Lvl _
  σ               : Subst _ _
  γ δ             : Conₘ _
  p q r           : Erasure
  m               : Mode
  s s₂            : Size

private

  -- An instance of T 𝟘ᵐ-allowed.

  instance

    𝟘ᵐ-ok : T 𝟘ᵐ-allowed
    𝟘ᵐ-ok = _


private opaque

  -- Some lemmas used below.

  ≤ᶜ+ᶜ·ᶜ : γ ≤ᶜ γ +ᶜ p ·ᶜ γ
  ≤ᶜ+ᶜ·ᶜ {γ} {p} = begin
    γ            ≡˘⟨ +ᶜ-idem _ ⟩
    γ +ᶜ γ       ≤⟨ +ᶜ-monotoneʳ ·ᶜ-increasingˡ ⟩
    γ +ᶜ p ·ᶜ γ  ∎
    where
    open ≤ᶜ-reasoning

  ≤ᶜ·ᶜ+ᶜ : γ ≤ᶜ p ·ᶜ γ +ᶜ γ
  ≤ᶜ·ᶜ+ᶜ {γ} {p} = begin
    γ            ≤⟨ ≤ᶜ+ᶜ·ᶜ ⟩
    γ +ᶜ p ·ᶜ γ  ≈⟨ +ᶜ-comm _ _ ⟩
    p ·ᶜ γ +ᶜ γ  ∎
    where
    open ≤ᶜ-reasoning

  𝟘≡⌜𝟘ᵐ?⌝· : 𝟘 PE.≡ ⌜ 𝟘ᵐ? ⌝ · p
  𝟘≡⌜𝟘ᵐ?⌝· {p} =
    𝟘            ≡⟨⟩
    𝟘 · p        ≡˘⟨ M.·-congʳ (⌜𝟘ᵐ?⌝≡𝟘 _) ⟩
    ⌜ 𝟘ᵐ? ⌝ · p  ∎
    where
    open Tools.Reasoning.PropositionalEquality

  ≢𝟘→·ᶜ≤ᶜ : p PE.≢ 𝟘 → p ·ᶜ γ ≤ᶜ γ
  ≢𝟘→·ᶜ≤ᶜ {p} {γ} p≢𝟘 = begin
    p ·ᶜ γ  ≈⟨ ·ᶜ-congʳ (≢𝟘→≡ω p≢𝟘) ⟩
    ω ·ᶜ γ  ≈⟨ ·ᶜ-identityˡ _ ⟩
    γ       ∎
    where
    open ≤ᶜ-reasoning

  ∙▸→∙⌜⌝·▸ : γ ∙ q ▸[ m ] t → γ ∙ ⌜ m ⌝ · q ▸[ m ] t
  ∙▸→∙⌜⌝·▸ {m = 𝟘ᵐ} ▸t = sub (▸-𝟘₀₁ ▸t) (greatest-elemᶜ _)
  ∙▸→∙⌜⌝·▸ {m = 𝟙ᵐ} ▸t = ▸t

  ∙∙▸→∙⌜⌝·∙⌜⌝·▸ :
    γ ∙ q ∙ r ▸[ m ] t → γ ∙ ⌜ m ⌝ · q ∙ ⌜ m ⌝ · r ▸[ m ] t
  ∙∙▸→∙⌜⌝·∙⌜⌝·▸ {m = 𝟘ᵐ} ▸t = sub (▸-𝟘₀₁ ▸t) (greatest-elemᶜ _)
  ∙∙▸→∙⌜⌝·∙⌜⌝·▸ {m = 𝟙ᵐ} ▸t = ▸t

  rec-lemma :
    δ ▸[ ⌞ p ⌟ ᵐ· q ] t →
    γ ≤ᶜ q ·ᶜ δ →
    γ ▸[ ⌞ p · q ⌟ ] t
  rec-lemma {δ} {p} {q} {γ} ▸t γ≤qδ =
    case M.is-𝟘? q of λ where
      (yes PE.refl) →
        let open Tools.Reasoning.PropositionalEquality in
        sub
          (▸-cong
             (𝟘ᵐ         ≡˘⟨ ⌞𝟘⌟′ ⟩
              ⌞ 𝟘 ⌟      ≡˘⟨ PE.cong ⌞_⌟ $ M.·-zeroʳ _ ⟩
              ⌞ p · 𝟘 ⌟  ∎) $
           ▸-𝟘₀₁ ▸t)
          (greatest-elemᶜ _)
      (no q≢𝟘) →
        let open ≤ᶜ-reasoning in
        sub (▸-cong ⌞⌟ᵐ· ▸t) $ begin
          γ       ≤⟨ γ≤qδ ⟩
          q ·ᶜ δ  ≤⟨ ≢𝟘→·ᶜ≤ᶜ q≢𝟘 ⟩
          δ       ∎

  [⌞⌟≡𝟙ᵐ→≤ω]→≤ : (⌞ p ⌟ PE.≡ 𝟙ᵐ → q ≤ ω) → q ≤ p
  [⌞⌟≡𝟙ᵐ→≤ω]→≤ {p = 𝟘} _   = greatest-elem _
  [⌞⌟≡𝟙ᵐ→≤ω]→≤ {p = ω} hyp = hyp ⌞𝟙⌟

------------------------------------------------------------------------
-- From the combined system to the other ones

opaque mutual

  -- A variant of ⊢[]→▸.

  ⊢→▸ : Γ C.⊢ A → 𝟘ᶜ ▸[ 𝟘ᵐ ] A
  ⊢→▸ ⊢A = ▸-cong ⌞𝟘⌟′ (⊢[]→▸ ⊢A)

  private

    -- A variant of ⊢→▸.

    ⊢[]→▸? : γ ▸ Γ ⊢[ p ] A → 𝟘ᶜ ▸[ 𝟘ᵐ? ] A
    ⊢[]→▸? ⊢A = 𝟘ᶜ▸[𝟘ᵐ?] _ (⊢[]→▸ ⊢A)

  -- If A is well-formed and well-resourced, then A is well-resourced.

  ⊢[]→▸ : γ ▸ Γ ⊢[ p ] A → γ ▸[ ⌞ p ⌟ ] A
  ⊢[]→▸ (Level _ _) =
    sub Levelₘ (greatest-elemᶜ _)
  ⊢[]→▸ (univ ⊢A) =
    ⊢∷[]→▸ ⊢A
  ⊢[]→▸ (Lift ⊢l ⊢A) =
    Liftₘ (⊢∷L→▸? ⊢l) (⊢[]→▸ ⊢A)
  ⊢[]→▸ {γ} (ΠΣ {p} ok ⊢A ⊢B) =
    sub (ΠΣₘ (▸-cong (PE.sym ⌞⌟ᵐ·) (⊢[]→▸ ⊢A)) (∙▸→∙⌜⌝·▸ (⊢[]→▸ ⊢B)))
      (begin
         γ            ≡˘⟨ +ᶜ-idem _ ⟩
         γ +ᶜ γ       ≤⟨ +ᶜ-monotoneˡ ·ᶜ-increasingˡ ⟩
         p ·ᶜ γ +ᶜ γ  ∎)
    where
    open ≤ᶜ-reasoning
  ⊢[]→▸ {γ} (Id {δ} _ hyp ⊢A ⊢t ⊢u) with Id-erased?
  … | yes erased =
    sub (Id₀ₘ erased (⊢[]→▸? ⊢A) (⊢∷[]→▸? ⊢t) (⊢∷[]→▸? ⊢u))
      (greatest-elemᶜ _)
  … | no not-erased =
    case hyp not-erased of λ {
      (PE.refl , PE.refl) →
    sub (Idₘ not-erased (⊢[]→▸ ⊢A) (⊢∷[]→▸ ⊢t) (⊢∷[]→▸ ⊢u)) $ begin
      γ            ≡⟨⟩
      δ            ≡˘⟨ PE.trans (PE.cong (_+ᶜ_ _) (+ᶜ-idem _)) (+ᶜ-idem _) ⟩
      δ +ᶜ δ +ᶜ δ  ∎ }
    where
    open ≤ᶜ-reasoning

  -- A variant of ⊢∷[]→▸.

  ⊢∷→▸ : Γ C.⊢ t ∷ A → 𝟘ᶜ ▸[ 𝟘ᵐ ] t
  ⊢∷→▸ ⊢t = ▸-cong ⌞𝟘⌟′ (⊢∷[]→▸ ⊢t)

  private

    -- A variant of ⊢∷[]→▸.

    ⊢∷[]→▸? : γ ▸ Γ ⊢ t ∷[ p ] A → 𝟘ᶜ ▸[ 𝟘ᵐ? ] t
    ⊢∷[]→▸? ⊢t = 𝟘ᶜ▸[𝟘ᵐ?] _ (⊢∷[]→▸ ⊢t)

  -- If t is well-typed and well-resourced, then t is well-resourced.

  ⊢∷[]→▸ : γ ▸ Γ ⊢ t ∷[ p ] A → γ ▸[ ⌞ p ⌟ ] t
  ⊢∷[]→▸ (conv ⊢t _) =
    ⊢∷[]→▸ ⊢t
  ⊢∷[]→▸ {γ} {p} (var {x} γ⟨x⟩≤p _ _) =
    sub var (begin
      γ                   ≡˘⟨ update-self _ _ ⟩
      γ , x ≔ γ ⟨ x ⟩     ≤⟨ update-monotone _ (greatest-elemᶜ _) γ⟨x⟩≤p ⟩
      𝟘ᶜ , x ≔ p          ≈˘⟨ update-congʳ (⌜⌞⌟⌝ _) ⟩
      𝟘ᶜ , x ≔ ⌜ ⌞ p ⌟ ⌝  ∎)
    where
    open ≤ᶜ-reasoning
  ⊢∷[]→▸ (defn _ _ _) =
    sub defn (greatest-elemᶜ _)
  ⊢∷[]→▸ (Level _ _) =
    sub Levelₘ (greatest-elemᶜ _)
  ⊢∷[]→▸ (zeroᵘ _ _) =
    sub zeroᵘₘ (greatest-elemᶜ _)
  ⊢∷[]→▸ (sucᵘ ⊢l) =
    sucᵘₘ (⊢∷[]→▸ ⊢l)
  ⊢∷[]→▸ (⊢supᵘ ⊢l₁ ⊢l₂) =
    PE.subst (_▸[ _ ] _) (+ᶜ-idem _) $
    supᵘₘ (⊢∷[]→▸ ⊢l₁) (⊢∷[]→▸ ⊢l₂)
  ⊢∷[]→▸ (U ⊢l) =
    sub (Uₘ (⊢∷L→▸? ⊢l)) (greatest-elemᶜ _)
  ⊢∷[]→▸ (Lift ⊢l ⊢A) =
    Liftₘ (⊢∷L→▸? ⊢l) (⊢∷[]→▸ ⊢A)
  ⊢∷[]→▸ (lift _ ⊢t) =
    liftₘ (⊢∷[]→▸ ⊢t)
  ⊢∷[]→▸ (lower ⊢t) =
    lowerₘ (⊢∷[]→▸ ⊢t)
  ⊢∷[]→▸ (Empty _) =
    sub Emptyₘ (greatest-elemᶜ _)
  ⊢∷[]→▸ (emptyrec ok ⊢A ⊢t) =
    sub (emptyrecₘ (▸-cong (PE.sym ⌞⌟ᵐ·) (⊢∷[]→▸ ⊢t)) (⊢[]→▸? ⊢A) ok)
      ·ᶜ-increasingˡ
  ⊢∷[]→▸ (Unit _ _) =
    sub Unitₘ (greatest-elemᶜ _)
  ⊢∷[]→▸ (star _ _) =
    sub starₘ (greatest-elemᶜ _)
  ⊢∷[]→▸ (unitrec ok ⊢A ⊢t ⊢u) =
    sub
      (unitrecₘ (▸-cong (PE.sym ⌞⌟ᵐ·) (⊢∷[]→▸ ⊢t)) (⊢∷[]→▸ ⊢u)
        (sub (⊢[]→▸? ⊢A) (greatest-elemᶜ (𝟘ᶜ ∙ _))) ok)
      ≤ᶜ·ᶜ+ᶜ
  ⊢∷[]→▸ {γ} (ΠΣ {p} _ ⊢A ⊢B) =
    sub (ΠΣₘ (▸-cong (PE.sym ⌞⌟ᵐ·) (⊢∷[]→▸ ⊢A)) (∙▸→∙⌜⌝·▸ (⊢∷[]→▸ ⊢B)))
      (begin
         γ           ≡˘⟨ +ᶜ-idem _ ⟩
         γ +ᶜ γ      ≤⟨ +ᶜ-monotoneˡ ·ᶜ-increasingˡ ⟩
         p ·ᶜ γ +ᶜ γ ∎)
    where
    open ≤ᶜ-reasoning
  ⊢∷[]→▸ (lam _ ⊢t) =
    lamₘ (∙▸→∙⌜⌝·▸ (⊢∷[]→▸ ⊢t))
  ⊢∷[]→▸ (app ⊢t ⊢u) =
    sub (⊢∷[]→▸ ⊢t ∘ₘ ▸-cong (PE.sym ⌞⌟ᵐ·) (⊢∷[]→▸ ⊢u)) ≤ᶜ+ᶜ·ᶜ
  ⊢∷[]→▸ (prod {s = 𝕨} _ _ ⊢t ⊢u) =
    sub (prodʷₘ (▸-cong (PE.sym ⌞⌟ᵐ·) (⊢∷[]→▸ ⊢t)) (⊢∷[]→▸ ⊢u)) ≤ᶜ·ᶜ+ᶜ
  ⊢∷[]→▸ {γ} (prod {s = 𝕤} {p} _ ⊢B ⊢t ⊢u) =
    sub (prodˢₘ (▸-cong (PE.sym ⌞⌟ᵐ·) (⊢∷[]→▸ ⊢t)) (⊢∷[]→▸ ⊢u)) $ begin
      γ            ≤⟨ ≤ᶜ·ᶜ+ᶜ ⟩
      p ·ᶜ γ +ᶜ γ  ≈˘⟨ ∧ᶜ≈ᶜ+ᶜ ⟩
      p ·ᶜ γ ∧ᶜ γ  ∎
    where
    open ≤ᶜ-reasoning
  ⊢∷[]→▸ {p} (fst {p = q} q≤p ⊢t) =
    fstₘ₀₁ ⌞ p ⌟ (▸-cong (PE.sym eq) (⊢∷[]→▸ ⊢t)) eq
      (λ ⌞p⌟≡𝟙ᵐ → begin
         q  ≤⟨ q≤p ⟩
         p  ≡⟨ ≢𝟘→≡ω (⌞⌟≡𝟙ᵐ→≢𝟘 _ ⌞p⌟≡𝟙ᵐ) ⟩
         ω  ∎)
    where
    lemma : ∀ p q → q ≤ p → p · q PE.≡ p
    lemma 𝟘 _ _  = PE.refl
    lemma ω 𝟘 ()
    lemma ω ω _  = PE.refl

    eq : ⌞ p ⌟ ᵐ· q PE.≡ ⌞ p ⌟
    eq =
      ⌞ p ⌟ ᵐ· q  ≡⟨ ⌞⌟ᵐ· ⟩
      ⌞ p · q ⌟   ≡⟨ PE.cong ⌞_⌟ (lemma _ _ q≤p) ⟩
      ⌞ p ⌟       ∎
      where
      open Tools.Reasoning.PropositionalEquality

    open POR
  ⊢∷[]→▸ (snd ⊢t) =
    sndₘ (⊢∷[]→▸ ⊢t)
  ⊢∷[]→▸ (prodrec ok ⊢C ⊢t ⊢u) =
    sub
      (prodrecₘ (▸-cong (PE.sym ⌞⌟ᵐ·) (⊢∷[]→▸ ⊢t))
         (∙∙▸→∙⌜⌝·∙⌜⌝·▸ (⊢∷[]→▸ ⊢u))
         (sub (⊢[]→▸? ⊢C) (greatest-elemᶜ (𝟘ᶜ ∙ _))) ok)
      ≤ᶜ·ᶜ+ᶜ
  ⊢∷[]→▸ (ℕ _) =
    sub ℕₘ (greatest-elemᶜ _)
  ⊢∷[]→▸ (zero _) =
    sub zeroₘ (greatest-elemᶜ _)
  ⊢∷[]→▸ (suc ⊢t) =
    sucₘ (⊢∷[]→▸ ⊢t)
  ⊢∷[]→▸ {γ} (natrec {p} {r} ⊢A ⊢t ⊢u ⊢v) =
    let ▸A = sub (⊢[]→▸? ⊢A) (greatest-elemᶜ (𝟘ᶜ ∙ _))
        ▸t = ⊢∷[]→▸ ⊢t
        ▸u = ∙∙▸→∙⌜⌝·∙⌜⌝·▸ (⊢∷[]→▸ ⊢u)
        ▸v = ⊢∷[]→▸ ⊢v
    in
    case PE.singleton natrec-mode of λ where
      (Nr ⦃ has-nr ⦄ , eq) →
        sub
          (natrecₘ
             ⦃ has-nr =
                 PE.subst Natrec-mode-has-nr (PE.sym eq)
                   (Nr ⦃ has-nr = has-nr ⦄) ⦄
             ▸t ▸u ▸v ▸A)
          (begin
             γ                             ≡˘⟨ +ᶜ-idem _ ⟩
             γ +ᶜ γ                        ≡˘⟨ PE.cong (_+ᶜ_ _) (+ᶜ-idem _) ⟩
             γ +ᶜ γ +ᶜ γ                   ≈˘⟨ nrᶜ≈ᶜ ⟩
             nrᶜ ⦃ has-nr = _ ⦄ p r γ γ γ  ≈˘⟨ nrᶜ-unique ⟩
             nrᶜ ⦃ has-nr = _ ⦄ p r γ γ γ  ∎)
      (No-nr , eq) →
        sub
          (natrec-no-nrₘ
             ⦃ no-nr = PE.subst Natrec-mode-no-nr (PE.sym eq) No-nr ⦄
             ▸t ▸u ▸v ▸A ≤ᶜ-refl (λ _ → ≤ᶜ-refl) (λ _ → ≤ᶜ-refl)
             (begin
                γ                      ≤⟨ ≤ᶜ+ᶜ·ᶜ ⟩
                γ +ᶜ (p + r) ·ᶜ γ      ≈⟨ +ᶜ-congˡ (·ᶜ-distribʳ-+ᶜ _ _ _) ⟩
                γ +ᶜ p ·ᶜ γ +ᶜ r ·ᶜ γ  ∎))
          (begin
             γ  ∎)
      (No-nr-glb ⦃ ok ⦄ , eq) →
        sub
          (natrec-no-nr-glbₘ
             ⦃ no-nr =
                 PE.subst Natrec-mode-no-nr-glb (PE.sym eq)
                   (No-nr-glb ⦃ ok = ok ⦄) ⦄
             ▸t ▸u ▸v ▸A (Erasure-nrᵢ-glb-∧ _ _ _) Erasure-nrᵢᶜ-glb-∧ᶜ)
          (begin
             γ                 ≡˘⟨ +ᶜ-idem _ ⟩
             γ +ᶜ γ            ≈˘⟨ +ᶜ-cong (·ᶜ-identityˡ _) (∧ᶜ-idem _) ⟩
             ω ·ᶜ γ +ᶜ γ ∧ᶜ γ  ∎)
    where
    open ≤ᶜ-reasoning
  ⊢∷[]→▸ {γ} (Id {δ} _ hyp ⊢A ⊢t ⊢u) with Id-erased?
  … | yes erased =
    sub (Id₀ₘ erased (⊢∷[]→▸? ⊢A) (⊢∷[]→▸? ⊢t) (⊢∷[]→▸? ⊢u))
      (greatest-elemᶜ _)
  … | no not-erased =
    case hyp not-erased of λ {
      (PE.refl , PE.refl) →
    sub (Idₘ not-erased (⊢∷[]→▸ ⊢A) (⊢∷[]→▸ ⊢t) (⊢∷[]→▸ ⊢u)) $ begin
      γ            ≡⟨⟩
      δ            ≡˘⟨ PE.trans (PE.cong (_+ᶜ_ _) (+ᶜ-idem _)) (+ᶜ-idem _) ⟩
      δ +ᶜ δ +ᶜ δ  ∎ }
    where
    open ≤ᶜ-reasoning
  ⊢∷[]→▸ (rfl _) =
    sub rflₘ (greatest-elemᶜ _)
  ⊢∷[]→▸
    {γ} {p}
    (J {p = p′} {q} {δ₁ = _ ∙ p″ ∙ q′} {r₁} {r₂} {B}
       hyp₁ hyp₂ hyp₃ ⊢A ⊢t ⊢B ⊢u ⊢v ⊢w) =
    let ▸A = ⊢[]→▸? ⊢A
        ▸t = ⊢∷[]→▸ ⊢t
        ▸B = ⊢[]→▸ ⊢B
        ▸u = ⊢∷[]→▸ ⊢u
        ▸v = ⊢∷[]→▸ ⊢v
        ▸w = ⊢∷[]→▸ ⊢w
    in
    case J-view p′ q ⌞ p ⌟ of λ where
      (is-all ≡all) →
        case hyp₃ ≡all of λ {
          (PE.refl , _ , PE.refl , PE.refl) →
        J₀ₘ₂ ≡all ▸A
          (PE.subst (flip (_▸[_]_ _) _) ⌞𝟘⌟≡𝟘ᵐ? ▸t)
          (PE.subst₂ (_▸[_] B)
             (PE.cong₂ _∙_ (PE.cong (_∙_ _) 𝟘≡⌜𝟘ᵐ?⌝·) 𝟘≡⌜𝟘ᵐ?⌝·) ⌞𝟘⌟≡𝟘ᵐ?
             (⊢[]→▸ ⊢B))
          ▸u (PE.subst (flip (_▸[_]_ _) _) ⌞𝟘⌟≡𝟘ᵐ? ▸v)
          (PE.subst (flip (_▸[_]_ _) _) ⌞𝟘⌟≡𝟘ᵐ? ▸w) }
      (is-some-yes ≡some (p′≡𝟘 , q≡𝟘)) →
        case hyp₂ ≡some p′≡𝟘 q≡𝟘 of λ {
          (PE.refl , _ , PE.refl , PE.refl) →
        sub
          (J₀ₘ₁ ≡some p′≡𝟘 q≡𝟘 ▸A
             (PE.subst (flip (_▸[_]_ _) _) ⌞𝟘⌟≡𝟘ᵐ? ▸t) ▸B ▸u
             (PE.subst (flip (_▸[_]_ _) _) ⌞𝟘⌟≡𝟘ᵐ? ▸v)
             (PE.subst (flip (_▸[_]_ _) _) ⌞𝟘⌟≡𝟘ᵐ? ▸w))
          (begin
             γ              ≡˘⟨ +ᶜ-idem _ ⟩
             γ +ᶜ γ         ≈˘⟨ ·ᶜ-identityˡ _ ⟩
             ω ·ᶜ (γ +ᶜ γ)  ∎) }
      (is-other ≤some ¬[p′≡𝟘×q≡𝟘]) →
        case hyp₁ ≤some ¬[p′≡𝟘×q≡𝟘] of λ {
          (PE.refl , PE.refl , PE.refl , PE.refl) →
        sub (Jₘ ≤some ¬[p′≡𝟘×q≡𝟘] ▸A ▸t (∙∙▸→∙⌜⌝·∙⌜⌝·▸ ▸B) ▸u ▸v ▸w)
          (begin
             γ                             ≡˘⟨ PE.trans
                                                 (PE.cong (_ +ᶜ_)
                                                    (PE.trans
                                                       (PE.cong (_ +ᶜ_)
                                                          (PE.trans (PE.cong (_ +ᶜ_) (+ᶜ-idem _)) $
                                                           +ᶜ-idem _)) $
                                                     +ᶜ-idem _)) $
                                               +ᶜ-idem _ ⟩
             γ +ᶜ γ +ᶜ γ +ᶜ γ +ᶜ γ         ≈˘⟨ ·ᶜ-identityˡ _ ⟩
             ω ·ᶜ (γ +ᶜ γ +ᶜ γ +ᶜ γ +ᶜ γ)  ∎) }
    where
    open ≤ᶜ-reasoning
  ⊢∷[]→▸
    {γ} {p}
    (K {p = p′} {δ₁ = _ ∙ p″} {r₁} {r₂} {B}
       hyp₁ hyp₂ hyp₃ _ ⊢A ⊢t ⊢B ⊢u ⊢v) =
    let ▸A = ⊢[]→▸? ⊢A
        ▸t = ⊢∷[]→▸ ⊢t
        ▸B = ⊢[]→▸ ⊢B
        ▸u = ⊢∷[]→▸ ⊢u
        ▸v = ⊢∷[]→▸ ⊢v
    in
    case K-view p′ ⌞ p ⌟ of λ where
      (is-all ≡all) →
        case hyp₃ ≡all of λ {
          (PE.refl , _ , PE.refl , PE.refl) →
        K₀ₘ₂ ≡all ▸A
          (PE.subst (flip (_▸[_]_ _) _) ⌞𝟘⌟≡𝟘ᵐ? ▸t)
          (PE.subst₂ (_▸[_] B) (PE.cong (_∙_ _) 𝟘≡⌜𝟘ᵐ?⌝·) ⌞𝟘⌟≡𝟘ᵐ?
             (⊢[]→▸ ⊢B))
          ▸u (PE.subst (flip (_▸[_]_ _) _) ⌞𝟘⌟≡𝟘ᵐ? ▸v) }
      (is-some-yes ≡some p′≡𝟘) →
        case hyp₂ ≡some p′≡𝟘 of λ {
          (PE.refl , _ , PE.refl , PE.refl) →
        sub
          (K₀ₘ₁ ≡some p′≡𝟘 ▸A
             (PE.subst (flip (_▸[_]_ _) _) ⌞𝟘⌟≡𝟘ᵐ? ▸t) ▸B ▸u
             (PE.subst (flip (_▸[_]_ _) _) ⌞𝟘⌟≡𝟘ᵐ? ▸v))
          (begin
             γ              ≡˘⟨ +ᶜ-idem _ ⟩
             γ +ᶜ γ         ≈˘⟨ ·ᶜ-identityˡ _ ⟩
             ω ·ᶜ (γ +ᶜ γ)  ∎) }
      (is-other ≤some p′≢𝟘) →
        case hyp₁ ≤some p′≢𝟘 of λ {
          (PE.refl , PE.refl , PE.refl , PE.refl) →
        sub (Kₘ ≤some p′≢𝟘 ▸A ▸t (∙▸→∙⌜⌝·▸ ▸B) ▸u ▸v)
          (begin
             γ                        ≡˘⟨ PE.trans
                                            (PE.cong (_ +ᶜ_)
                                               (PE.trans (PE.cong (_ +ᶜ_) (+ᶜ-idem _)) $
                                                +ᶜ-idem _)) $
                                          +ᶜ-idem _ ⟩
             γ +ᶜ γ +ᶜ γ +ᶜ γ         ≈˘⟨ ·ᶜ-identityˡ _ ⟩
             ω ·ᶜ (γ +ᶜ γ +ᶜ γ +ᶜ γ)  ∎) }
    where
    open ≤ᶜ-reasoning
  ⊢∷[]→▸ ([]-cong _ ok ⊢l ⊢A ⊢t ⊢u ⊢v) =
    sub
      ([]-congₘ (⊢∷L→▸? ⊢l) (⊢[]→▸? ⊢A) (⊢∷[]→▸? ⊢t) (⊢∷[]→▸? ⊢u)
         (⊢∷[]→▸? ⊢v) ok)
      (greatest-elemᶜ _)

  -- If l is a well-formed level, then l is well-resourced with
  -- respect to 𝟘ᶜ and 𝟘ᵐ.

  ⊢∷L→▸ : Γ C.⊢ l ∷Level → 𝟘ᶜ ▸[ 𝟘ᵐ ] l
  ⊢∷L→▸ (term _ ⊢l) =
    level (⊢∷→▸ ⊢l)
  ⊢∷L→▸ (literal ok _) =
    Level-literal→▸ (Allowed-literal→Level-literal ok)

  private

    -- A variant of ⊢∷L→▸.

    ⊢∷L→▸? : Γ C.⊢ l ∷Level → 𝟘ᶜ ▸[ 𝟘ᵐ? ] l
    ⊢∷L→▸? ⊢l = 𝟘ᶜ▸[𝟘ᵐ?] _ (⊢∷L→▸ ⊢l)

opaque

  -- If ∇ is well-formed and well-resourced, then ∇ is
  -- well-resourced.

  »→▸ : C.» ∇ → ▸[ ⌞ 𝟘 ⌟ ] ∇
  »→▸ ε             ()
  »→▸ (∙ᵒ _ »∇ _ _) (there α∈) = »→▸ »∇ α∈
  »→▸ (∙ᵗ _ ⊢t)     here       = ⊢∷[]→▸ ⊢t
  »→▸ (∙ᵗ »∇ _)     (there α∈) = »→▸ »∇ α∈

opaque

  -- If σ is well-formed and well-resourced, then σ is well-resourced.

  ⊢ˢʷ∷[]→▸ : δ ▸ Η ⊢ˢʷ σ ∷[ p ] Δ → ∀ x → δ ▸[ ⌞ p ⌟ ] σ x
  ⊢ˢʷ∷[]→▸ (ε _)       ()
  ⊢ˢʷ∷[]→▸ (_   ∙ ⊢σ₀) x0     = ⊢∷[]→▸ ⊢σ₀
  ⊢ˢʷ∷[]→▸ (⊢σ₊ ∙ _)   (x +1) = ⊢ˢʷ∷[]→▸ ⊢σ₊ x

opaque mutual

  -- If ∇ is well-formed, then ∇ is well-formed.

  »→» : C.» ∇ → T.» ∇
  »→» ε =
    ε
  »→» (∙ᵒ ok _ ⊢t ⊢A) =
    ∙ᵒ⟨ ok ⟩[ ⊢∷[]→⊢∷ ⊢t ∷ ⊢[]→⊢ ⊢A ]
  »→» (∙ᵗ _ ⊢t) =
    ∙ᵗ[ ⊢∷[]→⊢∷ ⊢t ]

  -- If Γ is well-formed, then Γ is well-formed.

  ⊢→⊢ : C.⊢ Γ → T.⊢ Γ
  ⊢→⊢ (ε »∇) = ε (»→» »∇)
  ⊢→⊢ (∙ ⊢A) = ∙ ⊢[]→⊢ ⊢A

  -- If A is well-formed and well-resourced, then A is well-formed.

  ⊢[]→⊢ : γ ▸ Γ ⊢[ p ] A → Γ T.⊢ A
  ⊢[]→⊢ (Level ok ⊢Γ) =
    Levelⱼ ok (⊢→⊢ ⊢Γ)
  ⊢[]→⊢ (univ ⊢A) =
    univ (⊢∷[]→⊢∷ ⊢A)
  ⊢[]→⊢ (Lift ⊢l ⊢A) =
    Liftⱼ (⊢∷L→⊢∷L ⊢l) (⊢[]→⊢ ⊢A)
  ⊢[]→⊢ (ΠΣ ok _ ⊢B) =
    ΠΣⱼ (⊢[]→⊢ ⊢B) ok
  ⊢[]→⊢ (Id _ _ _ ⊢t ⊢u) =
    Idⱼ′ (⊢∷[]→⊢∷ ⊢t) (⊢∷[]→⊢∷ ⊢u)

  -- If t is well-typed and well-resourced, then t is well-typed.

  ⊢∷[]→⊢∷ : γ ▸ Γ ⊢ t ∷[ p ] A → Γ T.⊢ t ∷ A
  ⊢∷[]→⊢∷ (conv ⊢t A₁≡A₂) =
    conv (⊢∷[]→⊢∷ ⊢t) (⊢≡→⊢≡ A₁≡A₂)
  ⊢∷[]→⊢∷ (var _ ⊢Γ x∈) =
    var (⊢→⊢ ⊢Γ) x∈
  ⊢∷[]→⊢∷ (defn ⊢Γ α∈ eq) =
    defn (⊢→⊢ ⊢Γ) α∈ eq
  ⊢∷[]→⊢∷ (Level ok ⊢Γ) =
    Levelⱼ (⊢→⊢ ⊢Γ) ok
  ⊢∷[]→⊢∷ (zeroᵘ ok ⊢Γ) =
    zeroᵘⱼ ok (⊢→⊢ ⊢Γ)
  ⊢∷[]→⊢∷ (sucᵘ ⊢l) =
    sucᵘⱼ (⊢∷[]→⊢∷ ⊢l)
  ⊢∷[]→⊢∷ (⊢supᵘ ⊢l₁ ⊢l₂) =
    supᵘⱼ (⊢∷[]→⊢∷ ⊢l₁) (⊢∷[]→⊢∷ ⊢l₂)
  ⊢∷[]→⊢∷ (U ⊢l) =
    Uⱼ (⊢∷L→⊢∷L ⊢l)
  ⊢∷[]→⊢∷ (Lift ⊢l ⊢A) =
    Liftⱼ′ (⊢∷L→⊢∷L ⊢l) (⊢∷[]→⊢∷ ⊢A)
  ⊢∷[]→⊢∷ (lift ⊢l ⊢t) =
    liftⱼ′ (⊢∷L→⊢∷L ⊢l) (⊢∷[]→⊢∷ ⊢t)
  ⊢∷[]→⊢∷ (lower ⊢t) =
    lowerⱼ (⊢∷[]→⊢∷ ⊢t)
  ⊢∷[]→⊢∷ (Empty ⊢Γ) =
    Emptyⱼ (⊢→⊢ ⊢Γ)
  ⊢∷[]→⊢∷ (emptyrec _ ⊢A ⊢t) =
    emptyrecⱼ (⊢[]→⊢ ⊢A) (⊢∷[]→⊢∷ ⊢t)
  ⊢∷[]→⊢∷ (Unit ok ⊢Γ) =
    Unitⱼ (⊢→⊢ ⊢Γ) ok
  ⊢∷[]→⊢∷ (star ok ⊢Γ) =
    starⱼ (⊢→⊢ ⊢Γ) ok
  ⊢∷[]→⊢∷ (unitrec _ ⊢A ⊢t ⊢u) =
    unitrecⱼ′ (⊢[]→⊢ ⊢A) (⊢∷[]→⊢∷ ⊢t) (⊢∷[]→⊢∷ ⊢u)
  ⊢∷[]→⊢∷ (ΠΣ ok ⊢A ⊢B) =
    ΠΣⱼ′ (⊢∷[]→⊢∷ ⊢A) (⊢∷[]→⊢∷ ⊢B) ok
  ⊢∷[]→⊢∷ (lam ok ⊢t) =
    lamⱼ′ ok (⊢∷[]→⊢∷ ⊢t)
  ⊢∷[]→⊢∷ (app ⊢t ⊢u) =
    ⊢∷[]→⊢∷ ⊢t ∘ⱼ ⊢∷[]→⊢∷ ⊢u
  ⊢∷[]→⊢∷ (prod ok ⊢B ⊢t ⊢u) =
    prodⱼ (⊢[]→⊢ ⊢B) (⊢∷[]→⊢∷ ⊢t) (⊢∷[]→⊢∷ ⊢u) ok
  ⊢∷[]→⊢∷ (fst _ ⊢t) =
    fstⱼ′ (⊢∷[]→⊢∷ ⊢t)
  ⊢∷[]→⊢∷ (snd ⊢t) =
    sndⱼ′ (⊢∷[]→⊢∷ ⊢t)
  ⊢∷[]→⊢∷ (prodrec _ ⊢C ⊢t ⊢u) =
    prodrecⱼ′ (⊢[]→⊢ ⊢C) (⊢∷[]→⊢∷ ⊢t) (⊢∷[]→⊢∷ ⊢u)
  ⊢∷[]→⊢∷ (ℕ ⊢Γ) =
    ℕⱼ (⊢→⊢ ⊢Γ)
  ⊢∷[]→⊢∷ (zero ⊢Γ) =
    zeroⱼ (⊢→⊢ ⊢Γ)
  ⊢∷[]→⊢∷ (suc ⊢t) =
    sucⱼ (⊢∷[]→⊢∷ ⊢t)
  ⊢∷[]→⊢∷ (natrec _ ⊢t ⊢u ⊢v) =
    natrecⱼ (⊢∷[]→⊢∷ ⊢t) (⊢∷[]→⊢∷ ⊢u) (⊢∷[]→⊢∷ ⊢v)
  ⊢∷[]→⊢∷ (Id _ _ ⊢A ⊢t ⊢u) =
    Idⱼ (⊢∷[]→⊢∷ ⊢A) (⊢∷[]→⊢∷ ⊢t) (⊢∷[]→⊢∷ ⊢u)
  ⊢∷[]→⊢∷ (rfl ⊢t) =
    rflⱼ (⊢∷[]→⊢∷ ⊢t)
  ⊢∷[]→⊢∷ (J _ _ _ _ _ ⊢B ⊢u _ ⊢w) =
    Jⱼ′ (⊢[]→⊢ ⊢B) (⊢∷[]→⊢∷ ⊢u) (⊢∷[]→⊢∷ ⊢w)
  ⊢∷[]→⊢∷ (K _ _ _ ok _ _ ⊢B ⊢u ⊢v) =
    Kⱼ (⊢[]→⊢ ⊢B) (⊢∷[]→⊢∷ ⊢u) (⊢∷[]→⊢∷ ⊢v) ok
  ⊢∷[]→⊢∷ ([]-cong ok _ ⊢l _ _ _ ⊢v) =
    []-congⱼ′ ok (⊢∷L→⊢∷L ⊢l) (⊢∷[]→⊢∷ ⊢v)

  -- If l is well-formed, then l is well-formed.

  ⊢∷L→⊢∷L : Γ C.⊢ l ∷Level → Γ T.⊢ l ∷Level
  ⊢∷L→⊢∷L (term ok ⊢l) =
    term ok (⊢∷[]→⊢∷ ⊢l)
  ⊢∷L→⊢∷L (literal ok ⊢Γ) =
    literal ok (⊢→⊢ ⊢Γ)

  -- Definitional equality implies definitional equality.

  ⊢≡→⊢≡ : Γ C.⊢ A₁ ≡ A₂ → Γ T.⊢ A₁ ≡ A₂
  ⊢≡→⊢≡ (refl ⊢A) =
    refl (⊢[]→⊢ ⊢A)
  ⊢≡→⊢≡ (sym A₁≡A₂) =
    sym (⊢≡→⊢≡ A₁≡A₂)
  ⊢≡→⊢≡ (trans A₁≡A₂ A₂≡A₃) =
    trans (⊢≡→⊢≡ A₁≡A₂) (⊢≡→⊢≡ A₂≡A₃)
  ⊢≡→⊢≡ (U-cong l₁≡l₂) =
    U-cong (⊢≡∷→⊢≡∷ l₁≡l₂)
  ⊢≡→⊢≡ (univ A₁≡A₂) =
    univ (⊢≡∷→⊢≡∷ A₁≡A₂)
  ⊢≡→⊢≡ (Lift-cong l₁≡l₂ A₁≡A₂) =
    Lift-cong (⊢≡∷L→⊢≡∷L l₁≡l₂) (⊢≡→⊢≡ A₁≡A₂)
  ⊢≡→⊢≡ (ΠΣ-cong ok A₁≡A₂ B₁≡B₂) =
    ΠΣ-cong (⊢≡→⊢≡ A₁≡A₂) (⊢≡→⊢≡ B₁≡B₂) ok
  ⊢≡→⊢≡ (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    Id-cong (⊢≡→⊢≡ A₁≡A₂) (⊢≡∷→⊢≡∷ t₁≡t₂) (⊢≡∷→⊢≡∷ u₁≡u₂)

  -- Definitional equality implies definitional equality.

  ⊢≡∷→⊢≡∷ : Γ C.⊢ t₁ ≡ t₂ ∷ A → Γ T.⊢ t₁ ≡ t₂ ∷ A
  ⊢≡∷→⊢≡∷ (conv t₁≡t₂ A₁≡A₂) =
    conv (⊢≡∷→⊢≡∷ t₁≡t₂) (⊢≡→⊢≡ A₁≡A₂)
  ⊢≡∷→⊢≡∷ (refl ⊢t) =
    refl (⊢∷[]→⊢∷ ⊢t)
  ⊢≡∷→⊢≡∷ (sym t₁≡t₂) =
    sym′ (⊢≡∷→⊢≡∷ t₁≡t₂)
  ⊢≡∷→⊢≡∷ (trans t₁≡t₂ t₂≡t₃) =
    trans (⊢≡∷→⊢≡∷ t₁≡t₂) (⊢≡∷→⊢≡∷ t₂≡t₃)
  ⊢≡∷→⊢≡∷ (δ-red ⊢Γ α∈ eq₁ eq₂) =
    δ-red (⊢→⊢ ⊢Γ) α∈ eq₁ eq₂
  ⊢≡∷→⊢≡∷ (sucᵘ-cong l₁≡l₂) =
    sucᵘ-cong (⊢≡∷→⊢≡∷ l₁≡l₂)
  ⊢≡∷→⊢≡∷ (supᵘ-cong l₁₁≡l₂₁ l₁₂≡l₂₂) =
    supᵘ-cong (⊢≡∷→⊢≡∷ l₁₁≡l₂₁) (⊢≡∷→⊢≡∷ l₁₂≡l₂₂)
  ⊢≡∷→⊢≡∷ (supᵘ-zeroˡ ⊢l) =
    supᵘ-zeroˡ (⊢∷[]→⊢∷ ⊢l)
  ⊢≡∷→⊢≡∷ (supᵘ-sucᵘ ⊢l₁ ⊢l₂) =
    supᵘ-sucᵘ (⊢∷[]→⊢∷ ⊢l₁) (⊢∷[]→⊢∷ ⊢l₂)
  ⊢≡∷→⊢≡∷ (supᵘ-assoc ⊢l₁ ⊢l₂ ⊢l₃) =
    supᵘ-assoc (⊢∷[]→⊢∷ ⊢l₁) (⊢∷[]→⊢∷ ⊢l₂) (⊢∷[]→⊢∷ ⊢l₃)
  ⊢≡∷→⊢≡∷ (supᵘ-comm ⊢l₁ ⊢l₂) =
    supᵘ-comm (⊢∷[]→⊢∷ ⊢l₁) (⊢∷[]→⊢∷ ⊢l₂)
  ⊢≡∷→⊢≡∷ (supᵘ-idem ⊢l) =
    supᵘ-idem (⊢∷[]→⊢∷ ⊢l)
  ⊢≡∷→⊢≡∷ (supᵘ-sub ⊢l) =
    supᵘ-sub (⊢∷[]→⊢∷ ⊢l)
  ⊢≡∷→⊢≡∷ (U-cong l₁≡l₂) =
    U-cong (⊢≡∷→⊢≡∷ l₁≡l₂)
  ⊢≡∷→⊢≡∷ (Lift-cong l₁≡l₂ A₁≡A₂) =
    Lift-cong′ (⊢≡∷L→⊢≡∷L l₁≡l₂) (⊢≡∷→⊢≡∷ A₁≡A₂)
  ⊢≡∷→⊢≡∷ (lower-cong t₁≡t₂) =
    lower-cong (⊢≡∷→⊢≡∷ t₁≡t₂)
  ⊢≡∷→⊢≡∷ (Lift-β ⊢t) =
    Lift-β′ (⊢∷[]→⊢∷ ⊢t)
  ⊢≡∷→⊢≡∷ (Lift-η ⊢t₁ ⊢t₂ lower-t₁≡lower-t₂) =
    Lift-η′ (⊢∷[]→⊢∷ ⊢t₁) (⊢∷[]→⊢∷ ⊢t₂) (⊢≡∷→⊢≡∷ lower-t₁≡lower-t₂)
  ⊢≡∷→⊢≡∷ (emptyrec-cong A₁≡A₂ t₁≡t₂) =
    emptyrec-cong (⊢≡→⊢≡ A₁≡A₂) (⊢≡∷→⊢≡∷ t₁≡t₂)
  ⊢≡∷→⊢≡∷ (η-unit ok ⊢t₁ ⊢t₂) =
    η-unit (⊢∷[]→⊢∷ ⊢t₁) (⊢∷[]→⊢∷ ⊢t₂) ok
  ⊢≡∷→⊢≡∷ (unitrec-cong no-η A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    unitrec-cong′ (⊢≡→⊢≡ A₁≡A₂) (⊢≡∷→⊢≡∷ t₁≡t₂) (⊢≡∷→⊢≡∷ u₁≡u₂)
  ⊢≡∷→⊢≡∷ (unitrec-β _ ⊢A ⊢t) =
    unitrec-β-≡ (⊢[]→⊢ ⊢A) (⊢∷[]→⊢∷ ⊢t)
  ⊢≡∷→⊢≡∷ (unitrec-β-η η ⊢A ⊢t ⊢u) =
    unitrec-β-η-≡ (⊢[]→⊢ ⊢A) (⊢∷[]→⊢∷ ⊢t) (⊢∷[]→⊢∷ ⊢u) η
  ⊢≡∷→⊢≡∷ (ΠΣ-cong ok A₁≡A₂ B₁≡B₂) =
    ΠΣ-cong′ (⊢≡∷→⊢≡∷ A₁≡A₂) (⊢≡∷→⊢≡∷ B₁≡B₂) ok
  ⊢≡∷→⊢≡∷ (app-cong t₁≡t₂ u₁≡u₂) =
    app-cong (⊢≡∷→⊢≡∷ t₁≡t₂) (⊢≡∷→⊢≡∷ u₁≡u₂)
  ⊢≡∷→⊢≡∷ (β-red ok ⊢t ⊢u) =
    β-red-≡ (⊢∷[]→⊢∷ ⊢t) (⊢∷[]→⊢∷ ⊢u) ok
  ⊢≡∷→⊢≡∷ (η-eq ⊢t₁ ⊢t₂ t₁∘0≡t₂∘0) =
    η-eq′ (⊢∷[]→⊢∷ ⊢t₁) (⊢∷[]→⊢∷ ⊢t₂) (⊢≡∷→⊢≡∷ t₁∘0≡t₂∘0)
  ⊢≡∷→⊢≡∷ (prod-cong ok ⊢B t₁≡t₂ u₁≡u₂) =
    prod-cong (⊢[]→⊢ ⊢B) (⊢≡∷→⊢≡∷ t₁≡t₂) (⊢≡∷→⊢≡∷ u₁≡u₂) ok
  ⊢≡∷→⊢≡∷ (fst-cong t₁≡t₂) =
    fst-cong′ (⊢≡∷→⊢≡∷ t₁≡t₂)
  ⊢≡∷→⊢≡∷ (Σ-β₁ ok ⊢B ⊢t ⊢u) =
    Σ-β₁-≡ (⊢[]→⊢ ⊢B) (⊢∷[]→⊢∷ ⊢t) (⊢∷[]→⊢∷ ⊢u) ok
  ⊢≡∷→⊢≡∷ (snd-cong t₁≡t₂) =
    snd-cong′ (⊢≡∷→⊢≡∷ t₁≡t₂)
  ⊢≡∷→⊢≡∷ (Σ-β₂ ok ⊢B ⊢t ⊢u) =
    Σ-β₂-≡ (⊢[]→⊢ ⊢B) (⊢∷[]→⊢∷ ⊢t) (⊢∷[]→⊢∷ ⊢u) ok
  ⊢≡∷→⊢≡∷ (Σ-η ⊢t₁ ⊢t₂ fst-t₁≡fst-t₂ snd-t₁≡snd-t₂) =
    Σ-η′ (⊢∷[]→⊢∷ ⊢t₁) (⊢∷[]→⊢∷ ⊢t₂) (⊢≡∷→⊢≡∷ fst-t₁≡fst-t₂)
      (⊢≡∷→⊢≡∷ snd-t₁≡snd-t₂)
  ⊢≡∷→⊢≡∷ (prodrec-cong C₁≡C₂ t₁≡t₂ u₁≡u₂) =
    prodrec-cong′ (⊢≡→⊢≡ C₁≡C₂) (⊢≡∷→⊢≡∷ t₁≡t₂) (⊢≡∷→⊢≡∷ u₁≡u₂)
  ⊢≡∷→⊢≡∷ (prodrec-β ⊢C ⊢t ⊢u ⊢v) =
    prodrec-β-≡ (⊢[]→⊢ ⊢C) (⊢∷[]→⊢∷ ⊢t) (⊢∷[]→⊢∷ ⊢u) (⊢∷[]→⊢∷ ⊢v)
  ⊢≡∷→⊢≡∷ (suc-cong t₁≡t₂) =
    suc-cong (⊢≡∷→⊢≡∷ t₁≡t₂)
  ⊢≡∷→⊢≡∷ (natrec-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂) =
    natrec-cong (⊢≡→⊢≡ A₁≡A₂) (⊢≡∷→⊢≡∷ t₁≡t₂) (⊢≡∷→⊢≡∷ u₁≡u₂)
      (⊢≡∷→⊢≡∷ v₁≡v₂)
  ⊢≡∷→⊢≡∷ (natrec-zero ⊢t ⊢u) =
    natrec-zero (⊢∷[]→⊢∷ ⊢t) (⊢∷[]→⊢∷ ⊢u)
  ⊢≡∷→⊢≡∷ (natrec-suc ⊢t ⊢u ⊢v) =
    natrec-suc (⊢∷[]→⊢∷ ⊢t) (⊢∷[]→⊢∷ ⊢u) (⊢∷[]→⊢∷ ⊢v)
  ⊢≡∷→⊢≡∷ (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    Id-cong (⊢≡∷→⊢≡∷ A₁≡A₂) (⊢≡∷→⊢≡∷ t₁≡t₂) (⊢≡∷→⊢≡∷ u₁≡u₂)
  ⊢≡∷→⊢≡∷ (J-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂) =
    J-cong′ (⊢≡→⊢≡ A₁≡A₂) (⊢≡∷→⊢≡∷ t₁≡t₂) (⊢≡→⊢≡ B₁≡B₂) (⊢≡∷→⊢≡∷ u₁≡u₂)
      (⊢≡∷→⊢≡∷ v₁≡v₂) (⊢≡∷→⊢≡∷ w₁≡w₂)
  ⊢≡∷→⊢≡∷ (J-β ⊢t ⊢B ⊢u) =
    J-β-≡ (⊢∷[]→⊢∷ ⊢t) (⊢[]→⊢ ⊢B) (⊢∷[]→⊢∷ ⊢u)
  ⊢≡∷→⊢≡∷ (K-cong ok A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂) =
    K-cong (⊢≡→⊢≡ A₁≡A₂) (⊢≡∷→⊢≡∷ t₁≡t₂) (⊢≡→⊢≡ B₁≡B₂) (⊢≡∷→⊢≡∷ u₁≡u₂)
      (⊢≡∷→⊢≡∷ v₁≡v₂) ok
  ⊢≡∷→⊢≡∷ (K-β ok ⊢B ⊢u) =
    K-β (⊢[]→⊢ ⊢B) (⊢∷[]→⊢∷ ⊢u) ok
  ⊢≡∷→⊢≡∷ ([]-cong-cong ok l₁≡l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂) =
    []-cong-cong (⊢≡∷L→⊢≡∷L l₁≡l₂) (⊢≡→⊢≡ A₁≡A₂) (⊢≡∷→⊢≡∷ t₁≡t₂)
      (⊢≡∷→⊢≡∷ u₁≡u₂) (⊢≡∷→⊢≡∷ v₁≡v₂) ok
  ⊢≡∷→⊢≡∷ ([]-cong-β ok ⊢l ⊢t) =
    []-cong-β-≡ (⊢∷L→⊢∷L ⊢l) (refl (⊢∷[]→⊢∷ ⊢t)) ok
  ⊢≡∷→⊢≡∷ (equality-reflection ok ⊢v) =
    equality-reflection′ ok (⊢∷[]→⊢∷ ⊢v)

  -- Definitional equality implies definitional equality.

  ⊢≡∷L→⊢≡∷L : Γ C.⊢ l₁ ≡ l₂ ∷Level → Γ T.⊢ l₁ ≡ l₂ ∷Level
  ⊢≡∷L→⊢≡∷L (term ok l₁≡l₂) =
    term ok (⊢≡∷→⊢≡∷ l₁≡l₂)
  ⊢≡∷L→⊢≡∷L (literal! ok ⊢Γ) =
    literal ok (⊢→⊢ ⊢Γ)

opaque

  -- If σ is well-formed and well-resourced, then σ is well-formed.

  ⊢ˢʷ∷[]→⊢ˢʷ∷ : δ ▸ Η ⊢ˢʷ σ ∷[ p ] Δ → Η S.⊢ˢʷ σ ∷ Δ
  ⊢ˢʷ∷[]→⊢ˢʷ∷ (ε ⊢Η)      = ⊢ˢʷ∷ε⇔ .proj₂ (⊢→⊢ ⊢Η)
  ⊢ˢʷ∷[]→⊢ˢʷ∷ (⊢σ₊ ∙ ⊢σ₀) =
    ⊢ˢʷ∷∙⇔ .proj₂ (⊢ˢʷ∷[]→⊢ˢʷ∷ ⊢σ₊ , ⊢∷[]→⊢∷ ⊢σ₀)

------------------------------------------------------------------------
-- From the other systems to the combined one

-- The translation in this direction makes use of some assumptions:
-- certain things must always be allowed when the mode is 𝟘ᵐ[ ok ].

record Allowed-at-𝟘ᵐ : Set where
  no-eta-equality
  field
    er : ∀ {ok} p     → Emptyrec-allowed       𝟘ᵐ[ ok ] p
    ur : ∀ {ok} p q   → Unitrec-allowed        𝟘ᵐ[ ok ] p q
    pr : ∀ {ok} r p q → Prodrec-allowed        𝟘ᵐ[ ok ] r p q
    bc : ∀ {ok} p     → []-cong-allowed-mode p 𝟘ᵐ[ ok ]

module _ (ok : Allowed-at-𝟘ᵐ) where

  open Allowed-at-𝟘ᵐ ok

  ----------------------------------------------------------------------
  -- From the other systems to the combined one part 1: lemmas that do
  -- not involve the usage relation _▸[_]_

  private

    -- Below several properties are proved simultaneously using
    -- well-founded induction. The properties are collected in the
    -- record type P.

    record P (s : Size) : Set where
      no-eta-equality
      field
        »←»       : (⊢∇ : T.» ∇) → size-» ⊢∇ PE.≡ s → C.» ∇
        ⊢←⊢′      : (⊢Γ : T.⊢ Γ) → size ⊢Γ PE.≡ s → C.⊢ Γ
        ⊢←⊢       : (⊢A : Γ T.⊢ A) → size ⊢A PE.≡ s → Γ C.⊢ A
        ⊢∷←⊢∷     : (⊢t : Γ T.⊢ t ∷ A) → size ⊢t PE.≡ s → Γ C.⊢ t ∷ A
        ⊢∷L←⊢∷L   : (⊢l : Γ T.⊢ l ∷Level) → size ⊢l PE.≡ s →
                    Γ C.⊢ l ∷Level
        ⊢≡←⊢≡     : (A₁≡A₂ : Γ T.⊢ A₁ ≡ A₂) → size A₁≡A₂ PE.≡ s →
                    Γ C.⊢ A₁ ≡ A₂
        ⊢≡∷←⊢≡∷   : (t₁≡t₂ : Γ T.⊢ t₁ ≡ t₂ ∷ A) → size t₁≡t₂ PE.≡ s →
                    Γ C.⊢ t₁ ≡ t₂ ∷ A
        ⊢≡∷L←⊢≡∷L : (l₁≡l₂ : Γ T.⊢ l₁ ≡ l₂ ∷Level) →
                    size l₁≡l₂ PE.≡ s → Γ C.⊢ l₁ ≡ l₂ ∷Level

  -- Variants of the fields of P.

  private module Variants (hyp : ∀ {s₁} → s₁ <ˢ s₂ → P s₁) where

    opaque

      -- Variants of the fields of P.

      »←» :
        (»∇ : T.» ∇) →
        ⦃ lt : size-» »∇ <ˢ s₂ ⦄ →
        C.» ∇
      »←» »∇ ⦃ lt ⦄ = P.»←» (hyp lt) »∇ PE.refl

      ⊢←⊢′ :
        (⊢Γ : T.⊢ Γ) →
        ⦃ lt : size ⊢Γ <ˢ s₂ ⦄ →
        C.⊢ Γ
      ⊢←⊢′ ⊢Γ ⦃ lt ⦄ = P.⊢←⊢′ (hyp lt) ⊢Γ PE.refl

      ⊢←⊢ :
        (⊢A : Γ T.⊢ A) →
        ⦃ lt : size ⊢A <ˢ s₂ ⦄ →
        Γ C.⊢ A
      ⊢←⊢ ⊢A ⦃ lt ⦄ = P.⊢←⊢ (hyp lt) ⊢A PE.refl

      ⊢∷←⊢∷ :
        (⊢t : Γ T.⊢ t ∷ A) →
        ⦃ lt : size ⊢t <ˢ s₂ ⦄ →
        Γ C.⊢ t ∷ A
      ⊢∷←⊢∷ ⊢t ⦃ lt ⦄ = P.⊢∷←⊢∷ (hyp lt) ⊢t PE.refl

      ⊢∷L←⊢∷L :
        (⊢l : Γ T.⊢ l ∷Level) →
        ⦃ lt : size ⊢l <ˢ s₂ ⦄ →
        Γ C.⊢ l ∷Level
      ⊢∷L←⊢∷L ⊢l ⦃ lt ⦄ = P.⊢∷L←⊢∷L (hyp lt) ⊢l PE.refl

      ⊢≡←⊢≡ :
        (A₁≡A₂ : Γ T.⊢ A₁ ≡ A₂) →
        ⦃ lt : size A₁≡A₂ <ˢ s₂ ⦄ →
        Γ C.⊢ A₁ ≡ A₂
      ⊢≡←⊢≡ A₁≡A₂ ⦃ lt ⦄ = P.⊢≡←⊢≡ (hyp lt) A₁≡A₂ PE.refl

      ⊢≡∷←⊢≡∷ :
        (t₁≡t₂ : Γ T.⊢ t₁ ≡ t₂ ∷ A) →
        ⦃ lt : size t₁≡t₂ <ˢ s₂ ⦄ →
        Γ C.⊢ t₁ ≡ t₂ ∷ A
      ⊢≡∷←⊢≡∷ t₁≡t₂ ⦃ lt ⦄ = P.⊢≡∷←⊢≡∷ (hyp lt) t₁≡t₂ PE.refl

      ⊢≡∷L←⊢≡∷L :
        (l₁≡l₂ : Γ T.⊢ l₁ ≡ l₂ ∷Level) →
        ⦃ lt : size l₁≡l₂ <ˢ s₂ ⦄ →
        Γ C.⊢ l₁ ≡ l₂ ∷Level
      ⊢≡∷L←⊢≡∷L l₁≡l₂ ⦃ lt ⦄ = P.⊢≡∷L←⊢≡∷L (hyp lt) l₁≡l₂ PE.refl

    opaque

      -- Variants of some of the variants.

      ▸⊢[𝟘]←⊢ :
        (⊢A : Γ T.⊢ A) →
        ⦃ lt : size ⊢A <ˢ s₂ ⦄ →
        γ ▸ Γ ⊢[ 𝟘 ] A
      ▸⊢[𝟘]←⊢ ⊢A = sub-⊢ (⊢←⊢ ⊢A) (greatest-elemᶜ _)

      ▸⊢∷[𝟘]←⊢∷ :
        (⊢t : Γ T.⊢ t ∷ A) →
        ⦃ lt : size ⊢t <ˢ s₂ ⦄ →
        γ ▸ Γ ⊢ t ∷[ 𝟘 ] A
      ▸⊢∷[𝟘]←⊢∷ ⊢t = sub-⊢∷ (⊢∷←⊢∷ ⊢t) (greatest-elemᶜ _)

      ⊢←⊢-<ˢ :
        (∃ λ (⊢A : Γ T.⊢ A) → size ⊢A <ˢ s) →
        ⦃ lt : s <ˢ s₂ ⦄ →
        Γ C.⊢ A
      ⊢←⊢-<ˢ (⊢A , lt) = ⊢←⊢ ⊢A ⦃ lt = <ˢ-trans lt ! ⦄

      ⊢∷←⊢∷-<ˢ :
        (∃ λ (⊢t : Γ T.⊢ t ∷ A) → size ⊢t <ˢ s) →
        ⦃ lt : s <ˢ s₂ ⦄ →
        Γ C.⊢ t ∷ A
      ⊢∷←⊢∷-<ˢ (⊢t , lt) = ⊢∷←⊢∷ ⊢t ⦃ lt = <ˢ-trans lt ! ⦄

  -- The type P s is inhabited for every s.

  private module Inhabited where

    opaque
      unfolding size

      -- If ∇ is well-formed, then ∇ is well-formed.

      »←»ₛ :
        (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
        (⊢∇ : T.» ∇) →
        size-» ⊢∇ PE.≡ s₂ →
        C.» ∇
      »←»ₛ hyp = let open Variants hyp in λ where
        ε _ →
          ε
        ∙ᵒ⟨ ok ⟩[ ⊢t ∷ ⊢A ] PE.refl →
          let ⊢Γ , Γ≤ = wf-≤ˢ ⊢A
              »∇ , ∇< = ⊢→»-<ˢ ⊢Γ
          in
          ∙ᵒ ok (»←» »∇ ⦃ lt = <ˢ-trans ∇< (<ˢ-trans-≤ˢˡ Γ≤ !) ⦄)
            (⊢∷←⊢∷ ⊢t) (⊢←⊢ ⊢A)
        ∙ᵗ[ ⊢t ] PE.refl →
          let ⊢Γ , Γ≤ = wf-≤ˢ ⊢t
              »∇ , ∇< = ⊢→»-<ˢ ⊢Γ
          in
          ∙ᵗ (»←» »∇ ⦃ lt = <ˢ-trans ∇< (<ˢ-trans-≤ˢˡ Γ≤ !) ⦄)
            (⊢∷←⊢∷ ⊢t)

      -- If Γ is well-formed, then Γ is well-formed.

      ⊢←⊢′ₛ :
        (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
        (⊢Γ : T.⊢ Γ) →
        size ⊢Γ PE.≡ s₂ →
        C.⊢ Γ
      ⊢←⊢′ₛ hyp = let open Variants hyp in λ where
        (ε »∇) PE.refl → ε (»←» »∇)
        (∙ ⊢A) PE.refl → ∙ ⊢←⊢ ⊢A

      -- If A is well-formed, then A is well-formed.

      ⊢←⊢ₛ :
        (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
        (⊢A : Γ T.⊢ A) →
        size ⊢A PE.≡ s₂ →
        Γ C.⊢ A
      ⊢←⊢ₛ hyp = let open Variants hyp in λ where
        (Levelⱼ ok ⊢Γ) PE.refl →
          Level ok (⊢←⊢′ ⊢Γ)
        (univ ⊢A) PE.refl →
          univ (⊢∷←⊢∷ ⊢A)
        (Liftⱼ ⊢l ⊢A) PE.refl →
          Lift (⊢∷L←⊢∷L ⊢l) (⊢←⊢ ⊢A)
        (ΠΣⱼ ⊢B ok) PE.refl →
          let _ , ⊢A = ∙⊢→⊢-<ˢ ⊢B in
          ΠΣ ok (⊢←⊢-<ˢ ⊢A) (▸⊢[𝟘]←⊢ ⊢B)
        (Idⱼ ⊢A ⊢t ⊢u) PE.refl →
          case Id-erased? of λ where
            (yes erased) →
              Id (λ _ → PE.refl , PE.refl) (⊥-elim ∘→ (_$ erased))
                (⊢←⊢ ⊢A) (⊢∷←⊢∷ ⊢t) (⊢∷←⊢∷ ⊢u)
            (no not-erased) →
              Id (⊥-elim ∘→ not-erased) (λ _ → PE.refl , PE.refl)
                (⊢←⊢ ⊢A) (⊢∷←⊢∷ ⊢t) (⊢∷←⊢∷ ⊢u)

      -- If t is well-typed, then t is well-typed.

      ⊢∷←⊢∷ₛ :
        (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
        (⊢t : Γ T.⊢ t ∷ A) →
        size ⊢t PE.≡ s₂ →
        Γ C.⊢ t ∷ A
      ⊢∷←⊢∷ₛ hyp = let open Variants hyp in λ where
        (conv ⊢t A≡B) PE.refl →
          conv (⊢∷←⊢∷ ⊢t) (⊢≡←⊢≡ A≡B)
        (var ⊢Γ x∈Γ) PE.refl →
          var (greatest-elem _) (⊢←⊢′ ⊢Γ) x∈Γ
        (defn ⊢Γ α∈ eq) PE.refl →
          defn (⊢←⊢′ ⊢Γ) α∈ eq
        (Levelⱼ ⊢Γ ok) PE.refl →
          Level ok (⊢←⊢′ ⊢Γ)
        (zeroᵘⱼ ok ⊢Γ) PE.refl →
          zeroᵘ ok (⊢←⊢′ ⊢Γ)
        (sucᵘⱼ ⊢l) PE.refl →
          sucᵘ (⊢∷←⊢∷ ⊢l)
        (supᵘⱼ ⊢l₁ ⊢l₂) PE.refl →
          ⊢supᵘ (⊢∷←⊢∷ ⊢l₁) (⊢∷←⊢∷ ⊢l₂)
        (Uⱼ ⊢l) PE.refl →
          U (⊢∷L←⊢∷L ⊢l)
        (Liftⱼ _ ⊢l ⊢A) PE.refl →
          Lift (⊢∷L←⊢∷L ⊢l) (⊢∷←⊢∷ ⊢A)
        (liftⱼ ⊢l _ ⊢t) PE.refl →
          lift (⊢∷L←⊢∷L ⊢l) (⊢∷←⊢∷ ⊢t)
        (lowerⱼ ⊢t) PE.refl →
          lower (⊢∷←⊢∷ ⊢t)
        (Emptyⱼ ⊢Γ) PE.refl →
          Empty (⊢←⊢′ ⊢Γ)
        (emptyrecⱼ ⊢A ⊢t) PE.refl →
          emptyrec (PE.subst (flip Emptyrec-allowed _) (PE.sym ⌞𝟘⌟′) (er _))
            (⊢←⊢ ⊢A) (⊢∷←⊢∷ ⊢t)
        (Unitⱼ ⊢Γ ok) PE.refl →
          Unit ok (⊢←⊢′ ⊢Γ)
        (starⱼ ⊢Γ ok) PE.refl →
          star ok (⊢←⊢′ ⊢Γ)
        (unitrecⱼ {p} {q} ⊢A ⊢t ⊢u _) PE.refl →
          unitrec (PE.subst (λ m → Unitrec-allowed m p q) (PE.sym ⌞𝟘⌟′) (ur p q))
            (⊢←⊢ ⊢A) (⊢∷←⊢∷ ⊢t) (⊢∷←⊢∷ ⊢u)
        (ΠΣⱼ _ ⊢A ⊢B ok) PE.refl →
          ΠΣ ok (⊢∷←⊢∷ ⊢A) (▸⊢∷[𝟘]←⊢∷ ⊢B)
        (lamⱼ _ ⊢t ok) PE.refl →
          lam ok (▸⊢∷[𝟘]←⊢∷ ⊢t)
        (⊢t ∘ⱼ ⊢u) PE.refl →
          app (⊢∷←⊢∷ ⊢t) (⊢∷←⊢∷ ⊢u)
        (prodⱼ ⊢B ⊢t ⊢u ok) PE.refl →
          prod ok (⊢←⊢ ⊢B) (⊢∷←⊢∷ ⊢t) (⊢∷←⊢∷ ⊢u)
        (fstⱼ _ ⊢t) PE.refl →
          fst (greatest-elem _) (⊢∷←⊢∷ ⊢t)
        (sndⱼ _ ⊢t) PE.refl →
          snd (⊢∷←⊢∷ ⊢t)
        (prodrecⱼ {p} {r} {q} ⊢C ⊢t ⊢u _) PE.refl →
          prodrec
            (PE.subst (λ m → Prodrec-allowed m r p q) (PE.sym ⌞𝟘⌟′) (pr r p q))
            (⊢←⊢ ⊢C) (⊢∷←⊢∷ ⊢t) (▸⊢∷[𝟘]←⊢∷ ⊢u)
        (ℕⱼ ⊢Γ) PE.refl →
          ℕ (⊢←⊢′ ⊢Γ)
        (zeroⱼ ⊢Γ) PE.refl →
          zero (⊢←⊢′ ⊢Γ)
        (sucⱼ ⊢t) PE.refl →
          suc (⊢∷←⊢∷ ⊢t)
        (natrecⱼ ⊢t ⊢u ⊢v) PE.refl →
          let _ , ⊢A = ∙⊢→⊢-<ˢ ⊢u in
          natrec (⊢←⊢-<ˢ ⊢A) (⊢∷←⊢∷ ⊢t) (▸⊢∷[𝟘]←⊢∷ ⊢u) (⊢∷←⊢∷ ⊢v)
        (Idⱼ ⊢A ⊢t ⊢u) PE.refl →
          case Id-erased? of λ where
            (yes erased) →
              Id (λ _ → PE.refl , PE.refl) (⊥-elim ∘→ (_$ erased))
                (⊢∷←⊢∷ ⊢A) (⊢∷←⊢∷ ⊢t) (⊢∷←⊢∷ ⊢u)
            (no not-erased) →
              Id (⊥-elim ∘→ not-erased) (λ _ → PE.refl , PE.refl)
                (⊢∷←⊢∷ ⊢A) (⊢∷←⊢∷ ⊢t) (⊢∷←⊢∷ ⊢u)
        (rflⱼ ⊢t) PE.refl →
          rfl (⊢∷←⊢∷ ⊢t)
        (Jⱼ {p} {q} ⊢t ⊢B ⊢u ⊢v ⊢w) PE.refl →
          let _ , ⊢A , _  = ∙∙⊢→⊢-<ˢ ⊢B in
          case J-view p q ⌞ 𝟘 ⌟ of λ where
            (is-all ≡all) →
              J (λ ≤some → case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ())
                (λ ≡some _ _ →
                   case PE.trans (PE.sym ≡some) ≡all of λ ())
                (λ _ → PE.refl , PE.refl , PE.refl , PE.refl)
                (⊢←⊢-<ˢ ⊢A) (⊢∷←⊢∷ ⊢t) (⊢←⊢ ⊢B) (⊢∷←⊢∷ ⊢u) (⊢∷←⊢∷ ⊢v)
                (⊢∷←⊢∷ ⊢w)
            (is-some-yes ≡some p≡𝟘×q≡𝟘) →
              J (λ _ ¬[p≡𝟘×q≡𝟘] → ⊥-elim (¬[p≡𝟘×q≡𝟘] ≡some p≡𝟘×q≡𝟘))
                (λ _ _ _ → PE.refl , PE.refl , PE.refl , PE.refl)
                (λ ≡all → case PE.trans (PE.sym ≡some) ≡all of λ ())
                (⊢←⊢-<ˢ ⊢A) (⊢∷←⊢∷ ⊢t) (⊢←⊢ ⊢B) (⊢∷←⊢∷ ⊢u) (⊢∷←⊢∷ ⊢v)
                (⊢∷←⊢∷ ⊢w)
            (is-other ≤some ¬[p≡𝟘×q≡𝟘]) →
              J (λ _ _ → PE.refl , PE.refl , PE.refl , PE.refl)
                (λ ≡some p≡𝟘 q≡𝟘 → ⊥-elim (¬[p≡𝟘×q≡𝟘] ≡some (p≡𝟘 , q≡𝟘)))
                (λ ≡all → case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ())
                (⊢←⊢-<ˢ ⊢A) (⊢∷←⊢∷ ⊢t) (▸⊢[𝟘]←⊢ ⊢B) (⊢∷←⊢∷ ⊢u)
                (⊢∷←⊢∷ ⊢v) (⊢∷←⊢∷ ⊢w)
        (Kⱼ {p} ⊢B ⊢u ⊢v ok) PE.refl →
          let _ , ⊢Id     = ∙⊢→⊢-<ˢ ⊢B
              ⊢A , ⊢t , _ = inversion-Id-⊢-<ˢ ⊢Id
          in
          case K-view p ⌞ 𝟘 ⌟ of λ where
            (is-all ≡all) →
              K (λ ≤some → case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ())
                (λ ≡some _ → case PE.trans (PE.sym ≡some) ≡all of λ ())
                (λ _ → PE.refl , PE.refl , PE.refl , PE.refl)
                ok (⊢←⊢-<ˢ ⊢A) (⊢∷←⊢∷-<ˢ ⊢t) (⊢←⊢ ⊢B) (⊢∷←⊢∷ ⊢u)
                (⊢∷←⊢∷ ⊢v)
            (is-some-yes ≡some p≡𝟘) →
              K (λ _ p≢𝟘 → ⊥-elim (p≢𝟘 ≡some p≡𝟘))
                (λ _ _ → PE.refl , PE.refl , PE.refl , PE.refl)
                (λ ≡all → case PE.trans (PE.sym ≡some) ≡all of λ ())
                ok (⊢←⊢-<ˢ ⊢A) (⊢∷←⊢∷-<ˢ ⊢t) (⊢←⊢ ⊢B) (⊢∷←⊢∷ ⊢u)
                (⊢∷←⊢∷ ⊢v)
            (is-other ≤some p≢𝟘) →
              K (λ _ _ → PE.refl , PE.refl , PE.refl , PE.refl)
                (λ ≡some p≡𝟘 → ⊥-elim (p≢𝟘 ≡some p≡𝟘))
                (λ ≡all → case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ())
                ok (⊢←⊢-<ˢ ⊢A) (⊢∷←⊢∷-<ˢ ⊢t) (▸⊢[𝟘]←⊢ ⊢B) (⊢∷←⊢∷ ⊢u)
                (⊢∷←⊢∷ ⊢v)
        ([]-congⱼ ⊢l ⊢A ⊢t ⊢u ⊢v ok) PE.refl →
          []-cong ok (PE.subst ([]-cong-allowed-mode _) (PE.sym ⌞𝟘⌟′) (bc _))
            (⊢∷L←⊢∷L ⊢l) (⊢←⊢ ⊢A) (⊢∷←⊢∷ ⊢t) (⊢∷←⊢∷ ⊢u) (⊢∷←⊢∷ ⊢v)

      -- If l is well-typed, then l is well-typed.

      ⊢∷L←⊢∷Lₛ :
        (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
        (⊢l : Γ T.⊢ l ∷Level) →
        size ⊢l PE.≡ s₂ →
        Γ C.⊢ l ∷Level
      ⊢∷L←⊢∷Lₛ hyp = let open Variants hyp in λ where
        (term ok ⊢l) PE.refl →
          term ok (⊢∷←⊢∷ ⊢l)
        (literal ok ⊢Γ) PE.refl →
          literal ok (⊢←⊢′ ⊢Γ)

      -- Definitional equality implies definitional equality.

      ⊢≡←⊢≡ₛ :
        (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
        (A₁≡A₂ : Γ T.⊢ A₁ ≡ A₂) →
        size A₁≡A₂ PE.≡ s₂ →
        Γ C.⊢ A₁ ≡ A₂
      ⊢≡←⊢≡ₛ hyp = let open Variants hyp in λ where
        (refl ⊢A) PE.refl →
          refl (⊢←⊢ ⊢A)
        (sym A₁≡A₂) PE.refl →
          sym (⊢≡←⊢≡ A₁≡A₂)
        (trans A₁≡A₂ A₂≡A₃) PE.refl →
          trans (⊢≡←⊢≡ A₁≡A₂) (⊢≡←⊢≡ A₂≡A₃)
        (U-cong l₁≡l₂) PE.refl →
          U-cong (⊢≡∷←⊢≡∷ l₁≡l₂)
        (univ A₁≡A₂) PE.refl →
          univ (⊢≡∷←⊢≡∷ A₁≡A₂)
        (Lift-cong l₁≡l₂ A₁≡A₂) PE.refl →
          Lift-cong (⊢≡∷L←⊢≡∷L l₁≡l₂) (⊢≡←⊢≡ A₁≡A₂)
        (ΠΣ-cong A₁≡A₂ B₁≡B₂ ok) PE.refl →
          ΠΣ-cong ok (⊢≡←⊢≡ A₁≡A₂) (⊢≡←⊢≡ B₁≡B₂)
        (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) PE.refl →
          Id-cong (⊢≡←⊢≡ A₁≡A₂) (⊢≡∷←⊢≡∷ t₁≡t₂) (⊢≡∷←⊢≡∷ u₁≡u₂)

      -- Definitional equality implies definitional equality.

      ⊢≡∷←⊢≡∷ₛ :
        (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
        (t₁≡t₂ : Γ T.⊢ t₁ ≡ t₂ ∷ A) →
        size t₁≡t₂ PE.≡ s₂ →
        Γ C.⊢ t₁ ≡ t₂ ∷ A
      ⊢≡∷←⊢≡∷ₛ hyp = let open Variants hyp in λ where
        (conv t₁≡t₂ A₁≡A₂) PE.refl →
          conv (⊢≡∷←⊢≡∷ t₁≡t₂) (⊢≡←⊢≡ A₁≡A₂)
        (refl ⊢t) PE.refl →
          refl (⊢∷←⊢∷ ⊢t)
        (sym _ t₁≡t₂) PE.refl →
          sym (⊢≡∷←⊢≡∷ t₁≡t₂)
        (trans t₁≡t₂ t₂≡t₃) PE.refl →
          trans (⊢≡∷←⊢≡∷ t₁≡t₂) (⊢≡∷←⊢≡∷ t₂≡t₃)
        (δ-red ⊢Γ α∈ eq₁ eq₂) PE.refl →
          δ-red (⊢←⊢′ ⊢Γ) α∈ eq₁ eq₂
        (sucᵘ-cong l₁≡l₂) PE.refl →
          sucᵘ-cong (⊢≡∷←⊢≡∷ l₁≡l₂)
        (supᵘ-cong l₁₁≡l₂₁ l₁₂≡l₂₂) PE.refl →
          supᵘ-cong (⊢≡∷←⊢≡∷ l₁₁≡l₂₁) (⊢≡∷←⊢≡∷ l₁₂≡l₂₂)
        (supᵘ-zeroˡ ⊢l) PE.refl →
          supᵘ-zeroˡ (⊢∷←⊢∷ ⊢l)
        (supᵘ-sucᵘ ⊢l₁ ⊢l₂) PE.refl →
          supᵘ-sucᵘ (⊢∷←⊢∷ ⊢l₁) (⊢∷←⊢∷ ⊢l₂)
        (supᵘ-assoc ⊢l₁ ⊢l₂ ⊢l₃) PE.refl →
          supᵘ-assoc (⊢∷←⊢∷ ⊢l₁) (⊢∷←⊢∷ ⊢l₂) (⊢∷←⊢∷ ⊢l₃)
        (supᵘ-comm ⊢l₁ ⊢l₂) PE.refl →
          supᵘ-comm (⊢∷←⊢∷ ⊢l₁) (⊢∷←⊢∷ ⊢l₂)
        (supᵘ-idem ⊢l) PE.refl →
          supᵘ-idem (⊢∷←⊢∷ ⊢l)
        (supᵘ-sub ⊢l) PE.refl →
          supᵘ-sub (⊢∷←⊢∷ ⊢l)
        (U-cong l₁≡l₂) PE.refl →
          U-cong (⊢≡∷←⊢≡∷ l₁≡l₂)
        (Lift-cong _ _ l₁≡l₂ A₁≡A₂) PE.refl →
          Lift-cong (⊢≡∷L←⊢≡∷L l₁≡l₂) (⊢≡∷←⊢≡∷ A₁≡A₂)
        (lower-cong t₁≡t₂) PE.refl →
          lower-cong (⊢≡∷←⊢≡∷ t₁≡t₂)
        (Lift-β _ ⊢t) PE.refl →
          Lift-β (⊢∷←⊢∷ ⊢t)
        (Lift-η _ _ ⊢t₁ ⊢t₂ lower-t₁≡lower-t₂) PE.refl →
          Lift-η (⊢∷←⊢∷ ⊢t₁) (⊢∷←⊢∷ ⊢t₂) (⊢≡∷←⊢≡∷ lower-t₁≡lower-t₂)
        (emptyrec-cong A₁≡A₂ t₁≡t₂) PE.refl →
          emptyrec-cong (⊢≡←⊢≡ A₁≡A₂) (⊢≡∷←⊢≡∷ t₁≡t₂)
        (η-unit ⊢t₁ ⊢t₂ ok) PE.refl →
          η-unit ok (⊢∷←⊢∷ ⊢t₁) (⊢∷←⊢∷ ⊢t₂)
        (unitrec-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ _ no-η) PE.refl →
          unitrec-cong no-η (⊢≡←⊢≡ A₁≡A₂) (⊢≡∷←⊢≡∷ t₁≡t₂)
            (⊢≡∷←⊢≡∷ u₁≡u₂)
        (unitrec-β ⊢A ⊢t _ η) PE.refl →
          unitrec-β η (⊢←⊢ ⊢A) (⊢∷←⊢∷ ⊢t)
        (unitrec-β-η ⊢A ⊢t ⊢u _ η) PE.refl →
          unitrec-β-η η (⊢←⊢ ⊢A) (⊢∷←⊢∷ ⊢t) (⊢∷←⊢∷ ⊢u)
        (ΠΣ-cong _ A₁≡A₂ B₁≡B₂ ok) PE.refl →
          ΠΣ-cong ok (⊢≡∷←⊢≡∷ A₁≡A₂) (⊢≡∷←⊢≡∷ B₁≡B₂)
        (app-cong t₁≡t₂ u₁≡u₂) PE.refl →
          app-cong (⊢≡∷←⊢≡∷ t₁≡t₂) (⊢≡∷←⊢≡∷ u₁≡u₂)
        (β-red _ ⊢t ⊢u PE.refl ok) PE.refl →
          β-red ok (⊢∷←⊢∷ ⊢t) (⊢∷←⊢∷ ⊢u)
        (η-eq _ ⊢t₁ ⊢t₂ t₁∘0≡t₂∘0 _) PE.refl →
          η-eq (⊢∷←⊢∷ ⊢t₁) (⊢∷←⊢∷ ⊢t₂) (⊢≡∷←⊢≡∷ t₁∘0≡t₂∘0)
        (prod-cong ⊢B t₁≡t₂ u₁≡u₂ ok) PE.refl →
          prod-cong ok (⊢←⊢ ⊢B) (⊢≡∷←⊢≡∷ t₁≡t₂) (⊢≡∷←⊢≡∷ u₁≡u₂)
        (fst-cong _ t₁≡t₂) PE.refl →
          fst-cong (⊢≡∷←⊢≡∷ t₁≡t₂)
        (Σ-β₁ ⊢B ⊢t ⊢u PE.refl ok) PE.refl →
          Σ-β₁ ok (⊢←⊢ ⊢B) (⊢∷←⊢∷ ⊢t) (⊢∷←⊢∷ ⊢u)
        (snd-cong _ t₁≡t₂) PE.refl →
          snd-cong (⊢≡∷←⊢≡∷ t₁≡t₂)
        (Σ-β₂ ⊢B ⊢t ⊢u PE.refl ok) PE.refl →
          Σ-β₂ ok (⊢←⊢ ⊢B) (⊢∷←⊢∷ ⊢t) (⊢∷←⊢∷ ⊢u)
        (Σ-η _ ⊢t₁ ⊢t₂ fst-t₁≡fst-t₂ snd-t₁≡snd-t₂ _) PE.refl →
          Σ-η (⊢∷←⊢∷ ⊢t₁) (⊢∷←⊢∷ ⊢t₂) (⊢≡∷←⊢≡∷ fst-t₁≡fst-t₂)
            (⊢≡∷←⊢≡∷ snd-t₁≡snd-t₂)
        (prodrec-cong C₁≡C₂ t₁≡t₂ u₁≡u₂ _) PE.refl →
          prodrec-cong (⊢≡←⊢≡ C₁≡C₂) (⊢≡∷←⊢≡∷ t₁≡t₂) (⊢≡∷←⊢≡∷ u₁≡u₂)
        (prodrec-β ⊢C ⊢t ⊢u ⊢v PE.refl _) PE.refl →
          prodrec-β (⊢←⊢ ⊢C) (⊢∷←⊢∷ ⊢t) (⊢∷←⊢∷ ⊢u) (⊢∷←⊢∷ ⊢v)
        (suc-cong t₁≡t₂) PE.refl →
          suc-cong (⊢≡∷←⊢≡∷ t₁≡t₂)
        (natrec-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂) PE.refl →
          natrec-cong (⊢≡←⊢≡ A₁≡A₂) (⊢≡∷←⊢≡∷ t₁≡t₂) (⊢≡∷←⊢≡∷ u₁≡u₂)
            (⊢≡∷←⊢≡∷ v₁≡v₂)
        (natrec-zero ⊢t ⊢u) PE.refl →
          natrec-zero (⊢∷←⊢∷ ⊢t) (⊢∷←⊢∷ ⊢u)
        (natrec-suc ⊢t ⊢u ⊢v) PE.refl →
          natrec-suc (⊢∷←⊢∷ ⊢t) (⊢∷←⊢∷ ⊢u) (⊢∷←⊢∷ ⊢v)
        (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) PE.refl →
          Id-cong (⊢≡∷←⊢≡∷ A₁≡A₂) (⊢≡∷←⊢≡∷ t₁≡t₂) (⊢≡∷←⊢≡∷ u₁≡u₂)
        (J-cong A₁≡A₂ _ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂) PE.refl →
          J-cong (⊢≡←⊢≡ A₁≡A₂) (⊢≡∷←⊢≡∷ t₁≡t₂) (⊢≡←⊢≡ B₁≡B₂)
            (⊢≡∷←⊢≡∷ u₁≡u₂) (⊢≡∷←⊢≡∷ v₁≡v₂) (⊢≡∷←⊢≡∷ w₁≡w₂)
        (J-β ⊢t ⊢B ⊢u PE.refl) PE.refl →
          J-β (⊢∷←⊢∷ ⊢t) (⊢←⊢ ⊢B) (⊢∷←⊢∷ ⊢u)
        (K-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ ok) PE.refl →
          K-cong ok (⊢≡←⊢≡ A₁≡A₂) (⊢≡∷←⊢≡∷ t₁≡t₂) (⊢≡←⊢≡ B₁≡B₂)
            (⊢≡∷←⊢≡∷ u₁≡u₂) (⊢≡∷←⊢≡∷ v₁≡v₂)
        (K-β ⊢B ⊢u ok) PE.refl →
          K-β ok (⊢←⊢ ⊢B) (⊢∷←⊢∷ ⊢u)
        ([]-cong-cong l₁≡l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok) PE.refl →
          []-cong-cong ok (⊢≡∷L←⊢≡∷L l₁≡l₂) (⊢≡←⊢≡ A₁≡A₂)
            (⊢≡∷←⊢≡∷ t₁≡t₂) (⊢≡∷←⊢≡∷ u₁≡u₂) (⊢≡∷←⊢≡∷ v₁≡v₂)
        ([]-cong-β ⊢l ⊢t PE.refl ok) PE.refl →
          []-cong-β ok (⊢∷L←⊢∷L ⊢l) (⊢∷←⊢∷ ⊢t)
        (equality-reflection ok _ ⊢v) PE.refl →
          equality-reflection ok (⊢∷←⊢∷ ⊢v)

      -- Definitional equality implies definitional equality.

      ⊢≡∷L←⊢≡∷Lₛ :
        (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
        (l₁≡l₂ : Γ T.⊢ l₁ ≡ l₂ ∷Level) →
        size l₁≡l₂ PE.≡ s₂ →
        Γ C.⊢ l₁ ≡ l₂ ∷Level
      ⊢≡∷L←⊢≡∷Lₛ hyp = let open Variants hyp in λ where
        (term ok l₁≡l₂) PE.refl →
          term ok (⊢≡∷←⊢≡∷ l₁≡l₂)
        (literal ok ⊢Γ) PE.refl →
          literal! ok (⊢←⊢′ ⊢Γ)

    opaque

      -- The type P s is inhabited for every s.

      P-inhabited : P s
      P-inhabited =
        well-founded-induction P
          (λ _ hyp →
             record
               { »←»       = »←»ₛ       hyp
               ; ⊢←⊢′      = ⊢←⊢′ₛ      hyp
               ; ⊢←⊢       = ⊢←⊢ₛ       hyp
               ; ⊢∷←⊢∷     = ⊢∷←⊢∷ₛ     hyp
               ; ⊢∷L←⊢∷L   = ⊢∷L←⊢∷Lₛ   hyp
               ; ⊢≡←⊢≡     = ⊢≡←⊢≡ₛ     hyp
               ; ⊢≡∷←⊢≡∷   = ⊢≡∷←⊢≡∷ₛ   hyp
               ; ⊢≡∷L←⊢≡∷L = ⊢≡∷L←⊢≡∷Lₛ hyp
               })
          _

  opaque

    -- If ∇ is well-formed, then ∇ is well-formed.

    »←» : T.» ∇ → C.» ∇
    »←» »∇ = P.»←» Inhabited.P-inhabited »∇ PE.refl

  opaque

    -- If Γ is well-formed, then Γ is well-formed.

    ⊢←⊢′ : T.⊢ Γ → C.⊢ Γ
    ⊢←⊢′ ⊢Γ = P.⊢←⊢′ Inhabited.P-inhabited ⊢Γ PE.refl


  opaque

    -- If A is well-formed, then A is well-formed.

    ⊢←⊢ : Γ T.⊢ A → Γ C.⊢ A
    ⊢←⊢ ⊢A = P.⊢←⊢ Inhabited.P-inhabited ⊢A PE.refl

  opaque

    -- If t is well-typed, then t is well-typed.

    ⊢∷←⊢∷ : Γ T.⊢ t ∷ A → Γ C.⊢ t ∷ A
    ⊢∷←⊢∷ ⊢t = P.⊢∷←⊢∷ Inhabited.P-inhabited ⊢t PE.refl

  opaque

    -- If l is well-formed, then l is well-formed.

    ⊢∷L←⊢∷L : Γ T.⊢ l ∷Level → Γ C.⊢ l ∷Level
    ⊢∷L←⊢∷L ⊢l = P.⊢∷L←⊢∷L Inhabited.P-inhabited ⊢l PE.refl

  opaque

    -- Definitional equality implies definitional equality.

    ⊢≡←⊢≡ : Γ T.⊢ A₁ ≡ A₂ → Γ C.⊢ A₁ ≡ A₂
    ⊢≡←⊢≡ A₁≡A₂ = P.⊢≡←⊢≡ Inhabited.P-inhabited A₁≡A₂ PE.refl

  opaque

    -- Definitional equality implies definitional equality.

    ⊢≡∷←⊢≡∷ : Γ T.⊢ t₁ ≡ t₂ ∷ A → Γ C.⊢ t₁ ≡ t₂ ∷ A
    ⊢≡∷←⊢≡∷ t₁≡t₂ = P.⊢≡∷←⊢≡∷ Inhabited.P-inhabited t₁≡t₂ PE.refl

  opaque

    -- Definitional equality implies definitional equality.

    ⊢≡∷L←⊢≡∷L : Γ T.⊢ l₁ ≡ l₂ ∷Level → Γ C.⊢ l₁ ≡ l₂ ∷Level
    ⊢≡∷L←⊢≡∷L l₁≡l₂ = P.⊢≡∷L←⊢≡∷L Inhabited.P-inhabited l₁≡l₂ PE.refl

  ----------------------------------------------------------------------
  -- From the other systems to the combined one, part 2: lemmas that do
  -- involve the usage relation _▸[_]_

  opaque mutual

    -- If A is well-formed and well-resourced, then A is well-formed
    -- and well-resourced.

    ⊢[]←⊢▸ : Γ T.⊢ A → γ ▸[ ⌞ p ⌟ ] A → γ ▸ Γ ⊢[ p ] A
    ⊢[]←⊢▸ (Levelⱼ ok ⊢Γ) _ =
      Level ok (⊢←⊢′ ⊢Γ)
    ⊢[]←⊢▸ (univ ⊢A) ▸A =
      univ (⊢∷[]←⊢∷▸ ⊢A ▸A)
    ⊢[]←⊢▸ (Liftⱼ ⊢l ⊢A) ▸Lift =
      let _ , ▸A = inv-usage-Lift ▸Lift in
      Lift (⊢∷L←⊢∷L ⊢l) (⊢[]←⊢▸ ⊢A ▸A)
    ⊢[]←⊢▸ {γ} {p} (ΠΣⱼ {p = r} {q} ⊢B ok) ▸ΠΣ =
      let open ≤ᶜ-reasoning
          invUsageΠΣ {δ} {η} ▸A ▸B γ≤δ+η = inv-usage-ΠΣ ▸ΠΣ
      in
      ΠΣ ok
        (⊢[]←⊢▸ (⊢∙→⊢ (wf ⊢B)) $ rec-lemma ▸A $ begin
          γ           ≤⟨ γ≤δ+η ⟩
          r ·ᶜ δ +ᶜ η ≤⟨ +ᶜ-decreasingˡ _ _ ⟩
          r ·ᶜ δ      ∎)
        (⊢[]←⊢▸ ⊢B $
         sub ▸B $ begin
           γ           ∙             q  ≤⟨ γ≤δ+η ∙ ≤-refl ⟩
           r ·ᶜ δ +ᶜ η ∙             q  ≤⟨ +ᶜ-decreasingʳ _ _ ∙ ·-increasingˡ ⟩
           η           ∙ ⌜ ⌞ p ⌟ ⌝ · q  ∎)
    ⊢[]←⊢▸ {γ} (Idⱼ ⊢A ⊢t ⊢u) ▸Id =
      case inv-usage-Id ▸Id of λ where
        (invUsageId {δ} {η} {θ} not-erased ▸A ▸t ▸u γ≤δ+η+θ) →
          Id (⊥-elim ∘→ not-erased) (λ _ → PE.refl , PE.refl)
            (⊢[]←⊢▸ ⊢A $ sub ▸A $ begin
               γ            ≤⟨ γ≤δ+η+θ ⟩
               δ +ᶜ η +ᶜ θ  ≤⟨ +ᶜ-decreasingˡ _ _ ⟩
               δ            ∎)
            (⊢∷[]←⊢∷▸ ⊢t $ sub ▸t $ begin
               γ            ≤⟨ γ≤δ+η+θ ⟩
               δ +ᶜ η +ᶜ θ  ≤⟨ +ᶜ-decreasingʳ _ _ ⟩
               η +ᶜ θ       ≤⟨ +ᶜ-decreasingˡ _ _ ⟩
               η            ∎)
            (⊢∷[]←⊢∷▸ ⊢u $ sub ▸u $ begin
               γ            ≤⟨ γ≤δ+η+θ ⟩
               δ +ᶜ η +ᶜ θ  ≤⟨ +ᶜ-decreasingʳ _ _ ⟩
               η +ᶜ θ       ≤⟨ +ᶜ-decreasingʳ _ _ ⟩
               θ            ∎)
        (invUsageId₀ erased _ _ _ _) →
          Id (λ _ → PE.refl , PE.refl) (⊥-elim ∘→ (_$ erased)) (⊢←⊢ ⊢A)
            (⊢∷←⊢∷ ⊢t) (⊢∷←⊢∷ ⊢u)
      where
      open ≤ᶜ-reasoning

    -- If t is well-typed and well-resourced, then t is well-typed and
    -- well-resourced.

    ⊢∷[]←⊢∷▸ : Γ T.⊢ t ∷ A → γ ▸[ ⌞ p ⌟ ] t → γ ▸ Γ ⊢ t ∷[ p ] A
    ⊢∷[]←⊢∷▸ {γ} {p = o} = λ where
      (conv ⊢t A≡B) ▸t →
        conv (⊢∷[]←⊢∷▸ ⊢t ▸t) (⊢≡←⊢≡ A≡B)
      (var {x} ⊢Γ x∈Γ) ▸x →
        var
          (let open POR in begin
             γ ⟨ x ⟩                     ≤⟨ lookup-monotone _ (inv-usage-var ▸x) ⟩
             (𝟘ᶜ , x ≔ ⌜ ⌞ o ⌟ ⌝) ⟨ x ⟩  ≡⟨ update-lookup 𝟘ᶜ x ⟩
             ⌜ ⌞ o ⌟ ⌝                   ≡⟨ ⌜⌞⌟⌝ _ ⟩
             o                           ∎)
          (⊢←⊢′ ⊢Γ) x∈Γ
      (defn ⊢Γ α∈ eq) _ →
        defn (⊢←⊢′ ⊢Γ) α∈ eq
      (Levelⱼ ⊢Γ ok) _ →
        Level ok (⊢←⊢′ ⊢Γ)
      (zeroᵘⱼ ok ⊢Γ) _ →
        zeroᵘ ok (⊢←⊢′ ⊢Γ)
      (sucᵘⱼ ⊢l) ▸sucᵘ →
        let ▸l = inv-usage-sucᵘ ▸sucᵘ in
        sucᵘ (⊢∷[]←⊢∷▸ ⊢l ▸l)
      (supᵘⱼ ⊢l₁ ⊢l₂) ▸supᵘ →
        let open ≤ᶜ-reasoning
            δ , η , γ≤δ+η , ▸l₁ , ▸l₂ = inv-usage-supᵘ ▸supᵘ
        in
        ⊢supᵘ
          (⊢∷[]←⊢∷▸ ⊢l₁ $
           sub ▸l₁ $ begin
             γ       ≤⟨ γ≤δ+η ⟩
             δ +ᶜ η  ≤⟨ +ᶜ-decreasingˡ _ _ ⟩
             δ       ∎)
          (⊢∷[]←⊢∷▸ ⊢l₂ $
           sub ▸l₂ $ begin
             γ       ≤⟨ γ≤δ+η ⟩
             δ +ᶜ η  ≤⟨ +ᶜ-decreasingʳ _ _ ⟩
             η       ∎)
      (Uⱼ ⊢l) _ →
        U (⊢∷L←⊢∷L ⊢l)
      (Liftⱼ _ ⊢l ⊢A) ▸Lift →
        let _ , ▸A = inv-usage-Lift ▸Lift in
        Lift (⊢∷L←⊢∷L ⊢l) (⊢∷[]←⊢∷▸ ⊢A ▸A)
      (liftⱼ ⊢l _ ⊢t) ▸lift →
        let ▸t = inv-usage-lift ▸lift in
        lift (⊢∷L←⊢∷L ⊢l) (⊢∷[]←⊢∷▸ ⊢t ▸t)
      (lowerⱼ ⊢t) ▸lower →
        let ▸t = inv-usage-lower ▸lower in
        lower (⊢∷[]←⊢∷▸ ⊢t ▸t)
      (Emptyⱼ ⊢Γ) _ →
        Empty (⊢←⊢′ ⊢Γ)
      (emptyrecⱼ ⊢A ⊢t) ▸er →
        let open ≤ᶜ-reasoning
            invUsageEmptyrec {δ} ▸t _ ok γ≤pδ =
              inv-usage-emptyrec ▸er
        in
        emptyrec ok (⊢←⊢ ⊢A) $
        ⊢∷[]←⊢∷▸ ⊢t (rec-lemma ▸t γ≤pδ)
      (Unitⱼ ⊢Γ ok) _ →
        Unit ok (⊢←⊢′ ⊢Γ)
      (starⱼ ⊢Γ ok) _ →
        star ok (⊢←⊢′ ⊢Γ)
      (unitrecⱼ {p} ⊢A ⊢t ⊢u ok) ▸ur →
        let open ≤ᶜ-reasoning
            invUsageUnitrec {δ} {η} ▸t ▸u _ ok γ≤pδ+η =
              inv-usage-unitrec ▸ur
        in
        unitrec ok (⊢←⊢ ⊢A)
          (⊢∷[]←⊢∷▸ ⊢t $
           rec-lemma ▸t $ begin
             γ            ≤⟨ γ≤pδ+η ⟩
             p ·ᶜ δ +ᶜ η  ≤⟨ +ᶜ-decreasingˡ _ _ ⟩
             p ·ᶜ δ       ∎)
          (⊢∷[]←⊢∷▸ ⊢u $
           sub ▸u $ begin
             γ            ≤⟨ γ≤pδ+η ⟩
             p ·ᶜ δ +ᶜ η  ≤⟨ +ᶜ-decreasingʳ _ _ ⟩
             η            ∎)
      (ΠΣⱼ {p} {q} _ ⊢A ⊢B ok) ▸ΠΣ →
        let open ≤ᶜ-reasoning
            invUsageΠΣ {δ} {η} ▸A ▸B γ≤δ+η = inv-usage-ΠΣ ▸ΠΣ
        in
        ΠΣ ok
          (⊢∷[]←⊢∷▸ ⊢A $
           rec-lemma ▸A $ begin
             γ            ≤⟨ γ≤δ+η ⟩
             p ·ᶜ δ +ᶜ η  ≤⟨ +ᶜ-decreasingˡ _ _ ⟩
             p ·ᶜ δ       ∎)
          (⊢∷[]←⊢∷▸ ⊢B $
           sub ▸B $ begin
             γ           ∙             q  ≤⟨ γ≤δ+η ∙ ≤-refl ⟩
             p ·ᶜ δ +ᶜ η ∙             q  ≤⟨ +ᶜ-decreasingʳ _ _ ∙ ·-increasingˡ ⟩
             η           ∙ ⌜ ⌞ o ⌟ ⌝ · q  ∎)
      (lamⱼ {p} _ ⊢t ok) ▸lam →
        let open ≤ᶜ-reasoning
            invUsageLam {δ} ▸t γ≤δ = inv-usage-lam ▸lam
        in
        lam ok $
        ⊢∷[]←⊢∷▸ ⊢t $
        sub ▸t $ begin
           γ ∙             p  ≤⟨ γ≤δ ∙ ·-increasingˡ ⟩
           δ ∙ ⌜ ⌞ o ⌟ ⌝ · p  ∎
      (_∘ⱼ_ {p} ⊢t ⊢u) ▸app →
        let open ≤ᶜ-reasoning
            invUsageApp {δ} {η} ▸t ▸u γ≤δ+pη = inv-usage-app ▸app
        in
        app
          (⊢∷[]←⊢∷▸ ⊢t $
           sub ▸t $ begin
             γ            ≤⟨ γ≤δ+pη ⟩
             δ +ᶜ p ·ᶜ η  ≤⟨ +ᶜ-decreasingˡ _ _ ⟩
             δ            ∎)
          (⊢∷[]←⊢∷▸ ⊢u $
           rec-lemma ▸u $ begin
             γ            ≤⟨ γ≤δ+pη ⟩
             δ +ᶜ p ·ᶜ η  ≤⟨ +ᶜ-decreasingʳ _ _ ⟩
             p ·ᶜ η       ∎)
      (prodⱼ {k = s} {p} ⊢B ⊢t ⊢u ok) ▸prod →
        let open ≤ᶜ-reasoning
            invUsageProd {δ} {η} ▸t ▸u γ≤pδ∧η γ≤pδ+η =
              inv-usage-prod ▸prod
            γ≤pδ+η = case PE.singleton s of λ where
              (𝕨 , eq) → γ≤pδ+η eq
              (𝕤 , eq) → begin
                γ            ≤⟨ γ≤pδ∧η eq ⟩
                p ·ᶜ δ ∧ᶜ η  ≈⟨ ∧ᶜ≈ᶜ+ᶜ ⟩
                p ·ᶜ δ +ᶜ η  ∎
        in
        prod ok (⊢←⊢ ⊢B)
          (⊢∷[]←⊢∷▸ ⊢t $
           rec-lemma ▸t $ begin
             γ            ≤⟨ γ≤pδ+η ⟩
             p ·ᶜ δ +ᶜ η  ≤⟨ +ᶜ-decreasingˡ _ _ ⟩
             p ·ᶜ δ       ∎)
          (⊢∷[]←⊢∷▸ ⊢u $
           sub ▸u $ begin
             γ            ≤⟨ γ≤pδ+η ⟩
             p ·ᶜ δ +ᶜ η  ≤⟨ +ᶜ-decreasingʳ _ _ ⟩
             η            ∎)
      (fstⱼ ⊢B ⊢t) ▸fst →
        let _ , _ , _ , ▸t , γ≤δ , ok = inv-usage-fst₀₁ ▸fst in
        fst ([⌞⌟≡𝟙ᵐ→≤ω]→≤ ok) (⊢∷[]←⊢∷▸ ⊢t (sub ▸t γ≤δ))
      (sndⱼ _ ⊢t) ▸snd →
        let invUsageSnd ▸t γ≤δ = inv-usage-snd ▸snd in
        snd (⊢∷[]←⊢∷▸ ⊢t (sub ▸t γ≤δ))
      (prodrecⱼ {p} {r} {q} ⊢C ⊢t ⊢u _) ▸pr →
        let open ≤ᶜ-reasoning
            invUsageProdrec {δ} {η} ▸t ▸u _ ok γ≤rδ+η =
              inv-usage-prodrec ▸pr
        in
        prodrec ok (⊢←⊢ ⊢C)
          (⊢∷[]←⊢∷▸ ⊢t $
           rec-lemma ▸t $ begin
             γ            ≤⟨ γ≤rδ+η ⟩
             r ·ᶜ δ +ᶜ η  ≤⟨ +ᶜ-decreasingˡ _ _ ⟩
             r ·ᶜ δ       ∎)
          (⊢∷[]←⊢∷▸ ⊢u $
           sub ▸u $ begin
             γ           ∙              r · p  ∙             r  ≤⟨ γ≤rδ+η ∙ ≤-refl ∙ ≤-refl ⟩
             r ·ᶜ δ +ᶜ η ∙              r · p  ∙             r  ≤⟨ +ᶜ-decreasingʳ _ _ ∙ ·-increasingˡ {q = ⌜ ⌞ _ ⌟ ⌝} ∙ ·-increasingˡ ⟩
             η           ∙ ⌜ ⌞ o ⌟ ⌝ · (r · p) ∙ ⌜ ⌞ o ⌟ ⌝ · r  ∎)
      (ℕⱼ ⊢Γ) _ →
        ℕ (⊢←⊢′ ⊢Γ)
      (zeroⱼ ⊢Γ) _ →
        zero (⊢←⊢′ ⊢Γ)
      (sucⱼ ⊢t) ▸suc →
        let invUsageSuc ▸t γ≤δ = inv-usage-suc ▸suc in
        suc (⊢∷[]←⊢∷▸ ⊢t (sub ▸t γ≤δ))
      (natrecⱼ {p} {r} ⊢t ⊢u ⊢v) ▸nr →
        let ⊢A = ⊢←⊢ (⊢∙→⊢ (wfTerm ⊢u))
        in
        case inv-usage-natrec₀₁ ▸nr of λ {
          (invUsageNatrec {δ} {η} {θ} {χ} ▸t ▸u ▸v ▸A γ≤χ more) →
        case more of λ where
          invUsageNatrecNr →
            let γ≤δ+η+θ = let open ≤ᶜ-reasoning in begin
                  γ                             ≤⟨ γ≤χ ⟩
                  nrᶜ ⦃ has-nr = _ ⦄ p r δ η θ  ≈⟨ nrᶜ-unique ⟩
                  nrᶜ ⦃ has-nr = _ ⦄ p r δ η θ  ≈⟨ nrᶜ≈ᶜ ⟩
                  δ +ᶜ η +ᶜ θ                   ∎
            in
            natrec ⊢A
              (⊢∷[]←⊢∷▸ ⊢t $
               sub ▸t $ let open ≤ᶜ-reasoning in begin
                 γ            ≤⟨ γ≤δ+η+θ ⟩
                 δ +ᶜ η +ᶜ θ  ≤⟨ +ᶜ-decreasingˡ _ _ ⟩
                 δ            ∎)
              (⊢∷[]←⊢∷▸ ⊢u $
               sub ▸u $ let open ≤ᶜ-reasoning in begin
                 γ           ∙             p ∙             r  ≤⟨ γ≤δ+η+θ ∙ ≤-refl ∙ ≤-refl ⟩
                 δ +ᶜ η +ᶜ θ ∙             p ∙             r  ≤⟨ +ᶜ-decreasingʳ _ _ ∙ ≤-refl ∙ ≤-refl ⟩
                 η +ᶜ θ      ∙             p ∙             r  ≤⟨ +ᶜ-decreasingˡ _ _ ∙ ·-increasingˡ ∙ ·-increasingˡ ⟩
                 η           ∙ ⌜ ⌞ o ⌟ ⌝ · p ∙ ⌜ ⌞ o ⌟ ⌝ · r  ∎)
              (⊢∷[]←⊢∷▸ ⊢v $
               sub ▸v $ let open ≤ᶜ-reasoning in begin
                 γ            ≤⟨ γ≤δ+η+θ ⟩
                 δ +ᶜ η +ᶜ θ  ≤⟨ +ᶜ-decreasingʳ _ _ ⟩
                 η +ᶜ θ       ≤⟨ +ᶜ-decreasingʳ _ _ ⟩
                 θ            ∎)
          (invUsageNatrecNoNr χ≤δ χ≤η χ≤θ _) →
            natrec ⊢A
              (⊢∷[]←⊢∷▸ ⊢t $
               sub ▸t $ let open ≤ᶜ-reasoning in begin
                 γ  ≤⟨ γ≤χ ⟩
                 χ  ≤⟨ χ≤δ ⟩
                 δ  ∎)
              (⊢∷[]←⊢∷▸ ⊢u $
               sub ▸u $ let open ≤ᶜ-reasoning in begin
                 γ ∙             p ∙             r  ≤⟨ γ≤χ ∙ ≤-refl ∙ ≤-refl ⟩
                 χ ∙             p ∙             r  ≤⟨ χ≤η (𝟘ᵐ-allowed→¬Trivialᵐ _) ∙ ·-increasingˡ ∙ ·-increasingˡ ⟩
                 η ∙ ⌜ ⌞ o ⌟ ⌝ · p ∙ ⌜ ⌞ o ⌟ ⌝ · r  ∎)
              (⊢∷[]←⊢∷▸ ⊢v $
               sub ▸v $ let open ≤ᶜ-reasoning in begin
                 γ  ≤⟨ γ≤χ ⟩
                 χ  ≤⟨ χ≤θ ⟩
                 θ  ∎)
          (invUsageNatrecNoNrGLB {χ} {x = q} glb₁ glb₂) →
            let q≡ω = let open Tools.Reasoning.PropositionalEquality in
                  q      ≡⟨ GLB-unique glb₁ (Erasure-nrᵢ-glb-∧ _ _ _) ⟩
                  ω ∧ p  ≡⟨⟩
                  ω      ∎
                open ≤ᶜ-reasoning
                γ≤θ+χ = begin
                  γ            ≤⟨ γ≤χ ⟩
                  q ·ᶜ θ +ᶜ χ  ≈⟨ +ᶜ-congʳ $ ·ᶜ-congʳ q≡ω ⟩
                  ω ·ᶜ θ +ᶜ χ  ≈⟨ +ᶜ-congʳ $ ·ᶜ-identityˡ _ ⟩
                  θ      +ᶜ χ  ∎
                γ≤δ+η = begin
                  γ       ≤⟨ γ≤θ+χ ⟩
                  θ +ᶜ χ  ≤⟨ +ᶜ-decreasingʳ _ _ ⟩
                  χ       ≈⟨ GLBᶜ-unique glb₂ Erasure-nrᵢᶜ-glb-∧ᶜ ⟩
                  δ ∧ᶜ η  ≈⟨ ∧ᶜ≈ᶜ+ᶜ ⟩
                  δ +ᶜ η  ∎
            in
            natrec ⊢A
              (⊢∷[]←⊢∷▸ ⊢t $
               sub ▸t $ begin
                 γ       ≤⟨ γ≤δ+η ⟩
                 δ +ᶜ η  ≤⟨ +ᶜ-decreasingˡ _ _ ⟩
                 δ       ∎)
              (⊢∷[]←⊢∷▸ ⊢u $
               sub ▸u $ begin
                 γ      ∙             p ∙             r  ≤⟨ γ≤δ+η ∙ ≤-refl ∙ ≤-refl ⟩
                 δ +ᶜ η ∙             p ∙             r  ≤⟨ +ᶜ-decreasingʳ _ _ ∙ ·-increasingˡ ∙ ·-increasingˡ ⟩
                 η      ∙ ⌜ ⌞ o ⌟ ⌝ · p ∙ ⌜ ⌞ o ⌟ ⌝ · r  ∎)
              (⊢∷[]←⊢∷▸ ⊢v $
               sub ▸v $ begin
                 γ       ≤⟨ γ≤θ+χ ⟩
                 θ +ᶜ χ  ≤⟨ +ᶜ-decreasingˡ _ _ ⟩
                 θ       ∎) }
      (Idⱼ ⊢A ⊢t ⊢u) ▸Id →
        let open ≤ᶜ-reasoning in
        case inv-usage-Id ▸Id of λ where
          (invUsageId {δ} {η} {θ} not-erased ▸A ▸t ▸u γ≤δ+η+θ) →
            Id (⊥-elim ∘→ not-erased) (λ _ → PE.refl , PE.refl)
              (⊢∷[]←⊢∷▸ ⊢A $ sub ▸A $ begin
                 γ            ≤⟨ γ≤δ+η+θ ⟩
                 δ +ᶜ η +ᶜ θ  ≤⟨ +ᶜ-decreasingˡ _ _ ⟩
                 δ            ∎)
              (⊢∷[]←⊢∷▸ ⊢t $ sub ▸t $ begin
                 γ            ≤⟨ γ≤δ+η+θ ⟩
                 δ +ᶜ η +ᶜ θ  ≤⟨ +ᶜ-decreasingʳ _ _ ⟩
                 η +ᶜ θ       ≤⟨ +ᶜ-decreasingˡ _ _ ⟩
                 η            ∎)
              (⊢∷[]←⊢∷▸ ⊢u $ sub ▸u $ begin
                 γ            ≤⟨ γ≤δ+η+θ ⟩
                 δ +ᶜ η +ᶜ θ  ≤⟨ +ᶜ-decreasingʳ _ _ ⟩
                 η +ᶜ θ       ≤⟨ +ᶜ-decreasingʳ _ _ ⟩
                 θ            ∎)
          (invUsageId₀ erased _ _ _ _) →
            Id (λ _ → PE.refl , PE.refl) (⊥-elim ∘→ (_$ erased))
              (⊢∷←⊢∷ ⊢A) (⊢∷←⊢∷ ⊢t) (⊢∷←⊢∷ ⊢u)
      (rflⱼ ⊢t) _ →
        rfl (⊢∷←⊢∷ ⊢t)
      (Jⱼ {p} {q} ⊢t ⊢B ⊢u ⊢v ⊢w) ▸J →
        let open ≤ᶜ-reasoning
            ⊢A = ⊢←⊢ (wf-⊢∷ ⊢t)
        in
        case inv-usage-J ▸J of λ where
          (invUsageJ
             {γ₂} {γ₃} {γ₄} {γ₅} {γ₆}
             ≤some ¬[p≡𝟘×q≡𝟘] _ ▸t ▸B ▸u ▸v ▸w γ≤) →
            let γ≤ = begin
                  γ                                    ≤⟨ γ≤ ⟩
                  M.ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)  ≈⟨ ·ᶜ-identityˡ _ ⟩
                  γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆           ∎
                γ≤′ = begin
                  γ                           ≤⟨ γ≤ ⟩
                  γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆  ≤⟨ +ᶜ-decreasingʳ _ _ ⟩
                  γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆        ∎
                γ≤″ = begin
                  γ                     ≤⟨ γ≤′ ⟩
                  γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆  ≤⟨ +ᶜ-decreasingʳ _ _ ⟩
                  γ₄ +ᶜ γ₅ +ᶜ γ₆        ∎
                γ≤‴ = begin
                  γ               ≤⟨ γ≤″ ⟩
                  γ₄ +ᶜ γ₅ +ᶜ γ₆  ≤⟨ +ᶜ-decreasingʳ _ _ ⟩
                  γ₅ +ᶜ γ₆        ∎
            in
            J (λ _ _ → PE.refl , PE.refl , PE.refl , PE.refl)
              (λ ≡some p≡𝟘 q≡𝟘 → ⊥-elim (¬[p≡𝟘×q≡𝟘] ≡some (p≡𝟘 , q≡𝟘)))
              (λ ≡all → case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ())
              ⊢A
              (⊢∷[]←⊢∷▸ ⊢t $
               sub ▸t $ begin
                 γ                           ≤⟨ γ≤ ⟩
                 γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆  ≤⟨ +ᶜ-decreasingˡ _ _ ⟩
                 γ₂                          ∎)
              (⊢[]←⊢▸ ⊢B $
               sub ▸B $ begin
                 γ                    ∙             p ∙             q  ≤⟨ γ≤′ ∙ ≤-refl ∙ ≤-refl ⟩
                 γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆ ∙             p ∙             q  ≤⟨ +ᶜ-decreasingˡ _ _ ∙ ·-increasingˡ ∙ ·-increasingˡ ⟩
                 γ₃                   ∙ ⌜ ⌞ o ⌟ ⌝ · p ∙ ⌜ ⌞ o ⌟ ⌝ · q  ∎)
              (⊢∷[]←⊢∷▸ ⊢u $
               sub ▸u $ begin
                 γ               ≤⟨ γ≤″ ⟩
                 γ₄ +ᶜ γ₅ +ᶜ γ₆  ≤⟨ +ᶜ-decreasingˡ _ _ ⟩
                 γ₄              ∎)
              (⊢∷[]←⊢∷▸ ⊢v $
               sub ▸v $ begin
                 γ         ≤⟨ γ≤‴ ⟩
                 γ₅ +ᶜ γ₆  ≤⟨ +ᶜ-decreasingˡ _ _ ⟩
                 γ₅        ∎)
              (⊢∷[]←⊢∷▸ ⊢w $
               sub ▸w $ begin
                 γ         ≤⟨ γ≤‴ ⟩
                 γ₅ +ᶜ γ₆  ≤⟨ +ᶜ-decreasingʳ _ _ ⟩
                 γ₆        ∎)
          (invUsageJ₀₁
             {γ₃} {γ₄} ≡some PE.refl PE.refl _ _ ▸B ▸u _ _ γ≤) →
            let γ≤γ₃+γ₄ = begin
                  γ                ≤⟨ γ≤ ⟩
                  ω ·ᶜ (γ₃ +ᶜ γ₄)  ≈⟨ ·ᶜ-identityˡ _ ⟩
                  γ₃ +ᶜ γ₄         ∎
            in
            J (λ _ ¬[p≡𝟘×q≡𝟘] →
                 ⊥-elim (¬[p≡𝟘×q≡𝟘] ≡some (PE.refl , PE.refl)))
              (λ _ _ _ → PE.refl , PE.refl , PE.refl , PE.refl)
              (λ ≡all → case PE.trans (PE.sym ≡some) ≡all of λ ())
              ⊢A (⊢∷←⊢∷ ⊢t)
              (⊢[]←⊢▸ ⊢B $
               sub ▸B $ begin
                 γ        ∙ 𝟘 ∙ 𝟘  ≤⟨ γ≤γ₃+γ₄ ∙ ≤-refl ∙ ≤-refl ⟩
                 γ₃ +ᶜ γ₄ ∙ 𝟘 ∙ 𝟘  ≤⟨ +ᶜ-decreasingˡ _ _ ∙ ≤-refl ∙ ≤-refl ⟩
                 γ₃       ∙ 𝟘 ∙ 𝟘  ∎)
              (⊢∷[]←⊢∷▸ ⊢u $
               sub ▸u $ begin
                 γ         ≤⟨ γ≤γ₃+γ₄ ⟩
                 γ₃ +ᶜ γ₄  ≤⟨ +ᶜ-decreasingʳ _ _ ⟩
                 γ₄        ∎)
              (⊢∷←⊢∷ ⊢v) (⊢∷←⊢∷ ⊢w)
          (invUsageJ₀₂ ≡all _ _ _ ▸u _ _ γ≤) →
            J (λ ≤some → case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ())
              (λ ≡some _ _ → case PE.trans (PE.sym ≡some) ≡all of λ ())
              (λ _ → PE.refl , PE.refl , PE.refl , PE.refl)
              ⊢A (⊢∷←⊢∷ ⊢t) (⊢←⊢ ⊢B) (⊢∷[]←⊢∷▸ ⊢u (sub ▸u γ≤))
              (⊢∷←⊢∷ ⊢v) (⊢∷←⊢∷ ⊢w)
      (Kⱼ {p} ⊢B ⊢u ⊢v ok) ▸K →
        let open ≤ᶜ-reasoning
            ⊢A , ⊢t , _ = inversion-Id (wf-⊢∷ ⊢v)
            ⊢A          = ⊢←⊢ ⊢A
        in
        case inv-usage-K ▸K of λ where
          (invUsageK {γ₂} {γ₃} {γ₄} {γ₅} ≤some p≢𝟘 _ ▸t ▸B ▸u ▸v γ≤) →
            let γ≤ = begin
                  γ                              ≤⟨ γ≤ ⟩
                  M.ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅)  ≈⟨ ·ᶜ-identityˡ _ ⟩
                  γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅           ∎
                γ≤′ = begin
                  γ                     ≤⟨ γ≤ ⟩
                  γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅  ≤⟨ +ᶜ-decreasingʳ _ _ ⟩
                  γ₃ +ᶜ γ₄ +ᶜ γ₅        ∎
                γ≤″ = begin
                  γ               ≤⟨ γ≤′ ⟩
                  γ₃ +ᶜ γ₄ +ᶜ γ₅  ≤⟨ +ᶜ-decreasingʳ _ _ ⟩
                  γ₄ +ᶜ γ₅        ∎
            in
            K (λ _ _ → PE.refl , PE.refl , PE.refl , PE.refl)
              (λ ≡some p≡𝟘 → ⊥-elim (p≢𝟘 ≡some p≡𝟘))
              (λ ≡all → case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ())
              ok ⊢A
              (⊢∷[]←⊢∷▸ ⊢t $
               sub ▸t $ begin
                 γ                     ≤⟨ γ≤ ⟩
                 γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅  ≤⟨ +ᶜ-decreasingˡ _ _ ⟩
                 γ₂                    ∎)
              (⊢[]←⊢▸ ⊢B $
               sub ▸B $ begin
                 γ              ∙             p  ≤⟨ γ≤′ ∙ ≤-refl ⟩
                 γ₃ +ᶜ γ₄ +ᶜ γ₅ ∙             p  ≤⟨ +ᶜ-decreasingˡ _ _ ∙ ·-increasingˡ ⟩
                 γ₃             ∙ ⌜ ⌞ o ⌟ ⌝ · p  ∎)
              (⊢∷[]←⊢∷▸ ⊢u $
               sub ▸u $ begin
                 γ         ≤⟨ γ≤″ ⟩
                 γ₄ +ᶜ γ₅  ≤⟨ +ᶜ-decreasingˡ _ _ ⟩
                 γ₄        ∎)
              (⊢∷[]←⊢∷▸ ⊢v $
               sub ▸v $ begin
                 γ         ≤⟨ γ≤″ ⟩
                 γ₄ +ᶜ γ₅  ≤⟨ +ᶜ-decreasingʳ _ _ ⟩
                 γ₅        ∎)
          (invUsageK₀₁ {γ₃} {γ₄} ≡some PE.refl _ _ ▸B ▸u _ γ≤) →
            let γ≤γ₃+γ₄ = begin
                  γ                ≤⟨ γ≤ ⟩
                  ω ·ᶜ (γ₃ +ᶜ γ₄)  ≈⟨ ·ᶜ-identityˡ _ ⟩
                  γ₃ +ᶜ γ₄         ∎
            in
            K (λ _ p≢𝟘 → ⊥-elim (p≢𝟘 ≡some PE.refl))
              (λ _ _ → PE.refl , PE.refl , PE.refl , PE.refl)
              (λ ≡all → case PE.trans (PE.sym ≡some) ≡all of λ ())
              ok ⊢A (⊢∷←⊢∷ ⊢t)
              (⊢[]←⊢▸ ⊢B $
               sub ▸B $ begin
                 γ        ∙ 𝟘  ≤⟨ γ≤γ₃+γ₄ ∙ ≤-refl ⟩
                 γ₃ +ᶜ γ₄ ∙ 𝟘  ≤⟨ +ᶜ-decreasingˡ _ _ ∙ ≤-refl ⟩
                 γ₃       ∙ 𝟘  ∎)
              (⊢∷[]←⊢∷▸ ⊢u $
               sub ▸u $ begin
                 γ         ≤⟨ γ≤γ₃+γ₄ ⟩
                 γ₃ +ᶜ γ₄  ≤⟨ +ᶜ-decreasingʳ _ _ ⟩
                 γ₄        ∎)
              (⊢∷←⊢∷ ⊢v)
          (invUsageK₀₂ ≡all _ _ _ ▸u _ γ≤) →
            K (λ ≤some → case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ())
              (λ ≡some _ → case PE.trans (PE.sym ≡some) ≡all of λ ())
              (λ _ → PE.refl , PE.refl , PE.refl , PE.refl)
              ok ⊢A (⊢∷←⊢∷ ⊢t) (⊢←⊢ ⊢B) (⊢∷[]←⊢∷▸ ⊢u (sub ▸u γ≤))
              (⊢∷←⊢∷ ⊢v)
      ([]-congⱼ ⊢l ⊢A ⊢t ⊢u ⊢v ok) ▸bc →
        let invUsage-[]-cong _ _ _ _ _ ok′ _ = inv-usage-[]-cong ▸bc in
        []-cong ok ok′ (⊢∷L←⊢∷L ⊢l) (⊢←⊢ ⊢A) (⊢∷←⊢∷ ⊢t) (⊢∷←⊢∷ ⊢u)
          (⊢∷←⊢∷ ⊢v)

  opaque

    -- If σ is well-formed and well-resourced, then σ is well-formed and
    -- well-resourced.

    ⊢ˢʷ∷[]←⊢ˢʷ∷▸ :
      Η S.⊢ˢʷ σ ∷ Δ → (∀ x → δ ▸[ ⌞ p ⌟ ] σ x) → δ ▸ Η ⊢ˢʷ σ ∷[ p ] Δ
    ⊢ˢʷ∷[]←⊢ˢʷ∷▸ {Δ = ε}     ⊢σ _  = ε (⊢←⊢′ (⊢ˢʷ∷ε⇔ .proj₁ ⊢σ))
    ⊢ˢʷ∷[]←⊢ˢʷ∷▸ {Δ = _ ∙ _} ⊢σ ▸σ =
      let ⊢σ₊ , ⊢σ₀ = ⊢ˢʷ∷∙⇔ .proj₁ ⊢σ in
      ⊢ˢʷ∷[]←⊢ˢʷ∷▸ ⊢σ₊ (▸σ ∘→ _+1) ∙ ⊢∷[]←⊢∷▸ ⊢σ₀ (▸σ x0)

------------------------------------------------------------------------
-- Logical equivalences

-- The equivalences are proven under the assumption that certain things
-- must always be allowed when the mode is 𝟘ᵐ[ ok ].

module _ (ok : Allowed-at-𝟘ᵐ) where

  opaque

    -- A logical equivalence for "is a well-formed type".

    ⊢[]⇔⊢▸ : γ ▸ Γ ⊢[ p ] A ⇔ (Γ T.⊢ A × γ ▸[ ⌞ p ⌟ ] A)
    ⊢[]⇔⊢▸ = (λ ⊢A → ⊢[]→⊢ ⊢A , ⊢[]→▸ ⊢A) , λ (⊢A , ▸A) → ⊢[]←⊢▸ ok ⊢A ▸A

  opaque

    -- A variant of ⊢[]⇔⊢▸.

    ⊢[]⇔⊢▸′ : γ ▸ Γ ⊢[ ⌜ m ⌝ ] A ⇔ (Γ T.⊢ A × γ ▸[ m ] A)
    ⊢[]⇔⊢▸′ =
      PE.subst (_⇔_ _)
        (PE.cong (_×_ _) (PE.cong (flip (_▸[_]_ _) _) (⌞⌜⌝⌟ _)))
        ⊢[]⇔⊢▸

  opaque

    -- A logical equivalence for "is a well-typed term".

    ⊢∷[]⇔⊢∷▸ : γ ▸ Γ ⊢ t ∷[ p ] A ⇔ (Γ T.⊢ t ∷ A × γ ▸[ ⌞ p ⌟ ] t)
    ⊢∷[]⇔⊢∷▸ = (λ ⊢t → ⊢∷[]→⊢∷ ⊢t , ⊢∷[]→▸ ⊢t) , λ (⊢t , ▸t) → ⊢∷[]←⊢∷▸ ok ⊢t ▸t

  opaque

    -- A variant of ⊢∷[]⇔⊢∷▸.

    ⊢∷[]⇔⊢∷▸′ : γ ▸ Γ ⊢ t ∷[ ⌜ m ⌝ ] A ⇔ (Γ T.⊢ t ∷ A × γ ▸[ m ] t)
    ⊢∷[]⇔⊢∷▸′ =
      PE.subst (_⇔_ _)
        (PE.cong (_×_ _) (PE.cong (flip (_▸[_]_ _) _) (⌞⌜⌝⌟ _)))
        ⊢∷[]⇔⊢∷▸

  opaque

    -- A logical equivalence for "is a well-formed substitution".

    ⊢ˢʷ∷[]⇔⊢ˢʷ∷▸ :
      δ ▸ Η ⊢ˢʷ σ ∷[ p ] Δ ⇔ (Η S.⊢ˢʷ σ ∷ Δ × ∀ x → δ ▸[ ⌞ p ⌟ ] σ x)
    ⊢ˢʷ∷[]⇔⊢ˢʷ∷▸ =
      (λ ⊢σ → ⊢ˢʷ∷[]→⊢ˢʷ∷ ⊢σ , ⊢ˢʷ∷[]→▸ ⊢σ) , uncurry (⊢ˢʷ∷[]←⊢ˢʷ∷▸ ok)

  opaque

    -- A variant of ⊢ˢʷ∷[]⇔⊢ˢʷ∷▸.

    ⊢ˢʷ∷[]⇔⊢ˢʷ∷▸′ :
      δ ▸ Η ⊢ˢʷ σ ∷[ ⌜ m ⌝ ] Δ ⇔ (Η S.⊢ˢʷ σ ∷ Δ × ∀ x → δ ▸[ m ] σ x)
    ⊢ˢʷ∷[]⇔⊢ˢʷ∷▸′ =
      PE.subst (_⇔_ _)
        (PE.cong (_×_ _) (PE.cong (λ m → ∀ _ → _ ▸[ m ] _) (⌞⌜⌝⌟ _)))
        ⊢ˢʷ∷[]⇔⊢ˢʷ∷▸

  opaque

    -- Logical equivalences between judgements without grade contexts.

    ⊢[]⇔⊢[] : Γ C.⊢[ 𝓙 ] ⇔ Γ T.⊢[ 𝓙 ]
    ⊢[]⇔⊢[] {𝓙 = [ctxt]}          = ⊢→⊢       , ⊢←⊢′      ok
    ⊢[]⇔⊢[] {𝓙 = [ _ type]}       = ⊢[]→⊢     , ⊢←⊢       ok
    ⊢[]⇔⊢[] {𝓙 = [ _ ≡ _ type]}   = ⊢≡→⊢≡     , ⊢≡←⊢≡     ok
    ⊢[]⇔⊢[] {𝓙 = [ _ ∷ _ ]}       = ⊢∷[]→⊢∷   , ⊢∷←⊢∷     ok
    ⊢[]⇔⊢[] {𝓙 = [ _ ≡ _ ∷ _ ]}   = ⊢≡∷→⊢≡∷   , ⊢≡∷←⊢≡∷   ok
    ⊢[]⇔⊢[] {𝓙 = [ _ ∷Level]}     = ⊢∷L→⊢∷L   , ⊢∷L←⊢∷L   ok
    ⊢[]⇔⊢[] {𝓙 = [ _ ≡ _ ∷Level]} = ⊢≡∷L→⊢≡∷L , ⊢≡∷L←⊢≡∷L ok
