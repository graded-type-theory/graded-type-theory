------------------------------------------------------------------------
-- Some properties related to typing and Erased
------------------------------------------------------------------------

open import Graded.Modality
open import Definition.Typed.Restrictions

module Graded.Derived.Erased.Typed
  {a} {M : Set a}
  (𝕄 : Modality M)
  (open Modality 𝕄)
  (R : Type-restrictions M)
  (open Type-restrictions R)
  -- The Unit restriction is assumed to hold.
  (Unit-ok : Unit-restriction)
  -- The Σₚ restriction is assumed to hold for 𝟘 and 𝟘.
  (Σₚ-ok : Σₚ-restriction 𝟘 𝟘)
  where

open import Definition.Typed R
open import Definition.Typed.Consequences.Inequality R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Properties R

open import Definition.Untyped M as U hiding (_∷_; _[_])
open import Graded.Derived.Erased.Untyped 𝕄

open import Graded.Context 𝕄
open import Graded.Modality.Properties 𝕄
import Graded.Usage 𝕄 as MU
import Graded.Usage.Inversion 𝕄 as MUI
open import Graded.Usage.Restrictions M

open import Graded.Mode 𝕄

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nullary
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder

private variable
  Γ       : Con Term _
  A B t u : Term _

------------------------------------------------------------------------
-- Typing rules

-- A formation rule for Erased.

Erasedⱼ : Γ ⊢ A → Γ ⊢ Erased A
Erasedⱼ ⊢A = ΠΣⱼ ⊢A (Unitⱼ (wf ⊢A ∙ ⊢A) Unit-ok) Σₚ-ok

-- A corresponding congruence rule.

Erased-cong :
  Γ ⊢ A ≡ B →
  Γ ⊢ Erased A ≡ Erased B
Erased-cong A≡B =
  ΠΣ-cong ⊢A A≡B (refl (Unitⱼ (wf ⊢A ∙ ⊢A) Unit-ok)) Σₚ-ok
  where
  ⊢A = syntacticEq A≡B .proj₁

-- An introduction rule for U.

Erasedⱼ-U : Γ ⊢ A ∷ U → Γ ⊢ Erased A ∷ U
Erasedⱼ-U ⊢A∷U = ΠΣⱼ ⊢A∷U (Unitⱼ (wf ⊢A ∙ ⊢A) Unit-ok) Σₚ-ok
  where
  ⊢A = univ ⊢A∷U

-- A corresponding congruence rule.

Erased-cong-U :
  Γ ⊢ A ≡ B ∷ U →
  Γ ⊢ Erased A ≡ Erased B ∷ U
Erased-cong-U A≡B =
  ΠΣ-cong ⊢A A≡B (refl (Unitⱼ (wf ⊢A ∙ ⊢A) Unit-ok)) Σₚ-ok
  where
  ⊢A = univ (syntacticEqTerm A≡B .proj₂ .proj₁)

-- An introduction rule for Erased.

[]ⱼ : Γ ⊢ t ∷ A → Γ ⊢ [ t ] ∷ Erased A
[]ⱼ ⊢t = prodⱼ ⊢A (Unitⱼ (⊢Γ ∙ ⊢A) Unit-ok) ⊢t (starⱼ ⊢Γ Unit-ok) Σₚ-ok
  where
  ⊢A = syntacticTerm ⊢t
  ⊢Γ = wf ⊢A

-- A corresponding congruence rule.

[]-cong :
  Γ ⊢ t ≡ u ∷ A → Γ ⊢ [ t ] ≡ [ u ] ∷ Erased A
[]-cong t≡u =
  prod-cong ⊢A (Unitⱼ (wf ⊢A ∙ ⊢A) Unit-ok) t≡u
    (refl (starⱼ (wf ⊢A) Unit-ok)) Σₚ-ok
  where
  ⊢A = syntacticEqTerm t≡u .proj₁

-- An elimination rule for Erased.

erasedⱼ : Γ ⊢ t ∷ Erased A → Γ ⊢ erased t ∷ A
erasedⱼ ⊢t = fstⱼ ⊢A (Unitⱼ (wf ⊢A ∙ ⊢A) Unit-ok) ⊢t
  where
  ⊢A = inversion-ΠΣ (syntacticTerm ⊢t) .proj₁

-- A corresponding congruence rule.

erased-cong : Γ ⊢ t ≡ u ∷ Erased A → Γ ⊢ erased t ≡ erased u ∷ A
erased-cong t≡u = fst-cong ⊢A (Unitⱼ (wf ⊢A ∙ ⊢A) Unit-ok) t≡u
  where
  ⊢A = inversion-ΠΣ (syntacticEqTerm t≡u .proj₁) .proj₁

-- A β-rule for Erased.

Erased-β :
  Γ ⊢ t ∷ A →
  Γ ⊢ erased [ t ] ≡ t ∷ A
Erased-β ⊢t =
  Σ-β₁ ⊢A (Unitⱼ (⊢Γ ∙ ⊢A) Unit-ok) ⊢t (starⱼ ⊢Γ Unit-ok) PE.refl Σₚ-ok
  where
  ⊢A = syntacticTerm ⊢t
  ⊢Γ = wf ⊢A

-- An η-rule for Erased.

Erased-η :
  Γ ⊢ t ∷ Erased A →
  Γ ⊢ u ∷ Erased A →
  Γ ⊢ erased t ≡ erased u ∷ A →
  Γ ⊢ t ≡ u ∷ Erased A
Erased-η ⊢t ⊢u t≡u = Σ-η
  ⊢A Γ∙A⊢Unit ⊢t ⊢u t≡u
  (η-unit (sndⱼ ⊢A Γ∙A⊢Unit ⊢t) (sndⱼ ⊢A Γ∙A⊢Unit ⊢u))
  where
  ⊢A       = syntacticEqTerm t≡u .proj₁
  Γ∙A⊢Unit = Unitⱼ (wf ⊢A ∙ ⊢A) Unit-ok

-- An instance of the η-rule.

[erased] :
  Γ ⊢ t ∷ Erased A →
  Γ ⊢ [ erased t ] ≡ t ∷ Erased A
[erased] ⊢t =
  Erased-η ([]ⱼ (erasedⱼ ⊢t)) ⊢t $
  Erased-β (erasedⱼ ⊢t)

------------------------------------------------------------------------
-- Inversion lemmas for typing

-- An inversion lemma for Erased.

inversion-Erased-∷ :
  Γ ⊢ Erased A ∷ B →
  Γ ⊢ A ∷ U × Γ ⊢ B ≡ U
inversion-Erased-∷ ⊢Erased =
  case inversion-ΠΣ-U ⊢Erased of λ (⊢A , _ , B≡ , _) →
  ⊢A , B≡

-- Another inversion lemma for Erased.

inversion-Erased : Γ ⊢ Erased A → Γ ⊢ A
inversion-Erased ⊢Erased = inversion-ΠΣ ⊢Erased .proj₁

-- An inversion lemma for [_].
--
-- TODO: Make it possible to replace the conclusion with
--
--   ∃ λ B → Γ ⊢ t ∷ B × Γ ⊢ A ≡ Erased B?

inversion-[] :
  Γ ⊢ [ t ] ∷ A →
  ∃₃ λ B q C →
     Γ ⊢ t ∷ B ×
     Γ ⊢ A ≡ Σₚ 𝟘 , q ▷ B ▹ C ×
     Γ ⊢ C U.[ t ] ≡ Unit
inversion-[] ⊢[] =
  case inversion-prod ⊢[] of
    λ (B , C , q , ⊢B , _ , ⊢t , ⊢star , A≡ , _) →
  case inversion-star ⊢star of λ (≡Unit , _) →
    B , q , C , ⊢t , A≡ , ≡Unit

-- Another inversion lemma for [_].

inversion-[]′ : Γ ⊢ [ t ] ∷ Erased A → Γ ⊢ t ∷ A
inversion-[]′ ⊢[] =
  case inversion-[] ⊢[] of
    λ (_ , _ , _ , ⊢t , Erased-A≡ , _) →
  case Σ-injectivity Erased-A≡ of
    λ (A≡ , _) →
  conv ⊢t (_⊢_≡_.sym A≡)

-- A certain form of inversion for [_] does not hold.

¬-inversion-[]′ :
  ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} →
     Γ ⊢ [ t ] ∷ A →
     ∃₂ λ B q → Γ ⊢ t ∷ B × Γ ⊢ A ≡ Σₚ 𝟘 , q ▷ B ▹ Unit)
¬-inversion-[]′ inversion-[] = bad
  where
  Γ′ = ε
  t′ = zero
  A′ = Σₚ 𝟘 , 𝟘 ▷ ℕ ▹ natrec 𝟙 𝟙 𝟙 U Unit ℕ (var x0)

  -- As an aside, note that if A′ is well-resourced then 𝟙 is equal
  -- to 𝟘.

  A′-well-resourced→𝟙≡𝟘 :
    (R : Usage-restrictions) →
    let open MU R in
    ∀ {γ} → γ ▸[ 𝟙ᵐ ] A′ → 𝟙 PE.≡ 𝟘
  A′-well-resourced→𝟙≡𝟘 R ▸A′ =
    case inv-usage-ΠΣ ▸A′ of λ {
      (invUsageΠΣ _ ▸nr _) →
    case inv-usage-natrec ▸nr of λ {
      (invUsageNatrec {δ = _ ∙ a} {η = _ ∙ b} {θ = _ ∙ c}
         _ ▸ℕ ▸0 _ (_ ∙ 𝟙𝟘≤a∧c⊛b+𝟙c▷𝟙)) →
    case inv-usage-ℕ ▸ℕ of λ {
      (_ ∙ _ ∙ 𝟙𝟙≤𝟘 ∙ _) →
    case inv-usage-var ▸0 of λ {
      (_ ∙ c≤𝟙) →
    ≤-antisym
      (begin
        𝟙      ≡˘⟨ ·-identityʳ _ ⟩
        𝟙 · 𝟙  ≤⟨ 𝟙𝟙≤𝟘 ⟩
        𝟘      ∎)
      (begin
         𝟘                        ≡˘⟨ ·-zeroʳ _ ⟩
         𝟙 · 𝟘                    ≤⟨ 𝟙𝟘≤a∧c⊛b+𝟙c▷𝟙 ⟩
         (a ∧ c) ⊛ b + 𝟙 · c ▷ 𝟙  ≤⟨ ⊛-ineq₂ _ _ _ ⟩
         a ∧ c                    ≤⟨ ∧-decreasingʳ _ _ ⟩
         c                        ≤⟨ c≤𝟙 ⟩
         𝟙                        ∎) }}}}
    where
    open Tools.Reasoning.PartialOrder ≤-poset
    open MUI R

  ⊢Γ′∙ℕ : ⊢ Γ′ ∙ ℕ
  ⊢Γ′∙ℕ = ε ∙ ℕⱼ ε

  ⊢Γ′∙ℕ∙ℕ : ⊢ Γ′ ∙ ℕ ∙ ℕ
  ⊢Γ′∙ℕ∙ℕ = ⊢Γ′∙ℕ ∙ ℕⱼ ⊢Γ′∙ℕ

  ⊢Γ′∙ℕ∙U : ⊢ Γ′ ∙ ℕ ∙ U
  ⊢Γ′∙ℕ∙U = ⊢Γ′∙ℕ ∙ Uⱼ ⊢Γ′∙ℕ

  ⊢[t′] : Γ′ ⊢ [ t′ ] ∷ A′
  ⊢[t′] = prodⱼ
    (ℕⱼ ε)
    (univ (natrecⱼ
             (Uⱼ ⊢Γ′∙ℕ∙ℕ)
             (Unitⱼ ⊢Γ′∙ℕ Unit-ok)
             (ℕⱼ (⊢Γ′∙ℕ∙ℕ ∙ Uⱼ ⊢Γ′∙ℕ∙ℕ))
             (var ⊢Γ′∙ℕ here)))
    (zeroⱼ ε)
    (conv (starⱼ ε Unit-ok)
       (_⊢_≡_.sym $
        univ (natrec-zero (Uⱼ ⊢Γ′∙ℕ) (Unitⱼ ε Unit-ok) (ℕⱼ ⊢Γ′∙ℕ∙U))))
    Σₚ-ok

  ℕ≡Unit : Γ′ ⊢ ℕ ≡ Unit
  ℕ≡Unit =
    case inversion-[] ⊢[t′] of
      λ (_ , _ , _ , A′≡) →
    case Σ-injectivity A′≡ of
      λ (_ , ≡Unit , _ , _ , _) →
    trans
      (_⊢_≡_.sym $ _⊢_≡_.univ $
       natrec-suc (Uⱼ ⊢Γ′∙ℕ) (Unitⱼ ε Unit-ok) (ℕⱼ ⊢Γ′∙ℕ∙U) (zeroⱼ ε))
      (substTypeEq ≡Unit (refl (sucⱼ (zeroⱼ ε))))

  bad : ⊥
  bad = ℕ≢Unitⱼ ℕ≡Unit

-- Another form of inversion for [] also does not hold.

¬-inversion-[] :
  ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} →
     Γ ⊢ [ t ] ∷ A →
     ∃ λ B → Γ ⊢ t ∷ B × Γ ⊢ A ≡ Erased B)
¬-inversion-[] inversion-[] =
  ¬-inversion-[]′ λ ⊢[] →
  case inversion-[] ⊢[] of λ (B , ⊢t , A≡) →
  B , 𝟘 , ⊢t , A≡

-- An inversion lemma for erased.
--
-- TODO: Make it possible to replace the conclusion with
--
--   Γ ⊢ t ∷ Erased A?

inversion-erased :
  Γ ⊢ erased t ∷ A →
  ∃₂ λ q B → Γ ⊢ t ∷ Σₚ 𝟘 , q ▷ A ▹ B
inversion-erased ⊢erased =
  case inversion-fst ⊢erased of λ (_ , C , q , ⊢B , ⊢C , ⊢t , ≡B) →
    q
  , C
  , conv ⊢t
      (ΠΣ-cong ⊢B (_⊢_≡_.sym ≡B) (refl ⊢C) (⊢∷ΠΣ→ΠΣ-restriction ⊢t))

-- A certain form of inversion for erased does not hold.

¬-inversion-erased′ :
  ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} →
     Γ ⊢ erased t ∷ A →
     ∃ λ q → Γ ⊢ t ∷ Σₚ 𝟘 , q ▷ A ▹ Unit)
¬-inversion-erased′ inversion-erased = bad
  where
  Γ′ = ε
  t′ = prodₚ 𝟘 zero zero
  A′ = ℕ

  ⊢Γ′∙ℕ : ⊢ Γ′ ∙ ℕ
  ⊢Γ′∙ℕ = ε ∙ ℕⱼ ε

  ⊢t′₁ : Γ′ ⊢ t′ ∷ Σ 𝟘 , 𝟘 ▷ ℕ ▹ ℕ
  ⊢t′₁ = prodⱼ (ℕⱼ ε) (ℕⱼ ⊢Γ′∙ℕ) (zeroⱼ ε) (zeroⱼ ε) Σₚ-ok

  ⊢erased-t′ : Γ′ ⊢ erased t′ ∷ A′
  ⊢erased-t′ = fstⱼ (ℕⱼ ε) (ℕⱼ ⊢Γ′∙ℕ) ⊢t′₁

  erased-t′≡zero : Γ′ ⊢ erased t′ ≡ zero ∷ A′
  erased-t′≡zero =
    Σ-β₁ (ℕⱼ ε) (ℕⱼ ⊢Γ′∙ℕ) (zeroⱼ ε) (zeroⱼ ε) PE.refl Σₚ-ok

  ⊢t′₂ : ∃ λ q → Γ′ ⊢ t′ ∷ Σₚ 𝟘 , q ▷ A′ ▹ Unit
  ⊢t′₂ = inversion-erased ⊢erased-t′

  ⊢snd-t′ : Γ′ ⊢ snd 𝟘 t′ ∷ Unit
  ⊢snd-t′ = sndⱼ (ℕⱼ ε) (Unitⱼ ⊢Γ′∙ℕ Unit-ok) (⊢t′₂ .proj₂)

  ℕ≡Unit : Γ′ ⊢ ℕ ≡ Unit
  ℕ≡Unit =
    case inversion-snd ⊢snd-t′ of
      λ (_ , _ , _ , _ , _ , ⊢t′ , Unit≡) →
    case inversion-prod ⊢t′ of
      λ (_ , _ , _ , _ , _ , ⊢zero , ⊢zero′ , Σ≡Σ , _) →
    case Σ-injectivity Σ≡Σ of
      λ (F≡F′ , G≡G′ , _ , _ , _) →
    case inversion-zero ⊢zero of
      λ ≡ℕ →
    case inversion-zero ⊢zero′ of
      λ ≡ℕ′ →
    _⊢_≡_.sym $
    _⊢_≡_.trans Unit≡ $
    trans
      (substTypeEq G≡G′ $
       conv erased-t′≡zero (_⊢_≡_.sym (trans F≡F′ ≡ℕ)))
    ≡ℕ′

  bad : ⊥
  bad = ℕ≢Unitⱼ ℕ≡Unit

-- Another form of inversion for erased also does not hold.

¬-inversion-erased :
  ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} →
     Γ ⊢ erased t ∷ A →
     Γ ⊢ t ∷ Erased A)
¬-inversion-erased inversion-erased =
  ¬-inversion-erased′ λ ⊢erased →
  _ , inversion-erased ⊢erased
