------------------------------------------------------------------------
-- Some properties related to typing and Erased
------------------------------------------------------------------------

open import Definition.Modality

module Definition.Typed.Erased
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open Modality 𝕄

open import Definition.Typed M
open import Definition.Typed.Consequences.Inequality M
open import Definition.Typed.Consequences.Injectivity M
open import Definition.Typed.Consequences.Inversion M
open import Definition.Typed.Consequences.Substitution M
open import Definition.Typed.Consequences.Syntactic M
open import Definition.Typed.Properties M

open import Definition.Untyped M as U hiding (_∷_; _[_])
open import Definition.Untyped.Erased 𝕄

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nullary
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  Γ       : Con Term _
  A B t u : Term _

------------------------------------------------------------------------
-- Typing rules

-- A formation rule for Erased.

Erasedⱼ : Γ ⊢ A → Γ ⊢ Erased A
Erasedⱼ ⊢A = ΠΣⱼ ⊢A ▹ Unitⱼ (wf ⊢A ∙ ⊢A)

-- A corresponding congruence rule.

Erased-cong :
  Γ ⊢ A ≡ B →
  Γ ⊢ Erased A ≡ Erased B
Erased-cong A≡B = ΠΣ-cong ⊢A A≡B (refl (Unitⱼ (wf ⊢A ∙ ⊢A)))
  where
  ⊢A = syntacticEq A≡B .proj₁

-- An introduction rule for U.

Erasedⱼ-U : Γ ⊢ A ∷ U → Γ ⊢ Erased A ∷ U
Erasedⱼ-U ⊢A∷U = ΠΣⱼ ⊢A∷U ▹ Unitⱼ (wf ⊢A ∙ ⊢A)
  where
  ⊢A = univ ⊢A∷U

-- A corresponding congruence rule.

Erased-cong-U :
  Γ ⊢ A ≡ B ∷ U →
  Γ ⊢ Erased A ≡ Erased B ∷ U
Erased-cong-U A≡B =
  ΠΣ-cong ⊢A A≡B (refl (Unitⱼ (wf ⊢A ∙ ⊢A)))
  where
  ⊢A = univ (syntacticEqTerm A≡B .proj₂ .proj₁)

-- An introduction rule for Erased.

[]ⱼ : Γ ⊢ t ∷ A → Γ ⊢ [ t ] ∷ Erased A
[]ⱼ ⊢t = prodⱼ ⊢A (Unitⱼ (⊢Γ ∙ ⊢A)) ⊢t (starⱼ ⊢Γ)
  where
  ⊢A = syntacticTerm ⊢t
  ⊢Γ = wf ⊢A

-- A corresponding congruence rule.

[]-cong :
  Γ ⊢ t ≡ u ∷ A → Γ ⊢ [ t ] ≡ [ u ] ∷ Erased A
[]-cong t≡u =
  prod-cong ⊢A (Unitⱼ (wf ⊢A ∙ ⊢A)) t≡u (refl (starⱼ (wf ⊢A)))
  where
  ⊢A = syntacticEqTerm t≡u .proj₁

-- An elimination rule for Erased.

erasedⱼ : Γ ⊢ t ∷ Erased A → Γ ⊢ erased t ∷ A
erasedⱼ ⊢t = fstⱼ ⊢A (Unitⱼ (wf ⊢A ∙ ⊢A)) ⊢t
  where
  ⊢A = case syntacticTerm ⊢t of λ where
    (ΠΣⱼ ⊢A ▹ _) → ⊢A
    (univ ⊢E-A)  → univ (inversion-ΠΣ ⊢E-A .proj₁)

-- A corresponding congruence rule.

erased-cong : Γ ⊢ t ≡ u ∷ Erased A → Γ ⊢ erased t ≡ erased u ∷ A
erased-cong t≡u = fst-cong ⊢A (Unitⱼ (wf ⊢A ∙ ⊢A)) t≡u
  where
  ⊢A = case syntacticEqTerm t≡u .proj₁ of λ where
    (ΠΣⱼ ⊢A ▹ _) → ⊢A
    (univ ⊢E-A)  → univ (inversion-ΠΣ ⊢E-A .proj₁)

-- A β-rule for Erased.

Erased-β :
  Γ ⊢ t ∷ A →
  Γ ⊢ erased [ t ] ≡ t ∷ A
Erased-β ⊢t = Σ-β₁ ⊢A (Unitⱼ (⊢Γ ∙ ⊢A)) ⊢t (starⱼ ⊢Γ) PE.refl
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
  Γ∙A⊢Unit = Unitⱼ (wf ⊢A ∙ ⊢A)

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
  case inversion-ΠΣ ⊢Erased of λ (⊢A , _ , B≡) →
  ⊢A , B≡

-- Another inversion lemma for Erased.

inversion-Erased : Γ ⊢ Erased A → Γ ⊢ A
inversion-Erased (ΠΣⱼ ⊢A ▹ _)   = ⊢A
inversion-Erased (univ ⊢Erased) =
  univ (inversion-Erased-∷ ⊢Erased .proj₁)

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
    λ (B , C , q , ⊢B , _ , ⊢t , ⊢star , A≡) →
  case inversion-star ⊢star of λ ≡Unit →
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
  A′ = Σₚ 𝟘 , 𝟙 ▷ ℕ ▹ natrec 𝟙 𝟙 𝟙 U Unit ℕ (var x0)

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
             (Unitⱼ ⊢Γ′∙ℕ)
             (ℕⱼ (⊢Γ′∙ℕ∙ℕ ∙ Uⱼ ⊢Γ′∙ℕ∙ℕ))
             (var ⊢Γ′∙ℕ here)))
    (zeroⱼ ε)
    (conv (starⱼ ε)
       (_⊢_≡_.sym $
        univ (natrec-zero (Uⱼ ⊢Γ′∙ℕ) (Unitⱼ ε) (ℕⱼ ⊢Γ′∙ℕ∙U))))

  ℕ≡Unit : Γ′ ⊢ ℕ ≡ Unit
  ℕ≡Unit =
    case inversion-[] ⊢[t′] of
      λ (_ , _ , _ , A′≡) →
    case Σ-injectivity A′≡ of
      λ (_ , ≡Unit , _ , _ , _) →
    trans
      (_⊢_≡_.sym $
       univ (natrec-suc (zeroⱼ ε) (Uⱼ ⊢Γ′∙ℕ) (Unitⱼ ε) (ℕⱼ ⊢Γ′∙ℕ∙U)))
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
  q , C , conv ⊢t (ΠΣ-cong ⊢B (_⊢_≡_.sym ≡B) (refl ⊢C))

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

  ⊢t′₁ : Γ′ ⊢ t′ ∷ Σ 𝟘 , 𝟙 ▷ ℕ ▹ ℕ
  ⊢t′₁ = prodⱼ (ℕⱼ ε) (ℕⱼ ⊢Γ′∙ℕ) (zeroⱼ ε) (zeroⱼ ε)

  ⊢erased-t′ : Γ′ ⊢ erased t′ ∷ A′
  ⊢erased-t′ = fstⱼ (ℕⱼ ε) (ℕⱼ ⊢Γ′∙ℕ) ⊢t′₁

  erased-t′≡zero : Γ′ ⊢ erased t′ ≡ zero ∷ A′
  erased-t′≡zero = Σ-β₁ (ℕⱼ ε) (ℕⱼ ⊢Γ′∙ℕ) (zeroⱼ ε) (zeroⱼ ε) PE.refl

  ⊢t′₂ : ∃ λ q → Γ′ ⊢ t′ ∷ Σₚ 𝟘 , q ▷ A′ ▹ Unit
  ⊢t′₂ = inversion-erased ⊢erased-t′

  ⊢snd-t′ : Γ′ ⊢ snd 𝟘 t′ ∷ Unit
  ⊢snd-t′ = sndⱼ (ℕⱼ ε) (Unitⱼ ⊢Γ′∙ℕ) (⊢t′₂ .proj₂)

  ℕ≡Unit : Γ′ ⊢ ℕ ≡ Unit
  ℕ≡Unit =
    case inversion-snd ⊢snd-t′ of
      λ (_ , _ , _ , _ , _ , ⊢t′ , Unit≡) →
    case inversion-prod ⊢t′ of
      λ (_ , _ , _ , _ , _ , ⊢zero , ⊢zero′ , Σ≡Σ) →
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
