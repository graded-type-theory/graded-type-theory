------------------------------------------------------------------------
-- Soundness of algorithmic equality.
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Conversion.Soundness
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Conversion R
open import Definition.Conversion.Whnf R
open import Definition.Typed.Consequences.DerivedRules R
open import Definition.Typed.Consequences.InverseUniv R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Consequences.NeTypeEq R

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n

mutual
  -- Algorithmic equality of neutrals is well-formed.
  soundness~↑ : ∀ {k l A} → Γ ⊢ k ~ l ↑ A → Γ ⊢ k ≡ l ∷ A
  soundness~↑ (var-refl x x≡y) = PE.subst (λ y → _ ⊢ _ ≡ var y ∷ _) x≡y (refl x)
  soundness~↑ (app-cong k~l x₁) =
    app-cong (soundness~↓ k~l) (soundnessConv↑Term x₁)
  soundness~↑ (fst-cong x) =
    let p≡ = soundness~↓ x
        ⊢ΣFG = proj₁ (syntacticEqTerm p≡)
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG
    in  fst-cong ⊢F ⊢G p≡
  soundness~↑ (snd-cong x) =
    let p≡ = soundness~↓ x
        ⊢ΣFG = proj₁ (syntacticEqTerm p≡)
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG
    in  snd-cong ⊢F ⊢G p≡
  soundness~↑ (natrec-cong x₁ x₂ x₃ k~l) =
    let F≡G = soundnessConv↑ x₁
        ⊢F = proj₁ (syntacticEq F≡G)
    in  natrec-cong ⊢F F≡G (soundnessConv↑Term x₂)
                    (soundnessConv↑Term x₃) (soundness~↓ k~l)
  soundness~↑ (prodrec-cong x x₁ x₂) =
    let C≡E = soundnessConv↑ x
        g≡h = soundness~↓ x₁
        u≡v = soundnessConv↑Term x₂
        ⊢F , ⊢G , ok = inversion-ΠΣ (proj₁ (syntacticEqTerm g≡h))
    in  prodrec-cong ⊢F ⊢G C≡E g≡h u≡v ok
  soundness~↑ (emptyrec-cong x₁ k~l) =
    emptyrec-cong (soundnessConv↑ x₁) (soundness~↓ k~l)
  soundness~↑ (J-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁~w₂ ≡Id) =
    case soundnessConv↑ A₁≡A₂ of λ {
      A₁≡A₂ →
    case soundnessConv↑Term t₁≡t₂ of λ {
      t₁≡t₂ →
    J-cong (syntacticEq A₁≡A₂ .proj₁) A₁≡A₂
      (syntacticEqTerm t₁≡t₂ .proj₂ .proj₁) t₁≡t₂ (soundnessConv↑ B₁≡B₂)
      (soundnessConv↑Term u₁≡u₂) (soundnessConv↑Term v₁≡v₂)
      (conv (soundness~↓ w₁~w₂) ≡Id) }}
  soundness~↑ (K-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁~v₂ ≡Id ok) =
    case soundnessConv↑Term t₁≡t₂ of λ {
      t₁≡t₂ →
    K-cong (soundnessConv↑ A₁≡A₂) (syntacticEqTerm t₁≡t₂ .proj₂ .proj₁)
      t₁≡t₂ (soundnessConv↑ B₁≡B₂) (soundnessConv↑Term u₁≡u₂)
      (conv (soundness~↓ v₁~v₂) ≡Id) ok }
  soundness~↑ ([]-cong-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁~v₂ ≡Id ok) =
    []-cong-cong (soundnessConv↑ A₁≡A₂) (soundnessConv↑Term t₁≡t₂)
      (soundnessConv↑Term u₁≡u₂) (conv (soundness~↓ v₁~v₂) ≡Id) ok

  -- Algorithmic equality of neutrals in WHNF is well-formed.
  soundness~↓ : ∀ {k l A} → Γ ⊢ k ~ l ↓ A → Γ ⊢ k ≡ l ∷ A
  soundness~↓ ([~] A₁ D whnfA k~l) = conv (soundness~↑ k~l) (subset* D)

  -- Algorithmic equality of types is well-formed.
  soundnessConv↑ : ∀ {A B} → Γ ⊢ A [conv↑] B → Γ ⊢ A ≡ B
  soundnessConv↑ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) =
    trans (subset* D) (trans (soundnessConv↓ A′<>B′) (sym (subset* D′)))

  -- Algorithmic equality of types in WHNF is well-formed.
  soundnessConv↓ : ∀ {A B} → Γ ⊢ A [conv↓] B → Γ ⊢ A ≡ B
  soundnessConv↓ (U-refl ⊢Γ) = refl (Uⱼ ⊢Γ)
  soundnessConv↓ (ℕ-refl ⊢Γ) = refl (ℕⱼ ⊢Γ)
  soundnessConv↓ (Empty-refl ⊢Γ) = refl (Emptyⱼ ⊢Γ)
  soundnessConv↓ (Unit-refl ⊢Γ ok) = refl (Unitⱼ ⊢Γ ok)
  soundnessConv↓ (ne x) = univ (soundness~↓ x)
  soundnessConv↓ (ΠΣ-cong F c c₁ ok) =
    ΠΣ-cong F (soundnessConv↑ c) (soundnessConv↑ c₁) ok
  soundnessConv↓ (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    Id-cong (soundnessConv↑ A₁≡A₂) (soundnessConv↑Term t₁≡t₂)
      (soundnessConv↑Term u₁≡u₂)

  -- Algorithmic equality of terms is well-formed.
  soundnessConv↑Term : ∀ {a b A} → Γ ⊢ a [conv↑] b ∷ A → Γ ⊢ a ≡ b ∷ A
  soundnessConv↑Term ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) =
    conv (trans (subset*Term d)
                (trans (soundnessConv↓Term t<>u)
                       (sym (subset*Term d′))))
         (sym (subset* D))

  -- Algorithmic equality of terms in WHNF is well-formed.
  soundnessConv↓Term : ∀ {a b A} → Γ ⊢ a [conv↓] b ∷ A → Γ ⊢ a ≡ b ∷ A
  soundnessConv↓Term (ℕ-ins x) = soundness~↓ x
  soundnessConv↓Term (Empty-ins x) = soundness~↓ x
  soundnessConv↓Term (Unit-ins x) = soundness~↓ x
  soundnessConv↓Term (Σᵣ-ins x x₁ x₂) =
    let a≡b = soundness~↓ x₂
        _ , neA , _ = ne~↓ x₂
        _ , ⊢a , _ = syntacticEqTerm a≡b
        Σ≡Σ′ = neTypeEq neA x ⊢a
    in  conv a≡b (sym Σ≡Σ′)
  soundnessConv↓Term (ne-ins t u x x₁) =
    let _ , neA , _ = ne~↓ x₁
        _ , t∷M , _ = syntacticEqTerm (soundness~↓ x₁)
        M≡A = neTypeEq neA t∷M t
    in  conv (soundness~↓ x₁) M≡A
  soundnessConv↓Term (univ x x₁ x₂) = inverseUnivEq x (soundnessConv↓ x₂)
  soundnessConv↓Term (zero-refl ⊢Γ) = refl (zeroⱼ ⊢Γ)
  soundnessConv↓Term (suc-cong c) = suc-cong (soundnessConv↑Term c)
  soundnessConv↓Term (prod-cong x x₁ x₂ x₃ ok) =
    prod-cong x x₁ (soundnessConv↑Term x₂) (soundnessConv↑Term x₃) ok
  soundnessConv↓Term (η-eq x x₁ y y₁ c) =
    let ⊢ΠFG = syntacticTerm x
        ⊢F , _ = syntacticΠ ⊢ΠFG
    in  η-eq ⊢F x x₁ (soundnessConv↑Term c)
  soundnessConv↓Term (Σ-η ⊢p ⊢r pProd rProd fstConv sndConv) =
    let ⊢ΣFG = syntacticTerm ⊢p
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG
        fst≡ = soundnessConv↑Term fstConv
        snd≡ = soundnessConv↑Term sndConv
    in  Σ-η ⊢F ⊢G ⊢p ⊢r fst≡ snd≡
  soundnessConv↓Term (η-unit [a] [b] aUnit bUnit) = η-unit [a] [b]
  soundnessConv↓Term
    {Γ} (Id-ins {v₁} {t} {u} {A} {A′} {t′} {u′} ⊢v₁ v₁~v₂) =
    case soundness~↓ v₁~v₂ of λ {
      v₁≡v₂ →
    conv v₁≡v₂
      (                                          $⟨ syntacticEqTerm v₁≡v₂ .proj₂ .proj₁ , ⊢v₁ ⟩
       Γ ⊢ v₁ ∷ Id A′ t′ u′ × Γ ⊢ v₁ ∷ Id A t u  →⟨ uncurry (neTypeEq (ne~↓ v₁~v₂ .proj₂ .proj₁)) ⟩
       Γ ⊢ Id A′ t′ u′ ≡ Id A t u                □) }
  soundnessConv↓Term (rfl-refl t≡u) =
    refl (rflⱼ′ t≡u)
