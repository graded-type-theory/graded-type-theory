------------------------------------------------------------------------
-- Extraction of WHNF from algorithmic equality of types in WHNF.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Conversion.Whnf
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Conversion R
open import Definition.Typed.EqRelInstance R using (eqRelInstance)
open import Definition.LogicalRelation.Properties.Whnf R ⦃ eqRelInstance ⦄

open import Tools.Nat
open import Tools.Product as Σ

private
  variable
    n : Nat
    Γ : Con Term n

mutual
  -- If Γ ⊢ t ~ u ↑ A holds, then t and u are atomic neutral.
  ne~↑ : ∀ {t u A}
       → Γ ⊢ t ~ u ↑ A
       → Neutralᵃ t × Neutralᵃ u
  ne~↑ (var-refl x₁ x≡y) = varᵃ , varᵃ
  ne~↑ (lower-cong x) =
    let _ , q , w = ne~↓ x
    in lowerₙᵃ q , lowerₙᵃ w
  ne~↑ (app-cong x x₁) = let _ , q , w = ne~↓ x
                         in  ∘ₙᵃ q , ∘ₙᵃ w
  ne~↑ (fst-cong x) =
    let _ , pNe , rNe = ne~↓ x
    in  fstₙᵃ pNe , fstₙᵃ rNe
  ne~↑ (snd-cong x) =
    let _ , pNe , rNe = ne~↓ x
    in  sndₙᵃ pNe , sndₙᵃ rNe
  ne~↑ (natrec-cong x x₁ x₂ x₃) = let _ , q , w = ne~↓ x₃
                                  in  natrecₙᵃ q , natrecₙᵃ w
  ne~↑ (prodrec-cong _ g~h _) =
    let _ , gNe , hNe = ne~↓ g~h
    in  prodrecₙᵃ gNe , prodrecₙᵃ hNe
  ne~↑ (emptyrec-cong x x₁) = let _ , q , w = ne~↓ x₁
                              in emptyrecₙᵃ q , emptyrecₙᵃ w
  ne~↑ (unitrec-cong _ k~l _ no-η) =
    let _ , kNe , lNe = ne~↓ k~l
    in  unitrecₙᵃ no-η kNe , unitrecₙᵃ no-η lNe
  ne~↑ (J-cong _ _ _ _ _ w₁~w₂ _) =
    Σ.map Jₙᵃ Jₙᵃ (ne~↓ w₁~w₂ .proj₂)
  ne~↑ (K-cong _ _ _ _ v₁~v₂ _ _) =
    Σ.map Kₙᵃ Kₙᵃ (ne~↓ v₁~v₂ .proj₂)
  ne~↑ ([]-cong-cong _ _ _ _ v₁~v₂ _ _) =
    Σ.map []-congₙᵃ []-congₙᵃ (ne~↓ v₁~v₂ .proj₂)

  -- If Γ ⊢ t ~ u ↓ A holds, then t and u are atomic neutral and A is
  -- in WHNF.
  ne~↓ : ∀ {t u A}
       → Γ ⊢ t ~ u ↓ A
       → Whnf A × Neutralᵃ t × Neutralᵃ u
  ne~↓ ([~] _ (_ , whnfB) k~l) = whnfB , ne~↑ k~l

  ne~∷ : ∀ {t u A}
       → Γ ⊢ t ~ u ∷ A
       → Neutralᵃ t × Neutralᵃ u
  ne~∷ (↑ A≡B k~↑l) = ne~↑ k~↑l

-- Extraction of WHNF from algorithmic equality of types in WHNF.
whnfConv↓ : ∀ {A B}
          → Γ ⊢ A [conv↓] B
          → Whnf A × Whnf B
whnfConv↓ (Level-refl _ _) = Levelₙ , Levelₙ
whnfConv↓ (U-cong _) = Uₙ , Uₙ
whnfConv↓ (Lift-cong _ _) = Liftₙ , Liftₙ
whnfConv↓ (ℕ-refl x) = ℕₙ , ℕₙ
whnfConv↓ (Empty-refl x) = Emptyₙ , Emptyₙ
whnfConv↓ (Unit-refl _ _) = Unitₙ , Unitₙ
whnfConv↓ (ne x) = let _ , neA , neB = ne~↓ x
                   in  ne! neA , ne! neB
whnfConv↓ (ΠΣ-cong _ _ _) = ΠΣₙ , ΠΣₙ
whnfConv↓ (Id-cong _ _ _) = Idₙ , Idₙ

whnfConv~ᵛ : ∀ {t v}
           → Γ ⊢ t ~ᵛ v
           → Neutral t
whnfConv~ᵛ (supᵘˡₙ x x₁ x₂) = supᵘˡₙ (whnfConv~ᵛ x₁)
whnfConv~ᵛ (supᵘʳₙ x x₁ x₂) = supᵘʳₙ (whnfConv~ᵛ x₂)
whnfConv~ᵛ (neₙ [t] x) = ne⁻ (ne~↓ [t] .proj₂ .proj₁)

whnfConv↓ᵛ : ∀ {t v}
           → Γ ⊢ t ↓ᵛ v
           → Whnf t
whnfConv↓ᵛ (zeroᵘₙ _ _) = zeroᵘₙ
whnfConv↓ᵛ (sucᵘₙ x x₁) = sucᵘₙ
whnfConv↓ᵛ (neₙ x) = ne (whnfConv~ᵛ x)

-- Extraction of WHNF from algorithmic equality of terms in WHNF.
whnfConv↓Term : ∀ {t u A}
              → Γ ⊢ t [conv↓] u ∷ A
              → Whnf A × Whnf t × Whnf u
whnfConv↓Term (Level-ins ([↓]ˡ tᵛ uᵛ t≡ u≡ t≡u)) =
  Levelₙ , whnfConv↓ᵛ t≡ , whnfConv↓ᵛ u≡
whnfConv↓Term (ℕ-ins x) = let _ , neT , neU = ne~↓ x
                           in ℕₙ , ne! neT , ne! neU
whnfConv↓Term (Empty-ins x) = let _ , neT , neU = ne~↓ x
                              in Emptyₙ , ne! neT , ne! neU
whnfConv↓Term (Unitʷ-ins _ t~u) =
  let _ , t-ne , u-ne = ne~↓ t~u in
  Unitₙ , ne! t-ne , ne! u-ne
whnfConv↓Term (Σʷ-ins x x₁ x₂) =
  let _ , neT , neU = ne~↓ x₂
  in  ΠΣₙ , ne! neT , ne! neU
whnfConv↓Term (ne-ins t u x x₁) =
  let _ , neT , neU = ne~↓ x₁
  in ne x , ne! neT , ne! neU
whnfConv↓Term (univ x x₁ x₂) = Uₙ , whnfConv↓ x₂
whnfConv↓Term (Lift-η x x₁ w₁ w₂ x₂) = Liftₙ , w₁ , w₂
whnfConv↓Term (zero-refl x) = ℕₙ , zeroₙ , zeroₙ
whnfConv↓Term (starʷ-refl _ _ _) = Unitₙ , starₙ , starₙ
whnfConv↓Term (suc-cong x) = ℕₙ , sucₙ , sucₙ
whnfConv↓Term (prod-cong _ _ _ _) = ΠΣₙ , prodₙ , prodₙ
whnfConv↓Term (η-eq x₁ x₂ y y₁ x₃) = ΠΣₙ , functionWhnf y , functionWhnf y₁
whnfConv↓Term (Σ-η _ _ pProd rProd _ _) = ΠΣₙ , productWhnf pProd , productWhnf rProd
whnfConv↓Term (η-unit _ _ tWhnf uWhnf _ _) = Unitₙ , tWhnf , uWhnf
whnfConv↓Term (Id-ins _ v₁~v₂) =
  Idₙ , Σ.map ne! ne! (ne~↓ v₁~v₂ .proj₂)
whnfConv↓Term (rfl-refl _) =
  Idₙ , rflₙ , rflₙ
