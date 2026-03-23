------------------------------------------------------------------------
-- Stability of algorithmic equality (in the absence of equality
-- reflection)
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Conversion.Stability
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  ⦃ no-equality-reflection : No-equality-reflection ⦄
  where

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Stability R
import Definition.Typed.Weakening R as W
open import Definition.Typed.Well-formed R
open import Definition.Conversion R
open import Definition.Conversion.Level R
open import Definition.Conversion.Soundness R

open import Tools.Bool
open import Tools.Function
open import Tools.List hiding (_∷_)
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    m n : Nat
    ∇ : DCon (Term 0) m
    Γ Δ : Con Term n
    l₁ l₂ : Lvl _
    d : Bool

mutual
  -- Stability of algorithmic equality of neutrals.
  stability~↑ : ∀ {k l A}
              → ∇ »⊢ Γ ≡ Δ
              → ∇ » Γ ⊢ k ~ l ↑ A
              → ∇ » Δ ⊢ k ~ l ↑ A
  stability~↑ Γ≡Δ (var-refl x x≡y) =
    var-refl (stability Γ≡Δ x) x≡y
  stability~↑ Γ≡Δ (defn-refl α α↦⊘ α≡β) =
    defn-refl (stability Γ≡Δ α) α↦⊘ α≡β
  stability~↑ Γ≡Δ (lower-cong x) =
    lower-cong (stability~↓ Γ≡Δ x)
  stability~↑ Γ≡Δ (app-cong k~l x) =
    app-cong (stability~↓ Γ≡Δ k~l) (stabilityConv↑Term Γ≡Δ x)
  stability~↑ Γ≡Δ (fst-cong p~r) =
    fst-cong (stability~↓ Γ≡Δ p~r)
  stability~↑ Γ≡Δ (snd-cong p~r) =
    snd-cong (stability~↓ Γ≡Δ p~r)
  stability~↑ Γ≡Δ (natrec-cong x₁ x₂ x₃ k~l) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        ⊢F = proj₁ (wf-⊢ (soundnessConv↑ x₁))
    in natrec-cong
         (stabilityConv↑ (Γ≡Δ ∙ (refl (⊢ℕ ⊢Γ))) x₁)
         (stabilityConv↑Term Γ≡Δ x₂)
         (stabilityConv↑Term (Γ≡Δ ∙ refl (⊢ℕ ⊢Γ) ∙ refl ⊢F) x₃)
         (stability~↓ Γ≡Δ k~l)
  stability~↑ Γ≡Δ (prodrec-cong x x₁ x₂) =
    let ⊢Σ , _ = wf-⊢ (soundness~↓ x₁)
        ⊢F , ⊢G , _ = inversion-ΠΣ ⊢Σ
    in  prodrec-cong (stabilityConv↑ (Γ≡Δ ∙ refl ⊢Σ) x)
          (stability~↓ Γ≡Δ x₁)
          (stabilityConv↑Term (Γ≡Δ ∙ refl ⊢F ∙ refl ⊢G) x₂)
  stability~↑ Γ≡Δ (emptyrec-cong x₁ k~l) =
    emptyrec-cong (stabilityConv↑ Γ≡Δ x₁)
                  (stability~↓ Γ≡Δ k~l)
  stability~↑ Γ≡Δ (unitrec-cong x x₁ x₂ no-η) =
    let k≡l = soundness~↓ x₁
        ⊢Unit = proj₁ (wf-⊢ k≡l)
    in  unitrec-cong (stabilityConv↑ (Γ≡Δ ∙ refl ⊢Unit) x)
          (stability~↓ Γ≡Δ x₁) (stabilityConv↑Term Γ≡Δ x₂) no-η
  stability~↑ Γ≡Δ (J-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁~w₂ ≡Id) =
    case wf-⊢ (soundnessConv↑ A₁≡A₂) .proj₁ of λ {
      ⊢A₁ →
    case wf-⊢ (soundnessConv↑Term t₁≡t₂) .proj₂ .proj₁ of λ {
      ⊢t₁ →
    J-cong (stabilityConv↑ Γ≡Δ A₁≡A₂) (stabilityConv↑Term Γ≡Δ t₁≡t₂)
      (stabilityConv↑
         (Γ≡Δ ∙ refl ⊢A₁ ∙ refl (Idⱼ′ (W.wk₁ ⊢A₁ ⊢t₁) (var₀ ⊢A₁)))
         B₁≡B₂)
      (stabilityConv↑Term Γ≡Δ u₁≡u₂) (stabilityConv↑Term Γ≡Δ v₁≡v₂)
      (stability~↓ Γ≡Δ w₁~w₂) (stability Γ≡Δ ≡Id) }}
  stability~↑ Γ≡Δ (K-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁~v₂ ≡Id ok) =
    case wf-⊢ (soundnessConv↑Term t₁≡t₂) .proj₂ .proj₁ of λ {
      ⊢t₁ →
    K-cong (stabilityConv↑ Γ≡Δ A₁≡A₂) (stabilityConv↑Term Γ≡Δ t₁≡t₂)
      (stabilityConv↑ (Γ≡Δ ∙ refl (Idⱼ′ ⊢t₁ ⊢t₁)) B₁≡B₂)
      (stabilityConv↑Term Γ≡Δ u₁≡u₂) (stability~↓ Γ≡Δ v₁~v₂)
      (stability Γ≡Δ ≡Id) ok }
  stability~↑ Γ≡Δ ([]-cong-cong l₁≡l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁~v₂ ≡Id ok) =
    []-cong-cong (stabilityConv↑Level Γ≡Δ l₁≡l₂)
      (stabilityConv↑ Γ≡Δ A₁≡A₂) (stabilityConv↑Term Γ≡Δ t₁≡t₂)
      (stabilityConv↑Term Γ≡Δ u₁≡u₂) (stability~↓ Γ≡Δ v₁~v₂)
      (stability Γ≡Δ ≡Id) ok

  -- Stability of algorithmic equality of neutrals of types in WHNF.
  stability~↓ : ∀ {k l A}
              → ∇ »⊢ Γ ≡ Δ
              → ∇ » Γ ⊢ k ~ l ↓ A
              → ∇ » Δ ⊢ k ~ l ↓ A
  stability~↓ Γ≡Δ ([~] A (D , whnfA) k~l) =
    [~] A (stabilityRed* Γ≡Δ D , whnfA) (stability~↑ Γ≡Δ k~l)

  stability~∷ : ∀ {k l A}
              → ∇ »⊢ Γ ≡ Δ
              → ∇ » Γ ⊢ k ~ l ∷ A
              → ∇ » Δ ⊢ k ~ l ∷ A
  stability~∷ Γ≡Δ (↑ A≡B k~l) =
    ↑ (stability Γ≡Δ A≡B) (stability~↑ Γ≡Δ k~l)

  -- Stability of algorithmic equality of types.
  stabilityConv↑ : ∀ {A B}
                 → ∇ »⊢ Γ ≡ Δ
                 → ∇ » Γ ⊢ A [conv↑] B
                 → ∇ » Δ ⊢ A [conv↑] B
  stabilityConv↑ Γ≡Δ ([↑] A′ B′ D D′ A′<>B′) =
    [↑] A′ B′ (stabilityRed↘ Γ≡Δ D) (stabilityRed↘ Γ≡Δ D′)
        (stabilityConv↓ Γ≡Δ A′<>B′)

  -- Stability of algorithmic equality of types in WHNF.
  stabilityConv↓ : ∀ {A B}
                 → ∇ »⊢ Γ ≡ Δ
                 → ∇ » Γ ⊢ A [conv↓] B
                 → ∇ » Δ ⊢ A [conv↓] B
  stabilityConv↓ Γ≡Δ (Level-refl ok _) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ in
    Level-refl ok ⊢Δ
  stabilityConv↓ Γ≡Δ (U-cong l₁≡l₂) =
    U-cong (stabilityConv↑Level Γ≡Δ l₁≡l₂)
  stabilityConv↓ Γ≡Δ (Lift-cong l₁≡l₂ F≡H) =
    Lift-cong (stabilityConv↑Level Γ≡Δ l₁≡l₂) (stabilityConv↑ Γ≡Δ F≡H)
  stabilityConv↓ Γ≡Δ (ℕ-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  ℕ-refl ⊢Δ
  stabilityConv↓ Γ≡Δ (Empty-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  Empty-refl ⊢Δ
  stabilityConv↓ Γ≡Δ (Unit-refl x ok) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in Unit-refl ⊢Δ ok
  stabilityConv↓ Γ≡Δ (ne x) =
    ne (stability~↓ Γ≡Δ x)
  stabilityConv↓ Γ≡Δ (ΠΣ-cong A<>B A<>B₁ ok) =
    ΠΣ-cong (stabilityConv↑ Γ≡Δ A<>B)
      (stabilityConv↑
         (Γ≡Δ ∙ refl (wf-⊢ (soundnessConv↑ A<>B) .proj₁)) A<>B₁)
      ok
  stabilityConv↓ Γ≡Δ (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    Id-cong (stabilityConv↑ Γ≡Δ A₁≡A₂) (stabilityConv↑Term Γ≡Δ t₁≡t₂)
      (stabilityConv↑Term Γ≡Δ u₁≡u₂)

  -- Stability of algorithmic equality of terms.
  stabilityConv↑Term : ∀ {t u A}
                     → ∇ »⊢ Γ ≡ Δ
                     → ∇ » Γ ⊢ t [conv↑] u ∷ A
                     → ∇ » Δ ⊢ t [conv↑] u ∷ A
  stabilityConv↑Term Γ≡Δ ([↑]ₜ B t′ u′ D d d′ t<>u) =
    [↑]ₜ B t′ u′ (stabilityRed↘ Γ≡Δ D) (stabilityRed↘Term Γ≡Δ d)
                 (stabilityRed↘Term Γ≡Δ d′)
                 (stabilityConv↓Term Γ≡Δ t<>u)

  -- Stability for _⊢_[conv↑]_∷Level.
  stabilityConv↑Level :
    ∇ »⊢ Γ ≡ Δ →
    ∇ » Γ ⊢ l₁ [conv↑] l₂ ∷Level →
    ∇ » Δ ⊢ l₁ [conv↑] l₂ ∷Level
  stabilityConv↑Level Γ≡Δ (term ok l₁≡l₂) =
    term ok (stabilityConv↑Term Γ≡Δ l₁≡l₂)
  stabilityConv↑Level Γ≡Δ (literal! ok _) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ in
    literal! ok ⊢Δ

  -- Stability of algorithmic equality of terms in WHNF.
  stabilityConv↓Term : ∀ {t u A}
                     → ∇ »⊢ Γ ≡ Δ
                     → ∇ » Γ ⊢ t [conv↓] u ∷ A
                     → ∇ » Δ ⊢ t [conv↓] u ∷ A
  stabilityConv↓Term Γ≡Δ (Level-ins x) =
    Level-ins (stabilityConv↓Level Γ≡Δ x)
  stabilityConv↓Term Γ≡Δ (ℕ-ins x) =
    ℕ-ins (stability~↓ Γ≡Δ x)
  stabilityConv↓Term Γ≡Δ (Empty-ins x) =
    Empty-ins (stability~↓ Γ≡Δ x)
  stabilityConv↓Term Γ≡Δ (Unitʷ-ins ok t~u) =
    Unitʷ-ins ok (stability~↓ Γ≡Δ t~u)
  stabilityConv↓Term Γ≡Δ (Σʷ-ins x x₁ x₂) =
    Σʷ-ins (stability Γ≡Δ x) (stability Γ≡Δ x₁) (stability~↓ Γ≡Δ x₂)
  stabilityConv↓Term Γ≡Δ (ne-ins t u neN x) =
    ne-ins (stability Γ≡Δ t) (stability Γ≡Δ u) neN (stability~↓ Γ≡Δ x)
  stabilityConv↓Term Γ≡Δ (univ x x₁ x₂) =
    univ (stability Γ≡Δ x) (stability Γ≡Δ x₁) (stabilityConv↓ Γ≡Δ x₂)
  stabilityConv↓Term Γ≡Δ (Lift-η ⊢t₁ ⊢t₂ w₁ w₂ lower≡lower) =
    Lift-η (stability Γ≡Δ ⊢t₁) (stability Γ≡Δ ⊢t₂) w₁ w₂ (stabilityConv↑Term Γ≡Δ lower≡lower)
  stabilityConv↓Term Γ≡Δ (zero-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  zero-refl ⊢Δ
  stabilityConv↓Term Γ≡Δ (starʷ-refl y ok no-η) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  starʷ-refl ⊢Δ ok no-η
  stabilityConv↓Term Γ≡Δ (suc-cong t<>u) = suc-cong (stabilityConv↑Term Γ≡Δ t<>u)
  stabilityConv↓Term Γ≡Δ (prod-cong x₁ x₂ x₃ ok) =
    prod-cong (stability (Γ≡Δ ∙ refl (⊢∙→⊢ (wf x₁))) x₁)
      (stabilityConv↑Term Γ≡Δ x₂) (stabilityConv↑Term Γ≡Δ x₃) ok
  stabilityConv↓Term Γ≡Δ (η-eq x x₁ y y₁ t<>u) =
    let ⊢F , ⊢G , _ = inversion-ΠΣ (wf-⊢ x)
    in  η-eq (stability Γ≡Δ x) (stability Γ≡Δ x₁)
             y y₁ (stabilityConv↑Term (Γ≡Δ ∙ (refl ⊢F)) t<>u)
  stabilityConv↓Term Γ≡Δ (Σ-η ⊢p ⊢r pProd rProd fstConv sndConv) =
    Σ-η (stability Γ≡Δ ⊢p) (stability Γ≡Δ ⊢r)
        pProd rProd
        (stabilityConv↑Term Γ≡Δ fstConv) (stabilityConv↑Term Γ≡Δ sndConv)
  stabilityConv↓Term Γ≡Δ (η-unit [t] [u] tUnit uUnit η) =
    let [t] = stability Γ≡Δ [t]
        [u] = stability Γ≡Δ [u]
    in  η-unit [t] [u] tUnit uUnit η
  stabilityConv↓Term Γ≡Δ (Id-ins ⊢v₁ v₁~v₂) =
    Id-ins (stability Γ≡Δ ⊢v₁) (stability~↓ Γ≡Δ v₁~v₂)
  stabilityConv↓Term Γ≡Δ (rfl-refl t≡u) =
    rfl-refl (stability Γ≡Δ t≡u)

  -- Stability of algorithmic equality of levels.

  stabilityConv↓Level : ∀ {t u}
                     → ∇ »⊢ Γ ≡ Δ
                     → ∇ » Γ ⊢ t [conv↓] u ∷Level
                     → ∇ » Δ ⊢ t [conv↓] u ∷Level
  stabilityConv↓Level Γ≡Δ ([↓]ˡ tᵛ uᵛ t≡ u≡ t≡u) =
    [↓]ˡ (stabilityLevelᵛ Γ≡Δ tᵛ) (stabilityLevelᵛ Γ≡Δ uᵛ)
      (stability-↓ᵛ Γ≡Δ t≡)
      (stability-↓ᵛ Γ≡Δ u≡)
      (stability-≡ᵛ Γ≡Δ tᵛ uᵛ t≡u)

  stabilityLevelAtom :
    ∇ »⊢ Γ ≡ Δ → LevelAtom (∇ » Γ) → LevelAtom (∇ » Δ)
  stabilityLevelAtom Γ≡Δ zeroᵘ = zeroᵘ
  stabilityLevelAtom Γ≡Δ (ne x) = ne (stability~↓ Γ≡Δ x)

  stabilityLevel⁺ : ∇ »⊢ Γ ≡ Δ → Level⁺ (∇ » Γ) → Level⁺ (∇ » Δ)
  stabilityLevel⁺ Γ≡Δ (n , l) = n , stabilityLevelAtom Γ≡Δ l

  stabilityLevelᵛ : ∇ »⊢ Γ ≡ Δ → Levelᵛ (∇ » Γ) → Levelᵛ (∇ » Δ)
  stabilityLevelᵛ Γ≡Δ L.[] = L.[]
  stabilityLevelᵛ Γ≡Δ (x L.∷ xs) = stabilityLevel⁺ Γ≡Δ x L.∷ stabilityLevelᵛ Γ≡Δ xs

  stabilityLevelAtom→Term :
    (Γ≡Δ : ∇ »⊢ Γ ≡ Δ) (t : LevelAtom (∇ » Γ)) →
    LevelAtom→Term (stabilityLevelAtom Γ≡Δ t) PE.≡ LevelAtom→Term t
  stabilityLevelAtom→Term Γ≡Δ zeroᵘ = PE.refl
  stabilityLevelAtom→Term Γ≡Δ (ne x) = PE.refl

  stabilityLevel⁺→Term :
    (Γ≡Δ : ∇ »⊢ Γ ≡ Δ) (t : Level⁺ (∇ » Γ)) →
    Level⁺→Term (stabilityLevel⁺ Γ≡Δ t) PE.≡ Level⁺→Term t
  stabilityLevel⁺→Term Γ≡Δ (n , a) =
    PE.cong (1ᵘ+ⁿ n) (stabilityLevelAtom→Term Γ≡Δ a)

  stabilityLevelᵛ→Term :
    ∀ {t} (Γ≡Δ : ∇ »⊢ Γ ≡ Δ) →
    Levelᵛ→Term (stabilityLevelᵛ Γ≡Δ t) PE.≡ Levelᵛ→Term t
  stabilityLevelᵛ→Term {t = L.[]} Γ≡Δ = PE.refl
  stabilityLevelᵛ→Term {t = x L.∷ t} Γ≡Δ = PE.cong₂ _supᵘ_ (stabilityLevel⁺→Term Γ≡Δ x) (stabilityLevelᵛ→Term Γ≡Δ)

  stability-≡ⁿ :
    (Γ≡Δ : ∇ »⊢ Γ ≡ Δ) {t u : Term n} →
    ≡ⁿ (∇ » Γ) t u d → ≡ⁿ (∇ » Δ) t u d
  stability-≡ⁿ Γ≡Δ (ne≡ x) = ne≡ (stability~↓ Γ≡Δ x)
  stability-≡ⁿ Γ≡Δ (ne≡' x) = ne≡' (stability~↓ Γ≡Δ x)

  stability-≤⁺ :
    (Γ≡Δ : ∇ »⊢ Γ ≡ Δ) (t u : Level⁺ (∇ » Γ)) →
    ≤⁺ d t u → ≤⁺ d (stabilityLevel⁺ Γ≡Δ t) (stabilityLevel⁺ Γ≡Δ u)
  stability-≤⁺ Γ≡Δ t u (x , zeroᵘ≤) = x , zeroᵘ≤
  stability-≤⁺ Γ≡Δ t u (x , ne≤ y) = x , ne≤ (stability-≡ⁿ Γ≡Δ y)

  stability-≤⁺ᵛ :
    (Γ≡Δ : ∇ »⊢ Γ ≡ Δ) (t : Level⁺ (∇ » Γ)) (u : Levelᵛ (∇ » Γ)) →
    ≤⁺ᵛ d t u → ≤⁺ᵛ d (stabilityLevel⁺ Γ≡Δ t) (stabilityLevelᵛ Γ≡Δ u)
  stability-≤⁺ᵛ Γ≡Δ t u (Any.here px) = Any.here (stability-≤⁺ Γ≡Δ _ _ px)
  stability-≤⁺ᵛ Γ≡Δ t u (Any.there t≤u) = Any.there (stability-≤⁺ᵛ Γ≡Δ _ _ t≤u)

  stability-≤ᵛ :
    (Γ≡Δ : ∇ »⊢ Γ ≡ Δ) (t u : Levelᵛ (∇ » Γ)) →
    ≤ᵛ d t u → ≤ᵛ d (stabilityLevelᵛ Γ≡Δ t) (stabilityLevelᵛ Γ≡Δ u)
  stability-≤ᵛ Γ≡Δ t u All.[] = All.[]
  stability-≤ᵛ Γ≡Δ t u (px All.∷ t≤u) = stability-≤⁺ᵛ Γ≡Δ _ _ px All.∷ stability-≤ᵛ Γ≡Δ _ _ t≤u

  stability-≡ᵛ :
    (Γ≡Δ : ∇ »⊢ Γ ≡ Δ) (t u : Levelᵛ (∇ » Γ)) →
    t ≡ᵛ u → stabilityLevelᵛ Γ≡Δ t ≡ᵛ stabilityLevelᵛ Γ≡Δ u
  stability-≡ᵛ Γ≡Δ t u (t≤u , u≤t) = stability-≤ᵛ Γ≡Δ t u t≤u , stability-≤ᵛ Γ≡Δ u t u≤t

  stability-sucᵛ :
    (Γ≡Δ : ∇ »⊢ Γ ≡ Δ) (v v′ : Levelᵛ (∇ » Γ)) → v PE.≡ sucᵛ v′ →
    stabilityLevelᵛ Γ≡Δ v PE.≡ sucᵛ (stabilityLevelᵛ Γ≡Δ v′)
  stability-sucᵛ Γ≡Δ v v′ PE.refl = PE.cong (_ L.∷_) (stability-map-suc⁺ Γ≡Δ _ _ PE.refl)

  stability-map-suc⁺ :
    (Γ≡Δ : ∇ »⊢ Γ ≡ Δ) (v v′ : Levelᵛ (∇ » Γ)) → v PE.≡ map-suc⁺ v′ →
    stabilityLevelᵛ Γ≡Δ v PE.≡ map-suc⁺ (stabilityLevelᵛ Γ≡Δ v′)
  stability-map-suc⁺ Γ≡Δ L.[] L.[] PE.refl = PE.refl
  stability-map-suc⁺ Γ≡Δ L.[] (x L.∷ v′) ()
  stability-map-suc⁺ Γ≡Δ (x L.∷ v) L.[] ()
  stability-map-suc⁺ Γ≡Δ ((n , a) L.∷ v) ((n′ , a′) L.∷ v′) PE.refl = PE.cong (_ L.∷_) (stability-map-suc⁺ Γ≡Δ v v′ PE.refl)

  stabilityLevel⁺-cong-suc⁺ :
    (Γ≡Δ : ∇ »⊢ Γ ≡ Δ) (a b : Level⁺ (∇ » Γ)) → a PE.≡ suc⁺ b →
    stabilityLevel⁺ Γ≡Δ a PE.≡ suc⁺ (stabilityLevel⁺ Γ≡Δ b)
  stabilityLevel⁺-cong-suc⁺ Γ≡Δ a b PE.refl = PE.refl

  stabilityLevel⁺-cong :
    (Γ≡Δ : ∇ »⊢ Γ ≡ Δ) (a b : Level⁺ (∇ » Γ)) → a PE.≡ b →
    stabilityLevel⁺ Γ≡Δ a PE.≡ stabilityLevel⁺ Γ≡Δ b
  stabilityLevel⁺-cong Γ≡Δ a b PE.refl = PE.refl

  stabilityLevelᵛ-cong :
    (Γ≡Δ : ∇ »⊢ Γ ≡ Δ) (a b : Levelᵛ (∇ » Γ)) → a PE.≡ b →
    stabilityLevelᵛ Γ≡Δ a PE.≡ stabilityLevelᵛ Γ≡Δ b
  stabilityLevelᵛ-cong Γ≡Δ a b PE.refl = PE.refl

  stability-supᵛ :
    (Γ≡Δ : ∇ »⊢ Γ ≡ Δ) (v v′ v″ : Levelᵛ (∇ » Γ)) → v PE.≡ supᵛ v′ v″ →
    stabilityLevelᵛ Γ≡Δ v PE.≡
    supᵛ (stabilityLevelᵛ Γ≡Δ v′) (stabilityLevelᵛ Γ≡Δ v″)
  stability-supᵛ Γ≡Δ L.[] L.[] v″ PE.refl = PE.refl
  stability-supᵛ Γ≡Δ L.[] (x L.∷ v′) v″ ()
  stability-supᵛ Γ≡Δ (x L.∷ v) L.[] v″ PE.refl = PE.refl
  stability-supᵛ Γ≡Δ (x L.∷ v) (x₁ L.∷ v′) v″ eq =
    let a , b = L.∷-injective eq
    in PE.cong₂ L._∷_ (stabilityLevel⁺-cong Γ≡Δ x x₁ a) (stability-supᵛ Γ≡Δ _ _ v″ b)

  stability-supᵛ-map-suc⁺ :
    (Γ≡Δ : ∇ »⊢ Γ ≡ Δ) (v v′ v″ : Levelᵛ (∇ » Γ)) →
    v PE.≡ supᵛ (map-suc⁺ v′) v″ →
    stabilityLevelᵛ Γ≡Δ v PE.≡
    supᵛ (map-suc⁺ (stabilityLevelᵛ Γ≡Δ v′)) (stabilityLevelᵛ Γ≡Δ v″)
  stability-supᵛ-map-suc⁺ Γ≡Δ L.[] L.[] v″ PE.refl = PE.refl
  stability-supᵛ-map-suc⁺ Γ≡Δ L.[] (x L.∷ v′) v″ ()
  stability-supᵛ-map-suc⁺ Γ≡Δ (x L.∷ v) L.[] v″ PE.refl = PE.refl
  stability-supᵛ-map-suc⁺ Γ≡Δ (x L.∷ v) (x₁ L.∷ v′) v″ eq =
    let a , b = L.∷-injective eq
    in PE.cong₂ L._∷_ (stabilityLevel⁺-cong-suc⁺ Γ≡Δ x x₁ a) (stability-supᵛ-map-suc⁺ Γ≡Δ _ _ v″ b)

  stability-supᵛ-sucᵛ :
    (Γ≡Δ : ∇ »⊢ Γ ≡ Δ) (v v′ v″ : Levelᵛ (∇ » Γ)) →
    v PE.≡ supᵛ (sucᵛ v′) v″ →
    stabilityLevelᵛ Γ≡Δ v PE.≡
    supᵛ (sucᵛ (stabilityLevelᵛ Γ≡Δ v′)) (stabilityLevelᵛ Γ≡Δ v″)
  stability-supᵛ-sucᵛ Γ≡Δ L.[] v′ v″ ()
  stability-supᵛ-sucᵛ Γ≡Δ (x L.∷ v) v′ v″ eq =
    let a , b = L.∷-injective eq
    in PE.cong₂ L._∷_ (stabilityLevel⁺-cong Γ≡Δ x _ a) (stability-supᵛ-map-suc⁺ Γ≡Δ v v′ v″ b)

  stability-↑ᵛ
    : ∀ {t} {v : Levelᵛ (∇ » Γ)}
    → (Γ≡Δ : ∇ »⊢ Γ ≡ Δ)
    → ∇ » Γ ⊢ t ↑ᵛ v
    → ∇ » Δ ⊢ t ↑ᵛ stabilityLevelᵛ Γ≡Δ v
  stability-↑ᵛ Γ≡Δ ([↑]ᵛ d t↓v) = [↑]ᵛ (stabilityRed↘Term Γ≡Δ d) (stability-↓ᵛ Γ≡Δ t↓v)

  stability-↓ᵛ
    : ∀ {t} {v : Levelᵛ (∇ » Γ)}
    → (Γ≡Δ : ∇ »⊢ Γ ≡ Δ)
    → ∇ » Γ ⊢ t ↓ᵛ v
    → ∇ » Δ ⊢ t ↓ᵛ stabilityLevelᵛ Γ≡Δ v
  stability-↓ᵛ Γ≡Δ (zeroᵘₙ ok _) =
    zeroᵘₙ ok (contextConvSubst Γ≡Δ .proj₂ .proj₁)
  stability-↓ᵛ Γ≡Δ (sucᵘₙ x t↑) = sucᵘₙ (stability-sucᵛ Γ≡Δ _ _ x) (stability-↑ᵛ Γ≡Δ t↑)
  stability-↓ᵛ Γ≡Δ (neₙ x) = neₙ (stability-~ᵛ Γ≡Δ x)

  stability-~ᵛ
    : ∀ {t} {v : Levelᵛ (∇ » Γ)}
    → (Γ≡Δ : ∇ »⊢ Γ ≡ Δ)
    → ∇ » Γ ⊢ t ~ᵛ v
    → ∇ » Δ ⊢ t ~ᵛ stabilityLevelᵛ Γ≡Δ v
  stability-~ᵛ Γ≡Δ (supᵘˡₙ {v′} {v″} x t~ u↑) =
    supᵘˡₙ (stability-supᵛ Γ≡Δ _ v′ v″ x) (stability-~ᵛ Γ≡Δ t~) (stability-↑ᵛ Γ≡Δ u↑)
  stability-~ᵛ Γ≡Δ (supᵘʳₙ {v′} {v″} x t↑ u~) =
    supᵘʳₙ (stability-supᵛ-sucᵛ Γ≡Δ _ v′ v″ x) (stability-↑ᵛ Γ≡Δ t↑) (stability-~ᵛ Γ≡Δ u~)
  stability-~ᵛ Γ≡Δ (neₙ [t] x) =
    neₙ (stability~↓ Γ≡Δ [t]) (stabilityLevelᵛ-cong Γ≡Δ _ _ x)
