------------------------------------------------------------------------
-- The algorithmic equality is closed under weakening (in the absence
-- of equality reflection)
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Conversion.Weakening
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  ⦃ no-equality-reflection : No-equality-reflection ⦄
  where

open import Definition.Untyped M as U hiding (wk)
open import Definition.Untyped.Erased 𝕄
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R
open import Definition.Typed.Weakening.Combined R
open import Definition.Typed.Weakening.Definition R
open import Definition.Typed.Well-formed R
open import Definition.Typed.EqRelInstance R using (eqRelInstance)
open import Definition.Conversion R
open import Definition.Conversion.Level R
open import Definition.Conversion.Soundness R
open import Definition.LogicalRelation R ⦃ eqRelInstance ⦄
import Definition.LogicalRelation.Weakening R ⦃ eqRelInstance ⦄ as W

open import Tools.Bool
open import Tools.Fin
open import Tools.Function
open import Tools.List hiding (_∷_)
open import Tools.Nat
import Tools.PropositionalEquality as PE
open import Tools.Product

private
  variable
    m n : Nat
    Γ₁ Γ₂ : Cons _ _
    A B t u : Term _
    l₁ l₂ : Lvl _
    ρ : Wk m n
    p r : M
    d : Bool

mutual
  -- Weakening of algorithmic equality of neutral terms.
  wk~↑ :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Γ₁ ⊢ t ~ u ↑ A →
    Γ₂ ⊢ U.wk ρ t ~ U.wk ρ u ↑ U.wk ρ A
  wk~↑ {ρ} [ρ] (var-refl x₁ x≡y) =
    var-refl (wk-⊢ [ρ] x₁) (PE.cong (wkVar ρ) x≡y)
  wk~↑ [ρ] (defn-refl α α↦⊘ α≡β) =
    defn-refl (wk-⊢ [ρ] α) (there*-↦⊘∈ (⊢ʷᵏ⇔ .proj₁ [ρ] .proj₁) α↦⊘) α≡β
  wk~↑ [ρ] (lower-cong x) =
    lower-cong (wk~↓ [ρ] x)
  wk~↑ ρ (app-cong {B} t~u x) =
    PE.subst (λ x → _ ⊢ _ ~ _ ↑ x) (PE.sym (wk-β B))
             (app-cong (wk~↓ ρ t~u) (wkConv↑Term ρ x))
  wk~↑ ρ (fst-cong p~r) =
    fst-cong (wk~↓ ρ p~r)
  wk~↑ ρ (snd-cong {B} p~r) =
    PE.subst (λ x → _ ⊢ _ ~ _ ↑ x)
             (PE.sym (wk-β B))
             (snd-cong (wk~↓ ρ p~r))
  wk~↑ [ρ] (natrec-cong {A₁} x x₁ x₂ t~u) =
    let ⊢Δ   = wf-⊢ʷᵏ [ρ]
        Δℕ⊢F = wk-⊢ (⊢ʷᵏlift [ρ] (⊢ℕ ⊢Δ)) (proj₁ (wf-⊢ (soundnessConv↑ x)))
    in
    PE.subst (_⊢_~_↑_ _ _ _) (PE.sym (wk-β A₁)) $
    natrec-cong (wkConv↑ (⊢ʷᵏlift [ρ] (⊢ℕ ⊢Δ)) x)
      (PE.subst (_⊢_[conv↑]_∷_ _ _ _) (wk-β A₁) $
       wkConv↑Term [ρ] x₁)
      (PE.subst (_⊢_[conv↑]_∷_ _ _ _) (wk-β-natrec _ A₁) $
       wkConv↑Term (⊢ʷᵏliftn [ρ] (∙ Δℕ⊢F)) x₂)
      (wk~↓ [ρ] t~u)
  wk~↑
    {ρ} [ρ]
    (prodrec-cong {C = C} {E} {g} {h} {u} {v} x g~h x₁) =
    let ρg~ρh = wk~↓ [ρ] g~h
        ⊢ρΣ , _ , _ = wf-⊢ (soundness~↓ ρg~ρh)
        _ , ⊢ρG , _ = inversion-ΠΣ ⊢ρΣ
        u↓v = PE.subst (_⊢_[conv↑]_∷_ _ _ _) (wk-β-prodrec ρ C)
                (wkConv↑Term (⊢ʷᵏliftn [ρ] (∙ ⊢ρG)) x₁)
    in  PE.subst  (λ x → _ ⊢ U.wk ρ (prodrec _ _ _ C g u) ~
                           U.wk ρ (prodrec _ _ _ E h v) ↑ x)
                  (PE.sym (wk-β C))
                  (prodrec-cong (wkConv↑ (⊢ʷᵏlift [ρ] ⊢ρΣ) x) ρg~ρh
                     u↓v)
  wk~↑ [ρ] (emptyrec-cong x t~u) =
    emptyrec-cong (wkConv↑ [ρ] x) (wk~↓ [ρ] t~u)
  wk~↑ [ρ] (unitrec-cong {A₁} x x₁ x₂ no-η) =
    let k~l = wk~↓ [ρ] x₁
        ⊢Unit , _ = wf-⊢ (soundness~↓ k~l)
        u↑v = PE.subst (_⊢_[conv↑]_∷_ _ _ _)
                       (wk-β A₁)
                       (wkConv↑Term [ρ] x₂)
    in  PE.subst (_⊢_~_↑_ _ _ _)
                 (PE.sym (wk-β A₁))
                 (unitrec-cong (wkConv↑ (⊢ʷᵏlift [ρ] ⊢Unit) x) k~l u↑v
                    no-η)
  wk~↑
    {ρ} [ρ]
    (J-cong {A₁} {B₁} {B₂} A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁~w₂ ≡Id) =
    case wf-⊢ (soundnessConv↑ A₁≡A₂) .proj₁ of λ {
      ⊢A₁ →
    case wf-⊢ (soundnessConv↑Term t₁≡t₂) .proj₂ .proj₁ of λ {
      ⊢t₁ →
    case wk-⊢ [ρ] ⊢A₁ of λ {
      ⊢wk-ρ-A₁ →
    PE.subst (_ ⊢ J _ _ _ _ _ _ _ _ ~ _ ↑_)
      (PE.sym $ wk-β-doubleSubst _ B₁ _ _) $
    J-cong (wkConv↑ [ρ] A₁≡A₂) (wkConv↑Term [ρ] t₁≡t₂)
      (PE.subst₃ _⊢_[conv↑]_
         (PE.cong₂ _»_ PE.refl $
          PE.cong (_∙_ _) $
          PE.cong₂ (λ A t → Id A t (var x0))
            (PE.sym $ wk1-wk≡lift-wk1 _ _)
            (PE.sym $ wk1-wk≡lift-wk1 _ _))
         PE.refl PE.refl $
       wkConv↑
         (⊢ʷᵏliftn [ρ] $ ∙_ $
          Idⱼ′
            (PE.subst₂ (_⊢_∷_ _)
               (PE.sym $ lift-wk1 _ _)
               (PE.sym $ lift-wk1 _ _) $
             wk-⊢ (⊢ʷᵏstepn [ρ] (∙ ⊢wk-ρ-A₁)) ⊢t₁)
            (PE.subst (_⊢_∷_ _ _) (wk1-wk≡lift-wk1 _ _) $
             var (∙ ⊢wk-ρ-A₁) here))
         B₁≡B₂)
      (PE.subst (_⊢_[conv↑]_∷_ _ _ _) (wk-β-doubleSubst _ B₁ _ _) $
       wkConv↑Term [ρ] u₁≡u₂)
      (wkConv↑Term [ρ] v₁≡v₂) (wk~↓ [ρ] w₁~w₂)
      (wk-⊢ [ρ] ≡Id) }}}
  wk~↑ [ρ] (K-cong {B₁} A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁~v₂ ≡Id ok) =
    case wf-⊢ (soundnessConv↑Term t₁≡t₂) .proj₂ .proj₁ of λ {
      ⊢t₁ →
    PE.subst (_ ⊢ K _ _ _ _ _ _ ~ _ ↑_)
      (PE.sym $ wk-β B₁) $
    K-cong (wkConv↑ [ρ] A₁≡A₂) (wkConv↑Term [ρ] t₁≡t₂)
      (wkConv↑ (⊢ʷᵏlift [ρ] (wk-⊢ [ρ] (Idⱼ′ ⊢t₁ ⊢t₁))) B₁≡B₂)
      (PE.subst (_⊢_[conv↑]_∷_ _ _ _) (wk-β B₁) $
       wkConv↑Term [ρ] u₁≡u₂)
      (wk~↓ [ρ] v₁~v₂) (wk-⊢ [ρ] ≡Id) ok }
  wk~↑ [ρ] ([]-cong-cong l₁≡l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁~v₂ ≡Id ok) =
    PE.subst (_⊢_~_↑_ _ _ _) (wk-Id-Erased _) $
    []-cong-cong (wkConv↑Level [ρ] l₁≡l₂) (wkConv↑ [ρ] A₁≡A₂)
      (wkConv↑Term [ρ] t₁≡t₂) (wkConv↑Term [ρ] u₁≡u₂) (wk~↓ [ρ] v₁~v₂)
      (wk-⊢ [ρ] ≡Id) ok

  -- Weakening of algorithmic equality of neutral terms in WHNF.
  wk~↓ :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Γ₁ ⊢ t ~ u ↓ A →
    Γ₂ ⊢ U.wk ρ t ~ U.wk ρ u ↓ U.wk ρ A
  wk~↓ {ρ} [ρ] ([~] A₁ D k~l) =
    [~] (U.wk ρ A₁) (wk-↘ [ρ] D) (wk~↑ [ρ] k~l)

  wk~∷ :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Γ₁ ⊢ t ~ u ∷ A →
    Γ₂ ⊢ U.wk ρ t ~ U.wk ρ u ∷ U.wk ρ A
  wk~∷ [ρ] (↑ A≡B t~u) = ↑ (wk-⊢ [ρ] A≡B) (wk~↑ [ρ] t~u)

  -- Weakening of algorithmic equality of types.
  wkConv↑ :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Γ₁ ⊢ A [conv↑] B →
    Γ₂ ⊢ U.wk ρ A [conv↑] U.wk ρ B
  wkConv↑ {ρ} [ρ] ([↑] A′ B′ D D′ A′<>B′) =
    [↑] (U.wk ρ A′) (U.wk ρ B′) (wk-↘ [ρ] D) (wk-↘ [ρ] D′)
      (wkConv↓ [ρ] A′<>B′)

  -- Weakening of algorithmic equality of types in WHNF.
  wkConv↓ :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Γ₁ ⊢ A [conv↓] B →
    Γ₂ ⊢ U.wk ρ A [conv↓] U.wk ρ B
  wkConv↓ ρ (Level-refl ok _) = Level-refl ok (wf-⊢ʷᵏ ρ)
  wkConv↓ ρ (U-cong l₁≡l₂) = U-cong (wkConv↑Level ρ l₁≡l₂)
  wkConv↓ ρ (Lift-cong l₁≡l₂ F≡H) =
    Lift-cong (wkConv↑Level ρ l₁≡l₂) (wkConv↑ ρ F≡H)
  wkConv↓ ρ (ℕ-refl x) = ℕ-refl (wf-⊢ʷᵏ ρ)
  wkConv↓ ρ (Empty-refl x) = Empty-refl (wf-⊢ʷᵏ ρ)
  wkConv↓ ρ (Unit-refl x ok) = Unit-refl (wf-⊢ʷᵏ ρ) ok
  wkConv↓ ρ (ne x) = ne (wk~↓ ρ x)
  wkConv↓ ρ (ΠΣ-cong A<>B A<>B₁ ok) =
    let ⊢ρF = wk-⊢ ρ (wf-⊢ (soundnessConv↑ A<>B) .proj₁) in
    ΠΣ-cong (wkConv↑ ρ A<>B) (wkConv↑ (⊢ʷᵏlift ρ ⊢ρF) A<>B₁) ok
  wkConv↓ ρ (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    Id-cong (wkConv↑ ρ A₁≡A₂) (wkConv↑Term ρ t₁≡t₂)
      (wkConv↑Term ρ u₁≡u₂)

  -- Weakening of algorithmic equality of terms.
  wkConv↑Term :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Γ₁ ⊢ t [conv↑] u ∷ A →
    Γ₂ ⊢ U.wk ρ t [conv↑] U.wk ρ u ∷ U.wk ρ A
  wkConv↑Term {ρ} [ρ] ([↑]ₜ B t′ u′ D d d′ t<>u) =
    [↑]ₜ (U.wk ρ B) (U.wk ρ t′) (U.wk ρ u′)
         (wk-↘ [ρ] D) (wk-↘∷ [ρ] d) (wk-↘∷ [ρ] d′)
         (wkConv↓Term [ρ] t<>u)

  -- Weakening for _⊢_[conv↑]_∷Level.
  wkConv↑Level :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Γ₁ ⊢ l₁ [conv↑] l₂ ∷Level →
    Γ₂ ⊢ U.wk ρ l₁ [conv↑] U.wk ρ l₂ ∷Level
  wkConv↑Level ρ∷ (term ok l₁≡l₂) =
    term ok (wkConv↑Term ρ∷ l₁≡l₂)
  wkConv↑Level ρ (literal! ok _) =
    literal! (Allowed-literal-wk-⇔ .proj₂ ok) (wf-⊢ʷᵏ ρ)

  -- Weakening of algorithmic equality of terms in WHNF.
  wkConv↓Term :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Γ₁ ⊢ t [conv↓] u ∷ A →
    Γ₂ ⊢ U.wk ρ t [conv↓] U.wk ρ u ∷ U.wk ρ A
  wkConv↓Term ρ (Level-ins x) =
    Level-ins (wkConv↓Level ρ x)
  wkConv↓Term ρ (ℕ-ins x) =
    ℕ-ins (wk~↓ ρ x)
  wkConv↓Term ρ (Empty-ins x) =
    Empty-ins (wk~↓ ρ x)
  wkConv↓Term ρ (Unitʷ-ins ok t~u) =
    Unitʷ-ins ok (wk~↓ ρ t~u)
  wkConv↓Term ρ (Σʷ-ins t u x) =
    Σʷ-ins (wk-⊢ ρ t) (wk-⊢ ρ u) (wk~↓ ρ x)
  wkConv↓Term [ρ] (ne-ins t u x x₁) =
    ne-ins (wk-⊢ [ρ] t) (wk-⊢ [ρ] u) (wk-Neutral [ρ] x) (wk~↓ [ρ] x₁)
  wkConv↓Term ρ (univ x x₁ x₂) =
    univ (wk-⊢ ρ x) (wk-⊢ ρ x₁) (wkConv↓ ρ x₂)
  wkConv↓Term [ρ] (Lift-η ⊢t ⊢u wt wu lower≡lower) =
    Lift-η (wk-⊢ [ρ] ⊢t) (wk-⊢ [ρ] ⊢u) (wk-Whnf [ρ] wt) (wk-Whnf [ρ] wu)
      (wkConv↑Term [ρ] lower≡lower)
  wkConv↓Term ρ (zero-refl x) = zero-refl (wf-⊢ʷᵏ ρ)
  wkConv↓Term ρ (starʷ-refl y ok no-η) =
    starʷ-refl (wf-⊢ʷᵏ ρ) ok no-η
  wkConv↓Term ρ (suc-cong t<>u) = suc-cong (wkConv↑Term ρ t<>u)
  wkConv↓Term ρ (prod-cong {G = G} x₁ x₂ x₃ ok) =
    let ⊢ρF = wk-⊢ ρ (⊢∙→⊢ (wf x₁))
        ⊢ρG = wk-⊢ (⊢ʷᵏlift ρ ⊢ρF) x₁
    in  prod-cong ⊢ρG (wkConv↑Term ρ x₂)
          (PE.subst (λ x → _ ⊢ _ [conv↑] _ ∷ x) (wk-β G)
             (wkConv↑Term ρ x₃))
          ok
  wkConv↓Term [ρ] (η-eq x₁ x₂ y y₁ t<>u) =
    let ⊢F , _ = inversion-ΠΣ (wf-⊢ x₁)
        ⊢ρF = wk-⊢ [ρ] ⊢F
    in
    η-eq (wk-⊢ [ρ] x₁) (wk-⊢ [ρ] x₂)
      (wk-Function [ρ] y) (wk-Function [ρ] y₁) $
    PE.subst₃ (_⊢_[conv↑]_∷_ _)
      (PE.cong₃ _∘⟨_⟩_ (PE.sym (wk1-wk≡lift-wk1 _ _)) PE.refl PE.refl)
      (PE.cong₃ _∘⟨_⟩_ (PE.sym (wk1-wk≡lift-wk1 _ _)) PE.refl PE.refl)
      PE.refl $
    wkConv↑Term (⊢ʷᵏlift [ρ] ⊢ρF) t<>u
  wkConv↓Term [ρ] (Σ-η {B} ⊢p ⊢r pProd rProd fstConv sndConv) =
    Σ-η (wk-⊢ [ρ] ⊢p)
        (wk-⊢ [ρ] ⊢r)
        (wk-Product [ρ] pProd)
        (wk-Product [ρ] rProd)
        (wkConv↑Term [ρ] fstConv)
        (PE.subst (λ x → _ ⊢ _ [conv↑] _ ∷ x)
                  (wk-β B)
                  (wkConv↑Term [ρ] sndConv))
  wkConv↓Term [ρ] (η-unit [t] [u] tWhnf uWhnf η) =
    η-unit (wk-⊢ [ρ] [t]) (wk-⊢ [ρ] [u])
           (wk-Whnf [ρ] tWhnf) (wk-Whnf [ρ] uWhnf) η
  wkConv↓Term ρ (Id-ins ⊢v₁ v₁~v₂) =
    Id-ins (wk-⊢ ρ ⊢v₁) (wk~↓ ρ v₁~v₂)
  wkConv↓Term ρ (rfl-refl t≡u) =
    rfl-refl (wk-⊢ ρ t≡u)

  -- Weakening of algorithmic equality of levels.

  wkConv↓Level :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Γ₁ ⊢ t [conv↓] u ∷Level →
    Γ₂ ⊢ U.wk ρ t [conv↓] U.wk ρ u ∷Level
  wkConv↓Level {ρ = ρ} [ρ] ([↓]ˡ tᵛ uᵛ t≡ u≡ t≡u) =
    [↓]ˡ
      (wkLevelᵛ [ρ] tᵛ) (wkLevelᵛ [ρ] uᵛ)
      (wk-↓ᵛ [ρ] t≡)
      (wk-↓ᵛ [ρ] u≡)
      (wk-≡ᵛ [ρ] _ _ t≡u)

  wkLevelAtom :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    LevelAtom Γ₁ →
    LevelAtom Γ₂
  wkLevelAtom [ρ] zeroᵘ = zeroᵘ
  wkLevelAtom [ρ] (ne x) = ne (wk~↓ [ρ] x)

  wkLevel⁺ :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Level⁺ Γ₁ →
    Level⁺ Γ₂
  wkLevel⁺ [ρ] (n , l) = n , wkLevelAtom [ρ] l

  wkLevelᵛ :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Levelᵛ Γ₁ →
    Levelᵛ Γ₂
  wkLevelᵛ [ρ] L.[] = L.[]
  wkLevelᵛ [ρ] (x L.∷ xs) = wkLevel⁺ [ρ] x L.∷ wkLevelᵛ [ρ] xs

  wkLevelAtom→Term :
    (⊢ρ : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁) (t : LevelAtom Γ₁) →
    LevelAtom→Term (wkLevelAtom ⊢ρ t) PE.≡ U.wk ρ (LevelAtom→Term t)
  wkLevelAtom→Term [ρ] zeroᵘ = PE.refl
  wkLevelAtom→Term [ρ] (ne x) = PE.refl

  wkLevel⁺→Term :
    (⊢ρ : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁) (t : Level⁺ Γ₁) →
    Level⁺→Term (wkLevel⁺ ⊢ρ t) PE.≡ U.wk ρ (Level⁺→Term t)
  wkLevel⁺→Term [ρ] (n , a) =
    PE.trans (PE.cong (1ᵘ+ⁿ n) (wkLevelAtom→Term [ρ] a))
      (PE.sym (wk-1ᵘ+ⁿ n))

  wkLevelᵛ→Term :
    ∀ {t} (⊢ρ : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁) →
    Levelᵛ→Term (wkLevelᵛ ⊢ρ t) PE.≡ U.wk ρ (Levelᵛ→Term t)
  wkLevelᵛ→Term {t = L.[]} [ρ] = PE.refl
  wkLevelᵛ→Term {t = x L.∷ t} [ρ] = PE.cong₂ _supᵘ_ (wkLevel⁺→Term [ρ] x) (wkLevelᵛ→Term [ρ])

  wk-sucᵛ :
    (⊢ρ : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁) (v v′ : Levelᵛ Γ₁) → v PE.≡ sucᵛ v′ →
    wkLevelᵛ ⊢ρ v PE.≡ sucᵛ (wkLevelᵛ ⊢ρ v′)
  wk-sucᵛ [ρ] v v′ PE.refl = PE.cong (_ L.∷_) (wk-map-suc⁺ [ρ] _ _ PE.refl)

  wk-map-suc⁺ :
    (⊢ρ : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁) (v v′ : Levelᵛ Γ₁) →
    v PE.≡ map-suc⁺ v′ → wkLevelᵛ ⊢ρ v PE.≡ map-suc⁺ (wkLevelᵛ ⊢ρ v′)
  wk-map-suc⁺ [ρ] L.[] L.[] PE.refl = PE.refl
  wk-map-suc⁺ [ρ] L.[] (x L.∷ v′) ()
  wk-map-suc⁺ [ρ] (x L.∷ v) L.[] ()
  wk-map-suc⁺ [ρ] ((n , a) L.∷ v) ((n′ , a′) L.∷ v′) PE.refl = PE.cong (_ L.∷_) (wk-map-suc⁺ [ρ] v v′ PE.refl)

  wkLevel⁺-cong-suc⁺ :
    (⊢ρ : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁) (a b : Level⁺ Γ₁) → a PE.≡ suc⁺ b →
    wkLevel⁺ ⊢ρ a PE.≡ suc⁺ (wkLevel⁺ ⊢ρ b)
  wkLevel⁺-cong-suc⁺ [ρ] a b PE.refl = PE.refl

  wkLevel⁺-cong :
    (⊢ρ : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁) (a b : Level⁺ Γ₁) → a PE.≡ b →
    wkLevel⁺ ⊢ρ a PE.≡ wkLevel⁺ ⊢ρ b
  wkLevel⁺-cong [ρ] a b PE.refl = PE.refl

  wkLevelᵛ-cong :
    (⊢ρ : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁) (a b : Levelᵛ Γ₁) → a PE.≡ b →
    wkLevelᵛ ⊢ρ a PE.≡ wkLevelᵛ ⊢ρ b
  wkLevelᵛ-cong [ρ] a b PE.refl = PE.refl

  wk-supᵛ :
    (⊢ρ : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁) (v v′ v″ : Levelᵛ Γ₁) →
    v PE.≡ supᵛ v′ v″ →
    wkLevelᵛ ⊢ρ v PE.≡ supᵛ (wkLevelᵛ ⊢ρ v′) (wkLevelᵛ ⊢ρ v″)
  wk-supᵛ [ρ] L.[] L.[] v″ PE.refl = PE.refl
  wk-supᵛ [ρ] L.[] (x L.∷ v′) v″ ()
  wk-supᵛ [ρ] (x L.∷ v) L.[] v″ PE.refl = PE.refl
  wk-supᵛ [ρ] (x L.∷ v) (x₁ L.∷ v′) v″ eq =
    let a , b = L.∷-injective eq
    in PE.cong₂ L._∷_ (wkLevel⁺-cong [ρ] x x₁ a) (wk-supᵛ [ρ] _ _ v″ b)

  wk-supᵛ-map-suc⁺ :
    (⊢ρ : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁) (v v′ v″ : Levelᵛ Γ₁) →
    v PE.≡ supᵛ (map-suc⁺ v′) v″ →
    wkLevelᵛ ⊢ρ v PE.≡ supᵛ (map-suc⁺ (wkLevelᵛ ⊢ρ v′)) (wkLevelᵛ ⊢ρ v″)
  wk-supᵛ-map-suc⁺ [ρ] L.[] L.[] v″ PE.refl = PE.refl
  wk-supᵛ-map-suc⁺ [ρ] L.[] (x L.∷ v′) v″ ()
  wk-supᵛ-map-suc⁺ [ρ] (x L.∷ v) L.[] v″ PE.refl = PE.refl
  wk-supᵛ-map-suc⁺ [ρ] (x L.∷ v) (x₁ L.∷ v′) v″ eq =
    let a , b = L.∷-injective eq
    in PE.cong₂ L._∷_ (wkLevel⁺-cong-suc⁺ [ρ] x x₁ a) (wk-supᵛ-map-suc⁺ [ρ] _ _ v″ b)

  wk-supᵛ-sucᵛ :
    (⊢ρ : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁) (v v′ v″ : Levelᵛ Γ₁) →
    v PE.≡ supᵛ (sucᵛ v′) v″ →
    wkLevelᵛ ⊢ρ v PE.≡ supᵛ (sucᵛ (wkLevelᵛ ⊢ρ v′)) (wkLevelᵛ ⊢ρ v″)
  wk-supᵛ-sucᵛ [ρ] L.[] v′ v″ ()
  wk-supᵛ-sucᵛ [ρ] (x L.∷ v) v′ v″ eq =
    let a , b = L.∷-injective eq
    in PE.cong₂ L._∷_ (wkLevel⁺-cong [ρ] _ _ a) (wk-supᵛ-map-suc⁺ [ρ] _ _ v″ b)

  wk-↑ᵛ :
    (⊢ρ : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁) →
    ∀ {t v} → Γ₁ ⊢ t ↑ᵛ v → Γ₂ ⊢ U.wk ρ t ↑ᵛ wkLevelᵛ ⊢ρ v
  wk-↑ᵛ [ρ] ([↑]ᵛ d t↓v) = [↑]ᵛ (wk-↘∷ [ρ] d) (wk-↓ᵛ [ρ] t↓v)

  wk-↓ᵛ :
    (⊢ρ : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁) →
    ∀ {t v} → Γ₁ ⊢ t ↓ᵛ v → Γ₂ ⊢ U.wk ρ t ↓ᵛ wkLevelᵛ ⊢ρ v
  wk-↓ᵛ [ρ] (zeroᵘₙ ok _) = zeroᵘₙ ok (wf-⊢ʷᵏ [ρ])
  wk-↓ᵛ [ρ] (sucᵘₙ {v} {v′} x₁ t≡u) = sucᵘₙ (wk-sucᵛ [ρ] v _ x₁) (wk-↑ᵛ [ρ] t≡u)
  wk-↓ᵛ [ρ] (neₙ x) = neₙ (wk-~ᵛ [ρ] x)

  wk-~ᵛ :
    (⊢ρ : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁) →
    ∀ {t v} → Γ₁ ⊢ t ~ᵛ v → Γ₂ ⊢ U.wk ρ t ~ᵛ wkLevelᵛ ⊢ρ v
  wk-~ᵛ {ρ = ρ} [ρ] (supᵘˡₙ {v′} {v″} x t~ u↑) = supᵘˡₙ (wk-supᵛ [ρ] _ v′ v″ x) (wk-~ᵛ [ρ] t~) (wk-↑ᵛ [ρ] u↑)
  wk-~ᵛ {ρ = ρ} [ρ] (supᵘʳₙ {v′} {v″} x t↑ u~) = supᵘʳₙ (wk-supᵛ-sucᵛ [ρ] _ v′ v″ x) (wk-↑ᵛ [ρ] t↑) (wk-~ᵛ [ρ] u~)
  wk-~ᵛ {ρ = ρ} [ρ] (neₙ [t] x) = neₙ (wk~↓ [ρ] [t]) (wkLevelᵛ-cong [ρ] _ _ x)

  wk-≡ⁿ :
    (⊢ρ : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁) (t u : Term n) → ≡ⁿ Γ₁ t u d →
    ≡ⁿ Γ₂ (U.wk ρ t) (U.wk ρ u) d
  wk-≡ⁿ [ρ] t u (ne≡ x) = ne≡ (wk~↓ [ρ] x)
  wk-≡ⁿ [ρ] t u (ne≡' x) = ne≡' (wk~↓ [ρ] x)

  wk-≤⁺ :
    (⊢ρ : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁) (t u : Level⁺ Γ₁) → ≤⁺ d t u →
    ≤⁺ d (wkLevel⁺ ⊢ρ t) (wkLevel⁺ ⊢ρ u)
  wk-≤⁺ [ρ] t u (x , zeroᵘ≤) = x , zeroᵘ≤
  wk-≤⁺ [ρ] t u (x , ne≤ y) = x , ne≤ (wk-≡ⁿ [ρ] _ _ y)

  wk-≤⁺ᵛ :
    (⊢ρ : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁) (t : Level⁺ Γ₁) (u : Levelᵛ Γ₁) →
    ≤⁺ᵛ d t u → ≤⁺ᵛ d (wkLevel⁺ ⊢ρ t) (wkLevelᵛ ⊢ρ u)
  wk-≤⁺ᵛ [ρ] t u (Any.here px) = Any.here (wk-≤⁺ [ρ] _ _ px)
  wk-≤⁺ᵛ [ρ] t u (Any.there t≤u) = Any.there (wk-≤⁺ᵛ [ρ] _ _ t≤u)

  wk-≤ᵛ :
    (⊢ρ : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁) (t u : Levelᵛ Γ₁) → ≤ᵛ d t u →
    ≤ᵛ d (wkLevelᵛ ⊢ρ t) (wkLevelᵛ ⊢ρ u)
  wk-≤ᵛ [ρ] t u All.[] = All.[]
  wk-≤ᵛ [ρ] t u (px All.∷ t≤u) = wk-≤⁺ᵛ [ρ] _ _ px All.∷ wk-≤ᵛ [ρ] _ _ t≤u

  wk-≡ᵛ :
    (⊢ρ : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁) (t u : Levelᵛ Γ₁) → t ≡ᵛ u →
    wkLevelᵛ ⊢ρ t ≡ᵛ wkLevelᵛ ⊢ρ u
  wk-≡ᵛ [ρ] t u (t≤u , u≤t) = wk-≤ᵛ [ρ] t u t≤u , wk-≤ᵛ [ρ] u t u≤t
