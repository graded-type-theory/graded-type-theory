------------------------------------------------------------------------
-- The algorithmic equality is symmetric.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions

module Definition.Conversion.Symmetry
  {a} {M : Set a}
  (R : Type-restrictions M)
  where

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R as W hiding (wk)
open import Definition.Conversion R
open import Definition.Conversion.Stability R
open import Definition.Conversion.Soundness R
open import Definition.Conversion.Conversion R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Consequences.Equality R
open import Definition.Typed.Consequences.Reduction R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Consequences.Stability R
open import Definition.Typed.Consequences.DerivedRules.Nat R

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ Δ : Con Term n

mutual
  -- Symmetry of algorithmic equality of neutrals.
  sym~↑ : ∀ {t u A} → ⊢ Γ ≡ Δ
        → Γ ⊢ t ~ u ↑ A
        → ∃ λ B → Γ ⊢ A ≡ B × Δ ⊢ u ~ t ↑ B
  sym~↑ Γ≡Δ (var-refl x x≡y) =
    let ⊢A = syntacticTerm x
    in  _ , refl ⊢A
     ,  var-refl (PE.subst (λ y → _ ⊢ var y ∷ _) x≡y (stabilityTerm Γ≡Δ x))
                 (PE.sym x≡y)
  sym~↑ Γ≡Δ (app-cong t~u x) =
    case contextConvSubst Γ≡Δ of λ {
      (⊢Γ , ⊢Δ , _) →
    case sym~↓ Γ≡Δ t~u of λ {
      (B , whnfB , A≡B , u~t) →
    case Π≡A A≡B whnfB of λ {
      (F′ , G′ , ΠF′G′≡B) →
    case injectivity (PE.subst (λ x → _ ⊢ _ ≡ x) ΠF′G′≡B A≡B) of λ {
      (F≡F′ , G≡G′ , _ , _) →
    _ , substTypeEq G≡G′ (soundnessConv↑Term x) ,
    app-cong (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) ΠF′G′≡B u~t)
      (convConvTerm (symConv↑Term Γ≡Δ x) (stabilityEq Γ≡Δ F≡F′)) }}}}
  sym~↑ Γ≡Δ (fst-cong p~r) =
    case sym~↓ Γ≡Δ p~r of λ (B , whnfB , A≡B , r~p) →
    case Σ≡A A≡B whnfB of λ where
      (F′ , G′ , PE.refl) →
        case Σ-injectivity A≡B of λ where
          (F≡ , G≡ , _ , _) →
            F′ , F≡ , fst-cong r~p
  sym~↑ Γ≡Δ (snd-cong {p} {r} {F} {G} p~r) =
    case sym~↓ Γ≡Δ p~r of λ (B , whnfB , A≡B , r~p) →
    case Σ≡A A≡B whnfB of λ where
      (F′ , G′ , PE.refl) →
        case Σ-injectivity A≡B of λ where
          (F≡ , G≡ , _ , _) →
            let fst≡ = soundness~↑ (fst-cong p~r) in
            G′ [ fst _ r ]₀ , substTypeEq G≡ fst≡ , snd-cong r~p
  sym~↑ Γ≡Δ (natrec-cong x x₁ x₂ t~u) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        B , whnfB , A≡B , u~t = sym~↓ Γ≡Δ t~u
        B≡ℕ = ℕ≡A A≡B whnfB
        F≡G = stabilityEq (Γ≡Δ ∙ refl (ℕⱼ ⊢Γ)) (soundnessConv↑ x)
        F[0]≡G[0] = substTypeEq F≡G (refl (zeroⱼ ⊢Δ))
    in  _ , substTypeEq (soundnessConv↑ x) (soundness~↓ t~u)
    ,   natrec-cong (symConv↑ (Γ≡Δ ∙ (refl (ℕⱼ ⊢Γ))) x)
                    (convConvTerm (symConv↑Term Γ≡Δ x₁) F[0]≡G[0])
                    (convConvTerm (symConv↑Term (Γ≡Δ ∙ refl (ℕⱼ ⊢Γ) ∙ soundnessConv↑ x) x₂) (sucCong′ F≡G))
                    (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) B≡ℕ u~t)
  sym~↑ {Γ = Γ} {Δ = Δ} Γ≡Δ
    (prodrec-cong {F = F} {G = G} C↑E g~h u↑v) =
    case sym~↓ Γ≡Δ g~h of λ (B , whnfB , ⊢Σ≡B , h~g) →
    case Σ≡A ⊢Σ≡B whnfB of λ where
      (F′ , G′ , PE.refl) →
        case Σ-injectivity (stabilityEq Γ≡Δ ⊢Σ≡B) of λ where
          (⊢F≡F′ , ⊢G≡G′ , _ , _ , _) →
            let g≡h = soundness~↓ g~h
                C≡E = soundnessConv↑ C↑E
                ⊢Σ , _ = syntacticEqTerm g≡h
                ⊢F , ⊢G , ok = inversion-ΠΣ ⊢Σ
                E↑C = symConv↑ (Γ≡Δ ∙ ⊢Σ≡B) C↑E
                v↑u = symConv↑Term (Γ≡Δ ∙ refl ⊢F ∙ refl ⊢G) u↑v
                ⊢Γ , ⊢Δ , ⊢idsubst = contextConvSubst Γ≡Δ
                ⊢F′ = stability Γ≡Δ ⊢F
                ⊢G′ = stability (Γ≡Δ ∙ refl ⊢F) ⊢G
                ⊢ΔF = ⊢Δ ∙ ⊢F′
                ⊢ΔFG = ⊢ΔF ∙ ⊢G′
                ⊢ρF = W.wk (step (step id)) ⊢ΔFG ⊢F′
                ⊢ρG = W.wk (lift (step (step id))) (⊢ΔFG ∙ ⊢ρF) ⊢G′
                C₊≡E₊ = subst↑²TypeEq-prod (stabilityEq (Γ≡Δ ∙ refl ⊢Σ) C≡E)
                          ok
            in  _ , substTypeEq C≡E g≡h
              , prodrec-cong E↑C h~g
                  (convConv↑Term (reflConEq ⊢Δ ∙ ⊢F≡F′ ∙ ⊢G≡G′)
                     C₊≡E₊ v↑u)
  sym~↑ Γ≡Δ (Emptyrec-cong x t~u) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        B , whnfB , A≡B , u~t = sym~↓ Γ≡Δ t~u
        B≡Empty = Empty≡A A≡B whnfB
        F≡G = stabilityEq Γ≡Δ (soundnessConv↑ x)
    in  _ , soundnessConv↑ x
    , Emptyrec-cong (symConv↑ Γ≡Δ x)
                    (PE.subst (λ x₁ → _ ⊢ _ ~ _ ↓ x₁) B≡Empty u~t)

  -- Symmetry of algorithmic equality of neutrals of types in WHNF.
  sym~↓ : ∀ {t u A} → ⊢ Γ ≡ Δ → Γ ⊢ t ~ u ↓ A
         → ∃ λ B → Whnf B × Γ ⊢ A ≡ B × Δ ⊢ u ~ t ↓ B
  sym~↓ Γ≡Δ ([~] A₁ D whnfA k~l) =
    let B , A≡B , k~l′ = sym~↑ Γ≡Δ k~l
        _ , ⊢B = syntacticEq A≡B
        B′ , whnfB′ , D′ = whNorm ⊢B
        A≡B′ = trans (sym (subset* D)) (trans A≡B (subset* (red D′)))
    in  B′ , whnfB′ , A≡B′ , [~] B (stabilityRed* Γ≡Δ (red D′)) whnfB′ k~l′

  -- Symmetry of algorithmic equality of types.
  symConv↑ : ∀ {A B} → ⊢ Γ ≡ Δ → Γ ⊢ A [conv↑] B → Δ ⊢ B [conv↑] A
  symConv↑ Γ≡Δ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) =
    [↑] B′ A′ (stabilityRed* Γ≡Δ D′) (stabilityRed* Γ≡Δ D) whnfB′ whnfA′
        (symConv↓ Γ≡Δ A′<>B′)

  -- Symmetry of algorithmic equality of types in WHNF.
  symConv↓ : ∀ {A B} → ⊢ Γ ≡ Δ → Γ ⊢ A [conv↓] B → Δ ⊢ B [conv↓] A
  symConv↓ Γ≡Δ (U-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  U-refl ⊢Δ
  symConv↓ Γ≡Δ (ℕ-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  ℕ-refl ⊢Δ
  symConv↓ Γ≡Δ (Empty-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  Empty-refl ⊢Δ
  symConv↓ Γ≡Δ (Unit-refl x ok) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  Unit-refl ⊢Δ ok
  symConv↓ Γ≡Δ (ne A~B) =
    let B , whnfB , U≡B , B~A = sym~↓ Γ≡Δ A~B
        B≡U = U≡A U≡B
    in  ne (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) B≡U B~A)
  symConv↓ Γ≡Δ (ΠΣ-cong x A<>B A<>B₁ ok) =
    let F≡H = soundnessConv↑ A<>B
        _ , ⊢H = syntacticEq (stabilityEq Γ≡Δ F≡H)
    in  ΠΣ-cong ⊢H (symConv↑ Γ≡Δ A<>B)
          (symConv↑ (Γ≡Δ ∙ F≡H) A<>B₁) ok

  -- Symmetry of algorithmic equality of terms.
  symConv↑Term : ∀ {t u A} → ⊢ Γ ≡ Δ → Γ ⊢ t [conv↑] u ∷ A → Δ ⊢ u [conv↑] t ∷ A
  symConv↑Term Γ≡Δ ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) =
    [↑]ₜ B u′ t′ (stabilityRed* Γ≡Δ D) (stabilityRed*Term Γ≡Δ d′)
         (stabilityRed*Term Γ≡Δ d) whnfB whnfu′ whnft′ (symConv↓Term Γ≡Δ t<>u)

  -- Symmetry of algorithmic equality of terms in WHNF.
  symConv↓Term : ∀ {t u A} → ⊢ Γ ≡ Δ → Γ ⊢ t [conv↓] u ∷ A → Δ ⊢ u [conv↓] t ∷ A
  symConv↓Term Γ≡Δ (ℕ-ins t~u) =
    let B , whnfB , A≡B , u~t = sym~↓ Γ≡Δ t~u
        B≡ℕ = ℕ≡A A≡B whnfB
    in  ℕ-ins (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) B≡ℕ u~t)
  symConv↓Term Γ≡Δ (Empty-ins t~u) =
    let B , whnfB , A≡B , u~t = sym~↓ Γ≡Δ t~u
        B≡Empty = Empty≡A A≡B whnfB
    in  Empty-ins (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) B≡Empty u~t)
  symConv↓Term Γ≡Δ (Unit-ins t~u) =
    let B , whnfB , A≡B , u~t = sym~↓ Γ≡Δ t~u
        B≡Unit = Unit≡A A≡B whnfB
    in  Unit-ins (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) B≡Unit u~t)
  symConv↓Term Γ≡Δ (Σᵣ-ins t u t~u) =
    case sym~↓ Γ≡Δ t~u of λ (B , whnfB , A≡B , u~t) →
    case Σ≡A A≡B whnfB of λ where
      (_ , B≡Σ , PE.refl) →
        Σᵣ-ins (stabilityTerm Γ≡Δ u) (stabilityTerm Γ≡Δ t) u~t
  symConv↓Term Γ≡Δ (ne-ins t u x t~u) =
    let B , whnfB , A≡B , u~t = sym~↓ Γ≡Δ t~u
    in  ne-ins (stabilityTerm Γ≡Δ u) (stabilityTerm Γ≡Δ t) x u~t
  symConv↓Term Γ≡Δ (univ x x₁ x₂) =
    univ (stabilityTerm Γ≡Δ x₁) (stabilityTerm Γ≡Δ x) (symConv↓ Γ≡Δ x₂)
  symConv↓Term Γ≡Δ (zero-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  zero-refl ⊢Δ
  symConv↓Term Γ≡Δ (suc-cong t<>u) = suc-cong (symConv↑Term Γ≡Δ t<>u)
  symConv↓Term Γ≡Δ (prod-cong x x₁ x₂ x₃ ok) =
    let Δ⊢F = stability Γ≡Δ x
        Δ⊢G = stability (Γ≡Δ ∙ refl x) x₁
        Δ⊢t′↑t = symConv↑Term Γ≡Δ x₂
        _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        Δ⊢u′↑u = symConv↑Term Γ≡Δ x₃
        Gt≡Gt′ = substTypeEq (refl Δ⊢G) (sym (soundnessConv↑Term Δ⊢t′↑t))
    in  prod-cong Δ⊢F Δ⊢G Δ⊢t′↑t
          (convConv↑Term (reflConEq ⊢Δ) Gt≡Gt′ Δ⊢u′↑u) ok
  symConv↓Term Γ≡Δ (η-eq x₁ x₂ y y₁ t<>u) =
    let ⊢F , _ = syntacticΠ (syntacticTerm x₁)
    in  η-eq (stabilityTerm Γ≡Δ x₂) (stabilityTerm Γ≡Δ x₁)
             y₁ y (symConv↑Term (Γ≡Δ ∙ refl ⊢F) t<>u)
  symConv↓Term Γ≡Δ (Σ-η ⊢p ⊢r pProd rProd fstConv sndConv) =
    let Δ⊢p = stabilityTerm Γ≡Δ ⊢p
        Δ⊢r = stabilityTerm Γ≡Δ ⊢r
        ⊢G = proj₂ (syntacticΣ (syntacticTerm ⊢p))
        Δfst≡ = symConv↑Term Γ≡Δ fstConv
        Δsnd≡₁ = symConv↑Term Γ≡Δ sndConv
        ΔGfstt≡Gfstu = stabilityEq Γ≡Δ (substTypeEq (refl ⊢G)
                                                    (soundnessConv↑Term fstConv))
        Δsnd≡ = convConvTerm Δsnd≡₁ ΔGfstt≡Gfstu
    in  Σ-η Δ⊢r Δ⊢p rProd pProd Δfst≡ Δsnd≡
  symConv↓Term Γ≡Δ (η-unit [t] [u] tUnit uUnit) =
    let [t] = stabilityTerm Γ≡Δ [t]
        [u] = stabilityTerm Γ≡Δ [u]
    in  η-unit [u] [t] uUnit tUnit

symConv↓Term′ : ∀ {t u A} → Γ ⊢ t [conv↓] u ∷ A → Γ ⊢ u [conv↓] t ∷ A
symConv↓Term′ tConvU =
  symConv↓Term (reflConEq (wfEqTerm (soundnessConv↓Term tConvU))) tConvU

-- Symmetry of algorithmic equality of types with preserved context.
symConv : ∀ {A B} → Γ ⊢ A [conv↑] B → Γ ⊢ B [conv↑] A
symConv A<>B =
  let ⊢Γ = wfEq (soundnessConv↑ A<>B)
  in  symConv↑ (reflConEq ⊢Γ) A<>B

-- Symmetry of algorithmic equality of terms with preserved context.
symConvTerm : ∀ {t u A} → Γ ⊢ t [conv↑] u ∷ A → Γ ⊢ u [conv↑] t ∷ A
symConvTerm t<>u =
  let ⊢Γ = wfEqTerm (soundnessConv↑Term t<>u)
  in  symConv↑Term (reflConEq ⊢Γ) t<>u
