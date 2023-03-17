module Definition.Conversion.Transitivity
  {a} (M : Set a) where

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed M
open import Definition.Typed.Properties M
open import Definition.Typed.RedSteps M
open import Definition.Conversion M
open import Definition.Conversion.Soundness M
open import Definition.Conversion.Stability M
open import Definition.Conversion.Whnf M
open import Definition.Conversion.Conversion M
open import Definition.Typed.Consequences.Syntactic M
open import Definition.Typed.Consequences.Injectivity M
import Definition.Typed.Consequences.Inequality M as WF
open import Definition.Typed.Consequences.Substitution M
open import Definition.Typed.Consequences.NeTypeEq M
open import Definition.Typed.Consequences.SucCong M

open import Tools.Nat
open import Tools.Product
open import Tools.Empty
open import Tools.PropositionalEquality as PE using (≈-sym; ≈-trans)


private
  variable
    n : Nat
    Γ Δ : Con Term n

mutual
  -- Transitivity of algorithmic equality of neutrals.
  trans~↑ : ∀ {t u v A B}
         → Γ ⊢ t ~ u ↑ A
         → Γ ⊢ u ~ v ↑ B
         → Γ ⊢ t ~ v ↑ A
         × Γ ⊢ A ≡ B
  trans~↑ (var-refl x₁ x≡y) (var-refl x₂ x≡y₁) =
    var-refl x₁ (PE.trans x≡y x≡y₁)
    , neTypeEq (var _) x₁
               (PE.subst (λ x → _ ⊢ var x ∷ _) (PE.sym x≡y)
                         x₂)
  trans~↑ (app-cong t~u a<>b p≈p₁ p≈p₃) (app-cong u~v b<>c p₄≈p₃ p₄≈p₂) =
    let t~v , ΠFG≡ΠF′G′ = trans~↓ t~u u~v
        F≡F₁ , G≡G₁ , p≈p₄ , _ = injectivity ΠFG≡ΠF′G′
        a<>c = transConv↑Term F≡F₁ a<>b b<>c
    in  app-cong t~v a<>c p≈p₁ (≈-trans p≈p₄ p₄≈p₂) , substTypeEq G≡G₁ (soundnessConv↑Term a<>b)
  trans~↑ (fst-cong t~u) (fst-cong u~v) =
    let t~v , ΣFG≡ΣF′G′ = trans~↓ t~u u~v
        F≡F′ , _ , _ = Σ-injectivity ΣFG≡ΣF′G′
    in  fst-cong t~v , F≡F′
  trans~↑ (snd-cong t~u) (snd-cong u~v) =
    let t~v , ΣFG≡ΣF′G′ = trans~↓ t~u u~v
        F≡F′ , G≡G′ , _ = Σ-injectivity ΣFG≡ΣF′G′
    in  snd-cong t~v , substTypeEq G≡G′ (soundness~↑ (fst-cong t~u))
  trans~↑ (natrec-cong A<>B a₀<>b₀ aₛ<>bₛ t~u p≈p′ r≈r′)
          (natrec-cong B<>C b₀<>c₀ bₛ<>cₛ u~v p′≈p″ r′≈r″) =
    let ⊢Γ = wf (proj₁ (syntacticEqTerm (soundness~↓ t~u)))
        A≡B = soundnessConv↑ A<>B
        F[0]≡F₁[0] = substTypeEq A≡B (refl (zeroⱼ ⊢Γ))
        ΠℕFs≡ΠℕF₁s = sucCong A≡B
        A<>C = transConv↑ A<>B B<>C
        a₀<>c₀ = transConv↑Term F[0]≡F₁[0] a₀<>b₀ b₀<>c₀
        aₛ<>cₛ = transConv↑Term ΠℕFs≡ΠℕF₁s aₛ<>bₛ
                                (stabilityConv↑Term ((reflConEq (⊢Γ ∙ (ℕⱼ ⊢Γ))) ∙ sym A≡B) bₛ<>cₛ)
        t~v , _ = trans~↓ t~u u~v
        p≈p″ = ≈-trans p≈p′ p′≈p″
        r≈r″ = ≈-trans r≈r′ r′≈r″
    in  natrec-cong A<>C a₀<>c₀ aₛ<>cₛ t~v p≈p″ r≈r″
    ,   substTypeEq A≡B (soundness~↓ t~u)
  trans~↑ {Γ = Γ} (prodrec-cong! {F = F} {G} A<>B a~b t<>u)
                  (prodrec-cong! B<>C b~c u<>v) =
    let a~c , Σ≡Σ′ = trans~↓ a~b b~c
        ⊢Γ = wfEq Σ≡Σ′
        Γ≡Γ = reflConEq ⊢Γ
        F≡F′ , G≡G′ , _ = Σ-injectivity (sym Σ≡Σ′)
        _ , ⊢F = syntacticEq F≡F′
        _ , ⊢G = syntacticEq G≡G′
        ⊢G = stability (Γ≡Γ ∙ F≡F′) ⊢G
        B<>C′ = stabilityConv↑ (Γ≡Γ ∙ sym Σ≡Σ′) B<>C
        A<>C = transConv↑ A<>B B<>C′
        u<>v′ = stabilityConv↑Term (Γ≡Γ ∙ F≡F′ ∙ G≡G′) u<>v
        _ , ⊢ΓFG , _ = contextConvSubst (Γ≡Γ ∙ F≡F′ ∙ G≡G′)
        A≡B = soundnessConv↑ A<>B
        A₊≡B₊ = subst↑²TypeEq A≡B
        t<>v = transConv↑Term A₊≡B₊ t<>u u<>v′
        a≡b = soundness~↓ a~b
        Aa≡Bb = substTypeEq A≡B a≡b
    in  prodrec-cong! A<>C a~c t<>v , Aa≡Bb
  trans~↑ (Emptyrec-cong A<>B t~u p≈p′) (Emptyrec-cong B<>C u~v p′≈p″) =
    let A≡B = soundnessConv↑ A<>B
        A<>C = transConv↑ A<>B B<>C
        t~v , _ = trans~↓  t~u u~v
    in  Emptyrec-cong A<>C t~v (≈-trans p≈p′ p′≈p″) , A≡B

  -- Transitivity of algorithmic equality of neutrals with types in WHNF.
  trans~↓ : ∀ {t u v A B}
          → Γ ⊢ t ~ u ↓ A
          → Γ ⊢ u ~ v ↓ B
          → Γ ⊢ t ~ v ↓ A
          × Γ ⊢ A ≡ B
  trans~↓ ([~] A₁ D whnfA k~l) ([~] A₂ D₁ whnfA₁ k~l₁) =
    let t~v , A≡B = trans~↑ k~l k~l₁
    in  [~] A₁ D whnfA t~v
    ,   trans (sym (subset* D))
              (trans A≡B
                     (subset* D₁))

  -- Transitivity of algorithmic equality of types.
  transConv↑ : ∀ {A B C}
            → Γ ⊢ A [conv↑] B
            → Γ ⊢ B [conv↑] C
            → Γ ⊢ A [conv↑] C
  transConv↑ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′)
             ([↑] A″ B″ D₁ D″ whnfA″ whnfB″ A′<>B″) =
    [↑] A′ B″ D D″ whnfA′ whnfB″
        (transConv↓ A′<>B′
                    (PE.subst (λ x → _ ⊢ x [conv↓] B″)
                              (whrDet* (D₁ , whnfA″)
                                        (D′ , whnfB′))
                              A′<>B″))
  transConv↑′ : ∀ {A B C}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ A [conv↑] B
              → Δ ⊢ B [conv↑] C
              → Γ ⊢ A [conv↑] C
  transConv↑′ Γ≡Δ aConvB bConvC =
    transConv↑ aConvB (stabilityConv↑ (symConEq Γ≡Δ) bConvC)

  -- Transitivity of algorithmic equality of types in WHNF.
  transConv↓ : ∀ {A B C}
            → Γ ⊢ A [conv↓] B
            → Γ ⊢ B [conv↓] C
            → Γ ⊢ A [conv↓] C
  transConv↓ (U-refl x) (U-refl x₁) = U-refl x
  transConv↓ (ℕ-refl x) (ℕ-refl x₁) = ℕ-refl x
  transConv↓ (Empty-refl x) (Empty-refl x₁) = Empty-refl x
  transConv↓ (Unit-refl x) (Unit-refl x₁) = Unit-refl x
  transConv↓ (ne x) (ne x₁) =
    let A~C , U≡U = trans~↓ x x₁
    in  ne A~C
  transConv↓ (ΠΣ-cong x x₁ x₂) (ΠΣ-cong x₃ x₄ x₅) =
    ΠΣ-cong x (transConv↑ x₁ x₄)
      (transConv↑′ (reflConEq (wf x) ∙ soundnessConv↑ x₁) x₂ x₅)
  -- Refutable cases
  transConv↓ (U-refl x) (ne ([~] A D whnfB ()))
  transConv↓ (ℕ-refl x) (ne ([~] A D whnfB ()))
  transConv↓ (Empty-refl x) (ne ([~] A D whnfB ()))
  transConv↓ (ΠΣ-cong _ _ _) (ne ([~] _ _ _ ()))
  transConv↓ (ne ([~] A₁ D whnfB ())) (U-refl x₁)
  transConv↓ (ne ([~] A₁ D whnfB ())) (ℕ-refl x₁)
  transConv↓ (ne ([~] A₁ D whnfB ())) (Empty-refl x₁)
  transConv↓ (ne ([~] _ _ _ ()))      (ΠΣ-cong _ _ _)

  -- Transitivity of algorithmic equality of terms.
  transConv↑Term : ∀ {t u v A B}
                → Γ ⊢ A ≡ B
                → Γ ⊢ t [conv↑] u ∷ A
                → Γ ⊢ u [conv↑] v ∷ B
                → Γ ⊢ t [conv↑] v ∷ A
  transConv↑Term A≡B ([↑]ₜ B₁ t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
                 ([↑]ₜ B₂ t″ u″ D₁ d₁ d″ whnfB₁ whnft″ whnfu″ t<>u₁) =
    let B₁≡B₂ = trans (sym (subset* D))
                      (trans A≡B
                             (subset* D₁))
        d₁″ = conv* d″ (sym B₁≡B₂)
        d₁′  = conv* d′ B₁≡B₂
    in  [↑]ₜ B₁ t′ u″ D d d₁″ whnfB whnft′ whnfu″
             (transConv↓Term B₁≡B₂ t<>u
                             (PE.subst (λ x → _ ⊢ x [conv↓] u″ ∷ B₂)
                                       (whrDet*Term (d₁ , whnft″)
                                                    (d₁′ , whnfu′))
                                       t<>u₁))

  transConv↑Term′ : ∀ {t u v A B}
                  → ⊢ Γ ≡ Δ
                  → Γ ⊢ A ≡ B
                  → Γ ⊢ t [conv↑] u ∷ A
                  → Δ ⊢ u [conv↑] v ∷ B
                  → Γ ⊢ t [conv↑] v ∷ A
  transConv↑Term′ Γ≡Δ A≡B tConvU uConvV =
    transConv↑Term A≡B tConvU (stabilityConv↑Term (symConEq Γ≡Δ) uConvV)

  -- Transitivity of algorithmic equality of terms in WHNF.
  transConv↓Term : ∀ {t u v A B}
                → Γ ⊢ A ≡ B
                → Γ ⊢ t [conv↓] u ∷ A
                → Γ ⊢ u [conv↓] v ∷ B
                → Γ ⊢ t [conv↓] v ∷ A
  transConv↓Term A≡B (ℕ-ins x) (ℕ-ins x₁) =
    ℕ-ins (proj₁ (trans~↓ x x₁))
  transConv↓Term A≡B (Empty-ins x) (Empty-ins x₁) =
    Empty-ins (proj₁ (trans~↓ x x₁))
  transConv↓Term A≡B (Unit-ins t~u) uConvV =
    let _ , [t] , _ = syntacticEqTerm (soundness~↓ t~u)
        _ , tNe , _ = ne~↓ t~u
        _ , _ , [v] = syntacticEqTerm (soundnessConv↓Term uConvV)
        [v] = conv [v] (sym A≡B)
        _ , _ , vWhnf = whnfConv↓Term uConvV
    in  η-unit [t] [v] (ne tNe) vWhnf
  transConv↓Term A≡B (Σᵣ-ins t u x) (Σᵣ-ins t′ u′ x₁) =
    Σᵣ-ins t (conv u′ (sym A≡B)) (proj₁ (trans~↓ x x₁))
  transConv↓Term A≡B (ne-ins t u x x₁) (ne-ins t′ u′ x₂ x₃) =
    ne-ins t (conv u′ (sym A≡B)) x
           (proj₁ (trans~↓ x₁ x₃))
  transConv↓Term A≡B (univ x x₁ x₂) (univ x₃ x₄ x₅) =
    univ x x₄ (transConv↓ x₂ x₅)
  transConv↓Term A≡B (zero-refl x) conv↓ =
    convConv↓Term (reflConEq x) (sym A≡B) ℕₙ conv↓
  transConv↓Term A≡B conv↓ (zero-refl _) = conv↓
  transConv↓Term A≡B (suc-cong x) (suc-cong x₁) =
    suc-cong (transConv↑Term A≡B x x₁)
  transConv↓Term A≡B (prod-cong! x x₁ x₂ x₃) (prod-cong! x₄ x₅ x₆ x₇) =
    let F≡F′ , G≡G′ , _ = Σ-injectivity A≡B
        t≡t′ = soundnessConv↑Term x₂
        Gt≡G′t′ = substTypeEq G≡G′ t≡t′
    in  prod-cong! x x₁ (transConv↑Term F≡F′ x₂ x₆)
          (transConv↑Term Gt≡G′t′ x₃ x₇)
  transConv↓Term A≡B (η-eq x₁ x₂ y y₁ x₃) (η-eq x₅ x₆ y₂ y₃ x₇) =
    let F₁≡F , G₁≡G , p≈p′ , _ = injectivity A≡B
    in  η-eq x₁ (conv x₆ (sym A≡B)) y y₃
             λ x x₄ → transConv↑Term′ (reflConEq (wfEq F₁≡F) ∙ F₁≡F) G₁≡G
                                      (x₃ x x₄) (x₇ (≈-trans (≈-sym p≈p′) x₄) (≈-trans (≈-sym p≈p′) x₄))
  transConv↓Term A≡B
    (Σ-η ⊢p ⊢r pProd rProd fstConv sndConv)
    (Σ-η ⊢r′ ⊢q _ qProd fstConv′ sndConv′)
    with Σ-injectivity A≡B
  ... | F≡ , G≡ , PE.refl , _ =
    let Gfst≡ = substTypeEq G≡ (soundnessConv↑Term fstConv)
    in  Σ-η ⊢p (conv ⊢q (sym A≡B)) pProd qProd
            (transConv↑Term F≡ fstConv fstConv′)
            (transConv↑Term Gfst≡ sndConv sndConv′)
  transConv↓Term A≡B (η-unit [t] [u] tUnit uUnit) uConvV =
    let _ , _ , [v] = syntacticEqTerm (soundnessConv↓Term uConvV)
        [v] = conv [v] (sym A≡B)
        _ , _ , vWhnf = whnfConv↓Term uConvV
    in  η-unit [t] [v] tUnit vWhnf

  -- Refutable cases
  transConv↓Term A≡B (ℕ-ins x) (ne-ins t u x₂ x₃) = ⊥-elim (WF.ℕ≢ne x₂ A≡B)
  transConv↓Term A≡B (ℕ-ins x) (univ x₂ x₃ x₄) = ⊥-elim (WF.U≢ℕ (sym A≡B))
  transConv↓Term A≡B (ℕ-ins x) (Empty-ins x₁) = ⊥-elim (WF.ℕ≢Emptyⱼ A≡B)
  transConv↓Term A≡B (ℕ-ins x) (Unit-ins x₁) = ⊥-elim (WF.ℕ≢Unitⱼ A≡B)
  transConv↓Term A≡B (ℕ-ins x) (Σᵣ-ins x₁ x₂ x₃) = ⊥-elim (WF.ℕ≢Σ A≡B)
  transConv↓Term A≡B (ℕ-ins ([~] A D whnfB ())) (suc-cong x₂)
  transConv↓Term A≡B (ℕ-ins x) (prod-cong! x₂ x₃ x₄ x₅) = ⊥-elim (WF.ℕ≢Σ A≡B)
  transConv↓Term A≡B (ℕ-ins x) (η-eq x₃ x₄ y y₁ x₅) = ⊥-elim (WF.ℕ≢Π A≡B)
  transConv↓Term A≡B (ℕ-ins x₁) (Σ-η x₂ x₃ x₄ x₅ x₆ x₇) = ⊥-elim (WF.ℕ≢Σ A≡B)
  transConv↓Term A≡B (ℕ-ins x) (η-unit _ _ _ _) = ⊥-elim (WF.ℕ≢Unitⱼ A≡B)
  transConv↓Term A≡B (Empty-ins x) (ne-ins t u x₂ x₃) = ⊥-elim (WF.Empty≢neⱼ x₂ A≡B)
  transConv↓Term A≡B (Empty-ins x) (univ x₂ x₃ x₄) = ⊥-elim (WF.U≢Emptyⱼ (sym A≡B))
  transConv↓Term A≡B (Empty-ins x₁) (ℕ-ins x) = ⊥-elim (WF.ℕ≢Emptyⱼ (sym A≡B))
  transConv↓Term A≡B (Empty-ins x₁) (Unit-ins x) = ⊥-elim (WF.Empty≢Unitⱼ A≡B)
  transConv↓Term A≡B (Empty-ins x) (Σᵣ-ins x₁ x₂ x₃) = ⊥-elim (WF.Empty≢Σⱼ A≡B)
  transConv↓Term A≡B (Empty-ins ([~] A D whnfB ())) (suc-cong x₂)
  transConv↓Term A≡B (Empty-ins x) (prod-cong! x₂ x₃ x₄ x₅) = ⊥-elim (WF.Empty≢Σⱼ A≡B)
  transConv↓Term A≡B (Empty-ins x) (η-eq x₃ x₄ y y₁ x₅) = ⊥-elim (WF.Empty≢Πⱼ A≡B)
  transConv↓Term A≡B (Empty-ins x₁) (Σ-η x₂ x₃ x₄ x₅ x₆ x₇) = ⊥-elim (WF.Empty≢Σⱼ A≡B)
  transConv↓Term A≡B (Empty-ins x₁) (η-unit _ _ _ _) = ⊥-elim (WF.Empty≢Unitⱼ A≡B)
  transConv↓Term A≡B (Σᵣ-ins x x₁ x₂) (ℕ-ins x₃) = ⊥-elim (WF.ℕ≢Σ (sym A≡B))
  transConv↓Term A≡B (Σᵣ-ins x x₁ x₂) (Empty-ins x₃) = ⊥-elim (WF.Empty≢Σⱼ (sym A≡B))
  transConv↓Term A≡B (Σᵣ-ins x x₁ x₂) (Unit-ins x₃) = ⊥-elim (WF.Unit≢Σⱼ (sym A≡B))
  transConv↓Term A≡B (Σᵣ-ins x x₁ x₂) (ne-ins x₃ x₄ x₅ x₆) = ⊥-elim (WF.Σ≢ne x₅ A≡B)
  transConv↓Term A≡B (Σᵣ-ins x x₁ x₂) (univ x₃ x₄ x₅) = ⊥-elim (WF.U≢Σ (sym A≡B))
  transConv↓Term A≡B (Σᵣ-ins x x₁ x₂) (η-eq x₃ x₄ x₅ x₆ x₇) = ⊥-elim (WF.Π≢Σⱼ (sym A≡B))
  transConv↓Term A≡B (Σᵣ-ins x x₁ x₂) (Σ-η x₃ x₄ x₅ x₆ x₇ x₈) = ⊥-elim (WF.Σₚ≢Σᵣⱼ (sym A≡B))
  transConv↓Term A≡B (Σᵣ-ins x x₁ x₂) (η-unit x₃ x₄ x₅ x₆) = ⊥-elim (⊥-elim (WF.Unit≢Σⱼ (sym A≡B)))
  transConv↓Term A≡B (ne-ins t u x x₁) (ℕ-ins x₂) = ⊥-elim (WF.ℕ≢ne x (sym A≡B))
  transConv↓Term A≡B (ne-ins t u x x₁) (Empty-ins x₂) = ⊥-elim (WF.Empty≢neⱼ x (sym A≡B))
  transConv↓Term A≡B (ne-ins t u x x₁) (Unit-ins x₂) = ⊥-elim (WF.Unit≢neⱼ x (sym A≡B))
  transConv↓Term A≡B (ne-ins x x₁ x₂ x₃) (Σᵣ-ins x₄ x₅ x₆) = ⊥-elim (WF.Σ≢ne x₂ (sym A≡B))
  transConv↓Term A≡B (ne-ins t u x x₁) (univ x₃ x₄ x₅) = ⊥-elim (WF.U≢ne x (sym A≡B))
  transConv↓Term A≡B (ne-ins t u x ([~] A D whnfB ())) (suc-cong x₃)
  transConv↓Term A≡B (ne-ins t u x x₁) (prod-cong! x₂ x₃ x₄ x₅) = ⊥-elim (WF.B≢ne BΣ! x (sym A≡B))
  transConv↓Term A≡B (ne-ins t u x x₁) (η-eq x₄ x₅ y y₁ x₆) = ⊥-elim (WF.Π≢ne x (sym A≡B))
  transConv↓Term A≡B (ne-ins t u x x₁) (Σ-η x₅ x₆ x₇ x₈ x₉ x₁₀) = ⊥-elim (WF.Σ≢ne x (sym A≡B))
  transConv↓Term A≡B (ne-ins t u x x₁) (η-unit _ _ _ _) = ⊥-elim (WF.Unit≢neⱼ x (sym A≡B))
  transConv↓Term A≡B (univ x x₁ x₂) (ℕ-ins x₃) = ⊥-elim (WF.U≢ℕ A≡B)
  transConv↓Term A≡B (univ x x₁ x₂) (Empty-ins x₃) = ⊥-elim (WF.U≢Emptyⱼ A≡B)
  transConv↓Term A≡B (univ x x₁ x₂) (Unit-ins x₃) = ⊥-elim (WF.U≢Unitⱼ A≡B)
  transConv↓Term A≡B (univ x x₁ x₂) (Σᵣ-ins x₃ x₄ x₅) = ⊥-elim (WF.U≢Σ A≡B)
  transConv↓Term A≡B (univ x x₁ x₂) (ne-ins t u x₃ x₄) = ⊥-elim (WF.U≢ne x₃ A≡B)
  transConv↓Term A≡B (univ x x₁ x₂) (suc-cong x₃) = ⊥-elim (WF.U≢ℕ A≡B)
  transConv↓Term A≡B (univ x x₁ x₂) (prod-cong! x₃ x₄ x₅ x₆) = ⊥-elim (WF.U≢B BΣ! A≡B)
  transConv↓Term A≡B (univ x x₁ x₂) (η-eq x₄ x₅ y y₁ x₆) = ⊥-elim (WF.U≢Π A≡B)
  transConv↓Term A≡B (univ x₁ x₂ x₃) (Σ-η x₄ x₅ x₆ x₇ x₈ x₉) = ⊥-elim (WF.U≢Σ A≡B)
  transConv↓Term A≡B (univ x x₁ x₂) (η-unit _ _ _ _) = ⊥-elim (WF.U≢Unitⱼ A≡B)
  transConv↓Term A≡B (suc-cong x) (ℕ-ins ([~] A D whnfB ()))
  transConv↓Term A≡B (suc-cong x) (Empty-ins ([~] A D whnfB ()))
  transConv↓Term A≡B (suc-cong x) (ne-ins t u x₁ ([~] A D whnfB ()))
  transConv↓Term A≡B (suc-cong x) (univ x₁ x₂ x₃) = ⊥-elim (WF.U≢ℕ (sym A≡B))
  transConv↓Term A≡B (suc-cong x) (η-eq x₂ x₃ y y₁ x₄) = ⊥-elim (WF.ℕ≢Π A≡B)
  transConv↓Term A≡B (suc-cong x₁) (Σ-η x₂ x₃ x₄ x₅ x₆ x₇) = ⊥-elim (WF.ℕ≢Σ A≡B)
  transConv↓Term A≡B (suc-cong x) (η-unit _ _ _ _) = ⊥-elim (WF.ℕ≢Unitⱼ A≡B)
  transConv↓Term A≡B (prod-cong! x x₁ x₂ x₃) (univ x₄ x₅ x₆) = ⊥-elim (WF.U≢B BΣ! (sym A≡B))
  transConv↓Term A≡B (prod-cong! x x₁ x₂ x₃) (η-eq x₄ x₅ x₆ x₇ x₈) = ⊥-elim (WF.Π≢Σⱼ (sym A≡B))
  transConv↓Term A≡B (prod-cong! x x₁ x₂ x₃) (Σ-η x₄ x₅ x₆ x₇ x₈ x₉) = ⊥-elim (WF.Σₚ≢Σᵣⱼ (sym A≡B))
  transConv↓Term A≡B (prod-cong! x x₁ x₂ x₃) (η-unit x₄ x₅ x₆ x₇) = ⊥-elim (WF.Unit≢Σⱼ (sym A≡B))
  transConv↓Term A≡B (η-eq x₁ x₂ y y₁ x₃) (ℕ-ins x₄) = ⊥-elim (WF.ℕ≢Π (sym A≡B))
  transConv↓Term A≡B (η-eq x₁ x₂ y y₁ x₃) (Empty-ins x₄) = ⊥-elim (WF.Empty≢Πⱼ (sym A≡B))
  transConv↓Term A≡B (η-eq x₁ x₂ y y₁ x₃) (Unit-ins _) = ⊥-elim (WF.Unit≢Πⱼ (sym A≡B))
  transConv↓Term A≡B (η-eq x x₁ x₂ x₃ x₄) (Σᵣ-ins x₅ x₆ x₇) = ⊥-elim (WF.Π≢Σⱼ A≡B)
  transConv↓Term A≡B (η-eq x₁ x₂ y y₁ x₃) (ne-ins t u x₄ x₅) = ⊥-elim (WF.Π≢ne x₄ A≡B)
  transConv↓Term A≡B (η-eq x₁ x₂ y y₁ x₃) (univ x₄ x₅ x₆) = ⊥-elim (WF.U≢Π (sym A≡B))
  transConv↓Term A≡B (η-eq x₁ x₂ y y₁ x₃) (suc-cong x₄) = ⊥-elim (WF.ℕ≢Π (sym A≡B))
  transConv↓Term A≡B (η-eq x x₁ x₂ x₃ x₄) (prod-cong! x₅ x₆ x₇ x₈) = ⊥-elim (WF.Π≢Σⱼ A≡B)
  transConv↓Term A≡B (η-eq x₂ x₃ x₄ x₅ x₆) (Σ-η x₇ x₈ x₉ x₁₀ x₁₁ x₁₂) = ⊥-elim (WF.Π≢Σⱼ A≡B)
  transConv↓Term A≡B (η-eq x₁ x₂ y y₁ x₃) (η-unit _ _ _ _) = ⊥-elim (WF.Unit≢Πⱼ (sym A≡B))
  transConv↓Term A≡B (Σ-η x₁ x₂ x₃ x₄ x₅ x₆) (ℕ-ins x₇) = ⊥-elim (WF.ℕ≢Σ (sym A≡B))
  transConv↓Term A≡B (Σ-η x₁ x₂ x₃ x₄ x₅ x₆) (Empty-ins x₇) = ⊥-elim (WF.Empty≢Σⱼ (sym A≡B))
  transConv↓Term A≡B (Σ-η x₁ x₂ x₃ x₄ x₅ x₆) (Unit-ins x₇) = ⊥-elim (WF.Unit≢Σⱼ (sym A≡B))
  transConv↓Term A≡B (Σ-η x x₁ x₂ x₃ x₄ x₅) (Σᵣ-ins x₆ x₇ x₈) = ⊥-elim (WF.Σₚ≢Σᵣⱼ A≡B)
  transConv↓Term A≡B (Σ-η x₁ x₂ x₃ x₄ x₅ x₆) (ne-ins x₇ x₈ x₉ x₁₀) = ⊥-elim (WF.Σ≢ne x₉ A≡B)
  transConv↓Term A≡B (Σ-η x₁ x₂ x₃ x₄ x₅ x₆) (univ x₇ x₈ x₉) = ⊥-elim (WF.U≢Σ (sym A≡B))
  transConv↓Term A≡B (Σ-η x₁ x₂ x₃ x₄ x₅ x₆) (suc-cong x₇) = ⊥-elim (WF.ℕ≢Σ (sym A≡B))
  transConv↓Term A≡B (Σ-η x x₁ x₂ x₃ x₄ x₅) (prod-cong! x₆ x₇ x₈ x₉) = ⊥-elim (WF.Σₚ≢Σᵣⱼ A≡B)
  transConv↓Term A≡B (Σ-η x₁ x₂ x₃ x₄ x₅ x₆) (η-unit x₇ x₈ x₉ x₁₀) = ⊥-elim (WF.Unit≢Σⱼ (sym A≡B))
  transConv↓Term A≡B (Σ-η x₁ x₂ x₃ x₄ x₅ x₆) (η-eq x₈ x₉ x₁₀ x₁₁ x₁₂) = ⊥-elim (WF.Π≢Σⱼ (sym A≡B))
  transConv↓Term A≡B (Σᵣ-ins x x₁ ()) (suc-cong x₃)
  transConv↓Term A≡B (Σᵣ-ins x x₁ ()) (prod-cong! x₃ x₄ x₅ x₆)
  transConv↓Term A≡B (suc-cong x) (Unit-ins ())
  transConv↓Term A≡B (suc-cong x) (Σᵣ-ins x₁ x₂ ())
  transConv↓Term A≡B (prod-cong! x x₁ x₂ x₃) (ℕ-ins ())
  transConv↓Term A≡B (prod-cong! x x₁ x₂ x₃) (Empty-ins ())
  transConv↓Term A≡B (prod-cong! x x₁ x₂ x₃) (Unit-ins ())
  transConv↓Term A≡B (prod-cong! x x₁ x₂ x₃) (Σᵣ-ins x₄ x₅ ())
  transConv↓Term A≡B (prod-cong! x x₁ x₂ x₃) (ne-ins x₄ x₅ x₆ ())

-- Transitivity of algorithmic equality of types of the same context.
transConv : ∀ {A B C}
          → Γ ⊢ A [conv↑] B
          → Γ ⊢ B [conv↑] C
          → Γ ⊢ A [conv↑] C
transConv A<>B B<>C = transConv↑ A<>B B<>C

-- Transitivity of algorithmic equality of terms of the same context.
transConvTerm : ∀ {t u v A}
              → Γ ⊢ t [conv↑] u ∷ A
              → Γ ⊢ u [conv↑] v ∷ A
              → Γ ⊢ t [conv↑] v ∷ A
transConvTerm t<>u u<>v =
  let t≡u = soundnessConv↑Term t<>u
      ⊢A , _ , _ = syntacticEqTerm t≡u
  in  transConv↑Term (refl ⊢A) t<>u u<>v
