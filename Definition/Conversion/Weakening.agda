{-# OPTIONS --without-K --safe #-}

open import Tools.Relation

module Definition.Conversion.Weakening {a ℓ} (M′ : Setoid a ℓ) where

open Setoid M′ using () renaming (Carrier to M)

open import Definition.Untyped M as U hiding (wk ; _∷_)
open import Definition.Untyped.Properties M
open import Definition.Typed M′
open import Definition.Typed.Weakening M′
open import Definition.Typed.Consequences.Syntactic M′
open import Definition.Conversion M′
open import Definition.Conversion.Soundness M′

open import Tools.Nat
import Tools.PropositionalEquality as PE
open import Tools.Product

private
  variable
    m n : Nat
    ρ : Wk m n
    p r : M

mutual
  -- Weakening of algorithmic equality of neutrals.
  wk~↑ : ∀ {t u A Γ Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) → ⊢ Δ
      → Γ ⊢ t ~ u ↑ A
      → Δ ⊢ U.wk ρ t ~ U.wk ρ u ↑ U.wk ρ A
  wk~↑ {ρ = ρ} [ρ] ⊢Δ (var-refl x₁ x≡y) = var-refl (wkTerm [ρ] ⊢Δ x₁) (PE.cong (wkVar ρ) x≡y)
  wk~↑ ρ ⊢Δ (app-cong {G = G} t~u x p≈p₁ p≈p₂) =
    PE.subst (λ x → _ ⊢ _ ~ _ ↑ x) (PE.sym (wk-β G))
             (app-cong (wk~↓ ρ ⊢Δ t~u) (wkConv↑Term ρ ⊢Δ x) p≈p₁ p≈p₂)
  wk~↑ ρ ⊢Δ (fst-cong p~r) =
    fst-cong (wk~↓ ρ ⊢Δ p~r)
  wk~↑ ρ ⊢Δ (snd-cong {G = G} p~r) =
    PE.subst (λ x → _ ⊢ _ ~ _ ↑ x)
             (PE.sym (wk-β G))
             (snd-cong (wk~↓ ρ ⊢Δ p~r))
  wk~↑ {ρ = ρ} {Δ = Δ} [ρ] ⊢Δ (natrec-cong {F = F} {G} {a₀} {b₀} {h} {g} {k} {l} {p} {r = r} x x₁ x₂ t~u p≈p′ r≈r′) =
    let ⊢Δℕ = ⊢Δ ∙ (ℕⱼ ⊢Δ)
        Δℕ⊢F = wk (lift [ρ]) ⊢Δℕ (proj₁ (syntacticEq (soundnessConv↑ x)))
    in  PE.subst (λ x → _ ⊢ U.wk ρ (natrec p r F a₀ h k) ~ _ ↑ x) (PE.sym (wk-β F))
                 (natrec-cong (wkConv↑ (lift [ρ]) (⊢Δ ∙ ℕⱼ ⊢Δ) x)
                              (PE.subst (λ x → _ ⊢ _ [conv↑] _ ∷ x) (wk-β F)
                                        (wkConv↑Term [ρ] ⊢Δ x₁))
                              (PE.subst (λ x → (Δ ∙ ℕ ∙ U.wk (lift ρ) F) ⊢ U.wk (lift (lift ρ)) h
                                             [conv↑] U.wk (lift (lift ρ)) g ∷ x)
                              (wk-β-natrec _ F) (wkConv↑Term (lift (lift [ρ]))
                                                             (⊢Δℕ ∙ Δℕ⊢F) x₂))
                              (wk~↓ [ρ] ⊢Δ t~u) p≈p′ r≈r′)
  wk~↑ {ρ = ρ} {Δ = Δ} [ρ] ⊢Δ (prodrec-cong {C = C} {E} {g} {h} {u} {v} {p} x g~h x₁ p≈p′) =
    let ρg~ρh = wk~↓ [ρ] ⊢Δ g~h
        ⊢ρΣ , _ , _ = syntacticEqTerm (soundness~↓ ρg~ρh)
        ⊢ρF , ⊢ρG = syntacticΣ ⊢ρΣ
        u↓v = PE.subst (λ x → _ ⊢ U.wk (liftn ρ 2) u [conv↑] U.wk (liftn ρ 2) v ∷ x)
                       (wk-β-prodrec ρ C)
                       (wkConv↑Term (lift (lift [ρ])) (⊢Δ ∙ ⊢ρF ∙ ⊢ρG) x₁)
    in  PE.subst  (λ x → _ ⊢ U.wk ρ (prodrec p C g u) ~ U.wk ρ (prodrec _ E h v) ↑ x)
                  (PE.sym (wk-β C))
                  (prodrec-cong (wkConv↑ (lift [ρ]) (⊢Δ ∙ ⊢ρΣ) x)
                                ρg~ρh u↓v p≈p′)
  wk~↑ {ρ} {Δ = Δ} [ρ] ⊢Δ (Emptyrec-cong {k} {l} {F} {G} x t~u p≈p′) =
    Emptyrec-cong (wkConv↑ [ρ] ⊢Δ x) (wk~↓ [ρ] ⊢Δ t~u) p≈p′

  -- Weakening of algorithmic equality of neutrals in WHNF.
  wk~↓ : ∀ {t u A Γ Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) → ⊢ Δ
      → Γ ⊢ t ~ u ↓ A
      → Δ ⊢ U.wk ρ t ~ U.wk ρ u ↓ U.wk ρ A
  wk~↓ {ρ = ρ} [ρ] ⊢Δ ([~] A₁ D whnfA k~l) =
    [~] (U.wk ρ A₁) (wkRed* [ρ] ⊢Δ D) (wkWhnf ρ whnfA) (wk~↑ [ρ] ⊢Δ k~l)

  -- Weakening of algorithmic equality of types.
  wkConv↑ : ∀ {A B Γ Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) → ⊢ Δ
          → Γ ⊢ A [conv↑] B
          → Δ ⊢ U.wk ρ A [conv↑] U.wk ρ B
  wkConv↑ {ρ = ρ} [ρ] ⊢Δ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) =
    [↑] (U.wk ρ A′) (U.wk ρ B′) (wkRed* [ρ] ⊢Δ D) (wkRed* [ρ] ⊢Δ D′)
        (wkWhnf ρ whnfA′) (wkWhnf ρ whnfB′) (wkConv↓ [ρ] ⊢Δ A′<>B′)

  -- Weakening of algorithmic equality of types in WHNF.
  wkConv↓ : ∀ {A B Γ Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) → ⊢ Δ
         → Γ ⊢ A [conv↓] B
         → Δ ⊢ U.wk ρ A [conv↓] U.wk ρ B
  wkConv↓ ρ ⊢Δ (U-refl x) = U-refl ⊢Δ
  wkConv↓ ρ ⊢Δ (ℕ-refl x) = ℕ-refl ⊢Δ
  wkConv↓ ρ ⊢Δ (Empty-refl x) = Empty-refl ⊢Δ
  wkConv↓ ρ ⊢Δ (Unit-refl x) = Unit-refl ⊢Δ
  wkConv↓ ρ ⊢Δ (ne x) = ne (wk~↓ ρ ⊢Δ x)
  wkConv↓ ρ ⊢Δ (Π-cong x A<>B A<>B₁ p≈p′ q≈q′) =
    let ⊢ρF = wk ρ ⊢Δ x
    in  Π-cong ⊢ρF (wkConv↑ ρ ⊢Δ A<>B) (wkConv↑ (lift ρ) (⊢Δ ∙ ⊢ρF) A<>B₁) p≈p′ q≈q′
  wkConv↓ ρ ⊢Δ (Σ-cong x A<>B A<>B₁ q≈q′) =
    let ⊢ρF = wk ρ ⊢Δ x
    in  Σ-cong ⊢ρF (wkConv↑ ρ ⊢Δ A<>B) (wkConv↑ (lift ρ) (⊢Δ ∙ ⊢ρF) A<>B₁) q≈q′

  -- Weakening of algorithmic equality of terms.
  wkConv↑Term : ∀ {t u A Γ Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) → ⊢ Δ
             → Γ ⊢ t [conv↑] u ∷ A
             → Δ ⊢ U.wk ρ t [conv↑] U.wk ρ u ∷ U.wk ρ A
  wkConv↑Term {ρ = ρ} [ρ] ⊢Δ ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) =
    [↑]ₜ (U.wk ρ B) (U.wk ρ t′) (U.wk ρ u′)
         (wkRed* [ρ] ⊢Δ D) (wkRed*Term [ρ] ⊢Δ d) (wkRed*Term [ρ] ⊢Δ d′)
         (wkWhnf ρ whnfB) (wkWhnf ρ whnft′) (wkWhnf ρ whnfu′)
         (wkConv↓Term [ρ] ⊢Δ t<>u)

  -- Weakening of algorithmic equality of terms in WHNF.
  wkConv↓Term : ∀ {t u A Γ Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) → ⊢ Δ
             → Γ ⊢ t [conv↓] u ∷ A
             → Δ ⊢ U.wk ρ t [conv↓] U.wk ρ u ∷ U.wk ρ A
  wkConv↓Term ρ ⊢Δ (ℕ-ins x) =
    ℕ-ins (wk~↓ ρ ⊢Δ x)
  wkConv↓Term ρ ⊢Δ (Empty-ins x) =
    Empty-ins (wk~↓ ρ ⊢Δ x)
  wkConv↓Term ρ ⊢Δ (Unit-ins x) =
    Unit-ins (wk~↓ ρ ⊢Δ x)
  wkConv↓Term ρ ⊢Δ (Σᵣ-ins t u x) =
    Σᵣ-ins (wkTerm ρ ⊢Δ t) (wkTerm ρ ⊢Δ u) (wk~↓ ρ ⊢Δ x)
  wkConv↓Term {ρ = ρ} [ρ] ⊢Δ (ne-ins t u x x₁) =
    ne-ins (wkTerm [ρ] ⊢Δ t) (wkTerm [ρ] ⊢Δ u) (wkNeutral ρ x) (wk~↓ [ρ] ⊢Δ x₁)
  wkConv↓Term ρ ⊢Δ (univ x x₁ x₂) =
    univ (wkTerm ρ ⊢Δ x) (wkTerm ρ ⊢Δ x₁) (wkConv↓ ρ ⊢Δ x₂)
  wkConv↓Term ρ ⊢Δ (zero-refl x) = zero-refl ⊢Δ
  wkConv↓Term ρ ⊢Δ (suc-cong t<>u) = suc-cong (wkConv↑Term ρ ⊢Δ t<>u)
  wkConv↓Term ρ ⊢Δ (prod-cong {G = G} x x₁ x₂ x₃) =
    let ⊢ρF = wk ρ ⊢Δ x
        ⊢ρG = wk (lift ρ) (⊢Δ ∙ ⊢ρF) x₁
    in  prod-cong ⊢ρF ⊢ρG (wkConv↑Term ρ ⊢Δ x₂)
                  (PE.subst (λ x → _ ⊢ _ [conv↑] _ ∷ x) (wk-β G) (wkConv↑Term ρ ⊢Δ x₃))
  wkConv↓Term {ρ = ρ} {Δ = Δ} [ρ] ⊢Δ (η-eq {F = F} {G = G} x₁ x₂ y y₁ t<>u) =
    let ⊢F , _ = syntacticΠ (syntacticTerm x₁)
        ⊢ρF = wk [ρ] ⊢Δ ⊢F
    in  η-eq (wkTerm [ρ] ⊢Δ x₁) (wkTerm [ρ] ⊢Δ x₂)
             (wkFunction ρ y) (wkFunction ρ y₁)
             λ x x₃ → (PE.subst₃ (λ x y z → Δ ∙ U.wk ρ F ⊢ x [conv↑] y ∷ z)
                                 (PE.cong₃ _∘_▷_ (PE.sym (wk1-wk≡lift-wk1 _ _)) PE.refl PE.refl)
                                 (PE.cong₃ _∘_▷_ (PE.sym (wk1-wk≡lift-wk1 _ _)) PE.refl PE.refl)
                                 PE.refl
                                 (wkConv↑Term (lift [ρ]) (⊢Δ ∙ ⊢ρF) (t<>u x x₃)))
  wkConv↓Term {ρ = ρ} [ρ] ⊢Δ (Σ-η {G = G} ⊢p ⊢r pProd rProd fstConv sndConv) =
    Σ-η (wkTerm [ρ] ⊢Δ ⊢p)
        (wkTerm [ρ] ⊢Δ ⊢r)
        (wkProduct ρ pProd)
        (wkProduct ρ rProd)
        (wkConv↑Term [ρ] ⊢Δ fstConv)
        (PE.subst (λ x → _ ⊢ _ [conv↑] _ ∷ x)
                  (wk-β G)
                  (wkConv↑Term [ρ] ⊢Δ sndConv))
  wkConv↓Term {ρ = ρ} [ρ] ⊢Δ (η-unit [t] [u] tWhnf uWhnf) =
    η-unit (wkTerm [ρ] ⊢Δ [t]) (wkTerm [ρ] ⊢Δ [u])
           (wkWhnf ρ tWhnf) (wkWhnf ρ uWhnf)
