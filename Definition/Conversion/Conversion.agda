------------------------------------------------------------------------
-- Type conversion lemmata for the algorithmic equality relations.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions

module Definition.Conversion.Conversion
  {a} {M : Set a}
  (R : Type-restrictions M)
  where

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed R
open import Definition.Typed.RedSteps R
open import Definition.Typed.Properties R
open import Definition.Conversion R
open import Definition.Conversion.Soundness R
open import Definition.Conversion.Stability R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Equality R
open import Definition.Typed.Consequences.Reduction R

open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE using (≈-sym; ≈-trans)

private
  variable
    n : Nat
    Γ Δ : Con Term n

mutual
  -- Conversion of algorithmic equality.
  convConv↑Term : ∀ {t u A B}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B
                → Γ ⊢ t [conv↑] u ∷ A
                → Δ ⊢ t [conv↑] u ∷ B
  convConv↑Term Γ≡Δ A≡B ([↑]ₜ B₁ t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) =
    let _ , ⊢B = syntacticEq A≡B
        B′ , whnfB′ , D′ = whNorm ⊢B
        B₁≡B′ = trans (sym (subset* D)) (trans A≡B (subset* (red D′)))
    in  [↑]ₜ B′ t′ u′ (stabilityRed* Γ≡Δ (red D′))
             (stabilityRed*Term Γ≡Δ (conv* d B₁≡B′))
             (stabilityRed*Term Γ≡Δ (conv* d′ B₁≡B′)) whnfB′ whnft′ whnfu′
             (convConv↓Term Γ≡Δ B₁≡B′ whnfB′ t<>u)

  -- Conversion of algorithmic equality with terms and types in WHNF.
  convConv↓Term : ∀ {t u A B}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B
                → Whnf B
                → Γ ⊢ t [conv↓] u ∷ A
                → Δ ⊢ t [conv↓] u ∷ B
  convConv↓Term Γ≡Δ A≡B whnfB (ℕ-ins x) rewrite ℕ≡A A≡B whnfB =
    ℕ-ins (stability~↓ Γ≡Δ x)
  convConv↓Term Γ≡Δ A≡B whnfB (Empty-ins x) rewrite Empty≡A A≡B whnfB =
    Empty-ins (stability~↓ Γ≡Δ x)
  convConv↓Term Γ≡Δ A≡B whnfB (Unit-ins x) rewrite Unit≡A A≡B whnfB =
    Unit-ins (stability~↓ Γ≡Δ x)
  convConv↓Term Γ≡Δ  A≡B whnfB (Σᵣ-ins x x₁ x₂) with Σ≡A A≡B whnfB
  ... | _ , _ , PE.refl =
    Σᵣ-ins (stabilityTerm Γ≡Δ (conv x A≡B))
           (stabilityTerm Γ≡Δ (conv x₁ A≡B))
           (stability~↓ Γ≡Δ x₂)
  convConv↓Term Γ≡Δ A≡B whnfB (ne-ins t u x x₁) with ne≡A x A≡B whnfB
  convConv↓Term Γ≡Δ A≡B whnfB (ne-ins t u x x₁) | B , neB , PE.refl =
    ne-ins (stabilityTerm Γ≡Δ (conv t A≡B)) (stabilityTerm Γ≡Δ (conv u A≡B))
           neB (stability~↓ Γ≡Δ x₁)
  convConv↓Term Γ≡Δ A≡B whnfB (univ x x₁ x₂) rewrite U≡A A≡B =
    univ (stabilityTerm Γ≡Δ x) (stabilityTerm Γ≡Δ x₁) (stabilityConv↓ Γ≡Δ x₂)
  convConv↓Term Γ≡Δ A≡B whnfB (zero-refl x) rewrite ℕ≡A A≡B whnfB =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  zero-refl ⊢Δ
  convConv↓Term Γ≡Δ A≡B whnfB (suc-cong x) rewrite ℕ≡A A≡B whnfB =
    suc-cong (stabilityConv↑Term Γ≡Δ x)
  convConv↓Term Γ≡Δ A≡B whnfB (prod-cong x x₁ x₂ x₃)
    with Σ≡A A≡B whnfB
  ... | F′ , G′ , PE.refl with Σ-injectivity A≡B
  ...   | F≡F′ , G≡G′ , _ , _ =
    let _ , ⊢F′ = syntacticEq F≡F′
        _ , ⊢G′ = syntacticEq G≡G′
        _ , ⊢t , _ = syntacticEqTerm (soundnessConv↑Term x₂)
        Gt≡G′t = substTypeEq G≡G′ (refl ⊢t)
    in  prod-cong (stability Γ≡Δ ⊢F′) (stability (Γ≡Δ ∙ F≡F′) ⊢G′)
          (convConv↑Term Γ≡Δ F≡F′ x₂) (convConv↑Term Γ≡Δ Gt≡G′t x₃)
  convConv↓Term Γ≡Δ A≡B whnfB (η-eq x₁ x₂ y y₁ x₃) with Π≡A A≡B whnfB
  convConv↓Term Γ≡Δ A≡B whnfB (η-eq x₁ x₂ y y₁ x₃) | F′ , G′ , PE.refl =
    case injectivity A≡B of λ {
      (F≡F′ , G≡G′ , _ , _) →
    η-eq (stabilityTerm Γ≡Δ (conv x₁ A≡B))
         (stabilityTerm Γ≡Δ (conv x₂ A≡B))
         y y₁
         (convConv↑Term (Γ≡Δ ∙ F≡F′) G≡G′ x₃) }
  convConv↓Term Γ≡Δ A≡B whnfB (Σ-η ⊢p ⊢r pProd rProd fstConv sndConv)
    with Σ≡A A≡B whnfB
  ... | F , G , PE.refl with Σ-injectivity A≡B
  ...   | F≡ , G≡ , _ , _ =
    let ⊢F = proj₁ (syntacticEq F≡)
        ⊢G = proj₁ (syntacticEq G≡)
        ⊢fst = fstⱼ ⊢F ⊢G ⊢p
    in  Σ-η (stabilityTerm Γ≡Δ (conv ⊢p A≡B))
            (stabilityTerm Γ≡Δ (conv ⊢r A≡B))
            pProd
            rProd
            (convConv↑Term Γ≡Δ F≡ fstConv)
            (convConv↑Term Γ≡Δ (substTypeEq G≡ (refl ⊢fst)) sndConv)
  convConv↓Term Γ≡Δ A≡B whnfB (η-unit [t] [u] tUnit uUnit) rewrite Unit≡A A≡B whnfB =
    let [t] = stabilityTerm Γ≡Δ [t]
        [u] = stabilityTerm Γ≡Δ [u]
    in  η-unit [t] [u] tUnit uUnit

-- Conversion of algorithmic equality with the same context.
convConvTerm : ∀ {t u A B}
              → Γ ⊢ t [conv↑] u ∷ A
              → Γ ⊢ A ≡ B
              → Γ ⊢ t [conv↑] u ∷ B
convConvTerm t<>u A≡B = convConv↑Term (reflConEq (wfEq A≡B)) A≡B t<>u
