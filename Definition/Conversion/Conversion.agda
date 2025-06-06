------------------------------------------------------------------------
-- Type conversion lemmata for the algorithmic equality relations.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Conversion.Conversion
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  -- Equality reflection is not allowed.
  ⦃ no-equality-reflection : No-equality-reflection ⦄
  where

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Typed R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.EqualityRelation.Instance R
open import Definition.Typed.Properties R
open import Definition.Typed.Stability R
open import Definition.Typed.Substitution R
open import Definition.Typed.Syntactic R
open import Definition.Conversion R
open import Definition.Conversion.Soundness R
open import Definition.Conversion.Stability R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Equality R
open import Definition.Typed.Consequences.Reduction R

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ Δ : Con Term n
    A B t u : Term _

mutual
  -- Conversion of algorithmic equality.
  convConv↑Term′ :
    ⊢ Γ ≡ Δ →
    Γ ⊢ A ≡ B →
    Γ ⊢ t [conv↑] u ∷ A →
    Δ ⊢ t [conv↑] u ∷ B
  convConv↑Term′ Γ≡Δ A≡B ([↑]ₜ B₁ t′ u′ (D , _) d d′ t<>u) =
    let _ , ⊢B = syntacticEq A≡B
        B′ , whnfB′ , D′ = whNorm ⊢B
        B₁≡B′ = trans (sym (subset* D)) (trans A≡B (subset* D′))
    in  [↑]ₜ B′ t′ u′ (stabilityRed↘ Γ≡Δ (D′ , whnfB′))
             (stabilityRed↘Term Γ≡Δ (conv↘∷ d B₁≡B′))
             (stabilityRed↘Term Γ≡Δ (conv↘∷ d′ B₁≡B′))
             (convConv↓Term′ Γ≡Δ B₁≡B′ whnfB′ t<>u)

  -- Conversion of algorithmic equality with terms and types in WHNF.
  convConv↓Term′ :
    ⊢ Γ ≡ Δ →
    Γ ⊢ A ≡ B →
    Whnf B →
    Γ ⊢ t [conv↓] u ∷ A →
    Δ ⊢ t [conv↓] u ∷ B
  convConv↓Term′ Γ≡Δ A≡B whnfB (ℕ-ins x) rewrite ℕ≡A A≡B whnfB =
    ℕ-ins (stability~↓ Γ≡Δ x)
  convConv↓Term′ Γ≡Δ A≡B whnfB (Empty-ins x) rewrite Empty≡A A≡B whnfB =
    Empty-ins (stability~↓ Γ≡Δ x)
  convConv↓Term′ Γ≡Δ A≡B B-whnf (Unitʷ-ins ok t~u)
    rewrite Unit≡A A≡B B-whnf =
    Unitʷ-ins ok (stability~↓ Γ≡Δ t~u)
  convConv↓Term′ Γ≡Δ  A≡B whnfB (Σʷ-ins x x₁ x₂) with Σ≡A A≡B whnfB
  ... | _ , _ , PE.refl =
    Σʷ-ins (stabilityTerm Γ≡Δ (conv x A≡B))
           (stabilityTerm Γ≡Δ (conv x₁ A≡B))
           (stability~↓ Γ≡Δ x₂)
  convConv↓Term′ Γ≡Δ A≡B whnfB (ne-ins t u x x₁) =
    ne-ins (stabilityTerm Γ≡Δ (conv t A≡B)) (stabilityTerm Γ≡Δ (conv u A≡B))
           (ne≡A x A≡B whnfB) (stability~↓ Γ≡Δ x₁)
  convConv↓Term′ Γ≡Δ A≡B whnfB (univ x x₁ x₂) rewrite U≡A A≡B whnfB =
    univ (stabilityTerm Γ≡Δ x) (stabilityTerm Γ≡Δ x₁) (stabilityConv↓ Γ≡Δ x₂)
  convConv↓Term′ Γ≡Δ A≡B whnfB (zero-refl x) rewrite ℕ≡A A≡B whnfB =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  zero-refl ⊢Δ
  convConv↓Term′ Γ≡Δ A≡B whnfB (starʷ-refl _ ok no-η)
    rewrite Unit≡A A≡B whnfB =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  starʷ-refl ⊢Δ ok no-η
  convConv↓Term′ Γ≡Δ A≡B whnfB (suc-cong x) rewrite ℕ≡A A≡B whnfB =
    suc-cong (stabilityConv↑Term Γ≡Δ x)
  convConv↓Term′ Γ≡Δ A≡B whnfB (prod-cong x₁ x₂ x₃ ok)
    with Σ≡A A≡B whnfB
  ... | F′ , G′ , PE.refl with ΠΣ-injectivity-no-equality-reflection A≡B
  ...   | F≡F′ , G≡G′ , _ , _ =
    let _ , ⊢G′ = syntacticEq G≡G′
        _ , ⊢t , _ = syntacticEqTerm (soundnessConv↑Term x₂)
        Gt≡G′t = substTypeEq G≡G′ (refl ⊢t)
    in  prod-cong (stability (Γ≡Δ ∙ F≡F′) ⊢G′)
          (convConv↑Term′ Γ≡Δ F≡F′ x₂) (convConv↑Term′ Γ≡Δ Gt≡G′t x₃) ok
  convConv↓Term′ Γ≡Δ A≡B whnfB (η-eq x₁ x₂ y y₁ x₃) with Π≡A A≡B whnfB
  convConv↓Term′ Γ≡Δ A≡B whnfB (η-eq x₁ x₂ y y₁ x₃) | _ , _ , PE.refl =
    case ΠΣ-injectivity-no-equality-reflection A≡B of λ {
      (F≡F′ , G≡G′ , _ , _) →
    η-eq (stabilityTerm Γ≡Δ (conv x₁ A≡B))
         (stabilityTerm Γ≡Δ (conv x₂ A≡B))
         y y₁
         (convConv↑Term′ (Γ≡Δ ∙ F≡F′) G≡G′ x₃) }
  convConv↓Term′ Γ≡Δ A≡B whnfB (Σ-η ⊢p ⊢r pProd rProd fstConv sndConv)
    with Σ≡A A≡B whnfB
  ... | F , G , PE.refl with ΠΣ-injectivity-no-equality-reflection A≡B
  ...   | F≡ , G≡ , _ , _ =
    let ⊢G = proj₁ (syntacticEq G≡)
        ⊢fst = fstⱼ ⊢G ⊢p
    in  Σ-η (stabilityTerm Γ≡Δ (conv ⊢p A≡B))
            (stabilityTerm Γ≡Δ (conv ⊢r A≡B))
            pProd
            rProd
            (convConv↑Term′ Γ≡Δ F≡ fstConv)
            (convConv↑Term′ Γ≡Δ (substTypeEq G≡ (refl ⊢fst)) sndConv)
  convConv↓Term′ Γ≡Δ A≡B whnfB (η-unit [t] [u] tUnit uUnit ok)
    rewrite Unit≡A A≡B whnfB =
    let [t] = stabilityTerm Γ≡Δ [t]
        [u] = stabilityTerm Γ≡Δ [u]
    in  η-unit [t] [u] tUnit uUnit ok
  convConv↓Term′ Γ≡Δ Id-A-t-u≡B B-whnf (Id-ins ⊢v₁ v₁~v₂) =
    case Id≡Whnf Id-A-t-u≡B B-whnf of λ {
      (_ , _ , _ , PE.refl) →
    Id-ins (stabilityTerm Γ≡Δ (conv ⊢v₁ Id-A-t-u≡B))
      (stability~↓ Γ≡Δ v₁~v₂) }
  convConv↓Term′ Γ≡Δ Id-A-t-u≡B B-whnf (rfl-refl t≡u) =
    case Id≡Whnf Id-A-t-u≡B B-whnf of λ {
      (_ , _ , _ , PE.refl) →
    case Id-injectivity Id-A-t-u≡B of λ {
      (A≡A′ , t≡t′ , u≡u′) →
    rfl-refl
      (stabilityEqTerm Γ≡Δ $
       conv (trans (sym′ t≡t′) (trans t≡u u≡u′)) A≡A′) }}

-- Conversion of algorithmic equality with the same context.
convConv↑Term :
  Γ ⊢ A ≡ B →
  Γ ⊢ t [conv↑] u ∷ A →
  Γ ⊢ t [conv↑] u ∷ B
convConv↑Term A≡B = convConv↑Term′ (reflConEq (wfEq A≡B)) A≡B

opaque

  -- Conversion for _⊢_[conv↓]_∷_.

  convConv↓Term :
    Γ ⊢ A ≡ B →
    Whnf B →
    Γ ⊢ t [conv↓] u ∷ A →
    Γ ⊢ t [conv↓] u ∷ B
  convConv↓Term A≡B = convConv↓Term′ (reflConEq (wfEq A≡B)) A≡B
