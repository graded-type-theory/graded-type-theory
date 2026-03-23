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
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed R
open import Definition.Typed.EqRelInstance R using (eqRelInstance)
open import Definition.Typed.EqualityRelation.Instance R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Stability R
open import Definition.Typed.Substitution R
open import Definition.Typed.Syntactic R
open import Definition.Conversion R
open import Definition.Conversion.Soundness R
open import Definition.Conversion.Stability R
open import Definition.Conversion.Whnf R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Equality R
open import Definition.Typed.Consequences.Reduction R

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    m n : Nat
    ∇ : DCon (Term 0) m
    Δ Η : Con Term n
    Γ : Cons _ _
    A B t u : Term _

mutual
  -- Conversion of algorithmic equality.
  convConv↑Term′ :
    ∇ »⊢ Δ ≡ Η →
    ∇ » Δ ⊢ A ≡ B →
    ∇ » Δ ⊢ t [conv↑] u ∷ A →
    ∇ » Η ⊢ t [conv↑] u ∷ B
  convConv↑Term′ Δ≡Η A≡B ([↑]ₜ B₁ t′ u′ (D , _) d d′ t<>u) =
    let _ , ⊢B = syntacticEq A≡B
        B′ , whnfB′ , D′ = whNorm ⊢B
        B₁≡B′ = trans (sym (subset* D)) (trans A≡B (subset* D′))
    in  [↑]ₜ B′ t′ u′ (stabilityRed↘ Δ≡Η (D′ , whnfB′))
             (stabilityRed↘Term Δ≡Η (conv↘∷ d B₁≡B′))
             (stabilityRed↘Term Δ≡Η (conv↘∷ d′ B₁≡B′))
             (convConv↓Term′ Δ≡Η B₁≡B′ whnfB′ t<>u)

  conv~∷ :
    ∇ »⊢ Δ ≡ Η →
    ∇ » Δ ⊢ A ≡ B →
    ∇ » Δ ⊢ t ~ u ∷ A →
    ∇ » Η ⊢ t ~ u ∷ B
  conv~∷ Γ≡Δ A≡B (↑ A≡C t~u) =
    stability~∷ Γ≡Δ $ ↑ (trans (sym A≡B) A≡C) t~u

  -- Conversion of algorithmic equality with terms and types in WHNF.
  convConv↓Term′ :
    ∇ »⊢ Δ ≡ Η →
    ∇ » Δ ⊢ A ≡ B →
    Whnf ∇ B →
    ∇ » Δ ⊢ t [conv↓] u ∷ A →
    ∇ » Η ⊢ t [conv↓] u ∷ B
  convConv↓Term′ Γ≡Δ A≡B whnfB (Level-ins x) rewrite Level≡A A≡B whnfB =
    Level-ins (stabilityConv↓Level Γ≡Δ x)
  convConv↓Term′ Δ≡Η A≡B whnfB (ℕ-ins x) rewrite ℕ≡A A≡B whnfB =
    ℕ-ins (stability~↓ Δ≡Η x)
  convConv↓Term′ Δ≡Η A≡B whnfB (Empty-ins x) rewrite Empty≡A A≡B whnfB =
    Empty-ins (stability~↓ Δ≡Η x)
  convConv↓Term′ Δ≡Η A≡B B-whnf (Unitʷ-ins ok t~u)
    rewrite Unit≡A A≡B B-whnf =
    Unitʷ-ins ok (stability~↓ Δ≡Η t~u)
  convConv↓Term′ Δ≡Η  A≡B whnfB (Σʷ-ins x x₁ x₂) with Σ≡A A≡B whnfB
  ... | _ , _ , PE.refl =
    Σʷ-ins (stability Δ≡Η (conv x A≡B))
           (stability Δ≡Η (conv x₁ A≡B))
           (stability~↓ Δ≡Η x₂)
  convConv↓Term′ Δ≡Η A≡B whnfB (ne-ins t u x x₁) =
    ne-ins (stability Δ≡Η (conv t A≡B)) (stability Δ≡Η (conv u A≡B))
           (ne↑⁺ (ne≡A (ne↑ₗ x) A≡B whnfB)) (stability~↓ Δ≡Η x₁)
  convConv↓Term′ Γ≡Δ A≡B whnfB (univ x x₁ x₂) =
    case U≡A A≡B whnfB of λ {
      (_ , PE.refl) →
    let l≡k = U-injectivity A≡B
        Ul≡Uk = U-cong-⊢≡ l≡k
    in univ (stability Γ≡Δ (conv x Ul≡Uk)) (stability Γ≡Δ (conv x₁ Ul≡Uk)) (stabilityConv↓ Γ≡Δ x₂) }
  convConv↓Term′ Γ≡Δ A≡B whnfB (Lift-η ⊢t ⊢u wt wu lower≡lower) =
    case Lift≡A A≡B whnfB of λ {
      (_ , _ , PE.refl) →
    let k≡k′ , A≡A′ = Lift-injectivity A≡B
    in Lift-η
      (stability Γ≡Δ (conv ⊢t A≡B))
      (stability Γ≡Δ (conv ⊢u A≡B))
      wt wu
      (convConv↑Term′ Γ≡Δ A≡A′ lower≡lower) }
  convConv↓Term′ Δ≡Η A≡B whnfB (zero-refl x) rewrite ℕ≡A A≡B whnfB =
    let _ , ⊢Η , _ = contextConvSubst Δ≡Η
    in  zero-refl ⊢Η
  convConv↓Term′ Δ≡Η A≡B whnfB (starʷ-refl _ ok no-η)
    rewrite Unit≡A A≡B whnfB =
    let _ , ⊢Η , _ = contextConvSubst Δ≡Η
    in  starʷ-refl ⊢Η ok no-η
  convConv↓Term′ Δ≡Η A≡B whnfB (suc-cong x) rewrite ℕ≡A A≡B whnfB =
    suc-cong (stabilityConv↑Term Δ≡Η x)
  convConv↓Term′ Δ≡Η A≡B whnfB (prod-cong x₁ x₂ x₃ ok)
    with Σ≡A A≡B whnfB
  ... | F′ , G′ , PE.refl with ΠΣ-injectivity-no-equality-reflection A≡B
  ...   | F≡F′ , G≡G′ , _ , _ =
    let _ , ⊢G′ = syntacticEq G≡G′
        _ , ⊢t , _ = syntacticEqTerm (soundnessConv↑Term x₂)
        Gt≡G′t = substTypeEq G≡G′ (refl ⊢t)
    in  prod-cong (stability (Δ≡Η ∙ F≡F′) ⊢G′)
          (convConv↑Term′ Δ≡Η F≡F′ x₂) (convConv↑Term′ Δ≡Η Gt≡G′t x₃) ok
  convConv↓Term′ Δ≡Η A≡B whnfB (η-eq x₁ x₂ y y₁ x₃) with Π≡A A≡B whnfB
  convConv↓Term′ Δ≡Η A≡B whnfB (η-eq x₁ x₂ y y₁ x₃) | _ , _ , PE.refl =
    case ΠΣ-injectivity-no-equality-reflection A≡B of λ {
      (F≡F′ , G≡G′ , _ , _) →
    η-eq (stability Δ≡Η (conv x₁ A≡B))
         (stability Δ≡Η (conv x₂ A≡B))
         y y₁
         (convConv↑Term′ (Δ≡Η ∙ F≡F′) G≡G′ x₃) }
  convConv↓Term′ Δ≡Η A≡B whnfB (Σ-η ⊢p ⊢r pProd rProd fstConv sndConv)
    with Σ≡A A≡B whnfB
  ... | F , G , PE.refl with ΠΣ-injectivity-no-equality-reflection A≡B
  ...   | F≡ , G≡ , _ , _ =
    let ⊢G = proj₁ (syntacticEq G≡)
        ⊢fst = fstⱼ ⊢G ⊢p
    in  Σ-η (stability Δ≡Η (conv ⊢p A≡B))
            (stability Δ≡Η (conv ⊢r A≡B))
            pProd
            rProd
            (convConv↑Term′ Δ≡Η F≡ fstConv)
            (convConv↑Term′ Δ≡Η (substTypeEq G≡ (refl ⊢fst)) sndConv)
  convConv↓Term′ Δ≡Η A≡B whnfB (η-unit [t] [u] tUnit uUnit ok)
    rewrite Unit≡A A≡B whnfB =
    let [t] = stability Δ≡Η [t]
        [u] = stability Δ≡Η [u]
    in  η-unit [t] [u] tUnit uUnit ok
  convConv↓Term′ Δ≡Η Id-A-t-u≡B B-whnf (Id-ins ⊢v₁ v₁~v₂) =
    case Id≡Whnf Id-A-t-u≡B B-whnf of λ {
      (_ , _ , _ , PE.refl) →
    Id-ins (stability Δ≡Η (conv ⊢v₁ Id-A-t-u≡B))
      (stability~↓ Δ≡Η v₁~v₂) }
  convConv↓Term′ Δ≡Η Id-A-t-u≡B B-whnf (rfl-refl t≡u) =
    case Id≡Whnf Id-A-t-u≡B B-whnf of λ {
      (_ , _ , _ , PE.refl) →
    case Id-injectivity Id-A-t-u≡B of λ {
      (A≡A′ , t≡t′ , u≡u′) →
    rfl-refl
      (stability Δ≡Η $
       conv (trans (sym′ t≡t′) (trans t≡u u≡u′)) A≡A′) }}

-- Conversion of algorithmic equality with the same context.
convConv↑Term :
  Γ ⊢ A ≡ B →
  Γ ⊢ t [conv↑] u ∷ A →
  Γ ⊢ t [conv↑] u ∷ B
convConv↑Term A≡B = convConv↑Term′ (reflConEq (wf A≡B)) A≡B

opaque

  -- Conversion for _⊢_[conv↓]_∷_.

  convConv↓Term :
    Γ ⊢ A ≡ B →
    Whnf (Γ .defs) B →
    Γ ⊢ t [conv↓] u ∷ A →
    Γ ⊢ t [conv↓] u ∷ B
  convConv↓Term A≡B = convConv↓Term′ (reflConEq (wf A≡B)) A≡B
