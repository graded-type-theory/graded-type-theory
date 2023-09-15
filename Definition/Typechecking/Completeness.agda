------------------------------------------------------------------------
-- Completeness of the bi-directional typechecking relations.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions

module Definition.Typechecking.Completeness
  {a} {M : Set a}
  (R : Type-restrictions M)
  where

open import Definition.Typechecking R
open import Definition.Typechecking.Soundness R
open import Definition.Typed R
open import Definition.Typed.Properties R
import Definition.Typed.Weakening R as W
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Reduction R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Consequences.Stability R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Untyped M hiding (_∷_)

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n
    t u A B : Term n

-- Bi-directional type checking relations are complete with respect to
-- their corresponding typing relations for Inferable/Checkable terms

mutual

  -- Completeness of checking for types

  completeness⇇Type : Checkable A → Γ ⊢ A → Γ ⊢ A ⇇Type
  completeness⇇Type A (Uⱼ x) = Uᶜ
  completeness⇇Type A (ℕⱼ x) = ℕᶜ
  completeness⇇Type A (Emptyⱼ x) = Emptyᶜ
  completeness⇇Type A (Unitⱼ x ok) = Unitᶜ ok
  completeness⇇Type (infᶜ (ΠΣᵢ F G)) (ΠΣⱼ ⊢F ⊢G ok) =
    ΠΣᶜ (completeness⇇Type F ⊢F) (completeness⇇Type G ⊢G) ok
  completeness⇇Type A (univ x) = univᶜ (completeness⇇ A x)

  -- Completeness of type inference

  completeness⇉ : Inferable t → Γ ⊢ t ∷ A → ∃ λ B → Γ ⊢ t ⇉ B × Γ ⊢ A ≡ B
  completeness⇉ Uᵢ ⊢t = ⊥-elim (inversion-U ⊢t)
  completeness⇉ (ΠΣᵢ F G) ⊢t =
    let ⊢F , ⊢G , A≡U , ok = inversion-ΠΣ-U ⊢t
        F⇇U = completeness⇇ F ⊢F
        G⇇U = completeness⇇ G ⊢G
    in  _ , ΠΣᵢ F⇇U G⇇U ok , A≡U
  completeness⇉ varᵢ ⊢t =
    let B , x∷B∈Γ , A≡B = inversion-var ⊢t
    in  _ , varᵢ x∷B∈Γ , A≡B
  completeness⇉ (∘ᵢ t u) ⊢tu =
    let F , G , q , ⊢t , ⊢u , A≡Gu = inversion-app ⊢tu
        B , t⇉B , ΠFG≡B = completeness⇉ t ⊢t
        F′ , G′ , B⇒Π′ , F≡F′ , G≡G′ = ΠNorm (proj₁ (soundness⇉ (wfTerm ⊢t) t⇉B)) (sym ΠFG≡B)
        ⊢u′ = conv ⊢u F≡F′
        u⇇G = completeness⇇ u ⊢u′
    in  _ , appᵢ t⇉B (B⇒Π′ , ΠΣₙ) u⇇G , trans A≡Gu (substTypeEq G≡G′ (refl ⊢u))
  completeness⇉ (fstᵢ t) ⊢t =
    let F , G , q , ⊢F , ⊢G , ⊢t , A≡F = inversion-fst ⊢t
        B , t⇉B , ΣFG≡B = completeness⇉ t ⊢t
        F′ , G′ , B⇒Σ′ , F≡F′ , G≡G′ = ΣNorm (proj₁ (soundness⇉ (wfTerm ⊢t) t⇉B)) (sym ΣFG≡B)
    in  _ , fstᵢ t⇉B (B⇒Σ′ , ΠΣₙ) , trans A≡F F≡F′
  completeness⇉ (sndᵢ t) ⊢t =
    let F , G , q , ⊢F , ⊢G , ⊢t , A≡Gt = inversion-snd ⊢t
        B , t⇉B , ΣFG≡B = completeness⇉ t ⊢t
        F′ , G′ , B⇒Σ′ , F≡F′ , G≡G′ = ΣNorm (proj₁ (soundness⇉ (wfTerm ⊢t) t⇉B)) (sym ΣFG≡B)
    in  _ , sndᵢ t⇉B (B⇒Σ′ , ΠΣₙ) , trans A≡Gt (substTypeEq G≡G′ (refl (fstⱼ ⊢F ⊢G ⊢t)))
  completeness⇉ (prodrecᵢ C t u) ⊢t =
    let F , G , q , ⊢F , ⊢G , ⊢C , ⊢t , ⊢u , A≡Ct = inversion-prodrec ⊢t
        ok = ⊢∷ΠΣ→ΠΣ-allowed ⊢t
        B , t⇉B , ΣFG≡B = completeness⇉ t ⊢t
        F′ , G′ , B⇒Σ′ , F≡F′ , G≡G′ = ΣNorm (proj₁ (soundness⇉ (wfTerm ⊢t) t⇉B)) (sym ΣFG≡B)
        u⇇C₊ = completeness⇇ u (stabilityTerm ((reflConEq (wf ⊢F)) ∙ F≡F′ ∙ G≡G′) ⊢u)
        C⇇Type = completeness⇇Type C $
                 stability
                   (reflConEq (wf ⊢F) ∙ ΠΣ-cong ⊢F F≡F′ G≡G′ ok) ⊢C
    in  _ , prodrecᵢ C⇇Type t⇉B (B⇒Σ′ , ΠΣₙ) u⇇C₊ , A≡Ct
  completeness⇉ ℕᵢ ⊢t = _ , ℕᵢ , inversion-ℕ ⊢t
  completeness⇉ zeroᵢ ⊢t = _ , zeroᵢ , inversion-zero ⊢t
  completeness⇉ (sucᵢ t) ⊢t =
    let ⊢t , A≡ℕ = inversion-suc ⊢t
        t⇇ℕ = completeness⇇ t ⊢t
    in  _ , sucᵢ t⇇ℕ , A≡ℕ
  completeness⇉ (natrecᵢ C z s n) ⊢t =
    let ⊢C , ⊢z , ⊢s , ⊢n , A≡Cn = inversion-natrec ⊢t
        z⇇C₀ = completeness⇇ z ⊢z
        s⇇C₊ = completeness⇇ s ⊢s
        n⇇ℕ = completeness⇇ n ⊢n
        C⇇Type = completeness⇇Type C ⊢C
    in  _ , natrecᵢ C⇇Type z⇇C₀ s⇇C₊ n⇇ℕ , A≡Cn
  completeness⇉ Unitᵢ ⊢t =
    case inversion-Unit-U ⊢t of λ {
      (≡U , ok) →
    _ , Unitᵢ ok , ≡U }
  completeness⇉ starᵢ ⊢t =
    case inversion-star ⊢t of λ {
      (≡Unit , ok) →
    _ , starᵢ ok , ≡Unit }
  completeness⇉ Emptyᵢ ⊢t = _ , Emptyᵢ , inversion-Empty ⊢t
  completeness⇉ (emptyrecᵢ C t) ⊢t =
    let ⊢C , ⊢t , A≡C = inversion-emptyrec ⊢t
        t⇇Empty = completeness⇇ t ⊢t
        C⇇Type = completeness⇇Type C ⊢C
    in  _ , emptyrecᵢ C⇇Type t⇇Empty , A≡C

  -- Completeness of type checking

  completeness⇇ : Checkable t → Γ ⊢ t ∷ A → Γ ⊢ t ⇇ A
  completeness⇇ (lamᶜ t) ⊢t =
    let F , G , q , ⊢F , ⊢t , A≡ΠFG , _ = inversion-lam ⊢t
        ⊢A , _ = syntacticEq A≡ΠFG
        F′ , G′ , A⇒ΠF′G′ , F≡F′ , G≡G′ = ΠNorm ⊢A A≡ΠFG
        t⇇G = completeness⇇ t (stabilityTerm (reflConEq (wf ⊢F) ∙ F≡F′) (conv ⊢t G≡G′))
    in  lamᶜ (A⇒ΠF′G′ , ΠΣₙ) t⇇G
  completeness⇇ (prodᶜ t u) ⊢t =
    let F , G , m , ⊢F , ⊢G , ⊢t , ⊢u , A≡ΣFG , _ = inversion-prod ⊢t
        ⊢A , _ = syntacticEq A≡ΣFG
        F′ , G′ , A⇒ΣF′G′ , F≡F′ , G≡G′ = ΣNorm ⊢A A≡ΣFG
        t⇇F = completeness⇇ t (conv ⊢t F≡F′)
        u⇇Gt = completeness⇇ u (conv ⊢u (substTypeEq G≡G′ (refl ⊢t)))
    in  prodᶜ (A⇒ΣF′G′ , ΠΣₙ) t⇇F u⇇Gt
  completeness⇇ (infᶜ t) ⊢t =
    let B , t⇉B , A≡B = completeness⇉ t ⊢t
    in  infᶜ t⇉B (sym A≡B)
