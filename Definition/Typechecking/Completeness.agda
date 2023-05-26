------------------------------------------------------------------------
-- Completeness of the bi-directional typechecking relations.
------------------------------------------------------------------------

module Definition.Typechecking.Completeness {a} (M : Set a) where

open import Definition.Conversion.Stability M
open import Definition.Typechecking M
open import Definition.Typechecking.Soundness M
open import Definition.Typed M
open import Definition.Typed.Properties M
import Definition.Typed.Weakening M as W
open import Definition.Typed.Consequences.Inversion M
open import Definition.Typed.Consequences.Reduction M
open import Definition.Typed.Consequences.Substitution  M
open import Definition.Typed.Consequences.Syntactic M
open import Definition.Untyped M hiding (_∷_)

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

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
  completeness⇇Type A (Unitⱼ x) = Unitᶜ
  completeness⇇Type (infᶜ (ΠΣᵢ F G)) (ΠΣⱼ ⊢F ▹ ⊢G) = ΠΣᶜ (completeness⇇Type F ⊢F) (completeness⇇Type G ⊢G)
  completeness⇇Type A (univ x) = univᶜ (completeness⇇ A x)

  -- Completeness of type inference

  completeness⇉ : Inferable t → Γ ⊢ t ∷ A → ∃ λ B → Γ ⊢ t ⇉ B × Γ ⊢ A ≡ B
  completeness⇉ Uᵢ ⊢t = PE.⊥-elim (inversion-U ⊢t)
  completeness⇉ (ΠΣᵢ F G) ⊢t =
    let ⊢F , ⊢G , A≡U = inversion-ΠΣ-U ⊢t
        F⇇U = completeness⇇ F ⊢F
        G⇇U = completeness⇇ G ⊢G
    in  _ , ΠΣᵢ F⇇U G⇇U , A≡U
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
        B , t⇉B , ΣFG≡B = completeness⇉ t ⊢t
        F′ , G′ , B⇒Σ′ , F≡F′ , G≡G′ = ΣNorm (proj₁ (soundness⇉ (wfTerm ⊢t) t⇉B)) (sym ΣFG≡B)
        u⇇C₊ = completeness⇇ u (stabilityTerm ((reflConEq (wf ⊢F)) ∙ F≡F′ ∙ G≡G′) ⊢u)
        C⇇Type = completeness⇇Type C (stability (reflConEq (wf ⊢F) ∙ ΠΣ-cong ⊢F F≡F′ G≡G′) ⊢C)
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
  completeness⇉ Unitᵢ ⊢t = _ , Unitᵢ , inversion-Unit ⊢t
  completeness⇉ starᵢ ⊢t = _ , starᵢ , inversion-star ⊢t
  completeness⇉ Emptyᵢ ⊢t = _ , Emptyᵢ , inversion-Empty ⊢t
  completeness⇉ (Emptyrecᵢ C t) ⊢t =
    let ⊢C , ⊢t , A≡C = inversion-Emptyrec ⊢t
        t⇇Empty = completeness⇇ t ⊢t
        C⇇Type = completeness⇇Type C ⊢C
    in  _ , Emptyrecᵢ C⇇Type t⇇Empty , A≡C

  -- Completeness of type checking

  completeness⇇ : Checkable t → Γ ⊢ t ∷ A → Γ ⊢ t ⇇ A
  completeness⇇ (lamᶜ t) ⊢t =
    let F , G , q , ⊢F , ⊢t , A≡ΠFG = inversion-lam ⊢t
        ⊢A , _ = syntacticEq A≡ΠFG
        F′ , G′ , A⇒ΠF′G′ , F≡F′ , G≡G′ = ΠNorm ⊢A A≡ΠFG
        t⇇G = completeness⇇ t (stabilityTerm (reflConEq (wf ⊢F) ∙ F≡F′) (conv ⊢t G≡G′))
    in  lamᶜ (A⇒ΠF′G′ , ΠΣₙ) t⇇G
  completeness⇇ (prodᶜ t u) ⊢t =
    let F , G , m , ⊢F , ⊢G , ⊢t , ⊢u , A≡ΣFG = inversion-prod ⊢t
        ⊢A , _ = syntacticEq A≡ΣFG
        F′ , G′ , A⇒ΣF′G′ , F≡F′ , G≡G′ = ΣNorm ⊢A A≡ΣFG
        t⇇F = completeness⇇ t (conv ⊢t F≡F′)
        u⇇Gt = completeness⇇ u (conv ⊢u (substTypeEq G≡G′ (refl ⊢t)))
    in  prodᶜ (A⇒ΣF′G′ , ΠΣₙ) t⇇F u⇇Gt
  completeness⇇ (infᶜ t) ⊢t =
    let B , t⇉B , A≡B = completeness⇉ t ⊢t
    in  infᶜ t⇉B (sym A≡B)
