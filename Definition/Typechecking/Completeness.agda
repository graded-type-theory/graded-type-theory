{-# OPTIONS --without-K --safe #-}

open import Tools.Relation

module Definition.Typechecking.Completeness {a ℓ} (M′ : Setoid a ℓ) where

open Setoid M′ using () renaming (Carrier to M; sym to ≈-sym)

open import Definition.Conversion.FullReduction M′
open import Definition.Conversion.Stability M′
open import Definition.Typechecking M′
open import Definition.Typechecking.Soundness M′
open import Definition.Typed M′
open import Definition.Typed.Properties M′
import Definition.Typed.Weakening M′ as W
open import Definition.Typed.Consequences.Inequality M′
open import Definition.Typed.Consequences.Inversion M′
open import Definition.Typed.Consequences.Reduction M′
open import Definition.Typed.Consequences.Substitution  M′
open import Definition.Typed.Consequences.Syntactic M′
open import Definition.Untyped M hiding (_∷_)

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Nullary

private
  variable
    n : Nat
    Γ : Con Term n
    t u A B : Term n


mutual

  completeness⇇Type : Nf A → Γ ⊢ A → Γ ⊢ A ⇇Type
  completeness⇇Type Uₙ ⊢A = Uᵢ
  completeness⇇Type (Πₙ F G) (Πⱼ ⊢F ▹ ⊢G) = Πᵢ (completeness⇇Type F ⊢F) (completeness⇇Type G ⊢G)
  completeness⇇Type (Πₙ F G) (univ x) =
    let ⊢F , ⊢G , U≡U = inversion-Π x
    in  univᵢ (infᶜ (Πᵢ (completeness⇇ F ⊢F) (completeness⇇ G ⊢G)) U≡U)
  completeness⇇Type (Σₙ F G) (Σⱼ ⊢F ▹ ⊢G) = Σᵢ (completeness⇇Type F ⊢F) (completeness⇇Type G ⊢G)
  completeness⇇Type (Σₙ F G) (univ x) =
    let ⊢F , ⊢G , U≡U = inversion-Σ x
    in  univᵢ (infᶜ (Σᵢ (completeness⇇ F ⊢F) (completeness⇇ G ⊢G)) U≡U)
  completeness⇇Type ℕₙ ⊢A = ℕᵢ
  completeness⇇Type Emptyₙ ⊢A = Emptyᵢ
  completeness⇇Type Unitₙ ⊢A = Unitᵢ
  completeness⇇Type (lamₙ A) (univ x) =
    let _ , _ , _ , _ , _ , U≡Π = inversion-lam x
    in  PE.⊥-elim (U≢Π U≡Π)
  completeness⇇Type (prodₙ A A₁) (univ x) =
    let _ , _ , _ , _ , _ , _ , _ , _ , U≡Σ = inversion-prod x
    in  PE.⊥-elim (U≢Σ U≡Σ)
  completeness⇇Type zeroₙ (univ x) = PE.⊥-elim (U≢ℕ (inversion-zero x))
  completeness⇇Type (sucₙ A) (univ x) = PE.⊥-elim (U≢ℕ (proj₂ (inversion-suc x)))
  completeness⇇Type starₙ (univ x) = PE.⊥-elim (U≢Unitⱼ (inversion-star x))
  completeness⇇Type (ne y) (univ x) =
    let B , A⇉B , U≡B = completeness⇉ y x
    in  univᵢ (infᶜ A⇉B (sym U≡B))

  completeness⇉ : NfNeutral t → Γ ⊢ t ∷ A → ∃ λ B → Γ ⊢ t ⇉ B × Γ ⊢ A ≡ B
  completeness⇉ (var x) ⊢t =
    let B , x∷B∈Γ , A≡B = inversion-var ⊢t
    in  _ , varᵢ x∷B∈Γ , A≡B
  completeness⇉ (∘ₙ {q = p} t u) ⊢tu =
    let F , G , q , ⊢t , ⊢u , A≡Gu = inversion-app ⊢tu
        B , t⇉B , ΠFG≡B = completeness⇉ t ⊢t
        F′ , G′ , p′ , q′ , B⇒Π′ , F≡F′ , G≡G′ , p≈p′ , q≈q′ = ΠNorm (proj₁ (soundness⇉ (wfTerm ⊢t) t⇉B)) (sym ΠFG≡B)
        ⊢u′ = conv ⊢u F≡F′
        u⇇G = completeness⇇ u ⊢u′
    in  _ , appᵢ t⇉B (B⇒Π′ , Πₙ) u⇇G (≈-sym p≈p′) , trans A≡Gu (substTypeEq G≡G′ (refl ⊢u))
  completeness⇉ (fstₙ t) ⊢t =
    let F , G , q , ⊢F , ⊢G , ⊢t , A≡F = inversion-fst ⊢t
        B , t⇉B , ΣFG≡B = completeness⇉ t ⊢t
        F′ , G′ , q′ , B⇒Σ′ , F≡F′ , G≡G′ , q≈q′ = ΣNorm (proj₁ (soundness⇉ (wfTerm ⊢t) t⇉B)) (sym ΣFG≡B)
    in  _ , fstᵢ t⇉B (B⇒Σ′ , Σₙ) , trans A≡F F≡F′
  completeness⇉ (sndₙ t) ⊢t =
    let F , G , q , ⊢F , ⊢G , ⊢t , A≡Gt = inversion-snd ⊢t
        B , t⇉B , ΣFG≡B = completeness⇉ t ⊢t
        F′ , G′ , q′ , B⇒Σ′ , F≡F′ , G≡G′ , q≈q′ = ΣNorm (proj₁ (soundness⇉ (wfTerm ⊢t) t⇉B)) (sym ΣFG≡B)
    in  _ , sndᵢ t⇉B (B⇒Σ′ , Σₙ) , trans A≡Gt (substTypeEq G≡G′ (refl (fstⱼ ⊢F ⊢G ⊢t)))
  completeness⇉ (natrecₙ C z s n) ⊢t =
    let ⊢C , ⊢z , ⊢s , ⊢n , A≡Cn = inversion-natrec ⊢t
        z⇇C₀ = completeness⇇ z ⊢z
        s⇇C₊ = completeness⇇ s ⊢s
        B , n⇉B , ℕ≡B = completeness⇉ n ⊢n
        C⇇Type = completeness⇇Type C ⊢C
    in  _ , natrecᵢ C⇇Type z⇇C₀ s⇇C₊ (infᶜ n⇉B (sym ℕ≡B)) , A≡Cn
  completeness⇉ (prodrecₙ C t u) ⊢t =
    let F , G , q , ⊢F , ⊢G , ⊢C , ⊢t , ⊢u , A≡Ct = inversion-prodrec ⊢t
        B , t⇉B , ΣFG≡B = completeness⇉ t ⊢t
        F′ , G′ , q′ , B⇒Σ′ , F≡F′ , G≡G′ , q≈q′ = ΣNorm (proj₁ (soundness⇉ (wfTerm ⊢t) t⇉B)) (sym ΣFG≡B)
        u⇇C₊ = completeness⇇ u (stabilityTerm ((reflConEq (wf ⊢F)) ∙ F≡F′ ∙ G≡G′) ⊢u)
        C⇇Type = completeness⇇Type C (stability (reflConEq (wf ⊢F) ∙ Σ-cong ⊢F F≡F′ G≡G′ q≈q′) ⊢C)
    in  _ , prodrecᵢ C⇇Type t⇉B (B⇒Σ′ , Σₙ) u⇇C₊ , A≡Ct
  completeness⇉ (Emptyrecₙ C t) ⊢t =
    let ⊢C , ⊢t , A≡C = inversion-Emptyrec ⊢t
        B , t⇉B , B≡Empty = completeness⇉ t ⊢t
        C⇇Type = completeness⇇Type C ⊢C
    in  _ , Emptyrecᵢ C⇇Type (infᶜ t⇉B (sym B≡Empty)) , A≡C

  completeness⇇ : Nf t → Γ ⊢ t ∷ A → Γ ⊢ t ⇇ A
  completeness⇇ Uₙ ⊢t = PE.⊥-elim (inversion-U ⊢t)
  completeness⇇ (Πₙ F G) ⊢t =
    let ⊢F , ⊢G , A≡U = inversion-Π ⊢t
        F⇇U = completeness⇇ F ⊢F
        G⇇U = completeness⇇ G ⊢G
    in  infᶜ (Πᵢ F⇇U G⇇U) (sym A≡U)
  completeness⇇ (Σₙ F G) ⊢t =
    let ⊢F , ⊢G , A≡U = inversion-Σ ⊢t
        F⇇U = completeness⇇ F ⊢F
        G⇇U = completeness⇇ G ⊢G
    in  infᶜ (Σᵢ F⇇U G⇇U) (sym A≡U)
  completeness⇇ ℕₙ ⊢t = infᶜ ℕᵢ (sym (inversion-ℕ ⊢t))
  completeness⇇ Emptyₙ ⊢t = infᶜ Emptyᵢ (sym (inversion-Empty ⊢t))
  completeness⇇ Unitₙ ⊢t = infᶜ Unitᵢ (sym (inversion-Unit ⊢t))
  completeness⇇ (lamₙ t) ⊢t =
    let F , G , q , ⊢F , ⊢t , A≡ΠFG = inversion-lam ⊢t
        ⊢A , _ = syntacticEq A≡ΠFG
        p′ , q′ , F′ , G′ , A⇒ΠF′G′ , F≡F′ , G≡G′ , p≈p′ , q≈q′ = ΠNorm ⊢A A≡ΠFG
        t⇇G = completeness⇇ t (stabilityTerm (reflConEq (wf ⊢F) ∙ F≡F′) (conv ⊢t G≡G′))
    in  lamᶜ (A⇒ΠF′G′ , Πₙ) t⇇G (≈-sym p≈p′)
  completeness⇇ (prodₙ t u) ⊢t =
    let F , G , q , m , ⊢F , ⊢G , ⊢t , ⊢u , A≡ΣFG = inversion-prod ⊢t
        ⊢A , _ = syntacticEq A≡ΣFG
        q′ , F′ , G′ , A⇒ΣF′G′ , F≡F′ , G≡G′ , q≈q′ = ΣNorm ⊢A A≡ΣFG
        t⇇F = completeness⇇ t (conv ⊢t F≡F′)
        u⇇Gt = completeness⇇ u (conv ⊢u (substTypeEq G≡G′ (refl ⊢t)))
    in  prodᶜ (A⇒ΣF′G′ , Σₙ) t⇇F u⇇Gt
  completeness⇇ zeroₙ ⊢t = infᶜ zeroᵢ (sym (inversion-zero ⊢t))
  completeness⇇ (sucₙ t) ⊢t =
    let ⊢t , A≡ℕ = inversion-suc ⊢t
        t⇇ℕ = completeness⇇ t ⊢t
    in  infᶜ (sucᵢ t⇇ℕ) (sym A≡ℕ)
  completeness⇇ starₙ ⊢t = infᶜ starᵢ (sym (inversion-star ⊢t))
  completeness⇇ (ne x) ⊢t =
    let B , t⇉B , A≡B = completeness⇉ x ⊢t
    in  infᶜ t⇉B (sym A≡B)
