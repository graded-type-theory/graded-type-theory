module Definition.Typechecking.Soundness {a} (M : Set a) where

open import Definition.Typechecking M
open import Definition.Typed M
open import Definition.Typed.Properties M
import Definition.Typed.Weakening M as W
open import Definition.Typed.Consequences.Syntactic M
open import Definition.Typed.Consequences.Substitution M
open import Definition.Untyped M hiding (_∷_)

open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n
    t A : Term n

soundness⇉-var : ∀ {x} →  ⊢ Γ → x ∷ A ∈ Γ → (Γ ⊢ A) × (Γ ⊢ var x ∷ A)
soundness⇉-var (⊢Γ ∙ ⊢A) here = W.wk (W.step W.id) (⊢Γ ∙ ⊢A) ⊢A , var (⊢Γ ∙ ⊢A) here
soundness⇉-var (⊢Γ ∙ ⊢B) (there x) =
  let ⊢A , ⊢x = soundness⇉-var ⊢Γ x
  in  W.wk (W.step W.id) (⊢Γ ∙ ⊢B) ⊢A , var (⊢Γ ∙ ⊢B) (there x)


mutual

  soundness⇇Type : ⊢ Γ → Γ ⊢ A ⇇Type → Γ ⊢ A
  soundness⇇Type ⊢Γ Uᶜ = Uⱼ ⊢Γ
  soundness⇇Type ⊢Γ ℕᶜ = ℕⱼ ⊢Γ
  soundness⇇Type ⊢Γ Unitᶜ = Unitⱼ ⊢Γ
  soundness⇇Type ⊢Γ Emptyᶜ = Emptyⱼ ⊢Γ
  soundness⇇Type ⊢Γ (ΠΣᶜ x x₁) =
    let ⊢F = soundness⇇Type ⊢Γ x
    in  ΠΣⱼ ⊢F ▹ soundness⇇Type (⊢Γ ∙ ⊢F) x₁
  soundness⇇Type ⊢Γ (univᶜ x) = univ (soundness⇇ ⊢Γ x)

  soundness⇉ : ⊢ Γ → Γ ⊢ t ⇉ A → (Γ ⊢ A) × (Γ ⊢ t ∷ A)
  soundness⇉ ⊢Γ (ΠΣᵢ F⇇U G⇇U) =
    let ⊢F = soundness⇇ ⊢Γ F⇇U
        ⊢G = soundness⇇ (⊢Γ ∙ univ ⊢F) G⇇U
    in  Uⱼ ⊢Γ , ΠΣⱼ ⊢F ▹ ⊢G
  soundness⇉ ⊢Γ (varᵢ x∷A∈Γ) = soundness⇉-var ⊢Γ x∷A∈Γ
  soundness⇉ ⊢Γ (appᵢ t⇉A (A⇒ΠFG , _) u⇇F) =
    let ⊢A , ⊢t = soundness⇉ ⊢Γ t⇉A
        A≡ΠFG = subset* A⇒ΠFG
        _ , ⊢ΠFG = syntacticEq A≡ΠFG
        ⊢F , ⊢G = syntacticΠ ⊢ΠFG
        ⊢u = soundness⇇ ⊢Γ u⇇F
        ⊢t′ = conv ⊢t A≡ΠFG
    in  substType ⊢G ⊢u , ⊢t′ ∘ⱼ ⊢u
  soundness⇉ ⊢Γ (fstᵢ t⇉A (A⇒ΣFG , _)) =
    let ⊢A , ⊢t = soundness⇉ ⊢Γ t⇉A
        A≡ΣFG = subset* A⇒ΣFG
        _ , ⊢ΣFG = syntacticEq A≡ΣFG
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG
    in  ⊢F , fstⱼ ⊢F ⊢G (conv ⊢t A≡ΣFG)
  soundness⇉ ⊢Γ (sndᵢ t⇉A (A⇒ΣFG , _)) =
    let ⊢A , ⊢t = soundness⇉ ⊢Γ t⇉A
        A≡ΣFG = subset* A⇒ΣFG
        _ , ⊢ΣFG = syntacticEq A≡ΣFG
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG
    in  substType ⊢G (fstⱼ ⊢F ⊢G (conv ⊢t A≡ΣFG)) , sndⱼ ⊢F ⊢G (conv ⊢t A≡ΣFG)
  soundness⇉ ⊢Γ (prodrecᵢ A⇇Type t⇉B (B⇒ΣFG , _) u⇇A₊) =
    let ⊢B , ⊢t = soundness⇉ ⊢Γ t⇉B
        B≡ΣFG = subset* B⇒ΣFG
        ⊢t′ = conv ⊢t B≡ΣFG
        _ , ⊢ΣFG = syntacticEq B≡ΣFG
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG
        ⊢A = soundness⇇Type (⊢Γ ∙ ⊢ΣFG) A⇇Type
        ⊢u = soundness⇇ (⊢Γ ∙ ⊢F ∙ ⊢G) u⇇A₊
    in  substType ⊢A ⊢t′ , prodrecⱼ ⊢F ⊢G ⊢A ⊢t′ ⊢u
  soundness⇉ ⊢Γ ℕᵢ = Uⱼ ⊢Γ , ℕⱼ ⊢Γ
  soundness⇉ ⊢Γ zeroᵢ = (ℕⱼ ⊢Γ) , (zeroⱼ ⊢Γ)
  soundness⇉ ⊢Γ (sucᵢ t⇇ℕ) = (ℕⱼ ⊢Γ) , (sucⱼ (soundness⇇ ⊢Γ t⇇ℕ))
  soundness⇉ ⊢Γ (natrecᵢ A⇇Type z⇇A₀ s⇇A₊ n⇇ℕ) =
    let ⊢ℕ = ℕⱼ ⊢Γ
        ⊢A = soundness⇇Type (⊢Γ ∙ ⊢ℕ) A⇇Type
        ⊢z = soundness⇇ ⊢Γ z⇇A₀
        ⊢s = soundness⇇ (⊢Γ ∙ ⊢ℕ ∙ ⊢A) s⇇A₊
        ⊢n = soundness⇇ ⊢Γ n⇇ℕ
    in  substType ⊢A ⊢n , (natrecⱼ ⊢A ⊢z ⊢s ⊢n)
  soundness⇉ ⊢Γ Unitᵢ = (Uⱼ ⊢Γ) , (Unitⱼ ⊢Γ)
  soundness⇉ ⊢Γ starᵢ = (Unitⱼ ⊢Γ) , (starⱼ ⊢Γ)
  soundness⇉ ⊢Γ Emptyᵢ = (Uⱼ ⊢Γ) , (Emptyⱼ ⊢Γ)
  soundness⇉ ⊢Γ (Emptyrecᵢ A⇇Type t⇇Empty) =
    let ⊢A = soundness⇇Type ⊢Γ A⇇Type
    in  ⊢A , (Emptyrecⱼ ⊢A (soundness⇇ ⊢Γ t⇇Empty))

  soundness⇇ : ⊢ Γ → Γ ⊢ t ⇇ A → Γ ⊢ t ∷ A
  soundness⇇ ⊢Γ (lamᶜ A↘ΠFG t⇇G)=
    let A≡ΠFG = subset* (proj₁ A↘ΠFG)
        _ , ⊢ΠFG = syntacticEq A≡ΠFG
        ⊢F , ⊢G = syntacticΠ ⊢ΠFG
        ⊢t = soundness⇇ (⊢Γ ∙ ⊢F) t⇇G
    in  conv (lamⱼ ⊢F ⊢t) (sym A≡ΠFG)
  soundness⇇ ⊢Γ (prodᶜ A↘ΣFG t⇇F u⇇Gt) =
    let A≡ΣFG = subset* (proj₁ A↘ΣFG)
        _ , ⊢ΣFG = syntacticEq A≡ΣFG
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG
        ⊢t = soundness⇇ ⊢Γ t⇇F
        ⊢u = soundness⇇ ⊢Γ u⇇Gt
    in  conv (prodⱼ ⊢F ⊢G ⊢t ⊢u) (sym A≡ΣFG)
  soundness⇇ ⊢Γ (infᶜ t⇉B A≡B) = conv (proj₂ (soundness⇉ ⊢Γ t⇉B)) A≡B
