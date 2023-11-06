------------------------------------------------------------------------
-- Soundness of the bi-directional typechecking relations.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typechecking.Soundness
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typechecking R
open import Definition.Typed R
open import Definition.Typed.Properties R
import Definition.Typed.Weakening R as W
open import Definition.Typed.Consequences.DerivedRules R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Untyped M hiding (_∷_)
open import Definition.Untyped.Properties M

open import Graded.Derived.Erased.Typed R

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

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
  soundness⇇Type ⊢Γ (Unitᶜ ok) = Unitⱼ ⊢Γ ok
  soundness⇇Type ⊢Γ Emptyᶜ = Emptyⱼ ⊢Γ
  soundness⇇Type ⊢Γ (ΠΣᶜ ⊢A ⊢B ok) =
    let ⊢F = soundness⇇Type ⊢Γ ⊢A
    in  ΠΣⱼ ⊢F (soundness⇇Type (⊢Γ ∙ ⊢F) ⊢B) ok
  soundness⇇Type ⊢Γ (Idᶜ _ ⊢t ⊢u) =
    Idⱼ (soundness⇇ ⊢Γ ⊢t) (soundness⇇ ⊢Γ ⊢u)
  soundness⇇Type ⊢Γ (univᶜ x) = univ (soundness⇇ ⊢Γ x)

  soundness⇉ : ⊢ Γ → Γ ⊢ t ⇉ A → (Γ ⊢ A) × (Γ ⊢ t ∷ A)
  soundness⇉ ⊢Γ (ΠΣᵢ F⇇U G⇇U ok) =
    let ⊢F = soundness⇇ ⊢Γ F⇇U
        ⊢G = soundness⇇ (⊢Γ ∙ univ ⊢F) G⇇U
    in  Uⱼ ⊢Γ , ΠΣⱼ ⊢F ⊢G ok
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
        ⊢F , ⊢G , ok = inversion-ΠΣ ⊢ΣFG
        ⊢A = soundness⇇Type (⊢Γ ∙ ⊢ΣFG) A⇇Type
        ⊢u = soundness⇇ (⊢Γ ∙ ⊢F ∙ ⊢G) u⇇A₊
    in  substType ⊢A ⊢t′ , prodrecⱼ ⊢F ⊢G ⊢A ⊢t′ ⊢u ok
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
  soundness⇉ ⊢Γ (Unitᵢ ok) = Uⱼ ⊢Γ , Unitⱼ ⊢Γ ok
  soundness⇉ ⊢Γ (starᵢ ok) = Unitⱼ ⊢Γ ok , starⱼ ⊢Γ ok
  soundness⇉ ⊢Γ (unitrecᵢ A⇇Type t⇇Unit u⇇A₊) =
    let ⊢t = soundness⇇ ⊢Γ t⇇Unit
        ⊢Unit = syntacticTerm ⊢t
        ok = inversion-Unit ⊢Unit
        ⊢A = soundness⇇Type (⊢Γ ∙ ⊢Unit) A⇇Type
        ⊢u = soundness⇇ ⊢Γ u⇇A₊
    in  substType ⊢A ⊢t , unitrecⱼ ⊢A ⊢t ⊢u ok
  soundness⇉ ⊢Γ Emptyᵢ = (Uⱼ ⊢Γ) , (Emptyⱼ ⊢Γ)
  soundness⇉ ⊢Γ (emptyrecᵢ A⇇Type t⇇Empty) =
    let ⊢A = soundness⇇Type ⊢Γ A⇇Type
    in  ⊢A , (emptyrecⱼ ⊢A (soundness⇇ ⊢Γ t⇇Empty))
  soundness⇉ ⊢Γ (Idᵢ ⊢A ⊢t ⊢u) =
    Uⱼ ⊢Γ , Idⱼ (soundness⇇ ⊢Γ ⊢A) (soundness⇇ ⊢Γ ⊢t) (soundness⇇ ⊢Γ ⊢u)
  soundness⇉ ⊢Γ (Jᵢ ⊢A ⊢t ⊢B ⊢u ⊢v ⊢w) =
    case soundness⇇Type ⊢Γ ⊢A of λ {
      ⊢A →
    case ⊢Γ ∙ ⊢A of λ {
      ⊢Γ∙A →
    case soundness⇇ ⊢Γ ⊢t of λ {
      ⊢t →
    case soundness⇇Type
           (⊢Γ∙A ∙ Idⱼ (W.wkTerm (W.step W.id) ⊢Γ∙A ⊢t) (var ⊢Γ∙A here))
           ⊢B of λ {
      ⊢B →
    case soundness⇇ ⊢Γ ⊢w of λ {
      ⊢w →
      substType₂ ⊢B (soundness⇇ ⊢Γ ⊢v)
        (PE.subst (_⊢_∷_ _ _) ≡Id-wk1-wk1-0[]₀ ⊢w)
    , Jⱼ′ ⊢B (soundness⇇ ⊢Γ ⊢u) ⊢w }}}}}
  soundness⇉ ⊢Γ (Kᵢ ⊢A ⊢t ⊢B ⊢u ⊢v ok) =
    case soundness⇇Type ⊢Γ ⊢A of λ {
      ⊢A →
    case soundness⇇ ⊢Γ ⊢t of λ {
      ⊢t →
    case soundness⇇Type (⊢Γ ∙ Idⱼ ⊢t ⊢t) ⊢B of λ {
      ⊢B →
    case soundness⇇ ⊢Γ ⊢v of λ {
      ⊢v →
      substType ⊢B ⊢v
    , Kⱼ′ ⊢B (soundness⇇ ⊢Γ ⊢u) ⊢v ok }}}}
  soundness⇉ ⊢Γ ([]-congᵢ _ ⊢t ⊢u ⊢v ok) =
      Idⱼ ([]ⱼ ([]-cong→Erased ok) (soundness⇇ ⊢Γ ⊢t))
        ([]ⱼ ([]-cong→Erased ok) (soundness⇇ ⊢Γ ⊢u))
    , []-congⱼ′ ok (soundness⇇ ⊢Γ ⊢v)

  soundness⇇ : ⊢ Γ → Γ ⊢ t ⇇ A → Γ ⊢ t ∷ A
  soundness⇇ ⊢Γ (lamᶜ A↘ΠFG t⇇G)=
    let A≡ΠFG = subset* (proj₁ A↘ΠFG)
        _ , ⊢ΠFG = syntacticEq A≡ΠFG
        ⊢F , ⊢G , ok = inversion-ΠΣ ⊢ΠFG
        ⊢t = soundness⇇ (⊢Γ ∙ ⊢F) t⇇G
    in  conv (lamⱼ ⊢F ⊢t ok) (sym A≡ΠFG)
  soundness⇇ ⊢Γ (prodᶜ A↘ΣFG t⇇F u⇇Gt) =
    let A≡ΣFG = subset* (proj₁ A↘ΣFG)
        _ , ⊢ΣFG = syntacticEq A≡ΣFG
        ⊢F , ⊢G , ok = inversion-ΠΣ ⊢ΣFG
        ⊢t = soundness⇇ ⊢Γ t⇇F
        ⊢u = soundness⇇ ⊢Γ u⇇Gt
    in  conv (prodⱼ ⊢F ⊢G ⊢t ⊢u ok) (sym A≡ΣFG)
  soundness⇇ _ (rflᶜ (A⇒*Id , _) t≡u) =
    conv (rflⱼ′ t≡u) (sym (subset* A⇒*Id))
  soundness⇇ ⊢Γ (infᶜ t⇉B A≡B) = conv (proj₂ (soundness⇉ ⊢Γ t⇉B)) A≡B
