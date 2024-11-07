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
open import Definition.Untyped M
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
soundness⇉-var (∙ ⊢A) here =
  W.wk₁ ⊢A ⊢A , var₀ ⊢A
soundness⇉-var (∙ ⊢B) (there x) =
  let ⊢A , ⊢x = soundness⇉-var (wf ⊢B) x
  in  W.wk₁ ⊢B ⊢A , var (∙ ⊢B) (there x)


mutual

  soundness⇇Type : ⊢ Γ → Γ ⊢ A ⇇Type → Γ ⊢ A
  soundness⇇Type ⊢Γ Uᶜ = Uⱼ ⊢Γ
  soundness⇇Type ⊢Γ ℕᶜ = ℕⱼ ⊢Γ
  soundness⇇Type ⊢Γ (Unitᶜ ok) = Unitⱼ ⊢Γ ok
  soundness⇇Type ⊢Γ Emptyᶜ = Emptyⱼ ⊢Γ
  soundness⇇Type ⊢Γ (ΠΣᶜ ⊢A ⊢B ok) =
    ΠΣⱼ (soundness⇇Type (∙ soundness⇇Type ⊢Γ ⊢A) ⊢B) ok
  soundness⇇Type _ (Idᶜ _ ⊢t ⊢u) =
    Idⱼ (soundness⇇ ⊢t) (soundness⇇ ⊢u)
  soundness⇇Type ⊢Γ (univᶜ ⊢A (A⇒*U , _)) =
    univ (conv (soundness⇉ ⊢Γ ⊢A .proj₂) (subset* A⇒*U))

  soundness⇉ : ⊢ Γ → Γ ⊢ t ⇉ A → (Γ ⊢ A) × (Γ ⊢ t ∷ A)
  soundness⇉ ⊢Γ Uᵢ = Uⱼ ⊢Γ , Uⱼ ⊢Γ
  soundness⇉ ⊢Γ (ΠΣᵢ ⊢A (⇒*U₁ , _) ⊢B (⇒*U₂ , _) ok) =
    let _ , ⊢A = soundness⇉ ⊢Γ ⊢A
        ⊢A     = conv ⊢A (subset* ⇒*U₁)
        _ , ⊢B = soundness⇉ (∙ univ ⊢A) ⊢B
        ⊢B     = conv ⊢B (subset* ⇒*U₂)
    in
    Uⱼ ⊢Γ , ΠΣⱼ ⊢A ⊢B ok
  soundness⇉ ⊢Γ (varᵢ x∷A∈Γ) = soundness⇉-var ⊢Γ x∷A∈Γ
  soundness⇉ ⊢Γ (appᵢ t⇉A (A⇒ΠFG , _) u⇇F) =
    let ⊢A , ⊢t = soundness⇉ ⊢Γ t⇉A
        A≡ΠFG = subset* A⇒ΠFG
        _ , ⊢ΠFG = syntacticEq A≡ΠFG
        ⊢F , ⊢G = syntacticΠ ⊢ΠFG
        ⊢u = soundness⇇ u⇇F
        ⊢t′ = conv ⊢t A≡ΠFG
    in  substType ⊢G ⊢u , ⊢t′ ∘ⱼ ⊢u
  soundness⇉ ⊢Γ (fstᵢ t⇉A (A⇒ΣFG , _)) =
    let ⊢A , ⊢t = soundness⇉ ⊢Γ t⇉A
        A≡ΣFG = subset* A⇒ΣFG
        _ , ⊢ΣFG = syntacticEq A≡ΣFG
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG
    in  ⊢F , fstⱼ ⊢G (conv ⊢t A≡ΣFG)
  soundness⇉ ⊢Γ (sndᵢ t⇉A (A⇒ΣFG , _)) =
    let ⊢A , ⊢t = soundness⇉ ⊢Γ t⇉A
        A≡ΣFG = subset* A⇒ΣFG
        _ , ⊢ΣFG = syntacticEq A≡ΣFG
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG
    in  substType ⊢G (fstⱼ ⊢G (conv ⊢t A≡ΣFG)) , sndⱼ ⊢G (conv ⊢t A≡ΣFG)
  soundness⇉ ⊢Γ (prodrecᵢ A⇇Type t⇉B (B⇒ΣFG , _) u⇇A₊) =
    let ⊢B , ⊢t = soundness⇉ ⊢Γ t⇉B
        B≡ΣFG = subset* B⇒ΣFG
        ⊢t′ = conv ⊢t B≡ΣFG
        _ , ⊢ΣFG = syntacticEq B≡ΣFG
        _ , _ , ok = inversion-ΠΣ ⊢ΣFG
        ⊢A = soundness⇇Type (∙ ⊢ΣFG) A⇇Type
        ⊢u = soundness⇇ u⇇A₊
    in  substType ⊢A ⊢t′ , prodrecⱼ ⊢A ⊢t′ ⊢u ok
  soundness⇉ ⊢Γ ℕᵢ = Uⱼ ⊢Γ , ℕⱼ ⊢Γ
  soundness⇉ ⊢Γ zeroᵢ = (ℕⱼ ⊢Γ) , (zeroⱼ ⊢Γ)
  soundness⇉ ⊢Γ (sucᵢ t⇇ℕ) = ℕⱼ ⊢Γ , sucⱼ (soundness⇇ t⇇ℕ)
  soundness⇉ ⊢Γ (natrecᵢ A⇇Type z⇇A₀ s⇇A₊ n⇇ℕ) =
    let ⊢ℕ = ℕⱼ ⊢Γ
        ⊢A = soundness⇇Type (∙ ⊢ℕ) A⇇Type
        ⊢z = soundness⇇ z⇇A₀
        ⊢s = soundness⇇ s⇇A₊
        ⊢n = soundness⇇ n⇇ℕ
    in  substType ⊢A ⊢n , natrecⱼ ⊢z ⊢s ⊢n
  soundness⇉ ⊢Γ (Unitᵢ ok) = Uⱼ ⊢Γ , Unitⱼ ⊢Γ ok
  soundness⇉ ⊢Γ (starᵢ ok) = Unitⱼ ⊢Γ ok , starⱼ ⊢Γ ok
  soundness⇉ _ (unitrecᵢ A⇇Type t⇇Unit u⇇A₊) =
    let ⊢t = soundness⇇ t⇇Unit
        ⊢Unit = syntacticTerm ⊢t
        ok = inversion-Unit ⊢Unit
        ⊢A = soundness⇇Type (∙ ⊢Unit) A⇇Type
        ⊢u = soundness⇇ u⇇A₊
    in  substType ⊢A ⊢t , unitrecⱼ ⊢A ⊢t ⊢u ok
  soundness⇉ ⊢Γ Emptyᵢ = (Uⱼ ⊢Γ) , (Emptyⱼ ⊢Γ)
  soundness⇉ ⊢Γ (emptyrecᵢ A⇇Type t⇇Empty) =
    let ⊢A = soundness⇇Type ⊢Γ A⇇Type
    in  ⊢A , (emptyrecⱼ ⊢A (soundness⇇ t⇇Empty))
  soundness⇉ ⊢Γ (Idᵢ ⊢A (⇒*U , _) ⊢t ⊢u) =
    let _ , ⊢A = soundness⇉ ⊢Γ ⊢A
        ⊢A     = conv ⊢A (subset* ⇒*U)
    in
    Uⱼ ⊢Γ , Idⱼ ⊢A (soundness⇇ ⊢t) (soundness⇇ ⊢u)
  soundness⇉ ⊢Γ (Jᵢ ⊢A ⊢t ⊢B ⊢u ⊢v ⊢w) =
    case soundness⇇Type ⊢Γ ⊢A of λ {
      ⊢A →
    case soundness⇇ ⊢t of λ {
      ⊢t →
    case soundness⇇Type (∙ Idⱼ (W.wkTerm₁ ⊢A ⊢t) (var₀ ⊢A)) ⊢B of λ {
      ⊢B →
    case soundness⇇ ⊢w of λ {
      ⊢w →
      substType₂ ⊢B (soundness⇇ ⊢v)
        (PE.subst (_⊢_∷_ _ _) ≡Id-wk1-wk1-0[]₀ ⊢w)
    , Jⱼ′ ⊢B (soundness⇇ ⊢u) ⊢w }}}}
  soundness⇉ ⊢Γ (Kᵢ ⊢A ⊢t ⊢B ⊢u ⊢v ok) =
    case soundness⇇Type ⊢Γ ⊢A of λ {
      ⊢A →
    case soundness⇇ ⊢t of λ {
      ⊢t →
    case soundness⇇Type (∙ Idⱼ ⊢t ⊢t) ⊢B of λ {
      ⊢B →
    case soundness⇇ ⊢v of λ {
      ⊢v →
      substType ⊢B ⊢v
    , Kⱼ′ ⊢B (soundness⇇ ⊢u) ⊢v ok }}}}
  soundness⇉ _ ([]-congᵢ _ ⊢t ⊢u ⊢v ok) =
      Idⱼ ([]ⱼ ([]-cong→Erased ok) (soundness⇇ ⊢t))
        ([]ⱼ ([]-cong→Erased ok) (soundness⇇ ⊢u))
    , []-congⱼ′ ok (soundness⇇ ⊢v)

  soundness⇇ : Γ ⊢ t ⇇ A → Γ ⊢ t ∷ A
  soundness⇇ (lamᶜ A↘ΠFG t⇇G)=
    let A≡ΠFG = subset* (proj₁ A↘ΠFG)
        _ , ⊢ΠFG = syntacticEq A≡ΠFG
        _ , ⊢G , ok = inversion-ΠΣ ⊢ΠFG
        ⊢t = soundness⇇ t⇇G
    in  conv (lamⱼ ⊢t ok) (sym A≡ΠFG)
  soundness⇇ (prodᶜ A↘ΣFG t⇇F u⇇Gt) =
    let A≡ΣFG = subset* (proj₁ A↘ΣFG)
        _ , ⊢ΣFG = syntacticEq A≡ΣFG
        _ , ⊢G , ok = inversion-ΠΣ ⊢ΣFG
        ⊢t = soundness⇇ t⇇F
        ⊢u = soundness⇇ u⇇Gt
    in  conv (prodⱼ ⊢G ⊢t ⊢u ok) (sym A≡ΣFG)
  soundness⇇ (rflᶜ (A⇒*Id , _) t≡u) =
    conv (rflⱼ′ t≡u) (sym (subset* A⇒*Id))
  soundness⇇ (infᶜ t⇉B A≡B) =
    conv (soundness⇉ (wfEq A≡B) t⇉B .proj₂) A≡B
