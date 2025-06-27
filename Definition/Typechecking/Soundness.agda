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
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Substitution R
open import Definition.Typed.Syntactic R
import Definition.Typed.Weakening R as W
open import Definition.Untyped M
open import Definition.Untyped.Properties M

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
soundness⇉-var ε      ()
soundness⇉-var (∙ ⊢A) here =
  W.wk₁ ⊢A ⊢A , var₀ ⊢A
soundness⇉-var (∙ ⊢B) (there x) =
  let ⊢A , ⊢x = soundness⇉-var (wf ⊢B) x
  in  W.wk₁ ⊢B ⊢A , var (∙ ⊢B) (there x)


mutual

  soundness⇇Type : ⊢ Γ → Γ ⊢ A ⇇Type → Γ ⊢ A
  soundness⇇Type ⊢Γ Levelᶜ = Levelⱼ ⊢Γ
  soundness⇇Type ⊢Γ (Uᶜ x) = Uⱼ (soundness⇇ x)
  soundness⇇Type ⊢Γ (Liftᶜ x y) = Liftⱼ (soundness⇇ x) (soundness⇇Type ⊢Γ y)
  soundness⇇Type ⊢Γ ℕᶜ = ℕⱼ ⊢Γ
  soundness⇇Type ⊢Γ (Unitᶜ x ok) = Unitⱼ (soundness⇇ x) ok
  soundness⇇Type ⊢Γ Emptyᶜ = Emptyⱼ ⊢Γ
  soundness⇇Type ⊢Γ (ΠΣᶜ ⊢A ⊢B ok) =
    ΠΣⱼ (soundness⇇Type (∙ soundness⇇Type ⊢Γ ⊢A) ⊢B) ok
  soundness⇇Type _ (Idᶜ _ ⊢t ⊢u) =
    Idⱼ′ (soundness⇇ ⊢t) (soundness⇇ ⊢u)
  soundness⇇Type ⊢Γ (univᶜ ⊢A) =
    univ (soundness⇇ ⊢A)

  soundness⇉ : ⊢ Γ → Γ ⊢ t ⇉ A → (Γ ⊢ A) × (Γ ⊢ t ∷ A)
  soundness⇉ ⊢Γ Levelᵢ = Uⱼ (zeroᵘⱼ ⊢Γ) , Levelⱼ ⊢Γ
  soundness⇉ ⊢Γ zeroᵘᵢ = Levelⱼ ⊢Γ , zeroᵘⱼ ⊢Γ
  soundness⇉ ⊢Γ (sucᵘᵢ t⇇Level) = Levelⱼ ⊢Γ , sucᵘⱼ (soundness⇇ t⇇Level)
  soundness⇉ ⊢Γ (maxᵘᵢ t⇇Level u⇇Level) = Levelⱼ ⊢Γ , maxᵘⱼ (soundness⇇ t⇇Level) (soundness⇇ u⇇Level)
  soundness⇉ ⊢Γ (Uᵢ x) =
    let ⊢l = soundness⇇ x
    in Uⱼ (sucᵘⱼ ⊢l) , Uⱼ ⊢l
  soundness⇉ ⊢Γ (Liftᵢ x y ↘U) =
    let _ , ⊢A = soundness⇉ ⊢Γ y
        ⊢l₂ = soundness⇇ x
        C≡U = subset* (↘U .proj₁)
        ⊢l₁ = inversion-U-Level (syntacticEq C≡U .proj₂)
    in Uⱼ (maxᵘⱼ ⊢l₁ ⊢l₂) , Liftⱼ′ ⊢l₂ (conv ⊢A C≡U)
  soundness⇉ ⊢Γ (ΠΣᵢ ⊢A (⇒*U₁ , _) ⊢B ok) =
    let _ , ⊢A = soundness⇉ ⊢Γ ⊢A
        ⊢A     = conv ⊢A (subset* ⇒*U₁)
        ⊢B     = soundness⇇ ⊢B
        ⊢l     = inversion-U-Level (syntacticTerm ⊢A)
    in
    Uⱼ ⊢l , ΠΣⱼ ⊢l ⊢A ⊢B ok
  soundness⇉ ⊢Γ (varᵢ x∷A∈Γ) = soundness⇉-var ⊢Γ x∷A∈Γ
  soundness⇉ ⊢Γ (lowerᵢ x (A⇒Lift , _)) =
    let A≡Lift = subset* A⇒Lift
        _ , ⊢Lift = syntacticEq A≡Lift
        ⊢l , ⊢A = inversion-Lift ⊢Lift
        _ , ⊢t = soundness⇉ ⊢Γ x
    in ⊢A , lowerⱼ (conv ⊢t A≡Lift)
  soundness⇉ ⊢Γ (appᵢ t⇉A (A⇒ΠFG , _) u⇇F) =
    let ⊢A , ⊢t = soundness⇉ ⊢Γ t⇉A
        A≡ΠFG = subset* A⇒ΠFG
        _ , ⊢ΠFG = syntacticEq A≡ΠFG
        ⊢F , ⊢G , _ = inversion-ΠΣ ⊢ΠFG
        ⊢u = soundness⇇ u⇇F
        ⊢t′ = conv ⊢t A≡ΠFG
    in  substType ⊢G ⊢u , ⊢t′ ∘ⱼ ⊢u
  soundness⇉ ⊢Γ (fstᵢ t⇉A (A⇒ΣFG , _)) =
    let ⊢A , ⊢t = soundness⇉ ⊢Γ t⇉A
        A≡ΣFG = subset* A⇒ΣFG
        _ , ⊢ΣFG = syntacticEq A≡ΣFG
        ⊢F , ⊢G , _ = inversion-ΠΣ ⊢ΣFG
    in  ⊢F , fstⱼ ⊢G (conv ⊢t A≡ΣFG)
  soundness⇉ ⊢Γ (sndᵢ t⇉A (A⇒ΣFG , _)) =
    let ⊢A , ⊢t = soundness⇉ ⊢Γ t⇉A
        A≡ΣFG = subset* A⇒ΣFG
        _ , ⊢ΣFG = syntacticEq A≡ΣFG
        ⊢F , ⊢G , _ = inversion-ΠΣ ⊢ΣFG
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
  soundness⇉ ⊢Γ ℕᵢ = Uⱼ (zeroᵘⱼ ⊢Γ) , ℕⱼ ⊢Γ
  soundness⇉ ⊢Γ zeroᵢ = (ℕⱼ ⊢Γ) , (zeroⱼ ⊢Γ)
  soundness⇉ ⊢Γ (sucᵢ t⇇ℕ) = ℕⱼ ⊢Γ , sucⱼ (soundness⇇ t⇇ℕ)
  soundness⇉ ⊢Γ (natrecᵢ A⇇Type z⇇A₀ s⇇A₊ n⇇ℕ) =
    let ⊢ℕ = ℕⱼ ⊢Γ
        ⊢A = soundness⇇Type (∙ ⊢ℕ) A⇇Type
        ⊢z = soundness⇇ z⇇A₀
        ⊢s = soundness⇇ s⇇A₊
        ⊢n = soundness⇇ n⇇ℕ
    in  substType ⊢A ⊢n , natrecⱼ ⊢z ⊢s ⊢n
  soundness⇉ ⊢Γ (Unitᵢ x ok) =
    let ⊢l = soundness⇇ x
    in Uⱼ ⊢l , Unitⱼ ⊢l ok
  soundness⇉ ⊢Γ (starᵢ x ok) =
    let ⊢l = soundness⇇ x
    in Unitⱼ ⊢l ok , starⱼ ⊢l ok
  soundness⇉ _ (unitrecᵢ l⇇Level A⇇Type t⇇Unit u⇇A₊) =
    let ⊢t = soundness⇇ t⇇Unit
        ⊢Unit = syntacticTerm ⊢t
        ⊢l , ok = inversion-Unit ⊢Unit
        ⊢A = soundness⇇Type (∙ ⊢Unit) A⇇Type
        ⊢u = soundness⇇ u⇇A₊
    in  substType ⊢A ⊢t , unitrecⱼ ⊢l ⊢A ⊢t ⊢u ok
  soundness⇉ ⊢Γ Emptyᵢ = Uⱼ (zeroᵘⱼ ⊢Γ) , (Emptyⱼ ⊢Γ)
  soundness⇉ ⊢Γ (emptyrecᵢ A⇇Type t⇇Empty) =
    let ⊢A = soundness⇇Type ⊢Γ A⇇Type
    in  ⊢A , (emptyrecⱼ ⊢A (soundness⇇ t⇇Empty))
  soundness⇉ ⊢Γ (Idᵢ ⊢A (⇒*U , _) ⊢t ⊢u) =
    let _ , ⊢A = soundness⇉ ⊢Γ ⊢A
        ⊢A     = conv ⊢A (subset* ⇒*U)
        ⊢l     = inversion-U-Level (syntacticTerm ⊢A)
    in
    Uⱼ ⊢l , Idⱼ ⊢A (soundness⇇ ⊢t) (soundness⇇ ⊢u)
  soundness⇉ ⊢Γ (Jᵢ ⊢A ⊢t ⊢B ⊢u ⊢v ⊢w) =
    case soundness⇇Type ⊢Γ ⊢A of λ {
      ⊢A →
    case soundness⇇ ⊢t of λ {
      ⊢t →
    case soundness⇇Type (∙ Idⱼ′ (W.wkTerm₁ ⊢A ⊢t) (var₀ ⊢A)) ⊢B of λ {
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
    case soundness⇇Type (∙ Idⱼ′ ⊢t ⊢t) ⊢B of λ {
      ⊢B →
    case soundness⇇ ⊢v of λ {
      ⊢v →
      substType ⊢B ⊢v
    , Kⱼ ⊢B (soundness⇇ ⊢u) ⊢v ok }}}}
  soundness⇉ _ ([]-congᵢ _ ⊢t ⊢u ⊢v ok) =
      Idⱼ′ ([]ⱼ ([]-cong→Erased ok) (soundness⇇ ⊢t))
        ([]ⱼ ([]-cong→Erased ok) (soundness⇇ ⊢u))
    , []-congⱼ′ ok (soundness⇇ ⊢v)

  soundness⇇ : Γ ⊢ t ⇇ A → Γ ⊢ t ∷ A
  soundness⇇ (liftᶜ A↘Lift t⇇B) =
    let A≡Lift = subset* (A↘Lift .proj₁)
        _ , ⊢Lift = syntacticEq A≡Lift
        ⊢l , ⊢B = inversion-Lift ⊢Lift
        ⊢t = soundness⇇ t⇇B
    in conv (liftⱼ′ ⊢l ⊢t) (sym A≡Lift)
  soundness⇇ (lamᶜ A↘ΠFG t⇇G)=
    let A≡ΠFG = subset* (proj₁ A↘ΠFG)
        _ , ⊢ΠFG = syntacticEq A≡ΠFG
        _ , ⊢G , ok = inversion-ΠΣ ⊢ΠFG
        ⊢t = soundness⇇ t⇇G
    in  conv (lamⱼ′ ok ⊢t) (sym A≡ΠFG)
  soundness⇇ (prodᶜ A↘ΣFG t⇇F u⇇Gt) =
    let A≡ΣFG = subset* (proj₁ A↘ΣFG)
        _ , ⊢ΣFG = syntacticEq A≡ΣFG
        _ , ⊢G , ok = inversion-ΠΣ ⊢ΣFG
        ⊢t = soundness⇇ t⇇F
        ⊢u = soundness⇇ u⇇Gt
    in  conv (prodⱼ ⊢G ⊢t ⊢u ok) (sym A≡ΣFG)
  soundness⇇ (rflᶜ (A↘Id , _) t≡u) =
    conv (rflⱼ′ t≡u) (sym (subset* A↘Id))
  soundness⇇ (infᶜ t⇉B A≡B) =
    conv (soundness⇉ (wfEq A≡B) t⇉B .proj₂) A≡B
