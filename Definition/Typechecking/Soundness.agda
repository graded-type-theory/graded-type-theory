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
import Definition.Typed.Weakening R as W
open import Definition.Typed.Well-formed R
open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    m n : Nat
    Γ : Cons m n
    A t : Term n
    l : Lvl _

soundness⇉-var :
  ∀ {x} → ⊢ Γ → x ∷ A ∈ Γ .vars → (Γ ⊢ A) × (Γ ⊢ var x ∷ A)
soundness⇉-var (ε »∇) ()
soundness⇉-var (∙ ⊢A) here =
  W.wk₁ ⊢A ⊢A , var₀ ⊢A
soundness⇉-var (∙ ⊢B) (there x) =
  let ⊢A , ⊢x = soundness⇉-var (wf ⊢B) x
  in  W.wk₁ ⊢B ⊢A , var (∙ ⊢B) (there x)


mutual

  soundness⇇Type : ⊢ Γ → Γ ⊢ A ⇇Type → Γ ⊢ A
  soundness⇇Type ⊢Γ (Levelᶜ ok) = Levelⱼ′ ok ⊢Γ
  soundness⇇Type ⊢Γ (Uᶜ ⊢l) = ⊢U (soundness⇇Level ⊢Γ ⊢l)
  soundness⇇Type ⊢Γ (Liftᶜ x y) =
    Liftⱼ (soundness⇇Level ⊢Γ x) (soundness⇇Type ⊢Γ y)
  soundness⇇Type ⊢Γ ℕᶜ = ⊢ℕ ⊢Γ
  soundness⇇Type ⊢Γ (Unitᶜ ok) = ⊢Unit ⊢Γ ok
  soundness⇇Type ⊢Γ Emptyᶜ = ⊢Empty ⊢Γ
  soundness⇇Type ⊢Γ (ΠΣᶜ ⊢A ⊢B ok) =
    ΠΣⱼ (soundness⇇Type (∙ soundness⇇Type ⊢Γ ⊢A) ⊢B) ok
  soundness⇇Type _ (Idᶜ _ ⊢t ⊢u) =
    Idⱼ′ (soundness⇇ ⊢t) (soundness⇇ ⊢u)
  soundness⇇Type ⊢Γ (univᶜ ⊢A ↘U) =
    let ⊢B , A∷B = soundness⇉ ⊢Γ ⊢A in
    univ (conv A∷B (subset* (↘U .proj₁)))

  soundness⇉ : ⊢ Γ → Γ ⊢ t ⇉ A → (Γ ⊢ A) × (Γ ⊢ t ∷ A)
  soundness⇉ ⊢Γ (Levelᵢ ok) = ⊢U₀ ⊢Γ , Levelⱼ ⊢Γ ok
  soundness⇉ ⊢Γ (zeroᵘᵢ ok) = Levelⱼ′ ok ⊢Γ , zeroᵘⱼ ok ⊢Γ
  soundness⇉ ⊢Γ (sucᵘᵢ t⇇Level) =
    let ⊢t = soundness⇇ t⇇Level
        ok = inversion-Level-⊢ (wf-⊢ ⊢t)
    in
    Levelⱼ′ ok ⊢Γ , sucᵘⱼ ⊢t
  soundness⇉ ⊢Γ (supᵘᵢ t⇇Level u⇇Level) =
    let ⊢t = soundness⇇ t⇇Level
        ok = inversion-Level-⊢ (wf-⊢ ⊢t)
    in
    Levelⱼ′ ok ⊢Γ , supᵘⱼ ⊢t (soundness⇇ u⇇Level)
  soundness⇉ ⊢Γ (Uᵢ ⊢l) =
    let ⊢l = soundness⇇Level ⊢Γ ⊢l in
    ⊢U (⊢1ᵘ+ ⊢l) , Uⱼ ⊢l
  soundness⇉ ⊢Γ (Liftᵢ x y ↘U) =
    let _ , ⊢A = soundness⇉ ⊢Γ y
        ⊢l₂ = soundness⇇Level ⊢Γ x
        C≡U = subset* (↘U .proj₁)
        ⊢l₁ = inversion-U-Level (wf-⊢ C≡U .proj₂)
    in
    ⊢U (⊢supᵘₗ ⊢l₁ ⊢l₂) , Liftⱼ′ ⊢l₂ (conv ⊢A C≡U)
  soundness⇉ ⊢Γ (ΠΣᵢ ⊢A (⇒*U₁ , _) ⊢B ok) =
    let _ , ⊢A = soundness⇉ ⊢Γ ⊢A
        ⊢A     = conv ⊢A (subset* ⇒*U₁)
        ⊢B     = soundness⇇ ⊢B
        ⊢l     = inversion-U-Level (wf-⊢ ⊢A)
    in
    ⊢U ⊢l , ΠΣⱼ ⊢l ⊢A ⊢B ok
  soundness⇉ ⊢Γ (varᵢ x∷A∈Γ) = soundness⇉-var ⊢Γ x∷A∈Γ
  soundness⇉ ⊢Γ (defnᵢ α↦t) =
    W.wk (W.wk₀∷ʷ⊇ ⊢Γ) (wf-↦∈ α↦t (defn-wf ⊢Γ)) , defn ⊢Γ α↦t PE.refl
  soundness⇉ ⊢Γ (lowerᵢ x (A⇒Lift , _)) =
    let A≡Lift = subset* A⇒Lift
        _ , ⊢Lift = wf-⊢ A≡Lift
        ⊢l , ⊢A = inversion-Lift ⊢Lift
        _ , ⊢t = soundness⇉ ⊢Γ x
    in ⊢A , lowerⱼ (conv ⊢t A≡Lift)
  soundness⇉ ⊢Γ (appᵢ t⇉A (A⇒ΠFG , _) u⇇F) =
    let ⊢A , ⊢t = soundness⇉ ⊢Γ t⇉A
        A≡ΠFG = subset* A⇒ΠFG
        _ , ⊢ΠFG = wf-⊢ A≡ΠFG
        ⊢F , ⊢G , _ = inversion-ΠΣ ⊢ΠFG
        ⊢u = soundness⇇ u⇇F
        ⊢t′ = conv ⊢t A≡ΠFG
    in  subst-⊢₀ ⊢G ⊢u , ⊢t′ ∘ⱼ ⊢u
  soundness⇉ ⊢Γ (fstᵢ t⇉A (A⇒ΣFG , _)) =
    let ⊢A , ⊢t = soundness⇉ ⊢Γ t⇉A
        A≡ΣFG = subset* A⇒ΣFG
        _ , ⊢ΣFG = wf-⊢ A≡ΣFG
        ⊢F , ⊢G , _ = inversion-ΠΣ ⊢ΣFG
    in  ⊢F , fstⱼ ⊢G (conv ⊢t A≡ΣFG)
  soundness⇉ ⊢Γ (sndᵢ t⇉A (A⇒ΣFG , _)) =
    let ⊢A , ⊢t = soundness⇉ ⊢Γ t⇉A
        A≡ΣFG = subset* A⇒ΣFG
        _ , ⊢ΣFG = wf-⊢ A≡ΣFG
        ⊢F , ⊢G , _ = inversion-ΠΣ ⊢ΣFG
    in  subst-⊢₀ ⊢G (fstⱼ ⊢G (conv ⊢t A≡ΣFG)) , sndⱼ ⊢G (conv ⊢t A≡ΣFG)
  soundness⇉ ⊢Γ (prodrecᵢ A⇇Type t⇉B (B⇒ΣFG , _) u⇇A₊) =
    let ⊢B , ⊢t = soundness⇉ ⊢Γ t⇉B
        B≡ΣFG = subset* B⇒ΣFG
        ⊢t′ = conv ⊢t B≡ΣFG
        _ , ⊢ΣFG = wf-⊢ B≡ΣFG
        _ , _ , ok = inversion-ΠΣ ⊢ΣFG
        ⊢A = soundness⇇Type (∙ ⊢ΣFG) A⇇Type
        ⊢u = soundness⇇ u⇇A₊
    in  subst-⊢₀ ⊢A ⊢t′ , prodrecⱼ ⊢A ⊢t′ ⊢u ok
  soundness⇉ ⊢Γ ℕᵢ = ⊢U₀ ⊢Γ , ℕⱼ ⊢Γ
  soundness⇉ ⊢Γ zeroᵢ = ⊢ℕ ⊢Γ , zeroⱼ ⊢Γ
  soundness⇉ ⊢Γ (sucᵢ t⇇ℕ) = ⊢ℕ ⊢Γ , sucⱼ (soundness⇇ t⇇ℕ)
  soundness⇉ ⊢Γ (natrecᵢ A⇇Type z⇇A₀ s⇇A₊ n⇇ℕ) =
    let ⊢ℕ = ⊢ℕ ⊢Γ
        ⊢A = soundness⇇Type (∙ ⊢ℕ) A⇇Type
        ⊢z = soundness⇇ z⇇A₀
        ⊢s = soundness⇇ s⇇A₊
        ⊢n = soundness⇇ n⇇ℕ
    in  subst-⊢₀ ⊢A ⊢n , natrecⱼ ⊢z ⊢s ⊢n
  soundness⇉ ⊢Γ (Unitᵢ ok) =
    ⊢U₀ ⊢Γ , Unitⱼ ⊢Γ ok
  soundness⇉ ⊢Γ (starᵢ ok) =
    ⊢Unit ⊢Γ ok , starⱼ ⊢Γ ok
  soundness⇉ _ (unitrecᵢ A⇇Type t⇇Unit u⇇A₊) =
    let ⊢t = soundness⇇ t⇇Unit
        ⊢Unit = wf-⊢ ⊢t
        ok = inversion-Unit ⊢Unit
        ⊢A = soundness⇇Type (∙ ⊢Unit) A⇇Type
        ⊢u = soundness⇇ u⇇A₊
    in  subst-⊢₀ ⊢A ⊢t , unitrecⱼ ⊢A ⊢t ⊢u ok
  soundness⇉ ⊢Γ Emptyᵢ = ⊢U₀ ⊢Γ , Emptyⱼ ⊢Γ
  soundness⇉ ⊢Γ (emptyrecᵢ A⇇Type t⇇Empty) =
    let ⊢A = soundness⇇Type ⊢Γ A⇇Type
    in  ⊢A , (emptyrecⱼ ⊢A (soundness⇇ t⇇Empty))
  soundness⇉ ⊢Γ (Idᵢ ⊢A (⇒*U , _) ⊢t ⊢u) =
    let _ , ⊢A = soundness⇉ ⊢Γ ⊢A
        ⊢A     = conv ⊢A (subset* ⇒*U)
        ⊢l     = inversion-U-Level (wf-⊢ ⊢A)
    in
    ⊢U ⊢l , Idⱼ ⊢A (soundness⇇ ⊢t) (soundness⇇ ⊢u)
  soundness⇉ ⊢Γ (Jᵢ ⊢A ⊢t ⊢B ⊢u ⊢v ⊢w) =
    case soundness⇇Type ⊢Γ ⊢A of λ {
      ⊢A →
    case soundness⇇ ⊢t of λ {
      ⊢t →
    case soundness⇇Type (∙ Idⱼ′ (W.wk₁ ⊢A ⊢t) (var₀ ⊢A)) ⊢B of λ {
      ⊢B →
    case soundness⇇ ⊢w of λ {
      ⊢w →
      subst-⊢₁₀ ⊢B (soundness⇇ ⊢v)
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
      subst-⊢₀ ⊢B ⊢v
    , Kⱼ ⊢B (soundness⇇ ⊢u) ⊢v ok }}}}
  soundness⇉ ⊢Γ ([]-congᵢ ⊢l _ ⊢t ⊢u ⊢v ok) =
    let ⊢l = soundness⇇Level ⊢Γ ⊢l in
    Idⱼ′ ([]ⱼ ([]-cong→Erased ok) ⊢l (soundness⇇ ⊢t))
      ([]ⱼ ([]-cong→Erased ok) ⊢l (soundness⇇ ⊢u)) ,
    []-congⱼ′ ok ⊢l (soundness⇇ ⊢v)

  soundness⇇ : Γ ⊢ t ⇇ A → Γ ⊢ t ∷ A
  soundness⇇ (liftᶜ A↘Lift t⇇B) =
    let A≡Lift = subset* (A↘Lift .proj₁)
        _ , ⊢Lift = wf-⊢ A≡Lift
        ⊢l , ⊢B = inversion-Lift ⊢Lift
        ⊢t = soundness⇇ t⇇B
    in conv (liftⱼ′ ⊢l ⊢t) (sym A≡Lift)
  soundness⇇ (lamᶜ A↘ΠFG t⇇G)=
    let A≡ΠFG = subset* (proj₁ A↘ΠFG)
        _ , ⊢ΠFG = wf-⊢ A≡ΠFG
        _ , ⊢G , ok = inversion-ΠΣ ⊢ΠFG
        ⊢t = soundness⇇ t⇇G
    in  conv (lamⱼ′ ok ⊢t) (sym A≡ΠFG)
  soundness⇇ (prodᶜ A↘ΣFG t⇇F u⇇Gt) =
    let A≡ΣFG = subset* (proj₁ A↘ΣFG)
        _ , ⊢ΣFG = wf-⊢ A≡ΣFG
        _ , ⊢G , ok = inversion-ΠΣ ⊢ΣFG
        ⊢t = soundness⇇ t⇇F
        ⊢u = soundness⇇ u⇇Gt
    in  conv (prodⱼ ⊢G ⊢t ⊢u ok) (sym A≡ΣFG)
  soundness⇇ (rflᶜ (A↘Id , _) t≡u) =
    conv (rflⱼ′ t≡u) (sym (subset* A↘Id))
  soundness⇇ (infᶜ t⇉B A≡B) =
    conv (soundness⇉ (wf A≡B) t⇉B .proj₂) A≡B

  soundness⇇Level : ⊢ Γ → Γ ⊢ l ⇇Level → Γ ⊢ l ∷Level
  soundness⇇Level _ (term ok ⊢l) =
    term ok (soundness⇇ ⊢l)
  soundness⇇Level ⊢Γ (literal ok) =
    literal ok ⊢Γ
