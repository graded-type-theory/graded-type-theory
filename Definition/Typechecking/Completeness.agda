------------------------------------------------------------------------
-- Completeness of the bi-directional typechecking relations (in the
-- absence of equality reflection)
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typechecking.Completeness
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  ⦃ no-equality-reflection : No-equality-reflection ⦄
  where

open import Definition.Typechecking R
open import Definition.Typed R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.EqualityRelation.Instance R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Stability R
open import Definition.Typed.Substitution R
open import Definition.Typed.Syntactic R
import Definition.Typed.Weakening R as W
open import Definition.Typed.Well-formed R
open import Definition.Typed.Consequences.Inequality R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Reduction R
open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n
    l t u A B : Term n

  univᶜ′ : (∃ λ A → Γ ⊢ t ⇉ A × Γ ⊢ U l ≡ A) → Γ ⊢ t ⇇Type
  univᶜ′ (_ , t⇉ , U≡A) = univᶜ t⇉ (U-norm (sym U≡A) .proj₂ , Uₙ)

-- Bi-directional type checking relations are complete with respect to
-- their corresponding typing relations for Inferable/Checkable terms

mutual

  -- If A is a checkable type that is well-formed with respect to Γ,
  -- then Γ ⊢ A ⇇Type holds.

  completeness⇇Type : Checkable-type A → Γ ⊢ A → Γ ⊢ A ⇇Type
  completeness⇇Type (Liftᶜ l A) ⊢A =
    let ⊢l , ⊢A = inversion-Lift ⊢A in
    Liftᶜ (completeness⇇ l ⊢l) (completeness⇇Type A ⊢A)
  completeness⇇Type (ΠΣᶜ B C) ⊢A =
    let ⊢B , ⊢C , ok = inversion-ΠΣ ⊢A in
    ΠΣᶜ (completeness⇇Type B ⊢B) (completeness⇇Type C ⊢C) ok
  completeness⇇Type (Idᶜ B t u) ⊢A =
    let ⊢B , ⊢t , ⊢u = inversion-Id ⊢A in
    Idᶜ (completeness⇇Type B ⊢B) (completeness⇇ t ⊢t)
      (completeness⇇ u ⊢u)
  completeness⇇Type (checkᶜ A) ⊢A =
    completeness⇇Type′ A ⊢A

  -- If A is a checkable term for which Γ ⊢ A holds, then Γ ⊢ A ⇇Type
  -- holds.

  completeness⇇Type′ : Checkable A → Γ ⊢ A → Γ ⊢ A ⇇Type
  completeness⇇Type′ (liftᶜ _) (univ ⊢A) =
    let _ , _ , _ , U≡Lift = inversion-lift ⊢A in
    ⊥-elim (U≢Liftⱼ U≡Lift)
  completeness⇇Type′ (lamᶜ _) (univ ⊢A) =
    let _ , _ , _ , _ , _ , U≡Π , _ = inversion-lam ⊢A in
    ⊥-elim (U≢ΠΣⱼ U≡Π)
  completeness⇇Type′ (prodᶜ _ _) (univ ⊢A) =
    let _ , _ , _ , _ , _ , _ , _ , U≡Σ , _ = inversion-prod ⊢A in
    ⊥-elim (U≢ΠΣⱼ U≡Σ)
  completeness⇇Type′ rflᶜ (univ ⊢A) =
    let _ , _ , _ , _ , U≡Id = inversion-rfl ⊢A in
    ⊥-elim (Id≢U (sym U≡Id))
  completeness⇇Type′ (infᶜ A) ⊢A =
    completeness⇉Type A ⊢A

  completeness⇉Type : Inferable A → Γ ⊢ A → Γ ⊢ A ⇇Type
  completeness⇉Type Levelᵢ ⊢A =
    Levelᶜ
  completeness⇉Type zeroᵘᵢ (univ ⊢A) =
    univᶜ′ (completeness⇉ zeroᵘᵢ ⊢A)
  completeness⇉Type (sucᵘᵢ x) (univ ⊢A) =
    univᶜ′ (completeness⇉ (sucᵘᵢ x) ⊢A)
  completeness⇉Type (supᵘᵢ x x₁) (univ ⊢A) =
    univᶜ′ (completeness⇉ (supᵘᵢ x x₁) ⊢A)
  completeness⇉Type (Uᵢ x) ⊢A = Uᶜ (completeness⇇ x (inversion-U-Level ⊢A))
  completeness⇉Type (Liftᵢ x x₁) ⊢A =
    let ⊢l , ⊢A = inversion-Lift ⊢A
    in Liftᶜ (completeness⇇ x ⊢l) (completeness⇉Type x₁ ⊢A)
  completeness⇉Type (ΠΣᵢ x x₁) ⊢A =
    let ⊢A , ⊢B , ok = inversion-ΠΣ ⊢A
    in ΠΣᶜ (completeness⇉Type x ⊢A) (completeness⇇Type′ x₁ ⊢B) ok
  completeness⇉Type varᵢ (univ ⊢A) =
    univᶜ′ (completeness⇉ varᵢ ⊢A)
  completeness⇉Type (lowerᵢ x) (univ ⊢A) =
    univᶜ′ (completeness⇉ (lowerᵢ x) ⊢A)
  completeness⇉Type (∘ᵢ t u) (univ ⊢tu) =
    univᶜ′ (completeness⇉ (∘ᵢ t u) ⊢tu)
  completeness⇉Type (fstᵢ x) (univ ⊢A) =
    univᶜ′ (completeness⇉ (fstᵢ x) ⊢A)
  completeness⇉Type (sndᵢ x) (univ ⊢A) =
    univᶜ′ (completeness⇉ (sndᵢ x) ⊢A)
  completeness⇉Type (prodrecᵢ x x₁ x₂) (univ ⊢A) =
    univᶜ′ (completeness⇉ (prodrecᵢ x x₁ x₂) ⊢A)
  completeness⇉Type ℕᵢ ⊢A = ℕᶜ
  completeness⇉Type zeroᵢ (univ ⊢A) =
    univᶜ′ (completeness⇉ zeroᵢ ⊢A)
  completeness⇉Type (sucᵢ x) (univ ⊢A) =
    univᶜ′ (completeness⇉ (sucᵢ x) ⊢A)
  completeness⇉Type (natrecᵢ x x₁ x₂ x₃) (univ ⊢A) =
    univᶜ′ (completeness⇉ (natrecᵢ x x₁ x₂ x₃) ⊢A)
  completeness⇉Type Unitᵢ ⊢A =
    let ok = inversion-Unit ⊢A
    in Unitᶜ ok
  completeness⇉Type starᵢ (univ ⊢A) =
    univᶜ′ (completeness⇉ starᵢ ⊢A)
  completeness⇉Type (unitrecᵢ x₁ x₂ x₃) (univ ⊢A) =
    univᶜ′ (completeness⇉ (unitrecᵢ x₁ x₂ x₃) ⊢A)
  completeness⇉Type Emptyᵢ ⊢A = Emptyᶜ
  completeness⇉Type (emptyrecᵢ x x₁) (univ ⊢A) =
    univᶜ′ (completeness⇉ (emptyrecᵢ x x₁) ⊢A)
  completeness⇉Type (Idᵢ x x₁ x₂) ⊢A =
    let ⊢A , ⊢t , ⊢u = inversion-Id ⊢A
    in Idᶜ (completeness⇉Type x ⊢A) (completeness⇇ x₁ ⊢t) (completeness⇇ x₂ ⊢u)
  completeness⇉Type (Jᵢ x x₁ x₂ x₃ x₄ x₅) (univ ⊢A) =
    univᶜ′ (completeness⇉ (Jᵢ x x₁ x₂ x₃ x₄ x₅) ⊢A)
  completeness⇉Type (Kᵢ x x₁ x₂ x₃ x₄) (univ ⊢A) =
    univᶜ′ (completeness⇉ (Kᵢ x x₁ x₂ x₃ x₄) ⊢A)
  completeness⇉Type ([]-congᵢ ⊢l ⊢B ⊢t ⊢u ⊢v) (univ ⊢A) =
    univᶜ′ (completeness⇉ ([]-congᵢ ⊢l ⊢B ⊢t ⊢u ⊢v) ⊢A)

  -- Completeness of type inference

  completeness⇉ : Inferable t → Γ ⊢ t ∷ A → ∃ λ B → Γ ⊢ t ⇉ B × Γ ⊢ A ≡ B
  completeness⇉ Levelᵢ ⊢t =
    let A≡ , ok = inversion-Level ⊢t
    in _ , Levelᵢ ok , A≡
  completeness⇉ zeroᵘᵢ ⊢t = _ , zeroᵘᵢ , inversion-zeroᵘ ⊢t
  completeness⇉ (sucᵘᵢ t) ⊢t =
    let ⊢t , A≡Level = inversion-sucᵘ ⊢t
        t⇇Level = completeness⇇ t ⊢t
    in  _ , sucᵘᵢ t⇇Level , A≡Level
  completeness⇉ (supᵘᵢ t u) ⊢t =
    let ⊢t , ⊢u , A≡Level = inversion-supᵘ ⊢t
        t⇇Level = completeness⇇ t ⊢t
        u⇇Level = completeness⇇ u ⊢u
    in  _ , supᵘᵢ t⇇Level u⇇Level , A≡Level
  completeness⇉ (Uᵢ l) ⊢t =
    _ , Uᵢ (completeness⇇ l (inversion-U∷-Level ⊢t)) , inversion-U ⊢t
  completeness⇉ (Liftᵢ x x₁) ⊢t =
    let _ , ⊢l , ⊢A , ≡U = inversion-Lift∷ ⊢t
        _ , A⇉ , ≡B = completeness⇉ x₁ ⊢A
        _ , ⇒U = U-norm (sym ≡B)
    in _
    , Liftᵢ (completeness⇇ x ⊢l) A⇉ (⇒U , Uₙ)
    , trans ≡U (U-cong (supᵘ-cong (U-injectivity (trans ≡B (subset* ⇒U))) (refl ⊢l)))
  completeness⇉ (ΠΣᵢ B C) ⊢ΠΣ =
    let _ , _ , ⊢B , ⊢C , A≡U , ok = inversion-ΠΣ-U ⊢ΠΣ
        _ , B⇉D , U≡D              = completeness⇉ B ⊢B
        _ , ⇒U = U-norm (sym U≡D)
        U≡X = trans U≡D (subset* ⇒U)
        C⇇E = completeness⇇ C (conv ⊢C (W.wkEq₁ (univ ⊢B) U≡X))
    in
      _
    , ΠΣᵢ B⇉D (⇒U , Uₙ) C⇇E ok
    , trans A≡U U≡X
  completeness⇉ varᵢ ⊢t =
    let B , x∷B∈Γ , A≡B = inversion-var ⊢t
    in  _ , varᵢ x∷B∈Γ , A≡B
  completeness⇉ (lowerᵢ x) ⊢t =
    let _ , _ , ⊢t , U≡B = inversion-lower ⊢t
        _ , t⇉ , Lift≡ = completeness⇉ x ⊢t
        _ , _ , ⇒Lift = Lift-norm (sym Lift≡)
        _ , eq = Lift-injectivity (trans Lift≡ (subset* ⇒Lift))
    in _ , lowerᵢ t⇉ (⇒Lift , Liftₙ) , trans U≡B eq
  completeness⇉ (∘ᵢ t u) ⊢tu =
    let F , G , q , ⊢t , ⊢u , A≡Gu = inversion-app ⊢tu
        B , t⇉B , ΠFG≡B = completeness⇉ t ⊢t
        F′ , G′ , B⇒Π′ , F≡F′ , G≡G′ , _ = ΠΣNorm (sym ΠFG≡B)
        ⊢u′ = conv ⊢u F≡F′
        u⇇G = completeness⇇ u ⊢u′
    in  _ , appᵢ t⇉B (B⇒Π′ , ΠΣₙ) u⇇G , trans A≡Gu (substTypeEq G≡G′ (refl ⊢u))
  completeness⇉ (fstᵢ t) ⊢t =
    let F , G , q , ⊢F , ⊢G , ⊢t , A≡F = inversion-fst ⊢t
        B , t⇉B , ΣFG≡B = completeness⇉ t ⊢t
        F′ , G′ , B⇒Σ′ , F≡F′ , G≡G′ = ΠΣNorm (sym ΣFG≡B)
    in  _ , fstᵢ t⇉B (B⇒Σ′ , ΠΣₙ) , trans A≡F F≡F′
  completeness⇉ (sndᵢ t) ⊢t =
    let F , G , q , _ , ⊢G , ⊢t , A≡Gt = inversion-snd ⊢t
        B , t⇉B , ΣFG≡B = completeness⇉ t ⊢t
        F′ , G′ , B⇒Σ′ , F≡F′ , G≡G′ , _ = ΠΣNorm (sym ΣFG≡B)
    in
    _ , sndᵢ t⇉B (B⇒Σ′ , ΠΣₙ) ,
    trans A≡Gt (substTypeEq G≡G′ (refl (fstⱼ ⊢G ⊢t)))
  completeness⇉ (prodrecᵢ C t u) ⊢t =
    let F , G , q , _ , ⊢G , ⊢C , ⊢t , ⊢u , A≡Ct = inversion-prodrec ⊢t
        ok = ⊢∷ΠΣ→ΠΣ-allowed ⊢t
        B , t⇉B , ΣFG≡B = completeness⇉ t ⊢t
        F′ , G′ , B⇒Σ′ , F≡F′ , G≡G′ , _ = ΠΣNorm (sym ΣFG≡B)
        u⇇C₊ = completeness⇇ u (stabilityTerm (refl-∙ F≡F′ ∙ G≡G′) ⊢u)
        C⇇Type = completeness⇇Type C $
                 stability (refl-∙ (ΠΣ-cong F≡F′ G≡G′ ok)) ⊢C
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
  completeness⇉ (unitrecᵢ A t u) ⊢t =
    case inversion-unitrec ⊢t of λ {
      (⊢A , ⊢t , ⊢u , A≡Ct) →
    case completeness⇇Type A ⊢A of λ
      A⇇Type →
    case completeness⇇ t ⊢t of λ
      t⇇Unit →
    case completeness⇇ u ⊢u of λ
      u⇇A₊ →
    _ , unitrecᵢ A⇇Type t⇇Unit u⇇A₊ , A≡Ct }
  completeness⇉ Emptyᵢ ⊢t = _ , Emptyᵢ , inversion-Empty ⊢t
  completeness⇉ (emptyrecᵢ C t) ⊢t =
    let ⊢C , ⊢t , A≡C = inversion-emptyrec ⊢t
        t⇇Empty = completeness⇇ t ⊢t
        C⇇Type = completeness⇇Type C ⊢C
    in  _ , emptyrecᵢ C⇇Type t⇇Empty , A≡C
  completeness⇉ (Idᵢ B t u) ⊢Id =
    let _ , ⊢B , ⊢t , ⊢u , A≡U = inversion-Id-U ⊢Id
        _ , B⇉C , U≡C          = completeness⇉ B ⊢B
        _ , ⇒U = U-norm (sym U≡C)
    in
      _
    , Idᵢ B⇉C (⇒U , Uₙ) (completeness⇇ t ⊢t) (completeness⇇ u ⊢u)
    , trans A≡U (trans U≡C (subset* ⇒U))
  completeness⇉ (Jᵢ A t B u v w) ⊢J =
    case inversion-J ⊢J of λ {
      (⊢A , ⊢t , ⊢B , ⊢u , ⊢v , ⊢w , ≡B) →
      _
    , Jᵢ (completeness⇇Type A ⊢A) (completeness⇇ t ⊢t)
        (completeness⇇Type B ⊢B) (completeness⇇ u ⊢u)
        (completeness⇇ v ⊢v) (completeness⇇ w ⊢w)
    , ≡B }
  completeness⇉ (Kᵢ A t B u v) ⊢K =
    case inversion-K ⊢K of λ {
      (⊢A , ⊢t , ⊢B , ⊢u , ⊢v , ok , ≡B) →
      _
    , Kᵢ (completeness⇇Type A ⊢A) (completeness⇇ t ⊢t)
        (completeness⇇Type B ⊢B) (completeness⇇ u ⊢u)
        (completeness⇇ v ⊢v) ok
    , ≡B }
  completeness⇉ ([]-congᵢ l A t u v) ⊢[]-cong =
    let ⊢A , ⊢t , ⊢u , ⊢v , ok , ≡B = inversion-[]-cong ⊢[]-cong
        ⊢l                          = inversion-U-Level (wf-⊢∷ ⊢A)
    in
    _ ,
    []-congᵢ (completeness⇇ l ⊢l) (completeness⇇ A ⊢A)
      (completeness⇇ t ⊢t) (completeness⇇ u ⊢u) (completeness⇇ v ⊢v)
      ok ,
    ≡B

  -- Completeness of type checking

  completeness⇇ : Checkable t → Γ ⊢ t ∷ A → Γ ⊢ t ⇇ A
  completeness⇇ (liftᶜ t) ⊢t =
    let _ , _ , x , A≡Lift = inversion-lift ⊢t
        _ , _ , A⇒Lift = Lift-norm A≡Lift
        t⇇ = completeness⇇ t (conv x (Lift-injectivity (trans (sym A≡Lift) (subset* A⇒Lift)) .proj₂))
    in liftᶜ (A⇒Lift , Liftₙ) t⇇
  completeness⇇ (lamᶜ t) ⊢t =
    let F , G , q , _ , ⊢t , A≡ΠFG , _ = inversion-lam ⊢t
        F′ , G′ , A⇒ΠF′G′ , F≡F′ , G≡G′ , _ = ΠΣNorm A≡ΠFG
        t⇇G = completeness⇇ t
                (stabilityTerm (refl-∙ F≡F′) (conv ⊢t G≡G′))
    in  lamᶜ (A⇒ΠF′G′ , ΠΣₙ) t⇇G
  completeness⇇ (prodᶜ t u) ⊢t =
    let F , G , m , ⊢F , ⊢G , ⊢t , ⊢u , A≡ΣFG , _ = inversion-prod ⊢t
        F′ , G′ , A⇒ΣF′G′ , F≡F′ , G≡G′ , _ = ΠΣNorm A≡ΣFG
        t⇇F = completeness⇇ t (conv ⊢t F≡F′)
        u⇇Gt = completeness⇇ u (conv ⊢u (substTypeEq G≡G′ (refl ⊢t)))
    in  prodᶜ (A⇒ΣF′G′ , ΠΣₙ) t⇇F u⇇Gt
  completeness⇇ rflᶜ ⊢rfl =
    case inversion-rfl ⊢rfl of λ {
      (_ , _ , _ , _ , A≡Id-B-t-t) →
    case Id-norm A≡Id-B-t-t of λ {
      (_ , _ , _ , A⇒*Id-B′-t′-u′ , A≡A′ , t≡t′ , t≡u′) →
    rflᶜ (A⇒*Id-B′-t′-u′ , Idₙ)
      (conv (trans (sym′ t≡t′) t≡u′) A≡A′) }}
  completeness⇇ (infᶜ t) ⊢t =
    let B , t⇉B , A≡B = completeness⇉ t ⊢t
    in  infᶜ t⇉B (sym A≡B)
