------------------------------------------------------------------------
-- Completeness of the bi-directional typechecking relations.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typechecking.Completeness
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typechecking R
open import Definition.Typechecking.Soundness R
open import Definition.Typed R
open import Definition.Typed.Properties R
import Definition.Typed.Weakening R as W
open import Definition.Typed.Consequences.Inequality R
open import Definition.Typed.Consequences.InverseUniv R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Reduction R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Consequences.Stability R
open import Definition.Typed.Consequences.Syntactic R
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
    t u A B : Term n

-- Bi-directional type checking relations are complete with respect to
-- their corresponding typing relations for Inferable/Checkable terms

mutual

  -- If A is a checkable type that is well-formed with respect to Γ,
  -- then Γ ⊢ A ⇇Type holds.

  completeness⇇Type : Checkable-type A → Γ ⊢ A → Γ ⊢ A ⇇Type
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
    let _ , A , U≡ = completeness⇉ A (inverseUniv ⊢A .proj₂) in
    univᶜ A (U-norm (sym U≡) , Uₙ)

  -- Completeness of type inference

  completeness⇉ : Inferable t → Γ ⊢ t ∷ A → ∃ λ B → Γ ⊢ t ⇉ B × Γ ⊢ A ≡ B
  completeness⇉ Uᵢ ⊢t =
    _ , Uᵢ , inversion-U ⊢t
  completeness⇉ (ΠΣᵢ B C) ⊢ΠΣ =
    let _ , _ , ⊢B , ⊢C , A≡U , ok = inversion-ΠΣ-U ⊢ΠΣ
        _ , B⇉D , U≡D              = completeness⇉ B ⊢B
        _ , C⇉E , U≡E              = completeness⇉ C ⊢C
    in
      _
    , ΠΣᵢ B⇉D (U-norm (sym U≡D) , Uₙ) C⇉E (U-norm (sym U≡E) , Uₙ) ok
    , A≡U
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
    let F , G , q , _ , ⊢G , ⊢t , A≡Gt = inversion-snd ⊢t
        B , t⇉B , ΣFG≡B = completeness⇉ t ⊢t
        F′ , G′ , B⇒Σ′ , F≡F′ , G≡G′ = ΣNorm (proj₁ (soundness⇉ (wfTerm ⊢t) t⇉B)) (sym ΣFG≡B)
    in
    _ , sndᵢ t⇉B (B⇒Σ′ , ΠΣₙ) ,
    trans A≡Gt (substTypeEq G≡G′ (refl (fstⱼ ⊢G ⊢t)))
  completeness⇉ (prodrecᵢ C t u) ⊢t =
    let F , G , q , ⊢F , ⊢G , ⊢C , ⊢t , ⊢u , A≡Ct = inversion-prodrec ⊢t
        ok = ⊢∷ΠΣ→ΠΣ-allowed ⊢t
        B , t⇉B , ΣFG≡B = completeness⇉ t ⊢t
        F′ , G′ , B⇒Σ′ , F≡F′ , G≡G′ = ΣNorm (proj₁ (soundness⇉ (wfTerm ⊢t) t⇉B)) (sym ΣFG≡B)
        u⇇C₊ = completeness⇇ u (stabilityTerm ((reflConEq (wf ⊢F)) ∙ F≡F′ ∙ G≡G′) ⊢u)
        C⇇Type = completeness⇇Type C $
                 stability (reflConEq (wf ⊢F) ∙ ΠΣ-cong F≡F′ G≡G′ ok) ⊢C
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
    in
      _
    , Idᵢ B⇉C (U-norm (sym U≡C) , Uₙ) (completeness⇇ t ⊢t)
        (completeness⇇ u ⊢u)
    , A≡U
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
  completeness⇉ ([]-congᵢ A t u v) ⊢[]-cong =
    case inversion-[]-cong ⊢[]-cong of λ {
      (⊢A , ⊢t , ⊢u , ⊢v , ok , ≡B) →
      _
    , []-congᵢ (completeness⇇Type A ⊢A) (completeness⇇ t ⊢t)
        (completeness⇇ u ⊢u) (completeness⇇ v ⊢v) ok
    , ≡B }

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
  completeness⇇ rflᶜ ⊢rfl =
    case inversion-rfl ⊢rfl of λ {
      (_ , _ , _ , _ , A≡Id-B-t-t) →
    case Id-norm A≡Id-B-t-t of λ {
      (_ , _ , _ , A⇒*Id-B′-t′-u′ , A≡A′ , t≡t′ , t≡u′) →
    rflᶜ (A⇒*Id-B′-t′-u′ , Idₙ)
      (conv (trans (sym t≡t′) t≡u′) A≡A′) }}
  completeness⇇ (infᶜ t) ⊢t =
    let B , t⇉B , A≡B = completeness⇉ t ⊢t
    in  infᶜ t⇉B (sym A≡B)
