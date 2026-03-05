------------------------------------------------------------------------
-- Validity for Erased and [_]
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality
open import Tools.Product

module Definition.LogicalRelation.Substitution.Introductions.Erased
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  -- Erased is assumed to be allowed.
  {s}
  (Erased-ok@(Unit-ok , Σ-ok) : Erased-allowed s)
  ⦃ eqrel : EqRelSet R ⦄
  where

open EqRelSet eqrel

open import Definition.LogicalRelation R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Hidden R ⦃ eqrel ⦄
import Definition.LogicalRelation.Hidden.Restricted R ⦃ eqrel ⦄ as R
open import Definition.LogicalRelation.Properties R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Substitution R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Substitution.Introductions.Level R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Substitution.Introductions.Lift
  R ⦃ eqrel ⦄
open import
  Definition.LogicalRelation.Substitution.Introductions.Pi-Sigma R ⦃ eqrel ⦄
open import
  Definition.LogicalRelation.Substitution.Introductions.Sigma R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Substitution.Introductions.Unit R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Weakening R
open import Definition.LogicalRelation.Weakening.Definition
  R ⦃ eqrel = eqrel ⦄
open import Definition.LogicalRelation.Weakening.Restricted R ⦃ eqrel ⦄
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R
open import Definition.Typed.Weakening.Definition R using (»_⊇_)
open import Definition.Typed.Well-formed R
open import Definition.Untyped M as U
open import Definition.Untyped.Erased 𝕄 s
open import Definition.Untyped.Properties M

open import Tools.Function
import Tools.PropositionalEquality as PE

private variable
  ∇ ∇′        : DCon _ _
  Δ Η         : Con _ _
  Γ           : Cons _ _
  A A₁ A₂ t u : Term _
  l l₁ l₂     : Lvl _
  ρ           : Wk _ _
  ℓ ℓ′        : Universe-level

private opaque

  -- A lemma used below.

  wk-Lift-Unit[]₀≡ :
    ∇ » Δ ⊩Level l₁ ≡ l₂ ∷Level →
    » ∇′ ⊇ ∇ →
    ∇′ » ρ ∷ʷʳ Η ⊇ Δ →
    ∇′ » Η ⊩⟨ ℓ ⟩ U.wk (lift ρ) (Lift (wk1 l₁) (Unit s)) [ t ]₀ ≡
      U.wk (lift ρ) (Lift (wk1 l₂) (Unit s)) [ u ]₀
  wk-Lift-Unit[]₀≡ {l₁} {l₂} l₁≡l₂ ∇′⊇∇ ρ∷ =
    let l₁≡l₂ = defn-wk-⊩≡∷L ∇′⊇∇ l₁≡l₂ in
    PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
      (PE.sym $ PE.cong (flip Lift _) $
       PE.trans (PE.cong _[ _ ]₀ $ lift-wk1 _ l₁) $
       step-sgSubst _ _)
      (PE.sym $ PE.cong (flip Lift _) $
       PE.trans (PE.cong _[ _ ]₀ $ lift-wk1 _ l₂) $
       step-sgSubst _ _) $
    ⊩Lift≡⇔ .proj₂
      ( _
      , _
      , id
          (Liftⱼ
             (wkLevel (∷ʷʳ⊇→∷ʷ⊇ ρ∷) $
              wf-⊢≡∷L (⊢≅∷L→⊢≡∷L (escapeLevelEq l₁≡l₂)) .proj₂)
             (⊢Unit (wf-∷ʷʳ⊇ ρ∷) Unit-ok))
      , wkEqTermLevel (∷ʷʳ⊇→∷ʷ⊇ ρ∷) l₁≡l₂
      , refl-⊩≡ (emb-⊩ 0≤ᵘ (⊩Unit (wf-∷ʷʳ⊇ ρ∷) Unit-ok))
      )

opaque
  unfolding Erased

  -- Reducibility for Erased.

  ⊩Erased :
    Γ ⊩Level l ∷Level → Γ ⊩⟨ ℓ ⟩ A → Γ ⊩⟨ ℓ ⟩ Erased l A
  ⊩Erased {l} ⊩l ⊩A =
    let ⊢A = escape-⊩ ⊩A in
    ⊩ΠΣ⇔ .proj₂
      ( ≅-ΠΣ-cong (escape-⊩≡ $ refl-⊩≡ ⊩A)
          (≅-Lift-cong
             (wk-⊢≅∷L (stepʷ id ⊢A) (escapeLevelEq (reflLevel ⊩l))) $
           ≅-Unit-refl (∙ ⊢A) Unit-ok)
          Σ-ok
      , λ ∇′⊇∇ ρ⊇ →
            wk-⊩ ρ⊇ (defn-wk ∇′⊇∇ ⊩A)
          , λ _ → wk-Lift-Unit[]₀≡ (reflLevel ⊩l) ∇′⊇∇ ρ⊇
      )

opaque
  unfolding Erased

  -- Reducibility of equality between applications of Erased.

  ⊩Erased≡Erased :
    Γ ⊩Level l₁ ≡ l₂ ∷Level →
    Γ ⊩⟨ ℓ ⟩ A₁ ≡ A₂ →
    Γ ⊩⟨ ℓ ⟩ Erased l₁ A₁ ≡ Erased l₂ A₂
  ⊩Erased≡Erased {l₁} {l₂} l₁≡l₂ A₁≡A₂ =
    let ⊩l₁ , ⊩l₂ = wf-Level-eq l₁≡l₂
        ⊩A₁ , ⊩A₂ = wf-⊩≡ A₁≡A₂
    in
    ⊩ΠΣ≡ΠΣ⇔ .proj₂
      ( ⊩Erased ⊩l₁ ⊩A₁
      , ⊩Erased ⊩l₂ ⊩A₂
      , ≅-ΠΣ-cong (escape-⊩≡ A₁≡A₂)
          (≅-Lift-cong
             (wk-⊢≅∷L (stepʷ id (escape-⊩ ⊩A₁)) (escapeLevelEq l₁≡l₂)) $
           ≅-Unit-refl (∙ escape-⊩ ⊩A₁) Unit-ok) Σ-ok
      , PE.refl , PE.refl , PE.refl
      , λ ∇′⊇∇ ρ⊇ →
            wk-⊩≡ ρ⊇ (defn-wk-⊩≡ ∇′⊇∇ A₁≡A₂)
          , λ _ → wk-Lift-Unit[]₀≡ l₁≡l₂ ∇′⊇∇ ρ⊇
      )

opaque

  -- Validity of equality preservation for Erased.

  Erased-congᵛ :
    Γ ⊩ᵛ⟨ ℓ′ ⟩ l₁ ≡ l₂ ∷Level →
    Γ ⊩ᵛ⟨ ℓ ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ ℓ ⟩ Erased l₁ A₁ ≡ Erased l₂ A₂
  Erased-congᵛ l₁≡l₂ A₁≡A₂ =
    case ⊩ᵛ≡⇔ʰ .proj₁ A₁≡A₂ of λ
      (⊩Γ , A₁≡A₂) →
    ⊩ᵛ≡⇔ʰ .proj₂
      ( ⊩Γ
      , λ ∇′⊇∇ σ₁≡σ₂ →
          PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
            (PE.sym Erased-[]) (PE.sym Erased-[]) $
          ⊩Erased≡Erased
            (⊩ᵛ≡∷L→⊩ˢ≡∷→⊩[]≡[]∷L (defn-wk-⊩ᵛ≡∷L ∇′⊇∇ l₁≡l₂) σ₁≡σ₂)
            (A₁≡A₂ ∇′⊇∇ σ₁≡σ₂)
      )

opaque

  -- Validity of Erased.

  Erasedᵛ :
    Γ ⊩ᵛ⟨ ℓ′ ⟩ l ∷Level →
    Γ ⊩ᵛ⟨ ℓ ⟩ A →
    Γ ⊩ᵛ⟨ ℓ ⟩ Erased l A
  Erasedᵛ ⊩l =
    ⊩ᵛ⇔⊩ᵛ≡ .proj₂ ∘→ Erased-congᵛ (refl-⊩ᵛ≡∷L ⊩l) ∘→ ⊩ᵛ⇔⊩ᵛ≡ .proj₁

opaque
  unfolding Erased [_]

  -- Reducibility of equality between applications of [_].

  ⊩[]≡[] :
    Γ ⊩Level l ∷Level →
    Γ ⊩⟨ ℓ ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ ℓ ⟩ [ t ] ≡ [ u ] ∷ Erased l A
  ⊩[]≡[] ⊩l t≡u =
    let ⊩A = wf-⊩∷ (wf-⊩≡∷ t≡u .proj₁)
        ⊢A = escape-⊩ ⊩A
        ⊢Γ = wf ⊢A
    in
    ⊩prod≡prod
      (Liftⱼ (wkLevel₁ ⊢A (escapeLevel ⊩l)) (⊢Unit (∙ ⊢A) Unit-ok))
      (⊩Erased ⊩l ⊩A) t≡u
      (refl-⊩≡∷ $
       ⊩lift
         (PE.subst (_⊩Level_∷Level _) (PE.sym $ wk1-sgSubst _ _)
            ⊩l)
         (⊩Unit ⊢Γ Unit-ok) (⊩star ⊢Γ Unit-ok))

opaque

  -- Reducibility for [_].

  ⊩[] :
    Γ ⊩Level l ∷Level →
    Γ ⊩⟨ ℓ ⟩ t ∷ A →
    Γ ⊩⟨ ℓ ⟩ [ t ] ∷ Erased l A
  ⊩[] ⊩l = ⊩∷⇔⊩≡∷ .proj₂ ∘→ ⊩[]≡[] ⊩l ∘→ ⊩∷⇔⊩≡∷ .proj₁

opaque

  -- Validity of equality preservation for [_].

  []-congᵛ :
    Γ ⊩ᵛ⟨ ℓ′ ⟩ l ∷Level →
    Γ ⊩ᵛ⟨ ℓ ⟩ t ≡ u ∷ A →
    Γ ⊩ᵛ⟨ ℓ ⟩ [ t ] ≡ [ u ] ∷ Erased l A
  []-congᵛ ⊩l t≡u =
    case ⊩ᵛ≡∷⇔ .proj₁ t≡u of λ
      (⊩A , _) →
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( Erasedᵛ ⊩l ⊩A
      , λ ∇′⊇∇ σ₁≡σ₂ →
          PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _)
            (PE.sym []-[]) (PE.sym []-[]) (PE.sym Erased-[]) $
          ⊩[]≡[]
            (⊩ᵛ∷L→⊩ˢ∷→⊩[]∷L (defn-wk-⊩ᵛ∷L ∇′⊇∇ ⊩l)
               (wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₁)) $
          R.⊩≡∷→ (⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ∇′⊇∇ t≡u) σ₁≡σ₂)
      )

opaque

  -- Validity of [_].

  []ᵛ :
    Γ ⊩ᵛ⟨ ℓ′ ⟩ l ∷Level →
    Γ ⊩ᵛ⟨ ℓ ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ ℓ ⟩ [ t ] ∷ Erased l A
  []ᵛ ⊩l = ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ ∘→ []-congᵛ ⊩l ∘→ ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁
