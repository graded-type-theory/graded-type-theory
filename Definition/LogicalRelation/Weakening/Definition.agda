------------------------------------------------------------------------
-- Weakening of the definition context for the logical relation
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Weakening.Definition
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Unary R
import Definition.LogicalRelation.Weakening R as LW
open import Definition.LogicalRelation.Weakening.Restricted R

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R using (_»_∷ʷ_⊇_)
open import Definition.Typed.Weakening.Combined R
open import Definition.Typed.Weakening.Definition R as W
  hiding (defn-wk)

open import Definition.Untyped M
open import Definition.Untyped.Allowed-literal R
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant

open import Tools.Function
import Tools.Level as L
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private
  variable
    p : L.Level
    ∇ ∇′ : DCon (Term 0) _
    Γ Δ : Con Term _
    Η : Cons _ _
    A B t t′ u : Term _
    l l′ l₁ l₂ : Lvl _
    ρ : Wk _ _
    ℓ ℓ₁ ℓ₂ : Universe-level
    s : Strength
    ok₁ ok₂ : Level-allowed

opaque

  defn-wkEqTermNe :
    » ∇′ ⊇ ∇ → ∇ » Γ ⊩neNf t ≡ u ∷ A → ∇′ » Γ ⊩neNf t ≡ u ∷ A
  defn-wkEqTermNe ξ⊇ (neNfₜ₌ neK neM k≡m) =
    neNfₜ₌ (defn-wkNeutralᵃ ξ⊇ neK) (defn-wkNeutralᵃ ξ⊇ neM)
      (~-defn-wk ξ⊇ k≡m)

opaque mutual

  defn-wkEqTermℕ : » ∇′ ⊇ ∇ → ∇ » Γ ⊩ℕ t ≡ u ∷ℕ → ∇′ » Γ ⊩ℕ t ≡ u ∷ℕ
  defn-wkEqTermℕ ξ⊇ (ℕₜ₌ k k′ d d′ k≡k′ prop) =
    ℕₜ₌ k k′ (defn-wkRed*Term ξ⊇ d) (defn-wkRed*Term ξ⊇ d′)
        (≅ₜ-defn-wk ξ⊇ k≡k′) (defn-wk[Natural]-prop ξ⊇ prop)

  defn-wk[Natural]-prop :
    » ∇′ ⊇ ∇ →
    [Natural]-prop (∇ » Γ) t u → [Natural]-prop (∇′ » Γ) t u
  defn-wk[Natural]-prop ξ⊇ (sucᵣ [n≡n′]) = sucᵣ (defn-wkEqTermℕ ξ⊇ [n≡n′])
  defn-wk[Natural]-prop ξ⊇ zeroᵣ         = zeroᵣ
  defn-wk[Natural]-prop ξ⊇ (ne nf)       = ne (defn-wkEqTermNe ξ⊇ nf)

opaque

  defn-wk[Unit]-prop′ :
    » ∇′ ⊇ ∇ →
    [Unit]-prop′ (∇ » Γ) s t u → [Unit]-prop′ (∇′ » Γ) s t u
  defn-wk[Unit]-prop′ ξ⊇ starᵣ   = starᵣ
  defn-wk[Unit]-prop′ ξ⊇ (ne nf) = ne (defn-wkEqTermNe ξ⊇ nf)

opaque

  defn-wk[Unit]-prop :
    » ∇′ ⊇ ∇ →
    [Unit]-prop (∇ » Γ) s t u → [Unit]-prop (∇′ » Γ) s t u
  defn-wk[Unit]-prop ξ⊇ (Unitₜ₌ʷ prop no-η) =
    Unitₜ₌ʷ (defn-wk[Unit]-prop′ ξ⊇ prop) no-η
  defn-wk[Unit]-prop ξ⊇ (Unitₜ₌ˢ η) =
    Unitₜ₌ˢ η

opaque

  defn-wkEqTermUnit :
    » ∇′ ⊇ ∇ →
    ∇ » Γ ⊩Unit⟨ s ⟩ t ≡ u ∷Unit →
    ∇′ » Γ ⊩Unit⟨ s ⟩ t ≡ u ∷Unit
  defn-wkEqTermUnit ξ⊇ (Unitₜ₌ _ _ ↘u₁ ↘u₂ prop) =
    Unitₜ₌ _ _ (defn-wkRed↘Term ξ⊇ ↘u₁) (defn-wkRed↘Term ξ⊇ ↘u₂)
      (defn-wk[Unit]-prop ξ⊇ prop)

opaque mutual

  -- Weakening for _⊩Level_∷Level.

  defn-wk-⊩∷L :
    » ∇′ ⊇ ∇ → ∇ » Γ ⊩Level l ∷Level → ∇′ » Γ ⊩Level l ∷Level
  defn-wk-⊩∷L ∇′⊇∇ = λ where
    (term l⇒l′ l′-prop) →
      term (defn-wkRed*Term ∇′⊇∇ l⇒l′) (defn-wk-Level-prop ∇′⊇∇ l′-prop)
    (literal ok ⊢Γ) →
      literal ok (W.defn-wk ∇′⊇∇ ⊢Γ)

  -- Weakening for Level-prop.

  defn-wk-Level-prop :
    » ∇′ ⊇ ∇ → Level-prop (∇ » Γ) t → Level-prop (∇′ » Γ) t
  defn-wk-Level-prop ∇′⊇∇ = λ where
    (zeroᵘᵣ ok) →
      zeroᵘᵣ ok
    (sucᵘᵣ ok ⊩l) →
      sucᵘᵣ ok (defn-wk-⊩∷L ∇′⊇∇ ⊩l)
    (neLvl ⊩l) →
      neLvl (defn-wk-neLevel-prop ∇′⊇∇ ⊩l)

  -- Weakening for neLevel-prop.

  defn-wk-neLevel-prop :
    » ∇′ ⊇ ∇ → neLevel-prop (∇ » Γ) t → neLevel-prop (∇′ » Γ) t
  defn-wk-neLevel-prop ∇′⊇∇ = λ where
    (supᵘˡᵣ ⊩l₁ ⊩l₂) →
      supᵘˡᵣ (defn-wk-neLevel-prop ∇′⊇∇ ⊩l₁) (defn-wk-⊩∷L ∇′⊇∇ ⊩l₂)
    (supᵘʳᵣ ⊩l₁ ⊩l₂) →
      supᵘʳᵣ (defn-wk-⊩∷L ∇′⊇∇ ⊩l₁) (defn-wk-neLevel-prop ∇′⊇∇ ⊩l₂)
    (ne ⊩l) →
      ne (defn-wkEqTermNe ∇′⊇∇ ⊩l)

opaque mutual

  -- Weakening for _⊩Level_≡_∷Level.

  defn-wk-⊩≡∷L :
    » ∇′ ⊇ ∇ → ∇ » Γ ⊩Level l₁ ≡ l₂ ∷Level →
    ∇′ » Γ ⊩Level l₁ ≡ l₂ ∷Level
  defn-wk-⊩≡∷L ∇′⊇∇ = λ where
    (term l₁⇒l₁′ l₂⇒l₂′ l₁′≡l₂′) →
      term (defn-wkRed*Term ∇′⊇∇ l₁⇒l₁′) (defn-wkRed*Term ∇′⊇∇ l₂⇒l₂′)
        (defn-wk-[Level]-prop ∇′⊇∇ l₁′≡l₂′)
    (literal! ok ⊢Γ) →
      literal! ok (W.defn-wk ∇′⊇∇ ⊢Γ)

  -- Weakening for [Level]-prop.

  defn-wk-[Level]-prop :
    » ∇′ ⊇ ∇ → [Level]-prop (∇ » Γ) t u → [Level]-prop (∇′ » Γ) t u
  defn-wk-[Level]-prop ∇′⊇∇ = λ where
    (zeroᵘᵣ ok) →
      zeroᵘᵣ ok
    (sucᵘᵣ ok l₁≡l₂) →
      sucᵘᵣ ok (defn-wk-⊩≡∷L ∇′⊇∇ l₁≡l₂)
    (supᵘ-subᵣ ⊩l₁ l₁≤l₂) →
      supᵘ-subᵣ (defn-wk-neLevel-prop ∇′⊇∇ ⊩l₁)
        (defn-wk-⊩≡∷L ∇′⊇∇ l₁≤l₂)
    (neLvl l₁≡l₂) →
      neLvl (defn-wk-[neLevel]-prop ∇′⊇∇ l₁≡l₂)
    (sym l₂≡l₁) →
      sym (defn-wk-[Level]-prop ∇′⊇∇ l₂≡l₁)
    (trans l₁≡l₂ l₂≡l₃) →
      trans (defn-wk-[Level]-prop ∇′⊇∇ l₁≡l₂)
        (defn-wk-[Level]-prop ∇′⊇∇ l₂≡l₃)

  -- Weakening for [neLevel]-prop.

  defn-wk-[neLevel]-prop :
    » ∇′ ⊇ ∇ → [neLevel]-prop (∇ » Γ) t u → [neLevel]-prop (∇′ » Γ) t u
  defn-wk-[neLevel]-prop ∇′⊇∇ = λ where
    (supᵘˡᵣ l₁₁≡l₂₁ l₁₂≡l₂₂) →
      supᵘˡᵣ (defn-wk-[neLevel]-prop ∇′⊇∇ l₁₁≡l₂₁)
        (defn-wk-⊩≡∷L ∇′⊇∇ l₁₂≡l₂₂)
    (supᵘʳᵣ l₁₁≡l₂₁ l₁₂≡l₂₂) →
      supᵘʳᵣ (defn-wk-⊩≡∷L ∇′⊇∇ l₁₁≡l₂₁)
        (defn-wk-[neLevel]-prop ∇′⊇∇ l₁₂≡l₂₂)
    (supᵘ-zeroʳᵣ ⊩l) →
      supᵘ-zeroʳᵣ (defn-wk-neLevel-prop ∇′⊇∇ ⊩l)
    (supᵘ-assoc¹ᵣ ⊩l₁ ⊩l₂ ⊩l₃) →
      supᵘ-assoc¹ᵣ (defn-wk-neLevel-prop ∇′⊇∇ ⊩l₁)
        (defn-wk-⊩∷L ∇′⊇∇ ⊩l₂) (defn-wk-⊩∷L ∇′⊇∇ ⊩l₃)
    (supᵘ-assoc²ᵣ ⊩l₁ ⊩l₂ ⊩l₃) →
      supᵘ-assoc²ᵣ (defn-wk-⊩∷L ∇′⊇∇ ⊩l₁)
        (defn-wk-neLevel-prop ∇′⊇∇ ⊩l₂) (defn-wk-⊩∷L ∇′⊇∇ ⊩l₃)
    (supᵘ-assoc³ᵣ ⊩l₁ ⊩l₂ ⊩l₃) →
      supᵘ-assoc³ᵣ (defn-wk-⊩∷L ∇′⊇∇ ⊩l₁) (defn-wk-⊩∷L ∇′⊇∇ ⊩l₂)
        (defn-wk-neLevel-prop ∇′⊇∇ ⊩l₃)
    (supᵘ-comm¹ᵣ ⊩l₁₁ l₁₁≡l₂₂ ⊩l₂₁ l₁₂≡l₂₁) →
      supᵘ-comm¹ᵣ (defn-wk-neLevel-prop ∇′⊇∇ ⊩l₁₁)
        (defn-wk-⊩≡∷L ∇′⊇∇ l₁₁≡l₂₂) (defn-wk-neLevel-prop ∇′⊇∇ ⊩l₂₁)
        (defn-wk-⊩≡∷L ∇′⊇∇ l₁₂≡l₂₁)
    (supᵘ-comm²ᵣ ⊩l₁₁ 1+l₁₁≡l₂₂ ⊩l₁₂) →
      supᵘ-comm²ᵣ (defn-wk-⊩∷L ∇′⊇∇ ⊩l₁₁) (defn-wk-⊩≡∷L ∇′⊇∇ 1+l₁₁≡l₂₂)
        (defn-wk-neLevel-prop ∇′⊇∇ ⊩l₁₂)
    (supᵘ-idemᵣ ⊩l₁ l₁≡l₂) →
      supᵘ-idemᵣ (defn-wk-neLevel-prop ∇′⊇∇ ⊩l₁)
        (defn-wk-⊩≡∷L ∇′⊇∇ l₁≡l₂)
    (ne l₁≡l₂) →
      ne (defn-wkEqTermNe ∇′⊇∇ l₁≡l₂)

opaque
 unfolding ↑ⁿ defn-wk-⊩∷L
 mutual

  -- The function defn-wk-⊩∷L does not affect the result of ↑ⁿ.

  ↑ⁿ-defn-wk-⊩∷L :
    (∇′⊇∇ : » ∇′ ⊇ ∇) (⊩t : ∇ » Γ ⊩Level level t ∷Level) →
    ↑ⁿ ok₁ ⊩t PE.≡ ↑ⁿ ok₂ (defn-wk-⊩∷L ∇′⊇∇ ⊩t)
  ↑ⁿ-defn-wk-⊩∷L {ok₁} ∇′⊇∇ = λ where
    (term _ l′-prop) →
      ↑ⁿ-prop-defn-wk-Level-prop ∇′⊇∇ l′-prop
    (literal ok _) →
      Level-allowed→Allowed-literal→ ok₁ ok

  -- The function defn-wk-Level-prop does not affect the result of
  -- ↑ⁿ-prop.

  ↑ⁿ-prop-defn-wk-Level-prop :
    (∇′⊇∇ : » ∇′ ⊇ ∇) (⊩t : Level-prop (∇ » Γ) t) →
    ↑ⁿ-prop ok₁ ⊩t PE.≡ ↑ⁿ-prop ok₂ (defn-wk-Level-prop ∇′⊇∇ ⊩t)
  ↑ⁿ-prop-defn-wk-Level-prop ∇′⊇∇ = λ where
    (zeroᵘᵣ _) →
      PE.refl
    (sucᵘᵣ _ ⊩l) →
      PE.cong 1+ (↑ⁿ-defn-wk-⊩∷L ∇′⊇∇ ⊩l)
    (neLvl ⊩l) →
      ↑ⁿ-neprop-defn-wk-neLevel-prop ∇′⊇∇ ⊩l

  -- The function defn-wk-neLevel-prop does not affect the result of
  -- ↑ⁿ-neprop.

  ↑ⁿ-neprop-defn-wk-neLevel-prop :
    (∇′⊇∇ : » ∇′ ⊇ ∇) (⊩t : neLevel-prop (∇ » Γ) t) →
    ↑ⁿ-neprop ok₁ ⊩t PE.≡ ↑ⁿ-neprop ok₂ (defn-wk-neLevel-prop ∇′⊇∇ ⊩t)
  ↑ⁿ-neprop-defn-wk-neLevel-prop ∇′⊇∇ = λ where
    (supᵘˡᵣ ⊩l₁ ⊩l₂) →
      PE.cong₂ _⊔_ (↑ⁿ-neprop-defn-wk-neLevel-prop ∇′⊇∇ ⊩l₁)
        (↑ⁿ-defn-wk-⊩∷L ∇′⊇∇ ⊩l₂)
    (supᵘʳᵣ ⊩l₁ ⊩l₂) →
      PE.cong₂ _⊔_ (PE.cong 1+ (↑ⁿ-defn-wk-⊩∷L ∇′⊇∇ ⊩l₁))
        (↑ⁿ-neprop-defn-wk-neLevel-prop ∇′⊇∇ ⊩l₂)
    (ne _) →
      PE.refl

opaque
  unfolding ↑ᵘ defn-wk-⊩∷L

  -- The function defn-wk-⊩∷L does not affect the result of ↑ᵘ.

  ↑ᵘ-defn-wk-⊩∷L :
    {⊩l : ∇ » Γ ⊩Level l ∷Level}
    (∇′⊇∇ : » ∇′ ⊇ ∇) →
    ↑ᵘ ⊩l PE.≡ ↑ᵘ (defn-wk-⊩∷L ∇′⊇∇ ⊩l)
  ↑ᵘ-defn-wk-⊩∷L {⊩l = term _ _} ∇′⊇∇ =
    PE.cong 0ᵘ+ (↑ⁿ-defn-wk-⊩∷L ∇′⊇∇ _)
  ↑ᵘ-defn-wk-⊩∷L {⊩l = literal _ _} _ =
    PE.refl

opaque

  -- A variant of ↑ᵘ-irrelevance.

  ↑ᵘ-irrelevance-»⊇ :
    {⊩l : ∇′ » Γ ⊩Level l ∷Level}
    {⊩l′ : ∇ » Γ ⊩Level l ∷Level} →
    » ∇′ ⊇ ∇ →
    ↑ᵘ ⊩l PE.≡ ↑ᵘ ⊩l′
  ↑ᵘ-irrelevance-»⊇ {⊩l} {⊩l′} ∇′⊇∇ =
    ↑ᵘ ⊩l                      ≡⟨ ↑ᵘ-irrelevance ⟩
    ↑ᵘ (defn-wk-⊩∷L ∇′⊇∇ ⊩l′)  ≡˘⟨ ↑ᵘ-defn-wk-⊩∷L ∇′⊇∇ ⟩
    ↑ᵘ ⊩l′                     ∎

opaque

  -- A combination of LW.wk-↑ᵘ and ↑ᵘ-irrelevance-»⊇.

  ↑ᵘ-irrelevance-»∷ʷ⊇-»⊇ :
    {⊩l : ∇ » Γ ⊩Level l ∷Level}
    {⊩l′ : ∇′ » Δ ⊩Level l′ ∷Level} →
    » ∇′ ⊇ ∇ →
    ∇′ » ρ ∷ʷ Δ ⊇ Γ →
    wk ρ l PE.≡ l′ →
    ↑ᵘ ⊩l′ PE.≡ ↑ᵘ ⊩l
  ↑ᵘ-irrelevance-»∷ʷ⊇-»⊇ {⊩l} {⊩l′} ∇′⊇∇ Δ⊇Γ PE.refl =
    ↑ᵘ ⊩l′                    ≡⟨ LW.wk-↑ᵘ (»∷ʷ⊇→⊢ʷᵏ Δ⊇Γ) PE.refl ⟩
    ↑ᵘ (defn-wk-⊩∷L ∇′⊇∇ ⊩l)  ≡⟨ ↑ᵘ-irrelevance-»⊇ ∇′⊇∇ ⟩
    ↑ᵘ ⊩l                     ∎
