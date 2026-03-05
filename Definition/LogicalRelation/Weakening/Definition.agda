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
open import Definition.Typed.Weakening.Definition R as W
  hiding (defn-wk; defn-wkTerm; defn-wkEq; defn-wkEqTerm)

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

  defn-wkTermNe : » ∇′ ⊇ ∇ → ∇ » Γ ⊩neNf t ∷ A → ∇′ » Γ ⊩neNf t ∷ A
  defn-wkTermNe ξ⊇ (neNfₜ neK k≡k) =
    neNfₜ (defn-wkNeutralᵃ ξ⊇ neK) (~-defn-wk ξ⊇ k≡k)

opaque mutual

  defn-wkTermℕ : » ∇′ ⊇ ∇ → ∇ » Γ ⊩ℕ t ∷ℕ → ∇′ » Γ ⊩ℕ t ∷ℕ
  defn-wkTermℕ ξ⊇ (ℕₜ n d n≡n prop) =
    ℕₜ n (defn-wkRed*Term ξ⊇ d) (≅ₜ-defn-wk ξ⊇ n≡n) (defn-wkNatural-prop ξ⊇ prop)

  defn-wkNatural-prop :
    » ∇′ ⊇ ∇ → Natural-prop (∇ » Γ) t → Natural-prop (∇′ » Γ) t
  defn-wkNatural-prop ξ⊇ (sucᵣ n) = sucᵣ (defn-wkTermℕ ξ⊇ n)
  defn-wkNatural-prop ξ⊇ zeroᵣ    = zeroᵣ
  defn-wkNatural-prop ξ⊇ (ne nf)  = ne (defn-wkTermNe ξ⊇ nf)

opaque

  defn-wkUnit-prop′ :
    » ∇′ ⊇ ∇ → Unit-prop′ (∇ » Γ) s t → Unit-prop′ (∇′ » Γ) s t
  defn-wkUnit-prop′ ξ⊇ starᵣ   = starᵣ
  defn-wkUnit-prop′ ξ⊇ (ne nf) = ne (defn-wkTermNe ξ⊇ nf)

opaque

  defn-wkUnit-prop :
    » ∇′ ⊇ ∇ → Unit-prop (∇ » Γ) s t → Unit-prop (∇′ » Γ) s t
  defn-wkUnit-prop ξ⊇ (Unitₜʷ prop no-η) =
    Unitₜʷ (defn-wkUnit-prop′ ξ⊇ prop) no-η
  defn-wkUnit-prop ξ⊇ (Unitₜˢ η) =
    Unitₜˢ η

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
      literal ok (defn-wk′ ∇′⊇∇ ⊢Γ)

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
      literal! ok (defn-wk′ ∇′⊇∇ ⊢Γ)

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
    ↑ᵘ ⊩l′                    ≡⟨ LW.wk-↑ᵘ Δ⊇Γ PE.refl ⟩
    ↑ᵘ (defn-wk-⊩∷L ∇′⊇∇ ⊩l)  ≡⟨ ↑ᵘ-irrelevance-»⊇ ∇′⊇∇ ⟩
    ↑ᵘ ⊩l                     ∎

private opaque

  -- A lemma used below.

  cast-⊩↑ᵘ≡/ :
    (⊩l : ∇ » Γ ⊩Level l ∷Level)
    (∇′⊇∇ : » ∇′ ⊇ ∇)
    (⊩A : ∇′ » Γ ⊩⟨ ↑ᵘ ⊩l ⟩ A) →
    ∇′ » Γ ⊩⟨ ↑ᵘ ⊩l ⟩ A ≡ B / ⊩A →
    ∇′ » Γ ⊩⟨ ↑ᵘ (defn-wk-⊩∷L ∇′⊇∇ ⊩l) ⟩ A ≡ B /
      PE.subst (flip (_⊩⟨_⟩_ _) _) (↑ᵘ-defn-wk-⊩∷L ∇′⊇∇) ⊩A
  cast-⊩↑ᵘ≡/ ⊩l ∇′⊇∇ ⊩A A≡B = lemma _ _ A≡B
    where
    lemma :
      (ℓ₁≡ℓ₂ : ℓ₁ PE.≡ ℓ₂)
      (⊩A : Η ⊩⟨ ℓ₁ ⟩ A) →
      Η ⊩⟨ ℓ₁ ⟩ A ≡ B / ⊩A →
      Η ⊩⟨ ℓ₂ ⟩ A ≡ B / PE.subst (flip (_⊩⟨_⟩_ _) _) ℓ₁≡ℓ₂ ⊩A
    lemma PE.refl _ A≡B = A≡B

private

  _•ᵈ→_ :
    ∀ {κ} {∇ : DCon (Term 0) κ} →
    {P : ∀ {κ′} {∇′ : DCon (Term 0) κ′}
       → ([ξ] : » ∇′ ⊇ ∇) → Set p} →
    ∀ {κ*} {∇* : DCon (Term 0) κ*} →
    ([ξ*] : » ∇* ⊇ ∇) →
    (∀ {κ′} {∇′ : DCon (Term 0) κ′}
     → ([ξ] : » ∇′ ⊇ ∇) → P [ξ]) →
    (∀ {κ′} {∇′ : DCon (Term 0) κ′}
     → ([ξ] : » ∇′ ⊇ ∇*) → P (»⊇-trans [ξ] [ξ*]))
  [ξ*] •ᵈ→ f = λ [ξ] → f (»⊇-trans [ξ] [ξ*])

private

  -- Types and lemmas used to implement defn-wk, defn-wkEq and
  -- defn-wkEqTerm.

  record Defn-wk (ℓ : Universe-level) : Set a where
    field
      defn-wk       : » ∇′ ⊇ ∇ → ∇ » Γ ⊩⟨ ℓ ⟩ A → ∇′ » Γ ⊩⟨ ℓ ⟩ A

      defn-wkEq     : (∇′⊇∇ : » ∇′ ⊇ ∇) (⊩A : ∇ » Γ ⊩⟨ ℓ ⟩ A) →
                      ∇ » Γ ⊩⟨ ℓ ⟩ A ≡ B / ⊩A →
                      ∇′ » Γ ⊩⟨ ℓ ⟩ A ≡ B / defn-wk ∇′⊇∇ ⊩A

      defn-wkEqTerm : (∇′⊇∇ : » ∇′ ⊇ ∇) (⊩A : ∇ » Γ ⊩⟨ ℓ ⟩ A) →
                      ∇ » Γ ⊩⟨ ℓ ⟩ t ≡ u ∷ A / ⊩A →
                      ∇′ » Γ ⊩⟨ ℓ ⟩ t ≡ u ∷ A / defn-wk ∇′⊇∇ ⊩A

  module Defn-wk-inhabited (rec : ∀ {ℓ′} → ℓ′ <ᵘ ℓ → Defn-wk ℓ′) where

    module Rec {ℓ′} (<ℓ : ℓ′ <ᵘ ℓ) = Defn-wk (rec <ℓ)

    opaque
     unfolding »⊇-trans
     mutual

      defn-wk :
        » ∇′ ⊇ ∇ →
        ∇ » Γ ⊩⟨ ℓ ⟩ A →
        ∇′ » Γ ⊩⟨ ℓ ⟩ A
      defn-wk ξ⊇ (Levelᵣ ⇒*Level) =
        Levelᵣ (defn-wkRed* ξ⊇ ⇒*Level)
      defn-wk ξ⊇ (Uᵣ′ _ ⊩k k< D) =
        Uᵣ′ _ (defn-wk-⊩∷L ξ⊇ ⊩k)
          (PE.subst (flip _<ᵘ_ _) (↑ᵘ-defn-wk-⊩∷L ξ⊇) k<)
          (defn-wkRed* ξ⊇ D)
      defn-wk ξ⊇ (Liftᵣ′ ⇒*Lift ⊩l ⊩A) =
        Liftᵣ′ (defn-wkRed* ξ⊇ ⇒*Lift) (defn-wk-⊩∷L ξ⊇ ⊩l)
          (defn-wk ξ⊇ ⊩A)
      defn-wk ξ⊇ (ℕᵣ D) = ℕᵣ (defn-wkRed* ξ⊇ D)
      defn-wk ξ⊇ (Emptyᵣ D) = Emptyᵣ (defn-wkRed* ξ⊇ D)
      defn-wk ξ⊇ (Unitᵣ′ D ok) = Unitᵣ′ (defn-wkRed* ξ⊇ D) ok
      defn-wk ξ⊇ (ne′ K* D neK K≡K) =
        ne′ K* (defn-wkRed* ξ⊇ D) (defn-wkNeutral ξ⊇ neK)
          (≅-defn-wk ξ⊇ K≡K)
      defn-wk ξ⊇ (Bᵣ′ W F G D A≡A [F] [G] G-ext ok) =
        Bᵣ′ W F G (defn-wkRed* ξ⊇ D) (≅-defn-wk ξ⊇ A≡A)
            (ξ⊇ •ᵈ→ [F]) (ξ⊇ •ᵈ→ [G]) (ξ⊇ •ᵈ→ G-ext) ok
      defn-wk ξ⊇ (Idᵣ ⊩A) = Idᵣ (record
        { ⇒*Id = defn-wkRed* ξ⊇ ⇒*Id
        ; ⊩Ty  = defn-wk ξ⊇ ⊩Ty
        ; ⊩lhs = defn-wkTerm ξ⊇ ⊩Ty ⊩lhs
        ; ⊩rhs = defn-wkTerm ξ⊇ ⊩Ty ⊩rhs
        })
        where
        open _⊩ₗId_ ⊩A

      defn-wkTerm :
        (ξ⊇ : » ∇′ ⊇ ∇) →
        ([A] : ∇ » Γ ⊩⟨ ℓ ⟩ A) →
        ∇ » Γ ⊩⟨ ℓ ⟩ t ∷ A / [A] →
        ∇′ » Γ ⊩⟨ ℓ ⟩ t ∷ A / defn-wk ξ⊇ [A]
      defn-wkTerm = defn-wkEqTerm

      defn-wkEq :
        (ξ⊇ : » ∇′ ⊇ ∇) →
        ([A] : ∇ » Γ ⊩⟨ ℓ ⟩ A) →
        ∇ » Γ ⊩⟨ ℓ ⟩ A ≡ B / [A] →
        ∇′ » Γ ⊩⟨ ℓ ⟩ A ≡ B / defn-wk ξ⊇ [A]
      defn-wkEq ξ⊇ (Levelᵣ _) ⇒*Level =
        defn-wkRed* ξ⊇ ⇒*Level
      defn-wkEq ξ⊇ (Uᵣ′ _ _ _ _) (U₌ _ ⇒*U l₁≡l₂) =
        U₌ _ (defn-wkRed* ξ⊇ ⇒*U) (defn-wk-⊩≡∷L ξ⊇ l₁≡l₂)
      defn-wkEq ξ⊇ (Liftᵣ′ _ _ ⊩A) (Lift₌ ⇒*Lift l₁≡l₂ A₁≡A₂) =
        Lift₌ (defn-wkRed* ξ⊇ ⇒*Lift) (defn-wk-⊩≡∷L ξ⊇ l₁≡l₂)
          (defn-wkEq ξ⊇ ⊩A A₁≡A₂)
      defn-wkEq ξ⊇ (ℕᵣ D) A≡B = defn-wkRed* ξ⊇ A≡B
      defn-wkEq ξ⊇ (Emptyᵣ D) A≡B = defn-wkRed* ξ⊇ A≡B
      defn-wkEq ξ⊇ (Unitᵣ′ _ _) (Unit₌ B⇒*) = Unit₌ (defn-wkRed* ξ⊇ B⇒*)
      defn-wkEq ξ⊇ (ne′ K* D neK K≡K) (ne₌ M D′ neM K≡M) =
        ne₌ M (defn-wkRed* ξ⊇ D′) (defn-wkNeutral ξ⊇ neM)
          (≅-defn-wk ξ⊇ K≡M)
      defn-wkEq ξ⊇ (Bᵣ′ W F G D A≡A [F] [G] G-ext ok)
                (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
        B₌ F′ G′ (defn-wkRed* ξ⊇ D′)
                 (≅-defn-wk ξ⊇ A≡B)
                 (ξ⊇ •ᵈ→ [F≡F′])
                 (ξ⊇ •ᵈ→ [G≡G′])
      defn-wkEq ξ⊇ (Idᵣ ⊩A) A≡B =
        Id₌′ (defn-wkRed* ξ⊇ ⇒*Id′)
             (defn-wkEq ξ⊇ ⊩Ty Ty≡Ty′)
             (defn-wkEqTerm ξ⊇ ⊩Ty lhs≡lhs′)
             (defn-wkEqTerm ξ⊇ ⊩Ty rhs≡rhs′)
        where
        open _⊩ₗId_ ⊩A
        open _⊩ₗId_≡_/_ A≡B

      defn-wkEqTerm :
        (ξ⊇ : » ∇′ ⊇ ∇) →
        ([A] : ∇ » Γ ⊩⟨ ℓ ⟩ A) →
        ∇ » Γ ⊩⟨ ℓ ⟩ t ≡ u ∷ A / [A] →
        ∇′ » Γ ⊩⟨ ℓ ⟩ t ≡ u ∷ A / defn-wk ξ⊇ [A]
      defn-wkEqTerm ξ⊇ (Levelᵣ _) t≡u =
        defn-wk-⊩≡∷L ξ⊇ t≡u
      defn-wkEqTerm
        ∇′⊇∇ (Uᵣ′ _ ⊩l′ l′<ℓ _)
        (Uₜ₌ _ _ d d′ A-type B-type A≅B ⊩t ⊩u t≡u) =
        let l′<ℓ′ =
              PE.subst (flip _<ᵘ_ _) (↑ᵘ-defn-wk-⊩∷L ∇′⊇∇) l′<ℓ
        in
        Uₜ₌ _ _ (defn-wkRed*Term ∇′⊇∇ d) (defn-wkRed*Term ∇′⊇∇ d′)
          (defn-wkType ∇′⊇∇ A-type) (defn-wkType ∇′⊇∇ B-type)
          (≅ₜ-defn-wk ∇′⊇∇ A≅B)
          (⊩<⇔⊩ l′<ℓ′ .proj₂ $
           PE.subst (flip (_⊩⟨_⟩_ _) _) (↑ᵘ-defn-wk-⊩∷L ∇′⊇∇) $
           Rec.defn-wk l′<ℓ ∇′⊇∇ (⊩<⇔⊩ l′<ℓ .proj₁ ⊩t))
          (⊩<⇔⊩ l′<ℓ′ .proj₂ $
           PE.subst (flip (_⊩⟨_⟩_ _) _) (↑ᵘ-defn-wk-⊩∷L ∇′⊇∇) $
           Rec.defn-wk l′<ℓ ∇′⊇∇ (⊩<⇔⊩ l′<ℓ .proj₁ ⊩u))
          (⊩<≡⇔⊩≡ l′<ℓ′ .proj₂ $
           irrelevanceEq _ _ $ cast-⊩↑ᵘ≡/ ⊩l′ ∇′⊇∇ _ $
           Rec.defn-wkEq l′<ℓ ∇′⊇∇ _ (⊩<≡⇔⊩≡ l′<ℓ .proj₁ t≡u))
      defn-wkEqTerm ξ⊇ (Liftᵣ′ _ _ ⊩A) (_ , _ , t↘t′ , u↘u′ , t′≡u′) =
        _ , _ , defn-wkRed↘Term ξ⊇ t↘t′ , defn-wkRed↘Term ξ⊇ u↘u′ ,
        defn-wkEqTerm ξ⊇ ⊩A t′≡u′
      defn-wkEqTerm ξ⊇ (ℕᵣ D) A≡B = defn-wkEqTermℕ ξ⊇ A≡B
      defn-wkEqTerm ξ⊇ (Emptyᵣ D) (Emptyₜ₌ k k′ d d′ k≡k′ (ne nf)) =
        Emptyₜ₌ k k′ (defn-wkRed*Term ξ⊇ d)
                     (defn-wkRed*Term ξ⊇ d′)
                     (≅ₜ-defn-wk ξ⊇ k≡k′)
                     (ne (defn-wkEqTermNe ξ⊇ nf))
      defn-wkEqTerm ξ⊇ (Unitᵣ′ _ _) t≡u = defn-wkEqTermUnit ξ⊇ t≡u
      defn-wkEqTerm ξ⊇ (ne′ K* D neK K≡K) (neₜ₌ k m d d′ nf) =
        neₜ₌ k m (defn-wkRed*Term ξ⊇ d)
                 (defn-wkRed*Term ξ⊇ d′)
                 (defn-wkEqTermNe ξ⊇ nf)
      defn-wkEqTerm ξ⊇ [A]@(Πᵣ′ F G D A≡A [F] [G] G-ext ok)
                    (Πₜ₌ f g d d′ funcF funcG f≡g [f≡g]) =
        Πₜ₌ f g (defn-wkRed*Term ξ⊇ d)
                (defn-wkRed*Term ξ⊇ d′)
                (defn-wkFunctionᵃ ξ⊇ funcF)
                (defn-wkFunctionᵃ ξ⊇ funcG)
                (≅ₜ-defn-wk ξ⊇ f≡g)
                (ξ⊇ •ᵈ→ [f≡g])
      defn-wkEqTerm ξ⊇ [A]@(Bᵣ′ BΣˢ F G D A≡A [F] [G] G-ext ok)
                    (Σₜ₌ p r d d′ pProd rProd p≅r
                         ([fstp] , [fstr] , [fst≡] , [snd≡])) =
        let id-Γ = id (wfEq (≅-eq A≡A))
            id-Γ′ = id (wfEq (≅-eq (≅-defn-wk ξ⊇ A≡A)))
            [Fid] = [F] id⊇ id-Γ
            [Fid]′ = [F] ξ⊇ id-Γ′
            [fstp]′ = irrelevanceTerm (defn-wk ξ⊇ [Fid]) [Fid]′
                                      (defn-wkTerm ξ⊇ [Fid] [fstp])
            [fstr]′ = irrelevanceTerm (defn-wk ξ⊇ [Fid]) [Fid]′
                                      (defn-wkTerm ξ⊇ [Fid] [fstr])
            [fst≡]′ = irrelevanceEqTerm (defn-wk ξ⊇ [Fid]) [Fid]′
                                        (defn-wkEqTerm ξ⊇ [Fid] [fst≡])
            [Gid] = [G] id⊇ id-Γ [fstp]
            [snd≡]′ = irrelevanceEqTerm (defn-wk ξ⊇ [Gid])
                        ([G] ξ⊇ id-Γ′ [fstp]′)
                        (defn-wkEqTerm ξ⊇ [Gid] [snd≡])
        in  Σₜ₌ p r (defn-wkRed*Term ξ⊇ d)
                    (defn-wkRed*Term ξ⊇ d′)
                    (defn-wkProductᵃ ξ⊇ pProd)
                    (defn-wkProductᵃ ξ⊇ rProd)
                    (≅ₜ-defn-wk ξ⊇ p≅r)
                    ([fstp]′ , [fstr]′ , [fst≡]′ , [snd≡]′)
      defn-wkEqTerm ξ⊇ [A]@(Bᵣ′ BΣʷ F G D A≡A [F] [G] G-ext ok)
        (Σₜ₌ p r d d′ prodₙ prodₙ p≅r
           (eq , eq′ , eq″ , eq‴ , [p₁] , [r₁] , [fst≡] , [snd≡])) =
        let id-Γ = id (wfEq (≅-eq A≡A))
            id-Γ′ = id (wfEq (≅-eq (≅-defn-wk ξ⊇ A≡A)))
            [Fid] = [F] id⊇ id-Γ
            [Fid]′ = [F] ξ⊇ id-Γ′
            [p₁]′ = irrelevanceTerm (defn-wk ξ⊇ [Fid]) [Fid]′
                                    (defn-wkTerm ξ⊇ [Fid] [p₁])
            [r₁]′ = irrelevanceTerm (defn-wk ξ⊇ [Fid]) [Fid]′
                                    (defn-wkTerm ξ⊇ [Fid] [r₁])
            [fst≡]′ = irrelevanceEqTerm (defn-wk ξ⊇ [Fid]) [Fid]′
                                        (defn-wkEqTerm ξ⊇ [Fid] [fst≡])
            [Gidp] = [G] id⊇ id-Γ [p₁]
            [Gidp]′ = [G] ξ⊇ id-Γ′ [p₁]′
            [Gidr] = [G] id⊇ id-Γ [r₁]
            [snd≡]′ = irrelevanceEqTerm (defn-wk ξ⊇ [Gidp]) [Gidp]′
                                        (defn-wkEqTerm ξ⊇ [Gidp] [snd≡])
        in  Σₜ₌ p r (defn-wkRed*Term ξ⊇ d)
                    (defn-wkRed*Term ξ⊇ d′)
                    prodₙ prodₙ
                    (≅ₜ-defn-wk ξ⊇ p≅r)
                    (eq , eq′ , eq″ , eq‴ , [p₁]′ , [r₁]′ ,
                     [fst≡]′ , [snd≡]′)
      defn-wkEqTerm ξ⊇ [A]@(Bᵣ′ BΣʷ F G D A≡A [F] [G] G-ext ok)
                    (Σₜ₌ p r d d′ (ne b) (ne b′) p≅r p~r) =
        Σₜ₌ p r (defn-wkRed*Term ξ⊇ d)
                (defn-wkRed*Term ξ⊇ d′)
                (ne (defn-wkNeutralᵃ ξ⊇ b))
                (ne (defn-wkNeutralᵃ ξ⊇ b′))
                (≅ₜ-defn-wk ξ⊇ p≅r)
                (~-defn-wk ξ⊇ p~r)
      defn-wkEqTerm _ (Bᵣ BΣʷ record{}) (Σₜ₌ _ _ _ _ prodₙ  (ne _) _ ())
      defn-wkEqTerm _ (Bᵣ BΣʷ record{}) (Σₜ₌ _ _ _ _ (ne _) prodₙ  _ ())
      defn-wkEqTerm ξ⊇ (Idᵣ ⊩A) (t′ , u′ , d , d′ , prop) =
        let prop′ = case prop of λ where
                      (rflₙ , rflₙ , lhs≡rhs) →
                        rflₙ , rflₙ , defn-wkEqTerm ξ⊇ ⊩Ty lhs≡rhs
                      (ne b , ne b′ , t′~u′) →
                        ne (defn-wkNeutralᵃ ξ⊇ b) ,
                        ne (defn-wkNeutralᵃ ξ⊇ b′) ,
                        ~-defn-wk ξ⊇ t′~u′
                      (rflₙ , ne b , ())
                      (ne b , rflₙ , ())
        in
        (t′ , u′ , defn-wkRed*Term ξ⊇ d , defn-wkRed*Term ξ⊇ d′ , prop′)
        where
        open _⊩ₗId_ ⊩A

  opaque

    defn-wk-inhabited : Defn-wk ℓ
    defn-wk-inhabited =
      <ᵘ-rec _ (λ _ rec → record { Defn-wk-inhabited rec }) _

opaque

  -- Weakening for _⊩⟨_⟩_.

  defn-wk : » ∇′ ⊇ ∇ → ∇ » Γ ⊩⟨ ℓ ⟩ A → ∇′ » Γ ⊩⟨ ℓ ⟩ A
  defn-wk = Defn-wk-inhabited.defn-wk (λ _ → defn-wk-inhabited)

opaque
  unfolding defn-wk

  -- Weakening for _⊩⟨_⟩_≡_/_.

  defn-wkEq :
    (∇′⊇∇ : » ∇′ ⊇ ∇) (⊩A : ∇ » Γ ⊩⟨ ℓ ⟩ A) →
    ∇ » Γ ⊩⟨ ℓ ⟩ A ≡ B / ⊩A → ∇′ » Γ ⊩⟨ ℓ ⟩ A ≡ B / defn-wk ∇′⊇∇ ⊩A
  defn-wkEq = Defn-wk-inhabited.defn-wkEq (λ _ → defn-wk-inhabited)

opaque
  unfolding defn-wk

  -- Weakening for _⊩⟨_⟩_≡_∷_/_.

  defn-wkEqTerm :
    (∇′⊇∇ : » ∇′ ⊇ ∇) (⊩A : ∇ » Γ ⊩⟨ ℓ ⟩ A) →
    ∇ » Γ ⊩⟨ ℓ ⟩ t ≡ u ∷ A / ⊩A →
    ∇′ » Γ ⊩⟨ ℓ ⟩ t ≡ u ∷ A / defn-wk ∇′⊇∇ ⊩A
  defn-wkEqTerm =
    Defn-wk-inhabited.defn-wkEqTerm (λ _ → defn-wk-inhabited)

opaque

  -- Weakening for _⊩⟨_⟩_∷_/_.

  defn-wkTerm :
    (∇′⊇∇ : » ∇′ ⊇ ∇) (⊩A : ∇ » Γ ⊩⟨ ℓ ⟩ A) →
    ∇ » Γ ⊩⟨ ℓ ⟩ t ∷ A / ⊩A →
    ∇′ » Γ ⊩⟨ ℓ ⟩ t ∷ A / defn-wk ∇′⊇∇ ⊩A
  defn-wkTerm = defn-wkEqTerm
