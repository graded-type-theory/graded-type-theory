------------------------------------------------------------------------
-- The logical relation is closed under weakening
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Weakening
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M as U hiding (wk; K)
open import Definition.Untyped.Allowed-literal R
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Untyped.Inversion M
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R hiding (wk)
open import Definition.Typed.Weakening.Combined R as C using (_⊢ʷᵏ_∷_)
open import Definition.Typed.Well-formed R
open import Definition.LogicalRelation R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Irrelevance R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Weakening.Restricted R ⦃ eqrel ⦄

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private
  variable
    m n κ : Nat
    ρ : Wk m n
    ∇ : DCon (Term 0) κ
    Γ Δ : Con Term m
    Γ₁ Γ₂ : Cons _ _
    A B k k′ t t′ u u′ : Term m
    l l′ l₁ l₂ : Lvl _
    ℓ : Universe-level
    s : Strength
    ok₁ ok₂ : Level-allowed

-- Weakening of neutral terms in WHNF

wkEqTermNe :
  Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
  Γ₁ ⊩neNf k ≡ k′ ∷ A → Γ₂ ⊩neNf U.wk ρ k ≡ U.wk ρ k′ ∷ U.wk ρ A
wkEqTermNe [ρ] (neNfₜ₌ neK neM k≡m) =
  neNfₜ₌ (C.wk-Neutralᵃ [ρ] neK) (C.wk-Neutralᵃ [ρ] neM) (~-wk [ρ] k≡m)

-- Weakening of reducible levels

mutual
  wkTermLevel : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁
              → Γ₁ ⊩Level l ∷Level
              → Γ₂ ⊩Level U.wk ρ l ∷Level
  wkTermLevel [ρ] (term d prop) =
    term (C.wk-⇒*∷ [ρ] d) (wkLevel-prop [ρ] prop)
  wkTermLevel [ρ] (literal ok _) =
    literal (Allowed-literal-wk-⇔ .proj₂ ok) (C.wf-⊢ʷᵏ [ρ])

  wkLevel-prop : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁
               → Level-prop Γ₁ t
               → Level-prop Γ₂ (U.wk ρ t)
  wkLevel-prop [ρ] (zeroᵘᵣ ok)   = zeroᵘᵣ ok
  wkLevel-prop [ρ] (sucᵘᵣ ok ⊩t) = sucᵘᵣ ok (wkTermLevel [ρ] ⊩t)
  wkLevel-prop [ρ] (neLvl ⊩t)    = neLvl (wkneLevel-prop [ρ] ⊩t)

  wkneLevel-prop : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁
                 → neLevel-prop Γ₁ t
                 → neLevel-prop Γ₂ (U.wk ρ t)
  wkneLevel-prop [ρ] (supᵘˡᵣ x y) = supᵘˡᵣ (wkneLevel-prop [ρ] x) (wkTermLevel [ρ] y)
  wkneLevel-prop [ρ] (supᵘʳᵣ x y) = supᵘʳᵣ (wkTermLevel [ρ] x) (wkneLevel-prop [ρ] y)
  wkneLevel-prop [ρ] (ne x) = ne (wkEqTermNe [ρ] x)

mutual
  wkEqTermLevel : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁
                → Γ₁ ⊩Level l₁ ≡ l₂ ∷Level
                → Γ₂ ⊩Level U.wk ρ l₁ ≡ U.wk ρ l₂ ∷Level
  wkEqTermLevel [ρ] (term d d′ prop) =
    term (C.wk-⇒*∷ [ρ] d) (C.wk-⇒*∷ [ρ] d′)
      (wk[Level]-prop [ρ] prop)
  wkEqTermLevel [ρ] (literal! ok _) =
    literal! (Allowed-literal-wk-⇔ .proj₂ ok) (C.wf-⊢ʷᵏ [ρ])

  wk[Level]-prop : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁
                 → [Level]-prop Γ₁ t u
                 → [Level]-prop Γ₂ (U.wk ρ t) (U.wk ρ u)
  wk[Level]-prop ρ (sucᵘᵣ ok [t≡u]) = sucᵘᵣ ok (wkEqTermLevel ρ [t≡u])
  wk[Level]-prop ρ (zeroᵘᵣ ok) = zeroᵘᵣ ok
  wk[Level]-prop ρ (neLvl x) = neLvl (wk[neLevel]-prop ρ x)
  wk[Level]-prop ρ (supᵘ-subᵣ x y) = supᵘ-subᵣ (wkneLevel-prop ρ x) (wkEqTermLevel ρ y)
  wk[Level]-prop [ρ] (sym u≡t) = sym (wk[Level]-prop [ρ] u≡t)
  wk[Level]-prop [ρ] (trans t≡u u≡v) = trans (wk[Level]-prop [ρ] t≡u) (wk[Level]-prop [ρ] u≡v)

  wk[neLevel]-prop : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁
                   → [neLevel]-prop Γ₁ t u
                   → [neLevel]-prop Γ₂ (U.wk ρ t) (U.wk ρ u)
  wk[neLevel]-prop [ρ] (supᵘˡᵣ t≡u x) = supᵘˡᵣ (wk[neLevel]-prop [ρ] t≡u) (wkEqTermLevel [ρ] x)
  wk[neLevel]-prop [ρ] (supᵘʳᵣ x t≡u) = supᵘʳᵣ (wkEqTermLevel [ρ] x) (wk[neLevel]-prop [ρ] t≡u)
  wk[neLevel]-prop [ρ] (supᵘ-zeroʳᵣ [u]) = supᵘ-zeroʳᵣ (wkneLevel-prop [ρ] [u])
  wk[neLevel]-prop [ρ] (supᵘ-assoc¹ᵣ x y z) = supᵘ-assoc¹ᵣ (wkneLevel-prop [ρ] x) (wkTermLevel [ρ] y) (wkTermLevel [ρ] z)
  wk[neLevel]-prop [ρ] (supᵘ-assoc²ᵣ x y z) = supᵘ-assoc²ᵣ (wkTermLevel [ρ] x) (wkneLevel-prop [ρ] y) (wkTermLevel [ρ] z)
  wk[neLevel]-prop [ρ] (supᵘ-assoc³ᵣ x y z) = supᵘ-assoc³ᵣ (wkTermLevel [ρ] x) (wkTermLevel [ρ] y) (wkneLevel-prop [ρ] z)
  wk[neLevel]-prop [ρ] (supᵘ-comm¹ᵣ x x₁ x₂ x₃) = supᵘ-comm¹ᵣ (wkneLevel-prop [ρ] x) (wkEqTermLevel [ρ] x₁) (wkneLevel-prop [ρ] x₂) (wkEqTermLevel [ρ] x₃)
  wk[neLevel]-prop [ρ] (supᵘ-comm²ᵣ x x₁ x₂) = supᵘ-comm²ᵣ (wkTermLevel [ρ] x) (wkEqTermLevel [ρ] x₁) (wkneLevel-prop [ρ] x₂)
  wk[neLevel]-prop [ρ] (supᵘ-idemᵣ x y) = supᵘ-idemᵣ (wkneLevel-prop [ρ] x) (wkEqTermLevel [ρ] y)
  wk[neLevel]-prop [ρ] (ne x) = ne (wkEqTermNe [ρ] x)

opaque
  unfolding ↑ⁿ

  -- Weakening preserves level realisation.

  mutual
    wk-↑ⁿ
      : ([ρ] : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁)
      → (t≡u : Γ₁ ⊩Level level t ∷Level)
      → (wk-t≡u′ : Γ₂ ⊩Level level t′ ∷Level)
      → t′ PE.≡ U.wk ρ t
      → ↑ⁿ ok₁ wk-t≡u′ PE.≡ ↑ⁿ ok₂ t≡u
    wk-↑ⁿ {ρ} [ρ] (term d prop) (term d′ prop′) PE.refl =
      case whrDet*Term (d′ , Level-prop→Whnf prop′)
             (C.wk-↘∷ [ρ] (d , Level-prop→Whnf prop)) of λ {
        PE.refl →
      wk-↑ⁿ-prop [ρ] prop prop′ PE.refl }
    wk-↑ⁿ {ok₁} _ (literal ok _) _ _ =
      Level-allowed→Allowed-literal→ ok₁ ok
    wk-↑ⁿ {ok₁} _ _ (literal ok _) _ =
      Level-allowed→Allowed-literal→ ok₁ ok

    wk-↑ⁿ-prop
      : ([ρ] : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁)
      → (t≡u : Level-prop Γ₁ t)
      → (wk-t≡u : Level-prop Γ₂ t′)
      → t′ PE.≡ U.wk ρ t
      → ↑ⁿ-prop ok₁ wk-t≡u PE.≡ ↑ⁿ-prop ok₂ t≡u
    wk-↑ⁿ-prop [ρ] (zeroᵘᵣ _) ⊩t′ PE.refl = ↑ⁿ-prop-zeroᵘ ⊩t′
    wk-↑ⁿ-prop [ρ] (sucᵘᵣ _ ⊩t) ⊩t′ PE.refl =
      let ⊩wk-t , ↑t′≡ = ↑ⁿ-prop-sucᵘ ⊩t′
      in PE.trans ↑t′≡ (PE.cong 1+ (wk-↑ⁿ [ρ] ⊩t ⊩wk-t PE.refl))
    wk-↑ⁿ-prop [ρ] (neLvl ⊩t) (zeroᵘᵣ _) p =
      case wk-zeroᵘ (PE.sym p) of λ {
        PE.refl →
      case nelevel ⊩t of λ
        () }
    wk-↑ⁿ-prop [ρ] (neLvl ⊩t) (sucᵘᵣ _ _) p =
      case wk-sucᵘ (PE.sym p) of λ {
        (_ , PE.refl , PE.refl) →
      case nelevel ⊩t of λ
        () }
    wk-↑ⁿ-prop [ρ] (neLvl x) (neLvl y) PE.refl = wk-↑ⁿ-neprop [ρ] x y PE.refl

    wk-↑ⁿ-neprop
      : ([ρ] : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁)
      → (t≡u : neLevel-prop Γ₁ t)
      → (wk-t≡u : neLevel-prop Γ₂ t′)
      → t′ PE.≡ U.wk ρ t
      → ↑ⁿ-neprop ok₁ wk-t≡u PE.≡ ↑ⁿ-neprop ok₂ t≡u
    wk-↑ⁿ-neprop [ρ] (supᵘˡᵣ t≡u x) (supᵘˡᵣ wk-t≡u x₁) PE.refl =
      PE.cong₂ _⊔_ (wk-↑ⁿ-neprop [ρ] t≡u wk-t≡u PE.refl) (wk-↑ⁿ [ρ] x x₁ PE.refl)
    wk-↑ⁿ-neprop [ρ] (supᵘʳᵣ x t≡u) (supᵘʳᵣ x₁ wk-t≡u) PE.refl =
      PE.cong₂ _⊔_ (PE.cong 1+ (wk-↑ⁿ [ρ] x x₁ PE.refl)) (wk-↑ⁿ-neprop [ρ] t≡u wk-t≡u PE.refl)
    wk-↑ⁿ-neprop [ρ] (ne _) (ne _) PE.refl = PE.refl
    wk-↑ⁿ-neprop [ρ] (supᵘˡᵣ t≡u x) (supᵘʳᵣ x₁ wk-t≡u) p =
      case supᵘ-PE-injectivity p of λ { (q , PE.refl) →
      case wk-sucᵘ (PE.sym q) of λ { (_ , PE.refl , PE.refl) →
      case nelevel t≡u of λ () }}
    wk-↑ⁿ-neprop _ (supᵘˡᵣ _ _) (ne (neNfₜ₌ n _ _)) PE.refl =
      Neutralᵃ-supᵘ→ n
    wk-↑ⁿ-neprop [ρ] (supᵘʳᵣ x t≡u) (supᵘˡᵣ wk-t≡u x₁) PE.refl =
      case nelevel wk-t≡u of λ ()
    wk-↑ⁿ-neprop _ (supᵘʳᵣ _ _) (ne (neNfₜ₌ n _ _)) PE.refl =
      Neutralᵃ-supᵘ→ n
    wk-↑ⁿ-neprop [ρ] (ne (neNfₜ₌ neK _ _)) (supᵘˡᵣ wk-t≡u x₁) p =
      case wk-supᵘ (PE.sym p) of λ { (_ , _ , PE.refl , _ , _) →
      Neutralᵃ-supᵘ→ neK }
    wk-↑ⁿ-neprop [ρ] (ne (neNfₜ₌ neK _ _)) (supᵘʳᵣ x₁ wk-t≡u) p =
      case wk-supᵘ (PE.sym p) of λ { (_ , _ , PE.refl , _ , _) →
      Neutralᵃ-supᵘ→ neK }

opaque
  unfolding ↑ᵘ

  wk-↑ᵘ
    : ([ρ] : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁)
    → {⊩l : Γ₁ ⊩Level l ∷Level}
    → {⊩l′ : Γ₂ ⊩Level l′ ∷Level}
    → l′ PE.≡ U.wk ρ l
    → ↑ᵘ ⊩l′ PE.≡ ↑ᵘ ⊩l
  wk-↑ᵘ [ρ] {⊩l = term _ _} {⊩l′ = term _ _} eq =
    PE.cong 0ᵘ+ (wk-↑ⁿ [ρ] _ _ (level-PE-injectivity eq))
  wk-↑ᵘ _ {⊩l = term ⇒∷L _} {⊩l′ = literal ok _} eq
    using okᴸ ← inversion-Level-⊢ (wf-⊢ (subset*Term ⇒∷L) .proj₁)
    with Allowed-literal→Infinite okᴸ ok
  … | ωᵘ+ = case eq of λ ()
  wk-↑ᵘ _ {⊩l = literal ok _} {⊩l′ = term ⇒∷L _} eq
    using okᴸ ← inversion-Level-⊢ (wf-⊢ (subset*Term ⇒∷L) .proj₁)
    with Allowed-literal→Infinite okᴸ ok
  … | ωᵘ+ = case eq of λ ()
  wk-↑ᵘ _ {⊩l = literal ok₁ _} {⊩l′ = literal ok₂ _} PE.refl =
    Allowed-literal→Universe-level ok₂                                ≡⟨ Allowed-literal→Universe-level-irrelevance ⟩
    Allowed-literal→Universe-level (Allowed-literal-wk-⇔ .proj₂ ok₁)  ≡⟨ Allowed-literal→Universe-level-Allowed-literal-wk-⇔ ⟩
    Allowed-literal→Universe-level ok₁                                ∎

-- Weakening of reducible natural numbers

mutual
  wkEqTermℕ : ∀ {t u} → Γ₂ ⊢ʷᵏ ρ ∷ Γ₁
            → Γ₁ ⊩ℕ t ≡ u ∷ℕ
            → Γ₂ ⊩ℕ U.wk ρ t ≡ U.wk ρ u ∷ℕ
  wkEqTermℕ {ρ = ρ} [ρ] (ℕₜ₌ k k′ d d′ t≡u prop) =
    ℕₜ₌ (U.wk ρ k) (U.wk ρ k′) (C.wk-⇒*∷ [ρ] d)
        (C.wk-⇒*∷ [ρ] d′) (≅ₜ-wk [ρ] t≡u)
        (wk[Natural]-prop [ρ] prop)

  wk[Natural]-prop : ∀ {n n′} → Γ₂ ⊢ʷᵏ ρ ∷ Γ₁
                   → [Natural]-prop Γ₁ n n′
                   → [Natural]-prop Γ₂ (U.wk ρ n) (U.wk ρ n′)
  wk[Natural]-prop ρ (sucᵣ [n≡n′]) = sucᵣ (wkEqTermℕ ρ [n≡n′])
  wk[Natural]-prop ρ zeroᵣ = zeroᵣ
  wk[Natural]-prop ρ (ne nf) = ne (wkEqTermNe ρ nf)

-- Empty

wk[Empty]-prop : ∀ {n n′} → Γ₂ ⊢ʷᵏ ρ ∷ Γ₁
  → [Empty]-prop Γ₁ n n′
  → [Empty]-prop Γ₂ (U.wk ρ n) (U.wk ρ n′)
wk[Empty]-prop ρ (ne nf) = ne (wkEqTermNe ρ nf)

wkEqTermEmpty : ∀ {t u} → Γ₂ ⊢ʷᵏ ρ ∷ Γ₁
  → Γ₁ ⊩Empty t ≡ u ∷Empty
  → Γ₂ ⊩Empty U.wk ρ t ≡ U.wk ρ u ∷Empty
wkEqTermEmpty {ρ} [ρ] (Emptyₜ₌ k k′ d d′ t≡u prop) =
  Emptyₜ₌ (U.wk ρ k) (U.wk ρ k′) (C.wk-⇒*∷ [ρ] d)
      (C.wk-⇒*∷ [ρ] d′) (≅ₜ-wk [ρ] t≡u) (wk[Empty]-prop [ρ] prop)

-- Unit
wkUnit : ∀ {s} ([ρ] : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁)
       → Γ₁ ⊩Unit⟨ s ⟩ A
       → Γ₂ ⊩Unit⟨ s ⟩ U.wk ρ A
wkUnit {ρ} [ρ] (Unitᵣ D ok) = Unitᵣ (C.wk-⇒* [ρ] D) ok

wkEqUnit : ∀ {s} ([ρ] : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁)
         → Γ₁ ⊩Unit⟨ s ⟩ A ≡ B
         → Γ₂ ⊩Unit⟨ s ⟩ U.wk ρ A ≡ U.wk ρ B
wkEqUnit [ρ] (Unit₌ D) = Unit₌ (C.wk-⇒* [ρ] D)

wk[Unit]-prop′ : ∀ {t u} ([ρ] : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁)
               → [Unit]-prop′ Γ₁ 𝕨 t u
               → [Unit]-prop′ Γ₂ 𝕨 (U.wk ρ t) (U.wk ρ u)
wk[Unit]-prop′ [ρ] starᵣ = starᵣ
wk[Unit]-prop′ [ρ] (ne x) = ne (wkEqTermNe [ρ] x)

-- Weakening for [Unit]-prop.
wk[Unit]-prop :
  Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
  [Unit]-prop Γ₁ s t u →
  [Unit]-prop Γ₂ s (U.wk ρ t) (U.wk ρ u)
wk[Unit]-prop ρ (Unitₜ₌ʷ prop no-η) =
  Unitₜ₌ʷ (wk[Unit]-prop′ ρ prop) no-η
wk[Unit]-prop ρ (Unitₜ₌ˢ η) =
  Unitₜ₌ˢ η

wkEqTermUnit : ∀ {t u s} ([ρ] : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁)
             → Γ₁ ⊩Unit⟨ s ⟩ t ≡ u ∷Unit
             → Γ₂ ⊩Unit⟨ s ⟩ U.wk ρ t ≡ U.wk ρ u ∷Unit
wkEqTermUnit {ρ} [ρ] (Unitₜ₌ u₁ u₂ ↘u₁ ↘u₂ prop) =
  Unitₜ₌ (U.wk ρ u₁) (U.wk ρ u₂) (C.wk-↘∷ [ρ] ↘u₁) (C.wk-↘∷ [ρ] ↘u₂)
    (wk[Unit]-prop [ρ] prop)

-- U
wkU : ∀ ([ρ] : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁)
    → Γ₁ ⊩′⟨ ℓ ⟩U A
    → Γ₂ ⊩′⟨ ℓ ⟩U U.wk ρ A
wkU {ρ} {ℓ} [ρ] (Uᵣ l′ [l′] l′< D) = Uᵣ (U.wk ρ l′)
  (wkTermLevel [ρ] [l′])
  (PE.subst (_<ᵘ ℓ) (PE.sym (wk-↑ᵘ [ρ] PE.refl)) l′<)
  (C.wk-⇒* [ρ] D)

-- Weakening of the logical relation

record WkKit (ℓ : Universe-level) : Set a where
  field
    wk :
      {ρ : Wk m n} →
      Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁ → Γ₁ ⊩⟨ ℓ ⟩ A → Γ₂ ⊩⟨ ℓ ⟩ U.wk ρ A

    wkEq :
      (⊢ρ : Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁) (⊩A : Γ₁ ⊩⟨ ℓ ⟩ A) →
      Γ₁ ⊩⟨ ℓ ⟩ A ≡ B / ⊩A →
      Γ₂ ⊩⟨ ℓ ⟩ U.wk ρ A ≡ U.wk ρ B / wk ⊢ρ ⊩A

    wkEqTerm :
      (⊢ρ : Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁) (⊩A : Γ₁ ⊩⟨ ℓ ⟩ A) →
      Γ₁ ⊩⟨ ℓ ⟩ t ≡ u ∷ A / ⊩A →
      Γ₂ ⊩⟨ ℓ ⟩ U.wk ρ t ≡ U.wk ρ u ∷ U.wk ρ A / wk ⊢ρ ⊩A

  wkTerm :
    (⊢ρ : Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁) (⊩A : Γ₁ ⊩⟨ ℓ ⟩ A) →
    Γ₁ ⊩⟨ ℓ ⟩ t ∷ A / ⊩A →
    Γ₂ ⊩⟨ ℓ ⟩ U.wk ρ t ∷ U.wk ρ A / wk ⊢ρ ⊩A
  wkTerm ⊩A ⊩t = wkEqTerm ⊩A ⊩t

private module Weakening (ℓ : Universe-level) (rec : ∀ {ℓ′} → ℓ′ <ᵘ ℓ → WkKit ℓ′) where

  module Rec {ℓ′} (ℓ′< : ℓ′ <ᵘ ℓ) = WkKit (rec ℓ′<)

  wk :
    {ρ : Wk m n} →
    Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁ → Γ₁ ⊩⟨ ℓ ⟩ A → Γ₂ ⊩⟨ ℓ ⟩ U.wk ρ A

  wkEq :
    (⊢ρ : Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁) (⊩A : Γ₁ ⊩⟨ ℓ ⟩ A) →
    Γ₁ ⊩⟨ ℓ ⟩ A ≡ B / ⊩A →
    Γ₂ ⊩⟨ ℓ ⟩ U.wk ρ A ≡ U.wk ρ B / wk ⊢ρ ⊩A

  wkEqTerm :
    (⊢ρ : Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁) (⊩A : Γ₁ ⊩⟨ ℓ ⟩ A) →
    Γ₁ ⊩⟨ ℓ ⟩ t ≡ u ∷ A / ⊩A →
    Γ₂ ⊩⟨ ℓ ⟩ U.wk ρ t ≡ U.wk ρ u ∷ U.wk ρ A / wk ⊢ρ ⊩A

  wkTerm :
    (⊢ρ : Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁) (⊩A : Γ₁ ⊩⟨ ℓ ⟩ A) →
    Γ₁ ⊩⟨ ℓ ⟩ t ∷ A / ⊩A →
    Γ₂ ⊩⟨ ℓ ⟩ U.wk ρ t ∷ U.wk ρ A / wk ⊢ρ ⊩A
  wkTerm ⊩A ⊩t = wkEqTerm ⊩A ⊩t

  wk ρ (Levelᵣ D) = Levelᵣ (wk-⇒* ρ D)
  wk ρ (Liftᵣ′ D [k] [F]) =
    Liftᵣ′ (wk-⇒* ρ D) (wkTermLevel (⊢ʷᵏʳ→⊢ʷᵏ ρ) [k]) (wk ρ [F])
  wk ρ (Uᵣ [A]) = Uᵣ (wkU (⊢ʷᵏʳ→⊢ʷᵏ ρ) [A])
  wk ρ (ℕᵣ D) = ℕᵣ (wk-⇒* ρ D)
  wk ρ (Emptyᵣ D) = Emptyᵣ (wk-⇒* ρ D)
  wk ρ (Unitᵣ [A]) = Unitᵣ (wkUnit (⊢ʷᵏʳ→⊢ʷᵏ ρ) [A])
  wk {ρ} [ρ] (ne′ _ D neK K≡K) =
    ne′ (U.wk ρ _) (wk-⇒* [ρ] D) (wk-Neutral [ρ] neK)
      (≅-wk (⊢ʷᵏʳ→⊢ʷᵏ [ρ]) K≡K)
  wk {Γ₁} {ρ} [ρ] (Bᵣ′ (BM _ _ _) F G D A≡A [F] [G] G-ext ok) =
    let [F]′ : ∀ {m₁ m₂ n₁ n₂} {Δ : Cons m₁ n₁} {ρ ρ′} {Ε : Cons m₂ n₂}
               ([ρ] : Ε ⊢ʷᵏʳ ρ ∷ Δ) ([ρ′] : Δ ⊢ʷᵏʳ ρ′ ∷ Γ₁)
             → Ε ⊩⟨ ℓ ⟩ U.wk ρ (U.wk ρ′ F)
        [F]′ [ρ] [ρ′] =
          irrelevance′ (PE.sym (wk-comp _ _ F))
            ([F] (⊢ʷᵏʳ• [ρ] [ρ′]))
        [a]′ : ∀ {m₁ m₂ n₁ n₂} {Δ : Cons m₁ n₁} {ρ ρ′} {Ε : Cons m₂ n₂}
                 {a}
               ([ρ] : Ε ⊢ʷᵏʳ ρ ∷ Δ) ([ρ′] : Δ ⊢ʷᵏʳ ρ′ ∷ Γ₁)
               ([a] : Ε ⊩⟨ ℓ ⟩ a ∷ U.wk ρ (U.wk ρ′ F) / [F]′ [ρ] [ρ′])
             → Ε ⊩⟨ ℓ ⟩ a ∷ U.wk (ρ • ρ′) F / [F] (⊢ʷᵏʳ• [ρ] [ρ′])
        [a]′ [ρ] [ρ′] [a] =
          irrelevanceTerm′ (wk-comp _ _ F) ([F]′ [ρ] [ρ′]) ([F] _) [a]
        [G]′ : ∀ {m₁ m₂ n₁ n₂} {Δ : Cons m₁ n₁} {ρ ρ′} {Ε : Cons m₂ n₂}
                 {a}
               ([ρ] : Ε ⊢ʷᵏʳ ρ ∷ Δ) ([ρ′] : Δ ⊢ʷᵏʳ ρ′ ∷ Γ₁)
               ([a] : Ε ⊩⟨ ℓ ⟩ a ∷ U.wk ρ (U.wk ρ′ F) / [F]′ [ρ] [ρ′])
             → Ε ⊩⟨ ℓ ⟩ U.wk (lift (ρ • ρ′)) G [ a ]₀
        [G]′ η η′ [a] = [G] _ ([a]′ η η′ [a])
    in
    Bᵣ′ _ (U.wk ρ F) (U.wk (lift ρ) G) (wk-⇒* [ρ] D)
      (≅-wk (⊢ʷᵏʳ→⊢ʷᵏ [ρ]) A≡A)
      (λ _ → irrelevance′ (PE.sym (wk-comp _ _ F)) ([F] _))
      (λ [ρ₁] [a] →
         irrelevance′ (wk-comp-subst _ _ G) ([G]′ [ρ₁] [ρ] [a]))
      (λ [ρ₁] [a] [b] [a≡b] →
         irrelevanceEq″ (wk-comp-subst _ _ G)
           (wk-comp-subst _ _ G) ([G]′ _ _ [a])
           (irrelevance′ (wk-comp-subst _ _ G) ([G]′ _ _ [a]))
           (G-ext _ ([a]′ _ _ [a]) ([a]′ _ _ [b]) $
            irrelevanceEqTerm′ (wk-comp _ _ F) ([F]′ _ [ρ])
              ([F] _) [a≡b]))
      ok
  wk ρ∷⊇ (Idᵣ ⊩A) = Idᵣ (record
    { ⇒*Id  = wk-⇒* ρ∷⊇ ⇒*Id
    ; ⊩Ty   = wk ρ∷⊇ ⊩Ty
    ; ⊩lhs  = wkTerm ρ∷⊇ ⊩Ty ⊩lhs
    ; ⊩rhs  = wkTerm ρ∷⊇ ⊩Ty ⊩rhs
    })
    where
    open _⊩ₗId_ ⊩A

  wkEq ρ (Levelᵣ D) A≡B = wk-⇒* ρ A≡B
  wkEq ρ (Liftᵣ′ D [k] [F]) (Lift₌ D′ k≡k′ F≡F′) =
    Lift₌ (wk-⇒* ρ D′) (wkEqTermLevel (⊢ʷᵏʳ→⊢ʷᵏ ρ) k≡k′)
      (wkEq ρ [F] F≡F′)
  wkEq ρ (Uᵣ′ l [l] l< D) (U₌ k D′ l≡k) =
    U₌ (U.wk _ k) (wk-⇒* ρ D′) (wkEqTermLevel (⊢ʷᵏʳ→⊢ʷᵏ ρ) l≡k)
  wkEq ρ (ℕᵣ D) A≡B = wk-⇒* ρ A≡B
  wkEq ρ (Emptyᵣ D) A≡B = wk-⇒* ρ A≡B
  wkEq ρ (Unitᵣ′ _ _) A≡B = wkEqUnit (⊢ʷᵏʳ→⊢ʷᵏ ρ) A≡B
  wkEq {ρ = ρ} [ρ] (ne′ _ _ _ _) (ne₌ M D′ neM K≡M) =
    ne₌ (U.wk ρ M) (wk-⇒* [ρ] D′) (wk-Neutral [ρ] neM)
      (≅-wk (⊢ʷᵏʳ→⊢ʷᵏ [ρ]) K≡M)
  wkEq
    {ρ} [ρ] (Bᵣ′ (BM _ _ _) F G D A≡A [F] [G] G-ext _)
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
    B₌ (U.wk ρ F′) (U.wk (lift ρ) G′) (wk-⇒* [ρ] D′)
      (≅-wk (⊢ʷᵏʳ→⊢ʷᵏ [ρ]) A≡B)
      (λ [ρ₁] →
         irrelevanceEq″ (PE.sym (wk-comp _ _ F))
           (PE.sym (wk-comp _ _ F′)) ([F] (⊢ʷᵏʳ• [ρ₁] [ρ]))
           (irrelevance′ (PE.sym (wk-comp _ _ F)) ([F] _)) ([F≡F′] _))
      (λ [ρ₁] [a] →
         let [a]′ =
               irrelevanceTerm′ (wk-comp _ _ F)
                 (irrelevance′ (PE.sym (wk-comp _ _ F)) ([F] _)) ([F] _)
                 [a]
         in
         irrelevanceEq″ (wk-comp-subst _ _ G) (wk-comp-subst _ _ G′)
           ([G] _ [a]′)
           (irrelevance′ (wk-comp-subst _ _ G) ([G] _ [a]′))
           ([G≡G′] _ [a]′))
  wkEq ρ∷⊇ (Idᵣ ⊩A) A≡B = Id₌′
    (wk-⇒* ρ∷⊇ ⇒*Id′)
    (wkEq ρ∷⊇ ⊩Ty Ty≡Ty′)
    (wkEqTerm ρ∷⊇ ⊩Ty lhs≡lhs′)
    (wkEqTerm ρ∷⊇ ⊩Ty rhs≡rhs′)
    where
    open _⊩ₗId_ ⊩A
    open _⊩ₗId_≡_/_ A≡B

  wkEqTerm ρ (Levelᵣ D) [t≡u] = wkEqTermLevel (⊢ʷᵏʳ→⊢ʷᵏ ρ) [t≡u]
  wkEqTerm
    {ρ} [ρ] (Uᵣ [U]@(Uᵣ k [k] k< D))
    (Uₜ₌ A B d d′ typeA typeB A≡B [t] [u] [t≡u]) =
    let [ρ]′ = ⊢ʷᵏʳ→⊢ʷᵏ [ρ]
        p = wkU [ρ]′ [U] ._⊩₁U_.k<
    in
    Uₜ₌ (U.wk ρ A) (U.wk ρ B) (wk-⇒*∷ [ρ] d) (wk-⇒*∷ [ρ] d′)
        (wk-Type [ρ] typeA) (wk-Type [ρ] typeB) (≅ₜ-wk [ρ]′ A≡B)
        (⊩<⇔⊩ p .proj₂ $ PE.subst (flip (_⊩⟨_⟩_ _) _) (PE.sym $ wk-↑ᵘ [ρ]′ PE.refl) $
          Rec.wk k< [ρ] (⊩<⇔⊩ k< .proj₁ [t]))
        (⊩<⇔⊩ p .proj₂ $ PE.subst (flip (_⊩⟨_⟩_ _) _) (PE.sym $ wk-↑ᵘ [ρ]′ PE.refl) $
          Rec.wk k< [ρ] (⊩<⇔⊩ k< .proj₁ [u]))
        (⊩<≡⇔⊩≡ p .proj₂ $ irrelevanceEq _ _ $
          Rec.wkEq k< [ρ] _ (⊩<≡⇔⊩≡ k< .proj₁ [t≡u]))
  wkEqTerm ρ (Liftᵣ′ D [k] [F]) (Liftₜ₌ _ _ t↘ u↘ t≡u) =
    Liftₜ₌ _ _ (wk-↘∷ ρ t↘) (wk-↘∷ ρ u↘) (wkEqTerm ρ [F] t≡u)
  wkEqTerm ρ (ℕᵣ D) [t≡u] = wkEqTermℕ (⊢ʷᵏʳ→⊢ʷᵏ ρ) [t≡u]
  wkEqTerm ρ (Emptyᵣ D) [t≡u] = wkEqTermEmpty (⊢ʷᵏʳ→⊢ʷᵏ ρ) [t≡u]
  wkEqTerm ρ (Unitᵣ′ _ _) [t≡u] = wkEqTermUnit (⊢ʷᵏʳ→⊢ʷᵏ ρ) [t≡u]
  wkEqTerm {ρ} [ρ] (ne′ _ D neK K≡K) (neₜ₌ k m d d′ nf) =
    neₜ₌ (U.wk ρ k) (U.wk ρ m) (wk-⇒*∷ [ρ] d)
      (wk-⇒*∷ [ρ] d′) (wkEqTermNe (⊢ʷᵏʳ→⊢ʷᵏ [ρ]) nf)
  wkEqTerm {ρ} [ρ] (Πᵣ′ F G _ _ [F] [G] _ _)
    (Πₜ₌ f g d d′ funcF funcG f≡g [f≡g]) =
    Πₜ₌ (U.wk ρ f) (U.wk ρ g) (wk-⇒*∷ [ρ] d) (wk-⇒*∷ [ρ] d′)
      (wk-Functionᵃ [ρ] funcF) (wk-Functionᵃ [ρ] funcG)
      (≅ₜ-wk (⊢ʷᵏʳ→⊢ʷᵏ [ρ]) f≡g)
      (λ [ρ₁] ⊩v ⊩w v≡w →
         let eq   = wk-comp _ _ F
             [F]₁ = [F] _
             [F]₂ = irrelevance′ (PE.sym eq) [F]₁
             ⊩v′  = irrelevanceTerm′ eq [F]₂ [F]₁ ⊩v
             [G]₁ = [G] _ ⊩v′
             [G]₂ = irrelevance′ (wk-comp-subst _ _ G) [G]₁
         in  irrelevanceEqTerm″
               (PE.cong (_∘ _) (PE.sym (wk-comp _ _ _)))
               (PE.cong (_∘ _) (PE.sym (wk-comp _ _ _)))
               (wk-comp-subst _ _ G)
               [G]₁ [G]₂
               ([f≡g] _ ⊩v′ (irrelevanceTerm′ eq [F]₂ [F]₁ ⊩w)
                  (irrelevanceEqTerm′ eq [F]₂ [F]₁ v≡w)))
  wkEqTerm {ρ} [ρ] [A]@(Bᵣ′ BΣʷ F G _ _ [F] [G] _ _)
          (Σₜ₌ p r d d′ (prodₙ {t = p₁}) prodₙ p≅r
              (PE.refl , PE.refl , PE.refl , PE.refl ,
              [p₁] , [r₁] , [fst≡] , [snd≡])) =
    let ρidF≡idρF = begin
                      U.wk ρ (U.wk id F)
                    ≡⟨ PE.cong (U.wk ρ) (wk-id F) ⟩
                      U.wk ρ F
                    ≡⟨ PE.sym (wk-id (U.wk ρ F)) ⟩
                      U.wk id (U.wk ρ F)
                    ∎
        [ρF] = irrelevance′ (PE.sym (wk-comp id ρ F)) ([F] [ρ])
        [ρp₁] = wkTerm [ρ] ([F] _) [p₁]
        [ρp₁]′ = irrelevanceTerm′
                    ρidF≡idρF
                    (wk [ρ] ([F] _)) [ρF]
                    [ρp₁]
        [ρr₁] = wkTerm [ρ] ([F] _) [r₁]
        [ρr₁]′ = irrelevanceTerm′
                    ρidF≡idρF
                    (wk [ρ] ([F] _)) [ρF]
                    [ρr₁]
        [ρfst≡] = wkEqTerm [ρ] ([F] _) [fst≡]
        [ρfst≡]′ = irrelevanceEqTerm′
                     ρidF≡idρF
                     (wk [ρ] ([F] _)) [ρF]
                     [ρfst≡]
        [ρsnd≡] = wkEqTerm [ρ] ([G] _ [p₁]) [snd≡]
        [ρG]′ = irrelevance′ (wk-comp-subst id ρ G)
                  ([G] [ρ]
                     (irrelevanceTerm′ (wk-comp id ρ F)
                        [ρF] ([F] [ρ]) [ρp₁]′))
        ρG-eq = λ t → (begin
                      U.wk ρ (U.wk (lift id) G [ t ]₀)
                    ≡⟨ PE.cong (λ x → U.wk ρ (x [ t ]₀)) (wk-lift-id G) ⟩
                      U.wk ρ (G [ t ]₀)
                    ≡⟨ wk-β G ⟩
                      (U.wk (lift ρ) G) [ U.wk ρ t ]₀
                    ≡⟨ PE.cong (λ x → x [ U.wk ρ t ]₀) (PE.sym (wk-lift-id (U.wk (lift ρ) G))) ⟩
                      (U.wk (lift id) (U.wk (lift ρ) G)) [ U.wk ρ t ]₀
                    ∎)
        [ρsnd≡]′ = irrelevanceEqTerm′
                    (ρG-eq p₁)
                    (wk [ρ] ([G] _ [p₁])) [ρG]′
                    [ρsnd≡]
    in
    Σₜ₌ (U.wk ρ p) (U.wk ρ r) (wk-⇒*∷ [ρ] d) (wk-⇒*∷ [ρ] d′)
      (wkProductᵃ prodₙ) (wkProductᵃ prodₙ) (≅ₜ-wk (⊢ʷᵏʳ→⊢ʷᵏ [ρ]) p≅r)
      (PE.refl , PE.refl , PE.refl , PE.refl ,
       irrelevanceTerm [ρF]
          (irrelevance′ (PE.sym (wk-comp id ρ F)) _) [ρp₁]′ ,
       irrelevanceTerm [ρF]
         (irrelevance′ (PE.sym (wk-comp id ρ F)) _) [ρr₁]′ ,
       irrelevanceEqTerm [ρF]
         (irrelevance′ (PE.sym (wk-comp id ρ F)) _) [ρfst≡]′ ,
       irrelevanceEqTerm [ρG]′
         (irrelevance′ (wk-comp-subst id ρ G) _) [ρsnd≡]′)
  wkEqTerm
    {ρ} [ρ] [A]@(Bᵣ′ BΣʷ _ _ _ _ _ _ _ _)
    (Σₜ₌ p r d d′ (ne x) (ne y) p≅r p~r) =
    let [ρ]′ = ⊢ʷᵏʳ→⊢ʷᵏ [ρ] in
    Σₜ₌ (U.wk ρ p) (U.wk ρ r) (wk-⇒*∷ [ρ] d) (wk-⇒*∷ [ρ] d′)
      (ne (wk-Neutralᵃ [ρ] x)) (ne (wk-Neutralᵃ [ρ] y))
      (≅ₜ-wk [ρ]′ p≅r) (~-wk [ρ]′ p~r)
  wkEqTerm
    {ρ} [ρ] [A]@(Bᵣ′ BΣˢ F G _ _ [F] [G] _ _)
    (Σₜ₌ p r d d′ pProd rProd p≅r ([fstp] , [fstr] , [fst≡] , [snd≡])) =
    let ρidF≡idρF = begin
                      U.wk ρ (U.wk id F)
                    ≡⟨ PE.cong (U.wk ρ) (wk-id F) ⟩
                      U.wk ρ F
                    ≡⟨ PE.sym (wk-id (U.wk ρ F)) ⟩
                      U.wk id (U.wk ρ F)
                    ∎
        [ρF] = irrelevance′ (PE.sym (wk-comp id ρ F)) ([F] [ρ])
        [ρfstp] = wkTerm [ρ] ([F] _) [fstp]
        [ρfstp]′ = irrelevanceTerm′
                    ρidF≡idρF
                    (wk [ρ] ([F] _)) [ρF]
                    [ρfstp]
        [ρfstr] = wkTerm [ρ] ([F] _) [fstr]
        [ρfstr]′ = irrelevanceTerm′
                    ρidF≡idρF
                    (wk [ρ] ([F] _)) [ρF]
                    [ρfstr]
        [ρfst≡] = wkEqTerm [ρ] ([F] _) [fst≡]
        [ρfst≡]′ = irrelevanceEqTerm′
                     ρidF≡idρF
                     (wk [ρ] ([F] _)) [ρF]
                     [ρfst≡]
        [ρsnd≡] = wkEqTerm [ρ] ([G] _ [fstp]) [snd≡]
        [ρG]′ = irrelevance′ (wk-comp-subst id ρ G)
                  ([G] [ρ]
                     (irrelevanceTerm′ (wk-comp id ρ F)
                        [ρF] ([F] [ρ]) [ρfstp]′))
        [ρsnd≡]′ = irrelevanceEqTerm′
          (begin
             U.wk ρ (U.wk (lift id) G [ fst _ p ]₀)                    ≡⟨ PE.cong (λ x → U.wk ρ (x [ fst _ p ]₀)) (wk-lift-id G) ⟩
             U.wk ρ (G [ fst _ p ]₀)                                   ≡⟨ wk-β G ⟩
             (U.wk (lift ρ) G) [ fst _ (U.wk ρ p) ]₀                   ≡⟨ PE.cong (λ x → x [ fst _ (U.wk ρ p) ]₀)
                                                                           (PE.sym (wk-lift-id (U.wk (lift ρ) G))) ⟩
             (U.wk (lift id) (U.wk (lift ρ) G)) [ fst _ (U.wk ρ p) ]₀  ∎)
          (wk [ρ] ([G] _ [fstp])) [ρG]′
          [ρsnd≡]
    in
    Σₜ₌ (U.wk ρ p) (U.wk ρ r) (wk-⇒*∷ [ρ] d) (wk-⇒*∷ [ρ] d′)
      (wk-Productᵃ [ρ] pProd) (wk-Productᵃ [ρ] rProd)
      (≅ₜ-wk (⊢ʷᵏʳ→⊢ʷᵏ [ρ]) p≅r)
      (irrelevanceTerm [ρF]
         (irrelevance′ (PE.sym (wk-comp id ρ F)) _) [ρfstp]′ ,
       irrelevanceTerm [ρF]
         (irrelevance′ (PE.sym (wk-comp id ρ F)) _) [ρfstr]′ ,
       irrelevanceEqTerm [ρF]
         (irrelevance′ (PE.sym (wk-comp id ρ F)) _) [ρfst≡]′ ,
       irrelevanceEqTerm [ρG]′
         (irrelevance′ (wk-comp-subst id ρ G) _) [ρsnd≡]′)
  wkEqTerm ρ∷⊇ (Idᵣ ⊩A) t≡u@(_ , _ , t⇒*t′ , u⇒*u′ , _) =
      _ , _
    , wk-⇒*∷ ρ∷⊇ t⇒*t′
    , wk-⇒*∷ ρ∷⊇ u⇒*u′
    , (case ⊩Id≡∷-view-inhabited ⊩A t≡u of λ where
        (rfl₌ lhs≡rhs) →
            rflₙ , rflₙ
          , wkEqTerm ρ∷⊇ ⊩Ty lhs≡rhs
        (ne t′-n u′-n t′~u′) →
            ne (wk-Neutralᵃ ρ∷⊇ t′-n)
          , ne (wk-Neutralᵃ ρ∷⊇ u′-n)
          , ~-wk (⊢ʷᵏʳ→⊢ʷᵏ ρ∷⊇) t′~u′)
    where
    open _⊩ₗId_ ⊩A

  -- Impossible cases
  wkEqTerm _ (Bᵣ BΣʷ record{}) (Σₜ₌ _ _ _ _ prodₙ (ne _) _ ())
  wkEqTerm _ (Bᵣ BΣʷ record{}) (Σₜ₌ _ _ _ _ (ne _) prodₙ _ ())

private opaque
  wkKit : ∀ l → WkKit l
  wkKit l = <ᵘ-rec WkKit (λ l rec → record { Weakening l rec }) l

module _ {l} where open WkKit (wkKit l) public
