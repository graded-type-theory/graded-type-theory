------------------------------------------------------------------------
-- Inversion lemmata for the typing relation.
------------------------------------------------------------------------

-- See also Definition.Typed.Inversion.

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.Inversion
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Stability R
open import Definition.Typed.Substitution R

open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Inequality R as I

open import Tools.Empty using (⊥; ⊥-elim)
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    m n : Nat
    Γ : Cons m n
    p p′ q : M
    s s′ s₁ s₂ : Strength
    l₁ l₂ : Universe-level
    A B t u : Term _

opaque

  -- A variant of inversion-lam.

  inversion-lam-Π′ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Γ ⊢ lam p′ t ∷ Π p , q ▷ A ▹ B →
    p PE.≡ p′ × Π-allowed p q ×
    (⦃ not-ok : No-equality-reflection ⦄ → Γ »∙ A ⊢ t ∷ B) ×
    ∃ λ B′ →
      Γ »∙ A ⊢ t ∷ B′ ×
      (∀ {u v} → Γ ⊢ u ≡ v ∷ A → Γ ⊢ B′ [ u ]₀ ≡ B [ v ]₀)
  inversion-lam-Π′ ⊢lam =
    case inversion-lam ⊢lam of λ
      (_ , _ , _ , _ , ⊢t , Π≡Π , ok) →
    case ΠΣ-injectivity′ Π≡Π of λ {
      (A≡A′ , B≡B′ , B[]≡B′[] , PE.refl , PE.refl , _) →
    let ⊢t = stabilityTerm (refl-∙ (sym A≡A′)) ⊢t in
    PE.refl , ok ,
    (λ ⦃ _ ⦄ → conv ⊢t (sym B≡B′)) ,
    _ , ⊢t , (λ {_ _} u≡v → sym (B[]≡B′[] (sym′ u≡v))) }

opaque

  -- A variant of inversion-lam.

  inversion-lam-Π :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Γ ⊢ lam p′ t ∷ Π p , q ▷ A ▹ B →
    ∃ λ B′ →
      Γ »∙ A ⊢ t ∷ B′ ×
      (∀ {u v} → Γ ⊢ u ≡ v ∷ A → Γ ⊢ B′ [ u ]₀ ≡ B [ v ]₀) ×
      p PE.≡ p′ × Π-allowed p q
  inversion-lam-Π ⊢lam =
    let p≡p′ , ok , _ , _ , ⊢t , B[]≡B′[] = inversion-lam-Π′ ⊢lam in
    _ , ⊢t , B[]≡B′[] , p≡p′ , ok

opaque

  -- A variant of inversion-lam.

  inversion-lam-Π-no-equality-reflection :
    ⦃ ok : No-equality-reflection ⦄ →
    Γ ⊢ lam p′ t ∷ Π p , q ▷ A ▹ B →
    Γ »∙ A ⊢ t ∷ B × p PE.≡ p′ × Π-allowed p q
  inversion-lam-Π-no-equality-reflection ⊢lam =
    let p≡p′ , ok , ⊢t , _ = inversion-lam-Π′ ⦃ ok = included ⦄ ⊢lam in
    ⊢t , p≡p′ , ok

opaque

  -- A variant of inversion-prod.

  inversion-prod-Σ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Γ ⊢ prod s′ p′ t u ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B →
    Γ ⊢ t ∷ A × Γ ⊢ u ∷ B [ t ]₀ ×
    s PE.≡ s′ × p PE.≡ p′ × Σ-allowed s p q
  inversion-prod-Σ ⊢prod =
    case inversion-prod ⊢prod of λ {
      (_ , _ , _ , _ , _ , ⊢t , ⊢u , Σ≡Σ , ok) →
    case ΠΣ-injectivity Σ≡Σ of λ {
      (A≡A′ , B[]≡B′[] , PE.refl , PE.refl , PE.refl) →
    case conv ⊢t (sym A≡A′) of λ {
      ⊢t →
      ⊢t
    , conv ⊢u (sym (B[]≡B′[] (refl ⊢t)))
    , PE.refl
    , PE.refl
    , ok }}}

opaque

  -- A variant of inversion-star.

  inversion-star-Unit :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Γ ⊢ star s₁ l₁ ∷ Unit s₂ l₂ →
    s₁ PE.≡ s₂ × l₁ PE.≡ l₂ × Unit-allowed s₁
  inversion-star-Unit ⊢star =
    let Unit≡Unit , Unit-ok = inversion-star ⊢star
        eq₁ , eq₂           = Unit-injectivity (sym Unit≡Unit)
    in
    eq₁ , eq₂ , Unit-ok

opaque

  -- A variant of inversion-rfl.

  inversion-rfl-Id :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Γ ⊢ rfl ∷ Id A t u →
    Γ ⊢ t ≡ u ∷ A
  inversion-rfl-Id ⊢rfl =
    case inversion-rfl ⊢rfl of λ {
      (_ , _ , _ , _ , Id≡Id) →
    case Id-injectivity Id≡Id of λ {
      (_ , t≡v , u≡v) →
    trans t≡v (sym′ u≡v) }}

opaque

  -- Inversion of products in WHNF.

  whnfProduct :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Γ ⊢ t ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B → Whnf (Γ .defs) t →
    Product⁺ (Γ .defs) t
  whnfProduct ⊢t = λ where
    prodₙ →
      prodₙ
    (ne t-ne) →
      ne t-ne
    Uₙ →
      ⊥-elim (U≢ΠΣⱼ (sym (inversion-U ⊢t)))
    ΠΣₙ →
      let _ , _ , _ , _ , Σ≡U , _ = inversion-ΠΣ-U ⊢t in
      ⊥-elim (U≢ΠΣⱼ (sym Σ≡U))
    ℕₙ →
      ⊥-elim (U≢ΠΣⱼ (sym (inversion-ℕ ⊢t)))
    Unitₙ →
      ⊥-elim (U≢ΠΣⱼ (sym (inversion-Unit-U ⊢t .proj₁)))
    Emptyₙ →
      ⊥-elim (U≢ΠΣⱼ (sym (inversion-Empty ⊢t)))
    lamₙ →
      let _ , _ , _ , _ , _ , Σ≡Π , _ = inversion-lam ⊢t in
      ⊥-elim (Π≢Σⱼ (sym Σ≡Π))
    zeroₙ →
      ⊥-elim (ℕ≢ΠΣⱼ (sym (inversion-zero ⊢t)))
    sucₙ →
      let _ , A≡ℕ = inversion-suc ⊢t in
      ⊥-elim (ℕ≢ΠΣⱼ (sym A≡ℕ))
    starₙ →
      ⊥-elim (Unit≢ΠΣⱼ (sym (inversion-star ⊢t .proj₁)))
    Idₙ →
      let _ , _ , _ , _ , eq = inversion-Id-U ⊢t in
      ⊥-elim (U≢ΠΣⱼ (sym eq))
    rflₙ →
      let _ , _ , _ , _ , eq = inversion-rfl ⊢t in
      ⊥-elim (I.Id≢ΠΣ (sym eq))
