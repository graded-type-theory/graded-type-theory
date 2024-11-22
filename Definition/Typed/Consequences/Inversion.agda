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
open import Definition.Untyped.Neutral M type-variant
open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Stability R
open import Definition.Typed.Substitution R

open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Inequality R as I

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Empty using (⊥; ⊥-elim)

private
  variable
    n : Nat
    Γ : Con Term n
    p p′ q : M
    s s′ s₁ s₂ : Strength
    l₁ l₂ : Universe-level
    A B t u : Term _

opaque

  -- A variant of inversion-lam.

  inversion-lam-Π :
    Γ ⊢ lam p′ t ∷ Π p , q ▷ A ▹ B →
    Γ ∙ A ⊢ t ∷ B × p PE.≡ p′ × Π-allowed p q
  inversion-lam-Π ⊢lam =
    case inversion-lam ⊢lam of λ {
      (_ , _ , _ , _ , ⊢t , Π≡Π , ok) →
    case ΠΣ-injectivity Π≡Π of λ {
      (A≡A′ , B≡B′ , PE.refl , PE.refl , _) →
      conv (stabilityTerm (refl-∙ (sym A≡A′)) ⊢t) (sym B≡B′)
    , PE.refl
    , ok }}

opaque

  -- A variant of inversion-prod.

  inversion-prod-Σ :
    Γ ⊢ prod s′ p′ t u ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B →
    Γ ⊢ t ∷ A × Γ ⊢ u ∷ B [ t ]₀ ×
    s PE.≡ s′ × p PE.≡ p′ × Σ-allowed s p q
  inversion-prod-Σ ⊢prod =
    case inversion-prod ⊢prod of λ {
      (_ , _ , _ , _ , _ , ⊢t , ⊢u , Σ≡Σ , ok) →
    case ΠΣ-injectivity Σ≡Σ of λ {
      (A≡A′ , B≡B′ , PE.refl , PE.refl , PE.refl) →
    case conv ⊢t (sym A≡A′) of λ {
      ⊢t →
      ⊢t
    , conv ⊢u (sym (substTypeEq B≡B′ (refl ⊢t)))
    , PE.refl
    , PE.refl
    , ok }}}

opaque

  -- A variant of inversion-star.

  inversion-star-Unit :
    Γ ⊢ star s₁ l₁ ∷ Unit s₂ l₂ →
    s₁ PE.≡ s₂ × l₁ PE.≡ l₂ × Unit-allowed s₁
  inversion-star-Unit ⊢star =
    let Unit≡Unit , ok = inversion-star ⊢star
        eq₁ , eq₂      = Unit-injectivity (sym Unit≡Unit)
    in
    eq₁ , eq₂ , ok

opaque

  -- A variant of inversion-rfl.

  inversion-rfl-Id : Γ ⊢ rfl ∷ Id A t u → Γ ⊢ t ≡ u ∷ A
  inversion-rfl-Id ⊢rfl =
    case inversion-rfl ⊢rfl of λ {
      (_ , _ , _ , _ , Id≡Id) →
    case Id-injectivity Id≡Id of λ {
      (_ , t≡v , u≡v) →
    trans t≡v (sym′ u≡v) }}

-- Inversion of products in WHNF.
whnfProduct :
  ∀ {p F G m} →
  Γ ⊢ p ∷ Σ⟨ m ⟩ p′ , q ▷ F ▹ G → Whnf p → Product p
whnfProduct x prodₙ = prodₙ
whnfProduct x (ne pNe) = ne pNe
whnfProduct ⊢∷Σ Uₙ = ⊥-elim (U≢ΠΣⱼ (sym (inversion-U ⊢∷Σ)))
whnfProduct x ΠΣₙ =
  let _ , _ , _ , _ , Σ≡U , _ = inversion-ΠΣ-U x
  in  ⊥-elim (U≢ΠΣⱼ (sym Σ≡U))
whnfProduct x ℕₙ = ⊥-elim (U≢ΠΣⱼ (sym (inversion-ℕ x)))
whnfProduct x Unitₙ = ⊥-elim (U≢ΠΣⱼ (sym (inversion-Unit-U x .proj₁)))
whnfProduct x Emptyₙ = ⊥-elim (U≢ΠΣⱼ (sym (inversion-Empty x)))
whnfProduct x lamₙ =
  let _ , _ , _ , _ , _ , Σ≡Π , _ = inversion-lam x
  in  ⊥-elim (Π≢Σⱼ (sym Σ≡Π))
whnfProduct x zeroₙ = ⊥-elim (ℕ≢ΠΣⱼ (sym (inversion-zero x)))
whnfProduct x sucₙ =
  let _ , A≡ℕ = inversion-suc x
  in  ⊥-elim (ℕ≢ΠΣⱼ (sym A≡ℕ))
whnfProduct x starₙ = ⊥-elim (Unit≢ΠΣⱼ (sym (inversion-star x .proj₁)))
whnfProduct ⊢∷Σ Idₙ =
  ⊥-elim (U≢ΠΣⱼ (sym (inversion-Id-U ⊢∷Σ .proj₂ .proj₂ .proj₂ .proj₂)))
whnfProduct ⊢∷Σ rflₙ =
  ⊥-elim (I.Id≢ΠΣ (sym (inversion-rfl ⊢∷Σ .proj₂ .proj₂ .proj₂ .proj₂)))
