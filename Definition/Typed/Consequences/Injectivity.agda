------------------------------------------------------------------------
-- Injectivity lemmas
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.Injectivity
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M hiding (wk)
import Definition.Untyped M as U
open import Definition.Untyped.Neutral M type-variant

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.EqRelInstance R
open import Definition.LogicalRelation.Hidden R ⦃ eqRelInstance ⦄
open import Definition.LogicalRelation.Properties R ⦃ eqRelInstance ⦄
open import Definition.LogicalRelation.Fundamental.Reducibility R ⦃ eqRelInstance ⦄
open import Definition.LogicalRelation.Substitution.Introductions R ⦃ eqRelInstance ⦄

open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    A A₁ A₂ B B₁ B₂ l l₁ l₂ t₁ t₂ u₁ u₂ : Term _
    p₁ p₂ q₁ q₂ : M
    b₁ b₂ : BinderMode
    s₁ s₂ : Strength

opaque

  -- A kind of injectivity for U.

  U-injectivity :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ U l₁ ≡ U l₂ → Γ ⊢ l₁ ≡ l₂ ∷ Level
  U-injectivity U≡U =
    case ⊩U≡U⇔ .proj₁ $ reducible-⊩≡ U≡U .proj₂ of λ
      (l₁≡l₂ , _) →
    escapeLevelEq l₁≡l₂

opaque

  -- A kind of injectivity for Lift.

  Lift-injectivity :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ Lift l₁ A ≡ Lift l₂ B → Γ ⊢ l₁ ≡ l₂ ∷ Level × Γ ⊢ A ≡ B
  Lift-injectivity Lift≡Lift =
    case ⊩Lift≡Lift⇔ .proj₁ $ reducible-⊩≡ Lift≡Lift .proj₂ of λ
      (_ , _ , l₁≡l₂ , a , b , c) →
    escapeLevelEq l₁≡l₂ , escape-⊩≡ a

opaque

  -- A kind of injectivity for Π and Σ.

  ΠΣ-injectivity′ :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ →
    Γ ⊢ A₁ ≡ A₂ ×
    (⦃ not-ok : No-equality-reflection ⦄ → Γ ∙ A₁ ⊢ B₁ ≡ B₂) ×
    (∀ {t₁ t₂} → Γ ⊢ t₁ ≡ t₂ ∷ A₁ → Γ ⊢ B₁ [ t₁ ]₀ ≡ B₂ [ t₂ ]₀) ×
    p₁ PE.≡ p₂ × q₁ PE.≡ q₂ × b₁ PE.≡ b₂
  ΠΣ-injectivity′ ΠΣ≡ΠΣ =
    let _ , ⊩ΠΣ≡ΠΣ                                = reducible-⊩≡ ΠΣ≡ΠΣ
        _ , b₁≡b₂ , p₁≡p₂ , q₁≡q₂ , A₁≡A₂ , B₁≡B₂ = ⊩ΠΣ≡ΠΣ→ ⊩ΠΣ≡ΠΣ
    in
    escape-⊩≡ A₁≡A₂ ,
    (λ ⦃ not-ok = not-ok ⦄ → escape-⊩≡ (B₁≡B₂ ⦃ inc = not-ok ⦄)) ,
    escape-⊩≡ ∘→ ⊩ΠΣ≡ΠΣ→⊩≡∷→⊩[]₀≡[]₀ ⊩ΠΣ≡ΠΣ ∘→ proj₂ ∘→ reducible-⊩≡∷ ,
    p₁≡p₂ , q₁≡q₂ , b₁≡b₂

opaque

  -- A kind of injectivity for Π and Σ.

  ΠΣ-injectivity :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ →
    Γ ⊢ A₁ ≡ A₂ ×
    (∀ {t₁ t₂} → Γ ⊢ t₁ ≡ t₂ ∷ A₁ → Γ ⊢ B₁ [ t₁ ]₀ ≡ B₂ [ t₂ ]₀) ×
    p₁ PE.≡ p₂ × q₁ PE.≡ q₂ × b₁ PE.≡ b₂
  ΠΣ-injectivity ΠΣ≡ΠΣ =
    let A₁≡A₂ , _ , B₁≡B₂ , p₁≡p₂ , q₁≡q₂ , b₁≡b₂ =
          ΠΣ-injectivity′ ΠΣ≡ΠΣ
    in
    A₁≡A₂ , B₁≡B₂ , p₁≡p₂ , q₁≡q₂ , b₁≡b₂

opaque

  -- A kind of injectivity for Π and Σ.

  ΠΣ-injectivity-no-equality-reflection :
    ⦃ not-ok : No-equality-reflection ⦄ →
    Γ ⊢ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ →
    Γ ⊢ A₁ ≡ A₂ × Γ ∙ A₁ ⊢ B₁ ≡ B₂ ×
    p₁ PE.≡ p₂ × q₁ PE.≡ q₂ × b₁ PE.≡ b₂
  ΠΣ-injectivity-no-equality-reflection ΠΣ≡ΠΣ =
    let A₁≡A₂ , B₁≡B₂ , _ , p₁≡p₂ , q₁≡q₂ , b₁≡b₂ =
          ΠΣ-injectivity′ ⦃ ok = included ⦄ ΠΣ≡ΠΣ
    in
    A₁≡A₂ , B₁≡B₂ , p₁≡p₂ , q₁≡q₂ , b₁≡b₂

opaque

  -- Injectivity of Id.

  Id-injectivity :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ Id A₁ t₁ u₁ ≡ Id A₂ t₂ u₂ →
    (Γ ⊢ A₁ ≡ A₂) × Γ ⊢ t₁ ≡ t₂ ∷ A₁ × Γ ⊢ u₁ ≡ u₂ ∷ A₁
  Id-injectivity Id≡Id =
    case ⊩Id≡Id⇔ .proj₁ $ reducible-⊩≡ Id≡Id .proj₂ of λ
      (A₁≡A₂ , t₁≡t₂ , u₁≡u₂) →
    escape-⊩≡ A₁≡A₂ , escape-⊩≡∷ t₁≡t₂ , escape-⊩≡∷ u₁≡u₂

opaque

  -- Injectivity of suc.

  suc-injectivity :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ suc t₁ ≡ suc t₂ ∷ ℕ →
    Γ ⊢ t₁ ≡ t₂ ∷ ℕ
  suc-injectivity {Γ} {t₁} {t₂} =
    Γ ⊢ suc t₁ ≡ suc t₂ ∷ ℕ                 →⟨ reducible-⊩≡∷ ⟩
    (∃ λ l → Γ ⊩⟨ l ⟩ suc t₁ ≡ suc t₂ ∷ ℕ)  ⇔⟨ Σ-cong-⇔ (λ _ → ⊩suc≡suc∷ℕ⇔) ⟩→
    (∃ λ l → Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ ℕ)          →⟨ escape-⊩≡∷ ∘→ proj₂ ⟩
    Γ ⊢ t₁ ≡ t₂ ∷ ℕ                         □

opaque

  -- Injectivity of Unit.

  Unit-injectivity :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ Unit s₁ l₁ ≡ Unit s₂ l₂ →
    s₁ PE.≡ s₂ × Γ ⊢ l₁ ≡ l₂ ∷ Level
  Unit-injectivity {Γ} {s₁} {l₁} {s₂} {l₂} =
    Γ ⊢ Unit s₁ l₁ ≡ Unit s₂ l₂                 →⟨ reducible-⊩≡ ⟩
    (∃ λ l → Γ ⊩⟨ l ⟩ Unit s₁ l₁ ≡ Unit s₂ l₂)  →⟨ map idᶠ proj₂ ∘→ ⊩Unit≡Unit⇔ .proj₁ ∘→ proj₂ ⟩
    (∃ λ l₁≡l₂ → Unit-allowed s₁ × s₁ PE.≡ s₂)  →⟨ (λ (l₁≡l₂ , _ , s₁≡s₂) → s₁≡s₂ , escapeLevelEq l₁≡l₂) ⟩
    (s₁ PE.≡ s₂ × Γ ⊢ l₁ ≡ l₂ ∷ Level)          □
