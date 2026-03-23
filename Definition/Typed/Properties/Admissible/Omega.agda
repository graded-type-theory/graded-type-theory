------------------------------------------------------------------------
-- Admissible rules related to ω and Ω
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Omega
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  where

open Type-restrictions TR

open import Definition.Typed TR
open import Definition.Typed.Properties.Admissible.Identity TR
open import Definition.Typed.Properties.Admissible.Pi TR
open import Definition.Typed.Properties.Admissible.Pi-Sigma TR
open import Definition.Typed.Properties.Admissible.Var TR
open import Definition.Typed.Properties.Reduction TR
open import Definition.Typed.Weakening TR

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Omega M
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum

private variable
  n   : Nat
  ∇   : DCon _ _
  Γ   : Cons _ _
  A t : Term _
  l   : Lvl _
  p q : M

private opaque

  -- A lemma used below.

  Π≡ :
    Equality-reflection →
    Π-allowed p q →
    Γ ⊢ t ∷ Empty →
    Γ ⊢ A ∷ U l →
    Γ ⊢ Π p , q ▷ A ▹ wk1 A ≡ A
  Π≡ ok₁ ok₂ ⊢t ⊢A =
    _⊢_≡_.univ $
    ⊢∷Empty→⊢≡∷ ok₁ ⊢t (ΠΣⱼ′ ⊢A (wk₁ (univ ⊢A) ⊢A) ok₂) ⊢A

opaque
  unfolding ω

  -- If equality reflection and Π p , q are allowed, the context Γ is
  -- inconsistent (in a certain sense), and Γ ⊢ A ∷ U l holds, then
  -- Γ ⊢ ω p ∷ A holds.

  ⊢ω∷ :
    Equality-reflection →
    Π-allowed p q →
    Γ ⊢ t ∷ Empty →
    Γ ⊢ A ∷ U l →
    Γ ⊢ ω p ∷ A
  ⊢ω∷ ok₁ ok₂ ⊢t ⊢A =
    let ΠAA≡A = Π≡ ok₁ ok₂ ⊢t ⊢A in
    conv
      (lamⱼ′ ok₂ $
       PE.subst (_⊢_∷_ _ _) (wkSingleSubstId _) $
       conv (var₀ (univ ⊢A)) (sym (wk₁ (univ ⊢A) ΠAA≡A)) ∘ⱼ
       var₀ (univ ⊢A))
      ΠAA≡A

opaque
  unfolding Ω

  -- If equality reflection and Π p , q are allowed, the context Γ is
  -- inconsistent (in a certain sense), and Γ ⊢ A ∷ U l holds, then
  -- Γ ⊢ Ω p ∷ A holds.

  ⊢Ω∷ :
    Equality-reflection →
    Π-allowed p q →
    Γ ⊢ t ∷ Empty →
    Γ ⊢ A ∷ U l →
    Γ ⊢ Ω p ∷ A
  ⊢Ω∷ ok₁ ok₂ ⊢t ⊢A =
    let ⊢ω = ⊢ω∷ ok₁ ok₂ ⊢t ⊢A in
    PE.subst (_⊢_∷_ _ _) (wk1-sgSubst _ _)
      (conv ⊢ω (sym (Π≡ ok₁ ok₂ ⊢t ⊢A)) ∘ⱼ ⊢ω)

private opaque
  unfolding Ω ω

  -- Ω does not return WHNFs.

  ¬-Whnf-Ω : ¬ Whnf ∇ (Ω {n = n} p)
  ¬-Whnf-Ω (ne (∘ₙ ()))

opaque
  unfolding Ω ω

  -- Ω returns terms that do not have WHNFs (as terms).

  Ω-does-not-reduce-to-WHNF-⊢∷ : Whnf (Γ .defs) t → ¬ Γ ⊢ Ω p ⇒* t ∷ A
  Ω-does-not-reduce-to-WHNF-⊢∷ Whnf-Ω (id _)      = ¬-Whnf-Ω Whnf-Ω
  Ω-does-not-reduce-to-WHNF-⊢∷ Whnf-u (Ω⇒t ⇨ t⇒u) =
    case inv-⇒-∘ Ω⇒t of λ where
      (inj₁ (_ , _ , ω⇒ , PE.refl)) → ⊥-elim (whnfRedTerm ω⇒ lamₙ)
      (inj₂ (_ , ω≡lam , PE.refl))  →
        case lam-PE-injectivity ω≡lam of λ {
          (_ , PE.refl) →
        Ω-does-not-reduce-to-WHNF-⊢∷ Whnf-u t⇒u }

opaque
  unfolding Ω ω

  -- Ω returns terms that do not have WHNFs (as types).

  Ω-does-not-reduce-to-WHNF-⊢ : Whnf (Γ .defs) A → ¬ Γ ⊢ Ω p ⇒* A
  Ω-does-not-reduce-to-WHNF-⊢ Whnf-Ω (id _)           = ¬-Whnf-Ω Whnf-Ω
  Ω-does-not-reduce-to-WHNF-⊢ Whnf-B (univ Ω⇒A ⇨ A⇒B) =
    case inv-⇒-∘ Ω⇒A of λ where
      (inj₁ (_ , _ , ω⇒ , PE.refl)) → ⊥-elim (whnfRedTerm ω⇒ lamₙ)
      (inj₂ (_ , ω≡lam , PE.refl))  →
        case lam-PE-injectivity ω≡lam of λ {
          (_ , PE.refl) →
        Ω-does-not-reduce-to-WHNF-⊢ Whnf-B A⇒B }
