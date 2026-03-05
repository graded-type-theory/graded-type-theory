------------------------------------------------------------------------
-- Inversion lemmas related to the algorithmic equality relations
------------------------------------------------------------------------

-- Some inversion lemmas do not return all available information. If
-- something can be easily recreated using the soundness lemmas, then
-- it is at least sometimes omitted.

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Conversion.Inversion
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Conversion R
open import Definition.Conversion.Whnf R

open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Well-formed R
open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Untyped.Whnf M type-variant

open import Tools.Empty
open import Tools.Function
open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum

private variable
  α β m n                           : Nat
  x y                               : Fin _
  ∇                                 : DCon (Term 0) _
  Γ                                 : Cons _ _
  A A₁ A₂ B B₁ B₂ C C₁ C₂
    t t₁ t₂ t₃ t₄ u u₁ u₂ u₃ u₄ v w : Term _
  l l₁ l₂                           : Lvl _
  V                                 : Set a
  b                                 : BinderMode
  s                                 : Strength
  p q r                             : M

------------------------------------------------------------------------
-- Inversion and similar lemmas for _⊢_~_↑_

opaque

  -- A kind of inversion lemma for var.

  inv-~-var :
    Γ ⊢ t ~ u ↑ A →
    (∃ λ x → t PE.≡ var x × u PE.≡ var x) ⊎
    ¬ (∃ λ x → t PE.≡ var x) × ¬ (∃ λ x → u PE.≡ var x)
  inv-~-var = λ where
    (var-refl _ PE.refl)         → inj₁ (_ , PE.refl , PE.refl)
    (defn-refl _ _ _)            → inj₂ ((λ ()) , (λ ()))
    (lower-cong _)               → inj₂ ((λ ()) , (λ ()))
    (app-cong _ _)               → inj₂ ((λ ()) , (λ ()))
    (fst-cong _)                 → inj₂ ((λ ()) , (λ ()))
    (snd-cong _)                 → inj₂ ((λ ()) , (λ ()))
    (prodrec-cong _ _ _)         → inj₂ ((λ ()) , (λ ()))
    (emptyrec-cong _ _)          → inj₂ ((λ ()) , (λ ()))
    (unitrec-cong _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (natrec-cong _ _ _ _)        → inj₂ ((λ ()) , (λ ()))
    (J-cong _ _ _ _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (K-cong _ _ _ _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    ([]-cong-cong _ _ _ _ _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for var.

  inv-var~ :
    Γ ⊢ var x ~ u ↑ A →
    u PE.≡ var x
  inv-var~ (var-refl _ PE.refl) = PE.refl

opaque

  -- Inversion for var.

  inv-~var :
    Γ ⊢ t ~ var y ↑ A →
    t PE.≡ var y
  inv-~var (var-refl _ PE.refl) = PE.refl

opaque

  -- A kind of inversion lemma for var.

  inv-~-defn :
    Γ ⊢ t ~ u ↑ A →
    (∃₂ λ α A → α ↦⊘∷ A ∈ Γ .defs × t PE.≡ defn α × u PE.≡ defn α) ⊎
    ¬ (∃ λ α → t PE.≡ defn α) × ¬ (∃ λ α → u PE.≡ defn α)
  inv-~-defn = λ where
    (defn-refl _ α↦⊘ PE.refl)    → inj₁ (_ , _ , α↦⊘ , PE.refl , PE.refl)
    (var-refl _ _)               → inj₂ ((λ ()) , (λ ()))
    (lower-cong _)               → inj₂ ((λ ()) , (λ ()))
    (app-cong _ _)               → inj₂ ((λ ()) , (λ ()))
    (fst-cong _)                 → inj₂ ((λ ()) , (λ ()))
    (snd-cong _)                 → inj₂ ((λ ()) , (λ ()))
    (prodrec-cong _ _ _)         → inj₂ ((λ ()) , (λ ()))
    (emptyrec-cong _ _)          → inj₂ ((λ ()) , (λ ()))
    (unitrec-cong _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (natrec-cong _ _ _ _)        → inj₂ ((λ ()) , (λ ()))
    (J-cong _ _ _ _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (K-cong _ _ _ _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    ([]-cong-cong _ _ _ _ _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for defn.

  inv-defn~ :
    Γ ⊢ defn α ~ u ↑ A →
    u PE.≡ defn α
  inv-defn~ (defn-refl _ _ PE.refl) = PE.refl

opaque

  -- Inversion for defn.

  inv-~defn :
    Γ ⊢ t ~ defn β ↑ A →
    t PE.≡ defn β
  inv-~defn (defn-refl _ _ PE.refl) = PE.refl

opaque

  -- Inversion for U.

  inv-U~ : ¬ Γ ⊢ U l ~ u ↑ A
  inv-U~ ()

opaque

  -- Inversion for U.

  inv-~U : ¬ Γ ⊢ t ~ U l ↑ A
  inv-~U ()

opaque

  -- Inversion for ΠΣ.

  inv-ΠΣ~ : ¬ Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ B₁ ▹ B₂ ~ u ↑ A
  inv-ΠΣ~ ()

opaque

  -- Inversion for ΠΣ.

  inv-~ΠΣ : ¬ Γ ⊢ t ~ ΠΣ⟨ b ⟩ p , q ▷ C₁ ▹ C₂ ↑ A
  inv-~ΠΣ ()

opaque

  -- A kind of inversion lemma for lower.

  inv-~-lower :
    Γ ⊢ t ~ u ↑ A →
    (∃₃ λ l t′ u′ →
     t PE.≡ lower t′ × u PE.≡ lower u′ ×
     Γ ⊢ t′ ~ u′ ↓ Lift l A) ⊎
    ¬ (∃ λ t′ → t PE.≡ lower t′) × ¬ (∃ λ u′ → u PE.≡ lower u′)
  inv-~-lower = λ where
    (lower-cong t′~u′) →
      inj₁ (_ , _ , _ , PE.refl , PE.refl , t′~u′)
    (var-refl _ _)               → inj₂ ((λ ()) , (λ ()))
    (defn-refl _ _ _)            → inj₂ ((λ ()) , (λ ()))
    (app-cong _ _)               → inj₂ ((λ ()) , (λ ()))
    (fst-cong _)                 → inj₂ ((λ ()) , (λ ()))
    (snd-cong _)                 → inj₂ ((λ ()) , (λ ()))
    (prodrec-cong _ _ _)         → inj₂ ((λ ()) , (λ ()))
    (emptyrec-cong _ _)          → inj₂ ((λ ()) , (λ ()))
    (unitrec-cong _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (natrec-cong _ _ _ _)        → inj₂ ((λ ()) , (λ ()))
    (J-cong _ _ _ _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (K-cong _ _ _ _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    ([]-cong-cong _ _ _ _ _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for lower.

  inv-lower~ :
    Γ ⊢ lower t ~ u ↑ A →
    ∃₂ λ l u′ →
    u PE.≡ lower u′ ×
    Γ ⊢ t ~ u′ ↓ Lift l A
  inv-lower~ (lower-cong t~u′) = _ , _ , PE.refl , t~u′

opaque

  -- Inversion for lam.

  inv-lam~ : ¬ Γ ⊢ lam p t ~ u ↑ A
  inv-lam~ ()

opaque

  -- Inversion for lam.

  inv-~lam : ¬ Γ ⊢ t ~ lam p u ↑ A
  inv-~lam ()

opaque

  -- A kind of inversion lemma for _∘⟨_⟩_.

  inv-~-∘ :
    Γ ⊢ t ~ u ↑ A →
    (∃₈ λ p q B C t₁ t₂ u₁ u₂ →
     A PE.≡ C [ t₂ ]₀ × t PE.≡ t₁ ∘⟨ p ⟩ t₂ × u PE.≡ u₁ ∘⟨ p ⟩ u₂ ×
     Γ ⊢ t₁ ~ u₁ ↓ Π p , q ▷ B ▹ C ×
     Γ ⊢ t₂ [conv↑] u₂ ∷ B) ⊎
    ¬ (∃₃ λ p t₁ t₂ → t PE.≡ t₁ ∘⟨ p ⟩ t₂) ×
    ¬ (∃₃ λ p u₁ u₂ → u PE.≡ u₁ ∘⟨ p ⟩ u₂)
  inv-~-∘ = λ where
    (app-cong t₁~u₁ t₂≡u₂) →
      inj₁ $
      _ , _ , _ , _ , _ , _ , _ , _ ,
      PE.refl , PE.refl , PE.refl , t₁~u₁ , t₂≡u₂
    (var-refl _ _)               → inj₂ ((λ ()) , (λ ()))
    (defn-refl _ _ _)            → inj₂ ((λ ()) , (λ ()))
    (lower-cong _)               → inj₂ ((λ ()) , (λ ()))
    (fst-cong _)                 → inj₂ ((λ ()) , (λ ()))
    (snd-cong _)                 → inj₂ ((λ ()) , (λ ()))
    (prodrec-cong _ _ _)         → inj₂ ((λ ()) , (λ ()))
    (emptyrec-cong _ _)          → inj₂ ((λ ()) , (λ ()))
    (unitrec-cong _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (natrec-cong _ _ _ _)        → inj₂ ((λ ()) , (λ ()))
    (J-cong _ _ _ _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (K-cong _ _ _ _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    ([]-cong-cong _ _ _ _ _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for _∘⟨_⟩_.

  inv-∘~ :
    Γ ⊢ t₁ ∘⟨ p ⟩ t₂ ~ u ↑ A →
    ∃₅ λ q B C u₁ u₂ →
    A PE.≡ C [ t₂ ]₀ ×
    u PE.≡ u₁ ∘⟨ p ⟩ u₂ ×
    Γ ⊢ t₁ ~ u₁ ↓ Π p , q ▷ B ▹ C ×
    Γ ⊢ t₂ [conv↑] u₂ ∷ B
  inv-∘~ (app-cong t₁~u₁ t₂≡u₂) =
    _ , _ , _ , _ , _ , PE.refl , PE.refl , t₁~u₁ , t₂≡u₂

opaque

  -- Inversion for _∘⟨_⟩_.

  inv-~∘ :
    Γ ⊢ t ~ u₁ ∘⟨ p ⟩ u₂ ↑ A →
    ∃₅ λ q B C t₁ t₂ →
    A PE.≡ C [ t₂ ]₀ ×
    t PE.≡ t₁ ∘⟨ p ⟩ t₂ ×
    Γ ⊢ t₁ ~ u₁ ↓ Π p , q ▷ B ▹ C ×
    Γ ⊢ t₂ [conv↑] u₂ ∷ B
  inv-~∘ (app-cong t₁~u₁ t₂≡u₂) =
    _ , _ , _ , _ , _ , PE.refl , PE.refl , t₁~u₁ , t₂≡u₂

opaque

  -- Inversion for prod.

  inv-prod~ : ¬ Γ ⊢ prod s p t₁ t₂ ~ u ↑ A
  inv-prod~ ()

opaque

  -- Inversion for prod.

  inv-~prod : ¬ Γ ⊢ t ~ prod s p u₁ u₂ ↑ A
  inv-~prod ()

opaque

  -- A kind of inversion lemma for fst.

  inv-~-fst :
    Γ ⊢ t ~ u ↑ A →
    (∃₅ λ p q B t′ u′ →
     t PE.≡ fst p t′ × u PE.≡ fst p u′ ×
     Γ ⊢ t′ ~ u′ ↓ Σˢ p , q ▷ A ▹ B) ⊎
    ¬ (∃₂ λ p t′ → t PE.≡ fst p t′) × ¬ (∃₂ λ p u′ → u PE.≡ fst p u′)
  inv-~-fst = λ where
    (fst-cong t′~u′) →
      inj₁ (_ , _ , _ , _ , _ , PE.refl , PE.refl , t′~u′)
    (var-refl _ _)               → inj₂ ((λ ()) , (λ ()))
    (defn-refl _ _ _)            → inj₂ ((λ ()) , (λ ()))
    (lower-cong _)               → inj₂ ((λ ()) , (λ ()))
    (app-cong _ _)               → inj₂ ((λ ()) , (λ ()))
    (snd-cong _)                 → inj₂ ((λ ()) , (λ ()))
    (prodrec-cong _ _ _)         → inj₂ ((λ ()) , (λ ()))
    (emptyrec-cong _ _)          → inj₂ ((λ ()) , (λ ()))
    (unitrec-cong _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (natrec-cong _ _ _ _)        → inj₂ ((λ ()) , (λ ()))
    (J-cong _ _ _ _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (K-cong _ _ _ _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    ([]-cong-cong _ _ _ _ _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for fst.

  inv-fst~ :
    Γ ⊢ fst p t ~ u ↑ A →
    ∃₃ λ q B u′ →
    u PE.≡ fst p u′ ×
    Γ ⊢ t ~ u′ ↓ Σˢ p , q ▷ A ▹ B
  inv-fst~ (fst-cong t~u′) = _ , _ , _ , PE.refl , t~u′

opaque

  -- Inversion for fst.

  inv-~fst :
    Γ ⊢ t ~ fst p u ↑ A →
    ∃₃ λ q B t′ →
    t PE.≡ fst p t′ ×
    Γ ⊢ t′ ~ u ↓ Σˢ p , q ▷ A ▹ B
  inv-~fst (fst-cong t′~u) = _ , _ , _ , PE.refl , t′~u

opaque

  -- A kind of inversion lemma for snd.

  inv-~-snd :
    Γ ⊢ t ~ u ↑ A →
    (∃₆ λ p q B C t′ u′ →
     A PE.≡ C [ fst p t′ ]₀ × t PE.≡ snd p t′ × u PE.≡ snd p u′ ×
     Γ ⊢ t′ ~ u′ ↓ Σˢ p , q ▷ B ▹ C) ⊎
    ¬ (∃₂ λ p t′ → t PE.≡ snd p t′) × ¬ (∃₂ λ p u′ → u PE.≡ snd p u′)
  inv-~-snd = λ where
    (snd-cong t′~u′) →
      inj₁ (_ , _ , _ , _ , _ , _ , PE.refl , PE.refl , PE.refl , t′~u′)
    (var-refl _ _)               → inj₂ ((λ ()) , (λ ()))
    (defn-refl _ _ _)            → inj₂ ((λ ()) , (λ ()))
    (lower-cong _)               → inj₂ ((λ ()) , (λ ()))
    (app-cong _ _)               → inj₂ ((λ ()) , (λ ()))
    (fst-cong _)                 → inj₂ ((λ ()) , (λ ()))
    (prodrec-cong _ _ _)         → inj₂ ((λ ()) , (λ ()))
    (emptyrec-cong _ _)          → inj₂ ((λ ()) , (λ ()))
    (unitrec-cong _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (natrec-cong _ _ _ _)        → inj₂ ((λ ()) , (λ ()))
    (J-cong _ _ _ _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (K-cong _ _ _ _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    ([]-cong-cong _ _ _ _ _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for snd.

  inv-snd~ :
    Γ ⊢ snd p t ~ u ↑ A →
    ∃₄ λ q B C u′ →
    A PE.≡ C [ fst p t ]₀ ×
    u PE.≡ snd p u′ ×
    Γ ⊢ t ~ u′ ↓ Σˢ p , q ▷ B ▹ C
  inv-snd~ (snd-cong t~u′) = _ , _ , _ , _ , PE.refl , PE.refl , t~u′

opaque

  -- Inversion for snd.

  inv-~snd :
    Γ ⊢ t ~ snd p u ↑ A →
    ∃₄ λ q B C t′ →
    A PE.≡ C [ fst p t′ ]₀ ×
    t PE.≡ snd p t′ ×
    Γ ⊢ t′ ~ u ↓ Σˢ p , q ▷ B ▹ C
  inv-~snd (snd-cong t′~u) = _ , _ , _ , _ , PE.refl , PE.refl , t′~u

opaque

  -- A kind of inversion lemma for prodrec.

  inv-~-prodrec :
    Γ ⊢ t ~ u ↑ A →
    (∃₄ λ r p q′ q → ∃₈ λ A₁ A₂ B C t₁ t₂ u₁ u₂ →
     A PE.≡ B [ t₁ ]₀ ×
     t PE.≡ prodrec r p q′ B t₁ t₂ ×
     u PE.≡ prodrec r p q′ C u₁ u₂ ×
     (Γ »∙ Σʷ p , q ▷ A₁ ▹ A₂ ⊢ B [conv↑] C) ×
     Γ ⊢ t₁ ~ u₁ ↓ Σʷ p , q ▷ A₁ ▹ A₂ ×
     Γ »∙ A₁ »∙ A₂ ⊢ t₂ [conv↑] u₂ ∷ B [ prodʷ p (var x1) (var x0) ]↑²) ⊎
    ¬ (∃₆ λ r p q′ B t₁ t₂ → t PE.≡ prodrec r p q′ B t₁ t₂) ×
    ¬ (∃₆ λ r p q′ C u₁ u₂ → u PE.≡ prodrec r p q′ C u₁ u₂)
  inv-~-prodrec = λ where
    (prodrec-cong B≡C t₁~u₁ t₂≡u₂) →
      inj₁ $
      _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ ,
      PE.refl , PE.refl , PE.refl , B≡C , t₁~u₁ , t₂≡u₂
    (var-refl _ _)               → inj₂ ((λ ()) , (λ ()))
    (defn-refl _ _ _)            → inj₂ ((λ ()) , (λ ()))
    (lower-cong _)               → inj₂ ((λ ()) , (λ ()))
    (app-cong _ _)               → inj₂ ((λ ()) , (λ ()))
    (fst-cong _)                 → inj₂ ((λ ()) , (λ ()))
    (snd-cong _)                 → inj₂ ((λ ()) , (λ ()))
    (emptyrec-cong _ _)          → inj₂ ((λ ()) , (λ ()))
    (unitrec-cong _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (natrec-cong _ _ _ _)        → inj₂ ((λ ()) , (λ ()))
    (J-cong _ _ _ _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (K-cong _ _ _ _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    ([]-cong-cong _ _ _ _ _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for prodrec.

  inv-prodrec~ :
    Γ ⊢ prodrec r p q B t₁ t₂ ~ u ↑ A →
    ∃₆ λ q′ A₁ A₂ C u₁ u₂ →
    A PE.≡ B [ t₁ ]₀ ×
    u PE.≡ prodrec r p q C u₁ u₂ ×
    (Γ »∙ Σʷ p , q′ ▷ A₁ ▹ A₂ ⊢ B [conv↑] C) ×
    Γ ⊢ t₁ ~ u₁ ↓ Σʷ p , q′ ▷ A₁ ▹ A₂ ×
    Γ »∙ A₁ »∙ A₂ ⊢ t₂ [conv↑] u₂ ∷ B [ prodʷ p (var x1) (var x0) ]↑²
  inv-prodrec~ (prodrec-cong B≡C t₁~u₁ t₂≡u₂) =
     _ , _ , _ , _ , _ , _ , PE.refl , PE.refl , B≡C , t₁~u₁ , t₂≡u₂

opaque

  -- Inversion for prodrec.

  inv-~prodrec :
    Γ ⊢ t ~ prodrec r p q C u₁ u₂ ↑ A →
    ∃₆ λ q′ A₁ A₂ B t₁ t₂ →
    A PE.≡ B [ t₁ ]₀ ×
    t PE.≡ prodrec r p q B t₁ t₂ ×
    (Γ »∙ Σʷ p , q′ ▷ A₁ ▹ A₂ ⊢ B [conv↑] C) ×
    Γ ⊢ t₁ ~ u₁ ↓ Σʷ p , q′ ▷ A₁ ▹ A₂ ×
    Γ »∙ A₁ »∙ A₂ ⊢ t₂ [conv↑] u₂ ∷ B [ prodʷ p (var x1) (var x0) ]↑²
  inv-~prodrec (prodrec-cong B≡C t₁~u₁ t₂≡u₂) =
     _ , _ , _ , _ , _ , _ , PE.refl , PE.refl , B≡C , t₁~u₁ , t₂≡u₂

opaque

  -- Inversion for Empty.

  inv-Empty~ : ¬ Γ ⊢ Empty ~ u ↑ A
  inv-Empty~ ()

opaque

  -- Inversion for Empty.

  inv-~Empty : ¬ Γ ⊢ t ~ Empty ↑ A
  inv-~Empty ()

opaque

  -- A kind of inversion lemma for emptyrec.

  inv-~-emptyrec :
    Γ ⊢ t ~ u ↑ A →
    (∃₄ λ p B t′ u′ →
     t PE.≡ emptyrec p A t′ × u PE.≡ emptyrec p B u′ ×
     (Γ ⊢ A [conv↑] B) ×
     Γ ⊢ t′ ~ u′ ↓ Empty) ⊎
    ¬ (∃₃ λ p A t′ → t PE.≡ emptyrec p A t′) ×
    ¬ (∃₃ λ p B u′ → u PE.≡ emptyrec p B u′)
  inv-~-emptyrec = λ where
    (emptyrec-cong A≡B t′~u′) →
      inj₁ (_ , _ , _ , _ , PE.refl , PE.refl , A≡B , t′~u′)
    (var-refl _ _)               → inj₂ ((λ ()) , (λ ()))
    (defn-refl _ _ _)            → inj₂ ((λ ()) , (λ ()))
    (lower-cong _)               → inj₂ ((λ ()) , (λ ()))
    (app-cong _ _)               → inj₂ ((λ ()) , (λ ()))
    (fst-cong _)                 → inj₂ ((λ ()) , (λ ()))
    (snd-cong _)                 → inj₂ ((λ ()) , (λ ()))
    (prodrec-cong _ _ _)         → inj₂ ((λ ()) , (λ ()))
    (unitrec-cong _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (natrec-cong _ _ _ _)        → inj₂ ((λ ()) , (λ ()))
    (J-cong _ _ _ _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (K-cong _ _ _ _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    ([]-cong-cong _ _ _ _ _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for emptyrec.

  inv-emptyrec~ :
    Γ ⊢ emptyrec p B t ~ u ↑ A →
    ∃₂ λ C u′ →
    A PE.≡ B ×
    u PE.≡ emptyrec p C u′ ×
    Γ ⊢ B [conv↑] C ×
    Γ ⊢ t ~ u′ ↓ Empty
  inv-emptyrec~ (emptyrec-cong B≡C t~u) =
    _ , _ , PE.refl , PE.refl , B≡C , t~u

opaque

  -- Inversion for emptyrec.

  inv-~emptyrec :
    Γ ⊢ t ~ emptyrec p C u ↑ A →
    ∃ λ t′ →
    t PE.≡ emptyrec p A t′ ×
    Γ ⊢ A [conv↑] C ×
    Γ ⊢ t′ ~ u ↓ Empty
  inv-~emptyrec (emptyrec-cong A≡C t~u) =
    _ , PE.refl , A≡C , t~u

opaque

  -- Inversion for Unit.

  inv-Unit~ : ¬ Γ ⊢ Unit s ~ u ↑ A
  inv-Unit~ ()

opaque

  -- Inversion for Unit.

  inv-~Unit : ¬ Γ ⊢ t ~ Unit s ↑ A
  inv-~Unit ()

opaque

  -- Inversion for star.

  inv-star~ : ¬ Γ ⊢ star s ~ u ↑ A
  inv-star~ ()

opaque

  -- Inversion for star.

  inv-~star : ¬ Γ ⊢ t ~ star s ↑ A
  inv-~star ()

opaque

  -- A kind of inversion lemma for unitrec.

  inv-~-unitrec :
    Γ ⊢ t ~ u ↑ A →
    (∃₂ λ p q → ∃₆ λ B C t₁ t₂ u₁ u₂ →
     A PE.≡ B [ t₁ ]₀ ×
     t PE.≡ unitrec p q B t₁ t₂ ×
     u PE.≡ unitrec p q C u₁ u₂ ×
     (Γ »∙ Unitʷ ⊢ B [conv↑] C) ×
     Γ ⊢ t₁ ~ u₁ ↓ Unitʷ ×
     Γ ⊢ t₂ [conv↑] u₂ ∷ B [ starʷ ]₀ ×
     ¬ Unitʷ-η) ⊎
    ¬ (∃₅ λ p q B t₁ t₂ → t PE.≡ unitrec p q B t₁ t₂) ×
    ¬ (∃₅ λ p q C u₁ u₂ → u PE.≡ unitrec p q C u₁ u₂)
  inv-~-unitrec = λ where
    (unitrec-cong B≡C t₁~u₁ t₂≡u₂ no-η) →
      inj₁ $
      _ , _ , _ , _ , _ , _ , _ , _ ,
      PE.refl , PE.refl , PE.refl , B≡C , t₁~u₁ , t₂≡u₂ , no-η
    (var-refl _ _)               → inj₂ ((λ ()) , (λ ()))
    (defn-refl _ _ _)            → inj₂ ((λ ()) , (λ ()))
    (lower-cong _)               → inj₂ ((λ ()) , (λ ()))
    (app-cong _ _)               → inj₂ ((λ ()) , (λ ()))
    (fst-cong _)                 → inj₂ ((λ ()) , (λ ()))
    (snd-cong _)                 → inj₂ ((λ ()) , (λ ()))
    (prodrec-cong _ _ _)         → inj₂ ((λ ()) , (λ ()))
    (emptyrec-cong _ _)          → inj₂ ((λ ()) , (λ ()))
    (natrec-cong _ _ _ _)        → inj₂ ((λ ()) , (λ ()))
    (J-cong _ _ _ _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (K-cong _ _ _ _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    ([]-cong-cong _ _ _ _ _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for unitrec.

  inv-unitrec~ :
    Γ ⊢ unitrec p q B t₁ t₂ ~ u ↑ A →
    ∃₃ λ C u₁ u₂ →
    A PE.≡ B [ t₁ ]₀ ×
    u PE.≡ unitrec p q C u₁ u₂ ×
    (Γ »∙ Unitʷ ⊢ B [conv↑] C) ×
    Γ ⊢ t₁ ~ u₁ ↓ Unitʷ ×
    Γ ⊢ t₂ [conv↑] u₂ ∷ B [ starʷ ]₀ ×
    ¬ Unitʷ-η
  inv-unitrec~ (unitrec-cong B≡C t₁~u₁ t₂≡u₂ no-η) =
    _ , _ , _ , PE.refl , PE.refl , B≡C , t₁~u₁ , t₂≡u₂ , no-η

opaque

  -- Inversion for unitrec.

  inv-~unitrec :
    Γ ⊢ t ~ unitrec p q C u₁ u₂ ↑ A →
    ∃₃ λ B t₁ t₂ →
    A PE.≡ B [ t₁ ]₀ ×
    t PE.≡ unitrec p q B t₁ t₂ ×
    (Γ »∙ Unitʷ ⊢ B [conv↑] C) ×
    Γ ⊢ t₁ ~ u₁ ↓ Unitʷ ×
    Γ ⊢ t₂ [conv↑] u₂ ∷ B [ starʷ ]₀ ×
    ¬ Unitʷ-η
  inv-~unitrec (unitrec-cong B≡C t₁~u₁ t₂≡u₂ no-η) =
    _ , _ , _ , PE.refl , PE.refl , B≡C , t₁~u₁ , t₂≡u₂ , no-η

opaque

  -- Inversion for ℕ.

  inv-ℕ~ : ¬ Γ ⊢ ℕ ~ u ↑ A
  inv-ℕ~ ()

opaque

  -- Inversion for ℕ.

  inv-~ℕ : ¬ Γ ⊢ t ~ ℕ ↑ A
  inv-~ℕ ()

opaque

  -- Inversion for zero.

  inv-zero~ : ¬ Γ ⊢ zero ~ u ↑ A
  inv-zero~ ()

opaque

  -- Inversion for zero.

  inv-~zero : ¬ Γ ⊢ t ~ zero ↑ A
  inv-~zero ()

opaque

  -- Inversion for suc.

  inv-suc~ : ¬ Γ ⊢ suc t ~ u ↑ A
  inv-suc~ ()

opaque

  -- Inversion for suc.

  inv-~suc : ¬ Γ ⊢ t ~ suc u ↑ A
  inv-~suc ()

opaque

  -- A kind of inversion lemma for natrec.

  inv-~-natrec :
    Γ ⊢ t ~ u ↑ A →
    (∃₃ λ p q r → ∃₈ λ B C t₁ t₂ t₃ u₁ u₂ u₃ →
     A PE.≡ B [ t₃ ]₀ ×
     t PE.≡ natrec p q r B t₁ t₂ t₃ ×
     u PE.≡ natrec p q r C u₁ u₂ u₃ ×
     (Γ »∙ ℕ ⊢ B [conv↑] C) ×
     Γ ⊢ t₁ [conv↑] u₁ ∷ B [ zero ]₀ ×
     Γ »∙ ℕ »∙ B ⊢ t₂ [conv↑] u₂ ∷ B [ suc (var x1) ]↑² ×
     Γ ⊢ t₃ ~ u₃ ↓ ℕ) ⊎
    ¬ (∃₇ λ p q r B t₁ t₂ t₃ → t PE.≡ natrec p q r B t₁ t₂ t₃) ×
    ¬ (∃₇ λ p q r C u₁ u₂ u₃ → u PE.≡ natrec p q r C u₁ u₂ u₃)
  inv-~-natrec = λ where
    (natrec-cong B≡C t₁≡u₁ t₂≡u₂ t₃~u₃) →
      inj₁ $
      _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ ,
      PE.refl , PE.refl , PE.refl , B≡C , t₁≡u₁ , t₂≡u₂ , t₃~u₃
    (var-refl _ _)               → inj₂ ((λ ()) , (λ ()))
    (defn-refl _ _ _)            → inj₂ ((λ ()) , (λ ()))
    (lower-cong _)               → inj₂ ((λ ()) , (λ ()))
    (app-cong _ _)               → inj₂ ((λ ()) , (λ ()))
    (fst-cong _)                 → inj₂ ((λ ()) , (λ ()))
    (snd-cong _)                 → inj₂ ((λ ()) , (λ ()))
    (prodrec-cong _ _ _)         → inj₂ ((λ ()) , (λ ()))
    (emptyrec-cong _ _)          → inj₂ ((λ ()) , (λ ()))
    (unitrec-cong _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (J-cong _ _ _ _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (K-cong _ _ _ _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    ([]-cong-cong _ _ _ _ _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for natrec.

  inv-natrec~ :
    Γ ⊢ natrec p q r B t₁ t₂ t₃ ~ u ↑ A →
    ∃₄ λ C u₁ u₂ u₃ →
    A PE.≡ B [ t₃ ]₀ ×
    u PE.≡ natrec p q r C u₁ u₂ u₃ ×
    (Γ »∙ ℕ ⊢ B [conv↑] C) ×
    Γ ⊢ t₁ [conv↑] u₁ ∷ B [ zero ]₀ ×
    Γ »∙ ℕ »∙ B ⊢ t₂ [conv↑] u₂ ∷ B [ suc (var x1) ]↑² ×
    Γ ⊢ t₃ ~ u₃ ↓ ℕ
  inv-natrec~ (natrec-cong B≡C t₁≡u₁ t₂≡u₂ t₃~u₃) =
    _ , _ , _ , _ , PE.refl , PE.refl , B≡C , t₁≡u₁ , t₂≡u₂ , t₃~u₃

opaque

  -- Inversion for natrec.

  inv-~natrec :
    Γ ⊢ t ~ natrec p q r C u₁ u₂ u₃ ↑ A →
    ∃₄ λ B t₁ t₂ t₃ →
    A PE.≡ B [ t₃ ]₀ ×
    t PE.≡ natrec p q r B t₁ t₂ t₃ ×
    (Γ »∙ ℕ ⊢ B [conv↑] C) ×
    Γ ⊢ t₁ [conv↑] u₁ ∷ B [ zero ]₀ ×
    Γ »∙ ℕ »∙ B ⊢ t₂ [conv↑] u₂ ∷ B [ suc (var x1) ]↑² ×
    Γ ⊢ t₃ ~ u₃ ↓ ℕ
  inv-~natrec (natrec-cong B≡C t₁≡u₁ t₂≡u₂ t₃~u₃) =
    _ , _ , _ , _ , PE.refl , PE.refl , B≡C , t₁≡u₁ , t₂≡u₂ , t₃~u₃

opaque

  -- Inversion for Id.

  inv-Id~ : ¬ Γ ⊢ Id B t₁ t₂ ~ u ↑ A
  inv-Id~ ()

opaque

  -- Inversion for Id.

  inv-~Id : ¬ Γ ⊢ t ~ Id C u₁ u₂ ↑ A
  inv-~Id ()

opaque

  -- Inversion for rfl.

  inv-rfl~ : ¬ Γ ⊢ rfl ~ u ↑ A
  inv-rfl~ ()

opaque

  -- Inversion for rfl.

  inv-~rfl : ¬ Γ ⊢ t ~ rfl ↑ A
  inv-~rfl ()

opaque

  -- A kind of inversion lemma for J.

  inv-~-J :
    Γ ⊢ t ~ u ↑ A →
    (∃₇ λ p q B₁ B₂ C₁ C₂ D → ∃₈ λ t₁ t₂ t₃ t₄ u₁ u₂ u₃ u₄ →
     A PE.≡ B₂ [ t₃ , t₄ ]₁₀ ×
     t PE.≡ J p q B₁ t₁ B₂ t₂ t₃ t₄ ×
     u PE.≡ J p q C₁ u₁ C₂ u₂ u₃ u₄ ×
     (Γ ⊢ B₁ [conv↑] C₁) ×
     Γ ⊢ t₁ [conv↑] u₁ ∷ B₁ ×
     (Γ »∙ B₁ »∙ Id (wk1 B₁) (wk1 t₁) (var x0) ⊢ B₂ [conv↑] C₂) ×
     Γ ⊢ t₂ [conv↑] u₂ ∷ B₂ [ t₁ , rfl ]₁₀ ×
     Γ ⊢ t₃ [conv↑] u₃ ∷ B₁ ×
     Γ ⊢ t₄ ~ u₄ ↓ D ×
     Γ ⊢ D ≡ Id B₁ t₁ t₃) ⊎
    ¬ (∃₈ λ p q B₁ B₂ t₁ t₂ t₃ t₄ → t PE.≡ J p q B₁ t₁ B₂ t₂ t₃ t₄) ×
    ¬ (∃₈ λ p q C₁ C₂ u₁ u₂ u₃ u₄ → u PE.≡ J p q C₁ u₁ C₂ u₂ u₃ u₄)
  inv-~-J = λ where
    (J-cong B₁≡C₁ t₁≡u₁ B₂≡C₂ t₂≡u₂ t₃≡u₃ t₄~u₄ D≡Id) →
      inj₁ $
      _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ ,
      PE.refl , PE.refl , PE.refl ,
      B₁≡C₁ , t₁≡u₁ , B₂≡C₂ , t₂≡u₂ , t₃≡u₃ , t₄~u₄ , D≡Id
    (var-refl _ _)               → inj₂ ((λ ()) , (λ ()))
    (defn-refl _ _ _)            → inj₂ ((λ ()) , (λ ()))
    (lower-cong _)               → inj₂ ((λ ()) , (λ ()))
    (app-cong _ _)               → inj₂ ((λ ()) , (λ ()))
    (fst-cong _)                 → inj₂ ((λ ()) , (λ ()))
    (snd-cong _)                 → inj₂ ((λ ()) , (λ ()))
    (prodrec-cong _ _ _)         → inj₂ ((λ ()) , (λ ()))
    (emptyrec-cong _ _)          → inj₂ ((λ ()) , (λ ()))
    (unitrec-cong _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (natrec-cong _ _ _ _)        → inj₂ ((λ ()) , (λ ()))
    (K-cong _ _ _ _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    ([]-cong-cong _ _ _ _ _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for J.

  inv-J~ :
    Γ ⊢ J p q B₁ t₁ B₂ t₂ t₃ t₄ ~ u ↑ A →
    ∃₇ λ C₁ C₂ D u₁ u₂ u₃ u₄ →
    A PE.≡ B₂ [ t₃ , t₄ ]₁₀ ×
    u PE.≡ J p q C₁ u₁ C₂ u₂ u₃ u₄ ×
    (Γ ⊢ B₁ [conv↑] C₁) ×
    Γ ⊢ t₁ [conv↑] u₁ ∷ B₁ ×
    (Γ »∙ B₁ »∙ Id (wk1 B₁) (wk1 t₁) (var x0) ⊢ B₂ [conv↑] C₂) ×
    Γ ⊢ t₂ [conv↑] u₂ ∷ B₂ [ t₁ , rfl ]₁₀ ×
    Γ ⊢ t₃ [conv↑] u₃ ∷ B₁ ×
    Γ ⊢ t₄ ~ u₄ ↓ D ×
    Γ ⊢ D ≡ Id B₁ t₁ t₃
  inv-J~ (J-cong B₁≡C₁ t₁≡u₁ B₂≡C₂ t₂≡u₂ t₃≡u₃ t₄~u₄ D≡) =
    _ , _ , _ , _ , _ , _ , _ , PE.refl , PE.refl ,
    B₁≡C₁ , t₁≡u₁ , B₂≡C₂ , t₂≡u₂ , t₃≡u₃ , t₄~u₄ , D≡

opaque

  -- Inversion for J.

  inv-~J :
    Γ ⊢ t ~ J p q C₁ u₁ C₂ u₂ u₃ u₄ ↑ A →
    ∃₇ λ B₁ B₂ D t₁ t₂ t₃ t₄ →
    A PE.≡ B₂ [ t₃ , t₄ ]₁₀ ×
    t PE.≡ J p q B₁ t₁ B₂ t₂ t₃ t₄ ×
    (Γ ⊢ B₁ [conv↑] C₁) ×
    Γ ⊢ t₁ [conv↑] u₁ ∷ B₁ ×
    (Γ »∙ B₁ »∙ Id (wk1 B₁) (wk1 t₁) (var x0) ⊢ B₂ [conv↑] C₂) ×
    Γ ⊢ t₂ [conv↑] u₂ ∷ B₂ [ t₁ , rfl ]₁₀ ×
    Γ ⊢ t₃ [conv↑] u₃ ∷ B₁ ×
    Γ ⊢ t₄ ~ u₄ ↓ D ×
    Γ ⊢ D ≡ Id B₁ t₁ t₃
  inv-~J (J-cong B₁≡C₁ t₁≡u₁ B₂≡C₂ t₂≡u₂ t₃≡u₃ t₄~u₄ D≡) =
    _ , _ , _ , _ , _ , _ , _ , PE.refl , PE.refl ,
    B₁≡C₁ , t₁≡u₁ , B₂≡C₂ , t₂≡u₂ , t₃≡u₃ , t₄~u₄ , D≡

opaque

  -- A kind of inversion lemma for K.

  inv-~-K :
    Γ ⊢ t ~ u ↑ A →
    (∃₆ λ p B₁ B₂ C₁ C₂ D → ∃₆ λ t₁ t₂ t₃ u₁ u₂ u₃ →
     A PE.≡ B₂ [ t₃ ]₀ ×
     t PE.≡ K p B₁ t₁ B₂ t₂ t₃ ×
     u PE.≡ K p C₁ u₁ C₂ u₂ u₃ ×
     (Γ ⊢ B₁ [conv↑] C₁) ×
     Γ ⊢ t₁ [conv↑] u₁ ∷ B₁ ×
     (Γ »∙ Id B₁ t₁ t₁ ⊢ B₂ [conv↑] C₂) ×
     Γ ⊢ t₂ [conv↑] u₂ ∷ B₂ [ rfl ]₀ ×
     Γ ⊢ t₃ ~ u₃ ↓ D ×
     Γ ⊢ D ≡ Id B₁ t₁ t₁ ×
     K-allowed) ⊎
    ¬ (∃₆ λ p B₁ B₂ t₁ t₂ t₃ → t PE.≡ K p B₁ t₁ B₂ t₂ t₃) ×
    ¬ (∃₆ λ p C₁ C₂ u₁ u₂ u₃ → u PE.≡ K p C₁ u₁ C₂ u₂ u₃)
  inv-~-K = λ where
    (K-cong B₁≡C₁ t₁≡u₁ B₂≡C₂ t₂≡u₂ t₃~u₃ D≡Id ok) →
      inj₁ $
      _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ ,
      PE.refl , PE.refl , PE.refl ,
      B₁≡C₁ , t₁≡u₁ , B₂≡C₂ , t₂≡u₂ , t₃~u₃ , D≡Id , ok
    (var-refl _ _)               → inj₂ ((λ ()) , (λ ()))
    (defn-refl _ _ _)            → inj₂ ((λ ()) , (λ ()))
    (lower-cong _)               → inj₂ ((λ ()) , (λ ()))
    (app-cong _ _)               → inj₂ ((λ ()) , (λ ()))
    (fst-cong _)                 → inj₂ ((λ ()) , (λ ()))
    (snd-cong _)                 → inj₂ ((λ ()) , (λ ()))
    (prodrec-cong _ _ _)         → inj₂ ((λ ()) , (λ ()))
    (emptyrec-cong _ _)          → inj₂ ((λ ()) , (λ ()))
    (unitrec-cong _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (natrec-cong _ _ _ _)        → inj₂ ((λ ()) , (λ ()))
    (J-cong _ _ _ _ _ _ _)       → inj₂ ((λ ()) , (λ ()))
    ([]-cong-cong _ _ _ _ _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for K.

  inv-K~ :
    Γ ⊢ K p B₁ t₁ B₂ t₂ t₃ ~ u ↑ A →
    ∃₆ λ C₁ C₂ D u₁ u₂ u₃ →
    A PE.≡ B₂ [ t₃ ]₀ ×
    u PE.≡ K p C₁ u₁ C₂ u₂ u₃ ×
    (Γ ⊢ B₁ [conv↑] C₁) ×
    Γ ⊢ t₁ [conv↑] u₁ ∷ B₁ ×
    (Γ »∙ Id B₁ t₁ t₁ ⊢ B₂ [conv↑] C₂) ×
    Γ ⊢ t₂ [conv↑] u₂ ∷ B₂ [ rfl ]₀ ×
    Γ ⊢ t₃ ~ u₃ ↓ D ×
    Γ ⊢ D ≡ Id B₁ t₁ t₁ ×
    K-allowed
  inv-K~ (K-cong B₁≡C₁ t₁≡u₁ B₂≡C₂ t₂≡u₂ t₃~u₃ D≡ ok) =
    _ , _ , _ , _ , _ , _ , PE.refl , PE.refl ,
    B₁≡C₁ , t₁≡u₁ , B₂≡C₂ , t₂≡u₂ , t₃~u₃ , D≡ , ok

opaque

  -- Inversion for K.

  inv-~K :
    Γ ⊢ t ~ K p C₁ u₁ C₂ u₂ u₃ ↑ A →
    ∃₆ λ B₁ B₂ D t₁ t₂ t₃ →
    A PE.≡ B₂ [ t₃ ]₀ ×
    t PE.≡ K p B₁ t₁ B₂ t₂ t₃ ×
    (Γ ⊢ B₁ [conv↑] C₁) ×
    Γ ⊢ t₁ [conv↑] u₁ ∷ B₁ ×
    (Γ »∙ Id B₁ t₁ t₁ ⊢ B₂ [conv↑] C₂) ×
    Γ ⊢ t₂ [conv↑] u₂ ∷ B₂ [ rfl ]₀ ×
    Γ ⊢ t₃ ~ u₃ ↓ D ×
    Γ ⊢ D ≡ Id B₁ t₁ t₁ ×
    K-allowed
  inv-~K (K-cong B₁≡C₁ t₁≡u₁ B₂≡C₂ t₂≡u₂ t₃~u₃ D≡ ok) =
    _ , _ , _ , _ , _ , _ , PE.refl , PE.refl ,
    B₁≡C₁ , t₁≡u₁ , B₂≡C₂ , t₂≡u₂ , t₃~u₃ , D≡ , ok

opaque

  -- A kind of inversion lemma for []-cong.

  inv-~-[]-cong :
    Γ ⊢ t ~ u ↑ A →
    (∃₄ λ s B C D → ∃₈ λ t₁ t₂ t₃ t₄ u₁ u₂ u₃ u₄ →
     let open Erased s in
     A PE.≡ Id (Erased t₁ B) [ t₂ ] ([ t₃ ]) ×
     t PE.≡ []-cong s t₁ B t₂ t₃ t₄ ×
     u PE.≡ []-cong s u₁ C u₂ u₃ u₄ ×
     Γ ⊢ t₁ [conv↑] u₁ ∷Level ×
     (Γ ⊢ B [conv↑] C) ×
     Γ ⊢ t₂ [conv↑] u₂ ∷ B ×
     Γ ⊢ t₃ [conv↑] u₃ ∷ B ×
     Γ ⊢ t₄ ~ u₄ ↓ D ×
     Γ ⊢ D ≡ Id B t₂ t₃ ×
     []-cong-allowed s) ⊎
    ¬ (∃₆ λ s B t₁ t₂ t₃ t₄ → t PE.≡ []-cong s t₁ B t₂ t₃ t₄) ×
    ¬ (∃₆ λ s C u₁ u₂ u₃ u₄ → u PE.≡ []-cong s u₁ C u₂ u₃ u₄)
  inv-~-[]-cong = λ where
    ([]-cong-cong t₁≡u₁ B≡C t₂≡u₂ t₃≡u₃ t₄~u₄ D≡Id ok) →
      inj₁ $
      _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ ,
      PE.refl , PE.refl , PE.refl ,
      t₁≡u₁ , B≡C , t₂≡u₂ , t₃≡u₃ , t₄~u₄ , D≡Id , ok
    (var-refl _ _)         → inj₂ ((λ ()) , (λ ()))
    (defn-refl _ _ _)      → inj₂ ((λ ()) , (λ ()))
    (lower-cong _)         → inj₂ ((λ ()) , (λ ()))
    (app-cong _ _)         → inj₂ ((λ ()) , (λ ()))
    (fst-cong _)           → inj₂ ((λ ()) , (λ ()))
    (snd-cong _)           → inj₂ ((λ ()) , (λ ()))
    (prodrec-cong _ _ _)   → inj₂ ((λ ()) , (λ ()))
    (emptyrec-cong _ _)    → inj₂ ((λ ()) , (λ ()))
    (unitrec-cong _ _ _ _)   → inj₂ ((λ ()) , (λ ()))
    (natrec-cong _ _ _ _)  → inj₂ ((λ ()) , (λ ()))
    (J-cong _ _ _ _ _ _ _) → inj₂ ((λ ()) , (λ ()))
    (K-cong _ _ _ _ _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for []-cong.

  inv-[]-cong~ :
    let open Erased s in
    Γ ⊢ []-cong s l B t₁ t₂ t₃ ~ u ↑ A →
    ∃₆ λ C D l′ u₁ u₂ u₃ →
    A PE.≡ Id (Erased l B) [ t₁ ] ([ t₂ ]) ×
    u PE.≡ []-cong s l′ C u₁ u₂ u₃ ×
    Γ ⊢ l [conv↑] l′ ∷Level ×
    (Γ ⊢ B [conv↑] C) ×
    Γ ⊢ t₁ [conv↑] u₁ ∷ B ×
    Γ ⊢ t₂ [conv↑] u₂ ∷ B ×
    Γ ⊢ t₃ ~ u₃ ↓ D ×
    Γ ⊢ D ≡ Id B t₁ t₂ ×
    []-cong-allowed s
  inv-[]-cong~ ([]-cong-cong l≡l′ B≡C t₁≡u₁ t₂≡u₂ t₃~u₃ D≡ ok) =
    _ , _ , _ , _ , _ , _ , PE.refl , PE.refl ,
    l≡l′ , B≡C , t₁≡u₁ , t₂≡u₂ , t₃~u₃ , D≡ , ok

opaque

  -- Inversion for []-cong.

  inv-~[]-cong :
    let open Erased s in
    Γ ⊢ t ~ []-cong s l C u₁ u₂ u₃ ↑ A →
    ∃₆ λ B D l′ t₁ t₂ t₃ →
    A PE.≡ Id (Erased l′ B) [ t₁ ] ([ t₂ ]) ×
    t PE.≡ []-cong s l′ B t₁ t₂ t₃ ×
    Γ ⊢ l′ [conv↑] l ∷Level ×
    (Γ ⊢ B [conv↑] C) ×
    Γ ⊢ t₁ [conv↑] u₁ ∷ B ×
    Γ ⊢ t₂ [conv↑] u₂ ∷ B ×
    Γ ⊢ t₃ ~ u₃ ↓ D ×
    Γ ⊢ D ≡ Id B t₁ t₂ ×
    []-cong-allowed s
  inv-~[]-cong ([]-cong-cong l′≡l B≡C t₁≡u₁ t₂≡u₂ t₃~u₃ D≡ ok) =
    _ , _ , _ , _ , _ , _ , PE.refl , PE.refl ,
    l′≡l , B≡C , t₁≡u₁ , t₂≡u₂ , t₃~u₃ , D≡ , ok

------------------------------------------------------------------------
-- Inversion and similar lemmas for _⊢_[conv↓]_

opaque

  -- A kind of inversion lemma for neutral terms.

  inv-[conv↓]-ne′ :
    Γ ⊢ A [conv↓] B →
    (∃ λ l → Γ ⊢ A ~ B ↓ U l) ⊎
    ¬ Neutral V (Γ .defs) A × ¬ Neutral V (Γ .defs) B
  inv-[conv↓]-ne′ = λ where
    (ne A~B)         → inj₁ (_ , A~B)
    (U-cong _)       → inj₂ (¬-Neutral-U     , ¬-Neutral-U)
    (Lift-cong _ _)  → inj₂ (¬-Neutral-Lift , ¬-Neutral-Lift)
    (ΠΣ-cong _ _ _)  → inj₂ (¬-Neutral-ΠΣ    , ¬-Neutral-ΠΣ)
    (Empty-refl _)   → inj₂ (¬-Neutral-Empty , ¬-Neutral-Empty)
    (Unit-refl _ _)  → inj₂ (¬-Neutral-Unit  , ¬-Neutral-Unit)
    (ℕ-refl _)       → inj₂ (¬-Neutral-ℕ     , ¬-Neutral-ℕ)
    (Level-refl _ _) → inj₂ (¬-Neutral-Level , ¬-Neutral-Level)
    (Id-cong _ _ _)  → inj₂ (¬-Neutral-Id    , ¬-Neutral-Id)

opaque

  -- Inversion for neutral terms.

  inv-[conv↓]-ne :
    Neutral V (Γ .defs) A →
    Γ ⊢ A [conv↓] B →
    ∃ λ l → Γ ⊢ A ~ B ↓ U l
  inv-[conv↓]-ne A-ne A≡B = case inv-[conv↓]-ne′ A≡B of λ where
    (inj₁ A~B)         → A~B
    (inj₂ (¬A-ne , _)) → ⊥-elim (¬A-ne A-ne)

opaque

  -- A kind of inversion lemma for U.

  inv-[conv↓]-U′ :
    Γ ⊢ A [conv↓] B →
    (∃₂ λ l₁ l₂ → A PE.≡ U l₁ × B PE.≡ U l₂ ×
     Γ ⊢ l₁ [conv↑] l₂ ∷Level) ⊎
    ¬ (∃ λ l → A PE.≡ U l) × ¬ (∃ λ l → B PE.≡ U l)
  inv-[conv↓]-U′ = λ where
    (U-cong l₁≡l₂) → inj₁ (_ , _ , PE.refl , PE.refl , l₁≡l₂)
    (ne A~B) →
      inj₂ $
      case ne~↓ A~B of λ
        (_ , A-ne , B-ne) →
        (λ { (_ , PE.refl) → ¬-Neutral-U (ne⁻ A-ne) })
      , (λ { (_ , PE.refl) → ¬-Neutral-U (ne⁻ B-ne) })
    (Lift-cong _ _)  → inj₂ ((λ ()) , (λ ()))
    (ΠΣ-cong _ _ _)  → inj₂ ((λ ()) , (λ ()))
    (Empty-refl _)   → inj₂ ((λ ()) , (λ ()))
    (Unit-refl _ _)  → inj₂ ((λ ()) , (λ ()))
    (ℕ-refl _)       → inj₂ ((λ ()) , (λ ()))
    (Level-refl _ _) → inj₂ ((λ ()) , (λ ()))
    (Id-cong _ _ _)  → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for U.

  inv-[conv↓]-U :
    Γ ⊢ U l₁ [conv↓] A →
    ∃ λ l₂ → A PE.≡ U l₂ × Γ ⊢ l₁ [conv↑] l₂ ∷Level
  inv-[conv↓]-U U≡A = case inv-[conv↓]-U′ U≡A of λ where
    (inj₁ (_ , _ , PE.refl , A≡U , l₁≡l₂)) → _ , A≡U , l₁≡l₂
    (inj₂ (U≢U , _))           → ⊥-elim (U≢U (_ , PE.refl))

opaque

  -- A kind of inversion lemma for Lift.

  inv-[conv↓]-Lift′ :
    Γ ⊢ A [conv↓] B →
    (∃₄ λ k₁ k₂ A₁ B₁ →
     A PE.≡ Lift k₁ A₁ ×
     B PE.≡ Lift k₂ B₁ ×
     Γ ⊢ k₁ [conv↑] k₂ ∷Level ×
     (Γ ⊢ A₁ [conv↑] B₁)) ⊎
    ¬ (∃₂ λ k X → A PE.≡ Lift k X) ×
    ¬ (∃₂ λ k X → B PE.≡ Lift k X)
  inv-[conv↓]-Lift′ = λ where
    (Lift-cong l₁≡l₂ F≡H) →
      inj₁ (_ , _ , _ , _ , PE.refl , PE.refl , l₁≡l₂ , F≡H)
    (ne A~B) →
      inj₂ $
      case ne~↓ A~B of λ
        (_ , A-ne , B-ne) →
        (λ { (_ , _ , PE.refl) → ¬-Neutral-Lift (ne⁻ A-ne) })
      , (λ { (_ , _ , PE.refl) → ¬-Neutral-Lift (ne⁻ B-ne) })
    (U-cong _)              → inj₂ ((λ ()) , (λ ()))
    (ΠΣ-cong A₁≡B₁ A₂≡B₂ _) → inj₂ ((λ ()) , (λ ()))
    (Empty-refl _)          → inj₂ ((λ ()) , (λ ()))
    (Unit-refl _ _)         → inj₂ ((λ ()) , (λ ()))
    (ℕ-refl _)              → inj₂ ((λ ()) , (λ ()))
    (Level-refl _ _)        → inj₂ ((λ ()) , (λ ()))
    (Id-cong _ _ _)         → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for Lift.

  inv-[conv↓]-Lift :
    Γ ⊢ Lift l₁ B [conv↓] A →
    ∃₂ λ l₂ C → A PE.≡ Lift l₂ C ×
    Γ ⊢ l₁ [conv↑] l₂ ∷Level × Γ ⊢ B [conv↑] C
  inv-[conv↓]-Lift Lift≡A = case inv-[conv↓]-Lift′ Lift≡A of λ where
    (inj₁ (_ , _ , _ , _ , PE.refl , PE.refl , x , y)) → _ , _ , PE.refl , x , y
    (inj₂ (no₁ , no₂)) → ⊥-elim (no₁ (_ , _ , PE.refl))

opaque

  -- A kind of inversion lemma for Π and Σ.

  inv-[conv↓]-ΠΣ′ :
    Γ ⊢ A [conv↓] B →
    (∃₇ λ b p q A₁ A₂ B₁ B₂ →
     A PE.≡ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ A₂ ×
     B PE.≡ ΠΣ⟨ b ⟩ p , q ▷ B₁ ▹ B₂ ×
     Γ ⊢ A₁ [conv↑] B₁ × Γ »∙ A₁ ⊢ A₂ [conv↑] B₂) ⊎
    ¬ (∃₅ λ b p q A₁ A₂ → A PE.≡ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ A₂) ×
    ¬ (∃₅ λ b p q B₁ B₂ → B PE.≡ ΠΣ⟨ b ⟩ p , q ▷ B₁ ▹ B₂)
  inv-[conv↓]-ΠΣ′ = λ where
    (ΠΣ-cong A₁≡B₁ A₂≡B₂ _) →
      inj₁ $
      _ , _ , _ , _ , _ , _ , _ , PE.refl , PE.refl , A₁≡B₁ , A₂≡B₂
    (ne A~B) →
      inj₂ $
      case ne~↓ A~B of λ
        (_ , A-ne , B-ne) →
        (λ { (_ , _ , _ , _ , _ , PE.refl) → ¬-Neutral-ΠΣ (ne⁻ A-ne) })
      , (λ { (_ , _ , _ , _ , _ , PE.refl) → ¬-Neutral-ΠΣ (ne⁻ B-ne) })
    (U-cong _)       → inj₂ ((λ ()) , (λ ()))
    (Lift-cong _ _)  → inj₂ ((λ ()) , (λ ()))
    (Empty-refl _)   → inj₂ ((λ ()) , (λ ()))
    (Unit-refl _ _)  → inj₂ ((λ ()) , (λ ()))
    (ℕ-refl _)       → inj₂ ((λ ()) , (λ ()))
    (Level-refl _ _) → inj₂ ((λ ()) , (λ ()))
    (Id-cong _ _ _)  → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for Π and Σ.

  inv-[conv↓]-ΠΣ :
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ A₂ [conv↓] B →
    ∃₂ λ B₁ B₂ →
    B PE.≡ ΠΣ⟨ b ⟩ p , q ▷ B₁ ▹ B₂ ×
    Γ ⊢ A₁ [conv↑] B₁ × Γ »∙ A₁ ⊢ A₂ [conv↑] B₂
  inv-[conv↓]-ΠΣ ΠΣ≡A = case inv-[conv↓]-ΠΣ′ ΠΣ≡A of λ where
    (inj₁ (_ , _ , _ , _ , _ , _ , _ , PE.refl , rest)) →
      _ , _ , rest
    (inj₂ (ΠΣ≢ΠΣ , _)) →
      ⊥-elim (ΠΣ≢ΠΣ (_ , _ , _ , _ , _ , PE.refl))

opaque

  -- A kind of inversion lemma for Empty.

  inv-[conv↓]-Empty′ :
    Γ ⊢ A [conv↓] B →
    A PE.≡ Empty × B PE.≡ Empty ⊎ A PE.≢ Empty × B PE.≢ Empty
  inv-[conv↓]-Empty′ = λ where
    (Empty-refl _) → inj₁ (PE.refl , PE.refl)
    (ne A~B) →
      inj₂ $
      case ne~↓ A~B of λ
        (_ , A-ne , B-ne) →
        (λ { PE.refl → ¬-Neutral-Empty (ne⁻ A-ne) })
      , (λ { PE.refl → ¬-Neutral-Empty (ne⁻ B-ne) })
    (U-cong _)       → inj₂ ((λ ()) , (λ ()))
    (Lift-cong _ _)  → inj₂ ((λ ()) , (λ ()))
    (ΠΣ-cong _ _ _)  → inj₂ ((λ ()) , (λ ()))
    (Unit-refl _ _)  → inj₂ ((λ ()) , (λ ()))
    (ℕ-refl _)       → inj₂ ((λ ()) , (λ ()))
    (Level-refl _ _) → inj₂ ((λ ()) , (λ ()))
    (Id-cong _ _ _)  → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for Empty.

  inv-[conv↓]-Empty :
    Γ ⊢ Empty [conv↓] A →
    A PE.≡ Empty
  inv-[conv↓]-Empty Empty≡A = case inv-[conv↓]-Empty′ Empty≡A of λ where
    (inj₁ (_ , A≡Empty))     → A≡Empty
    (inj₂ (Empty≢Empty , _)) → ⊥-elim (Empty≢Empty PE.refl)

opaque

  -- A kind of inversion lemma for Unit.

  inv-[conv↓]-Unit′ :
    Γ ⊢ A [conv↓] B →
    (∃ λ s → A PE.≡ Unit s × B PE.≡ Unit s) ⊎
    ¬ (∃ λ s → A PE.≡ Unit s) × ¬ (∃ λ s → B PE.≡ Unit s)
  inv-[conv↓]-Unit′ = λ where
    (Unit-refl _ _) → inj₁ (_ , PE.refl , PE.refl)
    (ne A~B) →
      inj₂ $
      case ne~↓ A~B of λ
        (_ , A-ne , B-ne) →
        (λ { (_ , PE.refl) → ¬-Neutral-Unit (ne⁻ A-ne) })
      , (λ { (_ , PE.refl) → ¬-Neutral-Unit (ne⁻ B-ne) })
    (U-cong _)       → inj₂ ((λ ()) , (λ ()))
    (Lift-cong _ _)  → inj₂ ((λ ()) , (λ ()))
    (ΠΣ-cong _ _ _)  → inj₂ ((λ ()) , (λ ()))
    (Empty-refl _)   → inj₂ ((λ ()) , (λ ()))
    (ℕ-refl _)       → inj₂ ((λ ()) , (λ ()))
    (Level-refl _ _) → inj₂ ((λ ()) , (λ ()))
    (Id-cong _ _ _)  → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for Unit.

  inv-[conv↓]-Unit :
    Γ ⊢ Unit s [conv↓] A →
    A PE.≡ Unit s
  inv-[conv↓]-Unit Unit≡A = case inv-[conv↓]-Unit′ Unit≡A of λ where
    (inj₁ (_ , PE.refl , A≡Unit)) → A≡Unit
    (inj₂ (Unit≢Unit , _))            →
      ⊥-elim (Unit≢Unit (_ , PE.refl))

opaque

  -- A kind of inversion lemma for Level.

  inv-[conv↓]-Level′ :
    Γ ⊢ A [conv↓] B →
    A PE.≡ Level × B PE.≡ Level ⊎ A PE.≢ Level × B PE.≢ Level
  inv-[conv↓]-Level′ = λ where
    (Level-refl _ _) → inj₁ (PE.refl , PE.refl)
    (ne A~B) →
      inj₂ $
      case ne~↓ A~B of λ
        (_ , A-ne , B-ne) →
        (λ { PE.refl → ¬-Neutral-Level (ne⁻ A-ne) })
      , (λ { PE.refl → ¬-Neutral-Level (ne⁻ B-ne) })
    (U-cong _)      → inj₂ ((λ ()) , (λ ()))
    (Lift-cong _ _) → inj₂ ((λ ()) , (λ ()))
    (ΠΣ-cong _ _ _) → inj₂ ((λ ()) , (λ ()))
    (Empty-refl _)  → inj₂ ((λ ()) , (λ ()))
    (Unit-refl _ _) → inj₂ ((λ ()) , (λ ()))
    (ℕ-refl _)      → inj₂ ((λ ()) , (λ ()))
    (Id-cong _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for Level.

  inv-[conv↓]-Level :
    Γ ⊢ Level [conv↓] A →
    A PE.≡ Level
  inv-[conv↓]-Level Level≡A = case inv-[conv↓]-Level′ Level≡A of λ where
    (inj₁ (_ , A≡Level)) → A≡Level
    (inj₂ (Level≢Level , _)) → ⊥-elim (Level≢Level PE.refl)

opaque

  -- A kind of inversion lemma for ℕ.

  inv-[conv↓]-ℕ′ :
    Γ ⊢ A [conv↓] B →
    A PE.≡ ℕ × B PE.≡ ℕ ⊎ A PE.≢ ℕ × B PE.≢ ℕ
  inv-[conv↓]-ℕ′ = λ where
    (ℕ-refl _) → inj₁ (PE.refl , PE.refl)
    (ne A~B) →
      inj₂ $
      case ne~↓ A~B of λ
        (_ , A-ne , B-ne) →
        (λ { PE.refl → ¬-Neutral-ℕ (ne⁻ A-ne) })
      , (λ { PE.refl → ¬-Neutral-ℕ (ne⁻ B-ne) })
    (U-cong _)       → inj₂ ((λ ()) , (λ ()))
    (Lift-cong _ _)  → inj₂ ((λ ()) , (λ ()))
    (ΠΣ-cong _ _ _)  → inj₂ ((λ ()) , (λ ()))
    (Empty-refl _)   → inj₂ ((λ ()) , (λ ()))
    (Unit-refl _ _)  → inj₂ ((λ ()) , (λ ()))
    (Level-refl _ _) → inj₂ ((λ ()) , (λ ()))
    (Id-cong _ _ _)  → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for ℕ.

  inv-[conv↓]-ℕ :
    Γ ⊢ ℕ [conv↓] A →
    A PE.≡ ℕ
  inv-[conv↓]-ℕ ℕ≡A = case inv-[conv↓]-ℕ′ ℕ≡A of λ where
    (inj₁ (_ , A≡ℕ)) → A≡ℕ
    (inj₂ (ℕ≢ℕ , _)) → ⊥-elim (ℕ≢ℕ PE.refl)

opaque

  -- A kind of inversion lemma for Id.

  inv-[conv↓]-Id′ :
    Γ ⊢ A [conv↓] B →
    (∃₆ λ A′ t₁ t₂ B′ u₁ u₂ →
     A PE.≡ Id A′ t₁ t₂ ×
     B PE.≡ Id B′ u₁ u₂ ×
    (Γ ⊢ A′ [conv↑] B′) ×
    Γ ⊢ t₁ [conv↑] u₁ ∷ A′ ×
    Γ ⊢ t₂ [conv↑] u₂ ∷ A′) ⊎
    ¬ (∃₃ λ A′ t₁ t₂ → A PE.≡ Id A′ t₁ t₂) ×
    ¬ (∃₃ λ B′ u₁ u₂ → B PE.≡ Id B′ u₁ u₂)
  inv-[conv↓]-Id′ = λ where
    (Id-cong A′≡B′ t₁≡u₁ t₂≡u₂) →
      inj₁ $
      _ , _ , _ , _ , _ , _ , PE.refl , PE.refl , A′≡B′ , t₁≡u₁ , t₂≡u₂
    (ne A~B) →
      inj₂ $
      case ne~↓ A~B of λ
        (_ , A-ne , B-ne) →
        (λ { (_ , _ , _ , PE.refl) → ¬-Neutral-Id (ne⁻ A-ne) })
      , (λ { (_ , _ , _ , PE.refl) → ¬-Neutral-Id (ne⁻ B-ne) })
    (U-cong _)       → inj₂ ((λ ()) , (λ ()))
    (Lift-cong _ _)  → inj₂ ((λ ()) , (λ ()))
    (ΠΣ-cong _ _ _)  → inj₂ ((λ ()) , (λ ()))
    (Empty-refl _)   → inj₂ ((λ ()) , (λ ()))
    (Unit-refl _ _)  → inj₂ ((λ ()) , (λ ()))
    (ℕ-refl _)       → inj₂ ((λ ()) , (λ ()))
    (Level-refl _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for Id.

  inv-[conv↓]-Id :
    Γ ⊢ Id A t₁ t₂ [conv↓] B →
    ∃₃ λ B′ u₁ u₂ →
    B PE.≡ Id B′ u₁ u₂ ×
    (Γ ⊢ A [conv↑] B′) ×
    Γ ⊢ t₁ [conv↑] u₁ ∷ A ×
    Γ ⊢ t₂ [conv↑] u₂ ∷ A
  inv-[conv↓]-Id Id≡A = case inv-[conv↓]-Id′ Id≡A of λ where
    (inj₁ (_ , _ , _ , _ , _ , _ , PE.refl , rest)) →
      _ , _ , _ , rest
    (inj₂ (Id≢Id , _)) →
      ⊥-elim (Id≢Id (_ , _ , _ , PE.refl))

------------------------------------------------------------------------
-- Inversion for _⊢_[conv↓]_∷_

opaque

  -- Inversion for neutral types.

  inv-[conv↓]∷-ne :
    Neutral V (Γ .defs) A →
    Γ ⊢ t [conv↓] u ∷ A →
    ∃ λ A → Γ ⊢ t ~ u ↓ A
  inv-[conv↓]∷-ne A-ne = λ where
    (ne-ins _ _ _ t~u)  → _ , t~u
    (univ _ _ _)        → ⊥-elim (¬-Neutral-U     A-ne)
    (Lift-η _ _ _ _ _)  → ⊥-elim (¬-Neutral-Lift  A-ne)
    (η-eq _ _ _ _ _)    → ⊥-elim (¬-Neutral-ΠΣ    A-ne)
    (Σ-η _ _ _ _ _ _)   → ⊥-elim (¬-Neutral-ΠΣ    A-ne)
    (Σʷ-ins _ _ _)      → ⊥-elim (¬-Neutral-ΠΣ    A-ne)
    (prod-cong _ _ _ _) → ⊥-elim (¬-Neutral-ΠΣ    A-ne)
    (Level-ins _)       → ⊥-elim (¬-Neutral-Level A-ne)
    (Empty-ins _)       → ⊥-elim (¬-Neutral-Empty A-ne)
    (Unitʷ-ins _ _)     → ⊥-elim (¬-Neutral-Unit  A-ne)
    (η-unit _ _ _ _ _)  → ⊥-elim (¬-Neutral-Unit  A-ne)
    (starʷ-refl _ _ _) → ⊥-elim (¬-Neutral-Unit  A-ne)
    (ℕ-ins _)           → ⊥-elim (¬-Neutral-ℕ     A-ne)
    (zero-refl _)       → ⊥-elim (¬-Neutral-ℕ     A-ne)
    (suc-cong _)        → ⊥-elim (¬-Neutral-ℕ     A-ne)
    (Id-ins _ _)        → ⊥-elim (¬-Neutral-Id    A-ne)
    (rfl-refl _)        → ⊥-elim (¬-Neutral-Id    A-ne)

opaque

  -- Inversion for U.

  inv-[conv↓]∷-U :
    Γ ⊢ A [conv↓] B ∷ U l →
    Γ ⊢ A [conv↓] B
  inv-[conv↓]∷-U (univ _ _ A≡B)    = A≡B
  inv-[conv↓]∷-U (ne-ins _ _ () _)

opaque

  -- Inversion for Lift.

  inv-[conv↓]∷-Lift :
    Γ ⊢ t [conv↓] u ∷ Lift l A →
    Γ ⊢ t ∷ Lift l A ×
    Γ ⊢ u ∷ Lift l A ×
    Whnf (Γ .defs) t ×
    Whnf (Γ .defs) u ×
    Γ ⊢ lower t [conv↑] lower u ∷ A
  inv-[conv↓]∷-Lift (Lift-η x x₁ x₂ x₃ x₄) = x , x₁ , x₂ , x₃ , x₄
  inv-[conv↓]∷-Lift (ne-ins _ _ () _)

opaque

  -- Inversion for Π.

  inv-[conv↓]∷-Π :
    Γ ⊢ t [conv↓] u ∷ Π p , q ▷ A ▹ B →
    Function⁺ (Γ .defs) t × Function⁺ (Γ .defs) u ×
    Γ »∙ A ⊢ wk1 t ∘⟨ p ⟩ var x0 [conv↑] wk1 u ∘⟨ p ⟩ var x0 ∷ B
  inv-[conv↓]∷-Π (η-eq _ _ t-fun u-fun t0≡u0) = t-fun , u-fun , t0≡u0
  inv-[conv↓]∷-Π (ne-ins _ _ () _)

opaque

  -- Inversion for Σˢ.

  inv-[conv↓]∷-Σˢ :
    Γ ⊢ t [conv↓] u ∷ Σˢ p , q ▷ A ▹ B →
    Product⁺ (Γ .defs) t × Product⁺ (Γ .defs) u ×
    Γ ⊢ fst p t [conv↑] fst p u ∷ A ×
    Γ ⊢ snd p t [conv↑] snd p u ∷ B [ fst p t ]₀
  inv-[conv↓]∷-Σˢ (Σ-η _ _ t-prod u-prod fst≡fst snd≡snd) =
    t-prod , u-prod , fst≡fst , snd≡snd
  inv-[conv↓]∷-Σˢ (ne-ins _ _ () _)

opaque

  -- Inversion for Σʷ.

  inv-[conv↓]∷-Σʷ :
    Γ ⊢ t [conv↓] u ∷ Σʷ p , q ▷ A ▹ B →
    (∃₄ λ p q A B → Γ ⊢ t ~ u ↓ Σʷ p , q ▷ A ▹ B) ⊎
    (∃₄ λ t₁ t₂ u₁ u₂ →
     t PE.≡ prodʷ p t₁ t₂ ×
     u PE.≡ prodʷ p u₁ u₂ ×
     Γ ⊢ t₁ [conv↑] u₁ ∷ A ×
     Γ ⊢ t₂ [conv↑] u₂ ∷ B [ t₁ ]₀)
  inv-[conv↓]∷-Σʷ (Σʷ-ins _ _ t~u) =
    inj₁ (_ , _ , _ , _ , t~u)
  inv-[conv↓]∷-Σʷ (prod-cong _ t₁≡u₁ t₂≡u₂ _) =
    inj₂ (_ , _ , _ , _ , PE.refl , PE.refl , t₁≡u₁ , t₂≡u₂)
  inv-[conv↓]∷-Σʷ (ne-ins _ _ () _)

opaque

  -- Inversion for Empty.

  inv-[conv↓]∷-Empty :
    Γ ⊢ t [conv↓] u ∷ Empty →
    Γ ⊢ t ~ u ↓ Empty
  inv-[conv↓]∷-Empty (Empty-ins t~u)   = t~u
  inv-[conv↓]∷-Empty (ne-ins _ _ () _)

opaque

  -- Inversion for Unitˢ.

  inv-[conv↓]∷-Unitˢ :
    Γ ⊢ t [conv↓] u ∷ Unitˢ →
    Whnf (Γ .defs) t × Whnf (Γ .defs) u
  inv-[conv↓]∷-Unitˢ (η-unit _ _ t-whnf u-whnf _) = t-whnf , u-whnf
  inv-[conv↓]∷-Unitˢ (ne-ins _ _ () _)

opaque

  -- Inversion for Unitʷ.

  inv-[conv↓]∷-Unitʷ :
    Γ ⊢ t [conv↓] u ∷ Unitʷ →
    ¬ Unitʷ-η ×
    (Γ ⊢ t ~ u ↓ Unitʷ ⊎
     t PE.≡ starʷ × u PE.≡ starʷ) ⊎
    Unitʷ-η × Whnf (Γ .defs) t × Whnf (Γ .defs) u
  inv-[conv↓]∷-Unitʷ (Unitʷ-ins no-η t~u) =
    inj₁ (no-η , inj₁ t~u)
  inv-[conv↓]∷-Unitʷ (starʷ-refl _ _ no-η) =
    inj₁ (no-η , inj₂ (PE.refl , PE.refl))
  inv-[conv↓]∷-Unitʷ (η-unit _ _ t-whnf u-whnf (inj₂ η)) =
    inj₂ (η , t-whnf , u-whnf)
  inv-[conv↓]∷-Unitʷ (η-unit _ _ _ _ (inj₁ ()))
  inv-[conv↓]∷-Unitʷ (ne-ins _ _ () _)

opaque

  -- Inversion for Unit.

  inv-[conv↓]∷-Unit :
    Γ ⊢ t [conv↓] u ∷ Unit s →
    Unit-with-η s × Whnf (Γ .defs) t × Whnf (Γ .defs) u ⊎
    ¬ Unit-with-η s ×
    (Γ ⊢ t ~ u ↓ Unit s ⊎
     t PE.≡ star s × u PE.≡ star s)
  inv-[conv↓]∷-Unit {s = 𝕤} t≡u =
    inj₁ (inj₁ PE.refl , inv-[conv↓]∷-Unitˢ t≡u)
  inv-[conv↓]∷-Unit {s = 𝕨} t≡u =
    case inv-[conv↓]∷-Unitʷ t≡u of λ where
      (inj₂ (η , t-whnf , u-whnf)) →
        inj₁ (inj₂ η , t-whnf , u-whnf)
      (inj₁ (no-η , rest)) →
        inj₂ ([ (λ ()) , no-η ] , rest)

opaque

  -- Inversion for Level.

  inv-[conv↓]∷-Level :
    Γ ⊢ t [conv↓] u ∷ Level →
    Γ ⊢ t [conv↓] u ∷Level
  inv-[conv↓]∷-Level (Level-ins t~u) = t~u
  inv-[conv↓]∷-Level (ne-ins _ _ () _)

-- A variant of _⊢_[conv↑]_∷ Level.

infix 4 _⊢_[conv↑]_∷Level′

record _⊢_[conv↑]_∷Level′ (Γ : Cons m n) (t u : Term n) : Set a where
  inductive
  no-eta-equality
  pattern
  constructor [↑]ˡ
  field
    tᵛ : Levelᵛ Γ
    uᵛ : Levelᵛ Γ
    t↑ : Γ ⊢ t ↑ᵛ tᵛ
    u↑ : Γ ⊢ u ↑ᵛ uᵛ
    t≡u : tᵛ ≡ᵛ uᵛ

opaque

  inv-[conv↑]∷-Level⇔ :
    Γ ⊢ t [conv↑] u ∷ Level ⇔ Γ ⊢ t [conv↑] u ∷Level′
  inv-[conv↑]∷-Level⇔ =
      (λ { ([↑]ₜ B t′ u′ (D , _) d d′ t<>u) →
        case whnfRed* D Levelₙ of λ {
          PE.refl →
        let [↓]ˡ v v′ t↓ u↓ t≡u = inv-[conv↓]∷-Level t<>u
        in [↑]ˡ v v′ ([↑]ᵛ d t↓) ([↑]ᵛ d′ u↓) t≡u }})
    , λ ([↑]ˡ v v′ ([↑]ᵛ d t↓) ([↑]ᵛ d′ u↓) t≡u) →
        let ok = inversion-Level-⊢
                   (wf-⊢≡∷ (subset*Term (d .proj₁)) .proj₁)
        in
        [↑]ₜ _ _ _
          (id (Levelⱼ′ ok (wfTerm (redFirst*Term (d .proj₁)))) , Levelₙ)
          d d′ (Level-ins ([↓]ˡ v v′ t↓ u↓ t≡u))

opaque

  -- Inversion for ℕ.

  inv-[conv↓]∷-ℕ :
    Γ ⊢ t [conv↓] u ∷ ℕ →
    Γ ⊢ t ~ u ↓ ℕ ⊎
    (t PE.≡ zero × u PE.≡ zero) ⊎
    ∃₂ λ t′ u′ → t PE.≡ suc t′ × u PE.≡ suc u′ ×
    Γ ⊢ t′ [conv↑] u′ ∷ ℕ
  inv-[conv↓]∷-ℕ (ℕ-ins t~u) =
    inj₁ t~u
  inv-[conv↓]∷-ℕ (zero-refl _) =
    inj₂ (inj₁ (PE.refl , PE.refl))
  inv-[conv↓]∷-ℕ (suc-cong t≡u) =
    inj₂ (inj₂ (_ , _ , PE.refl , PE.refl , t≡u))
  inv-[conv↓]∷-ℕ (ne-ins _ _ () _)

opaque

  -- Inversion for Id.

  inv-[conv↓]∷-Id :
    Γ ⊢ t [conv↓] u ∷ Id A v w →
    (∃₃ λ A v w → Γ ⊢ t ~ u ↓ Id A v w) ⊎
    t PE.≡ rfl × u PE.≡ rfl × Γ ⊢ v ≡ w ∷ A
  inv-[conv↓]∷-Id (Id-ins _ t~u)    = inj₁ (_ , _ , _ , t~u)
  inv-[conv↓]∷-Id (rfl-refl v≡w)    = inj₂ (PE.refl , PE.refl , v≡w)
  inv-[conv↓]∷-Id (ne-ins _ _ () _)
