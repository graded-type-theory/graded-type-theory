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
open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
import Definition.Untyped.Erased 𝕄 as Erased
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
  α β                                                   : Nat
  x y                                                   : Fin _
  ∇                                                     : DCon (Term 0) _
  Γ                                                     : Con Term _
  A A₁ A₂ B B₁ B₂ C C₁ C₂ t t₁ t₂ t₃ t₄ u u₁ u₂ u₃ u₄ v
    w                                                   : Term _
  V                                                     : Set a
  b                                                     : BinderMode
  s                                                     : Strength
  l                                                     : Universe-level
  p q r                                                 : M

------------------------------------------------------------------------
-- Inversion and similar lemmas for _⊢_~_↑_

opaque

  -- A kind of inversion lemma for var.

  inv-~-var :
    ∇ » Γ ⊢ t ~ u ↑ A →
    (∃ λ x → t PE.≡ var x × u PE.≡ var x) ⊎
    ¬ (∃ λ x → t PE.≡ var x) × ¬ (∃ λ x → u PE.≡ var x)
  inv-~-var = λ where
    (var-refl _ PE.refl)       → inj₁ (_ , PE.refl , PE.refl)
    (defn-refl _ _ _)          → inj₂ ((λ ()) , (λ ()))
    (app-cong _ _)             → inj₂ ((λ ()) , (λ ()))
    (fst-cong _)               → inj₂ ((λ ()) , (λ ()))
    (snd-cong _)               → inj₂ ((λ ()) , (λ ()))
    (prodrec-cong _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (emptyrec-cong _ _)        → inj₂ ((λ ()) , (λ ()))
    (unitrec-cong _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    (natrec-cong _ _ _ _)      → inj₂ ((λ ()) , (λ ()))
    (J-cong _ _ _ _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    (K-cong _ _ _ _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    ([]-cong-cong _ _ _ _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for var.

  inv-var~ :
    ∇ » Γ ⊢ var x ~ u ↑ A →
    u PE.≡ var x
  inv-var~ (var-refl _ PE.refl) = PE.refl

opaque

  -- Inversion for var.

  inv-~var :
    ∇ » Γ ⊢ t ~ var y ↑ A →
    t PE.≡ var y
  inv-~var (var-refl _ PE.refl) = PE.refl

opaque

  -- A kind of inversion lemma for var.

  inv-~-defn :
    ∇ » Γ ⊢ t ~ u ↑ A →
    (∃₂ λ α A → α ↦⊘∷ A ∈ ∇ × t PE.≡ defn α × u PE.≡ defn α) ⊎
    ¬ (∃ λ α → t PE.≡ defn α) × ¬ (∃ λ α → u PE.≡ defn α)
  inv-~-defn = λ where
    (defn-refl _ α↦⊘ PE.refl)  → inj₁ (_ , _ , α↦⊘ , PE.refl , PE.refl)
    (var-refl _ _)             → inj₂ ((λ ()) , (λ ()))
    (app-cong _ _)             → inj₂ ((λ ()) , (λ ()))
    (fst-cong _)               → inj₂ ((λ ()) , (λ ()))
    (snd-cong _)               → inj₂ ((λ ()) , (λ ()))
    (prodrec-cong _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (emptyrec-cong _ _)        → inj₂ ((λ ()) , (λ ()))
    (unitrec-cong _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    (natrec-cong _ _ _ _)      → inj₂ ((λ ()) , (λ ()))
    (J-cong _ _ _ _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    (K-cong _ _ _ _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    ([]-cong-cong _ _ _ _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for defn.

  inv-defn~ :
    ∇ » Γ ⊢ defn α ~ u ↑ A →
    u PE.≡ defn α
  inv-defn~ (defn-refl _ _ PE.refl) = PE.refl

opaque

  -- Inversion for defn.

  inv-~defn :
    ∇ » Γ ⊢ t ~ defn β ↑ A →
    t PE.≡ defn β
  inv-~defn (defn-refl _ _ PE.refl) = PE.refl

opaque

  -- Inversion for U.

  inv-U~ : ¬ ∇ » Γ ⊢ U l ~ u ↑ A
  inv-U~ ()

opaque

  -- Inversion for U.

  inv-~U : ¬ ∇ » Γ ⊢ t ~ U l ↑ A
  inv-~U ()

opaque

  -- Inversion for ΠΣ.

  inv-ΠΣ~ : ¬ ∇ » Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ B₁ ▹ B₂ ~ u ↑ A
  inv-ΠΣ~ ()

opaque

  -- Inversion for ΠΣ.

  inv-~ΠΣ : ¬ ∇ » Γ ⊢ t ~ ΠΣ⟨ b ⟩ p , q ▷ C₁ ▹ C₂ ↑ A
  inv-~ΠΣ ()

opaque

  -- Inversion for lam.

  inv-lam~ : ¬ ∇ » Γ ⊢ lam p t ~ u ↑ A
  inv-lam~ ()

opaque

  -- Inversion for lam.

  inv-~lam : ¬ ∇ » Γ ⊢ t ~ lam p u ↑ A
  inv-~lam ()

opaque

  -- A kind of inversion lemma for _∘⟨_⟩_.

  inv-~-∘ :
    ∇ » Γ ⊢ t ~ u ↑ A →
    (∃₈ λ p q B C t₁ t₂ u₁ u₂ →
     A PE.≡ C [ t₂ ]₀ × t PE.≡ t₁ ∘⟨ p ⟩ t₂ × u PE.≡ u₁ ∘⟨ p ⟩ u₂ ×
     ∇ » Γ ⊢ t₁ ~ u₁ ↓ Π p , q ▷ B ▹ C ×
     ∇ » Γ ⊢ t₂ [conv↑] u₂ ∷ B) ⊎
    ¬ (∃₃ λ p t₁ t₂ → t PE.≡ t₁ ∘⟨ p ⟩ t₂) ×
    ¬ (∃₃ λ p u₁ u₂ → u PE.≡ u₁ ∘⟨ p ⟩ u₂)
  inv-~-∘ = λ where
    (app-cong t₁~u₁ t₂≡u₂) →
      inj₁ $
      _ , _ , _ , _ , _ , _ , _ , _ ,
      PE.refl , PE.refl , PE.refl , t₁~u₁ , t₂≡u₂
    (var-refl _ _)             → inj₂ ((λ ()) , (λ ()))
    (defn-refl _ _ _)          → inj₂ ((λ ()) , (λ ()))
    (fst-cong _)               → inj₂ ((λ ()) , (λ ()))
    (snd-cong _)               → inj₂ ((λ ()) , (λ ()))
    (prodrec-cong _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (emptyrec-cong _ _)        → inj₂ ((λ ()) , (λ ()))
    (unitrec-cong _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    (natrec-cong _ _ _ _)      → inj₂ ((λ ()) , (λ ()))
    (J-cong _ _ _ _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    (K-cong _ _ _ _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    ([]-cong-cong _ _ _ _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for _∘⟨_⟩_.

  inv-∘~ :
    ∇ » Γ ⊢ t₁ ∘⟨ p ⟩ t₂ ~ u ↑ A →
    ∃₅ λ q B C u₁ u₂ →
    A PE.≡ C [ t₂ ]₀ ×
    u PE.≡ u₁ ∘⟨ p ⟩ u₂ ×
    ∇ » Γ ⊢ t₁ ~ u₁ ↓ Π p , q ▷ B ▹ C ×
    ∇ » Γ ⊢ t₂ [conv↑] u₂ ∷ B
  inv-∘~ (app-cong t₁~u₁ t₂≡u₂) =
    _ , _ , _ , _ , _ , PE.refl , PE.refl , t₁~u₁ , t₂≡u₂

opaque

  -- Inversion for _∘⟨_⟩_.

  inv-~∘ :
    ∇ » Γ ⊢ t ~ u₁ ∘⟨ p ⟩ u₂ ↑ A →
    ∃₅ λ q B C t₁ t₂ →
    A PE.≡ C [ t₂ ]₀ ×
    t PE.≡ t₁ ∘⟨ p ⟩ t₂ ×
    ∇ » Γ ⊢ t₁ ~ u₁ ↓ Π p , q ▷ B ▹ C ×
    ∇ » Γ ⊢ t₂ [conv↑] u₂ ∷ B
  inv-~∘ (app-cong t₁~u₁ t₂≡u₂) =
    _ , _ , _ , _ , _ , PE.refl , PE.refl , t₁~u₁ , t₂≡u₂

opaque

  -- Inversion for prod.

  inv-prod~ : ¬ ∇ » Γ ⊢ prod s p t₁ t₂ ~ u ↑ A
  inv-prod~ ()

opaque

  -- Inversion for prod.

  inv-~prod : ¬ ∇ » Γ ⊢ t ~ prod s p u₁ u₂ ↑ A
  inv-~prod ()

opaque

  -- A kind of inversion lemma for fst.

  inv-~-fst :
    ∇ » Γ ⊢ t ~ u ↑ A →
    (∃₅ λ p q B t′ u′ →
     t PE.≡ fst p t′ × u PE.≡ fst p u′ ×
     ∇ » Γ ⊢ t′ ~ u′ ↓ Σˢ p , q ▷ A ▹ B) ⊎
    ¬ (∃₂ λ p t′ → t PE.≡ fst p t′) × ¬ (∃₂ λ p u′ → u PE.≡ fst p u′)
  inv-~-fst = λ where
    (fst-cong t′~u′) →
      inj₁ (_ , _ , _ , _ , _ , PE.refl , PE.refl , t′~u′)
    (var-refl _ _)             → inj₂ ((λ ()) , (λ ()))
    (defn-refl _ _ _)          → inj₂ ((λ ()) , (λ ()))
    (app-cong _ _)             → inj₂ ((λ ()) , (λ ()))
    (snd-cong _)               → inj₂ ((λ ()) , (λ ()))
    (prodrec-cong _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (emptyrec-cong _ _)        → inj₂ ((λ ()) , (λ ()))
    (unitrec-cong _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    (natrec-cong _ _ _ _)      → inj₂ ((λ ()) , (λ ()))
    (J-cong _ _ _ _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    (K-cong _ _ _ _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    ([]-cong-cong _ _ _ _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for fst.

  inv-fst~ :
    ∇ » Γ ⊢ fst p t ~ u ↑ A →
    ∃₃ λ q B u′ →
    u PE.≡ fst p u′ ×
    ∇ » Γ ⊢ t ~ u′ ↓ Σˢ p , q ▷ A ▹ B
  inv-fst~ (fst-cong t~u′) = _ , _ , _ , PE.refl , t~u′

opaque

  -- Inversion for fst.

  inv-~fst :
    ∇ » Γ ⊢ t ~ fst p u ↑ A →
    ∃₃ λ q B t′ →
    t PE.≡ fst p t′ ×
    ∇ » Γ ⊢ t′ ~ u ↓ Σˢ p , q ▷ A ▹ B
  inv-~fst (fst-cong t′~u) = _ , _ , _ , PE.refl , t′~u

opaque

  -- A kind of inversion lemma for snd.

  inv-~-snd :
    ∇ » Γ ⊢ t ~ u ↑ A →
    (∃₆ λ p q B C t′ u′ →
     A PE.≡ C [ fst p t′ ]₀ × t PE.≡ snd p t′ × u PE.≡ snd p u′ ×
     ∇ » Γ ⊢ t′ ~ u′ ↓ Σˢ p , q ▷ B ▹ C) ⊎
    ¬ (∃₂ λ p t′ → t PE.≡ snd p t′) × ¬ (∃₂ λ p u′ → u PE.≡ snd p u′)
  inv-~-snd = λ where
    (snd-cong t′~u′) →
      inj₁ (_ , _ , _ , _ , _ , _ , PE.refl , PE.refl , PE.refl , t′~u′)
    (var-refl _ _)             → inj₂ ((λ ()) , (λ ()))
    (defn-refl _ _ _)          → inj₂ ((λ ()) , (λ ()))
    (app-cong _ _)             → inj₂ ((λ ()) , (λ ()))
    (fst-cong _)               → inj₂ ((λ ()) , (λ ()))
    (prodrec-cong _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (emptyrec-cong _ _)        → inj₂ ((λ ()) , (λ ()))
    (unitrec-cong _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    (natrec-cong _ _ _ _)      → inj₂ ((λ ()) , (λ ()))
    (J-cong _ _ _ _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    (K-cong _ _ _ _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    ([]-cong-cong _ _ _ _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for snd.

  inv-snd~ :
    ∇ » Γ ⊢ snd p t ~ u ↑ A →
    ∃₄ λ q B C u′ →
    A PE.≡ C [ fst p t ]₀ ×
    u PE.≡ snd p u′ ×
    ∇ » Γ ⊢ t ~ u′ ↓ Σˢ p , q ▷ B ▹ C
  inv-snd~ (snd-cong t~u′) = _ , _ , _ , _ , PE.refl , PE.refl , t~u′

opaque

  -- Inversion for snd.

  inv-~snd :
    ∇ » Γ ⊢ t ~ snd p u ↑ A →
    ∃₄ λ q B C t′ →
    A PE.≡ C [ fst p t′ ]₀ ×
    t PE.≡ snd p t′ ×
    ∇ » Γ ⊢ t′ ~ u ↓ Σˢ p , q ▷ B ▹ C
  inv-~snd (snd-cong t′~u) = _ , _ , _ , _ , PE.refl , PE.refl , t′~u

opaque

  -- A kind of inversion lemma for prodrec.

  inv-~-prodrec :
    ∇ » Γ ⊢ t ~ u ↑ A →
    (∃₄ λ r p q′ q → ∃₈ λ A₁ A₂ B C t₁ t₂ u₁ u₂ →
     A PE.≡ B [ t₁ ]₀ ×
     t PE.≡ prodrec r p q′ B t₁ t₂ ×
     u PE.≡ prodrec r p q′ C u₁ u₂ ×
     (∇ » Γ ∙ Σʷ p , q ▷ A₁ ▹ A₂ ⊢ B [conv↑] C) ×
     ∇ » Γ ⊢ t₁ ~ u₁ ↓ Σʷ p , q ▷ A₁ ▹ A₂ ×
     ∇ » Γ ∙ A₁ ∙ A₂ ⊢ t₂ [conv↑] u₂ ∷ B [ prodʷ p (var x1) (var x0) ]↑²) ⊎
    ¬ (∃₆ λ r p q′ B t₁ t₂ → t PE.≡ prodrec r p q′ B t₁ t₂) ×
    ¬ (∃₆ λ r p q′ C u₁ u₂ → u PE.≡ prodrec r p q′ C u₁ u₂)
  inv-~-prodrec = λ where
    (prodrec-cong B≡C t₁~u₁ t₂≡u₂) →
      inj₁ $
      _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ ,
      PE.refl , PE.refl , PE.refl , B≡C , t₁~u₁ , t₂≡u₂
    (var-refl _ _)             → inj₂ ((λ ()) , (λ ()))
    (defn-refl _ _ _)          → inj₂ ((λ ()) , (λ ()))
    (app-cong _ _)             → inj₂ ((λ ()) , (λ ()))
    (fst-cong _)               → inj₂ ((λ ()) , (λ ()))
    (snd-cong _)               → inj₂ ((λ ()) , (λ ()))
    (emptyrec-cong _ _)        → inj₂ ((λ ()) , (λ ()))
    (unitrec-cong _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    (natrec-cong _ _ _ _)      → inj₂ ((λ ()) , (λ ()))
    (J-cong _ _ _ _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    (K-cong _ _ _ _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    ([]-cong-cong _ _ _ _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for prodrec.

  inv-prodrec~ :
    ∇ » Γ ⊢ prodrec r p q B t₁ t₂ ~ u ↑ A →
    ∃₆ λ q′ A₁ A₂ C u₁ u₂ →
    A PE.≡ B [ t₁ ]₀ ×
    u PE.≡ prodrec r p q C u₁ u₂ ×
    (∇ » Γ ∙ Σʷ p , q′ ▷ A₁ ▹ A₂ ⊢ B [conv↑] C) ×
    ∇ » Γ ⊢ t₁ ~ u₁ ↓ Σʷ p , q′ ▷ A₁ ▹ A₂ ×
    ∇ » Γ ∙ A₁ ∙ A₂ ⊢ t₂ [conv↑] u₂ ∷ B [ prodʷ p (var x1) (var x0) ]↑²
  inv-prodrec~ (prodrec-cong B≡C t₁~u₁ t₂≡u₂) =
     _ , _ , _ , _ , _ , _ , PE.refl , PE.refl , B≡C , t₁~u₁ , t₂≡u₂

opaque

  -- Inversion for prodrec.

  inv-~prodrec :
    ∇ » Γ ⊢ t ~ prodrec r p q C u₁ u₂ ↑ A →
    ∃₆ λ q′ A₁ A₂ B t₁ t₂ →
    A PE.≡ B [ t₁ ]₀ ×
    t PE.≡ prodrec r p q B t₁ t₂ ×
    (∇ » Γ ∙ Σʷ p , q′ ▷ A₁ ▹ A₂ ⊢ B [conv↑] C) ×
    ∇ » Γ ⊢ t₁ ~ u₁ ↓ Σʷ p , q′ ▷ A₁ ▹ A₂ ×
    ∇ » Γ ∙ A₁ ∙ A₂ ⊢ t₂ [conv↑] u₂ ∷ B [ prodʷ p (var x1) (var x0) ]↑²
  inv-~prodrec (prodrec-cong B≡C t₁~u₁ t₂≡u₂) =
     _ , _ , _ , _ , _ , _ , PE.refl , PE.refl , B≡C , t₁~u₁ , t₂≡u₂

opaque

  -- Inversion for Empty.

  inv-Empty~ : ¬ ∇ » Γ ⊢ Empty ~ u ↑ A
  inv-Empty~ ()

opaque

  -- Inversion for Empty.

  inv-~Empty : ¬ ∇ » Γ ⊢ t ~ Empty ↑ A
  inv-~Empty ()

opaque

  -- A kind of inversion lemma for emptyrec.

  inv-~-emptyrec :
    ∇ » Γ ⊢ t ~ u ↑ A →
    (∃₄ λ p B t′ u′ →
     t PE.≡ emptyrec p A t′ × u PE.≡ emptyrec p B u′ ×
     (∇ » Γ ⊢ A [conv↑] B) ×
     ∇ » Γ ⊢ t′ ~ u′ ↓ Empty) ⊎
    ¬ (∃₃ λ p A t′ → t PE.≡ emptyrec p A t′) ×
    ¬ (∃₃ λ p B u′ → u PE.≡ emptyrec p B u′)
  inv-~-emptyrec = λ where
    (emptyrec-cong A≡B t′~u′) →
      inj₁ (_ , _ , _ , _ , PE.refl , PE.refl , A≡B , t′~u′)
    (var-refl _ _)             → inj₂ ((λ ()) , (λ ()))
    (defn-refl _ _ _)          → inj₂ ((λ ()) , (λ ()))
    (app-cong _ _)             → inj₂ ((λ ()) , (λ ()))
    (fst-cong _)               → inj₂ ((λ ()) , (λ ()))
    (snd-cong _)               → inj₂ ((λ ()) , (λ ()))
    (prodrec-cong _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (unitrec-cong _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    (natrec-cong _ _ _ _)      → inj₂ ((λ ()) , (λ ()))
    (J-cong _ _ _ _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    (K-cong _ _ _ _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    ([]-cong-cong _ _ _ _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for emptyrec.

  inv-emptyrec~ :
    ∇ » Γ ⊢ emptyrec p B t ~ u ↑ A →
    ∃₂ λ C u′ →
    A PE.≡ B ×
    u PE.≡ emptyrec p C u′ ×
    ∇ » Γ ⊢ B [conv↑] C ×
    ∇ » Γ ⊢ t ~ u′ ↓ Empty
  inv-emptyrec~ (emptyrec-cong B≡C t~u) =
    _ , _ , PE.refl , PE.refl , B≡C , t~u

opaque

  -- Inversion for emptyrec.

  inv-~emptyrec :
    ∇ » Γ ⊢ t ~ emptyrec p C u ↑ A →
    ∃ λ t′ →
    t PE.≡ emptyrec p A t′ ×
    ∇ » Γ ⊢ A [conv↑] C ×
    ∇ » Γ ⊢ t′ ~ u ↓ Empty
  inv-~emptyrec (emptyrec-cong A≡C t~u) =
    _ , PE.refl , A≡C , t~u

opaque

  -- Inversion for Unit.

  inv-Unit~ : ¬ ∇ » Γ ⊢ Unit s l ~ u ↑ A
  inv-Unit~ ()

opaque

  -- Inversion for Unit.

  inv-~Unit : ¬ ∇ » Γ ⊢ t ~ Unit s l ↑ A
  inv-~Unit ()

opaque

  -- Inversion for star.

  inv-star~ : ¬ ∇ » Γ ⊢ star s l ~ u ↑ A
  inv-star~ ()

opaque

  -- Inversion for star.

  inv-~star : ¬ ∇ » Γ ⊢ t ~ star s l ↑ A
  inv-~star ()

opaque

  -- A kind of inversion lemma for unitrec.

  inv-~-unitrec :
    ∇ » Γ ⊢ t ~ u ↑ A →
    (∃₃ λ l p q → ∃₆ λ B C t₁ t₂ u₁ u₂ →
     A PE.≡ B [ t₁ ]₀ ×
     t PE.≡ unitrec l p q B t₁ t₂ ×
     u PE.≡ unitrec l p q C u₁ u₂ ×
     (∇ » Γ ∙ Unitʷ l ⊢ B [conv↑] C) ×
     ∇ » Γ ⊢ t₁ ~ u₁ ↓ Unitʷ l ×
     ∇ » Γ ⊢ t₂ [conv↑] u₂ ∷ B [ starʷ l ]₀ ×
     ¬ Unitʷ-η) ⊎
    ¬ (∃₆ λ l p q B t₁ t₂ → t PE.≡ unitrec l p q B t₁ t₂) ×
    ¬ (∃₆ λ l p q C u₁ u₂ → u PE.≡ unitrec l p q C u₁ u₂)
  inv-~-unitrec = λ where
    (unitrec-cong B≡C t₁~u₁ t₂≡u₂ no-η) →
      inj₁ $
      _ , _ , _ , _ , _ , _ , _ , _ , _ ,
      PE.refl , PE.refl , PE.refl , B≡C , t₁~u₁ , t₂≡u₂ , no-η
    (var-refl _ _)             → inj₂ ((λ ()) , (λ ()))
    (defn-refl _ _ _)          → inj₂ ((λ ()) , (λ ()))
    (app-cong _ _)             → inj₂ ((λ ()) , (λ ()))
    (fst-cong _)               → inj₂ ((λ ()) , (λ ()))
    (snd-cong _)               → inj₂ ((λ ()) , (λ ()))
    (prodrec-cong _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (emptyrec-cong _ _)        → inj₂ ((λ ()) , (λ ()))
    (natrec-cong _ _ _ _)      → inj₂ ((λ ()) , (λ ()))
    (J-cong _ _ _ _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    (K-cong _ _ _ _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    ([]-cong-cong _ _ _ _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for unitrec.

  inv-unitrec~ :
    ∇ » Γ ⊢ unitrec l p q B t₁ t₂ ~ u ↑ A →
    ∃₃ λ C u₁ u₂ →
    A PE.≡ B [ t₁ ]₀ ×
    u PE.≡ unitrec l p q C u₁ u₂ ×
    (∇ » Γ ∙ Unitʷ l ⊢ B [conv↑] C) ×
    ∇ » Γ ⊢ t₁ ~ u₁ ↓ Unitʷ l ×
    ∇ » Γ ⊢ t₂ [conv↑] u₂ ∷ B [ starʷ l ]₀ ×
    ¬ Unitʷ-η
  inv-unitrec~ (unitrec-cong B≡C t₁~u₁ t₂≡u₂ no-η) =
    _ , _ , _ , PE.refl , PE.refl , B≡C , t₁~u₁ , t₂≡u₂ , no-η

opaque

  -- Inversion for unitrec.

  inv-~unitrec :
    ∇ » Γ ⊢ t ~ unitrec l p q C u₁ u₂ ↑ A →
    ∃₃ λ B t₁ t₂ →
    A PE.≡ B [ t₁ ]₀ ×
    t PE.≡ unitrec l p q B t₁ t₂ ×
    (∇ » Γ ∙ Unitʷ l ⊢ B [conv↑] C) ×
    ∇ » Γ ⊢ t₁ ~ u₁ ↓ Unitʷ l ×
    ∇ » Γ ⊢ t₂ [conv↑] u₂ ∷ B [ starʷ l ]₀ ×
    ¬ Unitʷ-η
  inv-~unitrec (unitrec-cong B≡C t₁~u₁ t₂≡u₂ no-η) =
    _ , _ , _ , PE.refl , PE.refl , B≡C , t₁~u₁ , t₂≡u₂ , no-η

opaque

  -- Inversion for ℕ.

  inv-ℕ~ : ¬ ∇ » Γ ⊢ ℕ ~ u ↑ A
  inv-ℕ~ ()

opaque

  -- Inversion for ℕ.

  inv-~ℕ : ¬ ∇ » Γ ⊢ t ~ ℕ ↑ A
  inv-~ℕ ()

opaque

  -- Inversion for zero.

  inv-zero~ : ¬ ∇ » Γ ⊢ zero ~ u ↑ A
  inv-zero~ ()

opaque

  -- Inversion for zero.

  inv-~zero : ¬ ∇ » Γ ⊢ t ~ zero ↑ A
  inv-~zero ()

opaque

  -- Inversion for suc.

  inv-suc~ : ¬ ∇ » Γ ⊢ suc t ~ u ↑ A
  inv-suc~ ()

opaque

  -- Inversion for suc.

  inv-~suc : ¬ ∇ » Γ ⊢ t ~ suc u ↑ A
  inv-~suc ()

opaque

  -- A kind of inversion lemma for natrec.

  inv-~-natrec :
    ∇ » Γ ⊢ t ~ u ↑ A →
    (∃₃ λ p q r → ∃₈ λ B C t₁ t₂ t₃ u₁ u₂ u₃ →
     A PE.≡ B [ t₃ ]₀ ×
     t PE.≡ natrec p q r B t₁ t₂ t₃ ×
     u PE.≡ natrec p q r C u₁ u₂ u₃ ×
     (∇ » Γ ∙ ℕ ⊢ B [conv↑] C) ×
     ∇ » Γ ⊢ t₁ [conv↑] u₁ ∷ B [ zero ]₀ ×
     ∇ » Γ ∙ ℕ ∙ B ⊢ t₂ [conv↑] u₂ ∷ B [ suc (var x1) ]↑² ×
     ∇ » Γ ⊢ t₃ ~ u₃ ↓ ℕ) ⊎
    ¬ (∃₇ λ p q r B t₁ t₂ t₃ → t PE.≡ natrec p q r B t₁ t₂ t₃) ×
    ¬ (∃₇ λ p q r C u₁ u₂ u₃ → u PE.≡ natrec p q r C u₁ u₂ u₃)
  inv-~-natrec = λ where
    (natrec-cong B≡C t₁≡u₁ t₂≡u₂ t₃~u₃) →
      inj₁ $
      _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ ,
      PE.refl , PE.refl , PE.refl , B≡C , t₁≡u₁ , t₂≡u₂ , t₃~u₃
    (var-refl _ _)             → inj₂ ((λ ()) , (λ ()))
    (defn-refl _ _ _)          → inj₂ ((λ ()) , (λ ()))
    (app-cong _ _)             → inj₂ ((λ ()) , (λ ()))
    (fst-cong _)               → inj₂ ((λ ()) , (λ ()))
    (snd-cong _)               → inj₂ ((λ ()) , (λ ()))
    (prodrec-cong _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (emptyrec-cong _ _)        → inj₂ ((λ ()) , (λ ()))
    (unitrec-cong _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    (J-cong _ _ _ _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    (K-cong _ _ _ _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    ([]-cong-cong _ _ _ _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for natrec.

  inv-natrec~ :
    ∇ » Γ ⊢ natrec p q r B t₁ t₂ t₃ ~ u ↑ A →
    ∃₄ λ C u₁ u₂ u₃ →
    A PE.≡ B [ t₃ ]₀ ×
    u PE.≡ natrec p q r C u₁ u₂ u₃ ×
    (∇ » Γ ∙ ℕ ⊢ B [conv↑] C) ×
    ∇ » Γ ⊢ t₁ [conv↑] u₁ ∷ B [ zero ]₀ ×
    ∇ » Γ ∙ ℕ ∙ B ⊢ t₂ [conv↑] u₂ ∷ B [ suc (var x1) ]↑² ×
    ∇ » Γ ⊢ t₃ ~ u₃ ↓ ℕ
  inv-natrec~ (natrec-cong B≡C t₁≡u₁ t₂≡u₂ t₃~u₃) =
    _ , _ , _ , _ , PE.refl , PE.refl , B≡C , t₁≡u₁ , t₂≡u₂ , t₃~u₃

opaque

  -- Inversion for natrec.

  inv-~natrec :
    ∇ » Γ ⊢ t ~ natrec p q r C u₁ u₂ u₃ ↑ A →
    ∃₄ λ B t₁ t₂ t₃ →
    A PE.≡ B [ t₃ ]₀ ×
    t PE.≡ natrec p q r B t₁ t₂ t₃ ×
    (∇ » Γ ∙ ℕ ⊢ B [conv↑] C) ×
    ∇ » Γ ⊢ t₁ [conv↑] u₁ ∷ B [ zero ]₀ ×
    ∇ » Γ ∙ ℕ ∙ B ⊢ t₂ [conv↑] u₂ ∷ B [ suc (var x1) ]↑² ×
    ∇ » Γ ⊢ t₃ ~ u₃ ↓ ℕ
  inv-~natrec (natrec-cong B≡C t₁≡u₁ t₂≡u₂ t₃~u₃) =
    _ , _ , _ , _ , PE.refl , PE.refl , B≡C , t₁≡u₁ , t₂≡u₂ , t₃~u₃

opaque

  -- Inversion for Id.

  inv-Id~ : ¬ ∇ » Γ ⊢ Id B t₁ t₂ ~ u ↑ A
  inv-Id~ ()

opaque

  -- Inversion for Id.

  inv-~Id : ¬ ∇ » Γ ⊢ t ~ Id C u₁ u₂ ↑ A
  inv-~Id ()

opaque

  -- Inversion for rfl.

  inv-rfl~ : ¬ ∇ » Γ ⊢ rfl ~ u ↑ A
  inv-rfl~ ()

opaque

  -- Inversion for rfl.

  inv-~rfl : ¬ ∇ » Γ ⊢ t ~ rfl ↑ A
  inv-~rfl ()

opaque

  -- A kind of inversion lemma for J.

  inv-~-J :
    ∇ » Γ ⊢ t ~ u ↑ A →
    (∃₇ λ p q B₁ B₂ C₁ C₂ D → ∃₈ λ t₁ t₂ t₃ t₄ u₁ u₂ u₃ u₄ →
     A PE.≡ B₂ [ t₃ , t₄ ]₁₀ ×
     t PE.≡ J p q B₁ t₁ B₂ t₂ t₃ t₄ ×
     u PE.≡ J p q C₁ u₁ C₂ u₂ u₃ u₄ ×
     (∇ » Γ ⊢ B₁ [conv↑] C₁) ×
     ∇ » Γ ⊢ t₁ [conv↑] u₁ ∷ B₁ ×
     (∇ » Γ ∙ B₁ ∙ Id (wk1 B₁) (wk1 t₁) (var x0) ⊢ B₂ [conv↑] C₂) ×
     ∇ » Γ ⊢ t₂ [conv↑] u₂ ∷ B₂ [ t₁ , rfl ]₁₀ ×
     ∇ » Γ ⊢ t₃ [conv↑] u₃ ∷ B₁ ×
     ∇ » Γ ⊢ t₄ ~ u₄ ↓ D ×
     ∇ » Γ ⊢ D ≡ Id B₁ t₁ t₃) ⊎
    ¬ (∃₈ λ p q B₁ B₂ t₁ t₂ t₃ t₄ → t PE.≡ J p q B₁ t₁ B₂ t₂ t₃ t₄) ×
    ¬ (∃₈ λ p q C₁ C₂ u₁ u₂ u₃ u₄ → u PE.≡ J p q C₁ u₁ C₂ u₂ u₃ u₄)
  inv-~-J = λ where
    (J-cong B₁≡C₁ t₁≡u₁ B₂≡C₂ t₂≡u₂ t₃≡u₃ t₄~u₄ D≡Id) →
      inj₁ $
      _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ ,
      PE.refl , PE.refl , PE.refl ,
      B₁≡C₁ , t₁≡u₁ , B₂≡C₂ , t₂≡u₂ , t₃≡u₃ , t₄~u₄ , D≡Id
    (var-refl _ _)             → inj₂ ((λ ()) , (λ ()))
    (defn-refl _ _ _)          → inj₂ ((λ ()) , (λ ()))
    (app-cong _ _)             → inj₂ ((λ ()) , (λ ()))
    (fst-cong _)               → inj₂ ((λ ()) , (λ ()))
    (snd-cong _)               → inj₂ ((λ ()) , (λ ()))
    (prodrec-cong _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (emptyrec-cong _ _)        → inj₂ ((λ ()) , (λ ()))
    (unitrec-cong _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    (natrec-cong _ _ _ _)      → inj₂ ((λ ()) , (λ ()))
    (K-cong _ _ _ _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    ([]-cong-cong _ _ _ _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for J.

  inv-J~ :
    ∇ » Γ ⊢ J p q B₁ t₁ B₂ t₂ t₃ t₄ ~ u ↑ A →
    ∃₇ λ C₁ C₂ D u₁ u₂ u₃ u₄ →
    A PE.≡ B₂ [ t₃ , t₄ ]₁₀ ×
    u PE.≡ J p q C₁ u₁ C₂ u₂ u₃ u₄ ×
    (∇ » Γ ⊢ B₁ [conv↑] C₁) ×
    ∇ » Γ ⊢ t₁ [conv↑] u₁ ∷ B₁ ×
    (∇ » Γ ∙ B₁ ∙ Id (wk1 B₁) (wk1 t₁) (var x0) ⊢ B₂ [conv↑] C₂) ×
    ∇ » Γ ⊢ t₂ [conv↑] u₂ ∷ B₂ [ t₁ , rfl ]₁₀ ×
    ∇ » Γ ⊢ t₃ [conv↑] u₃ ∷ B₁ ×
    ∇ » Γ ⊢ t₄ ~ u₄ ↓ D ×
    ∇ » Γ ⊢ D ≡ Id B₁ t₁ t₃
  inv-J~ (J-cong B₁≡C₁ t₁≡u₁ B₂≡C₂ t₂≡u₂ t₃≡u₃ t₄~u₄ D≡) =
    _ , _ , _ , _ , _ , _ , _ , PE.refl , PE.refl ,
    B₁≡C₁ , t₁≡u₁ , B₂≡C₂ , t₂≡u₂ , t₃≡u₃ , t₄~u₄ , D≡

opaque

  -- Inversion for J.

  inv-~J :
    ∇ » Γ ⊢ t ~ J p q C₁ u₁ C₂ u₂ u₃ u₄ ↑ A →
    ∃₇ λ B₁ B₂ D t₁ t₂ t₃ t₄ →
    A PE.≡ B₂ [ t₃ , t₄ ]₁₀ ×
    t PE.≡ J p q B₁ t₁ B₂ t₂ t₃ t₄ ×
    (∇ » Γ ⊢ B₁ [conv↑] C₁) ×
    ∇ » Γ ⊢ t₁ [conv↑] u₁ ∷ B₁ ×
    (∇ » Γ ∙ B₁ ∙ Id (wk1 B₁) (wk1 t₁) (var x0) ⊢ B₂ [conv↑] C₂) ×
    ∇ » Γ ⊢ t₂ [conv↑] u₂ ∷ B₂ [ t₁ , rfl ]₁₀ ×
    ∇ » Γ ⊢ t₃ [conv↑] u₃ ∷ B₁ ×
    ∇ » Γ ⊢ t₄ ~ u₄ ↓ D ×
    ∇ » Γ ⊢ D ≡ Id B₁ t₁ t₃
  inv-~J (J-cong B₁≡C₁ t₁≡u₁ B₂≡C₂ t₂≡u₂ t₃≡u₃ t₄~u₄ D≡) =
    _ , _ , _ , _ , _ , _ , _ , PE.refl , PE.refl ,
    B₁≡C₁ , t₁≡u₁ , B₂≡C₂ , t₂≡u₂ , t₃≡u₃ , t₄~u₄ , D≡

opaque

  -- A kind of inversion lemma for K.

  inv-~-K :
    ∇ » Γ ⊢ t ~ u ↑ A →
    (∃₆ λ p B₁ B₂ C₁ C₂ D → ∃₆ λ t₁ t₂ t₃ u₁ u₂ u₃ →
     A PE.≡ B₂ [ t₃ ]₀ ×
     t PE.≡ K p B₁ t₁ B₂ t₂ t₃ ×
     u PE.≡ K p C₁ u₁ C₂ u₂ u₃ ×
     (∇ » Γ ⊢ B₁ [conv↑] C₁) ×
     ∇ » Γ ⊢ t₁ [conv↑] u₁ ∷ B₁ ×
     (∇ » Γ ∙ Id B₁ t₁ t₁ ⊢ B₂ [conv↑] C₂) ×
     ∇ » Γ ⊢ t₂ [conv↑] u₂ ∷ B₂ [ rfl ]₀ ×
     ∇ » Γ ⊢ t₃ ~ u₃ ↓ D ×
     ∇ » Γ ⊢ D ≡ Id B₁ t₁ t₁ ×
     K-allowed) ⊎
    ¬ (∃₆ λ p B₁ B₂ t₁ t₂ t₃ → t PE.≡ K p B₁ t₁ B₂ t₂ t₃) ×
    ¬ (∃₆ λ p C₁ C₂ u₁ u₂ u₃ → u PE.≡ K p C₁ u₁ C₂ u₂ u₃)
  inv-~-K = λ where
    (K-cong B₁≡C₁ t₁≡u₁ B₂≡C₂ t₂≡u₂ t₃~u₃ D≡Id ok) →
      inj₁ $
      _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ ,
      PE.refl , PE.refl , PE.refl ,
      B₁≡C₁ , t₁≡u₁ , B₂≡C₂ , t₂≡u₂ , t₃~u₃ , D≡Id , ok
    (var-refl _ _)             → inj₂ ((λ ()) , (λ ()))
    (defn-refl _ _ _)          → inj₂ ((λ ()) , (λ ()))
    (app-cong _ _)             → inj₂ ((λ ()) , (λ ()))
    (fst-cong _)               → inj₂ ((λ ()) , (λ ()))
    (snd-cong _)               → inj₂ ((λ ()) , (λ ()))
    (prodrec-cong _ _ _)       → inj₂ ((λ ()) , (λ ()))
    (emptyrec-cong _ _)        → inj₂ ((λ ()) , (λ ()))
    (unitrec-cong _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    (natrec-cong _ _ _ _)      → inj₂ ((λ ()) , (λ ()))
    (J-cong _ _ _ _ _ _ _)     → inj₂ ((λ ()) , (λ ()))
    ([]-cong-cong _ _ _ _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for K.

  inv-K~ :
    ∇ » Γ ⊢ K p B₁ t₁ B₂ t₂ t₃ ~ u ↑ A →
    ∃₆ λ C₁ C₂ D u₁ u₂ u₃ →
    A PE.≡ B₂ [ t₃ ]₀ ×
    u PE.≡ K p C₁ u₁ C₂ u₂ u₃ ×
    (∇ » Γ ⊢ B₁ [conv↑] C₁) ×
    ∇ » Γ ⊢ t₁ [conv↑] u₁ ∷ B₁ ×
    (∇ » Γ ∙ Id B₁ t₁ t₁ ⊢ B₂ [conv↑] C₂) ×
    ∇ » Γ ⊢ t₂ [conv↑] u₂ ∷ B₂ [ rfl ]₀ ×
    ∇ » Γ ⊢ t₃ ~ u₃ ↓ D ×
    ∇ » Γ ⊢ D ≡ Id B₁ t₁ t₁ ×
    K-allowed
  inv-K~ (K-cong B₁≡C₁ t₁≡u₁ B₂≡C₂ t₂≡u₂ t₃~u₃ D≡ ok) =
    _ , _ , _ , _ , _ , _ , PE.refl , PE.refl ,
    B₁≡C₁ , t₁≡u₁ , B₂≡C₂ , t₂≡u₂ , t₃~u₃ , D≡ , ok

opaque

  -- Inversion for K.

  inv-~K :
    ∇ » Γ ⊢ t ~ K p C₁ u₁ C₂ u₂ u₃ ↑ A →
    ∃₆ λ B₁ B₂ D t₁ t₂ t₃ →
    A PE.≡ B₂ [ t₃ ]₀ ×
    t PE.≡ K p B₁ t₁ B₂ t₂ t₃ ×
    (∇ » Γ ⊢ B₁ [conv↑] C₁) ×
    ∇ » Γ ⊢ t₁ [conv↑] u₁ ∷ B₁ ×
    (∇ » Γ ∙ Id B₁ t₁ t₁ ⊢ B₂ [conv↑] C₂) ×
    ∇ » Γ ⊢ t₂ [conv↑] u₂ ∷ B₂ [ rfl ]₀ ×
    ∇ » Γ ⊢ t₃ ~ u₃ ↓ D ×
    ∇ » Γ ⊢ D ≡ Id B₁ t₁ t₁ ×
    K-allowed
  inv-~K (K-cong B₁≡C₁ t₁≡u₁ B₂≡C₂ t₂≡u₂ t₃~u₃ D≡ ok) =
    _ , _ , _ , _ , _ , _ , PE.refl , PE.refl ,
    B₁≡C₁ , t₁≡u₁ , B₂≡C₂ , t₂≡u₂ , t₃~u₃ , D≡ , ok

opaque

  -- A kind of inversion lemma for []-cong.

  inv-~-[]-cong :
    ∇ » Γ ⊢ t ~ u ↑ A →
    (∃₄ λ s B C D → ∃₆ λ t₁ t₂ t₃ u₁ u₂ u₃ →
     let open Erased s in
     A PE.≡ Id (Erased B) [ t₁ ] ([ t₂ ]) ×
     t PE.≡ []-cong s B t₁ t₂ t₃ ×
     u PE.≡ []-cong s C u₁ u₂ u₃ ×
     (∇ » Γ ⊢ B [conv↑] C) ×
     ∇ » Γ ⊢ t₁ [conv↑] u₁ ∷ B ×
     ∇ » Γ ⊢ t₂ [conv↑] u₂ ∷ B ×
     ∇ » Γ ⊢ t₃ ~ u₃ ↓ D ×
     ∇ » Γ ⊢ D ≡ Id B t₁ t₂ ×
     []-cong-allowed s) ⊎
    ¬ (∃₅ λ s B t₁ t₂ t₃ → t PE.≡ []-cong s B t₁ t₂ t₃) ×
    ¬ (∃₅ λ s C u₁ u₂ u₃ → u PE.≡ []-cong s C u₁ u₂ u₃)
  inv-~-[]-cong = λ where
    ([]-cong-cong B≡C t₁≡u₁ t₂≡u₂ t₃~u₃ D≡Id ok) →
      inj₁ $
      _ , _ , _ , _ , _ , _ , _ , _ , _ , _ ,
      PE.refl , PE.refl , PE.refl ,
      B≡C , t₁≡u₁ , t₂≡u₂ , t₃~u₃ , D≡Id , ok
    (var-refl _ _)         → inj₂ ((λ ()) , (λ ()))
    (defn-refl _ _ _)      → inj₂ ((λ ()) , (λ ()))
    (app-cong _ _)         → inj₂ ((λ ()) , (λ ()))
    (fst-cong _)           → inj₂ ((λ ()) , (λ ()))
    (snd-cong _)           → inj₂ ((λ ()) , (λ ()))
    (prodrec-cong _ _ _)   → inj₂ ((λ ()) , (λ ()))
    (emptyrec-cong _ _)    → inj₂ ((λ ()) , (λ ()))
    (unitrec-cong _ _ _ _) → inj₂ ((λ ()) , (λ ()))
    (natrec-cong _ _ _ _)  → inj₂ ((λ ()) , (λ ()))
    (J-cong _ _ _ _ _ _ _) → inj₂ ((λ ()) , (λ ()))
    (K-cong _ _ _ _ _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for []-cong.

  inv-[]-cong~ :
    let open Erased s in
    ∇ » Γ ⊢ []-cong s B t₁ t₂ t₃ ~ u ↑ A →
    ∃₅ λ C D u₁ u₂ u₃ →
    A PE.≡ Id (Erased B) [ t₁ ] ([ t₂ ]) ×
    u PE.≡ []-cong s C u₁ u₂ u₃ ×
    (∇ » Γ ⊢ B [conv↑] C) ×
    ∇ » Γ ⊢ t₁ [conv↑] u₁ ∷ B ×
    ∇ » Γ ⊢ t₂ [conv↑] u₂ ∷ B ×
    ∇ » Γ ⊢ t₃ ~ u₃ ↓ D ×
    ∇ » Γ ⊢ D ≡ Id B t₁ t₂ ×
    []-cong-allowed s
  inv-[]-cong~ ([]-cong-cong B≡C t₁≡u₁ t₂≡u₂ t₃~u₃ D≡ ok) =
    _ , _ , _ , _ , _ , PE.refl , PE.refl ,
    B≡C , t₁≡u₁ , t₂≡u₂ , t₃~u₃ , D≡ , ok

opaque

  -- Inversion for []-cong.

  inv-~[]-cong :
    let open Erased s in
    ∇ » Γ ⊢ t ~ []-cong s C u₁ u₂ u₃ ↑ A →
    ∃₅ λ B D t₁ t₂ t₃ →
    A PE.≡ Id (Erased B) [ t₁ ] ([ t₂ ]) ×
    t PE.≡ []-cong s B t₁ t₂ t₃ ×
    (∇ » Γ ⊢ B [conv↑] C) ×
    ∇ » Γ ⊢ t₁ [conv↑] u₁ ∷ B ×
    ∇ » Γ ⊢ t₂ [conv↑] u₂ ∷ B ×
    ∇ » Γ ⊢ t₃ ~ u₃ ↓ D ×
    ∇ » Γ ⊢ D ≡ Id B t₁ t₂ ×
    []-cong-allowed s
  inv-~[]-cong ([]-cong-cong B≡C t₁≡u₁ t₂≡u₂ t₃~u₃ D≡ ok) =
    _ , _ , _ , _ , _ , PE.refl , PE.refl ,
    B≡C , t₁≡u₁ , t₂≡u₂ , t₃~u₃ , D≡ , ok

------------------------------------------------------------------------
-- Inversion and similar lemmas for _⊢_[conv↓]_

opaque

  -- A kind of inversion lemma for neutral terms.

  inv-[conv↓]-ne′ :
    ∇ » Γ ⊢ A [conv↓] B →
    (∃ λ l → ∇ » Γ ⊢ A ~ B ↓ U l) ⊎ ¬ Neutral V ∇ A × ¬ Neutral V ∇ B
  inv-[conv↓]-ne′ =
    let l : ∀ {n} {T : Term n}
            → (∀ {X} → Neutral V ∇ X → T PE.≢ X) → ¬ Neutral V ∇ T
        l T≠ne T-ne = T≠ne T-ne PE.refl
    in  λ where
          (ne A~B)        → inj₁ (_ , A~B)
          (U-refl _)      → inj₂ (l U≢ne      , l U≢ne)
          (ΠΣ-cong _ _ _) → inj₂ (l (ΠΣ≢ne _) , l (ΠΣ≢ne _))
          (Empty-refl _)  → inj₂ (l Empty≢ne  , l Empty≢ne)
          (Unit-refl _ _) → inj₂ (l Unit≢ne   , l Unit≢ne)
          (ℕ-refl _)      → inj₂ (l ℕ≢ne      , l ℕ≢ne)
          (Id-cong _ _ _) → inj₂ (l Id≢ne     , l Id≢ne)


opaque

  -- Inversion for neutral terms.

  inv-[conv↓]-ne :
    Neutral V ∇ A →
    ∇ » Γ ⊢ A [conv↓] B →
    ∃ λ l → ∇ » Γ ⊢ A ~ B ↓ U l
  inv-[conv↓]-ne A-ne A≡B = case inv-[conv↓]-ne′ A≡B of λ where
    (inj₁ A~B)         → A~B
    (inj₂ (¬A-ne , _)) → ⊥-elim (¬A-ne A-ne)

opaque

  -- A kind of inversion lemma for U.

  inv-[conv↓]-U′ :
    ∇ » Γ ⊢ A [conv↓] B →
    (∃ λ l → A PE.≡ U l × B PE.≡ U l) ⊎
    ¬ (∃ λ l → A PE.≡ U l) × ¬ (∃ λ l → B PE.≡ U l)
  inv-[conv↓]-U′ = λ where
    (U-refl _) → inj₁ (_ , PE.refl , PE.refl)
    (ne A~B) →
      inj₂ $
      case ne~↓ A~B of λ
        (_ , A-ne , B-ne) →
        (λ { (_ , PE.refl) → U≢ne A-ne PE.refl })
      , (λ { (_ , PE.refl) → U≢ne B-ne PE.refl })
    (ΠΣ-cong _ _ _) → inj₂ ((λ ()) , (λ ()))
    (Empty-refl _)  → inj₂ ((λ ()) , (λ ()))
    (Unit-refl _ _) → inj₂ ((λ ()) , (λ ()))
    (ℕ-refl _)      → inj₂ ((λ ()) , (λ ()))
    (Id-cong _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for U.

  inv-[conv↓]-U :
    ∇ » Γ ⊢ U l [conv↓] A →
    A PE.≡ U l
  inv-[conv↓]-U U≡A = case inv-[conv↓]-U′ U≡A of λ where
    (inj₁ (_ , PE.refl , A≡U)) → A≡U
    (inj₂ (U≢U , _))           → ⊥-elim (U≢U (_ , PE.refl))

opaque

  -- A kind of inversion lemma for Π and Σ.

  inv-[conv↓]-ΠΣ′ :
    ∇ » Γ ⊢ A [conv↓] B →
    (∃₇ λ b p q A₁ A₂ B₁ B₂ →
     A PE.≡ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ A₂ ×
     B PE.≡ ΠΣ⟨ b ⟩ p , q ▷ B₁ ▹ B₂ ×
     ∇ » Γ ⊢ A₁ [conv↑] B₁ × ∇ » Γ ∙ A₁ ⊢ A₂ [conv↑] B₂) ⊎
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
        (λ { (b , _ , _ , _ , _ , PE.refl) → ΠΣ≢ne b A-ne PE.refl })
      , (λ { (b , _ , _ , _ , _ , PE.refl) → ΠΣ≢ne b B-ne PE.refl })
    (U-refl _)      → inj₂ ((λ ()) , (λ ()))
    (Empty-refl _)  → inj₂ ((λ ()) , (λ ()))
    (Unit-refl _ _) → inj₂ ((λ ()) , (λ ()))
    (ℕ-refl _)      → inj₂ ((λ ()) , (λ ()))
    (Id-cong _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for Π and Σ.

  inv-[conv↓]-ΠΣ :
    ∇ » Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ A₂ [conv↓] B →
    ∃₂ λ B₁ B₂ →
    B PE.≡ ΠΣ⟨ b ⟩ p , q ▷ B₁ ▹ B₂ ×
    ∇ » Γ ⊢ A₁ [conv↑] B₁ × ∇ » Γ ∙ A₁ ⊢ A₂ [conv↑] B₂
  inv-[conv↓]-ΠΣ ΠΣ≡A = case inv-[conv↓]-ΠΣ′ ΠΣ≡A of λ where
    (inj₁ (_ , _ , _ , _ , _ , _ , _ , PE.refl , rest)) →
      _ , _ , rest
    (inj₂ (ΠΣ≢ΠΣ , _)) →
      ⊥-elim (ΠΣ≢ΠΣ (_ , _ , _ , _ , _ , PE.refl))

opaque

  -- A kind of inversion lemma for Empty.

  inv-[conv↓]-Empty′ :
    ∇ » Γ ⊢ A [conv↓] B →
    A PE.≡ Empty × B PE.≡ Empty ⊎ A PE.≢ Empty × B PE.≢ Empty
  inv-[conv↓]-Empty′ = λ where
    (Empty-refl _) → inj₁ (PE.refl , PE.refl)
    (ne A~B) →
      inj₂ $
      case ne~↓ A~B of λ
        (_ , A-ne , B-ne) →
        (λ { PE.refl → Empty≢ne A-ne PE.refl })
      , (λ { PE.refl → Empty≢ne B-ne PE.refl })
    (U-refl _)      → inj₂ ((λ ()) , (λ ()))
    (ΠΣ-cong _ _ _) → inj₂ ((λ ()) , (λ ()))
    (Unit-refl _ _) → inj₂ ((λ ()) , (λ ()))
    (ℕ-refl _)      → inj₂ ((λ ()) , (λ ()))
    (Id-cong _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for Empty.

  inv-[conv↓]-Empty :
    ∇ » Γ ⊢ Empty [conv↓] A →
    A PE.≡ Empty
  inv-[conv↓]-Empty Empty≡A = case inv-[conv↓]-Empty′ Empty≡A of λ where
    (inj₁ (_ , A≡Empty))     → A≡Empty
    (inj₂ (Empty≢Empty , _)) → ⊥-elim (Empty≢Empty PE.refl)

opaque

  -- A kind of inversion lemma for Unit.

  inv-[conv↓]-Unit′ :
    ∇ » Γ ⊢ A [conv↓] B →
    (∃₂ λ s l → A PE.≡ Unit s l × B PE.≡ Unit s l) ⊎
    ¬ (∃₂ λ s l → A PE.≡ Unit s l) × ¬ (∃₂ λ s l → B PE.≡ Unit s l)
  inv-[conv↓]-Unit′ = λ where
    (Unit-refl _ _) → inj₁ (_ , _ , PE.refl , PE.refl)
    (ne A~B) →
      inj₂ $
      case ne~↓ A~B of λ
        (_ , A-ne , B-ne) →
        (λ { (_ , _ , PE.refl) → Unit≢ne A-ne PE.refl })
      , (λ { (_ , _ , PE.refl) → Unit≢ne B-ne PE.refl })
    (U-refl _)      → inj₂ ((λ ()) , (λ ()))
    (ΠΣ-cong _ _ _) → inj₂ ((λ ()) , (λ ()))
    (Empty-refl _)  → inj₂ ((λ ()) , (λ ()))
    (ℕ-refl _)      → inj₂ ((λ ()) , (λ ()))
    (Id-cong _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for Unit.

  inv-[conv↓]-Unit :
    ∇ » Γ ⊢ Unit s l [conv↓] A →
    A PE.≡ Unit s l
  inv-[conv↓]-Unit Unit≡A = case inv-[conv↓]-Unit′ Unit≡A of λ where
    (inj₁ (_ , _ , PE.refl , A≡Unit)) → A≡Unit
    (inj₂ (Unit≢Unit , _))            →
      ⊥-elim (Unit≢Unit (_ , _ , PE.refl))

opaque

  -- A kind of inversion lemma for ℕ.

  inv-[conv↓]-ℕ′ :
    ∇ » Γ ⊢ A [conv↓] B →
    A PE.≡ ℕ × B PE.≡ ℕ ⊎ A PE.≢ ℕ × B PE.≢ ℕ
  inv-[conv↓]-ℕ′ = λ where
    (ℕ-refl _) → inj₁ (PE.refl , PE.refl)
    (ne A~B) →
      inj₂ $
      case ne~↓ A~B of λ
        (_ , A-ne , B-ne) →
        (λ { PE.refl → ℕ≢ne A-ne PE.refl })
      , (λ { PE.refl → ℕ≢ne B-ne PE.refl })
    (U-refl _)      → inj₂ ((λ ()) , (λ ()))
    (ΠΣ-cong _ _ _) → inj₂ ((λ ()) , (λ ()))
    (Empty-refl _)  → inj₂ ((λ ()) , (λ ()))
    (Unit-refl _ _) → inj₂ ((λ ()) , (λ ()))
    (Id-cong _ _ _) → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for ℕ.

  inv-[conv↓]-ℕ :
    ∇ » Γ ⊢ ℕ [conv↓] A →
    A PE.≡ ℕ
  inv-[conv↓]-ℕ ℕ≡A = case inv-[conv↓]-ℕ′ ℕ≡A of λ where
    (inj₁ (_ , A≡ℕ)) → A≡ℕ
    (inj₂ (ℕ≢ℕ , _)) → ⊥-elim (ℕ≢ℕ PE.refl)

opaque

  -- A kind of inversion lemma for Id.

  inv-[conv↓]-Id′ :
    ∇ » Γ ⊢ A [conv↓] B →
    (∃₆ λ A′ t₁ t₂ B′ u₁ u₂ →
     A PE.≡ Id A′ t₁ t₂ ×
     B PE.≡ Id B′ u₁ u₂ ×
    (∇ » Γ ⊢ A′ [conv↑] B′) ×
    ∇ » Γ ⊢ t₁ [conv↑] u₁ ∷ A′ ×
    ∇ » Γ ⊢ t₂ [conv↑] u₂ ∷ A′) ⊎
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
        (λ { (_ , _ , _ , PE.refl) → Id≢ne A-ne PE.refl })
      , (λ { (_ , _ , _ , PE.refl) → Id≢ne B-ne PE.refl })
    (U-refl _)      → inj₂ ((λ ()) , (λ ()))
    (ΠΣ-cong _ _ _) → inj₂ ((λ ()) , (λ ()))
    (Empty-refl _)  → inj₂ ((λ ()) , (λ ()))
    (Unit-refl _ _) → inj₂ ((λ ()) , (λ ()))
    (ℕ-refl _)      → inj₂ ((λ ()) , (λ ()))

opaque

  -- Inversion for Id.

  inv-[conv↓]-Id :
    ∇ » Γ ⊢ Id A t₁ t₂ [conv↓] B →
    ∃₃ λ B′ u₁ u₂ →
    B PE.≡ Id B′ u₁ u₂ ×
    (∇ » Γ ⊢ A [conv↑] B′) ×
    ∇ » Γ ⊢ t₁ [conv↑] u₁ ∷ A ×
    ∇ » Γ ⊢ t₂ [conv↑] u₂ ∷ A
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
    Neutral V ∇ A →
    ∇ » Γ ⊢ t [conv↓] u ∷ A →
    ∃ λ A → ∇ » Γ ⊢ t ~ u ↓ A
  inv-[conv↓]∷-ne A-ne = λ where
    (ne-ins _ _ _ t~u)  → _ , t~u
    (univ _ _ _)        → ⊥-elim (U≢ne     A-ne PE.refl)
    (η-eq _ _ _ _ _)    → ⊥-elim (ΠΣ≢ne    _ A-ne PE.refl)
    (Σ-η _ _ _ _ _ _)   → ⊥-elim (ΠΣ≢ne    _ A-ne PE.refl)
    (Σʷ-ins _ _ _)      → ⊥-elim (ΠΣ≢ne    _ A-ne PE.refl)
    (prod-cong _ _ _ _) → ⊥-elim (ΠΣ≢ne    _ A-ne PE.refl)
    (Empty-ins _)       → ⊥-elim (Empty≢ne A-ne PE.refl)
    (Unitʷ-ins _ _)     → ⊥-elim (Unit≢ne  A-ne PE.refl)
    (η-unit _ _ _ _ _)  → ⊥-elim (Unit≢ne  A-ne PE.refl)
    (starʷ-refl _ _ _)  → ⊥-elim (Unit≢ne  A-ne PE.refl)
    (ℕ-ins _)           → ⊥-elim (ℕ≢ne     A-ne PE.refl)
    (zero-refl _)       → ⊥-elim (ℕ≢ne     A-ne PE.refl)
    (suc-cong _)        → ⊥-elim (ℕ≢ne     A-ne PE.refl)
    (Id-ins _ _)        → ⊥-elim (Id≢ne    A-ne PE.refl)
    (rfl-refl _)        → ⊥-elim (Id≢ne    A-ne PE.refl)

opaque

  -- Inversion for U.

  inv-[conv↓]∷-U :
    ∇ » Γ ⊢ A [conv↓] B ∷ U l →
    ∇ » Γ ⊢ A [conv↓] B
  inv-[conv↓]∷-U (univ _ _ A≡B)    = A≡B
  inv-[conv↓]∷-U (ne-ins _ _ () _)

opaque

  -- Inversion for Π.

  inv-[conv↓]∷-Π :
    ∇ » Γ ⊢ t [conv↓] u ∷ Π p , q ▷ A ▹ B →
    Function⁺ ∇ t × Function⁺ ∇ u ×
    ∇ » Γ ∙ A ⊢ wk1 t ∘⟨ p ⟩ var x0 [conv↑] wk1 u ∘⟨ p ⟩ var x0 ∷ B
  inv-[conv↓]∷-Π (η-eq _ _ t-fun u-fun t0≡u0) = t-fun , u-fun , t0≡u0
  inv-[conv↓]∷-Π (ne-ins _ _ () _)

opaque

  -- Inversion for Σˢ.

  inv-[conv↓]∷-Σˢ :
    ∇ » Γ ⊢ t [conv↓] u ∷ Σˢ p , q ▷ A ▹ B →
    Product⁺ ∇ t × Product⁺ ∇ u ×
    ∇ » Γ ⊢ fst p t [conv↑] fst p u ∷ A ×
    ∇ » Γ ⊢ snd p t [conv↑] snd p u ∷ B [ fst p t ]₀
  inv-[conv↓]∷-Σˢ (Σ-η _ _ t-prod u-prod fst≡fst snd≡snd) =
    t-prod , u-prod , fst≡fst , snd≡snd
  inv-[conv↓]∷-Σˢ (ne-ins _ _ () _)

opaque

  -- Inversion for Σʷ.

  inv-[conv↓]∷-Σʷ :
    ∇ » Γ ⊢ t [conv↓] u ∷ Σʷ p , q ▷ A ▹ B →
    (∃₄ λ p q A B → ∇ » Γ ⊢ t ~ u ↓ Σʷ p , q ▷ A ▹ B) ⊎
    (∃₄ λ t₁ t₂ u₁ u₂ →
     t PE.≡ prodʷ p t₁ t₂ ×
     u PE.≡ prodʷ p u₁ u₂ ×
     ∇ » Γ ⊢ t₁ [conv↑] u₁ ∷ A ×
     ∇ » Γ ⊢ t₂ [conv↑] u₂ ∷ B [ t₁ ]₀)
  inv-[conv↓]∷-Σʷ (Σʷ-ins _ _ t~u) =
    inj₁ (_ , _ , _ , _ , t~u)
  inv-[conv↓]∷-Σʷ (prod-cong _ t₁≡u₁ t₂≡u₂ _) =
    inj₂ (_ , _ , _ , _ , PE.refl , PE.refl , t₁≡u₁ , t₂≡u₂)
  inv-[conv↓]∷-Σʷ (ne-ins _ _ () _)

opaque

  -- Inversion for Empty.

  inv-[conv↓]∷-Empty :
    ∇ » Γ ⊢ t [conv↓] u ∷ Empty →
    ∇ » Γ ⊢ t ~ u ↓ Empty
  inv-[conv↓]∷-Empty (Empty-ins t~u)   = t~u
  inv-[conv↓]∷-Empty (ne-ins _ _ () _)

opaque

  -- Inversion for Unitˢ.

  inv-[conv↓]∷-Unitˢ :
    ∇ » Γ ⊢ t [conv↓] u ∷ Unitˢ l →
    Whnf ∇ t × Whnf ∇ u
  inv-[conv↓]∷-Unitˢ (η-unit _ _ t-whnf u-whnf _) = t-whnf , u-whnf
  inv-[conv↓]∷-Unitˢ (ne-ins _ _ () _)

opaque

  -- Inversion for Unitʷ.

  inv-[conv↓]∷-Unitʷ :
    ∇ » Γ ⊢ t [conv↓] u ∷ Unitʷ l →
    ¬ Unitʷ-η ×
    (∇ » Γ ⊢ t ~ u ↓ Unitʷ l ⊎
     t PE.≡ starʷ l × u PE.≡ starʷ l) ⊎
    Unitʷ-η × Whnf ∇ t × Whnf ∇ u
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
    ∇ » Γ ⊢ t [conv↓] u ∷ Unit s l →
    Unit-with-η s × Whnf ∇ t × Whnf ∇ u ⊎
    ¬ Unit-with-η s ×
    (∇ » Γ ⊢ t ~ u ↓ Unit s l ⊎
     t PE.≡ star s l × u PE.≡ star s l)
  inv-[conv↓]∷-Unit {s = 𝕤} t≡u =
    inj₁ (inj₁ PE.refl , inv-[conv↓]∷-Unitˢ t≡u)
  inv-[conv↓]∷-Unit {s = 𝕨} t≡u =
    case inv-[conv↓]∷-Unitʷ t≡u of λ where
      (inj₂ (η , t-whnf , u-whnf)) →
        inj₁ (inj₂ η , t-whnf , u-whnf)
      (inj₁ (no-η , rest)) →
        inj₂ ([ (λ ()) , no-η ] , rest)

opaque

  -- Inversion for ℕ.

  inv-[conv↓]∷-ℕ :
    ∇ » Γ ⊢ t [conv↓] u ∷ ℕ →
    ∇ » Γ ⊢ t ~ u ↓ ℕ ⊎
    (t PE.≡ zero × u PE.≡ zero) ⊎
    ∃₂ λ t′ u′ → t PE.≡ suc t′ × u PE.≡ suc u′ ×
    ∇ » Γ ⊢ t′ [conv↑] u′ ∷ ℕ
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
    ∇ » Γ ⊢ t [conv↓] u ∷ Id A v w →
    (∃₃ λ A v w → ∇ » Γ ⊢ t ~ u ↓ Id A v w) ⊎
    t PE.≡ rfl × u PE.≡ rfl × ∇ » Γ ⊢ v ≡ w ∷ A
  inv-[conv↓]∷-Id (Id-ins _ t~u)    = inj₁ (_ , _ , _ , t~u)
  inv-[conv↓]∷-Id (rfl-refl v≡w)    = inj₂ (PE.refl , PE.refl , v≡w)
  inv-[conv↓]∷-Id (ne-ins _ _ () _)
