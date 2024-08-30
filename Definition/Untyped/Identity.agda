------------------------------------------------------------------------
-- Definitions related to Id
------------------------------------------------------------------------

-- Typing rules for the terms given in this module can be found in
-- Definition.Typed.Properties.Admissible.Identity.

open import Graded.Modality

module Definition.Untyped.Identity
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open Modality 𝕄

open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.PropositionalEquality as PE hiding (cong; subst)
open import Tools.Reasoning.PropositionalEquality

private variable
  n                      : Nat
  A B eq eq₁ eq₂ t u v w : Term _
  σ                      : Subst _ _
  l                      : Universe-level
  p q                    : M

opaque

  -- Substitutivity.

  subst :
    M →
    Term n → Term (1+ n) → Term n → Term n → Term n → Term n → Term n
  subst p A B t u v w =
    J p 𝟘 A t (wk1 B) w u v

opaque
  unfolding subst

  -- A substitution lemma for subst.

  subst-[] :
    subst p A B t u v w [ σ ] ≡
    subst p (A [ σ ]) (B [ liftSubst σ ]) (t [ σ ]) (u [ σ ]) (v [ σ ])
      (w [ σ ])
  subst-[] {B} =
    cong₄ (J _ _ _ _) (wk1-liftSubst B) refl refl refl

opaque

  -- A cast lemma.

  cast : Universe-level → Term n → Term n → Term n → Term n → Term n
  cast l A B t u =
    subst 𝟙 (U l) (var x0) A B t u

opaque
  unfolding cast

  -- A substitution lemma for cast.

  cast-[] :
    cast l A B t u [ σ ] ≡
    cast l (A [ σ ]) (B [ σ ]) (t [ σ ]) (u [ σ ])
  cast-[] {l} {A} {B} {t} {u} {σ} =
    subst 𝟙 (U l) (var x0) A B t u [ σ ]                            ≡⟨ subst-[] ⟩
    subst 𝟙 (U l) (var x0) (A [ σ ]) (B [ σ ]) (t [ σ ]) (u [ σ ])  ∎

opaque

  -- Symmetry.

  symmetry :
    Term n → Term n → Term n → Term n → Term n
  symmetry A t u eq =
    subst ω A (Id (wk1 A) (var x0) (wk1 t)) t u eq rfl

opaque
  unfolding symmetry

  -- A substitution lemma for symmetry.

  symmetry-[] :
    symmetry A t u eq [ σ ] ≡
    symmetry (A [ σ ]) (t [ σ ]) (u [ σ ]) (eq [ σ ])
  symmetry-[] {A} {t} {u} {eq} {σ} =
    subst ω A (Id (wk1 A) (var x0) (wk1 t)) t u eq rfl [ σ ]         ≡⟨ subst-[] ⟩

    subst ω (A [ σ ])
      (Id (wk1 A [ liftSubst σ ]) (var x0) (wk1 t [ liftSubst σ ]))
      (t [ σ ]) (u [ σ ]) (eq [ σ ]) rfl                             ≡⟨ cong₅ (subst _ _)
                                                                          (cong₃ Id (wk1-liftSubst A) refl (wk1-liftSubst t))
                                                                          refl refl refl refl ⟩
    subst ω (A [ σ ])
      (Id (wk1 (A [ σ ])) (var x0) (wk1 (t [ σ ])))
      (t [ σ ]) (u [ σ ]) (eq [ σ ]) rfl                             ∎

opaque

  -- Transitivity.

  transitivity :
    Term n → Term n → Term n → Term n → Term n → Term n → Term n
  transitivity A t u v eq₁ eq₂ =
    subst ω A (Id (wk1 A) (wk1 t) (var x0)) u v eq₂ eq₁

opaque
  unfolding transitivity

  -- A substitution lemma for transitivity.

  transitivity-[] :
    transitivity A t u v eq₁ eq₂ [ σ ] ≡
    transitivity (A [ σ ]) (t [ σ ]) (u [ σ ]) (v [ σ ]) (eq₁ [ σ ])
      (eq₂ [ σ ])
  transitivity-[] {A} {t} {u} {v} {eq₁} {eq₂} {σ} =
    subst ω A (Id (wk1 A) (wk1 t) (var x0)) u v eq₂ eq₁ [ σ ]        ≡⟨ subst-[] ⟩

    subst ω (A [ σ ])
      (Id (wk1 A [ liftSubst σ ]) (wk1 t [ liftSubst σ ]) (var x0))
      (u [ σ ]) (v [ σ ]) (eq₂ [ σ ]) (eq₁ [ σ ])                    ≡⟨ cong₅ (subst _ _)
                                                                          (cong₃ Id (wk1-liftSubst A) (wk1-liftSubst t) refl)
                                                                          refl refl refl refl ⟩
    subst ω (A [ σ ]) (Id (wk1 (A [ σ ])) (wk1 (t [ σ ])) (var x0))
      (u [ σ ]) (v [ σ ]) (eq₂ [ σ ]) (eq₁ [ σ ])                    ∎

opaque

  -- A simplification lemma for transitivity and symmetry.

  transitivity-symmetryˡ :
    Term n → Term n → Term n → Term n → Term n
  transitivity-symmetryˡ A t u eq =
    J ω ω A t
      (Id (Id (wk2 A) (var x1) (var x1))
         (transitivity (wk2 A) (var x1) (wk2 t) (var x1)
            (symmetry (wk2 A) (wk2 t) (var x1) (var x0))
            (var x0))
         rfl)
      rfl u eq

opaque

  -- Congruence.

  cong :
    M → Term n → Term n → Term n → Term n → Term (1+ n) → Term n →
    Term n
  cong p A t u B v w =
    subst p A (Id (wk1 B) (wk1 (v [ t ]₀)) v) t u w rfl

opaque
  unfolding cong

  -- A substitution lemma for cong.

  cong-[] :
    cong p A t u B v w [ σ ] ≡
    cong p (A [ σ ]) (t [ σ ]) (u [ σ ]) (B [ σ ]) (v [ liftSubst σ ])
      (w [ σ ])
  cong-[] {p} {A} {t} {u} {B} {v} {w} {σ} =
    subst p A (Id (wk1 B) (wk1 (v [ t ]₀)) v) t u w rfl [ σ ]        ≡⟨ subst-[] ⟩

    subst p (A [ σ ])
      (Id (wk1 B [ liftSubst σ ]) (wk1 (v [ t ]₀) [ liftSubst σ ])
         (v [ liftSubst σ ]))
      (t [ σ ]) (u [ σ ]) (w [ σ ]) rfl                              ≡⟨ cong₅ (subst _ _)
                                                                          (cong₃ Id
                                                                             (wk1-liftSubst B)
                                                                             (
      wk1 (v [ t ]₀) [ liftSubst σ ]                                          ≡⟨ wk1-liftSubst (v [ _ ]₀) ⟩
      wk1 (v [ t ]₀ [ σ ])                                                    ≡⟨ PE.cong wk1 $ singleSubstLift v _ ⟩
      wk1 (v [ liftSubst σ ] [ t [ σ ] ]₀)                                    ∎)
                                                                             refl)
                                                                          refl refl refl refl ⟩
    subst p (A [ σ ])
      (Id (wk1 (B [ σ ])) (wk1 (v [ liftSubst σ ] [ t [ σ ] ]₀))
         (v [ liftSubst σ ]))
      (t [ σ ]) (u [ σ ]) (w [ σ ]) rfl                              ∎

opaque

  -- If two functions are equal, then they are pointwise equal.

  pointwise-equality :
    M → M → Term n → Term (1+ n) → Term n → Term n → Term n → Term n →
    Term n
  pointwise-equality p q A B t u v w =
    cong ω (Π p , q ▷ A ▹ B) t u (B [ w ]₀) (var x0 ∘⟨ p ⟩ wk1 w) v

opaque
  unfolding pointwise-equality

  -- A substitution lemma for pointwise-equality.

  pointwise-equality-[] :
    pointwise-equality p q A B t u v w [ σ ] ≡
    pointwise-equality p q (A [ σ ]) (B [ liftSubst σ ]) (t [ σ ])
      (u [ σ ]) (v [ σ ]) (w [ σ ])
  pointwise-equality-[] {p} {q} {A} {B} {t} {u} {v} {w} {σ} =
    cong ω (Π p , q ▷ A ▹ B) t u (B [ w ]₀) (var x0 ∘⟨ p ⟩ wk1 w) v
      [ σ ]                                                               ≡⟨ cong-[] ⟩

    cong ω (Π p , q ▷ A [ σ ] ▹ (B [ liftSubst σ ])) (t [ σ ]) (u [ σ ])
      (B [ w ]₀ [ σ ]) (var x0 ∘⟨ p ⟩ wk1 w [ liftSubst σ ]) (v [ σ ])    ≡⟨ cong₃ (cong _ _ _ _)
                                                                               (singleSubstLift B _)
                                                                               (PE.cong (_∘⟨_⟩_ _ _) $ wk1-liftSubst w)
                                                                               refl ⟩
    cong ω (Π p , q ▷ A [ σ ] ▹ (B [ liftSubst σ ])) (t [ σ ]) (u [ σ ])
      (B [ liftSubst σ ] [ w [ σ ] ]₀) (var x0 ∘⟨ p ⟩ wk1 (w [ σ ]))
      (v [ σ ])                                                           ∎

opaque

  -- Uniqueness of identity proofs (UIP)

  uip : M → M → Term n → Term n → Term n → Term n → Term n → Term n
  uip p q A t u eq₁ eq₂ =
    transitivity
      (Id A t u)
      eq₁
      (transitivity A t u u eq₂
         (transitivity A u t u (symmetry A t u eq₁) eq₁))
      eq₂
      (J ω ω A t
         (Id
            (Id (wk2 A) (wk2 t) (var x1))
            (var x0)
            (transitivity (wk2 A) (wk2 t) (wk2 u) (var x1) (wk2 eq₂)
               (transitivity (wk2 A) (wk2 u) (wk2 t) (var x1)
                  (symmetry (wk2 A) (wk2 t) (wk2 u) (wk2 eq₁))
                  (var x0))))
         (K ω A t (Id (Id (wk1 A) (wk1 t) (wk1 t)) rfl (var x0)) rfl
            (transitivity A t u t eq₂
               (transitivity A u t t (symmetry A t u eq₁) rfl)))
         u eq₁)
      (cong ω (Id A u u) (transitivity A u t u (symmetry A t u eq₁) eq₁)
         rfl (Id A t u)
         (transitivity (wk1 A) (wk1 t) (wk1 u) (wk1 u) (wk1 eq₂)
            (var x0))
         (transitivity-symmetryˡ A t u eq₁))
