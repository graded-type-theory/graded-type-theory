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

import Definition.Typed.Decidable.Internal.Term
import Definition.Typed.Decidable.Internal.Substitution.Primitive
import Definition.Typed.Decidable.Internal.Weakening
open import Definition.Typed.Restrictions

open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Maybe
open import Tools.Nat
open import Tools.PropositionalEquality as PE
  hiding (cong; cong₂; subst)
open import Tools.Reasoning.PropositionalEquality

private variable
  n                                                      : Nat
  A A₁ A₂ B eq eq₁ eq₂ l l₁ l₂ t t₁ t₂ u u₁ u₂ v w w₁ w₂ : Term _
  σ                                                      : Subst _ _
  ρ                                                      : Wk _ _
  p p′ q q′                                              : M

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

  -- A cast lemma.

  cast : Term n → Term n → Term n → Term n → Term n → Term n
  cast l A B t u =
    subst 𝟙 (U l) (var x0) A B t u

opaque
  unfolding cast

  -- A substitution lemma for cast.

  cast-[] :
    cast l A B t u [ σ ] ≡
    cast (l [ σ ]) (A [ σ ]) (B [ σ ]) (t [ σ ]) (u [ σ ])
  cast-[] {l} {A} {B} {t} {u} {σ} =
    subst 𝟙 (U l) (var x0) A B t u [ σ ]                            ≡⟨ subst-[] ⟩
    subst 𝟙 (U (l [ σ ])) (var x0) (A [ σ ]) (B [ σ ]) (t [ σ ]) (u [ σ ])  ∎

opaque

  -- A weakening lemma for cast.

  wk-cast :
    wk ρ (cast l A B t u) ≡
    cast (wk ρ l) (wk ρ A) (wk ρ B) (wk ρ t) (wk ρ u)
  wk-cast {ρ} {l} {A} {B} {t} {u} =
    wk ρ (cast l A B t u)                                       ≡⟨ wk≡subst _ _ ⟩

    cast l A B t u [ toSubst ρ ]                                ≡⟨ cast-[] ⟩

    cast (l [ toSubst ρ ]) (A [ toSubst ρ ]) (B [ toSubst ρ ])
      (t [ toSubst ρ ]) (u [ toSubst ρ ])                       ≡˘⟨ cong₅ cast (wk≡subst _ _) (wk≡subst _ _) (wk≡subst _ _) (wk≡subst _ _)
                                                                      (wk≡subst _ _) ⟩
    cast (wk ρ l) (wk ρ A) (wk ρ B) (wk ρ t) (wk ρ u)           ∎

opaque

  -- An inverse of cast.

  cast⁻¹ : Term n → Term n → Term n → Term n → Term n → Term n
  cast⁻¹ l A B t u =
    cast l B A (symmetry (U l) A B t) u

opaque
  unfolding cast⁻¹

  -- A substitution lemma for cast⁻¹.

  cast⁻¹-[] :
    cast⁻¹ l A B t u [ σ ] ≡
    cast⁻¹ (l [ σ ]) (A [ σ ]) (B [ σ ]) (t [ σ ]) (u [ σ ])
  cast⁻¹-[] {l} {A} {B} {t} {u} {σ} =
    cast l B A (symmetry (U l) A B t) u [ σ ]                           ≡⟨ cast-[] ⟩

    cast (l [ σ ]) (B [ σ ]) (A [ σ ]) (symmetry (U l) A B t [ σ ])
      (u [ σ ])                                                         ≡⟨ PE.cong₂ (cast _ _ _) symmetry-[] refl ⟩

    cast (l [ σ ]) (B [ σ ]) (A [ σ ])
      (symmetry (U (l [ σ ])) (A [ σ ]) (B [ σ ]) (t [ σ ])) (u [ σ ])  ∎

opaque

  -- A weakening lemma for cast⁻¹.

  wk-cast⁻¹ :
    wk ρ (cast⁻¹ l A B t u) ≡
    cast⁻¹ (wk ρ l) (wk ρ A) (wk ρ B) (wk ρ t) (wk ρ u)
  wk-cast⁻¹ {ρ} {l} {A} {B} {t} {u} =
    wk ρ (cast⁻¹ l A B t u)                                       ≡⟨ wk≡subst _ _ ⟩

    cast⁻¹ l A B t u [ toSubst ρ ]                                ≡⟨ cast⁻¹-[] ⟩

    cast⁻¹ (l [ toSubst ρ ]) (A [ toSubst ρ ]) (B [ toSubst ρ ])
      (t [ toSubst ρ ]) (u [ toSubst ρ ])                         ≡˘⟨ cong₅ cast⁻¹ (wk≡subst _ _) (wk≡subst _ _) (wk≡subst _ _) (wk≡subst _ _)
                                                                        (wk≡subst _ _) ⟩
    cast⁻¹ (wk ρ l) (wk ρ A) (wk ρ B) (wk ρ t) (wk ρ u)           ∎

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

  -- Binary congruence.

  cong₂ :
    M → Term n → Term n → Term n → Term n → Term n → Term n → Term n →
    Term (2+ n) → Term n → Term n → Term n
  cong₂ p A₁ t₁ u₁ A₂ t₂ u₂ B v w₁ w₂ =
    transitivity B (v [ t₁ , t₂ ]₁₀) (v [ u₁ , t₂ ]₁₀) (v [ u₁ , u₂ ]₁₀)
      (cong p A₁ t₁ u₁ B (v [ sgSubst (wk1 t₂) ]) w₁)
      (cong p A₂ t₂ u₂ B (v [ sgSubst u₁ ⇑ ]) w₂)

opaque
  unfolding cong₂

  -- A substitution lemma for cong₂.

  cong₂-[] :
    cong₂ p A₁ t₁ u₁ A₂ t₂ u₂ B v w₁ w₂ [ σ ] ≡
    cong₂ p (A₁ [ σ ]) (t₁ [ σ ]) (u₁ [ σ ]) (A₂ [ σ ]) (t₂ [ σ ])
      (u₂ [ σ ]) (B [ σ ]) (v [ σ ⇑[ 2 ] ]) (w₁ [ σ ]) (w₂ [ σ ])
  cong₂-[] {p} {A₁} {t₁} {u₁} {A₂} {t₂} {u₂} {B} {v} {w₁} {w₂} {σ} =
    transitivity B (v [ t₁ , t₂ ]₁₀) (v [ u₁ , t₂ ]₁₀) (v [ u₁ , u₂ ]₁₀)
      (cong p A₁ t₁ u₁ B (v [ sgSubst (wk1 t₂) ]) w₁)
      (cong p A₂ t₂ u₂ B (v [ sgSubst u₁ ⇑ ]) w₂)
      [ σ ]                                                               ≡⟨ transitivity-[] ⟩

    transitivity (B [ σ ]) (v [ t₁ , t₂ ]₁₀ [ σ ])
      (v [ u₁ , t₂ ]₁₀ [ σ ]) (v [ u₁ , u₂ ]₁₀ [ σ ])
      (cong p A₁ t₁ u₁ B (v [ sgSubst (wk1 t₂) ]) w₁ [ σ ])
      (cong p A₂ t₂ u₂ B (v [ sgSubst u₁ ⇑ ]) w₂ [ σ ])                   ≡⟨ PE.cong₂ (transitivity _ _ _ _)
                                                                               cong-[] cong-[] ⟩
    transitivity (B [ σ ]) (v [ t₁ , t₂ ]₁₀ [ σ ])
      (v [ u₁ , t₂ ]₁₀ [ σ ]) (v [ u₁ , u₂ ]₁₀ [ σ ])
      (cong p (A₁ [ σ ]) (t₁ [ σ ]) (u₁ [ σ ]) (B [ σ ])
         (v [ sgSubst (wk1 t₂) ] [ σ ⇑ ]) (w₁ [ σ ]))
      (cong p (A₂ [ σ ]) (t₂ [ σ ]) (u₂ [ σ ]) (B [ σ ])
         (v [ sgSubst u₁ ⇑ ] [ σ ⇑ ]) (w₂ [ σ ]))                         ≡⟨ cong₅ (transitivity _)
                                                                               ([,]-[]-commute v)
                                                                               ([,]-[]-commute v)
                                                                               ([,]-[]-commute v)
                                                                               (PE.cong (flip (cong _ _ _ _ _) _) $
                                                                                trans (singleSubstLift v _) $
                                                                                PE.cong (v [ _ ⇑[ 2 ] ] [_]₀) $
                                                                                wk1-liftSubst t₂)
                                                                               (PE.cong (flip (cong _ _ _ _ _) _) $
                                                                                trans (substCompEq v) $
                                                                                trans
                                                                                  (flip substVar-to-subst v λ x →
                                                                                   trans (substCompLift x) $
                                                                                   trans
                                                                                     (flip substVar-lift x λ where
                                                                                        x0 → refl
                                                                                        (x +1) → sym $ wk1-sgSubst _ _) $
                                                                                   sym (substCompLift x)) $
                                                                                sym $ substCompEq v) ⟩
    transitivity (B [ σ ])
      (v [ σ ⇑[ 2 ] ] [ t₁ [ σ ] , t₂ [ σ ] ]₁₀)
      (v [ σ ⇑[ 2 ] ] [ u₁ [ σ ] , t₂ [ σ ] ]₁₀)
      (v [ σ ⇑[ 2 ] ] [ u₁ [ σ ] , u₂ [ σ ] ]₁₀)
      (cong p (A₁ [ σ ]) (t₁ [ σ ]) (u₁ [ σ ]) (B [ σ ])
         (v [ σ ⇑[ 2 ] ] [ wk1 (t₂ [ σ ]) ]₀) (w₁ [ σ ]))
      (cong p (A₂ [ σ ]) (t₂ [ σ ]) (u₂ [ σ ]) (B [ σ ])
         (v [ σ ⇑[ 2 ] ] [ sgSubst (u₁ [ σ ]) ⇑ ]) (w₂ [ σ ]))            ∎

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

opaque

  -- A certain formulation of function extensionality.

  Funext : M → M → M → M → Term n → Term n → Term n
  Funext p q p′ q′ l₁ l₂ =
    Π p , q ▷ U l₁ ▹
    Π p′ , q′ ▷ (Π p , q ▷ var x0 ▹ U (wk[ 2 ]′ l₂)) ▹
    let Π-type = Π p , q ▷ var x1 ▹ (var x1 ∘⟨ p ⟩ var x0) in
    Π p′ , q′ ▷ Π-type ▹
    Π p′ , q′ ▷ wk1 Π-type ▹
    Π p′ , q′ ▷
      (Π p , q ▷ var x3 ▹
       Id (var x3 ∘⟨ p ⟩ var x0)
         (var x2 ∘⟨ p ⟩ var x0)
         (var x1 ∘⟨ p ⟩ var x0)) ▹
    Id (wk[ 3 ]′ Π-type) (var x2) (var x1)

opaque
  unfolding Funext

  -- A substitution lemma for Funext.

  Funext-[] :
    Funext p q p′ q′ l₁ l₂ [ σ ] ≡
    Funext p q p′ q′ (l₁ [ σ ]) (l₂ [ σ ])
  Funext-[] {p} {q} {p′} {q′} {l₂} =
    PE.cong (Π p , q ▷_▹_ _) $
    PE.cong (flip (Π p′ , q′ ▷_▹_) _) $
    PE.cong (Π p , q ▷_▹_ _) $
    PE.cong U $
    wk[]′-[⇑] l₂

opaque

  -- A weakening lemma for Funext.

  wk-Funext :
    wk ρ (Funext p q p′ q′ l₁ l₂) ≡
    Funext p q p′ q′ (wk ρ l₁) (wk ρ l₂)
  wk-Funext {ρ} {p} {q} {p′} {q′} {l₁} {l₂} =
    wk ρ (Funext p q p′ q′ l₁ l₂)                           ≡⟨ wk≡subst _ _ ⟩
    Funext p q p′ q′ l₁ l₂ [ toSubst ρ ]                    ≡⟨ Funext-[] ⟩
    Funext p q p′ q′ (l₁ [ toSubst ρ ]) (l₂ [ toSubst ρ ])  ≡˘⟨ PE.cong₂ (Funext _ _ _ _) (wk≡subst _ _) (wk≡subst _ _) ⟩
    Funext p q p′ q′ (wk ρ l₁) (wk ρ l₂)                    ∎

opaque

  -- A certain formulation of universe-polymorphic function
  -- extensionality.

  Poly-funext : M → M → M → M → Term n
  Poly-funext p q p′ q′ =
    Π p , q ▷ Level ▹
    Π p , q ▷ Level ▹
    Funext p q p′ q′ (var x1) (var x0)

opaque
  unfolding Poly-funext

  -- A substitution lemma for Poly-funext.

  Poly-funext-[] : Poly-funext p q p′ q′ [ σ ] ≡ Poly-funext p q p′ q′
  Poly-funext-[] {p} {q} =
    PE.cong (Π p , q ▷_▹_ _) $
    PE.cong (Π p , q ▷_▹_ _) $
    Funext-[]

opaque

  -- A weakening lemma for Poly-funext.

  wk-Poly-funext :
    wk ρ (Poly-funext p q p′ q′) ≡
    Poly-funext p q p′ q′
  wk-Poly-funext {ρ} {p} {q} {p′} {q′} =
    wk ρ (Poly-funext p q p′ q′)         ≡⟨ wk≡subst _ _ ⟩
    Poly-funext p q p′ q′ [ toSubst ρ ]  ≡⟨ Poly-funext-[] ⟩
    Poly-funext p q p′ q′                ∎

opaque

  -- A variant of function extensionality that works in the presence
  -- of equality reflection (see
  -- Definition.Typed.Properties.Admissible.Identity.⊢funext).

  funext : M → M → Term n
  funext p p′ = lam p $ lam p′ $ lam p′ $ lam p′ $ lam p′ rfl

opaque
  unfolding funext

  -- A substitution lemma for funext.

  funext-[] : funext p p′ [ σ ] ≡ funext p p′
  funext-[] = refl

opaque

  -- A variant of universe-polymorphic function extensionality that
  -- works in the presence of equality reflection (see
  -- Definition.Typed.Properties.Admissible.Identity.⊢poly-funext).

  poly-funext : M → M → Term n
  poly-funext p p′ = lam p $ lam p $ funext p p′

opaque
  unfolding poly-funext

  -- A substitution lemma for poly-funext.

  poly-funext-[] : poly-funext p p′ [ σ ] ≡ poly-funext p p′
  poly-funext-[] = PE.cong (lam _ ∘→ lam _) funext-[]

------------------------------------------------------------------------
-- Variants of some of the term formers, intended to be used with the
-- internal type-checker

module Internal (R : Type-restrictions 𝕄) where

  private
    module I =
      Definition.Typed.Decidable.Internal.Term R
    module IS =
      Definition.Typed.Decidable.Internal.Substitution.Primitive R
    module IW =
      Definition.Typed.Decidable.Internal.Weakening R

  private variable
    c                                                : I.Constants
    pᵢ p′ᵢ qᵢ q′ᵢ                                    : I.Termᵍ _
    Aᵢ A₁ᵢ A₂ᵢ Bᵢ eq₁ᵢ eq₂ᵢ
      lᵢ l₁ᵢ l₂ᵢ tᵢ t₁ᵢ t₂ᵢ uᵢ u₁ᵢ u₂ᵢ vᵢ wᵢ w₁ᵢ w₂ᵢ : I.Term _ _
    γ                                                : I.Contexts _

  -- A variant of subst, intended to be used with the internal
  -- type-checker.

  substᵢ :
    I.Termᵍ (c .I.gs) → I.Term c n → I.Term c (1+ n) → I.Term c n →
    I.Term c n → I.Term c n → I.Term c n → I.Term c n
  substᵢ p A B t u v w =
    I.J p I.𝟘 A t (IW.wk[ 1 ] B) w u v

  opaque
    unfolding subst

    -- A translation lemma for substᵢ.

    ⌜substᵢ⌝ :
      I.⌜ substᵢ pᵢ Aᵢ Bᵢ tᵢ uᵢ vᵢ wᵢ ⌝ γ ≡
      subst (I.⟦ pᵢ ⟧ᵍ γ) (I.⌜ Aᵢ ⌝ γ) (I.⌜ Bᵢ ⌝ γ) (I.⌜ tᵢ ⌝ γ)
        (I.⌜ uᵢ ⌝ γ) (I.⌜ vᵢ ⌝ γ) (I.⌜ wᵢ ⌝ γ)
    ⌜substᵢ⌝ = refl

  -- A variant of cast, intended to be used with the internal
  -- type-checker.

  castᵢ :
    I.Term c n → I.Term c n → I.Term c n → I.Term c n → I.Term c n →
    I.Term c n
  castᵢ l A B t u =
    substᵢ I.𝟙 (I.U l) (I.var x0) A B t u

  opaque
    unfolding cast subst

    -- A translation lemma for castᵢ.

    ⌜castᵢ⌝ :
      I.⌜ castᵢ lᵢ Aᵢ Bᵢ tᵢ uᵢ ⌝ γ ≡
      cast (I.⌜ lᵢ ⌝ γ) (I.⌜ Aᵢ ⌝ γ) (I.⌜ Bᵢ ⌝ γ) (I.⌜ tᵢ ⌝ γ)
        (I.⌜ uᵢ ⌝ γ)
    ⌜castᵢ⌝ = refl

  -- A variant of transitivity, intended to be used with the internal
  -- type-checker.

  transitivityᵢ :
    I.Term c n → I.Term c n → I.Term c n → I.Term c n → I.Term c n →
    I.Term c n → I.Term c n
  transitivityᵢ A t u v eq₁ eq₂ =
    substᵢ I.ω A (I.Id (IW.wk[ 1 ] A) (IW.wk[ 1 ] t) (I.var x0)) u v eq₂
      eq₁

  opaque
    unfolding subst transitivity

    -- A translation lemma for transitivityᵢ.

    ⌜transitivityᵢ⌝ :
      I.⌜ transitivityᵢ Aᵢ tᵢ uᵢ vᵢ eq₁ᵢ eq₂ᵢ ⌝ γ ≡
      transitivity (I.⌜ Aᵢ ⌝ γ) (I.⌜ tᵢ ⌝ γ) (I.⌜ uᵢ ⌝ γ) (I.⌜ vᵢ ⌝ γ)
        (I.⌜ eq₁ᵢ ⌝ γ) (I.⌜ eq₂ᵢ ⌝ γ)
    ⌜transitivityᵢ⌝ = refl

  -- A variant of cong, intended to be used with the internal
  -- type-checker.

  congᵢ :
    I.Termᵍ (c .I.gs) → I.Term c n → I.Term c n → I.Term c n →
    I.Term c n → I.Term c (1+ n) → I.Term c n → I.Term c n
  congᵢ p A t u B v w =
    substᵢ p A
      (I.Id (IW.wk[ 1 ] B) (IW.wk[ 1 ] (I.subst v (IS.sgSubst t))) v) t
      u w (I.rfl nothing)

  opaque
    unfolding cong subst

    -- A translation lemma for congᵢ.

    ⌜congᵢ⌝ :
      I.⌜ congᵢ pᵢ Aᵢ tᵢ uᵢ Bᵢ vᵢ wᵢ ⌝ γ ≡
      cong (I.⟦ pᵢ ⟧ᵍ γ) (I.⌜ Aᵢ ⌝ γ) (I.⌜ tᵢ ⌝ γ) (I.⌜ uᵢ ⌝ γ)
        (I.⌜ Bᵢ ⌝ γ) (I.⌜ vᵢ ⌝ γ) (I.⌜ wᵢ ⌝ γ)
    ⌜congᵢ⌝ = refl

  -- A variant of cong₂, intended to be used with the internal
  -- type-checker.

  cong₂ᵢ :
    I.Termᵍ (c .I.gs) → I.Term c n → I.Term c n → I.Term c n →
    I.Term c n → I.Term c n → I.Term c n → I.Term c n →
    I.Term c (2+ n) → I.Term c n → I.Term c n → I.Term c n
  cong₂ᵢ p A₁ t₁ u₁ A₂ t₂ u₂ B v w₁ w₂ =
    transitivityᵢ B (I.subst v (I.cons (IS.sgSubst t₁) t₂))
      (I.subst v (I.cons (IS.sgSubst u₁) t₂))
      (I.subst v (I.cons (IS.sgSubst u₁) u₂))
      (congᵢ p A₁ t₁ u₁ B (I.subst v (IS.sgSubst (IW.wk[ 1 ] t₂))) w₁)
      (congᵢ p A₂ t₂ u₂ B (I.subst v (IS.sgSubst u₁ I.⇑)) w₂)

  opaque
    unfolding cong cong₂ subst transitivity

    -- A translation lemma for cong₂ᵢ.

    ⌜cong₂ᵢ⌝ :
      I.⌜ cong₂ᵢ pᵢ A₁ᵢ t₁ᵢ u₁ᵢ A₂ᵢ t₂ᵢ u₂ᵢ Bᵢ vᵢ w₁ᵢ w₂ᵢ ⌝ γ ≡
      cong₂ (I.⟦ pᵢ ⟧ᵍ γ) (I.⌜ A₁ᵢ ⌝ γ) (I.⌜ t₁ᵢ ⌝ γ) (I.⌜ u₁ᵢ ⌝ γ)
        (I.⌜ A₂ᵢ ⌝ γ) (I.⌜ t₂ᵢ ⌝ γ) (I.⌜ u₂ᵢ ⌝ γ) (I.⌜ Bᵢ ⌝ γ)
        (I.⌜ vᵢ ⌝ γ) (I.⌜ w₁ᵢ ⌝ γ) (I.⌜ w₂ᵢ ⌝ γ)
    ⌜cong₂ᵢ⌝ = refl

  -- A variant of Funext, intended to be used with the internal
  -- type-checker.

  Funextᵢ :
    I.Termᵍ (c .I.gs) → I.Termᵍ (c .I.gs) → I.Termᵍ (c .I.gs) →
    I.Termᵍ (c .I.gs) → I.Term c n → I.Term c n →
    I.Term c n
  Funextᵢ p q p′ q′ l₁ l₂ =
    I.Π p , q ▷ I.U l₁ ▹
    I.Π p′ , q′ ▷ (I.Π p , q ▷ I.var x0 ▹ I.U (IW.wk[ 2 ] l₂)) ▹
    let Π-type = I.Π p , q ▷ I.var x1 ▹ (I.var x1 I.∘⟨ p ⟩ I.var x0)
    in
    I.Π p′ , q′ ▷ Π-type ▹
    I.Π p′ , q′ ▷ IW.wk[ 1 ] Π-type ▹
    I.Π p′ , q′ ▷
      (I.Π p , q ▷ I.var x3 ▹
       I.Id (I.var x3 I.∘⟨ p ⟩ I.var x0)
         (I.var x2 I.∘⟨ p ⟩ I.var x0)
         (I.var x1 I.∘⟨ p ⟩ I.var x0)) ▹
    I.Id (IW.wk[ 3 ] Π-type) (I.var x2) (I.var x1)

  opaque
    unfolding Funext

    -- A translation lemma for Funextᵢ.

    ⌜Funextᵢ⌝ :
      I.⌜ Funextᵢ {n = n} pᵢ qᵢ p′ᵢ q′ᵢ l₁ᵢ l₂ᵢ ⌝ γ ≡
      Funext (I.⟦ pᵢ ⟧ᵍ γ) (I.⟦ qᵢ ⟧ᵍ γ) (I.⟦ p′ᵢ ⟧ᵍ γ) (I.⟦ q′ᵢ ⟧ᵍ γ)
        (I.⌜ l₁ᵢ ⌝ γ) (I.⌜ l₂ᵢ ⌝ γ)
    ⌜Funextᵢ⌝ = refl
