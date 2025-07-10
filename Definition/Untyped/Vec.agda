------------------------------------------------------------------------
-- Vectors, defined using other types
------------------------------------------------------------------------

-- Typing rules for the term formers defined in this module can be
-- found in Definition.Typed.Properties.Admissible.Vec and, and usage
-- rules can be found in Graded.Derived.Vec.

import Graded.Modality
import Definition.Untyped

module Definition.Untyped.Vec
  {ℓ} {M : Set ℓ}
  (open Graded.Modality M)
  (open Definition.Untyped M)
  (𝕄 : Modality)
  -- Which Σ and Unit types should be used to define vectors?
  (s : Strength)
  -- The grade of the "heads"
  (p : M)
  where

open import Definition.Untyped.Properties M
open import Graded.Mode 𝕄

open import Tools.Fin
open import Tools.Function
open import Tools.Nat hiding (_+_)
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality

open Modality 𝕄

private variable
  n : Nat
  A k h t : Term _
  l : Universe-level
  σ : Subst _ _
  ρ : Wk _ _

opaque

  Vec′ : Universe-level → (A k : Term n) → Term n
  Vec′ l A k =
    natrec 𝟘 𝟘 𝟙
      (U l)
      (Unit s l)
      (Σ⟨ s ⟩ p , 𝟘 ▷ wk₂ A ▹ var x1)
      k

opaque

  Vec : Universe-level → Term n
  Vec l = lam 𝟙 (lam 𝟙 (Vec′ l (var x1) (var x0)))

opaque

  nil′ : Universe-level → (A : Term n) → Term n
  nil′ l _ = star s l

opaque

  nil : Universe-level → Term n
  nil l = lam 𝟘 (nil′ l (var x0))

opaque

  cons′ : (A k h t : Term n) → Term n
  cons′ _ _ h t = prod s p h t

opaque

  cons : Term n
  cons =
    lam 𝟘 $
    lam 𝟘 $
    lam 𝟙 $
    lam 𝟙 $
    cons′ (var x3) (var x2) (var x1) (var x0)

opaque

  vecrec-nil :
    {n : Nat} →
    Universe-level →
    (r q : M) →
    (P : Term (2+ n)) →
    (nl : Term n) →
    Term n
  vecrec-nil l r q P nl =
    lam r $
    unitrec l r q (P [ consSubst (wk1Subst idSubst) zero ⇑ ]) (var x0) (wk1 nl)

opaque

  vecrec-cons :
    {n : Nat} →
    (r q : M)
    (P : Term (2+ n)) →
    (cs : Term (4+ n)) →
    Term (2+ n)
  vecrec-cons r q P cs =
    lam r $
    prodrec r p q
      (P [ consSubst (wkSubst 3 idSubst) (suc (var x2)) ⇑ ])
      (var x0)
      (cs [ consSubst (consSubst (consSubst (consSubst (wkSubst 5 idSubst)
              (var x4)) (var x1)) (var x0)) (var x3 ∘⟨ r ⟩ var x0) ])

opaque

  vecrec′ :
    {n : Nat} →
    Universe-level →
    (p₁ p₂ r q₁ q₂ : M)
    (A : Term n)
    (P : Term (2+ n))
    (nl : Term n)
    (cs : Term (4+ n))
    (k xs : Term n) → Term n
  vecrec′ l p₁ p₂ r q₁ q₂ A P nl cs k xs =
    natrec p₁ (⌜ ⌞ r ⌟ ⌝ + q₁) p₂
      (Π r , q₂ ▷ Vec′ l (wk1 A) (var x0) ▹ P)
      (vecrec-nil l r q₂ P nl)
      (vecrec-cons r q₂ P cs)
      k
    ∘⟨ r ⟩ xs

opaque
  unfolding Vec′

  Vec′-subst : (Vec′ l A k) [ σ ] ≡ Vec′ l (A [ σ ]) (k [ σ ])
  Vec′-subst {A} =
    cong (λ x → natrec 𝟘 𝟘 𝟙 _ _ (Σ⟨ s ⟩ _ , _ ▷ x ▹ _) _)
      (wk[]′-[⇑] A)

opaque

  Vec′-wk : wk ρ (Vec′ l A k) ≡ Vec′ l (wk ρ A) (wk ρ k)
  Vec′-wk {ρ} {l} {A} {k} = begin
    wk ρ (Vec′ l A k)                          ≡⟨ wk≡subst _ _ ⟩
    (Vec′ l A k) [ toSubst ρ ]                 ≡⟨ Vec′-subst ⟩
    Vec′ l (A [ toSubst ρ ]) (k [ toSubst ρ ]) ≡˘⟨ cong₂ (Vec′ l) (wk≡subst _ _) (wk≡subst _ _) ⟩
    Vec′ l (wk ρ A) (wk ρ k)                   ∎

opaque
  unfolding nil′

  nil′-subst : (nil′ l A) [ σ ] ≡ nil′ l (A [ σ ])
  nil′-subst = refl

opaque
  unfolding cons′

  cons′-subst :
    (cons′ A k h t) [ σ ] ≡ cons′ (A [ σ ]) (k [ σ ]) (h [ σ ]) (t [ σ ])
  cons′-subst = refl

opaque
  unfolding nil′

  nil′≡star : nil′ l A ≡ star s l
  nil′≡star = refl

opaque
  unfolding cons′

  cons′≡prod : cons′ A k h t ≡ prod s p h t
  cons′≡prod = refl
