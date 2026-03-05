------------------------------------------------------------------------
-- Vectors, defined using other types
------------------------------------------------------------------------

-- Typing rules for the term formers defined in this module can be
-- found in Definition.Typed.Properties.Admissible.Vec and, and usage
-- rules can be found in Graded.Derived.Vec.

import Graded.Modality
import Graded.Mode
import Definition.Untyped

module Definition.Untyped.Vec
  {ℓ ℓ′} {M : Set ℓ} {Mode : Set ℓ′}
  (open Graded.Modality M)
  (open Definition.Untyped M)
  (𝕄 : Modality)
  (open Graded.Mode Mode 𝕄)
  (𝐌 : IsMode)
  -- Which Σ and Unit types should be used to define vectors?
  (s : Strength)
  -- The grade of the "heads"
  (p : M)
  where

import Definition.Typed.Decidable.Internal.Term
import Definition.Typed.Decidable.Internal.Substitution.Primitive
import Definition.Typed.Decidable.Internal.Weakening
open import Definition.Typed.Restrictions

open IsMode 𝐌

open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Maybe
open import Tools.Nat hiding (_+_)
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality

open Modality 𝕄

private variable
  n : Nat
  A P k h t nl cs xs : Term _
  l : Lvl _
  σ : Subst _ _
  ρ : Wk _ _
  p₁ p₂ r q q₁ q₂ : M

------------------------------------------------------------------------
-- Term formers

opaque

  Vec′ : Lvl n → (_ _ : Term n) → Term n
  Vec′ l A k =
    natrec 𝟘 𝟘 𝟙
      (U (wk1 l))
      (Lift l (Unit s))
      (Σ⟨ s ⟩ p , 𝟘 ▷ wk₂ A ▹ var x1)
      k

opaque

  Vec : Lvl n → Term n
  Vec l = lam 𝟙 (lam 𝟙 (Vec′ (wk[ 2 ]′ l) (var x1) (var x0)))

opaque

  nil′ : (A : Term n) → Term n
  nil′ _ = lift (star s)

opaque

  nil : Term n
  nil = lam 𝟘 (nil′ (var x0))

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
    (r q : M) →
    (P : Term (2+ n)) →
    (nl : Term n) →
    Term n
  vecrec-nil r q P nl =
    lam r $
    unitrec r q
      (P [ replace₂ zero (lift (var x0)) ]) (lower (var x0)) (wk1 nl)

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
    (p₁ p₂ r q₁ q₂ : M)
    (l : Lvl n)
    (A : Term n)
    (P : Term (2+ n))
    (nl : Term n)
    (cs : Term (4+ n))
    (k xs : Term n) → Term n
  vecrec′ p₁ p₂ r q₁ q₂ l A P nl cs k xs =
    natrec p₁ (r + q₁) p₂
      (Π r , q₂ ▷ Vec′ (wk1 l) (wk1 A) (var x0) ▹ P)
      (vecrec-nil r q₂ P nl)
      (vecrec-cons r q₂ P cs)
      k
    ∘⟨ r ⟩ xs

------------------------------------------------------------------------
-- Some lemmas about the term formers

opaque
  unfolding Vec′

  Vec′-subst : (Vec′ l A k) [ σ ] ≡ Vec′ (l [ σ ]) (A [ σ ]) (k [ σ ])
  Vec′-subst {l} {A} =
    cong₄ (natrec 𝟘 𝟘 𝟙) (cong U $ wk1-liftSubst l) refl
      (cong (flip (Σ⟨ s ⟩ p , 𝟘 ▷_▹_) _) $
       wk[]′-[⇑] A)
      refl

opaque

  Vec′-wk : wk ρ (Vec′ l A k) ≡ Vec′ (wk ρ l) (wk ρ A) (wk ρ k)
  Vec′-wk {ρ} {l} {A} {k} = begin
    wk ρ (Vec′ l A k)                                           ≡⟨ wk≡subst _ _ ⟩
    (Vec′ l A k) [ toSubst ρ ]                                  ≡⟨ Vec′-subst ⟩
    Vec′ (l [ toSubst ρ ]) (A [ toSubst ρ ]) (k [ toSubst ρ ])  ≡˘⟨ cong₃ Vec′ (wk≡subst _ _) (wk≡subst _ _) (wk≡subst _ _) ⟩
    Vec′ (wk ρ l) (wk ρ A) (wk ρ k)                             ∎

opaque
  unfolding nil′

  nil′-wk : wk ρ (nil′ A) ≡ nil′ (wk ρ A)
  nil′-wk = refl

opaque
  unfolding nil′

  nil′-subst : (nil′ A) [ σ ] ≡ nil′ (A [ σ ])
  nil′-subst = refl

opaque
  unfolding cons′

  cons′-subst :
    (cons′ A k h t) [ σ ] ≡ cons′ (A [ σ ]) (k [ σ ]) (h [ σ ]) (t [ σ ])
  cons′-subst = refl

opaque
  unfolding vecrec-nil replace₂

  vecrec-nil-subst :
    vecrec-nil r q P nl [ σ ] ≡ vecrec-nil r q (P [ σ ⇑[ 2 ] ]) (nl [ σ ])
  vecrec-nil-subst {P} {nl} {σ} =
    flip (cong₂ (λ x y → lam _ (unitrec _ _ x _ y)))
      (wk[]′-[⇑] nl)
      (P [ replace₂ zero (lift (var x0)) ] [ σ ⇑[ 2 ] ]       ≡⟨ substCompEq P ⟩

       P [ (σ ⇑[ 2 ]) ₛ•ₛ replace₂ zero (lift (var x0)) ]     ≡⟨ (flip substVar-to-subst P λ {
                                                                    x0        → refl;
                                                                    (x0 +1)   → refl;
                                                                    (x +1 +1) →
         wk[ 2 ] (σ x)                                                ≡⟨ wk[]≡wk[]′ ⟩
         wk[ 2 ]′ (σ x)                                               ≡⟨ wk≡subst _ _ ⟩
         σ x [ toSubst (stepn id 2) ]                                 ≡⟨⟩
         σ x [ replace₂ zero (lift (var x0)) ₛ• stepn id 2 ]          ≡˘⟨ subst-wk (σ _) ⟩
         wk[ 2 ]′ (σ x) [ replace₂ zero (lift (var x0)) ]             ≡˘⟨ cong _[ _ ] $ wk[]≡wk[]′ {t = σ _} ⟩
         wk[ 2 ] (σ x) [ replace₂ zero (lift (var x0)) ]              ∎ }) ⟩

       P [ replace₂ zero (lift (var x0)) ₛ•ₛ (σ ⇑[ 2 ]) ]     ≡˘⟨ substCompEq P ⟩

       P [ σ ⇑[ 2 ] ] [ replace₂ zero (lift (var x0)) ]       ∎)

opaque
  unfolding vecrec-cons

  vecrec-cons-subst :
    vecrec-cons r q P cs [ σ ⇑[ 2 ] ] ≡ vecrec-cons r q (P [ σ ⇑[ 2 ] ]) (cs [ σ ⇑[ 4 ] ])
  vecrec-cons-subst {P} {cs} {σ} =
    cong₂ (λ x y → lam _ (prodrec _ _ _ x _ y))
      (begin
        P [ consSubst (wkSubst 3 idSubst) (suc (var x2)) ⇑ ] [ σ ⇑[ 4 ] ]
          ≡⟨ substCompEq P ⟩
        P [ (σ ⇑[ 4 ]) ₛ•ₛ (consSubst (wkSubst 3 idSubst) (suc (var x2)) ⇑) ]
          ≡⟨ substVar-to-subst (λ
               { x0 → refl
               ; (_+1 x0) → refl
               ; (x +2) → sym (trans (wk1-liftSubst (wk1 (σ x)))
                            (cong wk1 (trans (wk1-tail (σ x))
                              (sym (trans wk[]≡wk[]′ (wk≡subst _ (σ x)))))))}) P ⟩
        P [ (consSubst (wkSubst 3 idSubst) (suc (var x2)) ⇑) ₛ•ₛ (σ ⇑[ 2 ]) ]
          ≡˘⟨ substCompEq P ⟩
        P [ σ ⇑[ 2 ] ] [ consSubst (wkSubst 3 idSubst) (suc (var x2)) ⇑ ] ∎)
      (begin
        cs [ consSubst (consSubst (consSubst (consSubst (wkSubst 5 idSubst) (var x4)) (var x1)) (var x0)) (var x3 ∘⟨ _ ⟩ var x0) ] [ σ ⇑[ 5 ] ]
          ≡⟨ substCompEq cs ⟩
        cs [ (σ ⇑[ 5 ]) ₛ•ₛ consSubst (consSubst (consSubst (consSubst (wkSubst 5 idSubst) (var x4)) (var x1)) (var x0)) (var x3 ∘⟨ _ ⟩ var x0) ]
          ≡⟨ substVar-to-subst (λ
              { x0 → refl ; (_+1 x0) → refl ; (x0 +2) → refl ; (_+1 x0 +2) → refl
              ; ((x +2) +2) → sym (trans (wk1-tail (wk[ 3 ] (σ x))) (trans (wk1-tail (wk[ 2 ] (σ x)))
                               (trans (wk1-tail (wk1 (σ x))) (trans (wk1-tail (σ x))
                               (sym (trans wk[]≡wk[]′ (wk≡subst _ (σ x))))))))}) cs ⟩
        cs [ consSubst (consSubst (consSubst (consSubst (wkSubst 5 idSubst) (var x4)) (var x1)) (var x0)) (var x3 ∘⟨ _ ⟩ var x0) ₛ•ₛ (σ ⇑[ 4 ]) ]
          ≡˘⟨ substCompEq cs ⟩
        cs [ σ ⇑[ 4 ] ] [ consSubst (consSubst (consSubst (consSubst (wkSubst 5 idSubst) (var x4)) (var x1)) (var x0)) (var x3 ∘⟨ _ ⟩ var x0) ] ∎)

opaque
  unfolding vecrec′

  vecrec′-subst :
    vecrec′ p₁ p₂ r q₁ q₂ l A P nl cs k xs [ σ ] ≡
    vecrec′ p₁ p₂ r q₁ q₂ (l [ σ ]) (A [ σ ]) (P [ σ ⇑[ 2 ] ])
      (nl [ σ ]) (cs [ σ ⇑[ 4 ] ]) (k [ σ ]) (xs [ σ ])
  vecrec′-subst {l} {A} =
    cong₃ (λ x y z → natrec _ _ _ (Π _ , _ ▷ x ▹ _) y z _ ∘⟨ _ ⟩ _)
      (trans Vec′-subst $
       cong₂ (λ l A → Vec′ l A _) (wk1-liftSubst l) (wk[]′-[⇑] A))
      vecrec-nil-subst vecrec-cons-subst

opaque
  unfolding nil′

  nil′≡star : nil′ A ≡ lift (star s)
  nil′≡star = refl

opaque
  unfolding cons′

  cons′≡prod : cons′ A k h t ≡ prod s p h t
  cons′≡prod = refl

------------------------------------------------------------------------
-- Variants of some of the term formers, intended to be used with the
-- internal type-checker

module Internal (R : Type-restrictions 𝕄) where

  private
    module I =
      Definition.Typed.Decidable.Internal.Term 𝐌 R
    module IS =
      Definition.Typed.Decidable.Internal.Substitution.Primitive 𝐌 R
    module IW =
      Definition.Typed.Decidable.Internal.Weakening 𝐌 R

  private variable
    c : I.Constants
    pᵢ p₁ᵢ p₂ᵢ p₃ᵢ p₄ᵢ p₅ᵢ p₆ᵢ q₁ᵢ q₂ᵢ : I.Termᵍ _
    sᵢ : I.Termˢ _
    Aᵢ A₁ᵢ A₂ᵢ tᵢ t₁ᵢ t₂ᵢ t₃ᵢ t₄ᵢ uᵢ vᵢ : I.Term _ _
    lᵢ : I.Lvl _ _
    γ : I.Contexts _

  -- A variant of Vec′.

  Vec′ᵢ :
    I.Termˢ (c .I.ss) → I.Termᵍ (c .I.gs) → I.Lvl c n →
    (_ _ : I.Term c n) → I.Term c n
  Vec′ᵢ s p l A t =
    I.natrec I.𝟘 I.𝟘 I.𝟙
      (I.U (IW.wk[ 1 ] l))
      (I.Lift l (I.Unit s))
      (I.ΠΣ⟨ I.BMΣ s ⟩ p , I.𝟘 ▷ IW.wk[ 2 ] A ▹ I.var x1)
      t

  opaque
    unfolding Vec′

    -- A translation lemma for Vec′ᵢ.

    ⌜Vec′ᵢ⌝ :
      I.⟦ sᵢ ⟧ˢ γ ≡ s →
      I.⟦ pᵢ ⟧ᵍ γ ≡ p →
      I.⌜ Vec′ᵢ sᵢ pᵢ lᵢ Aᵢ tᵢ ⌝ γ ≡
      Vec′ (I.⌜ lᵢ ⌝ γ) (I.⌜ Aᵢ ⌝ γ) (I.⌜ tᵢ ⌝ γ)
    ⌜Vec′ᵢ⌝ eq₁ eq₂ rewrite eq₁ | eq₂ = refl

  -- A variant of Vec.

  Vecᵢ :
    I.Termˢ (c .I.ss) → (_ _ _ : I.Termᵍ (c .I.gs)) → I.Lvl c n →
    I.Term c n
  Vecᵢ s p q₁ q₂ l =
    I.lam I.𝟙 (just (q₁ , I.U l)) $
    I.lam I.𝟙 (just (q₂ , I.ℕ)) $
    Vec′ᵢ s p (IW.wk[ 2 ] l) (I.var x1) (I.var x0)

  opaque
    unfolding Vec Vec′

    -- A translation lemma for Vecᵢ.

    ⌜Vecᵢ⌝ :
      I.⟦ sᵢ ⟧ˢ γ ≡ s →
      I.⟦ pᵢ ⟧ᵍ γ ≡ p →
      I.⌜ Vecᵢ {n = n} sᵢ pᵢ q₁ᵢ q₂ᵢ lᵢ ⌝ γ ≡ Vec (I.⌜ lᵢ ⌝ γ)
    ⌜Vecᵢ⌝ eq₁ eq₂ rewrite eq₁ | eq₂ = refl

  -- A variant of nil′.

  nil′ᵢ : I.Termˢ (c .I.ss) → I.Term c n
  nil′ᵢ s = I.lift nothing (I.star s)

  opaque
    unfolding nil′

    -- A translation lemma for nil′ᵢ.

    ⌜nil′ᵢ⌝ :
      I.⟦ sᵢ ⟧ˢ γ ≡ s →
      I.⌜ nil′ᵢ {n = n} sᵢ ⌝ γ ≡ nil′ A
    ⌜nil′ᵢ⌝ eq rewrite eq = refl

  -- A variant of nil.

  nilᵢ : I.Termˢ (c .I.ss) → I.Term c n
  nilᵢ s = I.lam I.𝟘 nothing (nil′ᵢ s)

  opaque
    unfolding nil nil′

    -- A translation lemma for nilᵢ.

    ⌜nilᵢ⌝ :
      I.⟦ sᵢ ⟧ˢ γ ≡ s →
      I.⌜ nilᵢ {n = n} sᵢ ⌝ γ ≡ nil
    ⌜nilᵢ⌝ eq rewrite eq = refl

  -- A variant of cons′.

  cons′ᵢ :
    I.Termˢ (c .I.ss) → I.Termᵍ (c .I.gs) → (_ _ : I.Term c n) →
    I.Term c n
  cons′ᵢ s p t u = I.prod s p nothing t u

  opaque
    unfolding cons′

    -- A translation lemma for cons′ᵢ.

    ⌜cons′ᵢ⌝ :
      I.⟦ sᵢ ⟧ˢ γ ≡ s →
      I.⟦ pᵢ ⟧ᵍ γ ≡ p →
      I.⌜ cons′ᵢ sᵢ pᵢ uᵢ vᵢ ⌝ γ ≡ cons′ A t (I.⌜ uᵢ ⌝ γ) (I.⌜ vᵢ ⌝ γ)
    ⌜cons′ᵢ⌝ eq₁ eq₂ rewrite eq₁ | eq₂ = refl

  -- A variant of cons.

  consᵢ : I.Termˢ (c .I.ss) → I.Termᵍ (c .I.gs) → I.Term c n
  consᵢ s p =
    I.lam I.𝟘 nothing $ I.lam I.𝟘 nothing $
    I.lam I.𝟙 nothing $ I.lam I.𝟙 nothing $
    cons′ᵢ s p (I.var x1) (I.var x0)

  opaque
    unfolding cons cons′

    -- A translation lemma for consᵢ.

    ⌜consᵢ⌝ :
      I.⟦ sᵢ ⟧ˢ γ ≡ s →
      I.⟦ pᵢ ⟧ᵍ γ ≡ p →
      I.⌜ consᵢ {n = n} sᵢ pᵢ ⌝ γ ≡ cons
    ⌜consᵢ⌝ eq₁ eq₂ rewrite eq₁ | eq₂ = refl

  -- A variant of vecrec′.

  vecrecᵢ :
    I.Termˢ (c .I.ss) →
    (_ _ _ _ _ _ : I.Termᵍ (c .I.gs)) → I.Lvl c n → I.Term c n →
    I.Term c (2+ n) → I.Term c n → I.Term c (4+ n) →
    (_ _ : I.Term c n) → I.Term c n
  vecrecᵢ s p₁ p₂ p₃ p₄ p₅ p₆ l A₁ A₂ t₁ t₂ t₃ t₄ =
    I.natrec p₂ (p₄ I.+ p₅) p₃
      (I.Π p₄ , p₆ ▷
         Vec′ᵢ s p₁ (IW.wk[ 1 ] l) (IW.wk[ 1 ] A₁) (I.var x0) ▹ A₂)
      (I.lam p₄ nothing $
       I.unitrec p₄ p₆
         (I.subst A₂
            (I.cons (I.cons (IS.wkSubst 2 I.id) I.zero)
               (I.lift nothing (I.var x0))))
         (I.lower (I.var x0)) (IW.wk[ 1 ] t₁))
      (I.lam p₄ nothing $
       I.prodrec p₄ p₁ p₆
         (I.subst A₂
            (I.cons (IS.wkSubst 3 I.id) (I.suc (I.var x2)) I.⇑))
         (I.var x0)
         (I.subst t₂
            (I.cons
               (I.cons
                  (I.cons (I.cons (IS.wkSubst 5 I.id) (I.var x4))
                     (I.var x1))
                  (I.var x0))
               (I.var x3 I.∘⟨ p₄ ⟩ I.var x0))))
      t₃ I.∘⟨ p₄ ⟩
    t₄

  opaque
    unfolding Vec′ replace₂ vecrec′ vecrec-nil vecrec-cons

    -- A translation lemma for vecrecᵢ.

    ⌜vecrecᵢ⌝ :
      I.⟦ sᵢ ⟧ˢ γ ≡ s →
      I.⟦ p₁ᵢ ⟧ᵍ γ ≡ p →
      I.⌜ vecrecᵢ sᵢ p₁ᵢ p₂ᵢ p₃ᵢ p₄ᵢ p₅ᵢ p₆ᵢ
            lᵢ A₁ᵢ A₂ᵢ t₁ᵢ t₂ᵢ t₃ᵢ t₄ᵢ ⌝
        γ ≡
      vecrec′ (I.⟦ p₂ᵢ ⟧ᵍ γ) (I.⟦ p₃ᵢ ⟧ᵍ γ) (I.⟦ p₄ᵢ ⟧ᵍ γ)
        (I.⟦ p₅ᵢ ⟧ᵍ γ) (I.⟦ p₆ᵢ ⟧ᵍ γ) (I.⌜ lᵢ ⌝ γ) (I.⌜ A₁ᵢ ⌝ γ)
        (I.⌜ A₂ᵢ ⌝ γ) (I.⌜ t₁ᵢ ⌝ γ) (I.⌜ t₂ᵢ ⌝ γ) (I.⌜ t₃ᵢ ⌝ γ)
        (I.⌜ t₄ᵢ ⌝ γ)
    ⌜vecrecᵢ⌝ eq₁ eq₂ rewrite eq₁ | eq₂ = refl
