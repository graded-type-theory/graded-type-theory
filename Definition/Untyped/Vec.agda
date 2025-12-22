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

import Definition.Typed.Decidable.Internal.Term 𝕄 as I
import Definition.Typed.Decidable.Internal.Substitution 𝕄 as IS
import Definition.Typed.Decidable.Internal.Weakening 𝕄 as IW

open import Definition.Untyped.Properties M
open import Graded.Mode 𝕄

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
  l : Universe-level
  σ : Subst _ _
  ρ : Wk _ _
  p₁ p₂ r q q₁ q₂ : M
  c : I.Constants
  pᵢ p₁ᵢ p₂ᵢ p₃ᵢ p₄ᵢ p₅ᵢ p₆ᵢ q₁ᵢ q₂ᵢ : I.Termᵍ _
  lᵢ : I.Termˡ _
  sᵢ : I.Termˢ _
  Aᵢ A₁ᵢ A₂ᵢ tᵢ t₁ᵢ t₂ᵢ t₃ᵢ t₄ᵢ uᵢ vᵢ : I.Term _ _
  γ : I.Contexts _

------------------------------------------------------------------------
-- Term formers

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

------------------------------------------------------------------------
-- Some lemmas about the term formers

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

  nil′-wk : wk ρ (nil′ l A) ≡ nil′ l (wk ρ A)
  nil′-wk = refl

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
  unfolding vecrec-nil

  vecrec-nil-subst :
    vecrec-nil l r q P nl [ σ ] ≡ vecrec-nil l r q (P [ σ ⇑[ 2 ] ]) (nl [ σ ])
  vecrec-nil-subst {P} {nl} {σ} =
    flip (cong₂ (λ x y → lam _ (unitrec _ _ _ x _ y)))
      (wk[]′-[⇑] nl) $ begin
      P [ consSubst (wk1Subst idSubst) zero ⇑ ] [ σ ⇑[ 2 ] ]
        ≡⟨ substCompEq P ⟩
      P [ (σ ⇑[ 2 ]) ₛ•ₛ (consSubst (wk1Subst idSubst) zero ⇑) ]
        ≡⟨ substVar-to-subst (λ
            { x0 → refl
            ; (x0 +1) → refl
            ; (x +2) → sym (trans (wk1-liftSubst (wk1 (σ x)))
                         (cong wk1 (trans (wk1-tail (σ x))
                           (sym (wk≡subst _ (σ x))))))}) P ⟩
      P [ (consSubst (wk1Subst idSubst) zero ⇑) ₛ•ₛ (σ ⇑[ 2 ]) ]
        ≡˘⟨ substCompEq P ⟩
      P [ σ ⇑[ 2 ] ] [ consSubst (wk1Subst idSubst) zero ⇑ ] ∎

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
    vecrec′ l p₁ p₂ r q₁ q₂ A P nl cs k xs [ σ ] ≡
    vecrec′ l p₁ p₂ r q₁ q₂ (A [ σ ]) (P [ σ ⇑[ 2 ] ])
      (nl [ σ ]) (cs [ σ ⇑[ 4 ] ]) (k [ σ ]) (xs [ σ ])
  vecrec′-subst {A} =
    cong₃ (λ x y z → natrec _ _ _ (Π _ , _ ▷ x ▹ _) y z _ ∘⟨ _ ⟩ _)
      (trans Vec′-subst (cong (λ x → Vec′ _ x _) (wk[]′-[⇑] A)))
      vecrec-nil-subst vecrec-cons-subst

opaque
  unfolding nil′

  nil′≡star : nil′ l A ≡ star s l
  nil′≡star = refl

opaque
  unfolding cons′

  cons′≡prod : cons′ A k h t ≡ prod s p h t
  cons′≡prod = refl

------------------------------------------------------------------------
-- Variants of some of the term formers, intended to be used with the
-- internal type-checker

-- A variant of Vec′.

Vec′ᵢ :
  I.Termˢ (c .I.ss) → I.Termᵍ (c .I.gs) → I.Termˡ (c .I.ls) →
  (_ _ : I.Term c n) → I.Term c n
Vec′ᵢ s p l A t =
  I.natrec I.𝟘 I.𝟘 I.𝟙
    (I.U l)
    (I.Unit s l)
    (I.ΠΣ⟨ I.BMΣ s ⟩ p , I.𝟘 ▷ IW.wk[ 2 ] A ▹ I.var x1)
    t

opaque
  unfolding Vec′

  -- A translation lemma for Vec′ᵢ.

  ⌜Vec′ᵢ⌝ :
    I.⟦ sᵢ ⟧ˢ γ ≡ s →
    I.⟦ pᵢ ⟧ᵍ γ ≡ p →
    I.⌜ Vec′ᵢ sᵢ pᵢ lᵢ Aᵢ tᵢ ⌝ γ ≡
    Vec′ (I.⟦ lᵢ ⟧ˡ γ) (I.⌜ Aᵢ ⌝ γ) (I.⌜ tᵢ ⌝ γ)
  ⌜Vec′ᵢ⌝ eq₁ eq₂ rewrite eq₁ | eq₂ = refl

-- A variant of Vec.

Vecᵢ :
  I.Termˢ (c .I.ss) → (_ _ _ : I.Termᵍ (c .I.gs)) → I.Termˡ (c .I.ls) →
  I.Term c n
Vecᵢ s p q₁ q₂ l =
  I.lam I.𝟙 (just (q₁ , I.U l)) $
  I.lam I.𝟙 (just (q₂ , I.ℕ)) $
  Vec′ᵢ s p l (I.var x1) (I.var x0)

opaque
  unfolding Vec Vec′

  -- A translation lemma for Vecᵢ.

  ⌜Vecᵢ⌝ :
    I.⟦ sᵢ ⟧ˢ γ ≡ s →
    I.⟦ pᵢ ⟧ᵍ γ ≡ p →
    I.⌜ Vecᵢ {n = n} sᵢ pᵢ q₁ᵢ q₂ᵢ lᵢ ⌝ γ ≡ Vec (I.⟦ lᵢ ⟧ˡ γ)
  ⌜Vecᵢ⌝ eq₁ eq₂ rewrite eq₁ | eq₂ = refl

-- A variant of nil′.

nil′ᵢ : I.Termˢ (c .I.ss) → I.Termˡ (c .I.ls) → I.Term c n
nil′ᵢ s l = I.star s l

opaque
  unfolding nil′

  -- A translation lemma for nil′ᵢ.

  ⌜nil′ᵢ⌝ :
    I.⟦ sᵢ ⟧ˢ γ ≡ s →
    I.⌜ nil′ᵢ {n = n} sᵢ lᵢ ⌝ γ ≡ nil′ (I.⟦ lᵢ ⟧ˡ γ) A
  ⌜nil′ᵢ⌝ eq rewrite eq = refl

-- A variant of nil.

nilᵢ : I.Termˢ (c .I.ss) → I.Termˡ (c .I.ls) → I.Term c n
nilᵢ s l = I.lam I.𝟘 nothing (nil′ᵢ s l)

opaque
  unfolding nil nil′

  -- A translation lemma for nilᵢ.

  ⌜nilᵢ⌝ :
    I.⟦ sᵢ ⟧ˢ γ ≡ s →
    I.⌜ nilᵢ {n = n} sᵢ lᵢ ⌝ γ ≡ nil (I.⟦ lᵢ ⟧ˡ γ)
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
  I.Termˢ (c .I.ss) → I.Termˡ (c .I.ls) →
  (_ _ _ _ _ _ : I.Termᵍ (c .I.gs)) → I.Term c n → I.Term c (2+ n) →
  I.Term c n → I.Term c (4+ n) → (_ _ : I.Term c n) → I.Term c n
vecrecᵢ s l p₁ p₂ p₃ p₄ p₅ p₆ A₁ A₂ t₁ t₂ t₃ t₄ =
  I.natrec p₂ (I.⌜⌞ p₄ ⌟⌝ I.+ p₅) p₃
    (I.Π p₄ , p₆ ▷ Vec′ᵢ s p₁ l (IW.wk[ 1 ] A₁) (I.var x0) ▹ A₂)
    (I.lam p₄ nothing $
     I.unitrec l p₄ p₆
       (I.subst A₂ (I.cons (I.wk1 I.id) I.zero I.⇑)) (I.var x0)
          (IW.wk[ 1 ] t₁))
    (I.lam p₄ nothing $
     I.prodrec p₄ p₁ p₆
       (I.subst A₂ (I.cons (IS.wkSubst 3 I.id) (I.suc (I.var x2)) I.⇑))
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
  unfolding Vec′ vecrec′ vecrec-nil vecrec-cons

  -- A translation lemma for vecrecᵢ.

  ⌜vecrecᵢ⌝ :
    I.⟦ sᵢ ⟧ˢ γ ≡ s →
    I.⟦ p₁ᵢ ⟧ᵍ γ ≡ p →
    I.⌜ vecrecᵢ sᵢ lᵢ p₁ᵢ p₂ᵢ p₃ᵢ p₄ᵢ p₅ᵢ p₆ᵢ A₁ᵢ A₂ᵢ t₁ᵢ t₂ᵢ t₃ᵢ t₄ᵢ ⌝
      γ ≡
    vecrec′ (I.⟦ lᵢ ⟧ˡ γ) (I.⟦ p₂ᵢ ⟧ᵍ γ) (I.⟦ p₃ᵢ ⟧ᵍ γ) (I.⟦ p₄ᵢ ⟧ᵍ γ)
      (I.⟦ p₅ᵢ ⟧ᵍ γ) (I.⟦ p₆ᵢ ⟧ᵍ γ) (I.⌜ A₁ᵢ ⌝ γ) (I.⌜ A₂ᵢ ⌝ γ)
      (I.⌜ t₁ᵢ ⌝ γ) (I.⌜ t₂ᵢ ⌝ γ) (I.⌜ t₃ᵢ ⌝ γ) (I.⌜ t₄ᵢ ⌝ γ)
  ⌜vecrecᵢ⌝ eq₁ eq₂ rewrite eq₁ | eq₂ = refl
