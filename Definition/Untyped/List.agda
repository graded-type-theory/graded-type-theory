------------------------------------------------------------------------
-- Lists defined using vectors
------------------------------------------------------------------------

-- Typing rules for the term formers defined in this module can be
-- found in Definition.Typed.Properties.Admissible.List and usage
-- rules can be found in Graded.Derived.List

import Graded.Modality
import Graded.Mode
import Definition.Untyped

module Definition.Untyped.List
  {ℓ ℓ′} {M : Set ℓ} {Mode : Set ℓ′}
  (open Graded.Modality M)
  (open Definition.Untyped M)
  (𝕄 : Modality)
  (open Graded.Mode Mode 𝕄)
  (𝐌 : IsMode)
  -- The grade of the "heads" and grade of the length component
  (pₕ pₗ : M)
  where

import Definition.Typed.Decidable.Internal.Term
import Definition.Typed.Decidable.Internal.Substitution.Primitive
import Definition.Typed.Decidable.Internal.Weakening
open import Definition.Typed.Restrictions

-- Use vectors defined using weak Unit and Σ-types.
import Definition.Untyped.Vec 𝕄 𝐌 𝕨 pₕ as V

open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Maybe
open import Tools.Nat using (Nat; 1+; 3+)
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
  p₁ p₂ p₃ q r₁ r₂ : M

------------------------------------------------------------------------
-- Term formers

opaque

  -- The type of lists as a term former
  -- Lists are encoded as a tuple where the first component
  -- represents the length (assigned grade pₗ) and the second
  -- is a vector (of that length).

  List : Lvl n → Term n → Term n
  List l A =
    Σʷ pₗ , 𝟙 ▷ Lift l ℕ ▹ V.Vec′ (wk1 l) (wk1 A) (lower (var x0))

opaque
  unfolding List

  -- Unfolding of List

  List≡ :
    List l A ≡
    Σʷ pₗ , 𝟙 ▷ Lift l ℕ ▹ V.Vec′ (wk1 l) (wk1 A) (lower (var x0))
  List≡ = refl

opaque
  unfolding List

  -- Applying a weakening to List

  List-wk : wk ρ (List l A) ≡ List (wk ρ l) (wk ρ A)
  List-wk =
    cong (Σʷ pₗ , 𝟙 ▷_▹_ _) $ trans V.Vec′-wk $ sym $
    cong₂ (λ l A → V.Vec′ l A _)
      (wk1-wk≡lift-wk1 _ _) (wk1-wk≡lift-wk1 _ _)

opaque
  unfolding List

  -- Applying a substitution to List

  List-subst : (List l A) [ σ ] ≡ List (l [ σ ]) (A [ σ ])
  List-subst {l} {A} {σ} =
    cong (Σʷ pₗ , 𝟙 ▷_▹_ _) $ begin
      V.Vec′ (wk1 l) (wk1 A) (lower (var x0)) [ σ ⇑ ]          ≡⟨ V.Vec′-subst ⟩
      V.Vec′ (wk1 l [ σ ⇑ ]) (wk1 A [ σ ⇑ ]) (lower (var x0))  ≡⟨ cong₂ (λ l A → V.Vec′ l A _) (wk1-liftSubst l) (wk1-liftSubst A) ⟩
      V.Vec′ (wk1 (l [ σ ])) (wk1 (A [ σ ])) (lower (var x0))  ∎

opaque

  -- The empty list as a term former

  nil : (A : Term n) → Term n
  nil A = prodʷ pₗ (lift zero) (V.nil′ A)

opaque
  unfolding nil

  -- unfolding of nil

  nil≡ : nil A ≡ prodʷ pₗ (lift zero) (V.nil′ A)
  nil≡ = refl

opaque

  -- cons as a term former

  cons : Lvl n → (_ _ _ : Term n) → Term n
  cons l A h t =
    prodrec 𝟙 pₗ 𝟘 (wk1 (List l A)) t
      (prodʷ pₗ (lift (suc (lower (var x1))))
         (V.cons′ (wk₂ A) (var x1) (wk₂ h) (var x0)))

opaque
  unfolding cons

  -- unfolding of cons

  cons≡ :
    cons l A h t ≡
    prodrec 𝟙 pₗ 𝟘 (wk1 (List l A)) t
      (prodʷ pₗ (lift (suc (lower (var x1))))
         (V.cons′ (wk₂ A) (var x1) (wk₂ h) (var x0)))
  cons≡ = refl

opaque

  -- Applying a substition to cons

  cons-subst :
    cons l A h t [ σ ] ≡ cons (l [ σ ]) (A [ σ ]) (h [ σ ]) (t [ σ ])
  cons-subst {l} {A} {h} {t} {σ} = begin
    cons l A h t [ σ ]                                                 ≡⟨ cong (_[ σ ]) cons≡ ⟩

    prodrec 𝟙 pₗ 𝟘 (wk1 (List l A)) t
      (prodʷ pₗ (lift (suc (lower (var x1))))
         (V.cons′ (wk₂ A) (var x1) (wk₂ h) (var x0)))
      [ σ ]                                                            ≡⟨ cong (prodrec 𝟙 pₗ 𝟘 _ _ ∘→ prodʷ pₗ _) V.cons′-subst ⟩

    prodrec 𝟙 pₗ 𝟘 (wk1 (List l A) [ σ ⇑ ]) (t [ σ ])
      (prodʷ pₗ (lift (suc (lower (var x1))))
         (V.cons′ (wk₂ A [ σ ⇑[ 2 ] ]) (var x1) (wk₂ h [ σ ⇑[ 2 ] ])
            (var x0)))                                                 ≡⟨ cong₃ (λ x y z → prodrec 𝟙 pₗ 𝟘 x _ (prodʷ pₗ _ (V.cons′ y _ z _)))
                                                                            (wk1-liftSubst (List l A)) (wk[]′-[⇑] A) (wk[]′-[⇑] h) ⟩
    prodrec 𝟙 pₗ 𝟘 (wk1 (List l A [ σ ])) (t [ σ ])
      (prodʷ pₗ (lift (suc (lower (var x1))))
         (V.cons′ (wk₂ (A [ σ ])) (var x1) (wk₂ (h [ σ ])) (var x0)))  ≡⟨ cong (λ x → prodrec 𝟙 pₗ 𝟘 (wk1 x) _ _) List-subst ⟩

    prodrec 𝟙 pₗ 𝟘 (wk1 (List (l [ σ ]) (A [ σ ]))) (t [ σ ])
      (prodʷ pₗ (lift (suc (lower (var x1))))
         (V.cons′ (wk₂ (A [ σ ])) (var x1) (wk₂ (h [ σ ])) (var x0)))  ≡˘⟨ cons≡ ⟩

    cons (l [ σ ]) (A [ σ ]) (h [ σ ]) (t [ σ ])                       ∎

opaque

  -- The eliminator for lists as a term former
  --
  -- The grades can be interpreted as follows:
  -- r₁ represents the total uses of the list
  -- r₂ represents the total uses of the vector component of the list
  -- p₁ represents the uses of the tail in cs
  -- p₂ represents the uses of the uses of the recursive call in cs
  -- q represents the uses of the list in the motive
  -- See also Graded.Derived.List.▸listrec′

  listrec :
    ∀ {n} →
    (r₁ r₂ p₁ p₂ q : M)
    (l : Lvl n)
    (A : Term n)
    (P : Term (1+ n))
    (nl : Term n)
    (cs : Term (3+ n))
    (xs : Term n) → Term n
  listrec r₁ r₂ p₁ p₂ q l A P nl cs xs =
    prodrec r₁ pₗ q P xs
      (V.vecrec′ (p₁ · pₗ) p₂ r₂ (q · pₗ) q (wk₂ l)
        (wk₂ A) (P [ 4 ][ prodʷ pₗ (lift (var x1)) (var x0) ]↑) (wk₂ nl)
        (cs [ flip consSubst (var x0) $
              flip consSubst (prodʷ pₗ (lift (var x3)) (var x1)) $
              flip consSubst (var x2) $
              wkSubst 6 idSubst
            ])
        (lower (var x1)) (var x0))

opaque
  unfolding listrec

  -- Unfolding listrec

  listrec≡ :
    listrec r₁ r₂ p₁ p₂ q l A P nl cs xs ≡
    prodrec r₁ pₗ q P xs
      (V.vecrec′ (p₁ · pₗ) p₂ r₂ (q · pₗ) q (wk₂ l)
        (wk₂ A) (P [ 4 ][ prodʷ pₗ (lift (var x1)) (var x0) ]↑) (wk₂ nl)
        (cs [ flip consSubst (var x0) $
              flip consSubst (prodʷ pₗ (lift (var x3)) (var x1)) $
              flip consSubst (var x2) $
              wkSubst 6 idSubst
            ])
        (lower (var x1)) (var x0))
  listrec≡ = refl

------------------------------------------------------------------------
-- Variants of the term formers, intended to be used with the internal
-- type-checker

module Internal (R : Type-restrictions 𝕄) where

  private
    module I =
      Definition.Typed.Decidable.Internal.Term 𝐌 R
    module IS =
      Definition.Typed.Decidable.Internal.Substitution.Primitive 𝐌 R
    module IW =
      Definition.Typed.Decidable.Internal.Weakening 𝐌 R
    module IV = V.Internal R

  private variable
    c : I.Constants
    p₁ᵢ p₂ᵢ p₃ᵢ p₄ᵢ p₅ᵢ pₕᵢ pₗᵢ : I.Termᵍ _
    Aᵢ A₁ᵢ A₂ᵢ t₁ᵢ t₂ᵢ t₃ᵢ : I.Term _ _
    lᵢ : I.Lvl _ _
    γ : I.Contexts _

  -- A variant of List.

  Listᵢ :
    (_ _ : I.Termᵍ (c .I.gs)) → I.Lvl c n → I.Term c n → I.Term c n
  Listᵢ pₕ pₗ l A =
    I.Σʷ pₗ , I.𝟙 ▷ I.Lift l I.ℕ ▹
    IV.Vec′ᵢ I.𝕨 pₕ (IW.wk[ 1 ] l) (IW.wk[ 1 ] A) (I.lower (I.var x0))

  opaque
    unfolding List V.Vec′

    -- A translation lemma for Listᵢ.

    ⌜Listᵢ⌝ :
      I.⟦ pₕᵢ ⟧ᵍ γ ≡ pₕ →
      I.⟦ pₗᵢ ⟧ᵍ γ ≡ pₗ →
      I.⌜ Listᵢ pₕᵢ pₗᵢ lᵢ Aᵢ ⌝ γ ≡
      List (I.⌜ lᵢ ⌝ γ) (I.⌜ Aᵢ ⌝ γ)
    ⌜Listᵢ⌝ eq₁ eq₂ rewrite eq₁ | eq₂ = refl

  -- A variant of nil.

  nilᵢ : (_ _ : I.Termᵍ (c .I.gs)) → I.Lvl c n → I.Term c n → I.Term c n
  nilᵢ pₗ pₕ l A =
    I.prod I.𝕨 pₗ
      (just
         (I.𝟙 ,
          IV.Vec′ᵢ I.𝕨 pₕ (IW.wk[ 1 ] l) (IW.wk[ 1 ] A)
            (I.lower (I.var x0))))
      (I.lift (just l) I.zero) (IV.nil′ᵢ I.𝕨)

  opaque
    unfolding nil V.nil′

    -- A translation lemma for nilᵢ.

    ⌜nilᵢ⌝ :
      I.⟦ pₗᵢ ⟧ᵍ γ ≡ pₗ →
      I.⌜ nilᵢ {n = n} pₗᵢ pₕᵢ lᵢ Aᵢ ⌝ γ ≡ nil (I.⌜ Aᵢ ⌝ γ)
    ⌜nilᵢ⌝ eq rewrite eq = refl

  -- A variant of cons.

  consᵢ :
    (_ _ : I.Termᵍ (c .I.gs)) → I.Lvl c n → (_ _ _ : I.Term c n) →
    I.Term c n
  consᵢ pₕ pₗ l A t₁ t₂ =
    I.prodrec I.𝟙 pₗ I.𝟘 (IW.wk[ 1 ] (Listᵢ pₕ pₗ l A)) t₂
      (I.prod I.𝕨 pₗ nothing
         (I.lift nothing (I.suc (I.lower (I.var x1))))
         (IV.cons′ᵢ I.𝕨 pₕ (IW.wk[ 2 ] t₁) (I.var x0)))

  opaque
    unfolding List V.Vec′ cons V.cons′

    -- A translation lemma for consᵢ.

    ⌜consᵢ⌝ :
      I.⟦ pₕᵢ ⟧ᵍ γ ≡ pₕ →
      I.⟦ pₗᵢ ⟧ᵍ γ ≡ pₗ →
      I.⌜ consᵢ pₕᵢ pₗᵢ lᵢ Aᵢ t₁ᵢ t₂ᵢ ⌝ γ ≡
      cons (I.⌜ lᵢ ⌝ γ) (I.⌜ Aᵢ ⌝ γ) (I.⌜ t₁ᵢ ⌝ γ) (I.⌜ t₂ᵢ ⌝ γ)
    ⌜consᵢ⌝ eq₁ eq₂ rewrite eq₁ | eq₂ = refl

  -- A variant of listrec.

  listrecᵢ :
    (_ _ _ _ _ _ _ : I.Termᵍ (c .I.gs)) → I.Lvl c n → I.Term c n →
    I.Term c (1+ n) → I.Term c n → I.Term c (3+ n) → I.Term c n →
    I.Term c n
  listrecᵢ pₕ pₗ p₁ p₂ p₃ p₄ p₅ l A₁ A₂ t₁ t₂ t₃ =
    I.prodrec p₁ pₗ p₅ A₂ t₃
      (IV.vecrecᵢ I.𝕨 pₕ (p₃ I.· pₗ) p₄ p₂ (p₅ I.· pₗ) p₅ (IW.wk[ 2 ] l)
        (IW.wk[ 2 ] A₁)
        (I.subst A₂
           (I.cons (IS.wkSubst 4 I.id)
              (I.prod I.𝕨 pₗ nothing (I.lift nothing (I.var x1))
                 (I.var x0))))
        (IW.wk[ 2 ] t₁)
        (I.subst t₂
           (I.cons
              (I.cons (I.cons (IS.wkSubst 6 I.id) (I.var x2))
                 (I.prod I.𝕨 pₗ
                    (just
                       (I.𝟙 ,
                        IV.Vec′ᵢ I.𝕨 pₕ (IW.wk[ 7 ] l) (IW.wk[ 7 ] A₁)
                          (I.lower (I.var x0))))
                    (I.lift (just (IW.wk[ 6 ] l)) (I.var x3))
                    (I.var x1)))
              (I.var x0)))
        (I.lower (I.var x1)) (I.var x0))

  opaque
    unfolding
      V.Vec′ listrec replace₂ V.vecrec′ V.vecrec-nil V.vecrec-cons

    -- A translation lemma for listrecᵢ.

    ⌜listrecᵢ⌝ :
      I.⟦ pₕᵢ ⟧ᵍ γ ≡ pₕ →
      I.⟦ pₗᵢ ⟧ᵍ γ ≡ pₗ →
      I.⌜ listrecᵢ pₕᵢ pₗᵢ p₁ᵢ p₂ᵢ p₃ᵢ p₄ᵢ p₅ᵢ lᵢ A₁ᵢ A₂ᵢ t₁ᵢ t₂ᵢ t₃ᵢ ⌝
        γ ≡
      listrec (I.⟦ p₁ᵢ ⟧ᵍ γ) (I.⟦ p₂ᵢ ⟧ᵍ γ) (I.⟦ p₃ᵢ ⟧ᵍ γ)
        (I.⟦ p₄ᵢ ⟧ᵍ γ) (I.⟦ p₅ᵢ ⟧ᵍ γ) (I.⌜ lᵢ ⌝ γ) (I.⌜ A₁ᵢ ⌝ γ)
        (I.⌜ A₂ᵢ ⌝ γ) (I.⌜ t₁ᵢ ⌝ γ) (I.⌜ t₂ᵢ ⌝ γ) (I.⌜ t₃ᵢ ⌝ γ)
    ⌜listrecᵢ⌝ eq₁ eq₂ rewrite eq₁ | eq₂ = refl
