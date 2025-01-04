------------------------------------------------------------------------
-- Types can be lifted to larger universes
------------------------------------------------------------------------

-- Typing rules for the term formers defined in this module can be
-- found in Definition.Typed.Properties.Admissible.Lift, and usage
-- rules can be found in Graded.Derived.Lift.

open import Graded.Modality

module Definition.Untyped.Lift
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open Modality 𝕄

open import Definition.Untyped M hiding (lift)
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sigma 𝕄
open import Definition.Untyped.Unit 𝕄

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality

private variable
  n     : Nat
  A l t u : Term _
  σ     : Subst _ _
  s     : Strength
  q r   : M

opaque

  -- Lifting.

  Lift : Strength → Term n → Term n → Term n
  Lift s l A = Σ⟨ s ⟩ 𝟙 , 𝟘 ▷ A ▹ Unit s (wk1 l)

opaque
  unfolding Lift

  -- A substitution lemma for Lift.

  Lift-[] : Lift s l A [ σ ] ≡ Lift s l (A [ σ ])
  Lift-[] = {!   !}

opaque

  -- A constructor for Lift.

  lift : Strength → Term n → Term n → Term n
  lift s l t = prod s 𝟙 t (star s l)

opaque
  unfolding lift

  -- A substitution lemma for lift.

  lift-[] : lift s l t [ σ ] ≡ lift s l (t [ σ ])
  lift-[] = {!   !}

opaque

  -- An eliminator for Lift.

  liftrec :
    M → M → Strength → Term n →
    Term (1+ n) → Term (1+ n) → Term n → Term n
  liftrec r q s l A t u =
    {!   !}
    -- prodrec⟨ s ⟩ r 𝟙 q A u
    --   (unitrec⟨ s ⟩ r q l
    --      (A [ consSubst (wkSubst 3 idSubst)
    --             (prod s 𝟙 (var x2) (var x0)) ])
    --      (var x0) (wk1 t))

{-
opaque
  unfolding liftrec

  -- A substitution lemma for liftrec.

  liftrec-[] :
    liftrec r q s l A t u [ σ ] ≡
    liftrec r q s l (A [ σ ⇑ ]) (t [ σ ⇑ ]) (u [ σ ])
  liftrec-[] {r} {q} {s} {l} {A} {t} {u} {σ} =
    liftrec r q s l A t u [ σ ]                        ≡⟨⟩

    prodrec⟨ s ⟩ r 𝟙 q A u
      (unitrec⟨ s ⟩ l r q
         (A [ consSubst (wkSubst 3 idSubst)
                (prod s 𝟙 (var x2) (var x0)) ])
         (var x0) (wk1 t)) [ σ ]                       ≡⟨ prodrec⟨⟩-[] ⟩

    prodrec⟨ s ⟩ r 𝟙 q (A [ σ ⇑ ]) (u [ σ ])
      (unitrec⟨ s ⟩ l r q
         (A [ consSubst (wkSubst 3 idSubst)
                (prod s 𝟙 (var x2) (var x0)) ])
         (var x0) (wk1 t) [ σ ⇑ ⇑ ])                   ≡⟨ cong (prodrec⟨ _ ⟩ _ _ _ _ _)
                                                          unitrec⟨⟩-[] ⟩
    prodrec⟨ s ⟩ r 𝟙 q (A [ σ ⇑ ]) (u [ σ ])
      (unitrec⟨ s ⟩ l r q
         (A [ consSubst (wkSubst 3 idSubst)
                (prod s 𝟙 (var x2) (var x0)) ]
            [ σ ⇑ ⇑ ⇑ ])
         (var x0) (wk1 t [ σ ⇑ ⇑ ]))                   ≡⟨ cong (prodrec⟨ _ ⟩ _ _ _ _ _) $
                                                          cong₃ (unitrec⟨ _ ⟩ _ _ _)
                                                            lemma₂ refl (wk1-liftSubst t) ⟩
    prodrec⟨ s ⟩ r 𝟙 q (A [ σ ⇑ ]) (u [ σ ])
      (unitrec⟨ s ⟩ l r q
         (A [ σ ⇑ ]
            [ consSubst (wkSubst 3 idSubst)
                (prod s 𝟙 (var x2) (var x0)) ])
         (var x0) (wk1 (t [ σ ⇑ ])))                   ≡⟨⟩

    liftrec r q s l (A [ σ ⇑ ]) (t [ σ ⇑ ]) (u [ σ ])  ∎
    where
    lemma₁ :
      (t : Term n) →
      wk[ 3 ] t ≡
      wk1 t
        [ consSubst (wkSubst 3 idSubst) (prod s 𝟙 (var x2) (var x0)) ]
    lemma₁ t =
      wk[ 3 ] t                                                         ≡⟨ wk[]≡[] 3 ⟩

      t [ wkSubst 3 idSubst ]                                           ≡˘⟨ cong _[ _ ] $ wk-id t ⟩

      wk id t [ wkSubst 3 idSubst ]                                     ≡˘⟨ step-consSubst t ⟩

      wk1 t
        [ consSubst (wkSubst 3 idSubst) (prod s 𝟙 (var x2) (var x0)) ]  ∎

    lemma₂ :
      A [ consSubst (wkSubst 3 idSubst) (prod s 𝟙 (var x2) (var x0)) ]
        [ σ ⇑ ⇑ ⇑ ] ≡
      A [ σ ⇑ ]
        [ consSubst (wkSubst 3 idSubst) (prod s 𝟙 (var x2) (var x0)) ]
    lemma₂ =
      A [ consSubst (wkSubst 3 idSubst) (prod s 𝟙 (var x2) (var x0)) ]
        [ σ ⇑ ⇑ ⇑ ]                                                       ≡⟨ substCompEq A ⟩

      A [ (σ ⇑ ⇑ ⇑) ₛ•ₛ
          consSubst (wkSubst 3 idSubst) (prod s 𝟙 (var x2) (var x0)) ]    ≡⟨ (flip substVar-to-subst A λ where
                                                                                x0     → refl
                                                                                (_ +1) → lemma₁ _) ⟩
      A [ consSubst (wkSubst 3 idSubst) (prod s 𝟙 (var x2) (var x0)) ₛ•ₛ
          (σ ⇑) ]                                                         ≡˘⟨ substCompEq A ⟩

      A [ σ ⇑ ]
        [ consSubst (wkSubst 3 idSubst) (prod s 𝟙 (var x2) (var x0)) ]    ∎
-}
