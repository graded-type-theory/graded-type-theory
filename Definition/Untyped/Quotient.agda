------------------------------------------------------------------------
-- Definitions related to quotients
------------------------------------------------------------------------

open import Graded.Modality

module Definition.Untyped.Quotient
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open Modality 𝕄

open import Definition.Untyped M
open import Definition.Untyped.Identity 𝕄
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+; 2+; 3+; 5+)
open import Tools.PropositionalEquality as PE hiding (subst)
open import Tools.Reasoning.PropositionalEquality

private variable
  m n           : Nat
  ∇             : DCon _ _
  ξ             : DExt _ _ _
  Γ Δ Δ′        : Con _ _
  A B C t u v w : Term[ _ ] _
  σ             : Subst _ _
  ρ             : Wk _ _

------------------------------------------------------------------------
-- Quot-rel-Con and Quot-rel-Cons

opaque

  -- The context of the Quot constructor's final argument.

  Quot-rel-Con : Con Term n → Term n → Con Term (2+ n)
  Quot-rel-Con Γ A = Γ ∙ A ∙ wk1 A

-- The context of the Quot constructor's final argument.

Quot-rel-Cons : Cons m n → Term n → Cons m (2+ n)
Quot-rel-Cons Γ A = Γ .defs » Quot-rel-Con (Γ .vars) A

opaque
  unfolding Quot-rel-Con

  -- A substitution lemma for Quot-rel-Con.

  Quot-rel-Con-[] :
    (Δ′ : Con Term n) (A : Term n) →
    ∇ » Δ ∙[ 2 ][ Quot-rel-Con Δ′ A ][ σ ] PE.≡
    ∇ » Quot-rel-Con Δ (A [ σ ])
  Quot-rel-Con-[] _ A =
    PE.cong (_»_ _) (PE.cong (_∙_ _) (wk1-liftSubst A))

opaque
  unfolding Quot-rel-Con inline-Con

  -- Inlining commutes with Quot-rel-Con.

  inline-Quot-rel-Con :
    inline-Con ξ (Quot-rel-Con Γ A) PE.≡
    Quot-rel-Con (inline-Con ξ Γ) (inline ξ A)
  inline-Quot-rel-Con {A} =
    PE.cong (_∙_ _) (PE.sym (wk-inline A))

opaque

  -- A variant of inline-Quot-rel-Con.

  inline-Quot-rel-Cons :
    ∇ » inline-Con ξ (Quot-rel-Con Γ A) PE.≡
    Quot-rel-Cons (∇ » inline-Con ξ Γ) (inline ξ A)
  inline-Quot-rel-Cons =
    PE.cong (_»_ _) inline-Quot-rel-Con

------------------------------------------------------------------------
-- Resp-Con and Resp-Cons

opaque

  -- The context of qrec's "the relation is respected" argument.

  Resp-Con : Con Term n → Term n → Term (2+ n) → Con Term (3+ n)
  Resp-Con Γ A B = Quot-rel-Con Γ A ∙ B

-- The context of qrec's "the relation is respected" argument.

Resp-Cons : Cons m n → Term n → Term (2+ n) → Cons m (3+ n)
Resp-Cons Γ A B = Γ .defs » Resp-Con (Γ .vars) A B

opaque
  unfolding Resp-Con

  -- A substitution lemma for Resp-Con.

  Resp-Con-[] :
    (Δ′ : Con Term n) (A : Term n) (B : Term (2+ n)) →
    ∇ » Δ ∙[ 3 ][ Resp-Con Δ′ A B ][ σ ] PE.≡
    ∇ » Resp-Con Δ (A [ σ ]) (B [ σ ⇑[ 2 ] ])
  Resp-Con-[] Δ′ A B =
    PE.cong (flip _»∙_ _) (Quot-rel-Con-[] Δ′ A)

opaque
  unfolding Resp-Con inline-Con

  -- Inlining commutes with Resp-Con.

  inline-Resp-Con :
    inline-Con ξ (Resp-Con Γ A B) PE.≡
    Resp-Con (inline-Con ξ Γ) (inline ξ A) (inline ξ B)
  inline-Resp-Con {A} =
    PE.cong (flip _∙_ _) (inline-Quot-rel-Con {A = A})

opaque

  -- A variant of inline-Resp-Con.

  inline-Resp-Cons :
    ∇ » inline-Con ξ (Resp-Con Γ A B) PE.≡
    Resp-Cons (∇ » inline-Con ξ Γ) (inline ξ A) (inline ξ B)
  inline-Resp-Cons =
    PE.cong (_»_ _) inline-Resp-Con

------------------------------------------------------------------------
-- Resp-type

opaque

  -- The type of qrec's "the relation is respected" argument.

  Resp-type : Term n → Term (2+ n) → (_ _ : Term (1+ n)) → Term (3+ n)
  Resp-type A B C t =
    Id (C [ 3 ][ class (var x1) ]↑)
      (subst ω (wk[ 3 ]′ (Quot A B)) (C [ 4 ][ var x0 ]↑)
         (class (var x2)) (class (var x1))
         (resp (wk[ 3 ]′ A) (wk (liftn (stepn id 3) 2) B) (var x2)
            (var x1) (var x0))
         (wk[ 2 ]′ t))
      (t [ 3 ][ var x1 ]↑)

opaque
  unfolding Resp-type

  -- A substitution lemma for Resp-type.

  Resp-type-[] :
    Resp-type A B C t [ σ ⇑[ 3 ] ] ≡
    Resp-type (A [ σ ]) (B [ σ ⇑[ 2 ] ]) (C [ σ ⇑ ]) (t [ σ ⇑ ])
  Resp-type-[] {A} {B} {C} {t} {σ} =
    Id (C [ 3 ][ class (var x1) ]↑ [ σ ⇑[ 3 ] ])
      (subst ω (wk[ 3 ]′ (Quot A B)) (C [ 4 ][ var x0 ]↑)
         (class (var x2)) (class (var x1))
         (resp (wk[ 3 ]′ A) (wk (liftn (stepn id 3) 2) B)
            (var x2) (var x1) (var x0))
         (wk[ 2 ]′ t) [ σ ⇑[ 3 ] ])
      (t [ 3 ][ var x1 ]↑ [ σ ⇑[ 3 ] ])                           ≡⟨ cong₃ Id ([][]↑-commutes C) subst-[] ([][]↑-commutes t) ⟩

    Id
      (C [ σ ⇑ ] [ 3 ][ class (var x1) ]↑)
      (subst ω (wk[ 3 ]′ (Quot A B) [ σ ⇑[ 3 ] ])
         (C [ 4 ][ var x0 ]↑ [ σ ⇑[ 4 ] ])
         (class (var x2)) (class (var x1))
         (resp (wk[ 3 ]′ A [ σ ⇑[ 3 ] ])
            (wk (liftn (stepn id 3) 2) B [ σ ⇑[ 5 ] ])
            (var x2) (var x1) (var x0))
         (wk[ 2 ]′ t [ σ ⇑[ 3 ] ]))
      (t [ σ ⇑ ] [ 3 ][ var x1 ]↑)                           ≡⟨ (PE.cong (flip (Id _) _) $
                                                                cong₅
                                                                  (λ A B C Q t →
                                                                     subst ω Q C (class (var x2)) (class (var x1))
                                                                       (resp A B (var x2) (var x1) (var x0)) t)
                                                                  (wk[]′-[⇑] A) (wk-liftn-stepn-[⇑]₂ 2 B)
                                                                  ([][]↑-commutes C)
                                                                  (wk[]′-[⇑] (Quot A B))
                                                                  (wk[]′-[⇑] t)) ⟩
    Id
      (C [ σ ⇑ ] [ 3 ][ class (var x1) ]↑)
      (subst ω (wk[ 3 ]′ (Quot A B [ σ ]))
         (C [ σ ⇑ ] [ 4 ][ var x0 ]↑)
         (class (var x2)) (class (var x1))
         (resp (wk[ 3 ]′ (A [ σ ]))
            (wk (liftn (stepn id 3) 2) (B [ σ ⇑[ 2 ] ]))
            (var x2) (var x1) (var x0))
         (wk[ 2 ]′ (t [ σ ⇑ ])))
      (t [ σ ⇑ ] [ 3 ][ var x1 ]↑)                           ∎

opaque
  unfolding Resp-type

  -- Another substitution lemma for Resp-type.

  Resp-type-[]₂₁₀ :
    Resp-type A B C t [ u , v , w ]₂₁₀ ≡
    Id (C [ class v ]₀)
      (subst ω (Quot A B) C (class u) (class v) (resp A B u v w)
         (t [ u ]₀))
      (t [ v ]₀)
  Resp-type-[]₂₁₀ {A} {B} {C} {t} =
    cong₃ Id ([][]↑-[] 3 C)
      (trans subst-[] $
       cong₆ (subst _)
         (trans (wk[]′-tail (Quot A B)) $
          subst-id _)
         (trans ([][]↑-[,,⇑] 1 C) [0]↑) refl refl
         (cong₅ resp (trans (wk[]′-tail A) (subst-id _))
            (trans (wk-liftn-[⇑] 2 B) ([idSubst⇑ⁿ]≡ 2)) refl refl refl)
         (wk[]′-tail t))
      ([][]↑-[] 3 t)

opaque

  -- A weakening lemma for Resp-type.

  wk-Resp-type :
    wk (liftn ρ 3) (Resp-type A B C t) ≡
    Resp-type (wk ρ A) (wk (liftn ρ 2) B) (wk (lift ρ) C)
      (wk (lift ρ) t)
  wk-Resp-type {ρ} {A} {B} {C} {t} =
    wk (liftn ρ 3) (Resp-type A B C t)                     ≡⟨ wk-liftn 3 ⟩

    Resp-type A B C t [ toSubst ρ ⇑[ 3 ] ]                 ≡⟨ Resp-type-[] ⟩

    Resp-type (A [ toSubst ρ ]) (B [ toSubst ρ ⇑[ 2 ] ])
      (C [ toSubst ρ ⇑ ]) (t [ toSubst ρ ⇑ ])              ≡˘⟨ cong₄ Resp-type (wk-liftn 0) (wk-liftn 2) (wk-liftn 1) (wk-liftn 1) ⟩

    Resp-type (wk ρ A) (wk (liftn ρ 2) B) (wk (lift ρ) C)
      (wk (lift ρ) t)                                      ∎

opaque
  unfolding Resp-type inline

  -- Inlining commutes with Resp-type.

  inline-Resp-type :
    inline ξ (Resp-type A B C t) PE.≡
    Resp-type (inline ξ A) (inline ξ B) (inline ξ C) (inline ξ t)
  inline-Resp-type {ξ} {A} {B} {C} {t} =
    PE.cong₃ Id (inline-[][]↑ C)
      (inline ξ
         (subst ω (wk[ 3 ]′ (Quot A B)) (C [ 4 ][ var x0 ]↑)
            (class (var x2)) (class (var x1))
            (resp (wk[ 3 ]′ A) (wk (liftn (stepn id 3) 2) B) (var x2)
               (var x1) (var x0))
            (wk[ 2 ]′ t))                                               ≡⟨ inline-subst ⟩

       subst ω (inline ξ (wk[ 3 ]′ (Quot A B)))
         (inline ξ (C [ 4 ][ var x0 ]↑))
         (class (var x2)) (class (var x1))
         (resp (inline ξ (wk[ 3 ]′ A))
            (inline ξ (wk (liftn (stepn id 3) 2) B)) (var x2) (var x1)
            (var x0))
         (inline ξ (wk[ 2 ]′ t))                                        ≡⟨ cong₆ (subst _) (sym (wk-inline (Quot A B)))
                                                                             (inline-[][]↑ C) refl refl
                                                                             (cong₅ resp (sym (wk-inline A)) (sym (wk-inline B)) refl refl refl)
                                                                             (sym (wk-inline t)) ⟩
       subst ω (wk[ 3 ]′ (inline ξ (Quot A B)))
         (inline ξ C [ 4 ][ var x0 ]↑) (class (var x2))
         (class (var x1))
         (resp (wk[ 3 ]′ (inline ξ A))
            (wk (liftn (stepn id 3) 2) (inline ξ B)) (var x2) (var x1)
            (var x0))
         (wk[ 2 ]′ (inline ξ t))                                        ∎)
      (inline-[][]↑ t)

------------------------------------------------------------------------
-- Is-set-Con and Is-set-Cons

opaque

  -- The context of qrec's "the target is a set" argument.

  Is-set-Con :
    Con Term n → Term n → Term (2+ n) → Term (1+ n) → Con Term (5+ n)
  Is-set-Con Γ A B C =
    Γ ∙ Quot A B ∙ C ∙ wk1 C ∙
    Id (wk[ 2 ]′ C) (var x1) (var x0) ∙
    Id (wk[ 3 ]′ C) (var x2) (var x1)

-- The context of qrec's "the target is a set" argument.

Is-set-Cons :
  Cons m n → Term n → Term (2+ n) → Term (1+ n) → Cons m (5+ n)
Is-set-Cons Γ A B C =
  Γ .defs » Is-set-Con (Γ .vars) A B C

opaque
  unfolding Is-set-Con

  -- A substitution lemma for Is-set-Con.

  Is-set-Con-[] :
    (Δ′ : Con Term n) (A : Term n) (B : Term (2+ n)) (C : Term (1+ n)) →
    ∇ » Δ ∙[ 5 ][ Is-set-Con Δ′ A B C ][ σ ] PE.≡
    ∇ » Is-set-Con Δ (A [ σ ]) (B [ σ ⇑[ 2 ] ]) (C [ σ ⇑ ])
  Is-set-Con-[] _ _ _ C =
    PE.cong (_»_ _) $
    PE.cong₂ _∙_
      (PE.cong₂ _∙_
         (PE.cong (_∙_ _) (wk1-liftSubst C))
         (PE.cong₃ Id (wk[]′-[⇑] C) PE.refl PE.refl))
      (PE.cong₃ Id (wk[]′-[⇑] C) PE.refl PE.refl)

opaque
  unfolding Is-set-Con inline-Con

  -- Inlining commutes with Is-set-Con.

  inline-Is-set-Con :
    inline-Con ξ (Is-set-Con Γ A B C) PE.≡
    Is-set-Con (inline-Con ξ Γ) (inline ξ A) (inline ξ B) (inline ξ C)
  inline-Is-set-Con {C} =
    PE.sym $
    PE.cong₂ _∙_
      (PE.cong₂ _∙_ (PE.cong (_∙_ _) (wk-inline C)) $
       PE.cong₃ Id (wk-inline C) PE.refl PE.refl)
      (PE.cong₃ Id (wk-inline C) PE.refl PE.refl)

opaque

  -- A variant of inline-Resp-Con.

  inline-Is-set-Cons :
    ∇ » inline-Con ξ (Is-set-Con Γ A B C) PE.≡
    Is-set-Cons (∇ » inline-Con ξ Γ) (inline ξ A) (inline ξ B)
      (inline ξ C)
  inline-Is-set-Cons =
    PE.cong (_»_ _) inline-Is-set-Con

------------------------------------------------------------------------
-- Is-set-type

opaque

  -- The goal of qrec's "the target is a set" argument.

  Is-set-type : Term (1+ n) → Term (5+ n)
  Is-set-type C =
    Id (Id (wk[ 4 ]′ C) (var x3) (var x2)) (var x1) (var x0)

opaque
  unfolding Is-set-type

  -- A substitution lemma for Is-set-type.

  Is-set-type-[] : Is-set-type C [ σ ⇑[ 5 ] ] ≡ Is-set-type (C [ σ ⇑ ])
  Is-set-type-[] {C} =
    cong₃ Id (cong₃ Id (wk[]′-[⇑] C) refl refl) refl refl

opaque

  -- A weakening lemma for Is-set-type.

  wk-Is-set-type :
    wk (liftn ρ 5) (Is-set-type C) ≡ Is-set-type (wk (lift ρ) C)
  wk-Is-set-type {ρ} {C} =
    wk (liftn ρ 5) (Is-set-type C)      ≡⟨ wk-liftn 5 ⟩
    Is-set-type C [ toSubst ρ ⇑[ 5 ] ]  ≡⟨ Is-set-type-[] ⟩
    Is-set-type (C [ toSubst ρ ⇑ ])     ≡˘⟨ PE.cong Is-set-type (wk-liftn 1) ⟩
    Is-set-type (wk (lift ρ) C)         ∎

opaque
  unfolding Is-set-type inline

  -- Inlining commutes with Is-set-type.

  inline-Is-set-type :
    inline ξ (Is-set-type C) PE.≡ Is-set-type (inline ξ C)
  inline-Is-set-type {C} =
    PE.cong₃ Id (PE.cong₃ Id (PE.sym (wk-inline C)) PE.refl PE.refl)
      PE.refl PE.refl
