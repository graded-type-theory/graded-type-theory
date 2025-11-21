------------------------------------------------------------------------
-- Typing, equality and reduction rules related to Bool
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Definition.Untyped.Bool
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Bool
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Definition.Untyped.Bool 𝕄)
  (open Modality 𝕄)
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  -- It is assumed that the modality has an nr function.
  ⦃ has-nr : Has-nr M semiring-with-meet ⦄
  -- It is assumed that certain Σ-types are allowed.
  (Σ-ok : Σʷ-allowed ω Boolᵍ)
  -- It is assumed that weak unit types are allowed.
  (Unitʷ-ok : Unitʷ-allowed)
  where

open import Definition.Typed R
open import Definition.Typed.Properties.Admissible.Bool.OK
  R Unitʷ-ok
open import Definition.Typed.Properties.Admissible.Empty R
open import Definition.Typed.Properties.Admissible.Level R
open import Definition.Typed.Properties.Admissible.Nat R
open import Definition.Typed.Properties.Admissible.Pi R
open import Definition.Typed.Properties.Admissible.Sigma R
open import Definition.Typed.Properties.Admissible.Unit R
open import Definition.Typed.Properties.Admissible.Var R
open import Definition.Typed.Properties.Reduction R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Reasoning.Reduction R
open import Definition.Typed.Reasoning.Type R
open import Definition.Typed.Substitution.Primitive R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Weakening R

open import Definition.Untyped M
open import Definition.Untyped.Empty 𝕄
open import Definition.Untyped.Nat 𝕄
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+; 2+; 3+)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private variable
  ∇                                 : DCon (Term 0) _
  k                                 : Nat
  Δ                                 : Con Term _
  Γ                                 : Cons _ _
  A A₁ A₂ B t t₁ t₂ u u₁ u₂ v v₁ v₂ : Term _
  p                                 : M

------------------------------------------------------------------------
-- Typing rules for Bool, true and false

opaque
  unfolding Bool

  -- A typing rule for Bool.

  ⊢Bool∷U :
    ⊢ Γ →
    Γ ⊢ Bool ∷ U zeroᵘ
  ⊢Bool∷U ⊢Γ =
    ΠΣⱼ (⊢zeroᵘ ⊢Γ) (ℕⱼ ⊢Γ) (⊢OK∷U (var₀ (⊢ℕ ⊢Γ))) Σ-ok

opaque

  -- A typing rule for Bool.

  ⊢Bool :
    ⊢ Γ →
    Γ ⊢ Bool
  ⊢Bool = univ ∘→ ⊢Bool∷U

opaque
  unfolding Bool true

  -- A typing rule for true.

  ⊢true :
    ⊢ Γ →
    Γ ⊢ true ∷ Bool
  ⊢true ⊢Γ =
    prodⱼ (⊢OK (var₀ (⊢ℕ ⊢Γ))) (sucⱼ (zeroⱼ ⊢Γ))
      (conv (starⱼ ⊢Γ Unitʷ-ok)
         (Unitʷ                      ≡˘⟨ OK-1≡ ⊢Γ ⟩⊢∎≡
          OK (suc zero)              ≡˘⟨ OK-[] ⟩
          OK (var x0) [ suc zero ]₀  ∎))
      Σ-ok

opaque
  unfolding Bool false

  -- A typing rule for false.

  ⊢false :
    ⊢ Γ →
    Γ ⊢ false ∷ Bool
  ⊢false ⊢Γ =
    prodⱼ (⊢OK (var₀ (⊢ℕ ⊢Γ))) (zeroⱼ ⊢Γ)
      (conv (starⱼ ⊢Γ Unitʷ-ok)
         (Unitʷ                  ≡˘⟨ OK-0≡ ⊢Γ ⟩⊢∎≡
          OK zero                ≡˘⟨ OK-[] ⟩
          OK (var x0) [ zero ]₀  ∎))
      Σ-ok

------------------------------------------------------------------------
-- Typing rules for Target

opaque
  unfolding Bool Target

  -- An equality rule for Target.

  Target-cong :
    ∇ » drop k Δ ∙ Bool ⊢ A₁ ≡ A₂ →
    ∇ » Δ ⊢ t₁ ≡ t₂ ∷ ℕ →
    ∇ » Δ ⊢ u₁ ≡ u₂ ∷ OK t₁ →
    ∇ » Δ ⊢ Target k A₁ t₁ u₁ ≡ Target k A₂ t₂ u₂
  Target-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ =
    [][]↑-cong A₁≡A₂ $
    PE.subst (_⊢_≡_∷_ _ _ _)
      (PE.cong (Σ⟨_⟩_,_▷_▹_ _ _ _ _) $ PE.sym OK-[]) $
    prod-cong (⊢OK (var₀ (⊢ℕ (wfEqTerm t₁≡t₂)))) t₁≡t₂
      (PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym OK-[]) u₁≡u₂)
      Σ-ok

private opaque

  -- A variant of Target-cong.

  Target-cong′ :
    ∇ » drop k Δ ∙ Bool ⊢ A₁ ≡ A₂ →
    ∇ » Δ ⊢ t ∷ ℕ →
    ∇ » Δ ⊢ u ∷ OK t →
    ∇ » Δ ⊢ Target k A₁ t u ≡ Target k A₂ t u
  Target-cong′ A₁≡A₂ ⊢t ⊢u =
    Target-cong A₁≡A₂ (refl ⊢t) (refl ⊢u)

opaque

  -- A typing rule for Target.

  ⊢Target :
    ∇ » drop k Δ ∙ Bool ⊢ A →
    ∇ » Δ ⊢ t ∷ ℕ →
    ∇ » Δ ⊢ u ∷ OK t →
    ∇ » Δ ⊢ Target k A t u
  ⊢Target ⊢A ⊢t ⊢u =
    syntacticEq (Target-cong′ (refl ⊢A) ⊢t ⊢u) .proj₁

------------------------------------------------------------------------
-- Typing rules for boolrec

-- Some lemmas used below.

private
  module Boolrec
    (Π-ok : Π-allowed boolrecᵍ-Π p)
    (Π-𝟙-𝟘-ok : Π-allowed 𝟙 𝟘)
    (Unitˢ-ok : Unitˢ-allowed)
    (A₁≡A₂ : Γ »∙ Bool ⊢ A₁ ≡ A₂)
    (t₁≡t₂ : Γ ⊢ t₁ ≡ t₂ ∷ A₁ [ true ]₀)
    (u₁≡u₂ : Γ ⊢ u₁ ≡ u₂ ∷ A₁ [ false ]₀)
    where

    opaque

      ⊢Γ : ⊢ Γ
      ⊢Γ = wfEqTerm t₁≡t₂

    opaque

      ⊢Unitʷ : Γ ⊢ Unitʷ
      ⊢Unitʷ = ⊢Unit ⊢Γ Unitʷ-ok

    opaque

      ⊢star : Γ ⊢ starʷ ∷ Unitʷ
      ⊢star = starⱼ ⊢Γ Unitʷ-ok

    opaque

      Π-lemma :
        drop k Δ PE.≡ Γ .vars →
        Γ .defs » Δ ∙ ℕ ⊢ t ∷ ℕ →
        Γ .defs » Δ ∙ ℕ ⊢
          Π boolrecᵍ-Π , p ▷ OK t ▹ Target (2+ k) A₁ (wk1 t) (var x0) ≡
          Π boolrecᵍ-Π , p ▷ OK t ▹ Target (2+ k) A₂ (wk1 t) (var x0)
      Π-lemma PE.refl ⊢t =
        let ⊢OK = ⊢OK ⊢t in
        ΠΣ-cong (refl ⊢OK)
          (Target-cong′ A₁≡A₂ (wkTerm₁ ⊢OK ⊢t) $
           (PE.subst (_⊢_∷_ _ _) wk-OK $
            var₀ ⊢OK))
          Π-ok

    opaque

      Π-[]₀-lemma :
        Γ ⊢ t [ u ]₀ ∷ ℕ →
        Γ ⊢ OK (t [ u ]₀) ≡ Unitʷ →
        Γ ⊢
          (Π boolrecᵍ-Π , p ▷ OK t ▹ Target 2 A₁ (wk1 t) (var x0))
            [ u ]₀ ≡
          Π boolrecᵍ-Π , p ▷ Unitʷ ▹
            Target 1 A₂ (wk1 (t [ u ]₀)) (var x0)
      Π-[]₀-lemma {t} ⊢t[u]₀ OK-t[u]₀≡Unit =
        let ⊢OK = ⊢OK ⊢t[u]₀ in
        PE.subst (flip (_⊢_≡_ _) _)
          (PE.sym $
           PE.cong₂ (Π_,_▷_▹_ _ _) OK-[]
             (PE.trans (Target-[₀⇑] 1) $
              PE.cong (flip (Target _ _) _) $
              wk1-liftSubst t)) $
        flip (ΠΣ-cong OK-t[u]₀≡Unit) Π-ok $
        Target-cong′ A₁≡A₂ (wkTerm₁ ⊢OK ⊢t[u]₀) $
        PE.subst (_⊢_∷_ _ _) wk-OK $
        var₀ ⊢OK

    opaque

      Target-lemma-0 :
        drop k Δ PE.≡ Γ .vars →
        Γ .defs »⊢ Δ →
        Γ .defs » Δ ∙ Unitʷ ⊢
          Target (1+ k) A₁ zero (var x0) ≡
          Target (1+ k) A₂ zero (var x0)
      Target-lemma-0 PE.refl ⊢Δ =
        let ⊢Unit = ⊢Unit ⊢Δ Unitʷ-ok in
        Target-cong′ A₁≡A₂ (zeroⱼ (∙ ⊢Unit))
          (conv (var₀ ⊢Unit) (sym (OK-0≡ (∙ ⊢Unit))))

    opaque

      Target-lemma-1 :
        drop k Δ PE.≡ Γ .vars →
        Γ .defs »⊢ Δ →
        Γ .defs » Δ ∙ Unitʷ ⊢
          Target (1+ k) A₁ (suc zero) (var x0) ≡
          Target (1+ k) A₂ (suc zero) (var x0)
      Target-lemma-1 PE.refl ⊢Δ =
        let ⊢Unit = ⊢Unit ⊢Δ Unitʷ-ok in
        Target-cong′ A₁≡A₂ (sucⱼ (zeroⱼ (∙ ⊢Unit)))
          (conv (var₀ ⊢Unit) (sym (OK-1≡ (∙ ⊢Unit))))

    opaque
      unfolding true

      wk-t₁≡wk-t₂ :
        drop k Δ PE.≡ Γ .vars →
        Γ .defs »⊢ Δ →
        Γ .defs » Δ ⊢ wk[ k ]′ t₁ ≡ wk[ k ]′ t₂ ∷
          Target (1+ k) A₁ (suc zero) (var x0) [ starʷ ]₀
      wk-t₁≡wk-t₂ PE.refl ⊢Δ =
        PE.subst (_⊢_≡_∷_ _ _ _)
          (PE.sym $ PE.trans (Target-[₀⇑] 0) Target-wk[]′) $
        wkEqTerm (ʷ⊇-drop ⊢Δ) t₁≡t₂

    opaque
      unfolding false

      wk-u₁≡wk-u₂ :
        drop k Δ PE.≡ Γ .vars →
        Γ .defs »⊢ Δ →
        Γ .defs » Δ ⊢ wk[ k ]′ u₁ ≡ wk[ k ]′ u₂ ∷
          Target (1+ k) A₁ zero (var x0) [ starʷ ]₀
      wk-u₁≡wk-u₂ PE.refl ⊢Δ =
        PE.subst (_⊢_≡_∷_ _ _ _)
          (PE.sym $ PE.trans (Target-[₀⇑] 0) Target-wk[]′) $
        wkEqTerm (ʷ⊇-drop ⊢Δ) u₁≡u₂

    opaque

      unitrec-lemma-0 :
        drop k Δ PE.≡ Γ .vars →
        Γ .defs » Δ ⊢ B ≡ Unitʷ →
        Γ .defs » Δ ∙ B ⊢
          unitrec boolrecᵍ-Π p (Target (2+ k) A₁ zero (var x0))
            (var x0) (wk[ 1+ k ]′ u₁) ≡
          unitrec boolrecᵍ-Π p (Target (2+ k) A₂ zero (var x0))
            (var x0) (wk[ 1+ k ]′ u₂) ∷
          Target (2+ k) A₁ zero (var x0) [ var x0 ]₀
      unitrec-lemma-0 ≡Γ B≡Unit =
        let ⊢B , _ = syntacticEq B≡Unit in
        unitrec-cong′
          (Target-lemma-0 ≡Γ (∙ ⊢B))
          (refl (conv (var₀ ⊢B) (wkEq₁ ⊢B B≡Unit)))
          (wk-u₁≡wk-u₂ ≡Γ (∙ ⊢B))

    opaque

      unitrec-lemma-1 :
        drop k Δ PE.≡ Γ .vars →
        Γ .defs » Δ ⊢ B ≡ Unitʷ →
        Γ .defs » Δ ∙ B ⊢
          unitrec boolrecᵍ-Π p
            (Target (2+ k) A₁ (suc zero) (var x0)) (var x0)
            (wk[ 1+ k ]′ t₁) ≡
          unitrec boolrecᵍ-Π p
            (Target (2+ k) A₂ (suc zero) (var x0)) (var x0)
            (wk[ 1+ k ]′ t₂) ∷
          Target (2+ k) A₁ (suc zero) (var x0) [ var x0 ]₀
      unitrec-lemma-1 ≡Γ B≡Unit =
        let ⊢B , _ = syntacticEq B≡Unit in
        unitrec-cong′
          (Target-lemma-1 ≡Γ (∙ ⊢B))
          (refl (conv (var₀ ⊢B) (wkEq₁ ⊢B B≡Unit)))
          (wk-t₁≡wk-t₂ ≡Γ (∙ ⊢B))

    opaque

      lam-lemma-0 :
        drop k Δ PE.≡ Γ .vars →
        Γ .defs »⊢ Δ →
        Γ .defs » Δ ⊢
          lam boolrecᵍ-Π
            (unitrec boolrecᵍ-Π p
               (Target (2+ k) A₁ zero (var x0)) (var x0)
               (wk[ 1+ k ]′ u₁)) ≡
          lam boolrecᵍ-Π
            (unitrec boolrecᵍ-Π p
               (Target (2+ k) A₂ zero (var x0)) (var x0)
               (wk[ 1+ k ]′ u₂)) ∷
          (Π boolrecᵍ-Π , p ▷ OK (var x0) ▹
           Target (2+ k) A₁ (var x1) (var x0))
            [ zero ]₀
      lam-lemma-0 ≡Γ ⊢Δ =
        flip lam-cong Π-ok $
        PE.subst₄ (_⊢_≡_∷_)
          (PE.cong (_»∙_ _) $ PE.sym OK-[]) PE.refl PE.refl
          (PE.trans (Target-[₀⇑] 0) $ PE.sym $ Target-[₀⇑] 1) $
        unitrec-lemma-0 ≡Γ (OK-0≡ ⊢Δ)

    opaque

      lam-lemma-1 :
        drop k Δ PE.≡ Γ .vars →
        Γ .defs »⊢ Δ →
        Γ .defs » Δ ⊢
          lam boolrecᵍ-Π
            (unitrec boolrecᵍ-Π p
               (Target (2+ k) A₁ (suc zero) (var x0)) (var x0)
               (wk[ 1+ k ]′ t₁)) ≡
          lam boolrecᵍ-Π
            (unitrec boolrecᵍ-Π p
               (Target (2+ k) A₂ (suc zero) (var x0)) (var x0)
               (wk[ 1+ k ]′ t₂)) ∷
          (Π boolrecᵍ-Π , p ▷ OK (suc (var x0)) ▹
           Target (2+ k) A₁ (suc (var x1)) (var x0))
            [ zero ]₀
      lam-lemma-1 ≡Γ ⊢Δ =
        flip lam-cong Π-ok $
        PE.subst₄ (_⊢_≡_∷_)
          (PE.cong (_»∙_ _) (PE.sym OK-[])) PE.refl PE.refl
          (PE.trans (Target-[₀⇑] 0) $ PE.sym $ Target-[₀⇑] 1) $
        unitrec-lemma-1 ≡Γ (OK-1≡ ⊢Δ)

    opaque

      lam-lemma-2+ :
        drop k Δ PE.≡ Γ .vars →
        Γ .defs »⊢ Δ →
        Γ .defs » Δ ∙ ℕ ⊢
          lam boolrecᵍ-Π
            (emptyrec-sink
               (Target (2+ k) A₁ (suc (suc (var x1))) (var x0))
               (var x0)) ≡
          lam boolrecᵍ-Π
            (emptyrec-sink
               (Target (2+ k) A₂ (suc (suc (var x1))) (var x0))
               (var x0)) ∷
          (Π boolrecᵍ-Π , p ▷ OK (suc (var x0)) ▹
           Target (2+ k) A₁ (suc (var x1)) (var x0))
            [ suc (var x0) ]↑
      lam-lemma-2+ PE.refl ⊢Δ =
        let ⊢OK = ⊢OK (sucⱼ (sucⱼ (var₀ (⊢ℕ ⊢Δ)))) in
        flip lam-cong Π-ok $
        PE.subst₄ (_⊢_≡_∷_)
          (PE.cong (_»∙_ _) $ PE.sym OK-[]) PE.refl PE.refl
          (PE.sym $ Target-[↑⇑] 1) $
        emptyrec-sink-cong Unitˢ-ok Π-𝟙-𝟘-ok
          (Target-cong′ A₁≡A₂ (sucⱼ (sucⱼ (var₁ ⊢OK)))
             (PE.subst (_⊢_∷_ _ _) wk-OK $
              var₀ ⊢OK))
          (_⊢_≡_∷_.refl $
           _⊢_∷_.conv (var₀ ⊢OK) $
           PE.subst (flip (_⊢_≡_ _) _) (PE.sym wk-OK) $
           OK-2+≡ (var₁ ⊢OK))

    opaque

      natcase-lemma :
        drop k Δ PE.≡ Γ .vars →
        Γ .defs »⊢ Δ →
        Γ .defs » Δ ∙ ℕ ⊢
          natcase boolrecᵍ-nc₁ (boolrecᵍ-nc₃ p)
            (Π boolrecᵍ-Π , p ▷ OK (suc (var x0)) ▹
             Target (3+ k) A₁ (suc (var x1)) (var x0))
            (lam boolrecᵍ-Π $
             unitrec boolrecᵍ-Π p
               (Target (3+ k) A₁ (suc zero) (var x0)) (var x0)
               (wk[ 2+ k ]′ t₁))
            (lam boolrecᵍ-Π $
             emptyrec-sink
               (Target (3+ k) A₁ (suc (suc (var x1))) (var x0))
               (var x0))
            (var x0) ≡
          natcase boolrecᵍ-nc₁ (boolrecᵍ-nc₃ p)
            (Π boolrecᵍ-Π , p ▷ OK (suc (var x0)) ▹
             Target (3+ k) A₂ (suc (var x1)) (var x0))
            (lam boolrecᵍ-Π $
             unitrec boolrecᵍ-Π p
               (Target (3+ k) A₂ (suc zero) (var x0)) (var x0)
               (wk[ 2+ k ]′ t₂))
            (lam boolrecᵍ-Π $
             emptyrec-sink
               (Target (3+ k) A₂ (suc (suc (var x1))) (var x0))
               (var x0))
            (var x0) ∷
          (Π boolrecᵍ-Π , p ▷ OK (var x0) ▹
           Target (2+ k) A₁ (var x1) (var x0))
            [ suc (var x0) ]↑
      natcase-lemma ≡Γ ⊢Δ =
        let ⊢ℕ′  = ⊢ℕ ⊢Δ
            ⊢Δ∙ℕ = ∙ ⊢ℕ′
        in
        PE.subst (_⊢_≡_∷_ _ _ _)
          (PE.cong₂ (Π_,_▷_▹_ _ _)
             (PE.trans OK-[] $ PE.sym OK-[])
             (PE.trans (Target-[₀⇑] 1) $
              PE.sym $ Target-[↑⇑] 1)) $
        natcase-cong
          (Π-lemma ≡Γ (sucⱼ (var₀ (⊢ℕ ⊢Δ∙ℕ))))
          (lam-lemma-1 ≡Γ ⊢Δ∙ℕ)
          (lam-lemma-2+ ≡Γ ⊢Δ∙ℕ)
          (refl (var₀ ⊢ℕ′))

    opaque
      unfolding boolrec

      natcase-natcase-lemma :
        Γ »∙ ℕ »∙ OK (var x0) ⊢
          natcase boolrecᵍ-nc₂ (boolrecᵍ-nc₃ p)
            (Π boolrecᵍ-Π , p ▷ OK (var x0) ▹
             Target 4 A₁ (var x1) (var x0))
            (lam boolrecᵍ-Π $
             unitrec boolrecᵍ-Π p (Target 4 A₁ zero (var x0))
               (var x0) (wk[ 3 ]′ u₁))
            (natcase boolrecᵍ-nc₁ (boolrecᵍ-nc₃ p)
               (Π boolrecᵍ-Π , p ▷ OK (suc (var x0)) ▹
                Target 5 A₁ (suc (var x1)) (var x0))
               (lam boolrecᵍ-Π $
                unitrec boolrecᵍ-Π p
                  (Target 5 A₁ (suc zero) (var x0)) (var x0)
                  (wk[ 4 ]′ t₁))
               (lam boolrecᵍ-Π $
                emptyrec-sink
                  (Target 5 A₁ (suc (suc (var x1))) (var x0)) (var x0))
               (var x0))
            (var x1) ∘⟨ boolrecᵍ-Π ⟩
          (var x0) ≡
          natcase boolrecᵍ-nc₂ (boolrecᵍ-nc₃ p)
            (Π boolrecᵍ-Π , p ▷ OK (var x0) ▹
             Target 4 A₂ (var x1) (var x0))
            (lam boolrecᵍ-Π $
             unitrec boolrecᵍ-Π p (Target 4 A₂ zero (var x0))
               (var x0) (wk[ 3 ]′ u₂))
            (natcase boolrecᵍ-nc₁ (boolrecᵍ-nc₃ p)
               (Π boolrecᵍ-Π , p ▷ OK (suc (var x0)) ▹
                Target 5 A₂ (suc (var x1)) (var x0))
               (lam boolrecᵍ-Π $
                unitrec boolrecᵍ-Π p
                  (Target 5 A₂ (suc zero) (var x0)) (var x0)
                  (wk[ 4 ]′ t₂))
               (lam boolrecᵍ-Π $
                emptyrec-sink
                  (Target 5 A₂ (suc (suc (var x1))) (var x0)) (var x0))
               (var x0))
            (var x1) ∘⟨ boolrecᵍ-Π ⟩
          (var x0) ∷
          A₁ [ prodʷ ω (var x1) (var x0) ]↑²
      natcase-natcase-lemma =
        let ⊢OK = ⊢OK (var₀ (⊢ℕ ⊢Γ)) in
        PE.subst (_⊢_≡_∷_ _ _ _)
          (PE.trans (PE.cong _[ _ ]₀ $ Target-[₀⇑] 1) $
           PE.trans (Target-[₀⇑] 0) Target≡) $
        app-cong
          (PE.subst (_⊢_≡_∷_ _ _ _)
             (PE.cong₂ (Π_,_▷_▹_ _ _)
                (PE.trans OK-[] $ PE.sym wk-OK) PE.refl) $
           natcase-cong
             (Π-lemma PE.refl (var₀ (⊢ℕ (∙ ⊢OK))))
             (lam-lemma-0 PE.refl (∙ ⊢OK))
             (natcase-lemma PE.refl (∙ ⊢OK))
             (refl (var₁ ⊢OK)))
          (refl (var₀ ⊢OK))

private opaque

  -- A lemma used below.

  natcase-natcase-[,]₁₀ :
    (natcase boolrecᵍ-nc₂ (boolrecᵍ-nc₃ p)
       (Π boolrecᵍ-Π , p ▷ OK (var x0) ▹ Target 4 A (var x1) (var x0))
       (lam boolrecᵍ-Π $
        unitrec boolrecᵍ-Π p (Target 4 A zero (var x0)) (var x0)
          (wk[ 3 ]′ u))
       (natcase boolrecᵍ-nc₁ (boolrecᵍ-nc₃ p)
          (Π boolrecᵍ-Π , p ▷ OK (suc (var x0)) ▹
           Target 5 A (suc (var x1)) (var x0))
          (lam boolrecᵍ-Π $
           unitrec boolrecᵍ-Π p (Target 5 A (suc zero) (var x0))
             (var x0) (wk[ 4 ]′ t))
          (lam boolrecᵍ-Π $
           emptyrec-sink (Target 5 A (suc (suc (var x1))) (var x0))
             (var x0))
          (var x0))
       (var x1)
       [ v , starʷ ]₁₀) ∘⟨ boolrecᵍ-Π ⟩
    starʷ PE.≡
    natcase boolrecᵍ-nc₂ (boolrecᵍ-nc₃ p)
      (Π boolrecᵍ-Π , p ▷ OK (var x0) ▹ Target 2 A (var x1) (var x0))
      (lam boolrecᵍ-Π $
       unitrec boolrecᵍ-Π p (Target 2 A zero (var x0)) (var x0)
         (wk[ 1 ]′ u))
      (natcase boolrecᵍ-nc₁ (boolrecᵍ-nc₃ p)
         (Π boolrecᵍ-Π , p ▷ OK (suc (var x0)) ▹
          Target 3 A (suc (var x1)) (var x0))
         (lam boolrecᵍ-Π $
          unitrec boolrecᵍ-Π p (Target 3 A (suc zero) (var x0))
            (var x0) (wk[ 2 ]′ t))
         (lam boolrecᵍ-Π $
          emptyrec-sink (Target 3 A (suc (suc (var x1))) (var x0))
            (var x0))
         (var x0))
      v ∘⟨ boolrecᵍ-Π ⟩
    starʷ
  natcase-natcase-[,]₁₀ =
    PE.cong (flip _∘⟨ boolrecᵍ-Π ⟩_ _) $
    PE.trans natcase-[] $
    PE.cong₄ (natcase _ _)
      (PE.cong₂ (Π_,_▷_▹_ _ _) OK-[] (Target-[,⇑] 2))
      (PE.cong (lam _) $
       PE.cong₃ (unitrec _ _)
         (Target-[,⇑] 2) PE.refl wk[2+]′[,⇑]≡)
      (PE.trans natcase-[] $
       PE.cong₄ (natcase _ _)
         (PE.cong₂ (Π_,_▷_▹_ _ _) OK-[] (Target-[,⇑] 3))
         (PE.cong (lam _) $
          PE.cong₃ (unitrec _ _)
            (Target-[,⇑] 3) PE.refl wk[2+]′[,⇑]≡)
         (PE.cong (lam _) $
          PE.trans emptyrec-sink-[] $
          PE.cong₂ emptyrec-sink (Target-[,⇑] 3) PE.refl)
         PE.refl)
      PE.refl

opaque
  unfolding Bool boolrec

  -- An equality rule for boolrec.

  boolrec-cong :
    Π-allowed boolrecᵍ-Π p →
    Π-allowed 𝟙 𝟘 →
    Unitˢ-allowed →
    Γ »∙ Bool ⊢ A₁ ≡ A₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ A₁ [ true ]₀ →
    Γ ⊢ u₁ ≡ u₂ ∷ A₁ [ false ]₀ →
    Γ ⊢ v₁ ≡ v₂ ∷ Bool →
    Γ ⊢ boolrec p A₁ t₁ u₁ v₁ ≡ boolrec p A₂ t₂ u₂ v₂ ∷ A₁ [ v₁ ]₀
  boolrec-cong Π-ok Π-𝟙-𝟘-ok Unitˢ-ok A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ =
    prodrec-cong′ A₁≡A₂ v₁≡v₂ $
    Boolrec.natcase-natcase-lemma Π-ok Π-𝟙-𝟘-ok Unitˢ-ok A₁≡A₂ t₁≡t₂
      u₁≡u₂

opaque

  -- A typing rule for boolrec.

  ⊢boolrec :
    Π-allowed boolrecᵍ-Π p →
    Π-allowed 𝟙 𝟘 →
    Unitˢ-allowed →
    Γ »∙ Bool ⊢ A →
    Γ ⊢ t ∷ A [ true ]₀ →
    Γ ⊢ u ∷ A [ false ]₀ →
    Γ ⊢ v ∷ Bool →
    Γ ⊢ boolrec p A t u v ∷ A [ v ]₀
  ⊢boolrec Π-ok Π-𝟙-𝟘-ok Unitˢ-ok ⊢A ⊢t ⊢u ⊢v =
    syntacticEqTerm
      (boolrec-cong Π-ok Π-𝟙-𝟘-ok Unitˢ-ok (refl ⊢A) (refl ⊢t) (refl ⊢u)
         (refl ⊢v))
      .proj₂ .proj₁

opaque
  unfolding Bool true boolrec

  -- A reduction rule for boolrec.

  boolrec-true-⇒ :
    Π-allowed boolrecᵍ-Π p →
    Π-allowed 𝟙 𝟘 →
    Unitˢ-allowed →
    Γ »∙ Bool ⊢ A →
    Γ ⊢ t ∷ A [ true ]₀ →
    Γ ⊢ u ∷ A [ false ]₀ →
    Γ ⊢ boolrec p A t u true ⇒* t ∷ A [ true ]₀
  boolrec-true-⇒ {p} {Γ} {A} {t} {u} Π-ok Π-𝟙-𝟘-ok Unitˢ-ok ⊢A ⊢t ⊢u =
    prodrec boolrecᵍ-pr ω p A
      (prodʷ ω (suc zero) starʷ)
      (natcase boolrecᵍ-nc₂ (boolrecᵍ-nc₃ p)
         (Π boolrecᵍ-Π , p ▷ OK (var x0) ▹ Target 4 A (var x1) (var x0))
         (lam boolrecᵍ-Π $
          unitrec boolrecᵍ-Π p (Target 4 A zero (var x0))
            (var x0) (wk[ 3 ]′ u))
         (natcase boolrecᵍ-nc₁ (boolrecᵍ-nc₃ p)
            (Π boolrecᵍ-Π , p ▷ OK (suc (var x0)) ▹
             Target 5 A (suc (var x1)) (var x0))
            (lam boolrecᵍ-Π $
             unitrec boolrecᵍ-Π p
               (Target 5 A (suc zero) (var x0)) (var x0) (wk[ 4 ]′ t))
            (lam boolrecᵍ-Π $
             emptyrec-sink (Target 5 A (suc (suc (var x1))) (var x0))
               (var x0))
            (var x0))
         (var x1) ∘⟨ boolrecᵍ-Π ⟩
       var x0)                                                            ⇒⟨ prodrec-β-⇒ ⊢A (sucⱼ (zeroⱼ ⊢Γ))
                                                                               (_⊢_∷_.conv ⊢star $
                                                                                PE.subst (_⊢_≡_ _ _) (PE.sym OK-[]) $
                                                                                sym $ OK-1≡ ⊢Γ)
                                                                               (syntacticEqTerm natcase-natcase-lemma .proj₂ .proj₁) ⟩
    (natcase boolrecᵍ-nc₂ (boolrecᵍ-nc₃ p)
       (Π boolrecᵍ-Π , p ▷ OK (var x0) ▹ Target 4 A (var x1) (var x0))
       (lam boolrecᵍ-Π $
        unitrec boolrecᵍ-Π p (Target 4 A zero (var x0)) (var x0)
          (wk[ 3 ]′ u))
       (natcase boolrecᵍ-nc₁ (boolrecᵍ-nc₃ p)
          (Π boolrecᵍ-Π , p ▷ OK (suc (var x0)) ▹
           Target 5 A (suc (var x1)) (var x0))
          (lam boolrecᵍ-Π $
           unitrec boolrecᵍ-Π p (Target 5 A (suc zero) (var x0))
             (var x0) (wk[ 4 ]′ t))
          (lam boolrecᵍ-Π $
           emptyrec-sink (Target 5 A (suc (suc (var x1))) (var x0))
             (var x0))
          (var x0))
       (var x1)
       [ suc zero , starʷ ]₁₀) ∘⟨ boolrecᵍ-Π ⟩
    starʷ ≡⟨ natcase-natcase-[,]₁₀ ⟩⇒

    natcase boolrecᵍ-nc₂ (boolrecᵍ-nc₃ p)
      (Π boolrecᵍ-Π , p ▷ OK (var x0) ▹ Target 2 A (var x1) (var x0))
      (lam boolrecᵍ-Π $
       unitrec boolrecᵍ-Π p (Target 2 A zero (var x0)) (var x0)
         (wk[ 1 ]′ u))
      (natcase boolrecᵍ-nc₁ (boolrecᵍ-nc₃ p)
         (Π boolrecᵍ-Π , p ▷ OK (suc (var x0)) ▹
          Target 3 A (suc (var x1)) (var x0))
         (lam boolrecᵍ-Π $
          unitrec boolrecᵍ-Π p (Target 3 A (suc zero) (var x0))
            (var x0) (wk[ 2 ]′ t))
         (lam boolrecᵍ-Π $
          emptyrec-sink (Target 3 A (suc (suc (var x1))) (var x0))
            (var x0))
         (var x0))
      (suc zero) ∘⟨ boolrecᵍ-Π ⟩
    starʷ ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _) (PE.trans (Target-[₀⇑] 0) Target≡) $
                                                                             app-subst
                                                                               (conv
                                                                                  (natcase-suc-⇒
                                                                                     (syntacticEq (Π-lemma PE.refl (var₀ (⊢ℕ ⊢Γ))) .proj₁)
                                                                                     (syntacticEqTerm (lam-lemma-0 PE.refl ⊢Γ) .proj₂ .proj₁)
                                                                                     (syntacticEqTerm (natcase-lemma PE.refl ⊢Γ) .proj₂ .proj₁)
                                                                                     (zeroⱼ ⊢Γ))
                                                                                  (Π-[]₀-lemma (sucⱼ (zeroⱼ ⊢Γ)) (OK-1≡ ⊢Γ)))
                                                                               ⊢star ⟩
    (natcase boolrecᵍ-nc₁ (boolrecᵍ-nc₃ p)
       (Π boolrecᵍ-Π , p ▷ OK (suc (var x0)) ▹
        Target 3 A (suc (var x1)) (var x0))
       (lam boolrecᵍ-Π $
        unitrec boolrecᵍ-Π p (Target 3 A (suc zero) (var x0))
          (var x0) (wk[ 2 ]′ t))
       (lam boolrecᵍ-Π $
        emptyrec-sink (Target 3 A (suc (suc (var x1))) (var x0))
          (var x0))
       (var x0)
       [ zero ]₀) ∘⟨ boolrecᵍ-Π ⟩
    starʷ ≡⟨ PE.cong (_∘⟨ boolrecᵍ-Π ⟩ _) $
                                                                             PE.trans natcase-[] $
                                                                             PE.cong₄ (natcase _ _)
                                                                               (PE.cong₂ (Π_,_▷_▹_ _ _) OK-[] (Target-[₀⇑] 2))
                                                                               (PE.cong (lam boolrecᵍ-Π) $
                                                                                PE.cong₃ (unitrec _ _) (Target-[₀⇑] 2) PE.refl
                                                                                  (PE.trans (PE.cong _[ _ ] $ PE.sym $ wk[]≡wk[]′ {t = t}) $
                                                                                   PE.trans (wk1-liftSubst (wk1 t)) $
                                                                                   PE.cong wk1 $ wk1-sgSubst _ _))
                                                                               (PE.cong (lam boolrecᵍ-Π) $
                                                                                PE.trans emptyrec-sink-[] $
                                                                                PE.cong₂ emptyrec-sink (Target-[₀⇑] 2) PE.refl)
                                                                               PE.refl ⟩⇒
    natcase boolrecᵍ-nc₁ (boolrecᵍ-nc₃ p)
      (Π boolrecᵍ-Π , p ▷ OK (suc (var x0)) ▹
       Target 2 A (suc (var x1)) (var x0))
      (lam boolrecᵍ-Π $
       unitrec boolrecᵍ-Π p (Target 2 A (suc zero) (var x0))
         (var x0) (wk1 t))
      (lam boolrecᵍ-Π $
       emptyrec-sink (Target 2 A (suc (suc (var x1))) (var x0))
         (var x0))
      zero ∘⟨ boolrecᵍ-Π ⟩
    starʷ ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _) (PE.trans (Target-[₀⇑] 0) Target≡) $
                                                                             app-subst
                                                                               (conv
                                                                                  (natcase-zero-⇒
                                                                                     (syntacticEq (Π-lemma PE.refl (sucⱼ (var₀ (⊢ℕ ⊢Γ)))) .proj₁)
                                                                                     (syntacticEqTerm (lam-lemma-1 PE.refl ⊢Γ) .proj₂ .proj₁)
                                                                                     (syntacticEqTerm (lam-lemma-2+ PE.refl ⊢Γ) .proj₂ .proj₁))
                                                                                  (Π-[]₀-lemma (sucⱼ (zeroⱼ ⊢Γ)) (OK-1≡ ⊢Γ)))
                                                                               ⊢star ⟩
    lam boolrecᵍ-Π
      (unitrec boolrecᵍ-Π p (Target 2 A (suc zero) (var x0))
         (var x0) (wk1 t))
      ∘⟨ boolrecᵍ-Π ⟩
    starʷ ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _)
                                                                               (PE.trans (PE.cong _[ _ ]₀ $ Target-[₀⇑] 0) $
                                                                                PE.trans (Target-[₀⇑] 0) Target≡) $
                                                                             β-red-⇒
                                                                               (syntacticEqTerm (unitrec-lemma-1 PE.refl (refl ⊢Unitʷ))
                                                                                  .proj₂ .proj₁)
                                                                               ⊢star Π-ok ⟩
    unitrec boolrecᵍ-Π p (Target 2 A (suc zero) (var x0)) (var x0)
      (wk1 t) [ starʷ ]₀                                            ≡⟨ PE.cong₃ (unitrec _ _)
                                                                               (Target-[₀⇑] 1) PE.refl (wk1-sgSubst _ _) ⟩⇒

    unitrec boolrecᵍ-Π p (Target 1 A (suc zero) (var x0))
      starʷ t                                                     ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _) (PE.trans (Target-[₀⇑] 0) Target≡) $
                                                                             unitrec-β-⇒
                                                                               (syntacticEq (Target-lemma-1 PE.refl ⊢Γ) .proj₁)
                                                                               (PE.subst (flip (_⊢_∷_ _) _) (wk-id _) $
                                                                                syntacticEqTerm (wk-t₁≡wk-t₂ PE.refl ⊢Γ) .proj₂ .proj₁) ⟩∎
    t                                                                     ∎
    where
    open Boolrec Π-ok Π-𝟙-𝟘-ok Unitˢ-ok (refl ⊢A) (refl ⊢t) (refl ⊢u)

opaque

  -- An equality rule for boolrec.

  boolrec-true-≡ :
    Π-allowed boolrecᵍ-Π p →
    Π-allowed 𝟙 𝟘 →
    Unitˢ-allowed →
    Γ »∙ Bool ⊢ A →
    Γ ⊢ t ∷ A [ true ]₀ →
    Γ ⊢ u ∷ A [ false ]₀ →
    Γ ⊢ boolrec p A t u true ≡ t ∷ A [ true ]₀
  boolrec-true-≡ Π-ok Π-𝟙-𝟘-ok Unitˢ-ok ⊢A ⊢t ⊢u =
    subset*Term (boolrec-true-⇒ Π-ok Π-𝟙-𝟘-ok Unitˢ-ok ⊢A ⊢t ⊢u)

opaque
  unfolding Bool false boolrec

  -- A reduction rule for boolrec.

  boolrec-false-⇒ :
    Π-allowed boolrecᵍ-Π p →
    Π-allowed 𝟙 𝟘 →
    Unitˢ-allowed →
    Γ »∙ Bool ⊢ A →
    Γ ⊢ t ∷ A [ true ]₀ →
    Γ ⊢ u ∷ A [ false ]₀ →
    Γ ⊢ boolrec p A t u false ⇒* u ∷ A [ false ]₀
  boolrec-false-⇒ {p} {Γ} {A} {t} {u} Π-ok Π-𝟙-𝟘-ok Unitˢ-ok ⊢A ⊢t ⊢u =
    prodrec boolrecᵍ-pr ω p A (prodʷ ω zero starʷ)
      (natcase boolrecᵍ-nc₂ (boolrecᵍ-nc₃ p)
         (Π boolrecᵍ-Π , p ▷ OK (var x0) ▹ Target 4 A (var x1) (var x0))
         (lam boolrecᵍ-Π $
          unitrec boolrecᵍ-Π p (Target 4 A zero (var x0))
            (var x0) (wk[ 3 ]′ u))
         (natcase boolrecᵍ-nc₁ (boolrecᵍ-nc₃ p)
            (Π boolrecᵍ-Π , p ▷ OK (suc (var x0)) ▹
             Target 5 A (suc (var x1)) (var x0))
            (lam boolrecᵍ-Π $
             unitrec boolrecᵍ-Π p
               (Target 5 A (suc zero) (var x0)) (var x0) (wk[ 4 ]′ t))
            (lam boolrecᵍ-Π $
             emptyrec-sink (Target 5 A (suc (suc (var x1))) (var x0))
               (var x0))
            (var x0))
         (var x1) ∘⟨ boolrecᵍ-Π ⟩
       var x0)                                                            ⇒⟨ prodrec-β-⇒ ⊢A (zeroⱼ ⊢Γ)
                                                                               (_⊢_∷_.conv ⊢star $
                                                                                PE.subst (_⊢_≡_ _ _) (PE.sym OK-[]) $
                                                                                sym $ OK-0≡ ⊢Γ)
                                                                               (syntacticEqTerm natcase-natcase-lemma .proj₂ .proj₁) ⟩
    (natcase boolrecᵍ-nc₂ (boolrecᵍ-nc₃ p)
       (Π boolrecᵍ-Π , p ▷ OK (var x0) ▹ Target 4 A (var x1) (var x0))
       (lam boolrecᵍ-Π $
        unitrec boolrecᵍ-Π p (Target 4 A zero (var x0)) (var x0)
          (wk[ 3 ]′ u))
       (natcase boolrecᵍ-nc₁ (boolrecᵍ-nc₃ p)
          (Π boolrecᵍ-Π , p ▷ OK (suc (var x0)) ▹
           Target 5 A (suc (var x1)) (var x0))
          (lam boolrecᵍ-Π $
           unitrec boolrecᵍ-Π p (Target 5 A (suc zero) (var x0))
             (var x0) (wk[ 4 ]′ t))
          (lam boolrecᵍ-Π $
           emptyrec-sink (Target 5 A (suc (suc (var x1))) (var x0))
             (var x0))
          (var x0))
       (var x1)
       [ zero , starʷ ]₁₀) ∘⟨ boolrecᵍ-Π ⟩
    starʷ ≡⟨ natcase-natcase-[,]₁₀ ⟩⇒

    natcase boolrecᵍ-nc₂ (boolrecᵍ-nc₃ p)
      (Π boolrecᵍ-Π , p ▷ OK (var x0) ▹ Target 2 A (var x1) (var x0))
      (lam boolrecᵍ-Π $
       unitrec boolrecᵍ-Π p (Target 2 A zero (var x0)) (var x0)
         (wk[ 1 ]′ u))
      (natcase boolrecᵍ-nc₁ (boolrecᵍ-nc₃ p)
         (Π boolrecᵍ-Π , p ▷ OK (suc (var x0)) ▹
          Target 3 A (suc (var x1)) (var x0))
         (lam boolrecᵍ-Π $
          unitrec boolrecᵍ-Π p (Target 3 A (suc zero) (var x0))
            (var x0) (wk[ 2 ]′ t))
         (lam boolrecᵍ-Π $
          emptyrec-sink (Target 3 A (suc (suc (var x1))) (var x0))
            (var x0))
         (var x0))
      zero ∘⟨ boolrecᵍ-Π ⟩
    starʷ ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _) (PE.trans (Target-[₀⇑] 0) Target≡) $
                                                                             app-subst
                                                                               (conv
                                                                                  (natcase-zero-⇒
                                                                                     (syntacticEq (Π-lemma PE.refl (var₀ (⊢ℕ ⊢Γ))) .proj₁)
                                                                                     (syntacticEqTerm (lam-lemma-0 PE.refl ⊢Γ) .proj₂ .proj₁)
                                                                                     (syntacticEqTerm (natcase-lemma PE.refl ⊢Γ) .proj₂ .proj₁))
                                                                                  (Π-[]₀-lemma (zeroⱼ ⊢Γ) (OK-0≡ ⊢Γ)))
                                                                               ⊢star ⟩
    lam boolrecᵍ-Π
      (unitrec boolrecᵍ-Π p (Target 2 A zero (var x0)) (var x0)
         (wk1 u))
      ∘⟨ boolrecᵍ-Π ⟩
    starʷ ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _)
                                                                               (PE.trans (PE.cong _[ _ ]₀ $ Target-[₀⇑] 0) $
                                                                                PE.trans (Target-[₀⇑] 0) Target≡) $
                                                                             β-red-⇒
                                                                               (syntacticEqTerm (unitrec-lemma-0 PE.refl (refl ⊢Unitʷ))
                                                                                  .proj₂ .proj₁)
                                                                               ⊢star Π-ok ⟩
    unitrec boolrecᵍ-Π p (Target 2 A zero (var x0)) (var x0)
      (wk1 u) [ starʷ ]₀                                            ≡⟨ PE.cong₃ (unitrec _ _)
                                                                               (Target-[₀⇑] 1) PE.refl (wk1-sgSubst _ _) ⟩⇒

    unitrec boolrecᵍ-Π p (Target 1 A zero (var x0)) starʷ
      u                                                                   ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _) (PE.trans (Target-[₀⇑] 0) Target≡) $
                                                                             unitrec-β-⇒
                                                                               (syntacticEq (Target-lemma-0 PE.refl ⊢Γ) .proj₁)
                                                                               (PE.subst (flip (_⊢_∷_ _) _) (wk-id _) $
                                                                                syntacticEqTerm (wk-u₁≡wk-u₂ PE.refl ⊢Γ) .proj₂ .proj₁) ⟩∎
    u                                                                     ∎
    where
    open Boolrec Π-ok Π-𝟙-𝟘-ok Unitˢ-ok (refl ⊢A) (refl ⊢t) (refl ⊢u)

opaque

  -- An equality rule for boolrec.

  boolrec-false-≡ :
    Π-allowed boolrecᵍ-Π p →
    Π-allowed 𝟙 𝟘 →
    Unitˢ-allowed →
    Γ »∙ Bool ⊢ A →
    Γ ⊢ t ∷ A [ true ]₀ →
    Γ ⊢ u ∷ A [ false ]₀ →
    Γ ⊢ boolrec p A t u false ≡ u ∷ A [ false ]₀
  boolrec-false-≡ Π-ok Π-𝟙-𝟘-ok Unitˢ-ok ⊢A ⊢t ⊢u =
    subset*Term (boolrec-false-⇒ Π-ok Π-𝟙-𝟘-ok Unitˢ-ok ⊢A ⊢t ⊢u)
