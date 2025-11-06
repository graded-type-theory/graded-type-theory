------------------------------------------------------------------------
-- Typing and equality rules related to Bool
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Definition.Untyped
import Definition.Untyped.Bool.Erased
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Bool.Erased
  {a} {M : Set a}
  (open Definition.Untyped M hiding (_[_]))
  {𝕄 : Modality M}
  (open Definition.Untyped.Bool.Erased 𝕄)
  (open Modality 𝕄)
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  -- It is assumed that modality has an nr function.
  ⦃ has-nr : Has-nr M semiring-with-meet ⦄
  -- It is assumed that certain Σ-types are allowed.
  (Σ-ok : Σʷ-allowed 𝟙 Boolᵍ)
  -- It is assumed that Erased is allowed for the strength 𝕨.
  (Erased-ok : Erased-allowed 𝕨)
  where

open import Definition.Typed R
import Definition.Typed.Properties.Admissible.Bool.OK
open import Definition.Typed.Properties.Admissible.Empty R
open import Definition.Typed.Properties.Admissible.Erased R
open import Definition.Typed.Properties.Admissible.Nat R
open import Definition.Typed.Properties.Admissible.Pi R
open import Definition.Typed.Properties.Admissible.Sigma R
open import Definition.Typed.Properties.Admissible.Unit R
open import Definition.Typed.Properties.Admissible.Var R
open import Definition.Typed.Properties.Well-formed R
import Definition.Typed.Reasoning.Term R as TmR
import Definition.Typed.Reasoning.Type R as TyR
open import Definition.Typed.Substitution.Primitive R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Weakening R

open import Definition.Untyped.Bool.Nr 𝕄 as B
  using (OK; OKᵍ; boolrecᵍ-nc₁; boolrecᵍ-nc₂)
open import Definition.Untyped.Empty 𝕄
open import Definition.Untyped.Erased 𝕄 𝕨
open import Definition.Untyped.Nat 𝕄
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+; 2+; 3+; 4+)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private variable
  k                                 : Nat
  ∇                                 : DCon (Term 0) _
  Δ                                 : Con Term _
  Γ                                 : Cons _ _
  A A₁ A₂ B t t₁ t₂ u u₁ u₂ v v₁ v₂ : Term _
  p                                 : M

------------------------------------------------------------------------
-- Some lemmas used below

private opaque

  Unitʷ-ok : Unitʷ-allowed
  Unitʷ-ok = Erased-ok .proj₁

open Definition.Typed.Properties.Admissible.Bool.OK OKᵍ R Unitʷ-ok

private opaque

  ⊢Erased-OK :
    Γ ⊢ t ∷ ℕ →
    Γ ⊢ Erased (OK t)
  ⊢Erased-OK = Erasedⱼ Erased-ok ∘→ ⊢OK

------------------------------------------------------------------------
-- Typing rules for Bool, true and false

opaque
  unfolding Bool

  -- A typing rule for Bool.

  ⊢Bool∷U :
    ⊢ Γ →
    Γ ⊢ Bool ∷ U 0
  ⊢Bool∷U ⊢Γ =
    ΠΣⱼ (ℕⱼ ⊢Γ) (Erasedⱼ-U Erased-ok (⊢OK∷U (var₀ (ℕⱼ ⊢Γ)))) Σ-ok

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
    prodⱼ (⊢Erased-OK (var₀ (ℕⱼ ⊢Γ)))
      (sucⱼ (zeroⱼ ⊢Γ))
      ([]ⱼ Erased-ok $
       _⊢_∷_.conv (starⱼ ⊢Γ Unitʷ-ok)
         (Unitʷ 0                    ≡˘⟨ OK-1≡ ⊢Γ ⟩⊢∎≡
          OK (suc zero)              ≡˘⟨ B.OK-[] ⟩
          OK (var x0) [ suc zero ]₀  ∎))
      Σ-ok
    where
    open TyR

opaque
  unfolding Bool false

  -- A typing rule for false.

  ⊢false :
    ⊢ Γ →
    Γ ⊢ false ∷ Bool
  ⊢false ⊢Γ =
    prodⱼ (⊢Erased-OK (var₀ (ℕⱼ ⊢Γ))) (zeroⱼ ⊢Γ)
      ([]ⱼ Erased-ok $
       _⊢_∷_.conv (starⱼ ⊢Γ Unitʷ-ok)
         (Unitʷ 0                ≡˘⟨ OK-0≡ ⊢Γ ⟩⊢∎≡
          OK zero                ≡˘⟨ B.OK-[] ⟩
          OK (var x0) [ zero ]₀  ∎))
      Σ-ok
    where
    open TyR

------------------------------------------------------------------------
-- Typing rules for Target

opaque
  unfolding Bool Target

  -- An equality rule for Target.

  Target-cong :
    ∇ » drop k Δ ∙ Bool ⊢ A₁ ≡ A₂ →
    ∇ » Δ ⊢ t₁ ≡ t₂ ∷ ℕ →
    ∇ » Δ ⊢ u₁ ≡ u₂ ∷ Erased (OK t₁) →
    ∇ » Δ ⊢ Target k A₁ t₁ u₁ ≡ Target k A₂ t₂ u₂
  Target-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ =
    [][]↑-cong A₁≡A₂ $
    PE.subst (_⊢_≡_∷_ _ _ _)
      (PE.cong (ΠΣ⟨_⟩_,_▷_▹_ _ _ _ _) $
       PE.cong Erased $ PE.sym B.OK-[]) $
    prod-cong (⊢Erased-OK (var₀ (ℕⱼ (wfEqTerm t₁≡t₂)))) t₁≡t₂
      (PE.subst (_⊢_≡_∷_ _ _ _) (PE.cong Erased $ PE.sym B.OK-[]) u₁≡u₂)
      Σ-ok

private opaque

  -- A variant of Target-cong.

  Target-cong′ :
    ∇ » drop k Δ ∙ Bool ⊢ A₁ ≡ A₂ →
    ∇ » Δ ⊢ t ∷ ℕ →
    ∇ » Δ ⊢ u ∷ Erased (OK t) →
    ∇ » Δ ⊢ Target k A₁ t u ≡ Target k A₂ t u
  Target-cong′ A₁≡A₂ ⊢t ⊢u =
    Target-cong A₁≡A₂ (refl ⊢t) (refl ⊢u)

opaque

  -- A typing rule for Target.

  ⊢Target :
    ∇ » drop k Δ ∙ Bool ⊢ A →
    ∇ » Δ ⊢ t ∷ ℕ →
    ∇ » Δ ⊢ u ∷ Erased (OK t) →
    ∇ » Δ ⊢ Target k A t u
  ⊢Target ⊢A ⊢t ⊢u =
    syntacticEq (Target-cong′ (refl ⊢A) ⊢t ⊢u) .proj₁

------------------------------------------------------------------------
-- Typing rules for boolrec

-- Some lemmas used below.

private
  module Boolrec
    (Π-ok : Π-allowed 𝟙 p)
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

      ⊢Unitʷ : Γ ⊢ Unitʷ 0
      ⊢Unitʷ = Unitⱼ ⊢Γ Unitʷ-ok

    opaque

      ⊢[starʷ] : Γ ⊢ [ starʷ 0 ] ∷ Erased (Unitʷ 0)
      ⊢[starʷ] = []ⱼ Erased-ok (starⱼ ⊢Γ Unitʷ-ok)

    opaque

      ⊢Erased-Unitʷ : Γ ⊢ Erased (Unitʷ 0)
      ⊢Erased-Unitʷ = syntacticTerm ⊢[starʷ]

    opaque

      Π-lemma :
        drop k Δ PE.≡ Γ .vars →
        Γ .defs » Δ ∙ ℕ ⊢ t ∷ ℕ →
        Γ .defs » Δ ∙ ℕ ⊢
          Π 𝟙 , p ▷ Erased (OK t) ▹ Target (2+ k) A₁ (wk1 t) (var x0) ≡
          Π 𝟙 , p ▷ Erased (OK t) ▹ Target (2+ k) A₂ (wk1 t) (var x0)
      Π-lemma PE.refl ⊢t =
        let ⊢OK = ⊢Erased-OK ⊢t in
        ΠΣ-cong (refl ⊢OK)
          (Target-cong′ A₁≡A₂ (wkTerm₁ ⊢OK ⊢t) $
           PE.subst (_⊢_∷_ _ _) (PE.cong Erased B.wk-OK) $
           var₀ ⊢OK)
          Π-ok

    opaque

      Π-[]₀-lemma :
        Γ ⊢ t [ u ]₀ ∷ ℕ →
        Γ ⊢ OK (t [ u ]₀) ≡ Unitʷ 0 →
        Γ ⊢
          (Π 𝟙 , p ▷ Erased (OK t) ▹ Target 2 A₁ (wk1 t) (var x0))
            [ u ]₀ ≡
          Π 𝟙 , p ▷ Erased (Unitʷ 0) ▹ Target 1 A₂ (wk1 (t [ u ]₀))
            (var x0)
      Π-[]₀-lemma {t} ⊢t[u]₀ OK-t[u]₀≡Unit =
        let ⊢OK = ⊢Erased-OK ⊢t[u]₀ in
        PE.subst (flip (_⊢_≡_ _) _)
          (PE.sym $
           PE.cong₂ (ΠΣ⟨_⟩_,_▷_▹_ _ _ _) (PE.cong Erased B.OK-[])
             (PE.trans (Target-[₀⇑] 1) $
              PE.cong (flip (Target _ _) _) $
              wk1-liftSubst t)) $
        flip (ΠΣ-cong (Erased-cong Erased-ok OK-t[u]₀≡Unit)) Π-ok $
        Target-cong′ A₁≡A₂ (wkTerm₁ ⊢OK ⊢t[u]₀) $
        PE.subst (_⊢_∷_ _ _) (PE.cong Erased B.wk-OK) $
        var₀ ⊢OK

    opaque

      Target-lemma-0 :
        drop k Δ PE.≡ Γ .vars →
        Γ .defs » Δ ∙ B ⊢ t ∷ Erased (Unitʷ 0) →
        Γ .defs » Δ ∙ B ⊢
          Target (1+ k) A₁ zero t ≡
          Target (1+ k) A₂ zero t
      Target-lemma-0 PE.refl ⊢t =
        let ⊢Δ∙B = wfTerm ⊢t in
        Target-cong′ A₁≡A₂ (zeroⱼ ⊢Δ∙B)
          (conv ⊢t (sym (Erased-cong Erased-ok (OK-0≡ ⊢Δ∙B))))

    opaque

      Target-lemma-1 :
        drop k Δ PE.≡ Γ .vars →
        Γ .defs » Δ ∙ B ⊢ t ∷ Erased (Unitʷ 0) →
        Γ .defs » Δ ∙ B ⊢
          Target (1+ k) A₁ (suc zero) t ≡
          Target (1+ k) A₂ (suc zero) t
      Target-lemma-1 PE.refl ⊢t =
        let ⊢Δ∙B = wfTerm ⊢t in
        Target-cong′ A₁≡A₂ (sucⱼ (zeroⱼ ⊢Δ∙B))
          (conv ⊢t (sym (Erased-cong Erased-ok (OK-1≡ ⊢Δ∙B))))

    opaque
      unfolding true

      wk-t₁≡wk-t₂ :
        drop k Δ PE.≡ Γ .vars →
        Γ .defs »⊢ Δ →
        Γ .defs » Δ ⊢ wk[ k ]′ t₁ ≡ wk[ k ]′ t₂ ∷
          Target (1+ k) A₁ (suc zero) [ var x0 ] [ starʷ 0 ]₀
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
          Target (1+ k) A₁ zero [ var x0 ] [ starʷ 0 ]₀
      wk-u₁≡wk-u₂ PE.refl ⊢Δ =
        PE.subst (_⊢_≡_∷_ _ _ _)
          (PE.sym $ PE.trans (Target-[₀⇑] 0) Target-wk[]′) $
        wkEqTerm (ʷ⊇-drop ⊢Δ) u₁≡u₂

    opaque

      unitrec-lemma-0 :
        drop k Δ PE.≡ Γ .vars →
        Γ .defs »⊢ Δ →
        Γ .defs » Δ ∙ Unitʷ 0 ⊢
          unitrec 0 𝟘 𝟘 (Target (2+ k) A₁ zero [ var x0 ])
            (var x0) (wk[ 1+ k ]′ u₁) ≡
          unitrec 0 𝟘 𝟘 (Target (2+ k) A₂ zero [ var x0 ])
            (var x0) (wk[ 1+ k ]′ u₂) ∷
          Target (1+ k) A₁ zero (var x0) [ [ var x0 ] ]↑
      unitrec-lemma-0 ≡Γ ⊢Δ =
        let ⊢Unitʷ = Unitⱼ ⊢Δ Unitʷ-ok in
        PE.subst (_⊢_≡_∷_ _ _ _)
          (PE.trans (Target-[₀⇑] 0) $ PE.sym $ Target-[↑⇑] 0) $
        unitrec-cong′
          (Target-lemma-0 ≡Γ $
           []ⱼ Erased-ok (var₀ (Unitⱼ (∙ ⊢Unitʷ) Unitʷ-ok)))
          (refl (var₀ ⊢Unitʷ))
          (wk-u₁≡wk-u₂ ≡Γ (∙ ⊢Unitʷ))

    opaque

      unitrec-lemma-1 :
        drop k Δ PE.≡ Γ .vars →
        Γ .defs »⊢ Δ →
        Γ .defs » Δ ∙ Unitʷ 0 ⊢
          unitrec 0 𝟘 𝟘 (Target (2+ k) A₁ (suc zero) [ var x0 ])
            (var x0) (wk[ 1+ k ]′ t₁) ≡
          unitrec 0 𝟘 𝟘 (Target (2+ k) A₂ (suc zero) [ var x0 ])
            (var x0) (wk[ 1+ k ]′ t₂) ∷
          Target (1+ k) A₁ (suc zero) (var x0) [ [ var x0 ] ]↑
      unitrec-lemma-1 ≡Γ ⊢Δ =
        let ⊢Unitʷ = Unitⱼ ⊢Δ Unitʷ-ok in
        PE.subst (_⊢_≡_∷_ _ _ _)
          (PE.trans (Target-[₀⇑] 0) $ PE.sym $ Target-[↑⇑] 0) $
        unitrec-cong′
          (Target-lemma-1 ≡Γ $
           []ⱼ Erased-ok (var₀ (Unitⱼ (∙ ⊢Unitʷ) Unitʷ-ok)))
          (refl (var₀ ⊢Unitʷ))
          (wk-t₁≡wk-t₂ ≡Γ (∙ ⊢Unitʷ))

    opaque

      erasedrec-lemma-0 :
        drop k Δ PE.≡ Γ .vars →
        Γ .defs » Δ ⊢ B ≡ Erased (Unitʷ 0) →
        Γ .defs » Δ ∙ B ⊢
          erasedrec p (Target (2+ k) A₁ zero (var x0))
            (unitrec 0 𝟘 𝟘 (Target (3+ k) A₁ zero [ var x0 ]) (var x0)
               (wk[ 2+ k ]′ u₁))
            (var x0) ≡
          erasedrec p (Target (2+ k) A₂ zero (var x0))
            (unitrec 0 𝟘 𝟘 (Target (3+ k) A₂ zero [ var x0 ]) (var x0)
               (wk[ 2+ k ]′ u₂))
            (var x0) ∷
          Target (2+ k) A₁ zero (var x0) [ var x0 ]₀
      erasedrec-lemma-0 ≡Γ B≡Unit =
        let ⊢B , ⊢E = syntacticEq B≡Unit in
        erasedrec-cong
          (Target-lemma-0 ≡Γ (var₀ (wk₁ ⊢B ⊢E)))
          (unitrec-lemma-0 ≡Γ (∙ ⊢B))
          (refl (conv (var₀ ⊢B) (wkEq₁ ⊢B B≡Unit)))

    opaque

      erasedrec-lemma-1 :
        drop k Δ PE.≡ Γ .vars →
        Γ .defs » Δ ⊢ B ≡ Erased (Unitʷ 0) →
        Γ .defs » Δ ∙ B ⊢
          erasedrec p (Target (2+ k) A₁ (suc zero) (var x0))
            (unitrec 0 𝟘 𝟘 (Target (3+ k) A₁ (suc zero) [ var x0 ])
               (var x0) (wk[ 2+ k ]′ t₁))
            (var x0) ≡
          erasedrec p (Target (2+ k) A₂ (suc zero) (var x0))
            (unitrec 0 𝟘 𝟘 (Target (3+ k) A₂ (suc zero) [ var x0 ])
               (var x0) (wk[ 2+ k ]′ t₂))
            (var x0) ∷
          Target (2+ k) A₁ (suc zero) (var x0) [ var x0 ]₀
      erasedrec-lemma-1 ≡Γ B≡Unit =
        let ⊢B , ⊢E = syntacticEq B≡Unit in
        erasedrec-cong
          (Target-lemma-1 ≡Γ (var₀ (wk₁ ⊢B ⊢E)))
          (unitrec-lemma-1 ≡Γ (∙ ⊢B))
          (refl (conv (var₀ ⊢B) (wkEq₁ ⊢B B≡Unit)))

    opaque

      lam-lemma-0 :
        drop k Δ PE.≡ Γ .vars →
        Γ .defs »⊢ Δ →
        Γ .defs » Δ ⊢
          lam 𝟙
            (erasedrec p (Target (2+ k) A₁ zero (var x0))
               (unitrec 0 𝟘 𝟘 (Target (3+ k) A₁ zero [ var x0 ])
                  (var x0) (wk[ 2+ k ]′ u₁))
               (var x0)) ≡
          lam 𝟙
            (erasedrec p (Target (2+ k) A₂ zero (var x0))
               (unitrec 0 𝟘 𝟘 (Target (3+ k) A₂ zero [ var x0 ])
                  (var x0) (wk[ 2+ k ]′ u₂))
               (var x0)) ∷
          (Π 𝟙 , p ▷ Erased (OK (var x0)) ▹
           Target (2+ k) A₁ (var x1) (var x0))
            [ zero ]₀
      lam-lemma-0 ≡Γ ⊢Δ =
        flip lam-cong Π-ok $
        PE.subst₄ _⊢_≡_∷_
          (PE.cong (_»∙_ _) $ PE.sym (PE.cong Erased B.OK-[]))
          PE.refl PE.refl
          (PE.trans (Target-[₀⇑] 0) $ PE.sym $ Target-[₀⇑] 1) $
        erasedrec-lemma-0 ≡Γ (Erased-cong Erased-ok (OK-0≡ ⊢Δ))

    opaque

      lam-lemma-1 :
        drop k Δ PE.≡ Γ .vars →
        Γ .defs »⊢ Δ →
        Γ .defs » Δ ⊢
          lam 𝟙
            (erasedrec p (Target (2+ k) A₁ (suc zero) (var x0))
               (unitrec 0 𝟘 𝟘 (Target (3+ k) A₁ (suc zero) [ var x0 ])
                  (var x0) (wk[ 2+ k ]′ t₁))
               (var x0)) ≡
          lam 𝟙
            (erasedrec p (Target (2+ k) A₂ (suc zero) (var x0))
               (unitrec 0 𝟘 𝟘 (Target (3+ k) A₂ (suc zero) [ var x0 ])
                  (var x0) (wk[ 2+ k ]′ t₂))
               (var x0)) ∷
          (Π 𝟙 , p ▷ Erased (OK (suc (var x0))) ▹
           Target (2+ k) A₁ (suc (var x1)) (var x0))
            [ zero ]₀
      lam-lemma-1 ≡Γ ⊢Δ =
        flip lam-cong Π-ok $
        PE.subst₄ _⊢_≡_∷_
          (PE.cong (_»∙_ _) (PE.sym (PE.cong Erased B.OK-[])))
          PE.refl PE.refl
          (PE.trans (Target-[₀⇑] 0) $ PE.sym $ Target-[₀⇑] 1) $
        erasedrec-lemma-1 ≡Γ (Erased-cong Erased-ok (OK-1≡ ⊢Δ))

    opaque

      lam-lemma-2+ :
        drop k Δ PE.≡ Γ .vars →
        Γ .defs »⊢ Δ →
        Γ .defs » Δ ∙ ℕ ⊢
          lam 𝟙
            (erasedrec p
               (Target (3+ k) A₁ (suc (suc (var x2))) (var x0))
               (emptyrec-sink
                  (Target (3+ k) A₁ (suc (suc (var x2))) [ var x0 ])
                  (var x0))
               (var x0)) ≡
          lam 𝟙
            (erasedrec p
               (Target (3+ k) A₂ (suc (suc (var x2))) (var x0))
               (emptyrec-sink
                  (Target (3+ k) A₂ (suc (suc (var x2))) [ var x0 ])
                  (var x0))
               (var x0)) ∷
          (Π 𝟙 , p ▷ Erased (OK (suc (var x0))) ▹
           Target (2+ k) A₁ (suc (var x1)) (var x0))
            [ suc (var x0) ]↑
      lam-lemma-2+ PE.refl ⊢Δ =
        let ⊢OK₁  = ⊢OK (sucⱼ (sucⱼ (var₀ (ℕⱼ ⊢Δ))))
            ⊢OK₂  = Erasedⱼ Erased-ok ⊢OK₁
            ⊢OK₃  = wk₁ ⊢OK₂ ⊢OK₁
            lemma = PE.trans (PE.cong wk1 B.wk-OK) B.wk-OK
        in
        flip lam-cong Π-ok $
        PE.subst₄ _⊢_≡_∷_
          (PE.cong (_»∙_ _) $ PE.sym $ PE.cong Erased B.OK-[])
          PE.refl PE.refl
          (PE.trans (Target-[₀⇑] 0) $ PE.sym $ Target-[↑⇑] 1) $
        erasedrec-cong
          (Target-cong′ A₁≡A₂ (sucⱼ (sucⱼ (var₂ (wk₁ ⊢OK₂ ⊢OK₂)))) $
           PE.subst (_⊢_∷_ _ _) (PE.cong Erased lemma) $
           var₀ (wk₁ ⊢OK₂ ⊢OK₂))
          (PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym (Target-[↑⇑] 0)) $
           emptyrec-sink-cong Unitˢ-ok Π-𝟙-𝟘-ok
             (Target-cong′ A₁≡A₂ (sucⱼ (sucⱼ (var₂ ⊢OK₃))) $
              []ⱼ Erased-ok $
              PE.subst (_⊢_∷_ _ _) lemma $
              var₀ ⊢OK₃)
             (_⊢_≡_∷_.refl $
              _⊢_∷_.conv (var₀ ⊢OK₃) $
              PE.subst (flip (_⊢_≡_ _) _) (PE.sym lemma) $
              OK-2+≡ (var₂ ⊢OK₃)))
          (refl (var₀ ⊢OK₂))

    opaque

      natcase-lemma :
        drop k Δ PE.≡ Γ .vars →
        Γ .defs »⊢ Δ →
        Γ .defs » Δ ∙ ℕ ⊢
          natcase boolrecᵍ-nc₁ (Boolᵍ + p)
            (Π 𝟙 , p ▷ Erased (OK (suc (var x0))) ▹
             Target (3+ k) A₁ (suc (var x1)) (var x0))
            (lam 𝟙 $
             erasedrec p (Target (3+ k) A₁ (suc zero) (var x0))
               (unitrec 0 𝟘 𝟘 (Target (4+ k) A₁ (suc zero) [ var x0 ])
                  (var x0) (wk[ 3+ k ]′ t₁))
               (var x0))
            (lam 𝟙 $
             erasedrec p
               (Target (4+ k) A₁ (suc (suc (var x2))) (var x0))
               (emptyrec-sink
                  (Target (4+ k) A₁ (suc (suc (var x2))) [ var x0 ])
                  (var x0))
               (var x0))
            (var x0) ≡
          natcase boolrecᵍ-nc₁ (Boolᵍ + p)
            (Π 𝟙 , p ▷ Erased (OK (suc (var x0))) ▹
             Target (3+ k) A₂ (suc (var x1)) (var x0))
            (lam 𝟙 $
             erasedrec p (Target (3+ k) A₂ (suc zero) (var x0))
               (unitrec 0 𝟘 𝟘 (Target (4+ k) A₂ (suc zero) [ var x0 ])
                  (var x0) (wk[ 3+ k ]′ t₂))
               (var x0))
            (lam 𝟙 $
             erasedrec p
               (Target (4+ k) A₂ (suc (suc (var x2))) (var x0))
               (emptyrec-sink
                  (Target (4+ k) A₂ (suc (suc (var x2))) [ var x0 ])
                  (var x0))
               (var x0))
            (var x0) ∷
          (Π 𝟙 , p ▷ Erased (OK (var x0)) ▹
           Target (2+ k) A₁ (var x1) (var x0))
            [ suc (var x0) ]↑
      natcase-lemma ≡Γ ⊢Δ =
        let ⊢ℕ   = ℕⱼ ⊢Δ
            ⊢Δ∙ℕ = ∙ ⊢ℕ
        in
        PE.subst (_⊢_≡_∷_ _ _ _)
          (PE.cong₂ (ΠΣ⟨_⟩_,_▷_▹_ _ _ _)
             (PE.cong Erased $ PE.trans B.OK-[] $ PE.sym B.OK-[])
             (PE.trans (Target-[₀⇑] 1) $ PE.sym $ Target-[↑⇑] 1)) $
        natcase-cong
          (Π-lemma ≡Γ (sucⱼ (var₀ (ℕⱼ ⊢Δ∙ℕ))))
          (lam-lemma-1 ≡Γ ⊢Δ∙ℕ)
          (lam-lemma-2+ ≡Γ ⊢Δ∙ℕ)
          (refl (var₀ ⊢ℕ))

    opaque
      unfolding boolrec

      natcase-natcase-lemma :
        Γ »∙ ℕ »∙ Erased (OK (var x0)) ⊢
          natcase boolrecᵍ-nc₂ (Boolᵍ + p)
            (Π 𝟙 , p ▷ Erased (OK (var x0)) ▹
             Target 4 A₁ (var x1) (var x0))
            (lam 𝟙 $
             erasedrec p (Target 4 A₁ zero (var x0))
               (unitrec 0 𝟘 𝟘 (Target 5 A₁ zero [ var x0 ]) (var x0)
                  (wk[ 4 ]′ u₁))
               (var x0))
            (natcase boolrecᵍ-nc₁ (Boolᵍ + p)
               (Π 𝟙 , p ▷ Erased (OK (suc (var x0))) ▹
                Target 5 A₁ (suc (var x1)) (var x0))
               (lam 𝟙 $
                erasedrec p (Target 5 A₁ (suc zero) (var x0))
                  (unitrec 0 𝟘 𝟘 (Target 6 A₁ (suc zero) [ var x0 ])
                     (var x0) (wk[ 5 ]′ t₁))
                  (var x0))
               (lam 𝟙 $
                erasedrec p
                  (Target 6 A₁ (suc (suc (var x2))) (var x0))
                  (emptyrec-sink
                     (Target 6 A₁ (suc (suc (var x2))) [ var x0 ])
                     (var x0))
                  (var x0))
               (var x0))
            (var x1) ∘⟨ 𝟙 ⟩
          (var x0) ≡
          natcase boolrecᵍ-nc₂ (Boolᵍ + p)
            (Π 𝟙 , p ▷ Erased (OK (var x0)) ▹
             Target 4 A₂ (var x1) (var x0))
            (lam 𝟙 $
             erasedrec p (Target 4 A₂ zero (var x0))
               (unitrec 0 𝟘 𝟘 (Target 5 A₂ zero [ var x0 ]) (var x0)
                  (wk[ 4 ]′ u₂))
               (var x0))
            (natcase boolrecᵍ-nc₁ (Boolᵍ + p)
               (Π 𝟙 , p ▷ Erased (OK (suc (var x0))) ▹
                Target 5 A₂ (suc (var x1)) (var x0))
               (lam 𝟙 $
                erasedrec p (Target 5 A₂ (suc zero) (var x0))
                  (unitrec 0 𝟘 𝟘 (Target 6 A₂ (suc zero) [ var x0 ])
                     (var x0) (wk[ 5 ]′ t₂))
                  (var x0))
               (lam 𝟙 $
                erasedrec p
                  (Target 6 A₂ (suc (suc (var x2))) (var x0))
                  (emptyrec-sink
                     (Target 6 A₂ (suc (suc (var x2))) [ var x0 ])
                     (var x0))
                  (var x0))
               (var x0))
            (var x1) ∘⟨ 𝟙 ⟩
          (var x0) ∷
          A₁ [ prodʷ 𝟙 (var x1) (var x0) ]↑²
      natcase-natcase-lemma =
        let ⊢OK = ⊢Erased-OK (var₀ (ℕⱼ ⊢Γ)) in
        PE.subst (_⊢_≡_∷_ _ _ _)
          (PE.trans (PE.cong _[ _ ]₀ $ Target-[₀⇑] 1) $
           PE.trans (Target-[₀⇑] 0) Target≡) $
        app-cong
          (PE.subst (_⊢_≡_∷_ _ _ _)
             (PE.cong₂ (ΠΣ⟨_⟩_,_▷_▹_ _ _ _)
                (PE.cong Erased $ PE.trans B.OK-[] $ PE.sym B.wk-OK)
                PE.refl) $
           natcase-cong
             (Π-lemma PE.refl (var₀ (ℕⱼ (∙ ⊢OK))))
             (lam-lemma-0 PE.refl (∙ ⊢OK))
             (natcase-lemma PE.refl (∙ ⊢OK))
             (refl (var₁ ⊢OK)))
          (refl (var₀ ⊢OK))

private opaque

  -- Some lemmas used below.

  natcase-natcase-[,]₁₀ :
    (natcase boolrecᵍ-nc₂ (Boolᵍ + p)
       (Π 𝟙 , p ▷ Erased (OK (var x0)) ▹
        Target 4 A (var x1) (var x0))
       (lam 𝟙 $
        erasedrec p (Target 4 A zero (var x0))
          (unitrec 0 𝟘 𝟘 (Target 5 A zero [ var x0 ]) (var x0)
             (wk[ 4 ]′ u))
          (var x0))
       (natcase boolrecᵍ-nc₁ (Boolᵍ + p)
          (Π 𝟙 , p ▷ Erased (OK (suc (var x0))) ▹
           Target 5 A (suc (var x1)) (var x0))
          (lam 𝟙 $
           erasedrec p (Target 5 A (suc zero) (var x0))
             (unitrec 0 𝟘 𝟘 (Target 6 A (suc zero) [ var x0 ])
                (var x0) (wk[ 5 ]′ t))
             (var x0))
          (lam 𝟙 $
           erasedrec p
             (Target 6 A (suc (suc (var x2))) (var x0))
             (emptyrec-sink
                (Target 6 A (suc (suc (var x2))) [ var x0 ])
                (var x0))
             (var x0))
          (var x0))
       (var x1)
       [ v , [ starʷ 0 ] ]₁₀)  ∘⟨ 𝟙 ⟩
    [ starʷ 0 ] PE.≡
    natcase boolrecᵍ-nc₂ (Boolᵍ + p)
      (Π 𝟙 , p ▷ Erased (OK (var x0)) ▹
       Target 2 A (var x1) (var x0))
      (lam 𝟙 $
       erasedrec p (Target 2 A zero (var x0))
         (unitrec 0 𝟘 𝟘 (Target 3 A zero [ var x0 ]) (var x0)
            (wk[ 2 ]′ u))
         (var x0))
      (natcase boolrecᵍ-nc₁ (Boolᵍ + p)
         (Π 𝟙 , p ▷ Erased (OK (suc (var x0))) ▹
          Target 3 A (suc (var x1)) (var x0))
         (lam 𝟙 $
          erasedrec p (Target 3 A (suc zero) (var x0))
            (unitrec 0 𝟘 𝟘 (Target 4 A (suc zero) [ var x0 ])
               (var x0) (wk[ 3 ]′ t))
            (var x0))
         (lam 𝟙 $
          erasedrec p
            (Target 4 A (suc (suc (var x2))) (var x0))
            (emptyrec-sink
               (Target 4 A (suc (suc (var x2))) [ var x0 ])
               (var x0))
            (var x0))
         (var x0))
      v ∘⟨ 𝟙 ⟩
    [ starʷ 0 ]
  natcase-natcase-[,]₁₀ =
    PE.cong (flip _∘⟨ 𝟙 ⟩_ _) $
    PE.trans natcase-[] $
    PE.cong₄ (natcase _ _)
      (PE.cong₂ (ΠΣ⟨_⟩_,_▷_▹_ _ _ _)
         (PE.cong Erased B.OK-[]) (Target-[,⇑] 2))
      (PE.cong (lam _) $
       PE.trans erasedrec-[] $
       PE.cong₃ (erasedrec _)
         (Target-[,⇑] 2)
         (PE.cong₃ (unitrec _ _ _)
            (Target-[,⇑] 3) PE.refl wk[2+]′[,⇑]≡)
         PE.refl)
      (PE.trans natcase-[] $
       PE.cong₄ (natcase _ _)
         (PE.cong₂ (ΠΣ⟨_⟩_,_▷_▹_ _ _ _)
            (PE.cong Erased B.OK-[]) (Target-[,⇑] 3))
         (PE.cong (lam _) $
          PE.trans erasedrec-[] $
          PE.cong₃ (erasedrec _)
            (Target-[,⇑] 3)
            (PE.cong₃ (unitrec _ _ _)
               (Target-[,⇑] 4) PE.refl wk[2+]′[,⇑]≡)
            PE.refl)
         (PE.cong (lam _) $
          PE.trans erasedrec-[] $
          PE.cong₃ (erasedrec _)
            (Target-[,⇑] 4)
            (PE.trans emptyrec-sink-[] $
             PE.cong₂ emptyrec-sink (Target-[,⇑] 4) PE.refl)
            PE.refl)
         PE.refl)
      PE.refl

opaque
  unfolding Bool boolrec

  -- An equality rule for boolrec.

  boolrec-cong :
    Π-allowed 𝟙 p →
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
    Π-allowed 𝟙 p →
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

  -- An equality rule for boolrec.

  boolrec-true-≡ :
    Π-allowed 𝟙 p →
    Π-allowed 𝟙 𝟘 →
    Unitˢ-allowed →
    Γ »∙ Bool ⊢ A →
    Γ ⊢ t ∷ A [ true ]₀ →
    Γ ⊢ u ∷ A [ false ]₀ →
    Γ ⊢ boolrec p A t u true ≡ t ∷ A [ true ]₀
  boolrec-true-≡ {p} {Γ} {A} {t} {u} Π-ok Π-𝟙-𝟘-ok Unitˢ-ok ⊢A ⊢t ⊢u =
    prodrec boolrecᵍ-pr 𝟙 p A
      (prodʷ 𝟙 (suc zero) [ starʷ 0 ])
      (natcase boolrecᵍ-nc₂ (Boolᵍ + p)
         (Π 𝟙 , p ▷ Erased (OK (var x0)) ▹ Target 4 A (var x1) (var x0))
         (lam 𝟙 $
          erasedrec p (Target 4 A zero (var x0))
            (unitrec 0 𝟘 𝟘 (Target 5 A zero [ var x0 ]) (var x0)
               (wk[ 4 ]′ u))
            (var x0))
         (natcase boolrecᵍ-nc₁ (Boolᵍ + p)
            (Π 𝟙 , p ▷ Erased (OK (suc (var x0))) ▹
             Target 5 A (suc (var x1)) (var x0))
            (lam 𝟙 $
             erasedrec p (Target 5 A (suc zero) (var x0))
               (unitrec 0 𝟘 𝟘 (Target 6 A (suc zero) [ var x0 ])
                  (var x0) (wk[ 5 ]′ t))
               (var x0))
            (lam 𝟙 $
             erasedrec p (Target 6 A (suc (suc (var x2))) (var x0))
               (emptyrec-sink
                  (Target 6 A (suc (suc (var x2))) [ var x0 ])
                  (var x0))
               (var x0))
            (var x0))
         (var x1) ∘⟨ 𝟙 ⟩
       var x0)                                                            ⇒⟨ prodrec-β-⇒ ⊢A (sucⱼ (zeroⱼ ⊢Γ))
                                                                               (_⊢_∷_.conv ⊢[starʷ] $
                                                                                PE.subst (_⊢_≡_ _ _) (PE.cong Erased $ PE.sym B.OK-[]) $
                                                                                Erased-cong Erased-ok $ sym $ OK-1≡ ⊢Γ)
                                                                               (syntacticEqTerm natcase-natcase-lemma .proj₂ .proj₁) ⟩⊢
    (natcase boolrecᵍ-nc₂ (Boolᵍ + p)
       (Π 𝟙 , p ▷ Erased (OK (var x0)) ▹ Target 4 A (var x1) (var x0))
       (lam 𝟙 $
        erasedrec p (Target 4 A zero (var x0))
          (unitrec 0 𝟘 𝟘 (Target 5 A zero [ var x0 ]) (var x0)
             (wk[ 4 ]′ u))
          (var x0))
       (natcase boolrecᵍ-nc₁ (Boolᵍ + p)
          (Π 𝟙 , p ▷ Erased (OK (suc (var x0))) ▹
           Target 5 A (suc (var x1)) (var x0))
          (lam 𝟙 $
           erasedrec p (Target 5 A (suc zero) (var x0))
             (unitrec 0 𝟘 𝟘 (Target 6 A (suc zero) [ var x0 ])
                (var x0) (wk[ 5 ]′ t))
             (var x0))
          (lam 𝟙 $
           erasedrec p (Target 6 A (suc (suc (var x2))) (var x0))
             (emptyrec-sink
                (Target 6 A (suc (suc (var x2))) [ var x0 ])
                (var x0))
             (var x0))
          (var x0))
       (var x1)
       [ suc zero , [ starʷ 0 ] ]₁₀) ∘⟨ 𝟙 ⟩
    [ starʷ 0 ]                                                           ≡⟨ natcase-natcase-[,]₁₀ ⟩⊢≡

    natcase boolrecᵍ-nc₂ (Boolᵍ + p)
      (Π 𝟙 , p ▷ Erased (OK (var x0)) ▹
       Target 2 A (var x1) (var x0))
      (lam 𝟙 $
       erasedrec p (Target 2 A zero (var x0))
         (unitrec 0 𝟘 𝟘 (Target 3 A zero [ var x0 ]) (var x0)
            (wk[ 2 ]′ u))
         (var x0))
      (natcase boolrecᵍ-nc₁ (Boolᵍ + p)
         (Π 𝟙 , p ▷ Erased (OK (suc (var x0))) ▹
          Target 3 A (suc (var x1)) (var x0))
         (lam 𝟙 $
          erasedrec p (Target 3 A (suc zero) (var x0))
            (unitrec 0 𝟘 𝟘 (Target 4 A (suc zero) [ var x0 ])
               (var x0) (wk[ 3 ]′ t))
            (var x0))
         (lam 𝟙 $
          erasedrec p
            (Target 4 A (suc (suc (var x2))) (var x0))
            (emptyrec-sink
               (Target 4 A (suc (suc (var x2))) [ var x0 ])
               (var x0))
            (var x0))
         (var x0))
      (suc zero) ∘⟨ 𝟙 ⟩
    [ starʷ 0 ]                                                           ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _) (PE.trans (Target-[₀⇑] 0) Target≡) $
                                                                             app-subst
                                                                               (conv
                                                                                  (natcase-suc-⇒
                                                                                     (syntacticEq (Π-lemma PE.refl (var₀ (ℕⱼ ⊢Γ))) .proj₁)
                                                                                     (syntacticEqTerm (lam-lemma-0 PE.refl ⊢Γ) .proj₂ .proj₁)
                                                                                     (syntacticEqTerm (natcase-lemma PE.refl ⊢Γ) .proj₂ .proj₁)
                                                                                     (zeroⱼ ⊢Γ))
                                                                                  (Π-[]₀-lemma (sucⱼ (zeroⱼ ⊢Γ)) (OK-1≡ ⊢Γ)))
                                                                               ⊢[starʷ] ⟩⊢
    (natcase boolrecᵍ-nc₁ (Boolᵍ + p)
       (Π 𝟙 , p ▷ Erased (OK (suc (var x0))) ▹
        Target 3 A (suc (var x1)) (var x0))
       (lam 𝟙 $
        erasedrec p (Target 3 A (suc zero) (var x0))
          (unitrec 0 𝟘 𝟘 (Target 4 A (suc zero) [ var x0 ])
             (var x0) (wk[ 3 ]′ t))
          (var x0))
       (lam 𝟙 $
        erasedrec p
          (Target 4 A (suc (suc (var x2))) (var x0))
          (emptyrec-sink
             (Target 4 A (suc (suc (var x2))) [ var x0 ])
             (var x0))
          (var x0))
       (var x0)
       [ zero ]₀) ∘⟨ 𝟙 ⟩
    [ starʷ 0 ]                                                           ≡⟨ PE.cong (_∘⟨ 𝟙 ⟩ _) $
                                                                             PE.trans natcase-[] $
                                                                             PE.cong₄ (natcase _ _)
                                                                               (PE.cong₂ (ΠΣ⟨_⟩_,_▷_▹_ _ _ _)
                                                                                  (PE.cong Erased B.OK-[]) (Target-[₀⇑] 2))
                                                                               (PE.cong (lam 𝟙) $
                                                                                PE.trans erasedrec-[] $
                                                                                 PE.cong₃ (erasedrec _)
                                                                                   (Target-[₀⇑] 2)
                                                                                   (PE.cong₃ (unitrec _ _ _)
                                                                                      (Target-[₀⇑] 3) PE.refl wk[+1]′-[₀⇑]≡)
                                                                                   PE.refl)
                                                                               (PE.cong (lam 𝟙) $
                                                                                PE.trans erasedrec-[] $
                                                                                PE.cong₃ (erasedrec _)
                                                                                  (Target-[₀⇑] 3)
                                                                                  (PE.trans emptyrec-sink-[] $
                                                                                   PE.cong₂ emptyrec-sink (Target-[₀⇑] 3) PE.refl)
                                                                                  PE.refl)
                                                                               PE.refl ⟩⊢≡
    natcase boolrecᵍ-nc₁ (Boolᵍ + p)
      (Π 𝟙 , p ▷ Erased (OK (suc (var x0))) ▹
       Target 2 A (suc (var x1)) (var x0))
       (lam 𝟙 $
        erasedrec p (Target 2 A (suc zero) (var x0))
          (unitrec 0 𝟘 𝟘 (Target 3 A (suc zero) [ var x0 ])
             (var x0) (wk[ 2 ]′ t))
          (var x0))
       (lam 𝟙 $
        erasedrec p
          (Target 3 A (suc (suc (var x2))) (var x0))
          (emptyrec-sink
             (Target 3 A (suc (suc (var x2))) [ var x0 ])
             (var x0))
          (var x0))
      zero ∘⟨ 𝟙 ⟩
    [ starʷ 0 ]                                                           ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _) (PE.trans (Target-[₀⇑] 0) Target≡) $
                                                                             app-subst
                                                                               (conv
                                                                                  (natcase-zero-⇒
                                                                                     (syntacticEq (Π-lemma PE.refl (sucⱼ (var₀ (ℕⱼ ⊢Γ)))) .proj₁)
                                                                                     (syntacticEqTerm (lam-lemma-1 PE.refl ⊢Γ) .proj₂ .proj₁)
                                                                                     (syntacticEqTerm (lam-lemma-2+ PE.refl ⊢Γ) .proj₂ .proj₁))
                                                                                  (Π-[]₀-lemma (sucⱼ (zeroⱼ ⊢Γ)) (OK-1≡ ⊢Γ)))
                                                                               ⊢[starʷ] ⟩⊢
    lam 𝟙
      (erasedrec p (Target 2 A (suc zero) (var x0))
         (unitrec 0 𝟘 𝟘 (Target 3 A (suc zero) [ var x0 ])
            (var x0) (wk[ 2 ]′ t))
         (var x0)) ∘⟨ 𝟙 ⟩
    [ starʷ 0 ]                                                           ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _)
                                                                               (PE.trans (PE.cong _[ _ ]₀ $ Target-[₀⇑] 0) $
                                                                                PE.trans (Target-[₀⇑] 0) Target≡) $
                                                                             β-red-⇒
                                                                               (syntacticEqTerm (erasedrec-lemma-1 PE.refl (refl ⊢Erased-Unitʷ))
                                                                                  .proj₂ .proj₁)
                                                                               ⊢[starʷ] Π-ok ⟩⊢
    erasedrec p (Target 2 A (suc zero) (var x0))
      (unitrec 0 𝟘 𝟘 (Target 3 A (suc zero) [ var x0 ])
         (var x0) (wk[ 2 ]′ t))
      (var x0)
      [ [ starʷ 0 ] ]₀                                                    ≡⟨ PE.trans erasedrec-[] $
                                                                             PE.cong₃ (erasedrec _)
                                                                               (Target-[₀⇑] 1)
                                                                               (PE.cong₃ (unitrec _ _ _) (Target-[₀⇑] 2) PE.refl wk[+1]′-[₀⇑]≡)
                                                                               PE.refl ⟩⊢≡
    erasedrec p (Target 1 A (suc zero) (var x0))
      (unitrec 0 𝟘 𝟘 (Target 2 A (suc zero) [ var x0 ])
         (var x0) (wk1 t))
      [ starʷ 0 ]                                                         ≡⟨ PE.subst (_⊢_≡_∷_ _ _ _) (PE.trans (Target-[₀⇑] 0) $ Target≡) $
                                                                             erasedrec-β
                                                                               (syntacticEq (Target-lemma-1 PE.refl (var₀ ⊢Erased-Unitʷ)) .proj₁)
                                                                               (syntacticEqTerm (unitrec-lemma-1 PE.refl ⊢Γ) .proj₂ .proj₁)
                                                                               (starⱼ ⊢Γ Unitʷ-ok) ⟩⊢

    unitrec 0 𝟘 𝟘 (Target 2 A (suc zero) [ var x0 ]) (var x0) (wk1 t)
      [ starʷ 0 ]₀                                                        ≡⟨ PE.cong₃ (unitrec _ _ _)
                                                                               (Target-[₀⇑] 1) PE.refl (wk1-sgSubst _ _) ⟩⊢≡

    unitrec 0 𝟘 𝟘 (Target 1 A (suc zero) [ var x0 ]) (starʷ 0) t          ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _) (PE.trans (Target-[₀⇑] 0) Target≡) $
                                                                             unitrec-β-⇒
                                                                               (syntacticEq
                                                                                  (Target-lemma-1 PE.refl ([]ⱼ Erased-ok (var₀ ⊢Unitʷ))) .proj₁)
                                                                               (PE.subst (flip (_⊢_∷_ _) _) (wk-id _) $
                                                                                syntacticEqTerm (wk-t₁≡wk-t₂ PE.refl ⊢Γ) .proj₂ .proj₁) ⟩⊢∎
    t                                                                     ∎
    where
    open Boolrec Π-ok Π-𝟙-𝟘-ok Unitˢ-ok (refl ⊢A) (refl ⊢t) (refl ⊢u)
    open TmR

opaque
  unfolding Bool false boolrec

  -- An equality rule for boolrec.

  boolrec-false-≡ :
    Π-allowed 𝟙 p →
    Π-allowed 𝟙 𝟘 →
    Unitˢ-allowed →
    Γ »∙ Bool ⊢ A →
    Γ ⊢ t ∷ A [ true ]₀ →
    Γ ⊢ u ∷ A [ false ]₀ →
    Γ ⊢ boolrec p A t u false ≡ u ∷ A [ false ]₀
  boolrec-false-≡ {p} {Γ} {A} {t} {u} Π-ok Π-𝟙-𝟘-ok Unitˢ-ok ⊢A ⊢t ⊢u =
    prodrec boolrecᵍ-pr 𝟙 p A (prodʷ 𝟙 zero [ starʷ 0 ])
      (natcase boolrecᵍ-nc₂ (Boolᵍ + p)
         (Π 𝟙 , p ▷ Erased (OK (var x0)) ▹ Target 4 A (var x1) (var x0))
         (lam 𝟙 $
          erasedrec p (Target 4 A zero (var x0))
            (unitrec 0 𝟘 𝟘 (Target 5 A zero [ var x0 ]) (var x0)
               (wk[ 4 ]′ u))
            (var x0))
         (natcase boolrecᵍ-nc₁ (Boolᵍ + p)
            (Π 𝟙 , p ▷ Erased (OK (suc (var x0))) ▹
             Target 5 A (suc (var x1)) (var x0))
            (lam 𝟙 $
             erasedrec p (Target 5 A (suc zero) (var x0))
               (unitrec 0 𝟘 𝟘 (Target 6 A (suc zero) [ var x0 ])
                  (var x0) (wk[ 5 ]′ t))
               (var x0))
            (lam 𝟙 $
             erasedrec p (Target 6 A (suc (suc (var x2))) (var x0))
               (emptyrec-sink
                  (Target 6 A (suc (suc (var x2))) [ var x0 ])
                  (var x0))
               (var x0))
            (var x0))
         (var x1) ∘⟨ 𝟙 ⟩
       var x0)                                                            ⇒⟨ prodrec-β-⇒ ⊢A (zeroⱼ ⊢Γ)
                                                                               (_⊢_∷_.conv ⊢[starʷ] $
                                                                                PE.subst (_⊢_≡_ _ _) (PE.cong Erased $ PE.sym B.OK-[]) $
                                                                                Erased-cong Erased-ok $ sym $ OK-0≡ ⊢Γ)
                                                                               (syntacticEqTerm natcase-natcase-lemma .proj₂ .proj₁) ⟩⊢
    (natcase boolrecᵍ-nc₂ (Boolᵍ + p)
       (Π 𝟙 , p ▷ Erased (OK (var x0)) ▹ Target 4 A (var x1) (var x0))
       (lam 𝟙 $
        erasedrec p (Target 4 A zero (var x0))
          (unitrec 0 𝟘 𝟘 (Target 5 A zero [ var x0 ]) (var x0)
             (wk[ 4 ]′ u))
          (var x0))
       (natcase boolrecᵍ-nc₁ (Boolᵍ + p)
          (Π 𝟙 , p ▷ Erased (OK (suc (var x0))) ▹
           Target 5 A (suc (var x1)) (var x0))
          (lam 𝟙 $
           erasedrec p (Target 5 A (suc zero) (var x0))
             (unitrec 0 𝟘 𝟘 (Target 6 A (suc zero) [ var x0 ])
                (var x0) (wk[ 5 ]′ t))
             (var x0))
          (lam 𝟙 $
           erasedrec p (Target 6 A (suc (suc (var x2))) (var x0))
             (emptyrec-sink
                (Target 6 A (suc (suc (var x2))) [ var x0 ])
                (var x0))
             (var x0))
          (var x0))
       (var x1)
       [ zero , [ starʷ 0 ] ]₁₀) ∘⟨ 𝟙 ⟩
    [ starʷ 0 ]                                                           ≡⟨ natcase-natcase-[,]₁₀ ⟩⊢≡

    natcase boolrecᵍ-nc₂ (Boolᵍ + p)
      (Π 𝟙 , p ▷ Erased (OK (var x0)) ▹
       Target 2 A (var x1) (var x0))
      (lam 𝟙 $
       erasedrec p (Target 2 A zero (var x0))
         (unitrec 0 𝟘 𝟘 (Target 3 A zero [ var x0 ]) (var x0)
            (wk[ 2 ]′ u))
         (var x0))
      (natcase boolrecᵍ-nc₁ (Boolᵍ + p)
         (Π 𝟙 , p ▷ Erased (OK (suc (var x0))) ▹
          Target 3 A (suc (var x1)) (var x0))
         (lam 𝟙 $
          erasedrec p (Target 3 A (suc zero) (var x0))
            (unitrec 0 𝟘 𝟘 (Target 4 A (suc zero) [ var x0 ])
               (var x0) (wk[ 3 ]′ t))
            (var x0))
         (lam 𝟙 $
          erasedrec p
            (Target 4 A (suc (suc (var x2))) (var x0))
            (emptyrec-sink
               (Target 4 A (suc (suc (var x2))) [ var x0 ])
               (var x0))
            (var x0))
         (var x0))
      zero ∘⟨ 𝟙 ⟩
    [ starʷ 0 ]                                                           ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _) (PE.trans (Target-[₀⇑] 0) Target≡) $
                                                                             app-subst
                                                                               (conv
                                                                                  (natcase-zero-⇒
                                                                                     (syntacticEq (Π-lemma PE.refl (var₀ (ℕⱼ ⊢Γ))) .proj₁)
                                                                                     (syntacticEqTerm (lam-lemma-0 PE.refl ⊢Γ) .proj₂ .proj₁)
                                                                                     (syntacticEqTerm (natcase-lemma PE.refl ⊢Γ) .proj₂ .proj₁))
                                                                                  (Π-[]₀-lemma (zeroⱼ ⊢Γ) (OK-0≡ ⊢Γ)))
                                                                               ⊢[starʷ] ⟩⊢
    lam 𝟙
      (erasedrec p (Target 2 A zero (var x0))
         (unitrec 0 𝟘 𝟘 (Target 3 A zero [ var x0 ]) (var x0)
            (wk[ 2 ]′ u))
         (var x0)) ∘⟨ 𝟙 ⟩
    [ starʷ 0 ]                                                           ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _)
                                                                               (PE.trans (PE.cong _[ _ ]₀ $ Target-[₀⇑] 0) $
                                                                                PE.trans (Target-[₀⇑] 0) Target≡) $
                                                                             β-red-⇒
                                                                               (syntacticEqTerm (erasedrec-lemma-0 PE.refl (refl ⊢Erased-Unitʷ))
                                                                                  .proj₂ .proj₁)
                                                                               ⊢[starʷ] Π-ok ⟩⊢
    erasedrec p (Target 2 A zero (var x0))
      (unitrec 0 𝟘 𝟘 (Target 3 A zero [ var x0 ]) (var x0)
         (wk[ 2 ]′ u))
      (var x0)
      [ [ starʷ 0 ] ]₀                                                    ≡⟨ PE.trans erasedrec-[] $
                                                                             PE.cong₃ (erasedrec _)
                                                                               (Target-[₀⇑] 1)
                                                                               (PE.cong₃ (unitrec _ _ _) (Target-[₀⇑] 2) PE.refl wk[+1]′-[₀⇑]≡)
                                                                               PE.refl ⟩⊢≡
    erasedrec p (Target 1 A zero (var x0))
      (unitrec 0 𝟘 𝟘 (Target 2 A zero [ var x0 ]) (var x0) (wk1 u))
      [ starʷ 0 ]                                                         ≡⟨ PE.subst (_⊢_≡_∷_ _ _ _) (PE.trans (Target-[₀⇑] 0) $ Target≡) $
                                                                             erasedrec-β
                                                                               (syntacticEq (Target-lemma-0 PE.refl (var₀ ⊢Erased-Unitʷ)) .proj₁)
                                                                               (syntacticEqTerm (unitrec-lemma-0 PE.refl ⊢Γ) .proj₂ .proj₁)
                                                                               (starⱼ ⊢Γ Unitʷ-ok) ⟩⊢
    unitrec 0 𝟘 𝟘 (Target 2 A zero [ var x0 ]) (var x0) (wk1 u)
      [ starʷ 0 ]₀                                                        ≡⟨ PE.cong₃ (unitrec _ _ _)
                                                                               (Target-[₀⇑] 1) PE.refl (wk1-sgSubst _ _) ⟩⊢≡

    unitrec 0 𝟘 𝟘 (Target 1 A zero [ var x0 ]) (starʷ 0) u                ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _) (PE.trans (Target-[₀⇑] 0) Target≡) $
                                                                             unitrec-β-⇒
                                                                               (syntacticEq (Target-lemma-0 PE.refl ([]ⱼ Erased-ok (var₀ ⊢Unitʷ)))
                                                                                  .proj₁)
                                                                               (PE.subst (flip (_⊢_∷_ _) _) (wk-id _) $
                                                                                syntacticEqTerm (wk-u₁≡wk-u₂ PE.refl ⊢Γ) .proj₂ .proj₁) ⟩⊢∎
    u                                                                     ∎
    where
    open Boolrec Π-ok Π-𝟙-𝟘-ok Unitˢ-ok (refl ⊢A) (refl ⊢t) (refl ⊢u)
    open TmR
