------------------------------------------------------------------------
-- Booleans
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Definition.Untyped.Bool
open import Definition.Untyped.NotParametrised using (Strength)
open import Graded.Modality
import Graded.Modality.Dedicated-nr

module Definition.Typed.Consequences.DerivedRules.Bool
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  (open Graded.Modality.Dedicated-nr 𝕄)
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  -- One can define the booleans using either weak or strong Σ and
  -- unit types.
  {s : Strength}
  (open Definition.Untyped.Bool 𝕄 s)
  -- It is assumed that there is a dedicated nr function.
  ⦃ has-nr : Dedicated-nr ⦄
  -- It is assumed that certain Σ-types are allowed.
  (Σ-ok : Σ-allowed s 𝟙 Boolᵍ)
  -- It is assumed that certain unit types are allowed.
  (Unit-ok : Unit-allowed s)
  where

open import Definition.Typed R
open import Definition.Typed.Consequences.DerivedRules.Nat R
open import Definition.Typed.Consequences.DerivedRules.Pi R
open import Definition.Typed.Consequences.DerivedRules.Pi-Sigma R
open import Definition.Typed.Consequences.DerivedRules.Sigma R
open import Definition.Typed.Consequences.DerivedRules.Unit R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Properties R
import Definition.Typed.Reasoning.Term R as TmR
import Definition.Typed.Reasoning.Type R as TyR
open import Definition.Typed.Weakening R

open import Definition.Untyped M
open import Definition.Untyped.Nat 𝕄
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sigma 𝕄
open import Definition.Untyped.Unit 𝕄

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+; 2+; 3+)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private variable
  k                                 : Nat
  Γ Δ                               : Con Term _
  A A₁ A₂ B t t₁ t₂ u u₁ u₂ v v₁ v₂ : Term _
  p                                 : M

------------------------------------------------------------------------
-- Typing rules for OK

opaque
  unfolding OK

  -- An equality rule for OK.

  OK-cong-U :
    Γ ⊢ t₁ ≡ t₂ ∷ ℕ →
    Γ ⊢ OK t₁ ≡ OK t₂ ∷ U 0
  OK-cong-U {Γ} t₁≡t₂ =
    natcase-cong (refl (Uⱼ (⊢→⊢∙ ⊢ℕ₁)))
      (refl (Unitⱼ ⊢Γ Unit-ok))
      (refl $
       ⊢natcase (Uⱼ (⊢→⊢∙ ⊢ℕ₂))
         (Unitⱼ (⊢→⊢∙ ⊢ℕ₁) Unit-ok)
         (Emptyⱼ (⊢→⊢∙ ⊢ℕ₂))
         (var₀ ⊢ℕ₁))
      t₁≡t₂
    where
    ⊢Γ : ⊢ Γ
    ⊢Γ = wfEqTerm t₁≡t₂

    ⊢ℕ₁ : Γ ⊢ ℕ
    ⊢ℕ₁ = ℕⱼ ⊢Γ

    ⊢ℕ₂ : Γ ∙ ℕ ⊢ ℕ
    ⊢ℕ₂ = ℕⱼ (⊢→⊢∙ ⊢ℕ₁)

opaque

  -- An equality rule for OK.

  OK-cong :
    Γ ⊢ t₁ ≡ t₂ ∷ ℕ →
    Γ ⊢ OK t₁ ≡ OK t₂
  OK-cong = univ ∘→ OK-cong-U

opaque

  -- A typing rule for OK.

  ⊢OK∷U :
    Γ ⊢ t ∷ ℕ →
    Γ ⊢ OK t ∷ U 0
  ⊢OK∷U ⊢t =
    syntacticEqTerm (OK-cong-U (refl ⊢t)) .proj₂ .proj₁

opaque

  -- A typing rule for OK.

  ⊢OK :
    Γ ⊢ t ∷ ℕ →
    Γ ⊢ OK t
  ⊢OK = univ ∘→ ⊢OK∷U

opaque
  unfolding OK

  -- An equality rule for OK.

  OK-0≡ :
    ⊢ Γ →
    Γ ⊢ OK zero ≡ Unit s 0
  OK-0≡ ⊢Γ =
    OK zero                                               ≡⟨⟩⊢

    natcase OKᵍ 𝟘 (U 0) (Unit s 0)
      (natcase 𝟘 𝟘 (U 0) (Unit s 0) Empty (var x0)) zero  ≡⟨ univ $
                                                             natcase-zero-≡ (Uⱼ (⊢Γ ∙[ ℕⱼ ])) (Unitⱼ ⊢Γ Unit-ok) $
                                                             ⊢natcase (Uⱼ (⊢Γ ∙[ ℕⱼ ] ∙[ ℕⱼ ])) (Unitⱼ (⊢Γ ∙[ ℕⱼ ]) Unit-ok)
                                                               (Emptyⱼ (⊢Γ ∙[ ℕⱼ ] ∙[ ℕⱼ ])) (var₀ (ℕⱼ ⊢Γ)) ⟩⊢∎
    Unit s 0                                              ∎
    where
    open TyR

opaque
  unfolding OK

  -- An equality rule for OK.

  OK-1≡ :
    ⊢ Γ →
    Γ ⊢ OK (suc zero) ≡ Unit s 0
  OK-1≡ ⊢Γ =
    OK (suc zero)                                               ≡⟨⟩⊢

    natcase OKᵍ 𝟘 (U 0) (Unit s 0)
      (natcase 𝟘 𝟘 (U 0) (Unit s 0) Empty (var x0)) (suc zero)  ≡⟨ PE.subst (_⊢_≡_ _ _) natcase-[] $
                                                                   _⊢_≡_.univ $
                                                                   natcase-suc-≡ (Uⱼ (⊢Γ ∙[ ℕⱼ ])) (Unitⱼ ⊢Γ Unit-ok)
                                                                     (⊢natcase (Uⱼ (⊢Γ ∙[ ℕⱼ ] ∙[ ℕⱼ ])) (Unitⱼ (⊢Γ ∙[ ℕⱼ ]) Unit-ok)
                                                                        (Emptyⱼ (⊢Γ ∙[ ℕⱼ ] ∙[ ℕⱼ ])) (var₀ (ℕⱼ ⊢Γ)))
                                                                     (zeroⱼ ⊢Γ) ⟩⊢

    natcase 𝟘 𝟘 (U 0) (Unit s 0) Empty zero                     ≡⟨ univ $
                                                                   natcase-zero-≡ (Uⱼ (⊢Γ ∙[ ℕⱼ ])) (Unitⱼ ⊢Γ Unit-ok)
                                                                     (Emptyⱼ (⊢Γ ∙[ ℕⱼ ])) ⟩⊢∎
    Unit s 0                                                    ∎
    where
    open TyR

opaque
  unfolding OK

  -- An equality rule for OK.

  OK-2+≡ :
    Γ ⊢ t ∷ ℕ →
    Γ ⊢ OK (suc (suc t)) ≡ Empty
  OK-2+≡ {Γ} {t} ⊢t =
    OK (suc (suc t))                                               ≡⟨⟩⊢

    natcase OKᵍ 𝟘 (U 0) (Unit s 0)
      (natcase 𝟘 𝟘 (U 0) (Unit s 0) Empty (var x0)) (suc (suc t))  ≡⟨ PE.subst (_⊢_≡_ _ _) natcase-[] $
                                                                      _⊢_≡_.univ $
                                                                      natcase-suc-≡ (Uⱼ (⊢→⊢∙ ⊢ℕ₁)) (Unitⱼ ⊢Γ Unit-ok)
                                                                        (⊢natcase (Uⱼ (⊢→⊢∙ ⊢ℕ₂)) (Unitⱼ (⊢→⊢∙ ⊢ℕ₁) Unit-ok)
                                                                           (Emptyⱼ (⊢→⊢∙ ⊢ℕ₂)) (var₀ ⊢ℕ₁))
                                                                        (sucⱼ ⊢t) ⟩⊢

    natcase 𝟘 𝟘 (U 0) (Unit s 0) Empty (suc t)                     ≡⟨ univ $
                                                                      natcase-suc-≡ (Uⱼ (⊢→⊢∙ ⊢ℕ₁)) (Unitⱼ ⊢Γ Unit-ok)
                                                                        (Emptyⱼ (⊢→⊢∙ ⊢ℕ₁)) ⊢t ⟩⊢∎
    Empty                                                          ∎
    where
    open TyR

    ⊢Γ : ⊢ Γ
    ⊢Γ = wfTerm ⊢t

    ⊢ℕ₁ : Γ ⊢ ℕ
    ⊢ℕ₁ = ℕⱼ ⊢Γ

    ⊢ℕ₂ : Γ ∙ ℕ ⊢ ℕ
    ⊢ℕ₂ = ℕⱼ (⊢→⊢∙ ⊢ℕ₁)

------------------------------------------------------------------------
-- Typing rules for Bool, true and false

opaque
  unfolding Bool

  -- A typing rule for Bool.

  ⊢Bool∷U :
    ⊢ Γ →
    Γ ⊢ Bool ∷ U 0
  ⊢Bool∷U ⊢Γ = ΠΣⱼ (ℕⱼ ⊢Γ) (⊢OK∷U (var₀ (ℕⱼ ⊢Γ))) Σ-ok

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
    prodⱼ (ℕⱼ ⊢Γ) (⊢OK (var₀ (ℕⱼ ⊢Γ))) (sucⱼ (zeroⱼ ⊢Γ))
      (conv (starⱼ ⊢Γ Unit-ok)
         (Unit s 0                   ≡˘⟨ OK-1≡ ⊢Γ ⟩⊢∎≡
          OK (suc zero)              ≡˘⟨ OK-[] ⟩
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
    prodⱼ (ℕⱼ ⊢Γ) (⊢OK (var₀ (ℕⱼ ⊢Γ))) (zeroⱼ ⊢Γ)
      (conv (starⱼ ⊢Γ Unit-ok)
         (Unit s 0               ≡˘⟨ OK-0≡ ⊢Γ ⟩⊢∎≡
          OK zero                ≡˘⟨ OK-[] ⟩
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
    drop k Γ ∙ Bool ⊢ A₁ ≡ A₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ ℕ →
    Γ ⊢ u₁ ≡ u₂ ∷ OK t₁ →
    Γ ⊢ Target k A₁ t₁ u₁ ≡ Target k A₂ t₂ u₂
  Target-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ =
    [][]↑-cong A₁≡A₂ $
    PE.subst (_⊢_≡_∷_ _ _ _)
      (PE.cong (Σ⟨_⟩_,_▷_▹_ _ _ _ _) $ PE.sym OK-[]) $
    prod-cong′ (⊢OK (var₀ (ℕⱼ (wfEqTerm t₁≡t₂)))) t₁≡t₂
      (PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym OK-[]) u₁≡u₂)
      Σ-ok

private opaque

  -- A variant of Target-cong.

  Target-cong′ :
    drop k Γ ∙ Bool ⊢ A₁ ≡ A₂ →
    Γ ⊢ t ∷ ℕ →
    Γ ⊢ u ∷ OK t →
    Γ ⊢ Target k A₁ t u ≡ Target k A₂ t u
  Target-cong′ A₁≡A₂ ⊢t ⊢u =
    Target-cong A₁≡A₂ (refl ⊢t) (refl ⊢u)

opaque

  -- A typing rule for Target.

  ⊢Target :
    drop k Γ ∙ Bool ⊢ A →
    Γ ⊢ t ∷ ℕ →
    Γ ⊢ u ∷ OK t →
    Γ ⊢ Target k A t u
  ⊢Target ⊢A ⊢t ⊢u =
    syntacticEq (Target-cong′ (refl ⊢A) ⊢t ⊢u) .proj₁

------------------------------------------------------------------------
-- Typing rules for boolrec

-- Some lemmas used below.

private
  module Boolrec
    (Π-ok : Π-allowed boolrecᵍ₁ p)
    (A₁≡A₂ : Γ ∙ Bool ⊢ A₁ ≡ A₂)
    (t₁≡t₂ : Γ ⊢ t₁ ≡ t₂ ∷ A₁ [ true ]₀)
    (u₁≡u₂ : Γ ⊢ u₁ ≡ u₂ ∷ A₁ [ false ]₀)
    where

    open TyR

    opaque

      ⊢Γ : ⊢ Γ
      ⊢Γ = wfEqTerm t₁≡t₂

    opaque

      ⊢Unit : Γ ⊢ Unit s 0
      ⊢Unit = Unitⱼ ⊢Γ Unit-ok

    opaque

      Π-lemma :
        drop k Δ PE.≡ Γ →
        Δ ∙ ℕ ⊢ t ∷ ℕ →
        Δ ∙ ℕ ⊢
          Π boolrecᵍ₁ , p ▷ OK t ▹ Target (2+ k) A₁ (wk1 t) (var x0) ≡
          Π boolrecᵍ₁ , p ▷ OK t ▹ Target (2+ k) A₂ (wk1 t) (var x0)
      Π-lemma PE.refl ⊢t =
        let ⊢OK = ⊢OK ⊢t in
        ΠΣ-cong′ (refl ⊢OK)
          (Target-cong′ A₁≡A₂ (wkTerm₁ ⊢OK ⊢t) $
           (PE.subst (_⊢_∷_ _ _) wk-OK $
            var₀ ⊢OK))
          Π-ok

    opaque

      Π-[]₀-lemma :
        Γ ⊢ t [ u ]₀ ∷ ℕ →
        Γ ⊢ OK (t [ u ]₀) ≡ Unit s 0 →
        Γ ⊢
          (Π boolrecᵍ₁ , p ▷ OK t ▹ Target 2 A₁ (wk1 t) (var x0))
            [ u ]₀ ≡
          Π boolrecᵍ₁ , p ▷ Unit s 0 ▹
            Target 1 A₂ (wk1 (t [ u ]₀)) (var x0)
      Π-[]₀-lemma {t} ⊢t[u]₀ OK-t[u]₀≡Unit =
        let ⊢OK = ⊢OK ⊢t[u]₀ in
        PE.subst (flip (_⊢_≡_ _) _)
          (PE.sym $
           PE.cong₂ (Π_,_▷_▹_ _ _) OK-[]
             (PE.trans (Target-[₀⇑] 1) $
              PE.cong (flip (Target _ _) _) $
              wk1-liftSubst t)) $
        flip (ΠΣ-cong′ OK-t[u]₀≡Unit) Π-ok $
        Target-cong′ A₁≡A₂ (wkTerm₁ ⊢OK ⊢t[u]₀) $
        PE.subst (_⊢_∷_ _ _) wk-OK $
        var₀ ⊢OK

    opaque

      Target-lemma-0 :
        drop k Δ PE.≡ Γ →
        ⊢ Δ →
        Δ ∙ Unit s 0 ⊢
          Target (1+ k) A₁ zero (var x0) ≡
          Target (1+ k) A₂ zero (var x0)
      Target-lemma-0 PE.refl ⊢Δ =
        let ⊢Unit = Unitⱼ ⊢Δ Unit-ok in
        Target-cong′ A₁≡A₂ (zeroⱼ (⊢→⊢∙ ⊢Unit))
          (conv (var₀ ⊢Unit) (sym (OK-0≡ (⊢→⊢∙ ⊢Unit))))

    opaque

      Target-lemma-1 :
        drop k Δ PE.≡ Γ →
        ⊢ Δ →
        Δ ∙ Unit s 0 ⊢
          Target (1+ k) A₁ (suc zero) (var x0) ≡
          Target (1+ k) A₂ (suc zero) (var x0)
      Target-lemma-1 PE.refl ⊢Δ =
        let ⊢Unit = Unitⱼ ⊢Δ Unit-ok in
        Target-cong′ A₁≡A₂ (sucⱼ (zeroⱼ (⊢→⊢∙ ⊢Unit)))
          (conv (var₀ ⊢Unit) (sym (OK-1≡ (⊢→⊢∙ ⊢Unit))))

    opaque
      unfolding true

      wk-t₁≡wk-t₂ :
        drop k Δ PE.≡ Γ →
        ⊢ Δ →
        Δ ⊢ wk[ k ]′ t₁ ≡ wk[ k ]′ t₂ ∷
          Target (1+ k) A₁ (suc zero) (var x0) [ star s 0 ]₀
      wk-t₁≡wk-t₂ PE.refl ⊢Δ =
        PE.subst (_⊢_≡_∷_ _ _ _)
          (PE.sym $ PE.trans (Target-[₀⇑] 0) Target-wk[]′) $
        wkEqTerm ⊇-drop ⊢Δ t₁≡t₂

    opaque
      unfolding false

      wk-u₁≡wk-u₂ :
        drop k Δ PE.≡ Γ →
        ⊢ Δ →
        Δ ⊢ wk[ k ]′ u₁ ≡ wk[ k ]′ u₂ ∷
          Target (1+ k) A₁ zero (var x0) [ star s 0 ]₀
      wk-u₁≡wk-u₂ PE.refl ⊢Δ =
        PE.subst (_⊢_≡_∷_ _ _ _)
          (PE.sym $ PE.trans (Target-[₀⇑] 0) Target-wk[]′) $
        wkEqTerm ⊇-drop ⊢Δ u₁≡u₂

    opaque

      unitrec-lemma-0 :
        drop k Δ PE.≡ Γ →
        Δ ⊢ B ≡ Unit s 0 →
        Δ ∙ B ⊢
          unitrec⟨ s ⟩ 0 𝟙 p (Target (2+ k) A₁ zero (var x0)) (var x0)
            (wk[ 1+ k ]′ u₁) ≡
          unitrec⟨ s ⟩ 0 𝟙 p (Target (2+ k) A₂ zero (var x0)) (var x0)
            (wk[ 1+ k ]′ u₂) ∷
          Target (2+ k) A₁ zero (var x0) [ var x0 ]₀
      unitrec-lemma-0 ≡Γ B≡Unit =
        let ⊢B , _ = syntacticEq B≡Unit in
        unitrec⟨⟩-cong
          (Target-lemma-0 ≡Γ (⊢→⊢∙ ⊢B))
          (refl (conv (var₀ ⊢B) (wkEq₁ ⊢B B≡Unit)))
          (wk-u₁≡wk-u₂ ≡Γ (⊢→⊢∙ ⊢B))

    opaque

      unitrec-lemma-1 :
        drop k Δ PE.≡ Γ →
        Δ ⊢ B ≡ Unit s 0 →
        Δ ∙ B ⊢
          unitrec⟨ s ⟩ 0 𝟙 p (Target (2+ k) A₁ (suc zero) (var x0))
            (var x0) (wk[ 1+ k ]′ t₁) ≡
          unitrec⟨ s ⟩ 0 𝟙 p (Target (2+ k) A₂ (suc zero) (var x0))
            (var x0) (wk[ 1+ k ]′ t₂) ∷
          Target (2+ k) A₁ (suc zero) (var x0) [ var x0 ]₀
      unitrec-lemma-1 ≡Γ B≡Unit =
        let ⊢B , _ = syntacticEq B≡Unit in
        unitrec⟨⟩-cong
          (Target-lemma-1 ≡Γ (⊢→⊢∙ ⊢B))
          (refl (conv (var₀ ⊢B) (wkEq₁ ⊢B B≡Unit)))
          (wk-t₁≡wk-t₂ ≡Γ (⊢→⊢∙ ⊢B))

    opaque

      lam-lemma-0 :
        drop k Δ PE.≡ Γ →
        ⊢ Δ →
        Δ ⊢
          lam boolrecᵍ₁
            (unitrec⟨ s ⟩ 0 𝟙 p (Target (2+ k) A₁ zero (var x0))
               (var x0) (wk[ 1+ k ]′ u₁)) ≡
          lam boolrecᵍ₁
            (unitrec⟨ s ⟩ 0 𝟙 p (Target (2+ k) A₂ zero (var x0))
               (var x0) (wk[ 1+ k ]′ u₂)) ∷
          (Π boolrecᵍ₁ , p ▷ OK (var x0) ▹
           Target (2+ k) A₁ (var x1) (var x0))
            [ zero ]₀
      lam-lemma-0 ≡Γ ⊢Δ =
        let ⊢OK = ⊢OK (zeroⱼ ⊢Δ) in
        flip lam-cong Π-ok $
        PE.subst₄ _⊢_≡_∷_
          (PE.cong (_∙_ _) $ PE.sym OK-[]) PE.refl PE.refl
          (PE.trans (Target-[₀⇑] 0) $ PE.sym $ Target-[₀⇑] 1) $
        unitrec-lemma-0 ≡Γ (OK-0≡ ⊢Δ)

    opaque

      lam-lemma-1 :
        drop k Δ PE.≡ Γ →
        ⊢ Δ →
        Δ ⊢
          lam boolrecᵍ₁
            (unitrec⟨ s ⟩ 0 𝟙 p (Target (2+ k) A₁ (suc zero) (var x0))
               (var x0) (wk[ 1+ k ]′ t₁)) ≡
          lam boolrecᵍ₁
            (unitrec⟨ s ⟩ 0 𝟙 p (Target (2+ k) A₂ (suc zero) (var x0))
               (var x0) (wk[ 1+ k ]′ t₂)) ∷
          (Π boolrecᵍ₁ , p ▷ OK (suc (var x0)) ▹
           Target (2+ k) A₁ (suc (var x1)) (var x0))
            [ zero ]₀
      lam-lemma-1 ≡Γ ⊢Δ =
        flip lam-cong Π-ok $
        PE.subst₄ _⊢_≡_∷_
          (PE.cong (_∙_ _) (PE.sym OK-[])) PE.refl PE.refl
          (PE.trans (Target-[₀⇑] 0) $ PE.sym $ Target-[₀⇑] 1) $
        unitrec-lemma-1 ≡Γ (OK-1≡ ⊢Δ)

    opaque

      lam-lemma-2+ :
        drop k Δ PE.≡ Γ →
        ⊢ Δ →
        Δ ∙ ℕ ⊢
          lam boolrecᵍ₁
            (emptyrec boolrecᵍ₁
               (Target (2+ k) A₁ (suc (suc (var x1))) (var x0))
               (var x0)) ≡
          lam boolrecᵍ₁
            (emptyrec boolrecᵍ₁
               (Target (2+ k) A₂ (suc (suc (var x1))) (var x0))
               (var x0)) ∷
          (Π boolrecᵍ₁ , p ▷ OK (suc (var x0)) ▹
           Target (2+ k) A₁ (suc (var x1)) (var x0))
            [ suc (var x0) ]↑
      lam-lemma-2+ PE.refl ⊢Δ =
        let ⊢OK = ⊢OK (sucⱼ (sucⱼ (var₀ (ℕⱼ ⊢Δ)))) in
        flip lam-cong Π-ok $
        PE.subst₄ _⊢_≡_∷_
          (PE.cong (_∙_ _) $ PE.sym OK-[]) PE.refl PE.refl
          (PE.sym $ Target-[↑⇑] 1) $
        emptyrec-cong
          (Target-cong′ A₁≡A₂ (sucⱼ (sucⱼ (var₁ ⊢OK)))
             (PE.subst (_⊢_∷_ _ _) wk-OK $
              var₀ ⊢OK))
          (_⊢_≡_∷_.refl $
           _⊢_∷_.conv (var₀ ⊢OK) $
           PE.subst (flip (_⊢_≡_ _) _) (PE.sym wk-OK) $
           OK-2+≡ (var₁ ⊢OK))

    opaque

      natcase-lemma :
        drop k Δ PE.≡ Γ →
        ⊢ Δ →
        Δ ∙ ℕ ⊢
          natcase 𝟘 (boolrecᵍ₂ + p)
            (Π boolrecᵍ₁ , p ▷ OK (suc (var x0)) ▹
             Target (3+ k) A₁ (suc (var x1)) (var x0))
            (lam boolrecᵍ₁ $
             unitrec⟨ s ⟩ 0 𝟙 p
               (Target (3+ k) A₁ (suc zero) (var x0)) (var x0)
               (wk[ 2+ k ]′ t₁))
            (lam boolrecᵍ₁ $
             emptyrec boolrecᵍ₁
               (Target (3+ k) A₁ (suc (suc (var x1))) (var x0))
               (var x0))
            (var x0) ≡
          natcase 𝟘 (boolrecᵍ₂ + p)
            (Π boolrecᵍ₁ , p ▷ OK (suc (var x0)) ▹
             Target (3+ k) A₂ (suc (var x1)) (var x0))
            (lam boolrecᵍ₁ $
             unitrec⟨ s ⟩ 0 𝟙 p
               (Target (3+ k) A₂ (suc zero) (var x0)) (var x0)
               (wk[ 2+ k ]′ t₂))
            (lam boolrecᵍ₁ $
             emptyrec boolrecᵍ₁
               (Target (3+ k) A₂ (suc (suc (var x1))) (var x0))
               (var x0))
            (var x0) ∷
          (Π boolrecᵍ₁ , p ▷ OK (var x0) ▹
           Target (2+ k) A₁ (var x1) (var x0))
            [ suc (var x0) ]↑
      natcase-lemma ≡Γ ⊢Δ =
        let ⊢ℕ   = ℕⱼ ⊢Δ
            ⊢Δ∙ℕ = ⊢→⊢∙ ⊢ℕ
        in
        PE.subst (_⊢_≡_∷_ _ _ _)
          (PE.cong₂ (Π_,_▷_▹_ _ _)
             (PE.trans OK-[] $ PE.sym OK-[])
             (PE.trans (Target-[₀⇑] 1) $
              PE.sym $ Target-[↑⇑] 1)) $
        natcase-cong
          (Π-lemma ≡Γ (sucⱼ (var₀ (ℕⱼ ⊢Δ∙ℕ))))
          (lam-lemma-1 ≡Γ ⊢Δ∙ℕ)
          (lam-lemma-2+ ≡Γ ⊢Δ∙ℕ)
          (refl (var₀ ⊢ℕ))

    opaque
      unfolding boolrec

      natcase-natcase-lemma :
        Γ ∙ ℕ ∙ OK (var x0) ⊢
          natcase OKᵍ (boolrecᵍ₂ + p)
            (Π boolrecᵍ₁ , p ▷ OK (var x0) ▹
             Target 4 A₁ (var x1) (var x0))
            (lam boolrecᵍ₁ $
             unitrec⟨ s ⟩ 0 𝟙 p (Target 4 A₁ zero (var x0)) (var x0)
               (wk[ 3 ]′ u₁))
            (natcase 𝟘 (boolrecᵍ₂ + p)
               (Π boolrecᵍ₁ , p ▷ OK (suc (var x0)) ▹
                Target 5 A₁ (suc (var x1)) (var x0))
               (lam boolrecᵍ₁ $
                unitrec⟨ s ⟩ 0 𝟙 p
                  (Target 5 A₁ (suc zero) (var x0)) (var x0)
                  (wk[ 4 ]′ t₁))
               (lam boolrecᵍ₁ $
                emptyrec boolrecᵍ₁
                  (Target 5 A₁ (suc (suc (var x1))) (var x0))
                  (var x0))
               (var x0))
            (var x1) ∘⟨ boolrecᵍ₁ ⟩
          (var x0) ≡
          natcase OKᵍ (boolrecᵍ₂ + p)
            (Π boolrecᵍ₁ , p ▷ OK (var x0) ▹
             Target 4 A₂ (var x1) (var x0))
            (lam boolrecᵍ₁ $
             unitrec⟨ s ⟩ 0 𝟙 p (Target 4 A₂ zero (var x0)) (var x0)
               (wk[ 3 ]′ u₂))
            (natcase 𝟘 (boolrecᵍ₂ + p)
               (Π boolrecᵍ₁ , p ▷ OK (suc (var x0)) ▹
                Target 5 A₂ (suc (var x1)) (var x0))
               (lam boolrecᵍ₁ $
                unitrec⟨ s ⟩ 0 𝟙 p
                  (Target 5 A₂ (suc zero) (var x0)) (var x0)
                  (wk[ 4 ]′ t₂))
               (lam boolrecᵍ₁ $
                emptyrec boolrecᵍ₁
                  (Target 5 A₂ (suc (suc (var x1))) (var x0))
                  (var x0))
               (var x0))
            (var x1) ∘⟨ boolrecᵍ₁ ⟩
          (var x0) ∷
          A₁ [ prod s 𝟙 (var x1) (var x0) ]↑²
      natcase-natcase-lemma =
        let ⊢OK = ⊢OK (var₀ (ℕⱼ ⊢Γ)) in
        PE.subst (_⊢_≡_∷_ _ _ _)
          (PE.trans (PE.cong _[ _ ]₀ $ Target-[₀⇑] 1) $
           PE.trans (Target-[₀⇑] 0) Target≡) $
        app-cong
          (PE.subst (_⊢_≡_∷_ _ _ _)
             (PE.cong₂ (Π_,_▷_▹_ _ _)
                (PE.trans OK-[] $ PE.sym wk-OK) PE.refl) $
           natcase-cong
             (Π-lemma PE.refl (var₀ (ℕⱼ (⊢→⊢∙ ⊢OK))))
             (lam-lemma-0 PE.refl (⊢→⊢∙ ⊢OK))
             (natcase-lemma PE.refl (⊢→⊢∙ ⊢OK))
             (refl (var₁ ⊢OK)))
          (refl (var₀ ⊢OK))

private opaque

  -- A lemma used below.

  natcase-natcase-[,]₁₀ :
    (natcase OKᵍ (boolrecᵍ₂ + p)
       (Π boolrecᵍ₁ , p ▷ OK (var x0) ▹ Target 4 A (var x1) (var x0))
       (lam boolrecᵍ₁ $
        unitrec⟨ s ⟩ 0 𝟙 p (Target 4 A zero (var x0)) (var x0)
          (wk[ 3 ]′ u))
       (natcase 𝟘 (boolrecᵍ₂ + p)
          (Π boolrecᵍ₁ , p ▷ OK (suc (var x0)) ▹
           Target 5 A (suc (var x1)) (var x0))
          (lam boolrecᵍ₁ $
           unitrec⟨ s ⟩ 0 𝟙 p (Target 5 A (suc zero) (var x0))
             (var x0) (wk[ 4 ]′ t))
          (lam boolrecᵍ₁ $
           emptyrec boolrecᵍ₁ (Target 5 A (suc (suc (var x1))) (var x0))
             (var x0))
          (var x0))
       (var x1)
       [ v , star s 0 ]₁₀) ∘⟨ boolrecᵍ₁ ⟩
    star s 0 PE.≡
    natcase OKᵍ (boolrecᵍ₂ + p)
      (Π boolrecᵍ₁ , p ▷ OK (var x0) ▹ Target 2 A (var x1) (var x0))
      (lam boolrecᵍ₁ $
       unitrec⟨ s ⟩ 0 𝟙 p (Target 2 A zero (var x0)) (var x0)
         (wk[ 1 ]′ u))
      (natcase 𝟘 (boolrecᵍ₂ + p)
         (Π boolrecᵍ₁ , p ▷ OK (suc (var x0)) ▹
          Target 3 A (suc (var x1)) (var x0))
         (lam boolrecᵍ₁ $
          unitrec⟨ s ⟩ 0 𝟙 p (Target 3 A (suc zero) (var x0))
            (var x0) (wk[ 2 ]′ t))
         (lam boolrecᵍ₁ $
          emptyrec boolrecᵍ₁ (Target 3 A (suc (suc (var x1))) (var x0))
            (var x0))
         (var x0))
      v ∘⟨ boolrecᵍ₁ ⟩
    star s 0
  natcase-natcase-[,]₁₀ =
    PE.cong (flip _∘⟨ boolrecᵍ₁ ⟩_ _) $
    PE.trans natcase-[] $
    PE.cong₄ (natcase _ _)
      (PE.cong₂ (Π_,_▷_▹_ _ _) OK-[] (Target-[,⇑] 2))
      (PE.cong (lam _) $
       PE.trans unitrec⟨⟩-[] $
       PE.cong₃ (unitrec⟨ _ ⟩ _ _ _)
         (Target-[,⇑] 2) PE.refl wk[2+]′[,⇑]≡)
      (PE.trans natcase-[] $
       PE.cong₄ (natcase _ _)
         (PE.cong₂ (Π_,_▷_▹_ _ _) OK-[] (Target-[,⇑] 3))
         (PE.cong (lam _) $
          PE.trans unitrec⟨⟩-[] $
          PE.cong₃ (unitrec⟨ _ ⟩ _ _ _)
            (Target-[,⇑] 3) PE.refl wk[2+]′[,⇑]≡)
         (PE.cong (lam _) $
          PE.cong₂ (emptyrec _) (Target-[,⇑] 3) PE.refl)
         PE.refl)
      PE.refl

opaque
  unfolding Bool boolrec

  -- An equality rule for boolrec.

  boolrec-cong :
    Π-allowed boolrecᵍ₁ p →
    Γ ∙ Bool ⊢ A₁ ≡ A₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ A₁ [ true ]₀ →
    Γ ⊢ u₁ ≡ u₂ ∷ A₁ [ false ]₀ →
    Γ ⊢ v₁ ≡ v₂ ∷ Bool →
    Γ ⊢ boolrec p A₁ t₁ u₁ v₁ ≡ boolrec p A₂ t₂ u₂ v₂ ∷ A₁ [ v₁ ]₀
  boolrec-cong Π-ok A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ =
    prodrec⟨⟩-cong A₁≡A₂ v₁≡v₂ $
    Boolrec.natcase-natcase-lemma Π-ok A₁≡A₂ t₁≡t₂ u₁≡u₂

opaque

  -- A typing rule for boolrec.

  ⊢boolrec :
    Π-allowed boolrecᵍ₁ p →
    Γ ∙ Bool ⊢ A →
    Γ ⊢ t ∷ A [ true ]₀ →
    Γ ⊢ u ∷ A [ false ]₀ →
    Γ ⊢ v ∷ Bool →
    Γ ⊢ boolrec p A t u v ∷ A [ v ]₀
  ⊢boolrec Π-ok ⊢A ⊢t ⊢u ⊢v =
    syntacticEqTerm
      (boolrec-cong Π-ok (refl ⊢A) (refl ⊢t) (refl ⊢u) (refl ⊢v))
      .proj₂ .proj₁

opaque
  unfolding Bool true boolrec

  -- An equality rule for boolrec.

  boolrec-true :
    Π-allowed boolrecᵍ₁ p →
    Γ ∙ Bool ⊢ A →
    Γ ⊢ t ∷ A [ true ]₀ →
    Γ ⊢ u ∷ A [ false ]₀ →
    Γ ⊢ boolrec p A t u true ≡ t ∷ A [ true ]₀
  boolrec-true {p} {Γ} {A} {t} {u} Π-ok ⊢A ⊢t ⊢u =
    prodrec⟨ s ⟩ (Boolᵍ ∧ boolrecᵍ₁) 𝟙 p A
      (prod s 𝟙 (suc zero) (star s 0))
      (natcase OKᵍ (boolrecᵍ₂ + p)
         (Π boolrecᵍ₁ , p ▷ OK (var x0) ▹ Target 4 A (var x1) (var x0))
         (lam boolrecᵍ₁ $
          unitrec⟨ s ⟩ 0 𝟙 p (Target 4 A zero (var x0)) (var x0)
            (wk[ 3 ]′ u))
         (natcase 𝟘 (boolrecᵍ₂ + p)
            (Π boolrecᵍ₁ , p ▷ OK (suc (var x0)) ▹
             Target 5 A (suc (var x1)) (var x0))
            (lam boolrecᵍ₁ $
             unitrec⟨ s ⟩ 0 𝟙 p (Target 5 A (suc zero) (var x0))
               (var x0) (wk[ 4 ]′ t))
            (lam boolrecᵍ₁ $
             emptyrec boolrecᵍ₁
               (Target 5 A (suc (suc (var x1))) (var x0)) (var x0))
            (var x0))
         (var x1) ∘⟨ boolrecᵍ₁ ⟩
       var x0)                                                            ≡⟨ prodrec⟨⟩-β (λ _ → ⊢A) (sucⱼ (zeroⱼ ⊢Γ))
                                                                               (_⊢_∷_.conv (starⱼ ⊢Γ Unit-ok) $
                                                                                PE.subst (_⊢_≡_ _ _) (PE.sym OK-[]) $
                                                                                sym $ OK-1≡ ⊢Γ)
                                                                               (syntacticEqTerm natcase-natcase-lemma .proj₂ .proj₁)
                                                                               Σ-ok ⟩⊢
    (natcase OKᵍ (boolrecᵍ₂ + p)
       (Π boolrecᵍ₁ , p ▷ OK (var x0) ▹ Target 4 A (var x1) (var x0))
       (lam boolrecᵍ₁ $
        unitrec⟨ s ⟩ 0 𝟙 p (Target 4 A zero (var x0)) (var x0)
          (wk[ 3 ]′ u))
       (natcase 𝟘 (boolrecᵍ₂ + p)
          (Π boolrecᵍ₁ , p ▷ OK (suc (var x0)) ▹
           Target 5 A (suc (var x1)) (var x0))
          (lam boolrecᵍ₁ $
           unitrec⟨ s ⟩ 0 𝟙 p (Target 5 A (suc zero) (var x0))
             (var x0) (wk[ 4 ]′ t))
          (lam boolrecᵍ₁ $
           emptyrec boolrecᵍ₁ (Target 5 A (suc (suc (var x1))) (var x0))
             (var x0))
          (var x0))
       (var x1)
       [ suc zero , star s 0 ]₁₀) ∘⟨ boolrecᵍ₁ ⟩
    star s 0                                                              ≡⟨ natcase-natcase-[,]₁₀ ⟩⊢≡

    natcase OKᵍ (boolrecᵍ₂ + p)
      (Π boolrecᵍ₁ , p ▷ OK (var x0) ▹ Target 2 A (var x1) (var x0))
      (lam boolrecᵍ₁ $
       unitrec⟨ s ⟩ 0 𝟙 p (Target 2 A zero (var x0)) (var x0)
         (wk[ 1 ]′ u))
      (natcase 𝟘 (boolrecᵍ₂ + p)
         (Π boolrecᵍ₁ , p ▷ OK (suc (var x0)) ▹
          Target 3 A (suc (var x1)) (var x0))
         (lam boolrecᵍ₁ $
          unitrec⟨ s ⟩ 0 𝟙 p (Target 3 A (suc zero) (var x0))
            (var x0) (wk[ 2 ]′ t))
         (lam boolrecᵍ₁ $
          emptyrec boolrecᵍ₁ (Target 3 A (suc (suc (var x1))) (var x0))
            (var x0))
         (var x0))
      (suc zero) ∘⟨ boolrecᵍ₁ ⟩
    star s 0                                                              ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _) (PE.trans (Target-[₀⇑] 0) Target≡) $
                                                                             app-subst
                                                                               (conv
                                                                                  (natcase-suc-⇒
                                                                                     (syntacticEq (Π-lemma PE.refl (var₀ (ℕⱼ ⊢Γ))) .proj₁)
                                                                                     (syntacticEqTerm (lam-lemma-0 PE.refl ⊢Γ) .proj₂ .proj₁)
                                                                                     (syntacticEqTerm (natcase-lemma PE.refl ⊢Γ) .proj₂ .proj₁)
                                                                                     (zeroⱼ ⊢Γ))
                                                                                  (Π-[]₀-lemma (sucⱼ (zeroⱼ ⊢Γ)) (OK-1≡ ⊢Γ)))
                                                                               (starⱼ ⊢Γ Unit-ok) ⟩⊢
    (natcase 𝟘 (boolrecᵍ₂ + p)
       (Π boolrecᵍ₁ , p ▷ OK (suc (var x0)) ▹
        Target 3 A (suc (var x1)) (var x0))
       (lam boolrecᵍ₁ $
        unitrec⟨ s ⟩ 0 𝟙 p (Target 3 A (suc zero) (var x0))
          (var x0) (wk[ 2 ]′ t))
       (lam boolrecᵍ₁ $
        emptyrec boolrecᵍ₁ (Target 3 A (suc (suc (var x1))) (var x0))
          (var x0))
       (var x0)
       [ zero ]₀) ∘⟨ boolrecᵍ₁ ⟩
    star s 0                                                              ≡⟨ PE.cong (_∘⟨ boolrecᵍ₁ ⟩ _) $
                                                                             PE.trans natcase-[] $
                                                                             PE.cong₄ (natcase _ _)
                                                                               (PE.cong₂ (Π_,_▷_▹_ _ _) OK-[] (Target-[₀⇑] 2))
                                                                               (PE.cong (lam boolrecᵍ₁) $
                                                                                PE.trans unitrec⟨⟩-[] $
                                                                                PE.cong₃ (unitrec⟨ _ ⟩ _ _ _) (Target-[₀⇑] 2) PE.refl
                                                                                  (PE.trans (PE.cong _[ _ ] $ PE.sym $ wk[]≡wk[]′ {t = t}) $
                                                                                   PE.trans (wk1-liftSubst (wk1 t)) $
                                                                                   PE.cong wk1 $ wk1-sgSubst _ _))
                                                                               (PE.cong (lam boolrecᵍ₁) $
                                                                                PE.cong₂ (emptyrec boolrecᵍ₁) (Target-[₀⇑] 2) PE.refl)
                                                                               PE.refl ⟩⊢≡
    natcase 𝟘 (boolrecᵍ₂ + p)
      (Π boolrecᵍ₁ , p ▷ OK (suc (var x0)) ▹
       Target 2 A (suc (var x1)) (var x0))
      (lam boolrecᵍ₁ $
       unitrec⟨ s ⟩ 0 𝟙 p (Target 2 A (suc zero) (var x0)) (var x0)
         (wk1 t))
      (lam boolrecᵍ₁ $
       emptyrec boolrecᵍ₁ (Target 2 A (suc (suc (var x1))) (var x0))
         (var x0))
      zero ∘⟨ boolrecᵍ₁ ⟩
    star s 0                                                              ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _) (PE.trans (Target-[₀⇑] 0) Target≡) $
                                                                             app-subst
                                                                               (conv
                                                                                  (natcase-zero-⇒
                                                                                     (syntacticEq (Π-lemma PE.refl (sucⱼ (var₀ (ℕⱼ ⊢Γ)))) .proj₁)
                                                                                     (syntacticEqTerm (lam-lemma-1 PE.refl ⊢Γ) .proj₂ .proj₁)
                                                                                     (syntacticEqTerm (lam-lemma-2+ PE.refl ⊢Γ) .proj₂ .proj₁))
                                                                                  (Π-[]₀-lemma (sucⱼ (zeroⱼ ⊢Γ)) (OK-1≡ ⊢Γ)))
                                                                               (starⱼ ⊢Γ Unit-ok) ⟩⊢
    lam boolrecᵍ₁
      (unitrec⟨ s ⟩ 0 𝟙 p (Target 2 A (suc zero) (var x0)) (var x0)
         (wk1 t)) ∘⟨ boolrecᵍ₁ ⟩
    star s 0                                                              ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _)
                                                                               (PE.trans (PE.cong _[ _ ]₀ $ Target-[₀⇑] 0) $
                                                                                PE.trans (Target-[₀⇑] 0) Target≡) $
                                                                             β-red-⇒
                                                                               (syntacticEqTerm (unitrec-lemma-1 PE.refl (refl ⊢Unit))
                                                                                  .proj₂ .proj₁)
                                                                               (starⱼ ⊢Γ Unit-ok) Π-ok ⟩⊢
    unitrec⟨ s ⟩ 0 𝟙 p (Target 2 A (suc zero) (var x0)) (var x0) (wk1 t)
      [ star s 0 ]₀                                                       ≡⟨ PE.trans unitrec⟨⟩-[] $
                                                                             PE.cong₃ (unitrec⟨ _ ⟩ _ _ _)
                                                                               (Target-[₀⇑] 1) PE.refl (wk1-sgSubst _ _) ⟩⊢≡

    unitrec⟨ s ⟩ 0 𝟙 p (Target 1 A (suc zero) (var x0)) (star s 0) t      ⇒*⟨ PE.subst (_⊢_⇒*_∷_ _ _ _) (PE.trans (Target-[₀⇑] 0) Target≡) $
                                                                              unitrec⟨⟩-β-⇒*
                                                                                (λ _ → syntacticEq (Target-lemma-1 PE.refl ⊢Γ) .proj₁)
                                                                                (PE.subst (flip (_⊢_∷_ _) _) (wk-id _) $
                                                                                 syntacticEqTerm (wk-t₁≡wk-t₂ PE.refl ⊢Γ) .proj₂ .proj₁) ⟩⊢∎
    t                                                                     ∎
    where
    open Boolrec Π-ok (refl ⊢A) (refl ⊢t) (refl ⊢u)
    open TmR

opaque
  unfolding Bool false boolrec

  -- An equality rule for boolrec.

  boolrec-false :
    Π-allowed boolrecᵍ₁ p →
    Γ ∙ Bool ⊢ A →
    Γ ⊢ t ∷ A [ true ]₀ →
    Γ ⊢ u ∷ A [ false ]₀ →
    Γ ⊢ boolrec p A t u false ≡ u ∷ A [ false ]₀
  boolrec-false {p} {Γ} {A} {t} {u} Π-ok ⊢A ⊢t ⊢u =
    prodrec⟨ s ⟩ (Boolᵍ ∧ boolrecᵍ₁) 𝟙 p A (prod s 𝟙 zero (star s 0))
      (natcase OKᵍ (boolrecᵍ₂ + p)
         (Π boolrecᵍ₁ , p ▷ OK (var x0) ▹ Target 4 A (var x1) (var x0))
         (lam boolrecᵍ₁ $
          unitrec⟨ s ⟩ 0 𝟙 p (Target 4 A zero (var x0)) (var x0)
            (wk[ 3 ]′ u))
         (natcase 𝟘 (boolrecᵍ₂ + p)
            (Π boolrecᵍ₁ , p ▷ OK (suc (var x0)) ▹
             Target 5 A (suc (var x1)) (var x0))
            (lam boolrecᵍ₁ $
             unitrec⟨ s ⟩ 0 𝟙 p (Target 5 A (suc zero) (var x0))
               (var x0) (wk[ 4 ]′ t))
            (lam boolrecᵍ₁ $
             emptyrec boolrecᵍ₁
               (Target 5 A (suc (suc (var x1))) (var x0)) (var x0))
            (var x0))
         (var x1) ∘⟨ boolrecᵍ₁ ⟩
       var x0)                                                            ≡⟨ prodrec⟨⟩-β (λ _ → ⊢A) (zeroⱼ ⊢Γ)
                                                                               (_⊢_∷_.conv (starⱼ ⊢Γ Unit-ok) $
                                                                                PE.subst (_⊢_≡_ _ _) (PE.sym OK-[]) $
                                                                                sym $ OK-0≡ ⊢Γ)
                                                                               (syntacticEqTerm natcase-natcase-lemma .proj₂ .proj₁)
                                                                               Σ-ok ⟩⊢
    (natcase OKᵍ (boolrecᵍ₂ + p)
       (Π boolrecᵍ₁ , p ▷ OK (var x0) ▹ Target 4 A (var x1) (var x0))
       (lam boolrecᵍ₁ $
        unitrec⟨ s ⟩ 0 𝟙 p (Target 4 A zero (var x0)) (var x0)
          (wk[ 3 ]′ u))
       (natcase 𝟘 (boolrecᵍ₂ + p)
          (Π boolrecᵍ₁ , p ▷ OK (suc (var x0)) ▹
           Target 5 A (suc (var x1)) (var x0))
          (lam boolrecᵍ₁ $
           unitrec⟨ s ⟩ 0 𝟙 p (Target 5 A (suc zero) (var x0))
             (var x0) (wk[ 4 ]′ t))
          (lam boolrecᵍ₁ $
           emptyrec boolrecᵍ₁ (Target 5 A (suc (suc (var x1))) (var x0))
             (var x0))
          (var x0))
       (var x1)
       [ zero , star s 0 ]₁₀) ∘⟨ boolrecᵍ₁ ⟩
    star s 0                                                              ≡⟨ natcase-natcase-[,]₁₀ ⟩⊢≡

    natcase OKᵍ (boolrecᵍ₂ + p)
      (Π boolrecᵍ₁ , p ▷ OK (var x0) ▹ Target 2 A (var x1) (var x0))
      (lam boolrecᵍ₁ $
       unitrec⟨ s ⟩ 0 𝟙 p (Target 2 A zero (var x0)) (var x0)
         (wk[ 1 ]′ u))
      (natcase 𝟘 (boolrecᵍ₂ + p)
         (Π boolrecᵍ₁ , p ▷ OK (suc (var x0)) ▹
          Target 3 A (suc (var x1)) (var x0))
         (lam boolrecᵍ₁ $
          unitrec⟨ s ⟩ 0 𝟙 p (Target 3 A (suc zero) (var x0))
            (var x0) (wk[ 2 ]′ t))
         (lam boolrecᵍ₁ $
          emptyrec boolrecᵍ₁ (Target 3 A (suc (suc (var x1))) (var x0))
            (var x0))
         (var x0))
      zero ∘⟨ boolrecᵍ₁ ⟩
    star s 0                                                              ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _) (PE.trans (Target-[₀⇑] 0) Target≡) $
                                                                             app-subst
                                                                               (conv
                                                                                  (natcase-zero-⇒
                                                                                     (syntacticEq (Π-lemma PE.refl (var₀ (ℕⱼ ⊢Γ))) .proj₁)
                                                                                     (syntacticEqTerm (lam-lemma-0 PE.refl ⊢Γ) .proj₂ .proj₁)
                                                                                     (syntacticEqTerm (natcase-lemma PE.refl ⊢Γ) .proj₂ .proj₁))
                                                                                  (Π-[]₀-lemma (zeroⱼ ⊢Γ) (OK-0≡ ⊢Γ)))
                                                                               (starⱼ ⊢Γ Unit-ok) ⟩⊢
    lam boolrecᵍ₁
      (unitrec⟨ s ⟩ 0 𝟙 p (Target 2 A zero (var x0)) (var x0) (wk1 u))
      ∘⟨ boolrecᵍ₁ ⟩
    star s 0                                                              ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _)
                                                                               (PE.trans (PE.cong _[ _ ]₀ $ Target-[₀⇑] 0) $
                                                                                PE.trans (Target-[₀⇑] 0) Target≡) $
                                                                             β-red-⇒
                                                                               (syntacticEqTerm (unitrec-lemma-0 PE.refl (refl ⊢Unit)) .proj₂ .proj₁)
                                                                               (starⱼ ⊢Γ Unit-ok) Π-ok ⟩⊢
    unitrec⟨ s ⟩ 0 𝟙 p (Target 2 A zero (var x0)) (var x0) (wk1 u)
      [ star s 0 ]₀                                                       ≡⟨ PE.trans unitrec⟨⟩-[] $
                                                                             PE.cong₃ (unitrec⟨ _ ⟩ _ _ _)
                                                                               (Target-[₀⇑] 1) PE.refl (wk1-sgSubst _ _) ⟩⊢≡

    unitrec⟨ s ⟩ 0 𝟙 p (Target 1 A zero (var x0)) (star s 0) u            ⇒*⟨ PE.subst (_⊢_⇒*_∷_ _ _ _) (PE.trans (Target-[₀⇑] 0) Target≡) $
                                                                              unitrec⟨⟩-β-⇒*
                                                                                (λ _ → syntacticEq (Target-lemma-0 PE.refl ⊢Γ) .proj₁)
                                                                                (PE.subst (flip (_⊢_∷_ _) _) (wk-id _) $
                                                                                 syntacticEqTerm (wk-u₁≡wk-u₂ PE.refl ⊢Γ) .proj₂ .proj₁) ⟩⊢∎
    u                                                                     ∎
    where
    open Boolrec Π-ok (refl ⊢A) (refl ⊢t) (refl ⊢u)
    open TmR
