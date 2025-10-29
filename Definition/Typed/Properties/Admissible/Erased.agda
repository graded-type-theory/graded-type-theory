------------------------------------------------------------------------
-- Some properties related to typing and Erased
------------------------------------------------------------------------

import Graded.Modality
open import Definition.Typed.Restrictions
import Definition.Untyped hiding (_[_])

module Definition.Typed.Properties.Admissible.Erased
  {a} {M : Set a}
  (open Definition.Untyped M)
  (open Graded.Modality M)
  {𝕄 : Modality}
  (R : Type-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties.Admissible.Equality R
import Definition.Typed.Properties.Admissible.Erased.Eta R as Eta
import Definition.Typed.Properties.Admissible.Erased.No-eta R as NoEta
import Definition.Typed.Properties.Admissible.Erased.Primitive R as P
open import Definition.Typed.Properties.Admissible.Identity R
open import Definition.Typed.Properties.Admissible.Lift R
open import Definition.Typed.Properties.Admissible.Nat R
open import Definition.Typed.Properties.Admissible.Pi-Sigma R
open import Definition.Typed.Properties.Admissible.Sigma R
open import Definition.Typed.Properties.Admissible.Unit R
open import Definition.Typed.Properties.Admissible.Var R
open import Definition.Typed.Properties.Reduction R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Reasoning.Reduction R
import Definition.Typed.Reasoning.Term R as TermR
import Definition.Typed.Reasoning.Type R as TypeR
open import Definition.Typed.Substitution.Primitive R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Weakening R as W
open import Definition.Typed.Well-formed R

import Definition.Untyped M as U
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Identity 𝕄
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sigma 𝕄
open import Definition.Untyped.Unit 𝕄

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation

private variable
  k n                                          : Nat
  Γ                                            : Con Term _
  A A₁ A₂ B B₁ B₂ C
    l l₁ l₂ t t′ t₁ t₂ u u₁ u₂ v v₁ v₂ w w₁ w₂ : Term _
  σ                                            : Subst _ _
  s                                            : Strength
  p                                            : M

------------------------------------------------------------------------
-- Lemmas about Erased, [_] and erased

-- Some lemmas that are proved under the assumption that Erased is
-- allowed.

module _ (Erased-ok : Erased-allowed s) where

  open Erased s

  private module P′ = P Erased-ok

  opaque

    -- An introduction rule for U for Erased.

    Erasedⱼ-U : Γ ⊢ A ∷ U l → Γ ⊢ Erased l A ∷ U l
    Erasedⱼ-U ⊢A = P′.Erasedⱼ-U (inversion-U-Level (wf-⊢∷ ⊢A)) ⊢A

  opaque

    -- An equality rule for U for Erased.

    Erased-cong-U :
      Γ ⊢ l₁ ≡ l₂ ∷ Level →
      Γ ⊢ A₁ ≡ A₂ ∷ U l₁ →
      Γ ⊢ Erased l₁ A₁ ≡ Erased l₂ A₂ ∷ U l₁
    Erased-cong-U l₁≡l₂ A₁≡A₂ =
      let _ , ⊢l₁ , _ = wf-⊢≡∷ l₁≡l₂
          _ , ⊢A₁ , _ = wf-⊢≡∷ A₁≡A₂
      in
      P′.Erased-cong-U ⊢l₁ l₁≡l₂ (univ ⊢A₁) A₁≡A₂

  opaque

    -- A formation rule for Erased.

    Erasedⱼ : Γ ⊢ A ∷ U l → Γ ⊢ Erased l A
    Erasedⱼ ⊢A = P′.Erasedⱼ (inversion-U-Level (wf-⊢∷ ⊢A)) ⊢A

  opaque

    -- An equality rule for Erased.

    Erased-cong :
      Γ ⊢ l₁ ≡ l₂ ∷ Level →
      Γ ⊢ A₁ ≡ A₂ ∷ U l₁ →
      Γ ⊢ Erased l₁ A₁ ≡ Erased l₂ A₂
    Erased-cong l₁≡l₂ A₁≡A₂ =
      let _ , ⊢l₁ , _ = wf-⊢≡∷ l₁≡l₂
          _ , ⊢A₁ , _ = wf-⊢≡∷ A₁≡A₂
      in
      P′.Erased-cong ⊢l₁ l₁≡l₂ (univ ⊢A₁) A₁≡A₂

  opaque

    -- An introduction rule for Erased.

    []ⱼ : Γ ⊢ A ∷ U l → Γ ⊢ t ∷ A → Γ ⊢ [ t ] ∷ Erased l A
    []ⱼ ⊢A = P′.[]ⱼ (inversion-U-Level (wf-⊢∷ ⊢A)) ⊢A

  opaque

    -- An equality rule for Erased.

    []-cong′ :
      Γ ⊢ A ∷ U l → Γ ⊢ t₁ ≡ t₂ ∷ A → Γ ⊢ [ t₁ ] ≡ [ t₂ ] ∷ Erased l A
    []-cong′ ⊢A t₁≡t₂ =
      let ⊢l            = inversion-U-Level (wf-⊢∷ ⊢A)
          _ , ⊢t₁ , ⊢t₂ = wf-⊢≡∷ t₁≡t₂
      in
      P′.[]-cong′ ⊢l ⊢A ⊢t₁ ⊢t₂ t₁≡t₂

  opaque
    unfolding erased

    -- A β-rule for Erased.

    Erased-β :
      Γ ⊢ t ∷ A →
      Γ ⊢ erased A [ t ] ≡ t ∷ A
    Erased-β = case PE.singleton s of λ where
      (𝕤 , PE.refl) → Eta.Erased-β Erased-ok
      (𝕨 , PE.refl) → NoEta.Erased-β Erased-ok

module _ where

  open Erased

  opaque
    unfolding erased

    -- An elimination rule for Erased.

    erasedⱼ : Γ ⊢ t ∷ Erased s l A → Γ ⊢ erased s A t ∷ A
    erasedⱼ {s} = case PE.singleton s of λ where
      (𝕤 , PE.refl) → Eta.erasedⱼ
      (𝕨 , PE.refl) → NoEta.erasedⱼ

  opaque
    unfolding erased

    -- A corresponding congruence rule.

    erased-cong :
      Γ ⊢ A₁ ≡ A₂ ∷ U l →
      Γ ⊢ t₁ ≡ t₂ ∷ Erased s l A₁ →
      Γ ⊢ erased s A₁ t₁ ≡ erased s A₂ t₂ ∷ A₁
    erased-cong {s} A₁≡A₂ = case PE.singleton s of λ where
      (𝕤 , PE.refl) → Eta.erased-cong
      (𝕨 , PE.refl) → NoEta.erased-cong A₁≡A₂

opaque
  unfolding Erased.Erased

  -- An inversion lemma for Erased.

  inversion-Erased-∷ :
    let open Erased s in
    Γ ⊢ Erased l A ∷ B →
    Erased-allowed s ×
    ∃ λ l₁ → Γ ⊢ A ∷ U l₁ × Γ ⊢ B ≡ U l₁ ×
    ∃ λ l₂ →
      Γ ∙ A ⊢ U (wk1 l₁) ≡ U (l₂ supᵘ wk1 l) × Γ ∙ A ⊢ U l₂ ≡ U zeroᵘ
  inversion-Erased-∷ ⊢Erased =
    let l₁ , _ , ⊢A , ⊢Lift-Unit , B≡U[l₁] , Σ-ok =
           inversion-ΠΣ-U ⊢Erased
        l₂ , _ , ⊢Unit , U[wk1-l₁]≡U[l₂⊔wk1-l] =
          inversion-Lift∷ ⊢Lift-Unit
        U[l₂]=U₀ , Unit-ok =
          inversion-Unit-U ⊢Unit
    in
    (Unit-ok , Σ-ok) ,
    l₁ , ⊢A , B≡U[l₁] ,
    l₂ , U[wk1-l₁]≡U[l₂⊔wk1-l] , U[l₂]=U₀

opaque
  unfolding Erased.Erased

  -- Another inversion lemma for Erased.

  inversion-Erased :
    let open Erased s in
    Γ ⊢ Erased l A →
    Erased-allowed s ×
    (Γ ⊢ A) ×
    Γ ∙ A ⊢ wk1 l ∷ Level
  inversion-Erased ⊢Erased =
    let ⊢A , ⊢Lift-Unit , Σ-ok = inversion-ΠΣ ⊢Erased
        ⊢wk1-l , ⊢Unit         = inversion-Lift ⊢Lift-Unit
        Unit-ok                = inversion-Unit ⊢Unit
    in
    (Unit-ok , Σ-ok) , ⊢A , ⊢wk1-l

opaque
  unfolding Erased.[_]

  -- An inversion lemma for [_].
  --
  -- TODO: Make it possible to replace the conclusion with
  --
  --   Erased-allowed × ∃ λ B → Γ ⊢ t ∷ B × ∃ λ l → Γ ⊢ A ≡ Erased l B?
  --
  -- See also inversion-[]′, ¬-inversion-[]′ and ¬-inversion-[] in
  -- Definition.Typed.Consequences.Inversion.Erased.

  inversion-[] :
    let open Erased s in
    Γ ⊢ [ t ] ∷ A →
    ∃₂ λ B q →
      Γ ⊢ t ∷ B ×
      (Unit-allowed s × Σ-allowed s 𝟘 q) ×
      ∃₂ λ C l →
      Γ ⊢ A ≡ Σ⟨ s ⟩ 𝟘 , q ▷ B ▹ C ×
      Γ ⊢ C [ t ]₀ ≡ Lift l (Unit s)
  inversion-[] ⊢[] =
    let B , C , q , _ , _ , ⊢t , ⊢lift-star , A≡ , Σˢ-ok =
          inversion-prod ⊢[]
        l , _ , ⊢star , C≡ =
          inversion-lift ⊢lift-star
        D≡ , Unit-ok =
          inversion-star ⊢star
        _ , ⊢Lift =
          wf-⊢≡ C≡
        ⊢l , _ =
          inversion-Lift ⊢Lift
    in
    B , q , ⊢t , (Unit-ok , Σˢ-ok) , C , l , A≡ ,
    trans C≡ (Lift-cong (refl ⊢l) D≡)

------------------------------------------------------------------------
-- Lemmas about erasedrec

private

  -- Some lemmas used below.

  opaque
    unfolding Erased.Erased

    erasedrec-lemma₁ :
      let open Erased s in
      Γ ∙ Erased l A₁ ⊢ B₁ ≡ B₂ →
      Γ ∙ A₁ ∙ Lift (wk1 l) (Unit s) ∙ Unit s ⊢
        B₁ [ 3 ][ prod s 𝟘 (var x2) (lift (var x0)) ]↑ ≡
        B₂ [ 3 ][ prod s 𝟘 (var x2) (lift (var x0)) ]↑
    erasedrec-lemma₁ B₁≡B₂ =
      let (Unit-ok , Σ-ok) , ⊢A₁ , ⊢wk1-l =
            inversion-Erased (⊢∙→⊢ (wfEq B₁≡B₂))
          ⊢Unit′        = ⊢Unit (∙ Liftⱼ ⊢wk1-l (⊢Unit (∙ ⊢A₁) Unit-ok))
                            Unit-ok
          ⊢wk3          = ⊢ˢʷ∷-wkSubst (∙ ⊢Unit′)
                            (⊢ˢʷ∷-idSubst (wf ⊢A₁))
          ⊢A[wk3]       = subst-⊢ ⊢A₁ ⊢wk3
          ⊢wk1-l-[wk3⇑] = subst-⊢∷ ⊢wk1-l (⊢ˢʷ∷-⇑ ⊢A[wk3] ⊢wk3)
      in
      [][]↑-cong B₁≡B₂ $ _⊢_≡_∷_.refl $
      prodⱼ
        (Liftⱼ ⊢wk1-l-[wk3⇑] (⊢Unit (∙ ⊢A[wk3]) Unit-ok))
        (PE.subst (_⊢_∷_ _ _) (wk[]≡[] 3) $ var₂ ⊢Unit′)
        (liftⱼ′
           (subst-⊢∷ ⊢wk1-l-[wk3⇑]
              (PE.subst (_⊢ˢʷ_∷_ _ _)
                 (PE.cong (_∙_ _) $
                  PE.trans (wk[]≡wk[]′ {k = 3}) $ wk≡subst _ _) $
               ⊢ˢʷ∷-sgSubst (var₂ ⊢Unit′)))
           (var₀ ⊢Unit′))
        Σ-ok

  opaque
    unfolding Erased.[_]

    erasedrec-lemma₂ :
      let open Erased s in
      ∀ B →
      Unit-allowed s →
      Γ ∙ A ⊢ wk1 l ∷ Level →
      Γ ∙ A ⊢ t₁ ≡ t₂ ∷ B [ [ var x0 ] ]↑ →
      Γ ∙ A ∙ Lift (wk1 l) (Unit s) ⊢ wk1 t₁ ≡ wk1 t₂ ∷
        B [ 3 ][ prod s 𝟘 (var x2) (lift (var x0)) ]↑ [ star s ]₀
    erasedrec-lemma₂ {s} B Unit-ok ⊢wk1-l t₁≡t₂ =
      flip (PE.subst (_⊢_≡_∷_ _ _ _))
        (wkEqTerm₁ (Liftⱼ ⊢wk1-l (⊢Unit (wfEqTerm t₁≡t₂) Unit-ok))
           t₁≡t₂) $
      wk1 (B [ [ var x0 ] ]↑)                                      ≡⟨ wk[]′[][]↑ 1 B ⟩
      B [ 2 ][ wk1 [ var x0 ] ]↑                                   ≡⟨⟩
      B [ 2 ][ prod s 𝟘 (var x1) (lift (star s)) ]↑                ≡˘⟨ [][]↑-[₀⇑] 0 B ⟩
      B [ 3 ][ prod s 𝟘 (var x2) (lift (var x0)) ]↑ [ star s ]₀    ∎
      where
      open Erased s

  opaque
    unfolding Erased.Erased

    erasedrec-lemma₃ :
      let open Erased s in
      drop k Γ ∙ Erased l A ⊢ B →
      Γ ⊢ t ∷ wk[ k ] A →
      Γ ⊢ u ∷ Lift (wk[ k ] l) (U.Unit s) →
      Γ ⊢
        B U.[ 1+ k ][ prod s 𝟘 (wk1 t) (lift (var x0)) ]↑
          U.[ lower u ]₀ ≡
        B U.[ k ][ prod s 𝟘 t u ]↑
    erasedrec-lemma₃ {s} {k} {l} {B} {t} {u} ⊢B ⊢t ⊢u =
      let (Unit-ok , Σ-ok) , ⊢A , ⊢wk1-l =
            inversion-Erased (⊢∙→⊢ (wf ⊢B))
          ⊢wk-A = W.wk (ʷ⊇-drop (wfTerm ⊢t)) ⊢A
      in
      B U.[ 1+ k ][ prod s 𝟘 (wk1 t) (lift (var x0)) ]↑ U.[ lower u ]₀  ≡⟨ [][]↑-[₀⇑] 0 B ⟩⊢≡

      B U.[ k ][ prod s 𝟘 (wk1 t U.[ lower u ]₀) (lift (lower u)) ]↑    ≡⟨ PE.cong (λ t → B U.[ _ ][ prod _ _ t _ ]↑) $ wk1-sgSubst _ _ ⟩⊢≡

      B U.[ k ][ prod s 𝟘 t (lift (lower u)) ]↑                         ≡⟨ subst-⊢≡ (refl ⊢B) $ ⊢ˢʷ≡∷-[][]↑ $
                                                                           PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym wk[]≡wk[]′) $
                                                                           prod-cong
                                                                             (Liftⱼ (W.wkTerm (liftʷ ⊇-drop ⊢wk-A) ⊢wk1-l)
                                                                                (⊢Unit (∙ ⊢wk-A) Unit-ok))
                                                                             (refl $
                                                                              PE.subst (_⊢_∷_ _ _) (wk[]≡wk[]′ {k = k})
                                                                                ⊢t)
                                                                             (⊢lift-lower≡∷ $
                                                                              PE.subst (_⊢_∷_ _ _)
                                                                                (PE.cong (flip Lift _) $ PE.sym $
                                                                                 PE.trans (PE.cong U._[ _ ]₀ $ lift-wk1 _ l) $
                                                                                 PE.trans (step-sgSubst _ _) $
                                                                                 PE.sym $ wk[]≡wk[]′ {k = k})
                                                                                ⊢u)
                                                                             Σ-ok ⟩⊢∎
      B U.[ k ][ prod s 𝟘 t u ]↑                                        ∎
      where
      open TypeR

  opaque

    erasedrec-lemma₃′ :
      let open Erased s in
      Γ ∙ Erased l A ⊢ B →
      Γ ∙ A ∙ Lift (wk1 l) (Unit s) ⊢
        B U.[ 3 ][ prod s 𝟘 (var x2) (lift (var x0)) ]↑
          U.[ lower (var x0) ]₀ ≡
        B U.[ 2 ][ prod s 𝟘 (var x1) (var x0) ]↑
    erasedrec-lemma₃′ ⊢B =
      let (Unit-ok , Σ-ok) , ⊢A , ⊢wk1-l =
            inversion-Erased (⊢∙→⊢ (wf ⊢B))
          ⊢Lift-Unit =
            Liftⱼ ⊢wk1-l (⊢Unit (∙ ⊢A) Unit-ok)
      in
      erasedrec-lemma₃ ⊢B (var₁ ⊢Lift-Unit) (var₀ ⊢Lift-Unit)

opaque
  unfolding Erased.Erased Erased.erasedrec

  -- An equality rule for erasedrec.

  erasedrec-cong :
    let open Erased s in
    Γ ∙ Erased l A ⊢ B₁ ≡ B₂ →
    Γ ∙ A ⊢ t₁ ≡ t₂ ∷ B₁ [ [ var x0 ] ]↑ →
    Γ ⊢ u₁ ≡ u₂ ∷ Erased l A →
    Γ ⊢ erasedrec p B₁ t₁ u₁ ≡ erasedrec p B₂ t₂ u₂ ∷ B₁ [ u₁ ]₀
  erasedrec-cong {s} {l} {B₁} B₁≡B₂ t₁≡t₂ u₁≡u₂ =
    let ⊢B₁ , _                     = wf-⊢≡ B₁≡B₂
        (Unit-ok , _) , ⊢A , ⊢wk1-l = inversion-Erased (⊢∙→⊢ (wf ⊢B₁))
    in
    prodrec⟨⟩-cong B₁≡B₂ u₁≡u₂ $
    conv
      (unitrec⟨⟩-cong (erasedrec-lemma₁ B₁≡B₂)
         (refl (lowerⱼ (var₀ (Liftⱼ ⊢wk1-l (⊢Unit (∙ ⊢A) Unit-ok)))))
         (erasedrec-lemma₂ B₁ Unit-ok ⊢wk1-l t₁≡t₂))
      (erasedrec-lemma₃′ ⊢B₁)

opaque

  -- A typing rule for erasedrec.

  ⊢erasedrec :
    let open Erased s in
    Γ ∙ Erased l A ⊢ B →
    Γ ∙ A ⊢ t ∷ B [ [ var x0 ] ]↑ →
    Γ ⊢ u ∷ Erased l A →
    Γ ⊢ erasedrec p B t u ∷ B [ u ]₀
  ⊢erasedrec ⊢B ⊢t ⊢u =
    syntacticEqTerm
      (erasedrec-cong (refl ⊢B) (refl ⊢t) (refl ⊢u))
      .proj₂ .proj₁

opaque
  unfolding Erased.Erased Erased.[_] Erased.erasedrec

  -- Another equality rule for erasedrec.

  erasedrec-β :
    let open Erased s in
    Γ ∙ Erased l A ⊢ B →
    Γ ∙ A ⊢ t ∷ B [ [ var x0 ] ]↑ →
    Γ ⊢ u ∷ A →
    Γ ⊢ erasedrec p B t [ u ] ≡ t [ u ]₀ ∷ B [ [ u ] ]₀
  erasedrec-β {s} {l} {B} {t} {u} {p} ⊢B ⊢t ⊢u =
    let (Unit-ok , Σ-ok) , ⊢A ,  ⊢wk1-l = inversion-Erased
                                            (⊢∙→⊢ (wf ⊢B))
        ⊢Γ                              = wf ⊢A
        ⊢Unit′                          = ⊢Unit ⊢Γ Unit-ok
        ⊢star                           = starⱼ ⊢Γ Unit-ok
        ⊢A′                             = wk₁ ⊢Unit′ ⊢A
        ⊢wk1-l[u]₀                      = substTerm ⊢wk1-l ⊢u
        ⊢l                              =
          PE.subst (flip (_⊢_∷_ _) _) (wk1-sgSubst _ _) ⊢wk1-l[u]₀
    in
    prodrec⟨ s ⟩ is-𝕨 𝟘 p B [ u ]
      (unitrec⟨ s ⟩ 𝟙 p (B [ 3 ][ prod s 𝟘 (var x2) (lift (var x0)) ]↑)
         (lower (var x0)) (wk1 t))                                       ≡⟨ prodrec⟨⟩-β (λ _ → ⊢B) ⊢u (liftⱼ′ ⊢wk1-l[u]₀ ⊢star)
                                                                              (conv
                                                                                 (⊢unitrec⟨⟩ (wf-⊢≡ (erasedrec-lemma₁ (refl ⊢B)) .proj₁)
                                                                                    (lowerⱼ (var₀ (Liftⱼ ⊢wk1-l (⊢Unit (wfTerm ⊢t) Unit-ok))))
                                                                                    (wf-⊢≡∷ (erasedrec-lemma₂ B Unit-ok ⊢wk1-l (refl ⊢t))
                                                                                       .proj₂ .proj₁))
                                                                                 (erasedrec-lemma₃′ ⊢B))
                                                                              (λ _ → Σ-ok) ⟩⊢
    unitrec⟨ s ⟩ 𝟙 p (B [ 3 ][ prod s 𝟘 (var x2) (lift (var x0)) ]↑)
      (lower (var x0)) (wk1 t)
      [ u , lift (star s) ]₁₀                                            ≡⟨ PE.trans unitrec⟨⟩-[] $
                                                                            PE.cong₃ (unitrec⟨_⟩ _ _ _)
                                                                              ([][]↑-[,⇑] 1 B) PE.refl (wk1-tail t) ⟩⊢≡
    unitrec⟨ s ⟩ 𝟙 p (B [ prod s 𝟘 (wk1 u) (lift (var x0)) ]↑)
      (lower (lift (star s))) (t [ u ]₀)                                 ≡⟨ conv
                                                                              (unitrec⟨⟩-cong
                                                                                 (refl $
                                                                                  wf-⊢≡
                                                                                    (erasedrec-lemma₃ ⊢B (wkTerm₁ ⊢Unit′ ⊢u) $
                                                                                     liftⱼ′
                                                                                       (PE.subst (flip (_⊢_∷_ _) _) (wk1-[][]↑ 1) $
                                                                                        subst-⊢∷ ⊢wk1-l (⊢ˢʷ∷-[][]↑ (wkTerm₁ ⊢Unit′ ⊢u)))
                                                                                       (var₀ ⊢Unit′))
                                                                                    .proj₂)
                                                                                 (Lift-β′ ⊢star)
                                                                                 (refl $
                                                                                  PE.subst (_⊢_∷_ _ _)
                                                                                    (PE.trans ([][]↑-[₀⇑] 0 B) $
                                                                                     PE.sym $
                                                                                     PE.trans ([][]↑-[₀⇑] 0 B) $
                                                                                     PE.cong (B U.[_]₀ ∘→ [_]) $ wk1-sgSubst _ _) $
                                                                                  substTerm ⊢t ⊢u))
                                                                              (erasedrec-lemma₃ ⊢B ⊢u (liftⱼ′ ⊢l ⊢star)) ⟩⊢
    unitrec⟨ s ⟩ 𝟙 p (B [ prod s 𝟘 (wk1 u) (lift (var x0)) ]↑) (star s)
      (t [ u ]₀)                                                         ≡⟨ (let lemma =
                                                                                   PE.trans ([][]↑-[₀⇑] 0 B) $
                                                                                   PE.cong (B U.[_]₀) $
                                                                                   PE.cong₂ (prod _ _) (wk1-sgSubst _ _) PE.refl
                                                                             in
                                                                             PE.subst (_⊢_≡_∷_ _ _ _) lemma $
                                                                             unitrec⟨⟩-β-≡
                                                                               (λ _ →
                                                                                  ⊢[][]↑ ⊢B $
                                                                                  PE.subst (_⊢_∷_ _ _) (wk[]≡[] 1) $
                                                                                  prodⱼ
                                                                                    (Liftⱼ
                                                                                       (wkTerm (liftʷ (step id) ⊢A′) $ wkTerm₁ ⊢A ⊢l)
                                                                                       (⊢Unit (∙ ⊢A′) Unit-ok))
                                                                                    (wkTerm₁ ⊢Unit′ ⊢u)
                                                                                    (liftⱼ′
                                                                                       (PE.subst (flip (_⊢_∷_ _) _)
                                                                                          (PE.trans (PE.sym $ PE.cong wk1 $ wk1-sgSubst _ _) $
                                                                                           wk-β (wk1 l)) $
                                                                                        wkTerm₁ ⊢Unit′ ⊢l) $
                                                                                     var₀ ⊢Unit′)
                                                                                    Σ-ok)
                                                                               (PE.subst (_⊢_∷_ _ _) (PE.trans ([]↑-[]₀ B) (PE.sym lemma)) $
                                                                                substTerm ⊢t ⊢u)) ⟩⊢∎
    t [ u ]₀                                                             ∎
    where
    open Erased s
    open TermR

------------------------------------------------------------------------
-- A lemma about Erased-η

opaque
  unfolding Erased.Erased-η

  -- A typing rule for Erased-η.

  ⊢Erased-η :
    let open Erased s in
    Γ ⊢ A ∷ U l →
    Γ ⊢ t ∷ Erased l A →
    Γ ⊢ Erased-η l A t ∷ Id (Erased l A) [ erased A t ] t
  ⊢Erased-η {s} {A} {l} ⊢A ⊢t =
    let ⊢Erased-A           = wf-⊢∷ ⊢t
        Erased-ok , ⊢A′ , _ = inversion-Erased ⊢Erased-A
        ⊢0                  = PE.subst (_⊢_∷_ _ _) wk-Erased $
                              var₀ ⊢Erased-A
    in
    PE.subst (_⊢_∷_ _ _)
      (PE.cong₃ Id
         (PE.trans Erased-[] $
          PE.cong₂ Erased (wk1-sgSubst _ _) (wk1-sgSubst _ _))
         (PE.trans []-[] $
          PE.cong [_] $
          PE.trans erased-[] $
          PE.cong₂ erased (wk1-sgSubst _ _) PE.refl)
         PE.refl) $
    ⊢erasedrec
      (Idⱼ′
         ([]ⱼ Erased-ok (wkTerm₁ (Erasedⱼ Erased-ok ⊢A) ⊢A)
            (erasedⱼ ⊢0))
         ⊢0)
      (PE.subst (_⊢_∷_ _ _)
         (PE.sym $
          PE.cong₃ Id
            (Erased (wk1 l) (wk1 A) [ [ var x0 ] ]↑                  ≡⟨ Erased-[] ⟩
             Erased (wk1 l [ [ var x0 ] ]↑) (wk1 A [ [ var x0 ] ]↑)  ≡⟨ PE.cong₂ Erased (wk1-[][]↑ 1) (wk1-[][]↑ 1) ⟩
             Erased (wk1 l) (wk1 A)                                  ∎)
            []-[] PE.refl) $
       rflⱼ′ $
       []-cong′ Erased-ok (wkTerm₁ ⊢A′ ⊢A)
         (erased (wk1 A) (var x0) [ [ var x0 ] ]↑    ≡⟨ erased-[] ⟩⊢≡
          erased (wk1 A [ [ var x0 ] ]↑) [ var x0 ]  ≡⟨ PE.cong (flip erased _) $ wk1-[][]↑ 1 ⟩⊢≡
          erased (wk1 A) [ var x0 ]                  ≡⟨ Erased-β Erased-ok (var₀ ⊢A′) ⟩⊢∎
          var x0                                     ∎))
      ⊢t
    where
    open Erased s
    open TermR

------------------------------------------------------------------------
-- Lemmas about mapᴱ

opaque
  unfolding Erased.mapᴱ

  -- An equality rule for mapᴱ.

  mapᴱ-cong :
    let open Erased s in
    Γ ⊢ A₁ ≡ A₂ ∷ U l₁ →
    Γ ⊢ B ∷ U l₂ →
    Γ ∙ A₁ ⊢ t₁ ≡ t₂ ∷ wk1 B →
    Γ ⊢ u₁ ≡ u₂ ∷ Erased l₁ A₁ →
    Γ ⊢ mapᴱ A₁ t₁ u₁ ≡ mapᴱ A₂ t₂ u₂ ∷ Erased l₂ B
  mapᴱ-cong A₁≡A₂ ⊢B t₁≡t₂ u₁≡u₂ =
    let ok , _ = inversion-Erased $ wf-⊢≡∷ u₁≡u₂ .proj₁ in
    []-cong′ ok ⊢B $
    PE.subst (_⊢_≡_∷_ _ _ _) (wk1-sgSubst _ _) $
    substTermEq t₁≡t₂ (erased-cong A₁≡A₂ u₁≡u₂)

opaque

  -- A typing rule for mapᴱ.

  ⊢mapᴱ :
    let open Erased s in
    Γ ⊢ A ∷ U l₁ →
    Γ ⊢ B ∷ U l₂ →
    Γ ∙ A ⊢ t ∷ wk1 B →
    Γ ⊢ u ∷ Erased l₁ A →
    Γ ⊢ mapᴱ A t u ∷ Erased l₂ B
  ⊢mapᴱ ⊢A ⊢B ⊢t ⊢u =
    wf-⊢≡∷ (mapᴱ-cong (refl ⊢A) ⊢B (refl ⊢t) (refl ⊢u)) .proj₂ .proj₁

opaque
  unfolding Erased.mapᴱ

  -- A β-rule for mapᴱ.

  mapᴱ-β :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ B ∷ U l →
    Γ ∙ A ⊢ t ∷ wk1 B →
    Γ ⊢ u ∷ A →
    Γ ⊢ mapᴱ A t [ u ] ≡ [ t [ u ]₀ ] ∷ Erased l B
  mapᴱ-β ok ⊢B ⊢t ⊢u =
    []-cong′ ok ⊢B $
    PE.subst (_⊢_≡_∷_ _ _ _) (wk1-sgSubst _ _) $
    substTermEq (refl ⊢t) (Erased-β ok ⊢u)

------------------------------------------------------------------------
-- Lemmas proved under the assumption that []-cong is allowed

module _ (ok : []-cong-allowed s) where

  open Erased s

  private opaque

    -- Some lemmas used below.

    Erased-ok : Erased-allowed s
    Erased-ok = []-cong→Erased ok

    Σ-ok : Σ-allowed s 𝟘 𝟘
    Σ-ok = Erased-ok .proj₂

    [erased-0]↑[[]]₀≡[]₀ :
      Γ ∙ A ⊢ B →
      Γ ⊢ t ∷ A →
      Γ ⊢ B [ erased (wk1 A) (var x0) ]↑ [ [ t ] ]₀ ≡ B [ t ]₀
    [erased-0]↑[[]]₀≡[]₀ {A} {B} {t} ⊢B ⊢t =
      B [ erased (wk1 A) (var x0) ]↑ [ [ t ] ]₀  ≡⟨ []↑-[]₀ B ⟩⊢≡
      B [ erased (wk1 A) (var x0) [ [ t ] ]₀ ]₀  ≡⟨ PE.cong (B [_]₀) erased-[] ⟩⊢≡
      B [ erased (wk1 A [ [ t ] ]₀) [ t ] ]₀     ≡⟨ PE.cong (λ A → B [ erased A _ ]₀) $ wk1-sgSubst _ _ ⟩⊢≡
      B [ erased A [ t ] ]₀                      ≡⟨ substTypeEq (refl ⊢B) $ Erased-β Erased-ok ⊢t ⟩⊢∎
      B [ t ]₀                                   ∎
      where
      open TypeR

    ⊢[erased-0]↑ :
      Γ ⊢ A ∷ U l →
      Γ ∙ A ⊢ B →
      Γ ∙ Erased l A ⊢ B [ erased (wk1 A) (var x0) ]↑
    ⊢[erased-0]↑ ⊢A ⊢B =
      subst-⊢ ⊢B $ ⊢ˢʷ∷-[][]↑ $ erasedⱼ $
      PE.subst (_⊢_∷_ _ _) wk-Erased $
      var₀ (Erasedⱼ Erased-ok ⊢A)

  ----------------------------------------------------------------------
  -- Lemmas related to substᵉ

  opaque
    unfolding substᵉ

    -- A typing rule for substᵉ.

    ⊢substᵉ :
      Γ ⊢ A ∷ U l →
      Γ ∙ A ⊢ B →
      Γ ⊢ v ∷ Id A t u →
      Γ ⊢ w ∷ B [ t ]₀ →
      Γ ⊢ substᵉ l A B t u v w ∷ B [ u ]₀
    ⊢substᵉ ⊢A ⊢B ⊢v ⊢w =
      let _ , ⊢t , ⊢u = inversion-Id (wf-⊢∷ ⊢v)
      in
      conv
        (⊢subst (⊢[erased-0]↑ ⊢A ⊢B) ([]-congⱼ′ ok ⊢A ⊢v)
           (conv ⊢w $ sym $ [erased-0]↑[[]]₀≡[]₀ ⊢B ⊢t))
        ([erased-0]↑[[]]₀≡[]₀ ⊢B ⊢u)

  opaque
    unfolding substᵉ

    -- A reduction rule for substᵉ.

    substᵉ-⇒*′ :
      Γ ⊢ A ∷ U l →
      Γ ∙ A ⊢ B →
      Γ ⊢ t ≡ t′ ∷ A →
      Γ ⊢ u ∷ B [ t ]₀ →
      Γ ⊢ substᵉ l A B t t′ rfl u ⇒* u ∷ B [ t ]₀
    substᵉ-⇒*′ {A} {l} {B} {t} {t′} {u} ⊢A ⊢B t≡t′ ⊢u =
      let _ , ⊢t , _ = wf-⊢≡∷ t≡t′
          ⊢B[]↑      = ⊢[erased-0]↑ ⊢A ⊢B
          [t]≡[t′]   = []-cong′ Erased-ok ⊢A t≡t′
          ≡B[t]₀     = [erased-0]↑[[]]₀≡[]₀ ⊢B ⊢t
          ⊢u         = conv ⊢u (sym ≡B[t]₀)
      in
      conv*
        (subst 𝟘 (Erased l A) (B [ erased (wk1 A) (var x0) ]↑)
           [ t ] [ t′ ] ([]-cong s l A t t′ rfl) u              ⇒⟨ conv (subst-subst ⊢B[]↑ ([]-cong-β-⇒ ⊢A t≡t′ ok) ⊢u) $
                                                                   substTypeEq (refl ⊢B[]↑) (sym′ [t]≡[t′]) ⟩
         subst 𝟘 (Erased l A) (B [ erased (wk1 A) (var x0) ]↑)
           [ t ] [ t′ ] rfl u                                   ⇒⟨ subst-⇒′ ⊢B[]↑ [t]≡[t′] ⊢u ⟩∎

         u                                                      ∎)
        ≡B[t]₀

  opaque

    -- Another reduction rule for substᵉ.

    substᵉ-⇒* :
      Γ ⊢ A ∷ U l →
      Γ ∙ A ⊢ B →
      Γ ⊢ t ∷ A →
      Γ ⊢ u ∷ B [ t ]₀ →
      Γ ⊢ substᵉ l A B t t rfl u ⇒* u ∷ B [ t ]₀
    substᵉ-⇒* ⊢A ⊢B ⊢t = substᵉ-⇒*′ ⊢A ⊢B (refl ⊢t)

  opaque

    -- An equality rule for substᵉ.

    substᵉ-≡ :
      Γ ⊢ A ∷ U l →
      Γ ∙ A ⊢ B →
      Γ ⊢ t ∷ A →
      Γ ⊢ u ∷ B [ t ]₀ →
      Γ ⊢ substᵉ l A B t t rfl u ≡ u ∷ B [ t ]₀
    substᵉ-≡ ⊢A ⊢B ⊢t ⊢u =
      subset*Term (substᵉ-⇒* ⊢A ⊢B ⊢t ⊢u)

  opaque
    unfolding substᵉ

    -- An equality rule for substᵉ.

    substᵉ-cong :
      Γ ⊢ l₁ ≡ l₂ ∷ Level →
      Γ ⊢ A₁ ≡ A₂ ∷ U l₁ →
      Γ ∙ A₁ ⊢ B₁ ≡ B₂ →
      Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
      Γ ⊢ u₁ ≡ u₂ ∷ A₁ →
      Γ ⊢ v₁ ≡ v₂ ∷ Id A₁ t₁ u₁ →
      Γ ⊢ w₁ ≡ w₂ ∷ B₁ [ t₁ ]₀ →
      Γ ⊢ substᵉ l₁ A₁ B₁ t₁ u₁ v₁ w₁ ≡ substᵉ l₂ A₂ B₂ t₂ u₂ v₂ w₂ ∷
        B₁ [ u₁ ]₀
    substᵉ-cong l₁≡l₂ A₁≡A₂ B₁≡B₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ w₁≡w₂ =
      let _ , ⊢A₁ , _ = wf-⊢≡∷ A₁≡A₂
          ⊢B₁ , _     = wf-⊢≡ B₁≡B₂
          _ , ⊢t₁ , _ = wf-⊢≡∷ t₁≡t₂
          _ , ⊢u₁ , _ = wf-⊢≡∷ u₁≡u₂
          ⊢Erased-A₁  = Erasedⱼ Erased-ok ⊢A₁
      in
      conv
        (subst-cong (Erased-cong Erased-ok l₁≡l₂ A₁≡A₂)
           (subst-⊢≡ B₁≡B₂ $ ⊢ˢʷ≡∷-[][]↑ $
            erased-cong (wkEqTerm₁ ⊢Erased-A₁ A₁≡A₂) $
            refl $ PE.subst (_⊢_∷_ _ _) wk-Erased $
            var₀ ⊢Erased-A₁)
           ([]-cong′ Erased-ok ⊢A₁ t₁≡t₂)
           ([]-cong′ Erased-ok ⊢A₁ u₁≡u₂)
           ([]-cong-cong l₁≡l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok)
           (conv w₁≡w₂ $ sym $ [erased-0]↑[[]]₀≡[]₀ ⊢B₁ ⊢t₁))
        ([erased-0]↑[[]]₀≡[]₀ ⊢B₁ ⊢u₁)

  opaque
    unfolding substᵉ

    -- A reduction rule for substᵉ.

    substᵉ-subst :
      Γ ⊢ A ∷ U l →
      Γ ∙ A ⊢ B →
      Γ ⊢ v₁ ⇒ v₂ ∷ Id A t u →
      Γ ⊢ w ∷ B [ t ]₀ →
      Γ ⊢ substᵉ l A B t u v₁ w ⇒ substᵉ l A B t u v₂ w ∷ B [ u ]₀
    substᵉ-subst ⊢A ⊢B v₁⇒v₂ ⊢w =
      let _ , ⊢t , ⊢u = inversion-Id (wf-⊢≡∷ (subsetTerm v₁⇒v₂) .proj₁)
      in
      conv
        (subst-subst (⊢[erased-0]↑ ⊢A ⊢B) ([]-cong-subst′ ⊢A v₁⇒v₂ ok)
           (conv ⊢w $ sym $ [erased-0]↑[[]]₀≡[]₀ ⊢B ⊢t))
        ([erased-0]↑[[]]₀≡[]₀ ⊢B ⊢u)

  ----------------------------------------------------------------------
  -- Lemmas related to Jᵉ

  private

    -- A definition used below.

    Singleton : Term n → Term n → Term n
    Singleton A t = Σ⟨ s ⟩ 𝟘 , 𝟘 ▷ A ▹ Id (wk1 A) (wk1 t) (var x0)

  private opaque

    -- Some lemmas used below.

    ⊢Singleton : Γ ⊢ A ∷ U l → Γ ⊢ t ∷ A → Γ ⊢ Singleton A t ∷ U l
    ⊢Singleton ⊢A ⊢t =
      let ⊢A′ = univ ⊢A in
      ΠΣⱼ′ ⊢A (Idⱼ (wkTerm₁ ⊢A′ ⊢A) (wkTerm₁ ⊢A′ ⊢t) (var₀ ⊢A′)) Σ-ok

    lemma₁ :
      wk₂ t PE.≡ U.wk (lift (step (step id))) (wk1 t) [ u ]₀
    lemma₁ {t} {u} =
      wk₂ t                                                  ≡⟨ wk≡subst _ _ ⟩
      t U.[ sgSubst u ₛ• lift (step (step id)) ₛ• step id ]  ≡˘⟨ subst-wk t ⟩
      wk1 t U.[ sgSubst u ₛ• lift (step (step id)) ]         ≡˘⟨ subst-wk (wk1 t) ⟩
      U.wk (lift (step (step id))) (wk1 t) [ u ]₀            ∎

    lemma₂ :
      wk2 t PE.≡ U.wk (lift (step (step id))) (wk1 t) [ u ]₀
    lemma₂ {t} {u} =
      wk2 t                                        ≡⟨ wk[]≡wk[]′ ⟩
      wk₂ t                                        ≡⟨ lemma₁ ⟩
      U.wk (lift (step (step id))) (wk1 t) [ u ]₀  ∎

    lemma₃ :
      U.wk (lift (step (step id))) t
        U.[ liftSubst (consSubst (sgSubst u) v) ] PE.≡
      t
    lemma₃ {t} {u} {v} =
      U.wk (lift (step (step id))) t
        U.[ liftSubst (consSubst (sgSubst u) v) ]                    ≡⟨ subst-wk t ⟩

      t U.[ liftSubst (consSubst (sgSubst u) v) ₛ•
            lift (step (step id)) ]                                  ≡⟨ subst-lift-ₛ• t ⟩

      t U.[ liftSubst (consSubst (sgSubst u) v ₛ• step (step id)) ]  ≡⟨⟩

      t U.[ liftSubst idSubst ]                                      ≡⟨ substVar-to-subst subst-lift-id t ⟩

      t U.[ idSubst ]                                                ≡⟨ subst-id _ ⟩

      t                                                              ∎

    lemma₄ :
      ∀ t → wk₂ t [ u ]₀ PE.≡ wk1 t U.[ consSubst (wk1Subst idSubst) v ]
    lemma₄ {u} {v} t =
      wk₂ t [ u ]₀                                ≡⟨ subst-wk t ⟩
      t U.[ wk1Subst idSubst ]                    ≡˘⟨ wk1-tail t ⟩
      wk1 t U.[ consSubst (wk1Subst idSubst) v ]  ∎

    lemma₅ :
      wk₂ t U.[ liftSubst (sgSubst u) ] PE.≡ wk1 t
    lemma₅ {t} {u} =
      wk₂ t U.[ liftSubst (sgSubst u) ]                ≡⟨ subst-wk t ⟩
      t U.[ liftSubst (sgSubst u) ₛ• step (step id) ]  ≡⟨⟩
      t U.[ tail idSubst ]                             ≡˘⟨ wk1-tailId _ ⟩
      wk1 t                                            ∎

    lemma₆ :
      Γ ⊢ A₁ ≡ A₂ →
      Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
      Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢
        Id (wk₂ (Singleton A₁ t₁)) (wk₂ (prod s 𝟘 t₁ rfl))
          (prod s 𝟘 (var x1) (var x0)) ≡
        Id (wk₂ (Singleton A₂ t₂)) (wk₂ (prod s 𝟘 t₂ rfl))
          (prod s 𝟘 (var x1) (var x0))
    lemma₆ A₁≡A₂ t₁≡t₂ =
      case syntacticEqTerm t₁≡t₂ of λ
        (⊢A₁ , ⊢t₁ , _) →
      case W.wk (stepʷ (step id) (J-motive-context-type ⊢t₁)) ⊢A₁ of λ
        ⊢A₁′ →
      Id-cong
        (ΠΣ-cong
           (wkEq (stepʷ (step id) (J-motive-context-type ⊢t₁)) A₁≡A₂)
           (Id-cong
              (wkEq (liftʷ (step (step id)) ⊢A₁′) (wkEq₁ ⊢A₁ A₁≡A₂))
              (wkEqTerm (liftʷ (step (step id)) ⊢A₁′)
                 (wkEqTerm₁ ⊢A₁ t₁≡t₂))
              (_⊢_≡_∷_.refl $
               PE.subst (_⊢_∷_ _ _) (wk1-wk≡lift-wk1 _ _) $
               var₀ ⊢A₁′))
           Σ-ok)
        (prod-cong
           (W.wk (liftʷ (step (step id)) ⊢A₁′)
              (J-motive-context-type ⊢t₁))
           (wkEqTerm (stepʷ (step id) (J-motive-context-type ⊢t₁))
              t₁≡t₂)
           (_⊢_≡_∷_.refl $
            PE.subst (_⊢_∷_ _ _)
              (PE.cong₃ Id lemma₁ lemma₁ PE.refl) $
            rflⱼ $
            wkTerm (stepʷ (step id) (J-motive-context-type ⊢t₁)) ⊢t₁)
           Σ-ok)
        (prod-cong
           (W.wk (liftʷ (step (step id)) ⊢A₁′)
              (J-motive-context-type ⊢t₁))
           (_⊢_≡_∷_.refl $
            PE.subst (_⊢_∷_ _ _) wk[]≡wk[]′ $
            var₁ (J-motive-context-type ⊢t₁))
           (_⊢_≡_∷_.refl $
            PE.subst (_⊢_∷_ _ _)
              (PE.cong₃ Id lemma₂ lemma₂ PE.refl) $
            var₀ (J-motive-context-type ⊢t₁))
           Σ-ok)

    lemma₆′ :
      Γ ⊢ t ∷ A →
      Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢
        Id (wk₂ (Singleton A t)) (wk₂ (prod s 𝟘 t rfl))
          (prod s 𝟘 (var x1) (var x0))
    lemma₆′ ⊢t =
      case syntacticTerm ⊢t of λ
        ⊢A →
      syntacticEq (lemma₆ (refl ⊢A) (refl ⊢t)) .proj₁

    lemma₇ :
      Γ ⊢ t ∷ A →
      Γ ⊢ rfl ∷
        Id (wk₂ (Singleton A t)) (wk₂ (prod s 𝟘 t rfl))
          (prod s 𝟘 (var x1) (var x0))
        [ t , rfl ]₁₀
    lemma₇ ⊢t =
      PE.subst (_⊢_∷_ _ _)
        (PE.sym $ PE.cong₃ Id
           (PE.cong₂ (Σ⟨_⟩_,_▷_▹_ s 𝟘 𝟘) wk₂-[,] $
            PE.cong₃ Id lemma₃ lemma₃ PE.refl)
           (PE.cong₂ (prod s 𝟘) wk₂-[,] PE.refl)
           PE.refl) $
      rflⱼ $
      prodⱼ (J-motive-context-type ⊢t) ⊢t
        (PE.subst (_⊢_∷_ _ _)
           (PE.sym $ PE.cong₃ Id
              (wk1-sgSubst _ _)
              (wk1-sgSubst _ _)
              PE.refl) $
         rflⱼ ⊢t)
        Σ-ok

    lemma₈ :
      Γ ⊢ A₁ ≡ A₂ →
      Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ ≡ B₂ →
      Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
      Γ ∙ Singleton A₁ t₁ ⊢
        B₁ U.[ consSubst
                 (consSubst (wk1Subst idSubst)
                    (fst⟨ s ⟩ 𝟘 (wk1 A₁) (var x0)))
                 (snd⟨ s ⟩ 𝟘 𝟘 (wk1 A₁) (Id (wk₂ A₁) (wk₂ t₁) (var x0))
                    (var x0))
             ] ≡
        B₂ U.[ consSubst
                 (consSubst (wk1Subst idSubst)
                    (fst⟨ s ⟩ 𝟘 (wk1 A₂) (var x0)))
                 (snd⟨ s ⟩ 𝟘 𝟘 (wk1 A₂) (Id (wk₂ A₂) (wk₂ t₂) (var x0))
                    (var x0))
             ]
    lemma₈ {A₁} {t₁} A₁≡A₂ B₁≡B₂ t₁≡t₂ =
      case syntacticEqTerm t₁≡t₂ of λ
        (⊢A₁ , ⊢t₁ , _) →
      case Idⱼ′ (wkTerm₁ ⊢A₁ ⊢t₁) (var₀ ⊢A₁) of λ
        ⊢Id →
      case ΠΣⱼ ⊢Id Σ-ok of λ
        ⊢Singleton₁ →
      case wkEq₁ ⊢Singleton₁ A₁≡A₂ of λ
        A₁≡A₂′ →
      case syntacticEq A₁≡A₂′ of λ
        (⊢A₁′ , _) →
      subst-⊢≡ B₁≡B₂ $
      →⊢ˢʷ≡∷∙ ⊢Id
        (⊢ˢʷ≡∷-[][]↑ (fst⟨⟩-cong A₁≡A₂′ $ refl (var₀ ⊢Singleton₁)))
        (PE.subst (_⊢_≡_∷_ _ _ _)
           (PE.cong₃ Id (lemma₄ A₁) (lemma₄ t₁) PE.refl)
           (snd⟨⟩-cong A₁≡A₂′
              (Id-cong (wkEq (stepʷ (step id) ⊢A₁′) A₁≡A₂)
                 (wkEqTerm (stepʷ (step id) ⊢A₁′) t₁≡t₂)
                 (refl (PE.subst (_⊢_∷_ _ _) wk[]≡wk[]′ $ var₀ ⊢A₁′))) $
            PE.subst (_⊢_≡_∷_ _ _ _)
              (PE.cong (Σ⟨_⟩_,_▷_▹_ s 𝟘 𝟘 (wk1 A₁)) $
               PE.cong₃ Id (lift-wk1 _ _) (lift-wk1 _ _) PE.refl) $
            refl (var₀ ⊢Singleton₁)))

    lemma₈′ :
      Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
      Γ ⊢ t ∷ A →
      Γ ∙ Singleton A t ⊢
        B U.[ consSubst
                (consSubst (wk1Subst idSubst)
                   (fst⟨ s ⟩ 𝟘 (wk1 A) (var x0)))
                (snd⟨ s ⟩ 𝟘 𝟘 (wk1 A) (Id (wk₂ A) (wk₂ t) (var x0))
                   (var x0))
            ]
    lemma₈′ ⊢B ⊢t =
      syntacticEq (lemma₈ (refl (syntacticTerm ⊢t)) (refl ⊢B) (refl ⊢t))
        .proj₁

    lemma₉ :
      Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
      Γ ⊢ v ∷ Id A t u →
      Γ ⊢
        B U.[ consSubst
                (consSubst (wk1Subst idSubst)
                   (fst⟨ s ⟩ 𝟘 (wk1 A) (var x0)))
                (snd⟨ s ⟩ 𝟘 𝟘 (wk1 A) (Id (wk₂ A) (wk₂ t) (var x0))
                   (var x0))
            ]
          [ prod s 𝟘 u v ]₀ ≡
        B [ u , v ]₁₀
    lemma₉ {A} {t} {B} {v} {u} ⊢B ⊢v =
      case inversion-Id (syntacticTerm ⊢v) of λ
        (_ , ⊢t , ⊢u) →
      case PE.subst (_⊢_∷_ _ _)
             (PE.sym $ PE.cong₃ Id
                (wk1-sgSubst _ _)
                (wk1-sgSubst _ _)
                PE.refl)
             ⊢v of λ
        ⊢v′ →

      B U.[ consSubst
              (consSubst (wk1Subst idSubst)
                 (fst⟨ s ⟩ 𝟘 (wk1 A) (var x0)))
              (snd⟨ s ⟩ 𝟘 𝟘 (wk1 A) (Id (wk₂ A) (wk₂ t) (var x0))
                 (var x0))
          ]
        [ prod s 𝟘 u v ]₀                                              ≡⟨ substCompEq B ⟩⊢≡

      B U.[ sgSubst (prod s 𝟘 u v) ₛ•ₛ
            consSubst
              (consSubst (wk1Subst idSubst)
                 (fst⟨ s ⟩ 𝟘 (wk1 A) (var x0)))
              (snd⟨ s ⟩ 𝟘 𝟘 (wk1 A) (Id (wk₂ A) (wk₂ t) (var x0))
                 (var x0))
          ]                                                            ≡⟨ (flip substVar-to-subst B λ where
                                                                             x0 → PE.refl
                                                                             (x0 +1) → PE.refl
                                                                             (_ +1 +1) → PE.refl) ⟩⊢≡
      B [ fst⟨ s ⟩ 𝟘 (wk1 A) (var x0) [ prod s 𝟘 u v ]₀
        , snd⟨ s ⟩ 𝟘 𝟘 (wk1 A) (Id (wk₂ A) (wk₂ t) (var x0)) (var x0)
            [ prod s 𝟘 u v ]₀
        ]₁₀                                                            ≡⟨ PE.cong₂ (λ t u → B [ t , u ]₁₀)
                                                                            (PE.trans fst⟨⟩-[] $
                                                                             PE.cong₂ (fst⟨ _ ⟩ _) (wk1-sgSubst _ _) PE.refl)
                                                                            (PE.trans snd⟨⟩-[] $
                                                                             PE.cong₃ (snd⟨ _ ⟩ _ _)
                                                                               (wk1-sgSubst _ _)
                                                                               (PE.cong₃ Id lemma₅ lemma₅ PE.refl)
                                                                               PE.refl) ⟩⊢≡
      B [ fst⟨ s ⟩ 𝟘 A (prod s 𝟘 u v)
        , snd⟨ s ⟩ 𝟘 𝟘 A (Id (wk1 A) (wk1 t) (var x0)) (prod s 𝟘 u v)
        ]₁₀                                                            ≡⟨ substTypeEq₂ (refl ⊢B)
                                                                            (fst⟨⟩-β-≡ (J-motive-context-type ⊢t) ⊢u ⊢v′ Σ-ok)
                                                                            (snd⟨⟩-β-≡ (J-motive-context-type ⊢t) ⊢u ⊢v′ Σ-ok) ⟩⊢∎
      B [ u , v ]₁₀                                                    ∎
      where
      open TypeR

  opaque
    unfolding Jᵉ

    -- An equality rule for Jᵉ.

    Jᵉ-cong :
      Γ ⊢ l₁ ≡ l₂ ∷ Level →
      Γ ⊢ A₁ ≡ A₂ ∷ U l₁ →
      Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
      Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ ≡ B₂ →
      Γ ⊢ u₁ ≡ u₂ ∷ B₁ [ t₁ , rfl ]₁₀ →
      Γ ⊢ v₁ ≡ v₂ ∷ A₁ →
      Γ ⊢ w₁ ≡ w₂ ∷ Id A₁ t₁ v₁ →
      Γ ⊢ Jᵉ l₁ A₁ t₁ B₁ u₁ v₁ w₁ ≡ Jᵉ l₂ A₂ t₂ B₂ u₂ v₂ w₂ ∷
        B₁ [ v₁ , w₁ ]₁₀
    Jᵉ-cong l₁≡l₂ A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂ =
      let ⊢B₁ , _        = wf-⊢≡ B₁≡B₂
          ⊢A₁ , ⊢t₁  , _ = wf-⊢≡∷ t₁≡t₂
          _ , ⊢w₁  , _   = wf-⊢≡∷ w₁≡w₂
      in
      conv
        (substᵉ-cong l₁≡l₂
           (ΠΣ-cong′ A₁≡A₂
              (Id-cong (wkEqTerm₁ ⊢A₁ A₁≡A₂) (wkEqTerm₁ ⊢A₁ t₁≡t₂)
                 (refl (var₀ ⊢A₁)))
              Σ-ok)
           (lemma₈ (univ A₁≡A₂) B₁≡B₂ t₁≡t₂)
           (prod-cong (J-motive-context-type ⊢t₁) t₁≡t₂
              (_⊢_≡_∷_.refl $
               PE.subst (_⊢_∷_ _ _)
                 (PE.sym $ PE.cong₃ Id
                    (wk1-sgSubst _ _)
                    (wk1-sgSubst _ _)
                    PE.refl) $
               rflⱼ ⊢t₁)
              Σ-ok)
           (prod-cong (J-motive-context-type ⊢t₁) v₁≡v₂
              (PE.subst (_⊢_≡_∷_ _ _ _)
                 (PE.sym $ PE.cong₃ Id
                    (wk1-sgSubst _ _)
                    (wk1-sgSubst _ _)
                    PE.refl)
                 w₁≡w₂)
              Σ-ok)
           (PE.subst (_⊢_≡_∷_ _ _ _)
              (PE.cong₃ Id wk₂-[,] wk₂-[,] PE.refl) $
            J-cong′ (univ A₁≡A₂) t₁≡t₂ (lemma₆ (univ A₁≡A₂) t₁≡t₂)
              (refl (lemma₇ ⊢t₁)) v₁≡v₂ w₁≡w₂)
           (conv u₁≡u₂ $ sym $ lemma₉ ⊢B₁ (rflⱼ ⊢t₁)))
        (lemma₉ ⊢B₁ ⊢w₁)

  opaque

    -- A typing rule for Jᵉ.

    ⊢Jᵉ :
      Γ ⊢ A ∷ U l →
      Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
      Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
      Γ ⊢ w ∷ Id A t v →
      Γ ⊢ Jᵉ l A t B u v w ∷ B [ v , w ]₁₀
    ⊢Jᵉ ⊢A ⊢B ⊢u ⊢w =
      let ⊢l          = inversion-U-Level (wf-⊢∷ ⊢A)
          _ , ⊢t , ⊢v = inversion-Id (wf-⊢∷ ⊢w)
      in
      wf-⊢≡∷
        (Jᵉ-cong (refl ⊢l) (refl ⊢A) (refl ⊢t) (refl ⊢B) (refl ⊢u)
           (refl ⊢v) (refl ⊢w))
        .proj₂ .proj₁

  opaque
    unfolding Jᵉ

    -- A reduction rule for Jᵉ.

    Jᵉ-⇒*′ :
      Γ ⊢ A ∷ U l →
      Γ ⊢ t ≡ t′ ∷ A →
      Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
      Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
      Γ ⊢ Jᵉ l A t B u t′ rfl ⇒* u ∷ B [ t , rfl ]₁₀
    Jᵉ-⇒*′ {A} {l} {t} {t′} {B} {u} ⊢A t≡t′ ⊢B ⊢u =
      let _ , ⊢t , _ = wf-⊢≡∷ t≡t′
          ⊢Singleton = ⊢Singleton ⊢A ⊢t
          ⊢rfl       =
            PE.subst (_⊢_∷_ _ _)
              (PE.sym $ PE.cong₃ Id
                 (wk1-sgSubst _ _)
                 (wk1-sgSubst _ _)
                 PE.refl) $
            rflⱼ ⊢t
          t,rfl≡t′,rfl =
            prod-cong (J-motive-context-type ⊢t) t≡t′ (refl ⊢rfl) Σ-ok
      in
      substᵉ
        l
        (Singleton A t)
        (B U.[ consSubst
                 (consSubst (wk1Subst idSubst)
                    (fst⟨ s ⟩ 𝟘 (wk1 A) (var x0)))
                 (snd⟨ s ⟩ 𝟘 𝟘 (wk1 A) (Id (wk₂ A) (wk₂ t) (var x0))
                    (var x0)) ])
        (prod s 𝟘 t rfl)
        (prod s 𝟘 t′ rfl)
        (J 𝟘 (𝟘 ∧ 𝟙) A t
           (Id (wk₂ (Singleton A t)) (wk₂ (prod s 𝟘 t rfl))
              (prod s 𝟘 (var x1) (var x0)))
           rfl t′ rfl)
        u                                                             ⇒⟨ _⊢_⇒_∷_.conv
                                                                           (substᵉ-subst ⊢Singleton (lemma₈′ ⊢B ⊢t)
                                                                              (conv
                                                                                 (PE.subst (_⊢_⇒_∷_ _ _ _)
                                                                                    (PE.cong₃ Id wk₂-[,] wk₂-[,] PE.refl) $
                                                                                  J-β-⇒ t≡t′ (lemma₆′ ⊢t) (lemma₇ ⊢t))
                                                                                  (Id-cong (refl (univ ⊢Singleton))
                                                                                     (refl (prodⱼ (J-motive-context-type ⊢t) ⊢t ⊢rfl Σ-ok))
                                                                                     t,rfl≡t′,rfl))
                                                                              (conv ⊢u $ sym $ lemma₉ ⊢B (rflⱼ ⊢t))) $
                                                                         _⊢_≡_.trans (lemma₉ ⊢B (rflⱼ′ t≡t′)) $
                                                                         substTypeEq₂ (refl ⊢B) (sym′ t≡t′) $
                                                                         PE.subst (_⊢_≡_∷_ _ _ _)
                                                                           (PE.sym $ PE.cong₃ Id
                                                                              (wk1-sgSubst _ _)
                                                                              (wk1-sgSubst _ _)
                                                                              PE.refl) $
                                                                         _⊢_≡_∷_.conv (refl (rflⱼ ⊢t)) $
                                                                         Id-cong (refl (univ ⊢A)) (refl ⊢t) t≡t′ ⟩
      substᵉ
        l
        (Singleton A t)
        (B U.[ consSubst
                 (consSubst (wk1Subst idSubst)
                    (fst⟨ s ⟩ 𝟘 (wk1 A) (var x0)))
                 (snd⟨ s ⟩ 𝟘 𝟘 (wk1 A) (Id (wk₂ A) (wk₂ t) (var x0))
                    (var x0)) ])
        (prod s 𝟘 t rfl)
        (prod s 𝟘 t′ rfl)
        rfl
        u                                                             ⇒*⟨ conv*
                                                                            (substᵉ-⇒*′ ⊢Singleton (lemma₈′ ⊢B ⊢t) t,rfl≡t′,rfl
                                                                               (conv ⊢u $ sym $ lemma₉ ⊢B (rflⱼ ⊢t)))
                                                                            (lemma₉ ⊢B (rflⱼ ⊢t)) ⟩∎

      u                                                               ∎

  opaque

    -- Another reduction rule for Jᵉ.

    Jᵉ-⇒* :
      Γ ⊢ A ∷ U l →
      Γ ⊢ t ∷ A →
      Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
      Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
      Γ ⊢ Jᵉ l A t B u t rfl ⇒* u ∷ B [ t , rfl ]₁₀
    Jᵉ-⇒* ⊢A ⊢t = Jᵉ-⇒*′ ⊢A (refl ⊢t)

  opaque

    -- An equality rule for Jᵉ.

    Jᵉ-≡ :
      Γ ⊢ A ∷ U l →
      Γ ⊢ t ∷ A →
      Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
      Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
      Γ ⊢ Jᵉ l A t B u t rfl ≡ u ∷ B [ t , rfl ]₁₀
    Jᵉ-≡ ⊢A ⊢t ⊢B ⊢u = subset*Term (Jᵉ-⇒* ⊢A ⊢t ⊢B ⊢u)

  opaque
    unfolding Erased.[_] Jᵉ substᵉ subst

    -- A certain reduction rule for Jᵉ is not valid.

    ¬-Jᵉ-subst :
      ¬ (∀ {n} {Γ : Con Term n} {l A t : Term n} {B : Term (2+ n)}
           {u v w₁ w₂ : Term n} →
         Γ ⊢ A ∷ U l →
         Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
         Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
         Γ ⊢ w₁ ⇒ w₂ ∷ Id A t v →
         Γ ⊢ Jᵉ l A t B u v w₁ ⇒ Jᵉ l A t B u v w₂ ∷ B [ v , w₁ ]₁₀)
    ¬-Jᵉ-subst Jᵉ-subst = ¬lhs⇒rhs lhs⇒rhs
      where
      Γ′                             : Con Term 0
      l′ A′ t″ u′ v′ w₁′ w₂′ lhs rhs : Term 0
      B′                             : Term 2
      Γ′  = ε
      l′  = zeroᵘ
      A′  = ℕ
      t″  = zero
      B′  = ℕ
      u′  = zero
      v′  = zero
      w₁′ = subst 𝟘 ℕ (Id ℕ zero zero) zero zero rfl rfl
      w₂′ = rfl
      lhs = Jᵉ l′ A′ t″ B′ u′ v′ w₁′
      rhs = Jᵉ l′ A′ t″ B′ u′ v′ w₂′

      ⊢A′ : Γ′ ⊢ A′ ∷ U l′
      ⊢A′ = ℕⱼ ε

      ⊢B′ : Γ′ ∙ A′ ∙ Id (wk1 A′) (wk1 t″) (var x0) ⊢ B′
      ⊢B′ = ⊢ℕ (∙ Idⱼ′ (zeroⱼ (∙ ⊢ℕ ε)) (var₀ (⊢ℕ ε)))

      ⊢u′ : Γ′ ⊢ u′ ∷ B′ [ t″ , rfl ]₁₀
      ⊢u′ = zeroⱼ ε

      w₁′⇒w₂′ : Γ′ ⊢ w₁′ ⇒ w₂′ ∷ Id A′ t″ v′
      w₁′⇒w₂′ = subst-⇒
        (Idⱼ′ (zeroⱼ (∙ ⊢ℕ ε)) (zeroⱼ (∙ ⊢ℕ ε)))
        (zeroⱼ ε)
        (rflⱼ (zeroⱼ ε))

      lhs⇒rhs : Γ′ ⊢ lhs ⇒ rhs ∷ B′ [ v′ , w₁′ ]₁₀
      lhs⇒rhs = Jᵉ-subst ⊢A′ ⊢B′ ⊢u′ w₁′⇒w₂′

      ¬lhs⇒rhs : ¬ Γ′ ⊢ lhs ⇒ rhs ∷ C
      ¬lhs⇒rhs (conv lhs⇒rhs _) = ¬lhs⇒rhs lhs⇒rhs
