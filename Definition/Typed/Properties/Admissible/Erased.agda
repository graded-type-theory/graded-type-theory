------------------------------------------------------------------------
-- Some properties related to typing and Erased
------------------------------------------------------------------------

import Graded.Modality
open import Definition.Typed.Restrictions
import Definition.Untyped hiding (_[_])

module Definition.Typed.Properties.Admissible.Erased
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (open Definition.Untyped M)
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
open import Definition.Typed.Properties.Admissible.Level R
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
open import Definition.Typed.Weakening R as W
open import Definition.Typed.Well-formed R

import Definition.Untyped M as U
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Identity 𝕄
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sigma 𝕄
open import Definition.Untyped.Sup R
open import Definition.Untyped.Unit 𝕄
open import Definition.Untyped.Whnf M

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

private variable
  k n                                                  : Nat
  Γ                                                    : Cons _ _
  A A₁ A₂ B B₁ B₂ C t t′ t₁ t₂ u u₁ u₂ v v₁ v₂ w w₁ w₂ : Term _
  l l₁ l₂                                              : Lvl _
  σ                                                    : Subst _ _
  s                                                    : Strength
  p                                                    : M

------------------------------------------------------------------------
-- Lemmas about Erased, [_] and erased

-- Some lemmas that are proved under the assumption that Erased is
-- allowed.

module _ (Erased-ok : Erased-allowed s) where

  open Erased s

  private module P′ = P Erased-ok

  opaque

    -- A formation rule for Erased.

    Erasedⱼ′ :
      Γ »∙ A ⊢ wk1 l ∷Level →
      Γ ⊢ Erased l A
    Erasedⱼ′ = P′.Erasedⱼ′

  opaque

    -- A variant of Erasedⱼ″.

    Erasedⱼ :
      Γ ⊢ l ∷Level →
      Γ ⊢ A →
      Γ ⊢ Erased l A
    Erasedⱼ = P′.Erasedⱼ

  opaque

    -- An equality rule for Erased.

    Erased-cong′ :
      Γ »∙ A₁ ⊢ wk1 l₁ ≡ wk1 l₂ ∷Level →
      Γ ⊢ A₁ ≡ A₂ →
      Γ ⊢ Erased l₁ A₁ ≡ Erased l₂ A₂
    Erased-cong′ = P′.Erased-cong′

  opaque

    -- A variant of Erased-cong′.

    Erased-cong :
      Γ ⊢ l₁ ≡ l₂ ∷Level →
      Γ ⊢ A₁ ≡ A₂ →
      Γ ⊢ Erased l₁ A₁ ≡ Erased l₂ A₂
    Erased-cong l₁≡l₂ A₁≡A₂ =
      let ⊢A₁ , _ = wf-⊢ A₁≡A₂ in
      P′.Erased-cong l₁≡l₂ ⊢A₁ A₁≡A₂

  opaque

    -- An introduction rule for U for Erased.

    Erasedⱼ-U : Γ ⊢ A ∷ U l → Γ ⊢ Erased l A ∷ U l
    Erasedⱼ-U ⊢A =
      let ⊢l = inversion-U-Level (wf-⊢ ⊢A) in
      P′.Erasedⱼ-U ⊢l ⊢A

  opaque

    -- An equality rule for U for Erased.

    Erased-cong-U′ :
      Γ »∙ A₁ ⊢ wk1 l₁ ≡ wk1 l₂ ∷Level →
      Γ ⊢ A₁ ≡ A₂ ∷ U l₁ →
      Γ ⊢ Erased l₁ A₁ ≡ Erased l₂ A₂ ∷ U l₁
    Erased-cong-U′ wk1-l₁≡wk1-l₂ A₁≡A₂ =
      let ⊢U , _ = wf-⊢ A₁≡A₂
          ⊢l₁    = inversion-U-Level ⊢U
      in
      P′.Erased-cong-U′ ⊢l₁ wk1-l₁≡wk1-l₂ A₁≡A₂

  opaque

    -- A variant of Erased-cong-U′.

    Erased-cong-U :
      Γ ⊢ l₁ ≡ l₂ ∷Level →
      Γ ⊢ A₁ ≡ A₂ ∷ U l₁ →
      Γ ⊢ Erased l₁ A₁ ≡ Erased l₂ A₂ ∷ U l₁
    Erased-cong-U l₁≡l₂ A₁≡A₂ =
      let ⊢l₁ , _     = wf-⊢ l₁≡l₂
          _ , ⊢A₁ , _ = wf-⊢ A₁≡A₂
      in
      P′.Erased-cong-U ⊢l₁ l₁≡l₂ (univ ⊢A₁) A₁≡A₂

  opaque

    -- An introduction rule for Erased.

    []ⱼ :
      Γ ⊢ l ∷Level →
      Γ ⊢ t ∷ A →
      Γ ⊢ [ t ] ∷ Erased l A
    []ⱼ ⊢l ⊢t = P′.[]ⱼ ⊢l (wf-⊢ ⊢t) ⊢t

  opaque

    -- An equality rule for Erased.

    []-cong′ :
      Γ ⊢ l ∷Level → Γ ⊢ t₁ ≡ t₂ ∷ A → Γ ⊢ [ t₁ ] ≡ [ t₂ ] ∷ Erased l A
    []-cong′ ⊢l t₁≡t₂ =
      let ⊢A , _ = wf-⊢ t₁≡t₂ in
      P′.[]-cong′ ⊢l ⊢A t₁≡t₂

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
      Γ ⊢ A₁ ≡ A₂ →
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
      Γ »∙ A ⊢ U (wk1 l₁) ≡ U (l₂ supᵘₗ wk1 l) × Γ »∙ A ⊢ U l₂ ≡ U₀
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
    Γ »∙ A ⊢ wk1 l ∷Level
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
          wf-⊢ C≡
        ⊢l , _ =
          inversion-Lift ⊢Lift
    in
    B , q , ⊢t , (Unit-ok , Σˢ-ok) , C , l , A≡ ,
    trans C≡ (Lift-cong (refl-⊢≡∷L ⊢l) D≡)

------------------------------------------------------------------------
-- Lemmas about erasedrec

private

  -- Some lemmas used below.

  opaque
    unfolding Erased.Erased

    erasedrec-lemma₁ :
      let open Erased s in
      Γ »∙ Erased l A₁ ⊢ B₁ ≡ B₂ →
      Γ »∙ A₁ »∙ Lift (wk1 l) (Unit s) »∙ Unit s ⊢
        B₁ [ 3 ][ prod s 𝟘 (var x2) (lift (var x0)) ]↑ ≡
        B₂ [ 3 ][ prod s 𝟘 (var x2) (lift (var x0)) ]↑
    erasedrec-lemma₁ B₁≡B₂ =
      let (Unit-ok , Σ-ok) , ⊢A₁ , ⊢wk1-l =
            inversion-Erased (⊢∙→⊢ (wf B₁≡B₂))
          ⊢Unit′        = ⊢Unit (∙ Liftⱼ ⊢wk1-l (⊢Unit (∙ ⊢A₁) Unit-ok))
                            Unit-ok
          ⊢wk3          = ⊢ˢʷ∷-wkSubst (∙ ⊢Unit′)
                            (⊢ˢʷ∷-idSubst (wf ⊢A₁))
          ⊢A[wk3]       = subst-⊢ ⊢A₁ ⊢wk3
          ⊢wk1-l-[wk3⇑] = subst-⊢ ⊢wk1-l (⊢ˢʷ∷-⇑ ⊢A[wk3] ⊢wk3)
      in
      [][]↑-cong B₁≡B₂ $ _⊢_≡_∷_.refl $
      prodⱼ
        (Liftⱼ ⊢wk1-l-[wk3⇑] (⊢Unit (∙ ⊢A[wk3]) Unit-ok))
        (PE.subst (_⊢_∷_ _ _) (wk[]≡[] 3) $ var₂ ⊢Unit′)
        (liftⱼ′
           (subst-⊢ ⊢wk1-l-[wk3⇑]
              (PE.subst (_⊢ˢʷ_∷_ _ _)
                 (PE.cong (_∙_ _) $
                  PE.trans (wk[]≡wk[]′ {n = 3}) $ wk≡subst _ _) $
               ⊢ˢʷ∷-sgSubst (var₂ ⊢Unit′)))
           (var₀ ⊢Unit′))
        Σ-ok

  opaque
    unfolding Erased.[_]

    erasedrec-lemma₂ :
      let open Erased s in
      ∀ B →
      Unit-allowed s →
      Γ »∙ A ⊢ wk1 l ∷Level →
      Γ »∙ A ⊢ t₁ ≡ t₂ ∷ B [ [ var x0 ] ]↑ →
      Γ »∙ A »∙ Lift (wk1 l) (Unit s) ⊢ wk1 t₁ ≡ wk1 t₂ ∷
        B [ 3 ][ prod s 𝟘 (var x2) (lift (var x0)) ]↑ [ star s ]₀
    erasedrec-lemma₂ {s} B Unit-ok ⊢wk1-l t₁≡t₂ =
      flip (PE.subst (_⊢_≡_∷_ _ _ _))
        (wk₁ (Liftⱼ ⊢wk1-l (⊢Unit (wf t₁≡t₂) Unit-ok))
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
      Γ .defs » drop k (Γ .vars) ∙ Erased l A ⊢ B →
      Γ ⊢ t ∷ wk[ k ] A →
      Γ ⊢ u ∷ Lift (wk[ k ] l) (U.Unit s) →
      Γ ⊢
        B U.[ 1+ k ][ prod s 𝟘 (wk1 t) (lift (var x0)) ]↑
          U.[ lower u ]₀ ≡
        B U.[ k ][ prod s 𝟘 t u ]↑
    erasedrec-lemma₃ {s} {k} {l} {B} {t} {u} ⊢B ⊢t ⊢u =
      let (Unit-ok , Σ-ok) , ⊢A , ⊢wk1-l =
            inversion-Erased (⊢∙→⊢ (wf ⊢B))
          ⊢wk-A = W.wk (ʷ⊇-drop (wf ⊢t)) ⊢A
      in
      B U.[ 1+ k ][ prod s 𝟘 (wk1 t) (lift (var x0)) ]↑ U.[ lower u ]₀  ≡⟨ [][]↑-[₀⇑] 0 B ⟩⊢≡

      B U.[ k ][ prod s 𝟘 (wk1 t U.[ lower u ]₀) (lift (lower u)) ]↑    ≡⟨ PE.cong (λ t → B U.[ _ ][ prod _ _ t _ ]↑) $ wk1-sgSubst _ _ ⟩⊢≡

      B U.[ k ][ prod s 𝟘 t (lift (lower u)) ]↑                         ≡⟨ subst-⊢≡ (refl ⊢B) $ ⊢ˢʷ≡∷-[][]↑ $
                                                                           PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym wk[]≡wk[]′) $
                                                                           prod-cong
                                                                             (Liftⱼ (W.wk (liftʷ ⊇-drop ⊢wk-A) ⊢wk1-l)
                                                                                (⊢Unit (∙ ⊢wk-A) Unit-ok))
                                                                             (refl $
                                                                              PE.subst (_⊢_∷_ _ _) (wk[]≡wk[]′ {n = k})
                                                                                ⊢t)
                                                                             (⊢lift-lower≡∷ $
                                                                              PE.subst (_⊢_∷_ _ _)
                                                                                (PE.cong (flip Lift _) $ PE.sym $
                                                                                 PE.trans (PE.cong U._[ _ ]₀ $ lift-wk1 _ l) $
                                                                                 PE.trans (step-sgSubst _ _) $
                                                                                 PE.sym $ wk[]≡wk[]′ {n = k})
                                                                                ⊢u)
                                                                             Σ-ok ⟩⊢∎
      B U.[ k ][ prod s 𝟘 t u ]↑                                        ∎
      where
      open TypeR

  opaque

    erasedrec-lemma₃′ :
      let open Erased s in
      Γ »∙ Erased l A ⊢ B →
      Γ »∙ A »∙ Lift (wk1 l) (Unit s) ⊢
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
    Γ »∙ Erased l A ⊢ B₁ ≡ B₂ →
    Γ »∙ A ⊢ t₁ ≡ t₂ ∷ B₁ [ [ var x0 ] ]↑ →
    Γ ⊢ u₁ ≡ u₂ ∷ Erased l A →
    Γ ⊢ erasedrec p B₁ t₁ u₁ ≡ erasedrec p B₂ t₂ u₂ ∷ B₁ [ u₁ ]₀
  erasedrec-cong {s} {l} {B₁} B₁≡B₂ t₁≡t₂ u₁≡u₂ =
    let ⊢B₁ , _                     = wf-⊢ B₁≡B₂
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
    Γ »∙ Erased l A ⊢ B →
    Γ »∙ A ⊢ t ∷ B [ [ var x0 ] ]↑ →
    Γ ⊢ u ∷ Erased l A →
    Γ ⊢ erasedrec p B t u ∷ B [ u ]₀
  ⊢erasedrec ⊢B ⊢t ⊢u =
    wf-⊢ (erasedrec-cong (refl ⊢B) (refl ⊢t) (refl ⊢u)) .proj₂ .proj₁

opaque
  unfolding Erased.Erased Erased.[_] Erased.erasedrec

  -- Another equality rule for erasedrec.

  erasedrec-β :
    let open Erased s in
    Γ »∙ Erased l A ⊢ B →
    Γ »∙ A ⊢ t ∷ B [ [ var x0 ] ]↑ →
    Γ ⊢ u ∷ A →
    Γ ⊢ erasedrec p B t [ u ] ≡ t [ u ]₀ ∷ B [ [ u ] ]₀
  erasedrec-β {s} {l} {B} {t} {u} {p} ⊢B ⊢t ⊢u =
    let (Unit-ok , Σ-ok) , ⊢A ,  ⊢wk1-l = inversion-Erased
                                            (⊢∙→⊢ (wf ⊢B))
        ⊢Γ                              = wf ⊢A
        ⊢Unit′                          = ⊢Unit ⊢Γ Unit-ok
        ⊢star                           = starⱼ ⊢Γ Unit-ok
        ⊢A′                             = wk₁ ⊢Unit′ ⊢A
        ⊢wk1-l[u]₀                      = subst-⊢₀ ⊢wk1-l ⊢u
        ⊢l                              =
          PE.subst (_⊢_∷Level _) (wk1-sgSubst _ _) ⊢wk1-l[u]₀
    in
    prodrec⟨ s ⟩ is-𝕨 𝟘 p B [ u ]
      (unitrec⟨ s ⟩ 𝟙 p (B [ 3 ][ prod s 𝟘 (var x2) (lift (var x0)) ]↑)
         (lower (var x0)) (wk1 t))                                       ≡⟨ prodrec⟨⟩-β (λ _ → ⊢B) ⊢u (liftⱼ′ ⊢wk1-l[u]₀ ⊢star)
                                                                              (conv
                                                                                 (⊢unitrec⟨⟩ (wf-⊢ (erasedrec-lemma₁ (refl ⊢B)) .proj₁)
                                                                                    (lowerⱼ (var₀ (Liftⱼ ⊢wk1-l (⊢Unit (wf ⊢t) Unit-ok))))
                                                                                    (wf-⊢ (erasedrec-lemma₂ B Unit-ok ⊢wk1-l (refl ⊢t))
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
                                                                                  wf-⊢
                                                                                    (erasedrec-lemma₃ ⊢B (wk₁ ⊢Unit′ ⊢u) $
                                                                                     liftⱼ′
                                                                                       (PE.subst (_⊢_∷Level _) (wk1-[][]↑ 1) $
                                                                                        subst-⊢ ⊢wk1-l (⊢ˢʷ∷-[][]↑ (wk₁ ⊢Unit′ ⊢u)))
                                                                                       (var₀ ⊢Unit′))
                                                                                    .proj₂)
                                                                                 (Lift-β′ ⊢star)
                                                                                 (refl $
                                                                                  PE.subst (_⊢_∷_ _ _)
                                                                                    (PE.trans ([][]↑-[₀⇑] 0 B) $
                                                                                     PE.sym $
                                                                                     PE.trans ([][]↑-[₀⇑] 0 B) $
                                                                                     PE.cong (B U.[_]₀ ∘→ [_]) $ wk1-sgSubst _ _) $
                                                                                  subst-⊢₀ ⊢t ⊢u))
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
                                                                                       (W.wk (liftʷ (step id) ⊢A′) $ wk₁ ⊢A ⊢l)
                                                                                       (⊢Unit (∙ ⊢A′) Unit-ok))
                                                                                    (wk₁ ⊢Unit′ ⊢u)
                                                                                    (liftⱼ′
                                                                                       (PE.subst (_⊢_∷Level _)
                                                                                          (PE.trans (PE.sym $ PE.cong wk1 $ wk1-sgSubst _ _) $
                                                                                           wk-β (wk1 l)) $
                                                                                        wk₁ ⊢Unit′ ⊢l) $
                                                                                     var₀ ⊢Unit′)
                                                                                    Σ-ok)
                                                                               (PE.subst (_⊢_∷_ _ _) (PE.trans ([]↑-[]₀ B) (PE.sym lemma)) $
                                                                                subst-⊢₀ ⊢t ⊢u)) ⟩⊢∎
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
    Γ ⊢ t ∷ Erased l A →
    Γ ⊢ Erased-η l A t ∷ Id (Erased l A) [ erased A t ] t
  ⊢Erased-η {s} {l} {A} ⊢t =
    let ⊢Erased-A           = wf-⊢ ⊢t
        Erased-ok , ⊢A , ⊢l = inversion-Erased ⊢Erased-A
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
         ([]ⱼ Erased-ok
            (PE.subst (_⊢_∷Level _) wk[]′-[]↑ $
             subst-⊢ ⊢l $ ⊢ˢʷ∷-[][]↑ $ erasedⱼ $
             PE.subst (_⊢_∷_ _ _) wk-Erased $
             var₀ ⊢Erased-A)
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
       []-cong′ Erased-ok ⊢l
         (erased (wk1 A) (var x0) [ [ var x0 ] ]↑    ≡⟨ erased-[] ⟩⊢≡
          erased (wk1 A [ [ var x0 ] ]↑) [ var x0 ]  ≡⟨ PE.cong (flip erased _) $ wk1-[][]↑ 1 ⟩⊢≡
          erased (wk1 A) [ var x0 ]                  ≡⟨ Erased-β Erased-ok (var₀ ⊢A) ⟩⊢∎
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
    Γ ⊢ l₂ ∷Level →
    Γ ⊢ A₁ ≡ A₂ →
    Γ »∙ A₁ ⊢ t₁ ≡ t₂ ∷ wk1 B →
    Γ ⊢ u₁ ≡ u₂ ∷ Erased l₁ A₁ →
    Γ ⊢ mapᴱ A₁ t₁ u₁ ≡ mapᴱ A₂ t₂ u₂ ∷ Erased l₂ B
  mapᴱ-cong ⊢l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ =
    let ok , _ = inversion-Erased $ wf-⊢ u₁≡u₂ .proj₁ in
    []-cong′ ok ⊢l₂ $
    PE.subst (_⊢_≡_∷_ _ _ _) (wk1-sgSubst _ _) $
    subst-⊢≡₀ t₁≡t₂ (erased-cong A₁≡A₂ u₁≡u₂)

opaque

  -- A typing rule for mapᴱ.

  ⊢mapᴱ :
    let open Erased s in
    Γ ⊢ l₂ ∷Level →
    Γ »∙ A ⊢ t ∷ wk1 B →
    Γ ⊢ u ∷ Erased l₁ A →
    Γ ⊢ mapᴱ A t u ∷ Erased l₂ B
  ⊢mapᴱ ⊢l₂ ⊢t ⊢u =
    wf-⊢ (mapᴱ-cong ⊢l₂ (refl (⊢∙→⊢ (wf ⊢t))) (refl ⊢t) (refl ⊢u))
      .proj₂ .proj₁

opaque
  unfolding Erased.mapᴱ

  -- A β-rule for mapᴱ.

  mapᴱ-β :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ l ∷Level →
    Γ »∙ A ⊢ t ∷ wk1 B →
    Γ ⊢ u ∷ A →
    Γ ⊢ mapᴱ A t [ u ] ≡ [ t [ u ]₀ ] ∷ Erased l B
  mapᴱ-β ok ⊢l ⊢t ⊢u =
    []-cong′ ok ⊢l $
    PE.subst (_⊢_≡_∷_ _ _ _) (wk1-sgSubst _ _) $
    subst-⊢≡₀ ⊢t (Erased-β ok ⊢u)

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
      Γ »∙ A ⊢ B →
      Γ ⊢ t ∷ A →
      Γ ⊢ B [ erased (wk1 A) (var x0) ]↑ [ [ t ] ]₀ ≡ B [ t ]₀
    [erased-0]↑[[]]₀≡[]₀ {A} {B} {t} ⊢B ⊢t =
      B [ erased (wk1 A) (var x0) ]↑ [ [ t ] ]₀  ≡⟨ []↑-[]₀ B ⟩⊢≡
      B [ erased (wk1 A) (var x0) [ [ t ] ]₀ ]₀  ≡⟨ PE.cong (B [_]₀) erased-[] ⟩⊢≡
      B [ erased (wk1 A [ [ t ] ]₀) [ t ] ]₀     ≡⟨ PE.cong (λ A → B [ erased A _ ]₀) $ wk1-sgSubst _ _ ⟩⊢≡
      B [ erased A [ t ] ]₀                      ≡⟨ subst-⊢≡₀ ⊢B $ Erased-β Erased-ok ⊢t ⟩⊢∎
      B [ t ]₀                                   ∎
      where
      open TypeR

    ⊢[erased-0]↑ :
      Γ »∙ A ⊢ B →
      Γ »∙ Erased zeroᵘₗ A ⊢ B [ erased (wk1 A) (var x0) ]↑
    ⊢[erased-0]↑ ⊢B =
      let ⊢A = ⊢∙→⊢ (wf ⊢B) in
      subst-⊢ ⊢B $ ⊢ˢʷ∷-[][]↑ $ erasedⱼ $
      PE.subst (_⊢_∷_ _ _) wk-Erased $
      var₀ (Erasedⱼ Erased-ok (⊢zeroᵘ (wf ⊢A)) ⊢A)

  ----------------------------------------------------------------------
  -- Lemmas related to substᵉ

  opaque
    unfolding substᵉ

    -- A typing rule for substᵉ.

    ⊢substᵉ :
      Γ »∙ A ⊢ B →
      Γ ⊢ v ∷ Id A t u →
      Γ ⊢ w ∷ B [ t ]₀ →
      Γ ⊢ substᵉ A B t u v w ∷ B [ u ]₀
    ⊢substᵉ ⊢B ⊢v ⊢w =
      let ⊢A , ⊢t , ⊢u = inversion-Id (wf-⊢ ⊢v) in
      conv
        (⊢subst (⊢[erased-0]↑ ⊢B) ([]-congⱼ′ ok (⊢zeroᵘ (wf ⊢A)) ⊢v)
           (conv ⊢w $ sym $ [erased-0]↑[[]]₀≡[]₀ ⊢B ⊢t))
        ([erased-0]↑[[]]₀≡[]₀ ⊢B ⊢u)

  opaque
    unfolding substᵉ

    -- A reduction rule for substᵉ.

    substᵉ-⇒*′ :
      Γ »∙ A ⊢ B →
      Γ ⊢ t ≡ t′ ∷ A →
      Γ ⊢ u ∷ B [ t ]₀ →
      Γ ⊢ substᵉ A B t t′ rfl u ⇒* u ∷ B [ t ]₀
    substᵉ-⇒*′ {A} {B} {t} {t′} {u} ⊢B t≡t′ ⊢u =
      let ⊢A , ⊢t , _ = wf-⊢ t≡t′
          ⊢B[]↑       = ⊢[erased-0]↑ ⊢B
          ⊢0          = ⊢zeroᵘ (wf ⊢A)
          [t]≡[t′]    = []-cong′ Erased-ok ⊢0 t≡t′
          ≡B[t]₀      = [erased-0]↑[[]]₀≡[]₀ ⊢B ⊢t
          ⊢u          = conv ⊢u (sym ≡B[t]₀)
      in
      conv*
        (subst 𝟘 (Erased zeroᵘₗ A) (B [ erased (wk1 A) (var x0) ]↑)
           [ t ] [ t′ ] ([]-cong s zeroᵘₗ A t t′ rfl) u              ⇒⟨ conv (subst-subst ⊢B[]↑ ([]-cong-β ⊢0 t≡t′ ok) ⊢u) $
                                                                        subst-⊢≡₀ ⊢B[]↑ (sym′ [t]≡[t′]) ⟩
         subst 𝟘 (Erased zeroᵘₗ A) (B [ erased (wk1 A) (var x0) ]↑)
           [ t ] [ t′ ] rfl u                                        ⇒⟨ subst-⇒′ ⊢B[]↑ [t]≡[t′] ⊢u ⟩∎

         u                                                           ∎)
        ≡B[t]₀

  opaque

    -- Another reduction rule for substᵉ.

    substᵉ-⇒* :
      Γ »∙ A ⊢ B →
      Γ ⊢ t ∷ A →
      Γ ⊢ u ∷ B [ t ]₀ →
      Γ ⊢ substᵉ A B t t rfl u ⇒* u ∷ B [ t ]₀
    substᵉ-⇒* ⊢B ⊢t = substᵉ-⇒*′ ⊢B (refl ⊢t)

  opaque

    -- An equality rule for substᵉ.

    substᵉ-≡ :
      Γ »∙ A ⊢ B →
      Γ ⊢ t ∷ A →
      Γ ⊢ u ∷ B [ t ]₀ →
      Γ ⊢ substᵉ A B t t rfl u ≡ u ∷ B [ t ]₀
    substᵉ-≡ ⊢B ⊢t ⊢u =
      subset*Term (substᵉ-⇒* ⊢B ⊢t ⊢u)

  opaque
    unfolding substᵉ

    -- An equality rule for substᵉ.

    substᵉ-cong :
      Γ ⊢ A₁ ≡ A₂ →
      Γ »∙ A₁ ⊢ B₁ ≡ B₂ →
      Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
      Γ ⊢ u₁ ≡ u₂ ∷ A₁ →
      Γ ⊢ v₁ ≡ v₂ ∷ Id A₁ t₁ u₁ →
      Γ ⊢ w₁ ≡ w₂ ∷ B₁ [ t₁ ]₀ →
      Γ ⊢ substᵉ A₁ B₁ t₁ u₁ v₁ w₁ ≡ substᵉ A₂ B₂ t₂ u₂ v₂ w₂ ∷
        B₁ [ u₁ ]₀
    substᵉ-cong A₁≡A₂ B₁≡B₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ w₁≡w₂ =
      let ⊢A₁ , _     = wf-⊢ A₁≡A₂
          ⊢B₁ , _     = wf-⊢ B₁≡B₂
          _ , ⊢t₁ , _ = wf-⊢ t₁≡t₂
          _ , ⊢u₁ , _ = wf-⊢ u₁≡u₂
          ⊢0          = ⊢zeroᵘ (wf ⊢A₁)
          ⊢Erased-A₁  = Erasedⱼ Erased-ok ⊢0 ⊢A₁
      in
      conv
        (subst-cong (Erased-cong Erased-ok (refl-⊢≡∷L ⊢0) A₁≡A₂)
           (subst-⊢≡ B₁≡B₂ $ ⊢ˢʷ≡∷-[][]↑ $
            erased-cong {l = zeroᵘₗ} (wk₁ ⊢Erased-A₁ A₁≡A₂) $
            refl $ PE.subst (_⊢_∷_ _ _) wk-Erased $
            var₀ ⊢Erased-A₁)
           ([]-cong′ Erased-ok ⊢0 t₁≡t₂)
           ([]-cong′ Erased-ok ⊢0 u₁≡u₂)
           ([]-cong-cong (refl-⊢≡∷L ⊢0) A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok)
           (conv w₁≡w₂ $ sym $ [erased-0]↑[[]]₀≡[]₀ ⊢B₁ ⊢t₁))
        ([erased-0]↑[[]]₀≡[]₀ ⊢B₁ ⊢u₁)

  opaque
    unfolding substᵉ

    -- A reduction rule for substᵉ.

    substᵉ-subst :
      Γ »∙ A ⊢ B →
      Γ ⊢ v₁ ⇒ v₂ ∷ Id A t u →
      Γ ⊢ w ∷ B [ t ]₀ →
      Γ ⊢ substᵉ A B t u v₁ w ⇒ substᵉ A B t u v₂ w ∷ B [ u ]₀
    substᵉ-subst ⊢B v₁⇒v₂ ⊢w =
      let _ , ⊢t , ⊢u = inversion-Id (wf-⊢ (subsetTerm v₁⇒v₂) .proj₁)
      in
      conv
        (subst-subst (⊢[erased-0]↑ ⊢B)
           ([]-cong-subst (⊢zeroᵘ (wf ⊢t)) v₁⇒v₂ ok)
           (conv ⊢w $ sym $ [erased-0]↑[[]]₀≡[]₀ ⊢B ⊢t))
        ([erased-0]↑[[]]₀≡[]₀ ⊢B ⊢u)

------------------------------------------------------------------------
-- Some lemmas related to Jᵉ

module _ {s : Strength} where

  open Erased s

  opaque
    unfolding Erased.[_] Jᵉ substᵉ subst

    -- A certain reduction rule for Jᵉ is not valid.

    ¬-Jᵉ-subst-⇒* :
      ¬ (∀ {m n} {Γ : Cons m n}
           {A t : Term n} {B : Term (2+ n)} {u v w₁ w₂ : Term n} →
         Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
         Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
         Γ ⊢ w₁ ⇒ w₂ ∷ Id A t v →
         Γ ⊢ Jᵉ A t B u v w₁ ⇒* Jᵉ A t B u v w₂ ∷ B [ v , w₁ ]₁₀)
    ¬-Jᵉ-subst-⇒* Jᵉ-subst = ¬lhs⇒*rhs lhs⇒*rhs
      where
      Γ′                          : Cons 0 0
      A′ t″ u′ v′ w₁′ w₂′ lhs rhs : Term 0
      B′                          : Term 2
      Γ′  = ε » ε
      A′  = ℕ
      t″  = zero
      B′  = ℕ
      u′  = zero
      v′  = zero
      w₁′ = subst 𝟘 ℕ (Id ℕ zero zero) zero zero rfl rfl
      w₂′ = rfl
      lhs = Jᵉ A′ t″ B′ u′ v′ w₁′
      rhs = Jᵉ A′ t″ B′ u′ v′ w₂′

      ⊢B′ : Γ′ »∙ A′ »∙ Id (wk1 A′) (wk1 t″) (var x0) ⊢ B′
      ⊢B′ = ⊢ℕ (∙ Idⱼ′ (zeroⱼ (∙ ⊢ℕ εε)) (var₀ (⊢ℕ εε)))

      ⊢u′ : Γ′ ⊢ u′ ∷ B′ [ t″ , rfl ]₁₀
      ⊢u′ = zeroⱼ εε

      w₁′⇒w₂′ : Γ′ ⊢ w₁′ ⇒ w₂′ ∷ Id A′ t″ v′
      w₁′⇒w₂′ = subst-⇒
        (Idⱼ′ (zeroⱼ (∙ ⊢ℕ εε)) (zeroⱼ (∙ ⊢ℕ εε)))
        (zeroⱼ εε)
        (rflⱼ (zeroⱼ εε))

      lhs⇒*rhs : Γ′ ⊢ lhs ⇒* rhs ∷ B′ [ v′ , w₁′ ]₁₀
      lhs⇒*rhs = Jᵉ-subst ⊢B′ ⊢u′ w₁′⇒w₂′

      ¬lhs⇒*rhs : ¬ Γ′ ⊢ lhs ⇒* rhs ∷ C
      ¬lhs⇒*rhs (d ⇨ ⇒*rhs) = case inv-⇒-subst d of λ {
        (inj₂ (() , _));
        (inj₁ (_ , d , PE.refl)) → case inv-⇒-[]-cong d of λ {
        (inj₂ (() , _));
        (inj₁ (_ , d , PE.refl)) → case inv-⇒-J d of λ {
        (inj₂ (() , _));
        (inj₁ (_ , d , PE.refl)) → case inv-⇒-subst d of λ {
        (inj₁ (_ , d , _))       → whnfRedTerm d rflₙ;
        (inj₂ (_ , PE.refl , _)) → case ⇒*rhs of λ {
        (d ⇨ ⇒*rhs)              → case inv-⇒-subst d of λ {
        (inj₂ (() , _));
        (inj₁ (_ , d , PE.refl)) → case inv-⇒-[]-cong d of λ {
        (inj₂ (() , _));
        (inj₁ (_ , d , PE.refl)) → case inv-⇒-J d of λ {
        (inj₁ (_ , d , _))       → whnfRedTerm d rflₙ;
        (inj₂ (_ , PE.refl , _)) → case ⇒*rhs of λ {
        (d ⇨ ⇒*rhs)              → case inv-⇒-subst d of λ {
        (inj₂ (() , _));
        (inj₁ (_ , d , PE.refl)) → case inv-⇒-[]-cong d of λ {
        (inj₁ (_ , d , _))       → whnfRedTerm d rflₙ;
        (inj₂ (_ , PE.refl , _)) → case ⇒*rhs of λ {
        (d ⇨ ⇒*rhs)              → case inv-⇒-subst d of λ {
        (inj₁ (_ , d , _))       → whnfRedTerm d rflₙ;
        (inj₂ (_ , PE.refl , _)) → case ⇒*rhs of λ {
        (d ⇨ _)                  → whnfRedTerm d zeroₙ }}}}}}}}}}}}}}

  opaque

    -- Another reduction rule for Jᵉ is also not valid.

    ¬-Jᵉ-subst :
      ¬ (∀ {m n} {Γ : Cons m n}
           {A t : Term n} {B : Term (2+ n)} {u v w₁ w₂ : Term n} →
         Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
         Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
         Γ ⊢ w₁ ⇒ w₂ ∷ Id A t v →
         Γ ⊢ Jᵉ A t B u v w₁ ⇒ Jᵉ A t B u v w₂ ∷ B [ v , w₁ ]₁₀)
    ¬-Jᵉ-subst Jᵉ-subst =
      ¬-Jᵉ-subst-⇒* (λ ⊢B ⊢u w₁⇒w₂ → redMany (Jᵉ-subst ⊢B ⊢u w₁⇒w₂))
