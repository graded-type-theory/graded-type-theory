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
open import Definition.Typed.Properties.Admissible.Identity.Primitive R
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

import Definition.Untyped M as U
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Identity 𝕄
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sigma 𝕄
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
  n                                                    : Nat
  Γ                                                    : Cons _ _
  A A₁ A₂ B B₁ B₂ C t t′ t₁ t₂ u u₁ u₂ v v₁ v₂ w w₁ w₂ : Term _
  σ                                                    : Subst _ _
  s                                                    : Strength
  l                                                    : Universe-level
  p                                                    : M

------------------------------------------------------------------------
-- Lemmas about Erased, [_] and erased

-- Some lemmas that are proved under the assumption that Erased is
-- allowed.

module _ (Erased-ok : Erased-allowed s) where

  open Erased s

  private module P′ = P Erased-ok

  -- A formation rule for Erased.

  Erasedⱼ : Γ ⊢ A → Γ ⊢ Erased A
  Erasedⱼ = P′.Erasedⱼ

  -- A corresponding congruence rule.

  Erased-cong :
    Γ ⊢ A ≡ B →
    Γ ⊢ Erased A ≡ Erased B
  Erased-cong A≡B = P′.Erased-cong ⊢A A≡B
    where
    ⊢A = syntacticEq A≡B .proj₁

  -- An introduction rule for U.

  Erasedⱼ-U : Γ ⊢ A ∷ U l → Γ ⊢ Erased A ∷ U l
  Erasedⱼ-U = P′.Erasedⱼ-U

  -- A corresponding congruence rule.

  Erased-cong-U :
    Γ ⊢ A ≡ B ∷ U l →
    Γ ⊢ Erased A ≡ Erased B ∷ U l
  Erased-cong-U A≡B = P′.Erased-cong-U ⊢A A≡B
    where
    ⊢A = univ (syntacticEqTerm A≡B .proj₂ .proj₁)

  -- An introduction rule for Erased.

  []ⱼ : Γ ⊢ t ∷ A → Γ ⊢ [ t ] ∷ Erased A
  []ⱼ ⊢t = P′.[]ⱼ ⊢A ⊢t
    where
    ⊢A = syntacticTerm ⊢t

  -- A corresponding congruence rule.

  []-cong′ :
    Γ ⊢ t ≡ u ∷ A → Γ ⊢ [ t ] ≡ [ u ] ∷ Erased A
  []-cong′ t≡u = P′.[]-cong′ ⊢A t≡u
    where
    ⊢A = syntacticEqTerm t≡u .proj₁

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

    erasedⱼ : Γ ⊢ t ∷ Erased s A → Γ ⊢ erased s A t ∷ A
    erasedⱼ {s} = case PE.singleton s of λ where
      (𝕤 , PE.refl) → Eta.erasedⱼ
      (𝕨 , PE.refl) → NoEta.erasedⱼ

  opaque
    unfolding erased

    -- A corresponding congruence rule.

    erased-cong :
      Γ ⊢ A ≡ B → Γ ⊢ t ≡ u ∷ Erased s A →
      Γ ⊢ erased s A t ≡ erased s B u ∷ A
    erased-cong {s} A≡B = case PE.singleton s of λ where
      (𝕤 , PE.refl) → Eta.erased-cong
      (𝕨 , PE.refl) → NoEta.erased-cong A≡B

opaque

  -- An inversion lemma for Erased.

  inversion-Erased-∷ :
    let open Erased s in
    Γ ⊢ Erased A ∷ B →
    ∃₂ λ l₁ l₂ → l₁ ≤ᵘ l₂ ×
      Γ ⊢ A ∷ U l₁ × Erased-allowed s × Γ ⊢ B ≡ U l₂
  inversion-Erased-∷ ⊢Erased =
    case inversion-ΠΣ-U ⊢Erased of λ {
      (_ , _ , ⊢A , ⊢Unit , B≡ , Σˢ-ok) →
    _ , _ , ≤ᵘ⊔ᵘʳ , ⊢A , (inversion-Unit (univ ⊢Unit) , Σˢ-ok) , B≡ }

opaque

  -- Another inversion lemma for Erased.

  inversion-Erased :
    let open Erased s in
    Γ ⊢ Erased A → Γ ⊢ A × Erased-allowed s
  inversion-Erased ⊢Erased =
    case inversion-ΠΣ ⊢Erased of λ {
      (⊢A , ⊢Unit , Σˢ-ok) →
    ⊢A , inversion-Unit ⊢Unit , Σˢ-ok }

opaque

  -- An inversion lemma for [_].
  --
  -- TODO: Make it possible to replace the conclusion with
  --
  --   ∃ λ B → Γ ⊢ t ∷ B × Erased-allowed × Γ ⊢ A ≡ Erased B?
  --
  -- See also inversion-[]′, ¬-inversion-[]′ and ¬-inversion-[] in
  -- Definition.Typed.Consequences.Inversion.Erased.

  inversion-[] :
    let open Erased s in
    Γ ⊢ [ t ] ∷ A →
    ∃₃ λ B q C →
       Γ ⊢ t ∷ B ×
       (Unit-allowed s × Σ-allowed s 𝟘 q) ×
       Γ ⊢ A ≡ Σ⟨ s ⟩ 𝟘 , q ▷ B ▹ C ×
       Γ ⊢ C [ t ]₀ ≡ Unit s 0
  inversion-[] ⊢[] =
    case inversion-prod ⊢[] of λ {
      (B , C , q , ⊢B , _ , ⊢t , ⊢star , A≡ , Σˢ-ok) →
    case inversion-star ⊢star of λ {
      (≡Unit , Unit-ok) →
    B , q , C , ⊢t , (Unit-ok , Σˢ-ok) , A≡ , ≡Unit }}

------------------------------------------------------------------------
-- Lemmas about erasedrec

private opaque

  -- Some lemmas used below.

  erasedrec-lemma₁ :
    let open Erased s in
    Γ »∙ Erased A₁ ⊢ B₁ ≡ B₂ →
    Γ »∙ A₁ »∙ Unit s 0 »∙ Unit s 0 ⊢
      B₁ [ 3 ][ prod s 𝟘 (var x2) (var x0) ]↑ ≡
      B₂ [ 3 ][ prod s 𝟘 (var x2) (var x0) ]↑
  erasedrec-lemma₁ B₁≡B₂ =
    case wfEq B₁≡B₂ of λ {
      (∙ ⊢Erased-A) →
    case inversion-Erased ⊢Erased-A of λ
      (⊢A , Unit-ok , Σ-ok) →
    case Unitⱼ (∙ Unitⱼ (∙ ⊢A) Unit-ok) Unit-ok of λ
      ⊢Unit →
    case ⊢ˢʷ∷-wkSubst (∙ ⊢Unit) (⊢ˢʷ∷-idSubst (wf ⊢A)) of λ
      ⊢wk3 →
    [][]↑-cong B₁≡B₂ $ _⊢_≡_∷_.refl $
    prodⱼ
      (Unitⱼ (∙ subst-⊢ ⊢A ⊢wk3) Unit-ok)
      (PE.subst (_⊢_∷_ _ _) (wk[]≡[] 3) $ var₂ ⊢Unit)
      (var₀ ⊢Unit) Σ-ok }

  erasedrec-lemma₂ :
    let open Erased s in
    ∀ B →
    Unit-allowed s →
    Γ »∙ A ⊢ t₁ ≡ t₂ ∷ B [ [ var x0 ] ]↑ →
    Γ »∙ A »∙ Unit s 0 ⊢ wk1 t₁ ≡ wk1 t₂ ∷
      B [ 3 ][ prod s 𝟘 (var x2) (var x0) ]↑ [ star s 0 ]₀
  erasedrec-lemma₂ {s} B Unit-ok t₁≡t₂ =
    flip (PE.subst (_⊢_≡_∷_ _ _ _))
      (wkEqTerm₁ (Unitⱼ (wfEqTerm t₁≡t₂) Unit-ok) t₁≡t₂) $
    wk1 (B [ [ var x0 ] ]↑)                                     ≡⟨ wk[]′[][]↑ 1 B ⟩
    B [ 2 ][ wk1 [ var x0 ] ]↑                                  ≡⟨⟩
    B [ 2 ][ prod s 𝟘 (var x1) (star s 0) ]↑                    ≡˘⟨ [][]↑-[₀⇑] 0 B ⟩
    B [ 3 ][ prod s 𝟘 (var x2) (var x0) ]↑ [ star s 0 ]₀        ∎
    where
    open Erased s

opaque
  unfolding Erased.erasedrec

  -- An equality rule for erasedrec.

  erasedrec-cong :
    let open Erased s in
    Γ »∙ Erased A ⊢ B₁ ≡ B₂ →
    Γ »∙ A ⊢ t₁ ≡ t₂ ∷ B₁ [ [ var x0 ] ]↑ →
    Γ ⊢ u₁ ≡ u₂ ∷ Erased A →
    Γ ⊢ erasedrec p B₁ t₁ u₁ ≡ erasedrec p B₂ t₂ u₂ ∷ B₁ [ u₁ ]₀
  erasedrec-cong {B₁} B₁≡B₂ t₁≡t₂ u₁≡u₂ =
    case wf $ syntacticEq B₁≡B₂ .proj₁ of λ {
      (∙ ⊢Erased-A) →
    case inversion-Erased ⊢Erased-A of λ
      (_ , Unit-ok , _) →
    prodrec⟨⟩-cong B₁≡B₂ u₁≡u₂ $
    PE.subst (_⊢_≡_∷_ _ _ _) ([][]↑-[₀⇑] 0 B₁) $
    unitrec⟨⟩-cong (erasedrec-lemma₁ B₁≡B₂)
      (refl $ var₀ $
       Unitⱼ (wfTerm (syntacticEqTerm t₁≡t₂ .proj₂ .proj₁)) Unit-ok)
      (erasedrec-lemma₂ B₁ Unit-ok t₁≡t₂) }

opaque

  -- A typing rule for erasedrec.

  ⊢erasedrec :
    let open Erased s in
    Γ »∙ Erased A ⊢ B →
    Γ »∙ A ⊢ t ∷ B [ [ var x0 ] ]↑ →
    Γ ⊢ u ∷ Erased A →
    Γ ⊢ erasedrec p B t u ∷ B [ u ]₀
  ⊢erasedrec ⊢B ⊢t ⊢u =
    syntacticEqTerm
      (erasedrec-cong (refl ⊢B) (refl ⊢t) (refl ⊢u))
      .proj₂ .proj₁

opaque
  unfolding Erased.erasedrec

  -- Another equality rule for erasedrec.

  erasedrec-β :
    let open Erased s in
    Γ »∙ Erased A ⊢ B →
    Γ »∙ A ⊢ t ∷ B [ [ var x0 ] ]↑ →
    Γ ⊢ u ∷ A →
    Γ ⊢ erasedrec p B t [ u ] ≡ t [ u ]₀ ∷ B [ [ u ] ]₀
  erasedrec-β {s} {B} {t} {u} {p} ⊢B ⊢t ⊢u =
    case wf ⊢B of λ {
      (∙ ⊢Erased-A) →
    case inversion-Erased ⊢Erased-A of λ
      (⊢A , Unit-ok , Σ-ok) →
    let ⊢Γ = wf ⊢A in
    case Unitⱼ ⊢Γ Unit-ok of λ
      ⊢Unit →
    prodrec⟨ s ⟩ is-𝕨 𝟘 p B [ u ]
      (unitrec⟨ s ⟩ 0 𝟙 p (B [ 3 ][ prod s 𝟘 (var x2) (var x0) ]↑)
        (var x0) (wk1 t))                                             ≡⟨ prodrec⟨⟩-β (λ _ → ⊢B) ⊢u (starⱼ ⊢Γ Unit-ok)
                                                                           (PE.subst (_⊢_∷_ _ _) ([][]↑-[₀⇑] 0 B) $
                                                                            ⊢unitrec⟨⟩ (syntacticEq (erasedrec-lemma₁ (refl ⊢B)) .proj₁)
                                                                              (var₀ $ Unitⱼ (wfTerm ⊢t) Unit-ok)
                                                                              (syntacticEqTerm (erasedrec-lemma₂ B Unit-ok (refl ⊢t))
                                                                                 .proj₂ .proj₁))
                                                                           (λ _ → Σ-ok) ⟩⊢
    unitrec⟨ s ⟩ 0 𝟙 p (B [ 3 ][ prod s 𝟘 (var x2) (var x0) ]↑)
      (var x0) (wk1 t)
      [ u , star s 0 ]₁₀                                              ≡⟨ PE.trans unitrec⟨⟩-[] $
                                                                         PE.cong₃ (unitrec⟨_⟩ _ _ _ _)
                                                                           ([][]↑-[,⇑] 1 B) PE.refl (wk1-tail t) ⟩⊢≡
    unitrec⟨ s ⟩ 0 𝟙 p (B [ prod s 𝟘 (wk1 u) (var x0) ]↑) (star s 0)
      (t [ u ]₀)                                                      ≡⟨ (case PE.trans ([][]↑-[₀⇑] 0 B) $
                                                                               PE.cong (B U.[_]₀) $
                                                                               PE.cong₂ (prod _ _) (wk1-sgSubst _ _) PE.refl of λ
                                                                            lemma →
                                                                          PE.subst (_⊢_≡_∷_ _ _ _) lemma $
                                                                          unitrec⟨⟩-β-≡
                                                                            (λ _ →
                                                                               ⊢[][]↑ ⊢B $
                                                                               PE.subst (_⊢_∷_ _ _) (wk[]≡[] 1) $
                                                                               prodⱼ (Unitⱼ (∙ (wk₁ ⊢Unit ⊢A)) Unit-ok) (wkTerm₁ ⊢Unit ⊢u)
                                                                                 (var₀ ⊢Unit) Σ-ok)
                                                                            (PE.subst (_⊢_∷_ _ _) (PE.trans ([]↑-[]₀ B) (PE.sym lemma)) $
                                                                             substTerm ⊢t ⊢u)) ⟩⊢∎
    t [ u ]₀                                                          ∎ }
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
    Γ ⊢ t ∷ Erased A →
    Γ ⊢ Erased-η A t ∷ Id (Erased A) [ erased A t ] t
  ⊢Erased-η {s} {A} ⊢t =
    case syntacticTerm ⊢t of λ
      ⊢Erased-A →
    case inversion-Erased ⊢Erased-A of λ
      (⊢A , Erased-ok) →
    PE.subst (_⊢_∷_ _ _)
      (PE.cong₃ Id
         (PE.cong Erased $ wk1-sgSubst _ _)
         (PE.cong [_] $
          PE.trans erased-[] $
          PE.cong₂ erased (wk1-sgSubst _ _) PE.refl)
         PE.refl) $
    ⊢erasedrec
      (Idⱼ′ ([]ⱼ Erased-ok (erasedⱼ (var₀ ⊢Erased-A))) (var₀ ⊢Erased-A))
      (rflⱼ′ $
       []-cong′ Erased-ok
         (erased (wk1 A) (var x0) [ [ var x0 ] ]↑    ≡⟨ erased-[] ⟩⊢≡
          erased (wk1 A [ [ var x0 ] ]↑) [ var x0 ]  ≡⟨ Erased-β Erased-ok $
                                                        PE.subst (_⊢_∷_ _ _)
                                                          (PE.trans (wk≡subst _ _) $
                                                           PE.sym $ wk1-tail A) $
                                                        var₀ ⊢A ⟩⊢∎
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
    Γ ⊢ A₁ ≡ A₂ →
    Γ »∙ A₁ ⊢ t₁ ≡ t₂ ∷ wk1 B →
    Γ ⊢ u₁ ≡ u₂ ∷ Erased A₁ →
    Γ ⊢ mapᴱ A₁ t₁ u₁ ≡ mapᴱ A₂ t₂ u₂ ∷ Erased B
  mapᴱ-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ =
    case inversion-Erased $ syntacticEqTerm u₁≡u₂ .proj₁ of λ
      (_ , ok) →
    []-cong′ ok $
    PE.subst (_⊢_≡_∷_ _ _ _) (wk1-sgSubst _ _) $
    substTermEq t₁≡t₂ (erased-cong A₁≡A₂ u₁≡u₂)

opaque

  -- A typing rule for mapᴱ.

  ⊢mapᴱ :
    let open Erased s in
    Γ »∙ A ⊢ t ∷ wk1 B →
    Γ ⊢ u ∷ Erased A →
    Γ ⊢ mapᴱ A t u ∷ Erased B
  ⊢mapᴱ ⊢t ⊢u =
    syntacticEqTerm
      (mapᴱ-cong (refl (inversion-Erased (syntacticTerm ⊢u) .proj₁))
         (refl ⊢t) (refl ⊢u))
      .proj₂ .proj₁

opaque
  unfolding Erased.mapᴱ

  -- A β-rule for mapᴱ.

  mapᴱ-β :
    let open Erased s in
    Erased-allowed s →
    Γ »∙ A ⊢ t ∷ wk1 B →
    Γ ⊢ u ∷ A →
    Γ ⊢ mapᴱ A t [ u ] ≡ [ t [ u ]₀ ] ∷ Erased B
  mapᴱ-β ok ⊢t ⊢u =
    []-cong′ ok $
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
      Γ »∙ A ⊢ B →
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
      Γ »∙ A ⊢ B →
      Γ »∙ Erased A ⊢ B [ erased (wk1 A) (var x0) ]↑
    ⊢[erased-0]↑ ⊢B =
      case wf ⊢B of λ {
        (∙ ⊢A) →
      case Erasedⱼ Erased-ok ⊢A of λ
        ⊢Erased-A →
      subst-⊢ ⊢B $
      ⊢ˢʷ∷-[][]↑ (erasedⱼ $ var₀ ⊢Erased-A) }

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
    ⊢substᵉ {A} {B} {u} ⊢B ⊢v ⊢w =
      case inversion-Id (syntacticTerm ⊢v) of λ
        (⊢A , ⊢t , ⊢u) →
      case wf ⊢A of λ
        ⊢Γ →
      case Erasedⱼ Erased-ok ⊢A of λ
        ⊢Erased-A →
      conv
        (⊢subst (⊢[erased-0]↑ ⊢B) ([]-congⱼ′ ok ⊢v)
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
      case syntacticEqTerm t≡t′ of λ
        (_ , ⊢t , _) →
      case ⊢[erased-0]↑ ⊢B of λ
        ⊢B[]↑ →
      case []-cong′ Erased-ok t≡t′ of λ
        [t]≡[t′] →
      case [erased-0]↑[[]]₀≡[]₀ ⊢B ⊢t of λ
        ≡B[t]₀ →
      case conv ⊢u (sym ≡B[t]₀) of λ
        ⊢u →
      conv*
        (subst 𝟘 (Erased A) (B [ erased (wk1 A) (var x0) ]↑)
           [ t ] [ t′ ] ([]-cong s A t t′ rfl) u              ⇒⟨ conv (subst-subst ⊢B[]↑ ([]-cong-β-⇒ t≡t′ ok) ⊢u) $
                                                                 substTypeEq (refl ⊢B[]↑) (sym′ [t]≡[t′]) ⟩
         subst 𝟘 (Erased A) (B [ erased (wk1 A) (var x0) ]↑)
           [ t ] [ t′ ] rfl u                                 ⇒⟨ subst-⇒′ ⊢B[]↑ [t]≡[t′] ⊢u ⟩∎

         u                                                    ∎)
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
      case syntacticEq B₁≡B₂ of λ
        (⊢B₁ , _) →
      case syntacticEqTerm t₁≡t₂ of λ
        (⊢A₁ , ⊢t₁ , _) →
      case syntacticEqTerm u₁≡u₂ of λ
        (_ , ⊢u₁ , _) →
      case Erasedⱼ Erased-ok ⊢A₁ of λ
        ⊢Erased-A₁ →
      conv
        (subst-cong (Erased-cong Erased-ok A₁≡A₂)
           (subst-⊢≡ B₁≡B₂ $ ⊢ˢʷ≡∷-[][]↑ $
            erased-cong (wkEq₁ ⊢Erased-A₁ A₁≡A₂)
              (refl $ var₀ ⊢Erased-A₁))
           ([]-cong′ Erased-ok t₁≡t₂)
           ([]-cong′ Erased-ok u₁≡u₂)
           ([]-cong-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok)
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
      case inversion-Id (syntacticEqTerm (subsetTerm v₁⇒v₂) .proj₁) of λ
        (_ , ⊢t , ⊢u) →
      conv
        (subst-subst (⊢[erased-0]↑ ⊢B) ([]-cong-subst′ v₁⇒v₂ ok)
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
      Γ »∙ A₁ »∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢
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
      Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢
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
      Γ »∙ A₁ »∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ ≡ B₂ →
      Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
      Γ »∙ Singleton A₁ t₁ ⊢
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
      Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
      Γ ⊢ t ∷ A →
      Γ »∙ Singleton A t ⊢
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
      Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
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
      Γ ⊢ A₁ ≡ A₂ →
      Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
      Γ »∙ A₁ »∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ ≡ B₂ →
      Γ ⊢ u₁ ≡ u₂ ∷ B₁ [ t₁ , rfl ]₁₀ →
      Γ ⊢ v₁ ≡ v₂ ∷ A₁ →
      Γ ⊢ w₁ ≡ w₂ ∷ Id A₁ t₁ v₁ →
      Γ ⊢ Jᵉ A₁ t₁ B₁ u₁ v₁ w₁ ≡ Jᵉ A₂ t₂ B₂ u₂ v₂ w₂ ∷ B₁ [ v₁ , w₁ ]₁₀
    Jᵉ-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂ =
      case syntacticEq B₁≡B₂ of λ
        (⊢B₁  , _) →
      case syntacticEqTerm t₁≡t₂ of λ
        (⊢A₁ , ⊢t₁  , _) →
      case syntacticEqTerm w₁≡w₂ of λ
        (_ , ⊢w₁  , _) →
      conv
        (substᵉ-cong
           (ΠΣ-cong A₁≡A₂
              (Id-cong (wkEq₁ ⊢A₁ A₁≡A₂) (wkEqTerm₁ ⊢A₁ t₁≡t₂)
                 (refl (var₀ ⊢A₁)))
              Σ-ok)
           (lemma₈ A₁≡A₂ B₁≡B₂ t₁≡t₂)
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
            J-cong′ A₁≡A₂ t₁≡t₂ (lemma₆ A₁≡A₂ t₁≡t₂) (refl (lemma₇ ⊢t₁))
              v₁≡v₂ w₁≡w₂)
           (conv u₁≡u₂ $ sym $ lemma₉ ⊢B₁ (rflⱼ ⊢t₁)))
        (lemma₉ ⊢B₁ ⊢w₁)

  opaque

    -- A typing rule for Jᵉ.

    ⊢Jᵉ :
      Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
      Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
      Γ ⊢ w ∷ Id A t v →
      Γ ⊢ Jᵉ A t B u v w ∷ B [ v , w ]₁₀
    ⊢Jᵉ ⊢B ⊢u ⊢w =
      case inversion-Id (syntacticTerm ⊢w) of λ
        (⊢A , ⊢t , ⊢v) →
      syntacticEqTerm
        (Jᵉ-cong (refl ⊢A) (refl ⊢t) (refl ⊢B) (refl ⊢u) (refl ⊢v)
           (refl ⊢w))
        .proj₂ .proj₁

  opaque
    unfolding Jᵉ

    -- A reduction rule for Jᵉ.

    Jᵉ-⇒*′ :
      Γ ⊢ t ≡ t′ ∷ A →
      Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
      Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
      Γ ⊢ Jᵉ A t B u t′ rfl ⇒* u ∷ B [ t , rfl ]₁₀
    Jᵉ-⇒*′ {t} {t′} {A} {B} {u} t≡t′ ⊢B ⊢u =
      case syntacticEqTerm t≡t′ of λ
        (⊢A , ⊢t , _) →
      case PE.subst (_⊢_∷_ _ _)
             (PE.sym $ PE.cong₃ Id
                (wk1-sgSubst _ _)
                (wk1-sgSubst _ _)
                PE.refl) $
           rflⱼ ⊢t of λ
        ⊢rfl →
      case prod-cong (J-motive-context-type ⊢t) t≡t′ (refl ⊢rfl)
             Σ-ok of λ
        t,rfl≡t′,rfl →
      case ΠΣⱼ (Idⱼ′ (wkTerm₁ ⊢A ⊢t) (var₀ ⊢A)) Σ-ok of λ
        ⊢Singleton →

      substᵉ
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
                                                                           (substᵉ-subst (lemma₈′ ⊢B ⊢t)
                                                                              (conv
                                                                                 (PE.subst (_⊢_⇒_∷_ _ _ _)
                                                                                    (PE.cong₃ Id wk₂-[,] wk₂-[,] PE.refl) $
                                                                                  J-β-⇒ t≡t′ (lemma₆′ ⊢t) (lemma₇ ⊢t))
                                                                                  (Id-cong (refl ⊢Singleton)
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
                                                                         Id-cong (refl ⊢A) (refl ⊢t) t≡t′ ⟩
      substᵉ
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
                                                                            (substᵉ-⇒*′ (lemma₈′ ⊢B ⊢t) t,rfl≡t′,rfl
                                                                               (conv ⊢u $ sym $ lemma₉ ⊢B (rflⱼ ⊢t)))
                                                                            (lemma₉ ⊢B (rflⱼ ⊢t)) ⟩∎

      u                                                               ∎

  opaque

    -- Another reduction rule for Jᵉ.

    Jᵉ-⇒* :
      Γ ⊢ t ∷ A →
      Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
      Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
      Γ ⊢ Jᵉ A t B u t rfl ⇒* u ∷ B [ t , rfl ]₁₀
    Jᵉ-⇒* ⊢t = Jᵉ-⇒*′ (refl ⊢t)

  opaque

    -- An equality rule for Jᵉ.

    Jᵉ-≡ :
      Γ ⊢ t ∷ A →
      Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
      Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
      Γ ⊢ Jᵉ A t B u t rfl ≡ u ∷ B [ t , rfl ]₁₀
    Jᵉ-≡ ⊢t ⊢B ⊢u = subset*Term (Jᵉ-⇒* ⊢t ⊢B ⊢u)

------------------------------------------------------------------------
-- More lemmas related to Jᵉ

module _ {s : Strength} where

  open Erased s

  opaque
    unfolding Jᵉ substᵉ subst

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
      ⊢B′ = ℕⱼ (∙ Idⱼ′ (zeroⱼ (∙ ℕⱼ εε)) (var₀ (ℕⱼ εε)))

      ⊢u′ : Γ′ ⊢ u′ ∷ B′ [ t″ , rfl ]₁₀
      ⊢u′ = zeroⱼ εε

      w₁′⇒w₂′ : Γ′ ⊢ w₁′ ⇒ w₂′ ∷ Id A′ t″ v′
      w₁′⇒w₂′ = subst-⇒
        (Idⱼ′ (zeroⱼ (∙ ℕⱼ εε)) (zeroⱼ (∙ ℕⱼ εε)))
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
