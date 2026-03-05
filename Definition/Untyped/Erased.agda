------------------------------------------------------------------------
-- The type constructor Erased
------------------------------------------------------------------------

open import Graded.Modality
open import Definition.Untyped.NotParametrised using (Strength)

module Definition.Untyped.Erased
  {a} {M : Set a}
  (𝕄 : Modality M)
  (s : Strength)
  where

open Modality 𝕄

import Definition.Typed.Decidable.Internal.Term
import Definition.Typed.Decidable.Internal.Substitution.Primitive
import Definition.Typed.Decidable.Internal.Weakening
open import Definition.Typed.Restrictions

open import Definition.Untyped M as U hiding (_[_])
import Definition.Untyped.Erased.Eta 𝕄 as Eta
open import Definition.Untyped.Identity 𝕄 hiding (module Internal)
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sigma 𝕄 as US hiding (module Internal)
open import Definition.Untyped.Unit 𝕄 as UU hiding (module Internal)

import Definition.Untyped.Erased.No-eta 𝕄 as NoEta

open import Graded.Mode

open import Tools.Fin
open import Tools.Function
open import Tools.Maybe
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE hiding (subst; cong)
open import Tools.Reasoning.PropositionalEquality

private variable
  n           : Nat
  ξ           : DExt _ _ _
  A B t u v w : Term _
  l           : Lvl _
  σ           : Subst _ _
  ρ           : Wk _ _
  p           : M

opaque

  -- The type constructor Erased.

  Erased : Lvl n → Term n → Term n
  Erased l A = Σ⟨ s ⟩ 𝟘 , 𝟘 ▷ A ▹ Lift (wk1 l) (Unit s)

opaque
  unfolding Erased

  -- A substitution lemma for Erased.

  Erased-[] : Erased l A U.[ σ ] ≡ Erased (l U.[ σ ]) (A U.[ σ ])
  Erased-[] {l} {A} {σ} =
    Σ⟨ s ⟩ 𝟘 , 𝟘 ▷ A U.[ σ ] ▹ Lift (wk1 l U.[ σ ⇑ ]) (Unit s)  ≡⟨ PE.cong (Σ⟨ s ⟩_,_▷_▹_ _ _ _) (PE.cong (flip Lift _) (wk1-liftSubst l)) ⟩
    Σ⟨ s ⟩ 𝟘 , 𝟘 ▷ A U.[ σ ] ▹ Lift (wk1 (l U.[ σ ])) (Unit s)  ∎

opaque

  -- A weakening lemma for Erased.

  wk-Erased : wk ρ (Erased l A) ≡ Erased (wk ρ l) (wk ρ A)
  wk-Erased {ρ} {l} {A} =
    wk ρ (Erased l A)                               ≡⟨ wk≡subst _ _ ⟩
    Erased l A U.[ toSubst ρ ]                      ≡⟨ Erased-[] ⟩
    Erased (l U.[ toSubst ρ ]) (A U.[ toSubst ρ ])  ≡˘⟨ PE.cong₂ Erased (wk≡subst _ _) (wk≡subst _ _) ⟩
    Erased (wk ρ l) (wk ρ A)                        ∎

opaque
  unfolding inline Erased

  -- Inlining commutes with Erased.

  inline-Erased :
    inline ξ (Erased l A) ≡ Erased (inline ξ l) (inline ξ A)
  inline-Erased {l} =
    PE.cong (Σ⟨ s ⟩ 𝟘 , 𝟘 ▷_▹_ _) $
    PE.cong (flip Lift _) $
    PE.sym $ wk-inline l

opaque

  -- The constructor [_].

  [_] : Term n → Term n
  [ t ] = prod s 𝟘 t (lift (star s))

opaque
  unfolding [_]

  -- A substitution lemma for [_].

  []-[] : [ t ] U.[ σ ] ≡ [ t U.[ σ ] ]
  []-[] = refl

opaque

  -- A weakening lemma for [_].

  wk-[] : wk ρ [ t ] ≡ [ wk ρ t ]
  wk-[] {ρ} {t} =
    wk ρ [ t ]             ≡⟨ wk≡subst _ _ ⟩
    [ t ] U.[ toSubst ρ ]  ≡⟨ []-[] ⟩
    [ t U.[ toSubst ρ ] ]  ≡˘⟨ PE.cong [_] $ wk≡subst _ _ ⟩
    [ wk ρ t ]             ∎

opaque
  unfolding inline [_]

  -- Inlining commutes with [_].

  inline-[]′ :
    inline ξ [ t ] ≡ [ inline ξ t ]
  inline-[]′ = refl

opaque

  -- A substitution lemma for Id, Erased and [_].

  Id-Erased-[] :
    Id (Erased (l U.[ σ ]) (A U.[ σ ])) [ t U.[ σ ] ] [ u U.[ σ ] ] ≡
    Id (Erased l A) [ t ] [ u ] U.[ σ ]
  Id-Erased-[] = sym $ cong₃ Id Erased-[] []-[] []-[]

opaque

  -- A weakening lemma for Id, Erased and [_].

  wk-Id-Erased :
    Id (Erased (wk ρ l) (wk ρ A)) [ wk ρ t ] [ wk ρ u ] ≡
    wk ρ (Id (Erased l A) [ t ] [ u ])
  wk-Id-Erased = sym $ cong₃ Id wk-Erased wk-[] wk-[]

opaque

  -- A combination of Id-Erased-[] and wk-Id-Erased.

  wk-Id-Erased-[]-[] :
    Id (Erased (wk ρ l U.[ σ ]) (wk ρ A U.[ σ ])) [ wk ρ t U.[ σ ] ]
       [ wk ρ u U.[ σ ] ] ≡
    wk ρ (Id (Erased l A) [ t ] [ u ]) U.[ σ ]
  wk-Id-Erased-[]-[] {ρ} {l} {σ} {A} {t} {u} =
    Id (Erased (wk ρ l U.[ σ ]) (wk ρ A U.[ σ ])) [ wk ρ t U.[ σ ] ]
       [ wk ρ u U.[ σ ] ]                                             ≡⟨ Id-Erased-[] ⟩

    Id (Erased (wk ρ l) (wk ρ A)) [ wk ρ t ] [ wk ρ u ] U.[ σ ]       ≡⟨ PE.cong U._[ σ ] wk-Id-Erased ⟩

    wk ρ (Id (Erased l A) [ t ] [ u ]) U.[ σ ]                        ∎

opaque
  unfolding inline

  -- An inlining lemma for Id, Erased and [_].

  inline-Id-Erased :
    Id (Erased (inline ξ l) (inline ξ A)) [ inline ξ t ]
      [ inline ξ u ] ≡
    inline ξ (Id (Erased l A) [ t ] [ u ])
  inline-Id-Erased {ξ} {l} {A} {t} {u} =
    Id (Erased (inline ξ l) (inline ξ A)) [ inline ξ t ] [ inline ξ u ]  ≡˘⟨ cong₃ Id inline-Erased inline-[]′ inline-[]′ ⟩
    Id (inline ξ (Erased l A)) (inline ξ [ t ]) (inline ξ [ u ])         ≡⟨⟩
    inline ξ (Id (Erased l A) [ t ] [ u ])                               ∎

opaque
  unfolding Eta.erased NoEta.erased

  -- The "projection" erased.

  erased : Term n → Term n → Term n
  erased A t = case s of λ where
    𝕤 → Eta.erased t
    𝕨 → NoEta.erased A t

opaque
  unfolding erased

  -- A substitution lemma for erased.

  erased-[] : erased A t U.[ σ ] ≡ erased (A U.[ σ ]) (t U.[ σ ])
  erased-[] {t} = case singleton s of λ where
    (𝕤 , refl) → Eta.erased-[] {t = t}
    (𝕨 , refl) → NoEta.erased-[]

opaque

  -- A weakening lemma for erased.

  wk-erased : wk ρ (erased A t) ≡ erased (wk ρ A) (wk ρ t)
  wk-erased {ρ} {A} {t} =
    wk ρ (erased A t)                               ≡⟨ wk≡subst _ _ ⟩
    erased A t U.[ toSubst ρ ]                      ≡⟨ erased-[] ⟩
    erased (A U.[ toSubst ρ ]) (t U.[ toSubst ρ ])  ≡˘⟨ PE.cong₂ erased (wk≡subst _ _) (wk≡subst _ _) ⟩
    erased (wk ρ A) (wk ρ t)                        ∎

opaque

  -- A grade that is used in the implementation of erasedrec.

  is-𝕨 : M
  is-𝕨 = case PE.singleton s of λ where
    (𝕨 , _) → 𝟙
    (𝕤 , _) → 𝟘

opaque

  -- An eliminator for Erased.

  erasedrec : M → Term (1+ n) → Term (1+ n) → Term n → Term n
  erasedrec p B t u =
    prodrec⟨ s ⟩ is-𝕨 𝟘 p B u
      (unitrec⟨ s ⟩ 𝟙 p (B [ 3 ][ prod s 𝟘 (var x2) (lift (var x0)) ]↑)
         (lower (var x0)) (wk1 t))

opaque
  unfolding erasedrec

  -- A substitution lemma for erasedrec.

  erasedrec-[] :
    erasedrec p B t u U.[ σ ] ≡
    erasedrec p (B U.[ liftSubst σ ]) (t U.[ liftSubst σ ]) (u U.[ σ ])
  erasedrec-[] {p} {B} {t} {u} {σ} =
    prodrec⟨ s ⟩ is-𝕨 𝟘 p B u
      (unitrec⟨ s ⟩ 𝟙 p (B [ 3 ][ prod s 𝟘 (var x2) (lift (var x0)) ]↑)
         (lower (var x0)) (wk1 t))
      U.[ σ ]                                                               ≡⟨ prodrec⟨⟩-[] ⟩

    prodrec⟨ s ⟩ is-𝕨 𝟘 p (B U.[ liftSubst σ ]) (u U.[ σ ])
      (unitrec⟨ s ⟩ 𝟙 p (B [ 3 ][ prod s 𝟘 (var x2) (lift (var x0)) ]↑)
         (lower (var x0)) (wk1 t)
         U.[ liftSubstn σ 2 ])                                              ≡⟨ PE.cong (prodrec⟨_⟩ _ _ _ _ _ _)
                                                                               unitrec⟨⟩-[] ⟩
    prodrec⟨ s ⟩ is-𝕨 𝟘 p (B U.[ liftSubst σ ]) (u U.[ σ ])
      (unitrec⟨ s ⟩ 𝟙 p
         (B [ 3 ][ prod s 𝟘 (var x2) (lift (var x0)) ]↑
            U.[ liftSubstn σ 3 ])
         (lower (var x0)) (wk1 t U.[ liftSubstn σ 2 ]))                     ≡⟨ PE.cong (prodrec⟨_⟩ _ _ _ _ _ _) $
                                                                               PE.cong₃ (unitrec⟨_⟩ _ _ _)
                                                                                 (PE.trans (substCompEq B) $
                                                                                  PE.trans (flip substVar-to-subst B λ
                                                                                              { x0     → PE.refl
                                                                                              ; (_ +1) → PE.sym $ wk1-[][]↑ 3
                                                                                              }) $
                                                                                  PE.sym $ substCompEq B)
                                                                                 PE.refl
                                                                                 (wk1-liftSubst t) ⟩
    prodrec⟨ s ⟩ is-𝕨 𝟘 p (B U.[ liftSubst σ ]) (u U.[ σ ])
      (unitrec⟨ s ⟩ 𝟙 p
         (B U.[ liftSubst σ ] [ 3 ][ prod s 𝟘 (var x2) (lift (var x0)) ]↑)
         (lower (var x0)) (wk1 (t U.[ liftSubst σ ])))                      ∎

opaque

  -- A propositional η-rule for Erased.

  Erased-η : Lvl n → Term n → Term n → Term n
  Erased-η l A t =
    erasedrec 𝟙
      (Id (Erased (wk1 l) (wk1 A)) [ erased (wk1 A) (var x0) ] (var x0))
      rfl t

opaque
  unfolding Erased-η

  -- A substitution lemma for Erased-η.

  Erased-η-[] :
    Erased-η l A u U.[ σ ] ≡
    Erased-η (l U.[ σ ]) (A U.[ σ ]) (u U.[ σ ])
  Erased-η-[] {l} {A} {u} {σ} =
    erasedrec 𝟙
      (Id (Erased (wk1 l) (wk1 A)) [ erased (wk1 A) (var x0) ] (var x0))
      rfl u U.[ σ ]                                                       ≡⟨ erasedrec-[] ⟩

    erasedrec 𝟙
      (Id (Erased (wk1 l) (wk1 A) U.[ σ ⇑ ])
         ([ erased (wk1 A) (var x0) ] U.[ σ ⇑ ]) (var x0))
      rfl (u U.[ σ ])                                                     ≡⟨ cong₃ (erasedrec _) (cong₃ Id Erased-[] []-[] refl) refl refl ⟩

    erasedrec 𝟙
      (Id (Erased (wk1 l U.[ σ ⇑ ]) (wk1 A U.[ σ ⇑ ]))
         [ erased (wk1 A) (var x0) U.[ σ ⇑ ] ] (var x0))
      rfl (u U.[ σ ])                                                     ≡⟨ cong₃ (erasedrec _)
                                                                               (cong₃ Id refl (PE.cong [_] erased-[]) refl)
                                                                               refl
                                                                               refl ⟩
    erasedrec 𝟙
      (Id (Erased (wk1 l U.[ σ ⇑ ]) (wk1 A U.[ σ ⇑ ]))
         [ erased (wk1 A U.[ σ ⇑ ]) (var x0) ] (var x0))
      rfl (u U.[ σ ])                                                     ≡⟨ PE.cong₂ (λ l A → erasedrec _ (Id (Erased l A) [ erased A _ ] _) _ _)
                                                                               (wk1-liftSubst l)
                                                                               (wk1-liftSubst A) ⟩
    erasedrec 𝟙
      (Id (Erased (wk1 (l U.[ σ ])) (wk1 (A U.[ σ ])))
         [ erased (wk1 (A U.[ σ ])) (var x0) ] (var x0))
      rfl (u U.[ σ ])                                                     ∎

opaque

  -- A map function for Erased.

  mapᴱ : Term n → Term (1+ n) → Term n → Term n
  mapᴱ A t u = [ t [ erased A u ]₀ ]

opaque
  unfolding mapᴱ

  -- A substitution lemma for mapᴱ.

  mapᴱ-[] :
    mapᴱ A t u U.[ σ ] ≡
    mapᴱ (A U.[ σ ]) (t U.[ σ ⇑ ]) (u U.[ σ ])
  mapᴱ-[] {A} {t} {u} {σ} =
    [ t U.[ erased A u ]₀ ] U.[ σ ]                        ≡⟨ []-[] ⟩
    [ t U.[ erased A u ]₀ U.[ σ ] ]                        ≡⟨ PE.cong ([_]) $ singleSubstLift t _ ⟩
    [ t U.[ σ ⇑ ] U.[ erased A u U.[ σ ] ]₀ ]              ≡⟨ PE.cong ([_] ∘→ t U.[ σ ⇑ ] U.[_]₀) erased-[] ⟩
    [ t U.[ σ ⇑ ] U.[ erased (A U.[ σ ]) (u U.[ σ ]) ]₀ ]  ∎

opaque

  -- A weakening lemma for mapᴱ.

  wk-mapᴱ :
    wk ρ (mapᴱ A t u) ≡
    mapᴱ (wk ρ A) (wk (lift ρ) t) (wk ρ u)
  wk-mapᴱ {ρ} {A} {t} {u} =
    wk ρ (mapᴱ A t u)                                                   ≡⟨ wk≡subst _ _ ⟩
    mapᴱ A t u U.[ toSubst ρ ]                                          ≡⟨ mapᴱ-[] ⟩
    mapᴱ (A U.[ toSubst ρ ]) (t U.[ toSubst ρ ⇑ ]) (u U.[ toSubst ρ ])  ≡˘⟨ cong₃ mapᴱ (wk≡subst _ _) (wk-liftn 1) (wk≡subst _ _) ⟩
    mapᴱ (wk ρ A) (wk (lift ρ) t) (wk ρ u)                              ∎

opaque

  -- Substitutivity.
  --
  -- This variant of subst is an alternative to subst 𝟘.

  substᵉ :
    Term n → Term (1+ n) → Term n → Term n → Term n → Term n → Term n
  substᵉ A B t u v w =
    subst 𝟘 (Erased zeroᵘₗ A) (B [ erased (wk1 A) (var x0) ]↑) [ t ]
      [ u ] ([]-cong s zeroᵘₗ A t u v) w

opaque
  unfolding substᵉ

  -- A substitution lemma for substᵉ.

  substᵉ-[] :
    substᵉ A B t u v w U.[ σ ] ≡
    substᵉ (A U.[ σ ]) (B U.[ liftSubst σ ]) (t U.[ σ ])
      (u U.[ σ ]) (v U.[ σ ]) (w U.[ σ ])
  substᵉ-[] {A} {B} {t} {u} {v} {w} {σ} =
    subst 𝟘 (Erased zeroᵘₗ A) (B [ erased (wk1 A) (var x0) ]↑) [ t ]
      [ u ] ([]-cong s zeroᵘₗ A t u v) w U.[ σ ]                          ≡⟨ subst-[] ⟩

    subst 𝟘 (Erased zeroᵘₗ A U.[ σ ])
      (B [ erased (wk1 A) (var x0) ]↑ U.[ σ ⇑ ]) ([ t ] U.[ σ ])
      ([ u ] U.[ σ ]) ([]-cong s zeroᵘₗ A t u v U.[ σ ]) (w U.[ σ ])      ≡⟨ cong₆ (subst _) Erased-[] lemma []-[] []-[] refl refl ⟩

    subst 𝟘 (Erased zeroᵘₗ (A U.[ σ ]))
      (B U.[ σ ⇑ ] [ erased (wk1 (A U.[ σ ])) (var x0) ]↑) [ t U.[ σ ] ]
      [ u U.[ σ ] ]
      ([]-cong s zeroᵘₗ (A U.[ σ ]) (t U.[ σ ]) (u U.[ σ ]) (v U.[ σ ]))
      (w U.[ σ ])                                                         ∎
    where
    lemma :
      B [ erased (wk1 A) (var x0) ]↑ U.[ liftSubst σ ] ≡
      B U.[ liftSubst σ ] [ erased (wk1 (A U.[ σ ])) (var x0) ]↑
    lemma =
      B [ erased (wk1 A) (var x0) ]↑ U.[ liftSubst σ ]            ≡⟨ singleSubstLift↑ _ B _ ⟩
      B U.[ liftSubst σ ] [ erased (wk1 A) (var x0) U.[ σ ⇑ ] ]↑  ≡⟨ PE.cong (B U.[ _ ] [_]↑) erased-[] ⟩
      B U.[ liftSubst σ ] [ erased (wk1 A U.[ σ ⇑ ]) (var x0) ]↑  ≡⟨ PE.cong (λ A → B U.[ _ ] [ erased A _ ]↑) (wk1-liftSubst A) ⟩
      B U.[ liftSubst σ ] [ erased (wk1 (A U.[ σ ])) (var x0) ]↑  ∎

opaque

  -- An alternative to J 𝟘 𝟘.

  Jᵉ : Term n → Term n → Term (2+ n) → Term n → Term n → Term n → Term n
  Jᵉ {n} A t B u v w =
    substᵉ Singleton
      (B U.[ consSubst
               (consSubst (wk1Subst idSubst)
                  (fst⟨ s ⟩ 𝟘 (wk1 A) (var x0)))
               (snd⟨ s ⟩ 𝟘 𝟘 (wk1 A) (Id (wk₂ A) (wk₂ t) (var x0))
                  (var x0)) ])
      (prod s 𝟘 t rfl)
      (prod s 𝟘 v w)
      (J 𝟘 (𝟘 ∧ 𝟙) A t
         (Id (wk₂ Singleton) (wk₂ (prod s 𝟘 t rfl))
            (prod s 𝟘 (var x1) (var x0)))
         rfl v w)
      u
    where
    Singleton : Term n
    Singleton = Σ⟨ s ⟩ 𝟘 , 𝟘 ▷ A ▹ Id (wk1 A) (wk1 t) (var x0)

opaque
  unfolding Jᵉ

  -- A substitution lemma for Jᵉ.

  Jᵉ-[] :
    Jᵉ A t B u v w U.[ σ ] ≡
    Jᵉ (A U.[ σ ]) (t U.[ σ ]) (B U.[ σ ⇑[ 2 ] ]) (u U.[ σ ])
      (v U.[ σ ]) (w U.[ σ ])
  Jᵉ-[] {A} {t} {B} {u} {v} {w} {σ} =
    case
      PE.cong (Σ⟨_⟩_,_▷_▹_ s 𝟘 𝟘 (A U.[ σ ]))
        {x = Id (wk1 A) (wk1 t) (var x0) U.[ _ ]} $
      cong₃ Id
        (wk1-liftSubst A)
        (wk1-liftSubst t)
        refl
    of λ
      lemma →
    substᵉ
      (Σ⟨ s ⟩ 𝟘 , 𝟘 ▷ A ▹ Id (wk1 A) (wk1 t) (var x0))
      (B U.[ consSubst
               (consSubst (wk1Subst idSubst)
                  (fst⟨ s ⟩ 𝟘 (wk1 A) (var x0)))
               (snd⟨ s ⟩ 𝟘 𝟘 (wk1 A) (Id (wk₂ A) (wk₂ t) (var x0))
                  (var x0)) ])
      (prod s 𝟘 t rfl)
      (prod s 𝟘 v w)
      (J 𝟘 (𝟘 ∧ 𝟙) A t
         (Id (wk₂ $ Σ⟨ s ⟩ 𝟘 , 𝟘 ▷ A ▹ Id (wk1 A) (wk1 t) (var x0))
            (wk₂ (prod s 𝟘 t rfl)) (prod s 𝟘 (var x1) (var x0)))
         rfl v w)
      u U.[ σ ]                                                          ≡⟨ substᵉ-[] ⟩

    substᵉ
      (Σ⟨ s ⟩ 𝟘 , 𝟘 ▷ A U.[ σ ] ▹
       Id (wk1 A U.[ liftSubst σ ]) (wk1 t U.[ liftSubst σ ]) (var x0))
      (B U.[ consSubst
               (consSubst (wk1Subst idSubst)
                  (fst⟨ s ⟩ 𝟘 (wk1 A) (var x0)))
               (snd⟨ s ⟩ 𝟘 𝟘 (wk1 A) (Id (wk₂ A) (wk₂ t) (var x0))
                  (var x0)) ]
         U.[ liftSubst σ ])
      (prod s 𝟘 (t U.[ σ ]) rfl)
      (prod s 𝟘 (v U.[ σ ]) (w U.[ σ ]))
      (J 𝟘 (𝟘 ∧ 𝟙) (A U.[ σ ]) (t U.[ σ ])
         (Id
            (wk₂ (Σ⟨ s ⟩ 𝟘 , 𝟘 ▷ A ▹ Id (wk1 A) (wk1 t) (var x0))
               U.[ liftSubstn σ 2 ])
            (wk₂ (prod s 𝟘 t rfl) U.[ liftSubstn σ 2 ])
            (prod s 𝟘 (var x1) (var x0)))
         rfl (v U.[ σ ]) (w U.[ σ ]))
      (u U.[ σ ])                                                         ≡⟨ cong₆ substᵉ lemma
                                                                               (
      B U.[ consSubst
              (consSubst (wk1Subst idSubst)
                 (fst⟨ s ⟩ 𝟘 (wk1 A) (var x0)))
              (snd⟨ s ⟩ 𝟘 𝟘 (wk1 A) (Id (wk₂ A) (wk₂ t) (var x0))
                 (var x0)) ]
        U.[ liftSubst σ ]                                                       ≡⟨ substCompEq B ⟩

      B U.[ liftSubst σ ₛ•ₛ
            consSubst
              (consSubst (wk1Subst idSubst)
                 (fst⟨ s ⟩ 𝟘 (wk1 A) (var x0)))
              (snd⟨ s ⟩ 𝟘 𝟘 (wk1 A) (Id (wk₂ A) (wk₂ t) (var x0))
                 (var x0)) ]                                                    ≡⟨ (flip substVar-to-subst B λ {
                                                                                      x0 →
        snd⟨ s ⟩ 𝟘 𝟘 (wk1 A) (Id (wk₂ A) (wk₂ t) (var x0)) (var x0)
          U.[ liftSubst σ ]                                                             ≡⟨ snd⟨⟩-[] ⟩

        snd⟨ s ⟩ 𝟘 𝟘 (wk1 A U.[ liftSubst σ ])
          (Id (wk₂ A U.[ liftSubstn σ 2 ]) (wk₂ t U.[ liftSubstn σ 2 ])
             (var x0))
          (var x0)                                                                      ≡⟨ cong₃ (snd⟨ _ ⟩ _ _)
                                                                                             (wk1-liftSubst A)
                                                                                             (cong₃ Id (wk[]′-[⇑] A) (wk[]′-[⇑] t) refl)
                                                                                             refl ⟩
        snd⟨ s ⟩ 𝟘 𝟘 (wk1 (A U.[ σ ]))
          (Id (wk₂ (A U.[ σ ])) (wk₂ (t U.[ σ ])) (var x0)) (var x0)                    ∎;
                                                                                      (x0 +1) →
        fst⟨ s ⟩ 𝟘 (wk1 A) (var x0) U.[ liftSubst σ ]                                   ≡⟨ fst⟨⟩-[] ⟩
        fst⟨ s ⟩ 𝟘 (wk1 A U.[ liftSubst σ ]) (var x0)                                   ≡⟨ PE.cong₂ (fst⟨ _ ⟩ _) (wk1-liftSubst A) refl ⟩
        fst⟨ s ⟩ 𝟘 (wk1 (A U.[ σ ])) (var x0)                                           ∎;
                                                                                      (x +1 +1) →
        wk1 (σ x)                                                                       ≡⟨ wk1-tailId _ ⟩
        σ x U.[ wk1Subst idSubst ]                                                      ∎ }) ⟩

      B U.[ consSubst
              (consSubst (wk1Subst idSubst ₛ•ₛ σ)
                 (fst⟨ s ⟩ 𝟘 (wk1 (A U.[ σ ])) (var x0)))
              (snd⟨ s ⟩ 𝟘 𝟘 (wk1 (A U.[ σ ]))
                 (Id (wk₂ (A U.[ σ ])) (wk₂ (t U.[ σ ])) (var x0))
                 (var x0)) ]                                                    ≡˘⟨ doubleSubstComp′ B ⟩

      B U.[ liftSubstn σ 2 ]
        U.[ consSubst
              (consSubst (wk1Subst idSubst)
                 (fst⟨ s ⟩ 𝟘 (wk1 (A U.[ σ ])) (var x0)))
              (snd⟨ s ⟩ 𝟘 𝟘 (wk1 (A U.[ σ ]))
                 (Id (wk₂ (A U.[ σ ])) (wk₂ (t U.[ σ ])) (var x0))
                 (var x0)) ]                                                    ∎)
                                                                               refl refl
                                                                               (cong₄ (J 𝟘 (𝟘 ∧ 𝟙) (A U.[ σ ]) (t U.[ σ ]))
                                                                                  (cong₃ Id
                                                                                     (trans
                                                                                        (wk[]′-[⇑]
                                                                                           (Σ⟨ _ ⟩ _ , _ ▷ A ▹ Id (wk1 A) (wk1 t) (var x0))) $
                                                                                      PE.cong wk₂ lemma)
                                                                                     (PE.cong₂ (prod s 𝟘) (wk[]′-[⇑] t) refl)
                                                                                     refl)
                                                                                  refl refl refl)
                                                                               refl ⟩
    substᵉ
      (Σ⟨ s ⟩ 𝟘 , 𝟘 ▷ A U.[ σ ] ▹
       Id (wk1 (A U.[ σ ])) (wk1 (t U.[ σ ])) (var x0))
      (B U.[ liftSubstn σ 2 ]
         U.[ consSubst
               (consSubst (wk1Subst idSubst)
                  (fst⟨ s ⟩ 𝟘 (wk1 (A U.[ σ ])) (var x0)))
               (snd⟨ s ⟩ 𝟘 𝟘 (wk1 (A U.[ σ ]))
                  (Id (wk₂ (A U.[ σ ])) (wk₂ (t U.[ σ ])) (var x0))
                  (var x0)) ])
      (prod s 𝟘 (t U.[ σ ]) rfl)
      (prod s 𝟘 (v U.[ σ ]) (w U.[ σ ]))
      (J 𝟘 (𝟘 ∧ 𝟙) (A U.[ σ ]) (t U.[ σ ])
         (Id
            (wk₂ $
             Σ⟨ s ⟩ 𝟘 , 𝟘 ▷ A U.[ σ ] ▹
             Id (wk1 (A U.[ σ ])) (wk1 (t U.[ σ ])) (var x0))
            (wk₂ (prod s 𝟘 (t U.[ σ ]) rfl))
            (prod s 𝟘 (var x1) (var x0)))
         rfl (v U.[ σ ]) (w U.[ σ ]))
      (u U.[ σ ])                                                         ∎

------------------------------------------------------------------------
-- Variants of some term formers, intended to be used with the
-- internal type-checker

module Internal
  {b} {Mode : Set b}
  (𝐌 : IsMode Mode 𝕄)
  (R : Type-restrictions 𝕄)
  where

  open US.Internal 𝐌 R
  open UU.Internal 𝐌 R

  private
    module I =
      Definition.Typed.Decidable.Internal.Term 𝐌 R
    module IS =
      Definition.Typed.Decidable.Internal.Substitution.Primitive 𝐌 R
    module IW =
      Definition.Typed.Decidable.Internal.Weakening 𝐌 R

  private variable
    c           : I.Constants
    pᵢ          : I.Termᵍ _
    Aᵢ Bᵢ tᵢ uᵢ : I.Term _ _
    lᵢ          : I.Lvl _ _
    γ           : I.Contexts _

  -- A variant of erased, intended to be used with the internal
  -- type-checker.

  erasedᵢ : (_ _ : I.Term c n) → I.Term c n
  erasedᵢ A t = fst⟨ s ⟩ᵢ I.𝟘 A t

  opaque
    unfolding erased fst⟨_⟩

    -- A translation lemma for erasedᵢ.

    ⌜erasedᵢ⌝ :
      I.⌜ erasedᵢ Aᵢ tᵢ ⌝ γ ≡
      erased (I.⌜ Aᵢ ⌝ γ) (I.⌜ tᵢ ⌝ γ)
    ⌜erasedᵢ⌝ with PE.singleton s
    … | 𝕨 , refl = refl
    … | 𝕤 , refl = refl

  -- A variant of erasedrec, intended to be used with the internal
  -- type-checker.

  erasedrecᵢ :
    I.Termᵍ (c .I.gs) → (_ _ : I.Term c (1+ n)) → I.Term c n →
    I.Term c n
  erasedrecᵢ p B t u =
    prodrec⟨ s ⟩ᵢ is-𝕨′ I.𝟘 p B u
      (unitrec⟨ s ⟩ᵢ I.𝟙 p
         (I.subst B (I.cons (IS.wkSubst 3 I.id)
            (I.prod s′ I.𝟘 nothing (I.var x2)
               (I.lift nothing (I.var x0)))))
         (I.lower (I.var x0)) (IW.wk[ 1 ] t))
    where
    s′ = case s of λ where
      𝕨 → I.𝕨
      𝕤 → I.𝕤

    is-𝕨′ = case PE.singleton s of λ where
      (𝕨 , _) → I.𝟙
      (𝕤 , _) → I.𝟘

  opaque
    unfolding erasedrec is-𝕨 prodrec⟨_⟩ unitrec⟨_⟩

    -- A translation lemma for erasedrecᵢ.

    ⌜erasedrecᵢ⌝ :
      I.⌜ erasedrecᵢ pᵢ Bᵢ tᵢ uᵢ ⌝ γ ≡
      erasedrec (I.⟦ pᵢ ⟧ᵍ γ) (I.⌜ Bᵢ ⌝ γ) (I.⌜ tᵢ ⌝ γ) (I.⌜ uᵢ ⌝ γ)
    ⌜erasedrecᵢ⌝ with PE.singleton s
    … | 𝕨 , refl = refl
    … | 𝕤 , refl = refl

  -- A variant of mapᴱ, intended to be used with the internal
  -- type-checker.

  mapᴱᵢ :
    I.Lvl c n → I.Term c n → I.Term c (1+ n) → I.Term c n → I.Term c n
  mapᴱᵢ l A t u = I.box s′ l (I.subst t (IS.sgSubst (erasedᵢ A u)))
    where
    s′ = case s of λ where
      𝕨 → I.𝕨
      𝕤 → I.𝕤

  opaque
    unfolding erased fst⟨_⟩ mapᴱ [_]

    -- A translation lemma for mapᴱᵢ.

    ⌜mapᴱᵢ⌝ :
      I.⌜ mapᴱᵢ lᵢ Aᵢ tᵢ uᵢ ⌝ γ ≡
      mapᴱ (I.⌜ Aᵢ ⌝ γ) (I.⌜ tᵢ ⌝ γ) (I.⌜ uᵢ ⌝ γ)
    ⌜mapᴱᵢ⌝ with PE.singleton s
    … | 𝕨 , refl = refl
    … | 𝕤 , refl = refl
