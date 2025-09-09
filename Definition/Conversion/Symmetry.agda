------------------------------------------------------------------------
-- The algorithmic equality is symmetric (in the absence of equality
-- reflection)
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Conversion.Symmetry
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  ⦃ no-equality-reflection : No-equality-reflection ⦄
  where

open import Definition.Untyped M
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.EqualityRelation.Instance R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Stability R
open import Definition.Typed.Substitution R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Weakening R as W hiding (wk)
open import Definition.Conversion R
open import Definition.Conversion.Soundness R
open import Definition.Conversion.Conversion R
open import Definition.Conversion.Whnf R
open import Definition.Typed.Consequences.Equality R
open import Definition.Typed.Consequences.Reduction R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.NeTypeEq R

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    m n : Nat
    ∇ : DCon (Term 0) m
    Δ Η : Con Term n
    Γ : Cons _ _

mutual
  -- Symmetry of algorithmic equality of neutral terms.
  sym~↑ : ∀ {t u A} → ∇ »⊢ Δ ≡ Η
        → ∇ » Δ ⊢ t ~ u ↑ A
        → ∃ λ B → ∇ » Δ ⊢ A ≡ B × ∇ » Η ⊢ u ~ t ↑ B
  sym~↑ Δ≡Η (var-refl x x≡y) =
    let ⊢A = syntacticTerm x in
    _ , refl ⊢A ,
    var-refl (PE.subst (λ y → _ ⊢ var y ∷ _) x≡y (stabilityTerm Δ≡Η x))
      (PE.sym x≡y)
  sym~↑ Δ≡Η (defn-refl α α↦⊘ α≡β) =
    let ⊢A = syntacticTerm α in
    _ , refl ⊢A ,
    defn-refl
      (PE.subst (λ β → _ ⊢ defn β ∷ _) α≡β (stabilityTerm Δ≡Η α))
      (PE.subst (_↦⊘∷ _ ∈ _) α≡β α↦⊘) (PE.sym α≡β)
  sym~↑ Δ≡Η (app-cong t~u x) =
    case contextConvSubst Δ≡Η of λ {
      (⊢Δ , ⊢Η , _) →
    case sym~↓ Δ≡Η t~u of λ {
      (B , whnfB , A≡B , u~t) →
    case Π≡A A≡B whnfB of λ {
      (F′ , G′ , ΠF′G′≡B) →
    case ΠΣ-injectivity (PE.subst (λ x → _ ⊢ _ ≡ x) ΠF′G′≡B A≡B) of λ {
      (F≡F′ , G≡G′ , _ , _) →
    _ , G≡G′ (soundnessConv↑Term x) ,
    app-cong (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) ΠF′G′≡B u~t)
      (convConv↑Term (stabilityEq Δ≡Η F≡F′) (symConv↑Term Δ≡Η x)) }}}}
  sym~↑ Δ≡Η (fst-cong p~r) =
    case sym~↓ Δ≡Η p~r of λ (B , whnfB , A≡B , r~p) →
    case Σ≡A A≡B whnfB of λ where
      (F′ , G′ , PE.refl) →
        case ΠΣ-injectivity A≡B of λ where
          (F≡ , G≡ , _ , _) →
            F′ , F≡ , fst-cong r~p
  sym~↑ Δ≡Η (snd-cong p~r) =
    case sym~↓ Δ≡Η p~r of λ (B , whnfB , A≡B , r~p) →
    case Σ≡A A≡B whnfB of λ where
      (F′ , G′ , PE.refl) →
        case ΠΣ-injectivity A≡B of λ where
          (F≡ , G≡ , _ , _) →
            let fst≡ = soundness~↑ (fst-cong p~r) in
            _ , G≡ fst≡ , snd-cong r~p
  sym~↑ Δ≡Η (natrec-cong x x₁ x₂ t~u) =
    let ⊢Δ , ⊢Η , _ = contextConvSubst Δ≡Η
        B , whnfB , A≡B , u~t = sym~↓ Δ≡Η t~u
        B≡ℕ = ℕ≡A A≡B whnfB
        F≡G = stabilityEq (Δ≡Η ∙ refl (ℕⱼ ⊢Δ)) (soundnessConv↑ x)
        F[0]≡G[0] = substTypeEq F≡G (refl (zeroⱼ ⊢Η))
    in  _ , substTypeEq (soundnessConv↑ x) (soundness~↓ t~u)
    ,   natrec-cong
          (symConv↑ (Δ≡Η ∙ refl (ℕⱼ ⊢Δ)) x)
          (convConv↑Term F[0]≡G[0] (symConv↑Term Δ≡Η x₁))
          (convConv↑Term (sucCong′ F≡G)
             (symConv↑Term (Δ≡Η ∙ refl (ℕⱼ ⊢Δ) ∙ soundnessConv↑ x) x₂))
          (PE.subst (_⊢_~_↓_ _ _ _) B≡ℕ u~t)
  sym~↑ {Δ = Δ} {Η = Η} Δ≡Η
    (prodrec-cong {F = F} {G = G} C↑E g~h u↑v) =
    case sym~↓ Δ≡Η g~h of λ (B , whnfB , ⊢Σ≡B , h~g) →
    case Σ≡A ⊢Σ≡B whnfB of λ where
      (F′ , G′ , PE.refl) →
        case ΠΣ-injectivity-no-equality-reflection
               (stabilityEq Δ≡Η ⊢Σ≡B) of λ where
          (⊢F≡F′ , ⊢G≡G′ , _ , _ , _) →
            let g≡h = soundness~↓ g~h
                C≡E = soundnessConv↑ C↑E
                ⊢Σ , _ = syntacticEqTerm g≡h
                ⊢F , ⊢G , _ = inversion-ΠΣ ⊢Σ
                E↑C = symConv↑ (Δ≡Η ∙ ⊢Σ≡B) C↑E
                v↑u = symConv↑Term (Δ≡Η ∙ refl ⊢F ∙ refl ⊢G) u↑v
                ⊢Δ , ⊢Η , ⊢idsubst = contextConvSubst Δ≡Η
                ⊢F′ = stability Δ≡Η ⊢F
                ⊢G′ = stability (Δ≡Η ∙ refl ⊢F) ⊢G
                ⊢ρF = W.wk (stepʷ (step id) ⊢G′) ⊢F′
                ⊢ρG = W.wk (liftʷ (step (step id)) ⊢ρF) ⊢G′
                C₊≡E₊ = subst↑²TypeEq-prod
                          (stabilityEq (Δ≡Η ∙ refl ⊢Σ) C≡E)
            in  _ , substTypeEq C≡E g≡h
              , prodrec-cong E↑C h~g
                  (convConv↑Term′ (refl-∙ ⊢F≡F′ ∙ ⊢G≡G′)
                     C₊≡E₊ v↑u)
  sym~↑ Δ≡Η (emptyrec-cong x t~u) =
    let ⊢Δ , ⊢Η , _ = contextConvSubst Δ≡Η
        B , whnfB , A≡B , u~t = sym~↓ Δ≡Η t~u
        B≡Empty = Empty≡A A≡B whnfB
        F≡G = stabilityEq Δ≡Η (soundnessConv↑ x)
    in  _ , soundnessConv↑ x
    , emptyrec-cong (symConv↑ Δ≡Η x)
                    (PE.subst (λ x₁ → _ ⊢ _ ~ _ ↓ x₁) B≡Empty u~t)
  sym~↑ Δ≡Η (unitrec-cong F<>H k~l u<>v no-η) =
    let k≡l = soundness~↓ k~l
        ⊢Unit = proj₁ (syntacticEqTerm k≡l)
        H<>F = symConv↑ (Δ≡Η ∙ refl ⊢Unit) F<>H
        B , whB , Unit≡B , l~k = sym~↓ Δ≡Η k~l
        l~k′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x)
                        (Unit≡A Unit≡B whB)
                        l~k
        ⊢Δ , _ = contextConvSubst Δ≡Η
        v<>u = symConv↑Term Δ≡Η u<>v
        ⊢F≡H = soundnessConv↑ F<>H
        ⊢F₊≡H₊ = substTypeEq ⊢F≡H (refl (starⱼ ⊢Δ (inversion-Unit ⊢Unit)))
        ⊢Fk≡Hl = substTypeEq ⊢F≡H k≡l
        v<>u′ = convConv↑Term (stabilityEq Δ≡Η ⊢F₊≡H₊) v<>u
    in  _ , ⊢Fk≡Hl , unitrec-cong H<>F l~k′ v<>u′ no-η
  sym~↑ Δ≡Η (J-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁~w₂ C≡Id-t₁-v₁) =
    case sym~↓ Δ≡Η w₁~w₂ of λ {
      (_ , _ , C≡D , w₂~w₁) →
    case soundnessConv↑ A₁≡A₂ of λ {
      ⊢A₁≡A₂ →
    case soundnessConv↑ B₁≡B₂ of λ {
      ⊢B₁≡B₂ →
    case soundnessConv↑Term t₁≡t₂ of λ {
      ⊢t₁≡t₂ →
    case soundnessConv↑Term v₁≡v₂ of λ {
      ⊢v₁≡v₂ →
    case reflConEq (wfEq ⊢A₁≡A₂) of λ {
      Δ≡Δ →
      _
    , J-result-cong ⊢B₁≡B₂ ⊢v₁≡v₂ (conv (soundness~↓ w₁~w₂) C≡Id-t₁-v₁)
    , J-cong (symConv↑ Δ≡Η A₁≡A₂)
        (convConv↑Term′ Δ≡Η ⊢A₁≡A₂ (symConv↑Term Δ≡Δ t₁≡t₂))
        (symConv↑ (J-motive-context-cong Δ≡Η ⊢A₁≡A₂ ⊢t₁≡t₂) B₁≡B₂)
        (convConv↑Term′ Δ≡Η (J-motive-rfl-cong ⊢B₁≡B₂ ⊢t₁≡t₂)
           (symConv↑Term Δ≡Δ u₁≡u₂))
        (convConv↑Term′ Δ≡Η ⊢A₁≡A₂ (symConv↑Term Δ≡Δ v₁≡v₂)) w₂~w₁
        (stabilityEq Δ≡Η $
         trans (trans (sym C≡D) C≡Id-t₁-v₁)
           (Id-cong ⊢A₁≡A₂ ⊢t₁≡t₂ ⊢v₁≡v₂)) }}}}}}
  sym~↑ Δ≡Η (K-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁~v₂ C≡Id-t₁-t₁ ok) =
    case sym~↓ Δ≡Η v₁~v₂ of λ {
      (_ , _ , C≡D , v₂~v₁) →
    case soundnessConv↑ A₁≡A₂ of λ {
      ⊢A₁≡A₂ →
    case soundnessConv↑ B₁≡B₂ of λ {
      ⊢B₁≡B₂ →
    case soundnessConv↑Term t₁≡t₂ of λ {
      ⊢t₁≡t₂ →
    case reflConEq (wfEq ⊢A₁≡A₂) of λ {
      Δ≡Δ →
      _
    , substTypeEq ⊢B₁≡B₂
        (conv (soundness~↓ v₁~v₂) C≡Id-t₁-t₁)
    , K-cong (symConv↑ Δ≡Η A₁≡A₂)
        (convConv↑Term′ Δ≡Η ⊢A₁≡A₂ (symConv↑Term Δ≡Δ t₁≡t₂))
        (symConv↑ (K-motive-context-cong Δ≡Η ⊢A₁≡A₂ ⊢t₁≡t₂) B₁≡B₂)
        (convConv↑Term′ Δ≡Η (K-motive-rfl-cong ⊢B₁≡B₂)
           (symConv↑Term Δ≡Δ u₁≡u₂))
        v₂~v₁
        (stabilityEq Δ≡Η $
         trans (trans (sym C≡D) C≡Id-t₁-t₁)
           (Id-cong ⊢A₁≡A₂ ⊢t₁≡t₂ ⊢t₁≡t₂))
        ok }}}}}
  sym~↑ Δ≡Η ([]-cong-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁~v₂ B≡Id-t₁-u₁ ok) =
    case sym~↓ Δ≡Η v₁~v₂ of λ {
      (_ , _ , B≡C , v₂~v₁) →
    case soundnessConv↑ A₁≡A₂ of λ {
      ⊢A₁≡A₂ →
    case soundnessConv↑Term t₁≡t₂ of λ {
      ⊢t₁≡t₂ →
    case soundnessConv↑Term u₁≡u₂ of λ {
      ⊢u₁≡u₂ →
    case reflConEq (wfEq ⊢A₁≡A₂) of λ {
      Δ≡Δ →
    case []-cong→Erased ok of λ {
      Erased-ok →
      _
    , Id-cong (Erased-cong Erased-ok ⊢A₁≡A₂) ([]-cong′ Erased-ok ⊢t₁≡t₂)
        ([]-cong′ Erased-ok ⊢u₁≡u₂)
    , []-cong-cong (symConv↑ Δ≡Η A₁≡A₂)
        (convConv↑Term′ Δ≡Η ⊢A₁≡A₂ (symConv↑Term Δ≡Δ t₁≡t₂))
        (convConv↑Term′ Δ≡Η ⊢A₁≡A₂ (symConv↑Term Δ≡Δ u₁≡u₂))
        v₂~v₁
        (stabilityEq Δ≡Η $
         trans (trans (sym B≡C) B≡Id-t₁-u₁)
           (Id-cong ⊢A₁≡A₂ ⊢t₁≡t₂ ⊢u₁≡u₂))
        ok }}}}}}

  -- Symmetry of algorithmic equality of neutral terms with types in WHNF.
  sym~↓ : ∀ {t u A} → ∇ »⊢ Δ ≡ Η → ∇ » Δ ⊢ t ~ u ↓ A
         → ∃ λ B → Whnf ∇ B × ∇ » Δ ⊢ A ≡ B × ∇ » Η ⊢ u ~ t ↓ B
  sym~↓ Δ≡Η ([~] A₁ (D , whnfA) k~l) =
    let B , A≡B , k~l′ = sym~↑ Δ≡Η k~l
        _ , ⊢B = syntacticEq A≡B
        B′ , whnfB′ , D′ = whNorm ⊢B
        A≡B′ = trans (sym (subset* D)) (trans A≡B (subset* D′))
    in  B′ , whnfB′ , A≡B′ ,
        [~] B (stabilityRed* Δ≡Η D′ , whnfB′) k~l′

  -- Symmetry of algorithmic equality of types.
  symConv↑ : ∀ {A B} → ∇ »⊢ Δ ≡ Η → ∇ » Δ ⊢ A [conv↑] B → ∇ » Η ⊢ B [conv↑] A
  symConv↑ Δ≡Η ([↑] A′ B′ D D′ A′<>B′) =
    [↑] B′ A′ (stabilityRed↘ Δ≡Η D′) (stabilityRed↘ Δ≡Η D)
        (symConv↓ Δ≡Η A′<>B′)

  -- Symmetry of algorithmic equality of types in WHNF.
  symConv↓ : ∀ {A B} → ∇ »⊢ Δ ≡ Η → ∇ » Δ ⊢ A [conv↓] B → ∇ » Η ⊢ B [conv↓] A
  symConv↓ Δ≡Η (U-refl x) =
    let _ , ⊢Η , _ = contextConvSubst Δ≡Η
    in  U-refl ⊢Η
  symConv↓ Δ≡Η (ℕ-refl x) =
    let _ , ⊢Η , _ = contextConvSubst Δ≡Η
    in  ℕ-refl ⊢Η
  symConv↓ Δ≡Η (Empty-refl x) =
    let _ , ⊢Η , _ = contextConvSubst Δ≡Η
    in  Empty-refl ⊢Η
  symConv↓ Δ≡Η (Unit-refl x ok) =
    let _ , ⊢Η , _ = contextConvSubst Δ≡Η
    in  Unit-refl ⊢Η ok
  symConv↓ Δ≡Η (ne A~B) =
    let B , whnfB , U≡B , B~A = sym~↓ Δ≡Η A~B
        B≡U = U≡A U≡B whnfB
    in  ne (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) B≡U B~A)
  symConv↓ Δ≡Η (ΠΣ-cong A<>B A<>B₁ ok) =
    let F≡H = soundnessConv↑ A<>B
    in  ΠΣ-cong (symConv↑ Δ≡Η A<>B)
          (symConv↑ (Δ≡Η ∙ F≡H) A<>B₁) ok
  symConv↓ Δ≡Η (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    case soundnessConv↑ A₁≡A₂ of λ {
      ⊢A₁≡A₂ →
    case reflConEq (wfEq ⊢A₁≡A₂) of λ {
      Δ≡Δ →
    Id-cong (symConv↑ Δ≡Η A₁≡A₂)
      (convConv↑Term′ Δ≡Η ⊢A₁≡A₂ (symConv↑Term Δ≡Δ t₁≡t₂))
      (convConv↑Term′ Δ≡Η ⊢A₁≡A₂ (symConv↑Term Δ≡Δ u₁≡u₂)) }}

  -- Symmetry of algorithmic equality of terms.
  symConv↑Term : ∀ {t u A} → ∇ »⊢ Δ ≡ Η → ∇ » Δ ⊢ t [conv↑] u ∷ A → ∇ » Η ⊢ u [conv↑] t ∷ A
  symConv↑Term Δ≡Η ([↑]ₜ B t′ u′ D d d′ t<>u) =
    [↑]ₜ B u′ t′ (stabilityRed↘ Δ≡Η D) (stabilityRed↘Term Δ≡Η d′)
         (stabilityRed↘Term Δ≡Η d) (symConv↓Term Δ≡Η t<>u)

  -- Symmetry of algorithmic equality of terms in WHNF.
  symConv↓Term : ∀ {t u A} → ∇ »⊢ Δ ≡ Η → ∇ » Δ ⊢ t [conv↓] u ∷ A → ∇ » Η ⊢ u [conv↓] t ∷ A
  symConv↓Term Δ≡Η (ℕ-ins t~u) =
    let B , whnfB , A≡B , u~t = sym~↓ Δ≡Η t~u
        B≡ℕ = ℕ≡A A≡B whnfB
    in  ℕ-ins (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) B≡ℕ u~t)
  symConv↓Term Δ≡Η (Empty-ins t~u) =
    let B , whnfB , A≡B , u~t = sym~↓ Δ≡Η t~u
        B≡Empty = Empty≡A A≡B whnfB
    in  Empty-ins (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) B≡Empty u~t)
  symConv↓Term Δ≡Η (Unitʷ-ins ok t~u) =
    let B , whnfB , A≡B , u~t = sym~↓ Δ≡Η t~u
        B≡Unit = Unit≡A A≡B whnfB
    in  Unitʷ-ins ok (PE.subst (_⊢_~_↓_ _ _ _) B≡Unit u~t)
  symConv↓Term Δ≡Η (Σʷ-ins t u t~u) =
    case sym~↓ Δ≡Η t~u of λ (B , whnfB , A≡B , u~t) →
    case Σ≡A A≡B whnfB of λ where
      (_ , B≡Σ , PE.refl) →
        Σʷ-ins (stabilityTerm Δ≡Η u) (stabilityTerm Δ≡Η t) u~t
  symConv↓Term Δ≡Η (ne-ins t u x t~u) =
    let B , whnfB , A≡B , u~t = sym~↓ Δ≡Η t~u
    in  ne-ins (stabilityTerm Δ≡Η u) (stabilityTerm Δ≡Η t) x u~t
  symConv↓Term Δ≡Η (univ x x₁ x₂) =
    univ (stabilityTerm Δ≡Η x₁) (stabilityTerm Δ≡Η x) (symConv↓ Δ≡Η x₂)
  symConv↓Term Δ≡Η (zero-refl x) =
    let _ , ⊢Η , _ = contextConvSubst Δ≡Η
    in  zero-refl ⊢Η
  symConv↓Term Δ≡Η (starʷ-refl _ ok no-η) =
    let _ , ⊢Η , _ = contextConvSubst Δ≡Η
    in  starʷ-refl ⊢Η ok no-η
  symConv↓Term Δ≡Η (suc-cong t<>u) = suc-cong (symConv↑Term Δ≡Η t<>u)
  symConv↓Term Δ≡Η (prod-cong x₁ x₂ x₃ ok) =
    let Η⊢G = stability (Δ≡Η ∙ refl (⊢∙→⊢ (wf x₁))) x₁
        Η⊢t′↑t = symConv↑Term Δ≡Η x₂
        Η⊢u′↑u = symConv↑Term Δ≡Η x₃
        Gt≡Gt′ = substTypeEq (refl Η⊢G)
                   (sym′ (soundnessConv↑Term Η⊢t′↑t))
    in  prod-cong Η⊢G Η⊢t′↑t (convConv↑Term Gt≡Gt′ Η⊢u′↑u) ok
  symConv↓Term Δ≡Η (η-eq x₁ x₂ y y₁ t<>u) =
    let ⊢F , _ , _ = inversion-ΠΣ (syntacticTerm x₁)
    in  η-eq (stabilityTerm Δ≡Η x₂) (stabilityTerm Δ≡Η x₁)
             y₁ y (symConv↑Term (Δ≡Η ∙ refl ⊢F) t<>u)
  symConv↓Term Δ≡Η (Σ-η ⊢p ⊢r pProd rProd fstConv sndConv) =
    let Η⊢p = stabilityTerm Δ≡Η ⊢p
        Η⊢r = stabilityTerm Δ≡Η ⊢r
        _ , ⊢G , _ = inversion-ΠΣ (syntacticTerm ⊢p)
        Ηfst≡ = symConv↑Term Δ≡Η fstConv
        Ηsnd≡₁ = symConv↑Term Δ≡Η sndConv
        ΗGfstt≡Gfstu = stabilityEq Δ≡Η (substTypeEq (refl ⊢G)
                                                    (soundnessConv↑Term fstConv))
        Ηsnd≡ = convConv↑Term ΗGfstt≡Gfstu Ηsnd≡₁
    in  Σ-η Η⊢r Η⊢p rProd pProd Ηfst≡ Ηsnd≡
  symConv↓Term Δ≡Η (η-unit [t] [u] tUnit uUnit ok) =
    let [t] = stabilityTerm Δ≡Η [t]
        [u] = stabilityTerm Δ≡Η [u]
    in  η-unit [u] [t] uUnit tUnit ok
  symConv↓Term Δ≡Η (Id-ins ⊢v₁ v₁~v₂) =
    case sym~↓ Δ≡Η v₁~v₂ of λ {
      (_ , B-whnf , Id≡B , v₂~v₁) →
    case Id≡Whnf Id≡B B-whnf of λ {
      (_ , _ , _ , PE.refl) →
    case syntacticEqTerm (soundness~↓ v₁~v₂) .proj₂ of λ {
      (⊢v₁′ , ⊢v₂) →
    case sym (neTypeEq (ne~↓ v₁~v₂ .proj₂ .proj₁) ⊢v₁ ⊢v₁′) of λ {
      Id≡Id →
    Id-ins (stabilityTerm Δ≡Η (conv ⊢v₂ Id≡Id)) v₂~v₁ }}}}
  symConv↓Term Δ≡Η (rfl-refl t≡u) =
    rfl-refl (stabilityEqTerm Δ≡Η t≡u)

symConv↓Term′ : ∀ {t u A} → Γ ⊢ t [conv↓] u ∷ A → Γ ⊢ u [conv↓] t ∷ A
symConv↓Term′ tConvU =
  symConv↓Term (reflConEq (wfEqTerm (soundnessConv↓Term tConvU))) tConvU

-- Symmetry of algorithmic equality of types with preserved context.
symConv : ∀ {A B} → Γ ⊢ A [conv↑] B → Γ ⊢ B [conv↑] A
symConv A<>B =
  let ⊢Γ = wfEq (soundnessConv↑ A<>B)
  in  symConv↑ (reflConEq ⊢Γ) A<>B

-- Symmetry of algorithmic equality of terms with preserved context.
symConvTerm : ∀ {t u A} → Γ ⊢ t [conv↑] u ∷ A → Γ ⊢ u [conv↑] t ∷ A
symConvTerm t<>u =
  let ⊢Γ = wfEqTerm (soundnessConv↑Term t<>u)
  in  symConv↑Term (reflConEq ⊢Γ) t<>u
