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
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed R
open import Definition.Typed.EqRelInstance R using (eqRelInstance)
open import Definition.Typed.EqualityRelation.Instance R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Stability R
open import Definition.Typed.Substitution R
open import Definition.Typed.Weakening R as W hiding (wk)
open import Definition.Typed.Well-formed R
open import Definition.Conversion R
open import Definition.Conversion.Soundness R
open import Definition.Conversion.Conversion R
open import Definition.Conversion.Stability R
open import Definition.Conversion.Whnf R
open import Definition.Typed.Consequences.Equality R
open import Definition.Typed.Consequences.Reduction R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.NeTypeEq R

open import Tools.Bool
open import Tools.Function
open import Tools.List hiding (_∷_)
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    m n : Nat
    ∇ : DCon (Term 0) m
    Δ Η : Con Term n
    Γ : Cons _ _
    l₁ l₂ : Lvl _
    d : Bool

mutual
  -- Symmetry of algorithmic equality of neutral terms.
  sym~↑ : ∀ {t u A} → ∇ »⊢ Δ ≡ Η
        → ∇ » Δ ⊢ t ~ u ↑ A
        → ∃ λ B → ∇ » Δ ⊢ A ≡ B × ∇ » Η ⊢ u ~ t ↑ B
  sym~↑ Γ≡Δ (var-refl x x≡y) =
    let ⊢A = wf-⊢ x
    in  _ , refl ⊢A
     ,  var-refl (PE.subst (λ y → _ ⊢ var y ∷ _) x≡y (stability Γ≡Δ x))
                 (PE.sym x≡y)
  sym~↑ Δ≡Η (defn-refl α α↦⊘ α≡β) =
    let ⊢A = wf-⊢ α in
    _ , refl ⊢A ,
    defn-refl
      (PE.subst (λ β → _ ⊢ defn β ∷ _) α≡β (stability Δ≡Η α))
      (PE.subst (_↦⊘∷ _ ∈ _) α≡β α↦⊘) (PE.sym α≡β)
  sym~↑ Γ≡Δ (lower-cong t₁~t₂) =
    case sym~↓ Γ≡Δ t₁~t₂ of λ
      (C , whnfB , A≡B , t₂~t₁) →
    case Lift≡A A≡B whnfB of λ {
      (k , D , PE.refl) →
    let _ , A≡D = Lift-injectivity A≡B
    in _ , A≡D , lower-cong t₂~t₁ }
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
      (convConv↑Term (stability Δ≡Η F≡F′) (symConv↑Term Δ≡Η x)) }}}}
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
        F≡G = stability (Δ≡Η ∙ refl (⊢ℕ ⊢Δ)) (soundnessConv↑ x)
        F[0]≡G[0] = subst-⊢≡₀ F≡G (refl (zeroⱼ ⊢Η))
    in  _ , subst-⊢≡₀ (soundnessConv↑ x) (soundness~↓ t~u)
    ,   natrec-cong
          (symConv↑ (Δ≡Η ∙ refl (⊢ℕ ⊢Δ)) x)
          (convConv↑Term F[0]≡G[0] (symConv↑Term Δ≡Η x₁))
          (convConv↑Term (sucCong′ F≡G)
             (symConv↑Term (Δ≡Η ∙ refl (⊢ℕ ⊢Δ) ∙ soundnessConv↑ x) x₂))
          (PE.subst (_⊢_~_↓_ _ _ _) B≡ℕ u~t)
  sym~↑ {Δ = Δ} {Η = Η} Δ≡Η
    (prodrec-cong {F = F} {G = G} C↑E g~h u↑v) =
    case sym~↓ Δ≡Η g~h of λ (B , whnfB , ⊢Σ≡B , h~g) →
    case Σ≡A ⊢Σ≡B whnfB of λ where
      (F′ , G′ , PE.refl) →
        case ΠΣ-injectivity-no-equality-reflection
               (stability Δ≡Η ⊢Σ≡B) of λ where
          (⊢F≡F′ , ⊢G≡G′ , _ , _ , _) →
            let g≡h = soundness~↓ g~h
                C≡E = soundnessConv↑ C↑E
                ⊢Σ , _ = wf-⊢ g≡h
                ⊢F , ⊢G , _ = inversion-ΠΣ ⊢Σ
                E↑C = symConv↑ (Δ≡Η ∙ ⊢Σ≡B) C↑E
                v↑u = symConv↑Term (Δ≡Η ∙ refl ⊢F ∙ refl ⊢G) u↑v
                ⊢Δ , ⊢Η , ⊢idsubst = contextConvSubst Δ≡Η
                ⊢F′ = stability Δ≡Η ⊢F
                ⊢G′ = stability (Δ≡Η ∙ refl ⊢F) ⊢G
                ⊢ρF = W.wk (stepʷ (step id) ⊢G′) ⊢F′
                ⊢ρG = W.wk (liftʷ (step (step id)) ⊢ρF) ⊢G′
                C₊≡E₊ = subst↑²TypeEq-prod
                          (stability (Δ≡Η ∙ refl ⊢Σ) C≡E)
            in  _ , subst-⊢≡₀ C≡E g≡h
              , prodrec-cong E↑C h~g
                  (convConv↑Term′ (refl-∙ ⊢F≡F′ ∙ ⊢G≡G′)
                     C₊≡E₊ v↑u)
  sym~↑ Δ≡Η (emptyrec-cong x t~u) =
    let ⊢Δ , ⊢Η , _ = contextConvSubst Δ≡Η
        B , whnfB , A≡B , u~t = sym~↓ Δ≡Η t~u
        B≡Empty = Empty≡A A≡B whnfB
        F≡G = stability Δ≡Η (soundnessConv↑ x)
    in  _ , soundnessConv↑ x
    , emptyrec-cong (symConv↑ Δ≡Η x)
                    (PE.subst (λ x₁ → _ ⊢ _ ~ _ ↓ x₁) B≡Empty u~t)
  sym~↑ Δ≡Η (unitrec-cong F<>H k~l u<>v no-η) =
    let k≡l = soundness~↓ k~l
        ⊢Unit = proj₁ (wf-⊢ k≡l)
        H<>F = symConv↑ (Δ≡Η ∙ refl ⊢Unit) F<>H
        B , whB , Unit≡B , l~k = sym~↓ Δ≡Η k~l
        l~k′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x)
                        (Unit≡A Unit≡B whB)
                        l~k
        ⊢Δ , _ = contextConvSubst Δ≡Η
        v<>u = symConv↑Term Δ≡Η u<>v
        ⊢F≡H = soundnessConv↑ F<>H
        ⊢F₊≡H₊ = subst-⊢≡₀ ⊢F≡H (refl (starⱼ ⊢Δ (inversion-Unit ⊢Unit)))
        ⊢Fk≡Hl = subst-⊢≡₀ ⊢F≡H k≡l
        v<>u′ = convConv↑Term (stability Δ≡Η ⊢F₊≡H₊) v<>u
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
    case reflConEq (wf ⊢A₁≡A₂) of λ {
      Δ≡Δ →
      _
    , J-result-cong ⊢B₁≡B₂ ⊢v₁≡v₂ (conv (soundness~↓ w₁~w₂) C≡Id-t₁-v₁)
    , J-cong (symConv↑ Δ≡Η A₁≡A₂)
        (convConv↑Term′ Δ≡Η ⊢A₁≡A₂ (symConv↑Term Δ≡Δ t₁≡t₂))
        (symConv↑ (J-motive-context-cong Δ≡Η ⊢A₁≡A₂ ⊢t₁≡t₂) B₁≡B₂)
        (convConv↑Term′ Δ≡Η (J-motive-rfl-cong ⊢B₁≡B₂ ⊢t₁≡t₂)
           (symConv↑Term Δ≡Δ u₁≡u₂))
        (convConv↑Term′ Δ≡Η ⊢A₁≡A₂ (symConv↑Term Δ≡Δ v₁≡v₂)) w₂~w₁
        (stability Δ≡Η $
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
    case reflConEq (wf ⊢A₁≡A₂) of λ {
      Δ≡Δ →
      _
    , subst-⊢≡₀ ⊢B₁≡B₂
        (conv (soundness~↓ v₁~v₂) C≡Id-t₁-t₁)
    , K-cong (symConv↑ Δ≡Η A₁≡A₂)
        (convConv↑Term′ Δ≡Η ⊢A₁≡A₂ (symConv↑Term Δ≡Δ t₁≡t₂))
        (symConv↑ (K-motive-context-cong Δ≡Η ⊢A₁≡A₂ ⊢t₁≡t₂) B₁≡B₂)
        (convConv↑Term′ Δ≡Η (K-motive-rfl-cong ⊢B₁≡B₂)
           (symConv↑Term Δ≡Δ u₁≡u₂))
        v₂~v₁
        (stability Δ≡Η $
         trans (trans (sym C≡D) C≡Id-t₁-t₁)
           (Id-cong ⊢A₁≡A₂ ⊢t₁≡t₂ ⊢t₁≡t₂))
        ok }}}}}
  sym~↑ Γ≡Δ ([]-cong-cong l₁≡l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁~v₂ B≡Id-t₁-u₁ ok) =
    let _ , _ , B≡C , v₂~v₁ = sym~↓ Γ≡Δ v₁~v₂
        ⊢l₁≡l₂              = soundnessConv↑Level l₁≡l₂
        ⊢l₁ , _             = wf-⊢ ⊢l₁≡l₂
        ⊢A₁≡A₂              = soundnessConv↑ A₁≡A₂
        ⊢t₁≡t₂              = soundnessConv↑Term t₁≡t₂
        ⊢u₁≡u₂              = soundnessConv↑Term u₁≡u₂
        Γ≡Γ                 = reflConEq (wf ⊢A₁≡A₂)
        Erased-ok           = []-cong→Erased ok
    in
    _ ,
    Id-cong (Erased-cong Erased-ok ⊢l₁≡l₂ ⊢A₁≡A₂)
      ([]-cong′ Erased-ok ⊢l₁ ⊢t₁≡t₂) ([]-cong′ Erased-ok ⊢l₁ ⊢u₁≡u₂) ,
    []-cong-cong (symConv↑Level Γ≡Δ l₁≡l₂) (symConv↑ Γ≡Δ A₁≡A₂)
      (convConv↑Term′ Γ≡Δ ⊢A₁≡A₂ (symConv↑Term Γ≡Γ t₁≡t₂))
      (convConv↑Term′ Γ≡Δ ⊢A₁≡A₂ (symConv↑Term Γ≡Γ u₁≡u₂))
      v₂~v₁
      (stability Γ≡Δ $
       trans (trans (sym B≡C) B≡Id-t₁-u₁)
         (Id-cong ⊢A₁≡A₂ ⊢t₁≡t₂ ⊢u₁≡u₂))
      ok

  -- Symmetry of algorithmic equality of neutral terms with types in WHNF.
  sym~↓ : ∀ {t u A} → ∇ »⊢ Δ ≡ Η → ∇ » Δ ⊢ t ~ u ↓ A
         → ∃ λ B → Whnf ∇ B × ∇ » Δ ⊢ A ≡ B × ∇ » Η ⊢ u ~ t ↓ B
  sym~↓ Δ≡Η ([~] A₁ (D , whnfA) k~l) =
    let B , A≡B , k~l′ = sym~↑ Δ≡Η k~l
        _ , ⊢B = wf-⊢ A≡B
        B′ , whnfB′ , D′ = whNorm ⊢B
        A≡B′ = trans (sym (subset* D)) (trans A≡B (subset* D′))
    in  B′ , whnfB′ , A≡B′ ,
        [~] B (stabilityRed* Δ≡Η D′ , whnfB′) k~l′

  sym~∷ : ∀ {t u A} → ∇ »⊢ Δ ≡ Η → ∇ » Δ ⊢ t ~ u ∷ A → ∇ » Η ⊢ u ~ t ∷ A
  sym~∷ Γ≡Δ (↑ A≡B k~l) =
    let C , B≡C , k~l′ = sym~↑ Γ≡Δ k~l
    in ↑ (stability Γ≡Δ (trans A≡B B≡C)) k~l′

  -- Symmetry of algorithmic equality of types.
  symConv↑ : ∀ {A B} → ∇ »⊢ Δ ≡ Η → ∇ » Δ ⊢ A [conv↑] B → ∇ » Η ⊢ B [conv↑] A
  symConv↑ Δ≡Η ([↑] A′ B′ D D′ A′<>B′) =
    [↑] B′ A′ (stabilityRed↘ Δ≡Η D′) (stabilityRed↘ Δ≡Η D)
        (symConv↓ Δ≡Η A′<>B′)

  -- Symmetry of algorithmic equality of types in WHNF.
  symConv↓ : ∀ {A B} → ∇ »⊢ Δ ≡ Η → ∇ » Δ ⊢ A [conv↓] B → ∇ » Η ⊢ B [conv↓] A
  symConv↓ Γ≡Δ (Level-refl ok _) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ in
    Level-refl ok ⊢Δ
  symConv↓ Γ≡Δ (U-cong l₁≡l₂) =
    U-cong (symConv↑Level Γ≡Δ l₁≡l₂)
  symConv↓ Γ≡Δ (Lift-cong l₁≡l₂ F≡H) =
    Lift-cong (symConv↑Level Γ≡Δ l₁≡l₂) (symConv↑ Γ≡Δ F≡H)
  symConv↓ Γ≡Δ (ℕ-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  ℕ-refl ⊢Δ
  symConv↓ Γ≡Δ (Empty-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  Empty-refl ⊢Δ
  symConv↓ Γ≡Δ (Unit-refl x ok) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  Unit-refl ⊢Δ ok
  symConv↓ Γ≡Δ (ne A~B) =
    let B , whnfB , U≡B , B~A = sym~↓ Γ≡Δ A~B
        B≡U = U≡A U≡B whnfB .proj₂
    in  ne (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) B≡U B~A)
  symConv↓ Δ≡Η (ΠΣ-cong A<>B A<>B₁ ok) =
    let F≡H = soundnessConv↑ A<>B
    in  ΠΣ-cong (symConv↑ Δ≡Η A<>B)
          (symConv↑ (Δ≡Η ∙ F≡H) A<>B₁) ok
  symConv↓ Δ≡Η (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    case soundnessConv↑ A₁≡A₂ of λ {
      ⊢A₁≡A₂ →
    case reflConEq (wf ⊢A₁≡A₂) of λ {
      Δ≡Δ →
    Id-cong (symConv↑ Δ≡Η A₁≡A₂)
      (convConv↑Term′ Δ≡Η ⊢A₁≡A₂ (symConv↑Term Δ≡Δ t₁≡t₂))
      (convConv↑Term′ Δ≡Η ⊢A₁≡A₂ (symConv↑Term Δ≡Δ u₁≡u₂)) }}

  -- Symmetry of algorithmic equality of terms.
  symConv↑Term : ∀ {t u A} → ∇ »⊢ Δ ≡ Η → ∇ » Δ ⊢ t [conv↑] u ∷ A → ∇ » Η ⊢ u [conv↑] t ∷ A
  symConv↑Term Δ≡Η ([↑]ₜ B t′ u′ D d d′ t<>u) =
    [↑]ₜ B u′ t′ (stabilityRed↘ Δ≡Η D) (stabilityRed↘Term Δ≡Η d′)
         (stabilityRed↘Term Δ≡Η d) (symConv↓Term Δ≡Η t<>u)

  -- A variant of symmetry for _⊢_[conv↑]_∷Level.
  symConv↑Level :
    ∇ »⊢ Δ ≡ Η →
    ∇ » Δ ⊢ l₁ [conv↑] l₂ ∷Level →
    ∇ » Η ⊢ l₂ [conv↑] l₁ ∷Level
  symConv↑Level Γ≡Δ (term ok l₁≡l₂) =
    term ok (symConv↑Term Γ≡Δ l₁≡l₂)
  symConv↑Level Γ≡Δ (literal! ok _) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ in
    literal! ok ⊢Δ

  -- Symmetry of algorithmic equality of terms in WHNF.
  symConv↓Term : ∀ {t u A} → ∇ »⊢ Δ ≡ Η → ∇ » Δ ⊢ t [conv↓] u ∷ A → ∇ » Η ⊢ u [conv↓] t ∷ A
  symConv↓Term Γ≡Δ (Level-ins t~u) =
    Level-ins (stabilityConv↓Level Γ≡Δ (symConv↓Level t~u))
  symConv↓Term Γ≡Δ (ℕ-ins t~u) =
    let B , whnfB , A≡B , u~t = sym~↓ Γ≡Δ t~u
        B≡ℕ = ℕ≡A A≡B whnfB
    in  ℕ-ins (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) B≡ℕ u~t)
  symConv↓Term Δ≡Η (Empty-ins t~u) =
    let B , whnfB , A≡B , u~t = sym~↓ Δ≡Η t~u
        B≡Empty = Empty≡A A≡B whnfB
    in  Empty-ins (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) B≡Empty u~t)
  symConv↓Term Γ≡Δ (Unitʷ-ins ok t~u) =
    let _ , B-whnf , A≡B , u~t = sym~↓ Γ≡Δ t~u in
    Unitʷ-ins ok (PE.subst (_⊢_~_↓_ _ _ _) (Unit≡A A≡B B-whnf) u~t)
  symConv↓Term Γ≡Δ (Σʷ-ins t u t~u) =
    case sym~↓ Γ≡Δ t~u of λ (B , whnfB , A≡B , u~t) →
    case Σ≡A A≡B whnfB of λ where
      (_ , B≡Σ , PE.refl) →
        Σʷ-ins (stability Γ≡Δ u) (stability Γ≡Δ t) u~t
  symConv↓Term Γ≡Δ (ne-ins t u x t~u) =
    let B , whnfB , A≡B , u~t = sym~↓ Γ≡Δ t~u
    in  ne-ins (stability Γ≡Δ u) (stability Γ≡Δ t) x u~t
  symConv↓Term Γ≡Δ (univ x x₁ x₂) =
    univ (stability Γ≡Δ x₁) (stability Γ≡Δ x) (symConv↓ Γ≡Δ x₂)
  symConv↓Term Γ≡Δ (Lift-η ⊢t ⊢u wt wu lower≡lower) =
    Lift-η (stability Γ≡Δ ⊢u) (stability Γ≡Δ ⊢t) wu wt (symConv↑Term Γ≡Δ lower≡lower)
  symConv↓Term Γ≡Δ (zero-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  zero-refl ⊢Δ
  symConv↓Term Γ≡Δ (starʷ-refl y ok no-η) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  starʷ-refl ⊢Δ ok no-η
  symConv↓Term Γ≡Δ (suc-cong t<>u) = suc-cong (symConv↑Term Γ≡Δ t<>u)
  symConv↓Term Γ≡Δ (prod-cong x₁ x₂ x₃ ok) =
    let Δ⊢G = stability (Γ≡Δ ∙ refl (⊢∙→⊢ (wf x₁))) x₁
        Δ⊢t′↑t = symConv↑Term Γ≡Δ x₂
        Δ⊢u′↑u = symConv↑Term Γ≡Δ x₃
        Gt≡Gt′ = subst-⊢≡₀ Δ⊢G (sym′ (soundnessConv↑Term Δ⊢t′↑t))
    in  prod-cong Δ⊢G Δ⊢t′↑t (convConv↑Term Gt≡Gt′ Δ⊢u′↑u) ok
  symConv↓Term Δ≡Η (η-eq x₁ x₂ y y₁ t<>u) =
    let ⊢F , _ , _ = inversion-ΠΣ (wf-⊢ x₁)
    in  η-eq (stability Δ≡Η x₂) (stability Δ≡Η x₁)
             y₁ y (symConv↑Term (Δ≡Η ∙ refl ⊢F) t<>u)
  symConv↓Term Δ≡Η (Σ-η ⊢p ⊢r pProd rProd fstConv sndConv) =
    let Η⊢p = stability Δ≡Η ⊢p
        Η⊢r = stability Δ≡Η ⊢r
        _ , ⊢G , _ = inversion-ΠΣ (wf-⊢ ⊢p)
        Ηfst≡ = symConv↑Term Δ≡Η fstConv
        Ηsnd≡₁ = symConv↑Term Δ≡Η sndConv
        ΗGfstt≡Gfstu =
          stability Δ≡Η (subst-⊢≡₀ ⊢G (soundnessConv↑Term fstConv))
        Ηsnd≡ = convConv↑Term ΗGfstt≡Gfstu Ηsnd≡₁
    in  Σ-η Η⊢r Η⊢p rProd pProd Ηfst≡ Ηsnd≡
  symConv↓Term Δ≡Η (η-unit [t] [u] tUnit uUnit ok) =
    let [t] = stability Δ≡Η [t]
        [u] = stability Δ≡Η [u]
    in  η-unit [u] [t] uUnit tUnit ok
  symConv↓Term Δ≡Η (Id-ins ⊢v₁ v₁~v₂) =
    case sym~↓ Δ≡Η v₁~v₂ of λ {
      (_ , B-whnf , Id≡B , v₂~v₁) →
    case Id≡Whnf Id≡B B-whnf of λ {
      (_ , _ , _ , PE.refl) →
    case wf-⊢ (soundness~↓ v₁~v₂) .proj₂ of λ {
      (⊢v₁′ , ⊢v₂) →
    case sym (neTypeEq (ne⁻ (ne~↓ v₁~v₂ .proj₂ .proj₁)) ⊢v₁ ⊢v₁′) of λ {
      Id≡Id →
    Id-ins (stability Δ≡Η (conv ⊢v₂ Id≡Id)) v₂~v₁ }}}}
  symConv↓Term Δ≡Η (rfl-refl t≡u) =
    rfl-refl (stability Δ≡Η t≡u)

  -- Symmetry of algorithmic equality of levels.

  symConv↓Level : ∀ {t u} → Γ ⊢ t [conv↓] u ∷Level → Γ ⊢ u [conv↓] t ∷Level
  symConv↓Level ([↓]ˡ tᵛ uᵛ t≡ u≡ t≡u) =
    [↓]ˡ uᵛ tᵛ u≡ t≡ (sym-≡ᵛ t≡u)

  sym~↓Level : ∀ {t u} → Γ ⊢ t ~ u ↓ Level → Γ ⊢ u ~ t ↓ Level
  sym~↓Level t~u =
    let B , whnfB , Level≡B , u~t = sym~↓ (reflConEq (wf (soundness~↓ t~u))) t~u
    in PE.subst (_⊢_~_↓_ _ _ _) (Level≡A Level≡B whnfB) u~t

  sym-≡ⁿ : ∀ {t u : Term n} → ≡ⁿ Γ t u d → ≡ⁿ Γ t u (not d)
  sym-≡ⁿ (ne≡ x) = ne≡' (sym~↓Level x)
  sym-≡ⁿ (ne≡' x) = ne≡ (sym~↓Level x)

  sym-≤ᵃ : ∀ {t u : LevelAtom Γ} → ≤ᵃ d t u → ≤ᵃ (not d) t u
  sym-≤ᵃ zeroᵘ≤ = zeroᵘ≤
  sym-≤ᵃ (ne≤ x) = ne≤ (sym-≡ⁿ x)

  sym-≤⁺ : ∀ {t u : Level⁺ Γ} → ≤⁺ d t u → ≤⁺ (not d) t u
  sym-≤⁺ (a , b) = a , sym-≤ᵃ b

  sym-≤⁺ᵛ : ∀ {t} {u : Levelᵛ Γ} → ≤⁺ᵛ d t u → ≤⁺ᵛ (not d) t u
  sym-≤⁺ᵛ (Any.here px) = Any.here (sym-≤⁺ px)
  sym-≤⁺ᵛ (Any.there x) = Any.there (sym-≤⁺ᵛ x)

  sym-≤ᵛ : ∀ {t u : Levelᵛ Γ} → ≤ᵛ d t u → ≤ᵛ (not d) t u
  sym-≤ᵛ All.[] = All.[]
  sym-≤ᵛ (px All.∷ x) = sym-≤⁺ᵛ px All.∷ sym-≤ᵛ x

  sym-≡ᵛ : ∀ {t u : Levelᵛ Γ} → t ≡ᵛ u → u ≡ᵛ t
  sym-≡ᵛ (t≤u , u≤t) = sym-≤ᵛ u≤t , sym-≤ᵛ t≤u

symConv↓Term′ : ∀ {t u A} → Γ ⊢ t [conv↓] u ∷ A → Γ ⊢ u [conv↓] t ∷ A
symConv↓Term′ tConvU =
  symConv↓Term (reflConEq (wf (soundnessConv↓Term tConvU))) tConvU

-- Symmetry of algorithmic equality of types with preserved context.
symConv : ∀ {A B} → Γ ⊢ A [conv↑] B → Γ ⊢ B [conv↑] A
symConv A<>B =
  let ⊢Γ = wf (soundnessConv↑ A<>B)
  in  symConv↑ (reflConEq ⊢Γ) A<>B

-- Symmetry of algorithmic equality of terms with preserved context.
symConvTerm : ∀ {t u A} → Γ ⊢ t [conv↑] u ∷ A → Γ ⊢ u [conv↑] t ∷ A
symConvTerm t<>u =
  let ⊢Γ = wf (soundnessConv↑Term t<>u)
  in  symConv↑Term (reflConEq ⊢Γ) t<>u
