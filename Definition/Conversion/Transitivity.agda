------------------------------------------------------------------------
-- The algorithmic equality is transitive (in the absence of equality
-- reflection)
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Conversion.Transitivity
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  ⦃ no-equality-reflection : No-equality-reflection ⦄
  where

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Properties.Neutral M type-variant
open import Definition.Typed R
open import Definition.Typed.EqRelInstance R using (eqRelInstance)
open import Definition.Typed.EqualityRelation.Instance R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Stability R
open import Definition.Typed.Substitution R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Well-formed R
open import Definition.Conversion R
open import Definition.Conversion.Inversion R
open import Definition.Conversion.Soundness R
open import Definition.Conversion.Stability R
open import Definition.Conversion.Whnf R
open import Definition.Conversion.Conversion R
open import Definition.Conversion.Level R
open import Definition.Typed.Consequences.Injectivity R
import Definition.Typed.Consequences.Inequality R as WF
open import Definition.Typed.Consequences.NeTypeEq R

open import Tools.Bool
open import Tools.Function
open import Tools.List hiding (_∷_)
open import Tools.Nat
open import Tools.Product
open import Tools.Empty
import Tools.PropositionalEquality as PE
open import Tools.Sum using (inj₁; inj₂)

private
  variable
    n : Nat
    Γ Δ : Con Term n
    A l₁ l₂ l₃ t u v : Term _
    d : Bool

mutual
  -- Transitivity of algorithmic equality of neutrals.
  trans~↑ : ∀ {t u v A B}
         → Γ ⊢ t ~ u ↑ A
         → Γ ⊢ u ~ v ↑ B
         → Γ ⊢ t ~ v ↑ A
         × Γ ⊢ A ≡ B
  trans~↑ (var-refl x₁ x≡y) (var-refl x₂ x≡y₁) =
    var-refl x₁ (PE.trans x≡y x≡y₁)
    , neTypeEq (var _) x₁
               (PE.subst (λ x → _ ⊢ var x ∷ _) (PE.sym x≡y)
                         x₂)
  trans~↑ (app-cong t~u a<>b) (app-cong u~v b<>c) =
    let t~v , ΠFG≡ΠF′G′ = trans~↓ t~u u~v
        F≡F₁ , G≡G₁ , p≡p₄ , _ = ΠΣ-injectivity ΠFG≡ΠF′G′
        a<>c = transConv↑Term F≡F₁ a<>b b<>c
    in  app-cong t~v a<>c , G≡G₁ (soundnessConv↑Term a<>b)
  trans~↑ (lower-cong t~u) (lower-cong u~v) =
    let t~v , Lift≡Lift = trans~↓ t~u u~v
        _ , F≡F′ = Lift-injectivity Lift≡Lift
    in  lower-cong t~v , F≡F′
  trans~↑ (fst-cong t~u) (fst-cong u~v) =
    let t~v , ΣFG≡ΣF′G′ = trans~↓ t~u u~v
        F≡F′ , _ , _ = ΠΣ-injectivity ΣFG≡ΣF′G′
    in  fst-cong t~v , F≡F′
  trans~↑ (snd-cong t~u) (snd-cong u~v) =
    let t~v , ΣFG≡ΣF′G′ = trans~↓ t~u u~v
        F≡F′ , G≡G′ , _ = ΠΣ-injectivity ΣFG≡ΣF′G′
    in  snd-cong t~v , G≡G′ (soundness~↑ (fst-cong t~u))
  trans~↑ (natrec-cong A<>B a₀<>b₀ aₛ<>bₛ t~u)
          (natrec-cong B<>C b₀<>c₀ bₛ<>cₛ u~v) =
    let ⊢Γ = wf (proj₁ (syntacticEqTerm (soundness~↓ t~u)))
        A≡B = soundnessConv↑ A<>B
        F[0]≡F₁[0] = substTypeEq A≡B (refl (zeroⱼ ⊢Γ))
        F↑̂²≡F₁↑² = sucCong A≡B
        A<>C = transConv↑ A<>B B<>C
        a₀<>c₀ = transConv↑Term F[0]≡F₁[0] a₀<>b₀ b₀<>c₀
        aₛ<>cₛ = transConv↑Term F↑̂²≡F₁↑² aₛ<>bₛ
                   (stabilityConv↑Term (refl-∙ (sym A≡B)) bₛ<>cₛ)
        t~v , _ = trans~↓ t~u u~v
    in  natrec-cong A<>C a₀<>c₀ aₛ<>cₛ t~v
    ,   substTypeEq A≡B (soundness~↓ t~u)
  trans~↑ {Γ = Γ} (prodrec-cong {F = F} {G} A<>B a~b t<>u)
                  (prodrec-cong B<>C b~c u<>v) =
    let a~c , Σ≡Σ′ = trans~↓ a~b b~c
        ⊢Γ = wfEq Σ≡Σ′
        F≡F′ , G≡G′ , _ =
          ΠΣ-injectivity-no-equality-reflection (sym Σ≡Σ′)
        _ , ⊢F = syntacticEq F≡F′
        _ , ⊢G = syntacticEq G≡G′
        ⊢G = stability (refl-∙ F≡F′) ⊢G
        B<>C′ = stabilityConv↑ (refl-∙ (sym Σ≡Σ′)) B<>C
        A<>C = transConv↑ A<>B B<>C′
        u<>v′ = stabilityConv↑Term (refl-∙ F≡F′ ∙ G≡G′) u<>v
        _ , ⊢ΓFG , _ = contextConvSubst (refl-∙ F≡F′ ∙ G≡G′)
        A≡B = soundnessConv↑ A<>B
        A₊≡B₊ = subst↑²TypeEq-prod A≡B
        t<>v = transConv↑Term A₊≡B₊ t<>u u<>v′
        a≡b = soundness~↓ a~b
        Aa≡Bb = substTypeEq A≡B a≡b
    in  prodrec-cong A<>C a~c t<>v , Aa≡Bb
  trans~↑ (emptyrec-cong A<>B t~u) (emptyrec-cong B<>C u~v) =
    let A≡B = soundnessConv↑ A<>B
        A<>C = transConv↑ A<>B B<>C
        t~v , _ = trans~↓  t~u u~v
    in  emptyrec-cong A<>C t~v , A≡B
  trans~↑ (unitrec-cong A<>B k~l u<>v no-η)
    (unitrec-cong B<>C l~m v<>w _) =
    let k~m , ⊢Unit≡Unit = trans~↓ k~l l~m
        ⊢Unit = proj₁ (syntacticEq ⊢Unit≡Unit)
        ok = inversion-Unit ⊢Unit
        ⊢Γ = wf ⊢Unit
        A<>C = transConv↑ A<>B B<>C
        A≡B = soundnessConv↑ A<>B
        A₊≡B₊ = substTypeEq A≡B (refl (starⱼ ⊢Γ ok))
        Ak≡Bl = substTypeEq A≡B (soundness~↓ k~l)
        u<>w = transConv↑Term A₊≡B₊ u<>v v<>w
    in  unitrec-cong A<>C k~m u<>w no-η , Ak≡Bl
  trans~↑ (J-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁~w₂ C₁≡Id-t₁-v₁)
    (J-cong A₂≡A₃ t₂≡t₃ B₂≡B₃ u₂≡u₃ v₂≡v₃ w₂~w₃ _) =
    case soundnessConv↑ A₁≡A₂ of λ {
      ⊢A₁≡A₂ →
    case soundnessConv↑ B₁≡B₂ of λ {
      ⊢B₁≡B₂ →
    case soundnessConv↑Term t₁≡t₂ of λ {
      ⊢t₁≡t₂ →
      J-cong (transConv↑ A₁≡A₂ A₂≡A₃)
        (transConv↑Term ⊢A₁≡A₂ t₁≡t₂ t₂≡t₃)
        (transConv↑ B₁≡B₂
           (stabilityConv↑
              (symConEq (J-motive-context-cong′ ⊢A₁≡A₂ ⊢t₁≡t₂)) B₂≡B₃))
        (transConv↑Term (J-motive-rfl-cong ⊢B₁≡B₂ ⊢t₁≡t₂) u₁≡u₂ u₂≡u₃)
        (transConv↑Term ⊢A₁≡A₂ v₁≡v₂ v₂≡v₃) (trans~↓ w₁~w₂ w₂~w₃ .proj₁)
        C₁≡Id-t₁-v₁
    , J-result-cong ⊢B₁≡B₂ (soundnessConv↑Term v₁≡v₂)
        (conv (soundness~↓ w₁~w₂) C₁≡Id-t₁-v₁) }}}
  trans~↑ (K-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁~v₂ C₁≡Id-t₁-t₁ ok)
    (K-cong A₂≡A₃ t₂≡t₃ B₂≡B₃ u₂≡u₃ v₂~v₃ _ _) =
    case soundnessConv↑ A₁≡A₂ of λ {
      ⊢A₁≡A₂ →
    case soundnessConv↑ B₁≡B₂ of λ {
      ⊢B₁≡B₂ →
      K-cong (transConv↑ A₁≡A₂ A₂≡A₃)
        (transConv↑Term ⊢A₁≡A₂ t₁≡t₂ t₂≡t₃)
        (transConv↑ B₁≡B₂
           (stabilityConv↑
              (symConEq $
               K-motive-context-cong′ ⊢A₁≡A₂ (soundnessConv↑Term t₁≡t₂))
              B₂≡B₃))
        (transConv↑Term (K-motive-rfl-cong ⊢B₁≡B₂) u₁≡u₂ u₂≡u₃)
        (trans~↓ v₁~v₂ v₂~v₃ .proj₁) C₁≡Id-t₁-t₁ ok
    , substTypeEq ⊢B₁≡B₂ (conv (soundness~↓ v₁~v₂) C₁≡Id-t₁-t₁) }}
  trans~↑ ([]-cong-cong l₁≡l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁~v₂ B₁≡Id-t₁-u₁ ok)
    ([]-cong-cong l₂≡l₃ A₂≡A₃ t₂≡t₃ u₂≡u₃ v₂~v₃ _ _) =
    let ⊢l₁≡l₂    = soundnessConv↑Level l₁≡l₂
        ⊢l₁ , _   = wf-⊢≡∷L ⊢l₁≡l₂
        ⊢A₁≡A₂    = soundnessConv↑ A₁≡A₂
        Erased-ok = []-cong→Erased ok
    in
    []-cong-cong (transConvLevel l₁≡l₂ l₂≡l₃) (transConv↑ A₁≡A₂ A₂≡A₃)
      (transConv↑Term ⊢A₁≡A₂ t₁≡t₂ t₂≡t₃)
      (transConv↑Term ⊢A₁≡A₂ u₁≡u₂ u₂≡u₃)
      (trans~↓ v₁~v₂ v₂~v₃ .proj₁) B₁≡Id-t₁-u₁ ok ,
    Id-cong (Erased-cong Erased-ok ⊢l₁≡l₂ ⊢A₁≡A₂)
      ([]-cong′ Erased-ok ⊢l₁ (soundnessConv↑Term t₁≡t₂))
      ([]-cong′ Erased-ok ⊢l₁ (soundnessConv↑Term u₁≡u₂))

  -- Transitivity of algorithmic equality of neutrals with types in WHNF.
  trans~↓ : ∀ {t u v A B}
          → Γ ⊢ t ~ u ↓ A
          → Γ ⊢ u ~ v ↓ B
          → Γ ⊢ t ~ v ↓ A
          × Γ ⊢ A ≡ B
  trans~↓ ([~] A₁ D′@(D , _) k~l) ([~] A₂ (D₁ , _) k~l₁) =
    let t~v , A≡B = trans~↑ k~l k~l₁
    in  [~] A₁ D′ t~v
    ,   trans (sym (subset* D))
              (trans A≡B
                     (subset* D₁))

  trans~∷ : ∀ {t u v A B}
          → Γ ⊢ t ~ u ∷ A
          → Γ ⊢ u ~ v ∷ B
          → Γ ⊢ t ~ v ∷ A
          × Γ ⊢ A ≡ B
  trans~∷ (↑ A≡C t~u) (↑ B≡D u~v) =
    let t~v , C≡D = trans~↑ t~u u~v
    in ↑ A≡C t~v , trans A≡C (trans C≡D (sym B≡D))

  -- Transitivity of algorithmic equality of types.
  transConv↑ : ∀ {A B C}
            → Γ ⊢ A [conv↑] B
            → Γ ⊢ B [conv↑] C
            → Γ ⊢ A [conv↑] C
  transConv↑ ([↑] A′ B′ D D′ A′<>B′)
             ([↑] A″ B″ D₁ D″ A′<>B″) =
    [↑] A′ B″ D D″
        (transConv↓ A′<>B′
                    (PE.subst (λ x → _ ⊢ x [conv↓] B″)
                       (whrDet* D₁ D′) A′<>B″))
  transConv↑′ : ∀ {A B C}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ A [conv↑] B
              → Δ ⊢ B [conv↑] C
              → Γ ⊢ A [conv↑] C
  transConv↑′ Γ≡Δ aConvB bConvC =
    transConv↑ aConvB (stabilityConv↑ (symConEq Γ≡Δ) bConvC)

  -- Transitivity of algorithmic equality of types in WHNF.
  transConv↓ : ∀ {A B C}
            → Γ ⊢ A [conv↓] B
            → Γ ⊢ B [conv↓] C
            → Γ ⊢ A [conv↓] C
  transConv↓ Level≡Level@(Level-refl _ _) Level≡C =
    case inv-[conv↓]-Level′ Level≡C of λ where
      (inj₁ (PE.refl , PE.refl)) → Level≡Level
      (inj₂ (Level≢Level , _))           → ⊥-elim (Level≢Level PE.refl)
  transConv↓ (ne A~B) B≡C =
    case inv-[conv↓]-ne′ B≡C of λ where
      (inj₁ (_ , B~C))    → ne (trans~↓ A~B B~C .proj₁)
      (inj₂ (¬-B-ne , _)) →
        let _ , _ , B-ne = ne~↓ A~B in
        ⊥-elim (¬-B-ne (ne⁻ B-ne))
  transConv↓ U≡U@(U-cong l₁≡l₂) U≡C =
    case inv-[conv↓]-U′ U≡C of λ where
      (inj₁ (_ , _ , PE.refl , PE.refl , l₂≡l₃)) →
        U-cong (transConvLevel l₁≡l₂ l₂≡l₃)
      (inj₂ (U≢U , _)) →
        ⊥-elim (U≢U (_ , PE.refl))
  transConv↓ (Lift-cong l₁≡l₂ F≡G) Lift≡C =
    case inv-[conv↓]-Lift′ Lift≡C of λ where
      (inj₁
         (_ , _ , _ , _ , PE.refl , PE.refl , l₂≡l₃ , G≡H)) →
        Lift-cong (transConvLevel l₁≡l₂ l₂≡l₃) (transConv↑ F≡G G≡H)
      (inj₂ (Lift≢Lift , _)) →
        ⊥-elim (Lift≢Lift (_ , _ , PE.refl))
  transConv↓ (ΠΣ-cong A₁≡B₁ A₂≡B₂ ok) ΠΣ≡C =
    case inv-[conv↓]-ΠΣ′ ΠΣ≡C of λ where
      (inj₁
         (_ , _ , _ , _ , _ , _ , _ ,
          PE.refl , PE.refl , B₁≡C₁ , B₂≡C₂)) →
        ΠΣ-cong (transConv↑ A₁≡B₁ B₁≡C₁)
          (transConv↑′ (refl-∙ (soundnessConv↑ A₁≡B₁)) A₂≡B₂ B₂≡C₂) ok
      (inj₂ (ΠΣ≢ΠΣ , _)) →
        ⊥-elim (ΠΣ≢ΠΣ (_ , _ , _ , _ , _ , PE.refl))
  transConv↓ Empty≡Empty@(Empty-refl _) Empty≡C =
    case inv-[conv↓]-Empty′ Empty≡C of λ where
      (inj₁ (PE.refl , PE.refl)) → Empty≡Empty
      (inj₂ (Empty≢Empty , _))   → ⊥-elim (Empty≢Empty PE.refl)
  transConv↓ Unit≡Unit@(Unit-refl x ok) Unit≡C =
    case inv-[conv↓]-Unit′ Unit≡C of λ where
      (inj₁ (_ , PE.refl , PE.refl)) →
        Unit-refl x ok
      (inj₂ (Unit≢Unit , _))             →
        ⊥-elim (Unit≢Unit (_ , PE.refl))
  transConv↓ ℕ≡ℕ@(ℕ-refl _) ℕ≡C =
    case inv-[conv↓]-ℕ′ ℕ≡C of λ where
      (inj₁ (PE.refl , PE.refl)) → ℕ≡ℕ
      (inj₂ (ℕ≢ℕ , _))           → ⊥-elim (ℕ≢ℕ PE.refl)
  transConv↓ (Id-cong A≡B t₁≡u₁ t₂≡u₂) Id≡C =
    case inv-[conv↓]-Id′ Id≡C of λ where
      (inj₁
         (_ , _ , _ , _ , _ , _ ,
          PE.refl , PE.refl , B≡C , u₁≡v₁ , u₂≡v₂)) →
        let ⊢A≡B = soundnessConv↑ A≡B in
        Id-cong (transConv↑ A≡B B≡C) (transConv↑Term ⊢A≡B t₁≡u₁ u₁≡v₁)
          (transConv↑Term ⊢A≡B t₂≡u₂ u₂≡v₂)
      (inj₂ (Id≢Id , _)) →
        ⊥-elim (Id≢Id (_ , _ , _ , PE.refl))

  -- Transitivity of algorithmic equality of terms.
  transConv↑Term : ∀ {t u v A B}
                → Γ ⊢ A ≡ B
                → Γ ⊢ t [conv↑] u ∷ A
                → Γ ⊢ u [conv↑] v ∷ B
                → Γ ⊢ t [conv↑] v ∷ A
  transConv↑Term A≡B ([↑]ₜ B₁ t′ u′ D d d′ t<>u)
                 ([↑]ₜ B₂ t″ u″ D₁ d₁ d″ t<>u₁) =
    let B₁≡B₂ = trans (sym (subset* (D .proj₁)))
                      (trans A≡B
                             (subset* (D₁ .proj₁)))
        d₁″ = conv↘∷ d″ (sym B₁≡B₂)
        d₁′  = conv↘∷ d′ B₁≡B₂
    in  [↑]ₜ B₁ t′ u″ D d d₁″
          (transConv↓Term t<>u
             (convConv↓Term (sym B₁≡B₂) (whnfConv↓Term t<>u .proj₁) $
              PE.subst (_ ⊢_[conv↓] _ ∷ _) (whrDet*Term d₁ d₁′) t<>u₁))

  -- Transitivity for _⊢_[conv↓]_∷_.
  transConv↓Term :
    Γ ⊢ t [conv↓] u ∷ A →
    Γ ⊢ u [conv↓] v ∷ A →
    Γ ⊢ t [conv↓] v ∷ A
  transConv↓Term (Level-ins x) u≡v = Level-ins (transConv↓Level x (inv-[conv↓]∷-Level u≡v))
  transConv↓Term (ne-ins ⊢t _ A-ne t~u) u≡v =
    let _ , u~v    = inv-[conv↓]∷-ne A-ne u≡v
        _ , _ , ⊢v = syntacticEqTerm (soundnessConv↓Term u≡v)
    in
    ne-ins ⊢t ⊢v A-ne (trans~↓ t~u u~v .proj₁)
  transConv↓Term (univ ⊢A ⊢B A≡B) B≡C =
    let _ , _ , ⊢C = syntacticEqTerm (soundnessConv↓Term B≡C) in
    univ ⊢A ⊢C (transConv↓ A≡B (inv-[conv↓]∷-U B≡C))
  transConv↓Term (Lift-η ⊢t ⊢u wt wu t≡u) [u≡v] =
    let _ , ⊢v , _ , wv , u≡v = inv-[conv↓]∷-Lift [u≡v]
        ⊢A , _ , _ = syntacticEqTerm (soundnessConv↑Term t≡u)
    in Lift-η ⊢t ⊢v wt wv (transConv↑Term (refl ⊢A) t≡u u≡v)
  transConv↓Term (η-eq ⊢t ⊢u t-fun u-fun t0≡u0) u≡v =
    let _ , v-fun , u0≡v0 = inv-[conv↓]∷-Π u≡v
        _ , _ , ⊢v        = syntacticEqTerm (soundnessConv↓Term u≡v)
    in
    η-eq ⊢t ⊢v t-fun v-fun (transConvTerm t0≡u0 u0≡v0)
  transConv↓Term (Σ-η ⊢t _ t-prod _ fst-t≡fst-u snd-t≡snd-u) u≡v =
    let _ , v-prod , fst-u≡fst-v , snd-u≡snd-v = inv-[conv↓]∷-Σˢ u≡v
        ⊢Σ , _ , ⊢v = syntacticEqTerm (soundnessConv↓Term u≡v)
        _ , ⊢B , _ = inversion-ΠΣ ⊢Σ
    in
    Σ-η ⊢t ⊢v t-prod v-prod (transConvTerm fst-t≡fst-u fst-u≡fst-v)
      (transConv↑Term
         (substTypeEq (refl ⊢B) (soundnessConv↑Term fst-t≡fst-u))
         snd-t≡snd-u snd-u≡snd-v)
  transConv↓Term (Σʷ-ins ⊢t _ t~u) u≡v =
    let _ , _ , ⊢v = syntacticEqTerm (soundnessConv↓Term u≡v) in
    case inv-[conv↓]∷-Σʷ u≡v of λ where
      (inj₁ (_ , _ , _ , _ , u~v)) →
        Σʷ-ins ⊢t ⊢v (trans~↓ t~u u~v .proj₁)
      (inj₂ (_ , _ , _ , _ , PE.refl , _)) →
        ⊥-elim $ ¬-Neutral-prod $ ne⁻ $ ne~↓ t~u .proj₂ .proj₂
  transConv↓Term (prod-cong ⊢B t₁≡u₁ t₂≡u₂ ok) u≡v =
    let _ , _ , ⊢v = syntacticEqTerm (soundnessConv↓Term u≡v) in
    case inv-[conv↓]∷-Σʷ u≡v of λ where
      (inj₁ (_ , _ , _ , _ , u~v)) →
        ⊥-elim $ ¬-Neutral-prod $ ne⁻ $ ne~↓ u~v .proj₂ .proj₁
      (inj₂ (_ , _ , _ , _ , u≡prod , PE.refl , u₁≡v₁ , u₂≡v₂)) →
        case prod-PE-injectivity u≡prod of λ {
          (_ , _ , PE.refl , PE.refl) →
        prod-cong ⊢B (transConvTerm t₁≡u₁ u₁≡v₁)
          (transConv↑Term
             (substTypeEq (refl ⊢B) (soundnessConv↑Term t₁≡u₁))
             t₂≡u₂ u₂≡v₂)
          ok }
  transConv↓Term (Empty-ins t~u) u≡v =
    Empty-ins (trans~↓ t~u (inv-[conv↓]∷-Empty u≡v) .proj₁)
  transConv↓Term (η-unit ⊢t _ t-whnf _ ok η) u≡v =
    let _ , _ , ⊢v = syntacticEqTerm (soundnessConv↓Term u≡v) in
    case inv-[conv↓]∷-Unit u≡v of λ where
      (inj₁ (_ , _ , v-whnf)) → η-unit ⊢t ⊢v t-whnf v-whnf ok η
      (inj₂ (no-η , _))       → ⊥-elim (no-η η)
  transConv↓Term (Unitʷ-ins no-η t~u) u≡v =
    case inv-[conv↓]∷-Unitʷ u≡v of λ where
      (inj₁ (_ , inj₁ u~v)) →
        Unitʷ-ins no-η (trans~↓ t~u u~v .proj₁)
      (inj₁ (_ , inj₂ (PE.refl , PE.refl))) →
        ⊥-elim $ ¬-Neutral-star $ ne⁻ $ ne~↓ t~u .proj₂ .proj₂
      (inj₂ (η , _)) →
        ⊥-elim (no-η η)
  transConv↓Term (starʷ-refl y ok no-η) u≡v =
    case inv-[conv↓]∷-Unitʷ u≡v of λ where
      (inj₁ (_ , inj₁ u~v)) →
        ⊥-elim $ ¬-Neutral-star $ ne⁻ $ ne~↓ u~v .proj₂ .proj₁
      (inj₁ (_ , inj₂ (_ , PE.refl))) →
        starʷ-refl y ok no-η
      (inj₂ (η , _)) →
        ⊥-elim (no-η η)
  transConv↓Term (ℕ-ins t~u) u≡v =
    case inv-[conv↓]∷-ℕ u≡v of λ where
      (inj₁ u~v) →
        ℕ-ins (trans~↓ t~u u~v .proj₁)
      (inj₂ (inj₁ (PE.refl , _))) →
        ⊥-elim $ ¬-Neutral-zero $ ne⁻ $ ne~↓ t~u .proj₂ .proj₂
      (inj₂ (inj₂ (_ , _ , PE.refl , _))) →
        ⊥-elim $ ¬-Neutral-suc $ ne⁻ $ ne~↓ t~u .proj₂ .proj₂
  transConv↓Term (zero-refl _) u≡v =
    case inv-[conv↓]∷-ℕ u≡v of λ where
      (inj₁ u~v) →
        ⊥-elim $ ¬-Neutral-zero $ ne⁻ $ ne~↓ u~v .proj₂ .proj₁
      (inj₂ (inj₁ (_ , PE.refl))) →
        u≡v
      (inj₂ (inj₂ (_ , _ , () , _)))
  transConv↓Term (suc-cong t≡u) u≡v =
    case inv-[conv↓]∷-ℕ u≡v of λ where
      (inj₁ u~v) →
        ⊥-elim $ ¬-Neutral-suc $ ne⁻ $ ne~↓ u~v .proj₂ .proj₁
      (inj₂ (inj₁ (() , _)))
      (inj₂ (inj₂ (_ , _ , PE.refl , PE.refl , u≡v))) →
        suc-cong (transConvTerm t≡u u≡v)
  transConv↓Term (Id-ins ⊢t t~u) u≡v =
    case inv-[conv↓]∷-Id u≡v of λ where
      (inj₁ (_ , _ , _ , u~v)) →
        Id-ins ⊢t (trans~↓ t~u u~v .proj₁)
      (inj₂ (PE.refl , _)) →
        ⊥-elim $ ¬-Neutral-rfl $ ne⁻ $ ne~↓ t~u .proj₂ .proj₂
  transConv↓Term t≡u@(rfl-refl _) u≡v =
    case inv-[conv↓]∷-Id u≡v of λ where
      (inj₁ (_ , _ , _ , u~v)) →
        ⊥-elim $ ¬-Neutral-rfl $ ne⁻ $ ne~↓ u~v .proj₂ .proj₁
      (inj₂ (_ , PE.refl , _)) →
        t≡u

  -- Transitivity of _⊢_[conv↑]_∷_.
  transConvTerm :
    Γ ⊢ t [conv↑] u ∷ A →
    Γ ⊢ u [conv↑] v ∷ A →
    Γ ⊢ t [conv↑] v ∷ A
  transConvTerm t<>u u<>v =
    let t≡u = soundnessConv↑Term t<>u
        ⊢A , _ , _ = syntacticEqTerm t≡u
    in  transConv↑Term (refl ⊢A) t<>u u<>v

  -- Transitivity for _⊢_[conv↑]_∷Level.
  transConvLevel :
    Γ ⊢ l₁ [conv↑] l₂ ∷Level →
    Γ ⊢ l₂ [conv↑] l₃ ∷Level →
    Γ ⊢ l₁ [conv↑] l₃ ∷Level
  transConvLevel (term ok l₁≡l₂) (term _ l₂≡l₃) =
    term ok (transConvTerm l₁≡l₂ l₂≡l₃)
  transConvLevel (term ok _) (literal not-ok _ _ _) =
    ⊥-elim (not-ok ok)
  transConvLevel (literal not-ok _ _ _) (term ok _) =
    ⊥-elim (not-ok ok)
  transConvLevel (literal! not-ok ⊢Γ l-lit) (literal! _ _ _) =
    literal! not-ok ⊢Γ l-lit

  -- Transitivity of algorithmic equality of levels.

  transConv↓Level :
    Γ ⊢ t [conv↓] u ∷Level →
    Γ ⊢ u [conv↓] v ∷Level →
    Γ ⊢ t [conv↓] v ∷Level
  transConv↓Level ([↓]ˡ tᵛ uᵛ t≡ u≡ t≡u) ([↓]ˡ uᵛ′ vᵛ u≡′ v≡ u≡v) =
    [↓]ˡ tᵛ vᵛ t≡ v≡ (trans-≡ᵛ t≡u (trans-≡≡ᵛ-≡ᵛ (deterministic-↓ᵛ u≡ u≡′) u≡v))

  trans-≡ⁿ : ∀ {t u v : Term n} → ≡ⁿ Γ t u false → ≡ⁿ Γ u v false → ≡ⁿ Γ t v false
  trans-≡ⁿ (ne≡ x) (ne≡ y) = ne≡ (trans~↓ x y .proj₁)

  trans-≤ᵃ : ∀ {t u v : LevelAtom Γ} → ≤ᵃ false t u → ≤ᵃ false u v → ≤ᵃ false t v
  trans-≤ᵃ zeroᵘ≤ u≤v = zeroᵘ≤
  trans-≤ᵃ (ne≤ t~u) (ne≤ u~v) = ne≤ (trans-≡ⁿ t~u u~v)

  trans-≤⁺ : ∀ {t u v : Level⁺ Γ} → ≤⁺ false t u → ≤⁺ false u v → ≤⁺ false t v
  trans-≤⁺ (n≤m , t≤u) (m≤o , u≤v) = ≤-trans n≤m m≤o , trans-≤ᵃ t≤u u≤v

  trans-≤⁺-≤⁺ᵛ : ∀ {t u : Level⁺ Γ} {v : Levelᵛ Γ} → ≤⁺ false t u → ≤⁺ᵛ false u v → ≤⁺ᵛ false t v
  trans-≤⁺-≤⁺ᵛ t≤u (Any.here px) = Any.here (trans-≤⁺ t≤u px)
  trans-≤⁺-≤⁺ᵛ t≤u (Any.there u≤v) = Any.there (trans-≤⁺-≤⁺ᵛ t≤u u≤v)

  trans-≤⁺ᵛ-≤ᵛ : ∀ {t : Level⁺ Γ} {u v : Levelᵛ Γ} → ≤⁺ᵛ false t u → ≤ᵛ false u v → ≤⁺ᵛ false t v
  trans-≤⁺ᵛ-≤ᵛ (Any.here px) (px₁ All.∷ u≤v) = trans-≤⁺-≤⁺ᵛ px px₁
  trans-≤⁺ᵛ-≤ᵛ (Any.there t≤u) (px All.∷ u≤v) = trans-≤⁺ᵛ-≤ᵛ t≤u u≤v

  trans-≤ᵛ : ∀ {t u v : Levelᵛ Γ} → ≤ᵛ false t u → ≤ᵛ false u v → ≤ᵛ false t v
  trans-≤ᵛ All.[] u≤v = All.[]
  trans-≤ᵛ (px All.∷ t≤u) u≤v = trans-≤⁺ᵛ-≤ᵛ px u≤v All.∷ trans-≤ᵛ t≤u u≤v

  trans'-≡ⁿ : ∀ {t u v : Term n} → ≡ⁿ Γ t u true → ≡ⁿ Γ u v true → ≡ⁿ Γ t v true
  trans'-≡ⁿ (ne≡' x) (ne≡' y) = ne≡' (trans~↓ y x .proj₁)

  trans'-≤ᵃ : ∀ {t u v : LevelAtom Γ} → ≤ᵃ true t u → ≤ᵃ true u v → ≤ᵃ true t v
  trans'-≤ᵃ zeroᵘ≤ u≤v = zeroᵘ≤
  trans'-≤ᵃ (ne≤ t~u) (ne≤ u~v) = ne≤ (trans'-≡ⁿ t~u u~v)

  trans'-≤⁺ : ∀ {t u v : Level⁺ Γ} → ≤⁺ true t u → ≤⁺ true u v → ≤⁺ true t v
  trans'-≤⁺ (n≤m , t≤u) (m≤o , u≤v) = ≤-trans n≤m m≤o , trans'-≤ᵃ t≤u u≤v

  trans'-≤⁺-≤⁺ᵛ : ∀ {t u : Level⁺ Γ} {v : Levelᵛ Γ} → ≤⁺ true t u → ≤⁺ᵛ true u v → ≤⁺ᵛ true t v
  trans'-≤⁺-≤⁺ᵛ t≤u (Any.here px) = Any.here (trans'-≤⁺ t≤u px)
  trans'-≤⁺-≤⁺ᵛ t≤u (Any.there u≤v) = Any.there (trans'-≤⁺-≤⁺ᵛ t≤u u≤v)

  trans'-≤⁺ᵛ-≤ᵛ : ∀ {t : Level⁺ Γ} {u v : Levelᵛ Γ} → ≤⁺ᵛ true t u → ≤ᵛ true u v → ≤⁺ᵛ true t v
  trans'-≤⁺ᵛ-≤ᵛ (Any.here px) (px₁ All.∷ u≤v) = trans'-≤⁺-≤⁺ᵛ px px₁
  trans'-≤⁺ᵛ-≤ᵛ (Any.there t≤u) (px All.∷ u≤v) = trans'-≤⁺ᵛ-≤ᵛ t≤u u≤v

  trans'-≤ᵛ : ∀ {t u v : Levelᵛ Γ} → ≤ᵛ true t u → ≤ᵛ true u v → ≤ᵛ true t v
  trans'-≤ᵛ All.[] u≤v = All.[]
  trans'-≤ᵛ (px All.∷ t≤u) u≤v = trans'-≤⁺ᵛ-≤ᵛ px u≤v All.∷ trans'-≤ᵛ t≤u u≤v

  trans-≡ᵛ : ∀ {t u v : Levelᵛ Γ} → t ≡ᵛ u → u ≡ᵛ v → t ≡ᵛ v
  trans-≡ᵛ (t≤u , u≤t) (u≤v , v≤u) = trans-≤ᵛ t≤u u≤v , trans'-≤ᵛ v≤u u≤t

-- Transitivity of algorithmic equality of types of the same context.
transConv : ∀ {A B C}
          → Γ ⊢ A [conv↑] B
          → Γ ⊢ B [conv↑] C
          → Γ ⊢ A [conv↑] C
transConv A<>B B<>C = transConv↑ A<>B B<>C
