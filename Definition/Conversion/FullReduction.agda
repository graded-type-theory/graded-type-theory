------------------------------------------------------------------------
-- Every well-typed term has an η-long normal form (in the absence of
-- equality reflection)
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Conversion.FullReduction
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  ⦃ no-equality-reflection : No-equality-reflection ⦄
  where

open import Definition.Conversion R
open import Definition.Conversion.Consequences.Completeness R
open import Definition.Conversion.Consequences.InverseUniv R
open import Definition.Conversion.Whnf R
open import Definition.Typed R
open import Definition.Typed.Consequences.Admissible.Pi R
open import Definition.Typed.Consequences.NeTypeEq R
open import Definition.Typed.EqRelInstance R using (eqRelInstance)
open import Definition.Typed.EqualityRelation.Instance R
open import Definition.Typed.Eta-long-normal-form R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Stability R
open import Definition.Typed.Substitution R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Well-formed R
open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant

open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  Γ    : Con Term _
  A A′ : Term _
  t t′ : Term _
  s    : Strength

mutual

  -- Some lemmas used to prove the main theorems below.

  fullRedNe :
    Γ ⊢ t ~ t′ ↑ A →
    ∃ λ u → Γ ⊢ne u ∷ A × Γ ⊢ t ≡ u ∷ A
  fullRedNe {Γ = Γ} = λ where
    (var-refl {x = x} ⊢x _) →
      case inversion-var ⊢x of λ {
        (_ , x∈ , A≡B) →
        var x
      , convₙ (varₙ (wfEq A≡B) x∈) (sym A≡B)
      , refl ⊢x }
    (lower-cong t~) →
      case fullRedNe~↓ t~ of λ
        (t′ , t′-ne , t≡t′) →
      case inversion-Lift (syntacticEqTerm t≡t′ .proj₁) of λ
        (⊢k , ⊢A) →
      lower t′ , lowerₙ t′-ne , lower-cong t≡t′
    (app-cong {u₁ = u} {B} t~ u↑) →
      case fullRedNe~↓ t~ of λ {
        (t′ , t′-ne , t≡t′) →
      case fullRedTermConv↑ u↑ of λ {
        (u′ , u′-nf , u≡u′) →
      case inversion-ΠΣ (syntacticEqTerm t≡t′ .proj₁) of λ {
        (_ , ⊢B , _) →
        t′ ∘ u′
      , (                           $⟨ ∘ₙ t′-ne u′-nf ⟩
         Γ ⊢ne t′ ∘ u′ ∷ B [ u′ ]₀  →⟨ flip convₙ $
                                       substTypeEq (refl ⊢B) (sym′ u≡u′) ⟩
         Γ ⊢ne t′ ∘ u′ ∷ B [ u ]₀   □)
      , app-cong t≡t′ u≡u′ }}}
    (fst-cong {p = p} t~) →
      case fullRedNe~↓ t~ of λ {
        (t′ , t′-ne , t≡t′) →
      case inversion-ΠΣ (syntacticEqTerm t≡t′ .proj₁) of λ {
        (_ , ⊢B , _) →
        fst p t′
      , fstₙ ⊢B t′-ne
      , fst-cong ⊢B t≡t′ }}
    (snd-cong {t₁ = t} {p} {B} t~) →
      case fullRedNe~↓ t~ of λ {
        (t′ , t′-ne , t≡t′) →
      case inversion-ΠΣ (syntacticEqTerm t≡t′ .proj₁) of λ {
        (_ , ⊢B , _) →
        snd p t′
      , (                                  $⟨ sndₙ ⊢B t′-ne ⟩
         Γ ⊢ne snd p t′ ∷ B [ fst p t′ ]₀  →⟨ flip _⊢ne_∷_.convₙ $
                                              substTypeEq (refl ⊢B) (fst-cong ⊢B (sym′ t≡t′)) ⟩
         Γ ⊢ne snd p t′ ∷ B [ fst p t ]₀   □)
      , snd-cong ⊢B t≡t′ }}
    (natrec-cong {A₁ = A} {v₁ = v} {p} {q} {r} A↑ t↑ u↑ v~) →
      case fullRedConv↑ A↑ of λ {
        (A′ , A′-nf , A≡A′) →
      case fullRedTermConv↑ t↑ of λ {
        (t′ , t′-nf , t≡t′) →
      case fullRedTermConv↑ u↑ of λ {
        (u′ , u′-nf , u≡u′) →
      case fullRedNe~↓ v~ of λ {
        (v′ , v′-ne , v≡v′) →
      case syntacticEq A≡A′ of λ {
        (_ , ⊢A′) →
      case wfEqTerm v≡v′ of λ {
        ⊢Γ →
        natrec p q r A′ t′ u′ v′
      , (                                             $⟨ u′-nf ⟩
         Γ ∙ ℕ ∙ A ⊢nf u′ ∷ A [ suc (var x1) ]↑²      →⟨ ⊢nf∷-stable (refl-∙ A≡A′) ⟩
         Γ ∙ ℕ ∙ A′ ⊢nf u′ ∷ A [ suc (var x1) ]↑²     →⟨ flip _⊢nf_∷_.convₙ $
                                                         subst↑²TypeEq A≡A′ (refl (sucⱼ (var₁ ⊢A′))) ⟩
         Γ ∙ ℕ ∙ A′ ⊢nf u′ ∷ A′ [ suc (var x1) ]↑²    →⟨ (λ hyp → natrecₙ
                                                            A′-nf
                                                            (convₙ t′-nf (substTypeEq A≡A′ (refl (zeroⱼ ⊢Γ))))
                                                            hyp
                                                            v′-ne) ⟩
         Γ ⊢ne natrec p q r A′ t′ u′ v′ ∷ A′ [ v′ ]₀  →⟨ flip _⊢ne_∷_.convₙ $ _⊢_≡_.sym $
                                                         substTypeEq A≡A′ v≡v′ ⟩
         Γ ⊢ne natrec p q r A′ t′ u′ v′ ∷ A [ v ]₀    □)
      , natrec-cong A≡A′ t≡t′ u≡u′ v≡v′ }}}}}}
    (prodrec-cong
       {p = p} {F = A} {G = B} {C = C} {g = u} {r = r} {q′ = q}
       C↑ u~ v↑) →
      case fullRedConv↑ C↑ of λ {
        (C′ , C′-nf , C≡C′) →
      case fullRedNe~↓ u~ of λ {
        (u′ , u′-ne , u≡u′) →
      case fullRedTermConv↑ v↑ of λ {
        (v′ , v′-nf , v≡v′) →
      case inversion-ΠΣ (syntacticEqTerm u≡u′ .proj₁) of λ {
        (_ , _ , ok) →
        prodrec r p q C′ u′ v′
      , (                                                       $⟨ v′-nf ⟩
         Γ ∙ A ∙ B ⊢nf v′ ∷ C [ prodʷ p (var x1) (var x0) ]↑²   →⟨ flip _⊢nf_∷_.convₙ $
                                                                   subst↑²TypeEq-prod C≡C′ ⟩
         Γ ∙ A ∙ B ⊢nf v′ ∷ C′ [ prodʷ p (var x1) (var x0) ]↑²  →⟨ flip (prodrecₙ C′-nf u′-ne) ok ⟩
         Γ ⊢ne prodrec r p q C′ u′ v′ ∷ C′ [ u′ ]₀              →⟨ flip _⊢ne_∷_.convₙ $ _⊢_≡_.sym $
                                                                   substTypeEq C≡C′ u≡u′ ⟩
         Γ ⊢ne prodrec r p q C′ u′ v′ ∷ C [ u ]₀                □)
      , prodrec-cong C≡C′ u≡u′ v≡v′ ok }}}}
    (emptyrec-cong {A₁ = A} {p} A↑ t~) →
      case fullRedConv↑ A↑ of λ {
        (A′ , A′-nf , A≡A′) →
      case fullRedNe~↓ t~ of λ {
        (t′ , t′-ne , t≡t′) →
        emptyrec p A′ t′
      , (                             $⟨ emptyrecₙ A′-nf t′-ne ⟩
         Γ ⊢ne emptyrec p A′ t′ ∷ A′  →⟨ flip _⊢ne_∷_.convₙ (sym A≡A′) ⟩
         Γ ⊢ne emptyrec p A′ t′ ∷ A   □)
      , emptyrec-cong A≡A′ t≡t′ }}
    (unitrec-cong {A₁ = A} {t₁ = t} A↑ t∷ u↑ no-η) →
      case fullRedConv↑ A↑ of λ {
        (A′ , A′-nf , A≡A′) →
      case fullRedNe~∷ t∷ of λ {
        (t′ , t′-ne , t≡t′) →
      case fullRedTermConv↑ u↑ of λ {
        (u′ , u′-nf , u≡u′) →
      case inversion-Unit (syntacticEqTerm t≡t′ .proj₁) of λ {
        ok →
        unitrec _ _ A′ t′ u′
      , (                                           $⟨ u′-nf ⟩
         Γ ⊢nf u′ ∷ A [ starʷ ]₀                  →⟨ flip _⊢nf_∷_.convₙ $
                                                       substTypeEq A≡A′ (refl (starⱼ (wfEqTerm t≡t′) ok)) ⟩
         Γ ⊢nf u′ ∷ A′ [ starʷ ]₀                 →⟨ (λ ⊢u′ → unitrecₙ A′-nf t′-ne ⊢u′ ok no-η) ⟩
         Γ ⊢ne unitrec _ _ A′ t′ u′ ∷ A′ [ t′ ]₀  →⟨ flip _⊢ne_∷_.convₙ $ _⊢_≡_.sym $
                                                       substTypeEq A≡A′ t≡t′ ⟩
         Γ ⊢ne unitrec _ _ A′ t′ u′ ∷ A [ t ]₀    □)
      , unitrec-cong′ A≡A′ t≡t′ u≡u′ }}}}
    (J-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁~w₂ C≡Id-t₁-v₁) →
      case fullRedConv↑ A₁≡A₂ of λ {
        (A₁′ , ⊢A₁′ , A₁≡A₁′) →
      case fullRedTermConv↑ t₁≡t₂ of λ {
        (t₁′ , ⊢t₁′ , t₁≡t₁′) →
      case fullRedConv↑ B₁≡B₂ of λ {
        (B₁′ , ⊢B₁′ , B₁≡B₁′) →
      case fullRedTermConv↑ u₁≡u₂ of λ {
        (u₁′ , ⊢u₁′ , u₁≡u₁′) →
      case fullRedTermConv↑ v₁≡v₂ of λ {
        (v₁′ , ⊢v₁′ , v₁≡v₁′) →
      case fullRedNe~↓ w₁~w₂ of λ {
        (w₁′ , ⊢w₁′ , w₁≡w₁′) →
      case conv w₁≡w₁′ C≡Id-t₁-v₁ of λ {
        w₁≡w₁′ →
        J _ _ A₁′ t₁′ B₁′ u₁′ v₁′ w₁′
      , convₙ
          (Jₙ ⊢A₁′ (convₙ ⊢t₁′ A₁≡A₁′)
             (⊢nf-stable (J-motive-context-cong′ A₁≡A₁′ t₁≡t₁′) ⊢B₁′)
             (convₙ ⊢u₁′ (J-motive-rfl-cong B₁≡B₁′ t₁≡t₁′))
             (convₙ ⊢v₁′ A₁≡A₁′)
             (convₙ ⊢w₁′
                (trans C≡Id-t₁-v₁ (Id-cong A₁≡A₁′ t₁≡t₁′ v₁≡v₁′))))
          (sym (J-result-cong B₁≡B₁′ v₁≡v₁′ w₁≡w₁′))
      , J-cong′ A₁≡A₁′ t₁≡t₁′ B₁≡B₁′ u₁≡u₁′ v₁≡v₁′ w₁≡w₁′ }}}}}}}
    (K-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁~v₂ C≡Id-t₁-t₁ ok) →
      case fullRedConv↑ A₁≡A₂ of λ {
        (A₁′ , ⊢A₁′ , A₁≡A₁′) →
      case fullRedTermConv↑ t₁≡t₂ of λ {
        (t₁′ , ⊢t₁′ , t₁≡t₁′) →
      case fullRedConv↑ B₁≡B₂ of λ {
        (B₁′ , ⊢B₁′ , B₁≡B₁′) →
      case fullRedTermConv↑ u₁≡u₂ of λ {
        (u₁′ , ⊢u₁′ , u₁≡u₁′) →
      case fullRedNe~↓ v₁~v₂ of λ {
        (v₁′ , ⊢v₁′ , v₁≡v₁′) →
      case conv v₁≡v₁′ C≡Id-t₁-t₁ of λ {
        v₁≡v₁′ →
        K _ A₁′ t₁′ B₁′ u₁′ v₁′
      , convₙ
          (Kₙ ⊢A₁′ (convₙ ⊢t₁′ A₁≡A₁′)
             (⊢nf-stable (K-motive-context-cong′ A₁≡A₁′ t₁≡t₁′) ⊢B₁′)
             (convₙ ⊢u₁′ (K-motive-rfl-cong B₁≡B₁′))
             (convₙ ⊢v₁′
                (trans C≡Id-t₁-t₁ (Id-cong A₁≡A₁′ t₁≡t₁′ t₁≡t₁′)))
             ok)
          (sym (substTypeEq B₁≡B₁′ v₁≡v₁′))
      , K-cong A₁≡A₁′ t₁≡t₁′ B₁≡B₁′ u₁≡u₁′ v₁≡v₁′ ok }}}}}}
    ([]-cong-cong l₁≡l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁~v₂ B≡Id-t₁-u₁ ok) →
      let l₁′ , ⊢l₁′ , l₁≡l₁′ = fullRedTermConv↑ l₁≡l₂
          A₁′ , ⊢A₁′ , A₁≡A₁′ = fullRedTermConv↑ A₁≡A₂
          t₁′ , ⊢t₁′ , t₁≡t₁′ = fullRedTermConv↑ t₁≡t₂
          u₁′ , ⊢u₁′ , u₁≡u₁′ = fullRedTermConv↑ u₁≡u₂
          v₁′ , ⊢v₁′ , v₁≡v₁′ = fullRedNe~↓ v₁~v₂
          _ , ⊢A₁ , _         = wf-⊢≡∷ A₁≡A₁′
          Erased-ok           = []-cong→Erased ok
      in
      []-cong _ l₁′ A₁′ t₁′ u₁′ v₁′ ,
      convₙ
        ([]-congₙ ⊢l₁′ (convₙ ⊢A₁′ (U-cong l₁≡l₁′))
           (convₙ ⊢t₁′ (univ A₁≡A₁′)) (convₙ ⊢u₁′ (univ A₁≡A₁′))
           (convₙ ⊢v₁′
              (trans B≡Id-t₁-u₁ (Id-cong (univ A₁≡A₁′) t₁≡t₁′ u₁≡u₁′)))
           ok)
        (_⊢_≡_.sym $
         Id-cong (Erased-cong Erased-ok l₁≡l₁′ A₁≡A₁′)
           ([]-cong′ Erased-ok ⊢A₁ t₁≡t₁′)
           ([]-cong′ Erased-ok ⊢A₁ u₁≡u₁′)) ,
      []-cong-cong l₁≡l₁′ A₁≡A₁′ t₁≡t₁′ u₁≡u₁′ (conv v₁≡v₁′ B≡Id-t₁-u₁)
        ok

  fullRedNe~↓ :
    Γ ⊢ t ~ t′ ↓ A →
    ∃ λ u → Γ ⊢ne u ∷ A × Γ ⊢ t ≡ u ∷ A
  fullRedNe~↓ ([~] _ (D , _) k~l) =
    let u , A-ne , t≡u = fullRedNe k~l
    in  u , convₙ A-ne A≡ , conv t≡u A≡
    where
    A≡ = subset* D

  fullRedNe~∷ :
    Γ ⊢ t ~ t′ ∷ A →
    ∃ λ u → Γ ⊢ne u ∷ A × Γ ⊢ t ≡ u ∷ A
  fullRedNe~∷ (↑ A≡B k~↑l) =
    let u , A-ne , t≡u = fullRedNe k~↑l
    in u , convₙ A-ne (sym A≡B) , conv t≡u (sym A≡B)

  fullRedConv↑ :
    Γ ⊢ A [conv↑] A′ →
    ∃ λ B → Γ ⊢nf B × Γ ⊢ A ≡ B
  fullRedConv↑ ([↑] _ _ (D , _) _ A′<>B′) =
    let B″ , nf , B′≡B″ = fullRedConv↓ A′<>B′
    in  B″ , nf , trans (subset* D) B′≡B″

  fullRedConv↓ :
    Γ ⊢ A [conv↓] A′ →
    ∃ λ B → Γ ⊢nf B × Γ ⊢ A ≡ B
  fullRedConv↓ = λ where
    (Level-refl ⊢Γ) → Level , Levelₙ ⊢Γ , refl (Levelⱼ′ ⊢Γ)
    (U-cong l₁≡l₂) →
      let l , ⊢l , l₁≡l = fullRedTermConv↑ l₁≡l₂
      in U l , Uₙ ⊢l , U-cong l₁≡l
    (Lift-cong l₁≡l₂ A≡B) →
      let l , ⊢l , l₁≡l = fullRedTermConv↑ l₁≡l₂
          C , ⊢C , A≡C = fullRedConv↑ A≡B
      in Lift _ _ , Liftₙ ⊢l ⊢C , Lift-cong l₁≡l A≡C
    (ℕ-refl     ⊢Γ)    → ℕ     , ℕₙ     ⊢Γ , refl (ℕⱼ     ⊢Γ)
    (Empty-refl ⊢Γ)    → Empty , Emptyₙ ⊢Γ , refl (Emptyⱼ ⊢Γ)
    (Unit-refl ⊢Γ ok) →
      Unit! , Unitₙ ⊢Γ ok , refl (Unitⱼ ⊢Γ ok)
    (ne A~) →
      case fullRedNe~↓ A~ of λ {
        (B , B-ne , A≡B) →
      B , univₙ (neₙ Uₙ (neₙ B-ne)) , univ A≡B }
    (ΠΣ-cong A↑ B↑ ok) →
      case fullRedConv↑ A↑ of λ {
        (A′ , A′-nf , A≡A′) →
      case fullRedConv↑ B↑ of λ {
        (B′ , B′-nf , B≡B′) →
      ΠΣ⟨ _ ⟩ _ , _ ▷ A′ ▹ B′ ,
      ΠΣₙ A′-nf (⊢nf-stable (refl-∙ A≡A′) B′-nf) ok ,
      ΠΣ-cong A≡A′ B≡B′ ok }}
    (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) →
      case fullRedConv↑ A₁≡A₂ of λ {
        (A₁′ , ⊢A₁′ , A₁≡A₁′) →
      case fullRedTermConv↑ t₁≡t₂ of λ {
        (t₁′ , ⊢t₁′ , t₁≡t₁′) →
      case fullRedTermConv↑ u₁≡u₂ of λ {
        (u₁′ , ⊢u₁′ , u₁≡u₁′) →
        Id A₁′ t₁′ u₁′
      , Idₙ ⊢A₁′ (convₙ ⊢t₁′ A₁≡A₁′) (convₙ ⊢u₁′ A₁≡A₁′)
      , Id-cong A₁≡A₁′ t₁≡t₁′ u₁≡u₁′ }}}

  fullRedTermConv↑ :
    Γ ⊢ t [conv↑] t′ ∷ A →
    ∃ λ u → Γ ⊢nf u ∷ A × Γ ⊢ t ≡ u ∷ A
  fullRedTermConv↑ ([↑]ₜ _ _ _ (D , _) (d , _) _ t<>u) =
    case fullRedTermConv↓ t<>u of λ {
      (u″ , nf , u′≡u″) →
    u″ ,
    convₙ nf B≡A ,
    conv (trans (subset*Term d) u′≡u″) B≡A }
    where
    B≡A = sym (subset* D)

  fullRedTermConv↑ᵛ :
    ∀ {tᵛ} →
    Γ ⊢ t ↑ᵛ tᵛ →
    ∃ λ u → Γ ⊢nf u ∷ Level × Γ ⊢ t ≡ u ∷ Level
  fullRedTermConv↑ᵛ ([↑]ᵛ (d , _) t↓v) =
    let u , ⊢u , t′≡u = fullRedTermConv↓ᵛ t↓v
    in u , ⊢u , trans (subset*Term d) t′≡u

  fullRedTermConv↓ᵛ :
    ∀ {tᵛ} →
    Γ ⊢ t ↓ᵛ tᵛ →
    ∃ λ u → Γ ⊢nf u ∷ Level × Γ ⊢ t ≡ u ∷ Level
  fullRedTermConv↓ᵛ (zeroᵘₙ ⊢Γ) =
    zeroᵘ , zeroᵘₙ ⊢Γ , refl (zeroᵘⱼ ⊢Γ)
  fullRedTermConv↓ᵛ (sucᵘₙ PE.refl t↑) =
    let t′ , ⊢t′ , t≡t′ = fullRedTermConv↑ᵛ t↑
    in _ , sucᵘₙ ⊢t′ , sucᵘ-cong t≡t′
  fullRedTermConv↓ᵛ (neₙ x) =
    let u , ⊢u , t≡u = fullRedTermConv~ᵛ x
    in _ , neₙ Levelₙ ⊢u , t≡u

  fullRedTermConv~ᵛ :
    ∀ {tᵛ} →
    Γ ⊢ t ~ᵛ tᵛ →
    ∃ λ u → Γ ⊢neˡ u ∷ Level × Γ ⊢ t ≡ u ∷ Level
  fullRedTermConv~ᵛ (supᵘˡₙ x t~ u↑) =
    let t′ , ⊢t′ , t≡t′ = fullRedTermConv~ᵛ t~
        u′ , ⊢u′ , u≡u′ = fullRedTermConv↑ᵛ u↑
    in _ , supᵘˡₙ ⊢t′ ⊢u′ , supᵘ-cong t≡t′ u≡u′
  fullRedTermConv~ᵛ (supᵘʳₙ x t↑ u~) =
    let t′ , ⊢t′ , t≡t′ = fullRedTermConv↑ᵛ t↑
        u′ , ⊢u′ , u≡u′ = fullRedTermConv~ᵛ u~
    in _ , supᵘʳₙ ⊢t′ ⊢u′ , supᵘ-cong (sucᵘ-cong t≡t′) u≡u′
  fullRedTermConv~ᵛ (neₙ [t] x) =
    let u , ⊢u , t≡u = fullRedNe~↓ [t]
    in u , neₙ ⊢u , t≡u

  fullRedTermConv↑Level :
    Γ ⊢ t [conv↑] t′ ∷Level →
    ∃ λ u → Γ ⊢nf u ∷ Level × Γ ⊢ t ≡ u ∷ Level
  fullRedTermConv↑Level ([↑]ˡ tᵛ uᵛ t↑ u↑ t≡u) = fullRedTermConv↑ᵛ t↑

  fullRedTermConv↓Level :
    Γ ⊢ t [conv↓] t′ ∷Level →
    ∃ λ u → Γ ⊢nf u ∷ Level × Γ ⊢ t ≡ u ∷ Level
  fullRedTermConv↓Level ([↓]ˡ tᵛ uᵛ t↓ u↓ t≡u) = fullRedTermConv↓ᵛ t↓

  fullRedTermConv↓ :
    Γ ⊢ t [conv↓] t′ ∷ A →
    ∃ λ u → Γ ⊢nf u ∷ A × Γ ⊢ t ≡ u ∷ A
  fullRedTermConv↓ {Γ = Γ} {t = t} = λ where
    (Level-ins t↓) →
      fullRedTermConv↓Level t↓
    (ℕ-ins t~) →
      case fullRedNe~↓ t~ of λ {
        (u , u-nf , t≡u) →
      u , neₙ ℕₙ (neₙ u-nf) , t≡u }
    (Empty-ins t~) →
      case fullRedNe~↓ t~ of λ {
        (u , u-nf , t≡u) →
      u , neₙ Emptyₙ (neₙ u-nf) , t≡u }
    (Unitʷ-ins no-η t∷) →
      case fullRedNe~∷ t∷ of λ
        (u , u-nf , t≡u) →
      u , neₙ (Unitʷₙ no-η) (neₙ u-nf) , t≡u
    (Σʷ-ins ⊢t∷ΣAB _ t~) →
      case fullRedNe~↓ t~ of λ {
        (v , v-ne , t≡v) →
      case syntacticEqTerm t≡v of λ {
        (_ , ⊢t∷ΣCD , _) →
      case ne~↓ t~ of λ {
        (_ , t-ne , _) →
      case neTypeEq t-ne ⊢t∷ΣCD ⊢t∷ΣAB of λ {
        ΣCD≡ΣAB →
      case inversion-ΠΣ (syntacticTerm ⊢t∷ΣAB) of λ {
        (⊢A , ⊢B) →
        v
      , neₙ Σʷₙ (neₙ (convₙ v-ne ΣCD≡ΣAB))
      , conv t≡v ΣCD≡ΣAB }}}}}
    (ne-ins ⊢t∷A _ A-ne t~↓B) →
      case fullRedNe~↓ t~↓B of λ {
        (u , u-ne , t≡u∷B) →
      case syntacticEqTerm t≡u∷B of λ {
        (_ , ⊢t∷B , _) →
      case ne~↓ t~↓B of λ {
        (_ , t-ne , _) →
      case neTypeEq t-ne ⊢t∷B ⊢t∷A of λ {
        B≡A →
        u
      , neₙ (neₙ A-ne) (neₙ (convₙ u-ne B≡A))
      , conv t≡u∷B B≡A }}}}
    (univ {l} {A} ⊢A _ A↓) →
      case fullRedConv↓ A↓ of λ {
        (B , B-nf , A≡B) →
        B
      , (                 $⟨ A≡B ⟩
         (Γ ⊢ A ≡ B)      →⟨ inverseUnivEq ⊢A ⟩
         Γ ⊢ A ≡ B ∷ U l  →⟨ (λ hyp → syntacticEqTerm hyp .proj₂ .proj₂) ⟩
         Γ ⊢ B ∷ U l      →⟨ ⊢nf∷U→⊢nf∷U B-nf ⟩
         Γ ⊢nf B ∷ U l    □)
      , inverseUnivEq ⊢A A≡B }
    (zero-refl ⊢Γ) →
      zero , zeroₙ ⊢Γ , refl (zeroⱼ ⊢Γ)
    (starʷ-refl ⊢Γ ok _) →
        starʷ
      , starₙ ⊢Γ ok
      , refl (starⱼ ⊢Γ ok)
    (suc-cong t↑) →
      case fullRedTermConv↑ t↑ of λ {
        (u , u-nf , t≡u) →
      suc u , sucₙ u-nf , suc-cong t≡u }
    (prod-cong {p} {q} {F = A} {G = B} {t} ⊢B t↑ u↑ ok) →
      case fullRedTermConv↑ t↑ of λ {
        (t′ , t′-nf , t≡t′) →
      case fullRedTermConv↑ u↑ of λ {
        (u′ , u′-nf , u≡u′) →
        prod! t′ u′
      , (                                      $⟨ u′-nf ⟩
         Γ ⊢nf u′ ∷ B [ t ]₀                   →⟨ flip _⊢nf_∷_.convₙ $
                                                  substTypeEq (refl ⊢B) t≡t′ ⟩
         Γ ⊢nf u′ ∷ B [ t′ ]₀                  →⟨ flip (_⊢nf_∷_.prodₙ ⊢B t′-nf) ok ⟩
         Γ ⊢nf prod! t′ u′ ∷ Σʷ p , q ▷ A ▹ B  □)
      , prod-cong ⊢B t≡t′ u≡u′ ok }}
    (η-eq {p = p} {q = q} {f = t} {F = A} {G = B} ⊢t _ _ _ t0≡u0) →
      case fullRedTermConv↑ t0≡u0 of λ {
        (u , u-nf , t0≡u) →
      case ⊢∷ΠΣ→ΠΣ-allowed ⊢t of λ {
        ok →
        lam p u
      , lamₙ u-nf ok
      , (                                                       $⟨ sym′ (Π-η ⊢t) ⟩
         Γ ⊢ t ≡ lam p (wk1 t ∘⟨ p ⟩ var x0) ∷ Π p , q ▷ A ▹ B  →⟨ flip _⊢_≡_∷_.trans (lam-cong t0≡u ok) ⟩
         Γ ⊢ t ≡ lam p u ∷ Π p , q ▷ A ▹ B                      □) }}
    (Lift-η ⊢t ⊢u wt wu lower≡lower) →
      case inversion-Lift (syntacticTerm ⊢t) of λ
        (⊢l , ⊢A) →
      case fullRedTermConv↑ lower≡lower of λ
        (t′ , t′-nf , lowert≡t′) →
      let ⊢t′ = (⊢nf∷→⊢∷ t′-nf)
      in lift t′
      , liftₙ ⊢l t′-nf
      , Lift-η-swap ⊢t lowert≡t′
    (Σ-η {p} {q} {A} {B} ⊢t _ _ _ fst-t↑ snd-t↑) →
      case inversion-ΠΣ (syntacticTerm ⊢t) of λ {
        (_ , ⊢B , ok) →
      case fullRedTermConv↑ fst-t↑ of λ {
        (u₁ , u₁-nf , fst-t≡u₁) →
      case fullRedTermConv↑ snd-t↑ of λ {
        (u₂ , u₂-nf , snd-t≡u₂) →
        prodˢ p u₁ u₂
      , (                                        $⟨ u₂-nf ⟩
         Γ ⊢nf u₂ ∷ B [ fst p t ]₀               →⟨ flip _⊢nf_∷_.convₙ $
                                                    substTypeEq (refl ⊢B) fst-t≡u₁ ⟩
         Γ ⊢nf u₂ ∷ B [ u₁ ]₀                    →⟨ flip (prodₙ ⊢B u₁-nf) ok ⟩
         Γ ⊢nf prodˢ p u₁ u₂ ∷ Σˢ p , q ▷ A ▹ B  □)
      , (                                                        $⟨ sym′ (Σ-η-prod-fst-snd ⊢t) ⟩
         Γ ⊢ t ≡ prodˢ p (fst p t) (snd p t) ∷ Σˢ p , q ▷ A ▹ B  →⟨ flip _⊢_≡_∷_.trans $
                                                                    prod-cong ⊢B fst-t≡u₁ snd-t≡u₂ ok ⟩
         Γ ⊢ t ≡ prodˢ p u₁ u₂ ∷ Σˢ p , q ▷ A ▹ B                □) }}}
    (η-unit ⊢t _ _ _ _ ok) →
      case wfTerm ⊢t of λ {
        ⊢Γ →
      case ⊢∷Unit→Unit-allowed ⊢t of λ {
        Unit-ok →
        star!
      , starₙ ⊢Γ Unit-ok
      , η-unit ⊢t (starⱼ ⊢Γ Unit-ok) Unit-ok ok }}
    (Id-ins ⊢t t~u) →
      case fullRedNe~↓ t~u of λ {
        (v , ⊢v , t≡v) →
      case neTypeEq (ne~↓ t~u .proj₂ .proj₁)
             (syntacticEqTerm t≡v .proj₂ .proj₁) ⊢t of λ {
        Id≡Id →
        v
      , neₙ Idₙ (neₙ (convₙ ⊢v Id≡Id))
      , conv t≡v Id≡Id }}
    (rfl-refl t≡u) →
      case syntacticEqTerm t≡u of λ {
        (⊢A , ⊢t , _) →
        rfl
      , convₙ (rflₙ ⊢t) (Id-cong (refl ⊢A) (refl ⊢t) t≡u)
      , refl (rflⱼ′ t≡u) }

-- If A is a well-formed type, then A is definitionally equal to a
-- type in η-long normal form.

fullRed : Γ ⊢ A → ∃ λ B → Γ ⊢nf B × Γ ⊢ A ≡ B
fullRed ⊢A = fullRedConv↑ (completeEq (refl ⊢A))

-- If t is a well-typed term, then t is definitionally equal to a term
-- in η-long normal form.

fullRedTerm : Γ ⊢ t ∷ A → ∃ λ u → Γ ⊢nf u ∷ A × Γ ⊢ t ≡ u ∷ A
fullRedTerm ⊢t = fullRedTermConv↑ (completeEqTerm (refl ⊢t))
