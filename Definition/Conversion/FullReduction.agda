------------------------------------------------------------------------
-- Every well-typed term has an η-long normal form
------------------------------------------------------------------------

open import Definition.Typed.Restrictions

module Definition.Conversion.FullReduction
  {a} {M : Set a}
  (R : Type-restrictions M)
  where

open import Definition.Conversion R
open import Definition.Conversion.Consequences.Completeness R
open import Definition.Conversion.Soundness R
open import Definition.Conversion.Whnf R
open import Definition.Typed R
open import Definition.Typed.Consequences.DerivedRules R
open import Definition.Typed.Consequences.InverseUniv R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.NeTypeEq R
open import Definition.Typed.Consequences.Stability R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Eta-long-normal-form R
open import Definition.Typed.Properties R
open import Definition.Untyped M hiding (_∷_)

open import Tools.Fin
open import Tools.Function
open import Tools.Product

private variable
  Γ    : Con Term _
  A A′ : Term _
  t t′ : Term _

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
    (app-cong {G = B} {t = u} t~ u↑) →
      case fullRedNe~↓ t~ of λ {
        (t′ , t′-ne , t≡t′) →
      case fullRedTermConv↑ u↑ of λ {
        (u′ , u′-nf , u≡u′) →
      case inversion-ΠΣ (syntacticEqTerm t≡t′ .proj₁) of λ {
        (_ , ⊢B , _) →
        t′ ∘ u′
      , (                           $⟨ ∘ₙ t′-ne u′-nf ⟩
         Γ ⊢ne t′ ∘ u′ ∷ B [ u′ ]₀  →⟨ flip convₙ $
                                      substTypeEq (refl ⊢B) (sym u≡u′) ⟩
         Γ ⊢ne t′ ∘ u′ ∷ B [ u ]₀   □)
      , app-cong t≡t′ u≡u′ }}}
    (fst-cong {p = p} t~) →
      case fullRedNe~↓ t~ of λ {
        (t′ , t′-ne , t≡t′) →
      case inversion-ΠΣ (syntacticEqTerm t≡t′ .proj₁) of λ {
        (⊢A , ⊢B , _) →
        fst p t′
      , fstₙ ⊢A ⊢B t′-ne
      , fst-cong ⊢A ⊢B t≡t′ }}
    (snd-cong {k = t} {p = p} {G = B} t~) →
      case fullRedNe~↓ t~ of λ {
        (t′ , t′-ne , t≡t′) →
      case inversion-ΠΣ (syntacticEqTerm t≡t′ .proj₁) of λ {
        (⊢A , ⊢B , _) →
        snd p t′
      , (                                  $⟨ sndₙ ⊢A ⊢B t′-ne ⟩
         Γ ⊢ne snd p t′ ∷ B [ fst p t′ ]₀  →⟨ flip _⊢ne_∷_.convₙ $
                                             substTypeEq (refl ⊢B) (fst-cong ⊢A ⊢B (sym t≡t′)) ⟩
         Γ ⊢ne snd p t′ ∷ B [ fst p t ]₀   □)
      , snd-cong ⊢A ⊢B t≡t′ }}
    (natrec-cong {F = A} {k = v} {p = p} {q = q} {r = r} A↑ t↑ u↑ v~) →
      case fullRedConv↑ A↑ of λ {
        (A′ , A′-nf , A≡A′) →
      case fullRedTermConv↑ t↑ of λ {
        (t′ , t′-nf , t≡t′) →
      case fullRedTermConv↑ u↑ of λ {
        (u′ , u′-nf , u≡u′) →
      case fullRedNe~↓ v~ of λ {
        (v′ , v′-ne , v≡v′) →
      case syntacticEq A≡A′ of λ {
        (⊢A , ⊢A′) →
      case wfEqTerm v≡v′ of λ {
        ⊢Γ →
      case ⊢Γ ∙ ℕⱼ ⊢Γ of λ {
        ⊢Γℕ →
        natrec p q r A′ t′ u′ v′
      , (                                             $⟨ u′-nf ⟩
         Γ ∙ ℕ ∙ A ⊢nf u′ ∷ A [ suc (var x1) ]↑²      →⟨ ⊢nf∷-stable (reflConEq ⊢Γℕ ∙ A≡A′) ⟩
         Γ ∙ ℕ ∙ A′ ⊢nf u′ ∷ A [ suc (var x1) ]↑²     →⟨ flip _⊢nf_∷_.convₙ $
                                                         subst↑²TypeEq (ℕⱼ ⊢Γ) ⊢A′ A≡A′
                                                           (refl (sucⱼ (var (⊢Γℕ ∙ ⊢A′) (there here)))) ⟩
         Γ ∙ ℕ ∙ A′ ⊢nf u′ ∷ A′ [ suc (var x1) ]↑²    →⟨ (λ hyp → natrecₙ
                                                            A′-nf
                                                            (convₙ t′-nf (substTypeEq A≡A′ (refl (zeroⱼ ⊢Γ))))
                                                            hyp
                                                            v′-ne) ⟩
         Γ ⊢ne natrec p q r A′ t′ u′ v′ ∷ A′ [ v′ ]₀  →⟨ flip _⊢ne_∷_.convₙ $ _⊢_≡_.sym $
                                                         substTypeEq A≡A′ v≡v′ ⟩
         Γ ⊢ne natrec p q r A′ t′ u′ v′ ∷ A [ v ]₀    □)
      , natrec-cong ⊢A A≡A′ t≡t′ u≡u′ v≡v′ }}}}}}}
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
        (⊢A , ⊢B , ok) →
        prodrec r p q C′ u′ v′
      , (                                                       $⟨ v′-nf ⟩
         Γ ∙ A ∙ B ⊢nf v′ ∷ C [ prodᵣ p (var x1) (var x0) ]↑²   →⟨ flip _⊢nf_∷_.convₙ $
                                                                   subst↑²TypeEq-prod C≡C′ ok ⟩
         Γ ∙ A ∙ B ⊢nf v′ ∷ C′ [ prodᵣ p (var x1) (var x0) ]↑²  →⟨ flip (prodrecₙ ⊢A ⊢B C′-nf u′-ne) ok ⟩
         Γ ⊢ne prodrec r p q C′ u′ v′ ∷ C′ [ u′ ]₀              →⟨ flip _⊢ne_∷_.convₙ $ _⊢_≡_.sym $
                                                                   substTypeEq C≡C′ u≡u′ ⟩
         Γ ⊢ne prodrec r p q C′ u′ v′ ∷ C [ u ]₀                □)
      , prodrec-cong ⊢A ⊢B C≡C′ u≡u′ v≡v′ ok }}}}
    (Emptyrec-cong {F = A} {p = p} A↑ t~) →
      case fullRedConv↑ A↑ of λ {
        (A′ , A′-nf , A≡A′) →
      case fullRedNe~↓ t~ of λ {
        (t′ , t′-ne , t≡t′) →
        Emptyrec p A′ t′
      , (                             $⟨ Emptyrecₙ A′-nf t′-ne ⟩
         Γ ⊢ne Emptyrec p A′ t′ ∷ A′  →⟨ flip _⊢ne_∷_.convₙ (sym A≡A′) ⟩
         Γ ⊢ne Emptyrec p A′ t′ ∷ A   □)
      , Emptyrec-cong A≡A′ t≡t′ }}

  fullRedNe~↓ :
    Γ ⊢ t ~ t′ ↓ A →
    ∃ λ u → Γ ⊢ne u ∷ A × Γ ⊢ t ≡ u ∷ A
  fullRedNe~↓ ([~] A D whnfB k~l) =
    let u , A-ne , t≡u = fullRedNe k~l
    in  u , convₙ A-ne A≡ , conv t≡u A≡
    where
    A≡ = subset* D

  fullRedConv↑ :
    Γ ⊢ A [conv↑] A′ →
    ∃ λ B → Γ ⊢nf B × Γ ⊢ A ≡ B
  fullRedConv↑ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) =
    let B″ , nf , B′≡B″ = fullRedConv↓ A′<>B′
    in  B″ , nf , trans (subset* D) B′≡B″

  fullRedConv↓ :
    Γ ⊢ A [conv↓] A′ →
    ∃ λ B → Γ ⊢nf B × Γ ⊢ A ≡ B
  fullRedConv↓ = λ where
    (U-refl     ⊢Γ)    → U     , Uₙ     ⊢Γ , refl (Uⱼ     ⊢Γ)
    (ℕ-refl     ⊢Γ)    → ℕ     , ℕₙ     ⊢Γ , refl (ℕⱼ     ⊢Γ)
    (Empty-refl ⊢Γ)    → Empty , Emptyₙ ⊢Γ , refl (Emptyⱼ ⊢Γ)
    (Unit-refl  ⊢Γ ok) →
      Unit , Unitₙ ⊢Γ ok , refl (Unitⱼ ⊢Γ ok)
    (ne A~) →
      case fullRedNe~↓ A~ of λ {
        (B , B-ne , A≡B) →
      B , univₙ (neₙ Uₙ B-ne) , univ A≡B }
    (ΠΣ-cong ⊢A A↑ B↑ ok) →
      case fullRedConv↑ A↑ of λ {
        (A′ , A′-nf , A≡A′) →
      case fullRedConv↑ B↑ of λ {
        (B′ , B′-nf , B≡B′) →
      ΠΣ⟨ _ ⟩ _ , _ ▷ A′ ▹ B′ ,
      ΠΣₙ A′-nf (⊢nf-stable (reflConEq (wfEq A≡A′) ∙ A≡A′) B′-nf) ok ,
      ΠΣ-cong ⊢A A≡A′ B≡B′ ok }}

  fullRedTermConv↑ :
    Γ ⊢ t [conv↑] t′ ∷ A →
    ∃ λ u → Γ ⊢nf u ∷ A × Γ ⊢ t ≡ u ∷ A
  fullRedTermConv↑
    ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) =
    case fullRedTermConv↓ t<>u of λ {
      (u″ , nf , u′≡u″) →
    u″ ,
    convₙ nf B≡A ,
    conv (trans (subset*Term d) u′≡u″) B≡A }
    where
    B≡A = sym (subset* D)

  fullRedTermConv↓ :
    Γ ⊢ t [conv↓] t′ ∷ A →
    ∃ λ u → Γ ⊢nf u ∷ A × Γ ⊢ t ≡ u ∷ A
  fullRedTermConv↓ {Γ = Γ} {t = t} = λ where
    (ℕ-ins t~) →
      case fullRedNe~↓ t~ of λ {
        (u , u-nf , t≡u) →
      u , neₙ ℕₙ u-nf , t≡u }
    (Empty-ins t~) →
      case fullRedNe~↓ t~ of λ {
        (u , u-nf , t≡u) →
      u , neₙ Emptyₙ u-nf , t≡u }
    (Unit-ins t~) →
      case syntacticEqTerm (soundness~↓ t~) of λ {
        (Γ⊢ , ⊢t , _) →
      case wf Γ⊢ of λ {
        ⊢Γ →
      case ⊢∷Unit→Unit-allowed ⊢t of λ {
        ok →
        star
      , starₙ ⊢Γ ok
      , η-unit ⊢t (starⱼ ⊢Γ ok) }}}
    (Σᵣ-ins ⊢t∷ΣAB _ t~) →
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
      , neₙ Σᵣₙ (convₙ v-ne ΣCD≡ΣAB)
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
      , neₙ (neₙ A-ne) (convₙ u-ne B≡A)
      , conv t≡u∷B B≡A }}}}
    (univ {A = A} ⊢A _ A↓) →
      case fullRedConv↓ A↓ of λ {
        (B , B-nf , A≡B) →
        B
      , (               $⟨ A≡B ⟩
         (Γ ⊢ A ≡ B)    →⟨ inverseUnivEq ⊢A ⟩
         Γ ⊢ A ≡ B ∷ U  →⟨ (λ hyp → syntacticEqTerm hyp .proj₂ .proj₂) ⟩
         Γ ⊢ B ∷ U      →⟨ ⊢nf∷U→⊢nf∷U B-nf ⟩
         Γ ⊢nf B ∷ U    □)
      , inverseUnivEq ⊢A A≡B }
    (zero-refl ⊢Γ) →
      zero , zeroₙ ⊢Γ , refl (zeroⱼ ⊢Γ)
    (suc-cong t↑) →
      case fullRedTermConv↑ t↑ of λ {
        (u , u-nf , t≡u) →
      suc u , sucₙ u-nf , suc-cong t≡u }
    (prod-cong {p = p} {q = q} {F = A} {G = B} {t = t} ⊢A ⊢B t↑ u↑ ok) →
      case fullRedTermConv↑ t↑ of λ {
        (t′ , t′-nf , t≡t′) →
      case fullRedTermConv↑ u↑ of λ {
        (u′ , u′-nf , u≡u′) →
        prod! t′ u′
      , (                                      $⟨ u′-nf ⟩
         Γ ⊢nf u′ ∷ B [ t ]₀                   →⟨ flip _⊢nf_∷_.convₙ $
                                                  substTypeEq (refl ⊢B) t≡t′ ⟩
         Γ ⊢nf u′ ∷ B [ t′ ]₀                  →⟨ flip (_⊢nf_∷_.prodₙ ⊢A ⊢B t′-nf) ok ⟩
         Γ ⊢nf prod! t′ u′ ∷ Σᵣ p , q ▷ A ▹ B  □)
      , prod-cong ⊢A ⊢B t≡t′ u≡u′ ok }}
    (η-eq {p = p} {q = q} {f = t} {F = A} {G = B} ⊢t _ _ _ t0≡u0) →
      case fullRedTermConv↑ t0≡u0 of λ {
        (u , u-nf , t0≡u) →
      case ⊢∷ΠΣ→ΠΣ-allowed ⊢t of λ {
        ok →
        lam p u
      , lamₙ (inversion-ΠΣ (syntacticTerm ⊢t) .proj₁) u-nf ok
      , (                                                       $⟨ sym (Π-η ⊢t) ⟩
         Γ ⊢ t ≡ lam p (wk1 t ∘⟨ p ⟩ var x0) ∷ Π p , q ▷ A ▹ B  →⟨ flip _⊢_≡_∷_.trans (lam-cong t0≡u ok) ⟩
         Γ ⊢ t ≡ lam p u ∷ Π p , q ▷ A ▹ B                      □) }}
    (Σ-η {p = p} {q = q} {F = A} {G = B} ⊢t _ _ _ fst-t↑ snd-t↑) →
      case inversion-ΠΣ (syntacticTerm ⊢t) of λ {
        (⊢A , ⊢B , ok) →
      case fullRedTermConv↑ fst-t↑ of λ {
        (u₁ , u₁-nf , fst-t≡u₁) →
      case fullRedTermConv↑ snd-t↑ of λ {
        (u₂ , u₂-nf , snd-t≡u₂) →
        prodₚ p u₁ u₂
      , (                                        $⟨ u₂-nf ⟩
         Γ ⊢nf u₂ ∷ B [ fst p t ]₀               →⟨ flip _⊢nf_∷_.convₙ $
                                                    substTypeEq (refl ⊢B) fst-t≡u₁ ⟩
         Γ ⊢nf u₂ ∷ B [ u₁ ]₀                    →⟨ flip (prodₙ ⊢A ⊢B u₁-nf) ok ⟩
         Γ ⊢nf prodₚ p u₁ u₂ ∷ Σₚ p , q ▷ A ▹ B  □)
      , (                                                        $⟨ sym (Σ-η-prod-fst-snd ⊢t) ⟩
         Γ ⊢ t ≡ prodₚ p (fst p t) (snd p t) ∷ Σₚ p , q ▷ A ▹ B  →⟨ flip _⊢_≡_∷_.trans $
                                                                    prod-cong ⊢A ⊢B fst-t≡u₁ snd-t≡u₂ ok ⟩
         Γ ⊢ t ≡ prodₚ p u₁ u₂ ∷ Σₚ p , q ▷ A ▹ B                □) }}}
    (η-unit ⊢t _ _ _) →
      case wfTerm ⊢t of λ {
        ⊢Γ →
      case ⊢∷Unit→Unit-allowed ⊢t of λ {
        ok →
        star
      , starₙ ⊢Γ ok
      , η-unit ⊢t (starⱼ ⊢Γ ok) }}

-- If A is a well-formed type, then A is definitionally equal to a
-- type in η-long normal form.

fullRed : Γ ⊢ A → ∃ λ B → Γ ⊢nf B × Γ ⊢ A ≡ B
fullRed ⊢A = fullRedConv↑ (completeEq (refl ⊢A))

-- If t is a well-typed term, then t is definitionally equal to a term
-- in η-long normal form.

fullRedTerm : Γ ⊢ t ∷ A → ∃ λ u → Γ ⊢nf u ∷ A × Γ ⊢ t ≡ u ∷ A
fullRedTerm ⊢t = fullRedTermConv↑ (completeEqTerm (refl ⊢t))
