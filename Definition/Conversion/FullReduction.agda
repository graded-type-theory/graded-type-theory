------------------------------------------------------------------------
-- Every term is equal to a fully reduced term.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions

module Definition.Conversion.FullReduction
  {a} {M : Set a}
  (R : Type-restrictions M)
  where

open import Definition.Untyped M as U hiding (wk ; _∷_)
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R
open import Definition.Conversion R
open import Definition.Conversion.Whnf R
open import Definition.Typed.Consequences.InverseUniv R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Consequences.NeTypeEq R
open import Definition.Typed.Consequences.Substitution R

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE using (≈-refl)

private
  variable
    m : Nat
    Γ : Con Term m
    A B C : Term m
    c g k n t u : Term m
    p q r : M
    b : BinderMode
    s : SigmaMode

mutual
  data NfNeutral {m : Nat} : Term m → Set a where
    var       : (x : Fin m)                             → NfNeutral (var x)
    ∘ₙ        : {k u : Term m}     → NfNeutral k → Nf u → NfNeutral (k ∘⟨ q ⟩ u)
    fstₙ      : NfNeutral t → NfNeutral (fst p t)
    sndₙ      : NfNeutral t → NfNeutral (snd p t)
    natrecₙ   : {C : Term (1+ m)} {c k : Term m} {g : Term (1+ (1+ m))}
                     → Nf C → Nf c → Nf g → NfNeutral k → NfNeutral (natrec p q r C c g k)
    prodrecₙ  : {C : Term (1+ m)} {t : Term m} {u : Term (1+ (1+ m))} →
                Nf C → NfNeutral t → Nf u →
                NfNeutral (prodrec r p q C t u)
    Emptyrecₙ : {C k : Term m}     → Nf C → NfNeutral k → NfNeutral (Emptyrec p C k)

  data Nf {m : Nat} : Term m → Set a where
    Uₙ     : Nf U
    ΠΣₙ    : {A : Term m} {B : Term (1+ m)} →
             Nf A → Nf B → Nf (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B)
    ℕₙ     : Nf ℕ
    Emptyₙ : Nf Empty
    Unitₙ  : Nf Unit

    lamₙ   : {t : Term (1+ m)} → Nf t → Nf (lam q t)
    prodₙ  : Nf t → Nf u → Nf (prod s p t u)
    zeroₙ  : Nf zero
    sucₙ   : {t : Term m} → Nf t → Nf (suc t)
    starₙ  : Nf star

    ne     : {n : Term m} → NfNeutral n → Nf n

nfNeutral : NfNeutral n → Neutral n
nfNeutral (var x) = var x
nfNeutral (∘ₙ n x) = ∘ₙ (nfNeutral n)
nfNeutral (fstₙ n) = fstₙ (nfNeutral n)
nfNeutral (sndₙ n) = sndₙ (nfNeutral n)
nfNeutral (natrecₙ x x₁ x₂ n) = natrecₙ (nfNeutral n)
nfNeutral (prodrecₙ x n x₁) = prodrecₙ (nfNeutral n)
nfNeutral (Emptyrecₙ x n) = Emptyrecₙ (nfNeutral n)

nfWhnf : Nf n → Whnf n
nfWhnf Uₙ = Uₙ
nfWhnf (ΠΣₙ n n₁) = ΠΣₙ
nfWhnf ℕₙ = ℕₙ
nfWhnf Emptyₙ = Emptyₙ
nfWhnf Unitₙ = Unitₙ
nfWhnf (lamₙ n) = lamₙ
nfWhnf (prodₙ n n₁) = prodₙ
nfWhnf zeroₙ = zeroₙ
nfWhnf (sucₙ n) = sucₙ
nfWhnf starₙ = starₙ
nfWhnf (ne x) = ne (nfNeutral x)

mutual
  fullRedNe : ∀ {t t′ A} → Γ ⊢ t ~ t′ ↑ A → ∃ λ u → NfNeutral u × Γ ⊢ t ≡ u ∷ A
  fullRedNe (var-refl x _) = var _ , var _ , refl x
  fullRedNe (app-cong t u) =
    let t′ , nfT′ , t≡t′ = fullRedNe~↓ t
        u′ , nfU′ , u≡u′ = fullRedTerm u
    in  (t′ ∘ u′) , (∘ₙ nfT′ nfU′) , app-cong t≡t′ u≡u′
  fullRedNe (fst-cong p~p) =
    let p′ , neP′ , p≡p′ = fullRedNe~↓ p~p
        ⊢ΣFG , _ , _ = syntacticEqTerm p≡p′
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG
    in  fst _ p′ , fstₙ neP′ , fst-cong ⊢F ⊢G p≡p′
  fullRedNe (snd-cong p~p) =
    let p′ , neP′ , p≡p′ = fullRedNe~↓ p~p
        ⊢ΣFG , _ , _ = syntacticEqTerm p≡p′
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG
    in  snd _ p′ , sndₙ neP′ , snd-cong ⊢F ⊢G p≡p′
  fullRedNe (natrec-cong C z s n) =
    let C′ , nfC′ , C≡C′ = fullRed C
        z′ , nfZ′ , z≡z′ = fullRedTerm z
        s′ , nfS′ , s≡s′ = fullRedTerm s
        n′ , nfN′ , n≡n′ = fullRedNe~↓ n
    in  natrec _ _ _ C′ z′ s′ n′ , natrecₙ nfC′ nfZ′ nfS′ nfN′
     , natrec-cong (proj₁ (syntacticEq C≡C′)) C≡C′ z≡z′ s≡s′ n≡n′
  fullRedNe (prodrec-cong C g u) =
    let C′ , nfC′ , C≡C′ = fullRed C
        g′ , nfg′ , g≡g′ = fullRedNe~↓ g
        u′ , nfu′ , u≡u′ = fullRedTerm u
        ⊢Σ , _ = syntacticEqTerm g≡g′
        ⊢F , ⊢G , ok = inversion-ΠΣ ⊢Σ
    in  prodrec _ _ _ C′ g′ u′ , prodrecₙ nfC′ nfg′ nfu′
     , prodrec-cong ⊢F ⊢G C≡C′ g≡g′ u≡u′ ok
  fullRedNe (Emptyrec-cong C n) =
    let C′ , nfC′ , C≡C′ = fullRed C
        n′ , nfN′ , n≡n′ = fullRedNe~↓ n
    in  Emptyrec _ C′ n′ , Emptyrecₙ nfC′ nfN′
     ,  Emptyrec-cong C≡C′ n≡n′

  fullRedNe~↓ : ∀ {t t′ A} → Γ ⊢ t ~ t′ ↓ A → ∃ λ u → NfNeutral u × Γ ⊢ t ≡ u ∷ A
  fullRedNe~↓ ([~] A D whnfB k~l) =
    let u , nf , t≡u = fullRedNe k~l
    in  u , nf , conv t≡u (subset* D)

  fullRed : ∀ {A A′} → Γ ⊢ A [conv↑] A′ → ∃ λ B → Nf B × Γ ⊢ A ≡ B
  fullRed ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) =
    let B″ , nf , B′≡B″ = fullRedConv↓ A′<>B′
    in  B″ , nf , trans (subset* D) B′≡B″

  fullRedConv↓ : ∀ {A A′} → Γ ⊢ A [conv↓] A′ → ∃ λ B → Nf B × Γ ⊢ A ≡ B
  fullRedConv↓ (U-refl ⊢Γ) = U , Uₙ , refl (Uⱼ ⊢Γ)
  fullRedConv↓ (ℕ-refl ⊢Γ) = ℕ , ℕₙ , refl (ℕⱼ ⊢Γ)
  fullRedConv↓ (Empty-refl ⊢Γ) = Empty , Emptyₙ , refl (Emptyⱼ ⊢Γ)
  fullRedConv↓ (Unit-refl ⊢Γ ok) = Unit , Unitₙ , refl (Unitⱼ ⊢Γ ok)
  fullRedConv↓ (ne A) =
    let B , nf , A≡B = fullRedNe~↓ A
    in  B , ne nf , univ A≡B
  fullRedConv↓ (ΠΣ-cong ⊢F F G ok) =
    let F′ , nfF′ , F≡F′ = fullRed F
        G′ , nfG′ , G≡G′ = fullRed G
    in  ΠΣ⟨ _ ⟩ _ , _ ▷ F′ ▹ G′ , ΠΣₙ nfF′ nfG′ ,
        ΠΣ-cong ⊢F F≡F′ G≡G′ ok

  fullRedTerm : ∀ {t t′ A} → Γ ⊢ t [conv↑] t′ ∷ A → ∃ λ u → Nf u × Γ ⊢ t ≡ u ∷ A
  fullRedTerm ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) =
    let u″ , nf , u′≡u″ = fullRedTermConv↓ t<>u
    in  u″ , nf , conv (trans (subset*Term d) u′≡u″) (sym (subset* D))

  fullRedTermConv↓ : ∀ {t t′ A} → Γ ⊢ t [conv↓] t′ ∷ A → ∃ λ u → Nf u × Γ ⊢ t ≡ u ∷ A
  fullRedTermConv↓ (ℕ-ins t) =
    let u , nf , t≡u = fullRedNe~↓ t
    in  u , ne nf , t≡u
  fullRedTermConv↓ (Empty-ins t) =
    let u , nf , t≡u = fullRedNe~↓ t
    in  u , ne nf , t≡u
  fullRedTermConv↓ (Unit-ins t) =
    let u , nf , t≡u = fullRedNe~↓ t
    in  u , ne nf , t≡u
  fullRedTermConv↓ (Σᵣ-ins t u t~u) =
    let v , nf , t≡v = fullRedNe~↓ t~u
        _ , t′ , _ = syntacticEqTerm t≡v
        _ , neT , _ = ne~↓ t~u
    in  v , ne nf , conv t≡v (neTypeEq neT t′ t)
  fullRedTermConv↓ (ne-ins ⊢t _ _ t) =
    let u , nfU , t≡u = fullRedNe~↓ t
        _ , ⊢t∷M , _ = syntacticEqTerm t≡u
        _ , neT , _ = ne~↓ t
    in  u , ne nfU , conv t≡u (neTypeEq neT ⊢t∷M ⊢t)
  fullRedTermConv↓ (univ ⊢t _ t) =
    let u , nf , t≡u = fullRedConv↓ t
    in  u , nf , inverseUnivEq ⊢t t≡u
  fullRedTermConv↓ (zero-refl ⊢Γ) = zero , zeroₙ , refl (zeroⱼ ⊢Γ)
  fullRedTermConv↓ (suc-cong t) =
    let u , nf , t≡u = fullRedTerm t
    in  suc u , sucₙ nf , suc-cong t≡u
  fullRedTermConv↓ (prod-cong ⊢F ⊢G t↑t u↑u ok) =
    let t′ , nfT , t≡t′ = fullRedTerm t↑t
        u′ , nfU , u≡u′ = fullRedTerm u↑u
    in  prod! t′ u′ , prodₙ nfT nfU , prod-cong ⊢F ⊢G t≡t′ u≡u′ ok
  fullRedTermConv↓ (η-eq {p = p} ⊢t _ _ _ t∘0) =
    let u , nf , t∘0≡u = fullRedTerm t∘0
        ⊢G , _ , ⊢u = syntacticEqTerm t∘0≡u
        ⊢F , _ = syntacticΠ (syntacticTerm ⊢t)
        ΓF⊢ = wf ⊢F ∙ ⊢F
        wk⊢F = wk (step id) ΓF⊢ ⊢F
        wk⊢G = wk (lift (step id)) (ΓF⊢ ∙ wk⊢F) ⊢G
        ΓFF'⊢ = ΓF⊢ ∙ wk⊢F
        wk⊢u = wkTerm (lift (step id)) ΓFF'⊢ ⊢u
        wk⊢t = wkTerm (step id) ΓF⊢ ⊢t
        λu∘0 = lam p (U.wk (lift (step id)) u) ∘⟨ p ⟩ var x0
        ok = ⊢∷ΠΣ→ΠΣ-restriction ⊢t
    in  lam _ u , lamₙ nf
     ,  η-eq ⊢F ⊢t (lamⱼ ⊢F ⊢u ok)
          (trans
             (PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x) (wkSingleSubstId _)
                (app-cong (refl wk⊢t) (refl (var ΓF⊢ here))))
             (trans t∘0≡u
                (PE.subst₂ (λ x y → _ ⊢ x ≡ λu∘0 ∷ y)
                   (wkSingleSubstId u) (wkSingleSubstId _)
                   (sym (β-red wk⊢F wk⊢G wk⊢u
                           (var ΓF⊢ here) PE.refl ok)))))
  fullRedTermConv↓ (Σ-η ⊢t _ tProd _ fstConv sndConv) =
    let fst′ , nfFst′ , fst≡fst′ = fullRedTerm fstConv
        snd′ , nfSnd′ , snd≡snd′ = fullRedTerm sndConv
        _ , _ , ⊢fst′ = syntacticEqTerm fst≡fst′
        _ , _ , ⊢snd′₁ = syntacticEqTerm snd≡snd′
        ⊢F , ⊢G , ok = inversion-ΠΣ (syntacticTerm ⊢t)

        Gfst≡Gfst′ = substTypeEq (refl ⊢G) fst≡fst′
        ⊢snd′ = conv ⊢snd′₁ Gfst≡Gfst′
        ⊢prod = prodⱼ ⊢F ⊢G ⊢fst′ ⊢snd′ ok

        fstprod≡fst′ = Σ-β₁ ⊢F ⊢G ⊢fst′ ⊢snd′ PE.refl ok
        fst≡fstprod = trans fst≡fst′ (sym fstprod≡fst′)
        Gfst≡Gfstprod = substTypeEq (refl ⊢G) fst≡fstprod
        sndprod≡snd′ = conv (Σ-β₂ ⊢F ⊢G ⊢fst′ ⊢snd′ PE.refl ok)
                         (sym Gfst≡Gfstprod)
        snd≡sndprod = trans snd≡snd′ (sym sndprod≡snd′)
    in  prod! fst′ snd′ , prodₙ nfFst′ nfSnd′
      , Σ-η ⊢F ⊢G ⊢t ⊢prod fst≡fstprod snd≡sndprod
  fullRedTermConv↓ (η-unit ⊢t _ tUnit _) =
    star , starₙ , η-unit ⊢t (starⱼ (wfTerm ⊢t) ok)
    where
    ok = ⊢∷Unit→Unit-restriction ⊢t
