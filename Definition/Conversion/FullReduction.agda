{-# OPTIONS --without-K --safe #-}

open import Tools.Relation

module Definition.Conversion.FullReduction {a ℓ} (M′ : Setoid a ℓ) where

open Setoid M′ using () renaming (Carrier to M; refl to ≈-refl)

open import Definition.Untyped M as U hiding (wk ; _∷_)
open import Definition.Untyped.Properties M
open import Definition.Typed M′
open import Definition.Typed.Properties M′
open import Definition.Typed.Weakening M′
open import Definition.Conversion M′
open import Definition.Conversion.Whnf M′
open import Definition.Typed.Consequences.InverseUniv M′
open import Definition.Typed.Consequences.Syntactic M′
open import Definition.Typed.Consequences.NeTypeEq M′
open import Definition.Typed.Consequences.Substitution M′

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    m : Nat
    Γ : Con Term m
    A B C : Term m
    c g k n p u : Term m
    q r : M
    s : SigmaMode

mutual
  data NfNeutral {m : Nat} : Term m → Set a where
    var       : (x : Fin m)                             → NfNeutral (var x)
    ∘ₙ        : {k u : Term m}     → NfNeutral k → Nf u → NfNeutral (k ∘ q ▷ u)
    fstₙ      : {p : Term m}       → NfNeutral p        → NfNeutral (fst p)
    sndₙ      : {p : Term m}       → NfNeutral p        → NfNeutral (snd p)
    natrecₙ   : {C : Term (1+ m)} {c k : Term m} {g : Term (1+ (1+ m))}
                     → Nf C → Nf c → Nf g → NfNeutral k → NfNeutral (natrec q r C c g k)
    prodrecₙ  : {C : Term (1+ m)} {t : Term m} {u : Term (1+ (1+ m))}
                     → Nf C → NfNeutral t → Nf u → NfNeutral (prodrec r C t u)
    Emptyrecₙ : {C k : Term m}     → Nf C → NfNeutral k → NfNeutral (Emptyrec q C k)

  data Nf {m : Nat} : Term m → Set a where
    Uₙ     : Nf U
    Πₙ     : {A : Term m} {B : Term (1+ m)} → Nf A → Nf B → Nf (Π r , q ▷ A ▹ B)
    Σₙ     : {A : Term m} {B : Term (1+ m)} → Nf A → Nf B → Nf (Σ⟨ s ⟩ q ▷ A ▹ B)
    ℕₙ     : Nf ℕ
    Emptyₙ : Nf Empty
    Unitₙ  : Nf Unit

    lamₙ   : {t : Term (1+ m)} → Nf t → Nf (lam q t)
    prodₙ  : {t u : Term m} → Nf t → Nf u → Nf (prod s t u)
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
nfWhnf (Πₙ n n₁) = Πₙ
nfWhnf (Σₙ n n₁) = Σₙ
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
  fullRedNe (app-cong t u p≈p₁ p≈p₂) =
    let t′ , nfT′ , t≡t′ = fullRedNe~↓ t
        u′ , nfU′ , u≡u′ = fullRedTerm u
    in  (t′ ∘ _ ▷ u′) , (∘ₙ nfT′ nfU′) , app-cong t≡t′ u≡u′ p≈p₁ p≈p₂
  fullRedNe (fst-cong p~p) =
    let p′ , neP′ , p≡p′ = fullRedNe~↓ p~p
        ⊢ΣFG , _ , _ = syntacticEqTerm p≡p′
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG
    in  fst p′ , fstₙ neP′ , fst-cong ⊢F ⊢G p≡p′
  fullRedNe (snd-cong p~p) =
    let p′ , neP′ , p≡p′ = fullRedNe~↓ p~p
        ⊢ΣFG , _ , _ = syntacticEqTerm p≡p′
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG
    in  snd p′ , sndₙ neP′ , snd-cong ⊢F ⊢G p≡p′
  fullRedNe (natrec-cong {p = p} {r = r} C z s n p≈p′ r≈r′) =
    let C′ , nfC′ , C≡C′ = fullRed C
        z′ , nfZ′ , z≡z′ = fullRedTerm z
        s′ , nfS′ , s≡s′ = fullRedTerm s
        n′ , nfN′ , n≡n′ = fullRedNe~↓ n
    in  natrec p r C′ z′ s′ n′ , natrecₙ nfC′ nfZ′ nfS′ nfN′
     , natrec-cong (proj₁ (syntacticEq C≡C′)) C≡C′ z≡z′ s≡s′ n≡n′ ≈-refl ≈-refl
  fullRedNe (prodrec-cong {p = p} C g u p≈p′) =
    let C′ , nfC′ , C≡C′ = fullRed C
        g′ , nfg′ , g≡g′ = fullRedNe~↓ g
        u′ , nfu′ , u≡u′ = fullRedTerm u
        ⊢Σ , _ = syntacticEqTerm g≡g′
        ⊢F , ⊢G = syntacticΣ ⊢Σ
    in  prodrec p C′ g′ u′ , prodrecₙ nfC′ nfg′ nfu′
     , prodrec-cong ⊢F ⊢G C≡C′ g≡g′ u≡u′ ≈-refl
  fullRedNe (Emptyrec-cong C n p≈p′) =
    let C′ , nfC′ , C≡C′ = fullRed C
        n′ , nfN′ , n≡n′ = fullRedNe~↓ n
    in  Emptyrec _ C′ n′ , Emptyrecₙ nfC′ nfN′
     ,  Emptyrec-cong C≡C′ n≡n′ p≈p′

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
  fullRedConv↓ (Unit-refl ⊢Γ) = Unit , Unitₙ , refl (Unitⱼ ⊢Γ)
  fullRedConv↓ (ne A) =
    let B , nf , A≡B = fullRedNe~↓ A
    in  B , ne nf , univ A≡B
  fullRedConv↓ (Π-cong ⊢F F G p≈p′ q≈q′) =
    let F′ , nfF′ , F≡F′ = fullRed F
        G′ , nfG′ , G≡G′ = fullRed G
    in  Π _ , _ ▷ F′ ▹ G′ , Πₙ nfF′ nfG′ , Π-cong ⊢F F≡F′ G≡G′ p≈p′ q≈q′
  fullRedConv↓ (Σ-cong ⊢F F G q≈q′) =
    let F′ , nfF′ , F≡F′ = fullRed F
        G′ , nfG′ , G≡G′ = fullRed G
    in  Σ _ ▷ F′ ▹ G′ , Σₙ nfF′ nfG′ , Σ-cong ⊢F F≡F′ G≡G′ q≈q′

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
  fullRedTermConv↓ (prod-cong ⊢F ⊢G t↑t u↑u) =
    let t′ , nfT , t≡t′ = fullRedTerm t↑t
        u′ , nfU , u≡u′ = fullRedTerm u↑u
    in  prod! t′ u′ , prodₙ nfT nfU , prod-cong ⊢F ⊢G t≡t′ u≡u′
  fullRedTermConv↓ (η-eq {p = p} ⊢t _ _ _ t∘0) =
    let u , nf , t∘0≡u = fullRedTerm (t∘0 ≈-refl ≈-refl)
        ⊢G , _ , ⊢u = syntacticEqTerm t∘0≡u
        ⊢F , _ = syntacticΠ (syntacticTerm ⊢t)
        ΓF⊢ = wf ⊢F ∙ ⊢F
        wk⊢F = wk (step id) ΓF⊢ ⊢F
        wk⊢G = wk (lift (step id)) (ΓF⊢ ∙ wk⊢F) ⊢G
        ΓFF'⊢ = ΓF⊢ ∙ wk⊢F
        wk⊢u = wkTerm (lift (step id)) ΓFF'⊢ ⊢u
        wk⊢t = wkTerm (step id) ΓF⊢ ⊢t
        λu∘0 = lam p (U.wk (lift (step id)) u) ∘ p ▷ var x0
    in  lam _ u , lamₙ nf
     ,  η-eq ⊢F ⊢t (lamⱼ ⊢F ⊢u) λ {p₁} {p₂} p≈p₁ p≈p₂ →
             let λu∘0 = lam p (U.wk (lift (step id)) u) ∘ p₂ ▷ var x0
             in  trans (PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x) (wkSingleSubstId _)
                                 (app-cong (refl wk⊢t) (refl (var ΓF⊢ here)) p≈p₁ ≈-refl))
                       (trans t∘0≡u (PE.subst₂ (λ x y → _ ⊢ x ≡ λu∘0 ∷ y)
                                    (wkSingleSubstId u) (wkSingleSubstId _)
                                    (sym (β-red wk⊢F wk⊢G wk⊢u (var ΓF⊢ here) p≈p₂))))
  fullRedTermConv↓ (Σ-η ⊢t _ tProd _ fstConv sndConv) =
    let fst′ , nfFst′ , fst≡fst′ = fullRedTerm fstConv
        snd′ , nfSnd′ , snd≡snd′ = fullRedTerm sndConv
        _ , _ , ⊢fst′ = syntacticEqTerm fst≡fst′
        _ , _ , ⊢snd′₁ = syntacticEqTerm snd≡snd′
        ⊢ΣFG = syntacticTerm ⊢t
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG

        Gfst≡Gfst′ = substTypeEq (refl ⊢G) fst≡fst′
        ⊢snd′ = conv ⊢snd′₁ Gfst≡Gfst′
        ⊢prod = prodⱼ ⊢F ⊢G ⊢fst′ ⊢snd′

        fstprod≡fst′ = Σ-β₁ ⊢F ⊢G ⊢fst′ ⊢snd′ ⊢prod
        fst≡fstprod = trans fst≡fst′ (sym fstprod≡fst′)
        Gfst≡Gfstprod = substTypeEq (refl ⊢G) fst≡fstprod
        sndprod≡snd′ = conv (Σ-β₂ ⊢F ⊢G ⊢fst′ ⊢snd′ ⊢prod) (sym Gfst≡Gfstprod)
        snd≡sndprod = trans snd≡snd′ (sym sndprod≡snd′)
    in  prod! fst′ snd′ , prodₙ nfFst′ nfSnd′
      , Σ-η ⊢F ⊢G ⊢t ⊢prod fst≡fstprod snd≡sndprod
  fullRedTermConv↓ (η-unit ⊢t _ tUnit _) =
    star , starₙ , η-unit ⊢t (starⱼ (wfTerm ⊢t))
