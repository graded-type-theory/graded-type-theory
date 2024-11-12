------------------------------------------------------------------------
-- Soundness of algorithmic equality.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Conversion.Soundness
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.RedSteps R
import Definition.Typed.Reasoning.Term R as TmR
import Definition.Typed.Reasoning.Type R as TyR
open import Definition.Typed.Stability R
open import Definition.Typed.Syntactic R
open import Definition.Conversion R
open import Definition.Conversion.Whnf R
open import Definition.Typed.Consequences.DerivedRules R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Reduction R
open import Definition.Typed.Consequences.NeTypeEq R

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n     : Nat
    Γ     : Con Term n
    A B   : Term _
    l₁ l₂ : Universe-level

mutual
  -- Algorithmic equality of neutrals is well-formed.
  soundness~↑ : ∀ {k l A} → Γ ⊢ k ~ l ↑ A → Γ ⊢ k ≡ l ∷ A
  soundness~↑ (var-refl x x≡y) = PE.subst (λ y → _ ⊢ _ ≡ var y ∷ _) x≡y (refl x)
  soundness~↑ (app-cong k~l x₁) =
    app-cong (soundness~↓ k~l) (soundnessConv↑Term x₁)
  soundness~↑ (fst-cong x) =
    let p≡ = soundness~↓ x
        ⊢ΣFG = proj₁ (syntacticEqTerm p≡)
        _ , ⊢G = syntacticΣ ⊢ΣFG
    in  fst-cong ⊢G p≡
  soundness~↑ (snd-cong x) =
    let p≡ = soundness~↓ x
        ⊢ΣFG = proj₁ (syntacticEqTerm p≡)
        _ , ⊢G = syntacticΣ ⊢ΣFG
    in  snd-cong ⊢G p≡
  soundness~↑ (natrec-cong x₁ x₂ x₃ k~l) =
    let F≡G = soundnessConv↑ x₁ in
    natrec-cong F≡G (soundnessConv↑Term x₂) (soundnessConv↑Term x₃)
      (soundness~↓ k~l)
  soundness~↑ (prodrec-cong x x₁ x₂) =
    let C≡E = soundnessConv↑ x
        g≡h = soundness~↓ x₁
        u≡v = soundnessConv↑Term x₂
        _ , _ , ok = inversion-ΠΣ (proj₁ (syntacticEqTerm g≡h))
    in  prodrec-cong C≡E g≡h u≡v ok
  soundness~↑ (emptyrec-cong x₁ k~l) =
    emptyrec-cong (soundnessConv↑ x₁) (soundness~↓ k~l)
  soundness~↑ (unitrec-cong x x₁ x₂ no-η) =
    let F≡H = soundnessConv↑ x
        k≡l = soundness~↓ x₁
        u≡v = soundnessConv↑Term x₂
        ok = inversion-Unit (proj₁ (syntacticEqTerm k≡l))
    in  unitrec-cong F≡H k≡l u≡v ok no-η
  soundness~↑ (J-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁~w₂ ≡Id) =
    case soundnessConv↑ A₁≡A₂ of λ {
      A₁≡A₂ →
    case soundnessConv↑Term t₁≡t₂ of λ {
      t₁≡t₂ →
    J-cong A₁≡A₂
      (syntacticEqTerm t₁≡t₂ .proj₂ .proj₁) t₁≡t₂ (soundnessConv↑ B₁≡B₂)
      (soundnessConv↑Term u₁≡u₂) (soundnessConv↑Term v₁≡v₂)
      (conv (soundness~↓ w₁~w₂) ≡Id) }}
  soundness~↑ (K-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁~v₂ ≡Id ok) =
    K-cong (soundnessConv↑ A₁≡A₂) (soundnessConv↑Term t₁≡t₂)
      (soundnessConv↑ B₁≡B₂) (soundnessConv↑Term u₁≡u₂)
      (conv (soundness~↓ v₁~v₂) ≡Id) ok
  soundness~↑ ([]-cong-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁~v₂ ≡Id ok) =
    []-cong-cong (soundnessConv↑ A₁≡A₂) (soundnessConv↑Term t₁≡t₂)
      (soundnessConv↑Term u₁≡u₂) (conv (soundness~↓ v₁~v₂) ≡Id) ok

  -- Algorithmic equality of neutrals in WHNF is well-formed.
  soundness~↓ : ∀ {k l A} → Γ ⊢ k ~ l ↓ A → Γ ⊢ k ≡ l ∷ A
  soundness~↓ ([~] A₁ (D , _) k~l) = conv (soundness~↑ k~l) (subset* D)

  -- Algorithmic equality of types is well-formed.
  soundnessConv↑ : ∀ {A B} → Γ ⊢ A [conv↑] B → Γ ⊢ A ≡ B
  soundnessConv↑ ([↑] _ _ (D , _) (D′ , _) A′<>B′) =
    trans (subset* D) (trans (soundnessConv↓ A′<>B′) (sym (subset* D′)))

  -- Algorithmic equality of types in WHNF is well-formed.
  soundnessConv↓ : ∀ {A B} → Γ ⊢ A [conv↓] B → Γ ⊢ A ≡ B
  soundnessConv↓ (U-refl ⊢Γ) = refl (Uⱼ ⊢Γ)
  soundnessConv↓ (ℕ-refl ⊢Γ) = refl (ℕⱼ ⊢Γ)
  soundnessConv↓ (Empty-refl ⊢Γ) = refl (Emptyⱼ ⊢Γ)
  soundnessConv↓ (Unit-refl ⊢Γ ok) = refl (Unitⱼ ⊢Γ ok)
  soundnessConv↓ (ne x) = univ (soundness~↓ x)
  soundnessConv↓ (ΠΣ-cong A₁≡A₂ B₁≡B₂ ok) =
    ΠΣ-cong (soundnessConv↑ A₁≡A₂) (soundnessConv↑ B₁≡B₂) ok
  soundnessConv↓ (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    Id-cong (soundnessConv↑ A₁≡A₂) (soundnessConv↑Term t₁≡t₂)
      (soundnessConv↑Term u₁≡u₂)

  -- Algorithmic equality of terms is well-formed.
  soundnessConv↑Term : ∀ {a b A} → Γ ⊢ a [conv↑] b ∷ A → Γ ⊢ a ≡ b ∷ A
  soundnessConv↑Term ([↑]ₜ B t′ u′ (D , _) (d , _) (d′ , _) t<>u) =
    conv (trans (subset*Term d)
                (trans (soundnessConv↓Term t<>u)
                       (sym′ (subset*Term d′))))
         (sym (subset* D))

  -- Algorithmic equality of terms in WHNF is well-formed.
  soundnessConv↓Term : ∀ {a b A} → Γ ⊢ a [conv↓] b ∷ A → Γ ⊢ a ≡ b ∷ A
  soundnessConv↓Term (ℕ-ins x) = soundness~↓ x
  soundnessConv↓Term (Empty-ins x) = soundness~↓ x
  soundnessConv↓Term (Unitʷ-ins _ t~u) = soundness~↓ t~u
  soundnessConv↓Term (Σʷ-ins x x₁ x₂) =
    let a≡b = soundness~↓ x₂
        _ , neA , _ = ne~↓ x₂
        _ , ⊢a , _ = syntacticEqTerm a≡b
        Σ≡Σ′ = neTypeEq neA x ⊢a
    in  conv a≡b (sym Σ≡Σ′)
  soundnessConv↓Term (ne-ins t u x x₁) =
    let _ , neA , _ = ne~↓ x₁
        _ , t∷M , _ = syntacticEqTerm (soundness~↓ x₁)
        M≡A = neTypeEq neA t∷M t
    in  conv (soundness~↓ x₁) M≡A
  soundnessConv↓Term (univ ⊢A ⊢B A≡B) =
    soundnessConv↓-U ⊢A ⊢B A≡B .proj₁
  soundnessConv↓Term (zero-refl ⊢Γ) = refl (zeroⱼ ⊢Γ)
  soundnessConv↓Term (starʷ-refl ⊢Γ ok _) = refl (starⱼ ⊢Γ ok)
  soundnessConv↓Term (suc-cong c) = suc-cong (soundnessConv↑Term c)
  soundnessConv↓Term (prod-cong x₁ x₂ x₃ ok) =
    prod-cong x₁ (soundnessConv↑Term x₂)
      (soundnessConv↑Term x₃) ok
  soundnessConv↓Term (η-eq x x₁ y y₁ c) =
    η-eq′ x x₁ (soundnessConv↑Term c)
  soundnessConv↓Term (Σ-η ⊢p ⊢r pProd rProd fstConv sndConv) =
    let fst≡ = soundnessConv↑Term fstConv
        snd≡ = soundnessConv↑Term sndConv
    in  Σ-η′ ⊢p ⊢r fst≡ snd≡
  soundnessConv↓Term (η-unit [a] [b] aUnit bUnit ok) =
    η-unit [a] [b] ok
  soundnessConv↓Term
    {Γ} (Id-ins {v₁} {t} {u} {A} {A′} {t′} {u′} ⊢v₁ v₁~v₂) =
    case soundness~↓ v₁~v₂ of λ {
      v₁≡v₂ →
    conv v₁≡v₂
      (                                          $⟨ syntacticEqTerm v₁≡v₂ .proj₂ .proj₁ , ⊢v₁ ⟩
       Γ ⊢ v₁ ∷ Id A′ t′ u′ × Γ ⊢ v₁ ∷ Id A t u  →⟨ uncurry (neTypeEq (ne~↓ v₁~v₂ .proj₂ .proj₁)) ⟩
       Γ ⊢ Id A′ t′ u′ ≡ Id A t u                □) }
  soundnessConv↓Term (rfl-refl t≡u) =
    refl (rflⱼ′ t≡u)

  -- A variant of soundnessConv↓.

  soundnessConv↓-U :
    Γ ⊢ A ∷ U l₁ →
    Γ ⊢ B ∷ U l₂ →
    Γ ⊢ A [conv↓] B →
    Γ ⊢ A ≡ B ∷ U l₁ × l₁ PE.≡ l₂
  soundnessConv↓-U {l₁} {l₂} ⊢A ⊢B (ne {l} A~B) =
    let A≡B             = soundness~↓ A~B
        _ , A-ne , B-ne = ne~↓ A~B
        _ , ⊢A′ , ⊢B′   = syntacticEqTerm A≡B
        U≡U₁            = neTypeEq A-ne ⊢A′ ⊢A
        U≡U₂            = neTypeEq B-ne ⊢B′ ⊢B
    in
      conv A≡B U≡U₁
    , U-injectivity
        (U l₁  ≡˘⟨ U≡U₁ ⟩⊢
         U l   ≡⟨ U≡U₂ ⟩⊢∎
         U l₂  ∎)
    where
    open TyR
  soundnessConv↓-U {l₁} {l₂} ⊢U₁ ⊢U₂ (U-refl {l} _) =
      refl ⊢U₁
    , U-injectivity
        (U l₁      ≡⟨ inversion-U ⊢U₁ ⟩⊢
         U (1+ l)  ≡˘⟨ inversion-U ⊢U₂ ⟩⊢∎
         U l₂      ∎)
    where
    open TyR
  soundnessConv↓-U {l₁} {l₂} ⊢ΠΣA₁A₂ ⊢ΠΣB₁B₂ (ΠΣ-cong A₁≡B₁ A₂≡B₂ ok) =
    let l₃ , l₄ , ⊢A₁ , ⊢A₂ , U≡U₁ , _ = inversion-ΠΣ-U ⊢ΠΣA₁A₂
        l₅ , l₆ , ⊢B₁ , ⊢B₂ , U≡U₂ , _ = inversion-ΠΣ-U ⊢ΠΣB₁B₂
        A₁≡B₁ , l₃≡l₅                  = soundnessConv↑-U ⊢A₁ ⊢B₁ A₁≡B₁
        A₂≡B₂ , l₄≡l₆                  =
          soundnessConv↑-U ⊢A₂
            (stabilityTerm (reflConEq (wfTerm ⊢A₁) ∙ sym (univ A₁≡B₁))
               ⊢B₂)
            A₂≡B₂
    in
      conv (ΠΣ-cong A₁≡B₁ A₂≡B₂ ok) (sym U≡U₁)
    , U-injectivity
        (U l₁          ≡⟨ U≡U₁ ⟩⊢
         U (l₃ ⊔ᵘ l₄)  ≡⟨ PE.cong U $ PE.cong₂ _⊔ᵘ_ l₃≡l₅ l₄≡l₆ ⟩⊢≡
         U (l₅ ⊔ᵘ l₆)  ≡˘⟨ U≡U₂ ⟩⊢∎
         U l₂          ∎)
    where
    open TyR
  soundnessConv↓-U {l₁} {l₂} ⊢Empty₁ ⊢Empty₂ (Empty-refl _) =
      refl ⊢Empty₁
    , U-injectivity
        (U l₁  ≡⟨ inversion-Empty ⊢Empty₁ ⟩⊢
         U 0   ≡˘⟨ inversion-Empty ⊢Empty₂ ⟩⊢∎
         U l₂  ∎)
    where
    open TyR
  soundnessConv↓-U {l₁} {l₂} ⊢Unit₁ ⊢Unit₂ (Unit-refl {l} _ _) =
      refl ⊢Unit₁
    , U-injectivity
        (U l₁  ≡⟨ inversion-Unit-U ⊢Unit₁ .proj₁ ⟩⊢
         U l   ≡˘⟨ inversion-Unit-U ⊢Unit₂ .proj₁ ⟩⊢∎
         U l₂  ∎)
    where
    open TyR
  soundnessConv↓-U {l₁} {l₂} ⊢ℕ₁ ⊢ℕ₂ (ℕ-refl _) =
      refl ⊢ℕ₁
    , U-injectivity
        (U l₁  ≡⟨ inversion-ℕ ⊢ℕ₁ ⟩⊢
         U 0   ≡˘⟨ inversion-ℕ ⊢ℕ₂ ⟩⊢∎
         U l₂  ∎)
    where
    open TyR
  soundnessConv↓-U
    {l₁} {l₂} ⊢IdAt₁t₂ ⊢IdBu₁u₂ (Id-cong A≡B t₁≡u₁ t₂≡u₂) =
    let l₃ , ⊢A , ⊢t₁ , ⊢t₂ , U≡U₁ = inversion-Id-U ⊢IdAt₁t₂
        l₄ , ⊢B , ⊢u₁ , ⊢u₂ , U≡U₂ = inversion-Id-U ⊢IdBu₁u₂
        A≡B , l₃≡l₄                = soundnessConv↑-U ⊢A ⊢B A≡B
    in
      conv
        (Id-cong A≡B (soundnessConv↑Term t₁≡u₁)
           (soundnessConv↑Term t₂≡u₂))
        (sym U≡U₁)
    , U-injectivity
        (U l₁  ≡⟨ U≡U₁ ⟩⊢
         U l₃  ≡⟨ PE.cong U l₃≡l₄ ⟩⊢≡
         U l₄  ≡˘⟨ U≡U₂ ⟩⊢∎
         U l₂  ∎)
    where
    open TyR

  -- A variant of soundnessConv↑.

  soundnessConv↑-U :
    Γ ⊢ A ∷ U l₁ → Γ ⊢ B ∷ U l₂ → Γ ⊢ A [conv↑] B →
    Γ ⊢ A ≡ B ∷ U l₁ × l₁ PE.≡ l₂
  soundnessConv↑-U {A} {l₁} {B} {l₂} ⊢A ⊢B ([↑] A′ B′ A↘A′ B↘B′ A′≡B′) =
    let A″ , A″-type , [ _ , ⊢A″ , A⇒*A″ ] = red-U ⊢A
        B″ , B″-type , [ _ , ⊢B″ , B⇒*B″ ] = red-U ⊢B
        A′≡A″ = whrDet* A↘A′ (univ* A⇒*A″ , typeWhnf A″-type)
        B′≡B″ = whrDet* B↘B′ (univ* B⇒*B″ , typeWhnf B″-type)
        A′≡B′ , l₁≡l₂ =
          soundnessConv↓-U (PE.subst (_ ⊢_∷ _) (PE.sym A′≡A″) ⊢A″)
            (PE.subst (_ ⊢_∷ _) (PE.sym B′≡B″) ⊢B″) A′≡B′
    in
      (A          ⇒*⟨ A⇒*A″ ⟩⊢
       A″         ≡˘⟨ A′≡A″ ⟩⊢≡
       A′ ∷ U l₁  ≡⟨ A′≡B′ ⟩⊢∷
                   ⟨ PE.cong U l₁≡l₂ ⟩≡≡
       B′ ∷ U l₂  ≡⟨ B′≡B″ ⟩⊢∷≡
       B″         ⇐*⟨ B⇒*B″ ⟩⊢∎
       B          ∎)
    , l₁≡l₂
    where
    open TmR
