------------------------------------------------------------------------
-- Soundness of algorithmic equality (in the absence of equality
-- reflection)
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Conversion.Soundness
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  ⦃ no-equality-reflection : No-equality-reflection ⦄
  where

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Typed R
open import Definition.Typed.EqRelInstance R using (eqRelInstance)
open import Definition.Typed.EqualityRelation.Instance R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
import Definition.Typed.Reasoning.Term R as TmR
import Definition.Typed.Reasoning.Type R as TyR
open import Definition.Typed.Stability R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Well-formed R
open import Definition.Conversion R
open import Definition.Conversion.Whnf R
open import Definition.Conversion.Level R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Reduction R
open import Definition.Typed.Consequences.NeTypeEq R

open import Tools.Bool
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

import Data.List as L
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as All
import Data.List.Relation.Unary.Any as Any
import Data.List.Relation.Unary.Any.Properties as Any

private
  variable
    n     : Nat
    Γ     : Con Term n
    A B l₁ l₂ : Term _
    d : Bool

mutual
  -- Algorithmic equality of neutrals is well-formed.
  soundness~↑ : ∀ {k l A} → Γ ⊢ k ~ l ↑ A → Γ ⊢ k ≡ l ∷ A
  soundness~↑ (var-refl x x≡y) = PE.subst (λ y → _ ⊢ _ ≡ var y ∷ _) x≡y (refl x)
  soundness~↑ (lower-cong x) = lower-cong (soundness~↓ x)
  soundness~↑ (app-cong k~l x₁) =
    app-cong (soundness~↓ k~l) (soundnessConv↑Term x₁)
  soundness~↑ (fst-cong x) =
    let p≡ = soundness~↓ x
        ⊢ΣFG = proj₁ (syntacticEqTerm p≡)
        _ , ⊢G , _ = inversion-ΠΣ ⊢ΣFG
    in  fst-cong ⊢G p≡
  soundness~↑ (snd-cong x) =
    let p≡ = soundness~↓ x
        ⊢ΣFG = proj₁ (syntacticEqTerm p≡)
        _ , ⊢G , _ = inversion-ΠΣ ⊢ΣFG
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
        k≡l = soundness~∷ x₁
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

  soundness~∷ : ∀ {k l A} → Γ ⊢ k ~ l ∷ A → Γ ⊢ k ≡ l ∷ A
  soundness~∷ (↑ A≡B k~l) = conv (soundness~↑ k~l) (sym A≡B)

  -- Algorithmic equality of types is well-formed.
  soundnessConv↑ : ∀ {A B} → Γ ⊢ A [conv↑] B → Γ ⊢ A ≡ B
  soundnessConv↑ ([↑] _ _ (D , _) (D′ , _) A′<>B′) =
    trans (subset* D) (trans (soundnessConv↓ A′<>B′) (sym (subset* D′)))

  -- Algorithmic equality of types in WHNF is well-formed.
  soundnessConv↓ : ∀ {A B} → Γ ⊢ A [conv↓] B → Γ ⊢ A ≡ B
  soundnessConv↓ (Level-refl ⊢Γ) = refl (Levelⱼ ⊢Γ)
  soundnessConv↓ (U-cong l₁≡l₂) = U-cong (soundnessConv↑Term l₁≡l₂)
  soundnessConv↓ (Lift-cong l₁≡l₂ F≡H) =
    Lift-cong (soundnessConv↑Term l₁≡l₂) (soundnessConv↑ F≡H)
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
  soundnessConv↓Term (Level-ins x) = soundnessConv↓Level x
  soundnessConv↓Term (ℕ-ins x) = soundness~↓ x
  soundnessConv↓Term (Empty-ins x) = soundness~↓ x
  soundnessConv↓Term (Unitʷ-ins _ (↑ y t~u)) =
    conv (soundness~↑ t~u) (sym y)
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
  soundnessConv↓Term (Lift-η x x₁ x₂ x₃ x₄) =
    Lift-η′ x x₁ (soundnessConv↑Term x₄)
  soundnessConv↓Term (zero-refl ⊢Γ) = refl (zeroⱼ ⊢Γ)
  soundnessConv↓Term (starʷ-refl ⊢Γ ok _) =
    refl (starⱼ ⊢Γ ok)
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
  soundnessConv↓Term (η-unit [a] [b] aUnit bUnit ok η) =
    η-unit [a] [b] ok η
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
    Γ ⊢ A ≡ B ∷ U l₁ × Γ ⊢ l₁ ≡ l₂ ∷ Level
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
  soundnessConv↓-U {l₁} {l₂} ⊢Level₁ ⊢Level₂ (Level-refl _) =
      refl ⊢Level₁
    , U-injectivity
        (U l₁     ≡⟨ inversion-Level ⊢Level₁ ⟩⊢
         U zeroᵘ  ≡˘⟨ inversion-Level ⊢Level₂ ⟩⊢∎
         U l₂     ∎)
    where
    open TyR
  soundnessConv↓-U {l₁} {l₂} ⊢U₁ ⊢U₂ (U-cong {l₁ = l₃} {l₂ = l₄} l₃≡l₄) =
    let l₃≡l₄ = soundnessConv↑Term l₃≡l₄
        U≡U₁ = inversion-U ⊢U₁
        U≡U₂ = inversion-U ⊢U₂
    in
      conv (U-cong l₃≡l₄) (sym U≡U₁)
    , U-injectivity
        (U l₁        ≡⟨ inversion-U ⊢U₁ ⟩⊢
         U (sucᵘ l₃) ≡⟨ U-cong (sucᵘ-cong l₃≡l₄) ⟩⊢
         U (sucᵘ l₄) ≡˘⟨ inversion-U ⊢U₂ ⟩⊢∎
         U l₂        ∎)
    where
    open TyR
  soundnessConv↓-U {l₁} {l₂} ⊢Lift₁ ⊢Lift₂ (Lift-cong {l₁ = l₃} {l₂ = l₄} l₃≡l₄ F≡H) =
    let k₁ , _ , ⊢F , U₁≡ = inversion-Lift∷ ⊢Lift₁
        k₂ , _ , ⊢H , U₂≡ = inversion-Lift∷ ⊢Lift₂
        l₃≡l₄ = soundnessConv↑Term l₃≡l₄
        F≡H , k₁≡k₂ = soundnessConv↑-U ⊢F ⊢H F≡H
    in
      conv (Lift-cong′ l₃≡l₄ F≡H) (sym U₁≡)
    , U-injectivity
        (U l₁           ≡⟨ U₁≡ ⟩⊢
         U (k₁ supᵘ l₃) ≡⟨ U-cong (supᵘ-cong k₁≡k₂ l₃≡l₄) ⟩⊢
         U (k₂ supᵘ l₄) ≡˘⟨ U₂≡ ⟩⊢∎
         U l₂           ∎)
    where
    open TyR
  soundnessConv↓-U {l₁} {l₂} ⊢ΠΣA₁A₂ ⊢ΠΣB₁B₂ (ΠΣ-cong A₁≡B₁ A₂≡B₂ ok) =
    let l₃ , ⊢l₃ , ⊢A₁ , ⊢A₂ , U≡U₁ , _ = inversion-ΠΣ-U ⊢ΠΣA₁A₂
        l₄ , ⊢l₄ , ⊢B₁ , ⊢B₂ , U≡U₂ , _ = inversion-ΠΣ-U ⊢ΠΣB₁B₂
        A₁≡B₁ , l₃≡l₄            = soundnessConv↑-U ⊢A₁ ⊢B₁ A₁≡B₁
        A₂≡B₂ , _                =
          soundnessConv↑-U ⊢A₂
            (stabilityTerm (refl-∙ (sym (univ A₁≡B₁))) ⊢B₂) A₂≡B₂
    in
      conv (ΠΣ-cong ⊢l₃ A₁≡B₁ A₂≡B₂ ok) (sym U≡U₁)
    , U-injectivity
        (U l₁  ≡⟨ U≡U₁ ⟩⊢
         U l₃  ≡⟨ U-cong l₃≡l₄ ⟩⊢
         U l₄  ≡˘⟨ U≡U₂ ⟩⊢∎
         U l₂  ∎)
    where
    open TyR
  soundnessConv↓-U {l₁} {l₂} ⊢Empty₁ ⊢Empty₂ (Empty-refl _) =
      refl ⊢Empty₁
    , U-injectivity
        (U l₁    ≡⟨ inversion-Empty ⊢Empty₁ ⟩⊢
         U zeroᵘ ≡˘⟨ inversion-Empty ⊢Empty₂ ⟩⊢∎
         U l₂    ∎)
    where
    open TyR
  soundnessConv↓-U {l₁} {l₂} ⊢Unit₁ ⊢Unit₂ (Unit-refl ⊢Γ ok) =
    let U≡U₁ , _ = inversion-Unit-U ⊢Unit₁
        U≡U₂ , _ = inversion-Unit-U ⊢Unit₂
    in
      refl (conv (Unitⱼ ⊢Γ ok) (sym U≡U₁))
    , U-injectivity
        (U l₁     ≡⟨ U≡U₁ ⟩⊢
         U zeroᵘ  ≡˘⟨ U≡U₂ ⟩⊢∎
         U l₂     ∎)
    where
    open TyR
  soundnessConv↓-U {l₁} {l₂} ⊢ℕ₁ ⊢ℕ₂ (ℕ-refl _) =
      refl ⊢ℕ₁
    , U-injectivity
        (U l₁     ≡⟨ inversion-ℕ ⊢ℕ₁ ⟩⊢
         U zeroᵘ  ≡˘⟨ inversion-ℕ ⊢ℕ₂ ⟩⊢∎
         U l₂     ∎)
    where
    open TyR
  soundnessConv↓-U
    {l₁} {l₂} ⊢IdAt₁t₂ ⊢IdBu₁u₂ (Id-cong A≡B t₁≡u₁ t₂≡u₂) =
    let l₃ , ⊢A , ⊢t₁ , ⊢t₂ , U≡U₁ = inversion-Id-U ⊢IdAt₁t₂
        l₄ , ⊢B , ⊢u₁ , ⊢u₂ , U≡U₂ = inversion-Id-U ⊢IdBu₁u₂
        A≡B , l₃≡l₄          = soundnessConv↑-U ⊢A ⊢B A≡B
    in
      conv
        (Id-cong A≡B (soundnessConv↑Term t₁≡u₁)
           (soundnessConv↑Term t₂≡u₂))
        (sym U≡U₁)
    , U-injectivity
        (U l₁  ≡⟨ U≡U₁ ⟩⊢
         U l₃  ≡⟨ U-cong l₃≡l₄ ⟩⊢
         U l₄  ≡˘⟨ U≡U₂ ⟩⊢∎
         U l₂  ∎)
    where
    open TyR

  -- A variant of soundnessConv↑.

  soundnessConv↑-U :
    Γ ⊢ A ∷ U l₁ → Γ ⊢ B ∷ U l₂ → Γ ⊢ A [conv↑] B →
    Γ ⊢ A ≡ B ∷ U l₁ × Γ ⊢ l₁ ≡ l₂ ∷ Level
  soundnessConv↑-U {A} {l₁} {B} {l₂} ⊢A ⊢B ([↑] A′ B′ A↘A′ B↘B′ A′≡B′) =
    let A″ , A″-type , A⇒*A″ = red-U ⊢A
        B″ , B″-type , B⇒*B″ = red-U ⊢B
        _ , _ , ⊢A″ = wf-⊢≡∷ (subset*Term A⇒*A″)
        _ , _ , ⊢B″ = wf-⊢≡∷ (subset*Term B⇒*B″)
        A′≡A″ = whrDet* A↘A′ (univ* A⇒*A″ , typeWhnf A″-type)
        B′≡B″ = whrDet* B↘B′ (univ* B⇒*B″ , typeWhnf B″-type)
        A′≡B′ , l₁≡l₂ =
          soundnessConv↓-U (PE.subst (_ ⊢_∷ _) (PE.sym A′≡A″) ⊢A″)
            (PE.subst (_ ⊢_∷ _) (PE.sym B′≡B″) ⊢B″) A′≡B′
    in
      (A          ⇒*⟨ A⇒*A″ ⟩⊢
       A″         ≡˘⟨ A′≡A″ ⟩⊢≡
       A′ ∷ U l₁  ≡⟨ A′≡B′ ⟩⊢∷
                   ⟨ U-cong l₁≡l₂ ⟩≡
       B′ ∷ U l₂  ≡⟨ B′≡B″ ⟩⊢∷≡
       B″         ⇐*⟨ B⇒*B″ ⟩⊢∎
       B          ∎)
    , l₁≡l₂
    where
    open TmR

  -- Algorithmic equality of levels is well-formed.

  soundnessConv↓Level : ∀ {a b} → Γ ⊢ a [conv↓] b ∷Level → Γ ⊢ a ≡ b ∷ Level
  soundnessConv↓Level ([↓]ˡ aᵛ bᵛ a≡ b≡ a≡b) =
    let a≡ = soundness↓ᵛ a≡
        b≡ = soundness↓ᵛ b≡
        ⊢Level , _ , _ = syntacticEqTerm a≡
        ⊢Γ = wf ⊢Level
    in trans a≡
        (trans (soundness-≡ᵛ ⊢Γ aᵛ bᵛ a≡b)
          (sym′ b≡))

  -- If t normalises to a level view, then t is well-formed.

  wf↑ᵛ : ∀ {t v} → Γ ⊢ t ↑ᵛ v → Γ ⊢ t ∷ Level
  wf↑ᵛ ([↑]ᵛ (d , _) t↓v) = redFirst*Term d

  wf↓ᵛ : ∀ {t v} → Γ ⊢ t ↓ᵛ v → Γ ⊢ t ∷ Level
  wf↓ᵛ (zeroᵘₙ x) = zeroᵘⱼ x
  wf↓ᵛ (sucᵘₙ x x₁) = sucᵘⱼ (wf↑ᵛ x₁)
  wf↓ᵛ (neₙ x) = wf~ᵛ x

  wf~ᵛ : ∀ {t v} → Γ ⊢ t ~ᵛ v → Γ ⊢ t ∷ Level
  wf~ᵛ (supᵘˡₙ x x₁ x₂) = supᵘⱼ (wf~ᵛ x₁) (wf↑ᵛ x₂)
  wf~ᵛ (supᵘʳₙ x x₁ x₂) = supᵘⱼ (sucᵘⱼ (wf↑ᵛ x₁)) (wf~ᵛ x₂)
  wf~ᵛ (neₙ [t] x) = syntacticEqTerm (soundness~↓ [t]) .proj₂ .proj₁

  -- A level view in a well-formed context induces a well-formed level.

  ⊢LevelAtom : ⊢ Γ → (l : LevelAtom Γ) → Γ ⊢ LevelAtom→Term l ∷ Level
  ⊢LevelAtom ⊢Γ zeroᵘ = zeroᵘⱼ ⊢Γ
  ⊢LevelAtom ⊢Γ (ne t≡t) =
    let _ , ⊢t , _ = syntacticEqTerm (soundness~↓ t≡t)
    in ⊢t

  ⊢Level⁺ : ⊢ Γ → (l : Level⁺ Γ) → Γ ⊢ Level⁺→Term l ∷ Level
  ⊢Level⁺ ⊢Γ (Nat.zero , l) = ⊢LevelAtom ⊢Γ l
  ⊢Level⁺ ⊢Γ (1+ n , l) = sucᵘⱼ (⊢Level⁺ ⊢Γ (n , l))

  ⊢Levelᵛ : ⊢ Γ → (l : Levelᵛ Γ) → Γ ⊢ Levelᵛ→Term l ∷ Level
  ⊢Levelᵛ ⊢Γ L.[] = zeroᵘⱼ ⊢Γ
  ⊢Levelᵛ ⊢Γ (x L.∷ l) = supᵘⱼ (⊢Level⁺ ⊢Γ x) (⊢Levelᵛ ⊢Γ l)

  ⊢suc⁺ : ⊢ Γ → (x : Level⁺ Γ) → Γ ⊢ Level⁺→Term (suc⁺ x) ∷ Level
  ⊢suc⁺ ⊢Γ (n , a) = sucᵘⱼ (⊢sucᵘᵏ (⊢LevelAtom ⊢Γ a))

  ⊢map-suc⁺ : ⊢ Γ → (l : Levelᵛ Γ) → Γ ⊢ Levelᵛ→Term (map-suc⁺ l) ∷ Level
  ⊢map-suc⁺ ⊢Γ L.[] = zeroᵘⱼ ⊢Γ
  ⊢map-suc⁺ ⊢Γ (x L.∷ l) = supᵘⱼ (⊢suc⁺ ⊢Γ x) (⊢map-suc⁺ ⊢Γ l)

  -- The reification of a level view commutes with the level operations.

  Levelᵛ→Term-suc : ⊢ Γ → (l : Levelᵛ Γ) → Γ ⊢ sucᵘ (Levelᵛ→Term l) ≡ Levelᵛ→Term (sucᵛ l) ∷ Level
  Levelᵛ→Term-suc ⊢Γ L.[] = sym′ (supᵘ-zeroʳ (sucᵘⱼ (zeroᵘⱼ ⊢Γ)))
  Levelᵛ→Term-suc ⊢Γ (x L.∷ l) =
    trans (sym′ (supᵘ-sucᵘ (⊢Level⁺ ⊢Γ x) (⊢Levelᵛ ⊢Γ l)))
      (trans (supᵘ-cong (refl (sucᵘⱼ (⊢Level⁺ ⊢Γ x))) (Levelᵛ→Term-suc ⊢Γ l))
        (supᵘ-comm-assoc (sucᵘⱼ (⊢Level⁺ ⊢Γ x)) (sucᵘⱼ (zeroᵘⱼ ⊢Γ)) (⊢map-suc⁺ ⊢Γ l)))

  Levelᵛ→Term-sup : ⊢ Γ → (t u : Levelᵛ Γ) → Γ ⊢ Levelᵛ→Term t supᵘ Levelᵛ→Term u ≡ Levelᵛ→Term (supᵛ t u) ∷ Level
  Levelᵛ→Term-sup ⊢Γ L.[] x = supᵘ-zeroˡ (⊢Levelᵛ ⊢Γ x)
  Levelᵛ→Term-sup ⊢Γ (x L.∷ t) u = trans (supᵘ-assoc (⊢Level⁺ ⊢Γ x) (⊢Levelᵛ ⊢Γ t) (⊢Levelᵛ ⊢Γ u)) (supᵘ-cong (refl (⊢Level⁺ ⊢Γ x)) (Levelᵛ→Term-sup ⊢Γ t u))

  Levelᵛ→Term-sup-map-suc⁺ : ⊢ Γ → (t u : Levelᵛ Γ) → Γ ⊢ Levelᵛ→Term (map-suc⁺ t) supᵘ Levelᵛ→Term u ≡ Levelᵛ→Term (supᵛ (map-suc⁺ t) u) ∷ Level
  Levelᵛ→Term-sup-map-suc⁺ ⊢Γ L.[] u = supᵘ-zeroˡ (⊢Levelᵛ ⊢Γ u)
  Levelᵛ→Term-sup-map-suc⁺ ⊢Γ (x L.∷ t) u = trans (supᵘ-assoc (⊢suc⁺ ⊢Γ x) (⊢map-suc⁺ ⊢Γ t) (⊢Levelᵛ ⊢Γ u)) (supᵘ-cong (refl (⊢suc⁺ ⊢Γ x)) (Levelᵛ→Term-sup-map-suc⁺ ⊢Γ t u))

  Levelᵛ→Term-sup-sucᵛ : ⊢ Γ → (t u : Levelᵛ Γ) → Γ ⊢ Levelᵛ→Term (sucᵛ t) supᵘ Levelᵛ→Term u ≡ Levelᵛ→Term (supᵛ (sucᵛ t) u) ∷ Level
  Levelᵛ→Term-sup-sucᵛ ⊢Γ t u = trans (supᵘ-assoc (sucᵘⱼ (zeroᵘⱼ ⊢Γ)) (⊢map-suc⁺ ⊢Γ t) (⊢Levelᵛ ⊢Γ u)) (supᵘ-cong (refl (sucᵘⱼ (zeroᵘⱼ ⊢Γ))) (Levelᵛ→Term-sup-map-suc⁺ ⊢Γ t u))

  -- If t normalises to a level view v, then t is equal to the reification of v.

  soundness↑ᵛ : ∀ {t} {v : Levelᵛ Γ} → Γ ⊢ t ↑ᵛ v → Γ ⊢ t ≡ Levelᵛ→Term v ∷ Level
  soundness↑ᵛ ([↑]ᵛ (d , _) t↓v) = trans (subset*Term d) (soundness↓ᵛ t↓v)

  soundness↓ᵛ : ∀ {t} {v : Levelᵛ Γ} → Γ ⊢ t ↓ᵛ v → Γ ⊢ t ≡ Levelᵛ→Term v ∷ Level
  soundness↓ᵛ (zeroᵘₙ x) = refl (zeroᵘⱼ x)
  soundness↓ᵛ (sucᵘₙ {v′} PE.refl t≡v) =
    trans (sucᵘ-cong (soundness↑ᵛ t≡v))
      (Levelᵛ→Term-suc (wfTerm (wf↑ᵛ t≡v)) v′)
  soundness↓ᵛ (neₙ x) = soundness~ᵛ x

  soundness~ᵛ : ∀ {t} {v : Levelᵛ Γ} → Γ ⊢ t ~ᵛ v → Γ ⊢ t ≡ Levelᵛ→Term v ∷ Level
  soundness~ᵛ (supᵘˡₙ {v′} {v″} y t~ u↑) =
    trans (supᵘ-cong (soundness~ᵛ t~) (soundness↑ᵛ u↑))
      (PE.subst (_ ⊢ _ ≡_∷ _) (PE.cong Levelᵛ→Term (PE.sym y))
        (Levelᵛ→Term-sup (wfTerm (wf~ᵛ t~)) v′ v″))
  soundness~ᵛ (supᵘʳₙ {v′} {v″} PE.refl t↑ u~) =
    let ⊢Γ = wfTerm (wf↑ᵛ t↑)
    in trans (supᵘ-cong (sucᵘ-cong (soundness↑ᵛ t↑)) (soundness~ᵛ u~))
        (trans (supᵘ-cong (Levelᵛ→Term-suc ⊢Γ v′) (refl (⊢Levelᵛ ⊢Γ v″))) (Levelᵛ→Term-sup-sucᵛ ⊢Γ v′ v″))
  soundness~ᵛ (neₙ [t′] PE.refl) =
    let ⊢Level , ⊢t′ , _ = syntacticEqTerm (soundness~↓ [t′])
    in sym′ (supᵘ-zeroʳ ⊢t′)

  -- Comparison and equality of level views is sound with respect to reification.

  soundness-≤ᵃ
    : ⊢ Γ
    → ∀ (t u : LevelAtom Γ)
    → ≤ᵃ d t u
    → Γ ⊢ LevelAtom→Term t ≤ LevelAtom→Term u ∷Level
  soundness-≤ᵃ ⊢Γ t u zeroᵘ≤ = supᵘ-zeroˡ (⊢LevelAtom ⊢Γ u)
  soundness-≤ᵃ ⊢Γ t u (ne≤ (ne≡ x)) = supᵘ-subᵏ (⊢≤-refl (soundness~↓ x))
  soundness-≤ᵃ ⊢Γ t u (ne≤ (ne≡' x)) = supᵘ-subᵏ (⊢≤-refl (sym′ (soundness~↓ x)))

  soundness-≤⁺
    : ⊢ Γ
    → ∀ (t u : Level⁺ Γ)
    → ≤⁺ d t u
    → Γ ⊢ Level⁺→Term t ≤ Level⁺→Term u ∷Level
  soundness-≤⁺ ⊢Γ (n , t) (m , u) (n≤m , t≤u) = ≤-sucᵘᵏ n≤m (soundness-≤ᵃ ⊢Γ _ _ t≤u)

  soundness-≤⁺ᵛ
    : ⊢ Γ
    → ∀ (t : Level⁺ Γ) (u : Levelᵛ Γ)
    → ≤⁺ᵛ d t u
    → Γ ⊢ Level⁺→Term t ≤ Levelᵛ→Term u ∷Level
  soundness-≤⁺ᵛ ⊢Γ t (u L.∷ us) (Any.here px) =
    let ⊢t = ⊢Level⁺ ⊢Γ t
        ⊢u = ⊢Level⁺ ⊢Γ u
        ⊢us = ⊢Levelᵛ ⊢Γ us
        ⊢Level = syntacticTerm ⊢t
    in trans (sym′ (supᵘ-assoc ⊢t ⊢u ⊢us))
      (supᵘ-cong (soundness-≤⁺ ⊢Γ _ _ px) (refl ⊢us))
  soundness-≤⁺ᵛ ⊢Γ t (u L.∷ us) (Any.there x) =
    let ⊢t = ⊢Level⁺ ⊢Γ t
        ⊢u = ⊢Level⁺ ⊢Γ u
        ⊢us = ⊢Levelᵛ ⊢Γ us
    in trans (supᵘ-comm-assoc ⊢t ⊢u ⊢us)
      (supᵘ-cong (refl ⊢u) (soundness-≤⁺ᵛ ⊢Γ _ _ x))
  soundness-≤⁺ᵛ ⊢Γ t L.[] ()

  soundness-≤ᵛ
    : ⊢ Γ
    → ∀ (t u : Levelᵛ Γ)
    → ≤ᵛ d t u
    → Γ ⊢ Levelᵛ→Term t ≤ Levelᵛ→Term u ∷Level
  soundness-≤ᵛ ⊢Γ t u All.[] = supᵘ-zeroˡ (⊢Levelᵛ ⊢Γ u)
  soundness-≤ᵛ ⊢Γ (t L.∷ ts) u (px All.∷ t≤u) =
    let ⊢t = ⊢Level⁺ ⊢Γ t
        ⊢ts = ⊢Levelᵛ ⊢Γ ts
        ⊢u = ⊢Levelᵛ ⊢Γ u
    in trans (supᵘ-assoc ⊢t ⊢ts ⊢u)
      (trans (supᵘ-cong (refl ⊢t) (soundness-≤ᵛ ⊢Γ ts u t≤u))
        (soundness-≤⁺ᵛ ⊢Γ t u px))

  soundness-≡ᵛ
    : ⊢ Γ
    → ∀ (t u : Levelᵛ Γ)
    → t ≡ᵛ u
    → Γ ⊢ Levelᵛ→Term t ≡ Levelᵛ→Term u ∷ Level
  soundness-≡ᵛ ⊢Γ t u (t≤u , u≤t) =
    trans (sym′ (soundness-≤ᵛ ⊢Γ u t u≤t))
      (trans (supᵘ-comm (⊢Levelᵛ ⊢Γ u) (⊢Levelᵛ ⊢Γ t))
        (soundness-≤ᵛ ⊢Γ t u t≤u))
