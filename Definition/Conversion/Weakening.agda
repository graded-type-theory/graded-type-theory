------------------------------------------------------------------------
-- The algorithmic equality is closed under weakening (in the absence
-- of equality reflection)
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Conversion.Weakening
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  ⦃ no-equality-reflection : No-equality-reflection ⦄
  where

open import Definition.Untyped M as U hiding (wk)
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Weakening R
open import Definition.Typed.EqRelInstance R using (eqRelInstance)
open import Definition.Conversion R
open import Definition.Conversion.Level R
open import Definition.Conversion.Soundness R
open import Definition.LogicalRelation R ⦃ eqRelInstance ⦄
import Definition.LogicalRelation.Weakening R ⦃ eqRelInstance ⦄ as W

open import Tools.Bool
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
import Tools.PropositionalEquality as PE
open import Tools.Product

import Data.List as L
import Data.List.Properties as L
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.Any as Any

private
  variable
    m n : Nat
    Δ Γ : Con Term n
    ρ : Wk m n
    p r : M
    d : Bool

mutual
  -- Weakening of algorithmic equality of neutrals.
  wk~↑ : ∀ {t u A Γ Δ} ([ρ] : ρ ∷ʷ Δ ⊇ Γ)
      → Γ ⊢ t ~ u ↑ A
      → Δ ⊢ U.wk ρ t ~ U.wk ρ u ↑ U.wk ρ A
  wk~↑ {ρ} [ρ] (var-refl x₁ x≡y) =
    var-refl (wkTerm [ρ] x₁) (PE.cong (wkVar ρ) x≡y)
  wk~↑ [ρ] (lower-cong x) =
    lower-cong (wk~↓ [ρ] x)
  wk~↑ ρ (app-cong {B} t~u x) =
    PE.subst (λ x → _ ⊢ _ ~ _ ↑ x) (PE.sym (wk-β B))
             (app-cong (wk~↓ ρ t~u) (wkConv↑Term ρ x))
  wk~↑ ρ (fst-cong p~r) =
    fst-cong (wk~↓ ρ p~r)
  wk~↑ ρ (snd-cong {B} p~r) =
    PE.subst (λ x → _ ⊢ _ ~ _ ↑ x)
             (PE.sym (wk-β B))
             (snd-cong (wk~↓ ρ p~r))
  wk~↑ [ρ] (natrec-cong {A₁} x x₁ x₂ t~u) =
    let ⊢Δ   = wf-∷ʷ⊇ [ρ]
        Δℕ⊢F =
          wk (liftʷʷ [ρ] (ℕⱼ ⊢Δ))
            (proj₁ (syntacticEq (soundnessConv↑ x)))
    in
    PE.subst (_⊢_~_↑_ _ _ _) (PE.sym (wk-β A₁)) $
    natrec-cong (wkConv↑ (liftʷ (∷ʷ⊇→∷⊇ [ρ]) (ℕⱼ ⊢Δ)) x)
      (PE.subst (_⊢_[conv↑]_∷_ _ _ _) (wk-β A₁) $
       wkConv↑Term [ρ] x₁)
      (PE.subst (_⊢_[conv↑]_∷_ _ _ _) (wk-β-natrec _ A₁) $
       wkConv↑Term (liftʷ (lift (∷ʷ⊇→∷⊇ [ρ])) Δℕ⊢F) x₂)
      (wk~↓ [ρ] t~u)
  wk~↑
    {ρ} {Δ} [ρ]
    (prodrec-cong {C = C} {E} {g} {h} {u} {v} x g~h x₁) =
    let ρg~ρh = wk~↓ [ρ] g~h
        ⊢ρΣ , _ , _ = syntacticEqTerm (soundness~↓ ρg~ρh)
        _ , ⊢ρG , _ = inversion-ΠΣ ⊢ρΣ
        u↓v = PE.subst (λ x → _ ⊢ U.wk (liftn ρ 2) u [conv↑] U.wk (liftn ρ 2) v ∷ x)
                       (wk-β-prodrec ρ C)
                       (wkConv↑Term (liftʷ (lift (∷ʷ⊇→∷⊇ [ρ])) ⊢ρG) x₁)
    in  PE.subst  (λ x → _ ⊢ U.wk ρ (prodrec _ _ _ C g u) ~
                           U.wk ρ (prodrec _ _ _ E h v) ↑ x)
                  (PE.sym (wk-β C))
                  (prodrec-cong (wkConv↑ (liftʷʷ [ρ] ⊢ρΣ) x) ρg~ρh
                     u↓v)
  wk~↑ [ρ] (emptyrec-cong x t~u) =
    emptyrec-cong (wkConv↑ [ρ] x) (wk~↓ [ρ] t~u)
  wk~↑ [ρ] (unitrec-cong {A₁} l₁≡l₂ x x₁ x₂ no-η) =
    let k~l = wk~∷ [ρ] x₁
        ⊢Unit , _ = syntacticEqTerm (soundness~∷ k~l)
        u↑v = PE.subst (_⊢_[conv↑]_∷_ _ _ _)
                       (wk-β A₁)
                       (wkConv↑Term [ρ] x₂)
    in  PE.subst (_⊢_~_↑_ _ _ _)
                 (PE.sym (wk-β A₁))
                 (unitrec-cong (wkConv↑Term [ρ] l₁≡l₂) (wkConv↑ (liftʷʷ [ρ] ⊢Unit) x) k~l u↑v
                    no-η)
  wk~↑
    {ρ} {Δ} [ρ]
    (J-cong {A₁} {B₁} {B₂} A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁~w₂ ≡Id) =
    case syntacticEq (soundnessConv↑ A₁≡A₂) .proj₁ of λ {
      ⊢A₁ →
    case syntacticEqTerm (soundnessConv↑Term t₁≡t₂) .proj₂ .proj₁ of λ {
      ⊢t₁ →
    case wk [ρ] ⊢A₁ of λ {
      ⊢wk-ρ-A₁ →
    PE.subst (_ ⊢ J _ _ _ _ _ _ _ _ ~ _ ↑_)
      (PE.sym $ wk-β-doubleSubst _ B₁ _ _) $
    J-cong (wkConv↑ [ρ] A₁≡A₂) (wkConv↑Term [ρ] t₁≡t₂)
      (PE.subst
         (λ Id →
            Δ ∙ U.wk ρ A₁ ∙ Id ⊢
              U.wk (lift (lift ρ)) B₁ [conv↑] U.wk (lift (lift ρ)) B₂)
         (PE.cong₂ (λ A t → Id A t (var x0))
            (PE.sym $ wk1-wk≡lift-wk1 _ _)
            (PE.sym $ wk1-wk≡lift-wk1 _ _)) $
       wkConv↑
         (liftʷ (lift (∷ʷ⊇→∷⊇ [ρ])) $
          Idⱼ′
            (PE.subst₂ (_⊢_∷_ _)
               (PE.sym $ lift-wk1 _ _)
               (PE.sym $ lift-wk1 _ _) $
             wkTerm (stepʷʷ [ρ] ⊢wk-ρ-A₁) ⊢t₁)
            (PE.subst (_⊢_∷_ _ _) (wk1-wk≡lift-wk1 _ _) $
             var (∙ ⊢wk-ρ-A₁) here))
         B₁≡B₂)
      (PE.subst (_⊢_[conv↑]_∷_ _ _ _) (wk-β-doubleSubst _ B₁ _ _) $
       wkConv↑Term [ρ] u₁≡u₂)
      (wkConv↑Term [ρ] v₁≡v₂) (wk~↓ [ρ] w₁~w₂)
      (wkEq [ρ] ≡Id) }}}
  wk~↑ [ρ] (K-cong {B₁} A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁~v₂ ≡Id ok) =
    case syntacticEqTerm (soundnessConv↑Term t₁≡t₂) .proj₂ .proj₁ of λ {
      ⊢t₁ →
    PE.subst (_ ⊢ K _ _ _ _ _ _ ~ _ ↑_)
      (PE.sym $ wk-β B₁) $
    K-cong (wkConv↑ [ρ] A₁≡A₂) (wkConv↑Term [ρ] t₁≡t₂)
      (wkConv↑ (liftʷʷ [ρ] (wk [ρ] (Idⱼ′ ⊢t₁ ⊢t₁))) B₁≡B₂)
      (PE.subst (_⊢_[conv↑]_∷_ _ _ _) (wk-β B₁) $
       wkConv↑Term [ρ] u₁≡u₂)
      (wk~↓ [ρ] v₁~v₂) (wkEq [ρ] ≡Id) ok }
  wk~↑ [ρ] ([]-cong-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁~v₂ ≡Id ok) =
    []-cong-cong (wkConv↑ [ρ] A₁≡A₂) (wkConv↑Term [ρ] t₁≡t₂)
      (wkConv↑Term [ρ] u₁≡u₂) (wk~↓ [ρ] v₁~v₂) (wkEq [ρ] ≡Id)
      ok

  -- Weakening of algorithmic equality of neutrals in WHNF.
  wk~↓ : ∀ {t u A Γ Δ} ([ρ] : ρ ∷ʷ Δ ⊇ Γ)
      → Γ ⊢ t ~ u ↓ A
      → Δ ⊢ U.wk ρ t ~ U.wk ρ u ↓ U.wk ρ A
  wk~↓ {ρ} [ρ] ([~] A₁ D k~l) =
    [~] (U.wk ρ A₁) (wkRed↘ [ρ] D) (wk~↑ [ρ] k~l)

  wk~∷ : ∀ {t u A Γ Δ} ([ρ] : ρ ∷ʷ Δ ⊇ Γ)
      → Γ ⊢ t ~ u ∷ A
      → Δ ⊢ U.wk ρ t ~ U.wk ρ u ∷ U.wk ρ A
  wk~∷ [ρ] (↑ A≡B t~u) = ↑ (wkEq [ρ] A≡B) (wk~↑ [ρ] t~u)

  -- Weakening of algorithmic equality of types.
  wkConv↑ : ∀ {A B Γ Δ} ([ρ] : ρ ∷ʷ Δ ⊇ Γ)
          → Γ ⊢ A [conv↑] B
          → Δ ⊢ U.wk ρ A [conv↑] U.wk ρ B
  wkConv↑ {ρ} [ρ] ([↑] A′ B′ D D′ A′<>B′) =
    [↑] (U.wk ρ A′) (U.wk ρ B′) (wkRed↘ [ρ] D) (wkRed↘ [ρ] D′)
      (wkConv↓ [ρ] A′<>B′)

  -- Weakening of algorithmic equality of types in WHNF.
  wkConv↓ : ∀ {A B Γ Δ} ([ρ] : ρ ∷ʷ Δ ⊇ Γ)
         → Γ ⊢ A [conv↓] B
         → Δ ⊢ U.wk ρ A [conv↓] U.wk ρ B
  wkConv↓ ρ (Level-refl x) = Level-refl (wf-∷ʷ⊇ ρ)
  wkConv↓ ρ (U-cong x) = U-cong (wkConv↑Term ρ x)
  wkConv↓ ρ (Lift-cong l₁≡l₂ F≡H) =
    Lift-cong (wkConv↑Term ρ l₁≡l₂) (wkConv↑ ρ F≡H)
  wkConv↓ ρ (ℕ-refl x) = ℕ-refl (wf-∷ʷ⊇ ρ)
  wkConv↓ ρ (Empty-refl x) = Empty-refl (wf-∷ʷ⊇ ρ)
  wkConv↓ ρ (Unit-cong x ok) = Unit-cong (wkConv↑Term ρ x) ok
  wkConv↓ ρ (ne x) = ne (wk~↓ ρ x)
  wkConv↓ ρ (ΠΣ-cong A<>B A<>B₁ ok) =
    let ⊢ρF = wk ρ (syntacticEq (soundnessConv↑ A<>B) .proj₁) in
    ΠΣ-cong (wkConv↑ ρ A<>B) (wkConv↑ (liftʷʷ ρ ⊢ρF) A<>B₁) ok
  wkConv↓ ρ (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    Id-cong (wkConv↑ ρ A₁≡A₂) (wkConv↑Term ρ t₁≡t₂)
      (wkConv↑Term ρ u₁≡u₂)

  -- Weakening of algorithmic equality of terms.
  wkConv↑Term : ∀ {t u A Γ Δ} ([ρ] : ρ ∷ʷ Δ ⊇ Γ)
             → Γ ⊢ t [conv↑] u ∷ A
             → Δ ⊢ U.wk ρ t [conv↑] U.wk ρ u ∷ U.wk ρ A
  wkConv↑Term {ρ} [ρ] ([↑]ₜ B t′ u′ D d d′ t<>u) =
    [↑]ₜ (U.wk ρ B) (U.wk ρ t′) (U.wk ρ u′)
         (wkRed↘ [ρ] D) (wkRed↘Term [ρ] d) (wkRed↘Term [ρ] d′)
         (wkConv↓Term [ρ] t<>u)

  wkLevelAtom : ρ ∷ʷ Δ ⊇ Γ → LevelAtom Γ → LevelAtom Δ
  wkLevelAtom [ρ] zeroᵘ = zeroᵘ
  wkLevelAtom [ρ] (ne x) = ne (wk~↓ [ρ] x)
  wkLevelPlus : ρ ∷ʷ Δ ⊇ Γ → LevelPlus Γ → LevelPlus Δ
  wkLevelPlus [ρ] (n , l) = n , wkLevelAtom [ρ] l
  wkLevelView : ρ ∷ʷ Δ ⊇ Γ → LevelView Γ → LevelView Δ
  wkLevelView [ρ] L.[] = L.[]
  wkLevelView [ρ] (x L.∷ xs) = wkLevelPlus [ρ] x L.∷ wkLevelView [ρ] xs

  wk-sucᵘᵏ : ∀ {t} k → sucᵘᵏ k (U.wk ρ t) PE.≡ U.wk ρ (sucᵘᵏ k t)
  wk-sucᵘᵏ (Nat.zero) = PE.refl
  wk-sucᵘᵏ (1+ k) = PE.cong sucᵘ (wk-sucᵘᵏ k)

  wkLevelAtom→Term : ([ρ] : ρ ∷ʷ Δ ⊇ Γ) (t : LevelAtom Γ) → LevelAtom→Term (wkLevelAtom [ρ] t) PE.≡ U.wk ρ (LevelAtom→Term t)
  wkLevelAtom→Term [ρ] zeroᵘ = PE.refl
  wkLevelAtom→Term [ρ] (ne x) = PE.refl
  wkLevelPlus→Term : ([ρ] : ρ ∷ʷ Δ ⊇ Γ) (t : LevelPlus Γ) → LevelPlus→Term (wkLevelPlus [ρ] t) PE.≡ U.wk ρ (LevelPlus→Term t)
  wkLevelPlus→Term [ρ] (n , a) = PE.trans (PE.cong (sucᵘᵏ n) (wkLevelAtom→Term [ρ] a)) (wk-sucᵘᵏ n)
  wkLevelView→Term : ∀ {t} → ([ρ] : ρ ∷ʷ Δ ⊇ Γ) → LevelView→Term (wkLevelView [ρ] t) PE.≡ U.wk ρ (LevelView→Term t)
  wkLevelView→Term {t = L.[]} [ρ] = PE.refl
  wkLevelView→Term {t = x L.∷ t} [ρ] = PE.cong₂ _maxᵘ_ (wkLevelPlus→Term [ρ] x) (wkLevelView→Term [ρ])

  wk-sucᵛ : ([ρ] : ρ ∷ʷ Δ ⊇ Γ) → (v v′ : LevelView Γ) → v PE.≡ sucᵛ v′ → wkLevelView [ρ] v PE.≡ sucᵛ (wkLevelView [ρ] v′)
  wk-sucᵛ [ρ] v v′ PE.refl = PE.cong (_ L.∷_) (wk-map-suc⁺ [ρ] _ _ PE.refl)

  wk-map-suc⁺ : ([ρ] : ρ ∷ʷ Δ ⊇ Γ) → (v v′ : LevelView Γ) → v PE.≡ map-suc⁺ v′ → wkLevelView [ρ] v PE.≡ map-suc⁺ (wkLevelView [ρ] v′)
  wk-map-suc⁺ [ρ] L.[] L.[] PE.refl = PE.refl
  wk-map-suc⁺ [ρ] L.[] (x L.∷ v′) ()
  wk-map-suc⁺ [ρ] (x L.∷ v) L.[] ()
  wk-map-suc⁺ [ρ] ((n , a) L.∷ v) ((n′ , a′) L.∷ v′) PE.refl = PE.cong (_ L.∷_) (wk-map-suc⁺ [ρ] v v′ PE.refl)

  wkLevelPlus-cong : ∀ ([ρ] : ρ ∷ʷ Δ ⊇ Γ) (a b : LevelPlus Γ) → a PE.≡ b → wkLevelPlus [ρ] a PE.≡ wkLevelPlus [ρ] b
  wkLevelPlus-cong [ρ] a b PE.refl = PE.refl
  wkLevelView-cong : ∀ ([ρ] : ρ ∷ʷ Δ ⊇ Γ) (a b : LevelView Γ) → a PE.≡ b → wkLevelView [ρ] a PE.≡ wkLevelView [ρ] b
  wkLevelView-cong [ρ] a b PE.refl = PE.refl

  wk-maxᵛ : ([ρ] : ρ ∷ʷ Δ ⊇ Γ) (v v′ v″ : LevelView Γ) → v PE.≡ maxᵛ v′ v″ → wkLevelView [ρ] v PE.≡ maxᵛ (wkLevelView [ρ] v′) (wkLevelView [ρ] v″)
  wk-maxᵛ [ρ] L.[] L.[] v″ PE.refl = PE.refl
  wk-maxᵛ [ρ] L.[] (x L.∷ v′) v″ ()
  wk-maxᵛ [ρ] (x L.∷ v) L.[] v″ PE.refl = PE.refl
  wk-maxᵛ [ρ] (x L.∷ v) (x₁ L.∷ v′) v″ eq =
    let a , b = L.∷-injective eq
    in PE.cong₂ L._∷_ (wkLevelPlus-cong [ρ] x x₁ a) (wk-maxᵛ [ρ] _ _ v″ b)

  wk-↑ᵛ : ([ρ] : ρ ∷ʷ Δ ⊇ Γ) → ∀ {t v} → Γ ⊢ t ↑ᵛ v → Δ ⊢ U.wk ρ t ↑ᵛ wkLevelView [ρ] v
  wk-↑ᵛ [ρ] ([↑]ᵛ d t↓v) = [↑]ᵛ (wkRed↘Term [ρ] d) (wk-↓ᵛ [ρ] t↓v)

  wk-↓ᵛ : ([ρ] : ρ ∷ʷ Δ ⊇ Γ) → ∀ {t v} → Γ ⊢ t ↓ᵛ v → Δ ⊢ U.wk ρ t ↓ᵛ wkLevelView [ρ] v
  wk-↓ᵛ [ρ] (zeroᵘ-↓ᵛ x) = zeroᵘ-↓ᵛ (wf-∷ʷ⊇ [ρ])
  wk-↓ᵛ [ρ] (sucᵘ-↓ᵛ {v} {v′} x₁ t≡u) = sucᵘ-↓ᵛ (wk-sucᵛ [ρ] v _ x₁) (wk-↑ᵛ [ρ] t≡u)
  wk-↓ᵛ {ρ} [ρ] (maxᵘ-↓ᵛ {v} {v′} x x₁ t≡u t≡u₁) = maxᵘ-↓ᵛ (wkWhnf ρ x) (wk-maxᵛ [ρ] v v′ _ x₁) (wk-↑ᵛ [ρ] t≡u) (wk-↑ᵛ [ρ] t≡u₁)
  wk-↓ᵛ [ρ] (ne-↓ᵛ [t′] x₁) = ne-↓ᵛ (wk~↓ [ρ] [t′]) (wkLevelView-cong [ρ] _ _ x₁)

  wk-≡ⁿ : ([ρ] : ρ ∷ʷ Δ ⊇ Γ) → (t u : Term n) → ≡ⁿ Γ t u d → ≡ⁿ Δ (U.wk ρ t) (U.wk ρ u) d
  wk-≡ⁿ [ρ] t u (ne≡ x) = ne≡ (wk~↓ [ρ] x)
  wk-≡ⁿ [ρ] t u (ne≡' x) = ne≡' (wk~↓ [ρ] x)

  wk-≤⁺ : ([ρ] : ρ ∷ʷ Δ ⊇ Γ) → (t u : LevelPlus Γ) → ≤⁺ d t u → ≤⁺ d (wkLevelPlus [ρ] t) (wkLevelPlus [ρ] u)
  wk-≤⁺ [ρ] t u (x , zeroᵘ≤) = x , zeroᵘ≤
  wk-≤⁺ [ρ] t u (x , ne≤ y) = x , ne≤ (wk-≡ⁿ [ρ] _ _ y)

  wk-≤⁺ᵛ : ([ρ] : ρ ∷ʷ Δ ⊇ Γ) → (t : LevelPlus Γ) → (u : LevelView Γ) → ≤⁺ᵛ d t u → ≤⁺ᵛ d (wkLevelPlus [ρ] t) (wkLevelView [ρ] u)
  wk-≤⁺ᵛ [ρ] t u (Any.here px) = Any.here (wk-≤⁺ [ρ] _ _ px)
  wk-≤⁺ᵛ [ρ] t u (Any.there t≤u) = Any.there (wk-≤⁺ᵛ [ρ] _ _ t≤u)

  wk-≤ᵛ : ([ρ] : ρ ∷ʷ Δ ⊇ Γ) → (t u : LevelView Γ) → ≤ᵛ d t u → ≤ᵛ d (wkLevelView [ρ] t) (wkLevelView [ρ] u)
  wk-≤ᵛ [ρ] t u All.[] = All.[]
  wk-≤ᵛ [ρ] t u (px All.∷ t≤u) = wk-≤⁺ᵛ [ρ] _ _ px All.∷ wk-≤ᵛ [ρ] _ _ t≤u

  wk-≡ᵛ : ([ρ] : ρ ∷ʷ Δ ⊇ Γ) → (t u : LevelView Γ) → t ≡ᵛ u → wkLevelView [ρ] t ≡ᵛ wkLevelView [ρ] u
  wk-≡ᵛ [ρ] t u (t≤u , u≤t) = wk-≤ᵛ [ρ] t u t≤u , wk-≤ᵛ [ρ] u t u≤t

  wkConv↓Level : ∀ {t u Γ Δ} ([ρ] : ρ ∷ʷ Δ ⊇ Γ)
             → Γ ⊢ t [conv↓] u ∷Level
             → Δ ⊢ U.wk ρ t [conv↓] U.wk ρ u ∷Level
  wkConv↓Level {ρ = ρ} [ρ] ([↓]ˡ tᵛ uᵛ t≡ u≡ t≡u) =
    [↓]ˡ
      (wkLevelView [ρ] tᵛ) (wkLevelView [ρ] uᵛ)
      (wk-↓ᵛ [ρ] t≡)
      (wk-↓ᵛ [ρ] u≡)
      (wk-≡ᵛ [ρ] _ _ t≡u)

  -- Weakening of algorithmic equality of terms in WHNF.
  wkConv↓Term : ∀ {t u A Γ Δ} ([ρ] : ρ ∷ʷ Δ ⊇ Γ)
             → Γ ⊢ t [conv↓] u ∷ A
             → Δ ⊢ U.wk ρ t [conv↓] U.wk ρ u ∷ U.wk ρ A
  wkConv↓Term ρ (Level-ins x) =
    Level-ins (wkConv↓Level ρ x)
  wkConv↓Term ρ (ℕ-ins x) =
    ℕ-ins (wk~↓ ρ x)
  wkConv↓Term ρ (Empty-ins x) =
    Empty-ins (wk~↓ ρ x)
  wkConv↓Term ρ (Unitʷ-ins ok t~u) =
    Unitʷ-ins ok (wk~∷ ρ t~u)
  wkConv↓Term ρ (Σʷ-ins t u x) =
    Σʷ-ins (wkTerm ρ t) (wkTerm ρ u) (wk~↓ ρ x)
  wkConv↓Term {ρ} [ρ] (ne-ins t u x x₁) =
    ne-ins (wkTerm [ρ] t) (wkTerm [ρ] u) (wkNeutral ρ x) (wk~↓ [ρ] x₁)
  wkConv↓Term ρ (univ x x₁ x₂) =
    univ (wkTerm ρ x) (wkTerm ρ x₁) (wkConv↓ ρ x₂)
  wkConv↓Term {ρ} [ρ] (Lift-η ⊢t ⊢u wt wu lower≡lower) =
    Lift-η (wkTerm [ρ] ⊢t) (wkTerm [ρ] ⊢u) (wkWhnf ρ wt) (wkWhnf ρ wu) (wkConv↑Term [ρ] lower≡lower)
  wkConv↓Term ρ (zero-refl x) = zero-refl (wf-∷ʷ⊇ ρ)
  wkConv↓Term ρ (starʷ-cong x y ok no-η) = starʷ-cong (wkEqTerm ρ x) (wkEqTerm ρ y) ok no-η
  wkConv↓Term ρ (suc-cong t<>u) = suc-cong (wkConv↑Term ρ t<>u)
  wkConv↓Term ρ (prod-cong {G = G} x₁ x₂ x₃ ok) =
    let ⊢ρF = wk ρ (⊢∙→⊢ (wf x₁))
        ⊢ρG = wk (liftʷʷ ρ ⊢ρF) x₁
    in  prod-cong ⊢ρG (wkConv↑Term ρ x₂)
          (PE.subst (λ x → _ ⊢ _ [conv↑] _ ∷ x) (wk-β G)
             (wkConv↑Term ρ x₃))
          ok
  wkConv↓Term {ρ} {Δ} [ρ] (η-eq {F = F} {G = G} x₁ x₂ y y₁ t<>u) =
    let ⊢F , _ = inversion-ΠΣ (syntacticTerm x₁)
        ⊢ρF = wk [ρ] ⊢F
    in
    η-eq (wkTerm [ρ] x₁) (wkTerm [ρ] x₂)
      (wkFunction ρ y) (wkFunction ρ y₁) $
    PE.subst₃ (λ x y z → Δ ∙ U.wk ρ F ⊢ x [conv↑] y ∷ z)
      (PE.cong₃ _∘⟨_⟩_ (PE.sym (wk1-wk≡lift-wk1 _ _)) PE.refl PE.refl)
      (PE.cong₃ _∘⟨_⟩_ (PE.sym (wk1-wk≡lift-wk1 _ _)) PE.refl PE.refl)
      PE.refl $
    wkConv↑Term (liftʷʷ [ρ] ⊢ρF) t<>u
  wkConv↓Term {ρ} [ρ] (Σ-η {B} ⊢p ⊢r pProd rProd fstConv sndConv) =
    Σ-η (wkTerm [ρ] ⊢p)
        (wkTerm [ρ] ⊢r)
        (wkProduct ρ pProd)
        (wkProduct ρ rProd)
        (wkConv↑Term [ρ] fstConv)
        (PE.subst (λ x → _ ⊢ _ [conv↑] _ ∷ x)
                  (wk-β B)
                  (wkConv↑Term [ρ] sndConv))
  wkConv↓Term {ρ} [ρ] (η-unit ⊢l [t] [u] tWhnf uWhnf ok₁ ok₂) =
    η-unit (wkTerm [ρ] ⊢l) (wkTerm [ρ] [t]) (wkTerm [ρ] [u])
           (wkWhnf ρ tWhnf) (wkWhnf ρ uWhnf) ok₁ ok₂
  wkConv↓Term ρ (Id-ins ⊢v₁ v₁~v₂) =
    Id-ins (wkTerm ρ ⊢v₁) (wk~↓ ρ v₁~v₂)
  wkConv↓Term ρ (rfl-refl t≡u) =
    rfl-refl (wkEqTerm ρ t≡u)
