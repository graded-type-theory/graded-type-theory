------------------------------------------------------------------------
-- Some basic properties of the logical relation for neutrals and levels.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.Primitive
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet eqrel
open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Allowed-literal R
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sup R
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Reduction R
open import Definition.Typed.Well-formed R
open import Definition.LogicalRelation R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties.Whnf R ⦃ eqrel ⦄

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum as ⊎

private
  variable
    V : Set _
    ℓ : Universe-level
    ∇ : DCon _ _
    A B t t₁ t₂ t₁′ t₂′ u u₁ u₂ v : Term _
    l l₁ l₂ : Lvl _
    Γ : Cons _ _
    ok₁ ok₂ ok₃ okᴸ : Level-allowed

mutual

  -- Reflexivity of level equality.

  reflLevel : Γ ⊩Level l ∷Level → Γ ⊩Level l ≡ l ∷Level
  reflLevel (term l⇒l′ l′-prop) =
    term l⇒l′ l⇒l′ (reflLevel-prop l′-prop)
  reflLevel (literal ok ⊢Γ) =
    literal! ok ⊢Γ

  reflLevel-prop : Level-prop Γ t → [Level]-prop Γ t t
  reflLevel-prop (zeroᵘᵣ ok) = zeroᵘᵣ ok
  reflLevel-prop (sucᵘᵣ ok x) = sucᵘᵣ ok (reflLevel x)
  reflLevel-prop (neLvl x₁) = neLvl (reflneLevel-prop x₁)

  reflneLevel-prop : neLevel-prop Γ t → [neLevel]-prop Γ t t
  reflneLevel-prop (supᵘˡᵣ x₁ x₂) = supᵘˡᵣ (reflneLevel-prop x₁) (reflLevel x₂)
  reflneLevel-prop (supᵘʳᵣ x₁ x₂) = supᵘʳᵣ (reflLevel x₁) (reflneLevel-prop x₂)
  reflneLevel-prop (ne x) = ne x

-- Transitivity for neutrals in WHNF and levels

transEqTermNe : ∀ {n n′ n″ A}
              → Γ ⊩neNf n  ≡ n′ ∷ A
              → Γ ⊩neNf n′ ≡ n″ ∷ A
              → Γ ⊩neNf n  ≡ n″ ∷ A
transEqTermNe (neNfₜ₌ neK neM k≡m) (neNfₜ₌ neK₁ neM₁ k≡m₁) =
  neNfₜ₌ neK neM₁ (~-trans k≡m k≡m₁)

transEqTermLevel : ∀ {n n′ n″}
                 → Γ ⊩Level n  ≡ n′ ∷Level
                 → Γ ⊩Level n′ ≡ n″ ∷Level
                 → Γ ⊩Level n  ≡ n″ ∷Level
transEqTermLevel
  (term l₁⇒l₁′ l₂⇒l₂′ l₁′≡l₂′) (term l₂⇒l₂″ l₃⇒l₃′ l₂″≡l₃′)
  with whrDet*Term (l₂⇒l₂′ , lsplit l₁′≡l₂′ .proj₂)
         (l₂⇒l₂″ , lsplit l₂″≡l₃′ .proj₁)
… | PE.refl = term l₁⇒l₁′ l₃⇒l₃′ (trans l₁′≡l₂′ l₂″≡l₃′)
transEqTermLevel (term ⇒∷Level _ _) (literal! ok _) =
  ⇒*∷Level→Allowed-literal→ ⇒∷Level ok
transEqTermLevel (literal! ok _) (term ⇒∷Level _ _) =
  ⇒*∷Level→Allowed-literal→ ⇒∷Level ok
transEqTermLevel (literal! ok ⊢Γ) (literal! _ _) =
  literal! ok ⊢Γ

-- Symmetry for neutrals in WHNF and levels

symNeutralTerm : ∀ {t u A}
               → Γ ⊩neNf t ≡ u ∷ A
               → Γ ⊩neNf u ≡ t ∷ A
symNeutralTerm (neNfₜ₌ neK neM k≡m) = neNfₜ₌ neM neK (~-sym k≡m)

symLevel : ∀ {k k′}
         → Γ ⊩Level k ≡ k′ ∷Level
         → Γ ⊩Level k′ ≡ k ∷Level
symLevel (term l₁⇒l₁′ l₂⇒l₂′ l₁′≡l₂′) =
  term l₂⇒l₂′ l₁⇒l₁′ (sym l₁′≡l₂′)
symLevel (literal! ok ⊢Γ) =
  literal! ok ⊢Γ

-- Some reduction and expansion lemmas

redLevel
  : ∀ {t t′}
  → Γ ⊢ t ⇒* t′ ∷ Level
  → Γ ⊩Level level t ∷Level
  → Γ ⊩Level level t ≡ level t′ ∷Level
redLevel l₁⇒l₂ (term l₁⇒l₃ l₃-prop) =
  term l₁⇒l₃ (whrDet↘Term (l₁⇒l₃ , Level-prop→Whnf l₃-prop) l₁⇒l₂)
    (reflLevel-prop l₃-prop)
redLevel l₁⇒ (literal ok _) =
  ⇒*∷Level→Allowed-literal→ l₁⇒ ok

redLevel′
  : ∀ {t t′}
  → Γ ⊢ t ⇒* t′ ∷ Level
  → Γ ⊩Level level t′ ∷Level
  → Γ ⊩Level level t ≡ level t′ ∷Level
redLevel′ l₁⇒l₂ (term l₂⇒l₃ l₃-prop) =
  term (l₁⇒l₂ ⇨∷* l₂⇒l₃) l₂⇒l₃ (reflLevel-prop l₃-prop)
redLevel′ l₁⇒ (literal ok _) =
  ⇒*∷Level→Allowed-literal→ l₁⇒ ok

⊩Level-⇒*
  : ∀ {t t′}
  → Γ ⊢ t′ ⇒* t ∷ Level
  → Γ ⊩Level level t ∷Level
  → Γ ⊩Level level t′ ∷Level
⊩Level-⇒* l₁⇒l₂ (term l₂⇒l₃ l₃-prop) =
  term (l₁⇒l₂ ⇨∷* l₂⇒l₃) l₃-prop
⊩Level-⇒* l₁⇒ (literal ok _) =
  ⇒*∷Level→Allowed-literal→ l₁⇒ ok

⊩Level≡-⇒*
  : ∀ {t t′ u u′}
  → Γ ⊢ t′ ⇒* t ∷ Level
  → Γ ⊢ u′ ⇒* u ∷ Level
  → Γ ⊩Level level t ≡ level u ∷Level
  → Γ ⊩Level level t′ ≡ level u′ ∷Level
⊩Level≡-⇒* l₁⇒l₁′ l₂⇒l₂′ (term l₁′⇒l₁″ l₂′⇒l₂″ l₁″≡l₂″) =
  term (l₁⇒l₁′ ⇨∷* l₁′⇒l₁″) (l₂⇒l₂′ ⇨∷* l₂′⇒l₂″) l₁″≡l₂″
⊩Level≡-⇒* l₁⇒ _ (literal! ok _) =
  ⇒*∷Level→Allowed-literal→ l₁⇒ ok

------------------------------------------------------------------------
-- Escape lemmas

opaque

  escape-neNf
    : Γ ⊩neNf t ≡ t ∷ A
    → Γ ⊢ t ∷ A
  escape-neNf (neNfₜ₌ neK neM k≡m) =
    wf-⊢ (≅ₜ-eq (~-to-≅ₜ k≡m)) .proj₂ .proj₁

opaque mutual

  -- Reducible levels are well-formed.

  escapeLevel
    : Γ ⊩Level l ∷Level
    → Γ ⊢ l ∷Level
  escapeLevel (term l⇒l′ _)   = term-⊢∷ (redFirst*Term l⇒l′)
  escapeLevel (literal ok ⊢Γ) = literal ok ⊢Γ

  escape-Level-prop
    : ⊢ Γ
    → Level-prop Γ t
    → Γ ⊢ t ∷ Level
  escape-Level-prop ⊢Γ (zeroᵘᵣ ok) =
    zeroᵘⱼ ok ⊢Γ
  escape-Level-prop ⊢Γ (sucᵘᵣ ok x) =
    sucᵘⱼ (⊢∷Level→⊢∷Level ok (escapeLevel x))
  escape-Level-prop ⊢Γ (neLvl x) =
    escape-neLevel-prop x

  escape-neLevel-prop
    : neLevel-prop Γ t
    → Γ ⊢ t ∷ Level
  escape-neLevel-prop (supᵘˡᵣ ⊩t₁ ⊩t₂) =
    let ⊢t₁ = escape-neLevel-prop ⊩t₁
        ok  = inversion-Level-⊢ (wf-⊢ ⊢t₁)
    in
    supᵘⱼ ⊢t₁ (⊢∷Level→⊢∷Level ok (escapeLevel ⊩t₂))
  escape-neLevel-prop (supᵘʳᵣ ⊩t₁ ⊩t₂) =
    let ⊢t₂ = escape-neLevel-prop ⊩t₂
        ok  = inversion-Level-⊢ (wf-⊢ ⊢t₂)
    in
    supᵘⱼ (sucᵘⱼ (⊢∷Level→⊢∷Level ok (escapeLevel ⊩t₁))) ⊢t₂
  escape-neLevel-prop (ne x) = escape-neNf x

opaque mutual

  -- Reducible levels that are terms are related to themselves.

  escapeLevel′ :
    Level-allowed →
    Γ ⊩Level level t ∷Level →
    Γ ⊢≅ t ∷ Level
  escapeLevel′ ok (term t⇒t′ t′-prop) =
    let t↘t′ = t⇒t′ , Level-prop→Whnf t′-prop
        ⊢Γ   = wf (redFirst*Term t⇒t′)
    in
    ≅ₜ-red (id (Levelⱼ′ ok ⊢Γ) , Levelₙ) t↘t′ t↘t′
      (escape-Level-prop′ ⊢Γ t′-prop)
  escapeLevel′ okᴸ (literal ok _) =
    Level-allowed→Allowed-literal→ okᴸ ok

  escape-Level-prop′
    : ⊢ Γ
    → Level-prop Γ t
    → Γ ⊢≅ t ∷ Level
  escape-Level-prop′ ⊢Γ (zeroᵘᵣ ok) =
    ≅ₜ-zeroᵘrefl ok ⊢Γ
  escape-Level-prop′ ⊢Γ (sucᵘᵣ ok ⊩t) =
    ≅ₜ-sucᵘ-cong (escapeLevel′ ok ⊩t)
  escape-Level-prop′ ⊢Γ (neLvl ⊩t) =
    escape-neLevel-prop′ ⊩t

  escape-neLevel-prop′
    : neLevel-prop Γ t
    → Γ ⊢≅ t ∷ Level
  escape-neLevel-prop′ (supᵘˡᵣ ⊩t₁ ⊩t₂) =
    let ⊢t₁ = escape-neLevel-prop′ ⊩t₁
        ok  = inversion-Level-⊢ (wf-⊢ (≅ₜ-eq ⊢t₁) .proj₁)
    in
    ≅ₜ-supᵘ-cong ⊢t₁ (escapeLevel′ ok ⊩t₂)
  escape-neLevel-prop′ (supᵘʳᵣ ⊩t₁ ⊩t₂) =
    let ⊢t₂ = escape-neLevel-prop′ ⊩t₂
        ok  = inversion-Level-⊢ (wf-⊢ (≅ₜ-eq ⊢t₂) .proj₁)
    in
    ≅ₜ-supᵘ-cong (≅ₜ-sucᵘ-cong (escapeLevel′ ok ⊩t₁)) ⊢t₂
  escape-neLevel-prop′ (ne (neNfₜ₌ _ _ k≡m)) =
    ~-to-≅ₜ k≡m

opaque mutual

  -- If Level is allowed, then reducible level equalities are
  -- well-formed.

  escapeLevelEq :
    Γ ⊩Level l₁ ≡ l₂ ∷Level →
    Γ ⊢ l₁ ≅ l₂ ∷Level
  escapeLevelEq (term t⇒t′ u⇒u′ t′≡u′) =
    let t′-whnf , u′-whnf = lsplit t′≡u′
        ⊢t                = redFirst*Term t⇒t′
        ⊢Γ                = wf ⊢t
        ok                = inversion-Level-⊢ (wf-⊢ ⊢t)
    in
    ⊢≅∷→⊢≅∷L $
    ≅ₜ-red (id (Levelⱼ′ ok ⊢Γ) , Levelₙ) (t⇒t′ , t′-whnf)
      (u⇒u′ , u′-whnf) (escape-[Level]-prop ⊢Γ t′≡u′)
  escapeLevelEq (literal! ok ⊢Γ) =
    Level-literal→⊢≅∷L ok ⊢Γ

  escape-[Level]-prop
    : ⊢ Γ
    → [Level]-prop Γ t u
    → Γ ⊢ t ≅ u ∷ Level
  escape-[Level]-prop ⊢Γ (zeroᵘᵣ ok) =
    ≅ₜ-zeroᵘrefl ok ⊢Γ
  escape-[Level]-prop ⊢Γ (sucᵘᵣ ok ⊩t) =
    ≅ₜ-sucᵘ-cong (⊢≅∷L→⊢≅∷ ok $ escapeLevelEq ⊩t)
  escape-[Level]-prop ⊢Γ (supᵘ-subᵣ ⊩t ⊩u) =
    let ⊢t = escape-neLevel-prop′ ⊩t
        ok = inversion-Level-⊢ (wf-⊢ (≅ₜ-eq ⊢t) .proj₁)
    in
    ≅ₜ-supᵘ-sub′ ⊢t (⊢≅∷L→⊢≅∷ ok $ escapeLevelEq ⊩u)
  escape-[Level]-prop ⊢Γ (neLvl n) = escape-[neLevel]-prop n
  escape-[Level]-prop ⊢Γ (sym x) = ≅ₜ-sym (escape-[Level]-prop ⊢Γ x)
  escape-[Level]-prop ⊢Γ (trans x y) =
    ≅ₜ-trans (escape-[Level]-prop ⊢Γ x) (escape-[Level]-prop ⊢Γ y)

  escape-[neLevel]-prop
    : [neLevel]-prop Γ t u
    → Γ ⊢ t ≅ u ∷ Level
  escape-[neLevel]-prop (supᵘˡᵣ ⊩t ⊩u) =
    let ⊢t = escape-[neLevel]-prop ⊩t
        ok = inversion-Level-⊢ (wf-⊢ (≅ₜ-eq ⊢t) .proj₁)
    in
    ≅ₜ-supᵘ-cong ⊢t (⊢≅∷L→⊢≅∷ ok $ escapeLevelEq ⊩u)
  escape-[neLevel]-prop (supᵘʳᵣ ⊩t ⊩u) =
    let ⊢u = escape-[neLevel]-prop ⊩u
        ok = inversion-Level-⊢ (wf-⊢ (≅ₜ-eq ⊢u) .proj₁)
    in
    ≅ₜ-supᵘ-cong (≅ₜ-sucᵘ-cong (⊢≅∷L→⊢≅∷ ok $ escapeLevelEq ⊩t)) ⊢u
  escape-[neLevel]-prop (supᵘ-zeroʳᵣ x) =
    let ⊢t = escape-neLevel-prop′ x
    in ≅ₜ-supᵘ-zeroʳ ⊢t
  escape-[neLevel]-prop (supᵘ-assoc¹ᵣ ⊩t ⊩u ⊩v) =
    let ⊢t = escape-neLevel-prop′ ⊩t
        ok = inversion-Level-⊢ (wf-⊢ (≅ₜ-eq ⊢t) .proj₁)
    in
    ≅ₜ-supᵘ-assoc ⊢t (escapeLevel′ ok ⊩u) (escapeLevel′ ok ⊩v)
  escape-[neLevel]-prop (supᵘ-assoc²ᵣ ⊩t ⊩u ⊩v) =
    let ⊢u = escape-neLevel-prop′ ⊩u
        ok = inversion-Level-⊢ (wf-⊢ (≅ₜ-eq ⊢u) .proj₁)
    in
    ≅ₜ-supᵘ-assoc (≅ₜ-sucᵘ-cong (escapeLevel′ ok ⊩t)) ⊢u
      (escapeLevel′ ok ⊩v)
  escape-[neLevel]-prop (supᵘ-assoc³ᵣ ⊩t ⊩u ⊩v) =
    let ⊢v = escape-neLevel-prop′ ⊩v
        ok = inversion-Level-⊢ (wf-⊢ (≅ₜ-eq ⊢v) .proj₁)
        ⊢t = escapeLevel′ ok ⊩t
        ⊢u = escapeLevel′ ok ⊩u
    in
    ≅ₜ-trans
      (≅ₜ-supᵘ-cong (≅ₜ-sym (≅ₜ-supᵘ-sucᵘ ⊢t ⊢u)) ⊢v)
      (≅ₜ-supᵘ-assoc (≅ₜ-sucᵘ-cong ⊢t) (≅ₜ-sucᵘ-cong ⊢u) ⊢v)
  escape-[neLevel]-prop (supᵘ-comm¹ᵣ ⊩t₁ t₁≡u₁ ⊩u₂ t₂≡u₂) =
    let ⊢t₁   = escape-neLevel-prop′ ⊩t₁
        ok    = inversion-Level-⊢ (wf-⊢ (≅ₜ-eq ⊢t₁) .proj₁)
        t₁≡u₁ = ⊢≅∷L→⊢≅∷ ok $ escapeLevelEq t₁≡u₁
        t₂≡u₂ = ⊢≅∷L→⊢≅∷ ok $ escapeLevelEq t₂≡u₂
        ⊢t₂ , _ = wf-⊢≅∷ t₂≡u₂
    in
    ≅ₜ-trans (≅ₜ-supᵘ-comm ⊢t₁ ⊢t₂) (≅ₜ-supᵘ-cong t₂≡u₂ t₁≡u₁)
  escape-[neLevel]-prop (supᵘ-comm²ᵣ ⊩t₁ 1+t₁≡u₂ ⊩t₂) =
    let ⊢t₂     = escape-neLevel-prop′ ⊩t₂
        ok      = inversion-Level-⊢ (wf-⊢ (≅ₜ-eq ⊢t₂) .proj₁)
        1+t₁≡u₂ = ⊢≅∷L→⊢≅∷ ok $ escapeLevelEq 1+t₁≡u₂
        _ , ⊢u₂ = wf-⊢≅∷ 1+t₁≡u₂
    in
    ≅ₜ-trans (≅ₜ-supᵘ-cong 1+t₁≡u₂ ⊢t₂) (≅ₜ-supᵘ-comm ⊢u₂ ⊢t₂)
  escape-[neLevel]-prop (supᵘ-idemᵣ ⊩t₁ t₁≡t₂) =
    let t₁≡t₁ = escape-neLevel-prop′ ⊩t₁
        ok    = inversion-Level-⊢ (wf-⊢ (≅ₜ-eq t₁≡t₁) .proj₁)
        t₁≡t₂ = ⊢≅∷L→⊢≅∷ ok $ escapeLevelEq t₁≡t₂
    in
    ≅ₜ-trans (≅ₜ-supᵘ-cong t₁≡t₁ (≅ₜ-sym t₁≡t₂)) (≅ₜ-supᵘ-idem t₁≡t₁)
  escape-[neLevel]-prop (ne (neNfₜ₌ _ _ k≡m)) =
    ~-to-≅ₜ k≡m

------------------------------------------------------------------------
-- Some introduction lemmas for _⊩Level_∷Level and _⊩Level_≡_∷Level.

⊩Lvl : ⊢ Γ → Level-prop Γ t → Γ ⊩Level level t ∷Level
⊩Lvl ⊢Γ ⊩t = term (id (escape-Level-prop ⊢Γ ⊩t)) ⊩t

⊩neLvl : neLevel-prop Γ t → Γ ⊩Level level t ∷Level
⊩neLvl ⊩t = term (id (escape-neLevel-prop ⊩t)) (neLvl ⊩t)

⊩[Lvl] : ⊢ Γ → [Level]-prop Γ t u → Γ ⊩Level level t ≡ level u ∷Level
⊩[Lvl] ⊢Γ t≡u =
  let _ , ⊢t , ⊢u = wf-⊢ (≅ₜ-eq (escape-[Level]-prop ⊢Γ t≡u)) in
  term (id ⊢t) (id ⊢u) t≡u

⊩[neLvl] : [neLevel]-prop Γ t u → Γ ⊩Level level t ≡ level u ∷Level
⊩[neLvl] t≡u =
  let _ , ⊢t , ⊢u = wf-⊢ (≅ₜ-eq (escape-[neLevel]-prop t≡u)) in
  term (id ⊢t) (id ⊢u) (neLvl t≡u)

opaque

  -- An introduction lemma for zeroᵘₗ.

  ⊩zeroᵘ : ⊢ Γ → Γ ⊩Level zeroᵘₗ ∷Level
  ⊩zeroᵘ ⊢Γ with Level-allowed?
  … | yes ok    = ⊩Lvl ⊢Γ (zeroᵘᵣ ok)
  … | no not-ok =
    literal (Allowed-literal-level-⇔ .proj₂ (zeroᵘ , not-ok)) ⊢Γ

opaque

  -- Introduction lemmas for 1ᵘ+.

  ⊩1ᵘ+ : Γ ⊩Level l ∷Level → Γ ⊩Level 1ᵘ+ l ∷Level
  ⊩1ᵘ+ ⊩t@(term t⇒*t′ _) =
    let ⊢t = redFirst*Term t⇒*t′
        ok = inversion-Level-⊢ (wf-⊢ ⊢t)
    in
    term
      (id (sucᵘⱼ (redFirst*Term t⇒*t′)))
      (sucᵘᵣ ok ⊩t)
  ⊩1ᵘ+ (literal ok ⊢Γ) =
    literal (Allowed-literal-1ᵘ+-⇔ .proj₂ ok) ⊢Γ

  ⊩1ᵘ+≡1ᵘ+ : Γ ⊩Level l₁ ≡ l₂ ∷Level → Γ ⊩Level 1ᵘ+ l₁ ≡ 1ᵘ+ l₂ ∷Level
  ⊩1ᵘ+≡1ᵘ+ t≡u@(term t⇒*t′ u⇒*u′ t′≡u′) =
    let ⊢t = redFirst*Term t⇒*t′
        ok = inversion-Level-⊢ (wf-⊢ ⊢t)
    in
    term
      (id (sucᵘⱼ ⊢t))
      (id (sucᵘⱼ (redFirst*Term u⇒*u′)))
      (sucᵘᵣ ok t≡u)
  ⊩1ᵘ+≡1ᵘ+ (literal! ok ⊢Γ) =
    literal! (Allowed-literal-1ᵘ+-⇔ .proj₂ ok) ⊢Γ

opaque

  -- A characterisation lemma for _⊩Level_∷Level.

  ⊩1ᵘ+⇔ : Γ ⊩Level 1ᵘ+ l ∷Level ⇔ Γ ⊩Level l ∷Level
  ⊩1ᵘ+⇔ = to , ⊩1ᵘ+
    where
    to : Γ ⊩Level 1ᵘ+ l ∷Level → Γ ⊩Level l ∷Level
    to {l = level _} (term suc⇒ (zeroᵘᵣ _)) =
      case whnfRed*Term suc⇒ sucᵘₙ of λ ()
    to {l = level _} (term suc⇒ (sucᵘᵣ _ ⊩l)) =
      case whnfRed*Term suc⇒ sucᵘₙ of λ {
        PE.refl →
      ⊩l }
    to {l = level _} (term suc⇒ (neLvl ⊩l)) =
      case whnfRed*Term suc⇒ sucᵘₙ of λ {
        PE.refl →
      case nelevel ⊩l of λ () }
    to (literal ok ⊢Γ) =
      literal (Allowed-literal-1ᵘ+-⇔ .proj₁ ok) ⊢Γ

opaque mutual

  -- An introduction lemma for supᵘ.

  ⊩supᵘ :
    Level-allowed →
    Γ ⊩Level level t ∷Level →
    Γ ⊩Level level u ∷Level →
    Γ ⊩Level level (t supᵘ u) ∷Level
  ⊩supᵘ {t} {u} okᴸ (term t⇒ propt) ⊩u =
    let ⊢u = ⊢∷Level→⊢∷Level okᴸ (escapeLevel ⊩u) in
    case propt of λ where
      (zeroᵘᵣ _) →
        ⊩Level-⇒*
          (t     supᵘ u  ⇒*⟨ supᵘ-substˡ* t⇒ ⊢u ⟩
           zeroᵘ supᵘ u  ⇒⟨ supᵘ-zeroˡ ⊢u ⟩∎
           u             ∎)
          ⊩u
      (sucᵘᵣ {k = t′} _ ⊩t′) →
        let ⊢t′ = ⊢∷Level→⊢∷Level okᴸ (escapeLevel ⊩t′) in
        case ⊩u of λ where
          (term u⇒ propu) →
            case propu of λ where
              (zeroᵘᵣ _) → term
                (t supᵘ u            ⇒*⟨ supᵘ-substˡ* t⇒ ⊢u ⟩
                 sucᵘ t′ supᵘ u      ⇒*⟨ supᵘ-substʳ* ⊢t′ u⇒ ⟩
                 sucᵘ t′ supᵘ zeroᵘ  ⇒⟨ supᵘ-zeroʳ ⊢t′ ⟩∎
                 sucᵘ t′             ∎)
                (sucᵘᵣ okᴸ ⊩t′)
              (sucᵘᵣ {k = u′} _ ⊩u′) →
                let ⊢u′ = ⊢∷Level→⊢∷Level okᴸ (escapeLevel ⊩u′) in
                term
                  (t supᵘ u              ⇒*⟨ supᵘ-substˡ* t⇒ ⊢u ⟩
                   sucᵘ t′ supᵘ u        ⇒*⟨ supᵘ-substʳ* ⊢t′ u⇒ ⟩
                   sucᵘ t′ supᵘ sucᵘ u′  ⇒⟨ supᵘ-sucᵘ ⊢t′ ⊢u′ ⟩∎
                   sucᵘ (t′ supᵘ u′)     ∎)
                  (sucᵘᵣ okᴸ (⊩supᵘ okᴸ ⊩t′ ⊩u′))
              (neLvl {k = u′} ⊩u′) → term
                (t supᵘ u         ⇒*⟨ supᵘ-substˡ* t⇒ ⊢u ⟩
                 sucᵘ t′ supᵘ u   ⇒*⟨ supᵘ-substʳ* ⊢t′ u⇒ ⟩∎
                 sucᵘ t′ supᵘ u′  ∎)
                (neLvl (supᵘʳᵣ ⊩t′ ⊩u′))
          (literal ok _) →
            Level-allowed→Allowed-literal→ okᴸ ok
      (neLvl ⊩t′) →
        term
          (supᵘ-substˡ* t⇒ ⊢u)
          (neLvl (supᵘˡᵣ ⊩t′ ⊩u))
  ⊩supᵘ okᴸ (literal ok _) _ =
    Level-allowed→Allowed-literal→ okᴸ ok

opaque
  unfolding _supᵘₗ_

  -- An introduction lemma for _supᵘₗ_.

  ⊩supᵘₗ :
    Γ ⊩Level l₁ ∷Level →
    Γ ⊩Level l₂ ∷Level →
    Γ ⊩Level l₁ supᵘₗ l₂ ∷Level
  ⊩supᵘₗ (literal ok₁ ⊢Γ) (literal ok₂ _) =
    literal (Allowed-literal-supᵘₗ ok₁ ok₂) ⊢Γ
  ⊩supᵘₗ {l₁ = ωᵘ+ _} {l₂ = level _} (literal ok ⊢Γ) _ =
    literal (Allowed-literal-ωᵘ+-→-Allowed-literal-ωᵘ+ ok) ⊢Γ
  ⊩supᵘₗ {l₁ = level _} {l₂ = ωᵘ+ _} _ (literal ok ⊢Γ) =
    literal (Allowed-literal-ωᵘ+-→-Allowed-literal-ωᵘ+ ok) ⊢Γ
  ⊩supᵘₗ {l₂ = level _} ⊩l₁@(term ⇒∷Level _) ⊩l₂ =
    let ok = inversion-Level-⊢ (wf-⊢ (subset*Term ⇒∷Level) .proj₁) in
    PE.subst (_⊩Level_∷Level _) (PE.sym $ supᵘₗ≡supᵘ ok) $
    ⊩supᵘ ok ⊩l₁ ⊩l₂
  ⊩supᵘₗ {l₁ = level _} ⊩l₁ ⊩l₂@(term ⇒∷Level _) =
    let ok = inversion-Level-⊢ (wf-⊢ (subset*Term ⇒∷Level) .proj₁) in
    PE.subst (_⊩Level_∷Level _) (PE.sym $ supᵘₗ≡supᵘ ok) $
    ⊩supᵘ ok ⊩l₁ ⊩l₂

opaque

  -- Associativity for supᵘ.

  ⊩supᵘ-assoc :
    Level-allowed →
    Γ ⊩Level level t ∷Level →
    Γ ⊩Level level u ∷Level →
    Γ ⊩Level level v ∷Level →
    Γ ⊩Level level ((t supᵘ u) supᵘ v) ≡ level (t supᵘ (u supᵘ v))
      ∷Level
  ⊩supᵘ-assoc
    ok ⊩t@(term t⇒ propt) ⊩u@(term u⇒ propu) ⊩v@(term v⇒ propv) =
    let
      ⊢u  = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩u)
      ⊢v  = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩v)
      ⊢Γ  = wf ⊢u
      ⊢t′ = escape-Level-prop ⊢Γ propt
      ⊢u′ = escape-Level-prop ⊢Γ propu
      ⊢v′ = escape-Level-prop ⊢Γ propv
    in
    ⊩Level≡-⇒*
      (supᵘ-substˡ* (supᵘ-substˡ* t⇒ ⊢u) ⊢v)
      (supᵘ-substˡ* t⇒ (supᵘⱼ ⊢u ⊢v)) $
      case propt of λ where
        (zeroᵘᵣ _) →
          ⊩Level≡-⇒*
            (redMany (supᵘ-substˡ (supᵘ-zeroˡ ⊢u) ⊢v))
            (redMany (supᵘ-zeroˡ (supᵘⱼ ⊢u ⊢v)))
            (reflLevel (⊩supᵘ ok ⊩u ⊩v))
        (sucᵘᵣ _ ⊩t″) →
          let ⊢t″ = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩t″) in
          ⊩Level≡-⇒*
            (supᵘ-substˡ* (supᵘ-substʳ* ⊢t″ u⇒) ⊢v)
            (supᵘ-substʳ* ⊢t″ (supᵘ-substˡ* u⇒ ⊢v)) $
            case propu of λ where
              (zeroᵘᵣ _) →
                ⊩Level≡-⇒*
                  (redMany (supᵘ-substˡ (supᵘ-zeroʳ ⊢t″) ⊢v))
                  (redMany (supᵘ-substʳ ⊢t″ (supᵘ-zeroˡ ⊢v)))
                  (reflLevel (⊩supᵘ ok (⊩1ᵘ+ ⊩t″) ⊩v))
              (sucᵘᵣ _ ⊩u″) →
                let ⊢u″ = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩u″) in
                ⊩Level≡-⇒*
                  (supᵘ-substˡ (supᵘ-sucᵘ ⊢t″ ⊢u″) ⊢v ⇨
                   supᵘ-substʳ* (supᵘⱼ ⊢t″ ⊢u″) v⇒)
                  (supᵘ-substʳ* ⊢t″ (supᵘ-substʳ* ⊢u″ v⇒)) $
                  case propv of λ where
                    (zeroᵘᵣ _) →
                      ⊩Level≡-⇒*
                        (redMany (supᵘ-zeroʳ (supᵘⱼ ⊢t″ ⊢u″)))
                        (supᵘ-substʳ ⊢t″ (supᵘ-zeroʳ ⊢u″) ⇨
                         redMany (supᵘ-sucᵘ ⊢t″ ⊢u″))
                        (reflLevel (⊩1ᵘ+ (⊩supᵘ ok ⊩t″ ⊩u″)))
                    (sucᵘᵣ _ ⊩v″) →
                      let ⊢v″ = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩v″) in
                      ⊩Level≡-⇒*
                        (redMany (supᵘ-sucᵘ (supᵘⱼ ⊢t″ ⊢u″) ⊢v″))
                        (supᵘ-substʳ ⊢t″ (supᵘ-sucᵘ ⊢u″ ⊢v″) ⇨
                         redMany (supᵘ-sucᵘ ⊢t″ (supᵘⱼ ⊢u″ ⊢v″)))
                        (⊩1ᵘ+≡1ᵘ+ (⊩supᵘ-assoc ok ⊩t″ ⊩u″ ⊩v″))
                    (neLvl nepropv) →
                      term
                        (id (supᵘⱼ (sucᵘⱼ (supᵘⱼ ⊢t″ ⊢u″)) ⊢v′))
                        (id (supᵘⱼ (sucᵘⱼ ⊢t″) (supᵘⱼ (sucᵘⱼ ⊢u″) ⊢v′)))
                        (neLvl (supᵘ-assoc³ᵣ ⊩t″ ⊩u″ nepropv))
              (neLvl nepropu) →
                term
                  (id (supᵘⱼ (supᵘⱼ (sucᵘⱼ ⊢t″) ⊢u′) ⊢v))
                  (id (supᵘⱼ (sucᵘⱼ ⊢t″) (supᵘⱼ ⊢u′ ⊢v)))
                  (neLvl (supᵘ-assoc²ᵣ ⊩t″ nepropu ⊩v))
        (neLvl nepropt) →
          term
            (id (supᵘⱼ (supᵘⱼ ⊢t′ ⊢u) ⊢v))
            (id (supᵘⱼ ⊢t′ (supᵘⱼ ⊢u ⊢v)))
            (neLvl (supᵘ-assoc¹ᵣ nepropt ⊩u ⊩v))
  ⊩supᵘ-assoc okᴸ (literal ok _) _ _ =
    Level-allowed→Allowed-literal→ okᴸ ok
  ⊩supᵘ-assoc okᴸ _ (literal ok _) _ =
    Level-allowed→Allowed-literal→ okᴸ ok
  ⊩supᵘ-assoc okᴸ _ _ (literal ok _) =
    Level-allowed→Allowed-literal→ okᴸ ok

opaque

  -- Right identity for supᵘ.

  ⊩supᵘ-zeroʳ′ :
    Γ ⊩Level level t ∷Level →
    Γ ⊢ u ⇒* zeroᵘ ∷ Level →
    Γ ⊩Level level (t supᵘ u) ≡ level t ∷Level
  ⊩supᵘ-zeroʳ′ (literal ok _) ⇒∷Level =
    let okᴸ = inversion-Level-⊢ (wf-⊢ (subset*Term ⇒∷Level) .proj₁) in
    Level-allowed→Allowed-literal→ okᴸ ok
  ⊩supᵘ-zeroʳ′ ⊩t@(term t⇒ prop) u⇒ =
    let ⊢u = redFirst*Term u⇒
        ⊢Γ = wf ⊢u
    in
    ⊩Level≡-⇒* (supᵘ-substˡ* t⇒ ⊢u) t⇒ $
    case prop of λ where
      (zeroᵘᵣ _) → redLevel′ (supᵘ-zeroˡ ⊢u ⇨ u⇒) (⊩zeroᵘ ⊢Γ)
      (sucᵘᵣ ok ⊩k) →
        let ⊢k = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩k) in
        redLevel′ (supᵘ-substʳ* ⊢k u⇒ ⇨∷* redMany (supᵘ-zeroʳ ⊢k))
          (⊩1ᵘ+ ⊩k)
      (neLvl ⊩k) →
        transEqTermLevel
          (⊩[neLvl] $
           supᵘˡᵣ (reflneLevel-prop ⊩k) (redLevel′ u⇒ (⊩zeroᵘ ⊢Γ)))
          (⊩[neLvl] (supᵘ-zeroʳᵣ ⊩k))

  ⊩supᵘ-zeroʳ :
    Level-allowed →
    Γ ⊩Level level t ∷Level →
    Γ ⊩Level level (t supᵘ zeroᵘ) ≡ level t ∷Level
  ⊩supᵘ-zeroʳ ok ⊩t =
    ⊩supᵘ-zeroʳ′ ⊩t $
    id (zeroᵘⱼ ok (wf (⊢∷Level→⊢∷Level ok (escapeLevel ⊩t))))

opaque

  -- Commutativity for supᵘ.

  ⊩supᵘ-comm :
    Level-allowed →
    Γ ⊩Level level t ∷Level →
    Γ ⊩Level level u ∷Level →
    Γ ⊩Level level (t supᵘ u) ≡ level (u supᵘ t) ∷Level
  ⊩supᵘ-comm ok ⊩t@(term t⇒ propt) ⊩u@(term u⇒ propu) =
    let ⊢t  = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩t)
        ⊢u  = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩u)
        ⊢Γ  = wf ⊢u
        ⊢t′ = escape-Level-prop ⊢Γ propt
        ⊢u′ = escape-Level-prop ⊢Γ propu
    in
    ⊩Level≡-⇒* (supᵘ-substˡ* t⇒ ⊢u) (id (supᵘⱼ ⊢u ⊢t)) $
    case propt of λ where
      (zeroᵘᵣ _) →
        ⊩Level≡-⇒*
          (redMany (supᵘ-zeroˡ ⊢u))
          (id (supᵘⱼ ⊢u ⊢t))
          (symLevel (⊩supᵘ-zeroʳ′ ⊩u t⇒))
      (sucᵘᵣ _ ⊩t′) →
        let ⊢t′ = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩t′) in
        ⊩Level≡-⇒* (supᵘ-substʳ* ⊢t′ u⇒) (supᵘ-substˡ* u⇒ ⊢t) $
        case propu of λ where
          (zeroᵘᵣ _) →
            ⊩Level≡-⇒*
              (redMany (supᵘ-zeroʳ ⊢t′))
              (supᵘ-zeroˡ ⊢t ⇨ t⇒)
              (reflLevel (⊩1ᵘ+ ⊩t′))
          (sucᵘᵣ _ ⊩u′) →
            let ⊢u′ = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩u′) in
            ⊩Level≡-⇒*
              (redMany (supᵘ-sucᵘ ⊢t′ ⊢u′))
              (supᵘ-substʳ* ⊢u′ t⇒ ⇨∷* redMany (supᵘ-sucᵘ ⊢u′ ⊢t′))
              (⊩1ᵘ+≡1ᵘ+ (⊩supᵘ-comm ok ⊩t′ ⊩u′))
          (neLvl ⊩u′) →
            term
              (id (supᵘⱼ (sucᵘⱼ ⊢t′) ⊢u′))
              (id (supᵘⱼ ⊢u′ ⊢t))
              (neLvl (supᵘ-comm²ᵣ ⊩t′ (symLevel (redLevel t⇒ ⊩t)) ⊩u′))
      (neLvl ⊩t′) →
        ⊩Level≡-⇒* (id (supᵘⱼ ⊢t′ ⊢u)) (supᵘ-substˡ* u⇒ ⊢t) $
        case propu of λ where
          (zeroᵘᵣ _) →
            ⊩Level≡-⇒* (id (supᵘⱼ ⊢t′ ⊢u)) (supᵘ-zeroˡ ⊢t ⇨ t⇒)
              (⊩supᵘ-zeroʳ′ (⊩neLvl ⊩t′) u⇒)
          (sucᵘᵣ _ ⊩u′) →
            let ⊢u′ = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩u′) in
            term (id (supᵘⱼ ⊢t′ ⊢u)) (supᵘ-substʳ* ⊢u′ t⇒)
              ([Level]-prop.sym $ [Level]-prop.neLvl $
               supᵘ-comm²ᵣ ⊩u′ (symLevel (redLevel u⇒ ⊩u)) ⊩t′)
          (neLvl ⊩u′) →
            term (id (supᵘⱼ ⊢t′ ⊢u)) (id (supᵘⱼ ⊢u′ ⊢t))
              ([Level]-prop.neLvl $
               supᵘ-comm¹ᵣ ⊩t′ (symLevel (redLevel t⇒ ⊩t)) ⊩u′
                 (redLevel u⇒ ⊩u))
  ⊩supᵘ-comm okᴸ (literal ok _) _ =
    Level-allowed→Allowed-literal→ okᴸ ok
  ⊩supᵘ-comm okᴸ _ (literal ok _) =
    Level-allowed→Allowed-literal→ okᴸ ok

opaque

  -- Idempotence for supᵘ.

  ⊩supᵘ-idem :
    Level-allowed →
    Γ ⊩Level level t ∷Level →
    Γ ⊩Level level (t supᵘ t) ≡ level t ∷Level
  ⊩supᵘ-idem {t} ok ⊩t@(term t⇒ propt) =
    let ⊢t = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩t) in
    case propt of λ where
      (zeroᵘᵣ _) → term
        (t supᵘ t      ⇒*⟨ supᵘ-substˡ* t⇒ ⊢t ⟩
         zeroᵘ supᵘ t  ⇒⟨ supᵘ-zeroˡ ⊢t ⟩
         t             ⇒*⟨ t⇒ ⟩∎
         zeroᵘ         ∎)
        (t      ⇒*⟨ t⇒ ⟩∎
         zeroᵘ  ∎)
        (zeroᵘᵣ ok)
      (sucᵘᵣ {k = t′} _ ⊩t′) →
        let ⊢t′ = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩t′) in
        term
          (t supᵘ t              ⇒*⟨ supᵘ-substˡ* t⇒ ⊢t ⟩
           sucᵘ t′ supᵘ t        ⇒*⟨ supᵘ-substʳ* ⊢t′ t⇒ ⟩
           sucᵘ t′ supᵘ sucᵘ t′  ⇒⟨ supᵘ-sucᵘ ⊢t′ ⊢t′ ⟩∎
           sucᵘ (t′ supᵘ t′)     ∎)
          (t        ⇒*⟨ t⇒ ⟩∎
           sucᵘ t′  ∎)
          (sucᵘᵣ ok (⊩supᵘ-idem ok ⊩t′))
      (neLvl {k = t′} ⊩t′) → term
        (t supᵘ t   ⇒*⟨ supᵘ-substˡ* t⇒ ⊢t ⟩∎
         t′ supᵘ t  ∎)
        (t   ⇒*⟨ t⇒ ⟩∎
         t′  ∎)
        ([Level]-prop.neLvl $
         supᵘ-idemᵣ ⊩t′ (symLevel (redLevel′ t⇒ (⊩neLvl ⊩t′))))
  ⊩supᵘ-idem okᴸ (literal ok _) =
    Level-allowed→Allowed-literal→ okᴸ ok

opaque

  -- Subsumption for supᵘ.

  ⊩supᵘ-sub′ :
    Γ ⊢ u ⇒* sucᵘ t ∷ Level →
    Γ ⊩Level level t ∷Level →
    Γ ⊩Level level (t supᵘ u) ≡ level u ∷Level
  ⊩supᵘ-sub′ u⇒ ⊩t@(term t⇒ propt) =
    let ⊢u  = redFirst*Term u⇒
        ok  = inversion-Level-⊢ (wf-⊢ ⊢u)
        ⊢t  = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩t)
        ⊢Γ  = wf ⊢t
        ⊢t′ = escape-Level-prop ⊢Γ propt
    in
    ⊩Level≡-⇒* (supᵘ-substˡ* t⇒ ⊢u) (id ⊢u) $
    case propt of λ where
      (zeroᵘᵣ _) →
        redLevel′ (redMany (supᵘ-zeroˡ ⊢u)) (⊩Level-⇒* u⇒ (⊩1ᵘ+ ⊩t))
      (sucᵘᵣ _ ⊩t′) →
        let ⊢t′ = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩t′) in
        ⊩Level≡-⇒* (supᵘ-substʳ* ⊢t′ u⇒ ⇨∷* redMany (supᵘ-sucᵘ ⊢t′ ⊢t))
          u⇒ (⊩1ᵘ+≡1ᵘ+ (⊩supᵘ-sub′ t⇒ ⊩t′))
      (neLvl x) → term (id (supᵘⱼ ⊢t′ ⊢u)) u⇒ $
        trans
          ([Level]-prop.neLvl $
           supᵘˡᵣ (reflneLevel-prop x) $
           ⊩Level≡-⇒* u⇒ (id (sucᵘⱼ ⊢t′)) (⊩1ᵘ+≡1ᵘ+ (redLevel t⇒ ⊩t)))
          (trans (supᵘ-subᵣ x (⊩supᵘ-idem ok (⊩neLvl x)))
             (sucᵘᵣ ok (symLevel (redLevel t⇒ ⊩t))))
  ⊩supᵘ-sub′ ⇒∷Level (literal ok _) =
    let okᴸ = inversion-Level-⊢ (wf-⊢ (subset*Term ⇒∷Level) .proj₁) in
    Level-allowed→Allowed-literal→ okᴸ ok

  ⊩supᵘ-sub :
    Level-allowed →
    Γ ⊩Level level t ∷Level →
    Γ ⊩Level level (t supᵘ sucᵘ t) ≡ level (sucᵘ t) ∷Level
  ⊩supᵘ-sub ok ⊩t =
    ⊩supᵘ-sub′ (id (sucᵘⱼ (⊢∷Level→⊢∷Level ok (escapeLevel ⊩t)))) ⊩t

-- Well-formedness for neutrals in WHNF and levels

opaque

  wf-neNf : Γ ⊩neNf t ≡ u ∷ A → Γ ⊩neNf t ≡ t ∷ A × Γ ⊩neNf u ≡ u ∷ A
  wf-neNf t≡u =
      transEqTermNe t≡u (symNeutralTerm t≡u)
    , transEqTermNe (symNeutralTerm t≡u) t≡u

opaque

  wf-neLevel-prop : neLevel-prop Γ t → ⊢ Γ
  wf-neLevel-prop (supᵘˡᵣ x₁ x₂) = wf-neLevel-prop x₁
  wf-neLevel-prop (supᵘʳᵣ x₁ x₂) = wf-neLevel-prop x₂
  wf-neLevel-prop (ne (neNfₜ₌ neK neM k≡m)) =
    wf (≅ₜ-eq (~-to-≅ₜ k≡m))

opaque mutual

  wf-Level-eq :
    Γ ⊩Level l₁ ≡ l₂ ∷Level → Γ ⊩Level l₁ ∷Level × Γ ⊩Level l₂ ∷Level
  wf-Level-eq (term t⇒t′ u⇒u′ t′≡u′) =
    let ⊩t′ , ⊩u′ = wf-[Level]-prop t′≡u′ in
    term t⇒t′ ⊩t′ , term u⇒u′ ⊩u′
  wf-Level-eq (literal! ok ⊢Γ) =
    literal ok ⊢Γ , literal ok ⊢Γ

  wf-[Level]-prop : [Level]-prop Γ t u → Level-prop Γ t × Level-prop Γ u
  wf-[Level]-prop (zeroᵘᵣ ok) =
    zeroᵘᵣ ok , zeroᵘᵣ ok
  wf-[Level]-prop (sucᵘᵣ ok t≡u) =
    let ⊩t , ⊩u = wf-Level-eq t≡u in
    sucᵘᵣ ok ⊩t , sucᵘᵣ ok ⊩u
  wf-[Level]-prop (supᵘ-subᵣ ⊩t ≡u) =
    let _ , ⊩u = wf-Level-eq ≡u
        ok     = inversion-Level-⊢ (wf-⊢ (escape-neLevel-prop ⊩t))
    in
    neLvl (supᵘˡᵣ ⊩t (⊩1ᵘ+ ⊩u)) , sucᵘᵣ ok ⊩u
  wf-[Level]-prop (neLvl t≡u) = let [t] , [u] = wf-[neLevel]-prop t≡u in neLvl [t] , neLvl [u]
  wf-[Level]-prop (sym u≡t) =
    let [u] , [t] = wf-[Level]-prop u≡t
    in [t] , [u]
  wf-[Level]-prop (trans x y) =
    let [t] , _ = wf-[Level]-prop x
        _ , [u] = wf-[Level]-prop y
    in [t] , [u]

  wf-[neLevel]-prop : [neLevel]-prop Γ t u → neLevel-prop Γ t × neLevel-prop Γ u
  wf-[neLevel]-prop (supᵘˡᵣ k₁≡k₁′ k₂≡k₂′) =
    let [k₁] , [k₁′] = wf-[neLevel]-prop k₁≡k₁′
        [k₂] , [k₂′] = wf-Level-eq k₂≡k₂′
    in supᵘˡᵣ [k₁] [k₂] , supᵘˡᵣ [k₁′] [k₂′]
  wf-[neLevel]-prop (supᵘʳᵣ k₁≡k₁′ k₂≡k₂′) =
    let [k₁] , [k₁′] = wf-Level-eq k₁≡k₁′
        [k₂] , [k₂′] = wf-[neLevel]-prop k₂≡k₂′
    in supᵘʳᵣ [k₁] [k₂] , supᵘʳᵣ [k₁′] [k₂′]
  wf-[neLevel]-prop (supᵘ-zeroʳᵣ ⊩k) =
    let ok = inversion-Level-⊢ (wf-⊢ (escape-neLevel-prop ⊩k)) in
    supᵘˡᵣ ⊩k (term (id (zeroᵘⱼ ok (wf-neLevel-prop ⊩k))) (zeroᵘᵣ ok)) ,
    ⊩k
  wf-[neLevel]-prop (supᵘ-assoc¹ᵣ ⊩t ⊩u ⊩v) =
    let ok = inversion-Level-⊢ (wf-⊢ (escape-neLevel-prop ⊩t)) in
    supᵘˡᵣ (supᵘˡᵣ ⊩t ⊩u) ⊩v , supᵘˡᵣ ⊩t (⊩supᵘ ok ⊩u ⊩v)
  wf-[neLevel]-prop (supᵘ-assoc²ᵣ [t] [u] [v]) =
    supᵘˡᵣ (supᵘʳᵣ [t] [u]) [v] , supᵘʳᵣ [t] (supᵘˡᵣ [u] [v])
  wf-[neLevel]-prop (supᵘ-assoc³ᵣ ⊩t ⊩u ⊩v) =
    let ok = inversion-Level-⊢ (wf-⊢ (escape-neLevel-prop ⊩v)) in
    supᵘʳᵣ (⊩supᵘ ok ⊩t ⊩u) ⊩v , supᵘʳᵣ ⊩t (supᵘʳᵣ ⊩u ⊩v)
  wf-[neLevel]-prop (supᵘ-comm¹ᵣ [t₁] d [u₂] d′) =
    let [u₁] , _ = wf-Level-eq d′
        _ , [t₂] = wf-Level-eq d
    in supᵘˡᵣ [t₁] [u₁] , supᵘˡᵣ [u₂] [t₂]
  wf-[neLevel]-prop (supᵘ-comm²ᵣ [t₁] d [u]) =
    let _ , [t₂] = wf-Level-eq d
    in supᵘʳᵣ [t₁] [u] , supᵘˡᵣ [u] [t₂]
  wf-[neLevel]-prop (supᵘ-idemᵣ [u] y) =
    let _ , [t₂] = wf-Level-eq y
    in supᵘˡᵣ [u] [t₂] , [u]
  wf-[neLevel]-prop (ne x) =
    let a , b = wf-neNf x
    in ne a , ne b

opaque

  -- Left congruence for supᵘ.

  private
    ⊩supᵘ-congʳ-⇒* :
      ∀ {t u u′} →
      Level-prop Γ t →
      Γ ⊩Level level u′ ∷Level →
      Γ ⊢ u ⇒* u′ ∷ Level →
      Γ ⊩Level level (t supᵘ u) ≡ level (t supᵘ u′) ∷Level
    ⊩supᵘ-congʳ-⇒* (zeroᵘᵣ ok) ⊩u′ u⇒ =
      ⊩Level≡-⇒*
        (redMany (supᵘ-zeroˡ (redFirst*Term u⇒)))
        (redMany (supᵘ-zeroˡ (⊢∷Level→⊢∷Level ok (escapeLevel ⊩u′))))
        (redLevel′ u⇒ ⊩u′)
    ⊩supᵘ-congʳ-⇒* (sucᵘᵣ ok ⊩t) ⊩u′ u⇒ =
      redLevel′ (supᵘ-substʳ* (⊢∷Level→⊢∷Level ok (escapeLevel ⊩t)) u⇒)
        (⊩supᵘ ok (⊩1ᵘ+ ⊩t) ⊩u′)
    ⊩supᵘ-congʳ-⇒* (neLvl ⊩t) ⊩u′ u⇒ =
      ⊩[neLvl] (supᵘˡᵣ (reflneLevel-prop ⊩t) (redLevel′ u⇒ ⊩u′))

  mutual
    ⊩supᵘ-congˡ-prop :
      [Level]-prop Γ t₁′ t₂′ →
      Γ ⊩Level level u ∷Level →
      Γ ⊩Level level (t₁′ supᵘ u) ≡ level (t₂′ supᵘ u) ∷Level
    ⊩supᵘ-congˡ-prop (zeroᵘᵣ ok) ⊩u =
      let ⊢u = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩u)
          d  = redMany (supᵘ-zeroˡ ⊢u)
      in
      ⊩Level≡-⇒* d d (reflLevel ⊩u)
    ⊩supᵘ-congˡ-prop (sucᵘᵣ okᴸ _) (literal ok _) =
      Level-allowed→Allowed-literal→ okᴸ ok
    ⊩supᵘ-congˡ-prop (sucᵘᵣ ok t₁′≡t₂′) (term u⇒ propu) =
      let _ , ⊢t₁′ , ⊢t₂′ =
            wf-⊢ (≅ₜ-eq (⊢≅∷L→⊢≅∷ ok $ escapeLevelEq t₁′≡t₂′))
      in
      ⊩Level≡-⇒* (supᵘ-substʳ* ⊢t₁′ u⇒) (supᵘ-substʳ* ⊢t₂′ u⇒) $
      case propu of λ where
        (zeroᵘᵣ _) →
          ⊩Level≡-⇒*
            (redMany (supᵘ-zeroʳ ⊢t₁′))
            (redMany (supᵘ-zeroʳ ⊢t₂′))
            (⊩1ᵘ+≡1ᵘ+ t₁′≡t₂′)
        (sucᵘᵣ _ ⊩u′) →
          let ⊢u′ = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩u′) in
          ⊩Level≡-⇒*
            (redMany (supᵘ-sucᵘ ⊢t₁′ ⊢u′))
            (redMany (supᵘ-sucᵘ ⊢t₂′ ⊢u′))
            (⊩1ᵘ+≡1ᵘ+ (⊩supᵘ-congˡ ok t₁′≡t₂′ ⊩u′))
        (neLvl ⊩u′) →
          ⊩[neLvl] (supᵘʳᵣ t₁′≡t₂′ (reflneLevel-prop ⊩u′))
    ⊩supᵘ-congˡ-prop {Γ} {u} k≤1+k′@(supᵘ-subᵣ {k′} ⊩k k≤k′) ⊩u =
      let okᴸ = inversion-Level-⊢ (wf-⊢ (escape-neLevel-prop ⊩k)) in
      case ⊩u of λ where
        (literal ok _) →
          Level-allowed→Allowed-literal→ okᴸ ok
        (term u⇒ propu) →
          let _ , ⊩k′ = wf-Level-eq k≤k′
              ⊢k      = escape-neLevel-prop ⊩k
              ⊢k′     = ⊢∷Level→⊢∷Level okᴸ (escapeLevel ⊩k′)
              ⊩k′+1   = ⊩1ᵘ+ ⊩k′
              ⊩k⊔k′+1 = ⊩supᵘ okᴸ (⊩neLvl ⊩k) ⊩k′+1
              ⊢Γ      = wf (redFirst*Term u⇒)
          in case propu of λ where
            (zeroᵘᵣ _) →
              transEqTermLevel (⊩supᵘ-zeroʳ′ ⊩k⊔k′+1 u⇒) $
                transEqTermLevel (⊩[Lvl] ⊢Γ k≤1+k′) $
                symLevel (⊩supᵘ-zeroʳ′ (⊩1ᵘ+ ⊩k′) u⇒)
            (sucᵘᵣ {k = u′} _ ⊩u′) →
              let ⊢u′ = ⊢∷Level→⊢∷Level okᴸ (escapeLevel ⊩u′)

                  d : Γ ⊢ sucᵘ k′ supᵘ u ⇒* sucᵘ (k′ supᵘ u′) ∷ Level
                  d =
                    supᵘ-substʳ* ⊢k′ u⇒ ⇨∷* redMany (supᵘ-sucᵘ ⊢k′ ⊢u′)
              in
                -- (k ⊔ sucᵘ k′) ⊔ u
                transEqTermLevel
                  (⊩supᵘ-assoc okᴸ (⊩neLvl ⊩k) (⊩1ᵘ+ ⊩k′) ⊩u) $
                -- k ⊔ (sucᵘ k′ ⊔ u)
                transEqTermLevel
                  (⊩supᵘ-congʳ-⇒* (neLvl ⊩k)
                     (⊩1ᵘ+ (⊩supᵘ okᴸ ⊩k′ ⊩u′)) d) $
                -- k ⊔ sucᵘ (k′ ⊔ u′)
                term (id (supᵘⱼ ⊢k (sucᵘⱼ (supᵘⱼ ⊢k′ ⊢u′)))) d
                  (supᵘ-subᵣ ⊩k (transEqTermLevel
                    -- k ⊔ (k′ ⊔ u′)
                    (symLevel (⊩supᵘ-assoc okᴸ (⊩neLvl ⊩k) ⊩k′ ⊩u′))
                    -- (k ⊔ k′) ⊔ u′
                    (⊩supᵘ-congˡ okᴸ k≤k′ ⊩u′)))
                    -- k′ ⊔ u′
                -- sucᵘ k′ ⊔ u
            (neLvl ⊩u′) →
              transEqTermLevel
                (⊩supᵘ-comm okᴸ (⊩supᵘ okᴸ (⊩neLvl ⊩k) (⊩1ᵘ+ ⊩k′)) ⊩u) $
                transEqTermLevel
                  (term
                     (supᵘ-substˡ* u⇒ (supᵘⱼ ⊢k (sucᵘⱼ ⊢k′)))
                     (supᵘ-substˡ* u⇒ (sucᵘⱼ ⊢k′))
                     ([Level]-prop.neLvl $
                      supᵘˡᵣ (reflneLevel-prop ⊩u′)
                        (⊩[Lvl] (wf ⊢k) k≤1+k′))) $
                ⊩supᵘ-comm okᴸ ⊩u (⊩1ᵘ+ ⊩k′)
    ⊩supᵘ-congˡ-prop (neLvl x) [u] =
      ⊩[neLvl] (supᵘˡᵣ x (reflLevel [u]))
    ⊩supᵘ-congˡ-prop (sym t₁′≡t₂′) [u] =
      symLevel (⊩supᵘ-congˡ-prop t₁′≡t₂′ [u])
    ⊩supᵘ-congˡ-prop (trans t₁′≡t₂′ t₂′≡t₃′) [u] =
      transEqTermLevel (⊩supᵘ-congˡ-prop t₁′≡t₂′ [u]) (⊩supᵘ-congˡ-prop t₂′≡t₃′ [u])

    ⊩supᵘ-congˡ :
      Level-allowed →
      Γ ⊩Level level t₁ ≡ level t₂ ∷Level →
      Γ ⊩Level level u ∷Level →
      Γ ⊩Level level (t₁ supᵘ u) ≡ level (t₂ supᵘ u) ∷Level
    ⊩supᵘ-congˡ ok (term t₁⇒ t₂⇒ prop) ⊩u =
      let ⊢u = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩u) in
      ⊩Level≡-⇒* (supᵘ-substˡ* t₁⇒ ⊢u) (supᵘ-substˡ* t₂⇒ ⊢u)
        (⊩supᵘ-congˡ-prop prop ⊩u)
    ⊩supᵘ-congˡ okᴸ (literal! ok _) _ =
      Level-allowed→Allowed-literal→ okᴸ ok

opaque

  -- Right congruence for supᵘ.

  ⊩supᵘ-congʳ :
    Level-allowed →
    Γ ⊩Level level t ∷Level →
    Γ ⊩Level level u₁ ≡ level u₂ ∷Level →
    Γ ⊩Level level (t supᵘ u₁) ≡ level (t supᵘ u₂) ∷Level
  ⊩supᵘ-congʳ ok ⊩t u₁≡u₂ =
    let ⊩u₁ , ⊩u₂ = wf-Level-eq u₁≡u₂ in
    transEqTermLevel (⊩supᵘ-comm ok ⊩t ⊩u₁) $
    transEqTermLevel (⊩supᵘ-congˡ ok u₁≡u₂ ⊩t) $
    ⊩supᵘ-comm ok ⊩u₂ ⊩t

opaque

  -- Congruence for supᵘ.

  ⊩supᵘ≡supᵘ :
    Level-allowed →
    Γ ⊩Level level t₁ ≡ level t₂ ∷Level →
    Γ ⊩Level level u₁ ≡ level u₂ ∷Level →
    Γ ⊩Level level (t₁ supᵘ u₁) ≡ level (t₂ supᵘ u₂) ∷Level
  ⊩supᵘ≡supᵘ ok t₁≡t₂ u₁≡u₂ =
    let ⊩t₁ , ⊩t₂ = wf-Level-eq t₁≡t₂
        ⊩u₁ , ⊩u₂ = wf-Level-eq u₁≡u₂
    in
    transEqTermLevel (⊩supᵘ-congʳ ok ⊩t₁ u₁≡u₂)
      (⊩supᵘ-congˡ ok t₁≡t₂ ⊩u₂)

opaque

  -- Distributivity of sucᵘ over _supᵘ_ (assuming that Level is
  -- allowed).

  ⊩sucᵘ-supᵘ-sucᵘ≡sucᵘ-supᵘ :
    Level-allowed →
    Γ ⊩Level level t ∷Level →
    Γ ⊩Level level u ∷Level →
    Γ ⊩Level level (sucᵘ t supᵘ sucᵘ u) ≡ level (sucᵘ (t supᵘ u)) ∷Level
  ⊩sucᵘ-supᵘ-sucᵘ≡sucᵘ-supᵘ ok ⊩t ⊩u =
    redLevel′
      (redMany $
       supᵘ-sucᵘ (⊢∷Level→⊢∷Level ok (escapeLevel ⊩t))
          (⊢∷Level→⊢∷Level ok (escapeLevel ⊩u)))
      (⊩1ᵘ+ (⊩supᵘ ok ⊩t ⊩u))

------------------------------------------------------------------------
-- Level realisation

opaque
  unfolding Allowed-literal→Universe-level ↑ᵘ

  -- The result of ↑ᵘ is necessarily strictly less than ωᵘ·2.

  ↑ᵘ<ᵘωᵘ·2 :
    {⊩l : Γ ⊩Level l ∷Level} →
    ↑ᵘ ⊩l <ᵘ ωᵘ·2
  ↑ᵘ<ᵘωᵘ·2 {⊩l = term _ _}    = 0ᵘ+<ᵘωᵘ·2
  ↑ᵘ<ᵘωᵘ·2 {⊩l = literal _ _} = Level-literal→Universe-level<ᵘωᵘ·2

opaque

  -- A simplification lemma for ↑ᵘ.

  ↑ᵘ-subst :
    {eq : l₁ PE.≡ l₂} {⊩l : Γ ⊩Level l₁ ∷Level} →
    ↑ᵘ (PE.subst (_⊩Level_∷Level _) eq ⊩l) PE.≡ ↑ᵘ ⊩l
  ↑ᵘ-subst {eq = PE.refl} = PE.refl

-- Irrelevance of the reducibility proof for level realisation.

opaque
  unfolding ↑ⁿ

  mutual
    ↑ⁿ-irrelevance
      : ∀ {t} ([t] [t]′ : Γ ⊩Level level t ∷Level)
      → ↑ⁿ ok₁ [t] PE.≡ ↑ⁿ ok₂ [t]′
    ↑ⁿ-irrelevance (term t⇒ ⊩t) (term t⇒′ ⊩t′) =
      case whrDet*Term (t⇒ , Level-prop→Whnf ⊩t)
             (t⇒′ , Level-prop→Whnf ⊩t′) of λ {
        PE.refl →
      ↑ⁿ-prop-irrelevance ⊩t ⊩t′ }
    ↑ⁿ-irrelevance {ok₁} _ (literal ok _) =
      Level-allowed→Allowed-literal→ ok₁ ok
    ↑ⁿ-irrelevance {ok₁} (literal ok _) _ =
      Level-allowed→Allowed-literal→ ok₁ ok

    ↑ⁿ-prop-irrelevance
      : ∀ {t} ([t] [t]′ : Level-prop Γ t)
      → ↑ⁿ-prop ok₁ [t] PE.≡ ↑ⁿ-prop ok₂ [t]′
    ↑ⁿ-prop-irrelevance (zeroᵘᵣ _) (zeroᵘᵣ _) =
      PE.refl
    ↑ⁿ-prop-irrelevance (sucᵘᵣ _ ⊩t) (sucᵘᵣ _ ⊩t′) =
      PE.cong 1+ (↑ⁿ-irrelevance ⊩t ⊩t′)
    ↑ⁿ-prop-irrelevance (neLvl ⊩t) (neLvl ⊩t′) =
      ↑ⁿ-neprop-irrelevance ⊩t ⊩t′
    ↑ⁿ-prop-irrelevance (zeroᵘᵣ _) (neLvl (ne (neNfₜ₌ (ne () _) _ _)))
    ↑ⁿ-prop-irrelevance
      (sucᵘᵣ _ _) (neLvl (ne (neNfₜ₌ (ne () _) _ _)))
    ↑ⁿ-prop-irrelevance (neLvl (ne (neNfₜ₌ (ne () _) _ _))) (zeroᵘᵣ _)
    ↑ⁿ-prop-irrelevance
      (neLvl (ne (neNfₜ₌ (ne () _) _ _))) (sucᵘᵣ _ _)

    ↑ⁿ-neprop-irrelevance
      : ∀ {t} ([t] [t]′ : neLevel-prop Γ t)
      → ↑ⁿ-neprop ok₁ [t] PE.≡ ↑ⁿ-neprop ok₂ [t]′
    ↑ⁿ-neprop-irrelevance (supᵘˡᵣ x x₁) (supᵘˡᵣ y x₂) =
      PE.cong₂ _⊔_ (↑ⁿ-neprop-irrelevance x y) (↑ⁿ-irrelevance x₁ x₂)
    ↑ⁿ-neprop-irrelevance (supᵘʳᵣ x x₁) (supᵘʳᵣ x₂ y) =
      PE.cong₂ _⊔_ (PE.cong 1+ (↑ⁿ-irrelevance x x₂)) (↑ⁿ-neprop-irrelevance x₁ y)
    ↑ⁿ-neprop-irrelevance (ne x) (ne x₁) = PE.refl
    ↑ⁿ-neprop-irrelevance (supᵘˡᵣ x x₁) (supᵘʳᵣ x₂ y) = case nelevel x of λ ()
    ↑ⁿ-neprop-irrelevance (supᵘˡᵣ _ _) (ne (neNfₜ₌ _ n _)) =
      Neutralᵃ-supᵘ→ n
    ↑ⁿ-neprop-irrelevance (supᵘʳᵣ x x₁) (supᵘˡᵣ y x₂) = case nelevel y of λ ()
    ↑ⁿ-neprop-irrelevance (supᵘʳᵣ _ _) (ne (neNfₜ₌ _ n _)) =
      Neutralᵃ-supᵘ→ n
    ↑ⁿ-neprop-irrelevance (ne (neNfₜ₌ _ n _)) (supᵘˡᵣ _ _) =
      Neutralᵃ-supᵘ→ n
    ↑ⁿ-neprop-irrelevance (ne (neNfₜ₌ _ n _)) (supᵘʳᵣ _ _) =
      Neutralᵃ-supᵘ→ n

opaque
  unfolding ↑ᵘ

  ↑ᵘ-irrelevance :
    {⊩l₁ ⊩l₂ : Γ ⊩Level l ∷Level} → ↑ᵘ ⊩l₁ PE.≡ ↑ᵘ ⊩l₂
  ↑ᵘ-irrelevance {⊩l₁ = ⊩t₁@(term _ _)} {⊩l₂ = ⊩t₂@(term _ _)} =
    PE.cong 0ᵘ+ (↑ⁿ-irrelevance ⊩t₁ ⊩t₂)
  ↑ᵘ-irrelevance {⊩l₁ = literal ok _} {⊩l₂ = term t⇒ _} =
    ⇒*∷Level→Allowed-literal→ t⇒ ok
  ↑ᵘ-irrelevance {⊩l₁ = term t⇒ _} {⊩l₂ = literal ok _} =
    ⇒*∷Level→Allowed-literal→ t⇒ ok
  ↑ᵘ-irrelevance {⊩l₁ = literal ok₁ _} {⊩l₂ = literal ok₂ _} =
    Allowed-literal→Universe-level ok₁  ≡⟨ Allowed-literal→Universe-level-irrelevance ⟩
    Allowed-literal→Universe-level ok₂  ∎

opaque
  unfolding ↑ⁿ

  -- Level realisation sends every atomic neutral level to a fixed
  -- external level.

  ↑ⁿ-prop-ne :
    (⊩t : Level-prop Γ t) →
    Neutralᵃ V (Γ .defs) t →
    ↑ⁿ-prop okᴸ ⊩t PE.≡ ↑ᵘ-neutral
  ↑ⁿ-prop-ne = λ where
    (zeroᵘᵣ _)           (ne () _)
    (sucᵘᵣ _ _)          (ne () _)
    (neLvl (supᵘˡᵣ _ _)) n         → Neutralᵃ-supᵘ→ n
    (neLvl (supᵘʳᵣ _ _)) n         → Neutralᵃ-supᵘ→ n
    (neLvl (ne _))       _         → PE.refl

opaque
  unfolding ↑ⁿ

  -- Level realisation sends every atomic neutral level to a fixed
  -- external level.

  ↑ⁿ-ne :
    (⊩t : Γ ⊩Level level t ∷Level) →
    Neutralᵃ V (Γ .defs) t →
    ↑ⁿ okᴸ ⊩t PE.≡ ↑ᵘ-neutral
  ↑ⁿ-ne (term l⇒l′ l′-prop) l-ne =
    case whnfRed*Term l⇒l′ (ne! l-ne) of λ {
      PE.refl →
    ↑ⁿ-prop-ne l′-prop l-ne }
  ↑ⁿ-ne (literal ok _) l-ne =
    ⊥-elim $
    ¬-Neutral-Level-literal (Allowed-literal-level-⇔ .proj₁ ok .proj₁)
      (ne⁻ l-ne)

opaque
  unfolding ↑ⁿ

  -- Level realisation sends zeroᵘ to 0.

  ↑ⁿ-prop-zeroᵘ :
    ([0] : Level-prop Γ zeroᵘ) → ↑ⁿ-prop okᴸ [0] PE.≡ 0
  ↑ⁿ-prop-zeroᵘ (zeroᵘᵣ _) = PE.refl
  ↑ⁿ-prop-zeroᵘ (neLvl n) = case nelevel n of λ ()

  ↑ⁿ-zeroᵘ : ([0] : Γ ⊩Level zeroᵘₗ ∷Level) → ↑ⁿ okᴸ [0] PE.≡ 0
  ↑ⁿ-zeroᵘ (term 0⇒ prop) with whnfRed*Term 0⇒ zeroᵘₙ
  ... | PE.refl = ↑ⁿ-prop-zeroᵘ prop
  ↑ⁿ-zeroᵘ {okᴸ} (literal ok _) =
    Level-allowed→Allowed-literal→ okᴸ ok

opaque
  unfolding Allowed-literal→Universe-level ↑ᵘ

  ↑ᵘ-zeroᵘ : (⊩0 : Γ ⊩Level zeroᵘₗ ∷Level) → ↑ᵘ ⊩0 PE.≡ 0ᵘ
  ↑ᵘ-zeroᵘ ⊩0@(term _ _)  = PE.cong 0ᵘ+ (↑ⁿ-zeroᵘ ⊩0)
  ↑ᵘ-zeroᵘ (literal ok _) =
    Allowed-literal→Universe-level ok                   ≡⟨ PE.cong Level-literal→Universe-level Level-literal-propositional ⟩
    Level-literal→Universe-level (level {n = 0} zeroᵘ)  ≡⟨⟩
    0ᵘ                                                  ∎

opaque
  unfolding ↑ⁿ ⊩1ᵘ+

  -- Level realisation sends sucᵘ to 1+.

  ↑ⁿ-prop-sucᵘ
    : ∀ {t} ([t+1] : Level-prop Γ (sucᵘ t))
    → ∃ λ ([t] : Γ ⊩Level level t ∷Level) →
        ↑ⁿ-prop okᴸ [t+1] PE.≡ 1+ (↑ⁿ okᴸ [t])
  ↑ⁿ-prop-sucᵘ (sucᵘᵣ _ ⊩t) = ⊩t , PE.refl
  ↑ⁿ-prop-sucᵘ (neLvl n)    = case nelevel n of λ ()

  ↑ⁿ-sucᵘ :
    ([t] : Γ ⊩Level level t ∷Level)
    ([t+1] : Γ ⊩Level level (sucᵘ t) ∷Level) →
    ↑ⁿ ok₁ [t+1] PE.≡ 1+ (↑ⁿ ok₂ [t])
  ↑ⁿ-sucᵘ ⊩t@(term _ _) ⊩t+1 =
    ↑ⁿ-irrelevance ⊩t+1 (⊩1ᵘ+ ⊩t)
  ↑ⁿ-sucᵘ {ok₁} (literal ok _) _ =
    Level-allowed→Allowed-literal→ ok₁ ok

opaque
  unfolding Allowed-literal→Universe-level ↑ᵘ

  ↑ᵘ-1ᵘ+ :
    {⊩l : Γ ⊩Level l ∷Level}
    {⊩1+l : Γ ⊩Level 1ᵘ+ l ∷Level} →
    ↑ᵘ ⊩1+l PE.≡ sucᵘₗ (↑ᵘ ⊩l)
  ↑ᵘ-1ᵘ+ {l = level _} {⊩l = term _ _} {⊩1+l = term _ _} =
    PE.cong 0ᵘ+ (↑ⁿ-sucᵘ _ _)
  ↑ᵘ-1ᵘ+ {l = level _} {⊩l = literal ok _} {⊩1+l = term ⇒∷L _} =
    ⇒*∷Level→Allowed-literal→ ⇒∷L ok
  ↑ᵘ-1ᵘ+ {l = level _} {⊩l = term ⇒∷L _} {⊩1+l = literal ok _} =
    ⇒*∷Level→Allowed-literal→ ⇒∷L ok
  ↑ᵘ-1ᵘ+ {l = level t} {⊩l = literal ok₁ _} {⊩1+l = literal ok₂ _} =
    let 1+t-lit = Allowed-literal→Level-literal ok₂
        t-lit   = Allowed-literal→Level-literal ok₁
    in
    Allowed-literal→Universe-level ok₂                               ≡⟨ Level-literal→Universe-level-level ⟩
    0ᵘ+ (size-of-Level (Level-literal-level-⇔ .proj₁ 1+t-lit))       ≡⟨ PE.cong (0ᵘ+ ∘→ size-of-Level) Level-literal-propositional ⟩
    0ᵘ+ (size-of-Level (sucᵘ (Level-literal-level-⇔ .proj₁ t-lit)))  ≡⟨⟩
    0ᵘ+ (1+ (size-of-Level (Level-literal-level-⇔ .proj₁ t-lit)))    ≡˘⟨ PE.cong sucᵘₗ Level-literal→Universe-level-level ⟩
    sucᵘₗ (Allowed-literal→Universe-level ok₁)                       ∎
  ↑ᵘ-1ᵘ+ {l = ωᵘ+ _} {⊩l = literal _ _} {⊩1+l = literal _ _} =
    PE.refl

opaque
  unfolding ↑ⁿ ⊩supᵘ

  -- Level realisation sends _supᵘ_ to _⊔_.

  ↑ⁿ-supᵘ :
    (⊩t : Γ ⊩Level level t ∷Level)
    (⊩u : Γ ⊩Level level u ∷Level) →
    ↑ⁿ ok₁ (⊩supᵘ ok₂ ⊩t ⊩u) PE.≡ ↑ⁿ ok₁ ⊩t ⊔ ↑ⁿ ok₁ ⊩u
  ↑ⁿ-supᵘ (term _ (zeroᵘᵣ _)) (term _ _) =
    PE.refl
  ↑ⁿ-supᵘ (term _ (sucᵘᵣ _ _)) (term _ (zeroᵘᵣ _)) =
    PE.refl
  ↑ⁿ-supᵘ {ok₁} {ok₂} (term _ (sucᵘᵣ _ ⊩t)) (term _ (sucᵘᵣ _ ⊩u)) =
    1+ (↑ⁿ ok₁ (⊩supᵘ ok₂ ⊩t ⊩u))    ≡⟨ PE.cong 1+ (↑ⁿ-supᵘ ⊩t ⊩u) ⟩
    1+ (↑ⁿ ok₁ ⊩t ⊔ ↑ⁿ ok₁ ⊩u)       ≡⟨⟩
    1+ (↑ⁿ ok₁ ⊩t) ⊔ 1+ (↑ⁿ ok₁ ⊩u)  ∎
  ↑ⁿ-supᵘ (term _ (sucᵘᵣ _ _)) (term _ (neLvl _)) =
    PE.refl
  ↑ⁿ-supᵘ (term _ (neLvl _)) (term _ _) =
    PE.refl
  ↑ⁿ-supᵘ {ok₁} (literal ok _) _ =
    Level-allowed→Allowed-literal→ ok₁ ok
  ↑ⁿ-supᵘ {ok₁} _ (literal ok _) =
    Level-allowed→Allowed-literal→ ok₁ ok

  ↑ⁿ-supᵘ′ :
    (⊩t : Γ ⊩Level level t ∷Level)
    (⊩u : Γ ⊩Level level u ∷Level)
    (⊩t⊔u : Γ ⊩Level level (t supᵘ u) ∷Level) →
    ↑ⁿ ok₁ ⊩t⊔u PE.≡ ↑ⁿ ok₂ ⊩t ⊔ ↑ⁿ ok₃ ⊩u
  ↑ⁿ-supᵘ′ {ok₁} {ok₂} {ok₃} ⊩t ⊩u ⊩t⊔u =
    ↑ⁿ ok₁ ⊩t⊔u               ≡⟨ ↑ⁿ-irrelevance ⊩t⊔u (⊩supᵘ ok₁ ⊩t ⊩u) ⟩
    ↑ⁿ ok₁ (⊩supᵘ ok₁ ⊩t ⊩u)  ≡⟨ ↑ⁿ-supᵘ ⊩t ⊩u ⟩
    ↑ⁿ ok₁ ⊩t ⊔ ↑ⁿ ok₁ ⊩u     ≡⟨ PE.cong₂ _⊔_ (↑ⁿ-irrelevance ⊩t ⊩t) (↑ⁿ-irrelevance ⊩u ⊩u) ⟩
    ↑ⁿ ok₂ ⊩t ⊔ ↑ⁿ ok₃ ⊩u     ∎

opaque
  unfolding ↑ᵘ

  ↑ᵘ-supᵘ :
    (⊩t : Γ ⊩Level level t ∷Level)
    (⊩u : Γ ⊩Level level u ∷Level) →
    ↑ᵘ (⊩supᵘ okᴸ ⊩t ⊩u) PE.≡ ↑ᵘ ⊩t ⊔ᵘ ↑ᵘ ⊩u
  ↑ᵘ-supᵘ {okᴸ} ⊩t@(term t⇒* t′-prop) ⊩u@(term u⇒* u′-prop)
    with ⊩supᵘ okᴸ ⊩t ⊩u
  … | ⊩t⊔u@(term t⊔u⇒* _) =
    let ok  = inversion-Level-⊢ (wf-⊢ (subset*Term t⊔u⇒*) .proj₁)
        ok₁ = inversion-Level-⊢ (wf-⊢ (subset*Term t⇒*) .proj₁)
        ok₂ = inversion-Level-⊢ (wf-⊢ (subset*Term u⇒*) .proj₁)
    in
    0ᵘ+ (↑ⁿ ok ⊩t⊔u)             ≡⟨ PE.cong 0ᵘ+ (↑ⁿ-supᵘ′ ⊩t ⊩u ⊩t⊔u) ⟩
    0ᵘ+ (↑ⁿ ok₁ ⊩t ⊔ ↑ⁿ ok₂ ⊩u)  ∎
  … | literal ok _ =
    case Allowed-literal→Level-literal ok of λ { (level ()) }
  ↑ᵘ-supᵘ {okᴸ} (literal ok _) _ =
    Level-allowed→Allowed-literal→ okᴸ ok
  ↑ᵘ-supᵘ {okᴸ} _ (literal ok _) =
    Level-allowed→Allowed-literal→ okᴸ ok

opaque
  unfolding Allowed-literal→Universe-level ↑ᵘ ⊩supᵘₗ

  -- A variant of ↑ᵘ-supᵘ for _supᵘₗ_.

  ↑ᵘ-supᵘₗ :
    {⊩l₁ : Γ ⊩Level l₁ ∷Level}
    {⊩l₂ : Γ ⊩Level l₂ ∷Level} →
    ↑ᵘ (⊩supᵘₗ ⊩l₁ ⊩l₂) PE.≡ ↑ᵘ ⊩l₁ ⊔ᵘ ↑ᵘ ⊩l₂
  ↑ᵘ-supᵘₗ {⊩l₁ = ⊩l₁@(term ⇒∷Level _)} {⊩l₂ = ⊩l₂@(term _ _)} =
    let ok = inversion-Level-⊢ (wf-⊢ (subset*Term ⇒∷Level) .proj₁) in
    ↑ᵘ (PE.subst (_⊩Level_∷Level _) (PE.sym $ supᵘₗ≡supᵘ ok)
          (⊩supᵘ ok ⊩l₁ ⊩l₂))                                 ≡⟨ ↑ᵘ-subst {eq = PE.sym $ supᵘₗ≡supᵘ _} ⟩

    ↑ᵘ (⊩supᵘ ok ⊩l₁ ⊩l₂)                                     ≡⟨ ↑ᵘ-supᵘ _ _ ⟩

    ↑ᵘ ⊩l₁ ⊔ᵘ ↑ᵘ ⊩l₂                                          ∎
  ↑ᵘ-supᵘₗ {⊩l₁ = literal _ _} {⊩l₂ = literal _ _} =
    Allowed-literal→Universe-level-Allowed-literal-supᵘₗ
  ↑ᵘ-supᵘₗ {l₂} {⊩l₁ = ⊩t₁@(term ⇒∷Level _)} {⊩l₂ = literal ok _}
    using okᴸ ← inversion-Level-⊢ (wf-⊢ (subset*Term ⇒∷Level) .proj₁)
    with Allowed-literal→Infinite {l = l₂} okᴸ ok
  … | ωᵘ+ =
    PE.refl
  ↑ᵘ-supᵘₗ {l₁} {⊩l₁ = literal ok _} {⊩l₂ = ⊩t₂@(term ⇒∷Level _)}
    using okᴸ ← inversion-Level-⊢ (wf-⊢ (subset*Term ⇒∷Level) .proj₁)
    with Allowed-literal→Infinite {l = l₁} okᴸ ok
  … | ωᵘ+ =
    PE.refl

opaque

  -- The level zeroᵘₗ is the smallest level.

  zeroᵘ-≤ᵘ : {⊩0 : Γ ⊩Level zeroᵘₗ ∷Level} → ↑ᵘ ⊩0 ≤ᵘ ℓ
  zeroᵘ-≤ᵘ {⊩0} = PE.subst (_≤ᵘ _) (PE.sym (↑ᵘ-zeroᵘ ⊩0)) 0≤ᵘ

opaque

  -- sucᵘ is inflationary.

  <′-sucᵘ :
    (⊩t : Γ ⊩Level level t ∷Level)
    (⊩1+t : Γ ⊩Level level (sucᵘ t) ∷Level) →
    ↑ⁿ ok₁ ⊩t <′ ↑ⁿ ok₂ ⊩1+t
  <′-sucᵘ ⊩t ⊩1+t =
    PE.subst (↑ⁿ _ ⊩t <′_) (PE.sym (↑ⁿ-sucᵘ ⊩t ⊩1+t)) ≤′-refl

opaque
  unfolding Allowed-literal→Universe-level ↑ᵘ

  -- 1ᵘ+ is inflationary.

  <ᵘ-1ᵘ+ :
    (⊩l : Γ ⊩Level l ∷Level) (⊩1+l : Γ ⊩Level 1ᵘ+ l ∷Level) →
    ↑ᵘ ⊩l <ᵘ ↑ᵘ ⊩1+l
  <ᵘ-1ᵘ+ {l = ωᵘ+ _} (literal _ _) (literal _ _) =
    ωᵘ+<ᵘωᵘ+ (<⇒<′ ≤-refl)
  <ᵘ-1ᵘ+ {l = level _} (term _ _) (term _ _) =
    0ᵘ+<ᵘ0ᵘ+ (<′-sucᵘ _ _)
  <ᵘ-1ᵘ+ {l = level _} (term ⇒∷Level _) (literal ok _) =
    ⇒*∷Level→Allowed-literal→ ⇒∷Level ok
  <ᵘ-1ᵘ+ {l = level _} (literal ok _) (term ⇒∷Level _) =
    ⇒*∷Level→Allowed-literal→ ⇒∷Level ok
  <ᵘ-1ᵘ+ {l = level _} (literal ok₁ _) (literal ok₂ _) =
    PE.subst (_<ᵘ_ _)
      (PE.sym $
       PE.cong Level-literal→Universe-level Level-literal-propositional)
      (0ᵘ+<ᵘ0ᵘ+ ≤′-refl)

opaque

  -- t supᵘ u is an upper bound of t and u.

  ≤ᵘ-supᵘʳ :
    {ok : Level-allowed}
    {⊩t ⊩t′ : Γ ⊩Level level t ∷Level}
    {⊩u : Γ ⊩Level level u ∷Level} →
    ↑ᵘ ⊩t ≤ᵘ ↑ᵘ (⊩supᵘ ok ⊩t′ ⊩u)
  ≤ᵘ-supᵘʳ {⊩t′} {⊩u} = PE.subst₂ (_≤ᵘ_) ↑ᵘ-irrelevance (PE.sym $ ↑ᵘ-supᵘ ⊩t′ ⊩u) ≤ᵘ⊔ᵘʳ

  ≤ᵘ-supᵘˡ :
    {ok : Level-allowed}
    {⊩t : Γ ⊩Level level t ∷Level}
    {⊩u ⊩u′ : Γ ⊩Level level u ∷Level} →
    ↑ᵘ ⊩u ≤ᵘ ↑ᵘ (⊩supᵘ ok ⊩t ⊩u′)
  ≤ᵘ-supᵘˡ {⊩t} {⊩u′} = PE.subst₂ (_≤ᵘ_) ↑ᵘ-irrelevance (PE.sym $ ↑ᵘ-supᵘ ⊩t ⊩u′) ≤ᵘ⊔ᵘˡ

opaque

  -- A variant of ≤ᵘ-supᵘʳ for _supᵘₗ_.

  ≤ᵘ-supᵘₗʳ :
    {⊩l₁₁ ⊩l₁₂ : Γ ⊩Level l₁ ∷Level}
    {⊩l₂ : Γ ⊩Level l₂ ∷Level} →
    ↑ᵘ ⊩l₁₁ ≤ᵘ ↑ᵘ (⊩supᵘₗ ⊩l₁₂ ⊩l₂)
  ≤ᵘ-supᵘₗʳ = PE.subst₂ _≤ᵘ_ ↑ᵘ-irrelevance (PE.sym ↑ᵘ-supᵘₗ) ≤ᵘ⊔ᵘʳ

-- Level realisation preserves equality.

opaque
  unfolding ↑ⁿ ⊩1ᵘ+

  mutual
    ↑ⁿ-cong
      : ([t] : Γ ⊩Level level t ∷Level) ([u] : Γ ⊩Level level u ∷Level)
      → Γ ⊩Level level t ≡ level u ∷Level
      → ↑ⁿ ok₁ [t] PE.≡ ↑ⁿ ok₂ [u]
    ↑ⁿ-cong (term t⇒ ⊩t) (term u⇒ ⊩u) (term t⇒′ u⇒′ t′≡u′) =
      case whrDet*Term (t⇒ , Level-prop→Whnf ⊩t)
             (t⇒′ , lsplit t′≡u′ .proj₁) of λ {
        PE.refl →
      case whrDet*Term (u⇒ , Level-prop→Whnf ⊩u)
             (u⇒′ , lsplit t′≡u′ .proj₂) of λ {
        PE.refl →
      ↑ⁿ-prop-cong ⊩t ⊩u t′≡u′ }}
    ↑ⁿ-cong {ok₁} (literal ok _) _ _ =
      Level-allowed→Allowed-literal→ ok₁ ok
    ↑ⁿ-cong {ok₁} _ (literal ok _) _ =
      Level-allowed→Allowed-literal→ ok₁ ok
    ↑ⁿ-cong {ok₁} _ _ (literal ok _ _) =
      Level-allowed→Allowed-literal→ ok₁ ok

    ↑ⁿ-prop-cong
      : ∀ {t u} ([t] : Level-prop Γ t) ([u] : Level-prop Γ u)
      → [Level]-prop Γ t u
      → ↑ⁿ-prop ok₁ [t] PE.≡ ↑ⁿ-prop ok₂ [u]
    ↑ⁿ-prop-cong ⊩0 ⊩0′ (zeroᵘᵣ _) =
      PE.trans (↑ⁿ-prop-zeroᵘ ⊩0) (PE.sym (↑ⁿ-prop-zeroᵘ ⊩0′))
    ↑ⁿ-prop-cong ⊩1+t ⊩1+u (sucᵘᵣ _ t≡u) =
      let ⊩t , ↑⊩1+t≡ = ↑ⁿ-prop-sucᵘ ⊩1+t
          ⊩u , ↑⊩1+u≡ = ↑ⁿ-prop-sucᵘ ⊩1+u
      in
      PE.trans ↑⊩1+t≡ $
      PE.trans (PE.cong 1+ (↑ⁿ-cong ⊩t ⊩u t≡u)) $
      PE.sym ↑⊩1+u≡
    ↑ⁿ-prop-cong
      (neLvl ⊩t⊔1+u) (sucᵘᵣ _ ⊩u@(term _ _)) (supᵘ-subᵣ ⊩t t≤u) =
      PE.trans
        (↑ⁿ-neprop-irrelevance ⊩t⊔1+u (supᵘˡᵣ ⊩t (⊩1ᵘ+ ⊩u)))
        (m≤n⇒m⊔n≡n $
         m≤n⇒m≤1+n (m⊔n≡n⇒m≤n (↑ⁿ-cong (⊩neLvl (supᵘˡᵣ ⊩t ⊩u)) ⊩u t≤u)))
    ↑ⁿ-prop-cong (neLvl x) (neLvl y) (neLvl z) = ↑ⁿ-neprop-cong x y z
    ↑ⁿ-prop-cong x y (sym z) = PE.sym (↑ⁿ-prop-cong y x z)
    ↑ⁿ-prop-cong {ok₂} x y (trans z z₁) =
      let _ , [k′] = wf-[Level]-prop z in
      PE.trans (↑ⁿ-prop-cong {ok₂ = ok₂} x [k′] z)
        (↑ⁿ-prop-cong [k′] y z₁)
    -- Absurd cases
    ↑ⁿ-prop-cong _ (sucᵘᵣ okᴸ (literal ok _)) _ =
      Level-allowed→Allowed-literal→ okᴸ ok
    ↑ⁿ-prop-cong (neLvl _) (neLvl ⊩u) (supᵘ-subᵣ _ _) =
      case nelevel ⊩u of λ ()
    ↑ⁿ-prop-cong (zeroᵘᵣ _) _ (neLvl t≡u) =
      case nelsplit t≡u of λ { (() , _) }
    ↑ⁿ-prop-cong (sucᵘᵣ _ _) _ (neLvl t≡u) =
      case nelsplit t≡u of λ { (() , _) }
    ↑ⁿ-prop-cong (neLvl _) (zeroᵘᵣ _) (neLvl t≡u) =
      case nelsplit t≡u of λ { (_ , ()) }
    ↑ⁿ-prop-cong (neLvl _) (sucᵘᵣ _ _) (neLvl t≡u) =
      case nelsplit t≡u of λ { (_ , ()) }

    ↑ⁿ-neprop-cong
      : ∀ {t u} ([t] : neLevel-prop Γ t) ([u] : neLevel-prop Γ u)
      → [neLevel]-prop Γ t u
      → ↑ⁿ-neprop ok₁ [t] PE.≡ ↑ⁿ-neprop ok₂ [u]
    ↑ⁿ-neprop-cong (supᵘˡᵣ x₄ x₅) (supᵘˡᵣ y x₇) (supᵘˡᵣ z x₃) =
      PE.cong₂ _⊔_ (↑ⁿ-neprop-cong x₄ y z) (↑ⁿ-cong x₅ x₇ x₃)
    ↑ⁿ-neprop-cong (supᵘʳᵣ x x₁) (supᵘʳᵣ x₂ y) (supᵘʳᵣ x₃ z) =
      PE.cong₂ _⊔_ (PE.cong 1+ (↑ⁿ-cong x x₂ x₃)) (↑ⁿ-neprop-cong x₁ y z)
    ↑ⁿ-neprop-cong (supᵘˡᵣ x x₁) y (supᵘ-zeroʳᵣ x₂) =
      PE.trans (PE.cong₂ _⊔_ (↑ⁿ-neprop-irrelevance x y) (↑ⁿ-zeroᵘ x₁)) (⊔-identityʳ _)
    ↑ⁿ-neprop-cong (ne x) (ne x₂) (ne x₁) = PE.refl
    ↑ⁿ-neprop-cong
      (supᵘˡᵣ (supᵘˡᵣ ⊩t₁ ⊩t₂) ⊩t₃) (supᵘˡᵣ ⊩u₁ ⊩u₂)
      (supᵘ-assoc¹ᵣ _ _ _) =
      let ok = inversion-Level-⊢ (wf-⊢ (escape-neLevel-prop ⊩t₁)) in
      PE.trans
        (⊔-assoc (↑ⁿ-neprop _ ⊩t₁) (↑ⁿ _ ⊩t₂) (↑ⁿ _ ⊩t₃))
        (PE.cong₂ _⊔_ (↑ⁿ-neprop-irrelevance ⊩t₁ ⊩u₁) (PE.trans
          (PE.sym (↑ⁿ-supᵘ ⊩t₂ ⊩t₃))
          (↑ⁿ-irrelevance (⊩supᵘ ok ⊩t₂ ⊩t₃) ⊩u₂)))
    ↑ⁿ-neprop-cong (supᵘˡᵣ (supᵘʳᵣ x x₄) x₃) (supᵘʳᵣ x₅ (supᵘˡᵣ y x₆)) (supᵘ-assoc²ᵣ x₁ z x₂) =
      PE.trans
        (⊔-assoc (1+ (↑ⁿ _ x)) (↑ⁿ-neprop _ x₄) (↑ⁿ _ x₃))
        (PE.cong₂ _⊔_ (PE.cong 1+ (↑ⁿ-irrelevance x x₅))
          (PE.cong₂ _⊔_ (↑ⁿ-neprop-irrelevance x₄ y)
            (↑ⁿ-irrelevance x₃ x₆)))
    ↑ⁿ-neprop-cong
      (supᵘʳᵣ ⊩t₁ ⊩t₂) (supᵘʳᵣ ⊩u₁ (supᵘʳᵣ ⊩u₂ ⊩u₃))
      (supᵘ-assoc³ᵣ _ _ _) =
      let ok = inversion-Level-⊢ (wf-⊢ (escape-neLevel-prop ⊩t₂)) in
      PE.trans
        (PE.cong₂ _⊔_
          (PE.cong 1+ $
           PE.trans (↑ⁿ-irrelevance ⊩t₁ (⊩supᵘ ok ⊩u₁ ⊩u₂)) (↑ⁿ-supᵘ ⊩u₁ ⊩u₂))
          (↑ⁿ-neprop-irrelevance ⊩t₂ ⊩u₃))
        (⊔-assoc (1+ (↑ⁿ _ ⊩u₁)) (1+ (↑ⁿ _ ⊩u₂)) (↑ⁿ-neprop _ ⊩u₃))
    ↑ⁿ-neprop-cong (supᵘˡᵣ x x₁) (supᵘˡᵣ y x₂) (supᵘ-comm¹ᵣ z d w d′) =
      PE.trans
        (⊔-comm (↑ⁿ-neprop _ x) (↑ⁿ _ x₁))
        (PE.cong₂ _⊔_ (↑ⁿ-cong x₁ (⊩neLvl y) d′) (↑ⁿ-cong (⊩neLvl x) x₂ d))
    ↑ⁿ-neprop-cong
      (supᵘʳᵣ ⊩t₁@(term _ _) ⊩t₂) (supᵘˡᵣ ⊩u₁ ⊩u₂)
      (supᵘ-comm²ᵣ _ 1+t₁≡u₂ _) =
      PE.trans
        (⊔-comm (1+ (↑ⁿ _ ⊩t₁)) (↑ⁿ-neprop _ ⊩t₂))
        (PE.cong₂ _⊔_ (↑ⁿ-neprop-irrelevance ⊩t₂ ⊩u₁)
           (↑ⁿ-cong (⊩1ᵘ+ ⊩t₁) ⊩u₂ 1+t₁≡u₂))
    ↑ⁿ-neprop-cong (supᵘˡᵣ x x₁) y (supᵘ-idemᵣ z w) = PE.trans
      (PE.cong₂ _⊔_
        (↑ⁿ-neprop-irrelevance x y)
        (PE.sym (↑ⁿ-cong (⊩neLvl y) x₁ w)))
      (⊔-idem (↑ⁿ-neprop _ y))
    -- Absurd cases
    ↑ⁿ-neprop-cong {ok₁} (supᵘʳᵣ (literal ok _) _) _ _ =
      Level-allowed→Allowed-literal→ ok₁ ok
    ↑ⁿ-neprop-cong (supᵘˡᵣ _ _) (supᵘʳᵣ _ _) (supᵘˡᵣ z _) = case nelsplit z .proj₂ of λ ()
    ↑ⁿ-neprop-cong _ (ne (neNfₜ₌ _ n _)) (supᵘˡᵣ _ _) =
      Neutralᵃ-supᵘ→ n
    ↑ⁿ-neprop-cong (supᵘʳᵣ _ _) _ (supᵘˡᵣ z _) = case nelsplit z .proj₁ of λ ()
    ↑ⁿ-neprop-cong (ne (neNfₜ₌ _ n _)) _ (supᵘˡᵣ _ _) =
      Neutralᵃ-supᵘ→ n
    ↑ⁿ-neprop-cong (supᵘˡᵣ x _) _ (supᵘʳᵣ _ _) = case nelevel x of λ ()
    ↑ⁿ-neprop-cong (supᵘʳᵣ _ _) (supᵘˡᵣ y _) (supᵘʳᵣ _ _) = case nelevel y of λ ()
    ↑ⁿ-neprop-cong _ (ne (neNfₜ₌ _ n _)) (supᵘʳᵣ _ _) =
      Neutralᵃ-supᵘ→ n
    ↑ⁿ-neprop-cong (ne (neNfₜ₌ _ n _)) _ (supᵘʳᵣ _ _) =
      Neutralᵃ-supᵘ→ n
    ↑ⁿ-neprop-cong (supᵘʳᵣ _ _) y (supᵘ-zeroʳᵣ _) = case nelevel y of λ ()
    ↑ⁿ-neprop-cong (ne (neNfₜ₌ _ n _)) _ (supᵘ-zeroʳᵣ _) =
      Neutralᵃ-supᵘ→ n
    ↑ⁿ-neprop-cong (supᵘˡᵣ _ _) _ (ne (neNfₜ₌ n _ _)) =
      Neutralᵃ-supᵘ→ n
    ↑ⁿ-neprop-cong (supᵘʳᵣ _ _) _ (ne (neNfₜ₌ n _ _)) =
      Neutralᵃ-supᵘ→ n
    ↑ⁿ-neprop-cong _ (supᵘˡᵣ _ _) (ne (neNfₜ₌ _ n _)) =
      Neutralᵃ-supᵘ→ n
    ↑ⁿ-neprop-cong _ (supᵘʳᵣ _ _) (ne (neNfₜ₌ _ n _)) =
      Neutralᵃ-supᵘ→ n
    ↑ⁿ-neprop-cong (supᵘˡᵣ (supᵘʳᵣ x x₅) x₃) (supᵘˡᵣ y x₄) (supᵘ-assoc¹ᵣ z x₁ x₂) = case nelevel y of λ ()
    ↑ⁿ-neprop-cong
      (supᵘˡᵣ (ne (neNfₜ₌ _ n _)) _) _ (supᵘ-assoc¹ᵣ _ _ _) =
      Neutralᵃ-supᵘ→ n
    ↑ⁿ-neprop-cong (supᵘˡᵣ x x₃) (supᵘʳᵣ x₄ y) (supᵘ-assoc¹ᵣ z x₁ x₂) = case nelevel z of λ ()
    ↑ⁿ-neprop-cong _ (ne (neNfₜ₌ _ n _)) (supᵘ-assoc¹ᵣ _ _ _) =
      Neutralᵃ-supᵘ→ n
    ↑ⁿ-neprop-cong (ne (neNfₜ₌ _ n _)) _ (supᵘ-assoc¹ᵣ _ _ _) =
      Neutralᵃ-supᵘ→ n
    ↑ⁿ-neprop-cong (supᵘˡᵣ (supᵘˡᵣ x x₄) x₃) y (supᵘ-assoc²ᵣ x₁ z x₂) = case nelevel x of λ ()
    ↑ⁿ-neprop-cong (supᵘˡᵣ (supᵘʳᵣ x x₄) x₃) (supᵘˡᵣ y x₅) (supᵘ-assoc²ᵣ x₁ z x₂) = case nelevel y of λ ()
    ↑ⁿ-neprop-cong (supᵘˡᵣ (supᵘʳᵣ x x₄) x₃) (supᵘʳᵣ x₅ (supᵘʳᵣ x₆ y)) (supᵘ-assoc²ᵣ x₁ z x₂) = case nelevel x₄ of λ ()
    ↑ⁿ-neprop-cong
      _ (supᵘʳᵣ _ (ne (neNfₜ₌ _ n _))) (supᵘ-assoc²ᵣ _ _ _) =
      Neutralᵃ-supᵘ→ n
    ↑ⁿ-neprop-cong _ (ne (neNfₜ₌ _ n _)) (supᵘ-assoc²ᵣ _ _ _) =
      Neutralᵃ-supᵘ→ n
    ↑ⁿ-neprop-cong
      (supᵘˡᵣ (ne (neNfₜ₌ _ n _)) _) _ (supᵘ-assoc²ᵣ _ _ _) =
      Neutralᵃ-supᵘ→ n
    ↑ⁿ-neprop-cong (ne (neNfₜ₌ _ n _)) _ (supᵘ-assoc²ᵣ _ _ _) =
      Neutralᵃ-supᵘ→ n
    ↑ⁿ-neprop-cong (supᵘˡᵣ x x₃) y (supᵘ-assoc³ᵣ x₁ x₂ z) = case nelevel x of λ ()
    ↑ⁿ-neprop-cong (supᵘʳᵣ x x₃) (supᵘˡᵣ y x₄) (supᵘ-assoc³ᵣ x₁ x₂ z) = case nelevel y of λ ()
    ↑ⁿ-neprop-cong (supᵘʳᵣ x x₃) (supᵘʳᵣ x₄ (supᵘˡᵣ y x₅)) (supᵘ-assoc³ᵣ x₁ x₂ z) = case nelevel y of λ ()
    ↑ⁿ-neprop-cong
      _ (supᵘʳᵣ _ (ne (neNfₜ₌ _ n _))) (supᵘ-assoc³ᵣ _ _ _) =
      Neutralᵃ-supᵘ→ n
    ↑ⁿ-neprop-cong _ (ne (neNfₜ₌ _ n _)) (supᵘ-assoc³ᵣ _ _ _) =
      Neutralᵃ-supᵘ→ n
    ↑ⁿ-neprop-cong (ne (neNfₜ₌ _ n _)) _ (supᵘ-assoc³ᵣ _ _ _) =
      Neutralᵃ-supᵘ→ n
    ↑ⁿ-neprop-cong (supᵘˡᵣ x x₁) (supᵘʳᵣ x₂ y) (supᵘ-comm¹ᵣ z d w d′) = case nelevel w of λ ()
    ↑ⁿ-neprop-cong _ (ne (neNfₜ₌ _ n _)) (supᵘ-comm¹ᵣ _ _ _ _) =
      Neutralᵃ-supᵘ→ n
    ↑ⁿ-neprop-cong (supᵘʳᵣ x x₁) y (supᵘ-comm¹ᵣ z d w d′) = case nelevel z of λ ()
    ↑ⁿ-neprop-cong (ne (neNfₜ₌ _ n _)) _ (supᵘ-comm¹ᵣ _ _ _ _) =
      Neutralᵃ-supᵘ→ n
    ↑ⁿ-neprop-cong (supᵘˡᵣ x x₁) y (supᵘ-comm²ᵣ z d w) = case nelevel x of λ ()
    ↑ⁿ-neprop-cong (supᵘʳᵣ x x₁) (supᵘʳᵣ x₂ y) (supᵘ-comm²ᵣ z d w) = case nelevel x₁ of λ ()
    ↑ⁿ-neprop-cong _ (ne (neNfₜ₌ _ n _)) (supᵘ-comm²ᵣ _ _ _) =
      Neutralᵃ-supᵘ→ n
    ↑ⁿ-neprop-cong (ne (neNfₜ₌ _ n _)) _ (supᵘ-comm²ᵣ _ _ _) =
      Neutralᵃ-supᵘ→ n
    ↑ⁿ-neprop-cong (supᵘʳᵣ x x₁) y (supᵘ-idemᵣ z w) = case nelevel y of λ ()
    ↑ⁿ-neprop-cong (ne (neNfₜ₌ _ n _)) _ (supᵘ-idemᵣ _ _) =
      Neutralᵃ-supᵘ→ n

opaque
  unfolding ↑ᵘ

  ↑ᵘ-cong :
    {⊩l₁ : Γ ⊩Level l₁ ∷Level} {⊩l₂ : Γ ⊩Level l₂ ∷Level} →
    Γ ⊩Level l₁ ≡ l₂ ∷Level → ↑ᵘ ⊩l₁ PE.≡ ↑ᵘ ⊩l₂
  ↑ᵘ-cong {⊩l₁ = term _ _} {⊩l₂ = term _ _} l₁≡l₂ =
    PE.cong 0ᵘ+ (↑ⁿ-cong _ _ l₁≡l₂)
  ↑ᵘ-cong {⊩l₁ = literal ok _} {⊩l₂ = term ⇒∷Level _} l₁≡l₂
    using okᴸ ← inversion-Level-⊢ (wf-⊢ (subset*Term ⇒∷Level) .proj₁)
    with Allowed-literal→Infinite okᴸ ok
  … | ωᵘ+ with l₁≡l₂
  ... | literal _ _ ()
  ↑ᵘ-cong {⊩l₁ = term ⇒∷Level _} {⊩l₂ = literal ok _} l₁≡l₂
    using okᴸ ← inversion-Level-⊢ (wf-⊢ (subset*Term ⇒∷Level) .proj₁)
    with Allowed-literal→Infinite okᴸ ok
  … | ωᵘ+ with l₁≡l₂
  ... | literal _ _ ()
  ↑ᵘ-cong {⊩l₁ = literal ok _} (term ⇒∷Level _ _) =
    ⇒*∷Level→Allowed-literal→ ⇒∷Level ok
  ↑ᵘ-cong {⊩l₁ = literal _ _} {⊩l₂ = literal _ _} (literal! _ _) =
    Allowed-literal→Universe-level-irrelevance

opaque

  -- Level realisation respects reduction.

  ↑ⁿ-respects-⇒* :
    {⊩t : Γ ⊩Level level t ∷Level} {⊩u : Γ ⊩Level level u ∷Level} →
    Γ ⊢ t ⇒* u ∷ Level →
    ↑ⁿ ok₁ ⊩t PE.≡ ↑ⁿ ok₂ ⊩u
  ↑ⁿ-respects-⇒* {⊩t} t⇒*u =
    ↑ⁿ-cong _ _ (redLevel t⇒*u ⊩t)

opaque

  -- Level realisation respects reduction.

  ↑ᵘ-respects-⇒* :
    {⊩t : Γ ⊩Level level t ∷Level} {⊩u : Γ ⊩Level level u ∷Level} →
    Γ ⊢ t ⇒* u ∷ Level →
    ↑ᵘ ⊩t PE.≡ ↑ᵘ ⊩u
  ↑ᵘ-respects-⇒* {⊩t} t⇒*u =
    ↑ᵘ-cong (redLevel t⇒*u ⊩t)

opaque

  -- Level realisation preserves inequality.

  ↑ⁿ-cong-≤ :
    {⊩t : Γ ⊩Level level t ∷Level} {⊩u : Γ ⊩Level level u ∷Level} →
    Γ ⊩Level level (t supᵘ u) ≡ level u ∷Level →
    ↑ⁿ ok₁ ⊩t ≤ ↑ⁿ ok₂ ⊩u
  ↑ⁿ-cong-≤ {ok₁} {⊩t} {⊩u} t≤u =
    m⊔n≡n⇒m≤n
      (PE.trans (PE.sym (↑ⁿ-supᵘ′ {ok₁ = ok₁} ⊩t ⊩u _))
        (↑ⁿ-cong (⊩supᵘ ok₁ ⊩t ⊩u) ⊩u t≤u))

opaque
  unfolding ↑ᵘ

  ↑ᵘ-cong-≤ :
    {⊩t : Γ ⊩Level level t ∷Level} {⊩u : Γ ⊩Level level u ∷Level} →
    Γ ⊩Level level (t supᵘ u) ≡ level u ∷Level →
    ↑ᵘ ⊩t ≤ᵘ ↑ᵘ ⊩u
  ↑ᵘ-cong-≤ {⊩t = term _ _} {⊩u = term _ _} t≤u =
    0ᵘ+≤ᵘ0ᵘ+ (≤⇒≤′ (↑ⁿ-cong-≤ t≤u))
  ↑ᵘ-cong-≤ {⊩t = literal ok _} (term ⇒∷Level _ _) =
    ⇒*∷Level→Allowed-literal→ ⇒∷Level ok
  ↑ᵘ-cong-≤ {⊩u = literal ok _} (term ⇒∷Level _ _) =
    ⇒*∷Level→Allowed-literal→ ⇒∷Level ok
  ↑ᵘ-cong-≤ (literal ok _ _) =
    case Allowed-literal→Level-literal ok of λ { (level ()) }

opaque
  unfolding ↑ⁿ

  -- Any function of a certain type that satisfies a certain
  -- specification is pointwise equal to ↑ⁿ okᴸ.

  ↑ⁿ-unique :
    (f : ∀ {m n} {Γ : Cons m n} {t} → Γ ⊩Level level t ∷Level → Nat) →
    (∀ {m n} {Γ : Cons m n} {t u}
       {⊩t : Γ ⊩Level level t ∷Level} {⊩u : Γ ⊩Level level u ∷Level} →
     Γ ⊢ t ⇒* u ∷ Level → f ⊩t PE.≡ f ⊩u) →
    (∀ {m n} {Γ : Cons m n} {⊩0 : Γ ⊩Level zeroᵘₗ ∷Level} →
     f ⊩0 PE.≡ 0) →
    (∀ {m n} {Γ : Cons m n} {t}
     {⊩t : Γ ⊩Level level t ∷Level}
     {⊩1+t : Γ ⊩Level level (sucᵘ t) ∷Level} →
     f ⊩1+t PE.≡ 1+ (f ⊩t)) →
    (∀ {m n} {Γ : Cons m n} {t u}
     {⊩t : Γ ⊩Level level t ∷Level} {⊩u : Γ ⊩Level level u ∷Level}
     {⊩t⊔u : Γ ⊩Level level (t supᵘ u) ∷Level} →
     f ⊩t⊔u PE.≡ f ⊩t ⊔ f ⊩u) →
    (∀ {V} {m n} {Γ : Cons m n} {t} {⊩t : Γ ⊩Level level t ∷Level} →
     Neutralᵃ V (Γ .defs) t → f ⊩t PE.≡ ↑ᵘ-neutral) →
    {⊩t : Γ ⊩Level level t ∷Level} →
    f ⊩t PE.≡ ↑ⁿ okᴸ ⊩t
  ↑ⁿ-unique {Γ} f f-⇒* f-0 f-1+ f-⊔ f-ne {⊩t} = f≡ _
    where
    f-irrelevance :
      {⊩t ⊩u : Γ ⊩Level level t ∷Level} →
      Level-allowed →
      f ⊩t PE.≡ f ⊩u
    f-irrelevance {⊩t} ok =
      f-⇒* (id (⊢∷Level→⊢∷Level ok (escapeLevel ⊩t)))

    f′ : Level-prop Γ t → Nat
    f′ = f ∘→ ⊩Lvl (wf (escapeLevel ⊩t))

    f″ : neLevel-prop Γ t → Nat
    f″ = f ∘→ ⊩neLvl

    mutual

      f≡ : (⊩t : Γ ⊩Level level t ∷Level) → f ⊩t PE.≡ ↑ⁿ okᴸ ⊩t
      f≡ {okᴸ} (literal ok _) =
        Level-allowed→Allowed-literal→ okᴸ ok
      f≡ {okᴸ} ⊩t@(term t⇒u ⊩u) =
        f ⊩t            ≡⟨ f-⇒* t⇒u ⟩
        f′ ⊩u           ≡⟨ f′≡ _ ⟩
        ↑ⁿ-prop okᴸ ⊩u  ≡⟨⟩
        ↑ⁿ okᴸ ⊩t       ∎

      f′≡ : (⊩t : Level-prop Γ t) → f′ ⊩t PE.≡ ↑ⁿ-prop okᴸ ⊩t
      f′≡ {okᴸ} ⊩t@(zeroᵘᵣ _) =
        f′ ⊩t           ≡⟨ f-0 ⟩
        0               ≡⟨⟩
        ↑ⁿ-prop okᴸ ⊩t  ∎
      f′≡ {okᴸ} ⊩t@(sucᵘᵣ _ ⊩t′) =
        f′ ⊩t            ≡⟨ f-1+ ⟩
        1+ (f ⊩t′)       ≡⟨ PE.cong 1+ (f≡ _) ⟩
        1+ (↑ⁿ okᴸ ⊩t′)  ≡⟨⟩
        ↑ⁿ-prop okᴸ ⊩t   ∎
      f′≡ {okᴸ} ⊩t@(neLvl ⊩t′) =
        f′ ⊩t              ≡⟨ f-irrelevance (inversion-Level-⊢ (wf-⊢ (escape-neLevel-prop ⊩t′))) ⟩
        f″ ⊩t′             ≡⟨ f″≡ _ ⟩
        ↑ⁿ-neprop okᴸ ⊩t′  ≡⟨⟩
        ↑ⁿ-prop okᴸ ⊩t     ∎

      f″≡ : (⊩t : neLevel-prop Γ t) → f″ ⊩t PE.≡ ↑ⁿ-neprop okᴸ ⊩t
      f″≡ {okᴸ} ⊩t@(supᵘˡᵣ ⊩t₁ ⊩t₂) =
        f″ ⊩t                           ≡⟨ f-⊔ ⟩
        f″ ⊩t₁ ⊔ f ⊩t₂                  ≡⟨ PE.cong₂ _⊔_ (f″≡ _) (f≡ _) ⟩
        ↑ⁿ-neprop okᴸ ⊩t₁ ⊔ ↑ⁿ okᴸ ⊩t₂  ≡⟨⟩
        ↑ⁿ-neprop okᴸ ⊩t                ∎
      f″≡ {okᴸ} ⊩t@(supᵘʳᵣ ⊩t₁ ⊩t₂) =
        f″ ⊩t                                ≡⟨ f-⊔ ⟩
        f (⊩1ᵘ+ ⊩t₁) ⊔ f″ ⊩t₂                ≡⟨ PE.cong (flip _⊔_ _) f-1+ ⟩
        1+ (f ⊩t₁) ⊔ f″ ⊩t₂                  ≡⟨ PE.cong₂ _⊔_ (PE.cong 1+ (f≡ _)) (f″≡ _) ⟩
        1+ (↑ⁿ okᴸ ⊩t₁) ⊔ ↑ⁿ-neprop okᴸ ⊩t₂  ≡⟨⟩
        ↑ⁿ-neprop okᴸ ⊩t                     ∎
      f″≡ {okᴸ} ⊩t@(ne (neNfₜ₌ t-ne _ _)) =
        f″ ⊩t             ≡⟨ f-ne t-ne ⟩
        ↑ᵘ-neutral        ≡⟨⟩
        ↑ⁿ-neprop okᴸ ⊩t  ∎
