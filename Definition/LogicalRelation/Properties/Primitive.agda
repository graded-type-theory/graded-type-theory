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
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
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

private
  variable
    n : Nat
    A B t t₁ t₂ t₁′ t₂′ u u₁ u₂ v : Term _
    Γ : Con Term n
    l : Universe-level

mutual

  -- Reflexivity of level equality.

  reflLevel : Γ ⊩Level t ∷Level → Γ ⊩Level t ≡ t ∷Level
  reflLevel (term l⇒l′ l′-prop) =
    term l⇒l′ l⇒l′ (reflLevel-prop l′-prop)
  reflLevel (literal not-ok ⊢Γ l-lit) =
    literal! not-ok ⊢Γ l-lit

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
transEqTermNe (neNfₜ₌ inc neK neM k≡m) (neNfₜ₌ _ neK₁ neM₁ k≡m₁) =
  neNfₜ₌ inc neK neM₁ (~-trans k≡m k≡m₁)

transEqTermLevel : ∀ {n n′ n″}
                 → Γ ⊩Level n  ≡ n′ ∷Level
                 → Γ ⊩Level n′ ≡ n″ ∷Level
                 → Γ ⊩Level n  ≡ n″ ∷Level
transEqTermLevel
  (term l₁⇒l₁′ l₂⇒l₂′ l₁′≡l₂′) (term l₂⇒l₂″ l₃⇒l₃′ l₂″≡l₃′)
  with whrDet*Term (l₂⇒l₂′ , lsplit l₁′≡l₂′ .proj₂)
         (l₂⇒l₂″ , lsplit l₂″≡l₃′ .proj₁)
… | PE.refl = term l₁⇒l₁′ l₃⇒l₃′ (trans l₁′≡l₂′ l₂″≡l₃′)
transEqTermLevel (term ⇒∷Level _ _) (literal! not-ok _ _) =
  ⊥-elim $ not-ok $
  inversion-Level-⊢ (wf-⊢≡∷ (subset*Term ⇒∷Level) .proj₁)
transEqTermLevel (literal! not-ok _ _) (term ⇒∷Level _ _) =
  ⊥-elim $ not-ok $
  inversion-Level-⊢ (wf-⊢≡∷ (subset*Term ⇒∷Level) .proj₁)
transEqTermLevel (literal! not-ok ⊢Γ l-lit) (literal! _ _ _) =
  literal! not-ok ⊢Γ l-lit

-- Symmetry for neutrals in WHNF and levels

symNeutralTerm : ∀ {t u A}
               → Γ ⊩neNf t ≡ u ∷ A
               → Γ ⊩neNf u ≡ t ∷ A
symNeutralTerm (neNfₜ₌ inc neK neM k≡m) = neNfₜ₌ inc neM neK (~-sym k≡m)

symLevel : ∀ {k k′}
         → Γ ⊩Level k ≡ k′ ∷Level
         → Γ ⊩Level k′ ≡ k ∷Level
symLevel (term l₁⇒l₁′ l₂⇒l₂′ l₁′≡l₂′) =
  term l₂⇒l₂′ l₁⇒l₁′ (sym l₁′≡l₂′)
symLevel (literal! not-ok ⊢Γ l-lit) =
  literal! not-ok ⊢Γ l-lit

-- Some reduction and expansion lemmas

redLevel
  : ∀ {t t′}
  → Γ ⊢ t ⇒* t′ ∷ Level
  → Γ ⊩Level t ∷Level
  → Γ ⊩Level t ≡ t′ ∷Level
redLevel l₁⇒l₂ (term l₁⇒l₃ l₃-prop) =
  term l₁⇒l₃ (whrDet↘Term (l₁⇒l₃ , level l₃-prop) l₁⇒l₂)
    (reflLevel-prop l₃-prop)
redLevel l₁⇒ (literal not-ok _ _) =
  ⊥-elim $ not-ok (inversion-Level-⊢ (wf-⊢≡∷ (subset*Term l₁⇒) .proj₁))

redLevel′
  : ∀ {t t′}
  → Γ ⊢ t ⇒* t′ ∷ Level
  → Γ ⊩Level t′ ∷Level
  → Γ ⊩Level t ≡ t′ ∷Level
redLevel′ l₁⇒l₂ (term l₂⇒l₃ l₃-prop) =
  term (l₁⇒l₂ ⇨∷* l₂⇒l₃) l₂⇒l₃ (reflLevel-prop l₃-prop)
redLevel′ l₁⇒ (literal not-ok _ _) =
  ⊥-elim $ not-ok (inversion-Level-⊢ (wf-⊢≡∷ (subset*Term l₁⇒) .proj₁))

⊩Level-⇒*
  : ∀ {t t′}
  → Γ ⊢ t′ ⇒* t ∷ Level
  → Γ ⊩Level t ∷Level
  → Γ ⊩Level t′ ∷Level
⊩Level-⇒* l₁⇒l₂ (term l₂⇒l₃ l₃-prop) =
  term (l₁⇒l₂ ⇨∷* l₂⇒l₃) l₃-prop
⊩Level-⇒* l₁⇒ (literal not-ok _ _) =
  ⊥-elim $ not-ok (inversion-Level-⊢ (wf-⊢≡∷ (subset*Term l₁⇒) .proj₁))

⊩Level≡-⇒*
  : ∀ {t t′ u u′}
  → Γ ⊢ t′ ⇒* t ∷ Level
  → Γ ⊢ u′ ⇒* u ∷ Level
  → Γ ⊩Level t ≡ u ∷Level
  → Γ ⊩Level t′ ≡ u′ ∷Level
⊩Level≡-⇒* l₁⇒l₁′ l₂⇒l₂′ (term l₁′⇒l₁″ l₂′⇒l₂″ l₁″≡l₂″) =
  term (l₁⇒l₁′ ⇨∷* l₁′⇒l₁″) (l₂⇒l₂′ ⇨∷* l₂′⇒l₂″) l₁″≡l₂″
⊩Level≡-⇒* l₁⇒ _ (literal! not-ok _ _) =
  ⊥-elim $ not-ok (inversion-Level-⊢ (wf-⊢≡∷ (subset*Term l₁⇒) .proj₁))

------------------------------------------------------------------------
-- Escape lemmas

opaque

  escape-neNf
    : Γ ⊩neNf t ≡ t ∷ A
    → Γ ⊢ t ∷ A
  escape-neNf (neNfₜ₌ _ neK neM k≡m) =
    wf-⊢≡∷ (≅ₜ-eq (~-to-≅ₜ k≡m)) .proj₂ .proj₁

opaque mutual

  -- Reducible levels are well-formed.

  escapeLevel
    : Γ ⊩Level t ∷Level
    → Γ ⊢ t ∷Level
  escapeLevel (term l⇒l′ _)             = term-⊢∷ (redFirst*Term l⇒l′)
  escapeLevel (literal not-ok ⊢Γ l-lit) = literal not-ok ⊢Γ l-lit

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
        ok  = inversion-Level-⊢ (wf-⊢∷ ⊢t₁)
    in
    supᵘⱼ ⊢t₁ (⊢∷Level→⊢∷Level ok (escapeLevel ⊩t₂))
  escape-neLevel-prop (supᵘʳᵣ ⊩t₁ ⊩t₂) =
    let ⊢t₂ = escape-neLevel-prop ⊩t₂
        ok  = inversion-Level-⊢ (wf-⊢∷ ⊢t₂)
    in
    supᵘⱼ (sucᵘⱼ (⊢∷Level→⊢∷Level ok (escapeLevel ⊩t₁))) ⊢t₂
  escape-neLevel-prop (ne x) = escape-neNf x

opaque mutual

  -- If Level is allowed, then reducible levels are related to
  -- themselves.

  escapeLevel′ :
    Level-allowed →
    Γ ⊩Level t ∷Level →
    Γ ⊢≅ t ∷ Level
  escapeLevel′ ok (term t⇒t′ t′-prop) =
    let t↘t′ = t⇒t′ , level t′-prop
        ⊢Γ   = wfTerm (redFirst*Term t⇒t′)
    in
    ≅ₜ-red (id (Levelⱼ′ ok ⊢Γ) , Levelₙ) t↘t′ t↘t′
      (escape-Level-prop′ ⊢Γ t′-prop)
  escapeLevel′ ok (literal not-ok _ _) =
    ⊥-elim (not-ok ok)

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
        ok  = inversion-Level-⊢ (wf-⊢≡∷ (≅ₜ-eq ⊢t₁) .proj₁)
    in
    ≅ₜ-supᵘ-cong ⊢t₁ (escapeLevel′ ok ⊩t₂)
  escape-neLevel-prop′ (supᵘʳᵣ ⊩t₁ ⊩t₂) =
    let ⊢t₂ = escape-neLevel-prop′ ⊩t₂
        ok  = inversion-Level-⊢ (wf-⊢≡∷ (≅ₜ-eq ⊢t₂) .proj₁)
    in
    ≅ₜ-supᵘ-cong (≅ₜ-sucᵘ-cong (escapeLevel′ ok ⊩t₁)) ⊢t₂
  escape-neLevel-prop′ (ne (neNfₜ₌ _ _ _ k≡m)) =
    ~-to-≅ₜ k≡m

opaque mutual

  -- If Level is allowed, then reducible level equalities are
  -- well-formed.

  escapeLevelEq :
    Γ ⊩Level t ≡ u ∷Level →
    Γ ⊢ t ≅ u ∷Level
  escapeLevelEq (term t⇒t′ u⇒u′ t′≡u′) =
    let t′-whnf , u′-whnf = lsplit t′≡u′
        ⊢t                = redFirst*Term t⇒t′
        ⊢Γ                = wfTerm ⊢t
        ok                = inversion-Level-⊢ (wf-⊢∷ ⊢t)
    in
    ⊢≅∷→⊢≅∷L $
    ≅ₜ-red (id (Levelⱼ′ ok ⊢Γ) , Levelₙ) (t⇒t′ , t′-whnf)
      (u⇒u′ , u′-whnf) (escape-[Level]-prop ⊢Γ t′≡u′)
  escapeLevelEq (literal! not-ok ⊢Γ t-lit) =
    Level-literal→⊢≅∷L not-ok ⊢Γ t-lit

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
        ok = inversion-Level-⊢ (wf-⊢≡∷ (≅ₜ-eq ⊢t) .proj₁)
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
        ok = inversion-Level-⊢ (wf-⊢≡∷ (≅ₜ-eq ⊢t) .proj₁)
    in
    ≅ₜ-supᵘ-cong ⊢t (⊢≅∷L→⊢≅∷ ok $ escapeLevelEq ⊩u)
  escape-[neLevel]-prop (supᵘʳᵣ ⊩t ⊩u) =
    let ⊢u = escape-[neLevel]-prop ⊩u
        ok = inversion-Level-⊢ (wf-⊢≡∷ (≅ₜ-eq ⊢u) .proj₁)
    in
    ≅ₜ-supᵘ-cong (≅ₜ-sucᵘ-cong (⊢≅∷L→⊢≅∷ ok $ escapeLevelEq ⊩t)) ⊢u
  escape-[neLevel]-prop (supᵘ-zeroʳᵣ x) =
    let ⊢t = escape-neLevel-prop′ x
    in ≅ₜ-supᵘ-zeroʳ ⊢t
  escape-[neLevel]-prop (supᵘ-assoc¹ᵣ ⊩t ⊩u ⊩v) =
    let ⊢t = escape-neLevel-prop′ ⊩t
        ok = inversion-Level-⊢ (wf-⊢≡∷ (≅ₜ-eq ⊢t) .proj₁)
    in
    ≅ₜ-supᵘ-assoc ⊢t (escapeLevel′ ok ⊩u) (escapeLevel′ ok ⊩v)
  escape-[neLevel]-prop (supᵘ-assoc²ᵣ ⊩t ⊩u ⊩v) =
    let ⊢u = escape-neLevel-prop′ ⊩u
        ok = inversion-Level-⊢ (wf-⊢≡∷ (≅ₜ-eq ⊢u) .proj₁)
    in
    ≅ₜ-supᵘ-assoc (≅ₜ-sucᵘ-cong (escapeLevel′ ok ⊩t)) ⊢u
      (escapeLevel′ ok ⊩v)
  escape-[neLevel]-prop (supᵘ-assoc³ᵣ ⊩t ⊩u ⊩v) =
    let ⊢v = escape-neLevel-prop′ ⊩v
        ok = inversion-Level-⊢ (wf-⊢≡∷ (≅ₜ-eq ⊢v) .proj₁)
        ⊢t = escapeLevel′ ok ⊩t
        ⊢u = escapeLevel′ ok ⊩u
    in
    ≅ₜ-trans
      (≅ₜ-supᵘ-cong (≅ₜ-sym (≅ₜ-supᵘ-sucᵘ ⊢t ⊢u)) ⊢v)
      (≅ₜ-supᵘ-assoc (≅ₜ-sucᵘ-cong ⊢t) (≅ₜ-sucᵘ-cong ⊢u) ⊢v)
  escape-[neLevel]-prop (supᵘ-comm¹ᵣ ⊩t₁ t₁≡u₁ ⊩u₂ t₂≡u₂) =
    let ⊢t₁   = escape-neLevel-prop′ ⊩t₁
        ok    = inversion-Level-⊢ (wf-⊢≡∷ (≅ₜ-eq ⊢t₁) .proj₁)
        t₁≡u₁ = ⊢≅∷L→⊢≅∷ ok $ escapeLevelEq t₁≡u₁
        t₂≡u₂ = ⊢≅∷L→⊢≅∷ ok $ escapeLevelEq t₂≡u₂
        ⊢t₂ , _ = wf-⊢≅∷ t₂≡u₂
    in
    ≅ₜ-trans (≅ₜ-supᵘ-comm ⊢t₁ ⊢t₂) (≅ₜ-supᵘ-cong t₂≡u₂ t₁≡u₁)
  escape-[neLevel]-prop (supᵘ-comm²ᵣ ⊩t₁ 1+t₁≡u₂ ⊩t₂) =
    let ⊢t₂     = escape-neLevel-prop′ ⊩t₂
        ok      = inversion-Level-⊢ (wf-⊢≡∷ (≅ₜ-eq ⊢t₂) .proj₁)
        1+t₁≡u₂ = ⊢≅∷L→⊢≅∷ ok $ escapeLevelEq 1+t₁≡u₂
        _ , ⊢u₂ = wf-⊢≅∷ 1+t₁≡u₂
    in
    ≅ₜ-trans (≅ₜ-supᵘ-cong 1+t₁≡u₂ ⊢t₂) (≅ₜ-supᵘ-comm ⊢u₂ ⊢t₂)
  escape-[neLevel]-prop (supᵘ-idemᵣ ⊩t₁ t₁≡t₂) =
    let t₁≡t₁ = escape-neLevel-prop′ ⊩t₁
        ok    = inversion-Level-⊢ (wf-⊢≡∷ (≅ₜ-eq t₁≡t₁) .proj₁)
        t₁≡t₂ = ⊢≅∷L→⊢≅∷ ok $ escapeLevelEq t₁≡t₂
    in
    ≅ₜ-trans (≅ₜ-supᵘ-cong t₁≡t₁ (≅ₜ-sym t₁≡t₂)) (≅ₜ-supᵘ-idem t₁≡t₁)
  escape-[neLevel]-prop (ne (neNfₜ₌ _ _ _ k≡m)) =
    ~-to-≅ₜ k≡m

------------------------------------------------------------------------
-- Some introduction lemmas for _⊩Level_∷Level and _⊩Level_≡_∷Level.

⊩Lvl : ⊢ Γ → Level-prop Γ t → Γ ⊩Level t ∷Level
⊩Lvl ⊢Γ ⊩t = term (id (escape-Level-prop ⊢Γ ⊩t)) ⊩t

⊩neLvl : neLevel-prop Γ t → Γ ⊩Level t ∷Level
⊩neLvl ⊩t = term (id (escape-neLevel-prop ⊩t)) (neLvl ⊩t)

⊩[Lvl] : ⊢ Γ → [Level]-prop Γ t u → Γ ⊩Level t ≡ u ∷Level
⊩[Lvl] ⊢Γ t≡u =
  let _ , ⊢t , ⊢u = wf-⊢≡∷ (≅ₜ-eq (escape-[Level]-prop ⊢Γ t≡u)) in
  term (id ⊢t) (id ⊢u) t≡u

⊩[neLvl] : [neLevel]-prop Γ t u → Γ ⊩Level t ≡ u ∷Level
⊩[neLvl] t≡u =
  let _ , ⊢t , ⊢u = wf-⊢≡∷ (≅ₜ-eq (escape-[neLevel]-prop t≡u)) in
  term (id ⊢t) (id ⊢u) (neLvl t≡u)

opaque

  -- An introduction lemma for zeroᵘ.

  ⊩zeroᵘ : ⊢ Γ → Γ ⊩Level zeroᵘ ∷Level
  ⊩zeroᵘ ⊢Γ with Level-allowed?
  … | yes ok    = ⊩Lvl ⊢Γ (zeroᵘᵣ ok)
  … | no not-ok = literal not-ok ⊢Γ zeroᵘ

opaque

  -- Introduction lemmas for sucᵘ.

  ⊩sucᵘ : Γ ⊩Level t ∷Level → Γ ⊩Level sucᵘ t ∷Level
  ⊩sucᵘ ⊩t@(term t⇒*t′ _) =
    let ⊢t = redFirst*Term t⇒*t′
        ok = inversion-Level-⊢ (wf-⊢∷ ⊢t)
    in
    term
      (id (sucᵘⱼ (redFirst*Term t⇒*t′)))
      (sucᵘᵣ ok ⊩t)
  ⊩sucᵘ (literal not-ok ⊢Γ t-lit) =
    literal not-ok ⊢Γ (sucᵘ t-lit)

  ⊩sucᵘ≡sucᵘ : Γ ⊩Level t ≡ u ∷Level → Γ ⊩Level sucᵘ t ≡ sucᵘ u ∷Level
  ⊩sucᵘ≡sucᵘ t≡u@(term t⇒*t′ u⇒*u′ t′≡u′) =
    let ⊢t = redFirst*Term t⇒*t′
        ok = inversion-Level-⊢ (wf-⊢∷ ⊢t)
    in
    term
      (id (sucᵘⱼ ⊢t))
      (id (sucᵘⱼ (redFirst*Term u⇒*u′)))
      (sucᵘᵣ ok t≡u)
  ⊩sucᵘ≡sucᵘ (literal! not-ok ⊢Γ t-lit) =
    literal! not-ok ⊢Γ (sucᵘ t-lit)

opaque mutual

  -- An introduction lemma for supᵘ.

  ⊩supᵘ :
    Level-allowed →
    Γ ⊩Level t ∷Level →
    Γ ⊩Level u ∷Level →
    Γ ⊩Level t supᵘ u ∷Level
  ⊩supᵘ {u} ok (term {l′ = t′} t⇒ propt) ⊩u =
    case ⊩u of λ where
      (literal not-ok _ _)      → ⊥-elim (not-ok ok)
      (term {l′ = u′} u⇒ propu) →
        let ⊢u  = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩u)
            ⊢Γ  = wfTerm ⊢u
            ⊢t′ = escape-Level-prop ⊢Γ propt
            ⊢u′ = escape-Level-prop ⊢Γ propu
        in
        ⊩Level-⇒* (supᵘ-substˡ* t⇒ ⊢u) $
        case propt of λ where
          (zeroᵘᵣ _) →
            term
              (zeroᵘ supᵘ u  ⇒⟨ supᵘ-zeroˡ ⊢u ⟩
               u             ⇒*⟨ u⇒ ⟩∎
               u′            ∎)
              propu
          (sucᵘᵣ {k = t′} _ ⊩t′) →
            let ⊢t′ = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩t′) in
            ⊩Level-⇒* (supᵘ-substʳ* ⊢t′ u⇒) $
            case propu of λ where
              (zeroᵘᵣ _) → term
                (sucᵘ t′ supᵘ zeroᵘ ⇒⟨ supᵘ-zeroʳ ⊢t′ ⟩∎
                 sucᵘ t′            ∎)
                (sucᵘᵣ ok ⊩t′)
              (sucᵘᵣ {k = u′} _ ⊩u′) →
                let ⊢u′ = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩u′) in
                term
                  (sucᵘ t′ supᵘ sucᵘ u′ ⇒⟨ supᵘ-sucᵘ ⊢t′ ⊢u′ ⟩∎
                   sucᵘ (t′ supᵘ u′)    ∎)
                  (sucᵘᵣ ok (⊩supᵘ ok ⊩t′ ⊩u′))
              (neLvl ⊩u′) →
                term
                  (id (supᵘⱼ (sucᵘⱼ ⊢t′) ⊢u′))
                  (neLvl (supᵘʳᵣ ⊩t′ ⊩u′))
          (neLvl ⊩t′) →
            term
              (id (supᵘⱼ ⊢t′ ⊢u))
              (neLvl (supᵘˡᵣ ⊩t′ ⊩u))
  ⊩supᵘ ok (literal not-ok _ _) _ =
    ⊥-elim (not-ok ok)

opaque

  -- An introduction lemma for _supᵘₗ_.

  ⊩supᵘₗ :
    Γ ⊩Level t ∷Level →
    Γ ⊩Level u ∷Level →
    Γ ⊩Level t supᵘₗ u ∷Level
  ⊩supᵘₗ ⊩t@(term ⇒∷Level _) ⊩u =
    let ok = inversion-Level-⊢ (wf-⊢≡∷ (subset*Term ⇒∷Level) .proj₁) in
    PE.subst (_⊩Level_∷Level _) (PE.sym $ supᵘₗ≡supᵘ ok) $
    ⊩supᵘ ok ⊩t ⊩u
  ⊩supᵘₗ (literal not-ok ⊢Γ t-lit) (literal _ _ u-lit) =
    literal not-ok ⊢Γ $
    Level-literal-supᵘₗ⇔ not-ok .proj₂ (t-lit , u-lit)
  ⊩supᵘₗ (literal not-ok _ _) (term ⇒∷Level _) =
    ⊥-elim $ not-ok $
    inversion-Level-⊢ (wf-⊢≡∷ (subset*Term ⇒∷Level) .proj₁)

opaque

  -- Associativity for supᵘ.

  ⊩supᵘ-assoc :
    Level-allowed →
    Γ ⊩Level t ∷Level →
    Γ ⊩Level u ∷Level →
    Γ ⊩Level v ∷Level →
    Γ ⊩Level (t supᵘ u) supᵘ v ≡ t supᵘ (u supᵘ v) ∷Level
  ⊩supᵘ-assoc
    ok ⊩t@(term t⇒ propt) ⊩u@(term u⇒ propu) ⊩v@(term v⇒ propv) =
    let
      ⊢u  = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩u)
      ⊢v  = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩v)
      ⊢Γ  = wfTerm ⊢u
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
                  (reflLevel (⊩supᵘ ok (⊩sucᵘ ⊩t″) ⊩v))
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
                        (reflLevel (⊩sucᵘ (⊩supᵘ ok ⊩t″ ⊩u″)))
                    (sucᵘᵣ _ ⊩v″) →
                      let ⊢v″ = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩v″) in
                      ⊩Level≡-⇒*
                        (redMany (supᵘ-sucᵘ (supᵘⱼ ⊢t″ ⊢u″) ⊢v″))
                        (supᵘ-substʳ ⊢t″ (supᵘ-sucᵘ ⊢u″ ⊢v″) ⇨
                         redMany (supᵘ-sucᵘ ⊢t″ (supᵘⱼ ⊢u″ ⊢v″)))
                        (⊩sucᵘ≡sucᵘ (⊩supᵘ-assoc ok ⊩t″ ⊩u″ ⊩v″))
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
  ⊩supᵘ-assoc ok (literal not-ok _ _) _ _ = ⊥-elim (not-ok ok)
  ⊩supᵘ-assoc ok _ (literal not-ok _ _) _ = ⊥-elim (not-ok ok)
  ⊩supᵘ-assoc ok _ _ (literal not-ok _ _) = ⊥-elim (not-ok ok)

opaque

  -- Right identity for supᵘ.

  ⊩supᵘ-zeroʳ′ :
    Γ ⊩Level t ∷Level →
    Γ ⊢ u ⇒* zeroᵘ ∷ Level →
    Γ ⊩Level t supᵘ u ≡ t ∷Level
  ⊩supᵘ-zeroʳ′ (literal not-ok _ _) ⇒∷Level =
    ⊥-elim $ not-ok $
    inversion-Level-⊢ (wf-⊢≡∷ (subset*Term ⇒∷Level) .proj₁)
  ⊩supᵘ-zeroʳ′ ⊩t@(term t⇒ prop) u⇒ =
    let ⊢u = redFirst*Term u⇒
        ⊢Γ = wfTerm ⊢u
    in
    ⊩Level≡-⇒* (supᵘ-substˡ* t⇒ ⊢u) t⇒ $
    case prop of λ where
      (zeroᵘᵣ _) → redLevel′ (supᵘ-zeroˡ ⊢u ⇨ u⇒) (⊩zeroᵘ ⊢Γ)
      (sucᵘᵣ ok ⊩k) →
        let ⊢k = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩k) in
        redLevel′ (supᵘ-substʳ* ⊢k u⇒ ⇨∷* redMany (supᵘ-zeroʳ ⊢k))
          (⊩sucᵘ ⊩k)
      (neLvl ⊩k) →
        transEqTermLevel
          (⊩[neLvl] $
           supᵘˡᵣ (reflneLevel-prop ⊩k) (redLevel′ u⇒ (⊩zeroᵘ ⊢Γ)))
          (⊩[neLvl] (supᵘ-zeroʳᵣ ⊩k))

  ⊩supᵘ-zeroʳ :
    Level-allowed →
    Γ ⊩Level t ∷Level →
    Γ ⊩Level t supᵘ zeroᵘ ≡ t ∷Level
  ⊩supᵘ-zeroʳ ok ⊩t =
    ⊩supᵘ-zeroʳ′ ⊩t $
    id (zeroᵘⱼ ok (wfTerm (⊢∷Level→⊢∷Level ok (escapeLevel ⊩t))))

opaque

  -- Commutativity for supᵘ.

  ⊩supᵘ-comm :
    Level-allowed →
    Γ ⊩Level t ∷Level →
    Γ ⊩Level u ∷Level →
    Γ ⊩Level t supᵘ u ≡ u supᵘ t ∷Level
  ⊩supᵘ-comm ok ⊩t@(term t⇒ propt) ⊩u@(term u⇒ propu) =
    let ⊢t  = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩t)
        ⊢u  = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩u)
        ⊢Γ  = wfTerm ⊢u
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
              (reflLevel (⊩sucᵘ ⊩t′))
          (sucᵘᵣ _ ⊩u′) →
            let ⊢u′ = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩u′) in
            ⊩Level≡-⇒*
              (redMany (supᵘ-sucᵘ ⊢t′ ⊢u′))
              (supᵘ-substʳ* ⊢u′ t⇒ ⇨∷* redMany (supᵘ-sucᵘ ⊢u′ ⊢t′))
              (⊩sucᵘ≡sucᵘ (⊩supᵘ-comm ok ⊩t′ ⊩u′))
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
  ⊩supᵘ-comm ok (literal not-ok _ _) _ = ⊥-elim (not-ok ok)
  ⊩supᵘ-comm ok _ (literal not-ok _ _) = ⊥-elim (not-ok ok)

opaque

  -- Idempotence for supᵘ.

  ⊩supᵘ-idem :
    Level-allowed →
    Γ ⊩Level t ∷Level →
    Γ ⊩Level t supᵘ t ≡ t ∷Level
  ⊩supᵘ-idem ok ⊩t@(term t⇒ propt) =
    let ⊢t = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩t)
        ⊢Γ = wfTerm ⊢t
        ⊢t′ = escape-Level-prop ⊢Γ propt
    in
    ⊩Level≡-⇒* (supᵘ-substˡ* t⇒ ⊢t) t⇒ $
    case propt of λ where
      (zeroᵘᵣ _) →
        redLevel′ (supᵘ-zeroˡ ⊢t ⇨ t⇒) (⊩zeroᵘ ⊢Γ)
      (sucᵘᵣ _ ⊩t′) →
        let ⊢t′ = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩t′) in
        ⊩Level≡-⇒*
          (supᵘ-substʳ* ⊢t′ t⇒ ⇨∷* redMany (supᵘ-sucᵘ ⊢t′ ⊢t′))
          (id (sucᵘⱼ ⊢t′))
          (⊩sucᵘ≡sucᵘ (⊩supᵘ-idem ok ⊩t′))
      (neLvl ⊩t′) →
        term
          (id (supᵘⱼ ⊢t′ ⊢t))
          (id ⊢t′)
          ([Level]-prop.neLvl $
           supᵘ-idemᵣ ⊩t′ (symLevel (redLevel′ t⇒ (⊩neLvl ⊩t′))))
  ⊩supᵘ-idem ok (literal not-ok _ _) = ⊥-elim (not-ok ok)

opaque

  -- Subsumption for supᵘ.

  ⊩supᵘ-sub′ :
    Γ ⊢ u ⇒* sucᵘ t ∷ Level →
    Γ ⊩Level t ∷Level →
    Γ ⊩Level t supᵘ u ≡ u ∷Level
  ⊩supᵘ-sub′ u⇒ ⊩t@(term t⇒ propt) =
    let ⊢u  = redFirst*Term u⇒
        ok  = inversion-Level-⊢ (wf-⊢∷ ⊢u)
        ⊢t  = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩t)
        ⊢Γ  = wfTerm ⊢t
        ⊢t′ = escape-Level-prop ⊢Γ propt
    in
    ⊩Level≡-⇒* (supᵘ-substˡ* t⇒ ⊢u) (id ⊢u) $
    case propt of λ where
      (zeroᵘᵣ _) →
        redLevel′ (redMany (supᵘ-zeroˡ ⊢u)) (⊩Level-⇒* u⇒ (⊩sucᵘ ⊩t))
      (sucᵘᵣ _ ⊩t′) →
        let ⊢t′ = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩t′) in
        ⊩Level≡-⇒* (supᵘ-substʳ* ⊢t′ u⇒ ⇨∷* redMany (supᵘ-sucᵘ ⊢t′ ⊢t))
          u⇒ (⊩sucᵘ≡sucᵘ (⊩supᵘ-sub′ t⇒ ⊩t′))
      (neLvl x) → term (id (supᵘⱼ ⊢t′ ⊢u)) u⇒ $
        trans
          ([Level]-prop.neLvl $
           supᵘˡᵣ (reflneLevel-prop x) $
           ⊩Level≡-⇒* u⇒ (id (sucᵘⱼ ⊢t′)) (⊩sucᵘ≡sucᵘ (redLevel t⇒ ⊩t)))
          (trans (supᵘ-subᵣ x (⊩supᵘ-idem ok (⊩neLvl x)))
             (sucᵘᵣ ok (symLevel (redLevel t⇒ ⊩t))))
  ⊩supᵘ-sub′ ⇒∷Level (literal not-ok _ _) =
    ⊥-elim $ not-ok $
    inversion-Level-⊢ (wf-⊢≡∷ (subset*Term ⇒∷Level) .proj₁)

  ⊩supᵘ-sub :
    Level-allowed →
    Γ ⊩Level t ∷Level →
    Γ ⊩Level t supᵘ sucᵘ t ≡ sucᵘ t ∷Level
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
  wf-neLevel-prop (ne (neNfₜ₌ _ neK neM k≡m)) = wfEqTerm (≅ₜ-eq (~-to-≅ₜ k≡m))

opaque mutual

  wf-Level-eq : Γ ⊩Level t ≡ u ∷Level → Γ ⊩Level t ∷Level × Γ ⊩Level u ∷Level
  wf-Level-eq (term t⇒t′ u⇒u′ t′≡u′) =
    let ⊩t′ , ⊩u′ = wf-[Level]-prop t′≡u′ in
    term t⇒t′ ⊩t′ , term u⇒u′ ⊩u′
  wf-Level-eq (literal! not-ok ⊢Γ t-lit) =
    literal not-ok ⊢Γ t-lit , literal not-ok ⊢Γ t-lit

  wf-[Level]-prop : [Level]-prop Γ t u → Level-prop Γ t × Level-prop Γ u
  wf-[Level]-prop (zeroᵘᵣ ok) =
    zeroᵘᵣ ok , zeroᵘᵣ ok
  wf-[Level]-prop (sucᵘᵣ ok t≡u) =
    let ⊩t , ⊩u = wf-Level-eq t≡u in
    sucᵘᵣ ok ⊩t , sucᵘᵣ ok ⊩u
  wf-[Level]-prop (supᵘ-subᵣ ⊩t ≡u) =
    let _ , ⊩u = wf-Level-eq ≡u
        ok     = inversion-Level-⊢ (wf-⊢∷ (escape-neLevel-prop ⊩t))
    in
    neLvl (supᵘˡᵣ ⊩t (⊩sucᵘ ⊩u)) , sucᵘᵣ ok ⊩u
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
    let ok = inversion-Level-⊢ (wf-⊢∷ (escape-neLevel-prop ⊩k)) in
    supᵘˡᵣ ⊩k (term (id (zeroᵘⱼ ok (wf-neLevel-prop ⊩k))) (zeroᵘᵣ ok)) ,
    ⊩k
  wf-[neLevel]-prop (supᵘ-assoc¹ᵣ ⊩t ⊩u ⊩v) =
    let ok = inversion-Level-⊢ (wf-⊢∷ (escape-neLevel-prop ⊩t)) in
    supᵘˡᵣ (supᵘˡᵣ ⊩t ⊩u) ⊩v , supᵘˡᵣ ⊩t (⊩supᵘ ok ⊩u ⊩v)
  wf-[neLevel]-prop (supᵘ-assoc²ᵣ [t] [u] [v]) =
    supᵘˡᵣ (supᵘʳᵣ [t] [u]) [v] , supᵘʳᵣ [t] (supᵘˡᵣ [u] [v])
  wf-[neLevel]-prop (supᵘ-assoc³ᵣ ⊩t ⊩u ⊩v) =
    let ok = inversion-Level-⊢ (wf-⊢∷ (escape-neLevel-prop ⊩v)) in
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
      Γ ⊩Level u′ ∷Level →
      Γ ⊢ u ⇒* u′ ∷ Level →
      Γ ⊩Level t supᵘ u ≡ t supᵘ u′ ∷Level
    ⊩supᵘ-congʳ-⇒* (zeroᵘᵣ ok) ⊩u′ u⇒ =
      ⊩Level≡-⇒*
        (redMany (supᵘ-zeroˡ (redFirst*Term u⇒)))
        (redMany (supᵘ-zeroˡ (⊢∷Level→⊢∷Level ok (escapeLevel ⊩u′))))
        (redLevel′ u⇒ ⊩u′)
    ⊩supᵘ-congʳ-⇒* (sucᵘᵣ ok ⊩t) ⊩u′ u⇒ =
      redLevel′ (supᵘ-substʳ* (⊢∷Level→⊢∷Level ok (escapeLevel ⊩t)) u⇒)
        (⊩supᵘ ok (⊩sucᵘ ⊩t) ⊩u′)
    ⊩supᵘ-congʳ-⇒* (neLvl ⊩t) ⊩u′ u⇒ =
      ⊩[neLvl] (supᵘˡᵣ (reflneLevel-prop ⊩t) (redLevel′ u⇒ ⊩u′))

  mutual
    ⊩supᵘ-congˡ-prop :
      [Level]-prop Γ t₁′ t₂′ →
      Γ ⊩Level u ∷Level →
      Γ ⊩Level t₁′ supᵘ u ≡ t₂′ supᵘ u ∷Level
    ⊩supᵘ-congˡ-prop (zeroᵘᵣ ok) ⊩u =
      let ⊢u = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩u)
          d  = redMany (supᵘ-zeroˡ ⊢u)
      in
      ⊩Level≡-⇒* d d (reflLevel ⊩u)
    ⊩supᵘ-congˡ-prop (sucᵘᵣ ok _) (literal not-ok _ _) =
      ⊥-elim (not-ok ok)
    ⊩supᵘ-congˡ-prop (sucᵘᵣ ok t₁′≡t₂′) (term u⇒ propu) =
      let _ , ⊢t₁′ , ⊢t₂′ =
            wf-⊢≡∷ (≅ₜ-eq (⊢≅∷L→⊢≅∷ ok $ escapeLevelEq t₁′≡t₂′))
      in
      ⊩Level≡-⇒* (supᵘ-substʳ* ⊢t₁′ u⇒) (supᵘ-substʳ* ⊢t₂′ u⇒) $
      case propu of λ where
        (zeroᵘᵣ _) →
          ⊩Level≡-⇒*
            (redMany (supᵘ-zeroʳ ⊢t₁′))
            (redMany (supᵘ-zeroʳ ⊢t₂′))
            (⊩sucᵘ≡sucᵘ t₁′≡t₂′)
        (sucᵘᵣ _ ⊩u′) →
          let ⊢u′ = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩u′) in
          ⊩Level≡-⇒*
            (redMany (supᵘ-sucᵘ ⊢t₁′ ⊢u′))
            (redMany (supᵘ-sucᵘ ⊢t₂′ ⊢u′))
            (⊩sucᵘ≡sucᵘ (⊩supᵘ-congˡ ok t₁′≡t₂′ ⊩u′))
        (neLvl ⊩u′) →
          ⊩[neLvl] (supᵘʳᵣ t₁′≡t₂′ (reflneLevel-prop ⊩u′))
    ⊩supᵘ-congˡ-prop {Γ} {u} k≤1+k′@(supᵘ-subᵣ {k′} ⊩k k≤k′) ⊩u =
      let ok = inversion-Level-⊢ (wf-⊢∷ (escape-neLevel-prop ⊩k)) in
      case ⊩u of λ where
        (literal not-ok _ _) →
          ⊥-elim (not-ok ok)
        (term u⇒ propu) →
          let _ , ⊩k′ = wf-Level-eq k≤k′
              ⊢k      = escape-neLevel-prop ⊩k
              ⊢k′     = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩k′)
              ⊩k′+1   = ⊩sucᵘ ⊩k′
              ⊩k⊔k′+1 = ⊩supᵘ ok (⊩neLvl ⊩k) ⊩k′+1
              ⊢Γ      = wfTerm (redFirst*Term u⇒)
          in case propu of λ where
            (zeroᵘᵣ _) →
              transEqTermLevel (⊩supᵘ-zeroʳ′ ⊩k⊔k′+1 u⇒) $
                transEqTermLevel (⊩[Lvl] ⊢Γ k≤1+k′) $
                symLevel (⊩supᵘ-zeroʳ′ (⊩sucᵘ ⊩k′) u⇒)
            (sucᵘᵣ {k = u′} _ ⊩u′) →
              let ⊢u′ = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩u′)

                  d : Γ ⊢ sucᵘ k′ supᵘ u ⇒* sucᵘ (k′ supᵘ u′) ∷ Level
                  d =
                    supᵘ-substʳ* ⊢k′ u⇒ ⇨∷* redMany (supᵘ-sucᵘ ⊢k′ ⊢u′)
              in
                -- (k ⊔ sucᵘ k′) ⊔ u
                transEqTermLevel
                  (⊩supᵘ-assoc ok (⊩neLvl ⊩k) (⊩sucᵘ ⊩k′) ⊩u) $
                -- k ⊔ (sucᵘ k′ ⊔ u)
                transEqTermLevel
                  (⊩supᵘ-congʳ-⇒* (neLvl ⊩k)
                     (⊩sucᵘ (⊩supᵘ ok ⊩k′ ⊩u′)) d) $
                -- k ⊔ sucᵘ (k′ ⊔ u′)
                term (id (supᵘⱼ ⊢k (sucᵘⱼ (supᵘⱼ ⊢k′ ⊢u′)))) d
                  (supᵘ-subᵣ ⊩k (transEqTermLevel
                    -- k ⊔ (k′ ⊔ u′)
                    (symLevel (⊩supᵘ-assoc ok (⊩neLvl ⊩k) ⊩k′ ⊩u′))
                    -- (k ⊔ k′) ⊔ u′
                    (⊩supᵘ-congˡ ok k≤k′ ⊩u′)))
                    -- k′ ⊔ u′
                -- sucᵘ k′ ⊔ u
            (neLvl ⊩u′) →
              transEqTermLevel
                (⊩supᵘ-comm ok (⊩supᵘ ok (⊩neLvl ⊩k) (⊩sucᵘ ⊩k′)) ⊩u) $
                transEqTermLevel
                  (term
                     (supᵘ-substˡ* u⇒ (supᵘⱼ ⊢k (sucᵘⱼ ⊢k′)))
                     (supᵘ-substˡ* u⇒ (sucᵘⱼ ⊢k′))
                     ([Level]-prop.neLvl $
                      supᵘˡᵣ (reflneLevel-prop ⊩u′)
                        (⊩[Lvl] (wfTerm ⊢k) k≤1+k′))) $
                ⊩supᵘ-comm ok ⊩u (⊩sucᵘ ⊩k′)
    ⊩supᵘ-congˡ-prop (neLvl x) [u] =
      ⊩[neLvl] (supᵘˡᵣ x (reflLevel [u]))
    ⊩supᵘ-congˡ-prop (sym t₁′≡t₂′) [u] =
      symLevel (⊩supᵘ-congˡ-prop t₁′≡t₂′ [u])
    ⊩supᵘ-congˡ-prop (trans t₁′≡t₂′ t₂′≡t₃′) [u] =
      transEqTermLevel (⊩supᵘ-congˡ-prop t₁′≡t₂′ [u]) (⊩supᵘ-congˡ-prop t₂′≡t₃′ [u])

    ⊩supᵘ-congˡ :
      Level-allowed →
      Γ ⊩Level t₁ ≡ t₂ ∷Level →
      Γ ⊩Level u ∷Level →
      Γ ⊩Level t₁ supᵘ u ≡ t₂ supᵘ u ∷Level
    ⊩supᵘ-congˡ ok (term t₁⇒ t₂⇒ prop) ⊩u =
      let ⊢u = ⊢∷Level→⊢∷Level ok (escapeLevel ⊩u) in
      ⊩Level≡-⇒* (supᵘ-substˡ* t₁⇒ ⊢u) (supᵘ-substˡ* t₂⇒ ⊢u)
        (⊩supᵘ-congˡ-prop prop ⊩u)
    ⊩supᵘ-congˡ ok (literal! not-ok _ _) _ =
      ⊥-elim (not-ok ok)

opaque

  -- Right congruence for supᵘ.

  ⊩supᵘ-congʳ :
    Level-allowed →
    Γ ⊩Level t ∷Level →
    Γ ⊩Level u₁ ≡ u₂ ∷Level →
    Γ ⊩Level t supᵘ u₁ ≡ t supᵘ u₂ ∷Level
  ⊩supᵘ-congʳ ok ⊩t u₁≡u₂ =
    let ⊩u₁ , ⊩u₂ = wf-Level-eq u₁≡u₂ in
    transEqTermLevel (⊩supᵘ-comm ok ⊩t ⊩u₁) $
    transEqTermLevel (⊩supᵘ-congˡ ok u₁≡u₂ ⊩t) $
    ⊩supᵘ-comm ok ⊩u₂ ⊩t

opaque

  -- Congruence for supᵘ.

  ⊩supᵘ≡supᵘ :
    Level-allowed →
    Γ ⊩Level t₁ ≡ t₂ ∷Level →
    Γ ⊩Level u₁ ≡ u₂ ∷Level →
    Γ ⊩Level t₁ supᵘ u₁ ≡ t₂ supᵘ u₂ ∷Level
  ⊩supᵘ≡supᵘ ok t₁≡t₂ u₁≡u₂ =
    let ⊩t₁ , ⊩t₂ = wf-Level-eq t₁≡t₂
        ⊩u₁ , ⊩u₂ = wf-Level-eq u₁≡u₂
    in
    transEqTermLevel (⊩supᵘ-congʳ ok ⊩t₁ u₁≡u₂)
      (⊩supᵘ-congˡ ok t₁≡t₂ ⊩u₂)

------------------------------------------------------------------------
-- Level realisation

opaque

  -- A simplification lemma for ↑ⁿ.

  ↑ⁿ-subst :
    {eq : t PE.≡ u} {⊩t : Γ ⊩Level t ∷Level} →
    ↑ⁿ (PE.subst (_⊩Level_∷Level _) eq ⊩t) PE.≡ ↑ⁿ ⊩t
  ↑ⁿ-subst {eq = PE.refl} = PE.refl

opaque

  -- A simplification lemma for ↑ᵘ.

  ↑ᵘ-subst :
    {eq : t PE.≡ u} {⊩t : Γ ⊩Level t ∷Level} →
    ↑ᵘ (PE.subst (_⊩Level_∷Level _) eq ⊩t) PE.≡ ↑ᵘ ⊩t
  ↑ᵘ-subst = PE.cong 0ᵘ+_ ↑ⁿ-subst

-- Irrelevance of the reducibility proof for level realisation.

opaque
  unfolding ↑ⁿ_

  mutual
    ↑ⁿ-irrelevance
      : ∀ {t} ([t] : Γ ⊩Level t ∷Level) ([t]′ : Γ ⊩Level t ∷Level)
      → ↑ⁿ [t] PE.≡ ↑ⁿ [t]′
    ↑ⁿ-irrelevance (term t⇒ ⊩t) (term t⇒′ ⊩t′) =
      case whrDet*Term (t⇒ , level ⊩t) (t⇒′ , level ⊩t′) of λ {
        PE.refl →
      ↑ⁿ-prop-irrelevance ⊩t ⊩t′ }
    ↑ⁿ-irrelevance (term ⇒∷Level _) (literal not-ok _ _) =
      ⊥-elim $ not-ok $
      inversion-Level-⊢ (wf-⊢≡∷ (subset*Term ⇒∷Level) .proj₁)
    ↑ⁿ-irrelevance (literal not-ok _ _) (term ⇒∷Level _) =
      ⊥-elim $ not-ok $
      inversion-Level-⊢ (wf-⊢≡∷ (subset*Term ⇒∷Level) .proj₁)
    ↑ⁿ-irrelevance (literal not-ok _ t-lit) (literal not-ok _ t-lit′) =
      PE.cong size-of-Level Level-literal-propositional

    ↑ⁿ-prop-irrelevance
      : ∀ {t} ([t] : Level-prop Γ t) ([t]′ : Level-prop Γ t)
      → ↑ⁿ-prop [t] PE.≡ ↑ⁿ-prop [t]′
    ↑ⁿ-prop-irrelevance (zeroᵘᵣ _) (zeroᵘᵣ _) =
      PE.refl
    ↑ⁿ-prop-irrelevance (sucᵘᵣ _ ⊩t) (sucᵘᵣ _ ⊩t′) =
      PE.cong 1+ (↑ⁿ-irrelevance ⊩t ⊩t′)
    ↑ⁿ-prop-irrelevance (neLvl ⊩t) (neLvl ⊩t′) =
      ↑ⁿ-neprop-irrelevance ⊩t ⊩t′
    ↑ⁿ-prop-irrelevance (zeroᵘᵣ _) (neLvl (ne (neNfₜ₌ _ () _ _)))
    ↑ⁿ-prop-irrelevance (sucᵘᵣ _ _) (neLvl (ne (neNfₜ₌ _ () _ _)))
    ↑ⁿ-prop-irrelevance (neLvl (ne (neNfₜ₌ _ () _ _))) (zeroᵘᵣ _)
    ↑ⁿ-prop-irrelevance (neLvl (ne (neNfₜ₌ _ () _ _))) (sucᵘᵣ _ _)

    ↑ⁿ-neprop-irrelevance
      : ∀ {t} ([t] : neLevel-prop Γ t) ([t]′ : neLevel-prop Γ t)
      → ↑ⁿ-neprop [t] PE.≡ ↑ⁿ-neprop [t]′
    ↑ⁿ-neprop-irrelevance (supᵘˡᵣ x x₁) (supᵘˡᵣ y x₂) =
      PE.cong₂ _⊔_ (↑ⁿ-neprop-irrelevance x y) (↑ⁿ-irrelevance x₁ x₂)
    ↑ⁿ-neprop-irrelevance (supᵘʳᵣ x x₁) (supᵘʳᵣ x₂ y) =
      PE.cong₂ _⊔_ (PE.cong 1+ (↑ⁿ-irrelevance x x₂)) (↑ⁿ-neprop-irrelevance x₁ y)
    ↑ⁿ-neprop-irrelevance (ne x) (ne x₁) = PE.refl
    ↑ⁿ-neprop-irrelevance (supᵘˡᵣ x x₁) (supᵘʳᵣ x₂ y) = case nelevel x of λ { (ne ()) }
    ↑ⁿ-neprop-irrelevance (supᵘˡᵣ x x₁) (ne (neNfₜ₌ _ () neM k≡m))
    ↑ⁿ-neprop-irrelevance (supᵘʳᵣ x x₁) (supᵘˡᵣ y x₂) = case nelevel y of λ { (ne ()) }
    ↑ⁿ-neprop-irrelevance (supᵘʳᵣ x x₁) (ne (neNfₜ₌ _ () neM k≡m))
    ↑ⁿ-neprop-irrelevance (ne (neNfₜ₌ _ () neM k≡m)) (supᵘˡᵣ y x₁)
    ↑ⁿ-neprop-irrelevance (ne (neNfₜ₌ _ () neM k≡m)) (supᵘʳᵣ x₁ y)

↑ᵘ-irrelevance
  : ∀ {t} {[t] : Γ ⊩Level t ∷Level} {[t]′ : Γ ⊩Level t ∷Level}
  → ↑ᵘ [t] PE.≡ ↑ᵘ [t]′
↑ᵘ-irrelevance {[t]} {[t]′} = PE.cong 0ᵘ+_ (↑ⁿ-irrelevance [t] [t]′)

opaque
  unfolding ↑ⁿ_ size-of-Level

  -- Level realisation sends zeroᵘ to 0ᵘ.

  ↑ⁿ-prop-zeroᵘ : ([0] : Level-prop Γ zeroᵘ) → ↑ⁿ-prop [0] PE.≡ 0
  ↑ⁿ-prop-zeroᵘ (zeroᵘᵣ _) = PE.refl
  ↑ⁿ-prop-zeroᵘ (neLvl n) = case nelevel n of λ { (ne ()) }

  ↑ⁿ-zeroᵘ : ([0] : Γ ⊩Level zeroᵘ ∷Level) → ↑ⁿ [0] PE.≡ 0
  ↑ⁿ-zeroᵘ (term 0⇒ prop) with whnfRed*Term 0⇒ zeroᵘₙ
  ... | PE.refl = ↑ⁿ-prop-zeroᵘ prop
  ↑ⁿ-zeroᵘ (literal _ _ zeroᵘ) = PE.refl

  ↑ᵘ-zeroᵘ : ([0] : Γ ⊩Level zeroᵘ ∷Level) → ↑ᵘ [0] PE.≡ 0ᵘ
  ↑ᵘ-zeroᵘ [0] = PE.cong 0ᵘ+_ (↑ⁿ-zeroᵘ [0])

opaque
  unfolding ↑ⁿ_ size-of-Level ⊩sucᵘ

  -- Level realisation sends sucᵘ to 1+.

  ↑ⁿ-prop-sucᵘ
    : ∀ {t} ([t+1] : Level-prop Γ (sucᵘ t))
    → ∃ λ ([t] : Γ ⊩Level t ∷Level) → ↑ⁿ-prop [t+1] PE.≡ 1+ (↑ⁿ [t])
  ↑ⁿ-prop-sucᵘ (sucᵘᵣ _ ⊩t) = ⊩t , PE.refl
  ↑ⁿ-prop-sucᵘ (neLvl n)    = case nelevel n of λ { (ne ()) }

  ↑ⁿ-sucᵘ
    : ∀ {t} ([t] : Γ ⊩Level t ∷Level) ([t+1] : Γ ⊩Level sucᵘ t ∷Level)
    → ↑ⁿ [t+1] PE.≡ 1+ (↑ⁿ [t])
  ↑ⁿ-sucᵘ ⊩t@(term _ _)      ⊩t+1 = ↑ⁿ-irrelevance ⊩t+1 (⊩sucᵘ ⊩t)
  ↑ⁿ-sucᵘ ⊩t@(literal _ _ _) ⊩t+1 = ↑ⁿ-irrelevance ⊩t+1 (⊩sucᵘ ⊩t)

opaque
  unfolding ↑ⁿ_ ⊩supᵘ

  -- Level realisation sends supᵘ to ⊔ᵘ.

  ↑ⁿ-supᵘ :
    {ok : Level-allowed}
    (⊩t : Γ ⊩Level t ∷Level)
    (⊩u : Γ ⊩Level u ∷Level) →
    ↑ⁿ ⊩supᵘ ok ⊩t ⊩u PE.≡ ↑ⁿ ⊩t ⊔ ↑ⁿ ⊩u
  ↑ⁿ-supᵘ (term _ (zeroᵘᵣ _)) (term _ _) =
    PE.refl
  ↑ⁿ-supᵘ (term _ (sucᵘᵣ _ _)) (term _ (zeroᵘᵣ _)) =
    PE.refl
  ↑ⁿ-supᵘ (term _ (sucᵘᵣ _ ⊩t)) (term _ (sucᵘᵣ _ ⊩u)) =
    PE.cong 1+ (↑ⁿ-supᵘ ⊩t ⊩u)
  ↑ⁿ-supᵘ (term _ (sucᵘᵣ _ _)) (term _ (neLvl _)) =
    PE.refl
  ↑ⁿ-supᵘ (term _ (neLvl _)) (term _ _) =
    PE.refl
  ↑ⁿ-supᵘ {ok} (literal not-ok _ _) _ = ⊥-elim (not-ok ok)
  ↑ⁿ-supᵘ {ok} _ (literal not-ok _ _) = ⊥-elim (not-ok ok)

  ↑ᵘ-supᵘ :
    {ok : Level-allowed}
    (⊩t : Γ ⊩Level t ∷Level)
    (⊩u : Γ ⊩Level u ∷Level) →
    ↑ᵘ ⊩supᵘ ok ⊩t ⊩u PE.≡ ↑ᵘ ⊩t ⊔ᵘ ↑ᵘ ⊩u
  ↑ᵘ-supᵘ ⊩t ⊩u = PE.cong 0ᵘ+_ (↑ⁿ-supᵘ ⊩t ⊩u)

opaque
  unfolding ↑ⁿ_ ⊩supᵘₗ

  -- A variant of ↑ᵘ-supᵘ for _supᵘₗ_.

  ↑ᵘ-supᵘₗ :
    {⊩t : Γ ⊩Level t ∷Level}
    {⊩u : Γ ⊩Level u ∷Level} →
    ↑ᵘ ⊩supᵘₗ ⊩t ⊩u PE.≡ ↑ᵘ ⊩t ⊔ᵘ ↑ᵘ ⊩u
  ↑ᵘ-supᵘₗ {⊩t = ⊩t@(term ⇒∷Level _)} {⊩u} =
    let ok = inversion-Level-⊢ (wf-⊢≡∷ (subset*Term ⇒∷Level) .proj₁) in
    ↑ᵘ PE.subst (_⊩Level_∷Level _) (PE.sym $ supᵘₗ≡supᵘ ok)
         (⊩supᵘ ok ⊩t ⊩u)                                    ≡⟨ ↑ᵘ-subst {eq = PE.sym $ supᵘₗ≡supᵘ _} ⟩

    ↑ᵘ ⊩supᵘ ok ⊩t ⊩u                                        ≡⟨ ↑ᵘ-supᵘ _ _ ⟩

    ↑ᵘ ⊩t ⊔ᵘ ↑ᵘ ⊩u                                           ∎
  ↑ᵘ-supᵘₗ {⊩t = literal _ _ _} {⊩u = literal _ _ _} =
    PE.cong 0ᵘ+_ size-of-Level-Level-literal-supᵘₗ⇔
  ↑ᵘ-supᵘₗ {⊩t = literal not-ok _ _} {⊩u = term ⇒∷Level _} =
    ⊥-elim $ not-ok $
    inversion-Level-⊢ (wf-⊢≡∷ (subset*Term ⇒∷Level) .proj₁)

opaque

  -- zeroᵘ is the smallest level.

  zeroᵘ-≤ᵘ : {[0] : Γ ⊩Level zeroᵘ ∷Level} → ↑ᵘ [0] ≤ᵘ l
  zeroᵘ-≤ᵘ {l} {[0]} = PE.subst (_≤ᵘ l) (PE.sym (↑ᵘ-zeroᵘ [0])) 0≤ᵘ

opaque

  -- sucᵘ is inflationary.

  <′-sucᵘ
    : ∀ {t} ([t] : Γ ⊩Level t ∷Level) ([t+1] : Γ ⊩Level sucᵘ t ∷Level)
    → ↑ⁿ [t] <′ ↑ⁿ [t+1]
  <′-sucᵘ [t] [t+1] = PE.subst (↑ⁿ [t] <′_) (PE.sym (↑ⁿ-sucᵘ [t] [t+1])) ≤′-refl

  <ᵘ-sucᵘ
    : ∀ {t} {[t] : Γ ⊩Level t ∷Level} {[t+1] : Γ ⊩Level sucᵘ t ∷Level}
    → ↑ᵘ [t] <ᵘ ↑ᵘ [t+1]
  <ᵘ-sucᵘ {[t]} {[t+1]} = <ᵘ-fin (<′-sucᵘ [t] [t+1])

opaque

  -- t supᵘ u is an upper bound of t and u.

  ≤ᵘ-supᵘʳ :
    {ok : Level-allowed}
    {⊩t ⊩t′ : Γ ⊩Level t ∷Level}
    {⊩u : Γ ⊩Level u ∷Level} →
    ↑ᵘ ⊩t ≤ᵘ ↑ᵘ ⊩supᵘ ok ⊩t′ ⊩u
  ≤ᵘ-supᵘʳ {⊩t′} {⊩u} = PE.subst₂ (_≤ᵘ_) ↑ᵘ-irrelevance (PE.sym $ ↑ᵘ-supᵘ ⊩t′ ⊩u) ≤ᵘ⊔ᵘʳ

  ≤ᵘ-supᵘˡ :
    {ok : Level-allowed}
    {⊩t : Γ ⊩Level t ∷Level}
    {⊩u ⊩u′ : Γ ⊩Level u ∷Level} →
    ↑ᵘ ⊩u ≤ᵘ ↑ᵘ ⊩supᵘ ok ⊩t ⊩u′
  ≤ᵘ-supᵘˡ {⊩t} {⊩u′} = PE.subst₂ (_≤ᵘ_) ↑ᵘ-irrelevance (PE.sym $ ↑ᵘ-supᵘ ⊩t ⊩u′) ≤ᵘ⊔ᵘˡ

opaque

  -- A variant of ≤ᵘ-supᵘʳ for _supᵘₗ_.

  ≤ᵘ-supᵘₗʳ :
    {⊩t₁ ⊩t₂ : Γ ⊩Level t ∷Level}
    {⊩u : Γ ⊩Level u ∷Level} →
    ↑ᵘ ⊩t₁ ≤ᵘ ↑ᵘ ⊩supᵘₗ ⊩t₂ ⊩u
  ≤ᵘ-supᵘₗʳ = PE.subst₂ _≤ᵘ_ ↑ᵘ-irrelevance (PE.sym ↑ᵘ-supᵘₗ) ≤ᵘ⊔ᵘʳ

-- Level realisation preserves equality.

opaque
  unfolding ↑ⁿ_ ⊩sucᵘ

  mutual
    ↑ⁿ-cong
      : ∀ {t u} ([t] : Γ ⊩Level t ∷Level) ([u] : Γ ⊩Level u ∷Level)
      → Γ ⊩Level t ≡ u ∷Level
      → ↑ⁿ [t] PE.≡ ↑ⁿ [u]
    ↑ⁿ-cong (term t⇒ ⊩t) (term u⇒ ⊩u) (term t⇒′ u⇒′ t′≡u′) =
      case whrDet*Term (t⇒ , level ⊩t)
             (t⇒′ , lsplit t′≡u′ .proj₁) of λ {
        PE.refl →
      case whrDet*Term (u⇒ , level ⊩u)
             (u⇒′ , lsplit t′≡u′ .proj₂) of λ {
        PE.refl →
      ↑ⁿ-prop-cong ⊩t ⊩u t′≡u′ }}
    ↑ⁿ-cong (literal _ _ _) (literal _ _ _) (literal! _ _ _) =
      PE.cong size-of-Level Level-literal-propositional
    ↑ⁿ-cong (term ⇒∷Level _) (literal not-ok _ _) _ =
      ⊥-elim $ not-ok $
      inversion-Level-⊢ (wf-⊢≡∷ (subset*Term ⇒∷Level) .proj₁)
    ↑ⁿ-cong (term ⇒∷Level _) _ (literal! not-ok _ _) =
      ⊥-elim $ not-ok $
      inversion-Level-⊢ (wf-⊢≡∷ (subset*Term ⇒∷Level) .proj₁)
    ↑ⁿ-cong (literal not-ok _ _) (term ⇒∷Level _) _ =
      ⊥-elim $ not-ok $
      inversion-Level-⊢ (wf-⊢≡∷ (subset*Term ⇒∷Level) .proj₁)
    ↑ⁿ-cong (literal not-ok _ _) _ (term ⇒∷Level _ _) =
      ⊥-elim $ not-ok $
      inversion-Level-⊢ (wf-⊢≡∷ (subset*Term ⇒∷Level) .proj₁)

    ↑ⁿ-prop-cong
      : ∀ {t u} ([t] : Level-prop Γ t) ([u] : Level-prop Γ u)
      → [Level]-prop Γ t u
      → ↑ⁿ-prop [t] PE.≡ ↑ⁿ-prop [u]
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
        (↑ⁿ-neprop-irrelevance ⊩t⊔1+u (supᵘˡᵣ ⊩t (⊩sucᵘ ⊩u)))
        (m≤n⇒m⊔n≡n $
         m≤n⇒m≤1+n (m⊔n≡n⇒m≤n (↑ⁿ-cong (⊩neLvl (supᵘˡᵣ ⊩t ⊩u)) ⊩u t≤u)))
    ↑ⁿ-prop-cong _ (sucᵘᵣ ok (literal not-ok _ _)) _ =
      ⊥-elim (not-ok ok)
    ↑ⁿ-prop-cong (neLvl x) (neLvl y) (neLvl z) = ↑ⁿ-neprop-cong x y z
    ↑ⁿ-prop-cong x y (sym z) = PE.sym (↑ⁿ-prop-cong y x z)
    ↑ⁿ-prop-cong x y (trans z z₁) =
      let _ , [k′] = wf-[Level]-prop z
      in PE.trans (↑ⁿ-prop-cong x [k′] z) (↑ⁿ-prop-cong [k′] y z₁)
    -- Absurd cases
    ↑ⁿ-prop-cong (neLvl _) (neLvl ⊩u) (supᵘ-subᵣ _ _) =
      case nelevel ⊩u of λ { (ne ()) }
    ↑ⁿ-prop-cong (zeroᵘᵣ _) _ (neLvl t≡u) =
      case nelsplit t≡u of λ { (ne () , _) }
    ↑ⁿ-prop-cong (sucᵘᵣ _ _) _ (neLvl t≡u) =
      case nelsplit t≡u of λ { (ne () , _) }
    ↑ⁿ-prop-cong (neLvl _) (zeroᵘᵣ _) (neLvl t≡u) =
      case nelsplit t≡u of λ { (_ , ne ()) }
    ↑ⁿ-prop-cong (neLvl _) (sucᵘᵣ _ _) (neLvl t≡u) =
      case nelsplit t≡u of λ { (_ , ne ()) }

    ↑ⁿ-neprop-cong
      : ∀ {t u} ([t] : neLevel-prop Γ t) ([u] : neLevel-prop Γ u)
      → [neLevel]-prop Γ t u
      → ↑ⁿ-neprop [t] PE.≡ ↑ⁿ-neprop [u]
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
      let ok = inversion-Level-⊢ (wf-⊢∷ (escape-neLevel-prop ⊩t₁)) in
      PE.trans
        (⊔-assoc (↑ⁿ-neprop ⊩t₁) (↑ⁿ ⊩t₂) (↑ⁿ ⊩t₃))
        (PE.cong₂ _⊔_ (↑ⁿ-neprop-irrelevance ⊩t₁ ⊩u₁) (PE.trans
          (PE.sym (↑ⁿ-supᵘ ⊩t₂ ⊩t₃))
          (↑ⁿ-irrelevance (⊩supᵘ ok ⊩t₂ ⊩t₃) ⊩u₂)))
    ↑ⁿ-neprop-cong (supᵘˡᵣ (supᵘʳᵣ x x₄) x₃) (supᵘʳᵣ x₅ (supᵘˡᵣ y x₆)) (supᵘ-assoc²ᵣ x₁ z x₂) =
      PE.trans
        (⊔-assoc (1+ (↑ⁿ x)) (↑ⁿ-neprop x₄) (↑ⁿ x₃))
        (PE.cong₂ _⊔_ (PE.cong 1+ (↑ⁿ-irrelevance x x₅))
          (PE.cong₂ _⊔_ (↑ⁿ-neprop-irrelevance x₄ y)
            (↑ⁿ-irrelevance x₃ x₆)))
    ↑ⁿ-neprop-cong
      (supᵘʳᵣ ⊩t₁ ⊩t₂) (supᵘʳᵣ ⊩u₁ (supᵘʳᵣ ⊩u₂ ⊩u₃))
      (supᵘ-assoc³ᵣ _ _ _) =
      let ok = inversion-Level-⊢ (wf-⊢∷ (escape-neLevel-prop ⊩t₂)) in
      PE.trans
        (PE.cong₂ _⊔_
          (PE.cong 1+ $
           PE.trans (↑ⁿ-irrelevance ⊩t₁ (⊩supᵘ ok ⊩u₁ ⊩u₂)) (↑ⁿ-supᵘ ⊩u₁ ⊩u₂))
          (↑ⁿ-neprop-irrelevance ⊩t₂ ⊩u₃))
        (⊔-assoc (1+ (↑ⁿ ⊩u₁)) (1+ (↑ⁿ ⊩u₂)) (↑ⁿ-neprop ⊩u₃))
    ↑ⁿ-neprop-cong (supᵘˡᵣ x x₁) (supᵘˡᵣ y x₂) (supᵘ-comm¹ᵣ z d w d′) =
      PE.trans
        (⊔-comm (↑ⁿ-neprop x) (↑ⁿ x₁))
        (PE.cong₂ _⊔_ (↑ⁿ-cong x₁ (⊩neLvl y) d′) (↑ⁿ-cong (⊩neLvl x) x₂ d))
    ↑ⁿ-neprop-cong
      (supᵘʳᵣ ⊩t₁@(term _ _) ⊩t₂) (supᵘˡᵣ ⊩u₁ ⊩u₂)
      (supᵘ-comm²ᵣ _ 1+t₁≡u₂ _) =
      PE.trans
        (⊔-comm (1+ (↑ⁿ ⊩t₁)) (↑ⁿ-neprop ⊩t₂))
        (PE.cong₂ _⊔_ (↑ⁿ-neprop-irrelevance ⊩t₂ ⊩u₁)
           (↑ⁿ-cong (⊩sucᵘ ⊩t₁) ⊩u₂ 1+t₁≡u₂))
    ↑ⁿ-neprop-cong (supᵘʳᵣ (literal not-ok _ _) ⊩t₂) _ _ =
      ⊥-elim $ not-ok $
      inversion-Level-⊢ (wf-⊢∷ (escape-neLevel-prop ⊩t₂))
    ↑ⁿ-neprop-cong (supᵘˡᵣ x x₁) y (supᵘ-idemᵣ z w) = PE.trans
      (PE.cong₂ _⊔_
        (↑ⁿ-neprop-irrelevance x y)
        (PE.sym (↑ⁿ-cong (⊩neLvl y) x₁ w)))
      (⊔-idem (↑ⁿ-neprop y))
    -- Absurd cases
    ↑ⁿ-neprop-cong (supᵘˡᵣ _ _) (supᵘʳᵣ _ _) (supᵘˡᵣ z _) = case nelsplit z .proj₂ of λ { (ne ()) }
    ↑ⁿ-neprop-cong (supᵘˡᵣ _ _) (ne (neNfₜ₌ _ () neM k≡m)) (supᵘˡᵣ z x₃)
    ↑ⁿ-neprop-cong (supᵘʳᵣ _ _) _ (supᵘˡᵣ z _) = case nelsplit z .proj₁ of λ { (ne ()) }
    ↑ⁿ-neprop-cong (ne (neNfₜ₌ _ () neM k≡m)) _ (supᵘˡᵣ _ _)
    ↑ⁿ-neprop-cong (supᵘˡᵣ x _) _ (supᵘʳᵣ _ _) = case nelevel x of λ { (ne ()) }
    ↑ⁿ-neprop-cong (supᵘʳᵣ _ _) (supᵘˡᵣ y _) (supᵘʳᵣ _ _) = case nelevel y of λ { (ne ()) }
    ↑ⁿ-neprop-cong (supᵘʳᵣ _ _) (ne (neNfₜ₌ _ () neM k≡m)) (supᵘʳᵣ _ _)
    ↑ⁿ-neprop-cong (ne (neNfₜ₌ _ () neM k≡m)) _ (supᵘʳᵣ _ _)
    ↑ⁿ-neprop-cong (supᵘʳᵣ _ _) y (supᵘ-zeroʳᵣ _) = case nelevel y of λ { (ne ()) }
    ↑ⁿ-neprop-cong (ne (neNfₜ₌ _ () neM k≡m)) _ (supᵘ-zeroʳᵣ _)
    ↑ⁿ-neprop-cong (supᵘˡᵣ _ _) _ (ne (neNfₜ₌ _ () neM k≡m))
    ↑ⁿ-neprop-cong (supᵘʳᵣ _ _) _ (ne (neNfₜ₌ _ () neM k≡m))
    ↑ⁿ-neprop-cong (ne _) (supᵘˡᵣ _ _) (ne (neNfₜ₌ _ neK () k≡m))
    ↑ⁿ-neprop-cong (ne _) (supᵘʳᵣ _ _) (ne (neNfₜ₌ _ neK () k≡m))
    ↑ⁿ-neprop-cong (supᵘˡᵣ (supᵘʳᵣ x x₅) x₃) (supᵘˡᵣ y x₄) (supᵘ-assoc¹ᵣ z x₁ x₂) = case nelevel y of λ { (ne ()) }
    ↑ⁿ-neprop-cong (supᵘˡᵣ (ne (neNfₜ₌ _ () neM k≡m)) x₃) (supᵘˡᵣ y x₄) (supᵘ-assoc¹ᵣ z x₁ x₂)
    ↑ⁿ-neprop-cong (supᵘˡᵣ x x₃) (supᵘʳᵣ x₄ y) (supᵘ-assoc¹ᵣ z x₁ x₂) = case nelevel z of λ { (ne ()) }
    ↑ⁿ-neprop-cong (supᵘˡᵣ x x₃) (ne (neNfₜ₌ _ () neM k≡m)) (supᵘ-assoc¹ᵣ z x₁ x₂)
    ↑ⁿ-neprop-cong (ne (neNfₜ₌ _ () neM k≡m)) y (supᵘ-assoc¹ᵣ z x₁ x₂)
    ↑ⁿ-neprop-cong (supᵘˡᵣ (supᵘˡᵣ x x₄) x₃) y (supᵘ-assoc²ᵣ x₁ z x₂) = case nelevel x of λ { (ne ()) }
    ↑ⁿ-neprop-cong (supᵘˡᵣ (supᵘʳᵣ x x₄) x₃) (supᵘˡᵣ y x₅) (supᵘ-assoc²ᵣ x₁ z x₂) = case nelevel y of λ { (ne ()) }
    ↑ⁿ-neprop-cong (supᵘˡᵣ (supᵘʳᵣ x x₄) x₃) (supᵘʳᵣ x₅ (supᵘʳᵣ x₆ y)) (supᵘ-assoc²ᵣ x₁ z x₂) = case nelevel x₄ of λ { (ne ()) }
    ↑ⁿ-neprop-cong (supᵘˡᵣ (supᵘʳᵣ x x₄) x₃) (supᵘʳᵣ x₅ (ne (neNfₜ₌ _ () neM k≡m))) (supᵘ-assoc²ᵣ x₁ z x₂)
    ↑ⁿ-neprop-cong (supᵘˡᵣ (supᵘʳᵣ x x₄) x₃) (ne (neNfₜ₌ _ () neM k≡m)) (supᵘ-assoc²ᵣ x₁ z x₂)
    ↑ⁿ-neprop-cong (supᵘˡᵣ (ne (neNfₜ₌ _ () neM k≡m)) x₃) y (supᵘ-assoc²ᵣ x₁ z x₂)
    ↑ⁿ-neprop-cong (ne (neNfₜ₌ _ () neM k≡m)) y (supᵘ-assoc²ᵣ x₁ z x₂)
    ↑ⁿ-neprop-cong (supᵘˡᵣ x x₃) y (supᵘ-assoc³ᵣ x₁ x₂ z) = case nelevel x of λ { (ne ()) }
    ↑ⁿ-neprop-cong (supᵘʳᵣ x x₃) (supᵘˡᵣ y x₄) (supᵘ-assoc³ᵣ x₁ x₂ z) = case nelevel y of λ { (ne ()) }
    ↑ⁿ-neprop-cong (supᵘʳᵣ x x₃) (supᵘʳᵣ x₄ (supᵘˡᵣ y x₅)) (supᵘ-assoc³ᵣ x₁ x₂ z) = case nelevel y of λ { (ne ()) }
    ↑ⁿ-neprop-cong (supᵘʳᵣ x x₃) (supᵘʳᵣ x₄ (ne (neNfₜ₌ _ () neM k≡m))) (supᵘ-assoc³ᵣ x₁ x₂ z)
    ↑ⁿ-neprop-cong (supᵘʳᵣ x x₃) (ne (neNfₜ₌ _ () neM k≡m)) (supᵘ-assoc³ᵣ x₁ x₂ z)
    ↑ⁿ-neprop-cong (ne (neNfₜ₌ _ () neM k≡m)) y (supᵘ-assoc³ᵣ x₁ x₂ z)
    ↑ⁿ-neprop-cong (supᵘˡᵣ x x₁) (supᵘʳᵣ x₂ y) (supᵘ-comm¹ᵣ z d w d′) = case nelevel w of λ { (ne ()) }
    ↑ⁿ-neprop-cong (supᵘˡᵣ x x₁) (ne (neNfₜ₌ _ () neM k≡m)) (supᵘ-comm¹ᵣ z d w d′)
    ↑ⁿ-neprop-cong (supᵘʳᵣ x x₁) y (supᵘ-comm¹ᵣ z d w d′) = case nelevel z of λ { (ne ()) }
    ↑ⁿ-neprop-cong (ne (neNfₜ₌ _ () neM k≡m)) y (supᵘ-comm¹ᵣ z d w d′)
    ↑ⁿ-neprop-cong (supᵘˡᵣ x x₁) y (supᵘ-comm²ᵣ z d w) = case nelevel x of λ { (ne ()) }
    ↑ⁿ-neprop-cong (supᵘʳᵣ x x₁) (supᵘʳᵣ x₂ y) (supᵘ-comm²ᵣ z d w) = case nelevel x₁ of λ { (ne ()) }
    ↑ⁿ-neprop-cong (supᵘʳᵣ x x₁) (ne (neNfₜ₌ _ () neM k≡m)) (supᵘ-comm²ᵣ z d w)
    ↑ⁿ-neprop-cong (ne (neNfₜ₌ _ () neM k≡m)) y (supᵘ-comm²ᵣ z d w)
    ↑ⁿ-neprop-cong (supᵘʳᵣ x x₁) y (supᵘ-idemᵣ z w) = case nelevel y of λ { (ne ()) }
    ↑ⁿ-neprop-cong (ne (neNfₜ₌ _ () neM k≡m)) y (supᵘ-idemᵣ z w)

↑ᵘ-cong
  : ∀ {t u} {[t] : Γ ⊩Level t ∷Level} {[u] : Γ ⊩Level u ∷Level}
  → Γ ⊩Level t ≡ u ∷Level
  → ↑ᵘ [t] PE.≡ ↑ᵘ [u]
↑ᵘ-cong {[t]} {[u]} t≡u = PE.cong 0ᵘ+_ (↑ⁿ-cong [t] [u] t≡u)

-- Level realisation preserves inequality.

↑ⁿ-cong-≤ :
  {⊩t : Γ ⊩Level t ∷Level} {⊩u : Γ ⊩Level u ∷Level} →
  Level-allowed →
  Γ ⊩Level t supᵘ u ≡ u ∷Level →
  ↑ⁿ ⊩t ≤ ↑ⁿ ⊩u
↑ⁿ-cong-≤ {⊩t} {⊩u} ok t≤u =
  m⊔n≡n⇒m≤n
    (PE.trans (PE.sym (↑ⁿ-supᵘ ⊩t ⊩u))
      (↑ⁿ-cong (⊩supᵘ ok ⊩t ⊩u) ⊩u t≤u))

↑ᵘ-cong-≤ :
  {⊩t : Γ ⊩Level t ∷Level} {⊩u : Γ ⊩Level u ∷Level} →
  Level-allowed →
  Γ ⊩Level t supᵘ u ≡ u ∷Level →
  ↑ᵘ ⊩t ≤ᵘ ↑ᵘ ⊩u
↑ᵘ-cong-≤ ok t≤u = ≤ᵘ-fin (≤⇒≤′ (↑ⁿ-cong-≤ ok t≤u))
