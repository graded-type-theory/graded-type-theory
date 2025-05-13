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
open import Definition.Typed R
open import Definition.Typed.Properties.Reduction R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Reasoning.Reduction R
open import Definition.Typed.Well-formed R
open import Definition.LogicalRelation R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties.Whnf R ⦃ eqrel ⦄

open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    A B t t₁ t₂ u u₁ u₂ v : Term _
    Γ : Con Term n

-- Some expansion lemmas

⊩Level-⇒*
  : ∀ {t t′}
  → Γ ⊢ t′ ⇒* t ∷ Level
  → Γ ⊩Level t ∷Level
  → Γ ⊩Level t′ ∷Level
⊩Level-⇒* t′⇒t (Levelₜ k d prop) =
  Levelₜ _ (t′⇒t ⇨∷* d) prop

⊩Level≡-⇒*
  : ∀ {t t′ u u′}
  → Γ ⊢ t′ ⇒* t ∷ Level
  → Γ ⊢ u′ ⇒* u ∷ Level
  → Γ ⊩Level t ≡ u ∷Level
  → Γ ⊩Level t′ ≡ u′ ∷Level
⊩Level≡-⇒* t′⇒t u′⇒u (Levelₜ₌ k k′ d d′ prop) =
  Levelₜ₌ _ _ (t′⇒t ⇨∷* d) (u′⇒u ⇨∷* d′) prop

mutual

  -- Reflexivity of level terms.

  reflLevel : Γ ⊩Level t ∷Level → Γ ⊩Level t ≡ t ∷Level
  reflLevel (Levelₜ k d prop) = Levelₜ₌ k k d d (reflLevel-prop prop)

  reflLevel-prop : Level-prop Γ t → [Level]-prop Γ t t
  reflLevel-prop zeroᵘᵣ = zeroᵘᵣ
  reflLevel-prop (sucᵘᵣ x) = sucᵘᵣ (reflLevel x)
  reflLevel-prop (neLvl x₁) = neLvl (reflneLevel-prop x₁)

  reflneLevel-prop : neLevel-prop Γ t → [neLevel]-prop Γ t t
  reflneLevel-prop (maxᵘˡᵣ x₁ x₂) = maxᵘˡᵣ (reflneLevel-prop x₁) (reflLevel x₂)
  reflneLevel-prop (maxᵘʳᵣ x₁ x₂) = maxᵘʳᵣ (reflLevel x₁) (reflneLevel-prop x₂)
  reflneLevel-prop (ne x) = ne x

-- Transitivity for neutrals in WHNF and levels

transEqTermNe : ∀ {n n′ n″ A}
              → Γ ⊩neNf n  ≡ n′ ∷ A
              → Γ ⊩neNf n′ ≡ n″ ∷ A
              → Γ ⊩neNf n  ≡ n″ ∷ A
transEqTermNe (neNfₜ₌ inc neK neM k≡m) (neNfₜ₌ _ neK₁ neM₁ k≡m₁) =
  neNfₜ₌ inc neK neM₁ (~-trans k≡m k≡m₁)

mutual
  transEqTermLevel : ∀ {n n′ n″}
                   → Γ ⊩Level n  ≡ n′ ∷Level
                   → Γ ⊩Level n′ ≡ n″ ∷Level
                   → Γ ⊩Level n  ≡ n″ ∷Level
  transEqTermLevel (Levelₜ₌ k _ d d′ prop) (Levelₜ₌ _ k″ d₁ d″ prop₁)
    with whrDet*Term (d₁ , proj₁ (lsplit prop₁)) (d′ , proj₂ (lsplit prop))
  ... | PE.refl = Levelₜ₌ k k″ d d″ (transLevel-prop prop prop₁)

  transLevel-prop : ∀ {k k′ k″}
                    → [Level]-prop Γ k k′
                    → [Level]-prop Γ k′ k″
                    → [Level]-prop Γ k k″
  transLevel-prop zeroᵘᵣ zeroᵘᵣ = zeroᵘᵣ
  transLevel-prop (sucᵘᵣ x) (sucᵘᵣ x₁) = sucᵘᵣ (transEqTermLevel x x₁)
  transLevel-prop (neLvl x₂) (neLvl x₅) = neLvl (trans x₂ x₅)
  transLevel-prop zeroᵘᵣ (neLvl n) = case nelsplit n .proj₁ of λ { (ne ()) }
  transLevel-prop (sucᵘᵣ _) (neLvl n) = case nelsplit n .proj₁ of λ { (ne ()) }
  transLevel-prop (neLvl n) zeroᵘᵣ = case nelsplit n .proj₂ of λ { (ne ()) }
  transLevel-prop (neLvl n) (sucᵘᵣ _) = case nelsplit n .proj₂ of λ { (ne ()) }

-- Symmetry for neutrals in WHNF and levels

symNeutralTerm : ∀ {t u A}
               → Γ ⊩neNf t ≡ u ∷ A
               → Γ ⊩neNf u ≡ t ∷ A
symNeutralTerm (neNfₜ₌ inc neK neM k≡m) = neNfₜ₌ inc neM neK (~-sym k≡m)

mutual
  symLevel-prop : ∀ {k k′}
                → [Level]-prop Γ k k′
                → [Level]-prop Γ k′ k
  symLevel-prop zeroᵘᵣ = zeroᵘᵣ
  symLevel-prop (sucᵘᵣ x) = sucᵘᵣ (symLevel x)
  symLevel-prop (neLvl x) = neLvl (sym x)

  symLevel : ∀ {k k′}
           → Γ ⊩Level k ≡ k′ ∷Level
           → Γ ⊩Level k′ ≡ k ∷Level
  symLevel (Levelₜ₌ k k′ d d′ prop) =
    Levelₜ₌ k′ k d′ d (symLevel-prop prop)

-- Escape lemmas for levels

mutual
  -- Reducible level equalities are well-formed.
  escapeLevelEq
    : Γ ⊩Level t ≡ u ∷Level
    → Γ ⊢ t ≅ u ∷ Level
  escapeLevelEq (Levelₜ₌ k k′ D D′ prop) =
    let lk , lk′ = lsplit prop in
    ≅ₜ-red (id (Levelⱼ (wfTerm (redFirst*Term D))) , Levelₙ) (D , lk) (D′ , lk′)
      (escape-[Level]-prop (wfTerm (redFirst*Term D)) prop)

  escape-[Level]-prop
    : ⊢ Γ
    → [Level]-prop Γ t u
    → Γ ⊢ t ≅ u ∷ Level
  escape-[Level]-prop ⊢Γ zeroᵘᵣ = ≅ₜ-zeroᵘrefl ⊢Γ
  escape-[Level]-prop ⊢Γ (sucᵘᵣ x) = ≅ₜ-sucᵘ-cong (escapeLevelEq x)
  escape-[Level]-prop ⊢Γ (neLvl n) = escape-[neLevel]-prop n

  escape-[neLevel]-prop
    : [neLevel]-prop Γ t u
    → Γ ⊢ t ≅ u ∷ Level
  escape-[neLevel]-prop (maxᵘˡᵣ x y) =
    ≅ₜ-maxᵘ-cong (escape-[neLevel]-prop x) (escapeLevelEq y)
  escape-[neLevel]-prop (maxᵘʳᵣ x y) =
    ≅ₜ-maxᵘ-cong (≅ₜ-sucᵘ-cong (escapeLevelEq x)) (escape-[neLevel]-prop y)
  escape-[neLevel]-prop (maxᵘ-zeroʳˡᵣ x) =
    let _ , ⊢t , _ = wf-⊢≡∷ (≅ₜ-eq (escape-[neLevel]-prop x))
    in ≅ₜ-maxᵘ-zeroʳ ⊢t
  escape-[neLevel]-prop (maxᵘ-assoc¹ᵣ x y z) =
    let _ , ⊢t , _ = wf-⊢≡∷ (≅ₜ-eq (escape-[neLevel]-prop x))
        _ , ⊢u , _ = wf-⊢≡∷ (≅ₜ-eq (escapeLevelEq y))
        _ , ⊢v , _ = wf-⊢≡∷ (≅ₜ-eq (escapeLevelEq z))
    in ≅ₜ-maxᵘ-assoc ⊢t ⊢u ⊢v
  escape-[neLevel]-prop (maxᵘ-assoc²ᵣ x y z) =
    let _ , ⊢t , _ = wf-⊢≡∷ (≅ₜ-eq (escapeLevelEq x))
        _ , ⊢u , _ = wf-⊢≡∷ (≅ₜ-eq (escape-[neLevel]-prop y))
        _ , ⊢v , _ = wf-⊢≡∷ (≅ₜ-eq (escapeLevelEq z))
    in ≅ₜ-maxᵘ-assoc (sucᵘⱼ ⊢t) ⊢u ⊢v
  escape-[neLevel]-prop (maxᵘ-assoc³ᵣ x y z) =
    let _ , ⊢t , _ = wf-⊢≡∷ (≅ₜ-eq (escapeLevelEq x))
        _ , ⊢u , _ = wf-⊢≡∷ (≅ₜ-eq (escapeLevelEq y))
        _ , ⊢v , _ = wf-⊢≡∷ (≅ₜ-eq (escape-[neLevel]-prop z))
    in ≅ₜ-trans
      (≅ₜ-maxᵘ-cong (≅ₜ-sym (≅ₜ-maxᵘ-sucᵘ ⊢t ⊢u)) (escape-[neLevel]-prop z))
      (≅ₜ-maxᵘ-assoc (sucᵘⱼ ⊢t) (sucᵘⱼ ⊢u) ⊢v)
  escape-[neLevel]-prop (ne (neNfₜ₌ _ _ _ k≡m)) =
    ~-to-≅ₜ k≡m
  escape-[neLevel]-prop (sym x) =
    ≅ₜ-sym (escape-[neLevel]-prop x)
  escape-[neLevel]-prop (trans x y) =
    ≅ₜ-trans (escape-[neLevel]-prop x) (escape-[neLevel]-prop y)

  -- Reducible levels are well-formed.
  escapeLevel
    : Γ ⊩Level t ∷Level
    → Γ ⊢ t ∷ Level
  escapeLevel (Levelₜ k D prop) = redFirst*Term D

  escape-Level-prop
    : ⊢ Γ
    → Level-prop Γ t
    → Γ ⊢ t ∷ Level
  escape-Level-prop ⊢Γ zeroᵘᵣ = zeroᵘⱼ ⊢Γ
  escape-Level-prop ⊢Γ (sucᵘᵣ x) = sucᵘⱼ (escapeLevel x)
  escape-Level-prop ⊢Γ (neLvl x) = escape-neLevel-prop x

  escape-neLevel-prop
    : neLevel-prop Γ t
    → Γ ⊢ t ∷ Level
  escape-neLevel-prop (maxᵘˡᵣ x y) = maxᵘⱼ (escape-neLevel-prop x) (escapeLevel y)
  escape-neLevel-prop (maxᵘʳᵣ x y) = maxᵘⱼ (sucᵘⱼ (escapeLevel x)) (escape-neLevel-prop y)
  escape-neLevel-prop (ne (neNfₜ₌ _ _ _ k≡m)) = wf-⊢≡∷ (≅ₜ-eq (~-to-≅ₜ k≡m)) .proj₂ .proj₁

opaque

  ⊩sucᵘ : Γ ⊩Level t ∷Level → Γ ⊩Level sucᵘ t ∷Level
  ⊩sucᵘ [t]@(Levelₜ _ t⇒*t′ prop) =
    Levelₜ _
      (id (sucᵘⱼ (redFirst*Term t⇒*t′)))
      (sucᵘᵣ [t])

  ⊩sucᵘ≡sucᵘ : Γ ⊩Level t ≡ u ∷Level → Γ ⊩Level sucᵘ t ≡ sucᵘ u ∷Level
  ⊩sucᵘ≡sucᵘ t≡u@(Levelₜ₌ _ _ t⇒*t′ u⇒*u′ t′≡u′) =
    let t′-ok , u′-ok = lsplit t′≡u′ in
    Levelₜ₌ _ _
      (id (sucᵘⱼ (redFirst*Term t⇒*t′)))
      (id (sucᵘⱼ (redFirst*Term u⇒*u′)))
      (sucᵘᵣ t≡u)

opaque

  -- An introduction lemma for _⊩Level _ maxᵘ _ ∷Level

  ⊩maxᵘ :
    Γ ⊩Level t ∷Level →
    Γ ⊩Level u ∷Level →
    Γ ⊩Level t maxᵘ u ∷Level
  ⊩maxᵘ {t} {u} [t]@(Levelₜ t′ t⇒ propt) [u]@(Levelₜ u′ u⇒ propu) =
    let ⊢u = escapeLevel [u]
        ⊢Γ = wfTerm ⊢u
        ⊢t′ = escape-Level-prop ⊢Γ propt
        ⊢u′ = escape-Level-prop ⊢Γ propu
    in ⊩Level-⇒* (maxᵘ-substˡ* t⇒ ⊢u) $
        case propt of λ where
          zeroᵘᵣ →
            Levelₜ u′
              (zeroᵘ maxᵘ u  ⇒⟨ maxᵘ-zeroˡ ⊢u ⟩
                          u  ⇒*⟨ u⇒ ⟩∎
                          u′ ∎)
              propu
          (sucᵘᵣ {k = t′} [t′]) →
            let ⊢t′ = escapeLevel [t′]
            in ⊩Level-⇒* (maxᵘ-substʳ* ⊢t′ u⇒) $
                case propu of λ where
                  zeroᵘᵣ → Levelₜ _
                    (sucᵘ t′ maxᵘ zeroᵘ ⇒⟨ maxᵘ-zeroʳ ⊢t′ ⟩∎
                     sucᵘ t′            ∎)
                    (sucᵘᵣ [t′])
                  (sucᵘᵣ {k = u′} [u′]) →
                    let ⊢u′ = escapeLevel [u′]
                    in Levelₜ _
                      (sucᵘ t′ maxᵘ sucᵘ u′ ⇒⟨ maxᵘ-sucᵘ ⊢t′ ⊢u′ ⟩∎
                       sucᵘ (t′ maxᵘ u′)    ∎)
                      (sucᵘᵣ (⊩maxᵘ [t′] [u′]))
                  (neLvl [u′]) →
                    Levelₜ _
                      (id (maxᵘⱼ (sucᵘⱼ ⊢t′) ⊢u′))
                      (neLvl (maxᵘʳᵣ [t′] [u′]))
          (neLvl [t′]) →
            Levelₜ (t′ maxᵘ u)
              (id (maxᵘⱼ ⊢t′ ⊢u))
              (neLvl (maxᵘˡᵣ [t′] [u]))

opaque

  -- An introduction lemma for _⊩Level _ maxᵘ _ ≡ _ maxᵘ _ ∷Level

  ⊩maxᵘ≡maxᵘ :
    Γ ⊩Level t₁ ≡ t₂ ∷Level →
    Γ ⊩Level u₁ ≡ u₂ ∷Level →
    Γ ⊩Level t₁ maxᵘ u₁ ≡ t₂ maxᵘ u₂ ∷Level
  ⊩maxᵘ≡maxᵘ {t₁} {t₂} {u₁} {u₂} t₁≡t₂@(Levelₜ₌ t₁′ t₂′ t₁⇒ t₂⇒ propt) u₁≡u₂@(Levelₜ₌ u₁′ u₂′ u₁⇒ u₂⇒ propu) =
    let _ , ⊢u₁ , ⊢u₂ = wf-⊢≡∷ (≅ₜ-eq (escapeLevelEq u₁≡u₂))
        ⊢Γ = wfTerm ⊢u₁
        _ , ⊢t₁′ , ⊢t₂′ = wf-⊢≡∷ (≅ₜ-eq (escape-[Level]-prop ⊢Γ propt))
        _ , ⊢u₁′ , ⊢u₂′ = wf-⊢≡∷ (≅ₜ-eq (escape-[Level]-prop ⊢Γ propu))
    in ⊩Level≡-⇒* (maxᵘ-substˡ* t₁⇒ ⊢u₁) (maxᵘ-substˡ* t₂⇒ ⊢u₂) $
        case propt of λ where
          zeroᵘᵣ →
            Levelₜ₌ u₁′ u₂′
              (zeroᵘ maxᵘ u₁  ⇒⟨ maxᵘ-zeroˡ ⊢u₁ ⟩
                          u₁  ⇒*⟨ u₁⇒ ⟩∎
                          u₁′ ∎)
              (zeroᵘ maxᵘ u₂  ⇒⟨ maxᵘ-zeroˡ ⊢u₂ ⟩
                          u₂  ⇒*⟨ u₂⇒ ⟩∎
                          u₂′ ∎)
              propu
          (sucᵘᵣ {k = t₁′} {k′ = t₂′} t₁′≡t₂′) →
            let _ , ⊢t₁′ , ⊢t₂′ = wf-⊢≡∷ (≅ₜ-eq (escapeLevelEq t₁′≡t₂′))
            in ⊩Level≡-⇒* (maxᵘ-substʳ* ⊢t₁′ u₁⇒) (maxᵘ-substʳ* ⊢t₂′ u₂⇒) $
                case propu of λ where
                  zeroᵘᵣ → Levelₜ₌ _ _
                    (sucᵘ t₁′ maxᵘ zeroᵘ ⇒⟨ maxᵘ-zeroʳ ⊢t₁′ ⟩∎
                     sucᵘ t₁′            ∎)
                    (sucᵘ t₂′ maxᵘ zeroᵘ ⇒⟨ maxᵘ-zeroʳ ⊢t₂′ ⟩∎
                     sucᵘ t₂′            ∎)
                    (sucᵘᵣ t₁′≡t₂′)
                  (sucᵘᵣ {k = u₁′} {k′ = u₂′} u₁′≡u₂′) →
                    let _ , ⊢u₁′ , ⊢u₂′ = wf-⊢≡∷ (≅ₜ-eq (escapeLevelEq u₁′≡u₂′))
                    in Levelₜ₌ _ _
                      (sucᵘ t₁′ maxᵘ sucᵘ u₁′ ⇒⟨ maxᵘ-sucᵘ ⊢t₁′ ⊢u₁′ ⟩∎
                       sucᵘ (t₁′ maxᵘ u₁′)    ∎)
                      (sucᵘ t₂′ maxᵘ sucᵘ u₂′ ⇒⟨ maxᵘ-sucᵘ ⊢t₂′ ⊢u₂′ ⟩∎
                       sucᵘ (t₂′ maxᵘ u₂′)    ∎)
                      (sucᵘᵣ (⊩maxᵘ≡maxᵘ t₁′≡t₂′ u₁′≡u₂′))
                  (neLvl u₁′≡u₂′) →
                    Levelₜ₌ _ _
                      (id (maxᵘⱼ (sucᵘⱼ ⊢t₁′) ⊢u₁′))
                      (id (maxᵘⱼ (sucᵘⱼ ⊢t₂′) ⊢u₂′))
                      (neLvl (maxᵘʳᵣ t₁′≡t₂′ u₁′≡u₂′))
          (neLvl t₁≡t₂) →
            Levelₜ₌ _ _
              (id (maxᵘⱼ ⊢t₁′ ⊢u₁))
              (id (maxᵘⱼ ⊢t₂′ ⊢u₂))
              (neLvl (maxᵘˡᵣ t₁≡t₂ u₁≡u₂))

opaque

  -- An associativity lemma for levels

  ⊩maxᵘ-assoc :
    Γ ⊩Level t ∷Level →
    Γ ⊩Level u ∷Level →
    Γ ⊩Level v ∷Level →
    Γ ⊩Level (t maxᵘ u) maxᵘ v ≡ t maxᵘ (u maxᵘ v) ∷Level
  ⊩maxᵘ-assoc {t} {u} {v} [t]@(Levelₜ t′ t⇒ propt) [u]@(Levelₜ u′ u⇒ propu) [v]@(Levelₜ v′ v⇒ propv) =
    let
      ⊢u = escapeLevel [u]
      ⊢v = escapeLevel [v]
      ⊢Γ = wfTerm ⊢u
      ⊢t′ = escape-Level-prop ⊢Γ propt
      ⊢u′ = escape-Level-prop ⊢Γ propu
      ⊢v′ = escape-Level-prop ⊢Γ propv
    in ⊩Level≡-⇒*
      (maxᵘ-substˡ* (maxᵘ-substˡ* t⇒ ⊢u) ⊢v)
      (maxᵘ-substˡ* t⇒ (maxᵘⱼ ⊢u ⊢v)) $
      case propt of λ where
        zeroᵘᵣ → ⊩Level≡-⇒*
          (redMany (maxᵘ-substˡ (maxᵘ-zeroˡ ⊢u) ⊢v))
          (redMany (maxᵘ-zeroˡ (maxᵘⱼ ⊢u ⊢v)))
          (reflLevel (⊩maxᵘ [u] [v]))
        (sucᵘᵣ {k = t″} [t″]) →
          let ⊢t″ = escapeLevel [t″]
          in ⊩Level≡-⇒*
            (maxᵘ-substˡ* (maxᵘ-substʳ* ⊢t″ u⇒) ⊢v)
            (maxᵘ-substʳ* ⊢t″ (maxᵘ-substˡ* u⇒ ⊢v)) $
            case propu of λ where
              zeroᵘᵣ → ⊩Level≡-⇒*
                (redMany (maxᵘ-substˡ (maxᵘ-zeroʳ ⊢t″) ⊢v))
                (redMany (maxᵘ-substʳ ⊢t″ (maxᵘ-zeroˡ ⊢v)))
                (reflLevel (⊩maxᵘ (⊩sucᵘ [t″]) [v]))
              (sucᵘᵣ {k = u″} [u″]) →
                let ⊢u″ = escapeLevel [u″]
                in ⊩Level≡-⇒*
                  (maxᵘ-substˡ (maxᵘ-sucᵘ ⊢t″ ⊢u″) ⊢v ⇨ maxᵘ-substʳ* (maxᵘⱼ ⊢t″ ⊢u″) v⇒)
                  (maxᵘ-substʳ* ⊢t″ (maxᵘ-substʳ* ⊢u″ v⇒)) $
                  case propv of λ where
                    zeroᵘᵣ → ⊩Level≡-⇒*
                      (redMany (maxᵘ-zeroʳ (maxᵘⱼ ⊢t″ ⊢u″)))
                      (maxᵘ-substʳ ⊢t″ (maxᵘ-zeroʳ ⊢u″) ⇨ redMany (maxᵘ-sucᵘ ⊢t″ ⊢u″))
                      (reflLevel (⊩sucᵘ (⊩maxᵘ [t″] [u″])))
                    (sucᵘᵣ {k = v″} [v″]) →
                      let ⊢v″ = escapeLevel [v″]
                      in ⊩Level≡-⇒*
                        (redMany (maxᵘ-sucᵘ (maxᵘⱼ ⊢t″ ⊢u″) ⊢v″))
                        (maxᵘ-substʳ ⊢t″ (maxᵘ-sucᵘ ⊢u″ ⊢v″) ⇨ redMany (maxᵘ-sucᵘ ⊢t″ (maxᵘⱼ ⊢u″ ⊢v″)))
                        (⊩sucᵘ≡sucᵘ (⊩maxᵘ-assoc [t″] [u″] [v″]))
                    (neLvl nepropv) →
                      Levelₜ₌ _ _
                        (id (maxᵘⱼ (sucᵘⱼ (maxᵘⱼ ⊢t″ ⊢u″)) ⊢v′))
                        (id (maxᵘⱼ (sucᵘⱼ ⊢t″) (maxᵘⱼ (sucᵘⱼ ⊢u″) ⊢v′)))
                        (neLvl (maxᵘ-assoc³ᵣ (reflLevel [t″]) (reflLevel [u″]) (reflneLevel-prop nepropv)))
              (neLvl nepropu) →
                Levelₜ₌ _ _
                  (id (maxᵘⱼ (maxᵘⱼ (sucᵘⱼ ⊢t″) ⊢u′) ⊢v))
                  (id (maxᵘⱼ (sucᵘⱼ ⊢t″) (maxᵘⱼ ⊢u′ ⊢v)))
                  (neLvl (maxᵘ-assoc²ᵣ (reflLevel [t″]) (reflneLevel-prop nepropu) (reflLevel [v])))
        (neLvl nepropt) →
          Levelₜ₌ _ _
            (id (maxᵘⱼ (maxᵘⱼ ⊢t′ ⊢u) ⊢v))
            (id (maxᵘⱼ ⊢t′ (maxᵘⱼ ⊢u ⊢v)))
            (neLvl (maxᵘ-assoc¹ᵣ (reflneLevel-prop nepropt) (reflLevel [u]) (reflLevel [v])))

-- Well-formedness for neutrals in WHNF and levels

wf-neNf : Γ ⊩neNf t ≡ u ∷ A → Γ ⊩neNf t ≡ t ∷ A × Γ ⊩neNf u ≡ u ∷ A
wf-neNf t≡u = transEqTermNe t≡u (symNeutralTerm t≡u) , transEqTermNe (symNeutralTerm t≡u) t≡u

wf-neLevel-prop : neLevel-prop Γ t → ⊢ Γ
wf-neLevel-prop (maxᵘˡᵣ x₁ x₂) = wf-neLevel-prop x₁
wf-neLevel-prop (maxᵘʳᵣ x₁ x₂) = wf-neLevel-prop x₂
wf-neLevel-prop (ne (neNfₜ₌ _ neK neM k≡m)) = wfEqTerm (≅ₜ-eq (~-to-≅ₜ k≡m))

mutual
  wf-Level-eq : Γ ⊩Level t ≡ u ∷Level → Γ ⊩Level t ∷Level × Γ ⊩Level u ∷Level
  wf-Level-eq (Levelₜ₌ k k′ d d′ prop) =
    let x , y = wf-[Level]-prop prop
    in Levelₜ k d x , Levelₜ k′ d′ y

  wf-[Level]-prop : [Level]-prop Γ t u → Level-prop Γ t × Level-prop Γ u
  wf-[Level]-prop zeroᵘᵣ = zeroᵘᵣ , zeroᵘᵣ
  wf-[Level]-prop (sucᵘᵣ x) = let a , b = wf-Level-eq x in sucᵘᵣ a , sucᵘᵣ b
  wf-[Level]-prop (neLvl t≡u) = let [t] , [u] = wf-[neLevel]-prop t≡u in neLvl [t] , neLvl [u]

  wf-[neLevel]-prop : [neLevel]-prop Γ t u → neLevel-prop Γ t × neLevel-prop Γ u
  wf-[neLevel]-prop (maxᵘˡᵣ k₁≡k₁′ k₂≡k₂′) =
    let [k₁] , [k₁′] = wf-[neLevel]-prop k₁≡k₁′
        [k₂] , [k₂′] = wf-Level-eq k₂≡k₂′
    in maxᵘˡᵣ [k₁] [k₂] , maxᵘˡᵣ [k₁′] [k₂′]
  wf-[neLevel]-prop (maxᵘʳᵣ k₁≡k₁′ k₂≡k₂′) =
    let [k₁] , [k₁′] = wf-Level-eq k₁≡k₁′
        [k₂] , [k₂′] = wf-[neLevel]-prop k₂≡k₂′
    in maxᵘʳᵣ [k₁] [k₂] , maxᵘʳᵣ [k₁′] [k₂′]
  wf-[neLevel]-prop (maxᵘ-zeroʳˡᵣ k≡k) =
    let [k] , _ = wf-[neLevel]-prop k≡k
    in maxᵘˡᵣ [k] (Levelₜ _ (id (zeroᵘⱼ (wf-neLevel-prop [k]))) zeroᵘᵣ) , [k]
  wf-[neLevel]-prop (maxᵘ-assoc¹ᵣ x y z) =
    let [t] , _ = wf-[neLevel]-prop x
        [u] , _ = wf-Level-eq y
        [v] , _ = wf-Level-eq z
    in maxᵘˡᵣ (maxᵘˡᵣ [t] [u]) [v] , maxᵘˡᵣ [t] (⊩maxᵘ [u] [v])
  wf-[neLevel]-prop (maxᵘ-assoc²ᵣ x y z) =
    let [t] , _ = wf-Level-eq x
        [u] , _ = wf-[neLevel]-prop y
        [v] , _ = wf-Level-eq z
    in maxᵘˡᵣ (maxᵘʳᵣ [t] [u]) [v] , maxᵘʳᵣ [t] (maxᵘˡᵣ [u] [v])
  wf-[neLevel]-prop (maxᵘ-assoc³ᵣ x y z) =
    let [t] , _ = wf-Level-eq x
        [u] , _ = wf-Level-eq y
        [v] , _ = wf-[neLevel]-prop z
    in maxᵘʳᵣ (⊩maxᵘ [t] [u]) [v] , maxᵘʳᵣ [t] (maxᵘʳᵣ [u] [v])
  wf-[neLevel]-prop (ne x) =
    let a , b = wf-neNf x
    in ne a , ne b
  wf-[neLevel]-prop (sym u≡t) =
    let [u] , [t] = wf-[neLevel]-prop u≡t
    in [t] , [u]
  wf-[neLevel]-prop (trans x y) =
    let [t] , _ = wf-[neLevel]-prop x
        _ , [u] = wf-[neLevel]-prop y
    in [t] , [u]
