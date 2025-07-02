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
open import Definition.Typed.Properties.Reduction R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Reasoning.Reduction R
open import Definition.Typed.Well-formed R
open import Definition.LogicalRelation R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties.Whnf R ⦃ eqrel ⦄

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    A B t t₁ t₂ t₁′ t₂′ u u₁ u₂ v : Term _
    Γ : Con Term n
    l : Universe-level

mutual

  -- Reflexivity of level equality.

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

transEqTermLevel : ∀ {n n′ n″}
                 → Γ ⊩Level n  ≡ n′ ∷Level
                 → Γ ⊩Level n′ ≡ n″ ∷Level
                 → Γ ⊩Level n  ≡ n″ ∷Level
transEqTermLevel (Levelₜ₌ k _ d d′ prop) (Levelₜ₌ _ k″ d₁ d″ prop₁)
  with whrDet*Term (d₁ , proj₁ (lsplit prop₁)) (d′ , proj₂ (lsplit prop))
... | PE.refl = Levelₜ₌ k k″ d d″ (trans prop prop₁)

-- Symmetry for neutrals in WHNF and levels

symNeutralTerm : ∀ {t u A}
               → Γ ⊩neNf t ≡ u ∷ A
               → Γ ⊩neNf u ≡ t ∷ A
symNeutralTerm (neNfₜ₌ inc neK neM k≡m) = neNfₜ₌ inc neM neK (~-sym k≡m)

symLevel : ∀ {k k′}
         → Γ ⊩Level k ≡ k′ ∷Level
         → Γ ⊩Level k′ ≡ k ∷Level
symLevel (Levelₜ₌ k k′ d d′ prop) = Levelₜ₌ k′ k d′ d (sym prop)

-- Some reduction and expansion lemmas

redLevel
  : ∀ {t t′}
  → Γ ⊢ t ⇒* t′ ∷ Level
  → Γ ⊩Level t ∷Level
  → Γ ⊩Level t ≡ t′ ∷Level
redLevel t⇒ (Levelₜ k d prop) =
  Levelₜ₌ _ _ d (whrDet↘Term (d , level prop) t⇒)
    (reflLevel-prop prop)

redLevel′
  : ∀ {t t′}
  → Γ ⊢ t ⇒* t′ ∷ Level
  → Γ ⊩Level t′ ∷Level
  → Γ ⊩Level t ≡ t′ ∷Level
redLevel′ t⇒ (Levelₜ k d prop) =
  Levelₜ₌ _ _ (t⇒ ⇨∷* d) d
    (reflLevel-prop prop)

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
  escape-neLevel-prop (maxᵘˡᵣ x y) =
    maxᵘⱼ (escape-neLevel-prop x) (escapeLevel y)
  escape-neLevel-prop (maxᵘʳᵣ x y) =
    maxᵘⱼ (sucᵘⱼ (escapeLevel x)) (escape-neLevel-prop y)
  escape-neLevel-prop (ne x) = escape-neNf x

opaque mutual

  -- Reducible levels are reflexive.

  escapeLevel′
    : Γ ⊩Level t ∷Level
    → Γ ⊢≅ t ∷ Level
  escapeLevel′ (Levelₜ k D prop) =
    let n = level prop
        ⊢Γ = wfTerm (redFirst*Term D)
    in ≅ₜ-red (id (Levelⱼ ⊢Γ) , Levelₙ) (D , n) (D , n)
      (escape-Level-prop′ ⊢Γ prop)

  escape-Level-prop′
    : ⊢ Γ
    → Level-prop Γ t
    → Γ ⊢≅ t ∷ Level
  escape-Level-prop′ ⊢Γ zeroᵘᵣ = ≅ₜ-zeroᵘrefl ⊢Γ
  escape-Level-prop′ ⊢Γ (sucᵘᵣ x) = ≅ₜ-sucᵘ-cong (escapeLevel′ x)
  escape-Level-prop′ ⊢Γ (neLvl x) = escape-neLevel-prop′ x

  escape-neLevel-prop′
    : neLevel-prop Γ t
    → Γ ⊢≅ t ∷ Level
  escape-neLevel-prop′ (maxᵘˡᵣ x y) =
    ≅ₜ-maxᵘ-cong (escape-neLevel-prop′ x) (escapeLevel′ y)
  escape-neLevel-prop′ (maxᵘʳᵣ x y) =
    ≅ₜ-maxᵘ-cong (≅ₜ-sucᵘ-cong (escapeLevel′ x)) (escape-neLevel-prop′ y)
  escape-neLevel-prop′ (ne (neNfₜ₌ _ _ _ k≡m)) =
    ~-to-≅ₜ k≡m

opaque mutual

  -- Reducible level equalities are well-formed.

  escapeLevelEq
    : Γ ⊩Level t ≡ u ∷Level
    → Γ ⊢ t ≅ u ∷ Level
  escapeLevelEq (Levelₜ₌ k k′ D D′ prop) =
    let lk , lk′ = lsplit prop
        ⊢Γ = wfTerm (redFirst*Term D)
    in ≅ₜ-red (id (Levelⱼ ⊢Γ) , Levelₙ) (D , lk) (D′ , lk′)
      (escape-[Level]-prop ⊢Γ prop)

  escape-[Level]-prop
    : ⊢ Γ
    → [Level]-prop Γ t u
    → Γ ⊢ t ≅ u ∷ Level
  escape-[Level]-prop ⊢Γ zeroᵘᵣ = ≅ₜ-zeroᵘrefl ⊢Γ
  escape-[Level]-prop ⊢Γ (sucᵘᵣ x) = ≅ₜ-sucᵘ-cong (escapeLevelEq x)
  escape-[Level]-prop ⊢Γ (maxᵘ-subᵣ x y) =
    ≅ₜ-maxᵘ-sub′ (escape-neLevel-prop′ x) (escapeLevelEq y)
  escape-[Level]-prop ⊢Γ (neLvl n) = escape-[neLevel]-prop n
  escape-[Level]-prop ⊢Γ (sym x) = ≅ₜ-sym (escape-[Level]-prop ⊢Γ x)
  escape-[Level]-prop ⊢Γ (trans x y) =
    ≅ₜ-trans (escape-[Level]-prop ⊢Γ x) (escape-[Level]-prop ⊢Γ y)

  escape-[neLevel]-prop
    : [neLevel]-prop Γ t u
    → Γ ⊢ t ≅ u ∷ Level
  escape-[neLevel]-prop (maxᵘˡᵣ x y) =
    ≅ₜ-maxᵘ-cong (escape-[neLevel]-prop x) (escapeLevelEq y)
  escape-[neLevel]-prop (maxᵘʳᵣ x y) =
    ≅ₜ-maxᵘ-cong (≅ₜ-sucᵘ-cong (escapeLevelEq x)) (escape-[neLevel]-prop y)
  escape-[neLevel]-prop (maxᵘ-zeroʳᵣ x) =
    let ⊢t = escape-neLevel-prop′ x
    in ≅ₜ-maxᵘ-zeroʳ ⊢t
  escape-[neLevel]-prop (maxᵘ-assoc¹ᵣ x y z) =
    ≅ₜ-maxᵘ-assoc (escape-neLevel-prop′ x) (escapeLevel′ y) (escapeLevel′ z)
  escape-[neLevel]-prop (maxᵘ-assoc²ᵣ x y z) =
    ≅ₜ-maxᵘ-assoc (≅ₜ-sucᵘ-cong (escapeLevel′ x)) (escape-neLevel-prop′ y) (escapeLevel′ z)
  escape-[neLevel]-prop (maxᵘ-assoc³ᵣ x y z) =
    let ⊢t = escapeLevel′ x
        ⊢u = escapeLevel′ y
        ⊢v = escape-neLevel-prop′ z
    in ≅ₜ-trans
      (≅ₜ-maxᵘ-cong (≅ₜ-sym (≅ₜ-maxᵘ-sucᵘ ⊢t ⊢u)) ⊢v)
      (≅ₜ-maxᵘ-assoc (≅ₜ-sucᵘ-cong ⊢t) (≅ₜ-sucᵘ-cong ⊢u) ⊢v)
  escape-[neLevel]-prop (maxᵘ-comm¹ᵣ x d y d′) =
    let t₁≡t₂ = escapeLevelEq d
        u₁≡u₂ = escapeLevelEq d′
        ⊢t₁ , _ = wf-⊢≅∷ t₁≡t₂
        ⊢u₁ , _ = wf-⊢≅∷ u₁≡u₂
    in ≅ₜ-trans (≅ₜ-maxᵘ-comm ⊢t₁ ⊢u₁) (≅ₜ-maxᵘ-cong u₁≡u₂ t₁≡t₂)
  escape-[neLevel]-prop (maxᵘ-comm²ᵣ [t₁] d [u]) =
    let t₁+1≡t₂ = escapeLevelEq d
        _ , ⊢t₂ = wf-⊢≅∷ t₁+1≡t₂
        ⊢u = escape-neLevel-prop′ [u]
    in ≅ₜ-trans (≅ₜ-maxᵘ-cong t₁+1≡t₂ ⊢u) (≅ₜ-maxᵘ-comm ⊢t₂ ⊢u)
  escape-[neLevel]-prop (maxᵘ-idemᵣ [t₁] y) =
    let t₁≡t₁ = escape-neLevel-prop′ [t₁]
        t₁≡t₂ = escapeLevelEq y
    in ≅ₜ-trans (≅ₜ-maxᵘ-cong t₁≡t₁ (≅ₜ-sym t₁≡t₂)) (≅ₜ-maxᵘ-idem t₁≡t₁)
  escape-[neLevel]-prop (ne (neNfₜ₌ _ _ _ k≡m)) =
    ~-to-≅ₜ k≡m

------------------------------------------------------------------------
-- Some introduction lemmas for _⊩Level_∷Level and _⊩Level_≡_∷Level.

⊩Lvl : ⊢ Γ → Level-prop Γ t → Γ ⊩Level t ∷Level
⊩Lvl ⊢Γ [t] = Levelₜ _ (id (escape-Level-prop ⊢Γ [t])) [t]

⊩neLvl : neLevel-prop Γ t → Γ ⊩Level t ∷Level
⊩neLvl [t] = Levelₜ _ (id (escape-neLevel-prop [t])) (neLvl [t])

⊩[Lvl] : ⊢ Γ → [Level]-prop Γ t u → Γ ⊩Level t ≡ u ∷Level
⊩[Lvl] ⊢Γ t≡u =
  let _ , ⊢t , ⊢u = wf-⊢≡∷ (≅ₜ-eq (escape-[Level]-prop ⊢Γ t≡u))
  in Levelₜ₌ _ _ (id ⊢t) (id ⊢u) t≡u

⊩[neLvl] : [neLevel]-prop Γ t u → Γ ⊩Level t ≡ u ∷Level
⊩[neLvl] t≡u =
  let _ , ⊢t , ⊢u = wf-⊢≡∷ (≅ₜ-eq (escape-[neLevel]-prop t≡u))
  in Levelₜ₌ _ _ (id ⊢t) (id ⊢u) (neLvl t≡u)

opaque

  -- An introduction lemma for zeroᵘ.

  ⊩zeroᵘ : ⊢ Γ → Γ ⊩Level zeroᵘ ∷Level
  ⊩zeroᵘ ⊢Γ = ⊩Lvl ⊢Γ zeroᵘᵣ

opaque

  -- Introduction lemmas for sucᵘ.

  ⊩sucᵘ : Γ ⊩Level t ∷Level → Γ ⊩Level sucᵘ t ∷Level
  ⊩sucᵘ [t]@(Levelₜ _ t⇒*t′ prop) =
    Levelₜ _
      (id (sucᵘⱼ (redFirst*Term t⇒*t′)))
      (sucᵘᵣ [t])

  ⊩sucᵘ≡sucᵘ : Γ ⊩Level t ≡ u ∷Level → Γ ⊩Level sucᵘ t ≡ sucᵘ u ∷Level
  ⊩sucᵘ≡sucᵘ t≡u@(Levelₜ₌ _ _ t⇒*t′ u⇒*u′ t′≡u′) =
    Levelₜ₌ _ _
      (id (sucᵘⱼ (redFirst*Term t⇒*t′)))
      (id (sucᵘⱼ (redFirst*Term u⇒*u′)))
      (sucᵘᵣ t≡u)

opaque

  -- An introduction lemma for maxᵘ.

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

  -- Associativity for maxᵘ.

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
                        (neLvl (maxᵘ-assoc³ᵣ [t″] [u″] nepropv))
              (neLvl nepropu) →
                Levelₜ₌ _ _
                  (id (maxᵘⱼ (maxᵘⱼ (sucᵘⱼ ⊢t″) ⊢u′) ⊢v))
                  (id (maxᵘⱼ (sucᵘⱼ ⊢t″) (maxᵘⱼ ⊢u′ ⊢v)))
                  (neLvl (maxᵘ-assoc²ᵣ [t″] nepropu [v]))
        (neLvl nepropt) →
          Levelₜ₌ _ _
            (id (maxᵘⱼ (maxᵘⱼ ⊢t′ ⊢u) ⊢v))
            (id (maxᵘⱼ ⊢t′ (maxᵘⱼ ⊢u ⊢v)))
            (neLvl (maxᵘ-assoc¹ᵣ nepropt [u] [v]))

opaque

  -- Right identity for maxᵘ.

  ⊩maxᵘ-zeroʳ′ :
    ∀ {z} →
    Γ ⊩Level t ∷Level →
    Γ ⊢ z ⇒* zeroᵘ ∷ Level →
    Γ ⊩Level t maxᵘ z ≡ t ∷Level
  ⊩maxᵘ-zeroʳ′ {t} [t]@(Levelₜ k t⇒ prop) z⇒ =
    let ⊢z = redFirst*Term z⇒
        ⊢Γ = wfTerm ⊢z
    in ⊩Level≡-⇒* (maxᵘ-substˡ* t⇒ ⊢z) t⇒ $
      case prop of λ where
        zeroᵘᵣ → redLevel′ (maxᵘ-zeroˡ ⊢z ⇨ z⇒) (⊩zeroᵘ ⊢Γ)
        (sucᵘᵣ x) →
          let ⊢k = escapeLevel x
          in redLevel′ (maxᵘ-substʳ* ⊢k z⇒ ⇨∷* redMany (maxᵘ-zeroʳ ⊢k)) (⊩sucᵘ x)
        (neLvl x) → transEqTermLevel
          (⊩[neLvl] (maxᵘˡᵣ (reflneLevel-prop x) (redLevel′ z⇒ (⊩zeroᵘ ⊢Γ))))
          (⊩[neLvl] (maxᵘ-zeroʳᵣ x))

  ⊩maxᵘ-zeroʳ :
    Γ ⊩Level t ∷Level →
    Γ ⊩Level t maxᵘ zeroᵘ ≡ t ∷Level
  ⊩maxᵘ-zeroʳ [t] = ⊩maxᵘ-zeroʳ′ [t] (id (zeroᵘⱼ (wfTerm (escapeLevel [t]))))

opaque

  -- Commutativity for maxᵘ.

  ⊩maxᵘ-comm :
    Γ ⊩Level t ∷Level →
    Γ ⊩Level u ∷Level →
    Γ ⊩Level t maxᵘ u ≡ u maxᵘ t ∷Level
  ⊩maxᵘ-comm {t} {u} [t]@(Levelₜ t′ t⇒ propt) [u]@(Levelₜ u′ u⇒ propu) =
    let
      ⊢t = escapeLevel [t]
      ⊢u = escapeLevel [u]
      ⊢Γ = wfTerm ⊢u
      ⊢t′ = escape-Level-prop ⊢Γ propt
      ⊢u′ = escape-Level-prop ⊢Γ propu
    in ⊩Level≡-⇒* (maxᵘ-substˡ* t⇒ ⊢u) (id (maxᵘⱼ ⊢u ⊢t)) $ case propt of λ where
      zeroᵘᵣ → ⊩Level≡-⇒*
        (redMany (maxᵘ-zeroˡ ⊢u))
        (id (maxᵘⱼ ⊢u ⊢t))
        (symLevel (⊩maxᵘ-zeroʳ′ [u] t⇒))
      (sucᵘᵣ {k = t′} [t′]) →
        let ⊢t′ = escapeLevel [t′]
        in
          ⊩Level≡-⇒* (maxᵘ-substʳ* ⊢t′ u⇒) (maxᵘ-substˡ* u⇒ ⊢t) $
          case propu of λ where
            zeroᵘᵣ → ⊩Level≡-⇒*
              (redMany (maxᵘ-zeroʳ ⊢t′))
              (maxᵘ-zeroˡ ⊢t ⇨ t⇒)
              (reflLevel (⊩sucᵘ [t′]))
            (sucᵘᵣ {k = u′} [u′]) →
              let ⊢u′ = escapeLevel [u′]
              in ⊩Level≡-⇒*
                (redMany (maxᵘ-sucᵘ ⊢t′ ⊢u′))
                (maxᵘ-substʳ* ⊢u′ t⇒ ⇨∷* redMany (maxᵘ-sucᵘ ⊢u′ ⊢t′))
                (⊩sucᵘ≡sucᵘ (⊩maxᵘ-comm [t′] [u′]))
            (neLvl [u′]) → Levelₜ₌ _ _
              (id (maxᵘⱼ (sucᵘⱼ ⊢t′) ⊢u′))
              (id (maxᵘⱼ ⊢u′ ⊢t))
              (neLvl (maxᵘ-comm²ᵣ [t′] (symLevel (redLevel t⇒ [t])) [u′]))
      (neLvl [t′]) → ⊩Level≡-⇒* (id (maxᵘⱼ ⊢t′ ⊢u)) (maxᵘ-substˡ* u⇒ ⊢t) $
        case propu of λ where
          zeroᵘᵣ → ⊩Level≡-⇒* (id (maxᵘⱼ ⊢t′ ⊢u)) (maxᵘ-zeroˡ ⊢t ⇨ t⇒)
            (⊩maxᵘ-zeroʳ′ (⊩neLvl [t′]) u⇒)
          (sucᵘᵣ {k = u′} [u′]) →
            let ⊢u′ = escapeLevel [u′]
            in Levelₜ₌ _ _ (id (maxᵘⱼ ⊢t′ ⊢u)) (maxᵘ-substʳ* ⊢u′ t⇒)
              (sym (neLvl (maxᵘ-comm²ᵣ [u′] (symLevel (redLevel u⇒ [u])) [t′])))
          (neLvl [u′]) →
            Levelₜ₌ _ _ (id (maxᵘⱼ ⊢t′ ⊢u)) (id (maxᵘⱼ ⊢u′ ⊢t))
              (neLvl (maxᵘ-comm¹ᵣ [t′] (symLevel (redLevel t⇒ [t])) [u′] (redLevel u⇒ [u])))

opaque

  -- Idempotence for maxᵘ.

  ⊩maxᵘ-idem :
    Γ ⊩Level t ∷Level →
    Γ ⊩Level t maxᵘ t ≡ t ∷Level
  ⊩maxᵘ-idem {t} [t]@(Levelₜ t′ t⇒ propt) =
    let
      ⊢t = escapeLevel [t]
      ⊢Γ = wfTerm ⊢t
      ⊢t′ = escape-Level-prop ⊢Γ propt
    in ⊩Level≡-⇒* (maxᵘ-substˡ* t⇒ ⊢t) t⇒ $
      case propt of λ where
        zeroᵘᵣ → redLevel′ (maxᵘ-zeroˡ ⊢t ⇨ t⇒) (⊩zeroᵘ ⊢Γ)
        (sucᵘᵣ [t′]) →
          let ⊢t′ = escapeLevel [t′]
          in ⊩Level≡-⇒*
            (maxᵘ-substʳ* ⊢t′ t⇒ ⇨∷* redMany (maxᵘ-sucᵘ ⊢t′ ⊢t′))
            (id (sucᵘⱼ ⊢t′))
            (⊩sucᵘ≡sucᵘ (⊩maxᵘ-idem [t′]))
        (neLvl [t′]) → Levelₜ₌ _ _
          (id (maxᵘⱼ ⊢t′ ⊢t))
          (id ⊢t′)
          (neLvl (maxᵘ-idemᵣ [t′] (symLevel (redLevel t⇒ [t]))))

opaque

  -- Subsumption for maxᵘ.

  ⊩maxᵘ-sub′ :
    Γ ⊢ u ⇒* sucᵘ t ∷ Level →
    Γ ⊩Level t ∷Level →
    Γ ⊩Level t maxᵘ u ≡ u ∷Level
  ⊩maxᵘ-sub′ {t} u⇒ [t]@(Levelₜ t′ t⇒ propt) =
    let
      ⊢t = escapeLevel [t]
      ⊢Γ = wfTerm ⊢t
      ⊢t′ = escape-Level-prop ⊢Γ propt
      ⊢u = redFirst*Term u⇒
    in ⊩Level≡-⇒* (maxᵘ-substˡ* t⇒ ⊢u) (id ⊢u) $
      case propt of λ where
        zeroᵘᵣ →
          redLevel′ (redMany (maxᵘ-zeroˡ ⊢u)) (⊩Level-⇒* u⇒ (⊩sucᵘ [t]))
        (sucᵘᵣ {k = t′} [t′]) →
          let ⊢t′ = escapeLevel [t′]
          in ⊩Level≡-⇒* (maxᵘ-substʳ* ⊢t′ u⇒ ⇨∷* redMany (maxᵘ-sucᵘ ⊢t′ ⊢t)) u⇒ (⊩sucᵘ≡sucᵘ (⊩maxᵘ-sub′ t⇒ [t′]))
        (neLvl x) → Levelₜ₌ _ _ (id (maxᵘⱼ ⊢t′ ⊢u)) u⇒ $
          trans (neLvl (maxᵘˡᵣ (reflneLevel-prop x) (⊩Level≡-⇒* u⇒ (id (sucᵘⱼ ⊢t′)) (⊩sucᵘ≡sucᵘ (redLevel t⇒ [t])))))
            (trans (maxᵘ-subᵣ x (⊩maxᵘ-idem (⊩neLvl x)))
              (sucᵘᵣ (symLevel (redLevel t⇒ [t]))))

  ⊩maxᵘ-sub :
    Γ ⊩Level t ∷Level →
    Γ ⊩Level t maxᵘ sucᵘ t ≡ sucᵘ t ∷Level
  ⊩maxᵘ-sub [t] = ⊩maxᵘ-sub′ (id (sucᵘⱼ (escapeLevel [t]))) [t]

-- Well-formedness for neutrals in WHNF and levels

opaque

  wf-neNf : Γ ⊩neNf t ≡ u ∷ A → Γ ⊩neNf t ≡ t ∷ A × Γ ⊩neNf u ≡ u ∷ A
  wf-neNf t≡u =
      transEqTermNe t≡u (symNeutralTerm t≡u)
    , transEqTermNe (symNeutralTerm t≡u) t≡u

opaque

  wf-neLevel-prop : neLevel-prop Γ t → ⊢ Γ
  wf-neLevel-prop (maxᵘˡᵣ x₁ x₂) = wf-neLevel-prop x₁
  wf-neLevel-prop (maxᵘʳᵣ x₁ x₂) = wf-neLevel-prop x₂
  wf-neLevel-prop (ne (neNfₜ₌ _ neK neM k≡m)) = wfEqTerm (≅ₜ-eq (~-to-≅ₜ k≡m))

opaque mutual

  wf-Level-eq : Γ ⊩Level t ≡ u ∷Level → Γ ⊩Level t ∷Level × Γ ⊩Level u ∷Level
  wf-Level-eq (Levelₜ₌ k k′ d d′ prop) =
    let x , y = wf-[Level]-prop prop
    in Levelₜ k d x , Levelₜ k′ d′ y

  wf-[Level]-prop : [Level]-prop Γ t u → Level-prop Γ t × Level-prop Γ u
  wf-[Level]-prop zeroᵘᵣ = zeroᵘᵣ , zeroᵘᵣ
  wf-[Level]-prop (sucᵘᵣ x) = let a , b = wf-Level-eq x in sucᵘᵣ a , sucᵘᵣ b
  wf-[Level]-prop (maxᵘ-subᵣ [t] y) =
    let _ , [k′] = wf-Level-eq y
    in neLvl (maxᵘˡᵣ [t] (⊩sucᵘ [k′])) , sucᵘᵣ [k′]
  wf-[Level]-prop (neLvl t≡u) = let [t] , [u] = wf-[neLevel]-prop t≡u in neLvl [t] , neLvl [u]
  wf-[Level]-prop (sym u≡t) =
    let [u] , [t] = wf-[Level]-prop u≡t
    in [t] , [u]
  wf-[Level]-prop (trans x y) =
    let [t] , _ = wf-[Level]-prop x
        _ , [u] = wf-[Level]-prop y
    in [t] , [u]

  wf-[neLevel]-prop : [neLevel]-prop Γ t u → neLevel-prop Γ t × neLevel-prop Γ u
  wf-[neLevel]-prop (maxᵘˡᵣ k₁≡k₁′ k₂≡k₂′) =
    let [k₁] , [k₁′] = wf-[neLevel]-prop k₁≡k₁′
        [k₂] , [k₂′] = wf-Level-eq k₂≡k₂′
    in maxᵘˡᵣ [k₁] [k₂] , maxᵘˡᵣ [k₁′] [k₂′]
  wf-[neLevel]-prop (maxᵘʳᵣ k₁≡k₁′ k₂≡k₂′) =
    let [k₁] , [k₁′] = wf-Level-eq k₁≡k₁′
        [k₂] , [k₂′] = wf-[neLevel]-prop k₂≡k₂′
    in maxᵘʳᵣ [k₁] [k₂] , maxᵘʳᵣ [k₁′] [k₂′]
  wf-[neLevel]-prop (maxᵘ-zeroʳᵣ [k]) =
    maxᵘˡᵣ [k] (Levelₜ _ (id (zeroᵘⱼ (wf-neLevel-prop [k]))) zeroᵘᵣ) , [k]
  wf-[neLevel]-prop (maxᵘ-assoc¹ᵣ [t] [u] [v]) =
    maxᵘˡᵣ (maxᵘˡᵣ [t] [u]) [v] , maxᵘˡᵣ [t] (⊩maxᵘ [u] [v])
  wf-[neLevel]-prop (maxᵘ-assoc²ᵣ [t] [u] [v]) =
    maxᵘˡᵣ (maxᵘʳᵣ [t] [u]) [v] , maxᵘʳᵣ [t] (maxᵘˡᵣ [u] [v])
  wf-[neLevel]-prop (maxᵘ-assoc³ᵣ [t] [u] [v]) =
    maxᵘʳᵣ (⊩maxᵘ [t] [u]) [v] , maxᵘʳᵣ [t] (maxᵘʳᵣ [u] [v])
  wf-[neLevel]-prop (maxᵘ-comm¹ᵣ [t₁] d [u₂] d′) =
    let [u₁] , _ = wf-Level-eq d′
        _ , [t₂] = wf-Level-eq d
    in maxᵘˡᵣ [t₁] [u₁] , maxᵘˡᵣ [u₂] [t₂]
  wf-[neLevel]-prop (maxᵘ-comm²ᵣ [t₁] d [u]) =
    let _ , [t₂] = wf-Level-eq d
    in maxᵘʳᵣ [t₁] [u] , maxᵘˡᵣ [u] [t₂]
  wf-[neLevel]-prop (maxᵘ-idemᵣ [u] y) =
    let _ , [t₂] = wf-Level-eq y
    in maxᵘˡᵣ [u] [t₂] , [u]
  wf-[neLevel]-prop (ne x) =
    let a , b = wf-neNf x
    in ne a , ne b

opaque

  -- Left congruence for maxᵘ.

  private
    ⊩maxᵘ-congʳ-⇒* :
      ∀ {t u u′} →
      Level-prop Γ t →
      Γ ⊩Level u′ ∷Level →
      Γ ⊢ u ⇒* u′ ∷ Level →
      Γ ⊩Level t maxᵘ u ≡ t maxᵘ u′ ∷Level
    ⊩maxᵘ-congʳ-⇒* zeroᵘᵣ [u′] u⇒ =
      ⊩Level≡-⇒*
        (redMany (maxᵘ-zeroˡ (redFirst*Term u⇒)))
        (redMany (maxᵘ-zeroˡ (escapeLevel [u′])))
        (redLevel′ u⇒ [u′])
    ⊩maxᵘ-congʳ-⇒* (sucᵘᵣ x) [u′] u⇒ =
      redLevel′ (maxᵘ-substʳ* (escapeLevel x) u⇒) (⊩maxᵘ (⊩sucᵘ x) [u′])
    ⊩maxᵘ-congʳ-⇒* (neLvl x) [u′] u⇒ =
      ⊩[neLvl] (maxᵘˡᵣ (reflneLevel-prop x) (redLevel′ u⇒ [u′]))

  mutual
    ⊩maxᵘ-congˡ-prop :
      [Level]-prop Γ t₁′ t₂′ →
      Γ ⊩Level u ∷Level →
      Γ ⊩Level t₁′ maxᵘ u ≡ t₂′ maxᵘ u ∷Level
    ⊩maxᵘ-congˡ-prop zeroᵘᵣ [u] =
      let ⊢u = escapeLevel [u]
          d = redMany (maxᵘ-zeroˡ ⊢u)
      in ⊩Level≡-⇒* d d (reflLevel [u])
    ⊩maxᵘ-congˡ-prop (sucᵘᵣ x) [u]@(Levelₜ u′ u⇒ propu) =
      let _ , ⊢k , ⊢k′ = wf-⊢≡∷ (≅ₜ-eq (escapeLevelEq x))
      in ⊩Level≡-⇒* (maxᵘ-substʳ* ⊢k u⇒) (maxᵘ-substʳ* ⊢k′ u⇒) $
        case propu of λ where
          zeroᵘᵣ → ⊩Level≡-⇒*
            (redMany (maxᵘ-zeroʳ ⊢k))
            (redMany (maxᵘ-zeroʳ ⊢k′))
            (⊩sucᵘ≡sucᵘ x)
          (sucᵘᵣ y) →
            let ⊢u′ = escapeLevel y
            in ⊩Level≡-⇒*
              (redMany (maxᵘ-sucᵘ ⊢k ⊢u′))
              (redMany (maxᵘ-sucᵘ ⊢k′ ⊢u′))
              (⊩sucᵘ≡sucᵘ (⊩maxᵘ-congˡ x y))
          (neLvl y) → ⊩[neLvl] (maxᵘʳᵣ x (reflneLevel-prop y))
    ⊩maxᵘ-congˡ-prop {Γ} {u} t₁′≡t₂′@(maxᵘ-subᵣ {k} {k′} [k] k≤k′) [u]@(Levelₜ u′ u⇒ propu) =
      let _ , [k′] = wf-Level-eq k≤k′
          ⊢k = escape-neLevel-prop [k]
          ⊢k′ = escapeLevel [k′]
          [k′+1] = ⊩sucᵘ [k′]
          [k⊔k′+1] = ⊩maxᵘ (⊩neLvl [k]) [k′+1]
          ⊢Γ = wfTerm (redFirst*Term u⇒)
      in case propu of λ where
        zeroᵘᵣ →
          transEqTermLevel (⊩maxᵘ-zeroʳ′ [k⊔k′+1] u⇒) $
            transEqTermLevel (⊩[Lvl] ⊢Γ t₁′≡t₂′) $
            symLevel (⊩maxᵘ-zeroʳ′ (⊩sucᵘ [k′]) u⇒)
        (sucᵘᵣ {k = u′} [u′]) →
          let ⊢u′ = escapeLevel [u′]
              d : Γ ⊢ sucᵘ k′ maxᵘ u ⇒* sucᵘ (k′ maxᵘ u′) ∷ Level
              d = maxᵘ-substʳ* ⊢k′ u⇒ ⇨∷* redMany (maxᵘ-sucᵘ ⊢k′ ⊢u′)
          in
            -- (k ⊔ sucᵘ k′) ⊔ u
            transEqTermLevel (⊩maxᵘ-assoc (⊩neLvl [k]) (⊩sucᵘ [k′]) [u]) $
            -- k ⊔ (sucᵘ k′ ⊔ u)
            transEqTermLevel (⊩maxᵘ-congʳ-⇒* (neLvl [k]) (⊩sucᵘ (⊩maxᵘ [k′] [u′])) d) $
            -- k ⊔ sucᵘ (k′ ⊔ u′)
            Levelₜ₌ _ _ (id (maxᵘⱼ ⊢k (sucᵘⱼ (maxᵘⱼ ⊢k′ ⊢u′)))) d
              (maxᵘ-subᵣ [k] (transEqTermLevel
                -- k ⊔ (k′ ⊔ u′)
                (symLevel (⊩maxᵘ-assoc (⊩neLvl [k]) [k′] [u′]))
                -- (k ⊔ k′) ⊔ u′
                (⊩maxᵘ-congˡ k≤k′ [u′])))
                -- k′ ⊔ u′
            -- sucᵘ k′ ⊔ u
        (neLvl [u′]) →
          transEqTermLevel (⊩maxᵘ-comm (⊩maxᵘ (⊩neLvl [k]) (⊩sucᵘ [k′])) [u]) $
            transEqTermLevel (Levelₜ₌ _ _
              (maxᵘ-substˡ* u⇒ (maxᵘⱼ ⊢k (sucᵘⱼ ⊢k′)))
              (maxᵘ-substˡ* u⇒ (sucᵘⱼ ⊢k′))
              (neLvl (maxᵘˡᵣ (reflneLevel-prop [u′]) (⊩[Lvl] (wfTerm ⊢k) t₁′≡t₂′)))) $
            ⊩maxᵘ-comm [u] (⊩sucᵘ [k′])
    ⊩maxᵘ-congˡ-prop (neLvl x) [u] =
      ⊩[neLvl] (maxᵘˡᵣ x (reflLevel [u]))
    ⊩maxᵘ-congˡ-prop (sym t₁′≡t₂′) [u] =
      symLevel (⊩maxᵘ-congˡ-prop t₁′≡t₂′ [u])
    ⊩maxᵘ-congˡ-prop (trans t₁′≡t₂′ t₂′≡t₃′) [u] =
      transEqTermLevel (⊩maxᵘ-congˡ-prop t₁′≡t₂′ [u]) (⊩maxᵘ-congˡ-prop t₂′≡t₃′ [u])

    ⊩maxᵘ-congˡ :
      Γ ⊩Level t₁ ≡ t₂ ∷Level →
      Γ ⊩Level u ∷Level →
      Γ ⊩Level t₁ maxᵘ u ≡ t₂ maxᵘ u ∷Level
    ⊩maxᵘ-congˡ t₁≡t₂@(Levelₜ₌ t₁′ t₂′ t₁⇒ t₂⇒ prop) [u] =
      let ⊢u = escapeLevel [u]
      in ⊩Level≡-⇒* (maxᵘ-substˡ* t₁⇒ ⊢u) (maxᵘ-substˡ* t₂⇒ ⊢u)
        (⊩maxᵘ-congˡ-prop prop [u])

opaque

  -- Right congruence for maxᵘ.

  ⊩maxᵘ-congʳ :
    Γ ⊩Level t ∷Level →
    Γ ⊩Level u₁ ≡ u₂ ∷Level →
    Γ ⊩Level t maxᵘ u₁ ≡ t maxᵘ u₂ ∷Level
  ⊩maxᵘ-congʳ [t] u₁≡u₂ =
    let [u₁] , [u₂] = wf-Level-eq u₁≡u₂
    in transEqTermLevel (⊩maxᵘ-comm [t] [u₁]) $
       transEqTermLevel (⊩maxᵘ-congˡ u₁≡u₂ [t]) $
       ⊩maxᵘ-comm [u₂] [t]

opaque

  -- Congruence for maxᵘ.

  ⊩maxᵘ≡maxᵘ :
    Γ ⊩Level t₁ ≡ t₂ ∷Level →
    Γ ⊩Level u₁ ≡ u₂ ∷Level →
    Γ ⊩Level t₁ maxᵘ u₁ ≡ t₂ maxᵘ u₂ ∷Level
  ⊩maxᵘ≡maxᵘ t₁≡t₂ u₁≡u₂ =
    let [t₁] , [t₂] = wf-Level-eq t₁≡t₂
        [u₁] , [u₂] = wf-Level-eq u₁≡u₂
    in transEqTermLevel (⊩maxᵘ-congʳ [t₁] u₁≡u₂) (⊩maxᵘ-congˡ t₁≡t₂ [u₂])

------------------------------------------------------------------------
-- Level reflection

-- Irrelevance of the reducibility proof for level reflection.

opaque
  unfolding ↑ⁿ_

  mutual
    ↑ⁿ-irrelevance
      : ∀ {t} ([t] : Γ ⊩Level t ∷Level) ([t]′ : Γ ⊩Level t ∷Level)
      → ↑ⁿ [t] PE.≡ ↑ⁿ [t]′
    ↑ⁿ-irrelevance (Levelₜ _ t⇒ [t]) (Levelₜ _ t⇒′ [t]′) =
      case whrDet*Term (t⇒ , level [t]) (t⇒′ , level [t]′) of λ {
        PE.refl →
      ↑ⁿ-prop-irrelevance [t] [t]′ }

    ↑ⁿ-prop-irrelevance
      : ∀ {t} ([t] : Level-prop Γ t) ([t]′ : Level-prop Γ t)
      → ↑ⁿ-prop [t] PE.≡ ↑ⁿ-prop [t]′
    ↑ⁿ-prop-irrelevance zeroᵘᵣ zeroᵘᵣ = PE.refl
    ↑ⁿ-prop-irrelevance (sucᵘᵣ x) (sucᵘᵣ y) = PE.cong 1+ (↑ⁿ-irrelevance x y)
    ↑ⁿ-prop-irrelevance (neLvl x) (neLvl y) = ↑ⁿ-neprop-irrelevance x y
    ↑ⁿ-prop-irrelevance zeroᵘᵣ (neLvl (ne (neNfₜ₌ _ () neM k≡m)))
    ↑ⁿ-prop-irrelevance (sucᵘᵣ x) (neLvl (ne (neNfₜ₌ _ () neM k≡m)))
    ↑ⁿ-prop-irrelevance (neLvl (ne (neNfₜ₌ _ () neM k≡m))) zeroᵘᵣ
    ↑ⁿ-prop-irrelevance (neLvl (ne (neNfₜ₌ _ () neM k≡m))) (sucᵘᵣ x₁)

    ↑ⁿ-neprop-irrelevance
      : ∀ {t} ([t] : neLevel-prop Γ t) ([t]′ : neLevel-prop Γ t)
      → ↑ⁿ-neprop [t] PE.≡ ↑ⁿ-neprop [t]′
    ↑ⁿ-neprop-irrelevance (maxᵘˡᵣ x x₁) (maxᵘˡᵣ y x₂) =
      PE.cong₂ _⊔_ (↑ⁿ-neprop-irrelevance x y) (↑ⁿ-irrelevance x₁ x₂)
    ↑ⁿ-neprop-irrelevance (maxᵘʳᵣ x x₁) (maxᵘʳᵣ x₂ y) =
      PE.cong₂ _⊔_ (PE.cong 1+ (↑ⁿ-irrelevance x x₂)) (↑ⁿ-neprop-irrelevance x₁ y)
    ↑ⁿ-neprop-irrelevance (ne x) (ne x₁) = PE.refl
    ↑ⁿ-neprop-irrelevance (maxᵘˡᵣ x x₁) (maxᵘʳᵣ x₂ y) = case nelevel x of λ { (ne ()) }
    ↑ⁿ-neprop-irrelevance (maxᵘˡᵣ x x₁) (ne (neNfₜ₌ _ () neM k≡m))
    ↑ⁿ-neprop-irrelevance (maxᵘʳᵣ x x₁) (maxᵘˡᵣ y x₂) = case nelevel y of λ { (ne ()) }
    ↑ⁿ-neprop-irrelevance (maxᵘʳᵣ x x₁) (ne (neNfₜ₌ _ () neM k≡m))
    ↑ⁿ-neprop-irrelevance (ne (neNfₜ₌ _ () neM k≡m)) (maxᵘˡᵣ y x₁)
    ↑ⁿ-neprop-irrelevance (ne (neNfₜ₌ _ () neM k≡m)) (maxᵘʳᵣ x₁ y)

↑ᵘ-irrelevance
  : ∀ {t} {[t] : Γ ⊩Level t ∷Level} {[t]′ : Γ ⊩Level t ∷Level}
  → ↑ᵘ [t] PE.≡ ↑ᵘ [t]′
↑ᵘ-irrelevance {[t]} {[t]′} = PE.cong 0ᵘ+_ (↑ⁿ-irrelevance [t] [t]′)

opaque
  unfolding ↑ⁿ_

  -- Level reflection sends zeroᵘ to 0ᵘ.

  ↑ⁿ-prop-zeroᵘ : ([0] : Level-prop Γ zeroᵘ) → ↑ⁿ-prop [0] PE.≡ 0
  ↑ⁿ-prop-zeroᵘ zeroᵘᵣ = PE.refl
  ↑ⁿ-prop-zeroᵘ (neLvl n) = case nelevel n of λ { (ne ()) }

  ↑ⁿ-zeroᵘ : ([0] : Γ ⊩Level zeroᵘ ∷Level) → ↑ⁿ [0] PE.≡ 0
  ↑ⁿ-zeroᵘ (Levelₜ _ 0⇒ prop) with whnfRed*Term 0⇒ zeroᵘₙ
  ... | PE.refl = ↑ⁿ-prop-zeroᵘ prop

  ↑ᵘ-zeroᵘ : ([0] : Γ ⊩Level zeroᵘ ∷Level) → ↑ᵘ [0] PE.≡ 0ᵘ
  ↑ᵘ-zeroᵘ [0] = PE.cong 0ᵘ+_ (↑ⁿ-zeroᵘ [0])

opaque
  unfolding ↑ⁿ_ ⊩sucᵘ

  -- Level reflection sends sucᵘ to 1+.

  ↑ⁿ-prop-sucᵘ
    : ∀ {t} ([t+1] : Level-prop Γ (sucᵘ t))
    → ∃ λ ([t] : Γ ⊩Level t ∷Level) → ↑ⁿ-prop [t+1] PE.≡ 1+ (↑ⁿ [t])
  ↑ⁿ-prop-sucᵘ (sucᵘᵣ x) = x , PE.refl
  ↑ⁿ-prop-sucᵘ (neLvl n) = case nelevel n of λ { (ne ()) }

  ↑ⁿ-sucᵘ
    : ∀ {t} ([t] : Γ ⊩Level t ∷Level) ([t+1] : Γ ⊩Level sucᵘ t ∷Level)
    → ↑ⁿ [t+1] PE.≡ 1+ (↑ⁿ [t])
  ↑ⁿ-sucᵘ [t]@record{} [t+1] = ↑ⁿ-irrelevance [t+1] (⊩sucᵘ [t])

opaque
  unfolding ↑ⁿ_ ⊩maxᵘ

  -- Level reflection sends maxᵘ to ⊔ᵘ.

  ↑ⁿ-maxᵘ :
    ([t] : Γ ⊩Level t ∷Level) →
    ([u] : Γ ⊩Level u ∷Level) →
    ↑ⁿ ⊩maxᵘ [t] [u] PE.≡ ↑ⁿ [t] ⊔ ↑ⁿ [u]
  ↑ⁿ-maxᵘ [t]@(Levelₜ t′ t⇒ zeroᵘᵣ) [u]@(Levelₜ u′ u⇒ propu) = PE.refl
  ↑ⁿ-maxᵘ [t]@(Levelₜ t′ t⇒ (sucᵘᵣ x)) [u]@(Levelₜ u′ u⇒ zeroᵘᵣ) = PE.refl
  ↑ⁿ-maxᵘ [t]@(Levelₜ t′ t⇒ (sucᵘᵣ x)) [u]@(Levelₜ u′ u⇒ (sucᵘᵣ x₁)) = PE.cong 1+ (↑ⁿ-maxᵘ x x₁)
  ↑ⁿ-maxᵘ [t]@(Levelₜ t′ t⇒ (sucᵘᵣ x)) [u]@(Levelₜ u′ u⇒ (neLvl x₁)) = PE.refl
  ↑ⁿ-maxᵘ [t]@(Levelₜ t′ t⇒ (neLvl x)) [u]@(Levelₜ u′ u⇒ propu) = PE.refl

  ↑ᵘ-maxᵘ :
    ([t] : Γ ⊩Level t ∷Level) →
    ([u] : Γ ⊩Level u ∷Level) →
    ↑ᵘ ⊩maxᵘ [t] [u] PE.≡ ↑ᵘ [t] ⊔ᵘ ↑ᵘ [u]
  ↑ᵘ-maxᵘ [t] [u] = PE.cong 0ᵘ+_ (↑ⁿ-maxᵘ [t] [u])

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
  <ᵘ-sucᵘ {[t]} {[t+1]} = <ᵘ-nat (<′-sucᵘ [t] [t+1])

opaque

  -- t maxᵘ u is an upper bound of t and u.

  ≤ᵘ-maxᵘʳ :
    {⊩t ⊩t′ : Γ ⊩Level t ∷Level} →
    {⊩u : Γ ⊩Level u ∷Level} →
    ↑ᵘ ⊩t ≤ᵘ ↑ᵘ ⊩maxᵘ ⊩t′ ⊩u
  ≤ᵘ-maxᵘʳ {⊩t′} {⊩u} = PE.subst₂ (_≤ᵘ_) ↑ᵘ-irrelevance (PE.sym $ ↑ᵘ-maxᵘ ⊩t′ ⊩u) ≤ᵘ⊔ᵘʳ

  ≤ᵘ-maxᵘˡ :
    {⊩t : Γ ⊩Level t ∷Level} →
    {⊩u ⊩u′ : Γ ⊩Level u ∷Level} →
    ↑ᵘ ⊩u ≤ᵘ ↑ᵘ ⊩maxᵘ ⊩t ⊩u′
  ≤ᵘ-maxᵘˡ {⊩t} {⊩u′} = PE.subst₂ (_≤ᵘ_) ↑ᵘ-irrelevance (PE.sym $ ↑ᵘ-maxᵘ ⊩t ⊩u′) ≤ᵘ⊔ᵘˡ

-- Level reflection preserves equality.

opaque
  unfolding ↑ⁿ_ ⊩sucᵘ

  mutual
    ↑ⁿ-cong
      : ∀ {t u} ([t] : Γ ⊩Level t ∷Level) ([u] : Γ ⊩Level u ∷Level)
      → Γ ⊩Level t ≡ u ∷Level
      → ↑ⁿ [t] PE.≡ ↑ⁿ [u]
    ↑ⁿ-cong (Levelₜ _ t⇒ [t]) (Levelₜ _ u⇒ [u]) (Levelₜ₌ _ _ t⇒′ u⇒′ t≡u) =
      case whrDet*Term (t⇒ , level [t]) (t⇒′ , lsplit t≡u .proj₁) of λ {
        PE.refl →
      case whrDet*Term (u⇒ , level [u]) (u⇒′ , lsplit t≡u .proj₂) of λ {
        PE.refl →
      ↑ⁿ-prop-cong [t] [u] t≡u }}

    ↑ⁿ-prop-cong
      : ∀ {t u} ([t] : Level-prop Γ t) ([u] : Level-prop Γ u)
      → [Level]-prop Γ t u
      → ↑ⁿ-prop [t] PE.≡ ↑ⁿ-prop [u]
    ↑ⁿ-prop-cong x y zeroᵘᵣ = PE.trans (↑ⁿ-prop-zeroᵘ x) (PE.sym (↑ⁿ-prop-zeroᵘ y))
    ↑ⁿ-prop-cong x y (sucᵘᵣ z) =
      let x′ , x≡ = ↑ⁿ-prop-sucᵘ x
          y′ , y≡ = ↑ⁿ-prop-sucᵘ y
      in PE.trans x≡ $ PE.trans (PE.cong 1+ (↑ⁿ-cong x′ y′ z)) $ PE.sym y≡
    ↑ⁿ-prop-cong (neLvl [t⊔1+u]) (sucᵘᵣ [u]@record{}) (maxᵘ-subᵣ {k = t} {k′ = u} [t] t⊔u≡u) =
      PE.trans
        (↑ⁿ-neprop-irrelevance [t⊔1+u] (maxᵘˡᵣ [t] (⊩sucᵘ [u])))
        (m≤n⇒m⊔n≡n (m≤n⇒m≤1+n (m⊔n≡n⇒m≤n (↑ⁿ-cong (⊩neLvl (maxᵘˡᵣ [t] [u])) [u] t⊔u≡u))))
    ↑ⁿ-prop-cong (neLvl x) (neLvl y) (neLvl z) = ↑ⁿ-neprop-cong x y z
    ↑ⁿ-prop-cong x y (sym z) = PE.sym (↑ⁿ-prop-cong y x z)
    ↑ⁿ-prop-cong x y (trans z z₁) =
      let _ , [k′] = wf-[Level]-prop z
      in PE.trans (↑ⁿ-prop-cong x [k′] z) (↑ⁿ-prop-cong [k′] y z₁)
    -- Absurd cases
    ↑ⁿ-prop-cong (neLvl x) (neLvl y) (maxᵘ-subᵣ _ _) = case nelevel y of λ { (ne ()) }
    ↑ⁿ-prop-cong zeroᵘᵣ y (neLvl n) = case nelsplit n .proj₁ of λ { (ne ()) }
    ↑ⁿ-prop-cong (sucᵘᵣ x) y (neLvl n) = case nelsplit n .proj₁ of λ { (ne ()) }
    ↑ⁿ-prop-cong (neLvl _) zeroᵘᵣ (neLvl n) = case nelsplit n .proj₂ of λ { (ne ()) }
    ↑ⁿ-prop-cong (neLvl _) (sucᵘᵣ _) (neLvl n) = case nelsplit n .proj₂ of λ { (ne ()) }

    ↑ⁿ-neprop-cong
      : ∀ {t u} ([t] : neLevel-prop Γ t) ([u] : neLevel-prop Γ u)
      → [neLevel]-prop Γ t u
      → ↑ⁿ-neprop [t] PE.≡ ↑ⁿ-neprop [u]
    ↑ⁿ-neprop-cong (maxᵘˡᵣ x₄ x₅) (maxᵘˡᵣ y x₇) (maxᵘˡᵣ z x₃) =
      PE.cong₂ _⊔_ (↑ⁿ-neprop-cong x₄ y z) (↑ⁿ-cong x₅ x₇ x₃)
    ↑ⁿ-neprop-cong (maxᵘʳᵣ x x₁) (maxᵘʳᵣ x₂ y) (maxᵘʳᵣ x₃ z) =
      PE.cong₂ _⊔_ (PE.cong 1+ (↑ⁿ-cong x x₂ x₃)) (↑ⁿ-neprop-cong x₁ y z)
    ↑ⁿ-neprop-cong (maxᵘˡᵣ x x₁) y (maxᵘ-zeroʳᵣ x₂) =
      PE.trans (PE.cong₂ _⊔_ (↑ⁿ-neprop-irrelevance x y) (↑ⁿ-zeroᵘ x₁)) (⊔-identityʳ _)
    ↑ⁿ-neprop-cong (ne x) (ne x₂) (ne x₁) = PE.refl
    ↑ⁿ-neprop-cong (maxᵘˡᵣ (maxᵘˡᵣ x x₅) x₃) (maxᵘˡᵣ y x₄) (maxᵘ-assoc¹ᵣ z x₁ x₂) =
      PE.trans
        (⊔-assoc (↑ⁿ-neprop x) (↑ⁿ x₅) (↑ⁿ x₃))
        (PE.cong₂ _⊔_ (↑ⁿ-neprop-irrelevance x y) (PE.trans
          (PE.sym (↑ⁿ-maxᵘ x₅ x₃))
          (↑ⁿ-irrelevance (⊩maxᵘ x₅ x₃) x₄)))
    ↑ⁿ-neprop-cong (maxᵘˡᵣ (maxᵘʳᵣ x x₄) x₃) (maxᵘʳᵣ x₅ (maxᵘˡᵣ y x₆)) (maxᵘ-assoc²ᵣ x₁ z x₂) =
      PE.trans
        (⊔-assoc (1+ (↑ⁿ x)) (↑ⁿ-neprop x₄) (↑ⁿ x₃))
        (PE.cong₂ _⊔_ (PE.cong 1+ (↑ⁿ-irrelevance x x₅))
          (PE.cong₂ _⊔_ (↑ⁿ-neprop-irrelevance x₄ y)
            (↑ⁿ-irrelevance x₃ x₆)))
    ↑ⁿ-neprop-cong (maxᵘʳᵣ x x₃) (maxᵘʳᵣ x₄ (maxᵘʳᵣ x₅ y)) (maxᵘ-assoc³ᵣ x₁ x₂ z) =
      PE.trans
        (PE.cong₂ _⊔_
          (PE.cong 1+ (PE.trans (↑ⁿ-irrelevance x (⊩maxᵘ x₄ x₅)) (↑ⁿ-maxᵘ x₄ x₅)))
          (↑ⁿ-neprop-irrelevance x₃ y))
        (⊔-assoc (1+ (↑ⁿ x₄)) (1+ (↑ⁿ x₅)) (↑ⁿ-neprop y))
    ↑ⁿ-neprop-cong (maxᵘˡᵣ x x₁) (maxᵘˡᵣ y x₂) (maxᵘ-comm¹ᵣ z d w d′) =
      PE.trans
        (⊔-comm (↑ⁿ-neprop x) (↑ⁿ x₁))
        (PE.cong₂ _⊔_ (↑ⁿ-cong x₁ (⊩neLvl y) d′) (↑ⁿ-cong (⊩neLvl x) x₂ d))
    ↑ⁿ-neprop-cong (maxᵘʳᵣ x@record{} x₁) (maxᵘˡᵣ y x₂) (maxᵘ-comm²ᵣ z d w) =
      PE.trans
        (⊔-comm (1+ (↑ⁿ x)) (↑ⁿ-neprop x₁))
        (PE.cong₂ _⊔_ (↑ⁿ-neprop-irrelevance x₁ y) (↑ⁿ-cong (⊩sucᵘ x) x₂ d))
    ↑ⁿ-neprop-cong (maxᵘˡᵣ x x₁) y (maxᵘ-idemᵣ z w) = PE.trans
      (PE.cong₂ _⊔_
        (↑ⁿ-neprop-irrelevance x y)
        (PE.sym (↑ⁿ-cong (⊩neLvl y) x₁ w)))
      (⊔-idem (↑ⁿ-neprop y))
    -- Absurd cases
    ↑ⁿ-neprop-cong (maxᵘˡᵣ _ _) (maxᵘʳᵣ _ _) (maxᵘˡᵣ z _) = case nelsplit z .proj₂ of λ { (ne ()) }
    ↑ⁿ-neprop-cong (maxᵘˡᵣ _ _) (ne (neNfₜ₌ _ () neM k≡m)) (maxᵘˡᵣ z x₃)
    ↑ⁿ-neprop-cong (maxᵘʳᵣ _ _) _ (maxᵘˡᵣ z _) = case nelsplit z .proj₁ of λ { (ne ()) }
    ↑ⁿ-neprop-cong (ne (neNfₜ₌ _ () neM k≡m)) _ (maxᵘˡᵣ _ _)
    ↑ⁿ-neprop-cong (maxᵘˡᵣ x _) _ (maxᵘʳᵣ _ _) = case nelevel x of λ { (ne ()) }
    ↑ⁿ-neprop-cong (maxᵘʳᵣ _ _) (maxᵘˡᵣ y _) (maxᵘʳᵣ _ _) = case nelevel y of λ { (ne ()) }
    ↑ⁿ-neprop-cong (maxᵘʳᵣ _ _) (ne (neNfₜ₌ _ () neM k≡m)) (maxᵘʳᵣ _ _)
    ↑ⁿ-neprop-cong (ne (neNfₜ₌ _ () neM k≡m)) _ (maxᵘʳᵣ _ _)
    ↑ⁿ-neprop-cong (maxᵘʳᵣ _ _) y (maxᵘ-zeroʳᵣ _) = case nelevel y of λ { (ne ()) }
    ↑ⁿ-neprop-cong (ne (neNfₜ₌ _ () neM k≡m)) _ (maxᵘ-zeroʳᵣ _)
    ↑ⁿ-neprop-cong (maxᵘˡᵣ _ _) _ (ne (neNfₜ₌ _ () neM k≡m))
    ↑ⁿ-neprop-cong (maxᵘʳᵣ _ _) _ (ne (neNfₜ₌ _ () neM k≡m))
    ↑ⁿ-neprop-cong (ne _) (maxᵘˡᵣ _ _) (ne (neNfₜ₌ _ neK () k≡m))
    ↑ⁿ-neprop-cong (ne _) (maxᵘʳᵣ _ _) (ne (neNfₜ₌ _ neK () k≡m))
    ↑ⁿ-neprop-cong (maxᵘˡᵣ (maxᵘʳᵣ x x₅) x₃) (maxᵘˡᵣ y x₄) (maxᵘ-assoc¹ᵣ z x₁ x₂) = case nelevel y of λ { (ne ()) }
    ↑ⁿ-neprop-cong (maxᵘˡᵣ (ne (neNfₜ₌ _ () neM k≡m)) x₃) (maxᵘˡᵣ y x₄) (maxᵘ-assoc¹ᵣ z x₁ x₂)
    ↑ⁿ-neprop-cong (maxᵘˡᵣ x x₃) (maxᵘʳᵣ x₄ y) (maxᵘ-assoc¹ᵣ z x₁ x₂) = case nelevel z of λ { (ne ()) }
    ↑ⁿ-neprop-cong (maxᵘˡᵣ x x₃) (ne (neNfₜ₌ _ () neM k≡m)) (maxᵘ-assoc¹ᵣ z x₁ x₂)
    ↑ⁿ-neprop-cong (ne (neNfₜ₌ _ () neM k≡m)) y (maxᵘ-assoc¹ᵣ z x₁ x₂)
    ↑ⁿ-neprop-cong (maxᵘˡᵣ (maxᵘˡᵣ x x₄) x₃) y (maxᵘ-assoc²ᵣ x₁ z x₂) = case nelevel x of λ { (ne ()) }
    ↑ⁿ-neprop-cong (maxᵘˡᵣ (maxᵘʳᵣ x x₄) x₃) (maxᵘˡᵣ y x₅) (maxᵘ-assoc²ᵣ x₁ z x₂) = case nelevel y of λ { (ne ()) }
    ↑ⁿ-neprop-cong (maxᵘˡᵣ (maxᵘʳᵣ x x₄) x₃) (maxᵘʳᵣ x₅ (maxᵘʳᵣ x₆ y)) (maxᵘ-assoc²ᵣ x₁ z x₂) = case nelevel x₄ of λ { (ne ()) }
    ↑ⁿ-neprop-cong (maxᵘˡᵣ (maxᵘʳᵣ x x₄) x₃) (maxᵘʳᵣ x₅ (ne (neNfₜ₌ _ () neM k≡m))) (maxᵘ-assoc²ᵣ x₁ z x₂)
    ↑ⁿ-neprop-cong (maxᵘˡᵣ (maxᵘʳᵣ x x₄) x₃) (ne (neNfₜ₌ _ () neM k≡m)) (maxᵘ-assoc²ᵣ x₁ z x₂)
    ↑ⁿ-neprop-cong (maxᵘˡᵣ (ne (neNfₜ₌ _ () neM k≡m)) x₃) y (maxᵘ-assoc²ᵣ x₁ z x₂)
    ↑ⁿ-neprop-cong (ne (neNfₜ₌ _ () neM k≡m)) y (maxᵘ-assoc²ᵣ x₁ z x₂)
    ↑ⁿ-neprop-cong (maxᵘˡᵣ x x₃) y (maxᵘ-assoc³ᵣ x₁ x₂ z) = case nelevel x of λ { (ne ()) }
    ↑ⁿ-neprop-cong (maxᵘʳᵣ x x₃) (maxᵘˡᵣ y x₄) (maxᵘ-assoc³ᵣ x₁ x₂ z) = case nelevel y of λ { (ne ()) }
    ↑ⁿ-neprop-cong (maxᵘʳᵣ x x₃) (maxᵘʳᵣ x₄ (maxᵘˡᵣ y x₅)) (maxᵘ-assoc³ᵣ x₁ x₂ z) = case nelevel y of λ { (ne ()) }
    ↑ⁿ-neprop-cong (maxᵘʳᵣ x x₃) (maxᵘʳᵣ x₄ (ne (neNfₜ₌ _ () neM k≡m))) (maxᵘ-assoc³ᵣ x₁ x₂ z)
    ↑ⁿ-neprop-cong (maxᵘʳᵣ x x₃) (ne (neNfₜ₌ _ () neM k≡m)) (maxᵘ-assoc³ᵣ x₁ x₂ z)
    ↑ⁿ-neprop-cong (ne (neNfₜ₌ _ () neM k≡m)) y (maxᵘ-assoc³ᵣ x₁ x₂ z)
    ↑ⁿ-neprop-cong (maxᵘˡᵣ x x₁) (maxᵘʳᵣ x₂ y) (maxᵘ-comm¹ᵣ z d w d′) = case nelevel w of λ { (ne ()) }
    ↑ⁿ-neprop-cong (maxᵘˡᵣ x x₁) (ne (neNfₜ₌ _ () neM k≡m)) (maxᵘ-comm¹ᵣ z d w d′)
    ↑ⁿ-neprop-cong (maxᵘʳᵣ x x₁) y (maxᵘ-comm¹ᵣ z d w d′) = case nelevel z of λ { (ne ()) }
    ↑ⁿ-neprop-cong (ne (neNfₜ₌ _ () neM k≡m)) y (maxᵘ-comm¹ᵣ z d w d′)
    ↑ⁿ-neprop-cong (maxᵘˡᵣ x x₁) y (maxᵘ-comm²ᵣ z d w) = case nelevel x of λ { (ne ()) }
    ↑ⁿ-neprop-cong (maxᵘʳᵣ x x₁) (maxᵘʳᵣ x₂ y) (maxᵘ-comm²ᵣ z d w) = case nelevel x₁ of λ { (ne ()) }
    ↑ⁿ-neprop-cong (maxᵘʳᵣ x x₁) (ne (neNfₜ₌ _ () neM k≡m)) (maxᵘ-comm²ᵣ z d w)
    ↑ⁿ-neprop-cong (ne (neNfₜ₌ _ () neM k≡m)) y (maxᵘ-comm²ᵣ z d w)
    ↑ⁿ-neprop-cong (maxᵘʳᵣ x x₁) y (maxᵘ-idemᵣ z w) = case nelevel y of λ { (ne ()) }
    ↑ⁿ-neprop-cong (ne (neNfₜ₌ _ () neM k≡m)) y (maxᵘ-idemᵣ z w)

↑ᵘ-cong
  : ∀ {t u} {[t] : Γ ⊩Level t ∷Level} {[u] : Γ ⊩Level u ∷Level}
  → Γ ⊩Level t ≡ u ∷Level
  → ↑ᵘ [t] PE.≡ ↑ᵘ [u]
↑ᵘ-cong {[t]} {[u]} t≡u = PE.cong 0ᵘ+_ (↑ⁿ-cong [t] [u] t≡u)

-- Level reflection preserves inequality.

↑ⁿ-cong-≤
  : ∀ {t u} {[t] : Γ ⊩Level t ∷Level} {[u] : Γ ⊩Level u ∷Level}
  → Γ ⊩Level t maxᵘ u ≡ u ∷Level
  → ↑ⁿ [t] ≤ ↑ⁿ [u]
↑ⁿ-cong-≤ {[t]} {[u]} t≤u =
  m⊔n≡n⇒m≤n
    (PE.trans (PE.sym (↑ⁿ-maxᵘ [t] [u]))
      (↑ⁿ-cong (⊩maxᵘ [t] [u]) [u] t≤u))

↑ᵘ-cong-≤
  : ∀ {t u} {[t] : Γ ⊩Level t ∷Level} {[u] : Γ ⊩Level u ∷Level}
  → Γ ⊩Level t maxᵘ u ≡ u ∷Level
  → ↑ᵘ [t] ≤ᵘ ↑ᵘ [u]
↑ᵘ-cong-≤ t≤u = ≤ᵘ-nat (≤⇒≤′ (↑ⁿ-cong-≤ t≤u))
