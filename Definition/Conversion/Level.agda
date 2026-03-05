------------------------------------------------------------------------
-- Some lemmas related to algorithmic conversion of levels.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Conversion.Level
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Conversion R
open import Definition.Conversion.Whnf R
open import Definition.Typed R
open import Definition.Typed.Properties R

open import Tools.Bool
open import Tools.Function
open import Tools.List
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    m n : Nat
    Γ : Cons m n
    t u : Term n
    d : Bool

-- Reification of level views as terms.

LevelAtom→Term : ∀ {Γ : Cons m n} → LevelAtom Γ → Term n
LevelAtom→Term zeroᵘ = zeroᵘ
LevelAtom→Term (ne {t} x) = t

Level⁺→Term : ∀ {Γ : Cons m n} → Level⁺ Γ → Term n
Level⁺→Term (n , a) = 1ᵘ+ⁿ n (LevelAtom→Term a)

Levelᵛ→Term : ∀ {Γ : Cons m n} → Levelᵛ Γ → Term n
Levelᵛ→Term L.[] = zeroᵘ
Levelᵛ→Term (l L.∷ xs) = Level⁺→Term l supᵘ Levelᵛ→Term xs

-- Reflexivity.

≡ⁿ-refl : ∀ {t} → Γ ⊢ t ~ t ↓ Level → ≡ⁿ Γ t t d
≡ⁿ-refl {d = false} t~t = ne≡ t~t
≡ⁿ-refl {d = true} t~t = ne≡' t~t

≤⁺-refl : ∀ (v : Level⁺ Γ) → ≤⁺ d v v
≤⁺-refl (n , zeroᵘ) = ≤-refl , zeroᵘ≤
≤⁺-refl (n , ne x) = ≤-refl , ne≤ (≡ⁿ-refl x)

≤ᵛ-refl : ∀ (v : Levelᵛ Γ) → ≤ᵛ d v v
≤ᵛ-refl L.[] = All.[]
≤ᵛ-refl (x L.∷ v) = Any.here (≤⁺-refl x) All.∷ All.map Any.there (≤ᵛ-refl v)

≡ᵛ-refl : ∀ (v : Levelᵛ Γ) → v ≡ᵛ v
≡ᵛ-refl v = ≤ᵛ-refl v , ≤ᵛ-refl v

-- Congruence for level successor.

≤⁺-suc : ∀ {u v : Level⁺ Γ} → ≤⁺ d u v → ≤⁺ d (suc⁺ u) (suc⁺ v)
≤⁺-suc (x , a) = s≤s x , a

≤⁺ᵛ-suc : ∀ {u : Level⁺ Γ} {v : Levelᵛ Γ} → ≤⁺ᵛ d u v → ≤⁺ᵛ d (suc⁺ u) (map-suc⁺ v)
≤⁺ᵛ-suc (Any.here px) = Any.here (≤⁺-suc px)
≤⁺ᵛ-suc (Any.there u≤v) = Any.there (≤⁺ᵛ-suc u≤v)

≤ᵛ-map-suc⁺ : ∀ {u v : Levelᵛ Γ} → ≤ᵛ d u v → ≤ᵛ d (map-suc⁺ u) (map-suc⁺ v)
≤ᵛ-map-suc⁺ All.[] = All.[]
≤ᵛ-map-suc⁺ (px All.∷ u≤v) = ≤⁺ᵛ-suc px All.∷ ≤ᵛ-map-suc⁺ u≤v

≤ᵛ-suc : ∀ {u v : Levelᵛ Γ} → ≤ᵛ d u v → ≤ᵛ d (sucᵛ u) (sucᵛ v)
≤ᵛ-suc u≤v = Any.here (≤⁺-refl _) All.∷ All.map Any.there (≤ᵛ-map-suc⁺ u≤v)

≡ᵛ-suc : ∀ {u v : Levelᵛ Γ} → u ≡ᵛ v → sucᵛ u ≡ᵛ sucᵛ v
≡ᵛ-suc (u≤v , v≤u) = ≤ᵛ-suc u≤v , ≤ᵛ-suc v≤u

-- Congruence for level supremum.

≤ᵛ-sup : ∀ {u u′ v v′ : Levelᵛ Γ} → ≤ᵛ d u v → ≤ᵛ d u′ v′ → ≤ᵛ d (supᵛ u u′) (supᵛ v v′)
≤ᵛ-sup u≤v u′≤v′ = All.++⁺ (All.map Any.++⁺ˡ u≤v) (All.map (Any.++⁺ʳ _) u′≤v′)

≡ᵛ-sup : ∀ {u u′ v v′ : Levelᵛ Γ} → u ≡ᵛ v → u′ ≡ᵛ v′ → supᵛ u u′ ≡ᵛ supᵛ v v′
≡ᵛ-sup (u≤v , v≤u) (u′≤v′ , v′≤u′) = ≤ᵛ-sup u≤v u′≤v′ , ≤ᵛ-sup v≤u v′≤u′

-- Syntactic equality of level views.

data _≡≡ᵃ_ {Γ : Cons m n} : LevelAtom Γ → LevelAtom Γ → Set a where
  zero : zeroᵘ ≡≡ᵃ zeroᵘ
  ne : ∀ {t} ([t] [t]′ : Γ ⊢ t ~ t ↓ Level) → ne [t] ≡≡ᵃ ne [t]′

_≡≡⁺_ : Level⁺ Γ → Level⁺ Γ → Set a
(n , a) ≡≡⁺ (m , b) = n PE.≡ m × a ≡≡ᵃ b

_≡≡ᵛ_ : Levelᵛ Γ → Levelᵛ Γ → Set a
_≡≡ᵛ_ = Pointwise.Pointwise _≡≡⁺_

-- Symmetry of syntactic equality.

sym-≡≡ᵃ : ∀ {a b : LevelAtom Γ} → a ≡≡ᵃ b → b ≡≡ᵃ a
sym-≡≡ᵃ zero = zero
sym-≡≡ᵃ (ne [t] [t]′) = ne [t]′ [t]

sym-≡≡⁺ : ∀ {a b : Level⁺ Γ} → a ≡≡⁺ b → b ≡≡⁺ a
sym-≡≡⁺ (n≡m , a≡b) = PE.sym n≡m , sym-≡≡ᵃ a≡b

sym-≡≡ᵛ : ∀ {a b : Levelᵛ Γ} → a ≡≡ᵛ b → b ≡≡ᵛ a
sym-≡≡ᵛ = Pointwise.symmetric sym-≡≡⁺

-- Transitivity of syntactic equality and weak equality.

trans-≡≡ᵃ-≤ᵃ : ∀ {a b c : LevelAtom Γ} → a ≡≡ᵃ b → ≤ᵃ d b c → ≤ᵃ d a c
trans-≡≡ᵃ-≤ᵃ zero zeroᵘ≤ = zeroᵘ≤
trans-≡≡ᵃ-≤ᵃ (ne [t] [t]′) (ne≤ x) = ne≤ x

trans-≡≡⁺-≤⁺ : ∀ {a b c : Level⁺ Γ} → a ≡≡⁺ b → ≤⁺ d b c → ≤⁺ d a c
trans-≡≡⁺-≤⁺ (PE.refl , a≡b) (m≤o , b≤c) = m≤o , trans-≡≡ᵃ-≤ᵃ a≡b b≤c

trans-≡≡⁺-≤⁺ᵛ : ∀ {a b} {c : Levelᵛ Γ} → a ≡≡⁺ b → ≤⁺ᵛ d b c → ≤⁺ᵛ d a c
trans-≡≡⁺-≤⁺ᵛ a≡b = Any.map (trans-≡≡⁺-≤⁺ a≡b)

trans-≡≡ᵛ-≤ᵛ : ∀ {a b c : Levelᵛ Γ} → a ≡≡ᵛ b → ≤ᵛ d b c → ≤ᵛ d a c
trans-≡≡ᵛ-≤ᵛ Pointwise.[] All.[] = All.[]
trans-≡≡ᵛ-≤ᵛ (x Pointwise.∷ a≡b) (px All.∷ b≤c) = trans-≡≡⁺-≤⁺ᵛ x px All.∷ trans-≡≡ᵛ-≤ᵛ a≡b b≤c

trans-≡≡ᵃ-≤ᵃ' : ∀ {a b c : LevelAtom Γ} → a ≡≡ᵃ b → ≤ᵃ d c b → ≤ᵃ d c a
trans-≡≡ᵃ-≤ᵃ' zero zeroᵘ≤ = zeroᵘ≤
trans-≡≡ᵃ-≤ᵃ' (ne [t] [t]′) zeroᵘ≤ = zeroᵘ≤
trans-≡≡ᵃ-≤ᵃ' (ne [t] [t]′) (ne≤ x) = ne≤ x

trans-≡≡⁺-≤⁺' : ∀ {a b c : Level⁺ Γ} → a ≡≡⁺ b → ≤⁺ d c b → ≤⁺ d c a
trans-≡≡⁺-≤⁺' (PE.refl , a≡b) (o≤m , c≤b) = o≤m , trans-≡≡ᵃ-≤ᵃ' a≡b c≤b

trans-≡≡⁺-≤⁺ᵛ' : ∀ {a b} {c : Level⁺ Γ} → a ≡≡ᵛ b → ≤⁺ᵛ d c b → ≤⁺ᵛ d c a
trans-≡≡⁺-≤⁺ᵛ' Pointwise.[] ()
trans-≡≡⁺-≤⁺ᵛ' (x Pointwise.∷ a≡b) (Any.here px) = Any.here (trans-≡≡⁺-≤⁺' x px)
trans-≡≡⁺-≤⁺ᵛ' (x Pointwise.∷ a≡b) (Any.there c≤b) = Any.there (trans-≡≡⁺-≤⁺ᵛ' a≡b c≤b)

trans-≡≡ᵛ-≤ᵛ' : ∀ {a b c : Levelᵛ Γ} → a ≡≡ᵛ b → ≤ᵛ d c b → ≤ᵛ d c a
trans-≡≡ᵛ-≤ᵛ' a≡b = All.map (trans-≡≡⁺-≤⁺ᵛ' a≡b)

trans-≡≡ᵛ-≡ᵛ : ∀ {a b c : Levelᵛ Γ} → a ≡≡ᵛ b → b ≡ᵛ c → a ≡ᵛ c
trans-≡≡ᵛ-≡ᵛ a≡b (b≤c , c≤b) = trans-≡≡ᵛ-≤ᵛ a≡b b≤c , trans-≡≡ᵛ-≤ᵛ' a≡b c≤b

trans-≡ᵛ-≡≡ᵛ : ∀ {a b c : Levelᵛ Γ} → a ≡ᵛ b → b ≡≡ᵛ c → a ≡ᵛ c
trans-≡ᵛ-≡≡ᵛ (a≤b , b≤a) b≡c = trans-≡≡ᵛ-≤ᵛ' (sym-≡≡ᵛ b≡c) a≤b , trans-≡≡ᵛ-≤ᵛ (sym-≡≡ᵛ b≡c) b≤a

-- Congruence lemmas for syntactic equality.

≡≡ᵛ-map-suc⁺ : ∀ {a b : Levelᵛ Γ} → a ≡≡ᵛ b → map-suc⁺ a ≡≡ᵛ map-suc⁺ b
≡≡ᵛ-map-suc⁺ Pointwise.[] = Pointwise.[]
≡≡ᵛ-map-suc⁺ ((x , y) Pointwise.∷ x₁) = (PE.cong 1+ x , y) Pointwise.∷ ≡≡ᵛ-map-suc⁺ x₁

≡≡ᵛ-sucᵛ : ∀ {a b : Levelᵛ Γ} → a ≡≡ᵛ b → sucᵛ a ≡≡ᵛ sucᵛ b
≡≡ᵛ-sucᵛ eq = (PE.refl , zero) Pointwise.∷ ≡≡ᵛ-map-suc⁺ eq

≡≡ᵛ-supᵛ : ∀ {a a′ b b′ : Levelᵛ Γ} → a ≡≡ᵛ b → a′ ≡≡ᵛ b′ → supᵛ a a′ ≡≡ᵛ supᵛ b b′
≡≡ᵛ-supᵛ = Pointwise.++⁺

-- Level normalisation is deterministic up to syntactic equality.

mutual
  deterministic-↑ᵛ : ∀ {t v v′} → Γ ⊢ t ↑ᵛ v → Γ ⊢ t ↑ᵛ v′ → v ≡≡ᵛ v′
  deterministic-↑ᵛ ([↑]ᵛ d t↓v) ([↑]ᵛ d₁ t↓v₁) =
    case whrDet*Term d d₁ of λ {
      PE.refl →
    deterministic-↓ᵛ t↓v t↓v₁ }

  deterministic-~ᵛ : ∀ {t v v′} → Γ ⊢ t ~ᵛ v → Γ ⊢ t ~ᵛ v′ → v ≡≡ᵛ v′
  deterministic-~ᵛ (supᵘˡₙ PE.refl x₁ x₂) (supᵘˡₙ PE.refl y x₄) =
    ≡≡ᵛ-supᵛ (deterministic-~ᵛ x₁ y) (deterministic-↑ᵛ x₂ x₄)
  deterministic-~ᵛ (supᵘʳₙ PE.refl x₁ x₂) (supᵘʳₙ PE.refl x₄ y) =
    ≡≡ᵛ-supᵛ (≡≡ᵛ-sucᵛ (deterministic-↑ᵛ x₁ x₄)) (deterministic-~ᵛ x₂ y)
  deterministic-~ᵛ (neₙ [t] PE.refl) (neₙ [t]₁ PE.refl) =
    (PE.refl , ne _ _) Pointwise.∷ Pointwise.[]
  -- Absurd cases
  deterministic-~ᵛ (supᵘˡₙ _ x₁ x₂) (supᵘʳₙ _ x₄ y) =
    case whnfConv~ᵛ x₁ of λ ()
  deterministic-~ᵛ (supᵘˡₙ x x₁ x₂) (neₙ [t] x₃) =
    Neutralᵃ-supᵘ→ (ne~↓ [t] .proj₂ .proj₁)
  deterministic-~ᵛ (supᵘʳₙ x x₁ x₂) (supᵘˡₙ x₃ y x₄) =
    case whnfConv~ᵛ y of λ ()
  deterministic-~ᵛ (supᵘʳₙ x x₁ x₂) (neₙ [t] x₃) =
    Neutralᵃ-supᵘ→ (ne~↓ [t] .proj₂ .proj₁)
  deterministic-~ᵛ (neₙ [t] x) (supᵘˡₙ x₁ y x₂) =
    Neutralᵃ-supᵘ→ (ne~↓ [t] .proj₂ .proj₁)
  deterministic-~ᵛ (neₙ [t] x) (supᵘʳₙ x₁ x₂ y) =
    Neutralᵃ-supᵘ→ (ne~↓ [t] .proj₂ .proj₁)

  deterministic-↓ᵛ : ∀ {t v v′} → Γ ⊢ t ↓ᵛ v → Γ ⊢ t ↓ᵛ v′ → v ≡≡ᵛ v′
  deterministic-↓ᵛ (zeroᵘₙ _ _) (zeroᵘₙ _ _) = Pointwise.[]
  deterministic-↓ᵛ (sucᵘₙ PE.refl x₁) (sucᵘₙ PE.refl x₃) =
    ≡≡ᵛ-sucᵛ (deterministic-↑ᵛ x₁ x₃)
  deterministic-↓ᵛ (neₙ x) (neₙ x₁) = deterministic-~ᵛ x x₁
  -- Absurd cases
  deterministic-↓ᵛ (zeroᵘₙ _ _) (neₙ t~v′) =
    case whnfConv~ᵛ t~v′ of λ ()
  deterministic-↓ᵛ (sucᵘₙ x x₁) (neₙ x₂) = case whnfConv~ᵛ x₂ of λ ()
  deterministic-↓ᵛ (neₙ t~v) (zeroᵘₙ _ _) =
    case whnfConv~ᵛ t~v of λ ()
  deterministic-↓ᵛ (neₙ x) (sucᵘₙ x₁ x₂) = case whnfConv~ᵛ x of λ ()

-- Properties of level comparison and equality.

≤ᵛ-sup-univ : ∀ {a b c : Levelᵛ Γ} → ≤ᵛ d a c → ≤ᵛ d b c → ≤ᵛ d (supᵛ a b) c
≤ᵛ-sup-univ a≤c b≤c = All.++⁺ a≤c b≤c

≤ᵛ-supˡ : ∀ {a b c : Levelᵛ Γ} → ≤ᵛ d c a → ≤ᵛ d c (supᵛ a b)
≤ᵛ-supˡ = All.map Any.++⁺ˡ

≤ᵛ-supʳ : ∀ {a b c : Levelᵛ Γ} → ≤ᵛ d c b → ≤ᵛ d c (supᵛ a b)
≤ᵛ-supʳ = All.map (Any.++⁺ʳ _)

≤ᵛ-zero : ∀ {v : Levelᵛ Γ} → ≤ᵛ d zeroᵛ v
≤ᵛ-zero = All.[]

≡ᵛ-supᵘ-zeroˡ : ∀ {v : Levelᵛ Γ} → supᵛ zeroᵛ v ≡ᵛ v
≡ᵛ-supᵘ-zeroˡ = ≤ᵛ-sup-univ ≤ᵛ-zero (≤ᵛ-refl _) , ≤ᵛ-supʳ (≤ᵛ-refl _)

≡ᵛ-supᵘ-zeroʳ : ∀ {v : Levelᵛ Γ} → supᵛ v zeroᵛ ≡ᵛ v
≡ᵛ-supᵘ-zeroʳ = ≤ᵛ-sup-univ (≤ᵛ-refl _) ≤ᵛ-zero , ≤ᵛ-supˡ (≤ᵛ-refl _)

≤ᵛ-map-suc⁺-sucᵛ : ∀ {a : Levelᵛ Γ} → ≤ᵛ d (map-suc⁺ a) (sucᵛ a)
≤ᵛ-map-suc⁺-sucᵛ = All.map Any.there (≤ᵛ-refl _)

≤ᵛ-supᵘ-map-suc⁺ : ∀ {a b : Levelᵛ Γ} → ≤ᵛ d (supᵛ (map-suc⁺ a) (map-suc⁺ b)) (supᵛ (sucᵛ a) (sucᵛ b))
≤ᵛ-supᵘ-map-suc⁺ {a} {b} = ≤ᵛ-sup-univ (≤ᵛ-supˡ ≤ᵛ-map-suc⁺-sucᵛ) (≤ᵛ-supʳ {a = sucᵛ a} (≤ᵛ-map-suc⁺-sucᵛ {a = b}))

map-suc⁺-++ : ∀ {a b : Levelᵛ Γ} → map-suc⁺ (supᵛ a b) PE.≡ supᵛ (map-suc⁺ a) (map-suc⁺ b)
map-suc⁺-++ {a = L.[]} = PE.refl
map-suc⁺-++ {a = x L.∷ a} = PE.cong (_ L.∷_) (map-suc⁺-++ {a = a})

≤ᵛ-supᵘ-sucᵘ : ∀ {a b : Levelᵛ Γ} → ≤ᵛ d (sucᵛ (supᵛ a b)) (supᵛ (sucᵛ a) (sucᵛ b))
≤ᵛ-supᵘ-sucᵘ {a} {b} = Any.here (≤⁺-refl _) All.∷ PE.subst (λ x → ≤ᵛ _ x (supᵛ (sucᵛ a) (sucᵛ b))) (PE.sym (map-suc⁺-++ {a = a} {b})) ≤ᵛ-supᵘ-map-suc⁺

≡ᵛ-supᵘ-sucᵘ : ∀ {a b : Levelᵛ Γ} → sucᵛ (supᵛ a b) ≡ᵛ supᵛ (sucᵛ a) (sucᵛ b)
≡ᵛ-supᵘ-sucᵘ = ≤ᵛ-supᵘ-sucᵘ , ≤ᵛ-sup-univ (≤ᵛ-suc (≤ᵛ-supˡ (≤ᵛ-refl _))) (≤ᵛ-suc (≤ᵛ-supʳ (≤ᵛ-refl _)))

≡ᵛ-supᵘ-assoc : ∀ {a b c : Levelᵛ Γ} → supᵛ (supᵛ a b) c ≡ᵛ supᵛ a (supᵛ b c)
≡ᵛ-supᵘ-assoc {a} {b} {c} = PE.subst (supᵛ (supᵛ a b) c ≡ᵛ_) (L.++-assoc a b c) (≡ᵛ-refl _)

≤ᵛ-supᵘ-comm : ∀ {a b : Levelᵛ Γ} → ≤ᵛ d (supᵛ a b) (supᵛ b a)
≤ᵛ-supᵘ-comm {a} {b} = All.map (Any.++-comm a b) (≤ᵛ-refl _)

≡ᵛ-supᵘ-comm : ∀ {a b : Levelᵛ Γ} → supᵛ a b ≡ᵛ supᵛ b a
≡ᵛ-supᵘ-comm {a} {b} = ≤ᵛ-supᵘ-comm {a = a} , ≤ᵛ-supᵘ-comm {a = b}

≤→sup≡ : ∀ {a b : Levelᵛ Γ} → ≤ᵛ false a b → supᵛ a b ≡ᵛ b
≤→sup≡ a≤b = ≤ᵛ-sup-univ a≤b (≤ᵛ-refl _) , ≤ᵛ-supʳ (≤ᵛ-refl _)

≡ᵛ-supᵘ-idem : ∀ {a : Levelᵛ Γ} → supᵛ a a ≡ᵛ a
≡ᵛ-supᵘ-idem {a} = ≤→sup≡ (≤ᵛ-refl _)

a≤⁺suca : ∀ {a b : Level⁺ Γ} → ≤⁺ d a b → ≤⁺ d a (suc⁺ b)
a≤⁺suca (n≤m , a≤b) = m≤n⇒m≤1+n n≤m , a≤b

a≤⁺ᵛmap-suc⁺a : ∀ {a : Level⁺ Γ} {b : Levelᵛ Γ} → ≤⁺ᵛ d a b → ≤⁺ᵛ d a (map-suc⁺ b)
a≤⁺ᵛmap-suc⁺a (Any.here px) = Any.here (a≤⁺suca px)
a≤⁺ᵛmap-suc⁺a (Any.there a≤b) = Any.there (a≤⁺ᵛmap-suc⁺a a≤b)

a≤ᵛmap-suc⁺a : ∀ {a : Levelᵛ Γ} → ≤ᵛ d a (map-suc⁺ a)
a≤ᵛmap-suc⁺a = All.map a≤⁺ᵛmap-suc⁺a (≤ᵛ-refl _)

a≤ᵛsuca : ∀ {a : Levelᵛ Γ} → ≤ᵛ d a (sucᵛ a)
a≤ᵛsuca = All.map Any.there a≤ᵛmap-suc⁺a

≡ᵛ-supᵘ-sub : ∀ {a : Levelᵛ Γ} → supᵛ a (sucᵛ a) ≡ᵛ sucᵛ a
≡ᵛ-supᵘ-sub {a} = ≤→sup≡ a≤ᵛsuca
