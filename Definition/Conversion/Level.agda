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

open import Definition.Untyped M
open import Definition.Untyped.Neutral M
open import Definition.Conversion R
open import Definition.Conversion.Whnf R
open import Definition.Typed R
open import Definition.Typed.Properties R

open import Tools.Bool
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

import Data.List as L
import Data.List.Properties as L
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as All
import Data.List.Relation.Unary.Any as Any
import Data.List.Relation.Unary.Any.Properties as Any
import Data.List.Relation.Binary.Pointwise as P

private
  variable
    n : Nat
    Γ : Con Term n
    t u : Term n
    d : Bool

LevelAtom→Term : ∀ {Γ : Con Term n} → LevelAtom Γ → Term n
LevelAtom→Term zeroᵘ = zeroᵘ
LevelAtom→Term (ne {t} x) = t

sucᵘᵏ : Nat → Term n → Term n
sucᵘᵏ Nat.zero t = t
sucᵘᵏ (1+ k) t = sucᵘ (sucᵘᵏ k t)

LevelPlus→Term : ∀ {Γ : Con Term n} → LevelPlus Γ → Term n
LevelPlus→Term (n , a) = sucᵘᵏ n (LevelAtom→Term a)

LevelView→Term : ∀ {Γ : Con Term n} → LevelView Γ → Term n
LevelView→Term L.[] = zeroᵘ
LevelView→Term (l L.∷ xs) = LevelPlus→Term l maxᵘ LevelView→Term xs

≡ⁿ-refl : ∀ {t} → Γ ⊢ t ~ t ↓ Level → ≡ⁿ Γ t t d
≡ⁿ-refl {d = false} t~t = ne≡ t~t
≡ⁿ-refl {d = true} t~t = ne≡' t~t

≤⁺-refl : ∀ (v : LevelPlus Γ) → ≤⁺ d v v
≤⁺-refl (n , zeroᵘ) = ≤-refl , zeroᵘ≤
≤⁺-refl (n , ne x) = ≤-refl , ne≤ (≡ⁿ-refl x)

≤ᵛ-refl : ∀ (v : LevelView Γ) → ≤ᵛ d v v
≤ᵛ-refl L.[] = All.[]
≤ᵛ-refl (x L.∷ v) = Any.here (≤⁺-refl x) All.∷ All.map Any.there (≤ᵛ-refl v)

≡ᵛ-refl : ∀ (v : LevelView Γ) → v ≡ᵛ v
≡ᵛ-refl v = ≤ᵛ-refl v , ≤ᵛ-refl v

≤⁺-suc : ∀ {u v : LevelPlus Γ} → ≤⁺ d u v → ≤⁺ d (suc⁺ u) (suc⁺ v)
≤⁺-suc (x , a) = s≤s x , a

≤⁺ᵛ-suc : ∀ {u : LevelPlus Γ} {v : LevelView Γ} → ≤⁺ᵛ d u v → ≤⁺ᵛ d (suc⁺ u) (map-suc⁺ v)
≤⁺ᵛ-suc (Any.here px) = Any.here (≤⁺-suc px)
≤⁺ᵛ-suc (Any.there u≤v) = Any.there (≤⁺ᵛ-suc u≤v)

≤ᵛ-map-suc⁺ : ∀ {u v : LevelView Γ} → ≤ᵛ d u v → ≤ᵛ d (map-suc⁺ u) (map-suc⁺ v)
≤ᵛ-map-suc⁺ All.[] = All.[]
≤ᵛ-map-suc⁺ (px All.∷ u≤v) = ≤⁺ᵛ-suc px All.∷ ≤ᵛ-map-suc⁺ u≤v

≤ᵛ-suc : ∀ {u v : LevelView Γ} → ≤ᵛ d u v → ≤ᵛ d (sucᵛ u) (sucᵛ v)
≤ᵛ-suc u≤v = Any.here (≤⁺-refl _) All.∷ All.map Any.there (≤ᵛ-map-suc⁺ u≤v)

≡ᵛ-suc : ∀ {u v : LevelView Γ} → u ≡ᵛ v → sucᵛ u ≡ᵛ sucᵛ v
≡ᵛ-suc (u≤v , v≤u) = ≤ᵛ-suc u≤v , ≤ᵛ-suc v≤u

≤ᵛ-max : ∀ {u u′ v v′ : LevelView Γ} → ≤ᵛ d u v → ≤ᵛ d u′ v′ → ≤ᵛ d (maxᵛ u u′) (maxᵛ v v′)
≤ᵛ-max u≤v u′≤v′ = All.++⁺ (All.map Any.++⁺ˡ u≤v) (All.map (Any.++⁺ʳ _) u′≤v′)

≡ᵛ-max : ∀ {u u′ v v′ : LevelView Γ} → u ≡ᵛ v → u′ ≡ᵛ v′ → maxᵛ u u′ ≡ᵛ maxᵛ v v′
≡ᵛ-max (u≤v , v≤u) (u′≤v′ , v′≤u′) = ≤ᵛ-max u≤v u′≤v′ , ≤ᵛ-max v≤u v′≤u′

data _≡≡ᵃ_ {Γ : Con Term n} : LevelAtom Γ → LevelAtom Γ → Set a where
  zero : zeroᵘ ≡≡ᵃ zeroᵘ
  ne : ∀ {t} ([t] [t]′ : Γ ⊢ t ~ t ↓ Level) → ne [t] ≡≡ᵃ ne [t]′

_≡≡⁺_ : LevelPlus Γ → LevelPlus Γ → Set a
(n , a) ≡≡⁺ (m , b) = n PE.≡ m × a ≡≡ᵃ b

_≡≡ᵛ_ : LevelView Γ → LevelView Γ → Set a
_≡≡ᵛ_ = P.Pointwise _≡≡⁺_

sym-≡≡ᵃ : ∀ {a b : LevelAtom Γ} → a ≡≡ᵃ b → b ≡≡ᵃ a
sym-≡≡ᵃ zero = zero
sym-≡≡ᵃ (ne [t] [t]′) = ne [t]′ [t]

sym-≡≡⁺ : ∀ {a b : LevelPlus Γ} → a ≡≡⁺ b → b ≡≡⁺ a
sym-≡≡⁺ (n≡m , a≡b) = PE.sym n≡m , sym-≡≡ᵃ a≡b

sym-≡≡ᵛ : ∀ {a b : LevelView Γ} → a ≡≡ᵛ b → b ≡≡ᵛ a
sym-≡≡ᵛ = P.symmetric sym-≡≡⁺

trans-≡≡ᵃ-≤ᵃ : ∀ {a b c : LevelAtom Γ} → a ≡≡ᵃ b → ≤ᵃ d b c → ≤ᵃ d a c
trans-≡≡ᵃ-≤ᵃ zero zeroᵘ≤ = zeroᵘ≤
trans-≡≡ᵃ-≤ᵃ (ne [t] [t]′) (ne≤ x) = ne≤ x

trans-≡≡⁺-≤⁺ : ∀ {a b c : LevelPlus Γ} → a ≡≡⁺ b → ≤⁺ d b c → ≤⁺ d a c
trans-≡≡⁺-≤⁺ (PE.refl , a≡b) (m≤o , b≤c) = m≤o , trans-≡≡ᵃ-≤ᵃ a≡b b≤c

trans-≡≡⁺-≤⁺ᵛ : ∀ {a b} {c : LevelView Γ} → a ≡≡⁺ b → ≤⁺ᵛ d b c → ≤⁺ᵛ d a c
trans-≡≡⁺-≤⁺ᵛ a≡b = Any.map (trans-≡≡⁺-≤⁺ a≡b)

trans-≡≡ᵛ-≤ᵛ : ∀ {a b c : LevelView Γ} → a ≡≡ᵛ b → ≤ᵛ d b c → ≤ᵛ d a c
trans-≡≡ᵛ-≤ᵛ P.[] All.[] = All.[]
trans-≡≡ᵛ-≤ᵛ (x P.∷ a≡b) (px All.∷ b≤c) = trans-≡≡⁺-≤⁺ᵛ x px All.∷ trans-≡≡ᵛ-≤ᵛ a≡b b≤c

trans-≡≡ᵃ-≤ᵃ' : ∀ {a b c : LevelAtom Γ} → a ≡≡ᵃ b → ≤ᵃ d c b → ≤ᵃ d c a
trans-≡≡ᵃ-≤ᵃ' zero zeroᵘ≤ = zeroᵘ≤
trans-≡≡ᵃ-≤ᵃ' (ne [t] [t]′) zeroᵘ≤ = zeroᵘ≤
trans-≡≡ᵃ-≤ᵃ' (ne [t] [t]′) (ne≤ x) = ne≤ x

trans-≡≡⁺-≤⁺' : ∀ {a b c : LevelPlus Γ} → a ≡≡⁺ b → ≤⁺ d c b → ≤⁺ d c a
trans-≡≡⁺-≤⁺' (PE.refl , a≡b) (o≤m , c≤b) = o≤m , trans-≡≡ᵃ-≤ᵃ' a≡b c≤b

trans-≡≡⁺-≤⁺ᵛ' : ∀ {a b} {c : LevelPlus Γ} → a ≡≡ᵛ b → ≤⁺ᵛ d c b → ≤⁺ᵛ d c a
trans-≡≡⁺-≤⁺ᵛ' P.[] ()
trans-≡≡⁺-≤⁺ᵛ' (x P.∷ a≡b) (Any.here px) = Any.here (trans-≡≡⁺-≤⁺' x px)
trans-≡≡⁺-≤⁺ᵛ' (x P.∷ a≡b) (Any.there c≤b) = Any.there (trans-≡≡⁺-≤⁺ᵛ' a≡b c≤b)

trans-≡≡ᵛ-≤ᵛ' : ∀ {a b c : LevelView Γ} → a ≡≡ᵛ b → ≤ᵛ d c b → ≤ᵛ d c a
trans-≡≡ᵛ-≤ᵛ' a≡b = All.map (trans-≡≡⁺-≤⁺ᵛ' a≡b)

trans-≡≡ᵛ-≡ᵛ : ∀ {a b c : LevelView Γ} → a ≡≡ᵛ b → b ≡ᵛ c → a ≡ᵛ c
trans-≡≡ᵛ-≡ᵛ a≡b (b≤c , c≤b) = trans-≡≡ᵛ-≤ᵛ a≡b b≤c , trans-≡≡ᵛ-≤ᵛ' a≡b c≤b

trans-≡ᵛ-≡≡ᵛ : ∀ {a b c : LevelView Γ} → a ≡ᵛ b → b ≡≡ᵛ c → a ≡ᵛ c
trans-≡ᵛ-≡≡ᵛ (a≤b , b≤a) b≡c = trans-≡≡ᵛ-≤ᵛ' (sym-≡≡ᵛ b≡c) a≤b , trans-≡≡ᵛ-≤ᵛ (sym-≡≡ᵛ b≡c) b≤a

≡≡ᵛ-map-suc⁺ : ∀ {a b : LevelView Γ} → a ≡≡ᵛ b → map-suc⁺ a ≡≡ᵛ map-suc⁺ b
≡≡ᵛ-map-suc⁺ P.[] = P.[]
≡≡ᵛ-map-suc⁺ ((x , y) P.∷ x₁) = (PE.cong 1+ x , y) P.∷ ≡≡ᵛ-map-suc⁺ x₁

≡≡ᵛ-sucᵛ : ∀ {a b : LevelView Γ} → a ≡≡ᵛ b → sucᵛ a ≡≡ᵛ sucᵛ b
≡≡ᵛ-sucᵛ eq = (PE.refl , zero) P.∷ ≡≡ᵛ-map-suc⁺ eq

≡≡ᵛ-maxᵛ : ∀ {a a′ b b′ : LevelView Γ} → a ≡≡ᵛ b → a′ ≡≡ᵛ b′ → maxᵛ a a′ ≡≡ᵛ maxᵛ b b′
≡≡ᵛ-maxᵛ = P.++⁺

mutual
  irrelevance-↑ᵛ : ∀ {t v v′} → Γ ⊢ t ↑ᵛ v → Γ ⊢ t ↑ᵛ v′ → v ≡≡ᵛ v′
  irrelevance-↑ᵛ ([↑]ᵛ d t↓v) ([↑]ᵛ d₁ t↓v₁) =
    case whrDet*Term d d₁ of λ {
      PE.refl →
    irrelevance-↓ᵛ t↓v t↓v₁ }

  irrelevance-~ᵛ : ∀ {t v v′} → Γ ⊢ t ~ᵛ v → Γ ⊢ t ~ᵛ v′ → v ≡≡ᵛ v′
  irrelevance-~ᵛ (maxᵘˡₙ PE.refl x₁ x₂) (maxᵘˡₙ PE.refl y x₄) =
    ≡≡ᵛ-maxᵛ (irrelevance-~ᵛ x₁ y) (irrelevance-↑ᵛ x₂ x₄)
  irrelevance-~ᵛ (maxᵘʳₙ PE.refl x₁ x₂) (maxᵘʳₙ PE.refl x₄ y) =
    ≡≡ᵛ-maxᵛ (≡≡ᵛ-sucᵛ (irrelevance-↑ᵛ x₁ x₄)) (irrelevance-~ᵛ x₂ y)
  irrelevance-~ᵛ (neₙ [t] PE.refl) (neₙ [t]₁ PE.refl) =
    (PE.refl , ne _ _) P.∷ P.[]
  -- Absurd cases
  irrelevance-~ᵛ (maxᵘˡₙ _ x₁ x₂) (maxᵘʳₙ _ x₄ y) = case whnfConv~ᵛ x₁ of λ { (ne ()) }
  irrelevance-~ᵛ (maxᵘˡₙ x x₁ x₂) (neₙ [t] x₃) = case ne~↓ [t] of λ ()
  irrelevance-~ᵛ (maxᵘʳₙ x x₁ x₂) (maxᵘˡₙ x₃ y x₄) = case whnfConv~ᵛ y of λ { (ne ()) }
  irrelevance-~ᵛ (maxᵘʳₙ x x₁ x₂) (neₙ [t] x₃) = case ne~↓ [t] of λ ()
  irrelevance-~ᵛ (neₙ [t] x) (maxᵘˡₙ x₁ y x₂) = case ne~↓ [t] of λ ()
  irrelevance-~ᵛ (neₙ [t] x) (maxᵘʳₙ x₁ x₂ y) = case ne~↓ [t] of λ ()

  irrelevance-↓ᵛ : ∀ {t v v′} → Γ ⊢ t ↓ᵛ v → Γ ⊢ t ↓ᵛ v′ → v ≡≡ᵛ v′
  irrelevance-↓ᵛ (zeroᵘₙ x) (zeroᵘₙ x₁) = P.[]
  irrelevance-↓ᵛ (sucᵘₙ PE.refl x₁) (sucᵘₙ PE.refl x₃) =
    ≡≡ᵛ-sucᵛ (irrelevance-↑ᵛ x₁ x₃)
  irrelevance-↓ᵛ (neₙ x) (neₙ x₁) = irrelevance-~ᵛ x x₁
  -- Absurd cases
  irrelevance-↓ᵛ (zeroᵘₙ x) (neₙ x₁) = case whnfConv~ᵛ x₁ of λ { (ne ()) }
  irrelevance-↓ᵛ (sucᵘₙ x x₁) (neₙ x₂) = case whnfConv~ᵛ x₂ of λ { (ne ()) }
  irrelevance-↓ᵛ (neₙ x) (zeroᵘₙ x₁) = case whnfConv~ᵛ x of λ { (ne ()) }
  irrelevance-↓ᵛ (neₙ x) (sucᵘₙ x₁ x₂) = case whnfConv~ᵛ x of λ { (ne ()) }

zeroᵘrefl : ⊢ Γ → Γ ⊢ zeroᵘ [conv↓] zeroᵘ ∷Level
zeroᵘrefl ⊢Γ = [↓]ˡ zeroᵛ zeroᵛ (zeroᵘₙ ⊢Γ) (zeroᵘₙ ⊢Γ) (≡ᵛ-refl zeroᵛ)

≤ᵛ-max-univ : ∀ {a b c : LevelView Γ} → ≤ᵛ d a c → ≤ᵛ d b c → ≤ᵛ d (maxᵛ a b) c
≤ᵛ-max-univ a≤c b≤c = All.++⁺ a≤c b≤c

≤ᵛ-maxˡ : ∀ {a b c : LevelView Γ} → ≤ᵛ d c a → ≤ᵛ d c (maxᵛ a b)
≤ᵛ-maxˡ = All.map Any.++⁺ˡ

≤ᵛ-maxʳ : ∀ {a b c : LevelView Γ} → ≤ᵛ d c b → ≤ᵛ d c (maxᵛ a b)
≤ᵛ-maxʳ = All.map (Any.++⁺ʳ _)

≤ᵛ-zero : ∀ {v : LevelView Γ} → ≤ᵛ d zeroᵛ v
≤ᵛ-zero = All.[]

≡ᵛ-maxᵘ-zeroˡ : ∀ {v : LevelView Γ} → maxᵛ zeroᵛ v ≡ᵛ v
≡ᵛ-maxᵘ-zeroˡ = ≤ᵛ-max-univ ≤ᵛ-zero (≤ᵛ-refl _) , ≤ᵛ-maxʳ (≤ᵛ-refl _)

≡ᵛ-maxᵘ-zeroʳ : ∀ {v : LevelView Γ} → maxᵛ v zeroᵛ ≡ᵛ v
≡ᵛ-maxᵘ-zeroʳ = ≤ᵛ-max-univ (≤ᵛ-refl _) ≤ᵛ-zero , ≤ᵛ-maxˡ (≤ᵛ-refl _)

≤ᵛ-map-suc⁺-sucᵛ : ∀ {a : LevelView Γ} → ≤ᵛ d (map-suc⁺ a) (sucᵛ a)
≤ᵛ-map-suc⁺-sucᵛ = All.map Any.there (≤ᵛ-refl _)

≤ᵛ-maxᵘ-map-suc⁺ : ∀ {a b : LevelView Γ} → ≤ᵛ d (maxᵛ (map-suc⁺ a) (map-suc⁺ b)) (maxᵛ (sucᵛ a) (sucᵛ b))
≤ᵛ-maxᵘ-map-suc⁺ {a} {b} = ≤ᵛ-max-univ (≤ᵛ-maxˡ ≤ᵛ-map-suc⁺-sucᵛ) (≤ᵛ-maxʳ {a = sucᵛ a} (≤ᵛ-map-suc⁺-sucᵛ {a = b}))

map-suc⁺-++ : ∀ {a b : LevelView Γ} → map-suc⁺ (maxᵛ a b) PE.≡ maxᵛ (map-suc⁺ a) (map-suc⁺ b)
map-suc⁺-++ {a = L.[]} = PE.refl
map-suc⁺-++ {a = x L.∷ a} = PE.cong (_ L.∷_) (map-suc⁺-++ {a = a})

≤ᵛ-maxᵘ-sucᵘ : ∀ {a b : LevelView Γ} → ≤ᵛ d (sucᵛ (maxᵛ a b)) (maxᵛ (sucᵛ a) (sucᵛ b))
≤ᵛ-maxᵘ-sucᵘ {a} {b} = Any.here (≤⁺-refl _) All.∷ PE.subst (λ x → ≤ᵛ _ x (maxᵛ (sucᵛ a) (sucᵛ b))) (PE.sym (map-suc⁺-++ {a = a} {b})) ≤ᵛ-maxᵘ-map-suc⁺

≡ᵛ-maxᵘ-sucᵘ : ∀ {a b : LevelView Γ} → sucᵛ (maxᵛ a b) ≡ᵛ maxᵛ (sucᵛ a) (sucᵛ b)
≡ᵛ-maxᵘ-sucᵘ = ≤ᵛ-maxᵘ-sucᵘ , ≤ᵛ-max-univ (≤ᵛ-suc (≤ᵛ-maxˡ (≤ᵛ-refl _))) (≤ᵛ-suc (≤ᵛ-maxʳ (≤ᵛ-refl _)))

≡ᵛ-maxᵘ-assoc : ∀ {a b c : LevelView Γ} → maxᵛ (maxᵛ a b) c ≡ᵛ maxᵛ a (maxᵛ b c)
≡ᵛ-maxᵘ-assoc {a} {b} {c} = PE.subst (maxᵛ (maxᵛ a b) c ≡ᵛ_) (L.++-assoc a b c) (≡ᵛ-refl _)

≤ᵛ-maxᵘ-comm : ∀ {a b : LevelView Γ} → ≤ᵛ d (maxᵛ a b) (maxᵛ b a)
≤ᵛ-maxᵘ-comm {a} {b} = All.map (Any.++-comm a b) (≤ᵛ-refl _)

≡ᵛ-maxᵘ-comm : ∀ {a b : LevelView Γ} → maxᵛ a b ≡ᵛ maxᵛ b a
≡ᵛ-maxᵘ-comm {a} {b} = ≤ᵛ-maxᵘ-comm {a = a} , ≤ᵛ-maxᵘ-comm {a = b}

≤→max≡ : ∀ {a b : LevelView Γ} → ≤ᵛ false a b → maxᵛ a b ≡ᵛ b
≤→max≡ a≤b = ≤ᵛ-max-univ a≤b (≤ᵛ-refl _) , ≤ᵛ-maxʳ (≤ᵛ-refl _)

≡ᵛ-maxᵘ-idem : ∀ {a : LevelView Γ} → maxᵛ a a ≡ᵛ a
≡ᵛ-maxᵘ-idem {a} = ≤→max≡ (≤ᵛ-refl _)

a≤⁺suca : ∀ {a b : LevelPlus Γ} → ≤⁺ d a b → ≤⁺ d a (suc⁺ b)
a≤⁺suca (n≤m , a≤b) = m≤n⇒m≤1+n n≤m , a≤b

a≤⁺ᵛmap-suc⁺a : ∀ {a : LevelPlus Γ} {b : LevelView Γ} → ≤⁺ᵛ d a b → ≤⁺ᵛ d a (map-suc⁺ b)
a≤⁺ᵛmap-suc⁺a (Any.here px) = Any.here (a≤⁺suca px)
a≤⁺ᵛmap-suc⁺a (Any.there a≤b) = Any.there (a≤⁺ᵛmap-suc⁺a a≤b)

a≤ᵛmap-suc⁺a : ∀ {a : LevelView Γ} → ≤ᵛ d a (map-suc⁺ a)
a≤ᵛmap-suc⁺a = All.map a≤⁺ᵛmap-suc⁺a (≤ᵛ-refl _)

a≤ᵛsuca : ∀ {a : LevelView Γ} → ≤ᵛ d a (sucᵛ a)
a≤ᵛsuca = All.map Any.there a≤ᵛmap-suc⁺a

≡ᵛ-maxᵘ-sub : ∀ {a : LevelView Γ} → maxᵛ a (sucᵛ a) ≡ᵛ sucᵛ a
≡ᵛ-maxᵘ-sub {a} = ≤→max≡ a≤ᵛsuca
