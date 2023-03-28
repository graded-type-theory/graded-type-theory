module Erasure.Target.Properties.Reduction where

open import Erasure.Target

open import Tools.Nat
import Tools.PropositionalEquality as PE
open import Tools.Sum

private
  variable
    n : Nat
    t t′ u : Term n

-- Reduction properties

-- Concatenation of reduction closure

red*concat : t ⇒* t′ → t′ ⇒* u → t ⇒* u
red*concat refl t′⇒*u = t′⇒*u
red*concat (trans x t⇒*t′) t′⇒*u = trans x (red*concat t⇒*t′ t′⇒*u)

-- Closure of substitution reductions

app-subst* : t ⇒* t′ → (t ∘ u) ⇒* (t′ ∘ u)
app-subst* refl = refl
app-subst* (trans x t⇒*t′) = trans (app-subst x) (app-subst* t⇒*t′)

fst-subst* : t ⇒* t′ → fst t ⇒* fst t′
fst-subst* refl = refl
fst-subst* (trans x t⇒*t′) = trans (fst-subst x) (fst-subst* t⇒*t′)

snd-subst* : t ⇒* t′ → snd t ⇒* snd t′
snd-subst* refl = refl
snd-subst* (trans x t⇒*t′) = trans (snd-subst x) (snd-subst* t⇒*t′)

natrec-subst* : ∀ {z s} → t ⇒* t′ → natrec z s t ⇒* natrec z s t′
natrec-subst* refl = refl
natrec-subst* (trans x t⇒t′) = trans (natrec-subst x) (natrec-subst* t⇒t′)

prodrec-subst* : t ⇒* t′ → prodrec t u ⇒* prodrec t′ u
prodrec-subst* refl = refl
prodrec-subst* (trans x t⇒t′) = trans (prodrec-subst x) (prodrec-subst* t⇒t′)


-- Reduction is deterministic
-- If a ⇒ b and a ⇒ c then b ≡ c

redDet : (u : Term n) → u ⇒ t → u ⇒ t′ → t PE.≡ t′
redDet (var x) () u⇒t′
redDet (lam a) () u⇒t′
redDet (a ∘ a₁) (app-subst u⇒t) (app-subst u⇒t′) =
  PE.cong₂ _∘_ (redDet a u⇒t u⇒t′) PE.refl
redDet (.(lam _) ∘ a) β-red β-red = PE.refl
redDet zero () u⇒t′
redDet (suc a) () u⇒t′
redDet (natrec a a₁ a₂) (natrec-subst u⇒t) (natrec-subst u⇒t′) =
  PE.cong (natrec a a₁) (redDet a₂ u⇒t u⇒t′)
redDet (natrec a a₁ .zero) natrec-zero natrec-zero = PE.refl
redDet (natrec a a₁ .(suc _)) natrec-suc natrec-suc = PE.refl
redDet (prod a a₁) () u⇒t′
redDet (fst a) (fst-subst u⇒t) (fst-subst u⇒t′) =
  PE.cong fst (redDet a u⇒t u⇒t′)
redDet (fst .(prod _ _)) Σ-β₁ Σ-β₁ = PE.refl
redDet (snd a) (snd-subst u⇒t) (snd-subst u⇒t′) =
  PE.cong snd (redDet a u⇒t u⇒t′)
redDet (snd .(prod _ _)) Σ-β₂ Σ-β₂ = PE.refl
redDet (prodrec a a₁) (prodrec-subst u⇒t) (prodrec-subst u⇒t′) =
  PE.cong (λ z → prodrec z a₁) (redDet a u⇒t u⇒t′)
redDet (prodrec .(prod _ _) a) prodrec-β prodrec-β = PE.refl
redDet star () u⇒t′
redDet ↯ () u⇒t′

-- Reduction closure is deterministic
-- (there is only one reduction path)
-- If a ⇒* b and a ⇒* c then b ⇒* c or c ⇒* b

red*Det : u ⇒* t → u ⇒* t′ → (t ⇒* t′) ⊎ (t′ ⇒* t)
red*Det refl refl = inj₁ refl
red*Det refl (trans x u⇒t′) = inj₁ (trans x u⇒t′)
red*Det (trans x u⇒t) refl = inj₂ (trans x u⇒t)
red*Det {u = u} (trans x u⇒t) (trans x₁ u⇒t′)
  rewrite redDet u x x₁ = red*Det u⇒t u⇒t′

-- Non-reducible terms

↯-noRed : ↯ ⇒* t → t PE.≡ ↯
↯-noRed refl = PE.refl

zero-noRed : zero ⇒* t → t PE.≡ zero
zero-noRed refl = PE.refl

suc-noRed : suc t ⇒* t′ → t′ PE.≡ suc t
suc-noRed refl = PE.refl

prod-noRed : prod t t′ ⇒* u → u PE.≡ prod t t′
prod-noRed refl = PE.refl

star-noRed : star ⇒* t → t PE.≡ star
star-noRed refl = PE.refl
