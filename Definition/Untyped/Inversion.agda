------------------------------------------------------------------------
-- Inversion lemmas for weakening
------------------------------------------------------------------------

module Definition.Untyped.Inversion {a} (M : Set a) where

open import Definition.Untyped M

open import Tools.Fin
open import Tools.Product
open import Tools.PropositionalEquality

private variable
  x           : Fin _
  ρ           : Wk _ _
  A B t u v w : Term _
  p q r       : M
  s           : SigmaMode
  b           : BinderMode

-- Inversion for var.

wk-var :
  wk ρ t ≡ var x →
  ∃ λ x′ → t ≡ var x′ × wkVar ρ x′ ≡ x
wk-var {t = var _} refl = _ , refl , refl

-- Inversion for U.

wk-U : wk ρ t ≡ U → t ≡ U
wk-U {t = U} refl = refl

-- Inversion for ΠΣ⟨_⟩_,_▷_▹_.

wk-ΠΣ :
  wk ρ t ≡ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
  ∃₂ λ A′ B′ →
     t ≡ ΠΣ⟨ b ⟩ p , q ▷ A′ ▹ B′ ×
     wk ρ A′ ≡ A × wk (lift ρ) B′ ≡ B
wk-ΠΣ {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} refl =
  _ , _ , refl , refl , refl

-- Inversion for lam.

wk-lam :
  wk ρ t ≡ lam p u →
  ∃ λ u′ → t ≡ lam p u′ × wk (lift ρ) u′ ≡ u
wk-lam {t = lam _ _} refl = _ , refl , refl

-- Inversion for _∘⟨_⟩_.

wk-∘ :
  wk ρ t ≡ u ∘⟨ p ⟩ v →
  ∃₂ λ u′ v′ → t ≡ u′ ∘⟨ p ⟩ v′ × wk ρ u′ ≡ u × wk ρ v′ ≡ v
wk-∘ {t = _ ∘⟨ _ ⟩ _} refl = _ , _ , refl , refl , refl

-- Inversion for prod.

wk-prod :
  wk ρ t ≡ prod s p u v →
  ∃₂ λ u′ v′ → t ≡ prod s p u′ v′ × wk ρ u′ ≡ u × wk ρ v′ ≡ v
wk-prod {t = prod _ _ _ _} refl = _ , _ , refl , refl , refl

-- Inversion for fst.

wk-fst :
  wk ρ t ≡ fst p u →
  ∃ λ u′ → t ≡ fst p u′ × wk ρ u′ ≡ u
wk-fst {t = fst _ _} refl = _ , refl , refl

-- Inversion for snd.

wk-snd :
  wk ρ t ≡ snd p u →
  ∃ λ u′ → t ≡ snd p u′ × wk ρ u′ ≡ u
wk-snd {t = snd _ _} refl = _ , refl , refl

-- Inversion for prodrec.

wk-prodrec :
  wk ρ t ≡ prodrec r p q A u v →
  ∃₃ λ A′ u′ v′ →
     t ≡ prodrec r p q A′ u′ v′ ×
     wk (lift ρ) A′ ≡ A × wk ρ u′ ≡ u × wk (lift (lift ρ)) v′ ≡ v
wk-prodrec {t = prodrec _ _ _ _ _ _} refl =
  _ , _ , _ , refl , refl , refl , refl

-- Inversion for Unit.

wk-Unit : wk ρ t ≡ Unit → t ≡ Unit
wk-Unit {t = Unit} refl = refl

-- Inversion for star.

wk-star : wk ρ t ≡ star → t ≡ star
wk-star {t = star} refl = refl

-- Inversion for Empty.

wk-Empty : wk ρ t ≡ Empty → t ≡ Empty
wk-Empty {t = Empty} refl = refl

-- Inversion for Emptyrec.

wk-Emptyrec :
  wk ρ t ≡ Emptyrec p A u →
  ∃₂ λ A′ u′ → t ≡ Emptyrec p A′ u′ × wk ρ A′ ≡ A × wk ρ u′ ≡ u
wk-Emptyrec {t = Emptyrec _ _ _} refl =
  _ , _ , refl , refl , refl

-- Inversion for ℕ.

wk-ℕ : wk ρ t ≡ ℕ → t ≡ ℕ
wk-ℕ {t = ℕ} refl = refl

-- Inversion for zero.

wk-zero : wk ρ t ≡ zero → t ≡ zero
wk-zero {t = zero} refl = refl

-- Inversion for suc.

wk-suc :
  wk ρ t ≡ suc u →
  ∃ λ u′ → t ≡ suc u′ × wk ρ u′ ≡ u
wk-suc {t = suc _} refl = _ , refl , refl

-- Inversion for natrec.

wk-natrec :
  wk ρ t ≡ natrec p q r A u v w →
  ∃₄ λ A′ u′ v′ w′ →
     t ≡ natrec p q r A′ u′ v′ w′ ×
     wk (lift ρ) A′ ≡ A ×
     wk ρ u′ ≡ u × wk (lift (lift ρ)) v′ ≡ v × wk ρ w′ ≡ w
wk-natrec {t = natrec _ _ _ _ _ _ _} refl =
  _ , _ , _ , _ , refl , refl , refl , refl , refl
