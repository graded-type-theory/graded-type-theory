------------------------------------------------------------------------
-- Inversion lemmas for weakening
------------------------------------------------------------------------

module Definition.Untyped.Inversion {a} (M : Set a) where

open import Definition.Untyped M

open import Tools.Fin
open import Tools.Product
open import Tools.PropositionalEquality

private variable
  x              : Fin _
  ρ              : Wk _ _
  A B t t′ u v w : Term _
  p q r          : M
  s              : SigmaMode
  b              : BinderMode

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

-- Inversion for emptyrec.

wk-emptyrec :
  wk ρ t ≡ emptyrec p A u →
  ∃₂ λ A′ u′ → t ≡ emptyrec p A′ u′ × wk ρ A′ ≡ A × wk ρ u′ ≡ u
wk-emptyrec {t = emptyrec _ _ _} refl =
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

-- Inversion for Id.

wk-Id :
  wk ρ v ≡ Id A t u →
  ∃₃ λ A′ t′ u′ →
     v ≡ Id A′ t′ u′ ×
     wk ρ A′ ≡ A × wk ρ t′ ≡ t × wk ρ u′ ≡ u
wk-Id {v = Id _ _ _} refl = _ , _ , _ , refl , refl , refl , refl

-- Inversion for rfl.

wk-rfl : wk ρ t ≡ rfl → t ≡ rfl
wk-rfl {t = rfl} refl = refl

-- Inversion for J.

wk-J :
  wk ρ w ≡ J p q A t B u t′ v →
  ∃₃ λ A′ t″ B′ → ∃₃ λ u′ t‴ v′ →
     w ≡ J p q A′ t″ B′ u′ t‴ v′ ×
     wk ρ A′ ≡ A × wk ρ t″ ≡ t × wk (lift (lift ρ)) B′ ≡ B ×
     wk ρ u′ ≡ u × wk ρ t‴ ≡ t′ × wk ρ v′ ≡ v
wk-J {w = J _ _ _ _ _ _ _ _} refl =
  _ , _ , _ , _ , _ , _ , refl , refl , refl , refl , refl , refl , refl

-- Inversion for K.

wk-K :
  wk ρ w ≡ K p A t B u v →
  ∃₃ λ A′ t′ B′ → ∃₂ λ u′ v′ →
     w ≡ K p A′ t′ B′ u′ v′ ×
     wk ρ A′ ≡ A × wk ρ t′ ≡ t × wk (lift ρ) B′ ≡ B ×
     wk ρ u′ ≡ u × wk ρ v′ ≡ v
wk-K {w = K _ _ _ _ _ _} refl =
  _ , _ , _ , _ , _ , refl , refl , refl , refl , refl , refl

-- Inversion for []-cong.

wk-[]-cong :
  wk ρ w ≡ []-cong A t u v →
  ∃₄ λ A′ t′ u′ v′ →
     w ≡ []-cong A′ t′ u′ v′ ×
     wk ρ A′ ≡ A × wk ρ t′ ≡ t × wk ρ u′ ≡ u × wk ρ v′ ≡ v
wk-[]-cong {w = []-cong _ _ _ _} refl =
  _ , _ , _ , _ , refl , refl , refl , refl , refl
