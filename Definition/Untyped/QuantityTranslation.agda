------------------------------------------------------------------------
-- Functions that can be used to replace quantities from one type with
-- quantities from another
------------------------------------------------------------------------

module Definition.Untyped.QuantityTranslation
  {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
  -- A translation function used for quantities other than those
  -- corresponding to the first components of Σ-types.
  (tr : M₁ → M₂)
  -- A translation function used for the first components of Σ-types.
  (tr-Σ : M₁ → M₂)
  where

open import Tools.Fin
open import Tools.Function
open import Tools.List
open import Tools.Nat
open import Tools.Product renaming (_,_ to _#_)
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality

open import Definition.Untyped
import Definition.Untyped.Properties

private
  module U₁  = Definition.Untyped M₁
  module U₂  = Definition.Untyped M₂
  module UP₁ = Definition.Untyped.Properties M₁
  module UP₂ = Definition.Untyped.Properties M₂

private variable
  m n         : Nat
  bs          : List _
  x           : Fin _
  p q r       : M₂
  s           : SigmaMode
  b           : BinderMode
  ts us       : GenTs _ _ _
  k l         : Kind _ _
  A B t u v w : Term _ _
  ρ           : Wk _ _
  σ           : Subst _ _ _

------------------------------------------------------------------------
-- Translation

-- Mode-dependent translation of quantities.

tr-BinderMode : BinderMode → M₁ → M₂
tr-BinderMode BMΠ     = tr
tr-BinderMode (BMΣ _) = tr-Σ

-- Translation of kinds.

tr-Kind : U₁.Kind bs → U₂.Kind bs
tr-Kind Ukind               = Ukind
tr-Kind (Binderkind b p q)  = Binderkind b (tr-BinderMode b p) (tr q)
tr-Kind (Lamkind p)         = Lamkind (tr p)
tr-Kind (Appkind p)         = Appkind (tr p)
tr-Kind (Prodkind s p)      = Prodkind s (tr-Σ p)
tr-Kind (Fstkind p)         = Fstkind (tr-Σ p)
tr-Kind (Sndkind p)         = Sndkind (tr-Σ p)
tr-Kind (Prodreckind r p q) = Prodreckind (tr r) (tr-Σ p) (tr q)
tr-Kind Natkind             = Natkind
tr-Kind Zerokind            = Zerokind
tr-Kind Suckind             = Suckind
tr-Kind (Natreckind p q r)  = Natreckind (tr p) (tr q) (tr r)
tr-Kind Unitkind            = Unitkind
tr-Kind Starkind            = Starkind
tr-Kind Emptykind           = Emptykind
tr-Kind (Emptyreckind p)    = Emptyreckind (tr p)

mutual

  -- Translation of terms.

  tr-Term : U₁.Term n → U₂.Term n
  tr-Term (var x)    = var x
  tr-Term (gen k ts) = gen (tr-Kind k) (tr-GenTs ts)

  -- Translation for GenTs.

  tr-GenTs : U₁.GenTs U₁.Term n bs → U₂.GenTs U₂.Term n bs
  tr-GenTs []       = []
  tr-GenTs (t ∷ ts) = tr-Term t ∷ tr-GenTs ts

-- Translation of contexts.

tr-Con : U₁.Con U₁.Term n → U₂.Con U₂.Term n
tr-Con ε       = ε
tr-Con (Γ ∙ A) = tr-Con Γ ∙ tr-Term A

-- Translation of substitutions.

tr-Subst : U₁.Subst m n → U₂.Subst m n
tr-Subst σ x = tr-Term (σ x)

------------------------------------------------------------------------
-- A lemma that applies when tr-Σ is pointwise equal to tr

module _ (tr-Σ≡tr : ∀ {p} → tr-Σ p ≡ tr p) where

  -- The function tr-BinderMode b is pointwise equal to tr.

  tr-BinderMode-one-function : ∀ {p} b → tr-BinderMode b p ≡ tr p
  tr-BinderMode-one-function BMΠ     = refl
  tr-BinderMode-one-function (BMΣ _) = tr-Σ≡tr

------------------------------------------------------------------------
-- Translation preserves various things

-- The function tr-Term preserves neutrality.

tr-Neutral : U₁.Neutral t → U₂.Neutral (tr-Term t)
tr-Neutral (var x)       = var x
tr-Neutral (∘ₙ n)        = ∘ₙ (tr-Neutral n)
tr-Neutral (fstₙ n)      = fstₙ (tr-Neutral n)
tr-Neutral (sndₙ n)      = sndₙ (tr-Neutral n)
tr-Neutral (natrecₙ n)   = natrecₙ (tr-Neutral n)
tr-Neutral (prodrecₙ n)  = prodrecₙ (tr-Neutral n)
tr-Neutral (Emptyrecₙ n) = Emptyrecₙ (tr-Neutral n)

-- The function tr-Term takes WHNFs to WHNFs.

tr-Whnf : U₁.Whnf t → U₂.Whnf (tr-Term t)
tr-Whnf Uₙ                = Uₙ
tr-Whnf (ΠΣₙ {b = BMΠ})   = ΠΣₙ
tr-Whnf (ΠΣₙ {b = BMΣ _}) = ΠΣₙ
tr-Whnf ℕₙ                = ℕₙ
tr-Whnf Unitₙ             = Unitₙ
tr-Whnf Emptyₙ            = Emptyₙ
tr-Whnf lamₙ              = lamₙ
tr-Whnf zeroₙ             = zeroₙ
tr-Whnf sucₙ              = sucₙ
tr-Whnf starₙ             = starₙ
tr-Whnf prodₙ             = prodₙ
tr-Whnf (ne n)            = ne (tr-Neutral n)

------------------------------------------------------------------------
-- Translation commutes with various things

mutual

  -- Weakening commutes with translation.

  tr-Term-wk : U₂.wk ρ (tr-Term t) ≡ tr-Term (U₁.wk ρ t)
  tr-Term-wk {t = var _}   = refl
  tr-Term-wk {t = gen _ _} = cong (gen _) tr-GenTs-wkGen

  -- Weakening commutes with translation.

  tr-GenTs-wkGen : U₂.wkGen ρ (tr-GenTs ts) ≡ tr-GenTs (U₁.wkGen ρ ts)
  tr-GenTs-wkGen {ts = []}    = refl
  tr-GenTs-wkGen {ts = _ ∷ _} = cong₂ _∷_ tr-Term-wk tr-GenTs-wkGen

-- The function liftSubst commutes with translation.

tr-Subst-liftSubst :
  ∀ x → U₂.liftSubst (tr-Subst σ) x ≡ tr-Subst (U₁.liftSubst σ) x
tr-Subst-liftSubst x0     = refl
tr-Subst-liftSubst (_ +1) = tr-Term-wk

-- The function liftSubstn commutes with translation.

tr-Subst-liftSubstn :
  ∀ n {x} →
  U₂.liftSubstn (tr-Subst σ) n x ≡ tr-Subst (U₁.liftSubstn σ n) x
tr-Subst-liftSubstn 0                      = refl
tr-Subst-liftSubstn {σ = σ} (1+ n) {x = x} =
  U₂.liftSubst (U₂.liftSubstn (tr-Subst σ) n) x  ≡⟨ UP₂.substVar-lift (λ _ → tr-Subst-liftSubstn n) x ⟩
  U₂.liftSubst (tr-Subst (U₁.liftSubstn σ n)) x  ≡⟨ tr-Subst-liftSubst x ⟩
  tr-Subst (U₁.liftSubst (U₁.liftSubstn σ n)) x  ∎

-- The function consSubst commutes with translation.

tr-Subst-consSubst :
  ∀ x →
  U₂.consSubst (tr-Subst σ) (tr-Term t) x ≡
  tr-Subst (U₁.consSubst σ t) x
tr-Subst-consSubst x0     = refl
tr-Subst-consSubst (_ +1) = refl

-- The function idSubst commutes with translation.

tr-Subst-idSubst : U₂.idSubst x ≡ tr-Subst U₁.idSubst x
tr-Subst-idSubst = refl

-- The function sgSubst commutes with translation.

tr-Subst-sgSubst :
  ∀ x → U₂.sgSubst (tr-Term u) x ≡ tr-Subst (U₁.sgSubst u) x
tr-Subst-sgSubst = tr-Subst-consSubst

-- The function wk1Subst commutes with translation.

tr-Subst-wk1Subst :
  ∀ x → U₂.wk1Subst (tr-Subst σ) x ≡ tr-Subst (U₁.wk1Subst σ) x
tr-Subst-wk1Subst x0     = tr-Term-wk
tr-Subst-wk1Subst (_ +1) = tr-Term-wk

mutual

  -- Substitution commutes with translation.

  tr-Term-subst :
    ∀ t → tr-Term t U₂.[ tr-Subst σ ] ≡ tr-Term (t U₁.[ σ ])
  tr-Term-subst (var _)   = refl
  tr-Term-subst (gen _ _) = cong (gen _) tr-GenTs-substGen

  -- Substitution commutes with translation.

  tr-GenTs-substGen :
    U₂.substGen (tr-Subst σ) (tr-GenTs ts) ≡ tr-GenTs (U₁.substGen σ ts)
  tr-GenTs-substGen         {ts = []}              = refl
  tr-GenTs-substGen {σ = σ} {ts = _∷_ {b = b} t _} = cong₂ _∷_
    (tr-Term t U₂.[ U₂.liftSubstn (tr-Subst σ) b ]  ≡⟨ UP₂.substVar-to-subst (λ _ → tr-Subst-liftSubstn b) (tr-Term t) ⟩
     tr-Term t U₂.[ tr-Subst (U₁.liftSubstn σ b) ]  ≡⟨ tr-Term-subst t ⟩
     tr-Term (t U₁.[ U₁.liftSubstn σ b ])           ∎)
    tr-GenTs-substGen

-- Substitution commutes with translation.

tr-Term-[] : ∀ t → tr-Term t U₂.[ tr-Term u ]₀ ≡ tr-Term (t U₁.[ u ]₀)
tr-Term-[] {u = u} t =
  tr-Term t U₂.[ U₂.sgSubst (tr-Term u) ]   ≡⟨ UP₂.substVar-to-subst tr-Subst-sgSubst (tr-Term t) ⟩
  tr-Term t U₂.[ tr-Subst (U₁.sgSubst u) ]  ≡⟨ tr-Term-subst t ⟩
  tr-Term (t U₁.[ U₁.sgSubst u ])           ∎

private

  -- A lemma used below.

  [,]-lemma :
    ∀ x →
    U₂.consSubst (U₂.sgSubst (tr-Term t)) (tr-Term u) x ≡
    tr-Subst (U₁.consSubst (U₁.sgSubst t) u) x
  [,]-lemma {t = t} {u = u} x =
    U₂.consSubst (U₂.sgSubst (tr-Term t)) (tr-Term u) x   ≡⟨ UP₂.consSubst-cong tr-Subst-sgSubst x ⟩
    U₂.consSubst (tr-Subst (U₁.sgSubst t)) (tr-Term u) x  ≡⟨ tr-Subst-consSubst x ⟩
    tr-Subst (U₁.consSubst (U₁.sgSubst t) u) x            ∎

-- Substitution commutes with translation.

tr-Term-[,] :
  ∀ t → tr-Term t U₂.[ tr-Term u , tr-Term v ] ≡ tr-Term (t U₁.[ u , v ])
tr-Term-[,] {u = u} {v = v} t =
  tr-Term t
    U₂.[ U₂.consSubst (U₂.sgSubst (tr-Term u)) (tr-Term v) ]  ≡⟨ UP₂.substVar-to-subst [,]-lemma (tr-Term t) ⟩

  tr-Term t
    U₂.[ tr-Subst (U₁.consSubst (U₁.sgSubst u) v)]            ≡⟨ tr-Term-subst t ⟩

  tr-Term (t U₁.[ U₁.consSubst (U₁.sgSubst u) v ])            ∎

private

  -- A lemma used below.

  []↑-lemma :
    ∀ x →
    U₂.consSubst (U₂.wk1Subst U₂.idSubst) (tr-Term t) x ≡
    tr-Subst (U₁.consSubst (U₁.wk1Subst U₁.idSubst) t) x
  []↑-lemma {t = t} x =
    U₂.consSubst (U₂.wk1Subst U₂.idSubst) (tr-Term t) x             ≡⟨ UP₂.consSubst-cong tr-Subst-wk1Subst x ⟩
    U₂.consSubst (tr-Subst (U₁.wk1Subst U₁.idSubst)) (tr-Term t) x  ≡⟨ tr-Subst-consSubst x ⟩
    tr-Subst (U₁.consSubst (U₁.wk1Subst U₁.idSubst) t) x            ∎

-- Substitution commutes with translation.

tr-Term-[]↑ : ∀ t → tr-Term t U₂.[ tr-Term u ]↑ ≡ tr-Term (t U₁.[ u ]↑)
tr-Term-[]↑ {u = u} t =
  tr-Term t
    U₂.[ U₂.consSubst (U₂.wk1Subst U₂.idSubst) (tr-Term u) ]   ≡⟨ UP₂.substVar-to-subst []↑-lemma (tr-Term t) ⟩

  tr-Term t
    U₂.[ tr-Subst (U₁.consSubst (U₁.wk1Subst U₁.idSubst) u) ]  ≡⟨ tr-Term-subst t ⟩

  tr-Term (t U₁.[ U₁.consSubst (U₁.wk1Subst U₁.idSubst) u ])   ∎

private

  -- A lemma used below.

  []↑²-lemma :
    ∀ x →
    U₂.consSubst (U₂.wk1Subst (U₂.wk1Subst U₂.idSubst)) (tr-Term t) x ≡
    tr-Subst (U₁.consSubst (U₁.wk1Subst (U₁.wk1Subst U₁.idSubst)) t) x
  []↑²-lemma {t = t} x =
    U₂.consSubst (U₂.wk1Subst (U₂.wk1Subst U₂.idSubst)) (tr-Term t) x   ≡⟨ UP₂.consSubst-cong (UP₂.wk1Subst-cong tr-Subst-wk1Subst) x ⟩

    U₂.consSubst (U₂.wk1Subst (tr-Subst (U₁.wk1Subst U₁.idSubst)))
      (tr-Term t) x                                                     ≡⟨ UP₂.consSubst-cong tr-Subst-wk1Subst x ⟩

    U₂.consSubst (tr-Subst (U₁.wk1Subst (U₁.wk1Subst U₁.idSubst)))
      (tr-Term t) x                                                     ≡⟨ tr-Subst-consSubst x ⟩

    tr-Subst (U₁.consSubst (U₁.wk1Subst (U₁.wk1Subst U₁.idSubst)) t) x  ∎

-- Substitution commutes with translation.

tr-Term-[]↑² :
  ∀ t → tr-Term t U₂.[ tr-Term u ]↑² ≡ tr-Term (t U₁.[ u ]↑²)
tr-Term-[]↑² {u = u} t =
  tr-Term t
    U₂.[ U₂.consSubst (U₂.wk1Subst (U₂.wk1Subst U₂.idSubst)) (tr-Term u) ]   ≡⟨ UP₂.substVar-to-subst []↑²-lemma (tr-Term t) ⟩

  tr-Term t
    U₂.[ tr-Subst (U₁.consSubst (U₁.wk1Subst (U₁.wk1Subst U₁.idSubst)) u) ]  ≡⟨ tr-Term-subst t ⟩

  tr-Term (t U₁.[ U₁.consSubst (U₁.wk1Subst (U₁.wk1Subst U₁.idSubst)) u ])   ∎

------------------------------------------------------------------------
-- Inversion lemmas for translation

-- Inversion for var.

tr-Term-var : tr-Term t ≡ var x → t ≡ var x
tr-Term-var {t = var _} refl = refl

-- Inversion for U.

tr-Term-U : tr-Term t ≡ U → t ≡ U
tr-Term-U {t = U} refl = refl

-- Inversion for ΠΣ⟨_⟩_,_▷_▹_.

tr-Term-ΠΣ :
  tr-Term t ≡ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
  ∃₄ λ p′ q′ A′ B′ →
     t ≡ ΠΣ⟨ b ⟩ p′ , q′ ▷ A′ ▹ B′ ×
     tr-BinderMode b p′ ≡ p × tr q′ ≡ q ×
     tr-Term A′ ≡ A × tr-Term B′ ≡ B
tr-Term-ΠΣ {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} refl =
  _ # _ # _ # _ # refl # refl # refl # refl # refl

-- Inversion for lam.

tr-Term-lam :
  tr-Term t ≡ lam p u →
  ∃₂ λ p′ u′ → t ≡ lam p′ u′ × tr p′ ≡ p × tr-Term u′ ≡ u
tr-Term-lam {t = lam _ _} refl = _ # _ # refl # refl # refl

-- Inversion for _∘⟨_⟩_.

tr-Term-∘ :
  tr-Term t ≡ u ∘⟨ p ⟩ v →
  ∃₃ λ u′ p′ v′ →
     t ≡ u′ ∘⟨ p′ ⟩ v′ × tr-Term u′ ≡ u × tr p′ ≡ p × tr-Term v′ ≡ v
tr-Term-∘ {t = _ ∘⟨ _ ⟩ _} refl = _ # _ # _ # refl # refl # refl # refl

-- Inversion for prod.

tr-Term-prod :
  tr-Term t ≡ prod s p u v →
  ∃₃ λ p′ u′ v′ →
     t ≡ prod s p′ u′ v′ ×
     tr-BinderMode (BMΣ s) p′ ≡ p × tr-Term u′ ≡ u × tr-Term v′ ≡ v
tr-Term-prod {t = prod _ _ _ _} refl =
  _ # _ # _ # refl # refl # refl # refl

-- Inversion for fst.

tr-Term-fst :
  tr-Term t ≡ fst p u →
  ∃₂ λ p′ u′ → t ≡ fst p′ u′ × tr-Σ p′ ≡ p × tr-Term u′ ≡ u
tr-Term-fst {t = fst _ _} refl = _ # _ # refl # refl # refl

-- Inversion for snd.

tr-Term-snd :
  tr-Term t ≡ snd p u →
  ∃₂ λ p′ u′ → t ≡ snd p′ u′ × tr-Σ p′ ≡ p × tr-Term u′ ≡ u
tr-Term-snd {t = snd _ _} refl = _ # _ # refl # refl # refl

-- Inversion for prodrec.

tr-Term-prodrec :
  tr-Term t ≡ prodrec r p q A u v →
  ∃₃ λ r′ p′ q′ → ∃₃ λ A′ u′ v′ →
     t ≡ prodrec r′ p′ q′ A′ u′ v′ × tr r′ ≡ r × tr-Σ p′ ≡ p ×
     tr q′ ≡ q × tr-Term A′ ≡ A × tr-Term u′ ≡ u × tr-Term v′ ≡ v
tr-Term-prodrec {t = prodrec _ _ _ _ _ _} refl =
  _ # _ # _ # _ # _ # _ # refl # refl # refl # refl # refl # refl # refl

-- Inversion for Unit.

tr-Term-Unit : tr-Term t ≡ Unit → t ≡ Unit
tr-Term-Unit {t = Unit} refl = refl

-- Inversion for star.

tr-Term-star : tr-Term t ≡ star → t ≡ star
tr-Term-star {t = star} refl = refl

-- Inversion for Empty.

tr-Term-Empty : tr-Term t ≡ Empty → t ≡ Empty
tr-Term-Empty {t = Empty} refl = refl

-- Inversion for Emptyrec.

tr-Term-Emptyrec :
  tr-Term t ≡ Emptyrec p A u →
  ∃₃ λ p′ A′ u′ →
     t ≡ Emptyrec p′ A′ u′ × tr p′ ≡ p × tr-Term A′ ≡ A × tr-Term u′ ≡ u
tr-Term-Emptyrec {t = Emptyrec _ _ _} refl =
  _ # _ # _ # refl # refl # refl # refl

-- Inversion for ℕ.

tr-Term-ℕ : tr-Term t ≡ ℕ → t ≡ ℕ
tr-Term-ℕ {t = ℕ} refl = refl

-- Inversion for zero.

tr-Term-zero : tr-Term t ≡ zero → t ≡ zero
tr-Term-zero {t = zero} refl = refl

-- Inversion for suc.

tr-Term-suc :
  tr-Term t ≡ suc u →
  ∃ λ u′ → t ≡ suc u′ × tr-Term u′ ≡ u
tr-Term-suc {t = suc _} refl = _ # refl # refl

-- Inversion for natrec.

tr-Term-natrec :
  tr-Term t ≡ natrec p q r A u v w →
  ∃₃ λ p′ q′ r′ → ∃₄ λ A′ u′ v′ w′ →
     t ≡ natrec p′ q′ r′ A′ u′ v′ w′ ×
     tr p′ ≡ p × tr q′ ≡ q × tr r′ ≡ r ×
     tr-Term A′ ≡ A × tr-Term u′ ≡ u × tr-Term v′ ≡ v × tr-Term w′ ≡ w
tr-Term-natrec {t = natrec _ _ _ _ _ _ _} refl =
  _ # _ # _ # _ # _ # _ # _ #
    refl # refl # refl # refl # refl # refl # refl # refl

mutual

  -- Inversion for wk.

  tr-Term-wk⁻¹ :
    tr-Term t ≡ U₂.wk ρ u →
    ∃ λ t′ → tr-Term t′ ≡ u × t ≡ U₁.wk ρ t′
  tr-Term-wk⁻¹ {t = var _}   {u = var x}   refl = var x # refl # refl
  tr-Term-wk⁻¹ {t = gen k _} {u = gen _ _} eq   =
    case U₂.gen-cong⁻¹ eq of λ where
      (refl # refl # eq) →
        case tr-GenTs-wkGen⁻¹ eq of λ (ts′ # eq₁ # eq₂) →
        gen k ts′ # cong (gen _) eq₁ # cong (gen _) eq₂

  -- Inversion for wkGen.

  tr-GenTs-wkGen⁻¹ :
    tr-GenTs ts ≡ U₂.wkGen ρ us →
    ∃ λ ts′ → tr-GenTs ts′ ≡ us × ts ≡ U₁.wkGen ρ ts′
  tr-GenTs-wkGen⁻¹ {ts = []}    {us = []}    refl = [] # refl # refl
  tr-GenTs-wkGen⁻¹ {ts = _ ∷ _} {us = _ ∷ _} eq   =
    case U₂.∷-cong⁻¹ eq of λ (eq₁ # eq₂) →
    case tr-Term-wk⁻¹ eq₁ of λ (t′ # eq₃ # eq₄) →
    case tr-GenTs-wkGen⁻¹ eq₂ of λ (ts′ # eq₅ # eq₆) →
    t′ U₂.∷ ts′ # cong₂ _∷_ eq₃ eq₅ # cong₂ _∷_ eq₄ eq₆

------------------------------------------------------------------------
-- Results that are proved under the assumption that the translation
-- functions tr and tr-Σ are injective

module Injective
  -- The function tr is injective.
  (tr-injective : ∀ {p q} → tr p ≡ tr q → p ≡ q)
  -- The function tr-Σ is injective.
  (tr-Σ-injective : ∀ {p q} → tr-Σ p ≡ tr-Σ q → p ≡ q)
  where

  ----------------------------------------------------------------------
  -- Certain functions are injective

  -- The function tr-BinderMode b is injective.

  tr-BinderMode-injective :
    ∀ {p q} b → tr-BinderMode b p ≡ tr-BinderMode b q → p ≡ q
  tr-BinderMode-injective BMΠ     = tr-injective
  tr-BinderMode-injective (BMΣ _) = tr-Σ-injective

  -- The function tr-Kind is injective.

  tr-Kind-injective : tr-Kind k ≡ tr-Kind l → k ≡ l
  tr-Kind-injective {k = Ukind}     {l = Ukind}     refl = refl
  tr-Kind-injective {k = Natkind}   {l = Natkind}   refl = refl
  tr-Kind-injective {k = Zerokind}  {l = Zerokind}  refl = refl
  tr-Kind-injective {k = Suckind}   {l = Suckind}   refl = refl
  tr-Kind-injective {k = Unitkind}  {l = Unitkind}  refl = refl
  tr-Kind-injective {k = Starkind}  {l = Starkind}  refl = refl
  tr-Kind-injective {k = Emptykind} {l = Emptykind} refl =
    refl
  tr-Kind-injective {k = Binderkind b p q} {l = Binderkind _ _ _} eq
    with tr-BinderMode b p in tr-p≡ | tr q in tr-q≡
  tr-Kind-injective {k = Binderkind b _ _} refl | _ | _ =
    cong₂ (Binderkind _)
      (tr-BinderMode-injective b tr-p≡)
      (tr-injective tr-q≡)
  tr-Kind-injective {k = Lamkind p} {l = Lamkind _} eq
    with tr p in tr-p≡
  tr-Kind-injective refl | _ =
    cong Lamkind (tr-injective tr-p≡)
  tr-Kind-injective {k = Appkind p} {l = Appkind _} eq
    with tr p in tr-p≡
  tr-Kind-injective refl | _ =
    cong Appkind (tr-injective tr-p≡)
  tr-Kind-injective {k = Prodkind s p} {l = Prodkind _ _} eq
    with tr-Σ p in tr-p≡
  tr-Kind-injective refl | _ =
    cong (Prodkind _) (tr-Σ-injective tr-p≡)
  tr-Kind-injective {k = Fstkind p} {l = Fstkind _} eq
    with tr-Σ p in tr-p≡
  tr-Kind-injective refl | _ =
    cong Fstkind (tr-Σ-injective tr-p≡)
  tr-Kind-injective {k = Sndkind p} {l = Sndkind _} eq
    with tr-Σ p in tr-p≡
  tr-Kind-injective refl | _ =
    cong Sndkind (tr-Σ-injective tr-p≡)
  tr-Kind-injective {k = Prodreckind r p q} {l = Prodreckind _ _ _} eq
    with tr r in tr-r≡ | tr-Σ p in tr-p≡ | tr q in tr-q≡
  tr-Kind-injective refl | _ | _ | _ =
    cong₃ Prodreckind (tr-injective tr-r≡) (tr-Σ-injective tr-p≡)
      (tr-injective tr-q≡)
  tr-Kind-injective {k = Natreckind p q r} {l = Natreckind _ _ _} eq
    with tr p in tr-p≡ | tr q in tr-q≡ | tr r in tr-r≡
  tr-Kind-injective refl | _ | _ | _ =
    cong₃ Natreckind (tr-injective tr-p≡) (tr-injective tr-q≡)
      (tr-injective tr-r≡)
  tr-Kind-injective {k = Emptyreckind p} {l = Emptyreckind _} eq
    with tr p in tr-p≡
  tr-Kind-injective refl | _ =
    cong Emptyreckind (tr-injective tr-p≡)

  mutual

    -- The function tr-Term is injective.

    tr-Term-injective : tr-Term t ≡ tr-Term u → t ≡ u
    tr-Term-injective {t = var _}   {u = var _}   refl = refl
    tr-Term-injective {t = gen _ _} {u = gen _ _} eq   =
      case U₂.gen-cong⁻¹ eq of λ where
        (refl # eq₁ # eq₂) →
          case tr-Kind-injective eq₁ of λ where
            refl → cong (gen _) (tr-GenTs-injective eq₂)

    -- The function tr-GenTs is injective.

    tr-GenTs-injective : tr-GenTs ts ≡ tr-GenTs us → ts ≡ us
    tr-GenTs-injective {ts = []}    {us = []}    _  = refl
    tr-GenTs-injective {ts = _ ∷ _} {us = _ ∷ _} eq =
      case U₂.∷-cong⁻¹ eq of λ (eq₁ # eq₂) →
      cong₂ _∷_ (tr-Term-injective eq₁) (tr-GenTs-injective eq₂)

  ----------------------------------------------------------------------
  -- Inversion lemmas

  mutual

    -- Inversion for subst.

    tr-Term-subst⁻¹ :
      tr-Term t ≡ u U₂.[ tr-Subst σ ] →
      ∃ λ u′ → tr-Term u′ ≡ u × t ≡ u′ U₁.[ σ ]
    tr-Term-subst⁻¹ {t = t} {u = var x} {σ = σ} eq =
      var x # refl # tr-Term-injective (
        tr-Term t                 ≡⟨ eq ⟩
        var x U₂.[ tr-Subst σ ]   ≡˘⟨ tr-Term-subst {σ = σ} (var x) ⟩
        tr-Term (var x U₁.[ σ ])  ∎)
    tr-Term-subst⁻¹ {t = gen k _} {u = gen _ _} eq =
      case U₂.gen-cong⁻¹ eq of λ where
        (refl # refl # eq) →
          case tr-Term-substGen⁻¹ eq of λ where
            (us′ # refl # refl) → gen k us′ # refl # refl

    -- Inversion for substGen.

    tr-Term-substGen⁻¹ :
      tr-GenTs ts ≡ U₂.substGen (tr-Subst σ) us →
      ∃ λ us′ → tr-GenTs us′ ≡ us × ts ≡ U₁.substGen σ us′
    tr-Term-substGen⁻¹ {ts = []} {us = []} _ =
      [] # refl # refl
    tr-Term-substGen⁻¹ {ts = _∷_ {b = b} t _} {σ = σ} {us = u ∷ _} eq =
      case U₂.∷-cong⁻¹ eq of λ (eq₁ # eq₂) →
      case
        tr-Term t                              ≡⟨ eq₁ ⟩
        u U₂.[ U₂.liftSubstn (tr-Subst σ) b ]  ≡⟨ UP₂.substVar-to-subst (λ _ → tr-Subst-liftSubstn b) u ⟩
        u U₂.[ tr-Subst (U₁.liftSubstn σ b) ]  ∎
      of λ lemma →
      case tr-Term-substGen⁻¹ eq₂ of λ where
        (us′ # refl # refl) →
          case tr-Term-subst⁻¹ {u = u} lemma of λ where
            (u′ # refl # refl) → u′ ∷ us′ # refl # refl

  -- Inversion for _[_].

  tr-Term-[]⁻¹ :
    ∀ u → tr-Term t ≡ u U₂.[ tr-Term v ]₀ →
    ∃ λ u′ → tr-Term u′ ≡ u × t ≡ u′ U₁.[ v ]₀
  tr-Term-[]⁻¹ {t = t} {v = v} u eq = tr-Term-subst⁻¹ (
    tr-Term t                         ≡⟨ eq ⟩
    u U₂.[ tr-Term v ]₀               ≡⟨⟩
    u U₂.[ U₂.sgSubst (tr-Term v) ]   ≡⟨ UP₂.substVar-to-subst tr-Subst-sgSubst u ⟩
    u U₂.[ tr-Subst (U₁.sgSubst v) ]  ∎)

  -- Inversion for _[_,_].

  tr-Term-[,]⁻¹ :
    tr-Term t ≡ u U₂.[ tr-Term v , tr-Term w ] →
    ∃ λ u′ → tr-Term u′ ≡ u × t ≡ u′ U₁.[ v , w ]
  tr-Term-[,]⁻¹ {t = t} {u = u} {v = v} {w = w} eq = tr-Term-subst⁻¹ (
    tr-Term t                                                   ≡⟨ eq ⟩
    u U₂.[ tr-Term v , tr-Term w ]                              ≡⟨⟩
    u U₂.[ U₂.consSubst (U₂.sgSubst (tr-Term v)) (tr-Term w) ]  ≡⟨ UP₂.substVar-to-subst [,]-lemma u ⟩
    u U₂.[ tr-Subst (U₁.consSubst (U₁.sgSubst v) w) ]           ∎)

  -- Inversion for _[_]↑.

  tr-Term-[]↑⁻¹ :
    tr-Term t ≡ u U₂.[ tr-Term v ]↑ →
    ∃ λ u′ → tr-Term u′ ≡ u × t ≡ u′ U₁.[ v ]↑
  tr-Term-[]↑⁻¹ {t = t} {u = u} {v = v} eq = tr-Term-subst⁻¹ (
    tr-Term t                                                    ≡⟨ eq ⟩
    u U₂.[ tr-Term v ]↑                                          ≡⟨⟩
    u U₂.[ U₂.consSubst (U₂.wk1Subst U₂.idSubst) (tr-Term v) ]   ≡⟨ UP₂.substVar-to-subst []↑-lemma u ⟩
    u U₂.[ tr-Subst (U₁.consSubst (U₁.wk1Subst U₁.idSubst) v) ]  ∎)

  -- Inversion for _[_]↑².

  tr-Term-[]↑²⁻¹ :
    tr-Term t ≡ u U₂.[ tr-Term v ]↑² →
    ∃ λ u′ → tr-Term u′ ≡ u × t ≡ u′ U₁.[ v ]↑²
  tr-Term-[]↑²⁻¹ {t = t} {u = u} {v = v} eq = tr-Term-subst⁻¹ (
    tr-Term t                                                                  ≡⟨ eq ⟩
    u U₂.[ tr-Term v ]↑²                                                       ≡⟨⟩
    u U₂.[ U₂.consSubst (U₂.wk1Subst (U₂.wk1Subst U₂.idSubst)) (tr-Term v) ]   ≡⟨ UP₂.substVar-to-subst []↑²-lemma u ⟩
    u U₂.[ tr-Subst (U₁.consSubst (U₁.wk1Subst (U₁.wk1Subst U₁.idSubst)) v) ]  ∎)
