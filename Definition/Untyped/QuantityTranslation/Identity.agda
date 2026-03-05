------------------------------------------------------------------------
-- If Definition.Untyped.QuantityTranslation is instantiated with
-- identity functions, then the translations are pointwise equal to
-- identity functions
------------------------------------------------------------------------

module Definition.Untyped.QuantityTranslation.Identity
  {a} (M : Set a)
  where

open import Tools.Fin
open import Tools.Function
open import Tools.PropositionalEquality

open import Definition.Untyped M
open import Definition.Untyped.Properties M
open import Definition.Untyped.QuantityTranslation {M₁ = M} idᶠ idᶠ

private variable
  p  : M
  c  : Constructor _ _
  t  : Term[ _ ] _
  k  : Term-kind
  ts : Args _ _
  ∇  : DCon (Term 0) _
  Δ  : Con Term _
  Γ  : Cons _ _
  σ  : Subst _ _
  x  : Fin _

opaque

  -- The function tr-BinderMode b is pointwise equal to an identity
  -- function.

  tr-BinderMode-id : ∀ b → tr-BinderMode b p ≡ p
  tr-BinderMode-id BMΠ     = refl
  tr-BinderMode-id (BMΣ _) = refl

opaque

  -- The function tr-Constructor is pointwise equal to an identity
  -- function.

  tr-Constructor-id : tr-Constructor c ≡ c
  tr-Constructor-id {c = defnᵏ _}        = refl
  tr-Constructor-id {c = Levelᵏ}         = refl
  tr-Constructor-id {c = zeroᵘᵏ}         = refl
  tr-Constructor-id {c = sucᵘᵏ}          = refl
  tr-Constructor-id {c = supᵘᵏ}          = refl
  tr-Constructor-id {c = ωᵘ+ᵏ _}         = refl
  tr-Constructor-id {c = levelᵏ}         = refl
  tr-Constructor-id {c = Uᵏ}             = refl
  tr-Constructor-id {c = Liftᵏ}          = refl
  tr-Constructor-id {c = liftᵏ}          = refl
  tr-Constructor-id {c = lowerᵏ}         = refl
  tr-Constructor-id {c = Emptyᵏ}         = refl
  tr-Constructor-id {c = emptyrecᵏ _}    = refl
  tr-Constructor-id {c = Unitᵏ _}        = refl
  tr-Constructor-id {c = starᵏ _}        = refl
  tr-Constructor-id {c = unitrecᵏ _ _}   = refl
  tr-Constructor-id {c = ΠΣᵏ b _ _}      = cong (flip (ΠΣᵏ _) _) $
                                           tr-BinderMode-id b
  tr-Constructor-id {c = lamᵏ _}         = refl
  tr-Constructor-id {c = appᵏ _}         = refl
  tr-Constructor-id {c = prodᵏ _ _}      = refl
  tr-Constructor-id {c = fstᵏ _}         = refl
  tr-Constructor-id {c = sndᵏ _}         = refl
  tr-Constructor-id {c = prodrecᵏ _ _ _} = refl
  tr-Constructor-id {c = ℕᵏ}             = refl
  tr-Constructor-id {c = zeroᵏ}          = refl
  tr-Constructor-id {c = sucᵏ}           = refl
  tr-Constructor-id {c = natrecᵏ _ _ _}  = refl
  tr-Constructor-id {c = Idᵏ}            = refl
  tr-Constructor-id {c = rflᵏ}           = refl
  tr-Constructor-id {c = Jᵏ _ _}         = refl
  tr-Constructor-id {c = Kᵏ _}           = refl
  tr-Constructor-id {c = []-congᵏ _}     = refl

opaque mutual

  -- The function tr-Term′ is pointwise equal to an identity function.

  tr-Term′-id : ∀ {n} {t : Term[ k ]′ n} → tr-Term′ t ≡ t
  tr-Term′-id {t = var _}   = refl
  tr-Term′-id {t = con _ _} = cong₂ con tr-Constructor-id tr-Args-id

  -- The function tr-Args is pointwise equal to an identity function.

  tr-Args-id : tr-Args ts ≡ ts
  tr-Args-id {ts = []}     = refl
  tr-Args-id {ts = _ ∷ₜ _} = cong₂ _∷ₜ_ tr-Term′-id tr-Args-id

opaque

  -- The function tr-Term is pointwise equal to an identity function.

  tr-Term-id : tr-Term t ≡ t
  tr-Term-id {t} rewrite tr-Term′-id {t = fromTerm t} =
    toTerm∘fromTerm _

opaque

  -- The function tr-Con is pointwise equal to an identity function.

  tr-Con-id : tr-Con Δ ≡ Δ
  tr-Con-id {Δ = ε}     = refl
  tr-Con-id {Δ = _ ∙ _} = cong₂ _∙_ tr-Con-id tr-Term-id

opaque

  -- The function tr-DCon is pointwise equal to an identity function.

  tr-DCon-id : tr-DCon ∇ ≡ ∇
  tr-DCon-id {∇ = ε}    = refl
  tr-DCon-id {∇ = _ ∙!} =
    cong₃ _∙⟨ _ ⟩[_∷_] tr-DCon-id tr-Term-id tr-Term-id

opaque

  -- The function tr-Cons is pointwise equal to an identity function.

  tr-Cons-id : tr-Cons Γ ≡ Γ
  tr-Cons-id = cong₂ _»_ tr-DCon-id tr-Con-id

opaque

  -- The function tr-Subst is pointwise equal to an identity function.

  tr-Subst-id : tr-Subst σ x ≡ σ x
  tr-Subst-id = tr-Term-id
