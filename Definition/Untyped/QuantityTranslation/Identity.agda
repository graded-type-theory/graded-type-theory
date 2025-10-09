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
  k  : Kind _
  t  : Term _
  ts : GenTs _ _ _
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

  -- The function tr-Kind is pointwise equal to an identity function.

  tr-Kind-id : tr-Kind k ≡ k
  tr-Kind-id {k = Defnkind _}        = refl
  tr-Kind-id {k = Ukind _}           = refl
  tr-Kind-id {k = Binderkind b _ _}  = cong (flip (Binderkind _) _) $
                                       tr-BinderMode-id b
  tr-Kind-id {k = Lamkind _}         = refl
  tr-Kind-id {k = Appkind _}         = refl
  tr-Kind-id {k = Prodkind _ _}      = refl
  tr-Kind-id {k = Fstkind _}         = refl
  tr-Kind-id {k = Sndkind _}         = refl
  tr-Kind-id {k = Prodreckind _ _ _} = refl
  tr-Kind-id {k = Natkind}           = refl
  tr-Kind-id {k = Zerokind}          = refl
  tr-Kind-id {k = Suckind}           = refl
  tr-Kind-id {k = Natreckind _ _ _}  = refl
  tr-Kind-id {k = Unitkind _ _}      = refl
  tr-Kind-id {k = Starkind _ _}      = refl
  tr-Kind-id {k = Unitreckind _ _ _} = refl
  tr-Kind-id {k = Emptykind}         = refl
  tr-Kind-id {k = Emptyreckind _}    = refl
  tr-Kind-id {k = Idkind}            = refl
  tr-Kind-id {k = Reflkind}          = refl
  tr-Kind-id {k = Jkind _ _}         = refl
  tr-Kind-id {k = Kkind _}           = refl
  tr-Kind-id {k = Boxcongkind _}     = refl

opaque mutual

  -- The function tr-Term′ is pointwise equal to an identity function.

  tr-Term′-id : ∀ {n} {t : Term′ n} → tr-Term′ t ≡ t
  tr-Term′-id {t = var _}   = refl
  tr-Term′-id {t = gen _ _} = cong₂ gen tr-Kind-id tr-GenTs-id

  -- The function tr-GenTs is pointwise equal to an identity function.

  tr-GenTs-id : tr-GenTs ts ≡ ts
  tr-GenTs-id {ts = []}     = refl
  tr-GenTs-id {ts = _ ∷ₜ _} = cong₂ _∷ₜ_ tr-Term′-id tr-GenTs-id

opaque

  -- The function tr-Term is pointwise equal to an identity function.

  tr-Term-id : tr-Term t ≡ t
  tr-Term-id {t} rewrite tr-Term′-id {t = fromTerm t} = toTerm∘fromTerm t

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
