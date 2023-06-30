------------------------------------------------------------------------
-- Normal forms
------------------------------------------------------------------------

module Definition.Untyped.Normal-form {a} (M : Set a) where

open import Definition.Untyped M

open import Tools.Fin
open import Tools.Nat

private variable
  A B C c g k n t u : Term _
  p q r             : M
  b                 : BinderMode
  s                 : SigmaMode

mutual

  -- Normal forms.

  data Nf {m : Nat} : Term m → Set a where
    Uₙ     : Nf U
    ΠΣₙ    : Nf A → Nf B → Nf (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B)
    ℕₙ     : Nf ℕ
    Emptyₙ : Nf Empty
    Unitₙ  : Nf Unit

    lamₙ   : Nf t → Nf (lam q t)
    prodₙ  : Nf t → Nf u → Nf (prod s p t u)
    zeroₙ  : Nf zero
    sucₙ   : Nf t → Nf (suc t)
    starₙ  : Nf star

    ne     : NfNeutral n → Nf n

  -- Neutral terms for which the "non-neutral parts" are in normal
  -- form.

  data NfNeutral {m : Nat} : Term m → Set a where
    var       : (x : Fin m) → NfNeutral (var x)
    ∘ₙ        : NfNeutral k → Nf u → NfNeutral (k ∘⟨ q ⟩ u)
    fstₙ      : NfNeutral t → NfNeutral (fst p t)
    sndₙ      : NfNeutral t → NfNeutral (snd p t)
    natrecₙ   : Nf C → Nf c → Nf g → NfNeutral k →
                NfNeutral (natrec p q r C c g k)
    prodrecₙ  : Nf C → NfNeutral t → Nf u →
                NfNeutral (prodrec r p q C t u)
    Emptyrecₙ : Nf C → NfNeutral k → NfNeutral (Emptyrec p C k)

-- If NfNeutral n holds, then n is neutral.

nfNeutral : NfNeutral n → Neutral n
nfNeutral = λ where
  (var _)           → var _
  (∘ₙ n _)          → ∘ₙ (nfNeutral n)
  (fstₙ n)          → fstₙ (nfNeutral n)
  (sndₙ n)          → sndₙ (nfNeutral n)
  (natrecₙ _ _ _ n) → natrecₙ (nfNeutral n)
  (prodrecₙ _ n _)  → prodrecₙ (nfNeutral n)
  (Emptyrecₙ _ n)   → Emptyrecₙ (nfNeutral n)

-- Normal forms are in WHNF.

nfWhnf : Nf n → Whnf n
nfWhnf = λ where
  Uₙ          → Uₙ
  (ΠΣₙ _ _)   → ΠΣₙ
  ℕₙ          → ℕₙ
  Emptyₙ      → Emptyₙ
  Unitₙ       → Unitₙ
  (lamₙ _)    → lamₙ
  (prodₙ _ _) → prodₙ
  zeroₙ       → zeroₙ
  (sucₙ _)    → sucₙ
  starₙ       → starₙ
  (ne n)      → ne (nfNeutral n)
