------------------------------------------------------------------------
-- Some simple examples related to the erasure modality and extraction
------------------------------------------------------------------------

open import Graded.Modality.Instances.Erasure
open import Graded.Mode.Restrictions
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions

module Graded.Erasure.Examples
  {p q}
  (MR : Mode-restrictions)
  (TR : Type-restrictions Erasure)
  (open Type-restrictions TR)
  (UR : Usage-restrictions Erasure)
  -- It is assumed that "Π 𝟘 , p" is allowed.
  (Π-𝟘-ok : Π-allowed 𝟘 p)
  -- It is assumed that "Π ω , q" is allowed.
  (Π-ω-ok : Π-allowed ω q)
  where

open import Definition.Typed TR as DT hiding (id)
import Definition.Typed.Weakening TR as W
open import Definition.Untyped Erasure hiding (id; _∷_)

open import Graded.Modality.Instances.Erasure.Modality MR

open import Graded.Context ErasureModality
open import Graded.Context.Properties ErasureModality
open import Graded.Erasure.Extraction
  ErasureModality
  (Has-well-behaved-zero.is-𝟘? erasure-has-well-behaved-zero)
import Graded.Erasure.Target as T
import Graded.Erasure.Target.Properties as TP
open import Graded.Mode ErasureModality
open import Graded.Usage ErasureModality UR
open import Graded.Usage.Inversion ErasureModality UR

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Nullary
open import Tools.PropositionalEquality
open import Tools.Sum as ⊎ using (_⊎_; inj₁; inj₂)

private variable
  γ : Conₘ _
  Γ : Con Term _
  n : Nat

private

  -- Some lemmas used below.

  ⊢ℕ : ⊢ ε ∙ ℕ
  ⊢ℕ = ε ∙ ℕⱼ ε

  ⊢U : ⊢ ε ∙ U
  ⊢U = ε ∙ Uⱼ ε

  U⊢0 : ε ∙ U ⊢ var x0
  U⊢0 = univ (var ⊢U here)

  ⊢U0 : ⊢ ε ∙ U ∙ var x0
  ⊢U0 = ⊢U ∙ U⊢0

  U⊢id : ε ∙ U ⊢ lam ω (var x0) ∷ Π ω , q ▷ var x0 ▹ var x1
  U⊢id = lamⱼ U⊢0 (var ⊢U0 here) Π-ω-ok

  ΓU⊢id : ⊢ Γ → Γ ∙ U ⊢ lam ω (var x0) ∷ Π ω , q ▷ var x0 ▹ var x1
  ΓU⊢id ε = U⊢id
  ΓU⊢id (⊢Γ ∙ ⊢A) =
    W.wkTerm (W.lift (W.step W.id))
             (⊢Γ ∙ ⊢A ∙ Uⱼ (⊢Γ ∙ ⊢A))
             (ΓU⊢id ⊢Γ)

------------------------------------------------------------------------
-- A polymorphic identity function

-- A polymorphic identity function with an erased type argument.

id : Term n
id = lam 𝟘 (lam ω (var x0))

-- The polymorphic identity function is well-typed (in a well-formed
-- context).

⊢id : ⊢ Γ → Γ ⊢ id ∷ Π 𝟘 , p ▷ U ▹ Π ω , q ▷ var x0 ▹ var x1
⊢id ⊢Γ = lamⱼ (Uⱼ ⊢Γ) (ΓU⊢id ⊢Γ) Π-𝟘-ok

-- The polymorphic identity function is well-resourced (with respect
-- to the zero usage context).

▸id : 𝟘ᶜ {n} ▸[ 𝟙ᵐ ] id
▸id = lamₘ (lamₘ var)

-- The polymorphic identity function applied to two free variables

id-x1-x0 : Term 2
id-x1-x0 = id ∘⟨ 𝟘 ⟩ var x1 ∘⟨ ω ⟩ var x0

-- The term id-x0-x1 is well-typed (in a certain context)

⊢id-x1-x0 : ε ∙ U ∙ var x0 ⊢ id-x1-x0 ∷ var x1
⊢id-x1-x0 = (⊢id ⊢Γ ∘ⱼ var ⊢Γ (there here)) ∘ⱼ var ⊢Γ here
  where
  ⊢Γ = ε ∙ Uⱼ ε ∙ univ (var (ε ∙ Uⱼ ε) here)

-- The term id-x1-x0 is well-resources (with respect to a specific
-- usage context).

▸id-x1-x0 : ε ∙ 𝟘 ∙ ω ▸[ 𝟙ᵐ ] id-x1-x0
▸id-x1-x0 = subst (λ γ → γ ▸[ 𝟙ᵐ ] id-x1-x0)
                  (≈ᶜ→≡ (ε ∙ refl ∙ cong ⌜_⌝ (ᵐ·-identityʳ {m = 𝟙ᵐ})))
                  ((▸id ∘ₘ var) ∘ₘ var)

-- The polymorphic identity function applied to two arguments.

id-ℕ-zero : Term 0
id-ℕ-zero = id ∘⟨ 𝟘 ⟩ ℕ ∘⟨ ω ⟩ zero

-- The erasure of id-ℕ-zero includes an erased part (T.↯).

erase-id-ℕ-zero :
  erase id-ℕ-zero ≡ T.lam (T.lam (T.var x0)) T.∘ T.↯ T.∘ T.zero
erase-id-ℕ-zero = refl

-- The term id-ℕ-zero is well-typed (in the empty context).

⊢id-ℕ-zero : ε ⊢ id-ℕ-zero ∷ ℕ
⊢id-ℕ-zero = (⊢id ε ∘ⱼ ℕⱼ ε) ∘ⱼ zeroⱼ ε

-- The term id-ℕ-zero is well-resourced (with respect to the empty
-- usage context).

▸id-ℕ-zero : ε ▸[ 𝟙ᵐ ] id-ℕ-zero
▸id-ℕ-zero = (▸id ∘ₘ ℕₘ) ∘ₘ zeroₘ

-- The term id-ℕ-zero reduces to zero.

id-ℕ-zero⇒*zero : ε ⊢ id-ℕ-zero ⇒* zero ∷ ℕ
id-ℕ-zero⇒*zero =
  app-subst
    (β-red (Uⱼ ε) (ΠΣⱼ U⊢0 (univ (var ⊢U0 (there here))) Π-ω-ok)
       U⊢id (ℕⱼ ε) refl Π-𝟘-ok)
    (zeroⱼ ε) ⇨
  (β-red (ℕⱼ ε) (ℕⱼ ⊢ℕ) (var ⊢ℕ here) (zeroⱼ ε) refl Π-ω-ok ⇨
   DT.id (zeroⱼ ε))

-- The erasure of id-ℕ-zero reduces to zero.

erase-id-ℕ-zero⇒*zero : erase id-ℕ-zero T.⇒* T.zero
erase-id-ℕ-zero⇒*zero =
  T.trans (T.app-subst T.β-red) (T.trans T.β-red T.refl)

------------------------------------------------------------------------
-- A function that uses an erased argument in a non-erased position

-- A (closed) identity function that takes an erased argument.

id₀ : Term 0
id₀ = lam 𝟘 (var x0)

-- The function id₀ is well-typed (in the empty context).

⊢id₀ : ε ⊢ id₀ ∷ Π 𝟘 , p ▷ ℕ ▹ ℕ
⊢id₀ = lamⱼ (ℕⱼ ε) (var (ε ∙ ℕⱼ ε) here) Π-𝟘-ok

-- The function id₀ is not well-resourced.

¬▸id₀ : ¬ γ ▸[ 𝟙ᵐ ] id₀
¬▸id₀ ▸id₀ =
  case inv-usage-lam ▸id₀ of λ {
    (invUsageLam ▸0 _) →
  case inv-usage-var ▸0 of λ {
    (_ ∙ ()) }}

-- The function id₀ applied to an argument.

id₀-zero : Term 0
id₀-zero = id₀ ∘⟨ 𝟘 ⟩ zero

-- The erasure of id₀-zero includes an erased part (T.↯).

erase-id₀-zero : erase id₀-zero ≡ T.lam (T.var x0) T.∘ T.↯
erase-id₀-zero = refl

-- The term id₀-zero is well-typed (in the empty context).

⊢id₀-zero : ε ⊢ id₀-zero ∷ ℕ
⊢id₀-zero = ⊢id₀ ∘ⱼ zeroⱼ ε

-- The term id₀-zero is not well-resourced.

¬▸id₀-zero : ¬ γ ▸[ 𝟙ᵐ ] id₀-zero
¬▸id₀-zero ▸id₀-zero =
  case inv-usage-app ▸id₀-zero of λ {
    (invUsageApp ▸id₀ _ _) →
  ¬▸id₀ ▸id₀ }

-- The term id₀-zero reduces to zero.

id₀-zero⇒*zero : ε ⊢ id₀-zero ⇒* zero ∷ ℕ
id₀-zero⇒*zero =
  β-red (ℕⱼ ε) (ℕⱼ ⊢ℕ) (var ⊢ℕ here) (zeroⱼ ε) refl Π-𝟘-ok ⇨
  DT.id (zeroⱼ ε)

-- The erasure of id₀-zero reduces to T.↯.

erase-id₀-zero⇒*↯ : erase id₀-zero T.⇒* T.↯
erase-id₀-zero⇒*↯ = T.trans T.β-red T.refl

-- The erasure of id₀-zero does not reduce to T.zero.

¬erase-id₀-zero⇒*zero : ¬ erase id₀-zero T.⇒* T.zero
¬erase-id₀-zero⇒*zero =
  erase id₀-zero T.⇒* T.zero         →⟨ TP.red*Det erase-id₀-zero⇒*↯ ⟩
  T.↯ T.⇒* T.zero ⊎ T.zero T.⇒* T.↯  →⟨ ⊎.map TP.↯-noRed TP.zero-noRed ⟩
  T.zero ≡ T.↯ ⊎ T.↯ ≡ T.zero        →⟨ (λ { (inj₁ ()); (inj₂ ()) }) ⟩
  ⊥                                  □
