------------------------------------------------------------------------
-- Some examples related to the erasure modality and extraction
------------------------------------------------------------------------

open import Tools.Level

open import Graded.Modality.Instances.Erasure
open import Graded.Modality.Instances.Erasure.Modality
open import Graded.Modality.Variant lzero
import Graded.Mode
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions

module Graded.Erasure.Examples
  {p q r s}
  (variant : Modality-variant)
  (open Graded.Mode (ErasureModality variant))
  (TR : Type-restrictions (ErasureModality variant))
  (open Type-restrictions TR)
  (UR : Usage-restrictions (ErasureModality variant))
  (open Usage-restrictions UR)
  -- It is assumed that "Π 𝟘 , p" is allowed.
  (Π-𝟘-ok : Π-allowed 𝟘 p)
  -- It is assumed that "Π ω , q" is allowed.
  (Π-ω-ok : Π-allowed ω q)
  -- It is assumed that "Σˢ ω , r" is allowed.
  (Σˢ-ω-ok : Σˢ-allowed ω r)
  -- It is assumed that Unit s is allowed.
  (Unit-ok : Unit-allowed s)
  -- It is assumed that emptyrec 𝟘 is allowed.
  (emptyrec-ok : Emptyrec-allowed 𝟙ᵐ 𝟘)
  where

private

  -- The modality that is used in this module.

  𝕄 : Modality
  𝕄 = ErasureModality variant

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+; 2+)
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum as ⊎ using (_⊎_; inj₁; inj₂)

open import Definition.Typed TR as DT hiding (id)
open import Definition.Typed.Consequences.Reduction TR
open import Definition.Typed.Consequences.Substitution TR
open import Definition.Typed.Consequences.Syntactic TR
open import Definition.Typed.EqRelInstance TR
open import Definition.Typed.Eta-long-normal-form TR
open import Definition.Typed.Properties TR
import Definition.Typed.Weakening TR as W
open import Definition.Untyped Erasure as U hiding (id; head)
open import Definition.Untyped.Properties Erasure

private

  EM : Modality
  EM = ErasureModality variant

  module EM = Modality EM

open import Graded.Context EM
open import Graded.Erasure.Consequences.Soundness TR UR
open import Graded.Erasure.Extraction EM
open import Graded.Erasure.Extraction.Properties EM
import Graded.Erasure.SucRed TR as S
open import Graded.Erasure.Target as T
  using (Strictness; strict; non-strict)
open import Graded.Erasure.Target.Non-terminating
import Graded.Erasure.Target.Properties as TP
open import Graded.Modality.Instances.Erasure.Properties variant
open import Graded.Usage EM UR
open import Graded.Usage.Inversion EM UR
open import Graded.Usage.Properties EM UR
open import Graded.Usage.Weakening EM UR

private variable
  n       : Nat
  Γ       : Con Term _
  A t u v : Term _
  γ       : Conₘ _
  str     : Strictness

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

  U⊢ℕ : ε ∙ U ⊢ ℕ
  U⊢ℕ = ℕⱼ ⊢U

  ⊢Uℕ : ⊢ ε ∙ U ∙ ℕ
  ⊢Uℕ = ⊢U ∙ U⊢ℕ

  ⊢Uℕℕ : ⊢ ε ∙ U ∙ ℕ ∙ ℕ
  ⊢Uℕℕ = ⊢Uℕ ∙ ℕⱼ ⊢Uℕ

  Uℕℕ⊢U : ε ∙ U ∙ ℕ ∙ ℕ ⊢ U
  Uℕℕ⊢U = Uⱼ ⊢Uℕℕ

  ⊢UℕℕU : ⊢ ε ∙ U ∙ ℕ ∙ ℕ ∙ U
  ⊢UℕℕU = ⊢Uℕℕ ∙ Uℕℕ⊢U

  UℕℕU⊢3 : ε ∙ U ∙ ℕ ∙ ℕ ∙ U ⊢ var x3 ∷ U
  UℕℕU⊢3 = var₃ Uℕℕ⊢U

  ⊢UℕℕU3 : ⊢ ε ∙ U ∙ ℕ ∙ ℕ ∙ U ∙ var x3
  ⊢UℕℕU3 = ⊢UℕℕU ∙ univ UℕℕU⊢3

  ⊢ℕℕ : ⊢ ε ∙ ℕ ∙ ℕ
  ⊢ℕℕ = ⊢ℕ ∙ ℕⱼ ⊢ℕ

  ℕℕ⊢U : ε ∙ ℕ ∙ ℕ ⊢ U
  ℕℕ⊢U = Uⱼ ⊢ℕℕ

  ⊢ℕℕU : ⊢ ε ∙ ℕ ∙ ℕ ∙ U
  ⊢ℕℕU = ⊢ℕℕ ∙ ℕℕ⊢U

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
  ⊢Γ = ε ∙ Uⱼ ε ∙ univ (var₀ (Uⱼ ε))

-- The term id-x1-x0 is well-resourced (with respect to a specific
-- usage context).

▸id-x1-x0 : ε ∙ 𝟘 ∙ ω ▸[ 𝟙ᵐ ] id-x1-x0
▸id-x1-x0 = PE.subst
  (λ γ → γ ▸[ 𝟙ᵐ ] id-x1-x0)
  (≈ᶜ→≡ (ε ∙ PE.refl ∙ PE.cong ⌜_⌝ (ᵐ·-identityʳ {m = 𝟙ᵐ})))
  ((▸id ∘ₘ var) ∘ₘ var)

-- The polymorphic identity function applied to two arguments.

id-ℕ-zero : Term 0
id-ℕ-zero = id ∘⟨ 𝟘 ⟩ ℕ ∘⟨ ω ⟩ zero

-- In the strict setting the extraction of id-ℕ-zero includes an
-- erased part (T.↯).

erase-strict-id-ℕ-zero :
  erase strict id-ℕ-zero PE.≡
  T.lam (T.lam (T.var x0)) T.∘⟨ strict ⟩ T.↯ T.∘⟨ strict ⟩ T.zero
erase-strict-id-ℕ-zero = PE.refl

-- In the non-strict setting that part is removed entirely, and one
-- lambda is removed.

erase-non-strict-id-ℕ-zero :
  erase non-strict id-ℕ-zero PE.≡
  T.lam (T.var x0) T.∘⟨ non-strict ⟩ T.zero
erase-non-strict-id-ℕ-zero = PE.refl

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
       U⊢id (ℕⱼ ε) PE.refl Π-𝟘-ok)
    (zeroⱼ ε) ⇨
  (β-red (ℕⱼ ε) (ℕⱼ ⊢ℕ) (var ⊢ℕ here) (zeroⱼ ε) PE.refl Π-ω-ok ⇨
   DT.id (zeroⱼ ε))

-- The erasure of id-ℕ-zero reduces to zero.

erase-id-ℕ-zero⇒*zero : erase str id-ℕ-zero T.⇒* T.zero
erase-id-ℕ-zero⇒*zero {str = strict} =
  T.trans (T.app-subst $ T.β-red T.↯) $
  T.trans (T.β-red $ TP.Value→Value⟨⟩ T.zero)
  T.refl
erase-id-ℕ-zero⇒*zero {str = non-strict} =
  T.trans (T.β-red _)
  T.refl

------------------------------------------------------------------------
-- A function that uses an erased argument in a non-erased position

-- A (closed) identity function that takes an erased argument.

id₀ : Term 0
id₀ = lam 𝟘 (var x0)

-- The function id₀ is well-typed (in the empty context).

⊢id₀ : ε ⊢ id₀ ∷ Π 𝟘 , p ▷ ℕ ▹ ℕ
⊢id₀ = lamⱼ (ℕⱼ ε) (var₀ (ℕⱼ ε)) Π-𝟘-ok

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

-- In the strict setting the extraction of id₀-zero includes an erased
-- part (T.↯).

erase-strict-id₀-zero :
  erase strict id₀-zero PE.≡ T.lam (T.var x0) T.∘⟨ strict ⟩ T.↯
erase-strict-id₀-zero = PE.refl

-- In the non-strict setting the extraction of id₀-zero is the
-- non-terminating term loop non-strict.

erase-non-strict-id₀-zero :
  erase non-strict id₀-zero PE.≡ loop non-strict
erase-non-strict-id₀-zero = PE.refl

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
  β-red (ℕⱼ ε) (ℕⱼ ⊢ℕ) (var ⊢ℕ here) (zeroⱼ ε) PE.refl Π-𝟘-ok ⇨
  DT.id (zeroⱼ ε)

-- The erasure of id₀-zero reduces to loop?.

erase-id₀-zero⇒*loop? : ∀ s → erase s id₀-zero T.⇒* loop? s
erase-id₀-zero⇒*loop? strict =
  T.trans (T.β-red T.↯) T.refl
erase-id₀-zero⇒*loop? non-strict =
  T.refl

opaque
  unfolding loop

  -- The erasure of id₀-zero does not reduce to T.zero.

  ¬erase-id₀-zero⇒*zero : ¬ erase str id₀-zero T.⇒* T.zero
  ¬erase-id₀-zero⇒*zero {str = strict} =
    erase strict id₀-zero T.⇒* T.zero  →⟨ TP.red*Det $ erase-id₀-zero⇒*loop? strict ⟩
    T.↯ T.⇒* T.zero ⊎ T.zero T.⇒* T.↯  →⟨ ⊎.map TP.↯-noRed TP.zero-noRed ⟩
    T.zero PE.≡ T.↯ ⊎ T.↯ PE.≡ T.zero  →⟨ (λ { (inj₁ ()); (inj₂ ()) }) ⟩
    ⊥                                  □
  ¬erase-id₀-zero⇒*zero {str = non-strict} =
    erase non-strict id₀-zero T.⇒* T.zero                      →⟨ TP.red*Det $ erase-id₀-zero⇒*loop? _ ⟩
    loop non-strict T.⇒* T.zero ⊎ T.zero T.⇒* loop non-strict  →⟨ ⊎.map (¬loop⇒* T.zero) TP.zero-noRed ⟩
    ⊥ ⊎ loop non-strict PE.≡ T.zero                            →⟨ (λ { (inj₁ ()); (inj₂ ()) }) ⟩
    ⊥                                                          □

------------------------------------------------------------------------
-- A larger example, which makes use of the fact that uses in the
-- arguments of the eliminator for the empty type can be "ignored"

private

  -- Parts of the implementation of Vec.

  Vec-body₂ : Term (2+ n)
  Vec-body₂ =
    natrec 𝟘 𝟘 ω
      U
      (Unit s)
      (Σˢ ω , r ▷ var x3 ▹ var x1)
      (var x0)

  Vec-body₁ : Term (1+ n)
  Vec-body₁ = lam ω Vec-body₂

-- Vectors (lists of a fixed length).

Vec : Term 0
Vec = lam ω Vec-body₁

-- Vec is well-resourced.

▸Vec : ε ▸[ 𝟙ᵐ ] Vec
▸Vec =
  lamₘ $
  lamₘ $
  natrec-nr-or-no-nrₘ Unitₘ
    (ΠΣₘ var $
     sub var $
     let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       𝟘ᶜ ∙ ω ∙ r  ≤⟨ ≤ᶜ-refl ∙ greatest-elem _ ⟩
       𝟘ᶜ ∙ ω ∙ 𝟘  ∎)
    (sub (var {x = x0} {m = 𝟙ᵐ}) $
     let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       ε ∙ ω ∙ ω  ≤⟨ ≤ᶜ-refl ⟩
       ε ∙ 𝟘 ∙ ω  ∎)
    (sub Uₘ $
     let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ EM.·-zeroʳ _ ⟩
       𝟘ᶜ                ∎)
    ≤ᶜ-refl
    ( ≤ᶜ-refl
    , (λ _ → ≤ᶜ-refl)
    , ≤ᶜ-refl
    , ≤ᶜ-refl
    )

private

  -- A typing rule for Vec-body₂.

  ⊢Vec-body₂ : ε ∙ U ∙ ℕ ⊢ Vec-body₂ ∷ U
  ⊢Vec-body₂ =
    natrecⱼ Uℕℕ⊢U (Unitⱼ ⊢Uℕ Unit-ok)
      (ΠΣⱼ UℕℕU⊢3 (var ⊢UℕℕU3 (there here)) Σˢ-ω-ok)
      (var ⊢Uℕ here)

  -- A typing rule for Vec-body₁.

  ⊢Vec-body₁ : ε ∙ U ⊢ Vec-body₁ ∷ Π ω , q ▷ ℕ ▹ U
  ⊢Vec-body₁ = lamⱼ U⊢ℕ ⊢Vec-body₂ Π-ω-ok

-- A typing rule for Vec.

⊢Vec : ε ⊢ Vec ∷ Π ω , q ▷ U ▹ Π ω , q ▷ ℕ ▹ U
⊢Vec = lamⱼ (Uⱼ ε) ⊢Vec-body₁ Π-ω-ok

-- Some lemmas used below.

private module Vec-lemmas (⊢A : Γ ⊢ A ∷ U) where

  open Tools.Reasoning.PropositionalEquality

  ⊢Γ : ⊢ Γ
  ⊢Γ = wfTerm ⊢A

  ⊢ΓA : ⊢ Γ ∙ A
  ⊢ΓA = ⊢Γ ∙ univ ⊢A

  ⊢ΓAℕ : ⊢ Γ ∙ A ∙ ℕ
  ⊢ΓAℕ = ⊢ΓA ∙ ℕⱼ ⊢ΓA

  ⊢Γℕ : ⊢ Γ ∙ ℕ
  ⊢Γℕ = ⊢Γ ∙ ℕⱼ ⊢Γ

  Γℕ⊢U : Γ ∙ ℕ ⊢ U
  Γℕ⊢U = Uⱼ ⊢Γℕ

  ⊢ΓℕU : ⊢ Γ ∙ ℕ ∙ U
  ⊢ΓℕU = ⊢Γℕ ∙ Γℕ⊢U

  wk2≡ :
    ∀ A →
    wk (step (step U.id)) A PE.≡
    wk1 (wk1 (wk1 A)) [ liftSubst (liftSubst (sgSubst t)) ]
  wk2≡ {t = t} A =
    wk (step (step U.id)) A                                   ≡⟨ wk≡subst _ _ ⟩
    A [ wk1Subst (wk1Subst (sgSubst (suc t))) ₛ• step U.id ]  ≡˘⟨ subst-wk A ⟩
    wk1 A [ wk1Subst (wk1Subst (sgSubst t)) ]                 ≡˘⟨ wk2-tail (wk1 A) ⟩
    wk1 (wk1 (wk1 A)) [ liftSubst (liftSubst (sgSubst t)) ]   ∎

  ≡wk3[][] :
    ∀ A →
    A PE.≡
    wk1 (wk1 (wk1 A)) [ liftSubst (liftSubst (sgSubst t)) ]
      [ consSubst (sgSubst u) v ]
  ≡wk3[][] {t = t} {u = u} {v = v} A =
    A                                                        ≡˘⟨ subst-id _ ⟩

    A [ consSubst (sgSubst u) v ₛ• step (step U.id) ]        ≡˘⟨ subst-wk A ⟩

    wk (step (step U.id)) A [ consSubst (sgSubst u) v ]      ≡⟨ PE.cong _[ _ ] $ wk2≡ A ⟩

    wk1 (wk1 (wk1 A)) [ liftSubst (liftSubst (sgSubst t)) ]
      [ consSubst (sgSubst u) v ]                            ∎

  wk3[]≡ :
    ∀ A →
    wk1 (wk1 (wk1 (wk1 A))) [ liftSubst (liftSubst (sgSubst t)) ] PE.≡
    wk (lift (lift (step U.id)))
      (wk1 (wk1 (wk1 A)) [ liftSubst (liftSubst (sgSubst u)) ])
  wk3[]≡ {t = t} {u = u} A =
    wk1 (wk1 (wk1 (wk1 A))) [ liftSubst (liftSubst (sgSubst t)) ]  ≡˘⟨ wk2≡ _ ⟩

    wk (step (step U.id)) (wk1 A)                                  ≡⟨ wk-comp _ _ _ ⟩

    wk (step (step (step U.id))) A                                 ≡˘⟨ wk-comp _ _ _ ⟩

    wk (lift (lift (step U.id))) (wk (step (step U.id)) A)         ≡⟨ PE.cong (wk _) $ wk2≡ _ ⟩

    wk (lift (lift (step U.id)))
      (wk1 (wk1 (wk1 A)) [ liftSubst (liftSubst (sgSubst u)) ])    ∎

  ΓℕU⊢A :
    Γ ∙ ℕ ∙ U ⊢
    wk1 (wk1 (wk1 A)) [ liftSubst (liftSubst (sgSubst t)) ] ∷ U
  ΓℕU⊢A =
    PE.subst (_ ⊢_∷ _) (wk2≡ _) $
    W.wkTerm (W.step (W.step W.id)) ⊢ΓℕU ⊢A

  ⊢Vec-body₁′ : Γ ∙ U ⊢ Vec-body₁ ∷ Π ω , q ▷ ℕ ▹ U
  ⊢Vec-body₁′ = W.wkTerm
    (W.lift W.wk₀∷⊇)
    (⊢Γ ∙ Uⱼ ⊢Γ)
    ⊢Vec-body₁

  ⊢Vec-body₁″ : Γ ∙ A ∙ U ⊢ Vec-body₁ ∷ Π ω , q ▷ ℕ ▹ U
  ⊢Vec-body₁″ = W.wkTerm
    (W.lift (W.step W.wk₀∷⊇))
    (⊢ΓA ∙ Uⱼ ⊢ΓA)
    ⊢Vec-body₁

  ⊢Vec-body₂′ :
    Γ ∙ ℕ ⊢ Vec-body₂ [ liftSubst (consSubst (toSubst wk₀) A) ] ∷ U
  ⊢Vec-body₂′ = substitutionTerm
    {σ = liftSubst (consSubst (toSubst wk₀) A)}
    ⊢Vec-body₂
    (liftSubst′ ⊢U ⊢Γ U⊢ℕ (DT.id , ⊢A))
    ⊢Γℕ

  ⊢Vec-body₂″ :
    Γ ∙ A ∙ ℕ ⊢
    Vec-body₂ [ liftSubst (consSubst (toSubst wk₀) (wk1 A)) ] ∷ U
  ⊢Vec-body₂″ = substitutionTerm
    {σ = liftSubst (consSubst (toSubst wk₀) (wk1 A))}
    ⊢Vec-body₂
    (liftSubst′ ⊢U ⊢ΓA U⊢ℕ (DT.id , W.wkTerm₁ (univ ⊢A) ⊢A))
    ⊢ΓAℕ

-- A computation rule for Vec.

Vec∘zero⇒* :
  Γ ⊢ A ∷ U →
  Γ ⊢ wk wk₀ Vec ∘⟨ ω ⟩ A ∘⟨ ω ⟩ zero ⇒* Unit s ∷ U
Vec∘zero⇒* {A = A} ⊢A =
  app-subst
    (β-red (Uⱼ ⊢Γ) (syntacticTerm ⊢Vec-body₁′)
       ⊢Vec-body₁′ ⊢A PE.refl Π-ω-ok)
    (zeroⱼ ⊢Γ) ⇨
  (β-red (ℕⱼ ⊢Γ) Γℕ⊢U ⊢Vec-body₂′ (zeroⱼ ⊢Γ) PE.refl Π-ω-ok ⇨
   (redMany $
    _⊢_⇒_∷_.natrec-zero Γℕ⊢U (Unitⱼ ⊢Γ Unit-ok) $
    ΠΣⱼ ΓℕU⊢A (var₁ (univ ΓℕU⊢A)) Σˢ-ω-ok))
  where
  open Vec-lemmas ⊢A

-- An equality rule for Vec.

Vec∘suc≡ :
  Γ ⊢ A ∷ U →
  Γ ⊢ t ∷ ℕ →
  Γ ⊢
    wk wk₀ Vec ∘⟨ ω ⟩ A ∘⟨ ω ⟩ suc t ≡
    Σˢ ω , r ▷ A ▹ (wk wk₀ Vec ∘⟨ ω ⟩ wk1 A ∘⟨ ω ⟩ wk1 t) ∷ U
Vec∘suc≡ {Γ = Γ} {A = A} {t = t} ⊢A ⊢t =
  _⊢_≡_∷_.trans
    (app-cong
       (β-red (Uⱼ ⊢Γ) (syntacticTerm ⊢Vec-body₁′)
          ⊢Vec-body₁′ ⊢A PE.refl Π-ω-ok)
       (refl (sucⱼ ⊢t))) $
  _⊢_≡_∷_.trans
    (β-red (ℕⱼ ⊢Γ) Γℕ⊢U ⊢Vec-body₂′ (sucⱼ ⊢t) PE.refl Π-ω-ok) $
  _⊢_≡_∷_.trans
    (flip (_⊢_≡_∷_.natrec-suc Γℕ⊢U (Unitⱼ ⊢Γ Unit-ok)) ⊢t $
     ΠΣⱼ ΓℕU⊢A (var₁ (univ ΓℕU⊢A)) Σˢ-ω-ok) $
  _⊢_≡_∷_.trans
    (_⊢_≡_∷_.sym $
     ΠΣ-cong (univ ⊢A)
       (PE.subst (_ ⊢ _ ≡_∷ _) (≡wk3[][] A) (refl ⊢A))
       (PE.subst (Γ ∙ A ⊢ (Vec-body₁ [ wk1 A ]₀) ∘⟨ ω ⟩ wk1 t ≡_∷ U)
          (PE.cong (flip (natrec 𝟘 𝟘 ω U (Unit s)) _) $
           PE.cong (Σˢ _ , _ ▷_▹ _) $
           wk3[]≡ A) $
        β-red (ℕⱼ ⊢ΓA) (Uⱼ ⊢ΓAℕ) ⊢Vec-body₂″
          (W.wkTerm₁ (univ ⊢A) ⊢t) PE.refl Π-ω-ok)
       Σˢ-ω-ok) $
  _⊢_≡_∷_.sym $
  flip (_⊢_≡_∷_.ΠΣ-cong (univ ⊢A) (refl ⊢A)) Σˢ-ω-ok $
  app-cong
    (β-red (Uⱼ ⊢ΓA) (syntacticTerm ⊢Vec-body₁″)
       ⊢Vec-body₁″ (W.wkTerm₁ (univ ⊢A) ⊢A) PE.refl Π-ω-ok) $
  _⊢_≡_∷_.refl $
  W.wkTerm₁ (univ ⊢A) ⊢t
  where
  open Vec-lemmas ⊢A

private

  -- Parts of the implementation of Non-zero.

  Non-zero-body : Term (1+ n)
  Non-zero-body =
    natrec 𝟘 𝟘 𝟘
      U
      Empty
      (Unit s)
      (var x0)

-- A natural number predicate that holds for non-zero numbers.

Non-zero : Term 0
Non-zero = lam ω Non-zero-body

-- Non-zero is well-resourced.

▸Non-zero : ε ▸[ 𝟙ᵐ ] Non-zero
▸Non-zero =
  lamₘ $
  natrec-nr-or-no-nrₘ Emptyₘ
    Unitₘ
    var
    (sub Uₘ $
     let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ EM.·-zeroʳ _ ⟩
       𝟘ᶜ                ∎)
    ≤ᶜ-refl
    ( ≤ᶜ-refl
    , (λ _ → ≤ᶜ-refl)
    , ≤ᶜ-refl
    , ≤ᶜ-refl
    )

private

  -- A typing rule for Non-zero-body.

  ⊢Non-zero-body : ε ∙ ℕ ⊢ Non-zero-body ∷ U
  ⊢Non-zero-body =
    natrecⱼ ℕℕ⊢U (Emptyⱼ ⊢ℕ) (Unitⱼ ⊢ℕℕU Unit-ok)
      (var ⊢ℕ here)

-- A typing rule for Non-zero.

⊢Non-zero : ε ⊢ Non-zero ∷ Π ω , q ▷ ℕ ▹ U
⊢Non-zero = lamⱼ (ℕⱼ ε) ⊢Non-zero-body Π-ω-ok

-- A computation rule for Non-zero.

Non-zero∘zero⇒* :
  ⊢ Γ →
  Γ ⊢ wk wk₀ Non-zero ∘⟨ ω ⟩ zero ⇒* Empty ∷ U
Non-zero∘zero⇒* ⊢Γ =
  β-red (ℕⱼ ⊢Γ) (Uⱼ ⊢Γℕ)
    (W.wkTerm (W.lift W.wk₀∷⊇) ⊢Γℕ ⊢Non-zero-body)
    (zeroⱼ ⊢Γ) PE.refl Π-ω-ok ⇨
  (redMany $
   natrec-zero (Uⱼ ⊢Γℕ) (Emptyⱼ ⊢Γ)
     (Unitⱼ (⊢Γℕ ∙ Uⱼ ⊢Γℕ) Unit-ok))
  where
  ⊢Γℕ = ⊢Γ ∙ ℕⱼ ⊢Γ

-- Another computation rule for Non-zero.

Non-zero∘suc⇒* :
  Γ ⊢ t ∷ ℕ →
  Γ ⊢ wk wk₀ Non-zero ∘⟨ ω ⟩ suc t ⇒* Unit s ∷ U
Non-zero∘suc⇒* ⊢t =
  β-red (ℕⱼ ⊢Γ) (Uⱼ ⊢Γℕ)
    (W.wkTerm (W.lift W.wk₀∷⊇) ⊢Γℕ ⊢Non-zero-body)
    (sucⱼ ⊢t) PE.refl Π-ω-ok ⇨
  (redMany $
   natrec-suc (Uⱼ ⊢Γℕ) (Emptyⱼ ⊢Γ)
     (Unitⱼ (⊢Γℕ ∙ Uⱼ ⊢Γℕ) Unit-ok) ⊢t)
  where
  ⊢Γ  = wfTerm ⊢t
  ⊢Γℕ = ⊢Γ ∙ ℕⱼ ⊢Γ

-- A safe head function for vectors.

head : Term 0
head =
  lam 𝟘 $
  lam ω $
  natrec
    𝟘 ω 𝟘
    (Π ω , q ▷ wk wk₀ Vec ∘⟨ ω ⟩ var x2 ∘⟨ ω ⟩ var x0 ▹
     Π 𝟘 , p ▷ wk wk₀ Non-zero ∘⟨ ω ⟩ var x1 ▹
     var x4)
    (lam ω $ lam 𝟘 $
     emptyrec 𝟘 (var x3) (var x0))
    (lam ω $ lam 𝟘 $ fst ω (var x1))
    (var x0)

-- In the strict setting the extraction of head includes an erased
-- part (loop strict).

erase-strict-head :
  erase strict head PE.≡
  (T.Term.lam $ T.Term.lam $
   T.natrec
     (T.lam (T.lam (loop strict)))
     (T.lam (T.lam (T.fst (T.var x1))))
     (T.var x0))
erase-strict-head = PE.refl

opaque
  unfolding loop

  -- In the non-strict setting the extraction of head also includes an
  -- erased part (loop non-strict), and several lambdas are removed.

  erase-non-strict-head :
    erase non-strict head PE.≡
    (T.Term.lam $
     T.natrec
       (T.lam (loop non-strict))
       (T.lam (T.fst (T.var x0)))
       (T.var x0))
  erase-non-strict-head = PE.refl

-- The term head is well-resourced.

▸head : ε ▸[ 𝟙ᵐ ] head
▸head =
  lamₘ $
  lamₘ $
  natrec-nr-or-no-nrₘ
    (lamₘ $
     lamₘ $
     sub (emptyrecₘ var var emptyrec-ok) $
     let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       𝟘ᶜ ∙ ω ∙ 𝟘  ≤⟨ ≤ᶜ-refl ⟩
       𝟘ᶜ          ∎)
    (lamₘ $
     lamₘ $
     fstₘ 𝟙ᵐ
       (sub var $
        let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
          𝟘ᶜ ∙ ω ∙ 𝟘  ≤⟨ ≤ᶜ-refl ⟩
          𝟘ᶜ          ∎)
       (≢𝟘→⌞⌟≡𝟙ᵐ {p = ω} (λ ()))
       (λ _ → PE.refl))
    var
    (sub
       (ΠΣₘ ((𝟘ᶜ▸[𝟙ᵐ]→ (wkUsage wk₀ ▸Vec) ∘ₘ var) ∘ₘ var) $
        sub
          (ΠΣₘ (𝟘ᶜ▸[𝟙ᵐ]→ (wkUsage wk₀ ▸Non-zero) ∘ₘ var) $
           sub var $
           let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
             ε ∙ ⌜ 𝟘ᵐ? ⌝ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ · p  ≤⟨ ≤ᶜ-refl ∙ greatest-elem _ ⟩
             ε ∙ ⌜ 𝟘ᵐ? ⌝ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟘            ∎) $
        let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
          ε ∙ ⌜ 𝟘ᵐ? ⌝ ∙ 𝟘 ∙ ⌜ (𝟘ᵐ? ᵐ· 𝟘) ᵐ· ω ⌝     ∙ ⌜ 𝟘ᵐ? ⌝ · q  ≤⟨ ≤ᶜ-refl ∙
                                                                      ≤-reflexive (PE.sym (EM.+-identityʳ _)) ∙
                                                                      greatest-elem _ ⟩
          ε ∙ ⌜ 𝟘ᵐ? ⌝ ∙ 𝟘 ∙ ⌜ (𝟘ᵐ? ᵐ· 𝟘) ᵐ· ω ⌝ + 𝟘 ∙ 𝟘            ∎) $
     let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       ε ∙ ⌜ (𝟘ᵐ? ᵐ· ω) ᵐ· ω ⌝ + 𝟘 + ⌜ 𝟘ᵐ? ⌝ ∙ 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ · ω  ≈⟨ ≈ᶜ-refl ∙ lemma ⟩

       ε ∙ ⌜ (𝟘ᵐ? ᵐ· ω) ᵐ· ω ⌝ + 𝟘 + ⌜ 𝟘ᵐ? ⌝ ∙ 𝟘 ∙
         ⌜ (𝟘ᵐ? ᵐ· ω) ᵐ· ω ⌝ + ⌜ (𝟘ᵐ? ᵐ· 𝟘) ᵐ· ω ⌝              ∎)
    ≤ᶜ-refl
    ( ≤ᶜ-refl
    , (λ _ → ≤ᶜ-refl)
    , ≤ᶜ-refl
    , ≤ᶜ-refl
    )
  where
  lemma : ⌜ 𝟘ᵐ? ⌝ · ω PE.≡ ⌜ (𝟘ᵐ? ᵐ· ω) ᵐ· ω ⌝ + ⌜ (𝟘ᵐ? ᵐ· 𝟘) ᵐ· ω ⌝
  lemma = 𝟘ᵐ?-elim
    (λ m → ⌜ m ⌝ · ω PE.≡ ⌜ (m ᵐ· ω) ᵐ· ω ⌝ + ⌜ (m ᵐ· 𝟘) ᵐ· ω ⌝)
    PE.refl
    (λ not-ok →
       ω                                ≡⟨ PE.sym $
                                           PE.cong₂ (λ m₁ m₂ → ⌜ m₁ ⌝ + ⌜ m₂ ⌝)
                                             {x = ⌞ ω ⌟ ᵐ· ω} {u = ⌞ 𝟘 ⌟ ᵐ· ω}
                                             (only-𝟙ᵐ-without-𝟘ᵐ not-ok)
                                             (only-𝟙ᵐ-without-𝟘ᵐ not-ok) ⟩
       ⌜ ⌞ ω ⌟ ᵐ· ω ⌝ + ⌜ ⌞ 𝟘 ⌟ ᵐ· ω ⌝  ∎)
    where
    open Tools.Reasoning.PropositionalEquality

-- A typing rule for head.

⊢head :
  ε ⊢
  head ∷
  Π 𝟘 , p ▷ U ▹
  Π ω , q ▷ ℕ ▹
  Π ω , q ▷ wk wk₀ Vec ∘⟨ ω ⟩ var x1 ∘⟨ ω ⟩ var x0 ▹
  Π 𝟘 , p ▷ wk wk₀ Non-zero ∘⟨ ω ⟩ var x1 ▹
  var x3
⊢head =
  flip (lamⱼ (Uⱼ ε)) Π-𝟘-ok $
  flip (lamⱼ U⊢ℕ) Π-ω-ok $
  natrecⱼ (univ Uℕℕ⊢ΠΠ∷U)
    (flip (lamⱼ (univ ⊢Vec-1-0)) Π-ω-ok $
     flip (lamⱼ (univ ⊢Non-zero-zero)) Π-𝟘-ok $
     emptyrecⱼ
       (univ (var₃ (univ ⊢Non-zero-zero)))
       (_⊢_∷_.conv (var₀ (univ ⊢Non-zero-zero)) $
        _⊢_≡_.univ $
        subset*Term $
        Non-zero∘zero⇒* ⊢Uℕ∙Vec∙Non-zero))
    (flip (lamⱼ (univ ⊢Vec-3-1+1)) Π-ω-ok $
     flip (lamⱼ (univ ⊢Non-zero-1+2)) Π-𝟘-ok $
     fstⱼ (univ ⊢5) (univ ⊢Vec-6-4) $
     _⊢_∷_.conv (var₁ (univ ⊢Non-zero-1+2)) $
     _⊢_≡_.univ $
     Vec∘suc≡ ⊢5 (var₃ (univ ⊢Non-zero-1+2)))
    (var ⊢Uℕ here)
  where
  ⊢Vec-2-0 :
    ε ∙ U ∙ ℕ ∙ ℕ ⊢ wk wk₀ Vec ∘⟨ ω ⟩ var x2 ∘⟨ ω ⟩ var x0 ∷ U
  ⊢Vec-2-0 =
    (W.wkTerm (W.step (W.step (W.step W.id))) ⊢Uℕℕ ⊢Vec ∘ⱼ
     var ⊢Uℕℕ (there (there here))) ∘ⱼ
    var ⊢Uℕℕ here

  ⊢Vec-1-0 :
    ε ∙ U ∙ ℕ ⊢ wk wk₀ Vec ∘⟨ ω ⟩ var x1 ∘⟨ ω ⟩ zero ∷ U
  ⊢Vec-1-0 = substTerm ⊢Vec-2-0 (zeroⱼ ⊢Uℕ)

  ⊢Non-zero-0 :
    ε ∙ U ∙ ℕ ∙ ℕ ⊢ wk wk₀ Non-zero ∘⟨ ω ⟩ var x0 ∷ U
  ⊢Non-zero-0 =
    W.wkTerm (W.step (W.step (W.step W.id))) ⊢Uℕℕ ⊢Non-zero ∘ⱼ
    var ⊢Uℕℕ here

  ⊢Uℕℕ∙Vec = ⊢Uℕℕ ∙ univ ⊢Vec-2-0

  ⊢Non-zero-1 :
    ε ∙ U ∙ ℕ ∙ ℕ ∙ wk wk₀ Vec ∘⟨ ω ⟩ var x2 ∘⟨ ω ⟩ var x0 ⊢
    wk wk₀ Non-zero ∘⟨ ω ⟩ var x1 ∷ U
  ⊢Non-zero-1 = W.wkTerm₁ (univ ⊢Vec-2-0) ⊢Non-zero-0

  ⊢Uℕ∙Vec = ⊢Uℕ ∙ univ ⊢Vec-1-0

  ⊢Non-zero-zero :
    ε ∙ U ∙ ℕ ∙ wk wk₀ Vec ∘⟨ ω ⟩ var x1 ∘⟨ ω ⟩ zero ⊢
    wk wk₀ Non-zero ∘⟨ ω ⟩ zero ∷ U
  ⊢Non-zero-zero = substitutionTerm
    ⊢Non-zero-1
    (liftSubst′ ⊢Uℕℕ ⊢Uℕ (univ ⊢Vec-2-0) (singleSubst (zeroⱼ ⊢Uℕ)))
    ⊢Uℕ∙Vec

  ⊢Uℕ∙Vec∙Non-zero  = ⊢Uℕ∙Vec ∙ univ ⊢Non-zero-zero
  ⊢Uℕℕ∙Vec∙Non-zero = ⊢Uℕℕ∙Vec ∙ univ ⊢Non-zero-1

  Uℕℕ⊢ΠΠ∷U :
    ε ∙ U ∙ ℕ ∙ ℕ ⊢
    Π ω , q ▷ wk wk₀ Vec ∘⟨ ω ⟩ var x2 ∘⟨ ω ⟩ var x0 ▹
      Π 𝟘 , p ▷ wk wk₀ Non-zero ∘⟨ ω ⟩ var x1 ▹ var x4 ∷
    U
  Uℕℕ⊢ΠΠ∷U =
    ΠΣⱼ ⊢Vec-2-0
      (ΠΣⱼ ⊢Non-zero-1
         (var ⊢Uℕℕ∙Vec∙Non-zero
            (there (there (there (there here)))))
         Π-𝟘-ok)
      Π-ω-ok

  Uℕℕ∙ΠΠ =
    ε ∙ U ∙ ℕ ∙ ℕ ∙
    Π ω , q ▷ wk wk₀ Vec ∘⟨ ω ⟩ var x2 ∘⟨ ω ⟩ var x0 ▹
      Π 𝟘 , p ▷ wk wk₀ Non-zero ∘⟨ ω ⟩ var x1 ▹ var x4
  ⊢Uℕℕ∙ΠΠ = ⊢Uℕℕ ∙ univ Uℕℕ⊢ΠΠ∷U

  ⊢Vec-3-1+1 :
    Uℕℕ∙ΠΠ ⊢ wk wk₀ Vec ∘⟨ ω ⟩ var x3 ∘⟨ ω ⟩ suc (var x1) ∷ U
  ⊢Vec-3-1+1 = substitutionTerm
    ⊢Vec-2-0
    (wk1Subst′ ⊢Uℕℕ (univ Uℕℕ⊢ΠΠ∷U)
       (singleSubst↑ (sucⱼ (var ⊢Uℕℕ here))))
    ⊢Uℕℕ∙ΠΠ

  Uℕℕ∙ΠΠ∙Vec  = Uℕℕ∙ΠΠ ∙ wk wk₀ Vec ∘⟨ ω ⟩ var x3 ∘⟨ ω ⟩ suc (var x1)
  ⊢Uℕℕ∙ΠΠ∙Vec = ⊢Uℕℕ∙ΠΠ ∙ univ ⊢Vec-3-1+1

  ⊢Non-zero-1+2 :
    Uℕℕ∙ΠΠ∙Vec ⊢ wk wk₀ Non-zero ∘⟨ ω ⟩ suc (var x2) ∷ U
  ⊢Non-zero-1+2 = substitutionTerm
    ⊢Non-zero-0
    (wk1Subst′ ⊢Uℕℕ (univ ⊢Vec-3-1+1)
       (wk1Subst′ ⊢Uℕℕ (univ Uℕℕ⊢ΠΠ∷U)
          (singleSubst↑ (sucⱼ (var ⊢Uℕℕ here)))))
    ⊢Uℕℕ∙ΠΠ∙Vec

  Uℕℕ∙ΠΠ∙Vec∙Non-zero =
    Uℕℕ∙ΠΠ∙Vec ∙ wk wk₀ Non-zero ∘⟨ ω ⟩ suc (var x2)
  ⊢Uℕℕ∙ΠΠ∙Vec∙Non-zero = ⊢Uℕℕ∙ΠΠ∙Vec ∙ univ ⊢Non-zero-1+2

  ⊢5 : Uℕℕ∙ΠΠ∙Vec∙Non-zero ⊢ var x5 ∷ U
  ⊢5 = var₅ (univ ⊢Non-zero-1+2)

  Uℕℕ∙ΠΠ∙Vec∙Non-zero∙5  = Uℕℕ∙ΠΠ∙Vec∙Non-zero ∙ var x5
  ⊢Uℕℕ∙ΠΠ∙Vec∙Non-zero∙5 = ⊢Uℕℕ∙ΠΠ∙Vec∙Non-zero ∙ univ ⊢5

  ⊢Vec-6-4 :
    Uℕℕ∙ΠΠ∙Vec∙Non-zero∙5 ⊢
    wk wk₀ Vec ∘⟨ ω ⟩ var x6 ∘⟨ ω ⟩ var x4 ∷ U
  ⊢Vec-6-4 = W.wkTerm
    (W.step (W.step (W.step (W.step W.id))))
    ⊢Uℕℕ∙ΠΠ∙Vec∙Non-zero∙5
    ⊢Vec-2-0

-- A concrete vector which contains a single natural number.

[0] : Term 0
[0] = prodˢ ω zero (star s)

-- [0] is well-resourced.

▸[0] : ε ▸[ 𝟙ᵐ ] [0]
▸[0] = prodˢₘ zeroₘ starₘ

-- [0] is in η-long normal form.

[0]-normal : ε ⊢nf [0] ∷ Vec ∘⟨ ω ⟩ ℕ ∘⟨ ω ⟩ suc zero
[0]-normal =
  _⊢nf_∷_.convₙ
    (prodₙ (ℕⱼ ε) (Unitⱼ ⊢ℕ Unit-ok) (zeroₙ ε)
       (starₙ ε Unit-ok) Σˢ-ω-ok) $
  _⊢_≡_.univ $
  _⊢_≡_∷_.sym $
  _⊢_≡_∷_.trans (Vec∘suc≡ (ℕⱼ ε) (zeroⱼ ε)) $
  ΠΣ-cong (ℕⱼ ε) (refl (ℕⱼ ε))
    (subset*Term (Vec∘zero⇒* (ℕⱼ (ε ∙ ℕⱼ ε)))) Σˢ-ω-ok

-- A typing rule for [0].

⊢[0] : ε ⊢ [0] ∷ Vec ∘⟨ ω ⟩ ℕ ∘⟨ ω ⟩ suc zero
⊢[0] = ⊢nf∷→⊢∷ [0]-normal

-- An application of head to [0] and some other arguments.

head-[0] : Term 0
head-[0] = head ∘⟨ 𝟘 ⟩ ℕ ∘⟨ ω ⟩ suc zero ∘⟨ ω ⟩ [0] ∘⟨ 𝟘 ⟩ (star s)

-- In the strict setting the extraction of id-ℕ-zero includes several
-- erased parts (T.↯ and loop strict).

erase-strict-head-[0] :
  erase strict head-[0] PE.≡
  T.lam
    (T.Term.lam $
     T.natrec (T.lam (T.lam (loop strict)))
       (T.lam (T.lam (T.fst (T.var x1))))
       (T.var x0)) T.∘⟨ strict ⟩
  T.↯ T.∘⟨ strict ⟩
  T.suc⟨ strict ⟩ T.zero T.∘⟨ strict ⟩
  T.prod⟨ strict ⟩ T.zero T.star T.∘⟨ strict ⟩
  T.↯
erase-strict-head-[0] = PE.refl

opaque
  unfolding loop

  -- In the non-strict setting two of those parts are removed
  -- entirely, and several lambdas are also removed.

  erase-non-strict-head-[0] :
    erase non-strict head-[0] PE.≡
    T.lam
      (T.natrec (T.lam (loop non-strict))
         (T.lam (T.fst (T.var x0)))
         (T.var x0)) T.∘⟨ non-strict ⟩
    T.suc T.zero T.∘⟨ non-strict ⟩
    T.prod T.zero T.star
  erase-non-strict-head-[0] = PE.refl

-- The term head-[0] is well-resourced.

▸head-[0] : ε ▸[ 𝟙ᵐ ] head-[0]
▸head-[0] = (((▸head ∘ₘ ℕₘ) ∘ₘ sucₘ zeroₘ) ∘ₘ 𝟘ᶜ▸[𝟙ᵐ]→ ▸[0]) ∘ₘ starₘ

-- The term head-[0] is well-typed.

⊢head-[0] : ε ⊢ head-[0] ∷ ℕ
⊢head-[0] =
  (((⊢head ∘ⱼ ℕⱼ ε) ∘ⱼ sucⱼ (zeroⱼ ε)) ∘ⱼ ⊢[0]) ∘ⱼ
  conv (starⱼ ε Unit-ok)
    (_⊢_≡_.univ $
     _⊢_≡_∷_.sym $
     subset*Term (Non-zero∘suc⇒* (zeroⱼ ε)))

-- The erasure of head-[0] reduces to T.zero.

erase-head-[0]⇒*zero : erase str head-[0] T.⇒* T.zero
erase-head-[0]⇒*zero {str = non-strict} =
  T.trans (T.app-subst $ T.β-red _) $
  T.trans (T.app-subst T.natrec-suc) $
  T.trans (T.β-red _) $
  T.trans T.Σ-β₁
  T.refl
erase-head-[0]⇒*zero {str = strict} =
  T.trans (T.app-subst $ T.app-subst $ T.app-subst $ T.β-red T.↯) $
  T.trans (T.app-subst $ T.app-subst $ T.app-subst-arg T.lam $
           T.β-red T.zero) $
  T.trans (T.app-subst $ T.app-subst $ T.β-red T.suc) $
  T.trans (T.app-subst $ T.app-subst $ T.natrec-suc) $
  T.trans (T.app-subst $ T.app-subst-arg T.lam $ T.app-subst $
           T.β-red T.zero) $
  T.trans (T.app-subst $ T.app-subst-arg T.lam $ T.β-red T.star) $
  T.trans (T.app-subst $ T.β-red T.prod) $
  T.trans (T.β-red T.↯) $
  T.trans T.Σ-β₁
  T.refl

-- The term head-[0] reduces to zero.
--
-- Note that this is proved using the fact that the (non-strict)
-- erasure of head-[0] reduces to T.zero.

head-[0]⇒*zero : ε ⊢ head-[0] ⇒* zero ∷ ℕ
head-[0]⇒*zero =
  case Soundness₀.soundness-ℕ
         T.non-strict ⊢head-[0] ▸head-[0] of λ where
    (0 , head-[0]⇒*zero , _) →
      S.⇒ˢ*zero∷ℕ→⇒*zero head-[0]⇒*zero
    (1+ _ , _ , erase-head-[0]⇒*suc) →
      case TP.red*Det (erase-head-[0]⇒*zero {str = non-strict})
              (S.⇒ˢ*suc→⇒*suc erase-head-[0]⇒*suc .proj₂)
      of λ where
        (inj₁ zero⇒*suc) → case TP.zero-noRed zero⇒*suc of λ ()
        (inj₂ suc⇒*zero) → case TP.suc-noRed  suc⇒*zero of λ ()
