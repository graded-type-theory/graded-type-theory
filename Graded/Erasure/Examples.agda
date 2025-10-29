------------------------------------------------------------------------
-- Some examples related to the erasure modality and extraction
------------------------------------------------------------------------

open import Tools.Level hiding (Level; Lift)

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
open import Definition.Typed.Eta-long-normal-form TR
open import Definition.Typed.Inversion TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Substitution TR hiding (id)
open import Definition.Typed.Syntactic TR
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
import Graded.Erasure.SucRed TR as S
open import Graded.Erasure.Target as T
  using (Strictness; strict; non-strict)
open import Graded.Erasure.Target.Non-terminating
import Graded.Erasure.Target.Properties as TP
open import Graded.Modality.Instances.Erasure.Properties variant
open import Graded.Usage EM UR
open import Graded.Usage.Inversion EM UR
open import Graded.Usage.Properties EM UR
open import Graded.Usage.Restrictions.Natrec EM
open import Graded.Usage.Weakening EM UR

private variable
  n       : Nat
  Γ       : Con Term _
  A t u v l : Term _
  γ       : Conₘ _
  str     : Strictness

private

  -- Some lemmas used below.

  ⊢εℕ : ⊢ ε ∙ ℕ
  ⊢εℕ = ∙ ⊢ℕ ε

  ⊢U0 : ε ∙ Level ⊢ U (var x0)
  ⊢U0 = ⊢U (var (∙ Levelⱼ′ ε) here)

  U⊢ℕ : ε ∙ Level ∙ U (var x0) ⊢ ℕ
  U⊢ℕ = ⊢ℕ (∙ ⊢U0)

  ⊢Uℕ : ⊢ ε ∙ Level ∙ U (var x0) ∙ ℕ
  ⊢Uℕ = ∙ U⊢ℕ

  U⊢0 : ε ∙ Level ∙ U (var x0) ⊢ var x0
  U⊢0 = univ (var (∙ ⊢U0) here)

  ⊢U∙0 : ⊢ ε ∙ Level ∙ U (var x0) ∙ var x0
  ⊢U∙0 = ∙ U⊢0

  U⊢id : ε ∙ Level ∙ U (var x0) ⊢ lam ω (var x0) ∷ Π ω , q ▷ var x0 ▹ var x1
  U⊢id = lamⱼ′ Π-ω-ok (var ⊢U∙0 here)

  ΓU⊢id : ⊢ Γ → Γ ∙ Level ∙ U (var x0) ⊢ lam ω (var x0) ∷ Π ω , q ▷ var x0 ▹ var x1
  ΓU⊢id ε = U⊢id
  ΓU⊢id (∙ ⊢A) =
    W.wkTerm
      (W.liftʷ (W.lift (W.step W.id))
         (⊢U (var (∙ Levelⱼ′ (∙ ⊢A)) here)))
      (ΓU⊢id (wf ⊢A))

  ⊢Uℕℕ : ⊢ ε ∙ Level ∙ U (var x0) ∙ ℕ ∙ ℕ
  ⊢Uℕℕ = ∙ ⊢ℕ ⊢Uℕ

  UℕℕU⊢3 : ε ∙ Level ∙ U (var x0) ∙ ℕ ∙ ℕ ∙ U (var x3) ⊢ var x3 ∷ U (var x4)
  UℕℕU⊢3 = var₃ (⊢U (var₃ (⊢ℕ ⊢Uℕ)))

  ⊢UℕℕU3 : ⊢ ε ∙ Level ∙ U (var x0) ∙ ℕ ∙ ℕ ∙ U (var x3) ∙ var x3
  ⊢UℕℕU3 = ∙ univ UℕℕU⊢3

  ⊢ℕℕ : ⊢ ε ∙ ℕ ∙ ℕ
  ⊢ℕℕ = ∙ ⊢ℕ ⊢εℕ

  ⊢ℕℕU : ⊢ ε ∙ ℕ ∙ ℕ ∙ Level ∙ U (var x0)
  ⊢ℕℕU = ∙ ⊢U (var (∙ Levelⱼ′ ⊢ℕℕ) here)

------------------------------------------------------------------------
-- A universe-polymorphic identity function

-- A universe-polymorphic identity function with an erased type argument.

id : Term n
id = lam 𝟘 (lam 𝟘 (lam ω (var x0)))

-- The universe-polymorphic identity function is well-typed (in a well-formed
-- context).

⊢id : ⊢ Γ → Γ ⊢ id ∷ Π 𝟘 , p ▷ Level ▹ Π 𝟘 , p ▷ U (var x0) ▹ Π ω , q ▷ var x0 ▹ var x1
⊢id ⊢Γ = lamⱼ′ Π-𝟘-ok (lamⱼ′ Π-𝟘-ok (ΓU⊢id ⊢Γ))

-- The universe-polymorphic identity function is well-resourced (with respect
-- to the zero usage context).

▸id : 𝟘ᶜ {n} ▸[ 𝟙ᵐ ] id
▸id = lamₘ (lamₘ (lamₘ var))

-- The universe-polymorphic identity function applied to three free
-- variables.

id-generic : Term 3
id-generic = id ∘⟨ 𝟘 ⟩ var x2 ∘⟨ 𝟘 ⟩ var x1 ∘⟨ ω ⟩ var x0

-- The term id-generic is well-typed (in a certain context).

⊢id-generic : ε ∙ Level ∙ U (var x0) ∙ var x0 ⊢ id-generic ∷ var x1
⊢id-generic = ((⊢id ⊢Γ ∘ⱼ var ⊢Γ (there (there here))) ∘ⱼ var ⊢Γ (there here)) ∘ⱼ var ⊢Γ here
  where
  ⊢Γ = ∙ univ (var₀ ⊢U0)

-- The term id-generic is well-resourced (with respect to a specific
-- usage context).

▸id-generic : ε ∙ 𝟘 ∙ 𝟘 ∙ ω ▸[ 𝟙ᵐ ] id-generic
▸id-generic = PE.subst
  (λ γ → γ ▸[ 𝟙ᵐ ] id-generic)
  (≈ᶜ→≡ (ε ∙ PE.refl ∙ PE.refl ∙ PE.cong ⌜_⌝ (ᵐ·-identityʳ {m = 𝟙ᵐ})))
  (((▸id ∘ₘ var) ∘ₘ var) ∘ₘ var)

-- The universe-polymorphic identity function applied to three
-- arguments.

id-ℕ-zero : Term 0
id-ℕ-zero = id ∘⟨ 𝟘 ⟩ zeroᵘ ∘⟨ 𝟘 ⟩ ℕ ∘⟨ ω ⟩ zero

-- In the strict setting the extraction of id-ℕ-zero includes some
-- erased parts (T.↯).

erase-strict-id-ℕ-zero :
  erase strict id-ℕ-zero PE.≡
  T.lam (T.lam (T.lam (T.var x0))) T.∘⟨ strict ⟩ T.↯ T.∘⟨ strict ⟩ T.↯ T.∘⟨ strict ⟩ T.zero
erase-strict-id-ℕ-zero = PE.refl

-- In the non-strict setting those parts are removed entirely, and one
-- lambda is removed.

erase-non-strict-id-ℕ-zero :
  erase non-strict id-ℕ-zero PE.≡
  T.lam (T.var x0) T.∘⟨ non-strict ⟩ T.zero
erase-non-strict-id-ℕ-zero = PE.refl

-- The term id-ℕ-zero is well-typed (in the empty context).

⊢id-ℕ-zero : ε ⊢ id-ℕ-zero ∷ ℕ
⊢id-ℕ-zero = ((⊢id ε ∘ⱼ zeroᵘⱼ ε) ∘ⱼ ℕⱼ ε) ∘ⱼ zeroⱼ ε

-- The term id-ℕ-zero is well-resourced (with respect to the empty
-- usage context).

▸id-ℕ-zero : ε ▸[ 𝟙ᵐ ] id-ℕ-zero
▸id-ℕ-zero = ((▸id ∘ₘ zeroᵘₘ) ∘ₘ ℕₘ) ∘ₘ zeroₘ

-- The term id-ℕ-zero reduces to zero.

id-ℕ-zero⇒*zero : ε ⊢ id-ℕ-zero ⇒* zero ∷ ℕ
id-ℕ-zero⇒*zero =
  β-red-⇒₃′ Π-𝟘-ok Π-𝟘-ok Π-ω-ok (var ⊢U∙0 here) (zeroᵘⱼ ε) (ℕⱼ ε)
    (zeroⱼ ε)

-- The erasure of id-ℕ-zero reduces to zero.

erase-id-ℕ-zero⇒*zero : erase str id-ℕ-zero T.⇒* T.zero
erase-id-ℕ-zero⇒*zero {str = strict} =
  T.trans (T.app-subst $ T.app-subst $ T.β-red T.↯) $
  T.trans (T.app-subst $ T.β-red T.↯) $
  T.trans (T.β-red (TP.Value→Value⟨⟩ T.zero)) $
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
⊢id₀ = lamⱼ′ Π-𝟘-ok (var₀ (⊢ℕ ε))

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
  redMany (β-red (⊢ℕ ⊢εℕ) (var ⊢εℕ here) (zeroⱼ ε) PE.refl Π-𝟘-ok)

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

  Vec-body₂ : Term (1+ (2+ n))
  Vec-body₂ =
    natrec 𝟘 𝟘 ω
      (U (var x3))
      (Lift (var x2) (Unit s))
      (Σˢ ω , r ▷ var x3 ▹ var x1)
      (var x0)

  Vec-body₁ : Term (2+ n)
  Vec-body₁ = lam ω Vec-body₂

-- Vectors (lists of a fixed length).

Vec : Term 0
Vec = lam ω (lam ω Vec-body₁)

-- Vec l is well-resourced.

▸Vec : ε ▸[ 𝟙ᵐ ] Vec
▸Vec =
  lamₘ $
  lamₘ $
  lamₘ $
  natrec-nr-or-no-nrₘ (Liftₘ var Unitₘ)
    (ΠΣₘ var $
     sub var $
     let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       𝟘ᶜ ∙ ω ∙ r  ≤⟨ ≤ᶜ-refl ∙ greatest-elem _ ⟩
       𝟘ᶜ ∙ ω ∙ 𝟘  ∎)
    (sub (var {x = x0} {m = 𝟙ᵐ}) $
     let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       replicateᶜ 3 ω ≤⟨ ≤ᶜ-refl ⟩
       ε ∙ 𝟘 ∙ 𝟘 ∙ ω  ∎)
    (sub (Uₘ var) $
     let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ EM.·-zeroʳ _ ⟩
       𝟘ᶜ                ∎)
    ≤ᶜ-refl
    ( ≤ᶜ-refl
    , (λ _ → ≤ᶜ-refl)
    , ≤ᶜ-refl
    , ≤ᶜ-refl
    )
    (let x , x-glb = Erasure-nrᵢ-glb ω ω 𝟘
         χ , χ-glb = ∃nrᵢ-GLB→∃nrᵢᶜ-GLB (Erasure-nrᵢ-glb _) 𝟘ᶜ _
         open Tools.Reasoning.PartialOrder ≤ᶜ-poset
    in  x , χ , x-glb , χ-glb , (begin
      replicateᶜ 3 ω                      ≡⟨⟩
      ω ·ᶜ replicateᶜ 3 ω +ᶜ decomposeᶜ χ ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (least-elem′ x (x-glb .proj₁ 0))) ⟩
      x ·ᶜ replicateᶜ 3 ω +ᶜ decomposeᶜ χ ≡⟨ PE.cong (λ y → x ·ᶜ replicateᶜ 3 ω +ᶜ y) (decomposeᶜ-correct χ) ⟩
      x ·ᶜ replicateᶜ 3 ω +ᶜ χ            ∎))

private

  -- A typing rule for Vec-body₂.

  ⊢Vec-body₂ : ε ∙ Level ∙ U (var x0) ∙ ℕ ⊢ Vec-body₂ ∷ U (var x2)
  ⊢Vec-body₂ =
    natrecⱼ
      (Liftⱼ≤ (supᵘ-zeroˡ (var ⊢Uℕ (there (there here)))) (Unitⱼ ⊢Uℕ Unit-ok))
      (ΠΣⱼ′ UℕℕU⊢3 (var ⊢UℕℕU3 (there here)) Σˢ-ω-ok)
      (var ⊢Uℕ here)

  -- A typing rule for Vec-body₁.

  ⊢Vec-body₁ : ε ∙ Level ∙ U (var x0) ⊢ Vec-body₁ ∷ Π ω , q ▷ ℕ ▹ U (var x2)
  ⊢Vec-body₁ = lamⱼ′ Π-ω-ok ⊢Vec-body₂

-- A typing rule for Vec.

⊢Vec : ε ⊢ Vec ∷ Π ω , q ▷ Level ▹ Π ω , q ▷ U (var x0) ▹ Π ω , q ▷ ℕ ▹ U (var x2)
⊢Vec = lamⱼ′ Π-ω-ok (lamⱼ′ Π-ω-ok ⊢Vec-body₁)
