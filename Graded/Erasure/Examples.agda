------------------------------------------------------------------------
-- Some examples related to the erasure modality and extraction
------------------------------------------------------------------------

open import Tools.Level hiding (Level; Lift)

open import Graded.Modality.Instances.Erasure
import Graded.Modality.Instances.Erasure.Modality as GMIEM
  hiding (nr; erasure-has-nr)
open GMIEM
open import Graded.Mode.Instances.Zero-one.Variant
import Graded.Mode.Instances.Zero-one
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions

module Graded.Erasure.Examples
  {p q r s}
  (variant : Mode-variant ErasureModality)
  (open Graded.Mode.Instances.Zero-one variant)
  (TR : Type-restrictions ErasureModality)
  (open Type-restrictions TR)
  (UR : Usage-restrictions ErasureModality Zero-one-isMode)
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
  𝕄 = ErasureModality

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.List using (List)
open import Tools.Nat using (Nat; 1+; 2+; 3+)
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
import Definition.Typed.Reasoning.Reduction TR as RR
import Definition.Typed.Reasoning.Term TR as TmR
import Definition.Typed.Reasoning.Type TR as TyR
open import Definition.Typed.Substitution TR hiding (id)
open import Definition.Typed.Syntactic TR
import Definition.Typed.Weakening TR as W
import Definition.Typed.Weakening.Definition TR as WD
open import Definition.Typed.Well-formed TR
open import Definition.Untyped Erasure as U hiding (id; head)
open import Definition.Untyped.Nat 𝕄
open import Definition.Untyped.Properties Erasure

private

  EM : Modality
  EM = ErasureModality

  module EM = Modality EM

open import Graded.Context EM
open import Graded.Derived.Nat UR
open import Graded.Erasure.Consequences.Soundness TR UR
open import Graded.Erasure.Extraction EM
import Graded.Erasure.SucRed TR as S
open import Graded.Erasure.Target as T
  using (Strictness; strict; non-strict)
open import Graded.Erasure.Target.Non-terminating
import Graded.Erasure.Target.Properties as TP
open import Graded.Modality.Nr-instances
open import Graded.Usage.Restrictions.Instance UR
open import Graded.Modality.Instances.Erasure.Properties
open import Graded.Usage UR
open import Graded.Usage.Inversion UR
open import Graded.Usage.Properties UR
open import Graded.Usage.Restrictions.Natrec EM
open import Graded.Usage.Weakening UR

private variable
  n         : Nat
  ∇         : DCon (Term 0) _
  Γ         : Cons _ _
  vs        : List (T.Term 0)
  A t u v l : Term _
  σ         : Subst _ _
  γ         : Conₘ _
  str       : Strictness

private

  -- Some lemmas used below.

  ⊢εℕ : ε »⊢ ε ∙ ℕ
  ⊢εℕ = ∙ ⊢ℕ εε

  ⊢ℕℕ : ε »⊢ ε ∙ ℕ ∙ ℕ
  ⊢ℕℕ = ∙ ⊢ℕ ⊢εℕ

  module _ (ok : Level-allowed) where

    ⊢U0 : » ∇ → ∇ » ε ∙ Level ⊢ U (var x0)
    ⊢U0 »∇ = ⊢U′ (var (∙ Levelⱼ′ ok (ε »∇)) here)

    U⊢ℕ : ε » ε ∙ Level ∙ U (var x0) ⊢ ℕ
    U⊢ℕ = ⊢ℕ (∙ ⊢U0 ε)

    ⊢Uℕ : ε »⊢ ε ∙ Level ∙ U (var x0) ∙ ℕ
    ⊢Uℕ = ∙ U⊢ℕ

    U⊢0 : » ∇ → ∇ » ε ∙ Level ∙ U (var x0) ⊢ var x0
    U⊢0 »∇ = univ (var (∙ ⊢U0 »∇) here)

    ⊢U∙0 : » ∇ → ∇ »⊢ ε ∙ Level ∙ U (var x0) ∙ var x0
    ⊢U∙0 »∇ = ∙ U⊢0 »∇

    U⊢id :
      » ∇ →
      ∇ » ε ∙ Level ∙ U (var x0) ⊢ lam ω (var x0) ∷
        Π ω , q ▷ var x0 ▹ var x1
    U⊢id »∇ = lamⱼ′ Π-ω-ok (var (⊢U∙0 »∇) here)

    ΓU⊢id :
      ⊢ Γ →
      Γ »∙ Level »∙ U (var x0) ⊢ lam ω (var x0) ∷
        Π ω , q ▷ var x0 ▹ var x1
    ΓU⊢id (ε »∇) = U⊢id »∇
    ΓU⊢id (∙ ⊢A) =
      W.wkTerm
        (W.liftʷ (W.lift (W.step W.id))
           (⊢U′ (var (∙ Levelⱼ′ ok (∙ ⊢A)) here)))
        (ΓU⊢id (wf ⊢A))

    UℕℕU⊢3 :
      ε » ε ∙ Level ∙ U (var x0) ∙ ℕ ∙ ℕ ∙ U (var x3) ⊢ var x3 ∷
        U (var x4)
    UℕℕU⊢3 = var₃ (⊢U′ (var₃ (⊢ℕ ⊢Uℕ)))

    ⊢UℕℕU3 : ε »⊢ ε ∙ Level ∙ U (var x0) ∙ ℕ ∙ ℕ ∙ U (var x3) ∙ var x3
    ⊢UℕℕU3 = ∙ univ UℕℕU⊢3

------------------------------------------------------------------------
-- A universe-polymorphic identity function

-- A universe-polymorphic identity function with an erased type argument.

id : Term n
id = lam 𝟘 (lam 𝟘 (lam ω (var x0)))

-- The universe-polymorphic identity function is well-typed (in a
-- well-formed context, assuming that Level is allowed).

⊢id :
  Level-allowed → ⊢ Γ →
  Γ ⊢ id ∷
    Π 𝟘 , p ▷ Level ▹ Π 𝟘 , p ▷ U (var x0) ▹ Π ω , q ▷ var x0 ▹ var x1
⊢id ok ⊢Γ = lamⱼ′ Π-𝟘-ok (lamⱼ′ Π-𝟘-ok (ΓU⊢id ok ⊢Γ))

-- The universe-polymorphic identity function is well-resourced (with respect
-- to the zero usage context).

▸id : 𝟘ᶜ {n} ▸[ 𝟙ᵐ ] id
▸id = lamₘ (lamₘ (lamₘ var))

-- The universe-polymorphic identity function applied to three free
-- variables.

id-generic : Term 3
id-generic = id ∘⟨ 𝟘 ⟩ var x2 ∘⟨ 𝟘 ⟩ var x1 ∘⟨ ω ⟩ var x0

-- The term id-generic is well-typed (in a certain context, assuming
-- that Level is allowed).

⊢id-generic :
  Level-allowed →
  ε » ε ∙ Level ∙ U (var x0) ∙ var x0 ⊢ id-generic ∷ var x1
⊢id-generic ok =
  ((⊢id ok ⊢Γ ∘ⱼ var ⊢Γ (there (there here))) ∘ⱼ var ⊢Γ (there here)) ∘ⱼ
  var ⊢Γ here
  where
  ⊢Γ = ∙ univ (var₀ (⊢U0 ok ε))

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

-- The term id-ℕ-zero is well-typed (in the empty context, assuming
-- that Level is allowed).

⊢id-ℕ-zero : Level-allowed → ε » ε ⊢ id-ℕ-zero ∷ ℕ
⊢id-ℕ-zero ok = ((⊢id ok εε ∘ⱼ zeroᵘⱼ ok εε) ∘ⱼ ℕⱼ εε) ∘ⱼ zeroⱼ εε

-- The term id-ℕ-zero is well-resourced (with respect to the empty
-- usage context).

▸id-ℕ-zero : ε ▸[ 𝟙ᵐ ] id-ℕ-zero
▸id-ℕ-zero = ((▸id ∘ₘ zeroᵘₘ) ∘ₘ ℕₘ) ∘ₘ zeroₘ

-- The term id-ℕ-zero reduces to zero (assuming that Level is
-- allowed).

id-ℕ-zero⇒*zero : Level-allowed → ε » ε ⊢ id-ℕ-zero ⇒* zero ∷ ℕ
id-ℕ-zero⇒*zero ok =
  β-red-⇒₃′ Π-𝟘-ok Π-𝟘-ok Π-ω-ok (var (⊢U∙0 ok ε) here) (zeroᵘⱼ ok εε)
    (ℕⱼ εε) (zeroⱼ εε)

-- The erasure of id-ℕ-zero reduces to zero.

erase-id-ℕ-zero⇒*zero : vs T.⊢ erase str id-ℕ-zero ⇒* T.zero
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

-- The function id₀ is well-typed (with respect to empty contexts).

⊢id₀ : ε » ε ⊢ id₀ ∷ Π 𝟘 , p ▷ ℕ ▹ ℕ
⊢id₀ = lamⱼ′ Π-𝟘-ok (var₀ (⊢ℕ εε))

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

-- The term id₀-zero is well-typed (with respect to empty contexts).

⊢id₀-zero : ε » ε ⊢ id₀-zero ∷ ℕ
⊢id₀-zero = ⊢id₀ ∘ⱼ zeroⱼ εε

-- The term id₀-zero is not well-resourced.

¬▸id₀-zero : ¬ γ ▸[ 𝟙ᵐ ] id₀-zero
¬▸id₀-zero ▸id₀-zero =
  case inv-usage-app ▸id₀-zero of λ {
    (invUsageApp ▸id₀ _ _) →
  ¬▸id₀ ▸id₀ }

-- The term id₀-zero reduces to zero.

id₀-zero⇒*zero : ε » ε ⊢ id₀-zero ⇒* zero ∷ ℕ
id₀-zero⇒*zero =
  redMany (β-red (⊢ℕ ⊢εℕ) (var ⊢εℕ here) (zeroⱼ εε) PE.refl Π-𝟘-ok)

-- The erasure of id₀-zero reduces to loop?.

erase-id₀-zero⇒*loop? : ∀ s → vs T.⊢ erase s id₀-zero ⇒* loop? s
erase-id₀-zero⇒*loop? strict =
  T.trans (T.β-red T.↯) T.refl
erase-id₀-zero⇒*loop? non-strict =
  T.refl

opaque
  unfolding loop

  -- The erasure of id₀-zero does not reduce to T.zero.

  ¬erase-id₀-zero⇒*zero : ¬ vs T.⊢ erase str id₀-zero ⇒* T.zero
  ¬erase-id₀-zero⇒*zero {vs} {str = strict} =
    vs T.⊢ erase strict id₀-zero ⇒* T.zero       →⟨ TP.red*Det $ erase-id₀-zero⇒*loop? strict ⟩
    vs T.⊢ T.↯ ⇒* T.zero ⊎ vs T.⊢ T.zero ⇒* T.↯  →⟨ ⊎.map TP.↯-noRed TP.zero-noRed ⟩
    T.zero PE.≡ T.↯ ⊎ T.↯ PE.≡ T.zero            →⟨ (λ { (inj₁ ()); (inj₂ ()) }) ⟩
    ⊥                                            □
  ¬erase-id₀-zero⇒*zero {vs} {str = non-strict} =
    vs T.⊢ erase non-strict id₀-zero ⇒* T.zero                           →⟨ TP.red*Det $ erase-id₀-zero⇒*loop? _ ⟩
    vs T.⊢ loop non-strict ⇒* T.zero ⊎ vs T.⊢ T.zero ⇒* loop non-strict  →⟨ ⊎.map (¬loop⇒* T.zero) TP.zero-noRed ⟩
    ⊥ ⊎ loop non-strict PE.≡ T.zero                                      →⟨ (λ { (inj₁ ()); (inj₂ ()) }) ⟩
    ⊥                                                                    □

------------------------------------------------------------------------
-- A larger example, which makes use of the fact that uses in the
-- arguments of the eliminator for the empty type can be "ignored"

opaque

  private

    -- Parts of the implementation of Vec.

    Vec-body₂ : Term (3+ n)
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
  Vec = lam 𝟘 (lam ω Vec-body₁)


opaque
  unfolding Vec

  -- Vec is well-resourced.

  ▸Vec : ε ▸[ 𝟙ᵐ ] Vec
  ▸Vec =
    lamₘ $
    lamₘ $
    lamₘ $
    natrec-nr-or-no-nrₘ (Liftₘ var Unitₘ)
      (ΠΣₘ var $ sub var $ begin
         𝟘ᶜ ∙ ω ∙ r  ≤⟨ ≤ᶜ-refl ∙ greatest-elem _ ⟩
         𝟘ᶜ ∙ ω ∙ 𝟘  ∎)
      (sub (var {x = x0} {m = 𝟙ᵐ}) $ begin
         ε ∙ 𝟘 ∙ ω ∙ ω  ≤⟨ ≤ᶜ-refl ⟩
         ε ∙ 𝟘 ∙ 𝟘 ∙ ω  ∎)
      (sub (Uₘ var) $ begin
         𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ EM.·-zeroʳ _ ⟩
         𝟘ᶜ                ∎)
      (begin
         ε ∙ 𝟘            ∙ ω ∙ ω  ≈˘⟨ ε ∙ nr-𝟘 ∙ PE.refl ∙ PE.refl ⟩
         ε ∙ nr 𝟘 ω 𝟘 𝟘 𝟘 ∙ ω ∙ ω  ∎)
      (≤ᶜ-refl , (λ _ → ≤ᶜ-refl) , (λ _ → ≤ᶜ-refl) , ≤ᶜ-refl)
      (let x , x-glb = Erasure-nrᵢ-glb ω ω 𝟘
           χ , χ-glb = ∃nrᵢ-GLB→∃nrᵢᶜ-GLB (Erasure-nrᵢ-glb _) 𝟘ᶜ _
       in
       x , χ , x-glb , χ-glb ,
       (begin
          ε ∙ 𝟘 ∙ ω ∙ ω              ≤⟨ (∧ᶜ-greatest-lower-bound ≤ᶜ-refl $
                                         χ-glb .proj₂ (ε ∙ 𝟘 ∙ ω ∙ ω) λ i →
                                         ε ∙ ≤-reflexive (PE.sym $ nrᵢ-𝟘 i) ∙ ≤-refl ∙ ≤-refl) ⟩
          (ε ∙ 𝟘 ∙ ω ∙ ω) ∧ᶜ χ       ≈⟨ ∧ᶜ≈ᶜ+ᶜ ⟩
          (ε ∙ 𝟘 ∙ ω ∙ ω) +ᶜ χ       ≡⟨⟩
          ω ·ᶜ (ε ∙ 𝟘 ∙ ω ∙ ω) +ᶜ χ  ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (least-elem′ x (x-glb .proj₁ 0))) ⟩
          x ·ᶜ (ε ∙ 𝟘 ∙ ω ∙ ω) +ᶜ χ  ∎))
      where
      open ≤ᶜ-reasoning

private opaque
  unfolding Vec

  -- A typing rule for Vec-body₂.

  ⊢Vec-body₂ :
    Level-allowed →
    ε » ε ∙ Level ∙ U (var x0) ∙ ℕ ⊢ Vec-body₂ ∷ U (var x2)
  ⊢Vec-body₂ ok =
    natrecⱼ
      (Liftⱼ≤ (supᵘ-zeroˡ (var (⊢Uℕ ok) (there (there here))))
         (Unitⱼ (⊢Uℕ ok) Unit-ok))
      (ΠΣⱼ′ (UℕℕU⊢3 ok) (var (⊢UℕℕU3 ok) (there here)) Σˢ-ω-ok)
      (var (⊢Uℕ ok) here)

private opaque
  unfolding Vec

  -- A typing rule for Vec-body₁.

  ⊢Vec-body₁ :
    Level-allowed →
    ε » ε ∙ Level ∙ U (var x0) ⊢ Vec-body₁ ∷ Π ω , q ▷ ℕ ▹ U (var x2)
  ⊢Vec-body₁ ok = lamⱼ′ Π-ω-ok (⊢Vec-body₂ ok)

opaque
  unfolding Vec

  -- A typing rule for Vec.

  ⊢Vec :
    Level-allowed →
    ε » ε ⊢ Vec ∷
      Π 𝟘 , p ▷ Level ▹ Π ω , q ▷ U (var x0) ▹ Π ω , q ▷ ℕ ▹ U (var x2)
  ⊢Vec ok = lamⱼ′ Π-𝟘-ok (lamⱼ′ Π-ω-ok (⊢Vec-body₁ ok))

-- Some lemmas used below.

private module Vec-lemmas (ok : Level-allowed) (⊢A : Γ ⊢ A ∷ U l) where

  opaque
    unfolding Vec

    ⊢Γ : ⊢ Γ
    ⊢Γ = wfTerm ⊢A

    »Γ : » Γ .defs
    »Γ = defn-wf ⊢Γ

    ⊢l : Γ ⊢ l ∷Level
    ⊢l = inversion-U-Level (wf-⊢∷ ⊢A)

    ⊢l∷ : Γ ⊢ l ∷ Level
    ⊢l∷ = ⊢∷Level→⊢∷Level ok ⊢l

    ΓLU⊢ℕ : Γ »∙ Level »∙ U (var x0) ⊢ ℕ
    ΓLU⊢ℕ = ⊢ℕ (∙ ⊢U′ (var₀ (Levelⱼ′ ok ⊢Γ)))

    Γℕ⊢Ul : Γ »∙ ℕ ⊢ U (wk1 l)
    Γℕ⊢Ul = ⊢U (W.wkLevel₁ (⊢ℕ ⊢Γ) ⊢l)

    ΓℕUl⊢A∷ :
      Γ »∙ ℕ »∙ U (wk1 l) ⊢ wk[ 2 ] A ∷
        U (wk1 l [ 2 ][ suc (var x1 ) ]↑)
    ΓℕUl⊢A∷ =
      PE.subst (_⊢_∷_ _ _) (PE.cong U $ PE.sym $ wk1-[][]↑ 2) $
      W.wkTerm₁ Γℕ⊢Ul (W.wkTerm₁ (⊢ℕ ⊢Γ) ⊢A)

    ΓℕUl⊢A : Γ »∙ ℕ »∙ U (wk1 l) ⊢ wk[ 2 ] A
    ΓℕUl⊢A = univ ΓℕUl⊢A∷

    Vec-step :
      Γ ⊢ t ∷ ℕ →
      Γ ⊢ wk wk₀ Vec ∘⟨ 𝟘 ⟩ l ∘⟨ ω ⟩ A ∘⟨ ω ⟩ t ⇒*
        Vec-body₂ [ consSubst (consSubst (sgSubst l) A) t ] ∷ U l
    Vec-step ⊢t =
      β-red-⇒₃′
        Π-𝟘-ok Π-ω-ok Π-ω-ok
        (W.wkTerm (W.liftʷ (W.lift (W.lift W.wk₀∷⊇)) ΓLU⊢ℕ) $
         WD.defn-wkTerm (WD.»⊇ε »Γ) $
         ⊢Vec-body₂ ok)
        ⊢l∷ ⊢A ⊢t

    ⊢Lift-Unit : Γ ⊢ Lift l (Unit s) ∷ U (wk1 l [ zero ]₀)
    ⊢Lift-Unit =
      conv (Liftⱼ′ ⊢l (Unitⱼ ⊢Γ Unit-ok))
        (U-cong-⊢≡ $
         PE.subst (_⊢_≡_∷Level _ _) (PE.sym $ wk1-sgSubst _ _) $
         supᵘₗ-identityˡ ⊢l)

    ⊢Σ1 :
      Γ »∙ ℕ »∙ U (wk1 l) ⊢ Σˢ ω , r ▷ wk[ 2 ] A ▹ var x1 ∷
        U (wk1 l [ 2 ][ suc (var x1 ) ]↑)
    ⊢Σ1 =
      ΠΣⱼ′ ΓℕUl⊢A∷
        (PE.subst (_⊢_∷_ _ _)
           (PE.cong (U ∘→ wk1) $ PE.sym $ wk1-[][]↑ 2) $
         var₁ ΓℕUl⊢A)
        Σˢ-ω-ok

opaque

  -- A typing rule for applications of Vec.

  ⊢Vec∘ :
    Level-allowed →
    Γ ⊢ A ∷ U l →
    Γ ⊢ t ∷ ℕ →
    Γ ⊢ wk wk₀ Vec ∘⟨ 𝟘 ⟩ l ∘⟨ ω ⟩ A ∘⟨ ω ⟩ t ∷ U l
  ⊢Vec∘ ok ⊢A ⊢t =
    redFirst*Term (Vec-lemmas.Vec-step ok ⊢A ⊢t)

opaque
  unfolding Vec

  -- A computation rule for Vec.

  Vec∘zero⇒* :
    Level-allowed →
    Γ ⊢ A ∷ U l →
    Γ ⊢ wk wk₀ Vec ∘⟨ 𝟘 ⟩ l ∘⟨ ω ⟩ A ∘⟨ ω ⟩ zero ⇒* Lift l (Unit s) ∷
      U l
  Vec∘zero⇒* {A} {l} ok ⊢A =
    wk wk₀ Vec ∘⟨ 𝟘 ⟩ l ∘⟨ ω ⟩ A ∘⟨ ω ⟩ zero                ⇒*⟨ Vec-step (zeroⱼ ⊢Γ) ⟩
    Vec-body₂ [ consSubst (consSubst (sgSubst l) A) zero ]  ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _) (PE.cong U $ wk1-sgSubst _ _) $
                                                               natrec-zero ⊢Lift-Unit ⊢Σ1 ⟩∎
    Lift l (Unit s)                                         ∎
    where
    open RR
    open Vec-lemmas ok ⊢A

opaque
  unfolding Vec

  -- An equality rule for Vec.

  Vec∘suc≡ :
    Level-allowed →
    Γ ⊢ A ∷ U l →
    Γ ⊢ t ∷ ℕ →
    Γ ⊢
      wk wk₀ Vec ∘⟨ 𝟘 ⟩ l ∘⟨ ω ⟩ A ∘⟨ ω ⟩ suc t ≡
      Σˢ ω , r ▷ A ▹
        (wk wk₀ Vec ∘⟨ 𝟘 ⟩ wk1 l ∘⟨ ω ⟩ wk1 A ∘⟨ ω ⟩ wk1 t) ∷
      U l
  Vec∘suc≡ {A} {l} {t} ok ⊢A ⊢t =
    let σ = consSubst (consSubst (sgSubst l) A) in
    wk wk₀ Vec ∘⟨ 𝟘 ⟩ l ∘⟨ ω ⟩ A ∘⟨ ω ⟩ suc t                           ⇒*⟨ V₁.Vec-step (sucⱼ ⊢t) ⟩⊢
    Vec-body₂ [ σ (suc t) ]                                             ⇒⟨ (let open V₁ in
                                                                            PE.subst₂ (_⊢_⇒_∷_ _ _)
                                                                              (PE.cong₂ (Σˢ ω , r ▷_▹_) wk2-[,] (wk-subst {σ = σ t} Vec-body₂))
                                                                              (PE.cong U $ wk1-sgSubst _ _) $
                                                                            natrec-suc ⊢Lift-Unit ⊢Σ1 ⊢t) ⟩⊢
    Σˢ ω , r ▷ A ▹ (Vec-body₂ [ wk1Subst (σ t) ])                       ≡˘⟨ ΠΣ-cong′ (refl ⊢A)
                                                                              (subset*Term (V₂.Vec-step (W.wkTerm₁ (univ ⊢A) ⊢t))) Σˢ-ω-ok ⟩⊢∎
    Σˢ ω , r ▷ A ▹ (wk wk₀ Vec ∘⟨ 𝟘 ⟩ wk1 l ∘⟨ ω ⟩ wk1 A ∘⟨ ω ⟩ wk1 t)  ∎
    where
    open Tools.Reasoning.PropositionalEquality
    open TmR
    module V₁ = Vec-lemmas ok ⊢A
    module V₂ = Vec-lemmas ok (W.wkTerm₁ (univ ⊢A) ⊢A)

opaque

  private

    -- Parts of the implementation of Non-zero.

    Non-zero-body : Term (1+ n)
    Non-zero-body =
      natcase 𝟘 𝟘
        (U zeroᵘ)
        Empty
        (Unit s)
        (var x0)

  -- A natural number predicate that holds for non-zero numbers.

  Non-zero : Term 0
  Non-zero = lam ω Non-zero-body

opaque
  unfolding Non-zero

  -- Non-zero is well-resourced.

  ▸Non-zero : ε ▸[ 𝟙ᵐ ] Non-zero
  ▸Non-zero =
    lamₘ $
    ▸natcase′ Emptyₘ Unitₘ var
      (sub (Uₘ zeroᵘₘ) $
       let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
         𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ EM.·-zeroʳ _ ⟩
         𝟘ᶜ                ∎)
      ≤ᶜ-refl (≤ᶜ-refl , (λ _ → ≤ᶜ-refl) , (λ _ → ≤ᶜ-refl) , ≤ᶜ-refl) ≤ᶜ-refl

opaque
  unfolding Non-zero

  private

    -- A typing rule for Non-zero-body.

    ⊢Non-zero-body : ε » ε ∙ ℕ ⊢ Non-zero-body ∷ U zeroᵘ
    ⊢Non-zero-body =
      ⊢natcase (⊢U₀ ⊢ℕℕ) (Emptyⱼ ⊢εℕ) (Unitⱼ ⊢ℕℕ Unit-ok) (var ⊢εℕ here)

  -- A typing rule for Non-zero.

  ⊢Non-zero : ε » ε ⊢ Non-zero ∷ Π ω , q ▷ ℕ ▹ U zeroᵘ
  ⊢Non-zero = lamⱼ′ Π-ω-ok ⊢Non-zero-body

private opaque
  unfolding Non-zero

  -- A reduction rule for Non-zero.

  Non-zero-step :
    Γ ⊢ t ∷ ℕ →
    Γ ⊢ wk wk₀ Non-zero ∘⟨ ω ⟩ t ⇒
      natcase 𝟘 𝟘 (U zeroᵘ) Empty (Unit s) t ∷ U zeroᵘ
  Non-zero-step ⊢t =
    let ⊢Γ = wfTerm ⊢t in
    PE.subst₂ (_⊢_⇒_∷_ _ _)
      (PE.trans (PE.cong _[ _ ]₀ wk-natcase)
       natcase-[])
      PE.refl $
    β-red (⊢U₀ (∙ ⊢ℕ ⊢Γ))
      (W.wkTerm (W.liftʷ W.wk₀∷⊇ (⊢ℕ ⊢Γ)) $
       WD.defn-wkTerm (WD.»⊇ε (defn-wf ⊢Γ)) ⊢Non-zero-body)
      ⊢t PE.refl Π-ω-ok

opaque

  -- A typing rule for applications of Non-zero.

  ⊢Non-zero∘ :
    Γ ⊢ t ∷ ℕ →
    Γ ⊢ wk wk₀ Non-zero ∘⟨ ω ⟩ t ∷ U zeroᵘ
  ⊢Non-zero∘ ⊢t =
    redFirstTerm (Non-zero-step ⊢t)

opaque
  unfolding Non-zero

  -- A computation rule for Non-zero.

  Non-zero∘zero⇒* :
    ⊢ Γ →
    Γ ⊢ wk wk₀ Non-zero ∘⟨ ω ⟩ zero ⇒* Empty ∷ U zeroᵘ
  Non-zero∘zero⇒* ⊢Γ =
    let ⊢Γℕ = ∙ ⊢ℕ ⊢Γ in
    wk wk₀ Non-zero ∘⟨ ω ⟩ zero                ⇒⟨ Non-zero-step (zeroⱼ ⊢Γ) ⟩
    natcase 𝟘 𝟘 (U zeroᵘ) Empty (Unit s) zero  ⇒⟨ natcase-zero-⇒ (⊢U₀ ⊢Γℕ) (Emptyⱼ ⊢Γ) (Unitⱼ ⊢Γℕ Unit-ok) ⟩∎
    Empty                                      ∎
    where
    open RR

opaque
  unfolding Non-zero

  -- Another computation rule for Non-zero.

  Non-zero∘suc⇒* :
    Γ ⊢ t ∷ ℕ →
    Γ ⊢ wk wk₀ Non-zero ∘⟨ ω ⟩ suc t ⇒* Unit s ∷ U zeroᵘ
  Non-zero∘suc⇒* {t} ⊢t =
    let ⊢Γ  = wfTerm ⊢t
        ⊢Γℕ = ∙ ⊢ℕ ⊢Γ
    in
    wk wk₀ Non-zero ∘⟨ ω ⟩ suc t                  ⇒⟨ Non-zero-step (sucⱼ ⊢t) ⟩
    natcase 𝟘 𝟘 (U zeroᵘ) Empty (Unit s) (suc t)  ⇒⟨ natcase-suc-⇒ (⊢U₀ ⊢Γℕ) (Emptyⱼ ⊢Γ) (Unitⱼ ⊢Γℕ Unit-ok) ⊢t ⟩∎
    Unit s                                        ∎
    where
    open RR

opaque

  -- A safe head function for vectors.

  head : Term 0
  head =
    lam 𝟘 $
    lam 𝟘 $
    lam ω $
    natcase 𝟘 ω
      (Π ω , q ▷ wk wk₀ Vec ∘⟨ 𝟘 ⟩ var x3 ∘⟨ ω ⟩ var x2 ∘⟨ ω ⟩ var x0 ▹
       Π 𝟘 , p ▷ wk wk₀ Non-zero ∘⟨ ω ⟩ var x1 ▹
       var x4)
      (lam ω $ lam 𝟘 $ emptyrec 𝟘 (var x3) (var x0))
      (lam ω $ lam 𝟘 $ fst ω (var x1))
      (var x0)

opaque
  unfolding head natcase

  -- In the strict setting the extraction of head includes an erased
  -- part (loop strict).

  erase-strict-head :
    erase strict head PE.≡
    (T.Term.lam $ T.Term.lam $ T.Term.lam $
     T.natrec
       (T.lam (T.lam (loop strict)))
       (T.lam (T.lam (T.fst (T.var x1))))
       (T.var x0))
  erase-strict-head = PE.refl

opaque
  unfolding head natcase loop

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

opaque
  unfolding head

  -- The term head is well-resourced.

  ▸head : ε ▸[ 𝟙ᵐ ] head
  ▸head =
    lamₘ $
    lamₘ $
    lamₘ $
    ▸natcase′
      (lamₘ $
       lamₘ $
       sub (emptyrecₘ var var emptyrec-ok) $ begin
         𝟘ᶜ ∙ ω ∙ 𝟘  ≤⟨ ≤ᶜ-refl ⟩
         𝟘ᶜ          ∎)
      (lamₘ $
       lamₘ $
       fstₘ 𝟙ᵐ
         (sub var $ begin
            𝟘ᶜ ∙ ω ∙ 𝟘  ≤⟨ ≤ᶜ-refl ⟩
            𝟘ᶜ ∙ ω ∙ 𝟘  ∎)
         (≢𝟘→⌞⌟≡𝟙ᵐ {p = ω} (λ ()))
         (λ _ → PE.refl))
      var
      (sub
         (ΠΣₘ (((𝟘ᶜ▸[𝟙ᵐ]→ (wkUsage wk₀ ▸Vec) ∘ₘ var) ∘ₘ var) ∘ₘ var) $
          sub
            (ΠΣₘ (𝟘ᶜ▸[𝟙ᵐ]→ (wkUsage wk₀ ▸Non-zero) ∘ₘ var) $
             sub var $ begin
               ε ∙ 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ · p  ≤⟨ ≤ᶜ-refl ∙ greatest-elem _ ⟩
               ε ∙ 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟘            ∎) $ begin
               𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ ∙ 𝟘 ∙ ⌜ (𝟘ᵐ? ᵐ· 𝟘) ᵐ· ω ⌝ ∙ ⌜ 𝟘ᵐ? ⌝ · q ≤⟨ ≤ᶜ-refl ∙ greatest-elem _ ∙ greatest-elem _ ⟩
               𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ ∙ 𝟘 ∙ 𝟘                   ∙ 𝟘      ∎) $ begin
               𝟘ᶜ ∙ ⌜ (𝟘ᵐ? ᵐ· ω) ᵐ· ω ⌝ + 𝟘 + ⌜ 𝟘ᵐ? ⌝ ∙ 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ · ω  ≈⟨ ≈ᶜ-refl ∙ lemma ⟩
               𝟘ᶜ ∙ ⌜ (𝟘ᵐ? ᵐ· ω) ᵐ· ω ⌝ + 𝟘 + ⌜ 𝟘ᵐ? ⌝ ∙ 𝟘 ∙
               ⌜ (𝟘ᵐ? ᵐ· ω) ᵐ· ω ⌝ + ⌜ (𝟘ᵐ? ᵐ· 𝟘) ᵐ· ω ⌝                 ∎)
      (begin
         𝟘ᶜ ∙ ω                  ≤⟨ ≤ᶜ-reflexive (≈ᶜ-sym nrᶜ-𝟘ᶜ) ∙ ≤-refl ⟩
         nrᶜ 𝟘 𝟘 𝟘ᶜ 𝟘ᶜ (𝟘ᶜ ∙ ω)  ∎)
      (≤ᶜ-refl , (λ _ → ≤ᶜ-refl) , (λ _ → ≤ᶜ-refl) , ≤ᶜ-refl)
      ≤ᶜ-refl
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
    open ≤ᶜ-reasoning

private opaque

  -- Some lemmas used below.

  wk-Vec-[]∘³≡ :
    (wk wk₀ Vec [ σ ]) ∘⟨ 𝟘 ⟩ l ∘⟨ ω ⟩ A ∘⟨ ω ⟩ t PE.≡
    wk wk₀ Vec ∘⟨ 𝟘 ⟩ l ∘⟨ ω ⟩ A ∘⟨ ω ⟩ t
  wk-Vec-[]∘³≡ =
    PE.cong (flip _∘⟨ ω ⟩_ _) $
    PE.cong (flip _∘⟨ ω ⟩_ _) $
    PE.cong (_∘⟨ _ ⟩ _) wk-wk₀-[]≡

  wk-Non-zero-[]∘≡ :
    (wk wk₀ Non-zero [ σ ]) ∘⟨ ω ⟩ t PE.≡
    wk wk₀ Non-zero ∘⟨ ω ⟩ t
  wk-Non-zero-[]∘≡ =
    PE.cong (_∘⟨ _ ⟩ _) wk-wk₀-[]≡

opaque
  unfolding head

  -- A typing rule for head.

  ⊢head :
    Level-allowed →
    ε » ε ⊢
    head ∷
    Π 𝟘 , p ▷ Level ▹
    Π 𝟘 , p ▷ U (var x0) ▹
    Π ω , q ▷ ℕ ▹
    Π ω , q ▷ wk wk₀ Vec ∘⟨ 𝟘 ⟩ var x2 ∘⟨ ω ⟩ var x1 ∘⟨ ω ⟩ var x0 ▹
    Π 𝟘 , p ▷ wk wk₀ Non-zero ∘⟨ ω ⟩ var x1 ▹
    var x3
  ⊢head ok =
    let LUℕ⊢ℕ        = ⊢ℕ (⊢Uℕ ok)
        ⊢Vec320      = ⊢Vec∘ ok (var₂ LUℕ⊢ℕ) (var₀ LUℕ⊢ℕ)
        ⊢Non-zero-0  =
          PE.subst (_⊢_ _) (PE.sym wk-Non-zero-[]∘≡) $
          _⊢_.univ $ ⊢Non-zero∘ $ zeroⱼ $ ∙_ $
          PE.subst (_⊢_ _) (PE.sym wk-Vec-[]∘³≡) $
          _⊢_.univ $ ⊢Vec∘ ok (var₁ (U⊢ℕ ok)) (zeroⱼ (∙ U⊢ℕ ok))
        ⊢Non-zero-1+ =
          PE.subst (_⊢_ _) (PE.sym wk-Non-zero-[]∘≡) $
          _⊢_.univ $ ⊢Non-zero∘ $ sucⱼ $ var₁ $
          PE.subst (_⊢_ _) (PE.sym wk-Vec-[]∘³≡) $
          _⊢_.univ $ ⊢Vec∘ ok (var₂ LUℕ⊢ℕ) (sucⱼ (var₀ LUℕ⊢ℕ))
    in
    PE.subst (_⊢_∷_ _ _)
      (PE.cong (Π 𝟘 , p ▷_▹_ _) $
       PE.cong (Π 𝟘 , p ▷_▹_ _) $
       PE.cong (Π ω , q ▷_▹_ _) $
       PE.cong₂ (Π ω , q ▷_▹_) wk-Vec-[]∘³≡ $
       PE.cong (flip (Π 𝟘 , p ▷_▹_) _) $
       PE.cong (flip _∘⟨ ω ⟩_ _)
       wk-wk₀-[]≡) $
    lamⱼ′ Π-𝟘-ok $
    lamⱼ′ Π-𝟘-ok $
    lamⱼ′ Π-ω-ok $
    ⊢natcase
      (ΠΣⱼ
         (ΠΣⱼ
            (univ $ var₄ $ _⊢_.univ $
             W.wkTerm (W.wk₀∷ʷ⊇ (∙ univ ⊢Vec320)) ⊢Non-zero ∘ⱼ
             var₁ (univ ⊢Vec320))
            Π-𝟘-ok)
         Π-ω-ok)
      (lamⱼ′ Π-ω-ok $
       lamⱼ′ Π-𝟘-ok $
       emptyrecⱼ
         (univ (var₃ ⊢Non-zero-0))
         (conv (var₀ ⊢Non-zero-0)
            (wk1 (wk wk₀ Non-zero [ sgSubst zero ⇑ ]) ∘⟨ ω ⟩ zero  ≡⟨ PE.cong wk1 wk-Non-zero-[]∘≡ ⟩⊢≡
             wk1 (wk wk₀ Non-zero) ∘⟨ ω ⟩ zero                     ≡⟨ PE.cong (flip _∘⟨ ω ⟩_ _) $
                                                                      wk-comp _ _ _ ⟩⊢≡
             wk wk₀ Non-zero ∘⟨ ω ⟩ zero                           ⇒*⟨ Non-zero∘zero⇒* (∙ ⊢Non-zero-0) ⟩⊢∷∎
             Empty                                                 ∎)))
      (lamⱼ′ Π-ω-ok $
       lamⱼ′ Π-𝟘-ok $
       fstⱼ′ $
       conv
         (var₁ $
          PE.subst (_⊢_ _) (PE.sym wk-Non-zero-[]∘≡) $
          _⊢_.univ $ ⊢Non-zero∘ $ sucⱼ $ var₁ $
          PE.subst (_⊢_ _) (PE.sym wk-Vec-[]∘³≡) $
          univ (⊢Vec∘ ok (var₂ LUℕ⊢ℕ) (sucⱼ (var₀ LUℕ⊢ℕ))))
         (wk[ 2 ] (wk wk₀ Vec [ suc (var x0) ]↑)
            ∘⟨ 𝟘 ⟩ var x5 ∘⟨ ω ⟩ var x4 ∘⟨ ω ⟩ suc (var x2)           ≡⟨ PE.cong wk[ 2 ] wk-Vec-[]∘³≡ ⟩⊢≡

          wk[ 2 ] (wk wk₀ Vec)
            ∘⟨ 𝟘 ⟩ var x5 ∘⟨ ω ⟩ var x4 ∘⟨ ω ⟩ suc (var x2)           ≡⟨ PE.cong (flip _∘⟨ ω ⟩_ _) $
                                                                         PE.cong (flip _∘⟨ ω ⟩_ _) $
                                                                         PE.cong (_∘⟨ _ ⟩ _) $
                                                                         PE.trans (wk[]≡wk[]′ {k = 2}) $
                                                                         wk-comp _ _ _ ⟩⊢≡

          wk wk₀ Vec ∘⟨ 𝟘 ⟩ var x5 ∘⟨ ω ⟩ var x4 ∘⟨ ω ⟩ suc (var x2)  ≡⟨ univ (Vec∘suc≡ ok (var₄ ⊢Non-zero-1+) (var₂ ⊢Non-zero-1+)) ⟩⊢∎

          Σˢ ω , r ▷ var x4 ▹
            (wk wk₀ Vec ∘⟨ 𝟘 ⟩ var x6 ∘⟨ ω ⟩ var x5 ∘⟨ ω ⟩ var x3)    ∎))
      (var₀ (U⊢ℕ ok))
      where
      open TyR

opaque

  -- A concrete vector which contains a single natural number.

  [0] : Term 0
  [0] = prodˢ ω zero (lift (star s))

opaque
  unfolding [0]

  -- [0] is well-resourced.

  ▸[0] : ε ▸[ 𝟙ᵐ ] [0]
  ▸[0] = prodˢₘ zeroₘ (liftₘ starₘ)

opaque
  unfolding [0]

  -- If Level is allowed, then [0] is in η-long normal form.

  [0]-normal :
    Level-allowed →
    ε » ε ⊢nf [0] ∷ Vec ∘⟨ 𝟘 ⟩ zeroᵘ ∘⟨ ω ⟩ ℕ ∘⟨ ω ⟩ suc zero
  [0]-normal ok =
    let ⊢0 = ⊢zeroᵘ εε in
    PE.subst (_⊢nf_∷_ _ _)
      (PE.cong (flip _∘⟨ ω ⟩_ _) $
       PE.cong (flip _∘⟨ ω ⟩_ _) $
       PE.cong (_∘⟨ _ ⟩ _) $
       wk-id _) $
    _⊢nf_∷_.convₙ
      (prodₙ (Liftⱼ (W.wkLevel₁ (⊢ℕ εε) ⊢0) (⊢Unit (∙ ⊢ℕ εε) Unit-ok))
         (zeroₙ εε) (liftₙ ⊢0 (starₙ εε Unit-ok)) Σˢ-ω-ok) $
    _⊢_≡_.univ $
    sym′ $
    _⊢_≡_∷_.trans (Vec∘suc≡ ok (ℕⱼ εε) (zeroⱼ εε)) $
    ΠΣ-cong ⊢0 (refl (ℕⱼ εε))
      (subset*Term (Vec∘zero⇒* ok (ℕⱼ (∙ ⊢ℕ εε)))) Σˢ-ω-ok

opaque

  -- A typing rule for [0].

  ⊢[0] :
    Level-allowed →
    ε » ε ⊢ [0] ∷ Vec ∘⟨ 𝟘 ⟩ zeroᵘ ∘⟨ ω ⟩ ℕ ∘⟨ ω ⟩ suc zero
  ⊢[0] = ⊢nf∷→⊢∷ ∘→ [0]-normal

opaque

  -- An application of head 0 to [0] and some other arguments.

  head-[0] : Term 0
  head-[0] =
    head ∘⟨ 𝟘 ⟩ zeroᵘ ∘⟨ 𝟘 ⟩ ℕ ∘⟨ ω ⟩ suc zero ∘⟨ ω ⟩ [0] ∘⟨ 𝟘 ⟩ star s

opaque
  unfolding head-[0] head [0] natcase

  -- In the strict setting the extraction of head-[0] includes several
  -- erased parts (T.↯ and loop strict).

  erase-strict-head-[0] :
    erase strict head-[0] PE.≡
    T.lam
      (T.Term.lam $ T.Term.lam $
       T.natrec (T.lam (T.lam (loop strict)))
         (T.lam (T.lam (T.fst (T.var x1))))
         (T.var x0)) T.∘⟨ strict ⟩
    T.↯ T.∘⟨ strict ⟩
    T.↯ T.∘⟨ strict ⟩
    T.suc⟨ strict ⟩ T.zero T.∘⟨ strict ⟩
    T.prod⟨ strict ⟩ T.zero T.star T.∘⟨ strict ⟩
    T.↯
  erase-strict-head-[0] = PE.refl

opaque
  unfolding head-[0] head [0] natcase loop

  -- In the non-strict setting three of those parts are removed
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

opaque
  unfolding head-[0]

  -- The term head-[0] is well-resourced.

  ▸head-[0] : ε ▸[ 𝟙ᵐ ] head-[0]
  ▸head-[0] =
    ((((▸head ∘ₘ zeroᵘₘ) ∘ₘ ℕₘ) ∘ₘ sucₘ zeroₘ) ∘ₘ 𝟘ᶜ▸[𝟙ᵐ]→ ▸[0]) ∘ₘ
    starₘ

opaque
  unfolding head-[0]

  -- The term head-[0] is well-typed (if Level is allowed).

  ⊢head-[0] :
    Level-allowed →
    ε » ε ⊢ head-[0] ∷ ℕ
  ⊢head-[0] ok =
    ((((⊢head ok ∘ⱼ zeroᵘⱼ ok εε) ∘ⱼ ℕⱼ εε) ∘ⱼ sucⱼ (zeroⱼ εε)) ∘ⱼ
     PE.subst (_⊢_∷_ _ _)
       (PE.sym $
        PE.cong (flip _∘⟨ ω ⟩_ _) $
        PE.cong (flip _∘⟨ ω ⟩_ _) $
        PE.cong (_∘⟨ _ ⟩ _) $
        PE.trans
          (PE.trans
             (PE.trans (substCompEq (wk _ Vec [ _ ])) $
              substCompEq (wk _ Vec))
           wk-wk₀-[]≡) $
        wk-id _)
       (⊢[0] ok)) ∘ⱼ
    conv (starⱼ εε Unit-ok)
      (Unit s                                                          ⇐*⟨ Non-zero∘suc⇒* (zeroⱼ εε) ⟩⊢∷∎≡

       wk wk₀ Non-zero ∘⟨ ω ⟩ suc zero                                 ≡˘⟨ PE.cong (flip _∘⟨ ω ⟩_ _) $
                                                                           PE.trans
                                                                             (PE.cong _[ [0] ]₀ $
                                                                              PE.trans
                                                                                (PE.cong _[ _ ] $
                                                                                 PE.trans
                                                                                   (PE.cong _[ _ ] $
                                                                                    wk-wk₀-[]≡ {t = Non-zero}) $
                                                                                 wk-wk₀-[]≡ {t = Non-zero}) $
                                                                              wk-wk₀-[]≡ {t = Non-zero}) $
                                                                           wk-wk₀-[]≡ ⟩
       (wk wk₀ Non-zero [ sgSubst zeroᵘ ⇑[ 3 ] ] [ sgSubst ℕ ⇑[ 2 ] ]
          [ sgSubst (suc zero) ⇑ ] [ [0] ]₀)
         ∘⟨ ω ⟩ suc zero                                               ∎)
    where
    open Tools.Reasoning.PropositionalEquality
    open TyR

opaque
  unfolding head-[0] head [0] natcase

  -- The erasure of head-[0] reduces to T.zero.

  erase-head-[0]⇒*zero : vs T.⊢ erase str head-[0] ⇒* T.zero
  erase-head-[0]⇒*zero {str = non-strict} =
    T.trans (T.app-subst $ T.β-red _) $
    T.trans (T.app-subst T.natrec-suc) $
    T.trans (T.β-red _) $
    T.trans T.Σ-β₁
    T.refl
  erase-head-[0]⇒*zero {str = strict} =
    T.trans (T.app-subst $ T.app-subst $ T.app-subst $ T.app-subst $
             T.β-red T.↯) $
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

opaque

  -- The term head-[0] reduces to zero (if Level is allowed).
  --
  -- Note that this is proved using the fact that the (non-strict)
  -- erasure of head-[0] reduces to T.zero.

  head-[0]⇒*zero :
    Level-allowed →
    ε » ε ⊢ head-[0] ⇒* zero ∷ ℕ
  head-[0]⇒*zero ok =
    case Soundness₀.soundness-ℕ (λ ()) (⊢head-[0] ok)
           ▸head-[0] of λ where
      (0 , head-[0]⇒*zero , _) →
        S.⇒ˢ*zero∷ℕ→⇒*zero ⦃ ok = ε ⦄ head-[0]⇒*zero
      (1+ _ , _ , erase-head-[0]⇒*suc) →
        case TP.red*Det (erase-head-[0]⇒*zero {str = T.non-strict})
               (S.⇒ˢ*suc→⇒*suc (erase-head-[0]⇒*suc _) .proj₂)
        of λ where
          (inj₁ zero⇒*suc) → case TP.zero-noRed zero⇒*suc of λ ()
          (inj₂ suc⇒*zero) → case TP.suc-noRed  suc⇒*zero of λ ()
