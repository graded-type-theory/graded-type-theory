------------------------------------------------------------------------
-- Some examples related to the erasure modality and extraction
------------------------------------------------------------------------

open import Tools.Level

open import Graded.Modality.Instances.Erasure
open import Graded.Modality.Instances.Erasure.Modality
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
open import Tools.Nat using (Nat; 1+; 2+)
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum as ⊎ using (_⊎_; inj₁; inj₂)

open import Definition.Typed TR as DT hiding (id)
open import Definition.Typed.Eta-long-normal-form TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Substitution TR hiding (id)
open import Definition.Typed.Syntactic TR
import Definition.Typed.Weakening TR as W
import Definition.Typed.Weakening.Definition TR as WD
open import Definition.Untyped Erasure as U hiding (id; head)
open import Definition.Untyped.Properties Erasure

private

  EM : Modality
  EM = ErasureModality

  module EM = Modality EM

open import Graded.Context EM
open import Graded.Erasure.Consequences.Soundness TR UR
open import Graded.Erasure.Extraction EM
import Graded.Erasure.SucRed TR as S
open import Graded.Erasure.Target as T
  using (Strictness; strict; non-strict)
open import Graded.Erasure.Target.Non-terminating
import Graded.Erasure.Target.Properties as TP
open import Graded.Modality.Instances.Erasure.Properties
open import Graded.Usage UR
open import Graded.Usage.Inversion UR
open import Graded.Usage.Properties UR
open import Graded.Usage.Restrictions.Natrec EM
open import Graded.Usage.Weakening UR

private variable
  n       : Nat
  ∇       : DCon (Term 0) _
  Γ       : Cons _ _
  vs      : List (T.Term 0)
  A t u v : Term _
  γ       : Conₘ _
  l       : Universe-level
  str     : Strictness

private

  -- Some lemmas used below.

  ⊢ℕ : ε »⊢ ε ∙ ℕ
  ⊢ℕ = ∙ ℕⱼ εε

  ⊢U : » ∇ → ∇ »⊢ ε ∙ U l
  ⊢U »∇ = ∙ Uⱼ (ε »∇)

  U⊢0 : » ∇ → ∇ » ε ∙ U l ⊢ var x0
  U⊢0 »∇ = univ (var (⊢U »∇) here)

  ⊢U0 : » ∇ → ∇ »⊢ ε ∙ U l ∙ var x0
  ⊢U0 »∇ = ∙ U⊢0 »∇

  U⊢id :
    » ∇ → ∇ » ε ∙ U l ⊢ lam ω (var x0) ∷ Π ω , q ▷ var x0 ▹ var x1
  U⊢id »∇ = lamⱼ′ Π-ω-ok (var (⊢U0 »∇) here)

  ΓU⊢id : ⊢ Γ → Γ »∙ U l ⊢ lam ω (var x0) ∷ Π ω , q ▷ var x0 ▹ var x1
  ΓU⊢id (ε »∇) = U⊢id »∇
  ΓU⊢id (∙ ⊢A) =
    W.wkTerm (W.liftʷ (W.step W.id) (Uⱼ (∙ ⊢A)))
             (ΓU⊢id (wf ⊢A))

  U⊢ℕ : » ∇ → ∇ » ε ∙ U l ⊢ ℕ
  U⊢ℕ »∇ = ℕⱼ (⊢U »∇)

  ⊢Uℕ : ε »⊢ ε ∙ U l ∙ ℕ
  ⊢Uℕ = ∙ U⊢ℕ ε

  ⊢Uℕℕ : ε »⊢ ε ∙ U l ∙ ℕ ∙ ℕ
  ⊢Uℕℕ = ∙ ℕⱼ ⊢Uℕ

  UℕℕU⊢3 : ε » ε ∙ U l ∙ ℕ ∙ ℕ ∙ U l ⊢ var x3 ∷ U l
  UℕℕU⊢3 = var₃ (Uⱼ ⊢Uℕℕ)

  ⊢UℕℕU3 : ε »⊢ ε ∙ U l ∙ ℕ ∙ ℕ ∙ U l ∙ var x3
  ⊢UℕℕU3 = ∙ univ UℕℕU⊢3

  ⊢ℕℕ : ε »⊢ ε ∙ ℕ ∙ ℕ
  ⊢ℕℕ = ∙ ℕⱼ ⊢ℕ

  ⊢ℕℕU : ε »⊢ ε ∙ ℕ ∙ ℕ ∙ U l
  ⊢ℕℕU = ∙ Uⱼ ⊢ℕℕ

------------------------------------------------------------------------
-- A polymorphic identity function

-- A polymorphic identity function with an erased type argument.

id : Term n
id = lam 𝟘 (lam ω (var x0))

-- The polymorphic identity function is well-typed (in a well-formed
-- context).

⊢id : ⊢ Γ → Γ ⊢ id ∷ Π 𝟘 , p ▷ U l ▹ Π ω , q ▷ var x0 ▹ var x1
⊢id ⊢Γ = lamⱼ′ Π-𝟘-ok (ΓU⊢id ⊢Γ)

-- The polymorphic identity function is well-resourced (with respect
-- to the zero usage context).

▸id : 𝟘ᶜ {n} ▸[ 𝟙ᵐ ] id
▸id = lamₘ (lamₘ var)

-- The polymorphic identity function applied to two free variables

id-x1-x0 : Term 2
id-x1-x0 = id ∘⟨ 𝟘 ⟩ var x1 ∘⟨ ω ⟩ var x0

-- The term id-x0-x1 is well-typed (in a certain context)

⊢id-x1-x0 : ε » ε ∙ U l ∙ var x0 ⊢ id-x1-x0 ∷ var x1
⊢id-x1-x0 = (⊢id ⊢Γ ∘ⱼ var ⊢Γ (there here)) ∘ⱼ var ⊢Γ here
  where
  ⊢Γ = ∙ univ (var₀ (Uⱼ εε))

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

-- The term id-ℕ-zero is well-typed (with respect to empty contexts).

⊢id-ℕ-zero : ε » ε ⊢ id-ℕ-zero ∷ ℕ
⊢id-ℕ-zero = (⊢id εε ∘ⱼ ℕⱼ εε) ∘ⱼ zeroⱼ εε

-- The term id-ℕ-zero is well-resourced (with respect to the empty
-- usage context).

▸id-ℕ-zero : ε ▸[ 𝟙ᵐ ] id-ℕ-zero
▸id-ℕ-zero = (▸id ∘ₘ ℕₘ) ∘ₘ zeroₘ

-- The term id-ℕ-zero reduces to zero.

id-ℕ-zero⇒*zero : ε » ε ⊢ id-ℕ-zero ⇒* zero ∷ ℕ
id-ℕ-zero⇒*zero =
  app-subst
    (β-red (ΠΣⱼ (univ (var (⊢U0 ε) (there here))) Π-ω-ok) (U⊢id ε)
       (ℕⱼ εε) PE.refl Π-𝟘-ok)
    (zeroⱼ εε) ⇨
  redMany (β-red (ℕⱼ ⊢ℕ) (var ⊢ℕ here) (zeroⱼ εε) PE.refl Π-ω-ok)

-- The erasure of id-ℕ-zero reduces to zero.

erase-id-ℕ-zero⇒*zero : vs T.⊢ erase str id-ℕ-zero ⇒* T.zero
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

-- The function id₀ is well-typed (with respect to empty contexts).

⊢id₀ : ε » ε ⊢ id₀ ∷ Π 𝟘 , p ▷ ℕ ▹ ℕ
⊢id₀ = lamⱼ′ Π-𝟘-ok (var₀ (ℕⱼ εε))

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
  redMany (β-red (ℕⱼ ⊢ℕ) (var ⊢ℕ here) (zeroⱼ εε) PE.refl Π-𝟘-ok)

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

private

  -- Parts of the implementation of Vec.

  Vec-body₂ : Universe-level → Term (2+ n)
  Vec-body₂ l =
    natrec 𝟘 𝟘 ω
      (U l)
      (Unit s l)
      (Σˢ ω , r ▷ var x3 ▹ var x1)
      (var x0)

  Vec-body₁ : Universe-level → Term (1+ n)
  Vec-body₁ l = lam ω (Vec-body₂ l)

-- Vectors (lists of a fixed length).

Vec : Universe-level → Term 0
Vec l = lam ω (Vec-body₁ l)

-- Vec l is well-resourced.

▸Vec : ε ▸[ 𝟙ᵐ ] Vec l
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
    , (λ _ → ≤ᶜ-refl)
    , ≤ᶜ-refl
    )
    (let x , x-glb = Erasure-nrᵢ-glb ω ω 𝟘
         χ , χ-glb = ∃nrᵢ-GLB→∃nrᵢᶜ-GLB (Erasure-nrᵢ-glb _) 𝟘ᶜ _
         open Tools.Reasoning.PartialOrder ≤ᶜ-poset
    in  x , χ , x-glb , χ-glb , (begin
      ε ∙ ω ∙ ω ≡⟨⟩
      ω ·ᶜ (ε ∙ ω ∙ ω) +ᶜ (ε ∙ headₘ (tailₘ χ) ∙ headₘ χ)               ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (least-elem′ x (x-glb .proj₁ 0))) ⟩
      x ·ᶜ (ε ∙ ω ∙ ω) +ᶜ (ε ∙ headₘ (tailₘ χ) ∙ headₘ χ)               ≈⟨ +ᶜ-congˡ {δ = _ ∙ headₘ (tailₘ χ) ∙ headₘ χ} (ε≈ᶜ ∙ PE.refl ∙ PE.refl) ⟩
      x ·ᶜ (ε ∙ ω ∙ ω) +ᶜ (tailₘ (tailₘ χ) ∙ headₘ (tailₘ χ) ∙ headₘ χ) ≡⟨ PE.cong (x ·ᶜ (ε ∙ ω ∙ ω) +ᶜ_) (PE.cong (_∙ headₘ χ)
                                                                             (headₘ-tailₘ-correct (tailₘ χ))) ⟩
      x ·ᶜ (ε ∙ ω ∙ ω) +ᶜ (tailₘ χ ∙ headₘ χ)                           ≡⟨ PE.cong (x ·ᶜ (ε ∙ ω ∙ ω) +ᶜ_) (headₘ-tailₘ-correct χ) ⟩
      x ·ᶜ (ε ∙ ω ∙ ω) +ᶜ χ       ∎))

private

  -- A typing rule for Vec-body₂.

  ⊢Vec-body₂ : ε » ε ∙ U l ∙ ℕ ⊢ Vec-body₂ l ∷ U l
  ⊢Vec-body₂ =
    natrecⱼ (Unitⱼ ⊢Uℕ Unit-ok)
      (PE.subst (_⊢_∷_ _ _) (PE.cong U ⊔ᵘ-idem) $
       ΠΣⱼ UℕℕU⊢3 (var ⊢UℕℕU3 (there here)) Σˢ-ω-ok)
      (var ⊢Uℕ here)

  -- A typing rule for Vec-body₁.

  ⊢Vec-body₁ : ε » ε ∙ U l ⊢ Vec-body₁ l ∷ Π ω , q ▷ ℕ ▹ U l
  ⊢Vec-body₁ = lamⱼ′ Π-ω-ok ⊢Vec-body₂

-- A typing rule for Vec.

⊢Vec : ε » ε ⊢ Vec l ∷ Π ω , q ▷ U l ▹ Π ω , q ▷ ℕ ▹ U l
⊢Vec = lamⱼ′ Π-ω-ok ⊢Vec-body₁

-- Some lemmas used below.

private module Vec-lemmas (⊢A : Γ ⊢ A ∷ U l) where

  open Tools.Reasoning.PropositionalEquality

  ⊢Γ : ⊢ Γ
  ⊢Γ = wfTerm ⊢A

  »Γ : » Γ .defs
  »Γ = defn-wf ⊢Γ

  Γ⊇ε : WD.» Γ .defs ⊇ ε
  Γ⊇ε = WD.»⊇ε »Γ

  ⊢ΓA : ⊢ Γ »∙ A
  ⊢ΓA = ∙ univ ⊢A

  ⊢ΓAℕ : ⊢ Γ »∙ A »∙ ℕ
  ⊢ΓAℕ = ∙ ℕⱼ ⊢ΓA

  ⊢Γℕ : ⊢ Γ »∙ ℕ
  ⊢Γℕ = ∙ ℕⱼ ⊢Γ

  Γℕ⊢U : Γ »∙ ℕ ⊢ U l
  Γℕ⊢U = Uⱼ ⊢Γℕ

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
    Γ »∙ ℕ »∙ U l ⊢
    wk1 (wk1 (wk1 A)) [ liftSubst (liftSubst (sgSubst t)) ] ∷ U l
  ΓℕU⊢A =
    PE.subst (_ ⊢_∷ _) (wk2≡ _) $
    W.wkTerm (W.stepʷ (W.step W.id) Γℕ⊢U) ⊢A

  ⊢Vec-body₁′ : Γ »∙ U l ⊢ Vec-body₁ l ∷ Π ω , q ▷ ℕ ▹ U l
  ⊢Vec-body₁′ =
    W.wkTerm (W.liftʷ W.wk₀∷⊇ (Uⱼ ⊢Γ)) $
    WD.defn-wkTerm Γ⊇ε ⊢Vec-body₁

  ⊢Vec-body₁″ : Γ »∙ A »∙ U l ⊢ Vec-body₁ l ∷ Π ω , q ▷ ℕ ▹ U l
  ⊢Vec-body₁″ =
    W.wkTerm
      (W.liftʷ (W.step W.wk₀∷⊇) (Uⱼ ⊢ΓA)) $
    WD.defn-wkTerm Γ⊇ε ⊢Vec-body₁

  ⊢Vec-body₂′ :
    Γ »∙ ℕ ⊢ Vec-body₂ l [ liftSubst (consSubst (toSubst wk₀) A) ] ∷ U l
  ⊢Vec-body₂′ = subst-⊢∷
    {σ = liftSubst (consSubst (toSubst wk₀) A)}
    (WD.defn-wkTerm Γ⊇ε ⊢Vec-body₂)
    (⊢ˢʷ∷-⇑′ (U⊢ℕ »Γ) (→⊢ˢʷ∷∙ (⊢ˢʷ∷ε⇔ .proj₂ ⊢Γ) ⊢A))

  ⊢Vec-body₂″ :
    Γ »∙ A »∙ ℕ ⊢
    Vec-body₂ l [ liftSubst (consSubst (toSubst wk₀) (wk1 A)) ] ∷ U l
  ⊢Vec-body₂″ = subst-⊢∷
    {σ = liftSubst (consSubst (toSubst wk₀) (wk1 A))}
    (WD.defn-wkTerm Γ⊇ε ⊢Vec-body₂)
    (⊢ˢʷ∷-⇑′ (U⊢ℕ »Γ) $
     →⊢ˢʷ∷∙ (⊢ˢʷ∷ε⇔ .proj₂ ⊢ΓA) (W.wkTerm₁ (univ ⊢A) ⊢A))

-- A computation rule for Vec.

Vec∘zero⇒* :
  Γ ⊢ A ∷ U l →
  Γ ⊢ wk wk₀ (Vec l) ∘⟨ ω ⟩ A ∘⟨ ω ⟩ zero ⇒* Unit s l ∷ U l
Vec∘zero⇒* {A = A} ⊢A =
  app-subst
    (β-red (syntacticTerm ⊢Vec-body₁′)
       ⊢Vec-body₁′ ⊢A PE.refl Π-ω-ok)
    (zeroⱼ ⊢Γ) ⇨
  (β-red Γℕ⊢U ⊢Vec-body₂′ (zeroⱼ ⊢Γ) PE.refl Π-ω-ok ⇨
   (redMany $
    _⊢_⇒_∷_.natrec-zero (Unitⱼ ⊢Γ Unit-ok) $
    PE.subst (_⊢_∷_ _ _) (PE.cong U ⊔ᵘ-idem) $
    ΠΣⱼ ΓℕU⊢A (var₁ (univ ΓℕU⊢A)) Σˢ-ω-ok))
  where
  open Vec-lemmas ⊢A

-- An equality rule for Vec.

Vec∘suc≡ :
  Γ ⊢ A ∷ U l →
  Γ ⊢ t ∷ ℕ →
  Γ ⊢
    wk wk₀ (Vec l) ∘⟨ ω ⟩ A ∘⟨ ω ⟩ suc t ≡
    Σˢ ω , r ▷ A ▹ (wk wk₀ (Vec l) ∘⟨ ω ⟩ wk1 A ∘⟨ ω ⟩ wk1 t) ∷ U l
Vec∘suc≡ {A} {l} ⊢A ⊢t =
  _⊢_≡_∷_.trans
    (app-cong
       (β-red (syntacticTerm ⊢Vec-body₁′) ⊢Vec-body₁′ ⊢A PE.refl Π-ω-ok)
       (refl (sucⱼ ⊢t))) $
  _⊢_≡_∷_.trans
    (β-red Γℕ⊢U ⊢Vec-body₂′ (sucⱼ ⊢t) PE.refl Π-ω-ok) $
  _⊢_≡_∷_.trans
    (flip (_⊢_≡_∷_.natrec-suc (Unitⱼ ⊢Γ Unit-ok)) ⊢t $
     PE.subst (_⊢_∷_ _ _) (PE.cong U ⊔ᵘ-idem) $
     ΠΣⱼ ΓℕU⊢A (var₁ (univ ΓℕU⊢A)) Σˢ-ω-ok) $
  PE.subst (_⊢_≡_∷_ _ _ _) (PE.cong U ⊔ᵘ-idem) $
  _⊢_≡_∷_.trans
    (sym′ $
     ΠΣ-cong (PE.subst (_ ⊢ _ ≡_∷ _) (≡wk3[][] A) (refl ⊢A))
       (PE.subst₂ (_⊢_≡_∷_ _ _)
          (PE.cong (flip (natrec 𝟘 𝟘 ω (U l) (Unit s l)) _) $
           PE.cong (Σˢ _ , _ ▷_▹ _) $
           wk3[]≡ A)
          PE.refl $
        β-red (Uⱼ ⊢ΓAℕ) ⊢Vec-body₂″ (W.wkTerm₁ (univ ⊢A) ⊢t) PE.refl
          Π-ω-ok)
       Σˢ-ω-ok) $
  sym′ $
  flip (_⊢_≡_∷_.ΠΣ-cong (refl ⊢A)) Σˢ-ω-ok $
  app-cong
    (β-red (syntacticTerm ⊢Vec-body₁″) ⊢Vec-body₁″
       (W.wkTerm₁ (univ ⊢A) ⊢A) PE.refl Π-ω-ok) $
  _⊢_≡_∷_.refl $
  W.wkTerm₁ (univ ⊢A) ⊢t
  where
  open Vec-lemmas ⊢A

private

  -- Parts of the implementation of Non-zero.

  Non-zero-body : Term (1+ n)
  Non-zero-body =
    natrec 𝟘 𝟘 𝟘
      (U 0)
      Empty
      (Unit s 0)
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
    , (λ _ → ≤ᶜ-refl)
    , ≤ᶜ-refl
    )
    (let x , x-glb = Erasure-nrᵢ-glb 𝟘 ω 𝟘
         χ-glb = GLBᶜ-const (λ i → nrᵢᶜ-𝟘ᶜ {i = i})
    in  _ , _ , x-glb , χ-glb , ε ∙ PE.refl)

private

  -- A typing rule for Non-zero-body.

  ⊢Non-zero-body : ε » ε ∙ ℕ ⊢ Non-zero-body ∷ U 0
  ⊢Non-zero-body =
    natrecⱼ (Emptyⱼ ⊢ℕ) (Unitⱼ ⊢ℕℕU Unit-ok) (var ⊢ℕ here)

-- A typing rule for Non-zero.

⊢Non-zero : ε » ε ⊢ Non-zero ∷ Π ω , q ▷ ℕ ▹ U 0
⊢Non-zero = lamⱼ′ Π-ω-ok ⊢Non-zero-body

-- A computation rule for Non-zero.

Non-zero∘zero⇒* :
  ⊢ Γ →
  Γ ⊢ wk wk₀ Non-zero ∘⟨ ω ⟩ zero ⇒* Empty ∷ U 0
Non-zero∘zero⇒* ⊢Γ =
  β-red (Uⱼ ⊢Γℕ)
    (W.wkTerm (W.liftʷ W.wk₀∷⊇ (ℕⱼ ⊢Γ)) $
     WD.defn-wkTerm (WD.»⊇ε (defn-wf ⊢Γ)) ⊢Non-zero-body)
    (zeroⱼ ⊢Γ) PE.refl Π-ω-ok ⇨
  (redMany $
   natrec-zero (Emptyⱼ ⊢Γ) (Unitⱼ (∙ Uⱼ ⊢Γℕ) Unit-ok))
  where
  ⊢Γℕ = ∙ ℕⱼ ⊢Γ

-- Another computation rule for Non-zero.

Non-zero∘suc⇒* :
  Γ ⊢ t ∷ ℕ →
  Γ ⊢ wk wk₀ Non-zero ∘⟨ ω ⟩ suc t ⇒* Unit s 0 ∷ U 0
Non-zero∘suc⇒* ⊢t =
  β-red (Uⱼ ⊢Γℕ)
    (W.wkTerm (W.liftʷ W.wk₀∷⊇ (ℕⱼ ⊢Γ)) $
     WD.defn-wkTerm (WD.»⊇ε (defn-wf ⊢Γ)) ⊢Non-zero-body)
    (sucⱼ ⊢t) PE.refl Π-ω-ok ⇨
  (redMany $
   natrec-suc (Emptyⱼ ⊢Γ) (Unitⱼ (∙ Uⱼ ⊢Γℕ) Unit-ok) ⊢t)
  where
  ⊢Γ  = wfTerm ⊢t
  ⊢Γℕ = ∙ ℕⱼ ⊢Γ

-- A safe head function for vectors.

head : Universe-level → Term 0
head l =
  lam 𝟘 $
  lam ω $
  natrec
    𝟘 ω 𝟘
    (Π ω , q ▷ wk wk₀ (Vec l) ∘⟨ ω ⟩ var x2 ∘⟨ ω ⟩ var x0 ▹
     Π 𝟘 , p ▷ wk wk₀ Non-zero ∘⟨ ω ⟩ var x1 ▹
     var x4)
    (lam ω $ lam 𝟘 $
     emptyrec 𝟘 (var x3) (var x0))
    (lam ω $ lam 𝟘 $ fst ω (var x1))
    (var x0)

-- In the strict setting the extraction of head includes an erased
-- part (loop strict).

erase-strict-head :
  erase strict (head l) PE.≡
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
    erase non-strict (head l) PE.≡
    (T.Term.lam $
     T.natrec
       (T.lam (loop non-strict))
       (T.lam (T.fst (T.var x0)))
       (T.var x0))
  erase-non-strict-head = PE.refl

-- The term head l is well-resourced.

▸head : ε ▸[ 𝟙ᵐ ] head l
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
          ε ∙ ⌜ 𝟘ᵐ? ⌝ ∙ 𝟘 ∙ ⌜ (𝟘ᵐ? ᵐ· 𝟘) ᵐ· ω ⌝  ∙ ⌜ 𝟘ᵐ? ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ⌜⌝-cong (ᵐ·-congʳ ᵐ·-zeroˡ) ∙ PE.refl ⟩
          ε ∙ ⌜ 𝟘ᵐ? ⌝ ∙ 𝟘 ∙ ⌜ 𝟘ᵐ? ᵐ· ω ⌝         ∙ ⌜ 𝟘ᵐ? ⌝ · q  ≤⟨ ≤ᶜ-refl ∙
                                                                  ≤-reflexive (PE.sym (EM.+-identityʳ _)) ∙
                                                                  greatest-elem _ ⟩
          ε ∙ ⌜ 𝟘ᵐ? ⌝ ∙ 𝟘 ∙ ⌜ 𝟘ᵐ? ᵐ· ω ⌝ + 𝟘 ∙ 𝟘            ∎) $
     let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       ε ∙ ⌜ (𝟘ᵐ? ᵐ· ω) ᵐ· ω ⌝ + 𝟘 + ⌜ 𝟘ᵐ? ⌝ ∙ 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ · ω  ≈⟨ ε ∙ EM.+-congʳ (EM.+-congʳ (⌜⌝-cong {m₂ = 𝟘ᵐ? ᵐ· ω} ᵐ·-identityʳ-ω)) ∙
                                                                     PE.refl ∙ lemma ⟩

       ε ∙ ⌜ 𝟘ᵐ? ᵐ· ω ⌝ + 𝟘 + ⌜ 𝟘ᵐ? ⌝ ∙ 𝟘 ∙
         ⌜ 𝟘ᵐ? ᵐ· ω ⌝ + ⌜ (𝟘ᵐ? ᵐ· 𝟘) ᵐ· ω ⌝              ∎)
    (λ ⦃ has-nr ⦄ → ε ∙ ≤-reflexive (PE.sym (nr-𝟘 ⦃ Natrec-mode-Has-nr has-nr ⦄ {p = 𝟘} {r = 𝟘})) ∙ PE.refl)
    ( ≤ᶜ-refl
    , (λ _ → ≤ᶜ-refl)
    , (λ _ → ≤ᶜ-refl)
    , ≤ᶜ-refl
    )
    (let x , x-glb = Erasure-nrᵢ-glb 𝟘 ω 𝟘
         χ-glb = GLBᶜ-const (λ i → nrᵢᶜ-𝟘ᶜ {i = i})
    in  _ , _ , x-glb , χ-glb
          , ε ∙ PE.sym (PE.trans (EM.+-identityʳ _) (EM.·-zeroʳ _)) ∙ PE.refl)
  where
  lemma : ⌜ 𝟘ᵐ? ⌝ · ω PE.≡ ⌜ 𝟘ᵐ? ᵐ· ω ⌝ + ⌜ (𝟘ᵐ? ᵐ· 𝟘) ᵐ· ω ⌝
  lemma = 𝟘ᵐ?-elim
    (λ m → ⌜ m ⌝ · ω PE.≡ ⌜ m ᵐ· ω ⌝ + ⌜ (m ᵐ· 𝟘) ᵐ· ω ⌝)
    PE.refl
    (λ not-ok →
       ω                              ≡⟨⟩
       ⌜ 𝟙ᵐ ⌝ + ⌜ ⌞ 𝟘 ⌟ ·ᵐ ⌞ ω ⌟ ⌝    ≡˘⟨ EM.+-congʳ {x = ⌜ ⌞ 𝟘 ⌟ ·ᵐ ⌞ ω ⌟ ⌝}
                                           (⌜⌝-cong {m₁ = ⌞ ω ⌟} (only-𝟙ᵐ-without-𝟘ᵐ not-ok)) ⟩
       ⌜ ⌞ ω ⌟ ⌝ + ⌜ ⌞ 𝟘 ⌟ ·ᵐ ⌞ ω ⌟ ⌝ ∎)
    where
    open Tools.Reasoning.PropositionalEquality

-- A typing rule for head.

⊢head :
  ε » ε ⊢
  head l ∷
  Π 𝟘 , p ▷ U l ▹
  Π ω , q ▷ ℕ ▹
  Π ω , q ▷ wk wk₀ (Vec l) ∘⟨ ω ⟩ var x1 ∘⟨ ω ⟩ var x0 ▹
  Π 𝟘 , p ▷ wk wk₀ Non-zero ∘⟨ ω ⟩ var x1 ▹
  var x3
⊢head {l} =
  lamⱼ′ Π-𝟘-ok $
  lamⱼ′ Π-ω-ok $
  natrecⱼ
    (lamⱼ′ Π-ω-ok $
     lamⱼ′ Π-𝟘-ok $
     emptyrecⱼ
       (univ (var₃ (univ ⊢Non-zero-zero)))
       (_⊢_∷_.conv (var₀ (univ ⊢Non-zero-zero)) $
        _⊢_≡_.univ $
        subset*Term $
        Non-zero∘zero⇒* ⊢Uℕ∙Vec∙Non-zero))
    (lamⱼ′ Π-ω-ok $
     lamⱼ′ Π-𝟘-ok $
     fstⱼ (univ ⊢Vec-6-4) $
     _⊢_∷_.conv (var₁ (univ ⊢Non-zero-1+2)) $
     _⊢_≡_.univ $
     Vec∘suc≡ ⊢5 (var₃ (univ ⊢Non-zero-1+2)))
    (var ⊢Uℕ here)
  where
  ⊢Vec-2-0 :
    ε » ε ∙ U l ∙ ℕ ∙ ℕ ⊢
    wk wk₀ (Vec l) ∘⟨ ω ⟩ var x2 ∘⟨ ω ⟩ var x0 ∷ U l
  ⊢Vec-2-0 =
    (W.wkTerm (W.stepʷ (W.step (W.step W.id)) (ℕⱼ ⊢Uℕ)) ⊢Vec ∘ⱼ
     var ⊢Uℕℕ (there (there here))) ∘ⱼ
    var ⊢Uℕℕ here

  ⊢Vec-1-0 :
    ε » ε ∙ U l ∙ ℕ ⊢ wk wk₀ (Vec l) ∘⟨ ω ⟩ var x1 ∘⟨ ω ⟩ zero ∷ U l
  ⊢Vec-1-0 = substTerm ⊢Vec-2-0 (zeroⱼ ⊢Uℕ)

  ⊢Non-zero-0 :
    ε » ε ∙ U l ∙ ℕ ∙ ℕ ⊢ wk wk₀ Non-zero ∘⟨ ω ⟩ var x0 ∷ U 0
  ⊢Non-zero-0 =
    W.wkTerm (W.stepʷ (W.step (W.step W.id)) (ℕⱼ ⊢Uℕ)) ⊢Non-zero ∘ⱼ
    var ⊢Uℕℕ here

  ⊢Non-zero-1 :
    ε » ε ∙ U l ∙ ℕ ∙ ℕ ∙ wk wk₀ (Vec l) ∘⟨ ω ⟩ var x2 ∘⟨ ω ⟩ var x0 ⊢
    wk wk₀ Non-zero ∘⟨ ω ⟩ var x1 ∷ U 0
  ⊢Non-zero-1 = W.wkTerm₁ (univ ⊢Vec-2-0) ⊢Non-zero-0

  ⊢Non-zero-zero :
    ε » ε ∙ U l ∙ ℕ ∙ wk wk₀ (Vec l) ∘⟨ ω ⟩ var x1 ∘⟨ ω ⟩ zero ⊢
    wk wk₀ Non-zero ∘⟨ ω ⟩ zero ∷ U 0
  ⊢Non-zero-zero = subst-⊢∷
    ⊢Non-zero-1
    (⊢ˢʷ∷-⇑′ (univ ⊢Vec-2-0) (⊢ˢʷ∷-sgSubst (zeroⱼ ⊢Uℕ)))

  ⊢Uℕ∙Vec∙Non-zero  = ∙ univ ⊢Non-zero-zero
  ⊢Uℕℕ∙Vec∙Non-zero = ∙ univ ⊢Non-zero-1

  Uℕℕ⊢ΠΠ∷U :
    ε » ε ∙ U l ∙ ℕ ∙ ℕ ⊢
    Π ω , q ▷ wk wk₀ (Vec l) ∘⟨ ω ⟩ var x2 ∘⟨ ω ⟩ var x0 ▹
      Π 𝟘 , p ▷ wk wk₀ Non-zero ∘⟨ ω ⟩ var x1 ▹ var x4 ∷
    U l
  Uℕℕ⊢ΠΠ∷U =
    PE.subst (_⊢_∷_ _ _)
      (PE.cong U $
       l ⊔ᵘ (0 ⊔ᵘ l)  ≡⟨ PE.cong (l ⊔ᵘ_) ⊔ᵘ-identityˡ ⟩
       l ⊔ᵘ l         ≡⟨ ⊔ᵘ-idem ⟩
       l              ∎) $
    ΠΣⱼ ⊢Vec-2-0
      (ΠΣⱼ ⊢Non-zero-1
         (var ⊢Uℕℕ∙Vec∙Non-zero
            (there (there (there (there here)))))
         Π-𝟘-ok)
      Π-ω-ok
    where
    open Tools.Reasoning.PropositionalEquality

  Uℕℕ∙ΠΠ =
    ε ∙ U l ∙ ℕ ∙ ℕ ∙
    Π ω , q ▷ wk wk₀ (Vec l) ∘⟨ ω ⟩ var x2 ∘⟨ ω ⟩ var x0 ▹
      Π 𝟘 , p ▷ wk wk₀ Non-zero ∘⟨ ω ⟩ var x1 ▹ var x4

  ⊢Vec-3-1+1 :
    ε » Uℕℕ∙ΠΠ ⊢ wk wk₀ (Vec l) ∘⟨ ω ⟩ var x3 ∘⟨ ω ⟩ suc (var x1) ∷ U l
  ⊢Vec-3-1+1 = subst-⊢∷
    ⊢Vec-2-0
    (⊢ˢʷ∷-wk1Subst (univ Uℕℕ⊢ΠΠ∷U) $
     ⊢ˢʷ∷-[][]↑ {k = 1} (sucⱼ (var ⊢Uℕℕ here)))

  Uℕℕ∙ΠΠ∙Vec =
    Uℕℕ∙ΠΠ ∙ wk wk₀ (Vec l) ∘⟨ ω ⟩ var x3 ∘⟨ ω ⟩ suc (var x1)

  ⊢Non-zero-1+2 :
    ε » Uℕℕ∙ΠΠ∙Vec ⊢ wk wk₀ Non-zero ∘⟨ ω ⟩ suc (var x2) ∷ U 0
  ⊢Non-zero-1+2 = subst-⊢∷
    ⊢Non-zero-0
    (⊢ˢʷ∷-wk1Subst (univ ⊢Vec-3-1+1) $
     ⊢ˢʷ∷-wk1Subst (univ Uℕℕ⊢ΠΠ∷U) $
     ⊢ˢʷ∷-[][]↑ {k = 1} (sucⱼ (var ⊢Uℕℕ here)))

  Uℕℕ∙ΠΠ∙Vec∙Non-zero = Uℕℕ∙ΠΠ∙Vec ∙ wk wk₀ Non-zero ∘⟨ ω ⟩ suc (var x2)

  ⊢5 : ε » Uℕℕ∙ΠΠ∙Vec∙Non-zero ⊢ var x5 ∷ U l
  ⊢5 = var₅ (univ ⊢Non-zero-1+2)

  Uℕℕ∙ΠΠ∙Vec∙Non-zero∙5 = Uℕℕ∙ΠΠ∙Vec∙Non-zero ∙ var x5

  ⊢Vec-6-4 :
    ε » Uℕℕ∙ΠΠ∙Vec∙Non-zero∙5 ⊢
    wk wk₀ (Vec l) ∘⟨ ω ⟩ var x6 ∘⟨ ω ⟩ var x4 ∷ U l
  ⊢Vec-6-4 = W.wkTerm
    (W.stepʷ (W.step (W.step (W.step W.id))) (univ ⊢5))
    ⊢Vec-2-0

-- A concrete vector which contains a single natural number.

[0] : Term 0
[0] = prodˢ ω zero (star s 0)

-- [0] is well-resourced.

▸[0] : ε ▸[ 𝟙ᵐ ] [0]
▸[0] = prodˢₘ zeroₘ starₘ

-- [0] is in η-long normal form.

[0]-normal : ε » ε ⊢nf [0] ∷ Vec 0 ∘⟨ ω ⟩ ℕ ∘⟨ ω ⟩ suc zero
[0]-normal =
  _⊢nf_∷_.convₙ
    (prodₙ (Unitⱼ ⊢ℕ Unit-ok) (zeroₙ εε) (starₙ εε Unit-ok) Σˢ-ω-ok) $
  _⊢_≡_.univ $
  sym′ $
  _⊢_≡_∷_.trans (Vec∘suc≡ (ℕⱼ εε) (zeroⱼ εε)) $
  ΠΣ-cong (refl (ℕⱼ εε)) (subset*Term (Vec∘zero⇒* (ℕⱼ (∙ ℕⱼ εε))))
    Σˢ-ω-ok

-- A typing rule for [0].

⊢[0] : ε » ε ⊢ [0] ∷ Vec 0 ∘⟨ ω ⟩ ℕ ∘⟨ ω ⟩ suc zero
⊢[0] = ⊢nf∷→⊢∷ [0]-normal

-- An application of head 0 to [0] and some other arguments.

head-[0] : Term 0
head-[0] = head 0 ∘⟨ 𝟘 ⟩ ℕ ∘⟨ ω ⟩ suc zero ∘⟨ ω ⟩ [0] ∘⟨ 𝟘 ⟩ star s 0

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

⊢head-[0] : ε » ε ⊢ head-[0] ∷ ℕ
⊢head-[0] =
  (((⊢head ∘ⱼ ℕⱼ εε) ∘ⱼ sucⱼ (zeroⱼ εε)) ∘ⱼ ⊢[0]) ∘ⱼ
  conv (starⱼ εε Unit-ok)
    (_⊢_≡_.univ $
     sym′ $
     subset*Term (Non-zero∘suc⇒* (zeroⱼ εε)))

-- The erasure of head-[0] reduces to T.zero.

erase-head-[0]⇒*zero : vs T.⊢ erase str head-[0] ⇒* T.zero
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

head-[0]⇒*zero : ε » ε ⊢ head-[0] ⇒* zero ∷ ℕ
head-[0]⇒*zero =
  case Soundness₀.soundness-ℕ (λ ())
         T.non-strict ⊢head-[0] ▸head-[0] of λ where
    (0 , head-[0]⇒*zero , _) →
      S.⇒ˢ*zero∷ℕ→⇒*zero ⦃ ok = ε ⦄ head-[0]⇒*zero
    (1+ _ , _ , erase-head-[0]⇒*suc) →
      case TP.red*Det (erase-head-[0]⇒*zero {str = non-strict})
              (S.⇒ˢ*suc→⇒*suc erase-head-[0]⇒*suc .proj₂)
      of λ where
        (inj₁ zero⇒*suc) → case TP.zero-noRed zero⇒*suc of λ ()
        (inj₂ suc⇒*zero) → case TP.suc-noRed  suc⇒*zero of λ ()
