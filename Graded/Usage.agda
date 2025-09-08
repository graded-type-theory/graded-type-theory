------------------------------------------------------------------------
-- The usage relation.
------------------------------------------------------------------------

import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Usage
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  (R : Usage-restrictions 𝕄)
  where

open Modality 𝕄
open Usage-restrictions R

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Mode 𝕄
open import Graded.Usage.Erased-matches
open import Graded.Usage.Restrictions.Instance R
open import Graded.Usage.Restrictions.Natrec 𝕄
open import Definition.Untyped M

open import Tools.Bool using (T; true; false)
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation

infix 10 _▸[_]_

private
  variable
    n l : Nat
    p q r : M
    γ γ′ γ₁ γ₂ γ₃ γ₄ γ₅ γ₆ δ η θ χ : Conₘ n
    A B F G : Term n
    t u v w z : Term n
    x : Fin n
    m m′ : Mode
    b : BinderMode
    s : Strength
    em : Erased-matches
    nm : Natrec-mode

-- A view used in the implementation of ⌈_⌉.

data ⌈⌉-view (A : Set a) (em : Erased-matches) : Set a where
  is-all      : em ≡ all → ⌈⌉-view A em
  is-some-yes : em ≡ some → A → ⌈⌉-view A em
  is-other    : em ≤ᵉᵐ some → (em ≡ some → ¬ A) → ⌈⌉-view A em

opaque

  -- The view ⌈⌉-view A em is inhabited if A is decided.

  ⌈⌉-view-inhabited : {A : Set a} → Dec A → ∀ em → ⌈⌉-view A em
  ⌈⌉-view-inhabited _       all  = is-all refl
  ⌈⌉-view-inhabited (yes p) some = is-some-yes refl p
  ⌈⌉-view-inhabited (no p)  some = is-other _ (λ _ → p)
  ⌈⌉-view-inhabited _       none = is-other _ (λ ())

opaque

  -- An instantiation of ⌈⌉-view-inhabited used for J.

  J-view : ∀ p q m → ⌈⌉-view (p ≡ 𝟘 × q ≡ 𝟘) (erased-matches-for-J m)
  J-view p q _ = ⌈⌉-view-inhabited (is-𝟘? p ×-dec is-𝟘? q) _

opaque

  -- An instantiation of ⌈⌉-view-inhabited used for K.

  K-view : ∀ p m → ⌈⌉-view (p ≡ 𝟘) (erased-matches-for-K m)
  K-view p _ = ⌈⌉-view-inhabited (is-𝟘? p) _

-- Modality context inference for natrec.

⌈⌉-natrec :
  ⦃ ok : Natrec-mode-supports-usage-inference nm ⦄ →
  (p r : M) (γ δ η : Conₘ n) → Conₘ n
⌈⌉-natrec ⦃ ok = Nr ⦃ (has-nr) ⦄ ⦄ p r γ δ η = nrᶜ ⦃ has-nr ⦄ p r γ δ η
⌈⌉-natrec ⦃ ok = No-nr-glb has-GLB ⦄ p r γ δ η =
  let x , _ = has-GLB r 𝟙 p
      χ , _ = nrᵢᶜ-has-GLBᶜ has-GLB r γ δ
  in  x ·ᶜ η +ᶜ χ

-- Modality context inference (for modalities with nr functions).

infix 50 ⌈_⌉

mutual
  ⌈_⌉ :
    ⦃ ok : Natrec-mode-supports-usage-inference natrec-mode ⦄ →
    Term n → Mode → Conₘ n
  ⌈ var x ⌉ m = 𝟘ᶜ , x ≔ ⌜ m ⌝
  ⌈ U _ ⌉ _ = 𝟘ᶜ
  ⌈ ΠΣ⟨ _ ⟩ p , q ▷ F ▹ G ⌉ m = ⌈ F ⌉ (m ᵐ· p) +ᶜ tailₘ (⌈ G ⌉ m)
  ⌈ lam p t ⌉ m = tailₘ (⌈ t ⌉ m)
  ⌈ t ∘⟨ p ⟩ u ⌉ m = ⌈ t ⌉ m +ᶜ p ·ᶜ ⌈ u ⌉ (m ᵐ· p)
  ⌈ prod 𝕨 p t u ⌉ m = p ·ᶜ ⌈ t ⌉ (m ᵐ· p) +ᶜ ⌈ u ⌉ m
  ⌈ prod 𝕤 p t u ⌉ m = p ·ᶜ ⌈ t ⌉ (m ᵐ· p) ∧ᶜ ⌈ u ⌉ m
  ⌈ fst p t ⌉ m = ⌈ t ⌉ m
  ⌈ snd p t ⌉ m = ⌈ t ⌉ m
  ⌈ prodrec r _ _ _ t u ⌉ m =
    r ·ᶜ ⌈ t ⌉ (m ᵐ· r) +ᶜ tailₘ (tailₘ (⌈ u ⌉ m))
  ⌈ ℕ ⌉ _ = 𝟘ᶜ
  ⌈ zero ⌉ _ = 𝟘ᶜ
  ⌈ suc t ⌉ m = ⌈ t ⌉ m
  ⌈ natrec p _ r _ z s n ⌉ m =
    ⌈⌉-natrec p r (⌈ z ⌉ m) (tailₘ (tailₘ (⌈ s ⌉ m))) (⌈ n ⌉ m)
  ⌈ Unit! ⌉ _ = 𝟘ᶜ
  ⌈ star! ⌉ _ = 𝟘ᶜ
  ⌈ unitrec _ p q A t u ⌉ m = p ·ᶜ ⌈ t ⌉ (m ᵐ· p) +ᶜ ⌈ u ⌉ m
  ⌈ Empty ⌉ _ = 𝟘ᶜ
  ⌈ emptyrec p _ t ⌉ m = p ·ᶜ ⌈ t ⌉ (m ᵐ· p)
  ⌈ Id _ t u ⌉ m = case Id-erased? of λ where
    (yes _) → 𝟘ᶜ
    (no _)  → ⌈ t ⌉ m +ᶜ ⌈ u ⌉ m
  ⌈ rfl ⌉ _ = 𝟘ᶜ
  ⌈ J p q _ t B u v w ⌉ m with J-view p q m
  … | is-all _        = ⌈ u ⌉ m
  … | is-some-yes _ _ = ω ·ᶜ (tailₘ (tailₘ (⌈ B ⌉ m)) +ᶜ ⌈ u ⌉ m)
  … | is-other _ _    =
        ω ·ᶜ
        (⌈ t ⌉ m +ᶜ tailₘ (tailₘ (⌈ B ⌉ m)) +ᶜ
         ⌈ u ⌉ m +ᶜ ⌈ v ⌉ m +ᶜ ⌈ w ⌉ m)
  ⌈ K p _ t B u v ⌉ m with K-view p m
  … | is-all _        = ⌈ u ⌉ m
  … | is-some-yes _ _ = ω ·ᶜ (tailₘ (⌈ B ⌉ m) +ᶜ ⌈ u ⌉ m)
  … | is-other _ _    =
        ω ·ᶜ (⌈ t ⌉ m +ᶜ tailₘ (⌈ B ⌉ m) +ᶜ ⌈ u ⌉ m +ᶜ ⌈ v ⌉ m)
  ⌈ []-cong _ _ _ _ _ ⌉ _ = 𝟘ᶜ

-- Well-usage of variables
data _◂_∈_  : (x : Fin n) (p : M) (γ : Conₘ n) → Set a where
  here  :                       x0 ◂ p ∈ γ ∙ p
  there : (h : x ◂ p ∈ γ) → (x +1) ◂ p ∈ γ ∙ q

-- Well-usage relation for terms.
--
-- The definition is partly based on Robert Atkey's "Syntax and
-- Semantics of Quantitative Type Theory".
--
-- There are several sets of usage rules for Id, J and K. One (where
-- Id-erased is not inhabited and erased-matches-for-J and
-- erased-matches-for-K are both equal to none) is based on the work
-- of Abel, Danielsson and Vezzosi on adding support for erasure to
-- cubical type theory, and is similar to the following Agda code:
--
--   {-# OPTIONS --erasure --safe --cubical-compatible #-}
--
--   data Id {@0 a} {@0 A : Set a} (x : A) : A → Set a where
--     refl : Id x x
--
--   J :
--     ∀ {@0 a} {p} {@0 A : Set a} {x : A}
--     (P : ∀ {y} → Id x y → Set p) →
--     P (refl {x = x}) →
--     {y : A} (x≡y : Id x y) → P x≡y
--   J _ r refl = r
--
-- Note that (at the time of writing) Agda rejects the code if one of
-- the non-erased arguments is made erased. In particular, "P" cannot
-- be made erased.
--
-- Another set of usage rules (where Id-erased is inhabited and
-- erased-matches-for-J and erased-matches-for-K are both equal to
-- all) is based on the following Agda code:
--
--   {-# OPTIONS --erasure --safe --with-K #-}
--
--   open import Agda.Builtin.Sigma
--
--   data Id {@0 a} {@0 A : Set a} (@0 x : A) : @0 A → Set a where
--     refl : Id x x
--
--   J :
--     ∀ {@0 a p} {@0 A : Set a} {@0 x : A}
--     (@0 P : ∀ {y} → Id x y → Set p) →
--     P (refl {x = x}) →
--     {@0 y : A} (@0 x≡y : Id x y) → P x≡y
--   J _ r refl = r
--
--   -- One variant of the K rule.
--
--   K :
--     ∀ {@0 a p} {@0 A : Set a} {@0 x : A}
--     (@0 P : Id x x → Set p) →
--     P refl →
--     (@0 x≡x : Id x x) → P x≡x
--   K _ r refl = r
--
--   -- Another variant of the K rule, which can be defined using the
--   -- first variant.
--
--   K′ :
--     ∀ {@0 a p} {@0 A : Set a}
--     (@0 P : ∀ x → Id x x → Set p) →
--     (∀ x → P x refl) →
--     (x : A) (@0 x≡x : Id x x) → P x x≡x
--   K′ P r x x≡x = K (P x) (r x) x≡x
--
--   _ :
--     ∀ {@0 a p} {@0 A : Set a}
--     (@0 P : ∀ x → Id x x → Set p)
--     (r : ∀ x → P x refl)
--     (x : A) →
--     Id (K′ P r x refl) (r x)
--   _ = λ _ _ _ → refl
--
--   -- The first variant of the K rule can also be defined using the
--   -- second (and J).
--
--   K″ :
--     ∀ {@0 a p} {@0 A : Set a} {@0 x : A}
--     (@0 P : Id x x → Set p) →
--     P refl →
--     (@0 x≡x : Id x x) → P x≡x
--   K″ P r x≡x =
--     J (λ {y = eq} _ → P refl → P eq)
--       (λ p → p)
--       (K′ (λ x (x≡x : Id x x) → Id refl x≡x) (λ _ → refl) _ x≡x)
--       r
--
--   _ :
--     ∀ {@0 a p} {@0 A : Set a} {@0 x : A}
--     (@0 P : Id x x → Set p)
--     (r : P refl)
--     (@0 x≡x : Id x x) →
--     Id (K″ P r refl) r
--   _ = λ _ _ _ → refl
--
-- Note that the K rule is active in the Agda code. However, the
-- variant of the J rule with an erased motive P can be considered
-- also in the absence of the K rule.
--
-- Yet another set of usage rules (where erased-matches-for-J and
-- erased-matches-for-K are both equal to "some") provides an
-- alternative to []-cong. If 𝟘ᵐ is allowed, then the given usage
-- rules for J more or less give the power of []-cong plus the "none"
-- variants of the usage rules for J:
--
-- * Graded.Box-cong.[]-cong-J is a variant of []-cong defined
--   using J. This term former satisfies typing rules that are similar
--   to those for []-cong (see Graded.Box-cong), and if the "some"
--   variants of the usage rules for J are used, then the term former
--   satisfies a usage rule that is similar to []-congₘ (see
--   Graded.Box-cong.▸[]-cong-J).
--
-- * Definition.Untyped.Erased.Jᵉ is a variant of J that is defined
--   using []-cong. If []-cong is allowed (which at the time of
--   writing implies that the modality is non-trivial, see
--   Definition.Typed.Restrictions.Type-restrictions.[]-cong→¬Trivial),
--   then this term former satisfies typing rules that are similar to
--   those for J (see Definition.Typed.Properties.Admissible.Erased).
--   Furthermore the term former satisfies a usage rule that is
--   similar to J₀ₘ₁ if 𝟘ᵐ is allowed (see
--   Graded.Derived.Erased.Usage.▸Jᵉ).
--
-- The "some" variants of the usage rules for K were included to
-- mirror the rules for J, but if the K rule is available, then it
-- might be a better idea to use the "all" rules.
data _▸[_]_ {n : Nat} : (γ : Conₘ n) → Mode → Term n → Set a where
  sub       : γ ▸[ m ] t
            → δ ≤ᶜ γ
            → δ ▸[ m ] t

  var       : (𝟘ᶜ , x ≔ ⌜ m ⌝) ▸[ m ] var x

  Uₘ        : 𝟘ᶜ ▸[ m ] U l

  Emptyₘ    : 𝟘ᶜ ▸[ m ] Empty

  emptyrecₘ : γ ▸[ m ᵐ· p ] t
            → δ ▸[ 𝟘ᵐ? ] A
            → Emptyrec-allowed m p
            → p ·ᶜ γ ▸[ m ] emptyrec p A t

  Unitₘ     : 𝟘ᶜ ▸[ m ] Unit s l

  -- If strong unit types are not allowed to be used as sinks, then γ
  -- must be 𝟘ᶜ.
  starˢₘ    : (¬ Starˢ-sink → 𝟘ᶜ ≈ᶜ γ)
            → ⌜ m ⌝ ·ᶜ γ ▸[ m ] starˢ l

  starʷₘ    : 𝟘ᶜ ▸[ m ] starʷ l

  unitrecₘ : γ ▸[ m ᵐ· p ] t
           → δ ▸[ m ] u
           → η ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A
           → Unitrec-allowed m p q
           → p ·ᶜ γ +ᶜ δ ▸[ m ] unitrec l p q A t u

  ΠΣₘ       : γ ▸[ m ᵐ· p ] F
            → δ ∙ ⌜ m ⌝ · q ▸[ m ] G
            → γ +ᶜ δ ▸[ m ] ΠΣ⟨ b ⟩ p , q ▷ F ▹ G

  lamₘ      : γ ∙ ⌜ m ⌝ · p ▸[ m ] t
            → γ ▸[ m ] lam p t

  _∘ₘ_      : γ ▸[ m ] t
            → δ ▸[ m ᵐ· p ] u
            → γ +ᶜ p ·ᶜ δ ▸[ m ] t ∘⟨ p ⟩ u

  prodˢₘ   : γ ▸[ m ᵐ· p ] t
           → δ ▸[ m ] u
           → p ·ᶜ γ ∧ᶜ δ ▸[ m ] prodˢ p t u

  -- Note that either p ≤ 𝟙 or m′ ≡ 𝟘ᵐ
  fstₘ      : ∀ m
            → γ ▸[ m ᵐ· p ] t
            → m ᵐ· p ≡ m′
            → (m′ ≡ 𝟙ᵐ → p ≤ 𝟙)
            → γ ▸[ m′ ] fst p t

  sndₘ      : γ ▸[ m ] t
            → γ ▸[ m ] snd p t

  prodʷₘ    : γ ▸[ m ᵐ· p ] t
            → δ ▸[ m ] u
            → p ·ᶜ γ +ᶜ δ ▸[ m ] prodʷ p t u

  prodrecₘ  : γ ▸[ m ᵐ· r ] t
            → δ ∙ ⌜ m ⌝ · r · p ∙ ⌜ m ⌝ · r ▸[ m ] u
            → η ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A
            → Prodrec-allowed m r p q
            → r ·ᶜ γ +ᶜ δ ▸[ m ] prodrec r p q A t u

  ℕₘ        : 𝟘ᶜ ▸[ m ] ℕ

  zeroₘ     : 𝟘ᶜ ▸[ m ] zero

  sucₘ      : γ ▸[ m ] t
            → γ ▸[ m ] suc t

  -- A usage rule for natrec which applies if a dedicated nr function
  -- ("natrec usage function") is available.
  natrecₘ   : ∀ {s n} ⦃ has-nr : Nr-available ⦄
            → γ ▸[ m ] z
            → δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s
            → η ▸[ m ] n
            → θ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A
            → nrᶜ p r γ δ η ▸[ m ] natrec p q r A z s n

  -- A usage rule for natrec which applies if a dedicated nr function
  -- is not available.
  --
  -- There are four inequality assumptions:
  --
  -- * Two are always required to hold. These assumptions are (at the
  --   time of writing) for instance used to prove the natrec-zero and
  --   natrec-suc cases of the subject reduction lemma
  --   Graded.Reduction.usagePresTerm.
  --
  -- * The assumption χ ≤ᶜ η is only required to hold if the
  --   modality's zero is well-behaved. This assumption is (at the
  --   time of writing) used, together with the two unrestricted
  --   assumptions, to prove the fundamental lemma
  --   Graded.Erasure.LogicalRelation.Fundamental.Fundamental.fundamental
  --   (among other things). The statement of this lemma includes the
  --   assumption that the modality's zero is well-behaved.
  --
  -- * The assumption χ ≤ᶜ δ is only required to hold if 𝟘ᵐ is
  --   allowed. This assumption is used to prove the substitution
  --   lemma Graded.Substitution.Properties.substₘ-lemma.
  --
  -- Note that this rule may not always be appropriate. See
  -- Graded.Modality.Instances.Linearity.Examples.Bad.No-nr,
  -- Graded.Modality.Instances.Affine.Examples.Bad.No-nr and
  -- Graded.Modality.Instances.Linear-or-affine.Examples.Bad.No-nr
  -- for some examples.
  natrec-no-nrₘ :
            ∀ {n s} ⦃ no-nr : Nr-not-available ⦄
            → γ ▸[ m ] z
            → δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s
            → η ▸[ m ] n
            → θ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A
            → χ ≤ᶜ γ
            → (T 𝟘ᵐ-allowed →
               χ ≤ᶜ δ)
            → (⦃ 𝟘-well-behaved :
                   Has-well-behaved-zero semiring-with-meet ⦄ →
               χ ≤ᶜ η)
            → χ ≤ᶜ δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ
            → χ ▸[ m ] natrec p q r A z s n

  -- Another usage rule for natrec which applies if a dedicated nr function
  -- is not available.
  --
  -- The usage count of natrec is assumed to consist of one part representing
  -- the usage contributions of the natural number and one part representing
  -- the usage contributions of the zero and successor cases.
  --
  -- The contribution of the natural number argument is given by the greatest
  -- lower bound of the sequence nrᵢ r 𝟙 p. The elements of the sequence
  -- represents the usage count of the natural number for a given number of
  -- unfoldings.
  -- When the natural number argument is zero the natural number argument is used
  -- once (for matching). This is represented by nr₀ r 𝟙 p ≡ 𝟙. When the natural
  -- number argument is suc n, the argument is used p times (by the successor case)
  -- plus an additional number of times in the recursive call. Assuming a
  -- suitable substitution lemma, the total usage counts become p + r · nrᵢ r 𝟙 p
  -- where nrᵢ r 𝟙 p is the usage count of the recursive call (being unfolded
  -- one time less). The greatest lower bound of all these usage counts is
  -- then compatible with all possible unfoldings (via subsumption)
  --
  -- The contribution of the zero and successor cases is similarly given by
  -- the greatest lower bound of the sequence nrᵢᶜ r γ δ. As before, each
  -- element of the sequence corresponds to the total usage count for a given
  -- number of unfoldings.

  natrec-no-nr-glbₘ :
           ∀ {n s x} ⦃ no-nr : Nr-not-available-GLB ⦄
           → γ ▸[ m ] z
           → δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s
           → η ▸[ m ] n
           → θ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A
           → Greatest-lower-bound x (nrᵢ r 𝟙 p)
           → Greatest-lower-boundᶜ χ (nrᵢᶜ r γ δ)
           → x ·ᶜ η +ᶜ χ ▸[ m ] natrec p q r A z s n

  Idₘ       : ¬ Id-erased
            → γ ▸[ 𝟘ᵐ? ] A
            → δ ▸[ m ] t
            → η ▸[ m ] u
            → δ +ᶜ η ▸[ m ] Id A t u

  Id₀ₘ      : Id-erased
            → γ ▸[ 𝟘ᵐ? ] A
            → δ ▸[ 𝟘ᵐ? ] t
            → η ▸[ 𝟘ᵐ? ] u
            → 𝟘ᶜ ▸[ m ] Id A t u

  rflₘ      : 𝟘ᶜ ▸[ m ] rfl

  Jₘ        : erased-matches-for-J m ≤ᵉᵐ some
            → (erased-matches-for-J m ≡ some → ¬ (p ≡ 𝟘 × q ≡ 𝟘))
            → γ₁ ▸[ 𝟘ᵐ? ] A
            → γ₂ ▸[ m ] t
            → γ₃ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · q ▸[ m ] B
            → γ₄ ▸[ m ] u
            → γ₅ ▸[ m ] v
            → γ₆ ▸[ m ] w
            → ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆) ▸[ m ] J p q A t B u v w

  J₀ₘ₁      : erased-matches-for-J m ≡ some
            → p ≡ 𝟘
            → q ≡ 𝟘
            → γ₁ ▸[ 𝟘ᵐ? ] A
            → γ₂ ▸[ 𝟘ᵐ? ] t
            → γ₃ ∙ 𝟘 ∙ 𝟘 ▸[ m ] B
            → γ₄ ▸[ m ] u
            → γ₅ ▸[ 𝟘ᵐ? ] v
            → γ₆ ▸[ 𝟘ᵐ? ] w
            → ω ·ᶜ (γ₃ +ᶜ γ₄) ▸[ m ] J p q A t B u v w

  J₀ₘ₂      : erased-matches-for-J m ≡ all
            → γ₁ ▸[ 𝟘ᵐ? ] A
            → γ₂ ▸[ 𝟘ᵐ? ] t
            → γ₃ ∙ ⌜ 𝟘ᵐ? ⌝ · p ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] B
            → γ₄ ▸[ m ] u
            → γ₅ ▸[ 𝟘ᵐ? ] v
            → γ₆ ▸[ 𝟘ᵐ? ] w
            → γ₄ ▸[ m ] J p q A t B u v w

  Kₘ        : erased-matches-for-K m ≤ᵉᵐ some
            → (erased-matches-for-K m ≡ some → p ≢ 𝟘)
            → γ₁ ▸[ 𝟘ᵐ? ] A
            → γ₂ ▸[ m ] t
            → γ₃ ∙ ⌜ m ⌝ · p ▸[ m ] B
            → γ₄ ▸[ m ] u
            → γ₅ ▸[ m ] v
            → ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅) ▸[ m ] K p A t B u v

  K₀ₘ₁      : erased-matches-for-K m ≡ some
            → p ≡ 𝟘
            → γ₁ ▸[ 𝟘ᵐ? ] A
            → γ₂ ▸[ 𝟘ᵐ? ] t
            → γ₃ ∙ 𝟘 ▸[ m ] B
            → γ₄ ▸[ m ] u
            → γ₅ ▸[ 𝟘ᵐ? ] v
            → ω ·ᶜ (γ₃ +ᶜ γ₄) ▸[ m ] K p A t B u v

  K₀ₘ₂      : erased-matches-for-K m ≡ all
            → γ₁ ▸[ 𝟘ᵐ? ] A
            → γ₂ ▸[ 𝟘ᵐ? ] t
            → γ₃ ∙ ⌜ 𝟘ᵐ? ⌝ · p ▸[ 𝟘ᵐ? ] B
            → γ₄ ▸[ m ] u
            → γ₅ ▸[ 𝟘ᵐ? ] v
            → γ₄ ▸[ m ] K p A t B u v

  []-congₘ  : γ₁ ▸[ 𝟘ᵐ? ] A
            → γ₂ ▸[ 𝟘ᵐ? ] t
            → γ₃ ▸[ 𝟘ᵐ? ] u
            → γ₄ ▸[ 𝟘ᵐ? ] v
            → []-cong-allowed-mode s m
            → 𝟘ᶜ ▸[ m ] []-cong s A t u v

-- Usage with implicit mode 𝟙ᵐ

_▸_ : (γ : Conₘ n) (t : Term n) → Set a
γ ▸ t = γ ▸[ 𝟙ᵐ ] t

opaque

  -- A variant of sub.

  sub-≈ᶜ : γ ▸[ m ] t → δ ≈ᶜ γ → δ ▸[ m ] t
  sub-≈ᶜ ▸t δ≈γ = sub ▸t (≤ᶜ-reflexive δ≈γ)

opaque

  -- A variant of starˢₘ and starʷₘ.

  starₘ : 𝟘ᶜ {n = n} ▸[ m ] star s l
  starₘ {s = 𝕤} = sub-≈ᶜ (starˢₘ λ _ → ≈ᶜ-refl) (≈ᶜ-sym (·ᶜ-zeroʳ _))
  starₘ {s = 𝕨} = starʷₘ
