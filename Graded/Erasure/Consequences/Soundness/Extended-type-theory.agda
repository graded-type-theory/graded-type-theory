------------------------------------------------------------------------
-- Soundness via extended type theories
------------------------------------------------------------------------

import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions

module Graded.Erasure.Consequences.Soundness.Extended-type-theory
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions TR

import Definition.Typed
open Definition.Typed TR
import Definition.Typed.Properties
import Definition.Typed.Substitution

open import Definition.Untyped M
open import Definition.Untyped.Identity 𝕄
open import Definition.Untyped.Properties M

open import Graded.Context 𝕄
open import Graded.Derived.Identity UR
import Graded.Erasure.Consequences.Soundness
open import Graded.Erasure.Extraction 𝕄
open import Graded.Erasure.Extraction.Properties 𝕄
import Graded.Erasure.SucRed
open Graded.Erasure.SucRed TR
open import Graded.Erasure.Target as T using (Strictness)
import Graded.Erasure.Target.Properties as TP
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄
import Graded.Modify-box-cong-or-J
open import Graded.Modify-box-cong-or-J.Configuration TR UR
open import Graded.Restrictions 𝕄
import Graded.Usage
open Graded.Usage 𝕄 UR
import Graded.Substitution.Properties

open import Tools.Bool
open import Tools.Fin
open import Tools.Function
open import Tools.Level
open import Tools.List as L using (List)
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation

private variable
  k l n     : Nat
  ∇         : DCon _ _
  Δ Η       : Con _ _
  Γ         : Cons _ _
  A t       : Term _
  l₁ l₂     : Universe-level
  γ         : Conₘ _
  m         : Mode
  p p′ q q′ : M
  str       : Strictness

------------------------------------------------------------------------
-- Extended type theories

-- Extended type theories, used to prove soundness of erasure.
--
-- There are counterexamples to soundness of erasure for open terms in
-- the presence of (certain) erased matches, see
-- Graded.Erasure.Consequences.Soundness. This type is an attempt to
-- work around this by instead using an extended type theory which
-- allows the assumptions in the variable context to be implemented.
-- The following assumptions are made about the extended theories:
--
-- * Soundness of erasure for closed terms of type ℕ holds (expressed
--   using judgemental equality rather than reduction).
--
-- * There are substitution lemmas for typing and usage, and a lemma
--   about how (roughly) extraction is not affected if anything is
--   substituted for erasable variables.
--
-- * There is a type- and usage-preserving translation from the basic
--   theory to the extended one. Extraction is not affected by
--   translation, and the application of a substitution to the
--   translation of ℕ is equal to the translation of ℕ.
--
-- Given those assumptions one can prove a soundness theorem for
-- *open* terms for the basic theory, assuming that the (translation
-- of the) context is inhabited in the extended theory (with a mild
-- assumption related to usage). In the statement of the soundness
-- theorem the extended theory is used to define what it means for
-- "the numeral" to be "correct".
--
-- Perhaps it is possible to construct an instance that uses cubical
-- type theory, and to use that to obtain a soundness result that
-- applies to terms that use []-cong and "postulated" erased
-- univalence. At the time of writing there is no such instance in
-- this module, but a similar exercise has been performed using
-- extensional type theory and postulated function extensionality, see
-- soundness-ℕ-with-function-extensionality and
-- soundness-ℕ-with-function-extensionality-𝟘ᵐ below.

record Extended-type-theory : Set (lsuc a) where
  infix 25 _[_]ᴱ
  infix  4 _⊢ᴱ_∷_ _⊢ᴱ_≡_∷_ _▸ᴱ[_]_ ▸ᴱ[_]_ _⊢ˢᴱ_∷_

  field
    -- "Extended" terms.
    Termᴱ : Nat → Set a

    -- A typing relation for extended terms.
    _⊢ᴱ_∷_ : Context-pair Termᴱ k n → Termᴱ n → Termᴱ n → Set a

    -- Judgemental equality for extended terms.
    _⊢ᴱ_≡_∷_ :
      Context-pair Termᴱ k n → Termᴱ n → Termᴱ n → Termᴱ n → Set a

    -- A usage relation for extended terms.
    _▸ᴱ[_]_ : Conₘ n → Mode → Termᴱ n → Set a

  -- A usage relation for definition contexts.

  ▸ᴱ[_]_ : Mode → DCon (Termᴱ 0) n → Set a
  ▸ᴱ[ m ] ∇ = ∀ {α t A} → α ↦ t ∷ A ∈ ∇ → ε ▸ᴱ[ m ] t

  -- Extended term substitutions.

  Substᴱ : Nat → Nat → Set a
  Substᴱ l n = Fin n → Termᴱ l

  field
    -- Application of substitutions for extended terms.
    _[_]ᴱ : Termᴱ n → Substᴱ l n → Termᴱ l

    -- Substitution well-formedness for extended terms.
    _⊢ˢᴱ_∷_ : Context-pair Termᴱ k l → Substᴱ l n → Con Termᴱ n → Set a

    -- A substitution lemma for the extended theory.
    subst-⊢∷ᴱ :
      {A t : Termᴱ n} {σ : Substᴱ l n} →
      ∇ » Δ ⊢ᴱ t ∷ A → ∇ » Η ⊢ˢᴱ σ ∷ Δ → ∇ » Η ⊢ᴱ t [ σ ]ᴱ ∷ A [ σ ]ᴱ

    -- Another substitution lemma for the extended theory.
    subst-▸ᴱ :
      {t : Termᴱ n} {σ : Substᴱ 0 n} →
      ((x : Fin n) → ε ▸ᴱ[ 𝟘ᵐ? ] σ x) →
      𝟘ᶜ ▸ᴱ[ m ] t → ε ▸ᴱ[ m ] t [ σ ]ᴱ

    -- A function translating from terms to extended terms.
    tr : Term n → Termᴱ n

    -- The result of applying a substitution to tr ℕ is tr ℕ.
    tr-ℕ-[]ᴱ :
      {σ : Substᴱ l n} →
      tr ℕ [ σ ]ᴱ PE.≡ tr ℕ

    -- The translation is type-preserving.
    tr-⊢∷ : Γ ⊢ t ∷ A → map-Cons tr Γ ⊢ᴱ tr t ∷ tr A

    -- The translation is usage-preserving.
    tr-▸ : γ ▸[ m ] t → γ ▸ᴱ[ m ] tr t

    -- Extraction for the target language.
    eraseᴱ : Strictness → Termᴱ n → T.Term n

    -- Extraction is not affected by translation.
    eraseᴱ-tr : eraseᴱ str (tr t) PE.≡ erase str t

    -- If all free variables are erasable, then the application of a
    -- closing substitution does not affect the result of extraction
    -- (except for the application of a weakening).
    eraseᴱ-[]ᴱ :
      {σ : Substᴱ 0 n} {t : Termᴱ n}
      ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
      𝟘ᶜ ▸ᴱ[ 𝟙ᵐ ] t →
      T.wk wk₀ (eraseᴱ str (t [ σ ]ᴱ)) PE.≡ eraseᴱ str t

  -- Erasure for definition contexts.

  eraseDConᴱ : Strictness → DCon (Termᴱ 0) n → List (T.Term 0)
  eraseDConᴱ str = eraseDCon″ (eraseᴱ str)

  field
    -- Soundness of erasure for closed terms of type ℕ for the
    -- extended theory. The assumptions are based on those of
    -- Graded.Erasure.Consequences.Soundness.Soundness₀.soundness-ℕ.
    soundness-ℕᴱ :
      {t : Termᴱ 0}
      ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
      glassify ∇ » ε ⊢ᴱ t ∷ tr ℕ →
      ▸ᴱ[ 𝟙ᵐ ] glassify ∇ →
      ε ▸ᴱ[ 𝟙ᵐ ] t →
      ∃ λ n →
        glassify ∇ » ε ⊢ᴱ t ≡ tr (sucᵏ n) ∷ tr ℕ ×
        eraseDConᴱ str ∇ ⊢ eraseᴱ str t ⇒ˢ⟨ str ⟩* T.sucᵏ n

  opaque
    unfolding eraseDCon′

    -- Extraction is not affected by translation.

    eraseDConᴱ-tr : eraseDConᴱ str (map-DCon tr ∇) PE.≡ eraseDCon str ∇
    eraseDConᴱ-tr {∇ = ε} = PE.refl
    eraseDConᴱ-tr {∇ = ∇ ∙⟨ x ⟩[ x₁ ∷ x₂ ]} =
      PE.cong₂ L._++_ (eraseDConᴱ-tr {∇ = ∇})
        (PE.cong (L._∷ _) eraseᴱ-tr)

  opaque

    -- Soundness of erasure for open terms of type ℕ for the "basic"
    -- theory. Note that it is assumed that there is a closing,
    -- well-resourced substitution for the extended theory, and that
    -- "t reduces to the numeral" has been replaced with a statement
    -- that refers to the extended theory.

    soundness-ℕ :
      {σ : Substᴱ 0 n}
      ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
      map-DCon tr (glassify ∇) » ε ⊢ˢᴱ σ ∷ map-Con tr Δ →
      ((x : Fin n) → ε ▸ᴱ[ 𝟘ᵐ? ] σ x) →
      glassify ∇ » Δ ⊢ t ∷ ℕ →
      ▸[ 𝟙ᵐ ] glassify ∇ →
      𝟘ᶜ ▸[ 𝟙ᵐ ] t →
      ∃ λ n →
        map-DCon tr (glassify ∇) » ε ⊢ᴱ
          tr t [ σ ]ᴱ ≡ tr (sucᵏ n) ∷ tr ℕ ×
        eraseDCon str ∇ ⊢ erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n
    soundness-ℕ {t} {str} {σ} ⊢σ ▸σ ⊢t ▸∇ ▸t =
      let n , eq , red =
            soundness-ℕᴱ
              (PE.subst₃ _⊢ᴱ_∷_
                 (PE.cong (flip _»_ _) $ PE.sym glassify-map-DCon)
                 PE.refl tr-ℕ-[]ᴱ $
               subst-⊢∷ᴱ (tr-⊢∷ ⊢t) ⊢σ)
              (λ α↦ →
                 case ↦∷∈-map-DCon $
                      PE.subst (_↦_∷_∈_ _ _ _) glassify-map-DCon
                        α↦ of λ {
                   (_ , _ , PE.refl , _ , α↦) →
                 tr-▸ (▸∇ α↦) })
              (subst-▸ᴱ ▸σ (tr-▸ ▸t))
      in
      n ,
      PE.subst₄ _⊢ᴱ_≡_∷_
        (PE.cong (flip _»_ _) glassify-map-DCon) PE.refl PE.refl PE.refl
        eq ,
      PE.subst₄ _⊢_⇒ˢ⟨_⟩*_
        eraseDConᴱ-tr
        (T.wk wk₀ (eraseᴱ str (tr t [ σ ]ᴱ))  ≡⟨ eraseᴱ-[]ᴱ (tr-▸ ▸t) ⟩
         eraseᴱ str (tr t)                    ≡⟨ eraseᴱ-tr ⟩
         erase str t                          ∎)
        PE.refl TP.wk-sucᵏ
        (wk-⇒ˢ⟨⟩* red)

------------------------------------------------------------------------
-- A trivial instance

opaque
  unfolding eraseDCon′

  -- A trivial instance of Extended-type-theory, used to ensure that
  -- the record type's fields make at least some sense.

  Trivial-extended-type-theory : Extended-type-theory
  Trivial-extended-type-theory = λ where
      .Termᴱ     → Term
      .tr        → idᶠ
      .eraseᴱ    → erase
      ._⊢ᴱ_∷_    → _⊢_∷_
      ._⊢ᴱ_≡_∷_  → _⊢_≡_∷_
      ._▸ᴱ[_]_   → _▸[_]_
      ._[_]ᴱ     → _[_]
      ._⊢ˢᴱ_∷_   → _⊢ˢʷ_∷_
      .subst-⊢∷ᴱ →
        subst-⊢∷
      .subst-▸ᴱ →
        substₘ-lemma-closed
      .tr-ℕ-[]ᴱ →
        PE.refl
      .tr-⊢∷ →
        PE.subst (_⊢ _ ∷ _) (PE.sym map-Cons-id)
      .tr-▸ →
        idᶠ
      .eraseᴱ-tr →
        PE.refl
      .eraseᴱ-[]ᴱ →
        hasX.wk₀-erase-[] UR
      .soundness-ℕᴱ ⊢t ▸∇ ▸t →
        let _ , t⇒n , erase-t⇒n = Soundness₀.soundness-ℕ ▸∇ _ ⊢t ▸t in
        _ , subset*Termˢ t⇒n , erase-t⇒n
    where
    open Definition.Typed.Substitution TR
    open Extended-type-theory
    open Graded.Erasure.Consequences.Soundness TR UR
    open Graded.Substitution.Properties 𝕄 UR

------------------------------------------------------------------------
-- An instance that uses equality reflection

opaque
  unfolding eraseDCon′ turn-on-equality-reflection

  -- An instance that uses equality reflection.

  Extended-type-theory-with-equality-reflection :
    ¬ Opacity-allowed → Extended-type-theory
  Extended-type-theory-with-equality-reflection no-opacity = λ where
      .Termᴱ      → Term
      .tr         → idᶠ
      .eraseᴱ     → erase
      ._⊢ᴱ_∷_     → DT._⊢_∷_
      ._⊢ᴱ_≡_∷_   → DT._⊢_≡_∷_
      ._▸ᴱ[_]_    → GU._▸[_]_
      ._[_]ᴱ      → _[_]
      ._⊢ˢᴱ_∷_    → _⊢ˢʷ_∷_
      .subst-⊢∷ᴱ  → subst-⊢∷
      .subst-▸ᴱ   → substₘ-lemma-closed
      .tr-ℕ-[]ᴱ   → PE.refl
      .eraseᴱ-tr  → PE.refl
      .eraseᴱ-[]ᴱ → hasX.wk₀-erase-[] _
      .tr-⊢∷      →
        PE.subst₃ DT._⊢_∷_ (map-Cons-cong λ _ → tr-id) tr-id tr-id ∘→
        GM.tr-⊢∷
      .tr-▸ →
        PE.subst (GU._▸[_]_ _ _) tr-id ∘→ GM.tr-▸
      .soundness-ℕᴱ ⊢t ▸∇ ▸t →
        let _ , t⇒n , erase-t⇒n = Soundness₀.soundness-ℕ ▸∇ _ ⊢t ▸t in
        _ , GS.subset*Termˢ t⇒n , erase-t⇒n
    where
    conf : Configuration
    conf = turn-on-equality-reflection no-opacity

    module Conf = Configuration conf

    module DT = Definition.Typed Conf.TRₜ
    module GS = Graded.Erasure.SucRed Conf.TRₜ
    module GM = Graded.Modify-box-cong-or-J conf
    module GU = Graded.Usage 𝕄 Conf.URₜ

    open Definition.Typed.Substitution Conf.TRₜ
    open Extended-type-theory
    open Graded.Erasure.Consequences.Soundness Conf.TRₜ Conf.URₜ
    open Graded.Substitution.Properties 𝕄 Conf.URₜ

    tr-id : GM.tr t PE.≡ t
    tr-id = GM.tr-id PE.refl PE.refl

opaque
  unfolding Extended-type-theory-with-equality-reflection

  -- A variant of the soundness theorem for erasure for natural
  -- numbers.
  --
  -- This theorem has no restrictions related to erased matches.
  -- However, the variable context has to be inhabited in an extended
  -- theory in which equality reflection has been turned on, and the
  -- extended theory is used to define what it means for "the numeral"
  -- to be "correct".

  soundness-ℕ-using-equality-reflection :
    let TR′         = with-equality-reflection TR
        module Ext  = Definition.Typed TR′
        module Extˢ = Definition.Typed.Substitution TR′
    in
    {σ : Subst 0 n}
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
    ¬ Opacity-allowed →
    ∇ » ε Extˢ.⊢ˢʷ σ ∷ Δ →
    ((x : Fin n) → ε ▸[ 𝟘ᵐ? ] σ x) →
    ∇ » Δ ⊢ t ∷ ℕ →
    ▸[ 𝟙ᵐ ] ∇ →
    𝟘ᶜ ▸[ 𝟙ᵐ ] t →
    ∃ λ n →
      ∇ » ε Ext.⊢ t [ σ ] ≡ sucᵏ n ∷ ℕ ×
      eraseDCon str ∇ ⊢ erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n
  soundness-ℕ-using-equality-reflection {∇} no-opacity ⊢σ ▸σ ⊢t ▸∇ ▸t =
    let transparent = »→Transparent no-opacity (defn-wf (wfTerm ⊢t))

        lemma =
          map-DCon idᶠ (glassify ∇)  ≡⟨ map-DCon-id ⟩
          glassify ∇                 ≡˘⟨ transparent ⟩
          ∇                          ∎

        _ , eq , d =
          soundness-ℕ
            (PE.subst₃ _⊢ˢᴱ_∷_
               (PE.cong (flip _»_ _) $ PE.sym lemma)
               PE.refl (PE.sym map-Con-id)
               ⊢σ)
            ▸σ
            (PE.subst₃ _⊢_∷_
               (PE.cong (flip _»_ _) transparent) PE.refl PE.refl
               ⊢t)
            (PE.subst (▸[ _ ]_) transparent ▸∇) ▸t
    in
    _ ,
    PE.subst₄ _⊢ᴱ_≡_∷_
      (PE.cong (flip _»_ _) lemma) PE.refl PE.refl PE.refl
      eq ,
    d
    where
    open Definition.Typed.Properties TR
    open Extended-type-theory
           (Extended-type-theory-with-equality-reflection
              no-opacity)

opaque
  unfolding Extended-type-theory-with-equality-reflection

  -- A variant of the soundness theorem for erasure for natural
  -- numbers that shows that it is, in some sense, safe to "postulate"
  -- erased function extensionality (for certain grades and levels,
  -- given certain assumptions).

  soundness-ℕ-with-function-extensionality :
    let module Ext = Definition.Typed (with-equality-reflection TR) in
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
    ¬ Opacity-allowed →
    Π-allowed p q →
    Π-allowed p′ q′ →
    ⌜ 𝟘ᵐ? ⌝ · p ≤ 𝟘 →
    ⌜ 𝟘ᵐ? ⌝ · p′ ≤ 𝟘 →
    ∇ » ε ∙ Funext p q p′ q′ l₁ l₂ ⊢ t ∷ ℕ →
    ▸[ 𝟙ᵐ ] ∇ →
    𝟘ᶜ ▸[ 𝟙ᵐ ] t →
    ∃ λ n →
      ∇ » ε Ext.⊢ t [ funext p p′ ]₀ ≡ sucᵏ n ∷ ℕ ×
      eraseDCon str ∇ ⊢ erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n
  soundness-ℕ-with-function-extensionality
    {∇} no-opacity Π-ok Π-ok′ ·p≤𝟘 ·p′≤𝟘 ⊢t =
    soundness-ℕ-using-equality-reflection no-opacity
      (⊢ˢʷ∷-sgSubst $ ⊢funext _ Π-ok Π-ok′ (DT.ε »∇))
      (λ { x0 → ▸funext ·p≤𝟘 ·p′≤𝟘; (() +1) })
      ⊢t
    where
    TR′ : Type-restrictions 𝕄
    TR′ = with-equality-reflection TR

    module DT = Definition.Typed TR′

    open Definition.Typed.Properties TR′
    open Definition.Typed.Substitution TR′
    open Extended-type-theory
           (Extended-type-theory-with-equality-reflection no-opacity)

    »∇ : DT.» ∇
    »∇ =
      PE.subst DT.»_ map-DCon-id $
      defn-wf (wfTerm (tr-⊢∷ ⊢t))

opaque

  -- A variant of soundness-ℕ-with-function-extensionality that can be
  -- used if 𝟘ᵐ is allowed.

  soundness-ℕ-with-function-extensionality-𝟘ᵐ :
    let module Ext = Definition.Typed (with-equality-reflection TR) in
    ⦃ ok : T 𝟘ᵐ-allowed ⦄ →
    ¬ Opacity-allowed →
    Π-allowed p q →
    Π-allowed p′ q′ →
    ∇ » ε ∙ Funext p q p′ q′ l₁ l₂ ⊢ t ∷ ℕ →
    ▸[ 𝟙ᵐ ] ∇ →
    𝟘ᶜ ▸[ 𝟙ᵐ ] t →
    ∃ λ n →
      ∇ » ε Ext.⊢ t [ funext p p′ ]₀ ≡ sucᵏ n ∷ ℕ ×
      eraseDCon str ∇ ⊢ erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n
  soundness-ℕ-with-function-extensionality-𝟘ᵐ
    ⦃ ok ⦄ no-opacity Π-ok Π-ok′ =
    soundness-ℕ-with-function-extensionality
      ⦃ 𝟘-well-behaved = 𝟘-well-behaved ok ⦄ no-opacity Π-ok Π-ok′
      lemma lemma
    where
    lemma : ⌜ 𝟘ᵐ? ⌝ · p ≤ 𝟘
    lemma {p} = ≤-reflexive
      (⌜ 𝟘ᵐ? ⌝ · p  ≡⟨ PE.cong (λ m → ⌜ m ⌝ · _) $ 𝟘ᵐ?≡𝟘ᵐ {ok = ok} ⟩
       𝟘 · p        ≡⟨ ·-zeroˡ _ ⟩
       𝟘            ∎)
