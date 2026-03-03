------------------------------------------------------------------------
-- Soundness via extended type theories
------------------------------------------------------------------------

import Graded.Modality
open import Graded.Mode.Instances.Zero-one.Variant
import Graded.Mode.Instances.Zero-one
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions

module Graded.Erasure.Consequences.Soundness.Extended-type-theory
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  {variant : Mode-variant 𝕄}
  (open Graded.Mode.Instances.Zero-one variant)
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄 Zero-one-isMode)
  where

open Modality 𝕄
open Mode-variant variant
open Type-restrictions TR

import Definition.Typed
open Definition.Typed TR
import Definition.Typed.Inversion
import Definition.Typed.Properties
import Definition.Typed.Properties.Definition
import Definition.Typed.Substitution

open import Definition.Untyped M
open import Definition.Untyped.Identity 𝕄
open import Definition.Untyped.Properties M

open import Graded.Context 𝕄
open import Graded.Derived.Identity UR
import Graded.Erasure.Consequences.Soundness
open import Graded.Erasure.Extraction 𝕄
open import Graded.Erasure.Extraction.Properties 𝕄
import Graded.Erasure.Extraction.Properties.Usage
import Graded.Erasure.SucRed
open Graded.Erasure.SucRed TR
open import Graded.Erasure.Target as T using (Strictness)
import Graded.Erasure.Target.Properties as TP
open import Graded.Modality.Properties 𝕄
import Graded.Modify-box-cong-or-J
open import Graded.Modify-box-cong-or-J.Configuration TR UR
open import Graded.Restrictions.Zero-one 𝕄 variant
import Graded.Usage
open Graded.Usage UR
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
  Γ         : Context-pair _ _ _
  A l₁ l₂ t : Term _
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
-- * There is a substitution lemma for typing and usage, and a lemma
--   about how (roughly) extraction is not affected if anything is
--   substituted for erasable variables.
--
-- * There is a translation from the basic theory to the extended one
--   that is type- and usage-preserving in a certain sense. Extraction
--   is not affected by translation, and the application of a
--   substitution to the translation of ℕ is equal to the translation
--   of ℕ. There is also an assumption related to translation of
--   definition contexts.
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
  infix  4 _▸_⊢ᴱ_∷[_]_ _⊢ᴱ_≡_∷_ _▸_⊢ˢᴱ_∷[_]_

  field
    -- "Extended" terms.
    Termᴱ : Nat → Set a

    -- A typing and usage relation for extended terms.
    _▸_⊢ᴱ_∷[_]_ :
      Conₘ n → Context-pair Termᴱ k n → Termᴱ n → Mode → Termᴱ n → Set a

    -- Judgemental equality for extended terms.
    _⊢ᴱ_≡_∷_ :
      Context-pair Termᴱ k n → Termᴱ n → Termᴱ n → Termᴱ n → Set a

  -- Extended term substitutions.

  Substᴱ : Nat → Nat → Set a
  Substᴱ l n = Fin n → Termᴱ l

  field
    -- Application of substitutions for extended terms.
    _[_]ᴱ : Termᴱ n → Substᴱ l n → Termᴱ l

    -- Substitution well-formedness for extended terms.
    _▸_⊢ˢᴱ_∷[_]_ :
      Conₘ l → Context-pair Termᴱ k l → Substᴱ l n → Mode →
      Con Termᴱ n → Set a

    -- A substitution lemma for the extended theory.
    subst-⊢∷ᴱ :
      {A t : Termᴱ n} {σ : Substᴱ 0 n} →
      𝟘ᶜ ▸ ∇ » Δ ⊢ᴱ t ∷[ m ] A →
      ε ▸ ∇ » ε ⊢ˢᴱ σ ∷[ 𝟘ᵐ? ] Δ →
      ε ▸ ∇ » ε ⊢ᴱ t [ σ ]ᴱ ∷[ m ] A [ σ ]ᴱ

    -- A function translating from terms to extended terms.
    tr : Term n → Termᴱ n

    -- A translation for definition contexts.
    tr-DCon : DCon (Term 0) n → DCon (Termᴱ 0) n

  -- A translation for context pairs.

  tr-Cons : Context-pair Term k n → Context-pair Termᴱ k n
  tr-Cons (∇ » Γ) = tr-DCon ∇ » map-Con tr Γ

  field
    -- The result of applying a substitution to tr ℕ is tr ℕ.
    tr-ℕ-[]ᴱ :
      {σ : Substᴱ l n} →
      tr ℕ [ σ ]ᴱ PE.≡ tr ℕ

    -- The definition context glassify (tr-DCon ∇) is equal to
    -- glassify (map-DCon tr ∇).
    glassify-tr-DCon :
      glassify (tr-DCon ∇) PE.≡ glassify (map-DCon tr ∇)

    -- The translation is, in a certain sense, type- and
    -- usage-preserving.
    tr-⊢∷ :
      Γ ⊢ t ∷ A → γ ▸[ m ] t → ▸[ m ] glassify (Γ .defs) →
      γ ▸ tr-Cons Γ ⊢ᴱ tr t ∷[ m ] tr A

    -- Extraction for the target language.
    eraseᴱ : Strictness → Termᴱ n → T.Term n

    -- Extraction is not affected by translation.
    eraseᴱ-tr : eraseᴱ str (tr t) PE.≡ erase str t

    -- If all free variables are erasable, then the application of a
    -- closing substitution does not affect the result of extraction
    -- (except for the application of a weakening).
    eraseᴱ-[]ᴱ :
      {σ : Substᴱ 0 n} {t A : Termᴱ n}
      ⦃ 𝟘-well-behaved : Has-well-behaved-zero 𝕄 ⦄ →
      𝟘ᶜ ▸ Γ ⊢ᴱ t ∷[ 𝟙ᵐ ] A →
      T.wk wk₀ (eraseᴱ str (t [ σ ]ᴱ)) PE.≡ eraseᴱ str t

  -- Erasure for definition contexts.

  eraseDConᴱ : Strictness → DCon (Termᴱ 0) n → List (T.Term 0)
  eraseDConᴱ str = eraseDCon″ (eraseᴱ str)

  field
    -- Soundness of erasure for closed terms of type ℕ for the
    -- extended theory.
    soundness-ℕᴱ :
      {t : Termᴱ 0}
      ⦃ 𝟘-well-behaved : Has-well-behaved-zero 𝕄 ⦄ →
      ε ▸ ∇ » ε ⊢ᴱ t ∷[ 𝟙ᵐ ] tr ℕ →
      ∃ λ n →
        glassify ∇ » ε ⊢ᴱ t ≡ tr (sucᵏ n) ∷ tr ℕ ×
        eraseDConᴱ str ∇ ⊢ eraseᴱ str t ⇒ˢ⟨ str ⟩* T.sucᵏ n

  opaque
    unfolding eraseDCon′

    -- Extraction is not affected by translation.

    eraseDConᴱ-map-DCon-tr :
      eraseDConᴱ str (map-DCon tr ∇) PE.≡ eraseDCon str ∇
    eraseDConᴱ-map-DCon-tr {∇ = ε} =
      PE.refl
    eraseDConᴱ-map-DCon-tr {∇ = ∇ ∙!} =
      PE.cong₂ L._++_ (eraseDConᴱ-map-DCon-tr {∇ = ∇})
        (PE.cong (L._∷ _) eraseᴱ-tr)

  opaque

    -- Extraction is not affected by translation.

    eraseDConᴱ-tr-DCon : eraseDConᴱ str (tr-DCon ∇) PE.≡ eraseDCon str ∇
    eraseDConᴱ-tr-DCon {str} {∇} =
      eraseDConᴱ str (tr-DCon ∇)                 ≡˘⟨ eraseDCon″-glassify ⟩
      eraseDConᴱ str (glassify (tr-DCon ∇))      ≡⟨ PE.cong (eraseDConᴱ _) glassify-tr-DCon ⟩
      eraseDConᴱ str (glassify (map-DCon tr ∇))  ≡⟨ eraseDCon″-glassify ⟩
      eraseDConᴱ str (map-DCon tr ∇)             ≡⟨ eraseDConᴱ-map-DCon-tr ⟩
      eraseDCon str ∇                            ∎

  opaque

    -- Soundness of erasure for open terms of type ℕ for the "basic"
    -- theory. Note that it is assumed that there is a closing,
    -- well-resourced substitution for the extended theory, and that
    -- "t reduces to the numeral" has been replaced with a statement
    -- that refers to the extended theory.

    soundness-ℕ :
      {σ : Substᴱ 0 n}
      ⦃ 𝟘-well-behaved : Has-well-behaved-zero 𝕄 ⦄ →
      ε ▸ tr-DCon ∇ » ε ⊢ˢᴱ σ ∷[ 𝟘ᵐ? ] map-Con tr Δ →
      ∇ » Δ ⊢ t ∷ ℕ →
      ▸[ 𝟙ᵐ ] glassify ∇ →
      𝟘ᶜ ▸[ 𝟙ᵐ ] t →
      ∃ λ n →
        map-DCon tr (glassify ∇) » ε ⊢ᴱ
          tr t [ σ ]ᴱ ≡ tr (sucᵏ n) ∷ tr ℕ ×
        eraseDCon str ∇ ⊢ erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n
    soundness-ℕ {∇} {t} {str} {σ} ⊢σ ⊢t ▸∇ ▸t =
      let ⊢tr-t = tr-⊢∷ ⊢t ▸t ▸∇

          n , eq , red =
            soundness-ℕᴱ $
            PE.subst (_▸_⊢ᴱ_∷[_]_ _ _ _ _) tr-ℕ-[]ᴱ $
            subst-⊢∷ᴱ ⊢tr-t ⊢σ
      in
      n ,
      PE.subst₄ _⊢ᴱ_≡_∷_
        (PE.cong (flip _»_ _)
           (glassify (tr-DCon ∇)      ≡⟨ glassify-tr-DCon ⟩
            glassify (map-DCon tr ∇)  ≡⟨ glassify-map-DCon ⟩
            map-DCon tr (glassify ∇)  ∎))
        PE.refl PE.refl PE.refl
        eq ,
      PE.subst₄ _⊢_⇒ˢ⟨_⟩*_
        eraseDConᴱ-tr-DCon
        (T.wk wk₀ (eraseᴱ str (tr t [ σ ]ᴱ))  ≡⟨ eraseᴱ-[]ᴱ ⊢tr-t ⟩
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
      .Termᴱ                 → Term
      ._[_]ᴱ                 → _[_]
      .tr                    → idᶠ
      .tr-DCon               → idᶠ
      .eraseᴱ                → erase
      ._⊢ᴱ_≡_∷_              → _⊢_≡_∷_
      ._▸_⊢ᴱ_∷[_]_ γ Γ t m A →
        Γ ⊢ t ∷ A × γ ▸[ m ] t × ▸[ m ] glassify (Γ .defs)
      ._▸_⊢ˢᴱ_∷[_]_ δ Δ σ m Γ →
        Δ ⊢ˢʷ σ ∷ Γ × (∀ x → δ ▸[ m ] σ x)
      .subst-⊢∷ᴱ (⊢t , ▸t , ▸∇) (⊢σ , ▸σ) →
        subst-⊢∷ ⊢t ⊢σ , substₘ-lemma-closed ▸σ ▸t , ▸∇
      .tr-ℕ-[]ᴱ →
        PE.refl
      .glassify-tr-DCon →
        PE.cong glassify $ PE.sym map-DCon-id
      .tr-⊢∷ ⊢t ▸t ▸∇ →
        PE.subst (_⊢ _ ∷ _) (PE.cong (_»_ _) (PE.sym map-Con-id)) ⊢t ,
        ▸t , ▸∇
      .eraseᴱ-tr →
        PE.refl
      .eraseᴱ-[]ᴱ (_ , ▸t , _) →
        wk₀-erase-[] ▸t
      .soundness-ℕᴱ (⊢t , ▸t , ▸∇) →
        let _ , t⇒n , erase-t⇒n = Soundness₀.soundness-ℕ ▸∇ ⊢t ▸t in
        _ , subset*Termˢ t⇒n , erase-t⇒n _
    where
    open Definition.Typed.Substitution TR
    open Extended-type-theory
    open Graded.Erasure.Consequences.Soundness TR UR
    open Graded.Substitution.Properties UR
    open Graded.Erasure.Extraction.Properties.Usage UR

------------------------------------------------------------------------
-- An instance that uses equality reflection

-- Some definitions used below.

private module Extended-type-theory-with-equality-reflection where

  module Conf = Configuration turn-on-equality-reflection
  module DT   = Definition.Typed Conf.TRₜ
  module DP   = Definition.Typed.Properties TR
  module DP′  = Definition.Typed.Properties Conf.TRₜ
  module DD   = Definition.Typed.Properties.Definition Conf.TRₜ
  module GS   = Graded.Erasure.SucRed Conf.TRₜ
  module GM   = Graded.Modify-box-cong-or-J turn-on-equality-reflection
  module GU   = Graded.Usage Conf.URₜ

  opaque
    unfolding turn-on-equality-reflection

    tr-id : GM.tr t PE.≡ t
    tr-id = GM.tr-id PE.refl PE.refl

  opaque
    unfolding turn-on-equality-reflection

    map-DCon-tr-id : map-DCon GM.tr ∇ PE.≡ ∇
    map-DCon-tr-id = GM.map-DCon-tr-id PE.refl PE.refl

  opaque
    unfolding
      turn-on-equality-reflection
      Graded.Modify-box-cong-or-J.tr-DCon
      Graded.Modify-box-cong-or-J.tr-Cons

    tr-Cons≡ : GM.tr-Cons (∇ » Δ) PE.≡ glassify ∇ » map-Con idᶠ Δ
    tr-Cons≡ {∇} {Δ} =
      PE.cong₂ _»_
        (glassify (map-DCon GM.tr ∇)  ≡⟨ PE.cong glassify map-DCon-tr-id ⟩
         glassify ∇                   ∎)
        (map-Con GM.tr Δ  ≡⟨ GM.map-Con-tr-id PE.refl PE.refl ⟩
         Δ                ≡˘⟨ map-Con-id ⟩
         map-Con idᶠ Δ    ∎)

opaque
  unfolding eraseDCon′

  -- An instance that uses equality reflection.

  Extended-type-theory-with-equality-reflection : Extended-type-theory
  Extended-type-theory-with-equality-reflection = λ where
      .Termᴱ                 → Term
      ._[_]ᴱ                 → _[_]
      .tr                    → idᶠ
      .tr-DCon               → glassify
      .eraseᴱ                → erase
      ._⊢ᴱ_≡_∷_              → DT._⊢_≡_∷_
      ._▸_⊢ᴱ_∷[_]_ γ Γ t m A →
        Γ DT.⊢ t ∷ A × γ GU.▸[ m ] t × GU.▸[ m ] glassify (Γ .defs)
      ._▸_⊢ˢᴱ_∷[_]_ δ Δ σ m Γ →
        Δ ⊢ˢʷ σ ∷ Γ × (∀ x → δ GU.▸[ m ] σ x)
      .subst-⊢∷ᴱ (⊢t , ▸t , ▸∇) (⊢σ , ▸σ) →
        subst-⊢∷ ⊢t ⊢σ , substₘ-lemma-closed ▸σ ▸t , ▸∇
      .tr-ℕ-[]ᴱ             → PE.refl
      .glassify-tr-DCon {∇} →
        glassify (glassify ∇)      ≡⟨ DD.glassify-idem _ ⟩
        glassify ∇                 ≡˘⟨ PE.cong glassify map-DCon-id ⟩
        glassify (map-DCon idᶠ ∇)  ∎
      .eraseᴱ-tr               → PE.refl
      .eraseᴱ-[]ᴱ (_ , ▸t , _) → wk₀-erase-[] ▸t
      .tr-⊢∷ {Γ} ⊢t ▸t ▸∇      →
        PE.subst₃ DT._⊢_∷_ tr-Cons≡ tr-id tr-id (GM.tr-⊢∷ ⊢t) ,
        PE.subst (GU._▸[_]_ _ _) tr-id (GM.tr-▸ ▸t) ,
        PE.subst (GU.▸[_]_ _)
          (map-DCon GM.tr (glassify (Γ .defs))  ≡⟨ map-DCon-tr-id ⟩
           glassify (Γ .defs)                   ≡˘⟨ DD.glassify-idem _ ⟩
           glassify (glassify (Γ .defs))        ∎)
          (GM.tr-▸-DCon ▸∇)
      .soundness-ℕᴱ (⊢t , ▸t , ▸∇) →
        let _ , t⇒n , erase-t⇒n = Soundness₀.soundness-ℕ ▸∇ ⊢t ▸t in
        _ , GS.subset*Termˢ t⇒n , erase-t⇒n _
    where
    open Extended-type-theory
    open Extended-type-theory-with-equality-reflection
    open Definition.Typed.Substitution Conf.TRₜ
    open Graded.Erasure.Consequences.Soundness Conf.TRₜ Conf.URₜ
    open Graded.Substitution.Properties Conf.URₜ
    open Graded.Erasure.Extraction.Properties.Usage Conf.URₜ

opaque
  unfolding
    Extended-type-theory-with-equality-reflection
    turn-on-equality-reflection

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
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero 𝕄 ⦄ →
    glassify ∇ » ε Extˢ.⊢ˢʷ σ ∷ Δ →
    ((x : Fin n) → ε ▸[ 𝟘ᵐ? ] σ x) →
    ∇ » Δ ⊢ t ∷ ℕ →
    ▸[ 𝟙ᵐ ] glassify ∇ →
    𝟘ᶜ ▸[ 𝟙ᵐ ] t →
    ∃ λ n →
      glassify ∇ » ε Ext.⊢ t [ σ ] ≡ sucᵏ n ∷ ℕ ×
      eraseDCon str ∇ ⊢ erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n
  soundness-ℕ-using-equality-reflection {∇} ⊢σ ▸σ ⊢t ▸∇ ▸t =
    let _ , eq , d =
          soundness-ℕ
            (PE.subst (_⊢ˢʷ_∷_ _ _ _) (PE.sym map-Con-id) ⊢σ , ▸σ)
            ⊢t ▸∇ ▸t
    in
    _ ,
    PE.subst₄ _⊢ᴱ_≡_∷_
      (PE.cong (flip _»_ _) map-DCon-id) PE.refl PE.refl PE.refl
      eq ,
    d
    where
    open Extended-type-theory
           Extended-type-theory-with-equality-reflection
    open Definition.Typed.Substitution

opaque
  unfolding
    Extended-type-theory-with-equality-reflection
    Funext
    Level-allowed
    turn-on-equality-reflection

  -- A variant of the soundness theorem for erasure for natural
  -- numbers that shows that it is, in some sense, safe to "postulate"
  -- erased function extensionality (for certain grades, given certain
  -- assumptions).

  soundness-ℕ-with-function-extensionality :
    let module Ext = Definition.Typed (with-equality-reflection TR) in
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero 𝕄 ⦄ →
    Level-allowed →
    Π-allowed p q →
    Π-allowed p′ q′ →
    ⌜ 𝟘ᵐ? ⌝ · p ≤ 𝟘 →
    ⌜ 𝟘ᵐ? ⌝ · p′ ≤ 𝟘 →
    ∇ » ε ∙ Poly-funext p q p′ q′ ⊢ t ∷ ℕ →
    ▸[ 𝟙ᵐ ] glassify ∇ →
    𝟘ᶜ ▸[ 𝟙ᵐ ] t →
    ∃ λ n →
      glassify ∇ » ε Ext.⊢ t [ poly-funext p p′ ]₀ ≡ sucᵏ n ∷ ℕ ×
      eraseDCon str ∇ ⊢ erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n
  soundness-ℕ-with-function-extensionality ok Π-ok Π-ok′ ·p≤𝟘 ·p′≤𝟘 ⊢t =
    soundness-ℕ-using-equality-reflection
      (⊢ˢʷ∷-sgSubst $
       DP′.⊢poly-funext _ ok Π-ok Π-ok′ $
       tr-⊢ (ε (DP.defn-wf (DP.wfTerm ⊢t))))
      (λ { x0 → ▸poly-funext ·p≤𝟘 ·p′≤𝟘; (() +1) })
      ⊢t
    where
    open Extended-type-theory-with-equality-reflection

    open Definition.Typed.Inversion TR
    open Definition.Typed.Properties TR
    open Definition.Typed.Substitution Conf.TRₜ
    open Extended-type-theory
           Extended-type-theory-with-equality-reflection

    tr-⊢ : ⊢ Γ → DT.⊢ tr-Cons Γ
    tr-⊢ = PE.subst DT.⊢_ tr-Cons≡ ∘→ GM.tr-⊢′

opaque

  -- A variant of soundness-ℕ-with-function-extensionality that can be
  -- used if 𝟘ᵐ is allowed.

  soundness-ℕ-with-function-extensionality-𝟘ᵐ :
    let module Ext = Definition.Typed (with-equality-reflection TR) in
    ⦃ ok : T 𝟘ᵐ-allowed ⦄ →
    Level-allowed →
    Π-allowed p q →
    Π-allowed p′ q′ →
    ∇ » ε ∙ Poly-funext p q p′ q′ ⊢ t ∷ ℕ →
    ▸[ 𝟙ᵐ ] glassify ∇ →
    𝟘ᶜ ▸[ 𝟙ᵐ ] t →
    ∃ λ n →
      glassify ∇ » ε Ext.⊢ t [ poly-funext p p′ ]₀ ≡ sucᵏ n ∷ ℕ ×
      eraseDCon str ∇ ⊢ erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n
  soundness-ℕ-with-function-extensionality-𝟘ᵐ ⦃ ok ⦄ okᴸ Π-ok Π-ok′ =
    soundness-ℕ-with-function-extensionality
      ⦃ 𝟘-well-behaved = 𝟘-well-behaved ok ⦄ okᴸ Π-ok Π-ok′ lemma lemma
    where
    lemma : ⌜ 𝟘ᵐ? ⌝ · p ≤ 𝟘
    lemma {p} = ≤-reflexive
      (⌜ 𝟘ᵐ? ⌝ · p  ≡⟨ PE.cong (λ m → ⌜ m ⌝ · _) $ 𝟘ᵐ?≡𝟘ᵐ {ok = ok} ⟩
       𝟘 · p        ≡⟨ ·-zeroˡ _ ⟩
       𝟘            ∎)
