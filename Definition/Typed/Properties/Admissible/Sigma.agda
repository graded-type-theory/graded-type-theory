------------------------------------------------------------------------
-- Admissible rules related to Σ
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Sigma
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M

open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties.Admissible.Equality R
open import Definition.Typed.Properties.Admissible.Identity R
open import Definition.Typed.Properties.Admissible.Level R
open import Definition.Typed.Properties.Admissible.Lift R
open import Definition.Typed.Properties.Admissible.Pi-Sigma R
open import Definition.Typed.Properties.Admissible.Var R
open import Definition.Typed.Properties.Reduction R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Reasoning.Reduction R
import Definition.Typed.Reasoning.Term R as TmR
import Definition.Typed.Reasoning.Type R as TyR
open import Definition.Typed.Substitution.Primitive R
open import Definition.Typed.Weakening R as W hiding (wk)
open import Definition.Typed.Well-formed R

open import Definition.Untyped.Lift M
open import Definition.Untyped.Pi-Sigma M
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sigma 𝕄

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private variable
  Γ                                               : Cons _ _
  A A₁ A₂ B B₁ B₂ C C₁ C₂ l₁ l₂ t t₁ t₂ u u₁ u₂ v : Term _
  p q q′ r                                        : M
  s                                               : Strength

------------------------------------------------------------------------
-- Simple variants of typing, equality and reduction rules

opaque

  -- A variant of Σ-η.

  Σ-η′ :
    Γ ⊢ t ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊢ u ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊢ fst p t ≡ fst p u ∷ A →
    Γ ⊢ snd p t ≡ snd p u ∷ B [ fst p t ]₀ →
    Γ ⊢ t ≡ u ∷ Σˢ p , q ▷ A ▹ B
  Σ-η′ ⊢t ⊢u t₁≡u₁ t₂≡u₂ =
    let _ , ⊢B , ok = inversion-ΠΣ (wf-⊢∷ ⊢t) in
    Σ-η ⊢B ⊢t ⊢u t₁≡u₁ t₂≡u₂ ok

opaque

  -- A variant of fstⱼ.

  fstⱼ′ :
    Γ ⊢ t ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊢ fst p t ∷ A
  fstⱼ′ ⊢t =
    let _ , ⊢B , _ = inversion-ΠΣ (wf-⊢∷ ⊢t) in
    fstⱼ ⊢B ⊢t

opaque

  -- A variant of sndⱼ.

  sndⱼ′ :
    Γ ⊢ t ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊢ snd p t ∷ B [ fst p t ]₀
  sndⱼ′ ⊢t =
    let _ , ⊢B , _ = inversion-ΠΣ (wf-⊢∷ ⊢t) in
    sndⱼ ⊢B ⊢t

opaque

  -- A variant of prodrecⱼ.

  prodrecⱼ′ :
    Γ »∙ Σʷ p , q′ ▷ A ▹ B ⊢ C →
    Γ ⊢ t ∷ Σʷ p , q′ ▷ A ▹ B →
    Γ »∙ A »∙ B ⊢ u ∷ C [ prodʷ p (var x1) (var x0) ]↑² →
    Γ ⊢ prodrec r p q C t u ∷ C [ t ]₀
  prodrecⱼ′ ⊢C ⊢t ⊢u =
    let _ , _ , ok = inversion-ΠΣ (wf-⊢∷ ⊢t) in
    prodrecⱼ ⊢C ⊢t ⊢u ok

opaque

  -- A variant of fst-subst.

  fst-subst′ :
    Γ ⊢ t ⇒ u ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊢ fst p t ⇒ fst p u ∷ A
  fst-subst′ t⇒u =
    let _ , ⊢B , _ = inversion-ΠΣ (wf-⊢∷ (redFirstTerm t⇒u)) in
    fst-subst ⊢B t⇒u

opaque

  -- A variant of fst-subst for _⊢_⇒*_∷_.

  fst-subst* :
    Γ ⊢ t ⇒* u ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊢ fst p t ⇒* fst p u ∷ A
  fst-subst* t⇒*u =
    let _ , ⊢B , _ = inversion-ΠΣ (wf-⊢∷ (redFirst*Term t⇒*u)) in
    case t⇒*u of λ where
      (id ⊢t)     → id (fstⱼ ⊢B ⊢t)
      (t⇒u ⇨ u⇒v) → fst-subst ⊢B t⇒u ⇨ fst-subst* u⇒v

opaque

  -- A variant of fst-cong.

  fst-cong′ :
    Γ ⊢ t ≡ u ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊢ fst p t ≡ fst p u ∷ A
  fst-cong′ t≡u =
    let _ , ⊢B , _ = inversion-ΠΣ (wf-⊢≡∷ t≡u .proj₁) in
    fst-cong ⊢B t≡u

opaque

  -- A variant of snd-subst.

  snd-subst′ :
    Γ ⊢ t ⇒ u ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊢ snd p t ⇒ snd p u ∷ B [ fst p t ]₀
  snd-subst′ t⇒u =
    let _ , ⊢B , _ = inversion-ΠΣ (wf-⊢∷ (redFirstTerm t⇒u)) in
    snd-subst ⊢B t⇒u

opaque

  -- A variant of snd-subst for _⊢_⇒*_∷_.

  snd-subst* :
    Γ ⊢ t ⇒* u ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊢ snd p t ⇒* snd p u ∷ B [ fst p t ]₀
  snd-subst* t⇒*u =
    let _ , ⊢B , _ = inversion-ΠΣ $ wf-⊢∷ $ redFirst*Term t⇒*u in
    case t⇒*u of λ where
      (id ⊢t)      → id (sndⱼ′ ⊢t)
      (t⇒v ⇨ v⇨*u) →
        snd-subst′ t⇒v ⇨
        conv* (snd-subst* v⇨*u)
          (substTypeEq (refl ⊢B) (sym′ (fst-cong′ (subsetTerm t⇒v))))

opaque

  -- A variant of snd-cong.

  snd-cong′ :
    Γ ⊢ t ≡ u ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊢ snd p t ≡ snd p u ∷ B [ fst p t ]₀
  snd-cong′ t≡u =
    let _ , ⊢B , _ = inversion-ΠΣ (wf-⊢≡∷ t≡u .proj₁) in
    snd-cong ⊢B t≡u

opaque

  -- A variant of prodrec-subst.

  prodrec-subst′ :
    Γ »∙ Σʷ p , q′ ▷ A ▹ B ⊢ C →
    Γ »∙ A »∙ B ⊢ u ∷ C [ prodʷ p (var x1) (var x0) ]↑² →
    Γ ⊢ t₁ ⇒ t₂ ∷ Σʷ p , q′ ▷ A ▹ B →
    Γ ⊢ prodrec r p q C t₁ u ⇒ prodrec r p q C t₂ u ∷ C [ t₁ ]₀
  prodrec-subst′ ⊢C ⊢u t₁⇒t₂ =
    let _ , _ , ok = inversion-ΠΣ (wf-⊢∷ (redFirstTerm t₁⇒t₂)) in
    prodrec-subst ⊢C ⊢u t₁⇒t₂ ok

opaque

  -- A variant of prodrec-subst for _⊢_⇒*_∷_.

  prodrec-subst* :
    Γ »∙ Σʷ p , q ▷ A ▹ B ⊢ C →
    Γ ⊢ t₁ ⇒* t₂ ∷ Σʷ p , q ▷ A ▹ B →
    Γ »∙ A »∙ B ⊢ u ∷ C [ prodʷ p (var x1) (var x0) ]↑² →
    Γ ⊢ prodrec r p q′ C t₁ u ⇒* prodrec r p q′ C t₂ u ∷ C [ t₁ ]₀
  prodrec-subst* ⊢C t₁⇒*t₂ ⊢u =
    case t₁⇒*t₂ of λ where
      (id ⊢t₁)         → id (prodrecⱼ′ ⊢C ⊢t₁ ⊢u)
      (t₁⇒t₃ ⇨ t₃⇒*t₂) →
        prodrec-subst′ ⊢C ⊢u t₁⇒t₃ ⇨
        conv* (prodrec-subst* ⊢C t₃⇒*t₂ ⊢u)
          (substTypeEq (refl ⊢C) (sym′ (subsetTerm t₁⇒t₃)))

opaque

  -- A variant of prodrec-cong.

  prodrec-cong′ :
    Γ »∙ Σʷ p , q′ ▷ A ▹ B ⊢ C₁ ≡ C₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ Σʷ p , q′ ▷ A ▹ B →
    Γ »∙ A »∙ B ⊢ u₁ ≡ u₂ ∷ C₁ [ prodʷ p (var x1) (var x0) ]↑² →
    Γ ⊢ prodrec r p q C₁ t₁ u₁ ≡ prodrec r p q C₂ t₂ u₂ ∷ C₁ [ t₁ ]₀
  prodrec-cong′ C₁≡C₂ t₁≡t₂ u₁≡u₂ =
    let _ , _ , ok = inversion-ΠΣ (wf-⊢≡∷ t₁≡t₂ .proj₁) in
    prodrec-cong C₁≡C₂ t₁≡t₂ u₁≡u₂ ok

opaque

  -- A variant of the reduction rule Σ-β₁.

  Σ-β₁-⇒ :
    Γ »∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σˢ-allowed p q →
    Γ ⊢ fst p (prodˢ p t u) ⇒ t ∷ A
  Σ-β₁-⇒ ⊢B ⊢t ⊢u =
    Σ-β₁ ⊢B ⊢t ⊢u PE.refl

opaque

  -- A variant of the equality rule Σ-β₁.

  Σ-β₁-≡ :
    Γ »∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σˢ-allowed p q →
    Γ ⊢ fst p (prodˢ p t u) ≡ t ∷ A
  Σ-β₁-≡ ⊢B ⊢t ⊢u ok =
    subsetTerm (Σ-β₁-⇒ ⊢B ⊢t ⊢u ok)

opaque

  -- A variant of the reduction rule Σ-β₂.

  Σ-β₂-⇒ :
    Γ »∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σˢ-allowed p q →
    Γ ⊢ snd p (prodˢ p t u) ⇒ u ∷ B [ t ]₀
  Σ-β₂-⇒ ⊢B ⊢t ⊢u =
    Σ-β₂ ⊢B ⊢t ⊢u PE.refl

opaque

  -- A variant of the equality rule Σ-β₂.

  Σ-β₂-≡ :
    Γ »∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σˢ-allowed p q →
    Γ ⊢ snd p (prodˢ p t u) ≡ u ∷ B [ t ]₀
  Σ-β₂-≡ ⊢B ⊢t ⊢u ok =
    subsetTerm (Σ-β₂-⇒ ⊢B ⊢t ⊢u ok)

opaque

  -- A variant of the reduction rule prodrec-β.

  prodrec-β-⇒ :
    Γ »∙ Σʷ p , q′ ▷ A ▹ B ⊢ C →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Γ »∙ A »∙ B ⊢ v ∷ C [ prodʷ p (var x1) (var x0) ]↑² →
    Γ ⊢ prodrec r p q C (prodʷ p t u) v ⇒ v [ t , u ]₁₀ ∷
      C [ prodʷ p t u ]₀
  prodrec-β-⇒ ⊢C ⊢t ⊢u ⊢v =
    let _ , _ , ok = inversion-ΠΣ (⊢∙→⊢ (wf ⊢C)) in
    prodrec-β ⊢C ⊢t ⊢u ⊢v PE.refl ok

opaque

  -- A variant of the equality rule prodrec-β.

  prodrec-β-≡ :
    Γ »∙ Σʷ p , q′ ▷ A ▹ B ⊢ C →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Γ »∙ A »∙ B ⊢ v ∷ C [ prodʷ p (var x1) (var x0) ]↑² →
    Γ ⊢ prodrec r p q C (prodʷ p t u) v ≡ v [ t , u ]₁₀ ∷
      C [ prodʷ p t u ]₀
  prodrec-β-≡ ⊢C ⊢t ⊢u ⊢v =
    subsetTerm (prodrec-β-⇒ ⊢C ⊢t ⊢u ⊢v)

opaque

  -- An η-rule for strong Σ-types.

  Σ-η-prod-fst-snd :
    Γ ⊢ t ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊢ prodˢ p (fst p t) (snd p t) ≡ t ∷ Σˢ p , q ▷ A ▹ B
  Σ-η-prod-fst-snd ⊢t =
    let _ , ⊢B , ok = inversion-ΠΣ (wf-⊢∷ ⊢t)
        ⊢fst        = fstⱼ′ ⊢t
        ⊢snd        = sndⱼ′ ⊢t
    in
    sym′ $
    Σ-η′ ⊢t (prodⱼ ⊢B ⊢fst ⊢snd ok) (sym′ (Σ-β₁-≡ ⊢B ⊢fst ⊢snd ok))
      (sym′ (Σ-β₂-≡ ⊢B ⊢fst ⊢snd ok))

------------------------------------------------------------------------
-- Some private definitions

private opaque

  -- A lemma that can be used to prove lemmas like snd-subst*.

  subst→subst* :
    ∀ t →
    Γ »∙ A ⊢ B →
    (∀ {u} →
     Γ ⊢ u ∷ A →
     Γ ⊢ t [ u ]₀ ∷ B [ u ]₀) →
    (∀ {u₁ u₂} →
     Γ ⊢ u₁ ⇒ u₂ ∷ A →
     Γ ⊢ t [ u₁ ]₀ ⇒ t [ u₂ ]₀ ∷ B [ u₁ ]₀) →
    Γ ⊢ u₁ ⇒* u₂ ∷ A →
    Γ ⊢ t [ u₁ ]₀ ⇒* t [ u₂ ]₀ ∷ B [ u₁ ]₀
  subst→subst* {B} {u₁} {u₂} t ⊢B ⊢t[] t[]⇒t[] = λ where
    (id ⊢u)                      → id (⊢t[] ⊢u)
    (_⇨_ {t′ = u₃} u₁⇒u₃ u₃⇒*u₂) →
      t [ u₁ ]₀ ∷ B [ u₁ ]₀  ⇒⟨ t[]⇒t[] u₁⇒u₃ ⟩∷
                              ⟨ substTypeEq (refl ⊢B) (subsetTerm u₁⇒u₃) ⟩⇒
      t [ u₃ ]₀ ∷ B [ u₃ ]₀  ⇒*⟨ subst→subst* t ⊢B ⊢t[] t[]⇒t[] u₃⇒*u₂ ⟩∎∷
      t [ u₂ ]₀              ∎

private opaque

  -- The lemma subst→subst* is private (and placed in this module
  -- rather than, say, Definition.Typed.Properties.Reduction) because
  -- it can be rather awkward to use: tastes may vary, but the
  -- following proof is at least (at the time of writing) longer than
  -- snd-subst*, even if one does not count the where clause.

  snd-subst*′ :
    Γ ⊢ t ⇒* u ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊢ snd p t ⇒* snd p u ∷ B [ fst p t ]₀
  snd-subst*′ {p} {B} t⇒*u =
    case wf-⊢∷ $ redFirst*Term t⇒*u of λ
      ⊢ΣAB →
    case inversion-ΠΣ ⊢ΣAB of λ
      (_ , ⊢B , _) →
    PE.subst (_⊢_⇒*_∷_ _ _ _) ([]↑-[]₀ B) $
    subst→subst* (snd p (var x0))
      (subst↑Type ⊢B (fstⱼ′ (var₀ ⊢ΣAB)))
      (λ ⊢u →
         PE.subst (_⊢_∷_ _ _) (PE.sym $ []↑-[]₀ B) $
         sndⱼ′ ⊢u)
      (λ u₁⇒u₂ →
         PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ []↑-[]₀ B) $
         snd-subst′ u₁⇒u₂)
      t⇒*u

------------------------------------------------------------------------
-- An investigation of to what degree weak Σ-types can emulate strong
-- Σ-types, and vice versa

-- The following part of this module (at the time of writing up to but
-- not including the section "Some lemmas related to Σʰ⟨_⟩") consists
-- of (parts of) an investigation of to what degree weak Σ-types can
-- emulate strong Σ-types, and vice versa. This investigation was
-- prompted by a question asked by an anonymous reviewer. See also
-- Definition.Untyped.Sigma, which contains some basic definitions,
-- and Graded.Derived.Sigma, which contains properties related to
-- usage. This module contains properties related to typing (a few
-- more such properties can be found in
-- Definition.Typed.Consequences.Admissible.Sigma).

------------------------------------------------------------------------
-- Typing and equality rules for prodrecˢ

private opaque

  -- A lemma used below.

  ⊢[1,0]↑²[fst,snd]≡ :
    Γ »∙ Σˢ p , q ▷ A ▹ B ⊢ C →
    Γ ⊢ t ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊢
      C [ prodˢ p (var x1) (var x0) ]↑² [ fst p t , snd p t ]₁₀ ≡
      C [ t ]₀
  ⊢[1,0]↑²[fst,snd]≡ {Γ} {p} {q} {A} {B} {C} {t} ⊢C =
    Γ ⊢ t ∷ Σˢ p , q ▷ A ▹ B                                         →⟨ Σ-η-prod-fst-snd ⟩

    Γ ⊢ prodˢ p (fst p t) (snd p t) ≡ t ∷ Σˢ p , q ▷ A ▹ B           →⟨ substTypeEq (refl ⊢C) ⟩

    Γ ⊢ C [ prodˢ p (fst p t) (snd p t) ]₀ ≡ C [ t ]₀                →⟨ PE.subst (_ ⊢_≡ _) (PE.sym $ [1,0]↑²[,] C) ⟩

    Γ ⊢ C [ prodˢ p (var x1) (var x0) ]↑² [ fst p t , snd p t ]₁₀ ≡
      C [ t ]₀                                                       □

opaque

  -- A typing rule for prodrecˢ.

  prodrecˢⱼ :
    Γ »∙ Σˢ p , q ▷ A ▹ B ⊢ C →
    Γ ⊢ t ∷ Σˢ p , q ▷ A ▹ B →
    Γ »∙ A »∙ B ⊢ u ∷ C [ prodˢ p (var x1) (var x0) ]↑² →
    Γ ⊢ prodrecˢ p t u ∷ C [ t ]₀
  prodrecˢⱼ {Γ} {p} {q} {A} {B} {C} {t} {u} ⊢C ⊢t ⊢u =           $⟨ fstⱼ′ ⊢t , sndⱼ′ ⊢t ⟩

    Γ ⊢ fst p t ∷ A ×
    Γ ⊢ snd p t ∷ B [ fst p t ]₀                                 →⟨ (λ (hyp₁ , hyp₂) → →⊢ˢʷ∷∙ (⊢ˢʷ∷-sgSubst hyp₁) hyp₂) ⟩

    Γ ⊢ˢʷ
      consSubst (consSubst idSubst (fst p t)) (snd p t) ∷
      Γ .vars ∙ A ∙ B                                            →⟨ subst-⊢∷ ⊢u ⟩

    Γ ⊢
      prodrecˢ p t u ∷
      C [ prodˢ p (var x1) (var x0) ]↑² [ fst p t , snd p t ]₁₀  →⟨ flip conv (⊢[1,0]↑²[fst,snd]≡ ⊢C ⊢t) ⟩

    Γ ⊢ prodrecˢ p t u ∷ C [ t ]₀                                □

opaque

  -- An equality rule for prodrecˢ.

  prodrecˢ-β :
    ∀ C →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Γ »∙ A »∙ B ⊢ v ∷ C [ prodˢ p (var x1) (var x0) ]↑² →
    Σˢ-allowed p q′ →
    Γ ⊢ prodrecˢ p (prodˢ p t u) v ≡ v [ t , u ]₁₀ ∷ C [ prodˢ p t u ]₀
  prodrecˢ-β {Γ} {t} {A} {u} {B} {v} {p} C ⊢t ⊢u ⊢v ok =
    let ⊢B = ⊢∙→⊢ (wfTerm ⊢v) in                                         $⟨ Σ-β₁-≡ ⊢B ⊢t ⊢u ok
                                                                          , Σ-β₂-≡ ⊢B ⊢t ⊢u ok
                                                                          ⟩
    Γ ⊢ fst p (prodˢ p t u) ≡ t ∷ A ×
    Γ ⊢ snd p (prodˢ p t u) ≡ u ∷ B [ t ]₀                               →⟨ (λ (hyp₁ , hyp₂) →
                                                                               →⊢ˢʷ≡∷∙ ⊢B (⊢ˢʷ≡∷-sgSubst (sym′ hyp₁)) (sym′ hyp₂)) ⟩
    Γ ⊢ˢʷ
      consSubst (consSubst idSubst t) u ≡
      consSubst (consSubst idSubst (fst p (prodˢ p t u)))
        (snd p (prodˢ p t u)) ∷
      Γ .vars ∙ A ∙ B                                                    →⟨ subst-⊢≡∷ (refl ⊢v) ⟩

    Γ ⊢
      v [ t , u ]₁₀ ≡
      prodrecˢ p (prodˢ p t u) v ∷
      C [ prodˢ p (var x1) (var x0) ]↑² [ t , u ]₁₀                      →⟨ PE.subst (_⊢_≡_∷_ _ _ _) ([1,0]↑²[,] C) ∘→ sym′ ⟩

    Γ ⊢ prodrecˢ p (prodˢ p t u) v ≡ v [ t , u ]₁₀ ∷ C [ prodˢ p t u ]₀  □

opaque

  -- Another equality rule for prodrecˢ.

  prodrecˢ-cong :
    Γ »∙ Σˢ p , q ▷ A ▹ B ⊢ C →
    Γ ⊢ t₁ ≡ t₂ ∷ Σˢ p , q ▷ A ▹ B →
    Γ »∙ A »∙ B ⊢ u₁ ≡ u₂ ∷ C [ prodˢ p (var x1) (var x0) ]↑² →
    Γ ⊢ prodrecˢ p t₁ u₁ ≡ prodrecˢ p t₂ u₂ ∷ C [ t₁ ]₀
  prodrecˢ-cong
    {Γ} {p} {q} {A} {B} {C} {t₁} {t₂} {u₁} {u₂} ⊢C t₁≡t₂ u₁≡u₂ =
    let ⊢Σ , ⊢t₁ , _ = wf-⊢≡∷ t₁≡t₂
        _ , ⊢B , _   = inversion-ΠΣ ⊢Σ
    in                                                             $⟨ fst-cong′ t₁≡t₂ , snd-cong′ t₁≡t₂ ⟩

    Γ ⊢ fst p t₁ ≡ fst p t₂ ∷ A ×
    Γ ⊢ snd p t₁ ≡ snd p t₂ ∷ B [ fst p t₁ ]₀                      →⟨ (λ (hyp₁ , hyp₂) → →⊢ˢʷ≡∷∙ ⊢B (⊢ˢʷ≡∷-sgSubst hyp₁) hyp₂) ⟩

    Γ ⊢ˢʷ
      consSubst (consSubst idSubst (fst p t₁)) (snd p t₁) ≡
      consSubst (consSubst idSubst (fst p t₂)) (snd p t₂) ∷
      Γ .vars ∙ A ∙ B                                              →⟨ subst-⊢≡∷ u₁≡u₂ ⟩

    Γ ⊢
      prodrecˢ p t₁ u₁ ≡
      prodrecˢ p t₂ u₂ ∷
      C [ prodˢ p (var x1) (var x0) ]↑² [ fst p t₁ , snd p t₁ ]₁₀  →⟨ flip conv (⊢[1,0]↑²[fst,snd]≡ ⊢C ⊢t₁) ⟩

    Γ ⊢ prodrecˢ p t₁ u₁ ≡ prodrecˢ p t₂ u₂ ∷ C [ t₁ ]₀            □

-- This module does not contain proofs of any reduction rules for
-- prodrecˢ. One might have hoped that the following rules should
-- hold:
--
--   Γ »∙ Σˢ p , q ▷ A ▹ B ⊢ C →
--   Γ ⊢ t ∷ A →
--   Γ ⊢ u ∷ B [ t ]₀ →
--   Γ »∙ A »∙ B ⊢ v ∷ C [ prodˢ p (var x1) (var x0) ]↑² →
--   Γ ⊢ prodrecˢ p (prodˢ p t u) v ⇒ v [ t , u ]₁₀ ∷ C [ prodˢ p t u ]₀
--
--   Γ »∙ Σˢ p , q ▷ A ▹ B ⊢ C →
--   Γ »∙ A »∙ B ⊢ u ∷ C [ prodʷ p (var x1) (var x0) ]↑² →
--   Γ ⊢ t₁ ⇒ t₂ ∷ Σʷ p , q ▷ A ▹ B →
--   Γ ⊢ prodrecˢ p t₁ u ⇒ prodrecˢ p t₂ u ∷ C [ t₁ ]₀
--
-- However, the reduction relation only allows reduction in certain
-- places in terms. For instance, it does not include reduction under
-- lambdas. Thus it seems unlikely that the rules above can be proved
-- (but there is no formal proof of this in this module).

------------------------------------------------------------------------
-- Some private lemmas related to wk1 and wk1Subst

private opaque

  -- Some lemmas used below.

  Σ⊢wk1 :
    Γ »∙ A ⊢ B →
    Σʷ-allowed p q →
    Γ »∙ Σʷ p , q ▷ A ▹ B ⊢ wk1 A
  Σ⊢wk1 ⊢B ok =
    W.wk₁ (ΠΣⱼ ⊢B ok) (⊢∙→⊢ (wf ⊢B))

  ⊢wk2 :
    Γ »∙ A ⊢ B →
    Γ »∙ A »∙ B ⊢ wk2 A
  ⊢wk2 ⊢B =
    let ⊢A = ⊢∙→⊢ (wf ⊢B) in
    W.wk₁ ⊢B (W.wk₁ ⊢A ⊢A)

  ⊢wk1[]≡ :
    Γ ⊢ A →
    Γ ⊢ wk1 A [ t ]₀ ≡ A
  ⊢wk1[]≡ {Γ} {A} {t} =
    Γ ⊢ A                   →⟨ refl ⟩
    (Γ ⊢ A ≡ A)             →⟨ PE.subst (_ ⊢_≡ _) (PE.sym (wk1-sgSubst _ _)) ⟩
    (Γ ⊢ wk1 A [ t ]₀ ≡ A)  □

  ⊢wk1≡ :
    Γ ⊢ A →
    Γ ⊢ B →
    Γ »∙ A ⊢ wk1 B ≡ B [ wk1Subst idSubst ]
  ⊢wk1≡ {Γ} {A} {B} ⊢A =
    Γ ⊢ B                                      →⟨ W.wk₁ ⊢A ⟩
    Γ »∙ A ⊢ wk1 B                             →⟨ refl ⟩
    (Γ »∙ A ⊢ wk1 B ≡ wk1 B)                   →⟨ PE.subst₂ (_ ⊢_≡_) PE.refl (wk[]≡[] 1) ⟩
    (Γ »∙ A ⊢ wk1 B ≡ B [ wk1Subst idSubst ])  □

  ⊢wk2≡ :
    Γ »∙ A ⊢ B →
    Γ »∙ A »∙ B ⊢ wk2 A ≡ A [ wkSubst 2 idSubst ]
  ⊢wk2≡ {Γ} {A} {B} =
    Γ »∙ A ⊢ B                                       →⟨ ⊢wk2 ⟩
    Γ »∙ A »∙ B ⊢ wk2 A                              →⟨ refl ⟩
    (Γ »∙ A »∙ B ⊢ wk2 A ≡ wk2 A)                    →⟨ PE.subst₂ (_⊢_≡_ _) PE.refl (wk[]≡[] 2) ⟩
    (Γ »∙ A »∙ B ⊢ wk2 A ≡ A [ wkSubst 2 idSubst ])  □

  ⊢ˢʷwk1Subst-idSubst :
    Γ ⊢ A →
    Γ »∙ A ⊢ˢʷ wk1Subst idSubst ∷ Γ .vars
  ⊢ˢʷwk1Subst-idSubst {Γ} {A} ⊢A =         $⟨ ⊢ˢʷ∷-idSubst (wf ⊢A) ⟩
    Γ ⊢ˢʷ idSubst ∷ Γ .vars                →⟨ ⊢ˢʷ∷-wk1Subst ⊢A ⟩
    Γ »∙ A ⊢ˢʷ wk1Subst idSubst ∷ Γ .vars  □

  ⊢ˢʷwkSubst-2-idSubst :
    Γ »∙ A ⊢ B →
    Γ »∙ A »∙ B ⊢ˢʷ wkSubst 2 idSubst ∷ Γ .vars
  ⊢ˢʷwkSubst-2-idSubst {Γ} {A} {B} ⊢B =          $⟨ ⊢ˢʷwk1Subst-idSubst (⊢∙→⊢ (wf ⊢B)) ⟩
    Γ »∙ A ⊢ˢʷ wk1Subst idSubst ∷ Γ .vars        →⟨ ⊢ˢʷ∷-wk1Subst ⊢B ⟩
    Γ »∙ A »∙ B ⊢ˢʷ wkSubst 2 idSubst ∷ Γ .vars  □

------------------------------------------------------------------------
-- Typing rules for fstʷ

private opaque

  -- A lemma used below.

  1∷wk1[1,0] :
    Γ »∙ A ⊢ B →
    Γ »∙ A »∙ B ⊢ var x1 ∷ wk1 A [ prodʷ p (var x1) (var x0) ]↑²
  1∷wk1[1,0] {Γ} {A} {B} {p} ⊢B =                                   $⟨ ⊢B ⟩
    Γ »∙ A ⊢ B                                                      →⟨ ⊢wk2 ⟩
    Γ »∙ A »∙ B ⊢ wk2 A                                             →⟨ refl ⟩
    (Γ »∙ A »∙ B ⊢ wk2 A ≡ wk2 A)                                   →⟨ PE.subst (_⊢_≡_ _ _) (PE.sym $ wk1-[][]↑ 2) ⟩
    (Γ »∙ A »∙ B ⊢ wk2 A ≡ wk1 A [ prodʷ p (var x1) (var x0) ]↑²)   →⟨ conv (var₁ ⊢B) ⟩
    (Γ »∙ A »∙ B ⊢ var x1 ∷ wk1 A [ prodʷ p (var x1) (var x0) ]↑²)  □

opaque

  -- A typing rule for fstʷ.

  fstʷⱼ :
    Γ ⊢ t ∷ Σʷ p , q ▷ A ▹ B →
    Γ ⊢ fstʷ p A t ∷ A
  fstʷⱼ {Γ} {t} {p} {q} {A} {B} ⊢t =
    let ⊢A , ⊢B , ok = inversion-ΠΣ (wf-⊢∷ ⊢t) in                 $⟨ Σ⊢wk1 ⊢B ok , 1∷wk1[1,0] ⊢B ⟩

    (Γ »∙ Σʷ p , q ▷ A ▹ B ⊢ wk1 A) ×
    Γ »∙ A »∙ B ⊢ var x1 ∷ wk1 A [ prodʷ p (var x1) (var x0) ]↑²  →⟨ (λ (hyp₁ , hyp₂) → prodrecⱼ′ hyp₁ ⊢t hyp₂) ⟩

    Γ ⊢ fstʷ p A t ∷ wk1 A [ t ]₀                                 →⟨ flip conv (⊢wk1[]≡ ⊢A) ⟩

    Γ ⊢ fstʷ p A t ∷ A                                            □

opaque

  -- A reduction rule for fstʷ.

  fstʷ-β-⇒ :
    Γ »∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σʷ-allowed p q →
    Γ ⊢ fstʷ p A (prodʷ p t u) ⇒ t ∷ A
  fstʷ-β-⇒ {Γ} {A} {B} {t} {u} {p} {q} ⊢B ⊢t ⊢u ok =              $⟨ Σ⊢wk1 ⊢B ok , 1∷wk1[1,0] ⊢B ⟩
    (Γ »∙ Σʷ p , q ▷ A ▹ B ⊢ wk1 A) ×
    Γ »∙ A »∙ B ⊢ var x1 ∷ wk1 A [ prodʷ p (var x1) (var x0) ]↑²  →⟨ (λ (hyp₁ , hyp₂) → prodrec-β-⇒ hyp₁ ⊢t ⊢u hyp₂) ⟩

    Γ ⊢ fstʷ p A (prodʷ p t u) ⇒ t ∷ wk1 A [ prodʷ p t u ]₀       →⟨ flip conv (⊢wk1[]≡ (wf-⊢∷ ⊢t)) ⟩

    Γ ⊢ fstʷ p A (prodʷ p t u) ⇒ t ∷ A                            □

opaque

  -- Another reduction rule for fstʷ.

  fstʷ-subst :
    Γ ⊢ t₁ ⇒ t₂ ∷ Σʷ p , q ▷ A ▹ B →
    Γ ⊢ fstʷ p A t₁ ⇒ fstʷ p A t₂ ∷ A
  fstʷ-subst {Γ} {t₁} {t₂} {p} {q} {A} {B} t₁⇒t₂ =
    let ⊢A , ⊢B , ok =
          inversion-ΠΣ (wf-⊢≡∷ (subsetTerm t₁⇒t₂) .proj₁)
    in                                                            $⟨ Σ⊢wk1 ⊢B ok , 1∷wk1[1,0] ⊢B ⟩

    (Γ »∙ Σʷ p , q ▷ A ▹ B ⊢ wk1 A) ×
    Γ »∙ A »∙ B ⊢ var x1 ∷ wk1 A [ prodʷ p (var x1) (var x0) ]↑²  →⟨ (λ (hyp₁ , hyp₂) → prodrec-subst′ hyp₁ hyp₂ t₁⇒t₂) ⟩

    Γ ⊢ fstʷ p A t₁ ⇒ fstʷ p A t₂ ∷ wk1 A [ t₁ ]₀                 →⟨ flip conv (⊢wk1[]≡ ⊢A) ⟩

    Γ ⊢ fstʷ p A t₁ ⇒ fstʷ p A t₂ ∷ A                             □

opaque

  -- An equality rule for fstʷ.

  fstʷ-β-≡ :
    Γ »∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σʷ-allowed p q →
    Γ ⊢ fstʷ p A (prodʷ p t u) ≡ t ∷ A
  fstʷ-β-≡ ⊢B ⊢t ⊢u ok = subsetTerm (fstʷ-β-⇒ ⊢B ⊢t ⊢u ok)

opaque

  -- Another equality rule for fstʷ.

  fstʷ-cong :
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ Σʷ p , q ▷ A₁ ▹ B₁ →
    Γ ⊢ fstʷ p A₁ t₁ ≡ fstʷ p A₂ t₂ ∷ A₁
  fstʷ-cong {Γ} {A₁} {A₂} {t₁} {t₂} {p} {q} {B₁} A₁≡A₂ t₁≡t₂ =
    let ⊢A₁ , ⊢B₁ , ok = inversion-ΠΣ (wf-⊢≡∷ t₁≡t₂ .proj₁) in       $⟨ W.wkEq₁ (ΠΣⱼ ⊢B₁ ok) A₁≡A₂
                                                                      , 1∷wk1[1,0] ⊢B₁
                                                                      ⟩
    (Γ »∙ Σʷ p , q ▷ A₁ ▹ B₁ ⊢ wk1 A₁ ≡ wk1 A₂) ×
    Γ »∙ A₁ »∙ B₁ ⊢ var x1 ∷ wk1 A₁ [ prodʷ p (var x1) (var x0) ]↑²  →⟨ (λ (hyp₁ , hyp₂) → prodrec-cong′ hyp₁ t₁≡t₂ (refl hyp₂)) ⟩

    Γ ⊢ fstʷ p A₁ t₁ ≡ fstʷ p A₂ t₂ ∷ wk1 A₁ [ t₁ ]₀                 →⟨ flip conv (⊢wk1[]≡ ⊢A₁) ⟩

    Γ ⊢ fstʷ p A₁ t₁ ≡ fstʷ p A₂ t₂ ∷ A₁                             □

------------------------------------------------------------------------
-- Some private lemmas related to fstʷ

private opaque

  -- Some lemmas used below.

  fstʷ-0[] : fstʷ p (wk1 A) (var x0) [ t ]₀ PE.≡ fstʷ p A t
  fstʷ-0[] {A} {t} = PE.cong (λ A → prodrec _ _ _ A _ _) $
    wk2 A [ liftSubst (sgSubst t) ]  ≡⟨ subst-wk (wk1 A) ⟩
    wk1 A [ wk1 ∘→ sgSubst t ]       ≡⟨ wk1-tail A ⟩
    A [ wk1Subst idSubst ]           ≡˘⟨ wk≡subst _ _ ⟩
    wk1 A                            ∎

  [fstʷ] :
    ∀ B → B [ fstʷ p A t ]₀ PE.≡ B [ fstʷ p (wk1 A) (var x0) ]↑ [ t ]₀
  [fstʷ] {p} {A} {t} B =
    B [ fstʷ p A t ]₀                                            ≡˘⟨ (flip substVar-to-subst B λ where
                                                                        x0     → fstʷ-0[]
                                                                        (_ +1) → PE.refl) ⟩
    B [ sgSubst t ₛ•ₛ
        consSubst (wk1Subst idSubst) (fstʷ p (wk1 A) (var x0)) ] ≡˘⟨ substCompEq B ⟩

    B [ fstʷ p (wk1 A) (var x0) ]↑ [ t ]₀                        ∎

  ⊢≡[fstʷ] :
    Γ ⊢ t ∷ Σʷ p , q ▷ A ▹ B →
    Γ ⊢ B [ fstʷ p (wk1 A) (var x0) ]↑ [ t ]₀ ≡ B [ fstʷ p A t ]₀
  ⊢≡[fstʷ] {Γ} {t} {p} {A} {B} ⊢t =                                  $⟨ subst-⊢ (inversion-ΠΣ (wf-⊢∷ ⊢t) .proj₂ .proj₁)
                                                                          (⊢ˢʷ∷-sgSubst (fstʷⱼ ⊢t)) ⟩
    Γ ⊢ B [ fstʷ p A t ]₀                                            →⟨ refl ⟩
    (Γ ⊢ B [ fstʷ p A t ]₀ ≡ B [ fstʷ p A t ]₀)                      →⟨ PE.subst₂ (_ ⊢_≡_) ([fstʷ] B) PE.refl ⟩
    (Γ ⊢ B [ fstʷ p (wk1 A) (var x0) ]↑ [ t ]₀ ≡ B [ fstʷ p A t ]₀)  □

  [fstʷ-0]↑[1,0]↑² :
    ∀ B →
    B [ fstʷ p (wk1 A) (var x0) ]↑ [ prodʷ p (var x1) (var x0) ]↑²
      PE.≡
    B [ fstʷ p (wk1 (wk1 A)) (prodʷ p (var x1) (var x0)) ]↑²
  [fstʷ-0]↑[1,0]↑² {p} {A} B =
    B [ fstʷ p (wk1 A) (var x0) ]↑ [ prodʷ p (var x1) (var x0) ]↑²     ≡⟨ substCompEq B ⟩

    B [ consSubst (wkSubst 2 idSubst) (prodʷ p (var x1) (var x0)) ₛ•ₛ
       consSubst (wk1Subst idSubst) (fstʷ p (wk1 A) (var x0)) ]        ≡⟨ (flip substVar-to-subst B λ where
                                                                             x0     → PE.refl
                                                                             (_ +1) → PE.refl) ⟩
    B [ prodrec _ p _
          (wk2 A
             [ liftSubst $ consSubst (wkSubst 2 idSubst) $
               prodʷ p (var x1) (var x0) ])
          (prodʷ p (var x1) (var x0))
          (var x1) ]↑²                                                 ≡⟨ PE.cong (λ A → B [ prodrec _ _ _ A _ _ ]↑²) $
                                                                          PE.trans (wk1-tail (wk1 A)) $
                                                                          wk1-tail A ⟩
    B [ prodrec _ p _ (A [ wkSubst 3 idSubst ])
          (prodʷ p (var x1) (var x0)) (var x1) ]↑²                     ≡˘⟨ PE.cong (λ A → B [ prodrec _ _ _ A _ _ ]↑²) $
                                                                           PE.trans (PE.cong (_[ _ ]) $ substCompEq A) $
                                                                           substCompEq A ⟩
    B [ prodrec _ p _
          (_[ wk1Subst idSubst ] $
           _[ wk1Subst idSubst ] $
           A [ wk1Subst idSubst ])
          (prodʷ p (var x1) (var x0))
          (var x1) ]↑²                                                 ≡˘⟨ PE.cong (λ A → B [ prodrec _ _ _ A _ _ ]↑²) $
                                                                           PE.trans (wk≡subst _ _) $
                                                                           PE.trans (PE.cong (_[ _ ]) $ wk≡subst _ (wk1 A)) $
                                                                           PE.cong (_[ _ ]) $ PE.cong (_[ _ ]) $ wk≡subst _ A ⟩
    B [ fstʷ p (wk1 (wk1 A)) (prodʷ p (var x1) (var x0)) ]↑²           ∎

  ⊢≡[fstʷ-0]↑[1,0]↑² :
    Γ »∙ A ⊢ B →
    Σʷ-allowed p q →
    Γ »∙ A »∙ B ⊢
      wk1 B ≡
      B [ fstʷ p (wk1 A) (var x0) ]↑ [ prodʷ p (var x1) (var x0) ]↑²
  ⊢≡[fstʷ-0]↑[1,0]↑² {Γ} {A} {B} {p} ⊢B ok =                          $⟨ →⊢ˢʷ≡∷∙ (⊢∙→⊢ (wf ⊢B)) (refl-⊢ˢʷ≡∷ (⊢ˢʷwkSubst-2-idSubst ⊢B)) lemma ⟩
    Γ »∙ A »∙ B ⊢ˢʷ
      consSubst (wkSubst 2 idSubst) (var x1) ≡
      consSubst (wkSubst 2 idSubst)
        (fstʷ p (wk2 A) (prodʷ p (var x1) (var x0))) ∷
      Γ .vars ∙ A                                                     →⟨ subst-⊢≡ (refl ⊢B) ⟩

    Γ »∙ A »∙ B ⊢
      B [ var x1 ]↑² ≡
      B [ fstʷ p (wk2 A) (prodʷ p (var x1) (var x0)) ]↑²              →⟨ PE.subst₂ (_⊢_≡_ _) [1]↑² (PE.sym $ [fstʷ-0]↑[1,0]↑² B) ⟩

    Γ »∙ A »∙ B ⊢
      wk1 B ≡
      B [ fstʷ p (wk1 A) (var x0) ]↑ [ prodʷ p (var x1) (var x0) ]↑²  □
    where
    lemma :
      Γ »∙ A »∙ B ⊢
        var x1 ≡
        fstʷ p (wk1 (wk1 A)) (prodʷ p (var x1) (var x0)) ∷
        A [ wkSubst 2 idSubst ]
    lemma =                                            $⟨ W.wk₁ ⊢B ⊢B ⟩

      (Γ »∙ A »∙ B ⊢ wk1 B)                            →⟨ refl ⟩

      Γ »∙ A »∙ B ⊢ wk1 B ≡ wk1 B                      →⟨ PE.subst₂ (_⊢_≡_ _) PE.refl (PE.sym (wk1-sgSubst (wk1 B) _)) ⟩

      Γ »∙ A »∙ B ⊢ wk1 B ≡ wk2 B [ var x1 ]₀          →⟨ conv (var₀ ⊢B) ⟩

      (Γ »∙ A »∙ B ⊢ var x0 ∷ wk2 B [ var x1 ]₀)       →⟨ (λ ⊢0 → ⊢wk2 (⊢wk2 ⊢B) , var₁ ⊢B , ⊢0) ⟩

      (Γ »∙ A »∙ B »∙ wk2 A ⊢ wk2 B) ×
      (Γ »∙ A »∙ B ⊢ var x1 ∷ wk2 A) ×
      (Γ »∙ A »∙ B ⊢ var x0 ∷ wk2 B [ var x1 ]₀)       →⟨ (λ (⊢B , ⊢1 , ⊢0) → fstʷ-β-≡ ⊢B ⊢1 ⊢0 ok) ⟩

      (Γ »∙ A »∙ B ⊢
         fstʷ p (wk2 A) (prodʷ p (var x1) (var x0)) ≡
         var x1 ∷
         wk2 A)                                        →⟨ flip _⊢_≡_∷_.conv (⊢wk2≡ ⊢B) ∘→ sym′ ⟩

      (Γ »∙ A »∙ B ⊢
         var x1 ≡
         fstʷ p (wk2 A) (prodʷ p (var x1) (var x0)) ∷
         A [ wkSubst 2 idSubst ])                      □

  ⊢[fstʷ-0]↑≡[fstʷ-0]↑ :
    Γ ⊢ A₁ ≡ A₂ →
    Γ »∙ A₁ ⊢ B₁ ≡ B₂ →
    Σʷ-allowed p q →
    Γ »∙ Σʷ p , q ▷ A₁ ▹ B₁ ⊢
      B₁ [ fstʷ p (wk1 A₁) (var x0) ]↑ ≡
      B₂ [ fstʷ p (wk1 A₂) (var x0) ]↑
  ⊢[fstʷ-0]↑≡[fstʷ-0]↑ {Γ} {A₁} {A₂} {B₁} {B₂} {p} {q} A₁≡A₂ B₁≡B₂ ok =
    let ⊢ΣA₁B₁ = ΠΣⱼ (wf-⊢≡ B₁≡B₂ .proj₁) ok in                  $⟨ refl (var₀ ⊢ΣA₁B₁) ⟩

    Γ »∙ Σʷ p , q ▷ A₁ ▹ B₁ ⊢
      var x0 ≡
      var x0 ∷
      wk1 (Σʷ p , q ▷ A₁ ▹ B₁)                                   →⟨ fstʷ-cong (W.wkEq (W.stepʷ id ⊢ΣA₁B₁) A₁≡A₂) ⟩

    Γ »∙ Σʷ p , q ▷ A₁ ▹ B₁ ⊢
      fstʷ p (wk1 A₁) (var x0) ≡
      fstʷ p (wk1 A₂) (var x0) ∷
      wk1 A₁                                                     →⟨ flip conv (⊢wk1≡ ⊢ΣA₁B₁ (wf-⊢≡ A₁≡A₂ .proj₁)) ⟩

    Γ »∙ Σʷ p , q ▷ A₁ ▹ B₁ ⊢
      fstʷ p (wk1 A₁) (var x0) ≡
      fstʷ p (wk1 A₂) (var x0) ∷
      A₁ [ wk1Subst idSubst ]                                    →⟨ →⊢ˢʷ≡∷∙ (wf-⊢≡ A₁≡A₂ .proj₁)
                                                                      (refl-⊢ˢʷ≡∷ (⊢ˢʷwk1Subst-idSubst ⊢ΣA₁B₁)) ⟩
    Γ »∙ Σʷ p , q ▷ A₁ ▹ B₁ ⊢ˢʷ
      consSubst (wk1Subst idSubst) (fstʷ p (wk1 A₁) (var x0)) ≡
      consSubst (wk1Subst idSubst) (fstʷ p (wk1 A₂) (var x0)) ∷
      Γ .vars ∙ A₁                                               →⟨ subst-⊢≡ B₁≡B₂ ⟩

    Γ »∙ Σʷ p , q ▷ A₁ ▹ B₁ ⊢
      B₁ [ fstʷ p (wk1 A₁) (var x0) ]↑ ≡
      B₂ [ fstʷ p (wk1 A₂) (var x0) ]↑                           □

  ⊢[fstʷ-0]↑ :
    Γ »∙ A ⊢ B →
    Σʷ-allowed p q →
    Γ »∙ Σʷ p , q ▷ A ▹ B ⊢ B [ fstʷ p (wk1 A) (var x0) ]↑
  ⊢[fstʷ-0]↑ ⊢B ok =
    wf-⊢≡ (⊢[fstʷ-0]↑≡[fstʷ-0]↑ (refl (⊢∙→⊢ (wf ⊢B))) (refl ⊢B) ok)
      .proj₁

  ⊢0∷[fstʷ-0]↑[1,0]↑² :
    Γ »∙ A ⊢ B →
    Σʷ-allowed p q →
    Γ »∙ A »∙ B ⊢
      var x0 ∷
      B [ fstʷ p (wk1 A) (var x0) ]↑ [ prodʷ p (var x1) (var x0) ]↑²
  ⊢0∷[fstʷ-0]↑[1,0]↑² {Γ} {A} {B} {p} ⊢B ok =                         $⟨ var₀ ⊢B ⟩

    Γ »∙ A »∙ B ⊢ var x0 ∷ wk1 B                                      →⟨ flip _⊢_∷_.conv (⊢≡[fstʷ-0]↑[1,0]↑² ⊢B ok) ⟩

    Γ »∙ A »∙ B ⊢
      var x0 ∷
      B [ fstʷ p (wk1 A) (var x0) ]↑ [ prodʷ p (var x1) (var x0) ]↑²  □

------------------------------------------------------------------------
-- Typing rules for sndʷ

opaque

  -- A typing rule for sndʷ.

  sndʷⱼ :
    Γ ⊢ t ∷ Σʷ p , q ▷ A ▹ B →
    Γ ⊢ sndʷ p q A B t ∷ B [ fstʷ p A t ]₀
  sndʷⱼ {Γ} {t} {p} {q} {A} {B} ⊢t =
    let _ , ⊢B , ok = inversion-ΠΣ (wf-⊢∷ ⊢t) in                $⟨ prodrecⱼ (⊢[fstʷ-0]↑ ⊢B ok) ⊢t
                                                                     (⊢0∷[fstʷ-0]↑[1,0]↑² ⊢B ok) ok ⟩
    Γ ⊢ sndʷ p q A B t ∷ B [ fstʷ p (wk1 A) (var x0) ]↑ [ t ]₀  →⟨ flip conv (⊢≡[fstʷ] ⊢t) ⟩
    Γ ⊢ sndʷ p q A B t ∷ B [ fstʷ p A t ]₀                      □

opaque

  -- A reduction rule for sndʷ.

  sndʷ-β-⇒ :
    Γ »∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σʷ-allowed p q →
    Γ ⊢ sndʷ p q A B (prodʷ p t u) ⇒ u ∷ B [ t ]₀
  sndʷ-β-⇒ {Γ} {A} {B} {t} {u} {p} {q} ⊢B ⊢t ⊢u ok =
                                                       $⟨ prodrec-β (⊢[fstʷ-0]↑ {q = q} ⊢B ok)
                                                            ⊢t ⊢u (⊢0∷[fstʷ-0]↑[1,0]↑² ⊢B ok) PE.refl ok ⟩
    Γ ⊢ sndʷ p q A B (prodʷ p t u) ⇒ u ∷
      B [ fstʷ p (wk1 A) (var x0) ]↑ [ prodʷ p t u ]₀  →⟨ flip conv (⊢≡[fstʷ] (prodⱼ ⊢B ⊢t ⊢u ok)) ⟩

    Γ ⊢ sndʷ p q A B (prodʷ p t u) ⇒ u ∷
      B [ fstʷ p A (prodʷ p t u) ]₀                    →⟨ flip conv (substTypeEq (refl ⊢B) (fstʷ-β-≡ ⊢B ⊢t ⊢u ok)) ⟩

    Γ ⊢ sndʷ p q A B (prodʷ p t u) ⇒ u ∷ B [ t ]₀      □

opaque

  -- Another reduction rule for sndʷ.

  sndʷ-subst :
    Γ ⊢ t₁ ⇒ t₂ ∷ Σʷ p , q ▷ A ▹ B →
    Γ ⊢ sndʷ p q A B t₁ ⇒ sndʷ p q A B t₂ ∷ B [ fstʷ p A t₁ ]₀
  sndʷ-subst {Γ} {t₁} {t₂} {p} {q} {A} {B} t₁⇒t₂ =
    let _ , ⊢t₁ , _ = wf-⊢≡∷ (subsetTerm t₁⇒t₂)
        _ , ⊢B , ok = inversion-ΠΣ (wf-⊢∷ ⊢t₁)
    in                                           $⟨ prodrec-subst′ (⊢[fstʷ-0]↑ ⊢B ok) (⊢0∷[fstʷ-0]↑[1,0]↑² ⊢B ok) t₁⇒t₂ ⟩
    Γ ⊢ sndʷ p q A B t₁ ⇒ sndʷ p q A B t₂ ∷
      B [ fstʷ p (wk1 A) (var x0) ]↑ [ t₁ ]₀     →⟨ flip conv (⊢≡[fstʷ] ⊢t₁) ⟩

    Γ ⊢ sndʷ p q A B t₁ ⇒ sndʷ p q A B t₂ ∷
      B [ fstʷ p A t₁ ]₀                         □

opaque

  -- An equality rule for sndʷ.

  sndʷ-β-≡ :
    Γ »∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σʷ-allowed p q →
    Γ ⊢ sndʷ p q A B (prodʷ p t u) ≡ u ∷ B [ t ]₀
  sndʷ-β-≡ ⊢B ⊢t ⊢u ok = subsetTerm (sndʷ-β-⇒ ⊢B ⊢t ⊢u ok)

opaque

  -- Another equality rule for sndʷ.

  sndʷ-cong :
    Γ ⊢ A₁ ≡ A₂ →
    Γ »∙ A₁ ⊢ B₁ ≡ B₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ Σʷ p , q ▷ A₁ ▹ B₁ →
    Γ ⊢ sndʷ p q A₁ B₁ t₁ ≡ sndʷ p q A₂ B₂ t₂ ∷ B₁ [ fstʷ p A₁ t₁ ]₀
  sndʷ-cong
    {Γ} {A₁} {A₂} {B₁} {B₂} {t₁} {t₂} {p} {q} A₁≡A₂ B₁≡B₂ t₁≡t₂ =
    let _ , ⊢t₁ , _ = wf-⊢≡∷ t₁≡t₂
        _ , ⊢B , ok = inversion-ΠΣ (wf-⊢∷ ⊢t₁)
    in                                           $⟨ prodrec-cong′ (⊢[fstʷ-0]↑≡[fstʷ-0]↑ A₁≡A₂ B₁≡B₂ ok)
                                                      t₁≡t₂ (refl (⊢0∷[fstʷ-0]↑[1,0]↑² ⊢B ok)) ⟩
    Γ ⊢ sndʷ p q A₁ B₁ t₁ ≡ sndʷ p q A₂ B₂ t₂ ∷
      B₁ [ fstʷ p (wk1 A₁) (var x0) ]↑ [ t₁ ]₀   →⟨ flip conv (⊢≡[fstʷ] ⊢t₁) ⟩

    Γ ⊢ sndʷ p q A₁ B₁ t₁ ≡ sndʷ p q A₂ B₂ t₂ ∷
      B₁ [ fstʷ p A₁ t₁ ]₀                       □

------------------------------------------------------------------------
-- A positive result related to η-rules for Σʷ

opaque
  unfolding Σʷ-η-prodʷ-fstʷ-sndʷ

  -- If Σʷ-allowed p q holds for some p and q, and equality reflection
  -- is not allowed, then a certain definitional η-rule for Σʷ, fstʷ
  -- and sndʷ does not hold in general, see
  -- Definition.Typed.Consequences.Admissible.Sigma.¬-Σʷ-η-prodʷ-fstʷ-sndʷ.
  -- However, the corresponding propositional η-rule does hold.

  ⊢Σʷ-η-prodʷ-fstʷ-sndʷ :
    Γ ⊢ t ∷ Σʷ p , q ▷ A ▹ B →
    Γ ⊢ Σʷ-η-prodʷ-fstʷ-sndʷ p q A B t ∷
      Id (Σʷ p , q ▷ A ▹ B) (prodʷ p (fstʷ p A t) (sndʷ p q A B t)) t
  ⊢Σʷ-η-prodʷ-fstʷ-sndʷ {t} {p} {q} {A} {B} ⊢t =
    let pair         = prodʷ p (var x1) (var x0)
        ⊢ΣAB         = wf-⊢∷ ⊢t
        ⊢A , ⊢B , ok = inversion-ΠΣ ⊢ΣAB
        ⊢B′          = W.wk
                         (liftʷ (step (step id)) $
                          W.wk (stepʷ (step id) ⊢B) ⊢A)
                         ⊢B
        ⊢B″          = W.wk (liftʷ (step id) (wk₁ ⊢ΣAB ⊢A)) ⊢B
        ⊢₁           = PE.subst (_⊢_∷_ _ _) (wk-comp _ _ _) $ var₁ ⊢B
        ⊢₀           = PE.subst (_⊢_∷_ _ _)
                         (PE.sym $ wkSingleSubstWk1 B) $
                       var₀ ⊢B
        eq₁          =
          wk1 A [ pair ]↑²       ≡⟨ wk1-[][]↑ 2 ⟩
          wk2 A                  ≡⟨ wk-comp _ _ _ ⟩
          wk (step (step id)) A  ∎
        eq₂ =
          wk (lift (step id)) B
            [ liftSubst (consSubst (wk1Subst (wk1Subst idSubst)) pair) ]   ≡⟨ subst-wk B ⟩

          B [ liftSubst (consSubst (wk1Subst (wk1Subst idSubst)) pair) ₛ•
              lift (step id) ]                                             ≡⟨ (flip substVar-to-subst B λ where
                                                                                 x0     → PE.refl
                                                                                 (_ +1) → PE.refl) ⟩

          B [ toSubst (lift (step (step id))) ]                            ≡˘⟨ wk≡subst _ _ ⟩

          wk (lift (step (step id))) B                                     ∎
    in
    PE.subst (_⊢_∷_ _ _)
      (Id (Σʷ p , q ▷ wk1 A ▹ wk (lift (step id)) B)
         (prodʷ p (fstʷ p (wk1 A) (var x0))
            (sndʷ p q (wk1 A) (wk (lift (step id)) B) (var x0)))
         (var x0)
         [ t ]₀                                                     ≡⟨ PE.cong
                                                                         (λ x →
                                                                            Id (Σʷ p , q ▷ wk1 A [ t ]₀ ▹
                                                                                (wk (lift (step id)) B [ liftSubst (sgSubst t) ]))
                                                                               x t) $
                                                                       PE.cong₂ (prodʷ p)
                                                                         (fstʷ-[] (wk1 A) (var x0))
                                                                         (sndʷ-[] (wk (lift (step id)) B) (var x0)) ⟩
       Id
         (Σʷ p , q ▷ wk1 A [ t ]₀ ▹
          (wk (lift (step id)) B [ liftSubst (sgSubst t) ]))
         (prodʷ p (fstʷ p (wk1 A [ t ]₀) t)
            (sndʷ p q (wk1 A [ t ]₀)
               (wk (lift (step id)) B [ liftSubst (sgSubst t) ])
               t))
         t                                                          ≡⟨ PE.cong₂
                                                                         (λ A B →
                                                                            Id (Σʷ p , q ▷ A ▹ B) (prodʷ p (fstʷ p A t) (sndʷ p q A B t)) t)
                                                                         (wk1-sgSubst _ _)
                                                                         (PE.trans (subst-wk B) $
                                                                          PE.trans
                                                                            (flip substVar-to-subst B λ where
                                                                               x0     → PE.refl
                                                                               (_ +1) → PE.refl) $
                                                                          subst-id _) ⟩
       Id (Σʷ p , q ▷ A ▹ B)
         (prodʷ p (fstʷ p A t) (sndʷ p q A B t)) t                  ∎) $
    prodrecⱼ′
      (Idⱼ′
         (prodⱼ ⊢B″ (fstʷⱼ (var₀ ⊢ΣAB)) (sndʷⱼ (var₀ ⊢ΣAB)) ok)
         (var₀ ⊢ΣAB))
      ⊢t
      (rflⱼ′
         (prodʷ p (fstʷ p (wk1 A) (var x0) [ pair ]↑²)
            (sndʷ p q (wk1 A) (wk (lift (step id)) B) (var x0)
               [ pair ]↑²)                                           ≡⟨ PE.cong₂ (prodʷ p)
                                                                          (fstʷ-[] (wk1 A) (var x0))
                                                                          (sndʷ-[] (wk (lift (step id)) B) (var x0)) ⟩⊢≡
          prodʷ p (fstʷ p (wk1 A [ pair ]↑²) pair)
            (sndʷ p q (wk1 A [ pair ]↑²)
               (wk (lift (step id)) B
                  [ liftSubst $
                    consSubst (wk1Subst (wk1Subst idSubst)) pair ])
               pair)                                                 ≡⟨ PE.cong₂ (λ A B → prodʷ _ (fstʷ _ A _) (sndʷ _ _ A B _)) eq₁ eq₂ ⟩⊢≡

          prodʷ p (fstʷ p (wk (step (step id)) A) pair)
            (sndʷ p q (wk (step (step id)) A)
               (wk (lift (step (step id))) B) pair)                  ≡⟨ PE.subst (_⊢_≡_∷_ _ _ _)
                                                                          (PE.sym $ PE.cong₂ (Σʷ _ , _ ▷_▹_) eq₁ eq₂) $
                                                                        prod-cong ⊢B′
                                                                          (fstʷ-β-≡ ⊢B′ ⊢₁ ⊢₀ ok)
                                                                          (conv (sndʷ-β-≡ ⊢B′ ⊢₁ ⊢₀ ok)
                                                                             (sym (substTypeEq (refl ⊢B′) (fstʷ-β-≡ ⊢B′ ⊢₁ ⊢₀ ok))))
                                                                          ok ⟩⊢∎

          pair                                                       ∎))
    where
    open TmR

------------------------------------------------------------------------
-- Typing rules for prodrec⟨_⟩

opaque
  unfolding prodrec⟨_⟩

  -- A typing rule for prodrec⟨_⟩.

  ⊢prodrec⟨⟩ :
    Γ »∙ Σ⟨ s ⟩ p , q′ ▷ A ▹ B ⊢ C →
    Γ ⊢ t ∷ Σ⟨ s ⟩ p , q′ ▷ A ▹ B →
    Γ »∙ A »∙ B ⊢ u ∷ C [ prod s p (var x1) (var x0) ]↑² →
    Γ ⊢ prodrec⟨ s ⟩ r p q C t u ∷ C [ t ]₀
  ⊢prodrec⟨⟩ {s = 𝕨} = prodrecⱼ′
  ⊢prodrec⟨⟩ {s = 𝕤} = prodrecˢⱼ

opaque
  unfolding prodrec⟨_⟩

  -- An equality rule for prodrec⟨_⟩.

  prodrec⟨⟩-β :
    (s PE.≡ 𝕨 → Γ »∙ Σ⟨ s ⟩ p , q′ ▷ A ▹ B ⊢ C) →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Γ »∙ A »∙ B ⊢ v ∷ C [ prod s p (var x1) (var x0) ]↑² →
    (s PE.≡ 𝕤 → Σ-allowed s p q′) →
    Γ ⊢ prodrec⟨ s ⟩ r p q C (prod s p t u) v ≡ v [ t , u ]₁₀ ∷
      C [ prod s p t u ]₀
  prodrec⟨⟩-β {s = 𝕨} ⊢C ⊢t ⊢u ⊢v _ =
    prodrec-β-≡ (⊢C PE.refl) ⊢t ⊢u ⊢v
  prodrec⟨⟩-β {s = 𝕤} {C} _  ⊢t ⊢u ⊢v ok =
    prodrecˢ-β C ⊢t ⊢u ⊢v (ok PE.refl)

opaque
  unfolding prodrec⟨_⟩

  -- Another equality rule for prodrec⟨_⟩.

  prodrec⟨⟩-cong :
    Γ »∙ Σ⟨ s ⟩ p , q′ ▷ A ▹ B ⊢ C₁ ≡ C₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ Σ⟨ s ⟩ p , q′ ▷ A ▹ B →
    Γ »∙ A »∙ B ⊢ u₁ ≡ u₂ ∷ C₁ [ prod s p (var x1) (var x0) ]↑² →
    Γ ⊢ prodrec⟨ s ⟩ r p q C₁ t₁ u₁ ≡
      prodrec⟨ s ⟩ r p q C₂ t₂ u₂ ∷ C₁ [ t₁ ]₀
  prodrec⟨⟩-cong {s = 𝕨} = prodrec-cong′
  prodrec⟨⟩-cong {s = 𝕤} = prodrecˢ-cong ∘→ proj₁ ∘→ wf-⊢≡

------------------------------------------------------------------------
-- Typing rules for fst⟨_⟩

opaque
  unfolding fst⟨_⟩

  -- A typing rule for fst⟨_⟩.

  ⊢fst⟨⟩ :
    Γ ⊢ t ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B →
    Γ ⊢ fst⟨ s ⟩ p A t ∷ A
  ⊢fst⟨⟩ {s = 𝕤} = fstⱼ′
  ⊢fst⟨⟩ {s = 𝕨} = fstʷⱼ

opaque
  unfolding fst⟨_⟩

  -- A reduction rule for fst⟨_⟩.

  fst⟨⟩-β-⇒ :
    Γ »∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σ-allowed s p q →
    Γ ⊢ fst⟨ s ⟩ p A (prod s p t u) ⇒ t ∷ A
  fst⟨⟩-β-⇒ {s = 𝕤} = Σ-β₁-⇒
  fst⟨⟩-β-⇒ {s = 𝕨} = fstʷ-β-⇒

opaque
  unfolding fst⟨_⟩

  -- Another reduction rule for fst⟨_⟩.

  fst⟨⟩-subst :
    Γ ⊢ t₁ ⇒ t₂ ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B →
    Γ ⊢ fst⟨ s ⟩ p A t₁ ⇒ fst⟨ s ⟩ p A t₂ ∷ A
  fst⟨⟩-subst {s = 𝕤} = fst-subst′
  fst⟨⟩-subst {s = 𝕨} = fstʷ-subst

opaque
  unfolding fst⟨_⟩

  -- An equality rule for fst⟨_⟩.

  fst⟨⟩-β-≡ :
    Γ »∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σ-allowed s p q →
    Γ ⊢ fst⟨ s ⟩ p A (prod s p t u) ≡ t ∷ A
  fst⟨⟩-β-≡ {s = 𝕤} = Σ-β₁-≡
  fst⟨⟩-β-≡ {s = 𝕨} = fstʷ-β-≡

opaque
  unfolding fst⟨_⟩

  -- Another equality rule for fst⟨_⟩.

  fst⟨⟩-cong :
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ Σ⟨ s ⟩ p , q ▷ A₁ ▹ B₁ →
    Γ ⊢ fst⟨ s ⟩ p A₁ t₁ ≡ fst⟨ s ⟩ p A₂ t₂ ∷ A₁
  fst⟨⟩-cong {s = 𝕤} = λ _ → fst-cong′
  fst⟨⟩-cong {s = 𝕨} = fstʷ-cong

------------------------------------------------------------------------
-- Typing rules for snd⟨_⟩

opaque
  unfolding fst⟨_⟩ snd⟨_⟩

  -- A typing rule for snd⟨_⟩.

  ⊢snd⟨⟩ :
    Γ ⊢ t ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B →
    Γ ⊢ snd⟨ s ⟩ p q A B t ∷ B [ fst⟨ s ⟩ p A t ]₀
  ⊢snd⟨⟩ {s = 𝕤} = sndⱼ′
  ⊢snd⟨⟩ {s = 𝕨} = sndʷⱼ

opaque
  unfolding fst⟨_⟩ snd⟨_⟩

  -- A reduction rule for snd⟨_⟩.

  snd⟨⟩-β-⇒ :
    Γ »∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σ-allowed s p q →
    Γ ⊢ snd⟨ s ⟩ p q A B (prod s p t u) ⇒ u ∷ B [ t ]₀
  snd⟨⟩-β-⇒ {s = 𝕤} = Σ-β₂-⇒
  snd⟨⟩-β-⇒ {s = 𝕨} = sndʷ-β-⇒

opaque
  unfolding fst⟨_⟩ snd⟨_⟩

  -- Another reduction rule for snd⟨_⟩.

  snd⟨⟩-subst :
    Γ ⊢ t₁ ⇒ t₂ ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B →
    Γ ⊢ snd⟨ s ⟩ p q A B t₁ ⇒ snd⟨ s ⟩ p q A B t₂ ∷
      B [ fst⟨ s ⟩ p A t₁ ]₀
  snd⟨⟩-subst {s = 𝕤} = snd-subst′
  snd⟨⟩-subst {s = 𝕨} = sndʷ-subst

opaque
  unfolding fst⟨_⟩ snd⟨_⟩

  -- An equality rule for snd⟨_⟩.

  snd⟨⟩-β-≡ :
    Γ »∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σ-allowed s p q →
    Γ ⊢ snd⟨ s ⟩ p q A B (prod s p t u) ≡ u ∷ B [ t ]₀
  snd⟨⟩-β-≡ {s = 𝕤} = Σ-β₂-≡
  snd⟨⟩-β-≡ {s = 𝕨} = sndʷ-β-≡

opaque
  unfolding fst⟨_⟩ snd⟨_⟩

  -- Another equality rule for snd⟨_⟩.

  snd⟨⟩-cong :
    Γ ⊢ A₁ ≡ A₂ →
    Γ »∙ A₁ ⊢ B₁ ≡ B₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ Σ⟨ s ⟩ p , q ▷ A₁ ▹ B₁ →
    Γ ⊢ snd⟨ s ⟩ p q A₁ B₁ t₁ ≡ snd⟨ s ⟩ p q A₂ B₂ t₂ ∷
      B₁ [ fst⟨ s ⟩ p A₁ t₁ ]₀
  snd⟨⟩-cong {s = 𝕤} = λ _ _ → snd-cong′
  snd⟨⟩-cong {s = 𝕨} = sndʷ-cong

------------------------------------------------------------------------
-- A propositional η-rule for fst⟨_⟩ and snd⟨_⟩

opaque
  unfolding Σ⟨_⟩-η-prod-fst-snd fst⟨_⟩ snd⟨_⟩

  -- A propositional η-rule.

  ⊢Σ⟨⟩-η-prod-fst-snd :
    Γ ⊢ t ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B →
    Γ ⊢ Σ⟨ s ⟩-η-prod-fst-snd p q A B t ∷
      Id (Σ⟨ s ⟩ p , q ▷ A ▹ B)
        (prod s p (fst⟨ s ⟩ p A t) (snd⟨ s ⟩ p q A B t)) t
  ⊢Σ⟨⟩-η-prod-fst-snd {s = 𝕤} = rflⱼ′ ∘→ Σ-η-prod-fst-snd
  ⊢Σ⟨⟩-η-prod-fst-snd {s = 𝕨} = ⊢Σʷ-η-prodʷ-fstʷ-sndʷ

------------------------------------------------------------------------
-- An inversion lemma

opaque

  -- An inversion lemma for fstʷ.

  inversion-fstʷ :
    Γ ⊢ fstʷ p A t ∷ C →
    ∃₂ λ q B → Γ ⊢ t ∷ Σʷ p , q ▷ A ▹ B × Γ ⊢ C ≡ A
  inversion-fstʷ {p} {A} {t} ⊢t₁ =
    case inversion-prodrec ⊢t₁ of λ
      (F , G , q , _ , ⊢G , ⊢wk1A , ⊢t , ⊢x₁ , C≡) →
    case inversion-var ⊢x₁ of λ {
      (_ , there here , ≡wk2F) →
    case PE.subst (_ ⊢ _ ≡_) (wk1-sgSubst A t) C≡ of λ
      C≡A →
    case PE.subst (_ ⊢_≡ _) (wk1-[][]↑ {t = A} 2) ≡wk2F of λ
      wk2A≡wk2F →
    case fstʷⱼ ⊢t of λ
      ⊢t₁ →
    case sndʷⱼ ⊢t of λ
      ⊢t₂ →
    case refl-⊢ˢʷ≡∷
           {σ = consSubst (sgSubst (fstʷ p F t)) (sndʷ p q F G t)}
           (→⊢ˢʷ∷∙ (⊢ˢʷ∷-sgSubst ⊢t₁) ⊢t₂) of λ
      [σ] →
    case subst-⊢≡ wk2A≡wk2F [σ] of λ
      A≡F′ →
    case PE.subst₂ (_ ⊢_≡_)
                   (PE.trans (wk2-tail A) (subst-id A))
                   (PE.trans (wk2-tail F) (subst-id F))
                   A≡F′ of λ
      A≡F →
    case inversion-ΠΣ (wf-⊢∷ ⊢t) of λ
      (_ , _ , Σ-ok) →
    q , G , conv ⊢t (ΠΣ-cong (sym A≡F) (refl ⊢G) Σ-ok) , C≡A  }

------------------------------------------------------------------------
-- Some lemmas related to Σʰ⟨_⟩

opaque
  unfolding ΠΣʰ prodʰ

  -- An equality rule for prodʰ.

  prodʰ-cong :
    Σ-allowed s p q →
    Γ ⊢ l₁ ∷Level →
    Γ ⊢ l₂ ∷Level →
    Γ »∙ A ⊢ B →
    Γ ⊢ t₁ ≡ t₂ ∷ A →
    Γ ⊢ u₁ ≡ u₂ ∷ B [ t₁ ]₀ →
    Γ ⊢ prodʰ s p t₁ u₁ ≡ prodʰ s p t₂ u₂ ∷ Σʰ⟨ s ⟩ p q l₁ l₂ A B
  prodʰ-cong ok ⊢l₁ ⊢l₂ ⊢B t₁≡t₂ u₁≡u₂ =
    let ⊢A          = ⊢∙→⊢ (wf ⊢B)
        _ , ⊢t₁ , _ = wf-⊢≡∷ t₁≡t₂
    in
    prod-cong (Liftⱼ (wkLevel₁ (Liftⱼ ⊢l₂ ⊢A) ⊢l₁) (lower₀Type ⊢l₂ ⊢B))
      (lift-cong ⊢l₂ t₁≡t₂)
      (lift-cong
         (PE.subst (_⊢_∷Level _) (PE.sym $ wk1-sgSubst _ _) ⊢l₁)
         (conv u₁≡u₂ (sym (lower₀[lift]₀ ⊢B ⊢t₁))))
      ok

opaque

  -- A typing rule for prodʰ.

  ⊢prodʰ :
    Σ-allowed s p q →
    Γ ⊢ l₁ ∷Level →
    Γ ⊢ l₂ ∷Level →
    Γ »∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Γ ⊢ prodʰ s p t u ∷ Σʰ⟨ s ⟩ p q l₁ l₂ A B
  ⊢prodʰ ok ⊢l₁ ⊢l₂ ⊢B ⊢t ⊢u =
    wf-⊢≡∷ (prodʰ-cong ok ⊢l₁ ⊢l₂ ⊢B (refl ⊢t) (refl ⊢u)) .proj₂ .proj₁

opaque
  unfolding ΠΣʰ fstʰ

  -- An equality rule for fstʰ.

  fstʰ-cong :
    Γ ⊢ t₁ ≡ t₂ ∷ Σʰˢ p q l₁ l₂ A B →
    Γ ⊢ fstʰ p t₁ ≡ fstʰ p t₂ ∷ A
  fstʰ-cong t₁≡t₂ = lower-cong (fst-cong′ t₁≡t₂)

opaque

  -- A typing rule for fstʰ.

  ⊢fstʰ :
    Γ ⊢ t ∷ Σʰˢ p q l₁ l₂ A B →
    Γ ⊢ fstʰ p t ∷ A
  ⊢fstʰ ⊢t = wf-⊢≡∷ (fstʰ-cong (refl ⊢t)) .proj₂ .proj₁

opaque
  unfolding ΠΣʰ fstʰ sndʰ lower₀

  -- An equality rule for sndʰ.

  sndʰ-cong :
    Γ ⊢ t₁ ≡ t₂ ∷ Σʰˢ p q l₁ l₂ A B →
    Γ ⊢ sndʰ p t₁ ≡ sndʰ p t₂ ∷ B [ fstʰ p t₁ ]₀
  sndʰ-cong {B} t₁≡t₂ =
    PE.subst (_⊢_≡_∷_ _ _ _) ([]↑-[]₀ B) $
    lower-cong (snd-cong′ t₁≡t₂)

opaque

  -- A typing rule for sndʰ.

  ⊢sndʰ :
    Γ ⊢ t ∷ Σʰˢ p q l₁ l₂ A B →
    Γ ⊢ sndʰ p t ∷ B [ fstʰ p t ]₀
  ⊢sndʰ ⊢t = wf-⊢≡∷ (sndʰ-cong (refl ⊢t)) .proj₂ .proj₁

opaque
  unfolding prodʰ fstʰ

  -- A β-rule for fstʰ.

  Σʰ-β₁ :
    Σˢ-allowed p q →
    Γ »∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Γ ⊢ fstʰ p (prodʰˢ p t u) ≡ t ∷ A
  Σʰ-β₁ {p} {t} {u} ok ⊢B ⊢t ⊢u =
    let ⊢A = ⊢∙→⊢ (wf ⊢B)
        ⊢0 = ⊢zeroᵘ (wf ⊢A)
    in
    lower (fst p (prodˢ p (lift t) (lift u)))  ≡⟨ lower-cong $
                                                  Σ-β₁-≡ (Liftⱼ (wkLevel₁ (Liftⱼ ⊢0 ⊢A) ⊢0) (lower₀Type ⊢0 ⊢B))
                                                    (liftⱼ′ ⊢0 ⊢t)
                                                    (liftⱼ′ ⊢0 (conv ⊢u (sym (lower₀[lift]₀ ⊢B ⊢t))))
                                                    ok ⟩⊢
    lower (lift t)                             ≡⟨ Lift-β′ ⊢t ⟩⊢∎
    t                                          ∎
    where
    open TmR

opaque
  unfolding prodʰ fstʰ sndʰ lower₀

  -- A β-rule for sndʰ.

  Σʰ-β₂ :
    Σˢ-allowed p q →
    Γ »∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Γ ⊢ sndʰ p (prodʰˢ p t u) ≡ u ∷ B [ t ]₀
  Σʰ-β₂ {p} {B} {t} {u} ok ⊢B ⊢t ⊢u =
    let ⊢0 = ⊢zeroᵘ (wfTerm ⊢t) in
    lower (snd p (prodˢ p (lift t) (lift u)))  ≡⟨ conv
                                                    (lower-cong $
                                                     Σ-β₂-≡ (Liftⱼ (wkLevel₁ (Liftⱼ ⊢0 (⊢∙→⊢ (wf ⊢B))) ⊢0) (lower₀Type ⊢0 ⊢B))
                                                       (liftⱼ′ ⊢0 ⊢t)
                                                       (liftⱼ′ ⊢0 (conv ⊢u (sym (lower₀[lift]₀ ⊢B ⊢t))))
                                                       ok)
                                                    (lower₀[lift]₀ ⊢B ⊢t) ⟩⊢
    lower (lift u)                             ≡⟨ Lift-β′ ⊢u ⟩⊢∎
    u                                          ∎
    where
    open TmR

opaque
  unfolding ΠΣʰ fstʰ sndʰ lower₀

  -- An η-rule for Σʰˢ.

  Σʰ-η :
    Γ »∙ A ⊢ B →
    Γ ⊢ t ∷ Σʰˢ p q l₁ l₂ A B →
    Γ ⊢ u ∷ Σʰˢ p q l₁ l₂ A B →
    Γ ⊢ fstʰ p t ≡ fstʰ p u ∷ A →
    Γ ⊢ sndʰ p t ≡ sndʰ p u ∷ B [ fstʰ p t ]₀ →
    Γ ⊢ t ≡ u ∷ Σʰˢ p q l₁ l₂ A B
  Σʰ-η {B} {t} {p} {l₁} {u} ⊢B ⊢t ⊢u fstʰ≡fstʰ sndʰ≡sndʰ =
    let ⊢l₁ , ⊢l₂ , _ = inversion-ΠΣʰ-⊢ {B = B} (wf-⊢∷ ⊢t)
        ⊢l₁           = PE.subst (_⊢_∷Level _) (wk1-sgSubst _ _) $
                        substLevel ⊢l₁ (wf-⊢≡∷ fstʰ≡fstʰ .proj₂ .proj₁)
        fst-t≡fst-u   = Lift-η′ (fstⱼ′ ⊢t) (fstⱼ′ ⊢u) fstʰ≡fstʰ
    in
    Σ-η′ ⊢t ⊢u fst-t≡fst-u
      (Lift-η′ (sndⱼ′ ⊢t)
         (conv (sndⱼ′ ⊢u)
            (Lift (wk1 l₁ [ fst p u ]₀) (lower₀ B [ fst p u ]₀)  ≡⟨ PE.cong₂ Lift (wk1-sgSubst _ _) PE.refl ⟩⊢≡
             Lift l₁ (lower₀ B [ fst p u ]₀)                     ≡˘⟨ Lift-cong (refl-⊢≡∷L ⊢l₁) $
                                                                     substTypeEq (refl (lower₀Type ⊢l₂ ⊢B)) fst-t≡fst-u ⟩⊢∎≡
             Lift l₁ (lower₀ B [ fst p t ]₀)                     ≡˘⟨ PE.cong (flip Lift _) (wk1-sgSubst _ _) ⟩
             Lift (wk1 l₁ [ fst p t ]₀) (lower₀ B [ fst p t ]₀)  ∎))
         (PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym ([]↑-[]₀ B)) sndʰ≡sndʰ))
    where
    open TyR

private

  -- Some lemmas used in the lemmas about prodrecʰ⟨_⟩ below.

  opaque

    wk1-lower₀ :
      wk1 (lower₀ t) PE.≡
      wk (lift (stepn id 2)) t [ lower (var x1) ]₀
    wk1-lower₀ {t} =
      wk1 (lower₀ t)                                               ≡⟨ wk-lower₀ ⟩
      t [ 2 ][ lower (var x1) ]↑                                   ≡⟨ (flip substVar-to-subst t λ where
                                                                         x0     → PE.refl
                                                                         (_ +1) → PE.refl) ⟩
      t [ sgSubst (lower (var x1)) ∘→ wkVar (lift (stepn id 2)) ]  ≡˘⟨ subst-wk t ⟩
      wk (lift (stepn id 2)) t [ lower (var x1) ]₀                 ∎

  opaque
    unfolding ΠΣʰ prodʰ

    ⊢prodʰ-lower-lower≡∷ :
      Σ-allowed s p q →
      Γ »∙ A ⊢ B →
      Γ ⊢ t ∷ Lift l₂ A →
      Γ ⊢ u ∷ Lift l₁ (B [ lower t ]₀) →
      Γ ⊢ prodʰ s p (lower t) (lower u) ≡ prod s p t u ∷
        Σʰ⟨ s ⟩ p q l₁ l₂ A B
    ⊢prodʰ-lower-lower≡∷ {B} {t} {l₁} ok ⊢B ⊢t ⊢u =
      let ⊢l₁ , _  = inversion-Lift (wf-⊢∷ ⊢u)
          ⊢l₂ , ⊢A = inversion-Lift (wf-⊢∷ ⊢t)
      in
      prod-cong
        (Liftⱼ (wkLevel₁ (Liftⱼ ⊢l₂ ⊢A) ⊢l₁) (lower₀Type ⊢l₂ ⊢B))
        (⊢lift-lower≡∷ ⊢t)
        (⊢lift-lower≡∷ $
         conv ⊢u
           (Lift l₁ (B [ lower t ]₀)                      ≡˘⟨ Lift-cong (refl-⊢≡∷L ⊢l₁) (lower₀[lift]₀ ⊢B (lowerⱼ ⊢t)) ⟩⊢∎≡
            Lift l₁ (lower₀ B [ lift (lower t) ]₀)        ≡˘⟨ PE.cong (flip Lift _) $ wk1-sgSubst _ _ ⟩
            Lift (wk1 l₁) (lower₀ B) [ lift (lower t) ]₀  ∎))
        ok
      where
      open TyR

  opaque

    ⊢prodʰ-lower-1-lower-0≡∷ :
      Σ-allowed s p q →
      Γ ⊢ l₁ ∷Level →
      Γ ⊢ l₂ ∷Level →
      Γ »∙ A ⊢ B →
      Γ »∙ Lift l₂ A »∙ Lift (wk1 l₁) (lower₀ B) ⊢
        prodʰ s p (lower (var x1)) (lower (var x0)) ≡
        prod s p (var x1) (var x0) ∷ wk2 (Σʰ⟨ s ⟩ p q l₁ l₂ A B)
    ⊢prodʰ-lower-1-lower-0≡∷ ok ⊢l₁ ⊢l₂ ⊢B =
      let ⊢A             = ⊢∙→⊢ (wf ⊢B)
          ⊢Lift-A        = Liftⱼ ⊢l₂ ⊢A
          ⊢Lift-lower₀-B = Liftⱼ (wkLevel₁ ⊢Lift-A ⊢l₁) (lower₀Type ⊢l₂ ⊢B)
      in
      PE.subst (_⊢_≡_∷_ _ _ _)
        (PE.sym $ PE.trans wk[]≡wk[]′ wk-ΠΣʰ) $
      ⊢prodʰ-lower-lower≡∷ ok
        (W.wk
           (liftʷ (step (step id)) $
            W.wk (stepʷ (step id) ⊢Lift-lower₀-B) ⊢A)
           ⊢B)
        (PE.subst (_⊢_∷_ _ _) wk[]≡wk[]′ $
         var₁ ⊢Lift-lower₀-B)
        (PE.subst (_⊢_∷_ _ _)
           (PE.cong₂ Lift wk[]≡wk[]′ wk1-lower₀) $
         var₀ ⊢Lift-lower₀-B)

  opaque
    unfolding prodʰ replace₂

    prodrecʰ⟨⟩-eq₁ :
      Σ-allowed s p q →
      Γ ⊢ l₁ ∷Level →
      Γ »∙ A ⊢ B →
      Γ »∙ Σʰ⟨ s ⟩ p q l₁ l₂ A B ⊢ C →
      Γ »∙ Lift l₂ A »∙ Lift (wk1 l₁) (lower₀ B) ⊢
        C [ 2 ][ prodʰ s p (var x1) (var x0) ]↑
          [ replace₂ (lower (var x1)) (lower (var x0)) ] ≡
        C [ prod s p (var x1) (var x0) ]↑²
    prodrecʰ⟨⟩-eq₁ {s} {p} {C} ok ⊢l₁ ⊢B ⊢C =
      let _ , ⊢l₂ , _ = inversion-ΠΣʰ-⊢ (⊢∙→⊢ (wf ⊢C)) in
      C [ 2 ][ prodʰ s p (var x1) (var x0) ]↑
        [ replace₂ (lower (var x1)) (lower (var x0)) ]     ≡⟨ [2][]↑-[replace₂] C ⟩⊢≡

      C [ prodʰ s p (lower (var x1)) (lower (var x0)) ]↑²  ≡⟨ subst↑²TypeEq (refl ⊢C) $
                                                              ⊢prodʰ-lower-1-lower-0≡∷ ok ⊢l₁ ⊢l₂ ⊢B ⟩⊢∎
      C [ prod s p (var x1) (var x0) ]↑²                   ∎
      where
      open TyR

  opaque
    unfolding prodʰ

    prodrecʰ⟨⟩-eq₂ :
      Σ-allowed s p q →
      Γ ⊢ l₁ ∷Level →
      Γ »∙ A ⊢ B →
      Γ »∙ Σʰ⟨ s ⟩ p q l₁ l₂ A B ⊢ C →
      Γ ⊢ t ∷ A →
      Γ ⊢ u ∷ lower₀ B [ lift t ]₀ →
      Γ ⊢
        C [ 2 ][ prodʰ s p (var x1) (var x0) ]↑
          [ lower (lift t) , lower (lift u) ]₁₀ ≡
        C [ prodʰ s p t u ]₀
    prodrecʰ⟨⟩-eq₂ {s} {p} {B} {C} {t} {u} ok ⊢l₁ ⊢B ⊢C ⊢t ⊢u =
      let _ , ⊢l₂ , _ = inversion-ΠΣʰ-⊢ (⊢∙→⊢ (wf ⊢C)) in
      C [ 2 ][ prodʰ s p (var x1) (var x0) ]↑
        [ lower (lift t) , lower (lift u) ]₁₀             ≡⟨ [][]↑-[,⇑] 0 C ⟩⊢≡

      C [ prodʰ s p (lower (lift t)) (lower (lift u)) ]₀  ≡⟨ substTypeEq (refl ⊢C) $
                                                             prodʰ-cong ok ⊢l₁ ⊢l₂ ⊢B (Lift-β′ ⊢t) $
                                                             conv (Lift-β (substType (lower₀Type ⊢l₂ ⊢B) (liftⱼ′ ⊢l₂ ⊢t)) ⊢u)
                                                               (
        lower₀ B [ lift t ]₀                                    ≡⟨ lower₀[lift]₀ ⊢B ⊢t ⟩⊢
        B [ t ]₀                                                ≡˘⟨ substTypeEq (refl ⊢B) (Lift-β′ ⊢t) ⟩⊢∎
        B [ lower (lift t) ]₀                                   ∎) ⟩⊢∎

      C [ prodʰ s p t u ]₀                                ∎
      where
      open TyR

  opaque

    ⊢ˢʷ∷-replace₂-lower-1-lower-0 :
      Γ ⊢ l₁ ∷Level →
      Γ ⊢ l₂ ∷Level →
      Γ »∙ A ⊢ B →
      Γ .defs » Γ .vars ∙ Lift l₂ A ∙ Lift (wk1 l₁) (lower₀ B) ⊢ˢʷ
        replace₂ (lower (var x1)) (lower (var x0)) ∷ Γ .vars ∙ A ∙ B
    ⊢ˢʷ∷-replace₂-lower-1-lower-0 ⊢l₁ ⊢l₂ ⊢B =
      let ⊢A             = ⊢∙→⊢ (wf ⊢B)
          ⊢Lift-A        = Liftⱼ ⊢l₂ ⊢A
          ⊢Lift-lower₀-B = Liftⱼ (wkLevel₁ ⊢Lift-A ⊢l₁) (lower₀Type ⊢l₂ ⊢B)
      in
      ⊢ˢʷ∷-replace₂
        (lowerⱼ $
         PE.subst (_⊢_∷_ _ _) wk[]≡wk[]′ $
         var₁ ⊢Lift-lower₀-B)
        (lowerⱼ $
         PE.subst (_⊢_∷_ _ _)
           (PE.cong₂ Lift (wk[]≡wk[]′ {k = 2}) wk1-lower₀) $
         var₀ ⊢Lift-lower₀-B)

opaque
  unfolding ΠΣʰ prodʰ prodrecʰ⟨_⟩

  -- An equality rule for prodrecʰ⟨_⟩.

  prodrecʰ⟨⟩-cong :
    Γ »∙ Σʰ⟨ s ⟩ p q′ l₁ l₂ A B ⊢ C₁ ≡ C₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ Σʰ⟨ s ⟩ p q′ l₁ l₂ A B →
    Γ »∙ A »∙ B ⊢ u₁ ≡ u₂ ∷ C₁ [ prodʰ s p (var x1) (var x0) ]↑² →
    Γ ⊢ prodrecʰ⟨ s ⟩ r p q C₁ t₁ u₁ ≡ prodrecʰ⟨ s ⟩ r p q C₂ t₂ u₂ ∷
      C₁ [ t₁ ]₀
  prodrecʰ⟨⟩-cong C₁≡C₂ t₁≡t₂ u₁≡u₂ =
    let ⊢B                     = ⊢∙→⊢ (wfEqTerm u₁≡u₂)
        ⊢Σ , ⊢t₁ , _           = wf-⊢≡∷ t₁≡t₂
        ⊢l₁ , ⊢l₂ , _ , _ , ok = inversion-ΠΣʰ-⊢ ⊢Σ
        ⊢l₁                    = PE.subst (_⊢_∷Level _)
                                   (wk1-sgSubst _ _) $
                                 substLevel ⊢l₁ (lowerⱼ (⊢fst⟨⟩ ⊢t₁))
    in
    prodrec⟨⟩-cong C₁≡C₂ t₁≡t₂
      (conv
         (subst-⊢≡∷ u₁≡u₂ $ refl-⊢ˢʷ≡∷ $
          ⊢ˢʷ∷-replace₂-lower-1-lower-0 ⊢l₁ ⊢l₂ ⊢B)
         (prodrecʰ⟨⟩-eq₁ ok ⊢l₁ ⊢B (wf-⊢≡ C₁≡C₂ .proj₁)))

opaque

  -- A typing rule for prodrecʰ⟨_⟩.

  ⊢prodrecʰ⟨⟩ :
    Γ »∙ Σʰ⟨ s ⟩ p q′ l₁ l₂ A B ⊢ C →
    Γ ⊢ t ∷ Σʰ⟨ s ⟩ p q′ l₁ l₂ A B →
    Γ »∙ A »∙ B ⊢ u ∷ C [ prodʰ s p (var x1) (var x0) ]↑² →
    Γ ⊢ prodrecʰ⟨ s ⟩ r p q C t u ∷ C [ t ]₀
  ⊢prodrecʰ⟨⟩ ⊢C ⊢t ⊢u =
    wf-⊢≡∷ (prodrecʰ⟨⟩-cong (refl ⊢C) (refl ⊢t) (refl ⊢u)) .proj₂ .proj₁

opaque
  unfolding ΠΣʰ prodʰ prodrecʰ⟨_⟩

  -- A β-rule for prodrecʰ⟨_⟩.

  prodrecʰ⟨⟩-β :
    Γ »∙ Σʰ⟨ s ⟩ p q′ l₁ l₂ A B ⊢ C →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Γ »∙ A »∙ B ⊢ v ∷ C [ prodʰ s p (var x1) (var x0) ]↑² →
    Γ ⊢ prodrecʰ⟨ s ⟩ r p q C (prodʰ s p t u) v ≡ v [ t , u ]₁₀ ∷
      C [ prodʰ s p t u ]₀
  prodrecʰ⟨⟩-β {s} {p} {C} {t} {u} {v} {r} {q} ⊢C ⊢t ⊢u ⊢v =
    let ⊢B                     = ⊢∙→⊢ (wfTerm ⊢v)
        ⊢l₁ , ⊢l₂ , _ , _ , ok = inversion-ΠΣʰ-⊢ (⊢∙→⊢ (wf ⊢C))
        ⊢l₁                    = PE.subst (_⊢_∷Level _)
                                   (wk1-sgSubst _ _) $
                                 substLevel ⊢l₁ ⊢t
        lower-lift-t≡t         = Lift-β′ ⊢t
        ⊢u′                    = conv ⊢u (sym (lower₀[lift]₀ ⊢B ⊢t))
    in
    prodrec⟨ s ⟩ r p q C (prod s p (lift t) (lift u))
      (v [ replace₂ (lower (var x1)) (lower (var x0)) ])  ≡⟨ prodrec⟨⟩-β (λ _ → ⊢C) (liftⱼ′ ⊢l₂ ⊢t)
                                                               (liftⱼ′ (PE.subst (_⊢_∷Level _) (PE.sym $ wk1-sgSubst _ _) ⊢l₁) ⊢u′)
                                                               (conv (subst-⊢∷ ⊢v $ ⊢ˢʷ∷-replace₂-lower-1-lower-0 ⊢l₁ ⊢l₂ ⊢B)
                                                                  (prodrecʰ⟨⟩-eq₁ ok ⊢l₁ ⊢B ⊢C))
                                                               (λ _ → ok) ⟩⊢
    v [ replace₂ (lower (var x1)) (lower (var x0)) ]
      [ lift t , lift u ]₁₀                               ≡⟨ [replace₂]-[,]₁₀ v ⟩⊢≡

    v [ lower (lift t) , lower (lift u) ]₁₀               ≡⟨ conv
                                                               (subst-⊢≡∷ (refl ⊢v) $
                                                                →⊢ˢʷ≡∷∙ ⊢B (⊢ˢʷ≡∷-sgSubst lower-lift-t≡t) $
                                                                Lift-β′ (conv ⊢u (substTypeEq (refl ⊢B) (sym′ lower-lift-t≡t))))
                                                               (prodrecʰ⟨⟩-eq₂ ok ⊢l₁ ⊢B ⊢C ⊢t ⊢u′) ⟩⊢∎
    v [ t , u ]₁₀                                         ∎
    where
    open TmR
