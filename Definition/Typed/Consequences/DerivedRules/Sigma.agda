------------------------------------------------------------------------
-- Derived rules related to Σ-types
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.DerivedRules.Sigma
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Consequences.DerivedRules.Identity R
open import Definition.Typed.Consequences.DerivedRules.Pi-Sigma R
open import Definition.Typed.Consequences.Inequality R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Reduction R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Term R
open import Definition.Typed.Weakening R as W

open import Definition.Untyped M as U
  hiding (_∷_) renaming (_[_,_] to _[_∣_])
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sigma M as Sigma using (prodrecˢ)

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation

private variable
  n                                           : Nat
  Γ                                           : Con _ _
  A A₁ A₂ B B₁ B₂ C C₁ C₂ t t₁ t₂ u u₁ u₂ v w : Term _
  p q q′ r                                    : M
  s s′                                        : Strength

------------------------------------------------------------------------
-- Some derived rules

-- A variant of the typing rule for prod.

⊢prod :
  Γ ∙ A ⊢ B →
  Γ ⊢ t ∷ A →
  Γ ⊢ u ∷ B [ t ]₀ →
  Σ-allowed s p q →
  Γ ⊢ prod s p t u ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B
⊢prod ⊢B ⊢t = prodⱼ (syntacticTerm ⊢t) ⊢B ⊢t

opaque

  -- A variant of the typing rule for fst.

  fstⱼ′ :
    Γ ⊢ t ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊢ fst p t ∷ A
  fstⱼ′ ⊢t =
    case inversion-ΠΣ (syntacticTerm ⊢t) of λ {
      (⊢A , ⊢B , _) →
    fstⱼ ⊢A ⊢B ⊢t }

opaque

  -- A variant of the typing rule for snd.

  sndⱼ′ :
    Γ ⊢ t ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊢ snd p t ∷ B [ fst p t ]₀
  sndⱼ′ ⊢t =
    case inversion-ΠΣ (syntacticTerm ⊢t) of λ {
      (⊢A , ⊢B , _) →
    sndⱼ ⊢A ⊢B ⊢t }

opaque

  -- A variant of the typing rule for prodrec.

  prodrecⱼ′ :
    Γ ∙ Σʷ p , q′ ▷ A ▹ B ⊢ C →
    Γ ⊢ t ∷ Σʷ p , q′ ▷ A ▹ B →
    Γ ∙ A ∙ B ⊢ u ∷ C [ prodʷ p (var x1) (var x0) ]↑² →
    Γ ⊢ prodrec r p q C t u ∷ C [ t ]₀
  prodrecⱼ′ ⊢C ⊢t ⊢u =
    case inversion-ΠΣ (syntacticTerm ⊢t) of λ {
      (⊢A , ⊢B , ok) →
    prodrecⱼ ⊢A ⊢B ⊢C ⊢t ⊢u ok }

opaque

  -- A variant of prod-cong.

  prod-cong′ :
    Γ ∙ A ⊢ B →
    Γ ⊢ t₁ ≡ t₂ ∷ A →
    Γ ⊢ u₁ ≡ u₂ ∷ B [ t₁ ]₀ →
    Σ-allowed s p q →
    Γ ⊢ prod s p t₁ u₁ ≡ prod s p t₂ u₂ ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B
  prod-cong′ ⊢B t₁≡t₂ =
    prod-cong (syntacticEqTerm t₁≡t₂ .proj₁) ⊢B t₁≡t₂

opaque

  -- A variant of fst-subst.

  fst-subst′ :
    Γ ⊢ t ⇒ u ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊢ fst p t ⇒ fst p u ∷ A
  fst-subst′ t⇒u =
    case inversion-ΠΣ (syntacticTerm (redFirstTerm t⇒u)) of λ {
      (⊢A , ⊢B , _) →
    fst-subst ⊢A ⊢B t⇒u }

opaque

  -- A variant of fst-cong.

  fst-cong′ :
    Γ ⊢ t ≡ u ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊢ fst p t ≡ fst p u ∷ A
  fst-cong′ t≡u =
    case inversion-ΠΣ (syntacticEqTerm t≡u .proj₁) of λ {
      (⊢A , ⊢B , _) →
    fst-cong ⊢A ⊢B t≡u }

opaque

  -- A variant of snd-subst.

  snd-subst′ :
    Γ ⊢ t ⇒ u ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊢ snd p t ⇒ snd p u ∷ B [ fst p t ]₀
  snd-subst′ t⇒u =
    case inversion-ΠΣ (syntacticTerm (redFirstTerm t⇒u)) of λ {
      (⊢A , ⊢B , _) →
    snd-subst ⊢A ⊢B t⇒u }

opaque

  -- A variant of snd-cong.

  snd-cong′ :
    Γ ⊢ t ≡ u ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊢ snd p t ≡ snd p u ∷ B [ fst p t ]₀
  snd-cong′ t≡u =
    case inversion-ΠΣ (syntacticEqTerm t≡u .proj₁) of λ {
      (⊢A , ⊢B , _) →
    snd-cong ⊢A ⊢B t≡u }

opaque

  -- A variant of prodrec-subst.

  prodrec-subst′ :
    Γ ∙ (Σʷ p , q′ ▷ A ▹ B) ⊢ C →
    Γ ∙ A ∙ B ⊢ u ∷ C [ prodʷ p (var x1) (var x0) ]↑² →
    Γ ⊢ t₁ ⇒ t₂ ∷ Σʷ p , q′ ▷ A ▹ B →
    Σʷ-allowed p q′ →
    Γ ⊢ prodrec r p q C t₁ u ⇒ prodrec r p q C t₂ u ∷ C [ t₁ ]₀
  prodrec-subst′ ⊢C ⊢u t₁⇒t₂ =
    case inversion-ΠΣ (syntacticTerm (redFirstTerm t₁⇒t₂)) of λ {
      (⊢A , ⊢B , _) →
    prodrec-subst ⊢A ⊢B ⊢C ⊢u t₁⇒t₂ }

opaque

  -- A variant of prodrec-cong.

  prodrec-cong′ :
    Γ ∙ (Σʷ p , q′ ▷ A ▹ B) ⊢ C₁ ≡ C₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ Σʷ p , q′ ▷ A ▹ B →
    Γ ∙ A ∙ B ⊢ u₁ ≡ u₂ ∷ C₁ [ prodʷ p (var x1) (var x0) ]↑² →
    Γ ⊢ prodrec r p q C₁ t₁ u₁ ≡ prodrec r p q C₂ t₂ u₂ ∷ C₁ [ t₁ ]₀
  prodrec-cong′ C₁≡C₂ t₁≡t₂ u₁≡u₂ =
    case inversion-ΠΣ (syntacticEqTerm t₁≡t₂ .proj₁) of λ {
      (⊢A , ⊢B , ok) →
    prodrec-cong ⊢A ⊢B C₁≡C₂ t₁≡t₂ u₁≡u₂ ok }

opaque

  -- A variant of the reduction rule Σ-β₁.

  Σ-β₁-⇒ :
    Γ ∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σˢ-allowed p q →
    Γ ⊢ fst p (prodˢ p t u) ⇒ t ∷ A
  Σ-β₁-⇒ ⊢B ⊢t ⊢u =
    Σ-β₁ (syntacticTerm ⊢t) ⊢B ⊢t ⊢u PE.refl

opaque

  -- A variant of the equality rule Σ-β₁.

  Σ-β₁-≡ :
    Γ ∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σˢ-allowed p q →
    Γ ⊢ fst p (prodˢ p t u) ≡ t ∷ A
  Σ-β₁-≡ ⊢B ⊢t ⊢u ok =
    subsetTerm (Σ-β₁-⇒ ⊢B ⊢t ⊢u ok)

opaque

  -- A variant of the reduction rule Σ-β₂.

  Σ-β₂-⇒ :
    Γ ∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σˢ-allowed p q →
    Γ ⊢ snd p (prodˢ p t u) ⇒ u ∷ B [ fst p (prodˢ p t u) ]₀
  Σ-β₂-⇒ ⊢B ⊢t ⊢u =
    Σ-β₂ (syntacticTerm ⊢t) ⊢B ⊢t ⊢u PE.refl

opaque

  -- A variant of the equality rule Σ-β₂.

  Σ-β₂-≡ :
    Γ ∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σˢ-allowed p q →
    Γ ⊢ snd p (prodˢ p t u) ≡ u ∷ B [ fst p (prodˢ p t u) ]₀
  Σ-β₂-≡ ⊢B ⊢t ⊢u ok =
    subsetTerm (Σ-β₂-⇒ ⊢B ⊢t ⊢u ok)

opaque

  -- A variant of the reduction rule prodrec-β.

  prodrec-β-⇒ :
    Γ ∙ (Σʷ p , q′ ▷ A ▹ B) ⊢ C →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Γ ∙ A ∙ B ⊢ v ∷ C [ prodʷ p (var x1) (var x0) ]↑² →
    Σʷ-allowed p q′ →
    Γ ⊢ prodrec r p q C (prodʷ p t u) v ⇒ v [ t ∣ u ] ∷
      C [ prodʷ p t u ]₀
  prodrec-β-⇒ ⊢C ⊢t ⊢u ⊢v ok =
    case wf ⊢C of λ {
      (_ ∙ ⊢ΣAB) →
    case inversion-ΠΣ ⊢ΣAB of λ {
      (⊢A , ⊢B , _) →
    prodrec-β ⊢A ⊢B ⊢C ⊢t ⊢u ⊢v PE.refl ok }}

opaque

  -- A variant of the equality rule prodrec-β.

  prodrec-β-≡ :
    Γ ∙ (Σʷ p , q′ ▷ A ▹ B) ⊢ C →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Γ ∙ A ∙ B ⊢ v ∷ C [ prodʷ p (var x1) (var x0) ]↑² →
    Σʷ-allowed p q′ →
    Γ ⊢ prodrec r p q C (prodʷ p t u) v ≡ v [ t ∣ u ] ∷
      C [ prodʷ p t u ]₀
  prodrec-β-≡ ⊢C ⊢t ⊢u ⊢v ok =
    subsetTerm (prodrec-β-⇒ ⊢C ⊢t ⊢u ⊢v ok)

opaque

  -- A variant of Σ-η.

  Σ-η′ :
    Γ ⊢ t ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊢ u ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊢ fst p t ≡ fst p u ∷ A →
    Γ ⊢ snd p t ≡ snd p u ∷ B [ fst p t ]₀ →
    Γ ⊢ t ≡ u ∷ Σˢ p , q ▷ A ▹ B
  Σ-η′ ⊢t =
    case inversion-ΠΣ (syntacticTerm ⊢t) of λ {
      (⊢A , ⊢B , _) →
    Σ-η ⊢A ⊢B ⊢t }

-- An η-rule for strong Σ-types.

Σ-η-prod-fst-snd :
  Γ ⊢ t ∷ Σˢ p , q ▷ A ▹ B →
  Γ ⊢ prodˢ p (fst p t) (snd p t) ≡ t ∷ Σˢ p , q ▷ A ▹ B
Σ-η-prod-fst-snd ⊢t = Σ-η′
  (⊢prod ⊢B ⊢fst ⊢snd ok)
  ⊢t
  (Σ-β₁-≡ ⊢B ⊢fst ⊢snd ok)
  (Σ-β₂-≡ ⊢B ⊢fst ⊢snd ok)
  where
  ⊢B,ok = inversion-ΠΣ (syntacticTerm ⊢t) .proj₂
  ⊢B    = ⊢B,ok .proj₁
  ok    = ⊢B,ok .proj₂
  ⊢fst  = fstⱼ′ ⊢t
  ⊢snd  = sndⱼ′ ⊢t

-- An "inverse" of prod-cong for Σˢ.

prod-cong⁻¹-Σˢ :
  Γ ⊢ prodˢ p t u ≡ prodˢ p v w ∷ Σˢ p , q ▷ A ▹ B →
  (Γ ∙ A ⊢ B) × Γ ⊢ t ≡ v ∷ A × Γ ⊢ u ≡ w ∷ B [ t ]₀ ×
  Σˢ-allowed p q
prod-cong⁻¹-Σˢ
  {Γ = Γ} {p = p} {t = t} {u = u} {v = v} {w = w}
  {q = q} {A = A} {B = B} prod≡prod =
  ⊢B , t≡v , u≡w , ok
  where
  ⊢ΣAB = syntacticEqTerm prod≡prod .proj₁
  ⊢B   = inversion-ΠΣ ⊢ΣAB .proj₂ .proj₁
  ok   = inversion-ΠΣ ⊢ΣAB .proj₂ .proj₂
  ⊢t,u = syntacticEqTerm prod≡prod .proj₂ .proj₁
  ⊢t   = inversion-prod-Σ ⊢t,u .proj₁
  ⊢u   = inversion-prod-Σ ⊢t,u .proj₂ .proj₁
  ⊢v,w = syntacticEqTerm prod≡prod .proj₂ .proj₂
  ⊢v   = inversion-prod-Σ ⊢v,w .proj₁
  ⊢w   = inversion-prod-Σ ⊢v,w .proj₂ .proj₁

  fst-t,u≡t = Σ-β₁-≡ ⊢B ⊢t ⊢u ok

  t≡v =                                                $⟨ prod≡prod ⟩
    Γ ⊢ prodˢ p t u ≡ prodˢ p v w ∷ Σˢ p , q ▷ A ▹ B   →⟨ fst-cong′ ⟩
    Γ ⊢ fst p (prodˢ p t u) ≡ fst p (prodˢ p v w) ∷ A  →⟨ (λ hyp → trans (sym fst-t,u≡t) (trans hyp (Σ-β₁-≡ ⊢B ⊢v ⊢w ok))) ⟩
    Γ ⊢ t ≡ v ∷ A                                      □

  u≡w =                                               $⟨ prod≡prod ⟩
    Γ ⊢ prodˢ p t u ≡ prodˢ p v w ∷ Σˢ p , q ▷ A ▹ B  →⟨ snd-cong′ ⟩

    Γ ⊢ snd p (prodˢ p t u) ≡ snd p (prodˢ p v w) ∷
      B [ fst p (prodˢ p t u) ]₀                       →⟨ (λ hyp → trans
                                                            (sym (Σ-β₂-≡ ⊢B ⊢t ⊢u ok))
                                                               (trans hyp
                                                                  (conv (Σ-β₂-≡ ⊢B ⊢v ⊢w ok)
                                                                     (substTypeEq (refl ⊢B)
                                                                        (fst-cong′ (sym prod≡prod)))))) ⟩

    Γ ⊢ u ≡ w ∷ B [ fst p (prodˢ p t u) ]₀             →⟨ flip _⊢_≡_∷_.conv (substTypeEq (refl ⊢B) fst-t,u≡t) ⟩

    Γ ⊢ u ≡ w ∷ B [ t ]₀                               □

------------------------------------------------------------------------
-- An investigation of to what degree weak Σ-types can emulate strong
-- Σ-types, and vice versa

-- The rest of this module, down to "More derived rules", consists of
-- (parts of) an investigation of to what degree weak Σ-types can
-- emulate strong Σ-types, and vice versa. This investigation was
-- prompted by a question asked by an anonymous reviewer. See also
-- Definition.Untyped.Sigma, which contains some basic definitions,
-- and Graded.Derived.Sigma, which contains properties related to
-- usage. This module contains properties related to typing.

------------------------------------------------------------------------
-- Typing and equality rules for prodrecˢ

private

  -- A lemma used below.

  ⊢[1,0]↑²[fst,snd]≡ :
    Γ ∙ (Σˢ p , q ▷ A ▹ B) ⊢ C →
    Γ ⊢ t ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊢
      C [ prodˢ p (var x1) (var x0) ]↑² [ fst p t ∣ snd p t ] ≡
      C [ t ]₀
  ⊢[1,0]↑²[fst,snd]≡
    {Γ = Γ} {p = p} {q = q} {A = A} {B = B} {C = C} {t = t} ⊢C =
    Γ ⊢ t ∷ Σˢ p , q ▷ A ▹ B                                     →⟨ Σ-η-prod-fst-snd ⟩

    Γ ⊢ prodˢ p (fst p t) (snd p t) ≡ t ∷ Σˢ p , q ▷ A ▹ B       →⟨ substTypeEq (refl ⊢C) ⟩

    Γ ⊢ C [ prodˢ p (fst p t) (snd p t) ]₀ ≡ C [ t ]₀              →⟨ PE.subst (_ ⊢_≡ _) (PE.sym $ [1,0]↑²[,] C) ⟩

    Γ ⊢
      C [ prodˢ p (var x1) (var x0) ]↑² [ fst p t ∣ snd p t ] ≡
      C [ t ]₀                                                    □

-- A typing rule for prodrecˢ.

prodrecˢⱼ :
  Γ ∙ (Σˢ p , q ▷ A ▹ B) ⊢ C →
  Γ ⊢ t ∷ Σˢ p , q ▷ A ▹ B →
  Γ ∙ A ∙ B ⊢ u ∷ C [ prodˢ p (var x1) (var x0) ]↑² →
  Γ ⊢ prodrecˢ p t u ∷ C [ t ]₀
prodrecˢⱼ
  {Γ = Γ} {p = p} {q = q} {A = A} {B = B} {C = C} {t = t} {u = u}
  ⊢C ⊢t ⊢u =                                                 $⟨ fstⱼ′ ⊢t , sndⱼ′ ⊢t ⟩
  Γ ⊢ fst p t ∷ A ×
  Γ ⊢ snd p t ∷ B [ fst p t ]₀                                →⟨ (λ (hyp₁ , hyp₂) →
                                                                   PE.subst (_ ⊢ _ ∷_) (PE.sym (subst-id _)) hyp₁ , hyp₂) ⟩
  Γ ⊢ fst p t ∷ A [ idSubst ] ×
  Γ ⊢ snd p t ∷ B [ fst p t ]₀                                →⟨ (λ (hyp₁ , hyp₂) → (idSubst′ ⊢Γ , hyp₁) , hyp₂) ⟩

  Γ ⊢ˢ
    consSubst (consSubst idSubst (fst p t)) (snd p t) ∷
    Γ ∙ A ∙ B                                                →⟨ flip (substitutionTerm ⊢u) ⊢Γ ⟩

  Γ ⊢
    prodrecˢ p t u ∷
    C [ prodˢ p (var x1) (var x0) ]↑² [ fst p t ∣ snd p t ]  →⟨ flip conv (⊢[1,0]↑²[fst,snd]≡ ⊢C ⊢t) ⟩

  Γ ⊢ prodrecˢ p t u ∷ C [ t ]₀                               □
  where
  ⊢Γ = wfTerm ⊢t

-- An equality rule for prodrecˢ.

prodrecˢ-β :
  Γ ⊢ t ∷ A →
  Γ ⊢ u ∷ B [ t ]₀ →
  Γ ∙ A ∙ B ⊢ v ∷ C [ prodˢ p (var x1) (var x0) ]↑² →
  Σˢ-allowed p q →
  Γ ⊢ prodrecˢ p (prodˢ p t u) v ≡ v [ t ∣ u ] ∷ C [ prodˢ p t u ]₀
prodrecˢ-β
  {Γ = Γ} {t = t} {A = A} {u = u} {B = B} {v = v} {C = C} {p = p}
  ⊢t ⊢u ⊢v ok =                                                     $⟨ Σ-β₁-≡ ⊢B ⊢t ⊢u ok
                                                                     , Σ-β₂-≡ ⊢B ⊢t ⊢u ok
                                                                     ⟩
  Γ ⊢ fst p (prodˢ p t u) ≡ t ∷ A ×
  Γ ⊢ snd p (prodˢ p t u) ≡ u ∷ B [ fst p (prodˢ p t u) ]₀           →⟨ (λ (hyp₁ , hyp₂) →
                                                                            PE.subst (_ ⊢ _ ≡ _ ∷_) (PE.sym $ subst-id _) hyp₁
                                                                          , conv hyp₂ (substTypeEq (refl ⊢B) hyp₁)) ⟩
  Γ ⊢ fst p (prodˢ p t u) ≡ t ∷ A [ idSubst ] ×
  Γ ⊢ snd p (prodˢ p t u) ≡ u ∷ B [ t ]₀                             →⟨ (λ (hyp₁ , hyp₂) →
                                                                          (substRefl (idSubst′ ⊢Γ) , sym hyp₁) , sym hyp₂) ⟩
  Γ ⊢ˢ
    consSubst (consSubst idSubst t) u ≡
    consSubst (consSubst idSubst (fst p (prodˢ p t u)))
      (snd p (prodˢ p t u)) ∷
    Γ ∙ A ∙ B                                                       →⟨ flip (substitutionEqTerm (refl ⊢v)) ⊢Γ ⟩

  Γ ⊢
    v [ t ∣ u ] ≡
    prodrecˢ p (prodˢ p t u) v ∷
    C [ prodˢ p (var x1) (var x0) ]↑² [ t ∣ u ]                     →⟨ PE.subst (_⊢_≡_∷_ _ _ _) ([1,0]↑²[,] C) ∘→ sym ⟩

  Γ ⊢ prodrecˢ p (prodˢ p t u) v ≡ v [ t ∣ u ] ∷ C [ prodˢ p t u ]₀  □
  where
  ⊢Γ = wfTerm ⊢t
  ⊢B = case wfTerm ⊢v of λ where
         (_ ∙ _ ∙ ⊢B) → ⊢B

-- Another equality rule for prodrecˢ.

prodrecˢ-cong :
  Γ ∙ (Σˢ p , q ▷ A ▹ B) ⊢ C →
  Γ ⊢ t₁ ≡ t₂ ∷ Σˢ p , q ▷ A ▹ B →
  Γ ∙ A ∙ B ⊢ u₁ ≡ u₂ ∷ C [ prodˢ p (var x1) (var x0) ]↑² →
  Γ ⊢ prodrecˢ p t₁ u₁ ≡ prodrecˢ p t₂ u₂ ∷ C [ t₁ ]₀
prodrecˢ-cong
  {Γ = Γ} {p = p} {q = q} {A = A} {B = B} {C = C} {t₁ = t₁} {t₂ = t₂}
  {u₁ = u₁} {u₂ = u₂} ⊢C t₁≡t₂ u₁≡u₂ =                         $⟨ fst-cong′ t₁≡t₂ , snd-cong′ t₁≡t₂ ⟩
  Γ ⊢ fst p t₁ ≡ fst p t₂ ∷ A ×
  Γ ⊢ snd p t₁ ≡ snd p t₂ ∷ B [ fst p t₁ ]₀                     →⟨ (λ (hyp₁ , hyp₂) →
                                                                     PE.subst (_ ⊢ _ ≡ _ ∷_) (PE.sym (subst-id _)) hyp₁ , hyp₂) ⟩
  Γ ⊢ fst p t₁ ≡ fst p t₂ ∷ A [ idSubst ] ×
  Γ ⊢ snd p t₁ ≡ snd p t₂ ∷ B [ fst p t₁ ]₀                     →⟨ (λ (hyp₁ , hyp₂) → (substRefl (idSubst′ ⊢Γ) , hyp₁) , hyp₂) ⟩

  Γ ⊢ˢ
    consSubst (consSubst idSubst (fst p t₁)) (snd p t₁) ≡
    consSubst (consSubst idSubst (fst p t₂)) (snd p t₂) ∷
    Γ ∙ A ∙ B                                                   →⟨ flip (substitutionEqTerm u₁≡u₂) ⊢Γ ⟩

  Γ ⊢
    prodrecˢ p t₁ u₁ ≡
    prodrecˢ p t₂ u₂ ∷
    C [ prodˢ p (var x1) (var x0) ]↑² [ fst p t₁ ∣ snd p t₁ ]   →⟨ flip conv (⊢[1,0]↑²[fst,snd]≡ ⊢C ⊢t₁) ⟩

  Γ ⊢ prodrecˢ p t₁ u₁ ≡ prodrecˢ p t₂ u₂ ∷ C [ t₁ ]₀           □
  where
  ⊢Γ  = wfEqTerm t₁≡t₂
  ⊢t₁ = syntacticEqTerm t₁≡t₂ .proj₂ .proj₁

-- This module does not contain proofs of any reduction rules for
-- prodrecˢ. One might have hoped that the following rules should
-- hold:
--
--   Γ ∙ (Σˢ p , q ▷ A ▹ B) ⊢ C →
--   Γ ⊢ t ∷ A →
--   Γ ⊢ u ∷ B [ t ]₀ →
--   Γ ∙ A ∙ B ⊢ v ∷ C [ prodˢ p (var x1) (var x0) ]↑² →
--   Γ ⊢ prodrecˢ p (prodˢ p t u) v ⇒ v [ t ∣ u ] ∷ C [ prodˢ p t u ]₀
--
--   Γ ∙ (Σˢ p , q ▷ A ▹ B) ⊢ C →
--   Γ ∙ A ∙ B ⊢ u ∷ C [ prodʷ p (var x1) (var x0) ]↑² →
--   Γ ⊢ t₁ ⇒ t₂ ∷ Σʷ p , q ▷ A ▹ B →
--   Γ ⊢ prodrecˢ p t₁ u ⇒ prodrecˢ p t₂ u ∷ C [ t₁ ]₀
--
-- However, the reduction relation only allows reduction in certain
-- places in terms. For instance, it does not include reduction under
-- lambdas. Thus it seems unlikely that the rules above can be proved
-- (but there is no formal proof of this in this module).

------------------------------------------------------------------------
-- The first and second projections for weak Σ-types

-- The projections are defined using some extra quantities r′ and q′.

module Fstʷ-sndʷ (r′ q′ : M) where

  open Sigma.Fstʷ-sndʷ r′ q′ public

  ----------------------------------------------------------------------
  -- Some private lemmas related to wk1 and wk1Subst

  private

    -- Some lemmas used below.

    Σ⊢wk1 :
      Γ ∙ A ⊢ B →
      Σʷ-allowed p q →
      Γ ∙ (Σʷ p , q ▷ A ▹ B) ⊢ wk1 A
    Σ⊢wk1 ⊢B ok = W.wk₁ (ΠΣⱼ′ ⊢B ok) ⊢A
      where
      ⊢A = case wf ⊢B of λ where
             (_ ∙ ⊢A) → ⊢A

    ⊢wk1-wk1 :
      Γ ∙ A ⊢ B →
      Γ ∙ A ∙ B ⊢ wk1 (wk1 A)
    ⊢wk1-wk1 ⊢B = W.wk₁ ⊢B (W.wk₁ ⊢A ⊢A)
      where
      ⊢A = case wf ⊢B of λ where
             (_ ∙ ⊢A) → ⊢A

    ⊢wk1[]≡ :
      Γ ⊢ A →
      Γ ⊢ wk1 A [ t ]₀ ≡ A
    ⊢wk1[]≡ {Γ = Γ} {A = A} {t = t} =
      Γ ⊢ A                  →⟨ refl ⟩
      (Γ ⊢ A ≡ A)            →⟨ PE.subst (_ ⊢_≡ _) (PE.sym (wk1-sgSubst _ _)) ⟩
      (Γ ⊢ wk1 A [ t ]₀ ≡ A)  □

    ⊢wk1≡ :
      Γ ⊢ A →
      Γ ⊢ B →
      Γ ∙ A ⊢ wk1 B ≡ B [ wk1Subst idSubst ]
    ⊢wk1≡ {Γ = Γ} {A = A} {B = B} ⊢A =
      Γ ⊢ B                                         →⟨ W.wk₁ ⊢A ⟩
      Γ ∙ A ⊢ wk1 B                                 →⟨ refl ⟩
      (Γ ∙ A ⊢ wk1 B ≡ wk1 B)                       →⟨ PE.subst₂ (_ ⊢_≡_) PE.refl lemma ⟩
      (Γ ∙ A ⊢ wk1 B ≡ B [ wk1Subst idSubst ])  □
      where
      open Tools.Reasoning.PropositionalEquality

      lemma =
        wk1 B                    ≡⟨ wk≡subst _ _ ⟩
        B [ toSubst (step id) ]  ≡⟨⟩
        B [ wk1Subst idSubst ]   ∎

    ⊢wk1-wk1≡ :
      Γ ∙ A ⊢ B →
      Γ ∙ A ∙ B ⊢ wk1 (wk1 A) ≡ A [ wk1Subst (wk1Subst idSubst) ]
    ⊢wk1-wk1≡ {Γ = Γ} {A = A} {B = B} =
      Γ ∙ A ⊢ B                                                      →⟨ ⊢wk1-wk1 ⟩
      Γ ∙ A ∙ B ⊢ wk1 (wk1 A)                                        →⟨ refl ⟩
      (Γ ∙ A ∙ B ⊢ wk1 (wk1 A) ≡ wk1 (wk1 A))                        →⟨ PE.subst₂ (_ ⊢_≡_) PE.refl lemma ⟩
      (Γ ∙ A ∙ B ⊢ wk1 (wk1 A) ≡ A [ wk1Subst (wk1Subst idSubst) ])  □
      where
      open Tools.Reasoning.PropositionalEquality

      lemma =
        wk1 (wk1 A)                        ≡⟨ wk1-wk _ _ ⟩
        U.wk (step (step id)) A            ≡⟨ wk≡subst _ _ ⟩
        A [ toSubst (step (step id)) ]     ≡⟨⟩
        A [ wk1Subst (wk1Subst idSubst) ]  ∎

    ⊢ˢwk1Subst-idSubst :
      Γ ⊢ A →
      Γ ∙ A ⊢ˢ wk1Subst idSubst ∷ Γ
    ⊢ˢwk1Subst-idSubst {Γ = Γ} {A = A} ⊢A =
                                     $⟨ idSubst′ ⊢Γ ⟩
      Γ ⊢ˢ idSubst ∷ Γ               →⟨ wk1Subst′ ⊢Γ ⊢Γ ⊢A ⟩
      Γ ∙ A ⊢ˢ wk1Subst idSubst ∷ Γ  □
      where
      ⊢Γ = wf ⊢A

    ⊢ˢwk1Subst-wk1Subst-idSubst :
      Γ ∙ A ⊢ B →
      Γ ∙ A ∙ B ⊢ˢ wk1Subst (wk1Subst idSubst) ∷ Γ
    ⊢ˢwk1Subst-wk1Subst-idSubst {Γ = Γ} {A = A} {B = B} ⊢B =
      case ⊢ΓA of λ { (⊢Γ ∙ ⊢A) →
                                                    $⟨ ⊢ˢwk1Subst-idSubst ⊢A ⟩
      Γ ∙ A ⊢ˢ wk1Subst idSubst ∷ Γ                 →⟨ wk1Subst′ ⊢Γ ⊢ΓA ⊢B ⟩
      Γ ∙ A ∙ B ⊢ˢ wk1Subst (wk1Subst idSubst) ∷ Γ  □ }
      where
      ⊢ΓA = wf ⊢B

  ----------------------------------------------------------------------
  -- Typing rules for fstʷ

  private

    -- A lemma used below.

    1∷wk1[1,0] :
      Γ ∙ A ⊢ B →
      Γ ∙ A ∙ B ⊢ var x1 ∷ wk1 A [ prodʷ p (var x1) (var x0) ]↑²
    1∷wk1[1,0] {Γ = Γ} {A = A} {B = B} {p = p} ⊢B =                      $⟨ ⊢B ⟩
      Γ ∙ A ⊢ B                                                          →⟨ ⊢wk1-wk1 ⟩
      Γ ∙ A ∙ B ⊢ wk1 (wk1 A)                                            →⟨ refl ⟩
      (Γ ∙ A ∙ B ⊢ wk1 (wk1 A) ≡ wk1 (wk1 A))                            →⟨ PE.subst (_⊢_≡_ _ _) (PE.sym wk1-[]↑²) ⟩
      (Γ ∙ A ∙ B ⊢ wk1 (wk1 A) ≡ wk1 A [ prodʷ p (var x1) (var x0) ]↑²)  →⟨ conv (var₁ ⊢B) ⟩
      (Γ ∙ A ∙ B ⊢ var x1 ∷ wk1 A [ prodʷ p (var x1) (var x0) ]↑²)       □

  -- A typing rule for fstʷ.

  fstʷⱼ :
    Γ ⊢ t ∷ Σʷ p , q ▷ A ▹ B →
    Γ ⊢ fstʷ p A t ∷ A
  fstʷⱼ {Γ = Γ} {t = t} {p = p} {q = q} {A = A} {B = B} ⊢t =    $⟨ Σ⊢wk1 ⊢B ok , 1∷wk1[1,0] ⊢B ⟩
    (Γ ∙ (Σʷ p , q ▷ A ▹ B) ⊢ wk1 A) ×
    Γ ∙ A ∙ B ⊢ var x1 ∷ wk1 A [ prodʷ p (var x1) (var x0) ]↑²  →⟨ (λ (hyp₁ , hyp₂) → prodrecⱼ′ hyp₁ ⊢t hyp₂) ⟩

    Γ ⊢ fstʷ p A t ∷ wk1 A [ t ]₀                                →⟨ flip conv (⊢wk1[]≡ ⊢A) ⟩

    Γ ⊢ fstʷ p A t ∷ A                                          □
    where
    ⊢A,⊢B,ok = inversion-ΠΣ (syntacticTerm ⊢t)
    ⊢A       = ⊢A,⊢B,ok .proj₁
    ⊢B       = ⊢A,⊢B,ok .proj₂ .proj₁
    ok       = ⊢A,⊢B,ok .proj₂ .proj₂

  -- A reduction rule for fstʷ.

  fstʷ-β-⇒ :
    Γ ∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σʷ-allowed p q →
    Γ ⊢ fstʷ p A (prodʷ p t u) ⇒ t ∷ A
  fstʷ-β-⇒
    {Γ = Γ} {A = A} {B = B} {t = t} {u = u} {p = p} {q = q}
    ⊢B ⊢t ⊢u ok =                                                $⟨ Σ⊢wk1 ⊢B ok , 1∷wk1[1,0] ⊢B ⟩
    (Γ ∙ (Σʷ p , q ▷ A ▹ B) ⊢ wk1 A) ×
    Γ ∙ A ∙ B ⊢ var x1 ∷ wk1 A [ prodʷ p (var x1) (var x0) ]↑²   →⟨ (λ (hyp₁ , hyp₂) → prodrec-β-⇒ hyp₁ ⊢t ⊢u hyp₂ ok) ⟩

    Γ ⊢ fstʷ p A (prodʷ p t u) ⇒ t ∷ wk1 A [ prodʷ p t u ]₀      →⟨ flip conv (⊢wk1[]≡ ⊢A) ⟩

    Γ ⊢ fstʷ p A (prodʷ p t u) ⇒ t ∷ A                           □
    where
    ⊢A = syntacticTerm ⊢t

  -- Another reduction rule for fstʷ.

  fstʷ-subst :
    Γ ∙ A ⊢ B →
    Γ ⊢ t₁ ⇒ t₂ ∷ Σʷ p , q ▷ A ▹ B →
    Γ ⊢ fstʷ p A t₁ ⇒ fstʷ p A t₂ ∷ A
  fstʷ-subst
    {Γ = Γ} {A = A} {B = B} {t₁ = t₁} {t₂ = t₂} {p = p} {q = q}
    ⊢B t₁⇒t₂ =                                                   $⟨ Σ⊢wk1 ⊢B ok , 1∷wk1[1,0] ⊢B ⟩
    (Γ ∙ (Σʷ p , q ▷ A ▹ B) ⊢ wk1 A) ×
    Γ ∙ A ∙ B ⊢ var x1 ∷ wk1 A [ prodʷ p (var x1) (var x0) ]↑²   →⟨ (λ (hyp₁ , hyp₂) → prodrec-subst′ hyp₁ hyp₂ t₁⇒t₂ ok) ⟩

    Γ ⊢ fstʷ p A t₁ ⇒ fstʷ p A t₂ ∷ wk1 A [ t₁ ]₀                →⟨ flip conv (⊢wk1[]≡ ⊢A) ⟩

    Γ ⊢ fstʷ p A t₁ ⇒ fstʷ p A t₂ ∷ A                            □
    where
    ⊢A = case wf ⊢B of λ where
           (_ ∙ ⊢A) → ⊢A
    ok = ⊢∷ΠΣ→ΠΣ-allowed $
         syntacticRedTerm (redMany t₁⇒t₂) .proj₂ .proj₁

  -- An equality rule for fstʷ.

  fstʷ-β-≡ :
    Γ ∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σʷ-allowed p q →
    Γ ⊢ fstʷ p A (prodʷ p t u) ≡ t ∷ A
  fstʷ-β-≡ ⊢B ⊢t ⊢u ok = subsetTerm (fstʷ-β-⇒ ⊢B ⊢t ⊢u ok)

  -- Another equality rule for fstʷ.

  fstʷ-cong :
    Γ ⊢ A₁ ≡ A₂ →
    Γ ∙ A₁ ⊢ B₁ →
    Γ ⊢ t₁ ≡ t₂ ∷ Σʷ p , q ▷ A₁ ▹ B₁ →
    Γ ⊢ fstʷ p A₁ t₁ ≡ fstʷ p A₂ t₂ ∷ A₁
  fstʷ-cong
    {Γ = Γ} {A₁ = A₁} {A₂ = A₂} {B₁ = B₁} {t₁ = t₁} {t₂ = t₂}
    {p = p} {q = q} A₁≡A₂ ⊢B₁ t₁≡t₂ =                              $⟨ W.wkEq₁ (ΠΣⱼ′ ⊢B₁ ok) A₁≡A₂
                                                                    , 1∷wk1[1,0] ⊢B₁
                                                                    ⟩
    (Γ ∙ (Σʷ p , q ▷ A₁ ▹ B₁) ⊢ wk1 A₁ ≡ wk1 A₂) ×
    Γ ∙ A₁ ∙ B₁ ⊢ var x1 ∷ wk1 A₁ [ prodʷ p (var x1) (var x0) ]↑²  →⟨ (λ (hyp₁ , hyp₂) → prodrec-cong′ hyp₁ t₁≡t₂ (refl hyp₂)) ⟩

    Γ ⊢ fstʷ p A₁ t₁ ≡ fstʷ p A₂ t₂ ∷ wk1 A₁ [ t₁ ]₀               →⟨ flip conv (⊢wk1[]≡ ⊢A₁) ⟩

    Γ ⊢ fstʷ p A₁ t₁ ≡ fstʷ p A₂ t₂ ∷ A₁                           □
    where
    ⊢A₁ = syntacticEq A₁≡A₂ .proj₁
    ok  = ⊢∷ΠΣ→ΠΣ-allowed $
          syntacticEqTerm t₁≡t₂ .proj₂ .proj₁

  ----------------------------------------------------------------------
  -- Some private lemmas related to fstʷ

  private

    -- Some lemmas used below.

    fstʷ-0[] : fstʷ p (wk1 A) (var x0) [ t ]₀ PE.≡ fstʷ p A t
    fstʷ-0[] {A = A} {t = t} = PE.cong (λ A → prodrec _ _ _ A _ _) $
      wk1 (wk1 A) [ liftSubst (sgSubst t) ]  ≡⟨ subst-wk (wk1 A) ⟩
      wk1 A [ wk1 ∘→ sgSubst t ]             ≡⟨ wk1-tail A ⟩
      A [ wk1Subst idSubst ]                 ≡˘⟨ wk≡subst _ _ ⟩
      wk1 A                                  ∎
      where
      open Tools.Reasoning.PropositionalEquality

    [fstʷ] :
      ∀ B → B [ fstʷ p A t ]₀ PE.≡ B [ fstʷ p (wk1 A) (var x0) ]↑ [ t ]₀
    [fstʷ] {p = p} {A = A} {t = t} B =
      B [ fstʷ p A t ]₀                                            ≡˘⟨ (flip substVar-to-subst B λ where
                                                                          x0     → fstʷ-0[]
                                                                          (_ +1) → PE.refl) ⟩
      B [ sgSubst t ₛ•ₛ
          consSubst (wk1Subst idSubst) (fstʷ p (wk1 A) (var x0)) ] ≡˘⟨ substCompEq B ⟩

      B [ fstʷ p (wk1 A) (var x0) ]↑ [ t ]₀                        ∎
      where
      open Tools.Reasoning.PropositionalEquality

    ⊢≡[fstʷ] :
      Γ ⊢ t ∷ Σʷ p , q ▷ A ▹ B →
      Γ ⊢ B [ fstʷ p (wk1 A) (var x0) ]↑ [ t ]₀ ≡ B [ fstʷ p A t ]₀
    ⊢≡[fstʷ] {Γ = Γ} {t = t} {p = p} {A = A} {B = B} ⊢t =              $⟨ substitution ⊢B (singleSubst (fstʷⱼ ⊢t)) ⊢Γ ⟩
      Γ ⊢ B [ fstʷ p A t ]₀                                            →⟨ refl ⟩
      (Γ ⊢ B [ fstʷ p A t ]₀ ≡ B [ fstʷ p A t ]₀)                      →⟨ PE.subst₂ (_ ⊢_≡_) ([fstʷ] B) PE.refl ⟩
      (Γ ⊢ B [ fstʷ p (wk1 A) (var x0) ]↑ [ t ]₀ ≡ B [ fstʷ p A t ]₀)  □
      where
      ⊢Γ = wfTerm ⊢t
      ⊢B = inversion-ΠΣ (syntacticTerm ⊢t) .proj₂ .proj₁

    [fstʷ-0]↑[1,0]↑² :
      ∀ B →
      B [ fstʷ p (wk1 A) (var x0) ]↑ [ prodʷ p (var x1) (var x0) ]↑²
        PE.≡
      B [ fstʷ p (wk1 (wk1 A)) (prodʷ p (var x1) (var x0)) ]↑²
    [fstʷ-0]↑[1,0]↑² {p = p} {A = A} B =
      B [ fstʷ p (wk1 A) (var x0) ]↑ [ prodʷ p (var x1) (var x0) ]↑²  ≡⟨ substCompEq B ⟩

      B [ consSubst (wk1Subst (wk1Subst idSubst))
           (prodʷ p (var x1) (var x0)) ₛ•ₛ
         consSubst (wk1Subst idSubst) (fstʷ p (wk1 A) (var x0)) ]     ≡⟨ (flip substVar-to-subst B λ where
                                                                            x0     → PE.refl
                                                                            (_ +1) → PE.refl) ⟩
      B [ prodrec r′ p q′
            (wk1 (wk1 A) [ liftSubst $
              consSubst (wk1Subst (wk1Subst idSubst)) $
              prodʷ p (var x1) (var x0) ])
            (prodʷ p (var x1) (var x0))
            (var x1) ]↑²                                              ≡⟨ PE.cong (λ A → B [ prodrec _ _ _ A _ _ ]↑²) $
                                                                         PE.trans (wk1-tail (wk1 A)) $
                                                                         wk1-tail A ⟩
      B [ prodrec r′ p q′
            (A [ wk1Subst (wk1Subst (wk1Subst idSubst)) ])
            (prodʷ p (var x1) (var x0))
            (var x1) ]↑²                                              ≡˘⟨ PE.cong (λ A → B [ prodrec _ _ _ A _ _ ]↑²) $
                                                                          PE.trans (PE.cong (_[ _ ]) $ substCompEq A) $
                                                                          substCompEq A ⟩
      B [ prodrec r′ p q′
            (_[ wk1Subst idSubst ] $
             _[ wk1Subst idSubst ] $
             A [ wk1Subst idSubst ])
            (prodʷ p (var x1) (var x0))
            (var x1) ]↑²                                              ≡˘⟨ PE.cong (λ A → B [ prodrec _ _ _ A _ _ ]↑²) $
                                                                          PE.trans (wk≡subst _ _) $
                                                                          PE.trans (PE.cong (_[ _ ]) $ wk≡subst _ (wk1 A)) $
                                                                          PE.cong (_[ _ ]) $ PE.cong (_[ _ ]) $ wk≡subst _ A ⟩
      B [ fstʷ p (wk1 (wk1 A)) (prodʷ p (var x1) (var x0)) ]↑²        ∎
      where
      open Tools.Reasoning.PropositionalEquality

    ⊢≡[fstʷ-0]↑[1,0]↑² :
      Γ ∙ A ⊢ B →
      Σʷ-allowed p q →
      Γ ∙ A ∙ B ⊢
        wk1 B ≡
        B [ fstʷ p (wk1 A) (var x0) ]↑ [ prodʷ p (var x1) (var x0) ]↑²
    ⊢≡[fstʷ-0]↑[1,0]↑² {Γ = Γ} {A = A} {B = B} {p = p} ⊢B ok =          $⟨ substRefl (⊢ˢwk1Subst-wk1Subst-idSubst ⊢B) , lemma ⟩
      Γ ∙ A ∙ B ⊢ˢ
        consSubst (wk1Subst (wk1Subst idSubst)) (var x1) ≡
        consSubst (wk1Subst (wk1Subst idSubst))
          (fstʷ p (wk1 (wk1 A)) (prodʷ p (var x1) (var x0))) ∷
        Γ ∙ A                                                           →⟨ flip (substitutionEq (refl ⊢B)) (wf ⊢B ∙ ⊢B) ⟩

      Γ ∙ A ∙ B ⊢
        B [ var x1 ]↑² ≡
        B [ fstʷ p (wk1 (wk1 A)) (prodʷ p (var x1) (var x0)) ]↑²        →⟨ PE.subst₂ (_ ⊢_≡_) [1]↑² (PE.sym $ [fstʷ-0]↑[1,0]↑² B) ⟩

      Γ ∙ A ∙ B ⊢
        wk1 B ≡
        B [ fstʷ p (wk1 A) (var x0) ]↑ [ prodʷ p (var x1) (var x0) ]↑²  □
      where
      lemma =                                                  $⟨ W.wk₁ ⊢B ⊢B ⟩

        (Γ ∙ A ∙ B ⊢ wk1 B)                                    →⟨ refl ⟩

        Γ ∙ A ∙ B ⊢ wk1 B ≡ wk1 B                              →⟨ PE.subst₂ (_ ⊢_≡_) PE.refl (PE.sym (wk1-sgSubst (wk1 B) _)) ⟩

        Γ ∙ A ∙ B ⊢ wk1 B ≡ wk1 (wk1 B) [ var x1 ]₀            →⟨ conv (var₀ ⊢B) ⟩

        (Γ ∙ A ∙ B ⊢ var x0 ∷ wk1 (wk1 B) [ var x1 ]₀)         →⟨ (λ ⊢0 → ⊢wk1-wk1 (⊢wk1-wk1 ⊢B) , var₁ ⊢B , ⊢0) ⟩

        (Γ ∙ A ∙ B ∙ wk1 (wk1 A) ⊢ wk1 (wk1 B)) ×
        (Γ ∙ A ∙ B ⊢ var x1 ∷ wk1 (wk1 A)) ×
        (Γ ∙ A ∙ B ⊢ var x0 ∷ wk1 (wk1 B) [ var x1 ]₀)         →⟨ (λ (⊢B , ⊢1 , ⊢0) → fstʷ-β-≡ ⊢B ⊢1 ⊢0 ok) ⟩

        (Γ ∙ A ∙ B ⊢
           fstʷ p (wk1 (wk1 A)) (prodʷ p (var x1) (var x0)) ≡
           var x1 ∷
           wk1 (wk1 A))                                        →⟨ flip _⊢_≡_∷_.conv (⊢wk1-wk1≡ ⊢B) ∘→ _⊢_≡_∷_.sym ⟩

        (Γ ∙ A ∙ B ⊢
           var x1 ≡
           fstʷ p (wk1 (wk1 A)) (prodʷ p (var x1) (var x0)) ∷
           A [ wk1Subst (wk1Subst idSubst) ])                  □

    ⊢[fstʷ-0]↑≡[fstʷ-0]↑ :
      Γ ⊢ A₁ ≡ A₂ →
      Γ ∙ A₁ ⊢ B₁ ≡ B₂ →
      Σʷ-allowed p q →
      Γ ∙ (Σʷ p , q ▷ A₁ ▹ B₁) ⊢
        B₁ [ fstʷ p (wk1 A₁) (var x0) ]↑ ≡
        B₂ [ fstʷ p (wk1 A₂) (var x0) ]↑
    ⊢[fstʷ-0]↑≡[fstʷ-0]↑
      {Γ = Γ} {A₁ = A₁} {A₂ = A₂} {B₁ = B₁} {B₂ = B₂} {p = p} {q = q}
      A₁≡A₂ B₁≡B₂ ok =                                             $⟨ refl (var₀ ⊢ΣA₁B₁) ⟩
      Γ ∙ (Σʷ p , q ▷ A₁ ▹ B₁) ⊢
        var x0 ≡
        var x0 ∷
        wk1 (Σʷ p , q ▷ A₁ ▹ B₁)                                   →⟨ fstʷ-cong
                                                                        (wkEq (step id) ⊢ΓΣA₁B₁ A₁≡A₂)
                                                                        (W.wk (lift (step id)) (⊢ΓΣA₁B₁ ∙ W.wk₁ ⊢ΣA₁B₁ ⊢A₁) ⊢B₁) ⟩
      Γ ∙ (Σʷ p , q ▷ A₁ ▹ B₁) ⊢
        fstʷ p (wk1 A₁) (var x0) ≡
        fstʷ p (wk1 A₂) (var x0) ∷
        wk1 A₁                                                     →⟨ flip conv (⊢wk1≡ ⊢ΣA₁B₁ ⊢A₁) ⟩

      Γ ∙ (Σʷ p , q ▷ A₁ ▹ B₁) ⊢
        fstʷ p (wk1 A₁) (var x0) ≡
        fstʷ p (wk1 A₂) (var x0) ∷
        A₁ [ wk1Subst idSubst ]                                    →⟨ substRefl (⊢ˢwk1Subst-idSubst ⊢ΣA₁B₁) ,_ ⟩

      Γ ∙ (Σʷ p , q ▷ A₁ ▹ B₁) ⊢ˢ
        consSubst (wk1Subst idSubst) (fstʷ p (wk1 A₁) (var x0)) ≡
        consSubst (wk1Subst idSubst) (fstʷ p (wk1 A₂) (var x0)) ∷
        Γ ∙ A₁                                                     →⟨ flip (substitutionEq B₁≡B₂) ⊢ΓΣA₁B₁ ⟩

      Γ ∙ (Σʷ p , q ▷ A₁ ▹ B₁) ⊢
        B₁ [ fstʷ p (wk1 A₁) (var x0) ]↑ ≡
        B₂ [ fstʷ p (wk1 A₂) (var x0) ]↑                           □
      where
      ⊢A₁     = syntacticEq A₁≡A₂ .proj₁
      ⊢B₁     = syntacticEq B₁≡B₂ .proj₁
      ⊢ΣA₁B₁  = ΠΣⱼ′ ⊢B₁ ok
      ⊢ΓΣA₁B₁ = wf ⊢A₁ ∙ ⊢ΣA₁B₁

    ⊢[fstʷ-0]↑ :
      Γ ∙ A ⊢ B →
      Σʷ-allowed p q →
      Γ ∙ (Σʷ p , q ▷ A ▹ B) ⊢ B [ fstʷ p (wk1 A) (var x0) ]↑
    ⊢[fstʷ-0]↑ ⊢B ok =
      syntacticEq (⊢[fstʷ-0]↑≡[fstʷ-0]↑ (refl ⊢A) (refl ⊢B) ok) .proj₁
      where
      ⊢A = case wf ⊢B of λ where
             (_ ∙ ⊢A) → ⊢A

    ⊢0∷[fstʷ-0]↑[1,0]↑² :
      Γ ∙ A ⊢ B →
      Σʷ-allowed p q →
      Γ ∙ A ∙ B ⊢
        var x0 ∷
        B [ fstʷ p (wk1 A) (var x0) ]↑ [ prodʷ p (var x1) (var x0) ]↑²
    ⊢0∷[fstʷ-0]↑[1,0]↑² {Γ = Γ} {A = A} {B = B} {p = p} ⊢B ok =
                                                                        $⟨ var₀ ⊢B ⟩

      Γ ∙ A ∙ B ⊢ var x0 ∷ wk1 B                                        →⟨ flip conv (⊢≡[fstʷ-0]↑[1,0]↑² ⊢B ok) ⟩

      Γ ∙ A ∙ B ⊢
        var x0 ∷
        B [ fstʷ p (wk1 A) (var x0) ]↑ [ prodʷ p (var x1) (var x0) ]↑²  □

  ----------------------------------------------------------------------
  -- Typing rules for sndʷ

  -- A typing rule for sndʷ.

  sndʷⱼ :
    Γ ⊢ t ∷ Σʷ p , q ▷ A ▹ B →
    Γ ⊢ sndʷ p q A B t ∷ B [ fstʷ p A t ]₀
  sndʷⱼ {Γ = Γ} {t = t} {p = p} {q = q} {A = A} {B = B} ⊢t =    $⟨ prodrecⱼ ⊢A ⊢B (⊢[fstʷ-0]↑ ⊢B ok) ⊢t
                                                                     (⊢0∷[fstʷ-0]↑[1,0]↑² ⊢B ok) ok ⟩
    Γ ⊢ sndʷ p q A B t ∷ B [ fstʷ p (wk1 A) (var x0) ]↑ [ t ]₀  →⟨ flip conv (⊢≡[fstʷ] ⊢t) ⟩
    Γ ⊢ sndʷ p q A B t ∷ B [ fstʷ p A t ]₀                      □
    where
    ⊢A,⊢B,ok = inversion-ΠΣ (syntacticTerm ⊢t)
    ⊢A       = ⊢A,⊢B,ok .proj₁
    ⊢B       = ⊢A,⊢B,ok .proj₂ .proj₁
    ok       = ⊢A,⊢B,ok .proj₂ .proj₂

  -- A reduction rule for sndʷ.

  sndʷ-β-⇒ :
    Γ ∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σʷ-allowed p q →
    Γ ⊢ sndʷ p q A B (prodʷ p t u) ⇒ u ∷ B [ fstʷ p A (prodʷ p t u) ]₀
  sndʷ-β-⇒
    {Γ = Γ} {A = A} {B = B} {t = t} {u = u} {p = p} {q = q}
    ⊢B ⊢t ⊢u ok =                                      $⟨ prodrec-β (syntacticTerm ⊢t) ⊢B (⊢[fstʷ-0]↑ {q = q} ⊢B ok)
                                                            ⊢t ⊢u (⊢0∷[fstʷ-0]↑[1,0]↑² ⊢B ok) PE.refl ok ⟩
    Γ ⊢ sndʷ p q A B (prodʷ p t u) ⇒ u ∷
      B [ fstʷ p (wk1 A) (var x0) ]↑ [ prodʷ p t u ]₀  →⟨ flip conv (⊢≡[fstʷ] (⊢prod ⊢B ⊢t ⊢u ok)) ⟩

    Γ ⊢ sndʷ p q A B (prodʷ p t u) ⇒ u ∷
      B [ fstʷ p A (prodʷ p t u) ]₀                    □

  -- Another reduction rule for sndʷ.

  sndʷ-subst :
    Γ ⊢ t₁ ⇒ t₂ ∷ Σʷ p , q ▷ A ▹ B →
    Γ ⊢ sndʷ p q A B t₁ ⇒ sndʷ p q A B t₂ ∷ B [ fstʷ p A t₁ ]₀
  sndʷ-subst
    {Γ = Γ} {t₁ = t₁} {t₂ = t₂} {p = p} {q = q} {A = A} {B = B} t₁⇒t₂ =
                                              $⟨ prodrec-subst′ (⊢[fstʷ-0]↑ ⊢B ok) (⊢0∷[fstʷ-0]↑[1,0]↑² ⊢B ok) t₁⇒t₂ ok ⟩
    Γ ⊢ sndʷ p q A B t₁ ⇒ sndʷ p q A B t₂ ∷
      B [ fstʷ p (wk1 A) (var x0) ]↑ [ t₁ ]₀  →⟨ flip conv (⊢≡[fstʷ] ⊢t₁) ⟩

    Γ ⊢ sndʷ p q A B t₁ ⇒ sndʷ p q A B t₂ ∷
      B [ fstʷ p A t₁ ]₀                      □
    where
    ⊢t₁   = syntacticEqTerm (subsetTerm t₁⇒t₂) .proj₂ .proj₁
    ⊢B,ok = inversion-ΠΣ (syntacticTerm ⊢t₁) .proj₂
    ⊢B    = ⊢B,ok .proj₁
    ok    = ⊢B,ok .proj₂

  -- An equality rule for sndʷ.

  sndʷ-β-≡ :
    Γ ∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σʷ-allowed p q →
    Γ ⊢ sndʷ p q A B (prodʷ p t u) ≡ u ∷ B [ fstʷ p A (prodʷ p t u) ]₀
  sndʷ-β-≡ ⊢B ⊢t ⊢u ok = subsetTerm (sndʷ-β-⇒ ⊢B ⊢t ⊢u ok)

  -- Another equality rule for sndʷ.

  sndʷ-cong :
    Γ ⊢ A₁ ≡ A₂ →
    Γ ∙ A₁ ⊢ B₁ ≡ B₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ Σʷ p , q ▷ A₁ ▹ B₁ →
    Γ ⊢ sndʷ p q A₁ B₁ t₁ ≡ sndʷ p q A₂ B₂ t₂ ∷ B₁ [ fstʷ p A₁ t₁ ]₀
  sndʷ-cong
    {Γ = Γ} {A₁ = A₁} {A₂ = A₂} {B₁ = B₁} {B₂ = B₂} {t₁ = t₁} {t₂ = t₂}
    {p = p} {q = q} A₁≡A₂ B₁≡B₂ t₁≡t₂ =           $⟨ prodrec-cong′ (⊢[fstʷ-0]↑≡[fstʷ-0]↑ A₁≡A₂ B₁≡B₂ ok)
                                                       t₁≡t₂ (refl (⊢0∷[fstʷ-0]↑[1,0]↑² ⊢B ok)) ⟩
    Γ ⊢ sndʷ p q A₁ B₁ t₁ ≡ sndʷ p q A₂ B₂ t₂ ∷
      B₁ [ fstʷ p (wk1 A₁) (var x0) ]↑ [ t₁ ]₀    →⟨ flip conv (⊢≡[fstʷ] ⊢t₁) ⟩

    Γ ⊢ sndʷ p q A₁ B₁ t₁ ≡ sndʷ p q A₂ B₂ t₂ ∷
      B₁ [ fstʷ p A₁ t₁ ]₀                        □
    where
    ⊢t₁   = syntacticEqTerm t₁≡t₂ .proj₂ .proj₁
    ⊢B,ok = inversion-ΠΣ (syntacticTerm ⊢t₁) .proj₂
    ⊢B    = ⊢B,ok .proj₁
    ok    = ⊢B,ok .proj₂

  -- If Σʷ-allowed p q holds for some p and q, then a certain
  -- definitional η-rule for Σʷ, fstʷ and sndʷ does not hold in
  -- general.

  ¬-Σʷ-η-prodʷ-fstʷ-sndʷ :
    ∀ {p q} →
    Σʷ-allowed p q →
    ¬ (∀ {n} {Γ : Con Term n} {t A B} →
       Γ ⊢ t ∷ Σʷ p , q ▷ A ▹ B →
       Γ ⊢ prodʷ p (fstʷ p A t) (sndʷ p q A B t) ≡ t ∷ Σʷ p , q ▷ A ▹ B)
  ¬-Σʷ-η-prodʷ-fstʷ-sndʷ {p = p} {q = q} Σ-ok hyp = ¬fst,snd≡ fst,snd≡
    where
    A′ = ℕ
    B′ = ℕ

    Γ′ = ε ∙ Σʷ p , q ▷ ℕ ▹ ℕ

    t′ : Term 1
    t′ = var x0

    ⊢Γ : ⊢ Γ′
    ⊢Γ = ε ∙ ΠΣⱼ′ (ℕⱼ (ε ∙ ℕⱼ ε)) Σ-ok

    ⊢B : Γ′ ∙ A′ ⊢ B′
    ⊢B = ℕⱼ (⊢Γ ∙ ℕⱼ ⊢Γ)

    ⊢t : Γ′ ⊢ t′ ∷ Σʷ p , q ▷ A′ ▹ B′
    ⊢t = var ⊢Γ here

    fst,snd≡ :
      Γ′ ⊢ prodʷ p (fstʷ p A′ t′) (sndʷ p q A′ B′ t′) ≡ t′ ∷
        Σʷ p , q ▷ A′ ▹ B′
    fst,snd≡ = hyp ⊢t

    ¬fst,snd≡ :
      ¬ Γ′ ⊢ prodʷ p (fstʷ p A′ t′) (sndʷ p q A′ B′ t′) ≡ t′ ∷
          Σʷ p , q ▷ A′ ▹ B′
    ¬fst,snd≡ = prodʷ≢ne (var _)

  opaque

    -- However, the corresponding propositional η-rule does hold.

    -- The η-rule's witness.

    Σʷ-η-prodʷ-fstʷ-sndʷ :
      M → M → Term n → Term (1+ n) → Term n → Term n
    Σʷ-η-prodʷ-fstʷ-sndʷ p q A B t =
      prodrec 𝟘 p 𝟙
        (Id (wk1 (Σʷ p , q ▷ A ▹ B))
           (prodʷ p (fstʷ p (wk1 A) (var x0))
              (sndʷ p q (wk1 A) (U.wk (lift (step id)) B) (var x0)))
           (var x0))
        t
        rfl

  opaque
    unfolding Σʷ-η-prodʷ-fstʷ-sndʷ

    -- The η-rule's typing rule.

    ⊢Σʷ-η-prodʷ-fstʷ-sndʷ :
      Γ ⊢ t ∷ Σʷ p , q ▷ A ▹ B →
      Γ ⊢ Σʷ-η-prodʷ-fstʷ-sndʷ p q A B t ∷
        Id (Σʷ p , q ▷ A ▹ B) (prodʷ p (fstʷ p A t) (sndʷ p q A B t)) t
    ⊢Σʷ-η-prodʷ-fstʷ-sndʷ {t} {p} {q} {A} {B} ⊢t =
      let pair = prodʷ p (var x1) (var x0) in
      case syntacticTerm ⊢t of λ {
        ⊢ΣAB →
      case inversion-ΠΣ ⊢ΣAB of λ {
        (⊢A , ⊢B , ok) →
      case
        wk1 A [ pair ]↑²         ≡⟨ wk1-[]↑² ⟩
        wk2 A                    ≡⟨ wk-comp _ _ _ ⟩
        U.wk (step (step id)) A  ∎
      of λ {
        eq₁ →
      case
        U.wk (lift (step id)) B
          [ liftSubst (consSubst (wk1Subst (wk1Subst idSubst)) pair) ]   ≡⟨ subst-wk B ⟩

        B [ liftSubst (consSubst (wk1Subst (wk1Subst idSubst)) pair) ₛ•
            lift (step id) ]                                             ≡⟨ (flip substVar-to-subst B λ where
                                                                               x0     → PE.refl
                                                                               (_ +1) → PE.refl) ⟩

        B [ toSubst (lift (step (step id))) ]                            ≡˘⟨ wk≡subst _ _ ⟩

        U.wk (lift (step (step id))) B                                   ∎
      of λ {
        eq₂ →
      case W.wk (lift (step (step id)))
             (wf ⊢B ∙ ⊢B ∙ W.wk (step (step id)) (wf ⊢B ∙ ⊢B) ⊢A)
             ⊢B of λ {
        ⊢B′ →
      case W.wk (lift (step id)) (wf ⊢A ∙ ⊢ΣAB ∙ wk₁ ⊢ΣAB ⊢A) ⊢B of λ {
        ⊢B″ →
      case PE.subst (_⊢_∷_ _ _) (wk-comp _ _ _) $ var₁ ⊢B of λ {
        ⊢₁ →
      case PE.subst (_⊢_∷_ _ _) (PE.sym $ wkSingleSubstWk1 B) $
           var₀ ⊢B of λ {
        ⊢₀ →
      PE.subst (_⊢_∷_ _ _)
        (Id (Σʷ p , q ▷ wk1 A ▹ U.wk (lift (step id)) B)
           (prodʷ p (fstʷ p (wk1 A) (var x0))
              (sndʷ p q (wk1 A) (U.wk (lift (step id)) B) (var x0)))
           (var x0)
           [ t ]₀                                                     ≡⟨ PE.cong
                                                                           (λ x →
                                                                              Id (Σʷ p , q ▷ wk1 A [ t ]₀ ▹
                                                                                  (U.wk (lift (step id)) B [ liftSubst (sgSubst t) ]))
                                                                                 x t) $
                                                                         PE.cong₂ (prodʷ p)
                                                                           (fstʷ-[] (wk1 A) (var x0))
                                                                           (sndʷ-[] (U.wk (lift (step id)) B) (var x0)) ⟩
         Id
           (Σʷ p , q ▷ wk1 A [ t ]₀ ▹
            (U.wk (lift (step id)) B [ liftSubst (sgSubst t) ]))
           (prodʷ p (fstʷ p (wk1 A [ t ]₀) t)
              (sndʷ p q (wk1 A [ t ]₀)
                 (U.wk (lift (step id)) B
                    [ liftSubst (sgSubst t) ]) t))
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
        (Idⱼ
           (⊢prod ⊢B″ (fstʷⱼ (var₀ ⊢ΣAB)) (sndʷⱼ (var₀ ⊢ΣAB)) ok)
           (var₀ ⊢ΣAB))
        ⊢t
        (rflⱼ′
           (prodʷ p (fstʷ p (wk1 A) (var x0) [ pair ]↑²)
              (sndʷ p q (wk1 A) (U.wk (lift (step id)) B) (var x0)
                 [ pair ]↑²)                                           ≡⟨ PE.cong₂ (prodʷ p)
                                                                            (fstʷ-[] (wk1 A) (var x0))
                                                                            (sndʷ-[] (U.wk (lift (step id)) B) (var x0)) ⟩⊢≡
            prodʷ p (fstʷ p (wk1 A [ pair ]↑²) pair)
              (sndʷ p q (wk1 A [ pair ]↑²)
                 (U.wk (lift (step id)) B
                    [ liftSubst $
                      consSubst (wk1Subst (wk1Subst idSubst)) pair ])
                 pair)                                                 ≡⟨ PE.cong₂ (λ A B → prodʷ _ (fstʷ _ A _) (sndʷ _ _ A B _)) eq₁ eq₂ ⟩⊢≡

            prodʷ p (fstʷ p (U.wk (step (step id)) A) pair)
              (sndʷ p q (U.wk (step (step id)) A)
                 (U.wk (lift (step (step id))) B) pair)                ≡⟨ PE.subst (_⊢_≡_∷_ _ _ _)
                                                                            (PE.sym $ PE.cong₂ (Σʷ _ , _ ▷_▹_) eq₁ eq₂) $
                                                                          prod-cong′ ⊢B′
                                                                            (fstʷ-β-≡ ⊢B′ ⊢₁ ⊢₀ ok)
                                                                            (sndʷ-β-≡ ⊢B′ ⊢₁ ⊢₀ ok)
                                                                            ok ⟩⊢∎

            pair                                                       ∎)) }}}}}}}}

  -- If Σʷ-allowed p q holds for some p and q, then a certain
  -- definitional η-rule for Σʷ, fstʷ and sndʷ does not hold in
  -- general.

  ¬-Σʷ-η :
    ∀ {p q} →
    Σʷ-allowed p q →
    ¬ (∀ {n} {Γ : Con Term n} {t A B u} →
       Γ ⊢ t ∷ Σʷ p , q ▷ A ▹ B →
       Γ ⊢ u ∷ Σʷ p , q ▷ A ▹ B →
       Γ ⊢ fstʷ p A t ≡ fstʷ p A u ∷ A →
       Γ ⊢ sndʷ p q A B t ≡ sndʷ p q A B u ∷ B [ fstʷ p A t ]₀ →
       Γ ⊢ t ≡ u ∷ Σʷ p , q ▷ A ▹ B)
  ¬-Σʷ-η Σ-ok hyp =
    ¬-Σʷ-η-prodʷ-fstʷ-sndʷ Σ-ok λ ⊢t →
      case inversion-ΠΣ (syntacticTerm ⊢t) of λ {
        (_ , ⊢B , ok) →
      hyp (⊢prod ⊢B (fstʷⱼ ⊢t) (sndʷⱼ ⊢t) ok) ⊢t
        (fstʷ-β-≡ ⊢B (fstʷⱼ ⊢t) (sndʷⱼ ⊢t) ok)
        (sndʷ-β-≡ ⊢B (fstʷⱼ ⊢t) (sndʷⱼ ⊢t) ok) }


  -- Inversion lemma for fstʷ.

  inversion-fstʷ : Γ ⊢ fstʷ p A t ∷ C →
    ∃₂ λ q B → Γ ⊢ t ∷ Σʷ p , q ▷ A ▹ B × Γ ⊢ C ≡ A
  inversion-fstʷ {p = p} {A} {t} ⊢t₁ =
    case inversion-prodrec ⊢t₁ of λ
      (F , G , q , ⊢F , ⊢G , ⊢wk1A , ⊢t , ⊢x₁ , C≡) →
    case inversion-var ⊢x₁ of λ {
      (_ , there here , ≡wk2F) →
    case PE.subst (_ ⊢ _ ≡_) (wk1-sgSubst A t) C≡ of λ
      C≡A →
    case PE.subst (_ ⊢_≡ _) (wk1-[]↑² {t = A}) ≡wk2F of λ
      wk2A≡wk2F →
    case PE.subst (_ ⊢ fstʷ p F t ∷_) (PE.sym (subst-id F)) (fstʷⱼ ⊢t) of λ
      ⊢t₁ →
    case sndʷⱼ ⊢t of λ
      ⊢t₂ →
    case substRefl {σ = consSubst (sgSubst (fstʷ p F t)) (sndʷ p q F G t)}
                   ((idSubst′ (wfTerm ⊢t₁) , ⊢t₁) , ⊢t₂) of λ
      [σ] →
    case substitutionEq wk2A≡wk2F [σ] (wfTerm ⊢t₁) of λ
      A≡F′ →
    case PE.subst₂ (_ ⊢_≡_)
                   (PE.trans (wk2-tail A) (subst-id A))
                   (PE.trans (wk2-tail F) (subst-id F))
                   A≡F′ of λ
      A≡F →
    case inversion-ΠΣ (syntacticTerm ⊢t) of λ
      (_ , _ , Σ-ok) →
    q , G , conv ⊢t (ΠΣ-cong ⊢F (sym A≡F) (refl ⊢G) Σ-ok) , C≡A  }

------------------------------------------------------------------------
-- More derived rules

-- An "inverse" of prod-cong for Σʷ.

prod-cong⁻¹-Σʷ :
  Γ ⊢ prodʷ p t u ≡ prodʷ p v w ∷ Σʷ p , q ▷ A ▹ B →
  (Γ ∙ A ⊢ B) × Γ ⊢ t ≡ v ∷ A × Γ ⊢ u ≡ w ∷ B [ t ]₀ ×
  Σʷ-allowed p q
prod-cong⁻¹-Σʷ
  {Γ = Γ} {p = p} {t = t} {u = u} {v = v} {w = w}
  {q = q} {A = A} {B = B} prod≡prod =
  ⊢B , t≡v , u≡w , ok
  where
  ⊢ΣAB = syntacticEqTerm prod≡prod .proj₁
  ⊢A   = inversion-ΠΣ ⊢ΣAB .proj₁
  ⊢B   = inversion-ΠΣ ⊢ΣAB .proj₂ .proj₁
  ok   = inversion-ΠΣ ⊢ΣAB .proj₂ .proj₂
  ⊢t,u = syntacticEqTerm prod≡prod .proj₂ .proj₁
  ⊢t   = inversion-prod-Σ ⊢t,u .proj₁
  ⊢u   = inversion-prod-Σ ⊢t,u .proj₂ .proj₁
  ⊢v,w = syntacticEqTerm prod≡prod .proj₂ .proj₂
  ⊢v   = inversion-prod-Σ ⊢v,w .proj₁
  ⊢w   = inversion-prod-Σ ⊢v,w .proj₂ .proj₁

  open Fstʷ-sndʷ p p

  fst-t,u≡t = fstʷ-β-≡ ⊢B ⊢t ⊢u ok

  t≡v =                                                      $⟨ prod≡prod ⟩
    Γ ⊢ prodʷ p t u ≡ prodʷ p v w ∷ Σʷ p , q ▷ A ▹ B         →⟨ fstʷ-cong (refl ⊢A) ⊢B ⟩
    Γ ⊢ fstʷ p A (prodʷ p t u) ≡ fstʷ p A (prodʷ p v w) ∷ A  →⟨ (λ hyp → trans (sym fst-t,u≡t)
                                                                   (trans hyp (fstʷ-β-≡ ⊢B ⊢v ⊢w ok))) ⟩
    Γ ⊢ t ≡ v ∷ A                                            □

  u≡w =                                                            $⟨ prod≡prod ⟩
    Γ ⊢ prodʷ p t u ≡ prodʷ p v w ∷ Σʷ p , q ▷ A ▹ B               →⟨ sndʷ-cong (refl ⊢A) (refl ⊢B) ⟩

    Γ ⊢ sndʷ p q A B (prodʷ p t u) ≡ sndʷ p q A B (prodʷ p v w) ∷
      B [ fstʷ p A (prodʷ p t u) ]₀                                →⟨ (λ hyp → trans
                                                                         (sym (sndʷ-β-≡ ⊢B ⊢t ⊢u ok))
                                                                            (trans hyp
                                                                               (conv (sndʷ-β-≡ ⊢B ⊢v ⊢w ok)
                                                                                  (substTypeEq (refl ⊢B)
                                                                                     (fstʷ-cong (refl ⊢A) ⊢B (sym prod≡prod)))))) ⟩

    Γ ⊢ u ≡ w ∷ B [ fstʷ p A (prodʷ p t u) ]₀                      →⟨ flip _⊢_≡_∷_.conv (substTypeEq (refl ⊢B) fst-t,u≡t) ⟩

    Γ ⊢ u ≡ w ∷ B [ t ]₀                                           □

-- An "inverse" of prod-cong.

prod-cong⁻¹ :
  Γ ⊢ prod s p t u ≡ prod s p v w ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B →
  (Γ ∙ A ⊢ B) × Γ ⊢ t ≡ v ∷ A × Γ ⊢ u ≡ w ∷ B [ t ]₀ ×
  Σ-allowed s p q
prod-cong⁻¹ {s = 𝕤} = prod-cong⁻¹-Σˢ
prod-cong⁻¹ {s = 𝕨} = prod-cong⁻¹-Σʷ
